-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5232
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:11:14.388536+00:00
-- url     : https://prove2.me/submissions/266022eb-c6ab-464f-aa26-7cbed542d74c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 940827338 ≤ n < 941007194 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 940828588 1250 940827338 940827373
    0xf020f0a0f11030105190f060b0a17090303100302010e040f0617250905060604090c08150402071119080f010207020111060f22240b0a051e0d05 63
    0x103916001d406180c81030b03106101050f080750403d40d200060451070841241c440b1032103800c0305a25040c20302c00082c40b143c0da108031607901d52182425000051207083ca4103020b2038204851a00315001c1c000071415450800150205101d641c040039050060030800340c105640c65400580b088040c1c0c600c00d000346941c802a221404000300c1d0940080d0080150b045110b84920070712404a03003603018031110252070084500000d0a020300600d4000204000101d2010074074020340c1d032907407100d5a5101040c80d00c901c4a84125020284aa120b24010080c0c200840c040c040454441d00c0b084070245070a4800c5a100d20404001ea84052418051000018106481075000c1e00c0302da8000e8a450030b171001c0310503a01d912400c00322182203a0b90100c40114a410f009440410f204451031140080003006c19191034003924041d9405018100a02c3d0702160303c00c1070b07800303000c034841d9054540b411203e060030005504155518102e00b50b03082002d00c642c0b00c0c0c2d551300313824040c03e42d00b09099907280110b1150510 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 940829838 1250 940828588 940828613
    0xc050d0309080d03020a0e09060103060305061f0e0105010203071205040801060f0e070804050307061a1201150501030203090c0909030909130b0915010303050a0c05160305060c0c0705010f020f0a 85
    0x42540500c03452004041e0290080786c240112517a1285030100c00101041600c88014000a04040e074070710000c000501d0412200340100d4066401c041031001c240d89903000d81d400c54001244403001c0c100100001d9800009951280e6030019002c440060919800c60340c6001c0d80c1e102c0340a540c01d100002804021345000c04041da00361400d220382664881d201561280c0065900800c17544c820003448002c1800303075211150f440803108842010090120009540d1a200140c928031650f68440a00120494621080c0146820b0a065066152404010341c48203401c440460050f0340d01d00000b05900c4050084400007880240340e8142c0b41080c030b5048811049500080710b0b1040d00f0004966021400140c881128401d1b104d40d0625a0842d41d04940710f0304007a490500307008211088a00149040c80706541c3c07100c0035034014850500e507081143c40e150024045124101c010040750900c180f0200d040c0f02070384c0e000e00b0f1046900b20303000c0f012850194500b90740304550044c0d040c160b04001c07400f0403a8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 940831088 1250 940829838 940829849
    0xd0b0a12050c04060311280b04061b050d032703020c090a060b030601270305010e1525121404120e090103020f06090a0e100f0608070c0c050d0309 64
    0x8078400d926071402c3c44202d80160002a000100c07503042818946810001c8203404100c40308800e0745140300040d902e00d169501d41046100850106003482882e5001c0030256000e07503080c174070200c50040c40c0c50f005d440780c06810301c4400300750319005e0b00718000345207003641c3c2070803c901e40c006059103810703044c02501c0356226030710140320b038078110082010401f03c2e01a6000303a5120a00345031035600c98000540342c1811b00c000c050f02a001c0144020300310301401c00114000d60154002284045594013801d0410300d07401c0e240d0481c0c06110b02071250503207092500141c400a400320f800305420b64203106844107000002000f80306420100059071904040c440c080c0039074802d01c41e040014110242c252a2040040462a00000114010030161070000c00780441140050030b61840e054084000c038100402c40e401051031050150f0900c0300c2407600b035031440018185406114142424254010700c2c4080c050810410014400448001d1000e00c011043c000c0c00024102002c1240342d04d400740c1b403209a032142 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 940832338 1250 940831088 940831093
    0x30b1819050705100512041104110d0606270b2b09050c0406211b080a020108010605071a0c090406090204051503100b070c150f12180f150504030504031209060807050d0b0a1205 77
    0x1c0c507141103100c000d445035030103b01440b9400383c14040c0e501080d4002074142c01062010010080c58245403440340364486002000225041c516410240e103090501c0c10820301403850300408105541c1456031035130350181d040c0e062869440e003508040f02d962903c0300090042c660302ca10005203049001a00200c1c60340300f80c0b21004241c0ea0740350107840034080c1500c060040d5070365418901c03804041600c043d0717100b011a9082030600040741c010508513030391504410b10450380000d05002c20724200c3c800031070b0815482022883c502d8020102c2060841d14800d80070341100104210080001c180c0401c409410b143c044151500840a0700510381d210341c05a40010590002c003000d40d403c881e004100030b150002801a001408940c0c440b05c01da541500286d5503089141222110416a400340718041d5000381e980548880c218105146840d243d09215414060340f104108402604013a46603480301c500d00384070b61a10406544403014155000380241c1c0300031802d4000c10080e40075003008a0481c000c604 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 940833588 1250 940832338 940832357
    0x30c040303020c06031e10090e030408010b040e03070b070504051f080a2d060e01170f0303040302190f0f0302010e0c0901030b1819050705100512041104110d0606 71
    0x74000e04c2d00c02900d9010f1180080c07a0711789809500726405a07000a081c222107210b89a66210300d00803603102e2603003018190000101044841303008d0292010304d8400702c13030821040205414559507480345010007440381c10340c40d0005074007074007030310580d030003080c02400c01250030101841984e040d0fa1841001008070301d400300866400f41d170912950360448000c07925554000034080c41c0308825034200b2042070300b5036219203020510144004546000341501c40300c0442030b48583c0001030030000c051038040e0342d5510510400c0086070b4001600c0403104040200320301100c4107030810080e04481458043c1a10308400d01341401c00d0f074151321150341c6200410640b207441c0d409408001e0004020700c8054500c48048000c541c0d4280000640015089150111598403042015400f900424403a041d9010340041100304074070f00701803020300301c00406480c00f01c1c03804203620154000600b0181014001011040d50900035407591780c80004200080f2090586480600e034030000a88054003460000030031012 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 940834838 1250 940833588 940833613
    0x51506040c0c020d0b270615060c030a1209050d200c0303040e07090f0f05031b03030a0e04022118030a170601140a020f0705010f02030d020d0f02030c04030302 70
    0x60207030b01d56402003504403800c00c0c94541001019014002a03000402040003043d2440303805651241c91101c4809040d552400c001800412a65018020301a500402480e10701c00d50100858040702101e00340380041d0012203900c00010220100018074900c02e00c1d4104e072859800041c41d1104002305002c00c010050082010754541104003940c503010f83c018041408006141102103500079420700e00002c2450307640c4000303c04c008050748110414007030072006100608051050b00c544140606480700e80f280c2e004040f035030701d203d1131003020108524818100c0c041d54480e012a110715581140c5240004180a00078400000990300b1315422580091455000c0c000482903c5040c801c43c1c503520401900d241c064045400002e003810304002d0011050300d03908030101c01500c201c5c1c2059004080d082541855a032809605422443c140a004090340c50300c158000219074030031000540245e12042841d10b800c000d4045074030f2800342d0340c3c0003008001240b0030b0700010702300300c03070085c1d003100c1c4580b8017403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 940836088 1250 940834838 940834847
    0xa0b09030601080f100504062703080a290d0507061116030f0213020d0207030e04051003260d05010326070c0e040503070f0302010509120f0421051506040c 68
    0x318000c401d5084081503654041065001561281c0280740c081100080070090610b4002c182c07280008240c9e107440c5203c289948080383c0351344010b02c05030801240840603201e03864008d1401c240d00c40b50f030345180204620703200c40d90b40c00340280e406021207180980340d42010b030038084030b51641032072407040404d4a10784034844003802044076000b26064824000540034000c4010440f1454203489400304050302d582c1165100501d06079000f5610342d88480021400c00042d80c50240c03d2804e01c40c8603200a00105a0014803101ca82c107031400a178200c0b101c4800c018801d8020030301d01c5150507142400000500c0054040c041d008400c4900c0c988400c91341241540150040c6030300907242010300384041c80344211120030640c200b80a2822641090090745c0d41450b11801d05a0440050351500c0c01e0000b041c6040001040040310041c0c03040c1000c45400e011102c0d40030310711400c0c06401590b460000d0146804100200c0c15801c0804c1da01c0981c030096110b40708076029078201e40602d00e042c2604d04010f114 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 940837338 1250 940836088 940836103
    0x3031e080114040b01050c1b040f0b0a0902030901060302042309060906040807020a0503060a060f0b040b09040209041103070306030c05010f0509041a040230060303040603110403020a0b0903060108 86
    0x101c50807190b140d6402c00c140001040c0c3c000406041c44000c0210315440303201040030315a00018210303007169045500d0705003c2031f11460003d80c201c0c3e50400e24203e00310b542c3c01040030140e81070301e00c0041c0c0366540e500d2000d01400180d0310280d0064508080300e00c01c551403495100e041a50301e00c048400391130702e21006a0b1550f0440d0607241c0c0380c005601117400078485070018070030140014110a4881d403107000003410410266034000e40703e03039100401c2001c900307051481c2000384402418a8245031070a82400000d1044100181c411a070000c5c40050594656010002a003611180944c4a00d05142c1c060000c003c0d038002680c10b548000703000a46136210704100e507078110741640c2d51402d0078541d5050001500e102c8481c450280c108104190a540302d91002d000c51068456001040c0588104480044801968400c50850000040000346e4034000121004c0341d540307107000110004c1d0008425910f003d140c01c001c0d404604e072100040d07810001c801400144008905440142e6030350001156180d00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 940838588 1250 940837338 940837349
    0x50c060408280c060206090c01091a0310030c03050f0c100e2202031e060d0c1e080604060f14250c0807030503100617010e0603150103031e0801 63
    0x4140040d28040049409030980c80c01c292000d85840701c160b0f40d000c0d0b0300c3d4441d000b10005034059000c0000e4a00d080140110b018020300b4030f0311000f410103c0310a6544001e01e0070000c01d80001002c2002c1440000030000156045144800202d03103900d401929012000036030407480c03003030030a40750451411040c481402e03941912000e03030100142c2c050029030a8941e40185000704403105d01000c100050005612a00da000404071003070b480000703403060b04c0f200508013501907020158040300241c0c129541405a851071150904884a0900b1103d002d900c140c000781150f00a44090204114950700710644114030001c05001e0050301c4000c01c41e21f158120b0341e4030643c00400c40c1000060121401102c007080141ca0b1500a00695032108199035000e071340d0460000780008100071512807541c0c05100500440c0c03500030315420407110400601c21040c0640e40a101464000c568680e504001982d11102c603840e0031091980d503400c020300b54210314114082c5c001d018420f034030714444c07140d01c4847c141c98 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 940839838 1250 940838588 940838593
    0x1e0312020414040b040f0905070602100209150c190c050901150807200a0b0f090703050d03020a2c030c0303120f09150a0e1009120e040f06080109050c060408 69
    0x2c800350104006818100b40340ba4100796107105549240185000342084c0300e00510007010310030b1914000a191103080c2c81c40384c04140c41172100041079541c040f4510355610000401c56118000e03403041505184240704202c0090491018003070810551540d0001210300072640410a6a69201c411980540301c0246000190400307000850950143e80d01c104a40590002c6600c3e0401d03e0b02c54038a400202803081e542c00c440c4004010350f0070428030026601c0310078403000e410414903554841e0f950b12542c60070f940605801060500c03460307205003035510440324030610f4000c04220b01d8132000c48441c0c0716000d090090107121400603048c140001250100d00e88810021f19681c0ca08c020207160483c0a01401414054180464201300c5840034281c040c9848000025a420f60790f1011032400c1e990280d20400d10b82041c0601c40884d12100083d0407040040c01d0000034010b20700300140c010450064050b201ca454007e010400e9201584840101449a0119200200385604100150080b4840c00318580e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 940841088 1250 940839838 940839869
    0x7020d09050f19180209040606020d08040605150603010902180306010f090905010f1e050105010c0f061e0e01090209011706070f030209061b0d1706011b1e03120204 72
    0x90400a40c40c3d024010300040c14030009840f5500110581c01d01040070103510380226910300246050310481e03004045500040642c00100c0781d02800704500204040c01d2555a0302c00244d440007860414484400003e0a0395940c0d03071039400c0c0000039008100322240d030440c500f1090b119410001503242c162810106030814032341c50705c0c2045019044480041311103549401280718200d04a005070f13601c42001d041912054081200c9903000ca6030142e000030304001d245058030001c82e0004412500442c1c100ba4042000c1d00250000140d0910166807941000d26016024040240644c041e0f0401d610031909050b282c0d0b0f03201d81003095501404e428cd045a000080494481ca001759200e50000915080140c18144010000782c4541c02c620b041e90400c0c00b0352046c1c1e14540000740202264900e1074244501c0e20b281030500d42001380d5000b4034241c140522030329000c01c03000d0307040349007801c2a600008c2c02c000d811000121565002c00b034882140442d43d00b000d0b0359614645402a2000d0314640000c2e140312 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 940842338 1250 940841088 940841119
    0x1005040c1712040b1308030d06150518062a071a041505090a12060203041202012a0903050307080a0801050a0e15040212040b040203060610021c03061502010507020d0905 74
    0x7075403012004014600c020000050640821f202900c0320002c8100c001a0b03c80c03400c060b03001e582100341601307800c000e0700704040d415180d11030302000b0300c0c00020740b0465102c508070311160070f80803000c2c40041c802080401240c10300c0400002c80b04141e40300d43c0031028950304100c104202d64020b600461505505404035071125520030781c00341c1080700d001400315030501d94403068254095a90f0009540040d0000100001c0c840360240302c096580070b600c020401c1c04120f110015801009514882a000c13581341c0403030078107110751400b0b800703103400606a83e80e031140e41c07900403d00d030f100d044081c010584c000300005403464410b42401c121401d2103011507035540c4a030307281c0ca4411100114240d02a6091100c8000000c04110700c0e40300340d00c91403840300507090500405103007941c000c02c0140316038100034400c11300550100303050300d241d2401b0320f0040350b8400c158815400b4200130b410801c0314400a1b25100340c0c40781c0c15013129014550507002d640304000031040031a8480785c18007507281c01104803c3d039280b5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 940843588 1250 940842338 940842359
    0x51206010302121c09050907051804200a030912050c0a03050a140d09053708071e0308092a040f0507030b0a050306271005040c171204 59
    0x30003240c1e0f20603180100142c010f2401c40c00d8407038100700300154141409006508150440d41d0304859107040a6043c2076420200c0001480c204254500468942c40340c03042003001048085203003030000314042e07150600600000c004010303c1205070b400b20340444074505020702840440c0d034070260078400307450300034510346068402da03105c00300c1d840c100500100800c1251102c2406010a0204142c002c0b44891541c28000d1a2854202c40b01254110f00c403000c1390781762481183c02d03000b11544000c0c0f903503041250901010303e00403443c0182c91607915051030f81038810082d000c560007603c240c54210550302c84154003a9542d003982d03400362108114080300286400b452280d04440e0348010300214400510a8180017030b02e0054812134007007602d0b0200d840651500f01003003009040194001c05542c0341000c05145400a00d8450b01014064803a0070008540c0a011060145171901e8041c0500d051501d04003600400070304c6a1f01e80c903503602c0446202403802050b80b012121007105814209802e0171400c10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 940844838 1250 940843588 940843609
    0x40b07020a0206030103030906020114060a060c11060d050912030c0301030b041b03032a020a05100507140309010f03090201171806190c02030412110f0301020d15051206010302 77
    0x2800e500c280400c400060740c07180000e5010314860340d11407000c4c914001002e402e6801d50104100850f09030341c100649511080721a104071101c61404c041e04940f035040003500206d1880302150044c200103801144100b041d00080d00803e003c0301115003410001940324070078001664000241c4408000400220b00840c41030303a0081e00600105103244043c14445da00c200c1d49c1d904c00c03004a008420100011074105181c102c882e00442c0d6802d0565070b580d80011002c485138028544100242c9022261b61482403040e070f6085540001c0142c603c02003591003d40ea9049264400e0000d0941a51070485901c64050320000c541e060f15401502144040c4d10101064000c040000b284a004490842a40e0800c01c95004071080602d2607802004d00c03201030152043c0c11142d909641c000c03c0100601d08040740250101600080c140680030290700c00501004078082003c1d138590b0001c1491140942c655103c010705001171054600010780c0c030028009020b410803c507610a4101e5801040903043c81d01401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 940846088 1250 940844838 940844851
    0x2040203070e06031f0510120c031e0603060c17040201030e10090b062707050304080f0408032802030f0903031306050a09230628030207020a0504060e040b 68
    0xb07074500864001040c81500101c4180e8007580c0e1803003071007203684c1c0503424440103408103442000080b00a654050401052050420030710b175510a4041143c610035882480340341020900040d000d02920a9800070b0042400152919490180c2d10b100d040c1c010100030407250340c400c00a04450f40d0f42d40040d001014040c2440315680640c6824143d118524407624050504c10441c503d19820400148002c81c0d901e107003544802e205c4000c47c05051444918116440302d02c5161842d6281e89500e0007a1042c0031312040300c2c5543c03a01040101f510f00010002e0a0b144005981d10064000c0c2d44419000c900020315108015800400c0341c603102e10241d1000b0700010901070100d0780b500755600b001c0710300c1040c0c0d0f500501c0060004900103c2180d4010b20540080200d503420352076011882c2d01c3c03c00407a002c04045445004001600548045070001d10301da4280c00c4840220803190420300503000e5404118120b100c0d031203144011030b0030f1030a882108141c4540f564203012594403543e68100b20fa90107040c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 940847338 1250 940846088 940846097
    0x90302040f0914070e010b0a051902070b12240f0f12062502010b10082502010c020c0915010c1e060207020a150f031a091e06030604030c0204020307 65
    0xc5040303002ca000084142c200202036061410075a05c010300e45c1030b041800c200c0c0c401c1002ea04900d900000342d503203000c002e100010301c0881000050f031a103240c642c0407038412107020403102c070305c1e00413100c50300d02c5003c000c030940d402000346211614802031240b403100e510000407540e80319282004500321001e680c0c0905181e0442e0b2507101d0b01e914008003100c040c550918094031300e0b1044407802095510500c5c1d50700081c02101301003000607001c40110f40000d4200a0f111001811a12806c41d46071901d0254084002d1044110b143c024081c003082188540548568414904c89040460030705101d00008140d241c51100f280c801107800941c42201914188d081d644c442c50f021041e440d058400301d12440c00181d9035036040c03040c0034031420725612030104011481080814944c001541c1c100f04029490006003001d000e00085200709405103605804c000f00300e003041395000304580b20f03d540095042180300c903540c0d400c0415a80728421540240014800712111005080c181c018541082503030030b1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 940848588 1250 940847338 940847351
    0x618010605030f0606040c1403060607031b030201050906070f02060f0406140f0a11180405040201030e070b071b06050f180411070b010504180201050c0f070312030507020d090302040f 80
    0x2078a080440102c80e030f0580c0003441880103e1505100781d02442d1a81e040c000c10a89403050101d000307000051800740101000280e00c010107209006c1010811480c60310f5800c45801814000d00800b8103c80700c800610445000c2403400d07015501c81300d40354216038000c26455035000c42c1082008005041200d506442d50106092201c5050a04d0312401c802c1c0b010030b00524104280740141ea090480c2250242e00400c010840000c2501c04240038600a5070042100e4846100480052104c5016104540a070600c0800d040383d07a18024600280035418200e008070417001c2c84040c2050710b1080b1008540100b008400c181d1700310000c4d0845010300c100c0307003d80d203903460081029104c0c415114031000030b001404408001903a01c0d030502400c8152000c200d89504c4800084100c4603440004e4140180440c1068076084104107103402c828110307043d2480c181d80d910308580c001002540000100341084001505948001a81d00e210f041c1c55460020a41c51902800000d1039002c219072101d64480c031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 940849838 1250 940848588 940848599
    0xf0e0d11030c09240118030b27150609060a060f020102071e0201030e060702030d020f09121c0201050403020601230901030c060e0a050d060e0708060c070b090d0206180106 75
    0x200854414203400da0740000130b08241c1c040114042d19000100d040c09548620944242400c0c0e200c030007626032010203030707001d0b45885500950040440300081c12848482c420b182820401080c24659503030500400c003140d8039a581008175400c001c440355038001050803010030080b071003460390907443e42c030300e000061800d01203455104c0e00d50102c038004204134500c0101881113582c148a82c1c03110603041c2026012038280414000d4513845902c080c4030086401250b245e03100b080640c12580751803001044010341c20710460720541c988160076411391520f60241902000035006000307491180ea41a405807980741e08003c801e1131041c240c0c420281c0c1400d01d05801e102d55858103140740e03010314010000c1c0354129251846c010b06416452081500441d127080c0c0c104a80e403550328203007041e1540004089170082500320030514143e9903a1100801b4812003050140030b071303c1000101101801078400201d550b458070189603840c0050521000181c1c00076000403c00038022030104a06a41710001103600c56a42 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 940851088 1250 940849838 940849849
    0x60304081b06071101150b090312030a063b04060f18021002010e03041701020c0a08040503070f06120c030b060a080a1a061c020702041b0f0e0d11030c 66
    0x811070700250703030064040c85240ca0b04003d082c0300d4024540e00030b02104403040d0381d007131440b044da01c50b0515420010869032110313502070014190355900c04c441e458a0745403d40d00c000c00b84c0b07014414582028009400c1240c12200c00c480c0031201c070842d03003400c01200502d442e4640d14410040041da18a48d5944180b0f441c1031241c015040054880d0040d80c2169145004000700181e04066180642e0303d482007041c480c1d02d000c0140e808843e03521201810603880700a405000e8071401351011203c2c01184845410030541102070416540140c08441645858408030b9005041701e00822010800c030002d054508091a004500850b01c5440d0204e0580c100070301255040d00516100800f045e0080200404040f49104040000030618041c4140326508000706455200e50f11104034103203944411100181d00c0340c0c045400c21540030b002000b1046405401489000310b446891000414401d403407200303d171140740f049505400080a481d1564800d640d403085d49501c5406082d0940a510403034802690352 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 940852338 1250 940851088 940851127
    0x90904080306130c020a02120601060c080702040e03031f15211514030f0106060903031215030f0b0f06061c0b1216150f111c051317060606030408 64
    0x41d174006103640c04191040108030040204070080d40d521290042001076405812610025000540729940d15140d00200740601401840f201c210302c000020b11641c2401506e0031ba0300200290b81212690380c8810f00c44503481c040c0500e0600040203100101f0001e00f070300508440f01010301000203804a20080c641c803004100da400100300c0118004da10300c50342802d0140a50100c20350008020071810550081c0c044022404040d041006150502d1090b008070b41c0101e842c101d03100c070020203582d070f0b074a08180f140c01c007118111100c00e60031010902c800e021841c0640100d40c0144683c0c00c0c50960000111501e13044a101c400c05074803884c4011064543c941d000340c00a81500142801e00034520b039600c10500d2130307400001403103024103003c06088d82c0300d862a040d6100c10b1408401c2d804500c0900c92a0590751180b01590b0b8100311207030351829420100030411071703507500281040340b41d0f922002d0480e00d640f070001103001e4000034002000303864050002c40d8894452079506003081d20840021440500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 940853588 1250 940852338 940852361
    0x22803090203061f380d05100f140f0402090301090f0605010f1211061b0d1107061407060c051c0203010302030606090603030702040b130c05040e010b09090408030613 73
    0x500d10b031030550710000d1503016014009084030400c0e0f8021710080301d41644a01051a075101c2c01d45402152071003031100440c0c1d0741c00d00d03808050016041071303142c007920800144138590214141701400210134445054982c0f510100034540710b510303c1e019050001070340c070a104035035055589850f0180064000c0e80a442880d01414001800e58104000d0501d202d200d5003004407074242d120640c0e0700060020081215040003610711a484107484030321214040d08c1200e1800c024041c440740e501c20181c1c8400820380c0d460f90b58088401169036400240c070b5800800181c13101d032960411608010900e02c0d00100ca07010254a0075510740026130340301090051800342d1000e02e050b0000010000d524042200982018040b00c25410394101746001a0780d910a9040082c015a2102da2000d01031755084034000c2052400c0c02c0502c41080c5040d80149a03078003a000b034003612400c5000200300032160030103917030400801034601021307522907880e2449071b41c0000381210b9104031002010140100c450040014058 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 940854838 1250 940853588 940853611
    0x1a0108091006140f01020f060c07110a0305031c0e0304060c05070b1b0d02030310090e010603050f0a0303140615030a0605030106030303020a030b010809062409070c020a0902280309020306 82
    0x11030000410130980354280c1c1660442d8440644030360750343e10205100d50050703204002a80e80d500c7c540b5002d825601d0311906954002c04007900082401004070050880342c0c031421f05252140102000d0004481d00c1800041d00780d88280070130f000d4180201c50300e4101c24024401c9508841d41c9080c0070311140c0c03140300c8186460740049031003070031100c1c1044a406899900d00146085180000a6804a00813441080d464540720031034140c000d00c080d881b4101642e001002d46940315021703c1e00329030754500501c0440000c0d103014084171450408101441c0954001070400034035103030b481801c09460304094820f10926a40300d000107190b541c248a080029813098401503100d2862410103000ca800d0203401c1d906011310201080001c1c1c2011071040c0d48007004010044425178401c80c030b202080d0401c10403d4000f011007040c0800a03400c40c0c5a581007038400c807060031342c458550080009900400c1c84041d0408a050b8100124500d400c45204d10030815140000c2c400c0092b8001a14001040e91840d4058 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 940856088 1250 940854838 940854869
    0xe03130f06022a01031d0a0803090f0c091f0b04060206151212031005041505210a020d390503070302010c0803070c080a120f1a0108091006 61
    0x482e0103120011015070a0410070001c094002961400580c1c00d03c0c0850416650b000c0007004040d0111603405002c034110129446210b031860084550382c4295800c070002d1003124500d0b43c01e800c0000c3c00c480740c100003900c1900e850700c807c90189000e4500c2904188044200d0324045103c2000d034002d0300c024070341640100300504054844046c501d14000c000c40c011000340002070b150110020308600443c68a40d50b840d940e07a00c2440110311703440c907900145d03405400e102d000c2001d00c1d150700300401628000c44880203c0324884036864120f2060507641140c0303410403904e0401502d400700d09003440d82e00a03001030707846175031490200240b0314912014480514464654401203d04150803401800d0305a00401300581503400203440ca440d07039a00104900c10002c0003512140c410400710840c9580520041c1d08d41d005084c02a090000c056180b5070031900e0208a0b8603140c1d00c0e8042e4075000d840300c10543d802800b801c001121160300082c00000c40307200310b03c3c0c1c1d01e40003402840344400400046c810403505 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 940857338 1250 940856088 940856099
    0x60d0b04150507140909180a030909060e01031a0601090b070b04030306061821020a0807031e020a0315110406030e1e12070c0305010f0b270a0e03130f 66
    0x2210b001a00000c00c0180c0c03050701c0802c6a2508044030a00311040f55011695659411046040301101d600315885001c0c0411010402d600301c1004c1c020744404980501015490b040281110b110910000c0c018401b18408050301101045080ba00a281071501c8480da5403070303c1c1030302a80c0c5d001038412038503400b03282e0410081c076502d449003801904103890084003215402542c1e1203c3d610034058001148803c03503411640c1d41420306030907072881d03010f86174007032a5035160b5000f40c40744503900c402c1e1607003850340d007442403200604502e1513212540204007410960031a1100c030032451409003030301206560b4540003160000803c01901c0101030603640800d244004001d094204031918040440c401d8045640c1c8100c000c01050320400c00940c2e8100a0700c4003910b0800b403014212a0b07001400c00d5203002d001003540c3c2c4840e040203054a03000c0e933140d07060102e0703d5074207200d8151804420a081c3c0140010825641c2e1a800903c5426194000c0380c0c206541040a010641003e50000c0301202401d40304001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 940858588 1250 940857338 940857341
    0x50f09010b010809030f0a021501030b040516180e011d0d030c03050907170a0b07120605060a0921061803020d02031204080307032703020115180203060d0b0415 70
    0x101220280b0f40005507050403003c155890007020040380d4003c4000c00c010201c180b082000d40b500c0d0306c00842d42900f9583d603060031203001d2000c0d82c0596071805071040c40c51800d0401c0000c00111910008803501c824a20401140200102c003005105952200a4040c208945042a15001c1840400340892105110000c0c04443c504145c0200b4035003401c0420100041c08207645007122421600c80342149220070000d400d04440483c0101400740c5403040c0001c00d54803605490010001403010050703643c4450420086014124100c2d000405407501440b8800140407803034520b803002403255145031030568038803041e600000307904880310038844104400e044d8100401c40b41c208440c0061072174a034901c4c4800c0301c038280080001c0e04401001000c13540c006c2c030a40c80031074445001c1c1d00f110603450000c1200c91008411f00d90640041d03082030210011040c040710140200c410b45000700003140b1642c80403801a42000303001950120080001c1d41c0890303022000544900e2145000c9001940c0e000c0c000700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 940859838 1250 940858588 940858601
    0x8010b18120d1b030e0609180708040203160302060a230c010219080c04030b070216121505090c0d08040f0312120212010e18120a021c141606050f0901 66
    0x10843e00154030b05000c240c00040c04418280d050b038095645021001c042420403c0f000f1101001c1066101080044ca52142510303010f45e10890580c1c1d186120b8403021840045075000203580b01404100c81c4080034050010b209410040302c1589080e001e2950142980750000003c608107a50001100303080c1c981701c4c80002c401109d0505001c2d0503803c0c00358190f41603000c0d50100801005524002c02c1e50a0700800114000485000f0009801912001880d04000142504540c7c04029070409420300e8031a009a030301c601388400c001e00c0c0300e01568041205a550585059503510390401020465055011042d00910b0040f1980403050007818402001c030041d90fa00500d4a41c8140558010307130a44c0451303181112401b40840c0c1e2552a40741d424101011603000400051141d0404a0000e189060141c03550700d00ca6000c0c1c4041681c1c201094512507070841004c00001d01500d41000103408042c050940d021100300780344226602d9681d1038044541c00d03291071426003c08010040054400d000c1c84 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 940861088 1250 940859838 940859867
    0xc030605030613030c0501140124080702030d180c09050601021c0504050d060e0714040c0206060901050114070b01060e1e0d060513080708070b090d08010b18120d 71
    0x82c0000c0c508040800d106000e0044020308204070651202c0c144a425044150042c0020024921559458212054542244c55100180c00c81001d021040130300903003c152180c50650051880e182003901c0f00801092062a1024040b07440000c0c1e00219103006040c5014103403407000001c039401c0942c000fa04e403060521401c800c0c0704907072451601c016030010130384003120016141040d6951140ca41f5401a044000407200343d07100e148000103c1c0c10040720405440c150580303041080500c40d140403038440340112001074209480900401040d44130700f40900b070000c0625500e508001e855036a0707050982e42a0300003000580701c4002c2031424134000c180e000080550a601d00300c107150081c0800d40070072906102802440c0d4940008a03152046030302c0c0c40b6501c0c0c0c003241103943e8456500d401c0c8820f070404141a10311010b803c00081c54000c0c000781e5154025400c0d250007480d6860511b15a08071303841143c0c080d40040d00e046803054243c0342d5401c2c3d94440b403001e5010740301c01c80042500030501c41042801 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 940862338 1250 940861088 940861093
    0xb0f0a03050a060506040209100801090b01030917030912040e0f060604210c0f0305100b04020406020709020c07241e050417190b040b1003080306040e0c0a090c03060503 74
    0x8100190703000074040c00180e403224010401c0c0c1d070303400d0006009004203405581c10075889400b0182031a4854066816150881001c104103190140111304607516003900a00d0650100c0642c0c2c411a25000550341c044556070031550701d4000300c07000c3d0040360016070003032000d0450003051280c4200281e000c00c0d40002c090b60910304262500d105500c8024918520454104444200805101090702e00001411100301031840607580d0b07240c502d40c0d6480010703000464900d0900001e403c3c0c5807900858040303c02d142e00920307203581031000580c000d60206405082520400b0030010b07440e0700041d5800c103094105007140039034443c01400030301500f030b4220a000a02410b00440c17510b00740c000068500341c542d1403002c200700003002c000043c58104041c4c0c440a0960b007090000f002c2000c2048498411440f40b021000580c9541e400d211611340c1030300008007100340034400036410342044c1d8810032000c840141241c5851041002103079600c00d850f04418100b0307840301c0d440c80d10250940a03800c02003400381d00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 940863588 1250 940862338 940862359
    0x21c08071a0408040905100e010b0903061807180906140612070e0c0a03020403082802070e0103021e130f0c08090a032105011e0e13120207080a060b0f 66
    0x11103d07079902c128011251529518404601c44644840c4250040d1100441070324403540c40341002055a0065903003244603124410004004d1100c100f408014014110010601d442c104442c41903041540d003144060240c0c1c0e10014000305440e4051807080000c8500184c15504004040c01003080c84140400c02c940d1281c030040051b00300b01c1c0b500340ea1110f00600402e0316040721420480c0239206507407014000040201e01e2604940d600031550342031780c0968404600b10001c40c0d100340d80303030903840c40344801d001c0b111001000541003040300d45105043d80c9400081c040d08140010303074019045407030071114540c1c1c0d800c00e000b0f5416900c641c082c0f80195061070102490541c044a0340c503503090710300900300002089152404490f01646041d25040107005110130b40c1c45142d82441c5900c01240b60b075480d12080000159502605c20050060501d9100302c20240402e45500c1c4036609d245605c10110710551400140c000b8041c425a40000d10070340b000f044804001c1d04006101c03128a40d00e038400d550141 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 940864838 1250 940863588 940863593
    0x12020f010c051c1b0815040501090605010e090f16050f031014060c06060409030e1509030105070e130915020f18060a1209051513050f06060d02040207021c08071a04 72
    0x50400741d01911324070b001c101039601d5001d5500300300c0c200c40209410508200000c0780e003d855412030b0b025510b00713030790300f08480da00c00d4200885400e098a001c1e1307540313400ca00498110168241c0c00c680c482c03014100203185c024000e90544041c1c1c030840da580c8481c101c0d0001404480e6448408412110301110000e003095a040e040c941c071a980940014800c0da5600c40c0c0108150064000d035500e19402403003104441820640c40c891540501441440381d4030703000003d8840c41c00b4020300303407a140001d006a220b04400b0380c007680041600d001f064a0718170f0b07030440c400c2c0c03e4603540c00200300210350190407a464a0101c10148084001c10001c507100311340920901c01c00c981d202011007401c800c03126002c50340d00c1c1c3c1402c1141c02c0c419001c01c10000310410f8401c200001c41490b88080e0802e20075012152540c6c01c910300a07880c0c0c807068601c0c1d079000c80900e20890161038590090410580014480c480b40405103070344801d00401054101c0c2c0e40307030700402ca40d420702c0074882d40c000700d44201d80018615468541d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 940866088 1250 940864838 940864871
    0x30f031a03150a060e0106020d030e0318062a0a1a0606120a06030807080903060609040305032a07110a0609050936030d1a03060412020f010c051c 64
    0x300b80c90440344900b0300000340480c460b50090340c014003c034012030200796103400700203450b44d0001040300c0c086410000c91400c1080004115828130b40c540c8040ca0030146008108940d65006030800074001011207408181000c500300481c4600c0080d800070480e11301e451501c22500c5460808804180820604010298883c4002c441d4001600d088200c0c0f66640d00144000610319900045c01c07800021503050700f00a0501c00500c82c1800807411243c1955a08082103c1020100e50050009406101280c05007080c0ea840e6082421101440c0d080c200d020b0100703200981000209441400c4040f201e412603003041070584000c4c2107207141c800000c1d81010041040c048e0068100341c1400340110150b606035002200c90249100d5891070307005072054020b44240d0341d0f003019901c20442d5180042c601e00b02821164405d810380c00250107400c059460780c0390720501d400301000e28000d6000c0e2402d1100203440a00c20b036440500d03243c543c1c23500c0301560201050902c6401d1082100c0c07a251810300b00b00350780703403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 940867338 1250 940866088 940866103
    0x90f0e010e0c220306050609090c12210a080c040f050f0a05061c0c110a290108060f241905040e0a0618030504030b0c0f0304030f031a03 60
    0x220101c110320344074940a4102ea1099000c1c11400000e6049008000000e540c080c004507400340ca000d0003251a900704202012038140d407130103c15402141d0302030702d508140c80c1038100703901c00c0c505540e583d25505d802e049040d0004400c0038441030340014010f0007a904000301c02c0e0045890007c1d182868100500c84030b05034880c1c000d070341c810f1140900392920303655107e00b400040d10000c0e000c60348070b521080030b618421120840814009042c50b80a43c4214802c40f031600c501e0b03d01100601803203545480d0180781c0013200420070100080c1146804001031803016403402021140300a00c128903040e9070441141a000c0c191001c050480442c3c800b0380010080b16180f400d004070b5100e00c5032116540d030f00141d2072460b8400d64009080c0622542000d00119100c940e0600130b490601403101110303e122034603012400010003180c801d10084c0003003101030010b5903204180c0309000703240c01c107042c0b140a21904110341c00c42c0044c1c0c1b04d0710825611075050007a640c0da0204071444102089566000039241c1c0c40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 940868588 1250 940867338 940867349
    0x3030c140406031d0a0201230f0f0901020d11070302040513050a050a050106060f0f050c0f100b0f040908040b030903040e130620041710060801051f03020d060506040e01050a0b01090f0e01 82
    0x39030b88441e080305504021209e2500b01113103042d982d441d403c041c10303001c1c2d0000010030b400b6018000c00c20781164029070708074103a110030758041c00303c01f821982004000c2c44050440003040345982406c50008008000c0301301c48070302070740040c510051f0600d411402e44080b500500f08210400031004082e9030444840741a5100c603080c0261500c3d034040e10145407042615500d020f40c03040d0146040b030305500e071f881800c5941007a80c1142641444100f484161010604010440d01c401c00c0200442111080515003007842e28003502d12301542d42c81d131030300441019280360080c0d00c41c12561404204952150120340140a500c1d100c7c40500a0403041150049214200710b402028880c0c4191500a02608800f0900f1032001c00c856915200d00c03a0007000304a81000f0003040c0c2c0d07030b800c1c02c07c0e03c00c43d0070010072a640144142c48820703aa640e0311002c0e00000c4c00c825007143c0c407454016a41c080a015840c407600304002d00088940e0031200040038070302c180d840342d800d42e01c10715018408050704071a40d505645 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 940869838 1250 940868588 940868627
    0x3020103020d15030c0609090501050603041e0501020315040c080415200c060109060b0c070504020711060c1b120a120c081c0c0e090403030c140406031d0a0201 70
    0xc491240041c0540c10341d100f40c000003000b004000c2112000c2d0810954046685c0c15008580341c02c3c2e0003049540a000f1207a11100500000b0001a5400c484011300c220724111030880304682d0b03852500b6030b00300390f559100c6128441a03001090070980314111458a00f07182c01c480b1340c14561220351200b4543d505d000c070003d8407114405068400050008110040c0c4040182c1d180c0000308501d031030320b50a02900c640c8900b41040014420300c4e400c00d4452031729041000e4003255240c9000c200c000d46c0f203920b0480d2400303c492024081940d800e005007640c00c6080005d000f5003d01c0401d420070460a03940300c00d2041c81d20700d07450b4000d03540005405201c6648445030004d50400001300b031f61100c414520082c0480b10003d01c0b105d40184074583c424141800c0103085c0001c405680069508a403000f0100740c1040c02c003000070780428407030303040321600c0f91840c142480c6124815080801aa215400c1100804d45800d2100c0c201040110210707218040e280107800026020381c0000e0140c22180e04001d03480 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 940871088 1250 940869838 940869847
    0x3031201060203030601140316120b101701080a0b0a2018030d02060c07080c0a0609080d0b0a1d060a0308040902090901050a03022211041202011101092a1e030b10030c0302010302 78
    0x1074020340c008138401d080203133000000c910310400104580d03e0407829070210041d00000007210307600000d0500c00f40d540101881c00c190f4462881c0070091603905050b500702c44058000c0c486960460001300080481e030b03440e2240441c0c8000505d0301d8034469a59910443d4060b404102810400c030341a146420f03448500c2c20741d20303c0d003580d10074600f02c0c9105001d8100f52500e0200010080c001d4018100180c1502040c00a50002002c01c05104228411034124050301205410032110719440d6650000000f0252009180c4030346640c82070b5000b680001c200f860740060190400d04d80482c116006190889900548a0860b404180742001c034078400490646000c01a41e02003100d600010f020700790069055859035a50a40d90342d0000c3c017410240d010401908801a8005040c00340751280e64125410428507a007035007c0d40c1645105010100e080c441038103000c18520b00d90514414101d0603200602d948074154100303150b00c110060001c1d040c80114020400018942e0f030684800c81e502420016141c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 940872338 1250 940871088 940871117
    0x8181c09030209010603021c02030c0315010318050127110409050a0b0c0a030b09360307050705090705070b15060903031902010c0207032003031201060203030601140316 74
    0x40c0c003003034100070351002c035800c00814030951542c042c0c10745c60290b11580302d141043c071006408030310081d00c029500da0f030f040000034000070b8000c9036811000018500061500892501c04920903400d1504950994481c11a2291580303090122002e030701c900c2c1c60080903801c0302d651317103801d0740e02c0c040a007401181c0b42c240b1101030020070310902808541001103901c00d03140030000c102c0360307612a50403100841d160135094001810000c010f140b00d02003061251030b8180198880d04010031450408a190f9007044903081041c1c80d09102411038a40b10302e0051011782d09180411281d81c00041210080140a006100120755001c1c03130941c01071320703040480108258103008580c0c0c0c2e00c120205203405100010b0038210640380152401801d5011340d008001218020808a03150070706848081d015034030700d00000141401c8a4480c09860900801300c9180050030010f030380842c1c0d0b0176449900560004810003141e544c20550000380c00080185103403840c90210241b514126a00e01d8050820508450394010b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 940873588 1250 940872338 940872347
    0x61410020f0d030e011b050715110a08010e090a05071e0306020c160e010f0509060d0f12020708010c051902070503070b0418060302031908040e040b040308181c 70
    0x81c01540954902901c48500600600000001e4811941c03800064080d0340b408079810004e403000d141d07038141c40e00d11140c68000002e00d00e906c01402e440e5070307a0f070b8400041032110010302e0020382c2501c40103455071500e401110f100000811007502d9410101e002070010b40d02007020020b450902541c00d0315030346400b081064140c01a0401485070b440001d20009045000450104072030f40c45503c9590b031030301c41010038400b6500380702c1c45000054071001440246001e4040c0741c2e220740301400703101001d9103640f242100c142d544001a100403405042089860b0703414060131001d0600c40c00203000000c0307107840003040c500ca00408085611042581c206585109101d14801000001c04031a140c030b484029038030141c0d00c00d201d0b046210740340039040b08400c11280a0b01013140c0e00100641324081543c401907944a0311030b002100d084000300f0002c201c2850700342e14240954012074498000d49418a0007408030318000d0020100c0b210040c03602400840300140251101e0141c01c441c0c1d020585141e4143c0e07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 940874838 1250 940873588 940873603
    0x503190e19080105181207050a02090f0403090819020d020f03010603030e0a060c15021c0c030f050601030b0306150303040b121f080a0206090a030506040308180106141002 75
    0x1903109008680424040111242001c20384240d0002003205440c0c4c1c01500d1a2134a03d2040f504a9401c1280807144c03249862001d0482c43c1d0140c0e05880880305580d0020705910001c4030301090741c9100906000c00e041c1c2c802000809812850010659422010b040e0959000318002c000d11610600c8600c0c421500c440102c0660300c072028009114045d243e260103440300064151060140465030300029403a449890039001882d00b003480501050700700c1c620000030f03621110244c02c1030a8502519a4625041d00c84c0d8102100a9074000924415070100501a118060440c60405042500039509642e0101e03000313802010722100112255281c1340800e046029a80c070026000c10040303201d00da4403801404091081c1900740544a6103a001c5007943d0302c184142c050008a54031600b03c507401803d1000007444414030060801014540d2560f40d280f8014003106d040300055a20414001c1c1111300d00300315024503030200028403c0c0f0341070445040316071150007c0c0c580304480249064804600038029807 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 940876088 1250 940874838 940874867
    0x27020705010e0c04051302060301140402090a06020a031404150e120f060f06011403010e25050d0f0203090d1b1a010f1401081303092102180103050319 66
    0x80c052580c42c41101d584034141c100407a4026420800000c01e00d80319000c102c00f101e036008000c28116401c00b22599150000c07840c8968002d5420402c0d400c040d611640480e009081641c0200707001c1a4a26000780b401c20001d0810110f004c051009012641e0319060001000c580d5140c64550070154500062a201072001c0c0d004060090001a80c01a1808141e0500c120403400c40c50301c6d00d0711000d00441d40781c0004030140343c1003007042c0b0040c0501601000c0700707900821404121801c5039111031082c0b030300c2010480300c00040345000179400d03140c50503030040e06280c0d2341501007181103207000c00085485904060723000081000e210f010600e0800c1121451081d01c0c1c10440182650401004614041ea42800750701c45840310384100191041051060f0000340380306940c2c103032113a202c202050741c5000d0185000ca0030301180c400049060591035107110441d0300c0d1044108002d00550051004526522072921800d844103401070011441c004101c40d031180c100c0e4030151500c0b00d44a422107000c415480b40c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 940877338 1250 940876088 940876091
    0x1202030a0f06150908060c0301030f03050d1406040c030b01141b01050a06080f0309150a120e031812211b0c180702100f0e0111070b0906012702070501 66
    0x320700321049100c08a406242901e40072842d45d11111240c2c0e940004a07060061400308100500001d914a4043e03054148281041410a000c421000d400c0e182c01c20b0745215a402ca64040182a10303040c02640301e1740e001401c08011400720b17040024103c0b210100d58648070003001500c0c621140440700300c5009540110b0003001181000c190400140049200342600c07446880e004c268803d01c0842112500308008102d1541c040322401c04102c40d80101034480d0500100c40400a0080140c1c000d00e403108090401940d51040e08001c02c9510b5209110079601401c02001405080308000448074071a00d02080380031000036100840e10070f10f1142c0107100710241805980644400000502000384643c102c903209034000c0c07210844030401e40e0440d0907a00590019820544030000350b44204020003e0000c0400d40f40700010550742960800441155a5840011b41c40148054486099004148003010b080c00354500404c410300700101d81c24901d88000d803440030280c0503a00c1e138102d80e2a650300000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 940878588 1250 940877338 940877351
    0x20109151e0c081803070f0807030b0711100603050d111e0a0807050105071407020d060504020103330b1606240e04110f0114160816211202030a0f 64
    0xe0300d028208a0b204c501d4001c2c41190ba021506a51040544090300e03181e4004120070340c51a250240c0c61500500403505001e0800164a640c450074803803d002c4045c00c05010a00da403540c60b01070318052404007800b003080882050000140c101048290107401c40307040c08020042c941124a08196801d003006100c039000080c04c108000042d0001031141e50f064444518100f003001103074805114141d0000e500c803038048200d9000a000e40d001541043c018940001c0308103d4072942c04282c003000440c00298201441441c0c3e050003d48481406420713589021410154845800360703000420100041c800c5480f60600198444084900d0301a429042c0185c01c07031541e00d50303140700800c03010f44066505482d0284050018104000d1181e03820006a44000c801203e4142c0082c50b034100e142c902419031400c503490360111300c0c81000350480c0d08148401c02c40d030424919008109980c00c0407409a0714a0b03c4d00c0c696030b41d603007240c290002c501580201507034a990700c000d142c00a000d030400080c240c618045 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 940879838 1250 940878588 940878607
    0x3010e060702060604020703270306060807030b06030d080402060c0f06070903061401030b010501030b040e0303040501051602070b0a030f1d03090102121303110109180504020109151e0c08 82
    0xe8040c0201c09075001d80b18103444503000e00059106c1e000014012650004407028101440809031045044004c1b6428200361a90388050640b506a0b005901c15406240b0a20902c01078005858104d00114000d200c0d090f0801e00c0945008802400603104802c00309070740d080403005101001d1404d1010060f04e0407131030446405040d4110702e010075540d481c608203529840001c4100401c0c1a80d402c50002c207a141c1c40c0c98011000b030800110f0554100c1d0721010340340c1c2052000c001031801580b1541c008200307450800ac00940021202c0304050442d44200e40411030001018111100703942c031403501052048000860002815200041c0c071241d4000c1079054083c14000300140107150000d80c29a8000d61408100342d0042c080c80881c801621403103181080014400c030703081c040d54041030400000c1c50350744100d400050410756000c20041600e9800700411580d22424840c05484821703c90f0303901c0d0514a100800e410301c01c0400010110018080821b418041c0e0b048012443d13102c550f0542d03811800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 940881088 1250 940879838 940879843
    0x12031908070e040207171308030301030804030b1f06031109030607080406051807091505090106080f0f0708063f070f05180c040905010b090312180d080903010e 70
    0x8441c5100040c03202400103000e880d2900071a121a504401100d03031001e1017001c1d913442e9070300201d2250410103441200003102142800903500860140301d0340742d2a42e1070f40c00c0c0800d009130014100e001411100590702d0040c040c20200505071a00c034500090310050040c0f90540502c42c42902550610900c0108040540d108141500c01c4c0e20401061003141c6514110301c880d03005d03449541d41c06400c00b0b0070502c000013541d4811101c04800041580300b03180d540e0082840710000f0b03004140000c0341a41009280304802801e250880c00c10007058100d0b150484000301841005003e2074410041c910341d504460026844103040b4400c0790245042030395070007540600f00c00400000d0043c0b030088460000d10944490303081000c5031409044070420307000600040054101c001c101000b07410301171001003070800180c401c41e40178000707982c01242c2d034180d58402c151803c10005034a0700f40003030402c8030310400304d1202c1a0015a5000343d4a00c1d900391418a0010010f01850400d142c05600e48080b58040342c200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 940882338 1250 940881088 940881091
    0x160f170c1c0305102d181404030e01120b04060602100510050d122f150601140a11010f0203040c06140f0c030c0706020601150801050f12031908 63
    0x450444890000c03001070a4095460840c0d0711003440d50298130400c103040001015480620012a18146842000d048881c00040e41e070003130903d4108860070710001561500c110721100c070151031100d0b103510b00b17690001c0c400341c0307182000c80c100a15110340d0121101980c02c2030042d41c000030300c1030007119187e52009658030f6501e00b007810074900b04808203c6000c080254101624000b03810700003200c080e51140c01d465545116650b0030009208030745901c82010304031300c101583c074000303140c1c0039818518581450030714862102c0005c0b01201081c40196038010000416011500c0d08031900c0c0d002502c02034900d03198024501d40341d542420780398502403000360f000b10b03c0f440c80744e1190746449480b843d0440c0d2070140e61100c8512280200401d165001b40c81026003410002d1404492602a04000050600700f0542c0030002590000c401806154015101e94581d50502d28251800b50b150800040345441c5020005004060890038110300c42e1003402124030b0b00d42030444030440c2a640481c003e086480 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 940883588 1250 940882338 940882363
    0x512030601180f0905041b0303090e070305060d060f090204020f03060a060804150906110a080709080f0723060c0c041d030a1409040c0203040e010902160f170c 70
    0x500d900c03400902828114241039410b01c1d90f00841890624070030700700412001d001640c42c090b04a01c03ca0f01c1001041d0f941c4040d600c25545c00c1d410f2441e050f042080d81070094140000d040c203110400220341c65903160440e2094111002050b502c0c1c0b000b11000091070008030180d0014000507408549402800c020750103040d09440a600965541c4000c407007903071041d1030041400d181403000707101c102400d401c03000c05c86002d0351000030500030b0301140550550100803031401299601b420440380503000050300d00100428005065903071820100a525241240520341403030b1100341207440c00501310070080d260341c3c001074081590789103400c804564408291610500c1141002d00c1c54100080081d80b04483c5c2100c8d400450509079692019101000700045004050405010f4100c41c1e40d02c500130a548080c4c15008ad50740c0d103041c800070702c1903000705810002545004009000600d0307002111004440c0e04501400c0300349829141c171140b00031142c01d4104600d100801c5011040c0e0b0049008401b444 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 940884838 1250 940883588 940883597
    0x120c1a071110110106090912030509060403030b06040918020f120718060e09070e07030c0503061e040f0b0a0b0703021f02041e08060a0603051c030e06070201091202010504170a03090512030601 84
    0x804003400c81c01e940c403c50754040bc1742c00c183c01190002e4066007004180301401000c5c0d038200707522aa060741c02c03241644505010440c40784494010744c05c100007103a0400c00161840094803036aa81c5e20ba40c0e954082c481c5012050780c2a81000b83c82d09941d0003500a42803581090b40c1a09103075100c4c075900c1c2c01074011180d9000c0c00b00c000c504440e021388201c403a00b00090304d50303906541c1e44000700183c216042d41d0052030500390740318160155450b44903003c407040101304000f503588280c41c14081070041d640c00c0070b841c03500f00300201e401007500010209085410101d61a00441140c41018080d004079801004881140302c0790760b040e4066004003c003174416207422100b1030b1361911206400c1d5500c520024105810803c45031b44140003004820500b4078150a0208040024108085c6042c0040310900c2c0140d55800882e01004100f550780c041319500d5100903c140d003482d0316a011703405030030b9580703200c045000140000a00d0003900b003524121b4101094401c010315042c540881a8011190303280041e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 940886088 1250 940884838 940884863
    0x6041110020c012c030604150c1d0607020307032f09070c0b1e040605070e060c0c0904021f02100e0307030e06070c120c1a0711101101060909 62
    0x1180700141c1c00c1101d500503034070701e4407804040003c00b07241014078010312400621110340400300d450421a80340074a1080c03140221880746000e441c1e08403407895003440100558014185001204110084030620080b038800783e0783c0701144000307031a00076198001440c0c0700100b01a00300b420707524102c0e1120752080c0d0a0001c010010402040401c080407038000c00400c01001861010891030820180e120780a4904142c03100d140356000040103100f140c04a0b4550344407010060f00943c0200d0440c210f51041c1e0708035092001405042c0e071a400c4215010b8000c10300c910000d4103540e41d421412140c6488103582182d011907541000b500e540e20006115000c034101050203044407070010450360941d80540e24142c1c7c0001d08804c11401d0707405640300f5915a11080d0001ca111400c2c0010301d400c2510400c1c44007201440c00c01e58850198051144240840b8184114008241c0c03038482c182d13000808a8080084081c140c0c005e440303206c14180d901c603096181c00004203203c0c5a540c0a6403c6d43c0c0074502c0e100c3c82 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 940887338 1250 940886088 940886119
    0x909010b09060a0b340f060b042304051203190501060915050c390114092e180807140130060302040b04050421050c060411 54
    0x1440514452404c01c6102003145050040d01d040103d6107030707811940241224135058840c5c8013030b801d0035007055990f803101d681124104002441384204803401510148100c0454010034000039120005070038030b250380d41c0001820094180310a100074926050741075280d0a050308c050800c00c00d041808020a80b80200114241e4041c0d5411402c80d41d048507080000f02e8840e2084400d900400f005010f0740c4a10614508082054001c40032056a40c103900c440014512180420700546603012a05000c2c1011101c070068205c80211000e0110541d01e1031040300d85070101501700c14a44404103070348456010340002d1a540210640701107031700d14482d40340203a1240e509903160082ca2003420795020045c60340d20382650007851400c0d07185000381e6401c80048008044000068a010a0000040d58131441402185014840c84070360441c180d6080050340307440e507a842c60802d10110340e40184402905001c1d00d26101c0c1044456054080080e9009800c5c00d2070610320300c2507440c0ca80c40c400c130049003100b4070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 940888588 1250 940887338 940887349
    0xb030105010b0f091207080102120c070201050406140904150f1a040e0c070501090c2414090a03171806070f030c0c03082d040803040e1003020909010b0906 68
    0x42c1e41c00c0051542c40c00e0304070900301d802540a1201d664200e0b644c00c120034031820701480481c00509002001595840235100c41407484c0c0001003085890500c00e200c00d07405030364460b00b91001d440c0380b0700342111a08005208400c160040f9000c6a40c001d0a00710f16181c1c0e44180b102500c115843d0720301c2e07a90306039164071448005581c0d81084809034a8140720410864450b000c4164025a00303042c854035000017500d40500752842010151107008103c10b0400002c0c803420044060500c0141c051045510880320042280101020f4620545804210b60f411759641c03420b184001d5030300c01000311154889840341b100701d400401d04203014142d1082c00558070704000040343d6441364425600c0f420401c080d64241c90f4504208400e803105105000c0200000d01020001c00d8500c40301a555a802c01425000c3d28540c1c81491401e6030500090004100000d00001924259403181100d00304640da0302d5440200801c169102a42c00006901070260a1a06501c4649000b009451813407171544d4450502c42d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 940889838 1250 940888588 940888591
    0x403020d032f0601080a020d0b0c12090304260607030e01180b04020f09160804051603030c020a060f021f0b030d05042d05060d0e0106060504170610060c0c0f06120b030105 75
    0x2508255080d1223000086d0240810b03a91143d0034001d060f007000090829410b51450403650301c0300f1a40000380c103000fa00c40300c54202001101e083e0980400080038950b6a448510140c002c2003855286e44440c00a207000790040d00900404040d00702c02c40c0c1c030f14200035103070001c280c4080e0302580c4011090201410400d072100e2040303440c2c4102d400c960010320000c03140841c0060060342c0b5030142d105840600c17100c03d41e0b1b843c001c40c081d6840801da04440c1c0104801030440742d0007442844a0001d40d00300e00c580100380c0c00c10030080304031925064805a55444082e008003e04c0741e034113010fa01d908000c440c2d0018064000d8404a20780e02c28580002c0d00740d0f68045450410ba0104580e4034842000305141000040c450901d00d50000f050b10280105110701b542ea1030340080f0003082c00460184005090048180b5400141e40020700c19410400480c01c90007045000c5c1504019103200c60b5401d00681120400003050010415014203030382d40e00040c15001074586034050a407d00a060b505071405020300b6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 940891088 1250 940889838 940889843
    0x5090a02010905130b1305180a2604050909030408070609051507110a030b011401020304030b07080915010f0306110c100e100204120605090604080403020d032f0601080a 74
    0x100d40c00c0c100020010398000e0106032407082601c5892601440c0c0310400c06c000380311441c990219960405044210035104804040706080d1702413481e0801189010b00490710001d03840e8a81c5003030302c032540c081196510450700039580200b4170505201e41c600000008108807a81d01007541e1803607071510011907880c80715104159218015214940c41140504d0080c82c04901c186180c515410f44030010609404c401d60003610707208480700c01004804222940000c07010001d201071803429043d130303942d41c51800024000108001c542d00006110b070701c0401140440d811605e00f16502036039100401400750303106000842c1e80909125000304203103003907815104d0109c00d03000070b0440030400040d184020b148000d840307490307807180403100381382c0718841d06c0240080c00080404454100c9907080107016140080c0c600d0485a1095003000301003034800040d02d050301e078112030003031005c82c09007001c5170030111036164070b0b007084022841a00500404c03040203000320050f00c103641c1c2e1603a0300e4802c140c450034151000f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 940892338 1250 940891088 940891097
    0x3051908070803070527131415060c06010e0103030e060a02031b0106051302030a05090a120305071e08070f0915031806061215020a0509040e12030a0c0305090a0201 72
    0x5000004a850b0b0146030302000c54540642444000354210142051441c180c40c0c0c0311500409031019403e00e40444086042031240c2840320300400b400c403146c4c424008200007001c070f02608184085d503992100b110041e0080200b01c6004c2d58583e50003801c550800c2c442200440d0f8094030028081c200a01611050318003600510b0910403c5c4100c1550004010f15000d0113560b150400b14041d5503803140b6007502c05d00701c0d0006899182408a0748110760000c3e0500740070394000310607000058440e014001c00e040c210716008c1125192681c054401c40010042c18070a0070000003000151588001032612458080c0d5555481184011040e109043c89004103c141c0d4182d0b05903503200c9000307801254600340c10126050b0503401300d484000442c0d009420030386c0b1080b10240424140208652100d900c1c0308007040c00c42c580500a01c01801c1c5100d8140894044c2e500c4600b80007070000b00740324141480346400f00c039941c1d92412030085c0000306a807010540200f031401c3c2c041100003500041c0c0020169040c1c4a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 940893588 1250 940892338 940892347
    0x2071e030209040317070f08060f090103080a2a12080121210305101d0403030f0b090a020d0f060305030706110c0d030f0522111311030103051908 64
    0xc0c04080b00c0c00410540a0207100480380c001c06459072992481580c05075221501c1144010740203140c410b000c0c0c02039216400300c0d80304101e41e0759480356142c11a640044a5580c1e064a5241503942510100c2c12201c05454031054405510540b081d01d04003a20408a400880b0fa074a003060350500400e000354503681c01c1b030562940c0500b00049004600e2030040c2484103002c244c0c601c00c60500300b0307402d000030000303a21001400720554148607104041c024001c000850201d4980750340d00021380080000d0300301502d4950500034425598400d2010390800b501d2000d0f6850200661001b0350b00c0306129480365860400304031850610b6100d0700e025603070301c01d0245291669540b24500600080f215400441e44200004e10900004000ca1450b0345002d850100c0e200f400420303140c040700d600400000c000210519001aa40c1003204003880721075111010829544210000c60903640450045550244c40c00210202c000d25400283d4100d82c4214129414000030045a0402245048008001031010b02 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 940894838 1250 940893588 940893593
    0x3040b180a140f0102220806040503250f05010b0f0604030b060904031e11101e110405040216060b0616080703211a01090b0d020c011d070602071e03 65
    0x240c0b03050054112000300e980c0d25800900260032a40080800700381c0021503811401d2054041c41400002c142c0304025001c14540354881d26201d00c10100703030b1000c40d0f20b020b00790200b69288484100e1030300e0300080094250700d818946140201203681d503040c4102c0b0506036403d10340c50250225001c0c0c03a07000b0070503131031601d0300b50174800340800c040c00480501c007d031840d2070410806000c808500030025035078661f00e01440d00a041c1850002e2000c800c0c0f0600340303094003d8020711000b100311b20701c6d41a0000104c1c0d2452a050303003014007a680105520500015852291081c8034112203072580c0610780c200042d0302201c040248501c55204040024002c0c0000070000c1560040a00700c4d050290509907aa050100454026102c080c039040450030b0340d600d01030308048488212600750030400c1c2040911507082903501c0c46540200845902110303000504052982400e41102203280c2280b090402d600c01c0c00c01c805611141d442c02130340e00500c9050350020789243c8800d10341c0c0c0c0320301151900c0800300b400e54 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 940896088 1250 940894838 940894853
    0x40813032f0a050112020919030b16140c10110703140703080612070e040b071d03191106070c051e010504050f032514010918020a021606020303040b180a 67
    0x4441005c0c40e0f400e10621400340c464400d1201090400c91003416003a0641c80c0035050442d0207081d50034528600b00715440c0c06030700407000c5060103024a200790f840780d241000b4035250100e0800480d001c2030070200815840c00c40c032400f400c40e062294a03000e841c2ca20081e215462030113120800303400079a0041c040f41003810144064600201802c0c10b0b10710030741e102c5030035010000c810b075002c482201d03c100c02c00000d1175012228000d80a007128038910045038030f030000b03030f132b10321154031111840b43d50b400c414010040720812404600358050a080c1d02c030403181c10030002d1841c80d403240c0c078015218402d00744405860500e0344c00c21080c058560701d08003810401030103007101c1741184d46c0c2d800d48074180b001c003d03100340511240140441003216491340341c00d20107003503404940600c0c101e06104104100340907210200504034001c01c0c41400058841c041060101d2800c840c840c10099440704e1541c010500310341c0072000b54451809841c0500207611040410000201035405011464101c3c684405c001040e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 940897338 1250 940896088 940896107
    0xb280504110d0216060212010603060b070c051309061103060117010e041725060c0e010c0b2806032f040c14040f0911090d0308040813032f0a0501 64
    0x146801a113003c00507035281012a8048021048058503010042000a40c540030b02406800c0140c804c9003020b40030355818012070001d028541c0b04141c0207580c0c0321580c941d684011742d2190891420700001c000f0100c00300151740b06031b89850003d11100d1649d940e000d06108958100c480b40d080398800760313445459440084400e402d11a4280c80e04119101406066951001c1d55001643c6c000901d0080c1c0c1c9004003c4a240c41210400d004d080100b20320340c1ea0700140b0208800e074100e203c001e200da544104903084032444242e1001c14401002a43c0f41c0143c0950003c41501d00c501040a00c002c03101d0300083c004a42d014050807032016020900c5243d040c281c0015402d0710303140c104600b0f211714a21188540b030b045070f0401c2c401c498143c3d02c108a011024007905881e040c1880500b803500c401140440c0d40b10380080c1c07001e400d00c040307900880c0800c0400707010cd44c00c036440c094440c51402c1d26440c06424048514201c4050100481d080341044501e00000d05800040145202007a601e04001075510521 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 940898588 1250 940897338 940897357
    0xf06042112020a030f0f061a07020303070c0b0c060a0501050d1401060f080d0206060607030e061804090b04141f0c110d0e13022b0b280504110d02 64
    0xe210709441660803180c0042c12040d44280c0b40824420318544e0400101d4044201514010341810005c1003049000c0c078940e041d84d500032409603039814103400440d01e1440fa0810091500c41d80307000015101e4800c4016004901110003a17424030385442010704203036002801443e80c03041c050792030000001c01581107070901c2041c0310001b042055450204c000b2040b0b850b40003043e1030f00040e0308038800039814008540e1107401218034504041440c1c40003000d03031514020b0036000d80300c002002800c0c41640c0d503022600400061090002c04510300d80781c080391205440403580414100038411020320046030304105210050100c84a210110070704c3c40141c0000d050035810b002c00c10b803800b50b040005210082284a86407a0024081b80086c1070040105807108280c001a2051040d1130b55040d02043c03a15103400c090f00d20311030401c07000312403000610001c02a290b1089041b0000d00300c0071a00104102120b06c00d035044d03001c0964030350500040c1e0b20074400c038444030541003103015000f15640e03010302945103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 940899838 1250 940898588 940898597
    0x806030f010c0503060102010606090e010302060702030f06010306200712180b190207060c0c0e270a0b06010c03090e0907120602120105010306050f13020c1506030f060421 75
    0x80480c0d14242101d01142002c800540e000040003410b5809019000c000e0400386030418185107001d812151140301070000a1048600083d4a000d55408002040102030b900080c3c2d80156544d20f0240c0c001c0c402c2c211102d01540c1089090800c41c0c07251820358000a4000510103a686060041141e00c141c40000c0c1c0c072080b140241002c52074500b0074016042d00d0026030300800724448141000b900d0b04c29135910000402c0420661000001c02980704901100d60590f54206141c07107140d15009054400c03418090b8800c01e00c65044900c010024000074400d0041c540480d030b07a103804004440c000b19102000d00414500c1d04c04022030704102110304c5d48549000141c07096140c44500100f098215a08140d42d500e4001c42c4224038054a0800c032401040c0909080004925090119000c4100c407880c0501c42c48070900090f4541d001e9404440c20035802c0d0040e1408080802d209451010003924030f9406403044110070304805100040d4075001e960010b43c404040f00d02c0100e03040103070729640c034180e0401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 940901088 1250 940899838 940899853
    0x606102c100e33070b060f0a21050319050d150f1a0c030705030a031505220b0307080a1a100b0d0b060a0c1a0f0a0207020109120804050109080c10080603 67
    0x3d000701000741c8503c80c801d15003400a0304020042012030881103c2e480e02c00c10300c101c030400151000700c03107000410002e20024825801182043c82c00c40c0280e45401c2c0507450059040b940d010f03031042c02080c801824a404000c14001282480c01011040c05504840702581d10107000d8021907920318443d00d00105180c91503c0001e083d45400c0d03030040e440c1100c1c1c0398004164042800d40601413034810b045154181d1035054074000008030ba40c05c0c000e0744134448070290f000c0b030051440142c00084c40030002808507002c0a5079810070b550765403480780c015201001c400c01c00c40d401080d25002c0d5800b60407208112510a41058010200c40d404014182c2255549a070041c1150703c0e218003400d006001c2303849202081c2c0c840e003000c0711071b1100c45140d18072111001c0c0800118092210303d0782d8000450300c00041e29209a40300580c3c0d0f8000c55081250060300303244503001007101440c000c1083e03176820b90f00c540b107559a98808076540c01e02d2882d440ea00c09070720007800e40135500c01c400d16940084d00074125100d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 940902338 1250 940901088 940901179
    0x1061a1b030d0e0607030b0607030f0e090f01081005010b0711060d05010308130e0402030d0815060304230304120f030e10020705100e01020606102c100e 67
    0x3542e000640e410a01d039120003041541020038400c0039804402802c05204a0750f60074000368081c032a80100401b409045800220070038411100c6003140503002c1c1401016050090b0b54047e01c000920981000e0f103d40500d8806007a01d50250a04807542c02d0b07121410a8116610342694060003514282c202d0b00a0041016215990103250b000714024180140e5030000c04500c4d0140c00d0041e004081e003801c85206000040c1c900281038060302c2e41502c2c0c0882d0307640321100c0d54110030580800d41540f0103400b20912052005050a00403d1008100300899020070030301d000e6180c1c0298807401c50340c009440854000700d207100050701e002a2182c9005610341040d000000c0d413505491264200690105209010505080d51445901c08036420040c032101d9504000030342c0d40d0b1000f445980a21042080c0100c0e050050050b1040c500c4c1c18003414090800000701341d29503e0803148040c1c41002800e4070b0201143c010a03110740350000c00380c1040301e010514069055010a020404031b001040c1c03425100d107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 940903588 1250 940902338 940902343
    0xb0c010b1e030601050f0105160602041503020c010c0806101101020d0606020d0e040b1c0501110a02061009060f061803050f0a060b0301050105010c1b1208091201061a1b 74
    0x20404041c045110441550a0524100c0140c0145000d00d41e801c6405240d81e0300141920074160410070b806aa580c1140381444c040d000b11362100300f00810704011592007913050703005480142a22070080100c84450103040f01c0e40c1c1415600305410483d00180a00c0883c4074405040c4002e089000140c900741c003a00c0319604071104c0e540400010f82008e15000301185d80034241c03840e4103800b1a000c9c40401485000902c012010140d0782100c0c0f042c1507000c608010082d008859a281850401500c400034bd04002c1d41b510000c880094901585a001203070000c6188290000d43c1c41e40a032481c0340700d003004400e80c1c40886864080c0c2d18008000310000002d20200045003820401c54003610f001c070102e144c00c10585009922030b40c800c1c1d042600600040e40c0c0800e04c05250703a04074508451110100640c007415401030340210024480390302c907107805d00ca80180107209440c07043e104142070113a42c07840f8a080740c3c1240100d0401d080141c000700c03d01d00b8540064544c4d070703400b03481706507903035003c0202d652 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 940904838 1250 940903588 940903609
    0x31003020d0c060e040e0d26040809090f0705070212100606031b02030c06040611070605070504150503060a060f03110c010f0c09060206010e0a02070203240601030b09010b0c010b 78
    0x507034200d202d060900c181640041140340242c420303502404022040c4034080d44582425143c5420400d070004807080e0409030041e05417901d0071401c598001418942010b280d56030110040340c0c0111b90181c042910110102d070014419030382641e0f03036400c148403a803c0000988074030b0019415482442c07610038089800b441001c0080000340c4000603443c400d41d40451b089445072110209642052012184051000c80c2031607000e50320807400102582c0c1a84918218010500d000d042c081c0390208001102d50444001d0007900c402c1c0190850707011401004840d10320080b0340e86500405505410020640500c0c07041c0380c050954100880d10194800043c81c45421000404803d0780d19458000700101d920301c1591540d14542c80c02603217450601b0800380d81c490043c0300701100303140160300041d208981581914a12680181525224140d41c0e0710142604d079030500e08542d0f81100c0000c5541580a4803034401c8400f009090403116038a000ca50a01a80000c101c4010a5491300010320040d51480f0210 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 940906088 1250 940904838 940904843
    0x703020f4e0c0405090a020303040e060a03120503010f051203070b09010f020c071406130605160204020703050901030f062d0806040318290d0e01020d0b0f03011a06031003020d 77
    0x180074080c0d0b03082c100029510050580403050f0802e000384c00150728040120340a07500c0b04521143c10340c172030f880841e0002c00198401380c41103002203007070340c0029408070040d81280c01a2041141280d202d0081001c0e01e4540d50048141c3e5008100d0f00c00000c1d075200b01c01d035000344004c000003401e018600a0304140e134001aa9202c454101803014420b10300d2032844be9640d864203641ea01d080c0f00c0d10748100e004e42490782c011042802804a04038002d1880b01e65184255640034000395241c61251038080c2440d08001c840e00d021908110100c41070310801d1082e034084560407110f082d400c5003c1c100da59001145407171803000d030518032000850908400c001d244c0c0958480d9580c8007250990051003c000c40c8503400001440c0481c00b49042003c0009040503405010301c0e44260b515550320302d540000306001c06d0b8aaa0550000c102d2407005196907000c0300e5a1207094078151400f1022008050032146146060380c288184d070000d0700002d06049020f140d118460405040442e5140e80000c0c1c000309202d0002c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 940907338 1250 940906088 940906093
    0x4020307180f060b0a200a06060f0e0601020d2f070b030106020f0703020901170f37080304080f13121a161416050703020f4e 55
    0xb840d500d4035961041100078400141000d051441444005205150000c1028840707603140700004a904424040501401e80c801410031800342e44508404108215100d138031800c2c800440010800c3d4004503144046900c140e0b50750754064181c070500f0030700319050748456031b440c0c100c800300700c1d01100b007084500c010740340e40001380740c4940c5800d01c020700c1c12517104884102600400d00070001a154035031040d041d1054250604d80304c500c5215130600c1d0050f904400f400c14131856004504007044102c4010f080c00308801410014a034520b030342d140252041030010004082000020046841c004c09002039000c44e409051405500c4040503000ba041604410f0040711056058030421070b00300e0908040000210000070b851825146042000b990f8044440030b02280a19a5a03010044011203681505071048440c1200407810a5562188940800c900030280010ba078240b0707140c0300405504a600c1400850001c44100441c00c010013014203005032100c41801300c2d08810010050000c5030071501000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 940908588 1250 940907338 940907351
    0xb1806130911070b0a0207080c010227031f0c03020906130e01090501060c030e030313241719020d0507030b100e0f041512050d02150712050402030718 66
    0x40a800b02d49148510b0302840c1c90400502002038648105140e00c441450340040e114095810400c0030340c1b18001410481e94400a548403180035298007600e040745000702e500507030741250824103075103035040003c495401281204284c4c5032696500305107018840e6140250138403846001044450304002299480c0c0c1103240824055002115a150300401030a00c051050b545010409440142c16080140811022480074030480e01c0c2001120f5480e40240d464141e45569540604449034200c80d100e81c003048407684018003148030384a40100302d110303071800c0c25042d107660038804024040d05407a2550580c0038070881111741070b94404d03148162311544001c038001d14040d0420640e615091031100500501003103540c20781c0c0381c40d22000d2480e00c05507400a914503500d0b40b11002c4044551141d1a52205416a03034201704000c10581d03100e100e80c0d000c4407034181d1120303660700400c8000c440c40d50004145980d0310b8150301c00754000c5900300e07001078256169903803601114000c0c280482c02d03c031901c50301c594 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 940909838 1250 940908588 940908599
    0x1d060c06042315010902070c18060317090a1814070504150807082d07020c18010e06100509120c031005041a09280308060315010b180613 60
    0x71507001d0340c100074141000850343c01d18842c81040c01004240c55000c100002041410b20002014120358417240c41003010254a9102602a0340000c44a0400401c140707500845140140c0d50852801000c0f1501c40d0f0500c01c03887e0089100f11a9186215102c0300d0340e0040c08419040c860045001c1c0e90f0342c07955681052000740321507504542400030000c0b00380402900c6036101c50317516003005021060107c580140f60091070041c90100c10360050083d80f100348400190005a40a020401a80c00d019600c2d90511400d102c40c00900c074100b0380e00c40c0c40740064220700e00402a90034458260901c103003421070000c007280340c1d075600820b0f92503d40e01504030340109207810000703c46580c0c15488280400e1400d030341e600c110f51400300380b4810341042c01d00c0890130841c001d00155007540d80c1c8600c0c80800146103d640200b0030704400c002e802045a920114030981000f003659a040c1750310503400c06460340fa148603800c403a0720111a01e4040458002d0080403030380d0b0500201141d90402d441980341e00d00b400b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 940911088 1250 940909838 940909883
    0x901150f17070c021f020d050c01060f0e0f310f06150302091b0d02090109150324060c0b0411060a0c1703060d12050405130903020c01020d1d060c0604 66
    0x4094602c0328203980205401703056002580c18011032103860000d449103031074083e087c094050350300600807841d2643d102040d0f0704d960035190b52041300d0240c0400650b449101c10040750150101c18078042c40800216134026440c1c030176001c20f8652240c201c4945601c02e40c1c0700c0c442110001d05c0310308001c0c160700004000358a4285202500001100182100c0340a1169401128860540c02480d1a50003045502c0703507a00030503001000340180c030022401d51a45050060007070090b480d41c2464003050440036507140014641c0403040d01c01c40c0d1500f005200440d00c0f013151403000240100e4021038454a941040e07150500940915800c544030b5803043d03c031528103034148241a5803401c580c01018410015103654070840c5e1580103401c14034814011803a4a422600b6100d9508416009007228100860350403941d0711202c0414040ea0035240c4d15407075100120385a400a900c10703000520301003403a440e9812086410180404020b15052038168804441801c04408590a440d02c1e403080b20340308100e4000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 940912338 1250 940911088 940911109
    0x902040e09060930040b030708180a08040b031008010e0a020a38090913060b010903021f090302040509030301030b0702060c0d050919060f0b0901150f17070c02 70
    0x1d002a05107500030704c0c581018032034820020300b42041003075040f203002d40310300c0102c0d03000c2c1003e141d01d290b492805e144084c0c558a81507031203400a00c100140d81d2078900c0081044880c60342d100c41d00700c1c58145402c03a43c10888c0c2000c0c0044448180402c800211000c2c00d200d45403c1c0c1032490081c2c00f042c460b0b80100040506140e11000d03000c50a55851070440b82250041088d031725980707420301c0c10365006480a8006003e07424046802c5010310042c00210100c1c09980340348588600c00c103001e54009031004480c0101030740b20082d0420120800900d0003503441c100d030241d00d0b005140c1030702c0b0b141c0c1e07030b80014080c0e4501740c411030a80d800000046c0180b0185141c1c6a90050490004181d1800d001d101c0c9000b510813611b140d03000b9607680020400c900c505101250b04200301c1000e84039190800d0800d20020004101c15028079480d1290b49529424001a0103041b5900c0c5c00340c842010b0081d0600b5141030600284660410055800203403002c17070f1003000c540c00713005141d1315036041041764810700061019 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 940913588 1250 940912338 940912351
    0xe01060905060f07080a111228090b0d0f1806230a1812110606011d0909030723150f07210e0c0415030c0308130902040e0906 55
    0x7010403c0391480140541200c01083e440381119569048100d81210031144138400a030b5203010b0281c0345203411a450703018010702c00c1c040c00021600c0e0b030742c2e660b80030700d0100250710140403030301e801c20401c8088031202c0646400e1034201804201008018081030464580f84000c0b92611098241d20080c05428400c8911840c0c401204155005030300442401a0000401e01100103440740c40f21b40000c2684d000c0e411806a0002c4500700c003a0b40c1485c0a032461080500c0100d2511880b00014a40e44c81028081d068695030b0070101942d42c900014884081390081031060203210800107a0000303110010580d144074501c90a1341407417480035410324101650b040f20400000e0075034091120108210030305582184042c2412202c60b0350030304060000810018100a58a103484000700c200c00c030115040082250407031f0100040c1042d40010b03004a00e50b80000742c80c42202d268280001550781000300000d219210040c020310340d803081b4000680c3c1c0240c200c507642540c21801d0001101c000c1105540110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 940914838 1250 940913588 940913599
    0x109060c0905090417070c06020d230f0309070f1203020d05030c0301050f04110d241d0c040506070609031709060a0207030e030a030305100e270f01060e01060905 71
    0x614100c005100c41c83c0181c405450b031145010554001c44100046840c42c4d540540541301c801d5980301701130b4481c0c01600c107100204046002e41c1c101c0ca11101c40c2c5000c407501900f40079003455444d0303401c5140d9400003887d450051003440404181000c05c260450001e100d54110b00c800c0341002d103002070400f441600740c40c040c00014014812003207041782c183c80c15604203482da9440c1e0013200c00081c0141c0040100d6030506000000d180000b071541c0e40155404190699805000348a84070207000001b80d98820301616020104003a00039004440c1e42d940c1098110f216107041c10b0f12880000e409501000c001c44860b561007969104058000150400c600c1000c42d0302240b40c54002e04507500c036440109400c85040c0e0000740b0404260003101d0651103100054122400c40c3e00502c1c0c003400601d07050303d055a103ca10004009020006a100e85110b8409115071102001c480c043c41c00103222510154001070245103a10400144244a024010403208986c000e655150117800360a0b41031a400807030061 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 940916088 1250 940914838 940914857
    0x607020d020d0e06090d0f061d0c091f03050607050310121a19050f15030303091b0f0402070615090216020f0f030f0d120509060402240c0109060c 64
    0x42c0d0420380040c81c0500c244c4d1a6039031051031000185c51400300480003400f138640c1882d10018070681e43d1003000e1307402250856401408841da48240d07a8010141807075404410080000c000140320400400a038007540c00d41868280c40c1d95942d0b0030701d00121424400207a002c002c02003001a03200e0603100500300d00c030103041148025101c0e440c0c80209e40100e040c0e045441350218200854503030f0740e1000007030100020005818050083c3e46600c03016980c241400c072001409140c1c40c5800300c103c0740124190f030014001e411440c1034062095040702511903004081303400381d0f00207803500d0000f010103c0c030680c000181001981c2e49040340f007000d9045016001e00c14009140e802100041801300e040e0100c640010000410380010101c0324511702ea2509401100401c41000d580081c80603504240340e00c80100c00d50724800d105080790001c44220380e26a110b003020a025041102d06d100c240038040c98100d0700a0800c0b44c1402a542c048648108a69540d0040c041402868400c0d00490180c914110101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 940917338 1250 940916088 940916113
    0x705031f2309010b0102010609140601030903230702120d080112020f0d0b0a0c1b110f0d03090807060c0c030b071404060c0219061e0306080d09030b15030322050405090607020d02 78
    0x7080c009112f54141a9100514802d040c002c454501e641070810300008001d0a11074001040ca07000708104030b00954444c002c000201c6000304181c4d100032019503034841c1341e138603103503281c10701e2810b01c002a80c00041d032150091164850346e0a50700b540380680316200140c100044440c00301d8101400070b00c200310000780b44100381c0046000236001030303401001101040b4002e0380000c1c11003441c24400ca82c8200c60380a00000c060f003194424089403100b07401e60341d00e1581d035601a901d081d4000401441d06480020600000d01d2900009812245a00e004104000081001000ca174440c7d0401d04c045020a2401d408614041400301d08004641c40c0f0341d00302c14a0050013409000468101400031342c0002290312140740b0a600c110b0042282c002143c00c8480c1c200d02c0034140130b03903500041e00c4c942c2421001a680c0034100381008180640036009600e0510030300d0312070540340d16030441008405806500002c01e986d80340140e5002d00c0d60f00024110038188224040c0c85c000d2035a140c0410754109a200815 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 940918588 1250 940917338 940917371
    0x40503060c0403140a0206090f0a0b030a06030b18070b0a031401030c140402280219030f030f0e06040323042607060f0807050f0a0309050705031f2309010b0102010609 73
    0x54650270380c0c4500341401300034009100403100381c10100301000e0200400841039800e8010000702c900809040742d958941190812010740800010400c981c0290410402851200c0082c005520a4940052030021114070640604020391041c0c900c804000800e01c1084520080000c1c0c0349002c903411131510541410400c4c403441d52581340da0b096400822600ca41c14001d10080144142402c803000802640d03281c0682a03280e411070380e000007031138400c408410004500c150303285090300a008040c160b945580c00c80d1000380b40c480e680e1601c2c519034400300f0303845c005101500150070840c5050001110441d00750b046032010316200b0b0078540c04980c1c04c02905400005102082003e40f500d041280e4078080c1c203650034402c0e042503590b81440010304128007607141d03100c2420b50344244140c40d9920350718010190b945c0c82d8003001ca40094005c41204480d010076a00151007940f120a952208811003040e140b100c0e9021a00480a651a40c0c00c0c0021581e083c1326640203444010402c1040c441552400d03034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 940919838 1250 940918588 940918597
    0x501091e050903090d060e0d05071a0a06051c1b270b1e0a150f030e0c040608060f09030301030b061c0506011202041104081908040503060c0403140a0206 67
    0x2100306645101040c0b0020007441210400070000d4140c2d02203150624080c03005119682030408035004411014032050300c00c0e812650080d400a10003d00c1003040c40c144c40010702d01401050b00c6554400c40040c040d01c94501c4040e45201c010f40c80303001d000c140e0400c030f00c0100040b036241c3e02142003e0000e03c08151490710181c0a1180340d0000340d994100807481c075000707080b0b01481507400324503150301508040c00203821442c0003005803078101d0419614003541c801c0e103201c107054102280e40d9041c1c01c2a000c2c884d43c02a818104d9a208a408800d0840003180845409400c0000c05400100800403907011040031503800c201c030000210304d9503166469240955001a0140e072251070482c0416000645542e400241d8a400c5410b403001545c4d210105240a80c0d4108202e0046003040d07030038508060345800f61000c072021000030f00007011001c0303504021060802021101c2000510010880381c0b41004218418025240e0301d5507078a0442c104a00c454009400001a95020504040068a4030020b46 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 940921088 1250 940919838 940919891
    0x16050a081203070309150e1c09150c1703010e16020d0302160c0b0307030e06010326120f04023610120501020702011107031101050f090616020301050109 67
    0x507102d0f00c0d418411806880c81d120003801e000003001001c0d0741e00d002640500600380c0c1300d2044031417906850040e102980d240b080110040350140b00100a0030a0b03031807407019508070601d485e26200b215551060702c01e000244d41c207007417048080014801d440720034604541022502d40d064110041d15080255a000110240010507030003041c0a203100045c100e5100000303a2000c1040b000d50b840d040c640000380c20031603410f400241005040c120300b850219085068035040107080000901030040b880342d00d46010024440c1b080300700501d00030422011502400b42d1000c1c880002c0b0740c100f40c0100300c240e481c5124020944100c0e00910360900400d405075a1059610072641495652007031404600015035038822890381070900850030400106500a10b0072901c02d03241c0e0303404e1041c0d8440c40c2e50344100c507001c024800258448101d030250b001d040035106a400403400c081c5001d003c0b00c00304905400500c400020907140e07008400452400380101405092208002c000c080204010070000f0340034403250 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 940922338 1250 940921088 940921123
    0x207140601033201020a17010515090f0609030a061e0218240a170c0319050901090c12050d0e01020c0d020a05042406031b03050702011401060216050a08 67
    0x7412001504518607107490076050f4021526940d003000c1c043c0203c001c0b1840c225010301408004601131038007001d00c0c0301454000305040d003010204000d1000402c2c2444000b50321040a2125183c11382d0104a5515118400c50001c600c000403d0010004251f64400910500d801440007441c2d402a01c403951b48980f0f01110240001c078400744110b08459415442202658400034048240a030058500640f2583c0c41c010302106942d000a441c1c00d074002540c2d12a4103100b18800c1091100f03080c0c01c0b03a50071820a03000007555485a070344040c40f140840d070081201241181846007407000511038091107110a0401d0300003101d955000030b49581c1d61151842c8100c212401d44820341d200c9503545005400b000c1e00400c0075020110403c01c0d245801040d210b0711512104000c50b2040c420f003c0d41c1e074100d920f805a60650540c0500c1600a00710044c00d203001c5669a44e07060354a0349004078418000d00141e0040c0c00c40300d104605101080300c95030040b80c09a2030342881008070345400110b0340020201c2061 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 940923588 1250 940922338 940922393
    0x60d0209040311070f08061807060c06020903010204030312150311010c230a020a0605040807030f110d0615061d0d03090e0702031222080307020a15020714060103 71
    0x201551240715081c3c40b64071511a0790400710301c001c81009284181c905a5080f14210380e03c0220380301c020b41509004000079000404204009801240c41c03001c1180306600242c117044c072030b03000300303089801a038815400100002180c48149000c0d101d4041c4c14941c680d0300100c1c06045449608407d0401c1341c100f4100210007070710308103100c00d12801c1c2c1528001e801c9440411460000115624001c0c0d15099102d8821041c001401038001c00441d030890b1981d0340544051851602c1b80d40c42c0c20782c005006d503444d82400c03c0d40003280c0c1d1640b0a1034000c034425100007400c09031a036112107a4140d5900003030309218820320040688401c100e640006000700f150785440844051a040303405010035401542a070740b0680a0000d10780c0c0100c007800400c0740490b0b00c824966903011844082c0300d09070b01640041c0091032406000f2900c410000c42e0301584500454031841c000341e95204c40c00d0308100042c0031880d404a0700c01c0400110b03076090048420761a000f015554155200c03010212000c050100d2552800b00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 940924838 1250 940923588 940923593
    0x60c1205090a03120f0603060506010f05030106142b06030b060f0d0f1b08150a0c0507020d0c0510050418020f0f0c0106030803190501050105040b0406050c1005130317060d020904 78
    0x400600b9a0150745c1c100780906907491038203401404040e962140070a100d9107040240c680f04000f901e04a9409942d0b240c0481102a80c0c0c4100c0da02003104001542c10924000f040804800540c03440ca00080e500041c6180c0f41d03050074000818080c04191188550110403015981c4980d00ca01045410200034112240d40d49040405500c445d00183c440e07000e080c0b00080c3c050004100181210003591221000342d480d13001280807941c44454000105409000440240c03e044081030300c060320030308420341c42644400004c2d045000180d0b5620021740b00040610242c0110140402c1404e120341007541040c48e00621000c0c2c501a00268202030f92021505201850003500600d0065801240159132070400b0f401c02400e9450700403181149134280400080d20794030800440e03080705d4810003060305060820f0f2085485512251408441d8880c0110540c04003440d441983e00643c981c42410101c02100d140240607443c100d490460031000306410001540c451804c28024140c0c100d804422503a143d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 940926088 1250 940924838 940924841
    0x1020f0a1d030601032a0e1602010e010e01020c07080a020303091c0209040609031d0a0501110708030309010605090709060c0f141e070b091302160f060c1205090a0312 73
    0x1c20303540c1e85441030702c0001090001e00d0381e0351a60030294000d07192400000c1d00c42c4180307540c1c09202d441c007007814120014501101d590644c111410b131610010448244020a4500307540881c0c00c11030480c0d50006d041040140100940d4004040103c05800e050b1155000252280900d20704280140348000303881c46018842c2c0e90001c0901c1c4d0090070103070107003024202007000f000345044c01c0303000c6882e41c0710440d071800701d0352001216140010204c034030303107824000115901840041500e055110f901702c04a4401c40a00240d44505220000025582d2500c410044420300191110080c8022543e0078400f680d440610440596005503203800350041501c1c0c52000461541c070348905e6800317516400c1290340381000f201d821955044041b84c1999454424050051051280c01c562041e2711046100d90030038180c0140c4001120345038a080745456a0300c880d1450001503001302d503031755550f00a0f0b285182c1c010550004031034081074100464900061482c0d0742d01c074185c0e4058280b1102200302403409049 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 940927338 1250 940926088 940926137
    0x30703170c100528051303140d061e0608070822080d0e06010603060509040b04030c0203030a020a0606090603050a0605060609062701032f040527070201020f0a 70
    0x420b002000a480e2102a01d1681c0040151610a00c01042546840c002e8980207440c0a04000c01c4109017910389035406440d042c1000e010340d05d070083c0c240400b003501502885603c0c0201107501c0d1610312545802c005080b6400c291300850241f102d00400c0c44856580403c2c1c10360b0002e84505419440410102074403101040a40020080c140016070501110b01ca900107404141500c4116055640c075168203405507042030060f80d401820b2040050b000c5041c01c07200783c1d0041d019045c04010b925403500841d041d41d01c110a0035000d680300d01100c504000e42c91080000801003440200701441c1159682902c661003014041c10300780d02e40000c5041582e9010444880b210000c002c00c0e5a60140805020304840320312455291500d0040008040d5003c0e028560300000c500b03080f05480c0340d4a920710504a00000140b843c4450306110210f041e8982045000c045d100d8402402c2c0e14904513800407c4c20030b0010a20380842e401031040c0c40a80e40c007501528034a01560614442407150080d000700d01410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 940928588 1250 940927338 940927363
    0x120609070f1b081c0e100203060f0609040e0a2d0b04060f1512020109080c0108010e0a0608241e0c09010203090310050f0f040b0705090d020d03020d0e030703170c 71
    0x3d043c0724050068041d0b8401191181c070740d17064400001030003140d2003c03400704540b400e8010f807843c1500a41850600000d220445004100092a20103261070925120341c00d00d00301c0f51004c03186226002e00494a041c4c060b034098031b19514032200051f50b00c040e45801e02420040060b0344502003042595203d4000844c461001e0303190074152980c6040e5041b01041a00c026270214000802c04203c1c0800842d07003000480040e183c0e0b9100d40d03c1c02c4c0034020091401400d0700351413036840c480411100402d000302892111020105921240004000c6654a8021307054000b4602030b604070340d10035101c0e240704075840800e119465032a41e6590005034118800e004c802541405100080c4890001c503a01007030041e50000325802c034965504002e01040b41c001d48003d03066400c680000307440320303100d2001007040d40c201400c00b90b218441d5a0111740c9100c440c0000302c0260700302a0310882075580c000044017140f07904400502103103286446044401402207000c1503d01d80001d250b1116140c20800000c00e90b6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 940929838 1250 940928588 940928617
    0x3090b0705010f051614030c070f05070902040902040512011b031a13090b06100210111218210409050c070503070305120106030c17100b120609070f1b08 67
    0x74181e107170b40e036405404090000114803007240716140c1e008104150f91240841c0050240f502c16031781ca80c004920407500382115184100d80c4c000c143c00c91140080e05c020540c2040158a6504000070040310032007030340841507a03a140248442c1800c0c09551604041d5003030382000103000450000d8426107850140e44540c10140c100304011112000d0343c0803a801ca40030f583c120005458480400c07000040c1da040b5000161304c42c0b00c99000c81c0030b0343d40c00740311702ca114064018602001500b014001e12000c481c03444d0301d0303001c2c0f10102e03260107410b01554070788110891003196031226201186800e801203001c2c004509a071100090305540340641190940d80c1c100c81240c0d243e10140c600107082d0780c01211244200e03c50744000040140c003d019450307160803a070700c03082d016203c503164040c488100284410b0310400c1d001e8000a0b420700800040100140c410420101071a024080c42600b0802a10560030050712034801c01080d54007030103201480c0c240e01e40188140350f490070301c140d06c0c1c003409210381c80c1c41c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 940931088 1250 940929838 940929841
    0x907120b040c170a1e020a031b1805031917041d1e01061d0409120203040918050303010b0c0f0613123f020a0801030215040303090b0705010f05 63
    0x125000300f5070b45400d0048242040081da03400c0301c41000e0340d41500d0030350707040724212881134056452a00600780b42251441c001800d00d5611401340040c80d0b00c407182c1c0c004a1007006164180200c48040500a01000c1d0b004040c203803003a014400f1082035000b009000000c405400c1440880103208640c000c01000031b41032004120070039000c0111005039105403800c01c1c401c20901042c1240000c41d4100c0d4403503140d92280d0048000001100c18001c1721055029941c1c42d400800a000900100c1015069500a5407030310f0509032040d04440008040a010a030881a110000f440000480341560010b45506883e5510110754902d844001c00000955015038420441c12103441c40b0309a0301c40c0e0042401301d48404009006a62070359400032548228a170501e18004405c502845040300440c0512041d030914900c2c1440000301d03046482d0040000c7d406500410540c508030103513050101030002c16a24052031a42c0c00341c042e48035482404102035012501d801403000a501c14603080030b4844003400325 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 940932338 1250 940931088 940931111
    0x31a09010e09100504050c010f1b060e010c030203090c010c02151210170706110f0717060108030a0503060108060d0203010e0c1306080604020913050708010b01120b0907120b04 77
    0x141c0112800c031000d200b000c044404440d6a0f0107141d01450f0003201502408502c10011107910b0058401242400612542080102035a00c0541061070090f01d0005003c030070740c4600b80c2503e000310b0b80a0f0406005000744000541c3c0801c8002d54650242050300758107a051000c41c013884640d00c00c141d801e450103d103282e050441d0344480c500c221050800d110205858080d00054410146841d05090f40202d10600c04540601c40345a1150072810440790301d81584560341d840c1a4098102505803070940da0789400300c0000700501405030031000041c600340088010000d09030f0100601940c100002c01c40459290f88480340001c0445401030001e2000c1c80c42144a1561082180e001c0780c0103030080760700c00401e4107003846582e0036141001c010f804192615020402d198201400c81c81c1803a11b8500709400103481001000c000340032806c00070400d6482d001c000343c5151030034031074441c000382040d030b004504c0e03624011001ea11580c030382019182c10700c10310610401000d00c040700319003091400541809 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 940933588 1250 940932338 940932359
    0x8030703030c030c080f04031b0c0e06091e0601090314031206010e0a0b0f0d0e070f050109240c080d02040f08010e060f090a0f0c230a06031a0901 64
    0x60050094400b80160b81c200708080b0111603a0b0703004840025020b00110b2088200704407a65080740c080d242c01042198042c42c0d00c060000400000c81e44201c0601b4104107010408039100d512142c1244d00d024180343c0014560f1040c10641c00d41e0145060400020740140c1c080d000017409142c0005103529401e6643e0038150343c81d40200030902d0301c0040c100c00986d244d07229400a0948120191603214654980301007400c0d40d4116000e8011440d4040c42811428170491081e140180c0e07244004240540c5825005410744a40b0341249040216507603062000c10701002e142c0c2184503901a4440c00f01d00354210840c1c10101d01503000300b40101c0020b0850203018960050401c0e80c0707c1d4803103031b89020b54503000c0508032002c40c090840240c229030002040010f11203506580290b84e8000c3e15400075065a45204040300c0d10003c03107100c98100030610a51602c1c58015080c0c0140f04c00480c4003698000010b100f030110361080108054541c1940702c0c03c0b00e0410301e582d0b40300101420125180d40c40e100204c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 940934838 1250 940933588 940933597
    0x30609032a0a0c171c05090310021222200619050406121505011b0804032004090c05130914010b2e120b130507030e2b0e030303010803 59
    0x1942d14034083e6800a04c08504903503800416813401c003440e244682c043d0754580200d90219414040d03241510841c0d281e90005024a01d4010544210341c0303865520084c60b485070051031021000002e100d0800211001315001480e01e42c45421074142d5600345c00070b00c05108040e080714280d492096039030310058005001c4d00940340180c0340c03c4489042034101a04540711141c10060381c4003804030400241d401494015040c031001d20103001c031500240c40340130b0181e1081d401118000d4007030406c090b8000c05554170301c0c42443e00329014000140e8903144c0d051003a405004280c420a0b100001a110b0b040c0c4d94401740c901e0340e101d2441070181030602400d60081281600300360280f610400c621461800701c2d5803800311602002c2000700307400b03100c12085844260f96489648501da03600d610b2046d9030307114404214041e4800700003040038030300b805000702a10040e0141c1141c60388003032103010110207401440c4906109854000c03096840540341203e0414400c9e02c15609800000008070301d0078800f10080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 940936088 1250 940934838 940934849
    0x903071a030c1b030705010912170f100f03050f0106050d020315071107031a06031212040602040f0915051905040b0f0909330402040b0102250e06030609032a0a0c 71
    0x2241c1140b0006580100e00c908ad00c0d600641c2c0c81c4001925040c4442c04550010000d48007041010744882c04420003a03a05d4100f50b40c90750122461115200b003d0080c0d1010304025035514800d00d0556002c2a92100c2c000349c50424044070714009440140305003184002981c00204072408a0b0b541d05080c0c10f50401d1350b101403d10310b150340005005003800108280c800c40350240d4545012507443c4200314440b030142048641e19000c120000c4c908891310040c0c406083d44010000340f00c000008456820005035220b2809900c45801e54000c0c55070005e840c008071002501c020810003103038030000e0455030942c2080c0313901002c0b527024001d0151000132200e072000104140e103186541250b02032007a281120464501120960380041d005060640000506150600480d80034000c404403043c00c81c07a4142407071042d000461000c02003125080d42454100d81c042e03015001e0343c20028080d903128468413400c0e042e140311058100c1075920180c4401c50444200c541a00d034044164075082031502e285100e503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 940937338 1250 940936088 940936103
    0x20d0b040b060c0729030106210603020108012d060e12070311060a26060f04090f0305090a0e010b1804140403030e030d0905030903071a030c1b0307050109 68
    0x8800c071906101d0115a16160703a43c00074a051381ca09160070301c460481e6066014058201c030891030092803100007a501034021519a41500244002842420b000c64400c00c2c441030f090040c10030241c1d030418012415101e91540881a01c0c1200d241100e030210206541c1e007135104904400245030354401120140f4440807104910191200720340d050f61400c29010140c0100c009014066082c68108000d040942141c2040a03200c204081c81030f01a202c14021500800c4550b01003180910305812110704215003210b042228181c0b54035a99140c5d509031718001d0034040005900c88244c1e81c1c4104a0000b812400c640003555a1104610b1240d500183c407298103071004040201c3c8149068000c411074100483d4400b4040d0740e464400311b0180880c0d200796031050008120000c40b0b10103a0041d03903507890040000b9035441000c0018949400d55690220302007000007600300031000b1965003202d400c4002503480d182c40d00301c084074030302d498001c500c6510386d103110020303070709007044810741048540c0c0c0e014164 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 940938588 1250 940937338 940937351
    0x1020c09010e0c210f0712090302120705030f03070509091302131d01140105090f01050d06020a02070e0a0f1515031d0d02030d200a0f030f020d0b04 65
    0xa02065440a010306400480b41a00095841481401401d20200300070074010150080e0b01040c03012000c1582c01200c4500564108070800303400c107103031035068007010104200010403910000d407209001d0a002220307220020720101800802c00036515504101c00301c0b56a641005200903005610140c56180150b10901c0051160644041100040340d0083e0248400c0d00c035140412008009401581c429090796168401d4030200910400406400d06212020294144010401240c07402007212940440000051000b83c42c0c4007100110303903a201c44056280c650300b04059040210310307000300762809884020810844410b0700103041950034540c1c20030030004900c4500c4442d84131030007110041d60300440e52118070752207a0301180c844c000800280c9805605030307026605103601c00820310f0060f0b101044c0b013500f26025120701c810f9010f440982d6459000c805210380e013a8040c1c10124070901c045202c814181a000e908491018a4202d0046540b01c200700d0303100300140034240c03403580583c0ca0200d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 940939838 1250 940938588 940938613
    0xc030f0901140a020a030e1b0108150a030f030903080a091d0403020d1803020603040303360b09031201060f09080a020904020d050a1a071106041a1503070e04020102 72
    0x30072400250b40041410320140c3d00c071075405010b5802008044200740d580d903916a40c0c44c105100e03907910a031000d805484042c80b00000140040c4024042e0b942c062014201202240c2e207181e0741d8412a540100c10f00b42004081c14180c0d01030920790700203005103900107200d070899039104c5007010a4034040ca02c000340c0c07089149042092120304071001400f582c0030382ca110410501440030301e201070480d030b040711512545136800314403140c00c180e408602080c0c50380c0e00364540381c1d80c048800c4541d5406010144c00365443c507200c0601c6d81a008005400300941b0404034000f000c0601c00c40700c0500c0601140300745945d603028010010010428501c00040422001003030a420210380100d00580081440c0d10b50384860b002c1110600303889008540b288240c800d102c00096141c3d644034800c2000c0e40c0b802c061445d140e0006030514540503480b40107030300004100300006801004a2106840c140c06c0c84c5030641c0c40481c0b201204810548030ba41c1343c890740e80005007507e01160b566106610070780c00c4e40c02101004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 940941088 1250 940939838 940939841
    0x114070b0f0f0907052101023f04150605090f0402030d0e130e0a0210050301050301140f0a0b0a0b130f120305070f0807141501060e060d0504020d08030c030f0901 71
    0x99900301004c0e0401101007107a81b4048001030300c010741d810080e00280c00f49030710b42401ca91005080c0c2100e00c0c1082c8283e041040784001a841c421010088240090607071600102050b200410052448048000d198081102944004e001d420b014203400c03894146815548100841140e08a109208400252064500c508041c0f80c01640260004c5d032840c0c00a01228058041141e41c1d01440c802c419545015079182c194003003a800154407036940d0782d4148814182036521521111501d802c202051202c904100a051588010007501c00241440c400d400100c01000d00d610400041c5008103000100b501d0024041c000c5515032542800704079602d401000301003613482d03005404140180f150b00081440981d034101c6551086060720700e03040c120b581d4021803402d2240109815404545800c28103100840502d002d44024140380b041540040b002508920400e03c9032010151520086030854403541485800a07511201164072480c0043d8448010b0300100c0c5c9031046505281c0118a244106 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 940942338 1250 940941088 940941091
    0xf0c111203072d170705010618180807020f0d061a0f030c090f100902040303110f1b040b03010906020304050109031e0f0e030f0d031b050405100305060114070b0f0f 72
    0x4440f450b007001155500da540825194056844040700d080201c680090000c0c801daa01a110394804560070281c0782d281882220180080c00c0e03000c4036445014004a2448000d640303909a04640e0950510500f001090910044400040659082030450100c81070068503450b000c0100750f88060201c0810020551b80381824891160010b28580c0420341600704144085da018010300c50215800ba504c402d290120383c8240e009070000303000d91581346000c0c5400d1003001d900d164044000d00d00d2003081d0040303540c00882d4008140c03040d5507c044075810b64a0a402c140011138001710110348a15003410818042c0610310700032800212124000700e07250004400a0440803440c1d9241c040424251100f990800c49500081e03600d889580d240081d52582001000944900c0c1e50300402c5800c6040c0018041c000006007550a0250a000c203011540300d032140740843c22201c2c903003c102c5442d090300603207407260403944402c0c000f07100003a84014040300700e03603050140d098005040b0343e95494103d0300000341070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 940943588 1250 940942338 940942403
    0x4050721051504092603010302120303060a0b0c01090b0a140c0c0d03050a0b030d021c020111071e0b10060e040908120c1b011512030f0c11120307 64
    0x7844070075588182044c1d840b030411248150b801610040401300000711102a0f0a6070b021030002c0040180210305021140040842184c00118118240703040050302120030b900458040d050046100c140c0c1600941014181a401c03002c1c10740241001e041540c0600804076464580440360383c085902d0030300b100c04451101a00d030001c1c00d8240d454240881c06850081c00c007000498503003030342c43e00c20341d424400c403000010f2540080c16070381d2501260362245c400d01c1c0030703d40640e49085900b298100c031500032998002d501c410781c180c86800180040c826031094400180c01000c0c0c1c001000101c00e02c805200d001d0700c189459420800d2007445c1000207840507072900074015241031004400071400c1d440c034075411440f0000e03480d040042103c145491458261110b00e000e07911208018810405410300001400103254200c07144a00307900c025000c02810031300e0004200b480d40c211014042c03010808529000c4c024190850609000c206c540d81e500400c82c03e982c0c01d001e5000300703031448090182e902c44460 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 940944838 1250 940943588 940943611
    0xe04030f031109040609020a080a050105010f0c140712060609050c040521010c0509041b27080a0b190b09060409140109051510080316020d020405072105 67
    0x412030811400703082c42040d0742c46038000a014a82c030ba82d495000b200054580315070b00584400c1e03001030003070805c81d010344403c840c1c900d000014049640d000e2031603041e10724a070906100f103e070986008145402d000d00c4a0015004d00d00c00410281c0401d80d0310f2160718021107051101c070380c5500500c42200d20a5414000e00c4404210401c031505198203048200d818107410101e80b1504a2103003070a4401e141c00c010001100011122400d24041c800e0101e00f148005a4940b00d40b55030300c0140035008070034561004c00441c0074a100c61510100c605501070460341d4241d8125005078134180454034016140d070180802107110040c0140d10038407070b00846400007032103207074640c440310f06004c01070001074000c3d030321600c6114912810701001d01445520707502c500018540c110080c200030704000009071000380d082050420400c030003080013045d00d403c0911003d41154290141c40090703542c1c04c42d800000c0d0090308200810001d10341100a031001c52108000c058a4030340040e0100d0200c4004075050b55000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 940946088 1250 940944838 940944857
    0x901080f0c011b1b21080f0c0f0d080f07111b0f0a0b030726060f2e090f03021806040212010b0304030e04090b13050102040f080c0a0e0403 61
    0x96100303900300c5100183c4000a64503640c0c01c3c1d01c0701584180a0900c0c0780c3c041210000c10000c10100c0800041e41040c0c0034000c04080490b03564101e201e202d51f010040050350045082e40e02150284900d40c101140c0c8003ca89103050443c80181a640782155003e00304003031100042c50b964002c003480740b240007a000140c48088100d02c0d40080000111081035001944408208a241ca84901c01409007074010140d030b843c0d01d00040020450191140110001c03c030000c0b0070030b4261402c40c1c8180c2c1011040310081464604507001c900900300191841c151031225803080180d20f0051226010010790503611041d84680f50386000c4100f280d1480000e400510460154851078443c800c0184c200c24014400b502d0889045a4414109800c0c2c00a0071710242c00001e0008042e00030520403c44002590305000e17401c06600c4448190f600140003d50f125912040c070000c0200030341c1124040c211142c4a1104c0980314602c840d6500100f03092540503440590010403409054022144030307582c560345d6649035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 940947338 1250 940946088 940946113
    0x4183918060c0201110f030d141b04090b0312070312200f2206020d02280818030f011413080f070314070f031b0c05190509040305090901080f 62
    0x707980000d55a5509010b6901b000301c126105000030102240c28103000b150350031003504681321602000e4603841fa021004a0004070f801030380c00039902210804080040c111076004046800c1030300710415803d11171303800240c180815030419080010304a0400040001c1442500f07943c600a00d415403000101000303001c00618582c52100400807580c00780a0000000d803c44c0e4402d030505455040a005a0446032a842140783d04000d00c02c08103410304a100390004800052010726440303c013001d00360700d5001550340e480c241c0d000d038482203900c0094102c402c40c040b8091414024113540c524125104d0000010404050302c84100103074940d00b00718100c2c50254071303a40e12501e50b4403019040302888032002c842c800480c0300d10090032001e401801c0d50422000701e13150091592000c001c582c5040709003100484046880f980505081d2001a640460880c054460040c802d0515602c103d510140d082c1c20001010380c0a0050443e40300240ca250b4226621160349176120158201c0c405155804020920103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 940948588 1250 940947338 940947347
    0x30d0813050f0a0c1a0301030201050f07030302160b060a2c04020d06020a08180109170f0705061302030f03040305060606030703090b1302130204183918060c0201 71
    0x1100340c49003089a8100900c114040d0a110401c3d0041e50700044082c000c014030800d54410a10381200203400c13514642c1990700180c02405505030018034500040351003010103007e941241e11152400d02040c0301d1000314600b20b40200ca0488000b0300400a800c000140c0302100f21001e5092554120b11030003407070b0786035500b4400700350081041e60f010a002140030b02144030b6100810101c03006659402c218900b20350880000d5801035414400717685001c065a010a080c1c100d808000c24003244816507403401f50281880a008852001c0c01600540007805500e40c92440e103200c80c140300f5006d035890000a2070b40070762070740940c0c44081e1581e0410b100192042c5820801184d001d5802c0c207002031030f49010b1701c2e1000540070480302d0300c3e01d90704048902401d40c81c02c10503d0907608032844042d85842d003001007007040183c0c400d044800e51521001c010212079003c82070b40710380000c543c440c0307034582c1002d0008064903991840f0203c04545016003038503024020828403025240305854415000980307500455 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 940949838 1250 940948588 940948621
    0x9052d0a0609030602070501140405030712050406021b03100204090e0c04021c0902131b020c09150f0303040806070804030e03030906070f0c0f1d01080d020d110102040801090303020315030d08 84
    0x81e1f85560b01c9035468840d2048000540c01a40100e008648a11041c580980c03021a14015002402810300003008030790360000d80040d0304100f0051440c9001c6c0d4850110386445001d81d80f00b8021030000c40e010450075120751001c0300041002007150003030000c01c01400200e00c00c5502d0341d0311880b0000d01702d9400c141039030010458a03101400d01c0c0c541d00328884003001110481580d00803000350000342c41c107481d40e040201c0a1660070407501b481031818004003402c0c0d20014204094003840401003c51015078080c0700380c0d8001d0111905960840c94044e400403d103403400c0720118003089010180511505000041d150603c3c00a4045803401c0c02d00d8a5884442c09000411030b520160740b0004190102d51282641c01400e05a0001d800101c9000d003030035407944160032840b000d40c03100e07030120510b6900144c0500c150811381410444034156403480d502900c0303140c01100c019828803600c5800c140c0d15a005611a40180c0703041c420b80d695500030180c45281a1031408009400f000c0415500c1005450700c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 940951088 1250 940949838 940949843
    0x90e0c0a0c0305120408120702060606031807080f0d020d050405060304060506040f1b120506031902190b0406031b0801170a151d06070903080a09052d0a060903060207 73
    0x70740c00c01803246164403030b030802105c00711601540416000e4001420054444d0000e015001601d010300c1c00d0004104980401040340c409070304644410042440113005120207054440103840100c41c80101e2259102e0348420010010f204901c62244807900c62002c0e01c2c00e54400416031480c42d19a6252071000d403d01924041d4010b947d10045421100345116965920b24008507000c0524803c20001e4040681400c00341d120781d06040030450b040da00450000c00100400c4c1e2003140000503400030400702c40d07008041c20300c005c0d0301c148007180030007105014004586166330b007400321000505109450400408503400070400d28001402401c1e40742602211990800c000c038ae200e0101034407680c8505e112100d0300804144c1c1c581e408903003064114000300341820394000410b0b59060004004003900d00c1c0d8480941920f10109a4410b158490608080140401805080054180c0c1442001a2205059401421900503003822103040081070001194003035242d503080c6501e1070b00c48102035070100408 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 940952338 1250 940951088 940951097
    0x70f06030f020c030a1814031216150e061303050a030902010216090609050a0905070e091009050c0a090501060c0f020d0210050301081603150e01111603090e0c0a0c03 73
    0x141c580d903c2080584292461a5140d00c144035412440b1905d0184a4001e411504921148491103440c000340daa00d0740201280d00030394882640b400000b806036403500042c504803241a503000c90540a0b0061000e40384174000352032690304c0d680c844080c3e80406100c01800b14905000c81c2a18038000d62202c10558018010703a400742da081c0c2d078000904591a0080444070ba40c0b000c2c14402c0502610610b0f60002040301c0070441c2c04900c2d00e0301e9580d11008c2c4a0344c80c010754508000383c40c00c1d2051041038040203e80c0f40600c0215007a1500d10b0312101d0304207645009810302c1c800000d00310541c0c001d8a04031030880d00c0d4400c401d0203540700e400804071139460a0f6046040b20f00350100503110724138003070034170a81640d90700d450754101180181401d5000b04000c01c042c031110740520215a086402555140c6c07649400989030f100280f4813409032103008418084a800860007041482002d815000d81c0e43c829659442a40e4580614420010040d20810510741c014012080c0b0907000f82440d80840740603040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 940953588 1250 940952338 940952347
    0x6190e3c04110d0e0c0f1e040207060203090c1008180a200a09051b1b07172e02070309080109030507060f0c2c15090a0503070f06030f02 60
    0x305080e20703010010b9152a601c0000d010010301800c0c89000300000d0b014000d05078030b100080002d0540003424905510603a150140c4503c40b000892074022154400303001991a03640714100180250411075030803005001c1c3c1c0040d95500c0c90006080c040c1d84090b03854252640d25120381d40a403040c084040e0300b84c0b5100785481d1001051a060010749241d1a01c588058511400414440c55850947c0141421810700d000e2154005003108004411101c007080e4079158404c5c80c0d6017941010420030000c113940150007010030024109030801584103c80f4080f6047c81da1b40103005e500034040c0c9100140407400d044400680c0c2e04964000300344850003440d0441d417094540e00c0c5242140c40300f020072004101c0024005041001c139001c2d0070b0001420080c01c001d4014160800ba001400b00c09041f41c411510007031494161106042290120070b025144520955156516450f590300c042d800f14071854620000050714a4002445819a01c0501c2305c0030314145414010340203410025810034006400b4031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 940954838 1250 940953588 940953709
    0xc1c110f07050a050603090c010c02010302071b0303030605100507141507020a0b160c1205041a031008010b0d060e010b3007080d110c06190e 62
    0x208032055034200090a0100d140c4030411984a010b540aa80502010703c100300500c100030036070300e504034420b0810004504007440120028850803a0003400d2203003a040fa01c030240f40d015074503400d9a2103518108091070b216010002c1d0350642001c8040040d504000e900002015444d101c8418403202d0100c4c0c204c40c00c0000030000410703003210b095005034003504440e010305c1a80100260000c0500000c03110361130302c03080010454034038410081c01c41c3d00384008001546205204450046c00ca045420b1008008039240008903401503d465100720b2500001080969042c0b00d10301104400510800040e0b10340d64a03100506094881040555070300e103400c1400d5107400544a4004064043c00c4d501205055241c0c50000002c0c03d2131503071070348402c0090261000018a01541c48000d06000039880c004011151807d070b4071050441d040344020428041c4100d6842d40440000c0c51502d81041d0200e0003020320031000e040c000002c042d40204001c032070040103101c0810403003004540a4241e2880c1c40c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 940956088 1250 940954838 940954843
    0x30209060a03022101080f06070504120206031801050c0408101104050114130b120a0b01080a020706020f0414090c121909120509040e03040b04030b190606030609110c1c11 75
    0x2648620904c0e000fa4032049603c00e018405254001e27640d081c6142002d09240a46901c00207904009000d9100000410f1a2910322560b24015911510082c401480d08915080d55504a40310b40d06c400d124585c020011000309000c0c0d41780741503142100e6400c1502d13000c01140c5440001102000c014002c0100d03c4c40c0400d0314651001401201081980c1c0f61209800040038080082650088074a4912940e41c540c1c2d01601c0321f604505401c1026841d02281e06021000b4890380904520f20000040c5c000b0701c0d0849010009060402182d4008190f606e0502548151240082c4060014401c1000400048107481d045940d002c02c41c0002035100e10f0303070380c0c0c403095100320488500110350045076007160743c0f0701806421242d03814000610305051400c000325166010705d0100820301c500b06000602d405510004c0350361030580408003841490350b6014081c00806090180182042c00d0180e0400707420384040481d081c1c41038041c0141002203503c207105002c03591400d0703a80700b00280c803902042400c504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 940957338 1250 940956088 940956091
    0x71820280801060909090f060e071d04060c0819090311010207140708190609030311040308030f0c030105010c110312070501050a05090d0804030309032319030209060a030221 76
    0x654580701c1c00c0d9410039601401207045507000030409418031012a00090a600442407110b50000010600308001141c403400c0069030380202c610b8080078007208220100510146000302d00505c0704201d01c0e94070003011280d40208940354081500141c2444044110031751010304580e0107407610449a03603800503001d003680e1103101c00740d4000300e0317070745009015040602c9104020070383c070402881c2d09401070179141d0740f41014000142c02d5039070740c00c030003410f042c080e4009400c00860081003d42d038075120300e8651005c0d0016214007100240010000c0d00b01603601d81120b043c1d50303050710b0340c00304908aa5503000c07948a00a0200741c043c0540c80301da940446c0400003804140e4490130003c107051801082a03022243c3c020407044007070b032000b80c00303540090300161a960055003526001c030728415182004c0e01c0720b02201d10920f8000d2000070710700748880b5008015143d0011038042c01e0038034200d81d0b50100d042e400381c124001da010004104030741259020382c0c01480d811016041011041d180c030322001a1381c090 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 940958588 1250 940957338 940957417
    0x41505070606061e08040f021206040c0e012d050405130213150b0d0209061b0610034106040b0106050f0904050603100e071820 56
    0x240861484100035050040302d000d8496481c107461840e0305030005100380c2c8031084052040c8114940824103011040424100054010b00040324807407481b00181d54840c42100c1c01e035646044184042608200c4021043c121900c2c80a03811078500001886150080c02d102c2c240780d0407500740c5001130366803140c0c042c040c0300394180341c1c9031094000140103018849050400991a440c03038010b80030200c150280d20b1f2400e48214118450311b4101944004000b4400c0202c126403000010601d5089003021144c4060138080d00c1060750708a4641c0c500310324100c2e42d5404000c02c0300b03440c081300c45840f54124030400004071040c01c080080b1400302d01c007021036010400a10101d50054400c000510490b0140c2900504462405914107422444800c05500440002600c1181c446000c1081c0e46e40401100800605044007040320141c05040c5981e00d06052103501046044c4100d01e0103d1202071103401c914030414140c074800080089000c85866101c17080e8500100d030458880a6041d0807018528211003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 940959838 1250 940958588 940958597
    0x1409060d0c0b0c0d03062925060f021602060306030a0c030606060f1d0405040218130c050103020901020c041805070e25020c10091508160806090f07050415 68
    0x103e58402030601120329109014141080c9007048489407075a8500c4144a0032844c020345542c0e81072401c03003103100f000f12030b00c91420011200054001d120b5a40c04040b031184004111002c10800e140091303010340c80700d0344c40d4505c0c144082c0e0050705100008580c42100101a0f683d402c9456843c070a604400307401c20354050382e641c402807051a410075005a0218158104284000c01082e12410101d0400d00740c0c0e400707a502c42d804a011900c8410100e01d0307550b001c4100d20401e180800602481802030759054450740f505100002e104e500920031940c4150301a4041d00302d0a49000030300c40a8000440400a500f600e100040046401449450302404402c20942d2031410007640c0c0010900c2030b500d0780c04510200b8a420350701c1680014403021000b4003a11515440101c864050300d18034583d0b880407000e0a10310800510750303036115200501ca284032450b11038020b00303c034000b1120304000b110456001800c10f000315100038003039144941e2003440c034a0202d1406440d8000201000c032040d16210114 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 940961088 1250 940959838 940959847
    0x30d090c090c201f020c0c0d050d030506061614070b0a091d271e0d17010e3409051201050c03130c0b040e070809071409060d0c0b 57
    0x80340000300f540880b0204a00801070302200b0b0703100b10004500c01c54040e0449500041100f103040d0188101880050b0080c0301c600440c0150402a485015030340c48074002030702c2d01000521070714060050301c100c0d902880d26424142100d565201002d480c0c1d400480443c03003a04800202042090010070b0341a281e030352031025441c90f151604e1281d100d580341c00504111a0b404110440c005040d901c00000b1006217a100c0140030005624149100d00c0d580c54809050541035140c40100007a210000d0101ca5846150070031411116074800d500a0003a44a02c10100000c038291500d503000c03112800b220004081c0d40c0030500901c80a2128034642d0300d80100c1c0e94000200300c1c5142241c100059550b120000b0305c06464000302c00c0074548801801c1000f5101200204010320a40c9804840600700ca1490560342d81d4803641050141c1c54101c59030030001c5c080c0c60000340c20716800f00c2e1b00300481c0d441003010354031410107504012110100415454014030340c2c2035404041035812160300001c010700716166544 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 940962338 1250 940961088 940961117
    0xe1209030c0d11190b07150b030706031a0603010302150f12040f060e0307050a060c020c151209150423030a090312030e061909050d0e0a0e01030203030d090c090c 71
    0xc035620b4400300d910480403080811040785040c0407210300030350000c82124103002521070107000741415440c6640600c1501d10122f8444d406a1000400c41030036070480795000559410070601c2d20003400001e401c40d078026003200886203060040d2940702d204d640703e14240704400f40b208580328011181603a80b080c08110010074003029200c2d0440808602014519000d42501c1e440e90300c0d2464940181010307a114002c101a40c801e100d80301078280001c06250469803d0595001160016031034031841040c90b0010501c0304030005040c4441009014000080da0740301c0d00c9592040c05000c0c4803059158104000703c1c1050014001030003034404649409410700d0550800c1c40e0408641b40720101450315001882c500c2c0603001850541c041e80129040380c1030085400440c01410400724024854861014070184282e00410307210756041040d07840281c241d0f074400e10b05141c1c14082c0300183d01a001044407110400346c542040c031a15009030300c0d0010741c41c0e4415030b00040b2090304650b000000c0c00450443c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 940963588 1250 940962338 940962349
    0x310021201060504240207150203041707050315100302060403120f09080307021c08211f171f060f0e01031a07030b04060e16030e1209030c0d11 63
    0x1420b0146411401c09040506014007030250085000010f1005440c0c00b50b000d100308500805482c406255031007505060710065540c1e005070140620519491a41d40e54110000074803204070707031000b0010a010b0480907000d048010300603040c48030a256034140400507803039000c010001588511110000c40a00d004000d00180d030600c2c0140400c00394040030803000301b0010940351165012100400c1403803550182040d00c05071000000c081c0c2c01c01081c880c3d10411802c000d1700000040c400d02c8005591a036215130040403818143c07004400e03649905103e92030341104814429128981101c40c1c208850402c5074005040019151809480e40010b01200000799003250092000051403502d95065660390304103800046281b42843c880c8200046806100307420207500400c000c0d104002140d01c1c0d60443e10320071412280001040d5003258151102c5201c1d11400e04244010005010258113240d0801c0c0d941d40040c507442ea040c4291070302d0100f035a07202054401e01070300c00c020042c2c03600140403d128 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 940964838 1250 940963588 940963591
    0xf02120f0d170723131802130e0c04030f050a1a06041a10030209011e05040918020d020f12030408070501030e0d0806010507061103040506061c02130f0b03100212 71
    0x2048201d2103180c1c00180512654403020301801e008507242c098002d03c1000021300ca500050000440d101c0d440700013202c6038010202d40c002c854082640585409e0702c48041c6506580003104010100030800100e00c0389c280a4503400d1080003038035002c0310342d501c601901c8410a24085d00c0b000328801402240e250503c180250583d9101ca5800e03c5284600090b0038003031501642000d268000134159005d0380b04009441d52500c00d501c03101015070f12071100a215070494082d403403019140c4102000180c9500041103d0103900902104601b81e0740e5080c003038050032205d0441e4021740c01141701080c030f081c180301401c00340403001c004102070361401000405030340e0705039007460040d00107035840059544d202c3c040348e03407114003800c0040c3d0b207810741e10303140c80104403015442078641000700610081047c0441d80034000c1070100c480000c189860b003002c1001c100b643c407000b03501c68034003020902001c03007a41205440305801a03000075014103c0010a003070000782100d00c803800c0e6001824429000410144a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 940966088 1250 940964838 940964851
    0x90b0a0608010e0c011707020c03070909031d030c0420070f120c030503010e1302220b09011d0603011d031c0b0a03031b0c120501050c070f02120f0d17 66
    0x801300f040d01c08001070a4814070159041110304410002001e1900070440c1244400e0040c0407610910fa81c1c89841c030040200b000e00f1000070301d40d04880341400e218040c0b10194120024058003600f40c0c02810007005100c1b009202e5084068503040540c1c84003d12b0182a1150103401440035589080c54030182a0080c1c0202c04240160b0110110229600c10107983c1940d10b461740246440e201c00030480c81c40900f00394000d52003008004d01517003036105d03841d000c19250030400301404440b500f8070811401c403a00b40582e0303400051805080da10700d103a90388682e030050006000021080c54042004101b0034045074030303003456800019038a00d403072010000751443d04040d2404000301c409000c00103102c0220f40c480034081240d1340c104000008090301c1c1141000c4e030b200094440b003903519982c1e050740c41c1235010191555482e000004507014041000c80f1030f1540c0c09990220100d01c19402c0011542441d100300010748a18001c0b01701c00a0b00700001c1d8810007082d02c40c10794504c032030001c145410200900a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 940967338 1250 940966088 940966093
    0x1403040f09020a05310b0d05091219110f06061804020d020d06140a1a030a020d1b08030a0305150102010c0f050a03110d06080d170402090703090b0a0608010e 69
    0x40b80f6010390000543e0901c444103294245842d40c001c800300024907031416609144404818001104e41040d07005010b001c4460304180095612901c036241c40d80140000120311070410050b8444580102c5e502d2160300f02141040c141095500c0050303840c065041c99071446540c000e41c00e110380e62811000d012a0091040005462807500340e0118910090340400240140c41c803020090801510f50480d02c054024031620f14100d1400c9081c80c80544002030002d0858484419220710328100815900c0d0311580250130050302030040d940b10b8040c0c00f40ca000403222440a2107021034800c806100800d030009039943e002c00d1170b040003109500703035030151071920b41560316000b1801d201d13540100000341000380f0303030070a1600e6040400701a00540501030712042c28100016192000030401d5000c4419141ca038001c0300c014480c20303903045c0e03051200d8250540c820342c1704c0c000041c0141382585100740e10220a10340170940c2c00550340c84110001d400d9460030207080d1600800c1c010907909100d4448240d404100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 940968588 1250 940967338 940967347
    0x501060201150b070b1302060705010b150705070b09030106080a030903060522030c020a081516020105191505040204180b0301020406120f0e1e07060903021c030c1403040f0902 77
    0x240c0f03000a01c1350740b000602a1041c1400111032900002c2da210310305801402c4c0b503580e015203150440c000c01c0070140d80340c4991030b04040340c481e61012030300303440f0180c1d8042c0050007020f0804140340030a800c0300d00303e0341c8c6c90340d02d40344040780e01841402120240352280c2c1300d1a0220b0709500e03042007503c0006186403041c81d030202e240480c000030088400d0401d034160500104072501400440e03a054080e13081000d152148441c0182180e000d420440c0c4500c41d4010b04210302c0001040c103e090300d2090700e05440510351491210300018040e80103240d04c101902100040c65540c601050070b0380c0065109085071000c100022003010342e5030089424a10044000b1494541011005403400c40c0610b01000d4003079568000044078800313540075200340f1070441c0c21100703800c005684108041040840340c01950042c0342000628a00500c030303080c00c0d070f54020078151a040c803410900b404000c2149094040007484081c80c00031821203496505030f5611600030310340d15070501d051541148403035440503110f54030410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 940969838 1250 940968588 940968599
    0x212070918020112150e010611160f152604050d02120d0b041805030c07060c020f10021c0e010e0d26040b0c03120c070c290409050106020115 62
    0x4480000340413030b031103002030300111102151040c5106a004911458500800801d104c3e80004404d5a1b0741490780c00c4502c0041b500e10120b44081d068800c00114544140081c4401c841043c0443d48001c01403a02a42607081c0c0d1249040401d84003611000401040f270030b22061141c184130b414189001360005004140d1001810100f5200d070111800e50309541d611400c496603104d4200ca00e12001903150081101d94070b040c110348035400180240c5042c0b00344000022141d00a14402203003c3c2c00a050811000340c46082c080e491540d48980421401191911005c00d075140001d50300a202661b50010034003400320024000d080e8554200740300380e445800c148002127418640c01c50145c810070f240804420028112141c0b400340da00000801d140c0030407801041e400c00000350400300f55039407000f400d81d02c0300072000050744500b603006401039043c0fa00600c0249039090b941d00c1c034101f180c2120740e1135948414889803da009904001c86c1c10b9280d000401c19580e090040301e070a42000d06404038528a0310 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 940971088 1250 940969838 940969847
    0x312041d0f040c05370e061f03020d0b18010513140112020d051f0b0a030206030f04051c081005030f03191407050a0b090606011d0a0302120709180201 66
    0xa1044c1e0744030314043d800c3e5120007080c608428000e0340111164810029601116031140071984c001c2021100c40c110000b005441c0072141d54100c0c0300032110099080d80d48401c1107000e50301c850348005240d41c8035003005031140c4821102c42c08503618001003502039410202040100c18075110651420382c10850784164030180100c25a04540c00c00300384804035015440402c0c1c84201c0310101408501440c10041a0010b04514510548801d501c041154000070020044144500e000c003a400034018000681150b00d40603003030f900035010700d00f111941d00c9503800405011010510140000d10703401c060001a0218000c0c1d8805080c0450180551910032030324a966401041050400c014410118680160056090324040181c0800e55541c6807001d0800681d00c1c5c09502045a5128008000601c04807001c40c12500400059440005124815640b030300c0d21140c540c1081da00c030360a4400040141c5c5d49440c0f1469488545001d0511a8980038100d02110210305680050300d03104945040183c0c2c1c032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 940972338 1250 940971088 940971113
    0x2309120f120c120a020d0912030e0904060902031f060f1a070c1a120604060e1b0405030d03050906010e0601080a0c11070905060310020c0d0302090312041d0f04 70
    0x120400c02d840c1d10300a00c8180ca007042c00302c0b031044a80d600007129000e0320350101c2d40c003001c80082c1e150a54540e648a202c0310240c030505001900050300c1c0c00b11032845103001d00c007040d0001d0080c0404944118030b0380020b82492822200700f2110100b43c440c41032548007c1c01018010040700020f04c540d03134030308419800e00c40601e20354081c040900298030f8040207c110520750241c814603403040e101d00d60b4a12859405c2e8800c3c1145e2408620a4000800d43d26050250406680c180007000103a5106d44a0388001101da0702c4103410341e40018800410252800c00c0501c40d401d001d65004616030030042100783c1480c8041c6c11408000902800b00111a41c0000700c80707030070031268140014901c00c0211b04032421034201800e004075000b10340c0000381c000d0a64200d14028a000c40940d9181c60140781400200d02c80c404062011f90000415003002601a0b8007900043c28094181c8070200702003080c8075403d074030541000c5a00c10340d0b1944107801d80702900c40725500c14440f0303103c2c4865080c552500c9021018 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 940973588 1250 940972338 940972363
    0x30b01051504030c0e0105040614030c012a11150c0303192a0201110a12050c0f130f0509042f061b37032309120f 50
    0x11034891034110892440c01c550040d500035104d015030760f444415056032010207110300780c480c40c20810040741c481d1030b040381c05401c114010010311808406d00d00550703100413044400c00010308100039110b2200308158036070550922920b0a108005505410080200412143e68007070704803d0040f401640d0000040f640c1001007072a600b881075501e2502240507011046207060030b400e0446195180001c0c06103400d02c1104d4540081c441d10b200e0f4004a1007a0050b01c1803017000942e00c0001108407403d5034401c641010105401d1490104e2202c40c0304566440030f000103245544004081128000404102c1d01902040728080c0c2141815107451000c950850340c06c101d12207401e000700c5080704508080d104850009810103489100079818504c01542c81c24100100d80034141e183e481110800c01c00b8590341c602d2804200186114404005009420001c100d0610101520032040c038001329098401614071450b81503964070402040c8051401101c800d2522613105154000c0e0104022030001d4034000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 940974838 1250 940973588 940973599
    0x2028020406080115030b04240504030e091501080c0c0f0a06060819080a031b050721020a140a05100605030c120c06090f060307020105071e050a0503130b070522030b0105 74
    0x7c036142015013003145205c1d21000d02c00044203400d1420351203504024440d501035100c1101222240b810f005100c40112149e6460b5946100184000c1d8013a00780c040d002183c014115042c5004101c01a11309429510794503156440615140c08112240c010344c00070748421800b41082c408944103122561140e514000c141c270a0114408903100c1c40313540000690604403164601e107032003083c0040c2aa03400f030441604c4103e00e4a8040e29a61284544204881c44c15401003c2c02e40c441c1c0c9070b42c103481d000c42840d00c81c280502000140468010400150010262800000c04900d0541010b24004234800700c14007560054100103008480032480302d28a942c2520801c2d0340d00c84a0340000e800c41c4101e00f0150744201d002c810301c8407103941503100b54032460300c688584401a44000e000c1c0d16113540ca6900c003000032810084036407054410409160410b054078812032820480369500140010101c6d88500041ea01284c0180e003002400d00a0032442034205500c0e25490851300d44404109050103036030700a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 940976088 1250 940974838 940974841
    0x16060207060e07180f0603080306041805150f131110021e0d080f04080a0c0c0b0a110d03060f12170333012028020406080115030b 57
    0xc0a03070340156440c92010700070355075000d49940040054008001c022401c4c03a150805111004000f03100d5002a69000808141142d5400d0308000203044140c103a2241900c2101d07500b000640c007082004031181c80080207075510724055008400d4640c004001c2c241c05024182d407007022a010b014144144e00c8241d808002801c65008142d00c7c100142c60034840421a1404c0c2031500403020074000000b4800da80c0303500003a100d00f20000c0040d0410342e00640040410031504c404240124085645240b142c1c070540d00b0786a0f01e45140a294105a00c48404500a4a1000c1201c00d0900c0112030f110024101000b0150604120718000c10040c003600030346c0d10140d51150180503032900d03001850340503030503015520701e449012130110001c12202d450f0f80340d60904180e021940514030f8620b03a12030607074400b02115400b000c1d064541c0444004d81d400c0b4002d400592421540303841c000031100c851800c2e200b001d02d0035841444112011a07128240c2c991500c1001e20360007074210025000ca1360032940c0e45225 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 940977338 1250 940976088 940976093
    0x30c051b010e0d0207031b0609120c0e090309031e0709390f1e0507020d05061302010e040c05040e07110a20030c010f030207050102040f24030216060207 67
    0x10a441802d06105208035a140d0501d40d500142203410b4034411180b19102c812000340307001d0560500e000d8140071505416080c0454603a0404080c040360140300c590301c42c00da44480b070012006050b6004d000c240c000040003042400c04000307026146d0f0080407101d443c41d000e10318a9403074001d01e0041148043d00c4103103411454444122071540b600318010b440c017100268100c0500034008030018400400c40081c40303400d101e402807925400d110201803e0341d48811221008a851b0390110f90101d0b44034002d42000404038408000d035620401100b0b401080c0100b8900014202075200901d0030701c290305052000c41290f601c4400c0c1c030111030080c0500c02840e264402d00751080c42040c5c001043d5072150416160078000800c2c040d0042089415406201035010802d0545491002c44181d0100b514030701184c1616209030b004015541c0203e000504080e1140f00c00c00040b01142e21000c0e02481800c01103030840c00c242d001100b10300e49400c04501c3c3c0b080c17106440090801700c0c0c1007c0c002e2035001c80c0480a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 940978588 1250 940977338 940977341
    0x6131e0302120f0703170405030901080403180b0301090e030310050d03050d0212060f0303161b081608010c0809071e03061404030e060915090a0b0a020a050c01030c051b01 75
    0x41040a498034203450f100c0455040140343c2103200190001118001082d14050a40c60802d0045810502443c40c0490110041d12403400c00340044042101ca00545038040c45050140300c050140050382c91f640754948000b88040d180300b085800460307081003051040090300348065008940c01078031540300c940040e080944440c010780d540e00003200c0c0005003940d1040740700b089552013071030110344c213040b1b010040e0300785581c9000b45480600f500000a03054030118004851061150302c480d044a0382054443c0c2425050080f5491303100204042e000d03060028035400e00410010060a280c82800ca1900340310695540c2c583e071081a21400e11059280d00d14050010000302940d0005018400b03480189020a0805030840e410780016000803440142494400e0403114020380c01007140141180242401c2150340c8018403941d40700f4190440080d1fa0b1030404040e0034501c1142d0003902408056092003420000083c07145410186005010351724540c00500b83d40c2003070400e180c24070410300c110315241d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 940979838 1250 940978588 940978603
    0x110d05030a1d1b0102010510270b03100b100c0b04030309031412090c03010203010b1c0605030a05030a09120b0f130519020a0b04080703080d02091003090506131e0302 73
    0x24280d006940120f0110600401040c48040b4280c4c000c00a83c2c0d9041603401002c034050180200420000003012441108940741900103546900b0005501d14400c4c002458801e00b0302800c0c80d540d441c0d8803800310781c5c50664100c03081c040050521020710f05550341c9140c46158020002014181d40745040e0051600c0362415002c0d818502042c907a8400008204d1480071900f00c3e0000154400e003811300e02030381818020780b41201d41c103101e86418100072000c1da060180c00e09003030000e0b40d47d5335040000c1656040180401c810301038806035075030f00c1c045d6000030710803c0241c01083c04082c01c05400300000d2490066603500c0360b02c1d4010004c060b2034020b0321306d1600a180902400d1803003598403095061498681000c07032144200c8001185a03603030300b082c0c242c40c080c9200d80c40c02500640010070216217008000c2603242c210000061508400200280a0150720030070742002940d102030301c0c0c0412204102140d00600d83c1046da81001c000d560f50a4190803d0403404c4d1440021799404008042c004c00c1080c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 940981088 1250 940979838 940979891
    0x1006051c060f030c0e071404141306030b01051c0b0f0a0905010606030506040c2303131202030a0311070203070b090f0402030414060f0408030a020a090510020106030201110d05030a 79
    0x3210203650f034107250b05442c40e00d00030310300c03148000404144103d00444e14000c2d0340300e03800240c0e41040e03d80740c1c510f8051035000040c5a000781c402c20203002040035034490407014500c154811440c55040100344018082e5110807a9000e40004d00d030b40000c510203030086c81e4403555014840c542640e034080c051000c2c1c42d100c84010121342c20400085000b60700343d00540c1c030030881943d04111016030f450301103031140303041085440c000300800c03007a0b20780c2e007544802107521038a6a0710f00e02c040b00c100e070780391116054207d04100060304007140c00700c8034680c140140400c2d10745c41404641028896000282c03150707980d100ea04038a6100198030841a250a40c452650a500520440d183c0c0340070b00b810f0141c10018000080341d40280700000c0c809080071000f83e80100d401c40e07002c80c11a0f50780c12800c1c000354080e860600c14003541c0c4900103850b6480d000040a06443c035030000c80e4052031440090309240d02e0304a040115080f0512812280c1d5210041d030f5840902507a010410b088056a009011640d26001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 940982338 1250 940981088 940981109
    0xd0c0602090109260c1c11060c1e060a09110111010f0c030603061104030f030f0c0b0c0a030e031606110702060f040305070506032e051002151006051c06 67
    0x2c0205000030f00e0440260130b254801e4841e81400c00c010442c54a4440805154804d06450304401090b14000b00980e140d00c01f500d007501e048920041e85107841c2d01d00c0003200124011444031014003030144115600484400c07000d00180d0700582d104504400c0b03070641070b410440343c40c01001e241d403401d421201d0b1a040300d9030304001a031000c03c03005002d06050300064039000e0034a40d903000342c2c20f88082100c0c12240c01020020341400da42e030f000c440500c08440c80c801001840140a0041410506d0180c041c000c081180d40d901c201c1010090182c0f50301c0312400d102500305100d0361341c00d6003044204034106a4001c0002070424a50402000b943c061060b01a400c0400498200c00c40c04401d00100705480c061811a80000d03907610800c2818882110400c0d00d4012444000340c0d4803110780c3c044040c02002e1400f0b1181c541d101e0700460039000b684412000140d200d560001c0080d00c10520550304035012054201d003a07030802c0d41c00b174000d00c50310301d26402c0d0600c540545020206142e0214018083c0b2402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 940983588 1250 940982338 940982369
    0x130221010b030f160501080c040302041803110f120d020d0608010c09080106140d081b1605031507360f08240603010f0e0d0801080d0c0602090109 64
    0x4014024030710440094041c1c8030700601600c000320005180c503075540840050a110b10300307040045844460161039503855003000d00000c001603440d8042e001c211000da83c0c51141b0604141001800440c5c0100d02d54460342106440405442c00410103600300c2200551380c0d40d640e4010300074100248500352803c02045d01d07020002c41d4440b4190040d640901a0395102e04880c2e49407000300f07003220124818034840ca0800244032540303040c980c2c11040d0f6103000d140100d08000301501ca95409000c820011b010a4001c1c520070305048036214650805064250024070352442003a0342089000c5c800780c850390038460b140e0f81005601030380700c1c0c501200500c01a05156441000210f4129030078490103225660480400046003140d40003030101440e0521691028062a21002029209038003403c690380654a81088004542003802400d02e0840b41c0030003014940d202150040c80400181c100031140d4118450030f1040c00c1d40483c000e019140c218600603981d8001c01d0040e07503504607a50150700000300204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 940984838 1250 940983588 940983649
    0xc090102032a060f010f050f040f180b0c04030b0a050c130314101a0d020f04020a0804060506040c21200a090605040f0b090a0b04170d020111031302 65
    0x300c5080003011804100c0d8141d803100c01301003000007400d00030b11502913460f071400c221520301301c4600c100990002e840025404600f00080c070545100c040200340c204a041010010451201d1483e42e0101d00200d03c0f500303142c115076a200700304001522503000e1503229008940b09054030000c9a00300c4902400802e4440c0d5240341008050500711641503d80c0200142d0441c607445600a0300511950422182100c600540422130054662a400d9810440351810300c41c15454510041400000e04c1d1500140d900d01440e1060a5400c01000710b400365040496071041d8503005452141e46000044100c050003482411000080c000d01400b584150001e51840d50400c00035030042c0740345050b90756103402864403201c003034846100318450860310b808130031400c004c003c1070038003c0c2c02000da004005203889507842010104942154110f9019249040c0c0e03015600401013084407801c4095000900824503d100803009074080100340c0360145480395055400c540e10340044035008440c1402820b8481440d6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 940986088 1250 940984838 940984897
    0x120f0f0f192a1d07090b22140f03010c02070501050f120a09030f0801080d03020d02130303050a1719020a020124140a180c02030705031c0f02120c09010203 68
    0x51041e210b00114504a05204030000a0301512418550b00e0b6140c01c2c40c9001c07181a035941c4440010b840e41d1403080740604181d1414524140180005941c0021000100e4100034208640e04c8040342b10760701d010103085100c6d80201d44541221804d003001611424034091108952264010300101c3c203074940108204515903030320034003426009680c1e045207055a410180c8004000703004e03a09c000d500c0b542c458800e05109400801c00024045805803d2400e0000c084c2c0181c400381d0011000b180d0702064640002da0320989045804070410128002410300c20181c80000811201c4c80e62000d8000480904440c000d400500c020500e504080c18000c54002040304107607824011031403640c5029404241e80c2c42c15054003019180070300e403c210b1489a400c8880c005003110035030340040d4002400250701150060014004010501030009110084041040c04030789400c088080300d940b0511803800c4214541680942c172265100181d13541d0072031800181c2c0f80d40200b1405007060401b0813a5104002d070305 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 940987338 1250 940986088 940986173
    0xf0a09050112030801080d2712080a0f1d040c110303070e0f03013b100606080106082202150f070b090a0201121a120f0f0f19 55
    0x4e984243da01c0c0d07207800143c0e494051590326040003800038004007040800c8084040c0304200c40707464074402c007603403807101300c49800c018203090b030b19000c000c40c04001103604a805a454006140344c880c1c1d1042180300070b03007018104030300d00781e004695816000c0c0406009546002c03da10005080b2500c0c0e00c0d110500420185070614800e00690030a6814200c0f1709050240b00d40100c90120700c0112000d0705120400880ea00d441260098000340d003c070740d01300100b4413441800c6030301ca42003c1101801d0010188c401702041e0f00c42810410f4902c208803401344800f40b030220541c43c041c40d40080c00c999000241d040800e140c0038200c0c1c440d0008500c80000f0030700008000c02841442c0b580c1242da10765060782d0300c07080d040c0d901a012031025a04c01c0c0d20f04180d940120f00c440590a00355580400c200b010034240c0350904581d42e103590245003400e100c801c0800003189026003040c001c29005c814002070b551600901c00d1000b91018522107920100103940c40c1d00b200020024045041c0f06020300c0071050f0080c0c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 940988588 1250 940987338 940987343
    0xa0b220e060a0501050f040b070c0f03080c010b19030201050c1e1b06070201090e0712090f03110c030304090c050702060f0304021507170d09050a0501052d01050f0a09050112 76
    0x2c44100184a50080050b1225259640c03500b508141c5003002c0d4440307a910410088820042400011607040301200b0208040c5000c0e0714603940300e00d080c64110382194080c0ca42284034882d110605801031030340c05200001d03283c3c2880c055441f0b0b40f0351021145000108000c0c03140d07018503040d1010841078009056800b080040070b00e4000c07003c1c0310f02406001d104004000e03002420540c401c0c00101d1107400180d0300050145800d1219480174155001140ca10314000c035018100c5000500078541d00c682c09842441000c1c0250500e40c0c4a0380c0000d950744100e21600103c070340c44405c40011075000e80e054403002c0d034020303004503030321078180c0d11406103136000b210228400e0303141301c604c2100e507018203081c0c550f42648074404055042804416026503000682002d20342c2d903da203000710003c2e40a0103c1401e0901c110300124031424441d250200b4880501c4482212a0620f0071028a49150140050449078203903001550201603c02003600c14030640c1050441504007400010514032610440700b0190 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 940989838 1250 940988588 940988599
    0x50120011b120e030f070203030c01060902040e0708090d110a02030f0a21050403031206030602120115030911190e07080601091203020604020f060d090309180207020a0b220e06 77
    0x24070004005040369007201c40000103500502a02c040c00017064000c00000c0d0008003100d05015085c0101c5082d25016003111101640204040100c084440403a42d04600b413414810014504650b07401d507502c0000548004000480100035815203050100f201d41e41c4d00501500c420344c41045000703030703a0210340100715130440c2508640380c005042d090000ca06004542c0e80d26140ca40341d0f88080700c001e10340d0224654002d030f5078400000028158030040c882c0c0503001c2a64040d5600d4590641d040700ca4440c041004e0501300b00c1c0c2440000d8041c00980d1014800302c0e41420810040c0c08004840081a00241800200c1c1c00a00001c1ea03044001107220707036026a03c0e20f005988541c1084001e0034548402000b580c07000700840d0040c031385400081d442c104040c1415040200c0511454241c464016090300884d400c140148800007841c1910700b105041d04105524103002c507408900203162034410101d00400203c1c0802a103039251001c5061402c003603125000480e07d801b400c02d05058180e0742c461003070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 940991088 1250 940989838 940989857
    0x16080c1501060c032a0501140901020a09230904030c050d0c08030c0c121305010201051506120903161a070306140d03020c0306010e100e040c050120011b 67
    0x200c0004000038140c070160754509a0b50300d003580d82a50044809071280c4491580c0119100c00c1600d00c482480d501400b450000c02c401003c440440340092014007800100d900401c07800c02c03129000441c1c401181d44c000d0310310018003003c2118207000d4101000d02030344031060009200916510804072030000d80184207841c00d000c224030081c3c58072000080c0050040340c0510025000303103500c2000d80202403801098620401001c08852005d60142c0b80c000c04400e4075100510080d42d091046940c8540d042d00d60030320b010401e0b0001392581c019450340400d00805c41e80028400710090066800080c107044055100c0400c9140081102d05071861382e0071034560034000101c03902d200c5d00904048032181d055070035414030040c1c01c1c4108440860400d6040d0f1180351240004d0780c508202d0b06001b06200803d83d5103504142812038400c1002c1d030f005540da400414103200115221018400c21507209007440c01e6149074a503081c10000e00502898075407540b0b40340c4050025a4242101c0c0c1c035030324480e40c401406 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 940992338 1250 940991088 940991113
    0x304090b0a08031806180a08030408101a041815020702090934050a030c08010605060403030f0516050a05011a3f2a01030504111516080c 60
    0x61303020f5842404240210f1050a80ca0b9080c0074000b13040030b000c0392949901090840c4c0124040300c0d055488496241d0000400700141801801580255815842c090010f002c495443c200401c1078011554071032603981e5503405160303800e0041025141ea2101140b1040150400d5000c000c0d009030000340d001d01800030004800c104003280076009585200350300d51817041e030888014041440703082c906203d03160411000c500c0c1d9440c1c2041100440c400c89413a01081c0c203101030380f803d44d43c41d5070251340580010711041c07000a401c0a0b490b000c0b44203504d4002d85485542c1340d40381d681d84241d40c018006005907010070090113019003110701004c0c3d80d240f03240585041e0005108103039615003220003011024100e400d000e48009040039024800d07260b81b000628055405882c01c101c410341106200f2108040800200d404011044c2d00e11a001d003030400c4cd91906858114900705100c040602c201050b6007000d454100c200281c4a901da090b04c840b040c40021441c01c08010792105010b01400d11602e42c03403030607 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 940993588 1250 940992338 940992343
    0x9150912071401051c0c120f020310050303040506070605090a0227010e010b0d2004260109200316141f020a02010c0519031710080601150c050304090b0a08 68
    0x3541c041700c0c066113420a0340c1d07145141c006c080184200c000c1003130800041e415904c0340e014041da4941c00d00001030703a0342000102e542480c0100c0e803195001ea00306010400c15684c1c0c2c041564499500113002052a40e070355210382d13082000b40c0f100258400519140500043c050b1284140007110181403400c241c0d8a60700d00000405003480b44500c90341c0704002101c04824150860508035080581c0c10711300008100750355146822a802c040e83e003104c0d142d40840e200f0703201c00420002600400080181885a460b51a0401951440c4010cc0c50410101c140f2175201044648002010005860b9a4a44980f1400150550015401e10805916040c186041c9294810818400007900100301003c8940d0043d12840e44c904000e481c40d015142e5a1a031b9000c040e048240018802d6032900600c41d003465403009035200152003601d4205209000740701c150b00014026041d42c49010480c5030503c00d5800031a046140050000c00034000420002080600c54208100c440c030101e80e1401e40b02e48a040d0583d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 940994838 1250 940993588 940993597
    0x3060f050606040b0a02010603170a02120304020913020315010803191d150412050606040c08040c06050c031b421801140708070c05030915091207140105 67
    0x56202c0010002045a03000d030800502c90f0105070300002c1703150355883d114a0b812052248001018840c000703002e801680e41400032201114400080e2801e5051540109200d142d00900542c400008180e5840556604101d903c8030000b540c10b000740d40f507031644010340d241d410200e1240c8483c884501c13811013880c09040991820035502c0001c2c1d81040c500f000b0401c4080400b1a4103400070703010003000c6840300492400a4515020350003c0491742440400d0100710b4a4041040040000308424007000450150302c2c0d0702142e00d20b19000c0d84500650350345900318071500341d217030500c2910900f40702554000844d022000e80c5058840741c03d0107494040078003400c0b551441c11405801f511100200c0d9841da003085681203801e06504a00010024020300d003100d003e0b15800f6040d510072401c105805601219155100c40b1034079280e00f400c601aa40d040e500d008807100f4500c034000705050101c54605400030b84411200c010b01c41150071250140880d00e1b0001c034044c3c40581c01349038040d80c1d050750207802140c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 940996088 1250 940994838 940994851
    0x14060303210c0f0f0703090b0301180b211605063f0103080904050a0606050405121005100e010801140601030b04060e100e060d0b1306150f03060f05 65
    0x700000c0d818402045801000501c1c2441035041800011840c5403c00050566008422010f541d66851820003815000c066400b442100c0750400c01482061480b800d940b400e802c0d405004510f40214030001442102e4084410800c000441c09502c52010001180291100b40b54464030030b1a0300c03101844502e1241c009201102c054001d0380100001d4609000000c162440c00c0303507000074061010304814801c082e4800e8802131000702d6885142e141a129094000c560381004010301880c0401c05400b50260b449118031030030004035000001d80701445801c098202500e4100418a00008444214034550280721100f50703141e0700109030130205100340b928100c4660061345280d0386040c01180508455048980c0060b2a0100024400ca42d104041d002d4440c82208102281c2012054440c1c2c0d08002d01c1d03144110101640403020880c01c11810307400007030766485220488010308003130000d04050880c240e96246840000555001d8078800d010650388561030a200d131030802c1207603600350355003034420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 940997338 1250 940996088 940996117
    0x60306010519090c03020d0b0a0303020601060f0c38010819241a0102012313121805090402011e090f15090b04140402071a04050114060303 61
    0x41c4194901040c009004000700c200310303940d0b80d448001c41c4080d80c4200014a022a070086107501c9000c40f503005030101d0003401d48201c400c00b855520020342e210410301c183d1062000050840c10361502c04c0080c00162500b010480e109910a2103050000c009000594020f000809001d451440c4040c40e03194102d903490002040a00c0c00c0340f01d0358103001c01c480401c0b52090f412232901c5500c1c0f01140c3d1000ca49003c10500040e0142c64910903040b4107240da02c0d203c6c1103924103005041048901644540d12801085070100241d032080c061040c130004001d80548803034043d640d01c50019a22410f490700b00b4511042100c203103a6650240054a042904c0081c0401c40d0340c0c4138a2092400003da07d03500d8101450420a01c654403141001000e8454202541c848107240c0408803003504500004001c0800d841d0092410745000d24841a41c0384c000b08080c071035038000074864280712150701801c5498074490f2040c0da6500b07091170320310b00034250340ea00054181111300001e80c0390300d8040150b540360060100c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 940998588 1250 940997338 940997341
    0x1106060103020901030b1306080d03091e020a030c0f0f090207050319020c1c0507080705031c1e0804050d05090f01030f14040309032105070336050109080105060306 72
    0x6601940040d42d00c42c4c101583c5000e52511981c40d00140007078000150380016880341001e60b6107007040c29501010003494107081d488000581003071604d48040c25a100643d88005192000540e00c8071a540050500780b0f007440081001045c4090190403a554820303180d2085030f0303c20340310f8140e004541d40a0712640050150700780306042403502230074503c86441a10703d0504080001456010146405000c00892003c01420000100500b0024140d40002031140360700c2e050000360b4802c05028140003c04811501205a40c09110080801c40440d80901000c000c404002000c0340001c407001d5440b88100703880080014010030482d211001c028002c11104448800198090f004504200d40c1c8940d5038800070664110001e2460b02032482650b599981501d11304264a0390021030154902c403031a078440214001d5081001c8690455142c100b4000c03404480381008040a50078407011052417950346840408802404102c05603903090301c4030b9002035100e0b5001c9003241d00481e1060b815601070300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 940999838 1250 940998588 940998601
    0x80a0201051911030d0c02120c0c0d03050d0f0203061c080d02090609030307050604020108160c350a030e060c0d091e1101031b02070b340201020601061106 68
    0xb212003011800d044181038030083e045032542e40284410004566101001eaa080d541404010741903051500f41d42c0c100107400300001d03254a81a041180304043c0800c01030101030207241070b612002a010004c000f085281000300c0043c1d40121003c1d442021078400746038480d000c90f00320340c0210b80c00020007800d2400f4400418000d501c00c0740040e0b400703402802114025542000103010707461007a0090101403d251002511100011781003a005000d04542c903940c942e0b004032501d003171541000c0070903007080710540342568003074002140c559248903c54003040d40d98107580c0182030700c10fa0380e542000f064000806580d2140c01c10340e00d401d103800e020440390b4135001c01c581000a48a000d0710188129400503014400650403481040700d210140d204070340c8042d03825214548180031038020b50701c00b991480500035120031030b60041440b01007001c16031524400c00f42400010806002c425145004094841c100b04462000b904a00600c41d420012800364401d00f603480d9603024100041c45103840f0340 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 941001088 1250 940999838 940999867
    0xf0a0b0a1a040f1d0a0606120506060607080910090807090e0705040b0a080a14010501120209040f0c08070f08010510150f0509060301030f110907020a030e0f030a140601080a020105 79
    0x48505041500d0b02010507031303030703a04480c2950b84090480080250041070319207202503400030b500c08010341258192010200341c0120b9039941c0b04404403125503903080030303160008083c000d203010290009004c071050010681c201549100342d0b1900c07021600b030b05035180340f040160b440340b1403840344a4000c02000c2019040076040588801c000801901300980c88050f507a2a08220027015900140c5070700e00d00e40420000e20419014004441d10704e0080380240c5c000ca0708103040600001d10540c81486e5540a1001c2c501005028042440c15102403c4e51441c03c42c800d074031503010b130f690325528041c0400c1c40c00748500203601c00c842042003481a1802513000c260741c409a07004e41c4a00f481001c0000d50515983d1200960203540316070308a0322003000d207061090900440d1152280200da281c0f0900810030340004007500d210303600d0720342401c4040d03e590226003600d641c0783c035090f01846042d41c460104000c441002c0102c50a0700c00700d40b920303a40d800a42c0da590700090400381c04580d04202c5a410f403000d2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 941002338 1250 941001088 941001101
    0x2030c1b0d031202040b0a021b0411030718050a1409060d052e02070303060e0f0705090d02030f0a03170f041502300a0c1106180a050f0a0b0a1a04 64
    0x401001410140d035505500c0b00e947c0712035203480050f04800c41840e80060924402d82c03a102090340c0812405407412060312003444050301450901000000c40075000162406c07242c05400003804c0500300030350b50000c140840c003020f014a8411400d0000080f80d5082024603c81e0058021009104100c1c41950403030841c40340c02c007407500a003800c48c60031078881018001003a040348a0345d00010154682080c000e005030001d0720007001400361030244144998803c1c1625030141c401c645150074803200703100084ca04a058020300c10f150180250300c00500da04440f40403880025801110005c3d5283d80c06140703241e80c1198020501502c7d160714002810503640944111502d0f890400d0f41c90f81d4150843e01080c0384800041c4507002d06a08101c8034201e10300032100c190f484c90400c900b9070001d220700c180c1c5901e07004002c0d041e0110200502800048104080d41903550800d01b554441e2110700b007015102d005448040d1070040115000c11005001407090712401005800042c090400200810000d400b4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 941003588 1250 941002338 941002367
    0x91409010909380115120b03010204120b1f0612020711060316110c1f1809060303031112040f110a0b0c010b0312030a05041a0702030c1b0d03 62
    0x42004101c00188500d8644520041c1c2c0308064100344800b121050083c2ea81604004024496a41c00d10500e036000001010100e81410011440c60b2004010a00a000e1580481000d09902e90800c00703106001450700d0184907410030030207000554200e2006228000e1081c0c60020b0080c004039608200c2e954090150148100c0c0000c84072503003032000490f660800c0d00c81a10381000c10083d0248503030440b0401050586060141c04040503070000102040030002400b441c07000b40740759001886100302c1000c0c8030b1842c0200c0c040842d0b40c81c0c0601704006d001c140422004a8034040031034600501783e4003901e610396011868580d040c4d03156178800030351100c041400c42d0400d1154000c03a03a035640711100300024102ca551600e407918101c869540c2500c078160101780c001d03044100301d080c071900b01c0313002c89912410b010004601030f00d4528250303000c200b020544410016200c0f041c049595804401804010789900840b1322250021076040c55031840e00e0081903020f02100c40540c0003c0c0510f00d1110340c1030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 941004838 1250 941003588 941003603
    0x50301051e091c020c010f0f0e09090c06040f0e010803040f0b09030f0d032007080a1d040c110607140d0911100e01090f0b180d0507090b01091409010909 67
    0xb40c1c800414591075541c0410003025800c030311017451503568002d080507100c8010340382c601c4009261500280c049240c0b940c000740a02c0b01e520001307410074410421081e403814003400c200d0790340c2e40c2e0f10340050980107a40900300c0419220342c00092030100c000f080d10240c2d40f5824440360305500e403071041161a440003000c6074140c002d4140706844041c0612103203401c908076803008541056403030344260750082d44582c0024082814029400452044030039a070b000002410030bc00ea00701c0c2007803420410104104100d80c0282440310100001c0e60064180c8c8001c40820300310390268a40d4041560710003000e5061a540501c01e001d100c2c21039640350000d8a402d402000082440300300034000c184100b5071009000042841e0300d0204510b542d20a44008c01082c0b403c024800e41400c22002080380e1064411510780c8000d00d82c099680c80d95145882da000755803080844100d02d83c1c0e0100b16014080c004412800b0655554000920041074600b048403a1801040290241e0800200c500140f15990b800d0f980417 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 941006088 1250 941004838 941004853
    0x140d170c250b0115050705030904050603161203120b0f0103181e05060c0336060f18160b030a140c0706050c0403051903050c030a090f050301051e09 65
    0x70148180c50800780524209105981420850b4652030304040c1039a080080400102000c10380100c19507802510848011616407100d80003e40f42c0000d40703102251020244d1030018a034100c6110b001200351098442c144112000000704003107417805603403103800c0450b0340740341c01440d84250310114142c2e9100c8052405040310340c5400a483c03142a42e54007030380c03500302500c3c818001c08010003580b180004409030324600c2c1c20749245541c40c110f450703140c0803040e903462003181842042c05002c3d0300e4445481203034100c1c50045480b00e5906801d4603122a451080400441045404540c1000e00840303203580c07040c440e04c0d100609529520081c00d0315582c41c0d441c10341035040038501c19101e00414400e8105601d030f480c00d00b403010840d003018042540c25101040204002540400c02d01100c006143c1200112141c03401c007607803d8451104400314a0000250f158401904080e00740107603140c110303002010b00d0f100c80505080f40e90584020007640c5c03903020740100c0c10a9548100d41d1010100040c2d0380034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 941007194 1106 941006088 941006137
    0x209060f07020d060f021801020f03120604020f040612060506030f16031104060c0b010e012403020d06140f0d03050919050d140d170c 59
    0xa504042481402c0d5616252034420841d0449001c1c04104244000c2c8402580510079080e085d46140750700b040e00d940700080d522505a0414001c524008000c041c0411344c00300108120b03030141e020010410030303490301000b5200518241e03c0740c500003900ea44240d016074205411182c02041d0a00400c80701e4110306e0205030b04001101c4ca551440707220500120040c0c07448044005c2031440c0024001101c42d0721404c65070400740107160b00d00171a62103002158140074280301d41171031424180d0791040d4400300c0c580c0c04103101c8811f00b801450001e5064203001a00c2c569031080240003000d0040c1d45050600d80014080d0540803282e884180e00303565405000e5004010360a80100325244003a04220220200000038107001800191aa4180e01e000e50384840e403030714212080d000c1c001c40301c030140340a07801400440f0412190340b00c8039540c40980700f60b00d0f0081d440d45a601400c030142200e4 = true := by decide +kernel

theorem cover : BRFrame.Cov 940827338 941007194 := by
  have h0 := BRFrame.cov_init 940827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 940827338 ≤ n) (h2 : n < 941007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
