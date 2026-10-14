-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3669
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:20:24.7728+00:00
-- url     : https://prove2.me/submissions/80f9ec25-29dc-4652-8d0f-d147fc8872aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 659712230 ≤ n < 659892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 659713480 1250 659712230 659712293
    0x51c060b180420090a020403110d050715020c10030c0e0910060c03120c0201061701020c121614010c27120c030609080307082202130b0d06020403 64
    0x3071080c0e90081e00064902c0c0341420080c2c0070440c40d031a060300660302c4041101400000a543c1d03003d031042c4c4c0d20544840250100745010003900c56940100180b596110700e0080c00071121008001c030440040d070040710203595103000040d2520181903c0d07070002a513100300800510f50f01502c1c80c031030001c01317440f1390402d41010385402c0322154882c090507080c00f0010201d441010b01c0340000300c480c002404820010881d9900c0002c0c0a0720081c410503050082d04140c60300340c2c050603c2140c41440b1100700404180b4103d00c070920494100004141000800c030480c80c1c04101e030140340c01542d003030300350001804400c4601c0141c0f45480c145003421f1045100350302d2811114001515800f542c1d01c092500c10203c17807a11b46080c00b040341d504001c0102d41841100390400a4410203075014204544585001d6514080c21600780741c0034141629048850411b0040941022030100212220714080821000c00d658085a88050000d0007201d981c2d40c00101001848140340400c00b182c080002d044030350341c454 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 659714730 1250 659713480 659713519
    0x5030a021b01030b0f0114040308040803030124090e04140a050601050102010c09120b060a0512010920090f06040e010606080411010306030b220f080a0f0207080a0b040c051c060b 78
    0x200d070b03080b1b414000c2e142551442200c00f00291401103602103000c0c0d544030380394040c00e0b80305d40081c852444031607207100c103645c84641c00c08003c10004515076120181c0300d2501c0172520748540c4c060710a80345040c040b2854103d008060003020200381c0248010181545004002421074904001020421940b003100303011240c42e005450701c48981010031040640c41e0080000c1038800264481940005201c40140c0ca070030064200c4001a40280c603080b03418001101d900414103055040164090200720008160110a0659a800c0b10014100084a01f5480f002c142164040e030400c0003c140c0c11400c000070480b0210b54010120800c0c60140807d0346503a8441440c040c0c0030782000ea2070398200a80d182e11580646001d480c298100d952403032901140c6c00d104000b80e0085400c40001340840032001211800021044c003102c007000010b02c10001e0a48030f820804001410031503c01c404804000794560345c0c10591452980c65098102d4000312070310b4443c0c100c0c0c80d08160a4007990b505580d283c54010f0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 659715980 1250 659714730 659714749
    0x6111c090c0803030618090f0706180b03040c15030e07170708011a090c09030d0801090f0504030f030902030c09040311060901050f01061d0406090b0310112505030a021b01030b 77
    0x2148040043d0342c0314103444d5030800c05a90004107441c4106440020160307402f05100300b44000154824280c00e8540300c064036107200880d0040c0071401001c408200841c004400c0c000c02140610700096881c0000d4602402c2488550107440d1480707964201c00c4140d001030001c90001c0014074020024134261a2848a04980915055224451000000d420241305034112454080c00509a404446404102030104102070080303110301c503d0042c11960207504c500c5124003031754064403800d134103c00803202100a0b0580078012070301405181284240303501d0311110303540103078400c1e02e503100d40d4050400f05034034102e80207000d07880c603031b04210030b11100035800c8003c90f0568444d40703400d051004c2c0420440c14019800184039400034608640090203068580c40302504c400200c2c180e501e0090480d00f0201590907003035400e4140c0c0401c02548000800c0c041c1070b5a200e00c821402d05034002403648070b150079500811840c0c000f60b0040c2052904565000c2c6040603903003c2405d0421210b0031400120301c1043c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 659717230 1250 659715980 659716009
    0x507122f041103060d1b330203070201020a02100908010e100e150403080606070506130212070b180d05060408090f1516030306211a070c06111c090c08030306 69
    0x31b800c402c4d118203001840b406802500318101c2000d0500f03901c0c82c910350b82d42c406030780f0036820360f4400c110040050700c0402100e42c0943c0580c0181110382043d000c00094003440001c03078080c031100c00d070002042035017030180e00515149000a0140201c401031130000361060742a0040f800d80080c00e14680511b06e420780b4641158040c0703440a080d6441b4400310f03245100304540a05a07214000410400d5903982034188207080c826100040482800a08240d03910701c00e00070319440d614107108108104c0c91400340384036440c80061020012480da070b1102c1c0e050281c00d43e01a1070f401d03400900c200080c00c2c031110000c44140c0c291103e0700c815480c8000102c450050b190a4201800d403100e01d00309061190300280080c0c049a81c80f01050440e604203141801c01140e0103c40b40c0e1075041150f007503807a410001c10b01c074003000d403144525001507a40d01401018420a480352020051000c481e05071202c65002c2404006440002000201c1d400c00d103800800c01d900206182d0710410030404261a40d299040c0a403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 659718480 1250 659717230 659717243
    0x4030503060607140c011806020309010305060324100506030f010b0c1516030510050f061c0c050d0b030601030215072d030f0c0507122f041103060d 65
    0x30780350140002c6207071040c010007800815a070f45260064450210311680380704426203d00b0b0921100c519482c44180c0288101c001581040c4141113565000790060707a4001c0006040d1068403aa042a14544140d003555048030500948104084081101d10711400b5102c12a295070031480c0c542281040d4003014003c8004403070340407034910360b1a10200302590340030300c100b01c4044240ca4480c0030110100b0503140d2050000b4141004900d0003107032004607400307444014120025601191041c00b46079404009c030020206240010400600c10512a20032041c440d560b441c0c1c1d95498180d0700c2c8d0140c5c1d40030285d1034803a410a000420050751041214a089416002140d445080764140a0221900481440c541030120059118180c0348900c0c1c0d0a13402e0300c65100c0c1c0880703550000048486009d4407500400d40c0e4001d001c180281c0072203001d000a014490010f2503600000710905070414496440d107256010007180e10400185401d01410b401141c0040c9101d003186004000900c002001c2d00014106 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 659719730 1250 659718480 659718487
    0x2060a0c02030d110c060c07030215040e0a020d0b031504031d090a0b01030e06043c050c1c03050403060b011106130201020111040605070b0603160308121509040305 72
    0x21603014008040e24680c0041c10f9400b207100110300503284004a10750b01200c0e0041000400180c602142a207a05c100500020f00484d0308550074051030703903000c5444800d0b40105110000d048015011424030500c2010307800b603210007410300c031001541d00200e00310b031103500160b400c43c003c108179011141d0f01a0300b51801c3d0700e0304100e82c1009040da40d01d45c1e0254bd00b010208040000d442e405801c440c6100400382d07010040e501d8007115094036400b0039240101245003640240e40300e0b00700488109600c203460f800000d4095441420840e542030b240d0700032125500070b081c9034001403800c2e55010781481d260003c40340c00140305650040045c856800028074007517499504103002d911030070a0020f80c0030004122a46810302041204180d060003008900640c203002a1002110300300003950b048030307056140e090606000790380320304007507a0040065400d44a0b0380d940c141c40c00710504203100114002d1001940d25240c101c4151042203004103414244103100000c10416200c40031003d90003501458425103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 659720980 1250 659719730 659719747
    0x302060a1517070315090f060b03070906031a070216060c0503090301060b1209010b090f0a11030a1a150a050d02041208040e0609101203200c0109060c020d0206 70
    0x181c040c09a0403440c50303495550722040002d080012010142d9000c1c3d008400901680c4290205440c880e960090955540d080110001030b125004800818130040c01d844e40d05496440300c1040311580d41c81aa960382108000100c819409190700350068407a01c054a1840061024041040181d00c944070410851001d05414004244150b13010440010020300505540301d4801c2056004610a0b070118481c01c40443e42e40001407003080100307078010b002c00500742d0b2181665691284000d10141003d9160315040e040704580000075440b40e0204000003c0c10400380c092142f04c0c8403a51281801442021682c03032181e101101500c0d01421249002950b03031a034030a808010303005640c03154440000c201980c00c20481c944002d003007039410765000440b95544201c1000b210790740540e210b103e040980b83c0709020180d00c45000b400c1c031600a04028902d001c0da13000503c05500b907045600c3c4550404075a9586940e4440d6810004103018a0400d2240103150005101014100c030024420140060b1400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 659722230 1250 659720980 659721011
    0x10f1d0112061502030403290a052223150a150906061e080417030601050702060f0d0c08010605030c131701240e0c0a17041b0504090302060a 62
    0x81c007401c03040c660f01e14209080b46000e5900c0d0803c1c041194070112039807844617256920b50783c0348114062841400040e89554038a58018000030300304d0012045921403070010100b100110b60b0317990380f080e0500079884944410201d411920a0311014560b0000314041031441d10f01c82080340c07c00104074000074221101c101100c0c0c500c04550004c21224100980002c4040e080060340720302c170b401d0b4024801105840700040303c07820381c1294010442704d90410308984544000d0061580400c046c10301d2498040513400150868200c402c0d40d849600000444140c07020706406a020003200c2070500105035414100050000d02004081d07211002c40811040701440f0100d183c14014202440e030340130b1302980416254040d10f545080c201c402d50b0210135910b03c640051500100303e9100c44200c1000783c58410300780810f540441c466070304010403136155000b049040081c1601440c070441c0b0854000702414140c0440300e5032544100d104034501420300001c650041001c607844055180000381c01079842a41c071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 659723480 1250 659722230 659722241
    0xe1f05091615080a05190902031002040b0309010c020d02150901060b070303090b07210203150918010f05040807140a05011d010b0a0b0703050a0507050a11010f1d0112 73
    0xc031a07248401100240095255400b031010b440d007075403507000b90756842c0138102c25610156407940b02680c1c4050900e84203c2c0039400043c0003840101034940e505c0800c01d4280a0740c1003030f00111701d040000018070489030001d101c1c580c5102c1c00340c0003511800e01040e40294942c4209100c18140b00a43c80006080800c01e504c110054030b42460806d45030b00560900500601c00c84e40121580c032010008031f080e4070b02078010703103407014a5103a03081440c002d0100500c010790406411035001251810741c202d03007a43c40300405889002e4a42d6a000207001d4a402d446c251100f10052010403840e00003844040f0b4840d0381110002900544540d05298052402c3d91519a40310005019546001d07122039903002e4016010040e5039410b002030084103800801c11580c1e0103244076003c00540100034100009006102406603682903081031810400b07151540c0341403100c4840c088800315031041c0059455078016030003800d100c1c1d03545491010b070404c0d2810000514240e1020303070b0500039030000c0043e41c42d00c682c110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 659724730 1250 659723480 659723503
    0x4080d0504080a020d02010e0c040c120504241415010c050604050106050a060504050307330512130c05011209050f010504020f060c0606100311031302040e1f0509 71
    0x10001032400c1d0610b490160800890400180502d04600341460310500802c1d9002c2c0b41c0c40d000c1c240c5a5102c00c2000000d0090600359010302c69030120b09850b100c814030905100701c1c0110382800c000f000c8240c180c1ca07800410345040aa0626005400c0c00341041c003204558000102c00c0c41500e81c07100a40180e5140c0003d202c02845403003080c0070001000010f400a0782224002d070b0320044d031aa100ca009030b40a005a02031240c25a00c2000100603503001e030044086c280002a18103042d01c1c40340601d02981205201d100303408600b0000b841900600e28801080d40030400782030310004440603654011a148040c86014104401c00203013225a084941c08803120355417120440c1e0400304076180080c040d02c41194280e1294282c191450703000c0c18030701c04550300990070402800c8180d80b403108000142c040e84050341c0c1015564420b140e4107030001030055014200c0c000550350010030f54070400041e1078140004084941004042d100344404040b0100d04c5000e200c480030070140c0d00d21481c5403074403840001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 659725980 1250 659724730 659724757
    0x6031508010c0903050115030b1504111b070b07031e050d022701030c02030a08130204050c130506040b0a03090204020c0105010b030106030e0102030f011401090b0418140c0708030408 80
    0x100b16032190000561400c42c2e1084009111420300300b200494030000034440071344920001400101c502d24484000825403000510018035003410545021a03a008405801c0380308550906181e801e0741c0820111004000e2070030010f1070008195402880141c240b0300700d0318941910001d581c003050141081d24080c2440c400304546640079040c0f90420b030801c0c900e807040c0085400e00b9403d41944079000d032110780c1d01d00d40c005515000b00c881c021a152034008180d1100e00d80707804402c000581d035500a01d4080d021030320354161a25950701003a008034076a82c0c00b052140c101008200492106801981c540410794100010380c1c81035800030038060710a0401c038030419441d18001142c840d800c1d0010314181c410b560740c208145401d580000d0300700c2c40305841038209604148010020581c544912070b24025041c504526110340d500a10003454000e40c1002e80c0d08180c8121122412045206182a0340c416011640290402807100b4416110b03004c00034081d400001b0005003131040d50313001c40380506103440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 659727230 1250 659725980 659725991
    0x150603070504061101110f070c05030312040605160f1103090301140412031503060504151b0f05030f013501051806060906010e03010f240e100603150801 67
    0x10005181c1c2d4400d00924021950305106401002ca0512540941e0f407000f802d42481d04002c0514100e00c0d8100881c11a000400a440400c5e940c40a0001c0c1513480e070304160282950a080c501242540c0c002400c0302d0700003174000c1407010030a030f00080e440f640305030b20b0900c0644200b90404030313130a40c406c0500d500d40640c00c2500c1d8540b207204940545105600507162004400d50008041701581c00c40c943d2041d21402c0c3c0001031000c1001640200d80280c070030302d04c602200c01c8202150b0705480b011040b007401100c00c5110403e556400c08104502c003091031600c0c03865480d00b50441d030404e20040c00713915600001668440420b8003e00740b1609080d580020b07441500e0140c800c8030313020709002c80303498484138105140400401d100080c41e41c05250020301d80000b69480200442d90b031044888025032564a071f6a100521003440c0c0b03c0c40407905408102d202c003001c146544440481d050ba03102000100c0c07028104070310760171b010b05000d00780c0f5540c1c80c0c08221401a200c0000c00c104154025901d035501c0c0a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 659728480 1250 659727230 659727241
    0x702010914100606020601060e0402030c070609050c030c0f060d2414040b040b010813020f0402070c140901030f032609162106050408213408150603 65
    0xc1c1c11a07141d0808082440f0194440000b01c0c0c850030288140c501003010340f008901c051816030042c540c00784011152a00304000c039154002136543c010310075070307068202c921100110700f824060b408002c04103440d80e00080d11050302241440c45800c0815420ba1354607078240b10400464920b03030404500300e680482c1040e0b10b800e003282000034003800051045141102140190400e40164403035000e05845100290740c0300c0d0b40d200b1b40c408a42c1b00807a030043e51f41d0a07050033f03030b9154800742448a00600c00c410300182000c80c804174004a43c410540700301c481100410014003901c1113141e0b0389605252036440c0400c044540c929500c0354540080d05442c0050410404402c000f8206001031049020315208903900d11881c2c4280485020384210360076080641c030702059581c0c1246401900c01c1400500d006908840c81c16444900480400b80480c038006108940c2141c80e100a800250f041002c00d2000b101e41b0702c0b145d0300700c00c022018248030b500c5000450b564414506404441c0300070300140c0c1c0d030380b911 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 659729730 1250 659728480 659728483
    0x702040207050a032a15021c060b0d0b090402060703050717030f0609130503220b03040f1a070c02011b051b04110906071e0f0c0f06170f0702010914 65
    0x5145411070740168901d42c0c0040b02485552107525904441940350b507600010851010351b00a00c01e0303840c81082103c0c0a12311030520b1103000c0c010848000442e03101c802d48507140c4141c03030719404070310310421040d802c0c4005a43c1d240100d87c1c1c10355050030410fa44020302d191000c2d4003148443c030300400c00c501108004004000c80b80c420b21810088482d00c6d666034504455a99442c0c02c00806401c2e54400e0042d8000c400c80c445103034000c003042c107180101c42a81c82050322060340c0704a030100c070784035401c81c042410040300510200480e140702c03044821501d86500000c0000040440190400094101c0248074001c00681c00840136080020740d69862652110100500800801e85005519045003000010851000e4402d40480103001901e016940d407285c44500b45080d40c0c80c000c2c02a0703180c0d01c00006019400c107900240c0301d6007100546c50301c1c05140545451041d03020070180400164168401000009425400031900140503203a49403400c080f8014140480f0050a0307a03110462003107030440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 659730980 1250 659729730 659729747
    0x4031215170327060706150501020d020d080c0a03020f070c14180114040e0d03050402041a010c0b190f0e0601050111100e1501150201050a0c12020702040207050a03 72
    0x94a69420811550709051030707590780b01e08104450707a100341c40e03009024550b61084107460040c2c000c040e141030114030f8451808950705101158078440c0113060030401541c05200140c0b01c1030280c0043c0000f842000d4014101e00d20003044464171560008600118074025415650b9007100c00c51a603031a0b00091900c0100c0700c400b8010f210001c0a489445410f600d000c4242104240346183c80e03190991030200c0c00030103104a508002d40c42510b400781c1e100b24541c00c0144ca0851111a90701103a0fa00700748c014041210a4220b26a051488050342840e50fa600f0004035125541c1c0700380b92a40c5961886042407074a02c49655900f00c440c00e00c2261207032584035400104017441c4007015910f081c2d1380c0d68019210b0403c05000c1d5219508004504050005258070685c2c1d44404081034071105c800b05880d000200c5801d0b003040103500d6217050441c2c0001e909114255008000c130004100e4007e000001400b08415404040d09668001903840115102d0f40c058a07550740c4d2100856014811364a00035290b0b18 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 659732230 1250 659730980 659730989
    0x120f02030f0f0c070f140a1209082a0112060605090a0806010812030a150b070b0702210d0902131d06070c0305070302010b0a06020f07050105040f050904031215 70
    0xc015000b0a11080c0b5064140303005045021540d0719111880d610b034855920b802c0d50564079034000e0b25549501c10010b0000c3e482e118415001003445424041c009003000d000b035003107000d4070782c0302000c48a5602c00c0110076442c11104003a80710000020a00100d80808580720100d03500703400c0c40d20000d1410b4200c0f02034920b103034044510844054503005040e680d032800b440f504481e54090070482200d59207005c02141c100030348050101c0c0ba0b403003c01c100c00782e4141551288501303804c001410401d1007101008190800c5003403018000c1c03400030941500e2031190040003521000c500003a00e1152a03071f55400010555405400050803018040c5a40002c1c9035000b01011001e6001842c00300844020031310b24400c01c010380300c05040180d151022070f101c1d0000c01045040d5944d598240d030569a40c00d4803040209042c0c1e0040070702c00c007050482c60070805103600c45414010240824030141b50514040c0c000d0b1a0281c0c1c0c0550300b075442d42012101584c40c103021039441843d003900c1c1382c00600c00300451021b89 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 659733480 1250 659732230 659732251
    0x16060e07050f060d020f040305010908030708090a210216090209010e060a23092e020c060d0203071803080901020d14030f0402010915020609010606090605070b0601120f0203 76
    0x30380c0e90020700a102c8110504164007a0040028408102035540500000b90380e494103942050b0700c81e603440d42100c1044c10184c0310100b02000700002c070741d0300c981003e40c0940d032070003e0300c03240744a0f0b070300d09000c1c3c4c1500070108000c407061030510070340718402c1203055a440401ca4035014000e640f200f0f010000d6110354140303030002d81a070340900000d00306002241c3c403000150380c4070f9410250b2050a459199101d4210000c24a0108000341c0070790303103040034014514601035042952541c11543d0041085001c0c04510654014400c400c82036038035882a1448082d020034090b949941e520030032200d18400345000c0034512401c4101009102802c4007030145051f00f80c085070148003115100703880003046444800c030380440400008516041c00001650464410306203801100d8660380294a21500c81c240c200c0145d01000403c4050742c42401008000c11850911000e201e0803d07070010554498031001038200f41050010409a911031034a074002c1a1080d5070400140810100c8a00030794401c1c3c91100381d2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 659734730 1250 659733480 659733493
    0x20d020d090b0a060605183115050d0f02040209040905070f06080606040b0703030b061602030606041109060a1403040b0906070305010f151202041403190c0501030b0616060e 76
    0x10440ca03840340320240e0711152643c608065801c40f02030b1f4105680300c000360308140303c04d2000300402c1c0395403403198003250310202e0322401001c882140030890f5045000d43c0d2601d583e080c4104100d8481148400125401c4408002c52115030300105000c1d1054101241e04a07143c1151081030000105555041d80c1c504400080e2043daa540c089034844004c0d0383d0180c0c4030030100410419848180000d1410910a0401050072210440081d145400c640000130850790100038a60440c9030074000e89500107000c5508101c0e100d01c0806551490103000344442c000c0ca000100e0450340b60080c000030803108401028103607a0f140c1454449403901054848540610580020450300d9010f4080d4506a0341845c2c901c0c6000d03440c1407451448080d509200d081801454031084c0e0780350205000410280c100101e1651465010720309240c900b001441982c0003081d82200803c00082e15402c0d01803c070b0780e0074640410b006510500240d03c0d4418410f08074056868a07202d24204101c580158043c00030075801d640781e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 659735980 1250 659734730 659734741
    0x601020111032a1303150b0906010c0219141002030403050604020909070b0c030a11192009011214070e06090a0612050f07060f0c080a0c050f07050405100302030d0f03020d020d090b 79
    0xa41f140c40b00305580c040f40a41c0014442d510a50b0550710707060005010061403580d550300c5103002e034520303000701d00c01c40480f65040345039080c00010084c4003103440c0f005602d41440e645885407a4003000e0402403040d4800408103070348070347c2080000080c05070841100d0f41c07208101000790f520350141107600c0100740540070f02c00c00c0b04c0001c034800600d25102080d955550f6101c0d13481c148000c010743c0c1800c811800310388800031161240060b0601030510180c058030404520704180d43c0448036a03449002640c02084144aa419404074858000c0810303280511152588070040c400703408990003814100b00da6080c040140070001601842e692100800e4a0086813940c40441d601c031000c01c480004201c6442e986400545a00b000f0402e040161801c41c09164042d6940c2d07060100c0c45880d05010b41c0925000c0c8203e140510405410080125212410500c1c43d03000c240c8400c69104c842040c005292003094415000f50100d41028820101c115915240e0030103038001002c0416060b01d06010402c000399 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 659737230 1250 659735980 659736023
    0x201c020f100c1407020d1101110d08192d06051003020915040825030506131e0201140c010f0509100b0303090108041e080a03060e0601020111032a1303 66
    0x21300440d00505846500d52040d104d50061400e08140315040240c0031040381801a01400010015030307065803044040d0400c0048a040300d00320a4034085d09a00d4040350001161140e03410058681d06228043c5c803452010101d0306c01003606a121a4100c51008082340b10250305500800002e08111440c2303542c080302400c0480f090043d030103a844545d110381d41612060030507171003022101d2200000040c000340c4954489040a5017503894842e411103c028801c104541d924444803003803055541c014180700c1640009040c2d01c0c03d040d0ba1408454000307811103007074000303400c0000e007820071150901c01424014006036496400c1402940c01501c0c000e101e00311403802100310303000490305035580c500a48407900d420551506d040d000014040d5840c02140c001907030321001e0315030341200d03844c000b90051900d8541414040010f00e0203045901d804412071804240c0c0c0142c07500b012030103031039040340340001c00c40c3d03082c042078a00c031302d08244000f02d4210102c0c0140010881a603104d02440e04c200d100714480c84 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 659738480 1250 659737230 659737237
    0x80106091b0801060918020f0a0c0302070608151e040c121103010b0301051504080105070c02040e0f070e1b0c0c0a05010512010605070303090819201c020f100c14 71
    0x4d000034081c60400c00295010004085500d918560014905045d03420a402c1c1c40d400b1640300b80100e607100160740c05141e014018000108414100740c1402d01e4038a080b402001e00004285214404100041d000350510040100d510540035000304000134400f0000b8000046c04107100780c001e8100120300303101114140503207040307504451a8904507424001003003815508043c0442c00c0f80c03000d01c40000c00d442c09016487c0600c250b501c50301c58150880c018081034038451040851107500540504507141800200081180d10a86807142a600c40b0f0f080c40b03250300080311000f80494070108081294240208904440d04c81c1214140c20035640c0710010340700c5020380c1010b10380e43d201d114010403443c3c0c000c0e8010441a4401c0c900001c0c0701d030041c0d5404455030880101c9015848031051044050703034121001880010b05201d005981c03e589184560f5544041501402d5607002203612526050080203811100742883c41522010050421100010448041c0c0200043d2140104611411500d002c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 659739730 1250 659738480 659738489
    0xc1115100f0f03080703020f070f14010512040209090c031005160e010c0b060301090b040b040203010b2d0607141c030902280803031006020f0615010c030207080106091b0801 76
    0x400700318924684071800c4681118505500b50b00602c6c220340d03090f11050003204040c044040c43da150560400e0344400860601d000c0c8bc0d410b0060401000c10202c440c007000c10350065040760b24102070342e80c0512b014280f85944000c0d0345c25110703030805040300391001d0308001e1003400c06461403018021444402c441000300e5460680c0424421055203001c03070f01c0380180640c4144d003d030002c58840c0640c0e0f2124140e24046800b900c1e9000100240130841c0303428000d040c403448003113030608403000d841158003416500341d0400240b07070307a0702c40c2c951446500c411b015100c019410008440300301840b02c00c0c950316000890462158944908044240c143c0284500420340d41c02805250840c40a07040c01c01042e00c0f042100c07407840c035003150006402d900800055204000501e000c07002d107460208003920b00845500c01094681010040102d290f040403501d240240b0b09203001e4200150724181070303080001c15003005480f5420044085000752650f00284412002c004000350180c2069104489210080c0113 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 659740980 1250 659739730 659739749
    0xf0c0e09061818030a050d051302220e12040e090d051b030c0a080c011503111c050604030206270c060c03041206200705060106030c1115100f 62
    0x2800703801c03040d4604102d030b444141c14400c544408a096442d030300d1a0440030190b00091000612254100120b00a00703400c0030b00840099076403005640041d50400402540014030042e42039003008003041d81e00480f1850b40d5a01c151102803401c000e5202c101d90050090b290318151800105441410004c1d481a0004030790340e46609005c046d0b5840c5400001c100d451915921060041c07600c582018024440814851680507643c3d14964440b2802c1d0780c6c140c0c2108802d0a01101c3c10800302d00b5610310025a60340445c1c00030308007076200c01c00c9121481e0a4a01501a204200411082540000300302d802801d841454112082d5041141440790841d00c180c000c03260402c40e122030090030800041c1c40d01a11800c1035904203030700c8a0741d8051060211101b6290715440d41c60360104244040c194070aa8103840400e28540056500c8550390b0701c20610170141090f90303d144403803070700d4403864400d08102180c030203a410506201580400c070b100c090340c2c0103c2c044031070080043c401c6281c42c2103100316030600c41e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 659742230 1250 659740980 659740999
    0x102030c1005150603090706081b09060a020102070c1719050a240f060f0f030b0114011202030c180603072f070e010303030f15030204020c01060503010f0c0e0906 71
    0x380404050500075103d1001000b40c64426449a62050041c0d40324555043c020030700300380703031080042243c600a050852408001c2140d20b440c4a82e90003207400021b41078403220f594240b0503004a00912491402070101c0800f0300700030440e140d401914640c007000d980201c903031690748140c0c00304005c001194010140d6001c0903031034001404442c6a458010b20052480018106105115050307030041441c2580b03041d9140030034001c4804151002c2e016003100003ca03958541159100c400404041c090820841c200c04142c001d143c0c81510020b00710f14419100759200d040c032032100030f071a40200e94491300384028031a030784609041420550348907688a9440c0c0700001d01d445c03419140a40e401c0c8224010300c0104c600240381c6042004202c3c000c10544116412035851030900130100c1d0710b4407002102c001d0601d00e044c41301024842e2400d007941d03011034005030359000e03092501d40100340740c0d0300c0503825500f0071003521514089a4081d4044403140d0703d610096204800800c008494100e0743d180c1c0c09917140c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 659743480 1250 659742230 659742253
    0x703030c140301180914010e07142202040b0a0e0f151c0f020c0f0d18061d12010b180910110c0f07150509150a0302070b04150b0102030c 60
    0x407075030700320f503610b100b1000a02e52085c0d15548180414240030206e5030791a24a032225640040160900503c00700c1c100c40c41d102c0c2c450001404040a49441008100009241e0016040c441d0b0440c1c005100c2c031415280e0745c01c0c00f070034050180d0718207500344c610805518a008480307041030700015245010b0b200016241c905861032400b41d080400d10003030b4402d69191721100304880b140c4010f01c3e1404402c801400d5424840401505c1c04200c10f5041c2c003001189102d0084490446d40c3c080c00f51240c90525414000091f44000030510b42d01650341d90011654005c0d021008040d8021848180b05440201503180817443c0c000ca003600031b841980644c3c0c0015585400e240b042d503c00c0709000b841d17040b4945040c080c01020341c0344c01200128000603410803202009500310105003802c0000d580d040440c1415500c01c002901e07100b05400030482c040c8006420b158140c8254103d42d0810f920a90141250405080c15821500d142e01c2983c81c8919111032416a0741c00001074544030500000207022a0060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 659744730 1250 659743480 659743499
    0x1d01021801030507120f050405060106050f0a0c11130b031b0a03020409030e120c0102191a04054b1b030309090c12060f0105040504230c0703030c140301 67
    0xc00c0001040346003205e82d010800c0a004040b450040a00041020b0030117003820783c00d20740b040c1d0103041400700410180c8948548201543e01074103203410001040f16081c103101d01c4403450380c0c642503806103400d00600452074107944110800e410990480c1c0740f100d00c101c01c951031f040400200650100400720100010b180903001b07103044a2017458041400070891000c20f0241030701800c11807482d00800d0300704181d075904200042c050300e041440314101050759150307107241011602c020000039074054006802e100c0104003ca0441800864022800380c1300115107a9241c0f011588108030500300b2130200309800138003044c240420941019003101800540072411400300320701c0b0315425020034031500c21320750b5942086a10400904003201d42c2e0f4942d001c3e036150b070704000800c9503104090194503801241d0744001030b50152603040d1000543c0e40341d404c0b040d16911107190300114240c91000e041221502d107540c086c3c121144292028003117071011410599001302d20b04030000c43c0d041c0600041242105 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 659745980 1250 659744730 659744741
    0x807063b010204090e030d20030606030402010c0203100c08011211120c04060605030106031404080d0b01020f0a0309030b09062a0c0105040602040510030b15130b0309011d0102180103 80
    0xd6000006280c1039881c0707203084c1079400c5500089280c0d0400b20701020220014000d4402c02440b04072031030900300700101c01e68068000504200c5c002c420200c0007404590051249101007500101107503a621820b5150b60060310758142150b0008840b400006034452108450404250f806290690f550b118041030228851041110007264804c03480c0060094840d4403484010302407650b02c0303170781da51305198000c0c0076168001c0110628582210030000800e5040c426604000700200700443d50191001c0100c1c98184410790000082c020018038208040d08110418201ea2281085d44010340c5c070704120b030b1744445046541086051480c0e91100701190020a943c0030b01c95400c0300380303040c101001c8241d801c42d00115411900d2660000d4280110f14102d075000700ca6488502c1e0038461803885d00081041222440c000202c0e4036000320700f034018aa841888034010704001e843c0c1c1c588a15203900300354080c01c0b40007414030400310703080342d0750104080600803610746a0001a0004041941c1c500441c001c04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 659747230 1250 659745980 659746091
    0xf0e0d031808070507090b1002300f031e07090308130305160302210a020d02030a05060915100b09010f0216030f050d1812020f040504080706 62
    0x92080741d12000090044010784002c030b008000500c0e4983c201106041203900c00c184280c480c88004e401e0004441d4000b41d00000e40c0700148403091020301c0440d818409511141614040540102d401d05442034610080c3d8490490015400c0b083c084c5a58203001c100c03001d032021400691849001e1010403600c1c001400c603d8520030240328038030fa0740d8455508104426910030130f0801c00c45010021b501c1c15205c0b440008410365a6059099202d100031a42c4030b40b4004024021060390f9000019507609228003844140c0050507500e240c5441912146c98484a01480c0010340070305011400c1321408071400c500b5984010300492a0072003c0005441c08014501c20b0003c5100d01c4010507010070710260954010b52041300035034485a96031030154203240c207840400c0208901c0c080030043c515250203655080361521100c0c8140b0003014000f040c03440d101840e13030b15040741c1000300f40410000e40800a1000c20b0103034004100c0811000e0000303442c40020340640000c10242c00080c02541403210005c0c0400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 659748480 1250 659747230 659747261
    0x1502040506121312020a0201090801050c09040f0f0c050715020405131d0d020309010311120103020d0f0b010311041a012a050d0c03021005100306020a180b04090f0e0d03 74
    0x1c820b50f5a08004140084c0420040e000000984115600900d200000e003500c240240702901d0f1000c00c69515020701c0018a10444e12410581021891a0300190941c044c0400034851640d07a440090b001d0303130040f50110745207280b40c0b0a1100c42045842550192000100219080c8100e2200c034000b8240003010840b8412500c042031150407010003d2014006a68014503280d0131004009030454054074030508c00300d00200300d01e5600020362202035041d04d60490301c6c6c849a900b2414455030500c212140244401182000401407001e025000c000b012000c540c18001101041d0f20840000140b002d02c5000c1400c00003200503e10500190a8080382040b510202103240790326803031700d8004c19481c07000102d40d4507030b600d030203041c0c0c180002030508031190014006428245101136212038940720251103a03501155085101e441614011030100d14040d184400b030340c84102019965009108803000c0900e45201000c8041c023501606441403c0c000180a02101c0c1450a4024004031343c1c0e1284130 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 659749730 1250 659748480 659748511
    0x40210030b030109140d03050609010509100f18110703080406181a0f1303080c0f1b0114131109040204060503030c061e0103050a030e0a0b0403050a150204050612 71
    0x7075481c00d12032425100d0103100900c040e80407401c00303d07051809281c0e00d203040600348020000c06442d51040c0c0c50440e07905030b82c0701020342d88800301c90400c10240c2e04606600c4041440010300c040740320841c4200c01360743c00b00c00c001c000b0880d20505003520409000501088883c40041c02043d040c4d4041d12840c0500e003c85844042c0c03950355a129a080303808120002d100403018840441034801120358000c2c0032205400c031214903501e014010b41c40c0240720000704c0c2d40025001030b040f80184150340e010440a15400380e265030141d4080c4c0a441d901c551a603101000800240b054030790b40d0081440c854001076010080040107007030202c45074008000740d800c0b07134841c2800681a181000280b5401d84110042d10840c2000d1050008145407910041e00190141005102042001c2402d0a0055042c288005d0501000c40843e807480d115900000c00110b003c01c002080c068082081240d0510030701103505181c0d20207190f0003c80c004d50240035000081442060004a1520b207403681001e100182c0041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 659750980 1250 659749730 659749751
    0xe1608090c03070801230106050708130e0106020c10091a0c070f0e150307180e010b03101535150a0f0c1d0d0f05010203010b09030d09030b04021003 65
    0x6010030a6010580c207030355a80e04106c0002100b119402d00e1001e8912106036545003d84c011304074000c0e41806014040002400d01c40d441c01a501c0724001c110541c8200c810707603906c0802948503240030f00d903940180c0035845100e515620800109040e40c1d5545110041d208441c0d10714410341d0000b42121b04548210743e030110707554202c01e0125004100d080500c103c20b00d4001c000084001035621841e0181c4d11500c814002c0d010907005c0c000c01c50f60540000200e88201000907030140c0350090801d90140a0040d80403052251500000443d00c000312481d40000da66080070340c6a030170912924803c0700e428001c000c130b01d521244800c0880c5511175080300c80c2c221034048400400304e4191500c04900343c0d259103800c8205410b000b015440c90709824174468811001c0f60f00001e81202926103071290810a400d00200704030f880e4010b0005810400864036580c680300442001c1d0305c16035213207100344118510300d0074151140588800780c990000900000b81c68507400d1161420402c2201410705440b2041e81e074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 659752230 1250 659750980 659750983
    0xc10050f04181b0f0c0f1a18010c0816081b1c0b060a0c0210050f07060b010e0a150e040b120d030b0d0b06130207080d090302070e1608090c03 62
    0xc485460280001941214074481c1003010500c0600900134000301c0391036031580b95000940b40345c03640d80103c0d1861045c4083d2401181c42c40d00100030104d902c01140034028400007881d02e11081154100c0200001c5c1c201c034005841c50b1004941c0140e80c408240c0301000701c64032440601c1c0d01f00d80070310a5500010541c101c8408070340c00040e07050070441103001c142040284180100c1c1d6443c0800d1754001c0c43c1c003084280040c4540c043da20040d00448915403181c40040c42181210805424400841c1c3c60307982902e0314038060803c0603030307107400a00d1b00b1108588a1600f40c0c110710440341907013401041c1e100d07800000c1c0d039094620540b040e8020703503030200b1310125198012129442080318019040e12a2000c101801311034040384041e0040704002d1007000000c11b03016184d904050100c03050026414220010720280c400c0c060020118603011801c284034540310740000481b58840d800395147e00b030300d90900b031422075021070b01d45a8140503170365116842805040300c1c1e5001654030302a100704000f0340c40800d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 659753480 1250 659752230 659752259
    0x712030509010305150d1709030106060804050f0111161a01060c12023f122e060c110303040f08070b070503220801090f0b090c10050f04 60
    0x258041400001c01200640e41403060540c03242540c078040e805080d000011507100c15544000506404c8081007100144001200f65007070200014024441c00e42c480d14003e15080c81a20b00b10f8251180c0d903a880c1e94000c041c0250300400c0614030b590381c100250504006000801d03000191003846854440500c075036021205580a0300d03040e00d910b001030000c0d250600035034902828103811500140e00c0140010755034000c03040400e1481482102d05110071040403420744440303031740145a41d0300255820626002d000d98510074528550b20107444807a59694901d10004041117400c02c0e0610364041c010720f800307941554002d40c02100d12241168001010070716681c45a04442801d0141078020032a080023081301002400b8016102400e0000e60b039100c580da4021500c4032016440c0c2c40713400303c10946418100c0d20090140d80024007901009007031200710b10301810300603a45000040e000902c1c0e105c002514068100020300101817030002c0b0001151150000160400300a00803c00021001051601c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 659754730 1250 659753480 659753483
    0x1b04060305070f080c0301051005090a03121416020405090102120702071e180b13090809100c0210050a0c05011d06010f030b010b1303020d0c050405010f050d0f050712 73
    0x80e241032000024016240821110f0100000281048240f00d0740030305031b0b0704440e803c1e41d00c1e01e0b45000741d401c00d43c1c007802074450041d00b0810300c2c2c40010500c00084441d500942050310747c94240800da018184c0b40d40f2540c102c0c80242c8504254000050078554030680d84150301100060074090b1100c1048484070094a58030010b910540c810300a003080c000c0d8a06180d803102e14035a01540c42c05a010180003001c1c11b440343d10b10b6580c0d109139119252100306100c0a82100c01c1000741c81d090703142100a6030000c200c003501841c0f102c2100150f05010b40840344070036800808400310440c101c8801c44156010b2407901c000c00c200701040740002002405448240e00c40c503860055001c002000b20342c64148160300c03c4400071107020b820800700c0c59007040a810342d28061042942c481010300d9145031442207a20080d01300403420800c0c0700740900c0001c40421388204413400c1c072203640da41c0c01a034901001c80c02503035030040c030b409400000600140f890030310b480d201d10240d5240720341d501542c6290360030300c020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 659755980 1250 659754730 659754737
    0xe010e152e18141305040311060702160b04121203020412060b030c0102031215150301060e0a081216060b090907060e060304210201091704090b030a03171b0406 70
    0x103030300b0491080c030b9481c00b02502071400b8058042c421080011900e801c100d02c0d0a03031040da5400420141440b03a503165082d1060350080f03401604080100030f6a801c0c2a80002122016005002c1026151102141e0031a240507982d0314003610f8648903410043c0388107000c0c0d01816420000015082501044c103104207028040000f000b4540342c00b0b050800c40a01c442e1411074100300500c2c0701c48401201d4194100b001040001c090000c94008034840005010340c0c604000004000010690b9128444c690691026650009a01e6848452075518110144051442c4406201030b0300420308056088111038040d800c007241c2002c000000c56071400c0700340c88070904c64104034403c2c0911900f01e000d9241a8400742d4031145103140c180c4400b51900e480c4c0c002480c1700035480071102c654520035002403007040e420292205c10014512051203841e807281c1314407082241425484455441c0c00705601e00019015120341c41c09811040c42800d552400400d0100044000145407000104240252014240320346 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 659757230 1250 659755980 659755997
    0x70216060906090e0126120313030f0c021f20071505030402100305070210240f0b030a0207050a050604300938040e010e152e 55
    0x4000030900b035026003101050001ca030b00100000032071407074051a03040401b8081c8a406014050701c900740390b00705800560844010040c441e0f6100d02c14524011701e0320a03295140321401d42c0d00291040c1e01c5840010794819464200942203140784c0c0e10107480d410151500c80415034191020181034400d403403000301070341e21201c4188900e6000c00204200540c0b5400d006040d4a01750740091210003406044004041d01e64012401542c0200300710001c4001d00071081c42810460410120707092001070301c2c01003600340c12a001440741840440b0406031034851003a18174680c1c035015040040d40c440c07101201c26100c0c404600011560030301c10240501d01c0349040c01d8800205c01c508000710540305080d09030010f850a007403a05950030200c0a4211107041c021100010402034103903400c8420740d1880482e58204448205c02c040b03020380140f065507036059400d400c82e40c0311030106140300822140d125014070445040151031402e03075181083c03d40007070343e19482041d00740921039800d02840150070202c2c200741c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 659758480 1250 659757230 659757239
    0x30f0106080619031b0308180a06030c080609090a05060403050910030c0c0303151d04051b012001060314010209130c0c0f060e060112050709050c120702160609 70
    0x1075640d90300710104440403808100d242c0c0d0180d00005007480000c01025003001e400420340d9034001d6890003580c10245a685030102903041c61100401d802855220341e50141d0b000c518140640304415603c011581c88480950350001802000380c0007078804019172123840e5000c0e0000c0d20410038140f045119564440e21140c030201403148864001a0b100181420450307000412984440145c4016406150202d07145860181041c0c2e0301906400c003120311940410140350462800403060f000d5440f8104450519400c03040f81013801d070002440070300003010f55401c111001c58a40315010440c568000000f043c65072940c8004500c1006200c100060750013192409061078000b07030182100350041001e2020700103555000f4072000650354020243e00000f1a400c2c00d0101c80d46c4000007a14040017220450758440401032040f0303400600460309407142c10400314624040d130245501900c6d03d14400e5003403407181c880d07010901c0c10050072041180b0480c00010f103482e100c040300a008003003948580c48804d061 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 659759730 1250 659758480 659758487
    0x501020a0513120807061805030a0201020a021204050604180209040204060c0510060821040e040606030209090f0717030717360415080109110f01080402030c100e0303030f0106 77
    0x2da10203004a40d03e2403800300411361070702c11224619400480054400c0401d090b52555820041c00038209100104642030b240d5015030041400c110650203c901c9828014a02201031040f4050603412950070b00040050300400c83c07103010342c1c2809107805405c0007010703408a4226007160303015000041c03181d004501442428441400800500c0505004003800c185500366a02950803031140c481400d4101e510303081075464240e0300500b0581099086509160600348007031b12712400f083c1d1044c403466010450f000c1c00014099203040352600a016001c4c500404a140040c1d0f44c00e030321103240010485034000640d0200480100809501d00940724a1006280404220701c3c5529891030441d2450341604000140189a00c2c45c1c0111804a00b21100d00c4217580c003072240b070b4000700c103a41c00c00030750760200f01c0106041044800c081d613400b0604010400110f072155810b1303902a415807c460343c10f40c05820003000d1f00440001e1810705907115081480032074030f5a07100325030b6800800006001030206550 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 659760980 1250 659759730 659759767
    0x60d0509030d180c1e0305100b01020d050c1203071b1208060f090c070606170105061509060a030f022a0705040615050c07050a032102030a0c06180501020a05 69
    0x18a00f40d6500c01c0449641c0d503490b8030316207000d800c500d01d1803550000b42c0410341c0348144002d10f43c0801641c20011000503400090444400101d003d80584040881d00318801d0043d01e81e1590b41500400c2c0302c079100010001968800391595040103c18030103020b01260020309054058414449180040c84843c0014603000002e1b00340c0b40f03d041c2c0341401440c2960303070301c4900341c10080c55401c8aa84000b245000d00c0284029400317890b825030704e42284a1100c5041d44801e120f524140c588400914041a442410348116a409980841c09108809000d071107907000300404c034800280180340608078041d11304030411380c03001d14034190040503802d404000140400c0340100001c2c0c1d4148640750804620340a6504140c40003410844045a041341c080b00c200b04140c02440302030111007072191203040141d9814030850916100d1844401c1800e80302e440042101e942003041d03070312b9180700d0610347e80c0d035001b84c5604424014000001114200403500c00e2004108102141c0c59440d80e5117a6001c0d004040103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 659762230 1250 659760980 659761001
    0x3020f0c0913080d0905010e070e0a0504171b1914010203041a130f080a08090624130f090b011202030d08130f060e25030f02060d0509030d 61
    0x1c020034107121100c054010428119a0b00240e00d5481c0c61410110a004000c074600c003030110340c02c180580b0421b0002003041c0f415108203110309000c5603074420405c0152001079500620071000400410b2056405e80081c202030760381200301901844020480c60300e000354003a01036098000751070740e090402082201c014084c0710917400030740c15454192100e00c09180001140d03100000b48100164801c42c0314100184d019511050b12603506540341008041c0e03400c0f50041e8804a4950301c00320304101c03000540140700b94542118242c000c0741090303030418005400d481d495004040c0e6001000071412074007070358025201040000812243c40d003010b261004042c3d010b42103c112800c43c240260b18041030100214449040c80280ca0300d450207200301080c420000036012114098040701000095080071240803d64000c50b0312003002c203141032080e0700d00181e452805c10300038403041002a0010409003000e40c0024846820b240d003001e0084151001201e0603000e035000090803024044161103441c1400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 659763480 1250 659762230 659762239
    0x130b120703050307030c030903150203040b240112020d050c07020a1a0720041a0306070f020a260403050706020d050702010e12100c030608010b090405030a030e01021603020f0c 77
    0xe881c5031a05626072250600185c00c20428904102c149030281c024680207550024a5100501150403480001d40065034110394000c1e0040c00310ba1800d200a5204a840303141c1c0f84c0e0400b0203211640151183d51132030a6000342145c081c040111102c0e10340c4144d5203e1902001401e44d112014810408120451342000c1c0140d061182a000601a040142c90300c4545c0461048003810701d114038000395004400096038080d040203070071561104c41155800c0d4441d01901180e41c191100f038001ea460889120142c401a4031010055010a40d04900e80030ba1280c80d502c0c040c1310040d0754405680990140d0800c0e152544405003c0044542c1003224803111240c40c42c00c141401d4080d40000c1080c0794401040d8820b918243c0c003001c00100c1070000450911801004000381c0c8000000900035007000c2c031a00300554038007807061855091402186108940c04001785281c62480b00c5e0a50040c030607841c07295602c0d0b60034040300d4151140e0040708010a4000e400509242c070034480c800e403501c2401086c00307018 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 659764730 1250 659763480 659763493
    0x10c0c1a011a070206070209040515010512030a031d0a0506190b010c03050c1203070e0f0402090d1e1704080c030703050309100309020a0b0322080a1d130b12 69
    0x15210010001d2035412550751255030320080f44c0000b80c01d174000c060700603522021800130307c010003d0001d502c0d110101001038103800c580e621410441170001602000c5003a0300308012034607030b0700c1c031035448580d000040080f004801c1c104001001d203170410340e0038203c400760300036003e03c42e1070b541c000b540b60303019450b034801880503442110000340710262250700102482004030b1040031003a001c1c88924504082da9030191384a2516000c000c10198010400d9401104140d102d0019801d01d402200d240d103202501600d406904c641d01c0c1d075400300c02c18000c1170a40c0500b102a10000e01404690303040c280c05510f44030344850600b50f485003402e1010108074440d0b40121030820018030040180c80700b0180c21200300b043d21040039015170281c59812030085d40102203440100b95903c14001842c02400b103520002c2096420703285c03040ca003030b61031807014040340c0040c004d403021240f05403c8103c00c00080c484100c100d5074464045101c80c03050803102003c0b103466070030f442c178241800c8440ea03000b44a104000c20f807 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 659765980 1250 659764730 659764739
    0xd0b13020112061d07052b0606020303131707060f0b0a15080c030702030d1d12041206050c040e040f0201031a0604091505190e06121518010c0c1a01 65
    0x3068442e5000c40a902c81388000640c4140c010780c140c41000800510754a004948511412950721040300302601c40e52070220701065051001055070f11440d011500c02000909036103401e402104401e035403044506082056000140f018081d5140003c25110045910800c1e50204694a00e880d001210f0045214041c082201c1e440b400c080d400142d0720581998949555108034110310501000c034107501e05040b5a03048004000003040d900b900301009965645d4200003003a8550303c250f00c1420310350b50051094a01042e00c542c08207800442c08150b0914040d0303514540c4540c0107046038266190381e00b10350702c801956010b0151a004180c001d14950b501106030f40010340740c0c082c2c0c2c002c5e03070400da580d583d501c0c0d03003000500003000103000c00514014054440d54400c5035000030724080e0030300001844011650604281c40c2d0000401045009030801f00710303403200070802090081ca43e51112102070307405054000288503402a800c201c0e51200d1401000741441c0e518121400ca200190f4246c1c17800402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 659767230 1250 659765980 659765999
    0xf090f05220602221706010b040b0f07061d0d0207082512121215090e01090b0901090c050906031e2a1311180d0b1302011206 55
    0x90a0080004400103107904a0034400c00a000381d000e5075900d00380e0048000c60304104000344c5400c035002c0c640300c410405c50b00588141c480101b03100704e01e24440300340000c0c4102d240000c0a000031b0340326000568100580740c0c076204242c41c1210400d90a544860031450000b807024444a03400e403d9600003425120b1808003100c5d956120301c101c0620384000d650300390240c0050b801c1c0210060001d03c056024a0b070b0b05081621080f041c540e21600822400c5141105c01980c1d40540d61402c00180b111030a42460b000a032400340111494400c415580d40d808440090f03003403070115014a47c640000148101d26250103042c1c03507050703000345105101440c00c1000940c0c001400c40c1e015407102da440c1c108000006105407030041d014080143c0d0081d10728040c1012104404000c264040894100010050f1882c0040c12038224840042c0081c3d407c101d00c040710380c2200b0098901840281c90141402941c1d02c44400c2e54400b52050075800d00110740150035580e010004c04510b0319881d504002d10351a281071017 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 659768480 1250 659767230 659767261
    0x302090a0b19080c03060108010507050d1d060106020f100b060702040908070f030e041404050a030e01020f19030305181f0209060c01150f1a0304060e070f090f05 71
    0xd020341619070030307000c207580c450b007845915841148100d030ba00c4503100c01e640c0742c40700305042440e8020311480f00009840001400b03001e0082a85031211841d0540e04105c0d00c001d415a0070610358680c42d0b455200b02c0700281000200d0091040e98040c0464a6581d00700078101039154106005403420205c5c01c0e00c0a03941c1e5401c403011250304590002e04ca800c11316240d84c1900a800010b043c0b119122901014190483c9201c4015001242c0c20409001d00d00034407414540189c0703015049a01840300000040e00070404004221070500441d20000130350190704d03203400e860301021300134499100c1e00c24040640501800741c120000c4001e07110800d0060022541d81c4020181100b03807050210b40c082004800c07641283d1414101078241075581d409001c009018266030705403200048008040050101d4150784084140c404441004084500e5107005030902d40000e8810390321a45d4812290640301000c00c401c2c001440e440c280c0e0b240d05483c114400089540c6500c400c0b49583c10181001340b0340750800b408 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 659769730 1250 659768480 659768491
    0xa060608030a0503130314040603020903010b0607151d0a0606030c0b0717070201050706061d0a020a0c110a090e0706020601091b031d07060201060306180b0601230d0506040c0207030209 81
    0x204490031744508089030210408148508601c00020300403c0c00c41d03254005041190040d002804103000c1101441950b03c10080c01038000201040380842900319600410002005e1003004036039504914031040c00c1009844080f200d440c0d440804204000848403641e00500340d010255052140c03584807042c04802c1012481070301e0200081030011a03000d44156840340340c01071010401c450300e17140d02181c0d40c00302090604100300c0100000e07401c18501c0c021100120615660070361a4500340c0d84101d408048400001d038445201a40407e00e542c841c45100051450800240304d1186403d00190600d13006030884d1080509150400b07000c0c0030703000d0840540c40002c3c9000103000103007000d045030150305c03c011002140689c02c1c0004242c0d170305410450541e07000c0c420401c40d42c0401c940e1804189800100144821b4000c4006101c40d80256840000d880781443c0d40c400c8a6002e0b00c0244842d4800c0800a03800c41c1ea5405126650400340718070301d000c4240703000406801e400c2d50005200080010b00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 659770980 1250 659769730 659769751
    0x503040b0d0f062c041106210a060302100f0206070e0d1b091104081902030a06051018050f0109020c01060506030c071106040b0406050d090b0403020a060608030a0503 73
    0x703035400c10741e10561200e8280c000c1d5550400c070144d2602200030314143d07007a00c2d03940001c1e0820f5003510501228080c1c0750007990b00c10784200c400040c0d0800d000c4148c1004405048610000080601400c9081082e0f031203495040000180341c0d04502c100b001089e250f2022608210003840201951a000142d080e004865818590003507848070001442500304004020704031038000345041007040d500e04585054444091040c40010403403d2000745902891107910001e030b0211400c42d20340c440151040d01c00c3ea0002d02a070b0820925900ea9400b90394080c2d40d042642a074424081194410b6801c0090712184581004d01c880d043c000c0c00328426103c10300403800c00075400139010360100300c25032001000f4400901180d4992402080c00895a000306030240c6406481c00c07807000342e6140503001c4506669504889905090a181c4116901d03080410140c0383d040e030711040c032000b01d000e00c5505032040707119a0040004007414034082c02515810b912040095005102403c2850b8002c03042d42e034059403101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 659772230 1250 659770980 659770987
    0x405040606030822080f0a0b0c041e06020601050906010c332c030a050703200c041401080d0c0f080406020d020106050f150325020c04060e040503040b 66
    0x300030009103860390009140c00800030f80c2518884541e42010070360790202c0b24a40040da940d0000c0340d00d84c41d03401c903c00c00e40e4201c82c409100040650b860a9000300d90100700300d050039101c440c090050207507015400082c18020008010702641004420302600040c0c801603910f09000e00045e2450001a03030091200394949a0082a003801c1007880407411800a41072011207280c0119000402841100c200480c548044c0d011401298901d03140b40c104050009503c0c04620741c8084905030402c070000c074101f00000041c01803a00d0042806454030350420090202e416964003000200c42c001800041c1a444805c01000311080229210a070b08006040070242100039150012442c11450344c0104450781c0420086811a400120b00461a08940080000c0c5841c0c4041215644010b190f55a00050624064041b881c0c07001c00b03190483c0034101c80950b800d49102100c0c8000e050030301141c1c016486454240c1162415024000c0100030441c120704a40c140754450644038400c81c06490540c84002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 659773480 1250 659772230 659772233
    0x50d0b0a0e0303150a0e0c0f0f040801020f030108012009060a022a0102070623090f040501060503240a090207030909060f050103061e14030a0c0b19050f09040504 71
    0x250003008600e01d000003966601c0c5081c56000d2119251008198000e1541660115030000b2100c42d4600404114503018100341500450181550003428240a501403d0000185148003400070b07101c4901d04007503190300c2c1e40c10000c00c0c600b16148105150703104514034002102000c03223201140d18085094075110ba440003060700591401c01000c2540c0a01d189a181e89981d00c60039807481034401800b6401ea40409030741d1031044070700c180080c945144d000407141700200080404070050800010140210340c64000c91310010301101c00907848240402c2c03001041100812107a80e2124903100200d511405694401d0040342e0302c0002402003016003580022441c2c1458020082d400040424070814001e258440c00701c020000c01038070556001c2070510001107609050380a0780000c1d80803131000452414038003c82c03004800c08000005805004400a903004a036a11040343c02610300f04c015039036284000e8442c070408090b00c2550a007040000d00c40340740781d0105107049404a900441e0080341d10b0b10349 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 659774730 1250 659773480 659773501
    0x190203090d2904060e0c010c15051b0a08011a040b0702060904020c06010b0702192114031323060403151404052d12030406020f04062007050d0b 63
    0x21221032040441d041c8104010400d40d5040810700220a00a0300d03070006c104801501d9001140c88000c0480404c01000c0c07940c0c4030380e50304c0141d00c070179540a0200110704800e82c00c005903102c08076413000100c02038018000c401e01c001000001d031381d0f400c409900d00b51424581b901c803800750341c800910443c00020051410380d190f8042d205050810002e407403103540e43c3d00c0c0300d811640c002d00080340030b450040d610116000b441040760088400c05822040080d0005101c92145070070720310200d0b41003e0f2000b12824203c0d007080641080e16807415941e82d001e08048003007030800e1030b450007196019403080c0240c070135850b07030001e440c01c89502c2162100d140184014041c09046440c07000301511018904100c01d00000143d00c81c3c20343c0000b40c00305140c06a048045050f984102e0300110b03103a2200661034240100740c0020b541c0a40034a20041c1010003042c54400c1681c400c0d07100340b0004002100e03464080650b100402e0202d4015401880c2d00c6142078089400780605041c0504150340401c00180102c40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 659775980 1250 659774730 659774783
    0xb090a020316030501050601050412021c0813030b100303051e0c030d14060d0b0105130f1104030b071b020f1f080a150308030606090111070605190203090d 68
    0x34020162042004214108020020b0714842652a0340c03c0c0000702d40d6035401071089909036034542003029091340143e020302c206007802c0104049004c610000c6040415030080c090000c03150005220f04619103141810716420001600700121201240410400a90094201d89001e20400048171190080051000d070600a0340c0d46050a4000065080006016544a0a44106914509681d50700c80c4401d004200311003070b40c000d05200e1070800501180c50403465607a620303150000c1c04207400d1000e040c11002e40d01500a0881443c0d0301203001e008008501d81d5150b800a424030704800e0040014005103004a115a00a4003a28521a2041ba40d0b03c3d500d030034844011904000c20100110390f0001000000b0894000ea40c0500d8042500815544601c4900c2201d42100000e411600c03180100710341a13215011250500c03a109150300d180041c14480b0320014405602c0d09074440103510b040b44818105560b5400854208115090396a9980f16000c0c0c11130b43c0003620141c0b0161240c00500b0b0034075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 659777230 1250 659775980 659775983
    0x120b0916050c12040e09010e06240607060501030b0c130b070227070f0201090203070b1809040b091903080a09080c0a05030c0111130312030b21120f070b090a 69
    0x40c203038852803828030143c0140308550081519a82a0b03540c03c0d070007401c0b500035030041c1840b604501d0101d40221800181041d40101c00e802030b0509490210000b41c041d84400011140151154010000e110600210301d07440003041c041c40e031411121511401000500e0302481c0c91079007000c1004411f41d10b8a550f6500742002042c0f0114201d50f640b580704182410440d901c400207407a00c2c0c24601841d106000e04024250302800404c0020b017401c500140c29080b00110039011038580c8030380c52450303490016003400741e40505030414450401da0b040c41d081c445000301040854075013000150001c0d510004403940015151400101900149030512552050005043c40c911503080010240040030009066100b5428000c0019885070902d002d030314040c0c100c2d441c40031555101c040001c260007062010868040d8580029414010b4000580c20764244414252200c0070b0550b0400b8200708002032028905081422820301c0c81181151031a4400c6d410010207140754403002c01c140350300800035016402d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 659778480 1250 659777230 659777233
    0xc0b010303120b1c0b0105030d1d0d0206160c0b190309031e17013507090203150f01020106050f0f010207030c06020607020d180e0405030904110307120b0916050c 71
    0x4c0320a8407400c1c6814007001098400d40404400082d5070704c4c000468032990495501c8101040c52002803c41594207120328058005a0701904680160f980030001c04013050a21b941d042840800c1c1400b5802408075004191641010130003007901002807407000188840900e00418005814030342104c800402c084210081410002941d66043d0001c054011205801a804103580e9959841c03050025958450891954003451100d000301c80000030000f81d5143e01045030b104943da440d600c000ca0348201c40c0108180c07242034100c0710074a81105d0350110034000340700038080385080200092220800c14110342c410041140300c2d00d502d134024000d5000546c1c0001000781501d0340c1c0c0f98041d44603601100e86100500400d020102800c0c0102e4024061307850100e55462560300304076440124042c0900700765000e1009101442c641e07034681c02900701c0e101c5040e40c80c3d07840382084003003e0021024103407400070950030002c440c121602c3e0242043c1d8006074241c120400c4a088100603560f070721a103040000c15 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 659779730 1250 659778480 659778499
    0x50a150806011707031a13200f030a02090f0a06091b032901050a050d02071101121a090406180b100e1306050709090204060305160c0b010303120b 64
    0x280200818094120f4042d001042091810300d02d146807a00280d0100070304040350080540c01040520708807590003054100100b48107840c94075400035a0602c92945100220304020a5019080c41800d050300c1e4041a00140200c15050b40040d4a03100d00401c20381c0c8040c0400000359002c801508000001c007102e0340f0403c542e0712114071800303415203402418400300e402c1c201010b8030b603545101c040c031409203014108e028200902d80112220350120b981801008014040b4101085041c8001d00b03510717115a114030500c00e600c3c40050222110201e40c414460b2829100d601110200e026a4548007000c0361803401980c3c079440c2409c002c00080100b0701da41c803113540700b00e01084400d0a8440c001c030022074035242070655403440a2803100e8100c4c0c100660301820704030b06000440c1e40c0c20050300485241014503240c0d8031900038004903041503106600298691041c0043c0d250b98185242000c440703440c0204a08599440e84101e100781031000030208850b00300e851983d02e04960040278002c1008007052503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 659780980 1250 659779730 659779739
    0xd1e0302030403060e0606060307050306010e150901020607080108070b0f040305070f0306050615090103021303021f080a020301050d03050304030e06181c0507050f18100e010b0901050706050a15 85
    0x41d250800d000c12103240d40384c01009121100c0008000380b05038401410310f451a07823000d5003256542c0014040e0760501c200b850340c02d002c981d50070001c43c000c4000032003001e88a00c0300000092415001800140502a1800c014000d00c18003055880039210000003072603a6a44032901301c0420310881d880a00503004401e00030070740b008180f0415080724044d02041c071081e21600b04200345000119160711510408103e00b8241d0b50180e00030303040d0282514544030555a694002c82e401c490340e1405407408900007a100e400c0300340c021810341d4001001c10f004505560608000c10f21280c5100d0300035003400300110004040601c035030701c4042d210b13002508a03500c9441c40d5075a42000c48420060320b00c200d40310104030040c0c0100d10aa016020b4220008000c03140ca45002d2061080c00600f006030083c07404000450883d8040003518040c0000b40e400c960700918110485882900c1030b003189011a00030410101d0b20ba0b404015134500c41c0d0001d01c00130b5551a084004802425031092024080450200001307 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 659782230 1250 659780980 659780983
    0x1060c1712010f09020f030402130f32090a02061b0a03020d030605010e01120c032c060708070c1b05030a15110702090a0903140d0504030e060f090d1e0302 68
    0xc2c103d404030340314002c40c2c40e103034850802640291621110142000c5c000100546005400185052076015002a09107148408541540c00300f05e500c480010b04041001c0c10000c20f9803c44402002c1284200154201404004d84802c401100644608004a110008007680c1c100050b180556001280c0440b0414a0060b41300ca900c1d068000209140c4000007580b1350280701562039580c070580d12185c844100560306c200130416000180c0407d44d80f0360f912002e40c0c40780b01d044194030807050101c040240110a00c1e84c0ba011005085030b04010038003041c00072254000c40308200140c1c0c40138005030040e00840c065034010702243e001c6a80b40c032503400000f0500c41980d2406900340c0e8403010910440c640d01c202d8105034800c2a100a410010315000a00003186560100c8031440c40b82c81d00c0707000c0e524201e80c410300640001441440c150f9542040c00300b017580080800548500a594403404d100c4100400000c0c0d01450100d2800381c0c0401c107086040004000c0070070740700701e070402d041c2d09070100b2802d009 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 659783480 1250 659782230 659782267
    0x1b06021615050a060b03040f0c1d060a21030c050a0209130311010501260c090f01080c2238030610080c0d0c050a0314010c0e01020601060c17 62
    0x200740c01482c1802054502820340900341c1034402e0421403620310303146d40c0d039803800840710340f0b100b40d5000c3c030641c5000c900084c000d801c82c2c0c5a07408481c00c4400c14240a01000004115030b400303000c41c01c2152021441800e1311282000356107806041c000380312181c030305080303003032446c00745000358040180000c0084c4001d510740c05800c2240030b569003059500315032404500702d5800380114440d08510521041c00c54201d81240d0301e001c10064181c1c0c00c0307800c0030008540c040700140ca103010741c11b2201006010b103480400403044a601e003110b0251142c0403500001c2c2c1d400b0b98a030061040943c440000081070032800003070801d40208000d045180004030030001c00107011041c2114840d000700c0c2d0200d81d44d14000c0c1611000e83d81200007500303c0300820740070070240348100582220022091040020a540d54a50801c0254000c50b080c05034400c0c455030117421102e06d0314521003404000e052100281c1d034001015419590b2905210f0385004041c20b241d88a0240c090390340401000005a40c1c904100001e00c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 659784730 1250 659783480 659783513
    0x13020c0601090c080a050103030203030a090503040905090c0102060a02070b0c070203011d0d0314010b0301140d080703090f0617010b0d020d02030115110f1c0e0d030905010e060a1b060216 82
    0x1245013544070404008255402844050011703401400803071030724007850340007562141c85541200c1c90710740d032204650f0659400320b44075881034115103500031031544c040c080750f9484103003510218600507503a6078412100b400a03040d044901d002203070324001c644003544406800100514440749002c0c1302c104250b0b0345c1d0109c1c4100ca0001e0304010103001900149a01c290594040104040c1140e08110100c005140d9a510741640a80c1c4a01801e01049180c002406075078000c5d981d041600d420003001c2c3e905141e103a8071200812400110702d400c5000c01c900f03103506695000814940e0b80318029800e5020f401842c010903845480000001140302c581030f22000000816110701c0b040640e00020107848421140c0044038035004090000c075180006030401c0e5102442d07013010b050080111020826441008100310040394400780280b2056030040216503058004840403850035102050080403680c0c0000a03403010031070108001d0400090b601600c2d480020058900080c030304a081c12000340c904d0004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 659785980 1250 659784730 659784737
    0x240c0403200306100906050609030c0405042a090614030a0b07020c1e0f04021c273f0309211d032d0124060908010506030c13020c0601090c 61
    0x100010300c2c0c145901912140b0274001c02610b0038402e108144800340500901c02c41c0e405039000c0980800c02c405261050a17581010402e00b817413030030541c801c412500031760440b21110304069021703542541d00240c201c458641c021148040b546401c03000760320700702440c9145c59114040c407414200c1c9131480982c10230703605000c07035480102d80c00041c1840101c0c03240c480c0c01e02100c1d4041451071b400901c1900000d00f40000c01e04402ca0305c50045080150700380e0036203000c460980340d40102d10006405004180c1420b16000f01d42c003560725200c5000041c00b03041242c880240760b100e50a40c4280f20b10f492221075480103451003c5206240ba5000810f203012070004181c0030003540c1200c95a6090000c3c40400d42060354494000240d840c001c180748400c41d808140c88103648601c40e0070000c501e1300140d0170416040a01c00c601960408001800080c0c0300e411031461b0380c0c580000c00407140d0300010700c04403d80090b15000075408050310617901921071148014102d208140000845542662018440c900c00e581d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 659787230 1250 659785980 659785991
    0x3090301060f06080f1b13031434030204020703020114070c0807030516053304050601060503040c0b0a021615020616110a05240c04032003061009 64
    0x8121002c0407001c0d01a201c0003801340800108241c8008000a400c5040e140c00840341850035588425594442c0c2015924400c00100c10400c0040e652040108085c0d008007502264403001e1520003441c101d5580b864446665080c41001071101d89108e4000e103030007800a40d80c502003810045c0c003030268040907600c08503547e0002907226219610102c46141d00c2140340d49072070380a803801c490035080a502407080d691800e8111001440c20010002c108100d00300c0e40046804d00d045000201007924003510840b06580c04000000d0b0b00412002c1c152051420980e8980e212401c2c407440d64545a0070010251200040e218403054000801425040040314111030701e070344401c40c41c00e4078040d05042e840943d028502161404080b811805511803403417801d0f54240c0701e198809450700020a034152625003003c03904001110303220825150487d420002010182404000695203124522016002940641d070280d841c074201211b0f18803e140090855405041c10913946002800394400c106070207143c40b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 659788480 1250 659787230 659787239
    0x20901030515011502030d0b0a051c030801080c060d050c040b03150901060e241303080403060506010302160b061512150312040b0c0f030f0307030c1d040e011d0309030106 75
    0xd1030480c420444c5038044c504010b80900c048020f0404015416800259500301040540302c0300904041d0b040c1440c601f000011050030003420505c0180c22191190300440c3c206042600d40d10226000294001c43c0011181e9814403401c0c1c0f107001e1078002c445802400400d00404801e45440614084411200d040d0140d9031038030192007600540e0101c40c1c001c81c4403112503040d07203a80c01100202c030700318400081c50458410780c5144803150340d410071145200040f03004d1003440518400e00350b0000b82828214644083c5070402020b042480310001c00c1038441c000001c580782c0342d60440314924a092170703c10340c580c0c4544440d1944510111500070580c4502c000c0b4484510740061103490b0b04040c544080d180500301085198240e0200080f40b805111740c8611101c001d40c20402420945002680c96440e800e0000e00101a00c0c0c0302e074203005c01c1018203450341180010854a10f4903407041110000788461000400c24094030380d0014000c2c5100ca44002c0d1001d032000800209900c000840003005095120b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 659789730 1250 659788480 659788499
    0xb071805010c060e0708010f06080c0901050f0607030509131d12180312030103031709030a020c0f040f091b06111c120c0c060c030c0e01030b01030902090103051501 72
    0x2203118481c0040d1810000030081601c41d444140c0e0911003009035811261180300e5035094410b80040600b02d503554810400c1100b00910030007a414004803014002c5503d4180016500c00d02020001d00c00c180010708942018059000c8580740310010300500c00e00f50104104800400c50071550411362000d10148404805001c50320450b00014082d00b02d00340707290062403181596590444076003500c164602840702040580196000350b01c00da5529818090103190152805006802d4088640c1300b84010460550003041100e90b002060b20f800c0c46d55800107001502401c11910310352921454502200c1c180150400d421850f2605912001140355442e8021140d41201180340d440c1500b01e817410800040305003902900b648964505420382c10303000340c0b801046600301e40039080842d2441001500b0041e5900403081c417408141020024581030b0040600005075242c0310b54101582c0d280c2001c9681c0c025400b85c130803a0f8025004501c0340d80c491411644d03402c40c08581031380b0714a40200020300c9284 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 659790980 1250 659789730 659789777
    0x103120810170c060d0b1005210712050702010e0622080318160317030106202e0f1509090507090c031a0a12110303160b07 54
    0x50070900c07410303110314255003490810828081c014031400303480f21030621540c8100281c02603000300d50000131004081780401046040910340c5505004003485019205480a4280d1512180d072001000c05542c501070201c40141d442d2107145100c510f08424400300303c0d4158000e00c188412281120758035112208181e01000340b503c0441c0b0740202c40d5040c60001641c4201441d08084070300d00344440112251402c40c00d00304550082c1900b910111030405c1400000b160b134031046401ca8003120303d15410444020081014902d4980c1c150124405034000c40c5020840840071540420910603090705158800c2d640c0d05200e4042e03400780d030070448607400320b000510a2100751915040001c40442c034120307241028020f01d5600340c0d070a020b0007400091203205401000c50000096a0024510442440200350b81d20754480ea1b60154018500a00c103903a50001c1c981c0c4803a4004010003072151207040000e1541c420b1400400302148018041d8080285002100d401020951614100c000c102c0c00c200343c2286 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 659792230 1250 659790980 659790991
    0x30c01050f090418061416090b030a090c0306020412030809010b1815030d0f200303060d1e08040305120906070807050a210e090408180109030b010b0301031208 70
    0x8008020440841c5044d51000d200c503030702c807200070003900d0640c0c03510005c40b0b603008103400c40441c1c0c050030004100108110b09030381040d01d040c9035481e14240750450fa813501006010700714590741c40c24032006000030480305500450340303d0020365403261690030320301d001040400100c0100e406040411200344060041c0214500040c103c1d42841c00c151062071380d4001c01800080ca00d40500341d544a4584090240340902e000f6500e81c55401410182c004003440580020580038960711000d68018081c04001ca03500080120340c00f242407225400c10b0101030b01d2500e0020b50030817851a040b820803c251020f48203e80c01a0305803460101e0203003801d1074501c2440049584001c080101c1000507007074802820076940900102ea00038a426078805a41d0140e02051618914940040101c0581d0208851941c424141c030500700904040d520100c0c2070050000c00c201c0b00461842e0000d41d640f04e402600b0003541c02440c903102c0355a45014454080e031082c0000c2d03c40071018020f01c11090b00401c2c000d800782 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 659793480 1250 659792230 659792257
    0x2010207020306060f01170a0c080f0f070e0a0f080601030516030302060c1b010905330c0d0b060d021306030612020f0423060307060f02060f0a0b1c02030c0105 70
    0x1644c41904101c0d403801000f5240c0c0c107000401003500807103407003d40f040748990700649000480c962030707c0010b848094000c1040c002035109408102c100031144c4021900883c860411015491103000050302c040b041ea0401c00000100303020008000d040011030a0481c1d00500035680e1504042c1c4803c00030905034000503000da40400b0200e00c2039103101c0014000710800f11211168091040c852909407004031074241c507d5072142c101030319082c2c10140d410302810014000c0f0600000c440c401d8045013000203000101405000c651914000c101381c220075040b07107000b400a0f0380c2e6032950348072200079080402c0d03e0507407807500c9001084043c040d00c0f4840c19528a5203038021850041e03402c12040f944100200e036082a110104100f40010030024451000503914102006d03261507828949040916405602084904185804840d80100f401500100729142c00150756a8456000014200364200c0c1900328441c1003d00f055040019404400c03e8400c070b09a50340c60fa070440044a0a01400746c0c0d00c0043d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 659794730 1250 659793480 659793493
    0xb0705070e071b030c0218010f03060b06090d080d050108030306090402100311040f080c030705011b030c02030d05040e0601140d2313021005070b15280f06020102070203 74
    0x42074110301403541e20810314079160702042004200c8601c0403410788001c4003c90b800810a408500d82402c1d4000e088400c0e18500300c096141c030500414010b282c4c400540340070364402084540e511890205c0d801c14101400c4550006034502c0c00084507400140c046541511344800410311200100c100c0340261001400c2000c13688968081106040c4101404801d040d61282c2c0524071300181e0002e44000c10386004010030513464a4080c90801c004800307518425002404103108581e0801d1300191300740040d08514030303035501d245000d81d030452801c10040c4d850b01c98000290303413241c0e03c84020004c0c0c98006008005540f5003000650f800380ca002c0040a00c0c5009100988403040709501802a00c00c0f0b518a4905110440402c42010082628101141d0b80808618815418181d4400c21581181e20340309140c401d15841d15034100e01d01401118421200c9503400c030b196034550161801c8980000d60400b08903507841501d01d4514500d100c0e8852812000302c0014000340103101782c1d5503254018001e40103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 659795980 1250 659794730 659794739
    0x617010e0c0c0f06150f0f100c050f01020f0306040b010309150e21071a0c040323010c020c0301060609031524090c0306050402190c05120a020c0a0b070507 68
    0xd0075003090701c42e80e281d4482c914800c3e51400c01040f096019030181100002c2c40304a51003480203101706400d01c0d60164003944080302254494076086807680c185854802c02600307252401c05c2c00d05810300d0a245056000dc95221400c1c0800f0001b10b004007000c0303408110b10701c4200d00550548121403130242406032034140080d00c2040b160008102460144241c032407520f2080404003210320b10101000400c000881c9200401801208200407850351480c440401c3c607082e0001d0030705118500004043d0f00100c8058802000c0c214a6051890038800087c0110384030040000d503100c0359140f03800d110f5030800b00e000a4590291103035600f0b50750000510714403401402000806040305000501c0300c0d8100c1b503400142c050f007038039411010384218400460001c081120090944920340c001d61f21841c81044010300c2c00c8001d01c0c1d03a02e000d03031103402c001d40e82c00d00d41e042072801c02d005800d03003940b205400a51a04510b5000c16010050403048a50032032050f00c60008a84074010b0000c010407a501c030040900 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 659797230 1250 659795980 659796001
    0xa050c12060604050d15050117031b12040b1c1a060304020f060307020a1205270411031602071e0e09070906060e0f1503010b0a120c0203040617010e 65
    0x6910440c0a40803a14242e0f8540100754010171a000503181c240032400d81d059201c20501403140180904080100589042000740c1d0b143e00c02c0408408046040c82e0100380340d900248811040c045030750030410b80301d0303598580e4000f00e80c0c0241c0382c0360000700d0386001808850300c15203d5400c01c0b03100c904c00c4804480c041428442264405032060340d00400709400b210321039441c5c0005611500030313503010300166005403601a0212505111311010302c0b10620080311030888038140c050301c41a5207003c5d00310f035040c0c40340414020504682e0100c0c0e070000c00002c0200e410505000c24030640020ba003201c40c1d5641d02c204881980050111201500c06440010002304100a51f11a0001d4446042c0d0b00010354401541e000c4445940c850310200d100089118107515000400540c0c2c200d007990015142c460000001445100c14040c065000c0c0b40420072001b0588a070082c201004c0708100100200c4551001c0695030340c1141c411140090101d01b1108896103810310114102d50b49102d422100391910031100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 659798480 1250 659797230 659797267
    0x100903032d0b0409050a031713170d1404060204230d082802060a0b09040309030b0a09060617070b1315110d090f0f0602070b090f030616080a050c 64
    0x15540315131a084e075000450300502058969501c20f4581c10703040158404401022000101110b503403442d58000340c004203040d1161001000307550070b60140c2e40c0c86200b040c075006160110280d800d207032120007040100400c980c0144203456202d048861015800d5203441c100008408166801c51985800f120000d44040c0180c1240320b070888081001c000100c2586c00d61000c02c37654000140d0101c01440552a12403040101c18001a0b036104650318041d20041e004c1a01c5100043c1502503100014815614640c05030001981c89041444140d03610356400039100b41884d00c0b50381c0381c041c070000080d41000490803104600a800038021445242c012140b10300d0b640045405c00384424400340008181d0148115817400d646c584442000d00e09100c1c1c0d00000d0142500714500c2e00c110880c050010a80000c0c00f64116002d0040142c0d03106091004154031004a090680d01846050140300e1a44504030f0018403e040759692803196a68501c0403a003075480a0355035040b030140401410045403400d1140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 659799730 1250 659798480 659798501
    0xe070f12020a12112203021905091303020c06040303020304150203031909080717070605070f0c020f21060901270f03030b150408060a0213060f020f100903032d 70
    0x75084c03d4450110a242c0c14803104400c10320285a00c0c103004501d00300c4900e60304440181c44007209203040c5000702b10642300c058040c0c100c40d8160041802010300c00c0228595801d8050841500c55940f4a80030b13549421a00500020b000c51040c0f0f888103d00c0002903038420508505904140220301085000900790200143c504035410007111020030490114651400c548159203a511140341c24240d0440c0c00152154081001034105107628542c4042e0500240350116800c0040c0c6110100080d1400309409007003410742d000705c0c075071100c40c400441d1291107070040c0c00003480f081c600040c0890f036050340001c0c0b80004d091410304c80408a404402d56580c0701e071003402e0025a4903030120001d9140f181000d801f18201c60002001e014411b0140038483e040010746405508264a00c801241d4448031401402d003041710540b18000100e00c01c00200900300e1022043da84801040100000940420802600801d04182d02a13550003041c8400d00c3c40d0100b00003020b0640003401030410041e0803500c0c2d5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 659800980 1250 659799730 659799761
    0x20913050c101106040804060e03060f01140604090c09152609100e1c09080303070807180905060a0b07110f01020106080708011401080a030c02010c06060e070f12020a12 74
    0xc10f000e40c1030100b18050049004080041d1141e2030b205009080f1400c00000f90302030f80000d42400b141c04000c4001c24156002e01e00444400d40034000854118006c0e9400100501c0c2031000b01d410254114141c81d09503010701c980f04c52460032528054560a50a104000203000400c1c2c40c40413005c010710003580c0004008090350701c0b244904408000741c1d800001d001e14079403c80d040c0b1540f9074152141c0200d503d00355040c1500214035001810343c6a0000503c40e03c280a82240022440381c4207401252107020310603c8440d040362108010b0005000442d00240034a8101c900400d542c030f00902130f20441c40c4d00c11000d011007043c420038000080126a5038a041d1364841402152030782c03090009201500300600005052103088403c0c5002c00300c11390000f0a240c015004000110381c1c80410324104c241c086c00c0041c004150b61030a100148629403089841c03100960901204a40c000311001d41460190745054130110403c07180f404030320981d901840400c40c11400d800814059803c4002103010542 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 659802230 1250 659800980 659800997
    0x12120403110a03110106050a180513080d361202031611041b02030f03070905120d030c08071d0d0b0c0c011b05030c03091c020109020913050c10 63
    0x81c40c4500d01180c040c411004103460030084005244240300b500c0c0186070481d0007000f510301d0b00c0d15803401051114510710903d40c4940004115070b03401000740c280e8070340c404007069403801682c181c44010402d405106041005001003840803001088c403036485e03540c1c020726038440322115640d403900001031540031000394081800700071031000c00c01c940e040085001d00303031070007e14041204010488080f0302296404445407041c1d003081c26400415034005036810b540d61541ea40380c0c0e01040e20300c0301459020590207680c1c80988407000001140030b044503030091300e0070300c4905140c3c2c1c8281d4103400216001c000185040c101010000501310075041480c0000d030418030600040e850b014108107044a808500c0710b0001850007903060244500c006421400c004400600c01440c001041ca1002410b9010b10030804000704034400000c0c0500d04661400d4009140d2004c82c0c02400380c081e1075015402d922071940440091500c400c10701048100d2603010b006000700b107042c002040b02c4010b4524500003000180c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 659803480 1250 659802230 659802257
    0x503040609150822140a030e060c120d021306030b01030b01080105060d0908130305150a0504050c010e040f06090b12010204080a060e1005010e1902090306060f06070602031305010605010212120403 86
    0x70140180301502c00040d001b21041c03424043c2c04d400c00381d52200e00884040200c925021804103100c00700c0c41c801512035aa44100840e440c0203030081400b03180103002031400c001840b030303010340c420205260281c03030920950424400549480200740714003034019500300001a0f2111656100c004442e20038800b19090a4070050301c44089003164004461580c8290700401401058205040e400a480d140034802882c01e51b41d0591981024224907041c44030403403000c18540c0c0c0b070360010028813100c00d40c01c02c900d60380d611405010f420000c1000d802a42082e07540340c0c191806008607401e460f28000200100c03006030b61010028042c40f03402d04100c1c010400711403019440d9000381c0e4000e221048440c1c0c61403d2403903102e04403485808a07210003502c100041ca00e140c5000c124540e1042c411a027906400602d031002c10700310b202c2c10000406440c8004100b01c030240130401280c1c0c00c140502c000b0000642c41e103005903694480b5541410548038207110b034056020040c10007030b500c50b03c28904520142d20a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 659804730 1250 659803480 659803493
    0x120e060415201201090e1c031d060a1a01020705180408040e0405011e0902100807110102040b03011e0b0403080d200c01050f0705120c12040503040609150822 69
    0xc5009503180c01d600c0c0d00403c43c0c00c45074020006c0f2000000c02402d0b00080c1e8124040240e0000d08010b404d0680303d54070807903203440303440e48a401e072251002038030182c0ca01250b28400611903415001004200003240036055440040c0e24800c0c2e039409031040c0f021400701c08c90f54028010041080300c04220812000c6900b606c6100071600441c810800803c48150030131024081a4810052140d018944a81d06026940300d26154060030503604010031980c55103a0212400c11824550a101c3d41c00080c0c00a00003c0705001075040340c03a820000d24101c0c0c804c922050101686e032080d40002c040501041c0b010904800050402d00b003c07403000030700119500c2e0700d5104e4035540c0400038040d45020881c104140d13400e024095101c2c103400000e03006440c25110240041c0902d52050100802d2400022080c10b450000c82c0d051001000c00c0443c00d1038986407255403075105004420015201c6100060340d2184c02d050b9001d19009030320b40240325602d6034100200304650041540f12008691070403c00700d0013 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 659805980 1250 659804730 659804737
    0xe0a0902041407091208040302102f1002040f17010b0316060806040c0815010507020406030807150c0207031202151008011a0906060a020f030a120e06041520 69
    0xb00350091140b500000207404150282e10800500e40c502d1300750320000780d11030b00b1103041e44e90468203d030036001108004c03901c100b440f8108000c020b559010010340035952490b000701407104001150b804500c2402d6107010707801944610901c0390b12501c0d0900104038944966806070341c02000000302d03025560006407400320305440c92880c07446100020700110390721601ea554007100688050080140c0044020f00f08040108224006090b40c45d0640850f84110115040a500144140f040e180c90303040c00e42c0c0561050310100c807400010120000304020b1070090300001c00c410b03000381c0445c511b992a10080c003c6010034890440c003620400c2800b0b41c40c0013074a2405515144440b40d8a14204075080d0700b100e1401a08000b01c251002c0c44500766a01c481c98190303c8402510030311b45030100b4001c1031b031a00b031982c4280c62681c003011071801505075000c12040160708030303c0821302c40880310641c0716031110000d44000e40088028480400080255005401e0721140d2200d40e020340c0306041810f205a40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 659807230 1250 659805980 659806001
    0x100b03062a0d05060405090a050c10031401080606010e0904111512101a0c28300e01080402150d0204031b080d1d0a03080d2004050a0e0a090204 63
    0xd982c1c01c00d11071a402c0a104080e0312040000042c040c0c806241c54276683c1d000c05e00c003500d01c249540b904115485110390002c0515010004007800c1d1035865103e0203445900446240340007405070245642d852400d0802140115080407200032490058000d0000e5080000d80e1040036060400104210042500040c0d201c1c80c031201b000c07188141000038445a01829214425072190705004107170304210b01182c0d00c40c504004282c1c0507554408544040c11440070301c04090100480003000c510985c001001c2c001008008a08036410096400f0040d0f5030319820402d0740b400641d00d40c3c0081c0c01414044440902d40118484040c241017500c50300c02c3c141c0c0c3c000d0b08111000d401c00000b145440d601803500c80098000b68004e84007031850400c004085c005104450242c0d103030f9031f030401409074030b480e48288003640e0090702c3e0541e600840d4031203034040d103412100c4103c0550484408059008500c0a807420f4500081140200514001d8080000b603006424070785c81b12741d0b40243c60010ba64901c02e540044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 659808480 1250 659807230 659807257
    0xf03040f05120a090509090f0a0f030e0307121416080705130203061c1703010902040305060a0b1e030f0601060917011509050a0212010e0603100b03062a 67
    0x410034900316007002d215800c2c074070b01400240198a00240c000d0b03004825a002500c02c1c240c00d40d81c00b115030740351403160302e401006806100c50b86004d208460301c0a01210b4000d0b200c44a007440b8120038140e5501e6a03100360100709001c0110ba4000a2054258410104801c0f00300d6110507045602c07000b440302140c1c003a08003588000c80801803400e104c03044c851220815801141036142410100301804070401c1600e0505491010202c20862820f00c0c0c01c04400b48080c18545030340e1141c440000035485808292494410800000c5c0720200a01942100480141c4518507810004116070b642c01000340b01590306004914401c540c408003000030500074500c641e0f8252802d803900c0c000140d604410713081c00ca441d905280c1102c4031003402d15500c01c00c6407101c0d280080c04d940e03070304000340c001d0080c14102403081d001000000740c072081c0721030205c0c00380b50101d058417484448144214211504520840d4068102400140804100c002c8040e0301001c464441d5903640082c0200321125401000e01c140311 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 659809730 1250 659808480 659808503
    0x1407050d021b06030906041b091506030e0105150105130911070309060206130f0c080d09060210140103110a051011011d1c121d1203010f06080c0f0304 66
    0x8003481e0040010502d109036042032660500700b0140380c44201c0144042c0418141c861020b0400300c04001210080803401001c03c48009001607141c1c8c4001c05200b4040005c1c1801c0e04001c11140611840e40115815041000980d2842c0c00548054005405a0006522160001601c81840d0207160080300348042090f41d42c0311107140c05403520041d41c00c9102190302c244100f10100c4003202c0301c0035a407600100100315a04042c60040a40d904a401c03c0545001e001e1245020903048081002a60401d07000d4a0064400e2485d82d0112454058110282614200104045501454558091031000e841900840d8407940440e100702401c5d008a0001001d0316034a2401039020300c1107482315600c0c800a40100c0c807404c004241c0e0350780d0b05400e01142070107030519030789c0d801d0050401056094944400b808854211030b02e070f00d80b000110540d180b0600070f0b13282410310704841000b103e041c6c4400c059003914130b504010707048070550002403191030f0341d6000f0031600159054100146200354030402245a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 659810980 1250 659809730 659809753
    0x210a0f031d0a02090109090b040305070f0c0612060e15270117010c03020a0c0803100302150a02010b03070b0a0807050706090b06042a0c0c030602030901051609060507031407050d02 79
    0x6210744c0503402100c000389820500000104851021a0842c4d018a02241c0340d9040b42004213800035600303001496400c2520300040c0140d048840303c008886410300c20010f5030768800125175286400c0b129004044500220080396140500c110707a6000780c0c92100030700c042e1201c401c41c0175550007030700000f00b401d64060016803104400d0041c603510700740c58a415414030218071000360400c44110707402400c481c404000110100c4848603500015500107194808002d0314100d44541c40e880900800019420034036000124240050104116500c0482e281c1c508400014200c2c0c0e003400140814082100400c12040803d02d180143c0c440b4038082d10380307604941040002c0204641402a41031103030000e104454074010350944240341c00041d242000e14600d441c174a05103800060703070307000141410b10206c02c1c0144000150b0215100d10340ca244070312446c18692030203648544861180c4c1d400603c0070411b40c00000c0c450308907511180400000103082140a54900d400d180e1a448000d0040e4800c42c4c180d039 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 659812230 1250 659810980 659810989
    0xc060a360807031a04050a0f110a1d0105011404081002040918030c02120c09040807060c021225080a030905060a020909010e0915070c05210a0f031d0a02 67
    0xc005003081c000405200c1c1c0703140d440c58121160140590031007000d80000070b0a200d402c0c4140311035030740c2c444010345c11114540b600d4403030002d103041554041e507400302c0045001d0000101c0c0c0308400088404c10101c1da8601401140c0344406d0407001c000140d000d0000103907808040006d070b070b0501c405030400750b1a1418403080781c04603000504081c801c9110444c40d1400f107500b0181001c417454042da4200c5841b07038252001c9103048180c000d01038100040c0d104020a01001c07801a003103580c40740c072052100e05031010041b40d03514194001040520f000b0014041140140034689443d010b8440c4803c94080481d00d8002850300800c1b01c8401080e140c0500000300300050020b107a01c02d010400442c11b0203500804940303a808140074454061072108007241c8050410090a041a407007040ba0559610f44064000c0c9812001c103c00c581302e101d1b40c00170846a4005001110501ea507a030341d00350404c0001d000460b0070b4800342010009159603074040d4400b100d462000220f0f4050746100030882c071483c510512 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 659813480 1250 659812230 659812337
    0x307020a24030614010e030c130f05010803030405030313051f0c030e010e0a030309050c06040f030c1505030403030b1f091a0702010807270312200c060a 67
    0x78800c15140200900c01c489046149042041080c40c02ca1184c020410101c1e25090b140c400455002e501c0c000024070468441c0c0005200345041ca00c1400180da80390403259aa00040da8003e013190818800103d900d1065484247c1c0f0900920403655415035079000112406040317503d5801d540d445040707550031607402d4004e6081c444003150080003840810302221b034543c00000002400c2549405000c1d0034040108040030300030b04010140d50f99541d4888200c841e0540c54441255640b401c800000385500d0400d41d400780d201e8480c1c0f81d075440d5a680340e5040b03004045a070800d55002c01990788040c83d41d410907901442c40039894882e440118100980b0032208011200c4070080040308000703000c0180d034004001138201c906070034003000800038224441c10045641180541d05803d80300000b00f03000c458000c0c14168101516403d101080c0324600c44400c0354807418001459018400c501c80d203003000300040882c1e58041c503003070300030161204089001d0140b080d074059100803040260501c089004401c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 659814730 1250 659813480 659813549
    0xb071109040302070501051305060a03060e0a0908031503150901021b071518080316231c0e0405040b1510080601030914061e01120203030d0e0307020a 66
    0xa64a072400c1c0c0e41c029a00d0b0305030300079a03040040103d4040641c0ca2001100301c050140140203075100c42403100010014000342c4210b602000d00e5001140c411400c3c2d100d21840c40360001d16a81c0b4580c0c80d6050304010070385c2401d030b45406100d04504000301940049903503002e41c60351400565669106801c5a0340c510142081d1503882d000303176000700910ad55111416028104500305050501000e0050720b0310724141d903000a2950000003520151a649000080e003040e00c200400c5481c0303681c00e0382c0d8000e01080b02c2e0b000c010b0360788030a84400d45a4000c07242d12a06c40002d01d450078441207004085000e4902c01c0d20110b50084484041c404100940c000c0c200345400191400c00d224a200c00d00100a0f180140c40241455030320300c503000501202104181c0030840301c0084680c2030030320605008807004100319510581c902c44002140100d01e840410f80c0442e0018002c40c1032400d19144080141421805034625210070000040103071030b0a00c0f041b000384044801c1140d800150040c003011414440c1c0d9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 659815980 1250 659814730 659814739
    0x50603070b0a021f11070609030f112a0a080a06050919030c0f08070809090105031605012f0601240804082209020a020c04020a0806090c130b0711 64
    0x388071165002510124000c041050f81619140f1504500c0003000400d501791001140001c0150600815400c115907051003a510f000e049002c0c0b62084500b117a2014a41c00160480000b0000080141e29402c07090042c4050419200320400c00040541d8055030003003282e500415030a80a0000c80e02c200c580c8141c00d2809041a410850071544a02d080c688000303041c000903d250700c00b0b0110090194440907404401c02d40d5640840c02c081215400c0408402c1c842d0603104000300b107034140803400c840f180405041f0704200c030303060000548100080700c0080104000c900d8124000105a0040c40240038030b940203882c80c2e50400540c4201c0c0340181c02c427403880741400364120380c815503c00705640d0f000e50084201c50b21054140141c1da5801501540381601520030f58002c40c034940c40707030f0003880034150580031107815042c3c250501060380034110f511004100110005092801d02440f11680000c2c0e09599074901001100400c050f0304039a0484551064003050603000c00a826001c110200f00484 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 659817230 1250 659815980 659815987
    0x81f0b060a05031305030d020d0b1c031d060c011107050d081303030504030c0501090c05032a120a0b010305100614090718030b090604061b09060e1c06050603070b 71
    0x840a4014403010703203130308084a11040c407001484000c0c030a40e13407031540c11030781036543c0c084049040d00030b401d409100740c0c030400103024480c00310100da041c009040c0354135445405032110040c0e85e9803007000c0c162130140d170064410002820800c2c802e104083c402d940342c198081c0c60321b2003401e11500d0840303070707620460920041d2001d201810302110703030200c0d603ea40351401148a035200c0c81c0c00c44402015020061141d800e12400001304448201032400b0398200303604951a505902c1140c400c800391883c0c1c80c81c0c461400c54240041b070b00300410a10585110441140c501d045596144c0702076100c240d0080d91150841d0f145040e901c4424028034000b841040404e4460002c036400103415a0f00180000c0144051403001c0c8a00124201e622801542c00540e00c00386403405001490b00d0b000c0840d000c540c2d003841e100f424600480d10070b0002c0023074003090b900c100c3c0b16030900c1425101000c408a403a0381c012903000e0016030726500c407518040c2a0f889001d000c581070909000345450220140c00000241d00d0a1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 659818480 1250 659817230 659817247
    0x6050a1116140f1c170f16020a02010801050405040c03050a030801050f06040b0306010320120f070302030f0408030402130518010b06030105060d02090a170d021c27081f0b06 76
    0x9854030308040c4013141a02031202c03040c042d030700900c444104030078640002c820051009401810035115180c4210750f83c895450314403080b41c036280c1d031401c000d0205030680c0050040d414180d001e5039104e88140c0c80e10700c1c03840c1c994480394505002964103c0c00034851500500c910300f441400002040815200b080c141400e0040d4001c2c7e0303000c002c01081c10075680d031a2003200c00366a1000154000e190f0683c030359944555074155031001c1ca00302c4000c00c240c14042d010039161482403089031b225001c8050f400a00740c907140c1d60f031940c55001903c140d91040100d012903000480a10505010f039481505034a081d2503180001403c0da200b09820a1042c80240010801a161b20702282e8004400e50700040e074900c1d44100090b0b0151b0769402208030020b1440ba244600f0360001507040c41603915400711000c20505031480e106a0b6405961000022951080c116100b884d1903010301c80c000038440c40c41046521042c800b49030400c403864240811001d500c80d50107a690a100f1626488001d96940d031519510 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 659819730 1250 659818480 659818483
    0x19210801091e06060c0b060a1d0c090a2c19020a121109011101050114012a030e010f030e03191112040905180a06050a1116140f 56
    0x14820741da041d58558294540102e8000010000e006107440d08000c05911024014031940c1ea0b2001210340c4500040030413654606113154804480c550300c90300720048005c2c140c1c8050071001a0003e43c0840c03090120b1320700e40da658940c25014202d400d1411808030b81e0000c5d00030b101840c0f0810b00105084480178041e82080e10741305011080e404020159035403c40e80000c4402c8090203482142c550b28001c486400c0440e04001004030000903070755a0200c841c2e4952842c22a8020310031559000400050a81c45501a140c002c4132000c000301910003c020448031100b000351003072400c400103030300e038103000d0010360308044240c2c1ca0004900c1c040150b401e000c0202075a81c410b10030b61000310001e00c0400c882c01c2e84114209007501100c0e40a40704809600b400200e40c0e0342040c05401e00ca030b400c04001036a621180481d0740c0c0d0034242000106144c5107103031503820082c80040c00703015501d500c40f80e495103251110300080881c542c1c0444c0b070a81220240c10403510410101c403500c0250b8021a0089402000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 659820980 1250 659819730 659819747
    0x20f0d06170705010f090905090607030b220507050c031204021201020406090302060d2a030605060906030f0402040e0123070305010b07121701030302011a010e0627031921 75
    0x428240348002d01940e00c5e040d2468000c5170b0021070004e0400080054000010a205005004a48051103060180401c1090115483c44003040b01c0501d24054444000c440c0c005c070b43c01070401d08100d0714224007620700ca425035003c9508000313072260b408180710450814040020b0120b51050085042c40c1c14a41c0c002d100c0c134064440a0312520f00418413401e643c52550003071590764481440b11400145440ea506140c8990520a1000c40d20b03010b000201d60070f0038412510900c800900c038a2440e81c410b8080c000705c0750064000e0340c009a442003409101c0d1401d00c40d600d01242c42c0c2a004454504000c904041400005c202908140c1080300402410b64003d080c0d4072100d0f8000c86503140400f844208840540000e000c41180d40c00030b0300004141078066000300618034000c2e41c40354400e000c1c18010f44040c0b2a8529081c0c01590800c1240600d000c161100600180000c010075070180589001a18042c110454a10a00d01410700704007046400302c810802c0d1200c3d50000080304c10303039000c058615030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 659822230 1250 659820980 659820989
    0x307031103010b060301030b1602011119020a0b070306050a120201050f03040302011b080603100606080c07050715030b0306070e030a032d030c030e0c060f070f06020f0d061707 77
    0x25841042200c0c180c1d02034002c0000a48060312040d2a581e581c00c0100980e402034440f0008a654502a21070380b07071040c0252151701d080d1061061a02c90140c0d000955259403466440843c0120b550304c100240c0442c034143d01071403042e40d01007030040c04c04042001c0300c8c1031988941301d940080c2002d03c0050341c01c0030554071202400400300b03032a5a00c40c101a070141c0145060b50028499101d4000c010030f030080700003401448280c0856208801551810044840c20f005d52008204044009403140c0c0d40d507001070000f10b2042050b42c9003140d5805801d581188031005103c0825110320b50346113542070404c072969114201e840d0030004030f40e0000110351510708406014040041c0d48082d641d030f405035550b440c65007c1c80300c51308440240b45110000d0081a2212102c0f0001f400c140e45814684000295600c45620041c280d52400c4010081d20034103500c5048200c030009044600400802c0c15403000e8400c485014270410341d182c5014240ca011100c894101c803040c2e801c580001d26008000191410554 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 659823480 1250 659822230 659822243
    0x1401090f15050304031404030507030605060d020901140d0501021204050c0d17070206040b0d050709080a0314071a01180501090606050d0b010201061e05090c031902090d060e06091b030703 82
    0x2900c4604007201d041210303801030406d00200217400800c0040000303c1d502101d001d8a01000140c45040400a511601400281d4800081e80041c404050010307201420700500406c3d9002003100d030307980c1c00d0030b90700202000180194100100020302200740040100500300b110354800f444910f80d5806100c2100350b21300c0c0182c14001ca03403041152146c000702c5005c7d1880c41c200d00d496510000d0424043c0034100d525000042c049100010342c100002284841954141c40742c01d0100e0714040c2001c40b541060800b43c03901e88142164907417200001d1003150291818516410010144494980c15510f069121400c1a03281002c100705656000099442c200e007150004aa010b80e00f00c0100d024040c20b801001416010305c81100180a20750b080d00121581540d0111669030b40b0300741040103010456141c000d0100c0c03484004c200104543c01042880d0f4000c114074003081c1e10f03803501401c80f54081d0170312003180d01640a0050841c0e04002c0c150008501c1c44c0355000c02c001350004a80c80d070320144401400c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 659824730 1250 659823480 659823487
    0x201090b090a052104031505060a141503190e030a03050c28110105011d09070509040f050a0b0c071506080c01030b041d010212180d0c020105131401090f1505 69
    0x40c04604c0b0102c0e4000e581001c15454a90b64403856100180b03130595001c0d1080c48401000554621806506102034000a0040f000e0003c86c041201050388024140c15003960a000301c50020139840c46400b1144038071100440d2214000703a80902101c40c0540004115103052082d000e01d92034140702441c000007000782a0200443c1d40c0010b85000c000320200c4142542001c00206800801508510400c1e103503807070030721044c2c40d103078409929582203001d400e4000841a0000300460100900043c41900c241c080741c2890360b2070b46962504880689000327080c9000010100c00b4481c2d00806102400d99070039003001054030b010903265803103204c02629810302d0786078050001c00303942c1c6038404c80c0b8103d481c2868841401400c2001d5000790704c03443c11300054488840c0420032101c03074150342a4500800d80000c00304106100420341e1260401c0900300c0c10000d081010b2a4210b070702e00c3c1c03044001c110340c46c141106070545100140c8008000e4100d200420300038607042000e0746450080304801c9900e818602e55 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 659825980 1250 659824730 659824783
    0x3020607030c050f1b061201030f08070c0605090f01020c030705040f1d0106050324010315020d021809150102060a05061f020c03061003050a120e0a060201090b090a05 73
    0xc40804948000d0f1090044503c0e40007010804280580b0343d489940c40103268136010005c00c0420b000d070f604c81141542c85040103200003000c0c113a0b039451040c0103a40741420705045541e400000c441c035400c110300140300450f4494081c281248200d403035241c24001740000700400d1022a070340d01c100d4450701c4d10a58486000004102c600e0f4018002c50504000031307480402000d100f240604840d204e80b034005c0c8a14200401c0e04980001481e0307401c8802c142d03d14860b4695110380626000c2a00024002682004142c13044401ca2004043c0080d41881c01442011000100a007078240100604105805c80c441992140e074042241544440c4039240001e058855102003101c01c4c91102518010b00c1c0304680e11003110307800040652039070382d017207007114502d90f15035081c0c0703002000a201c0200140d01c420300d100c0008080d00c005000340c00483c600349518020017030000306588155440580540d640f0306520051103c0c440241e980f141e100380051021360fa45540b03ca40d40d40050480d82e41107003c851a500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 659827230 1250 659825980 659825987
    0x5010504050c03360f0d020c0607121b0f05120f160f2901050303090f040f1e060303021e0607110a020619272d081c0305100302060703 59
    0x9110301312403114451401c4903c81d83c5588203201e030351203c444d1250f0150300d0f03001c510029401020a40282019081170b15503612030b000c00b01548014801d00001030341000c101e40d529042c104109000b002c191511030402e042842c01c0c5140f099078100003a07001c012000d41b024840d812240d8800310718801c140100c0980c20300d01820a103444004100c510400e003499a01400203401350009440c406c080b00860340d0f41e000b01075aa03c200b87c0510b4000841c0f0141000b285040e50109115006103180414031007003110120140418000b043c0e043c880d0b50310b10070710901da410007540b0141c0d4201c980b404188101e44441d1a81d842c0000c040908002c0400000220b442c0c05120904134103038007500946d101c1f07204403903500441410b0440e40c0c1c006500d6100c82c091251000780d5071030382d02e160405003981c5035060a915900c11072000e6410810940308005191645800040301001061454003a0007589103032200582000c0310f00120004043c00c005c20321141500304014030049a904688140d500d038010701e02a03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 659828480 1250 659827230 659827291
    0x6070507022b0212070503060f0a020c0d03020c010b0904082a0f0604120503040f03050c031606061a03091b0f04020a020106030c080123040f02060708040905010504050c03 75
    0x2d425890000a0400c07000c144082c00109207108032078188018a24109080c1e452055118203685940310001054441900b80704c1240c000101c018098986a8081e054500d03142d100300302140000c0c2e0000d0781c961080020303c00c0c51928076048910816a08082c0c440000d10f02400d0b0002001650b14402210b80b00625002c42c146100703500152036070b00f91100e031b200b522030070704407416101003180e042c01e00340651042c02140e100d581d002c2d101c807030011101d480858090f0403070801840584010000590781b01c0d0440a001982c41c800c1e64013140c411b08103c01c0501d42c901c580700c130081c440c0051051004070040402d00b04130101350081c491842301110000540c0003941303181840d030000d100040301000c080e410b4001d40d042d24000c5107460f01c1e0a5444501500f01d40d901c0e056200449440b02c003a03a10960410b001344d400501400718010348101035000100280e120a1045886030740004003004451f406000302e41c01000f00f101e00300614584030103c04080d01c03006204950103c8106a40c0005d0611000389 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 659829730 1250 659828480 659828509
    0xb1b0306040e0a1b0f09060605180f0d060501081501080d0e030309040515090603030f0d0b03070e07020d020f010b0607030509210f19020f13140a0204150305040201020607050702 78
    0x804c4115030305100000d410a600e80201c000c0c1c80c101000201c0d1660160168800300e0b0000c2d9149850103030002c030003400d0440403003c203c3d03100c001e60141d10030720746d1010515005203004102c0018254940700485240640300360000c0003a038007541c0100510207002c0b60600005005092968010720044002401c0d0f11a211701540c2c03091030030062010076030380e181a083d82071000b43c580c007a00c0c1d2610f0781010754a002d2041071a01713201c010041428100100d4010050b500d102034203c6100765111440100740d030f1400c07152000168860700d000048180d0411003441341781030a0000f00000c1e000d0401042c0325104100c4064103000c400600c024503515a0907a6040030700c1c0110b00c4a03201400103c0d07842e1501070014002c5498032440903e13060010b101d5404d48482a801460b16000110400900005810f16400180e2580c0e0380c4002010b20742e68104414070810309290010703522400c20a600023010408540d200c01c041c5443e0030400141d80000305541c110b51a8100303280ca4608910026118a0413140c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 659830980 1250 659829730 659829743
    0x11d010b0a0b1e0d0c090612091106090102010b030d0c02150406140a050903070602010c02010b01080606160302031c0c300b0303040b0c030d1b020d030f0f05040f0b1b0306040e0a 78
    0x40c00e9120f502141646c00c1d215035039104686001c00d0000141510300180c40600091714000700015a403411000074886036070103000201c0e62000d0392002900b032480410b510004500e0441d075200c00c6241170504d000082c1031740403003a41003038200b00c00100150310740669094984000524481d21a0041085c0c40314400c005084034074240d00c0b42c000a029103491420030000d5824040042c0f5a5805605983e00c142030103400e1504181003290744812200659400307806600040116660300a890140e101c0341c0300c08031070301142140c05410003c0c64902022401e04a602c0702c1c10305c01c2254042c032811445024100d400214625800d06d0019086d48629845000000c3c00058450302c0d80402001806040300c002c03000300425a80c3c4603042c614034100121000c01030300300d10b0900e00d44602030350002c00c0c4c04406c00d20028110b0b01c82c128003c00c48005460990f080210b600740a0104a12100001c2c0d100d0071065a110030709006802414003400b003d421148503d8541c3d0100d00310722401c02c10140711641000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 659832230 1250 659830980 659830991
    0x109050d03110d020106030f0f0204090b010915050d1e11121006150819020f0f030f0702030a14070f050319090909020918070305011d010b0a0b1e0d 65
    0x6005850003000001000150140f150042c01e100d006200303600172285c1140410440807a140c0c5c0f035403540d00f2841070032a4007965079140714020030000c1c020980a40140d410000300e07484541d45044a1540560010744074001c801042000104d01ca075850202d052002c4254150203898900700303107002034542070b503038000000c0201d03041c0d040c4000135034880715902c1030420800b1b16192404c19a001050010a8004c224601d010a91041c1031040842070702d04094030042c10485048140001984000f004003444500401846002005200c0d003d41082d079070b0004514080340c081d005800c0d086440f000c1c40b09007501040700c00074010704590400d03089a01c41d09481e941e03400030f84a5000300701c94103d407100041e21010082580c81c8540300759241d642d001008900e140d51130341d45414134441da552006081d40030f00d120000000e80c0902403509000041b001c1044070540b251011030849004c03980c110f12401d5054030403c17160b40c1d8a81150b5003408503610364161200d09828541091041c0500f2a84240c0307001c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 659833480 1250 659832230 659832233
    0x30414060307111c08010510200102040302040204030605041203092613080607140408071406130b0a1b020904060b180c120f0f060f011701030b06030c0607030e09060109050d 76
    0x2010342031000781040d110120103036202d1088c0948040942000e8000c50b12400903000345020380d080910420940b0b0001500d01a200c2d8041000e98006510032511903407110144020041a0b0b116001c1d40344c040e160401c042a002e440341c0c14240d002c119403819100d480381d12643d1404801040b6040c00401f1840f00114940e0355002d20303520b1008480d240000344869803419410031a00b03048a0480306144004d0030307241d082c01c1c0c90187c603048407078440f0f0340072004001c0186241c00e4072480c0f00c024885c61140c1034440d0704402000d8144e00c0e0910100958000c50303414440140d44900c079060304950004030010701302c0b00e0000030030703201500211041e820810000400c1000c100d564001c00314400f400c40e2481d440c0d141c9110101080200396848004004c0c1e0340e0010344141000c541c031140b402c2051601e00400341a0b0700750554890710030382003560020380ba070707003000081e040420801d8013408003590140d06d0304215460091042c0103480210380f1a40806022800e20703842000483c0107804001e001001d045080d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 659834730 1250 659833480 659833513
    0x1e0c080f07170c2211190e0f120d03052d07090503070f06140a0f0f05310e06060403201309030e0906010c0b0408040b0304080c010e03041406030711 65
    0x76003424842440c10b00740901c4600b940c0209450301810f01c00784001811a0f4032001f541c9140c803840b03885800280c841001da4007699000740103142030f698100508240d0312148c800506840e4010f00142c0c000946491705e0700e018041d0840c0404020551103040c2c1c480d2034042c0100c400c05d115030710155042c4140600420044401c4c0c4518080356609e4170740c008510b0540100c0c440b035008001701d1002068100d02d80511b2180280e40c414060b2140d4a4070b28600f00054160700b07202e440400716070321004c0030345005a00d000c4200700301e4400781102c01c0f103000540c41c080c1c00080041c4920300004110300000003648649080a400d10321011100504405200c2c0f5100340038001480032800903000074000307160000b550308015408078051101a95060042225500e840f0302040c0041c0085446020400c4002813501504e4003460141e481060782d0742d92180140c0308a82519401c0fa0380241c1e83d0801c00c801c2100344510000b810301ea6000340d034180d440b40d8031940300341c0b540c0c0021001c4140c80d000d03091003040d482d01c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 659835980 1250 659834730 659834779
    0xf140f1b0c1c081006030504080304020f120706020c0111060c0a1d040203010909110f0603012d030305190201020c060105010f1112031806090c0f0d1e0c080f07170c 72
    0x801c1340030074903010b41d02c14040b81030765410703580a0000c801c1040410058144609015054240513040030312041e5640c090303078900440b0742c1c44078005810088424403590381c411a07510507414020020b044a0510449951642c4114070191003800038405210500403407100c1d20710709001e401481103440350ba68200c03070f10117071540c5402100c1c10021a40111040c0c0b0f00f0008200c0c01a402a202c582160f090540307030302101d0781030006030070222995a0806041441c50030303140055031207580c0d0282c48504106640303000c46041310a5805590040c403602d5981140002d1060444400346800c600d04085a60140c40c105118200080640036103409007400c0f414242c0194042e40f4480a5850291201100c8c1e0362541c0c2c0c192409001a0008411900d0ba4540882d681c4440c020080422192034603907602d1402940b101032204500d4034480840744107000307200603400002d050b02da001d030105058130045c480d200d86107405500d1200c081c941d202183c0c25010042400d002d40081e04240c54002d01c160319160300007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 659837230 1250 659835980 659835991
    0x603190308250207060f0c0c03080c1204032604090c020c0f030d0806060f04050307090506031b010804060e0718021917010b09130f140f1b0c1c08 64
    0x801481102c2e4101e419000075081c54035039000c0d0040320b003054000ca40c0c0080300c41042080045e690701c19004110429100b03802107106c5c2c40e003143d40c1c0980c0c9419074204180745c103c0403041101030004001240c0030000700c40c005090383d84080c000307c503c84007003480c900030380d006620007a140c40d54480041c3e4000905080000d000c441c444c0d0314100160030180c0e1544903c0c0b501d00011101c44c00703d902c6040c410013419410440c40c003c2c60070b040e2234101080c60411143c0c8041e0340281c555050145900342402141c461580c018043c0c00c03010789100000e4020728000d4401003c0707030394641d41281009810703c20900a4441e4113400d0384819083c1500e403000e50030240c900d0216001342d5011024107406010280203501051030300580583c6000e40d03036505030300140c40c03041e003104000b101c2503001c140300c1c030440a02088003480042c00000580350464103060003800751045401c0801400011110713081c6c030000d000e200f1034119586444403c0d0541c24000014041c10070304588985d20030505810814192269 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 659838480 1250 659837230 659837251
    0x18060221060604080c0103090611210105030a11121507020307060f0b090c0c01060302030303041a100803032a032a1c020708090a0e01090e03130603050603190308 71
    0x1078441c10100111442a40308488541d40301c1404030700c281d4001e40001030f41c503004141c001400d40307040070f0340c100c40d038440568540c5802e141805100706500c0d550070103001d4501a00203240c1c081e105d656400780c0c3c401895a8500c5805022005015050300b0001a40d581d00040101465400c0c0444043d5403038000c1c9500f00e41d014144450708108181c588218100f003007000380402295210080c0d100c0507980300304e00c407100c0395403144004005a2401c0000318003e0740304014601f50891000444040380c100644456000c402521040101c500d00000f9640c10000c2010441e421680b080351000962107030741a414000b40300031040140c0c0c2d042c0042200000b040c0308281140380134024050948a12903420070b020503000c0411490840030a55002e000c2591060070b205281544640c0000c003c484103600242945a0040050150304d04c04c0c0210341c84e4044100040d410410040c1061580040e6801038508155545001500995080050925000841a030844032a505041c0181590700844440116 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 659839730 1250 659838480 659838547
    0x90c0801021b0c0319050a0b070503040c050f09010b0f0702030a0b090712080403080307110f01091101090b030c1e0a0e1f170907090606020606040b01110d03180602 72
    0x1100c0d0b0100d0702c0c50b03280000401401109030030f40b40c0d460182480e0501036516108500b98180083d1130801601d001c0c20755501d6054030f900e06850000c80482194014900a06a030401d5079a1900c0b481040303810340d20104111603c407840c8031500d402e28000ca650195141c410100001c1c2884002250a40078003408130a0314412520390b13108901134604542c00400307a0404100410214200102170350300007190782307401038000740000f07181707460003501036280c1049956800b181c1c0c04000940860848400081c04e180c1030040c40e0012050035804014900d80f2103080c0040c40a8101d1003801248081c100aa00441e8940464150082408034601c4000d800390040e0340d0540681c90000715416840c141c7c0b652510483e4440403034506003d00082c01c2c3d0240c502c210100412901c400340152005480c3d1540105a5850030344104002d881e251140a81440480c02c0040d000b014080b54415185841d0309021584540990705c4481d883e16044003e1b000c10b02c0880d10126240034910107003048103150010101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 659840980 1250 659839730 659839777
    0x9060b040b0f01090b07020307170d1106070909020d0b0301060b071a0402060a03020d090212010e01060f030804170709050a021809060a140a050a060906020f0111040e0a090c080102 79
    0x40e0341d240b416405010032480d500400482d030701480145422031001c2d003a40e80d490380d601800e945401d00388801c46102e030480103d81d03400c90782c0010020030380365001c001004141418000070b003034004507000c0c408010b5000642d9040100712a040500c030b02801600130030540380c1c0c8914404154100003c00c580307880d4a030010000782031100801c00d0090b40c00826035881d00040050650080d44149204030409440d500150050781d41c08241408114800c0c0c0041001035881114a08545154008440344201c440e8140082400340003607600340c0d03941f042e0960700b00d43d203140c1c5c0d249406030740d0b40300fa04a141080d082104042c150b8014110800007040a10b00c011244401c029181508550050f040440380d0020030101c030300d035025401d07980e40c041c0810704039588400c003041a001481c1c00ca14003080c10300307030100800745d4100725850302141220002c102c01d00135890100060703c81d901c11442000d005902003001007016038044107066500c040c000c0c0013030781c1d03598015001c2d4000580c1e0351140c2000210380e48 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 659842230 1250 659840980 659840989
    0x3020d0905030c0d1a0a05070e0406180207170f120105100e041d010e0c15040f03060b061b0c040510080a06020f0906030703051501050c030a0c1509060b040b 69
    0x40a560009000d4400080752406000400f0b002c0e5100385c0e482c480309058603014100300c00c034640c0a01010362012540f40b81014019001441c1c00360100e000f40d1609100700400c940c2100708484d91280c0c21409030b40c41e40b0604103801d00028481301f5604941d000140c11040d10413100050010848800742006540e0360388040103420010305c1400c00c04039507100c24540c02403605a1040451051140c0300c1c0c0c07007031044a03186a003103a20705050350380f09600403401c0c0b5059252a041100c000c492060049151500700304180950036411320008008a841d0700e0009007560703581058031a600f484411041101c4541507426664143c0514400d0080c0e00e00350100345020f1007103800006403200d20005103c800406d680b40786c001d5210501020501d8814480140035559000055016000c103a4002c41c01e81440c948407410f0380384040182e07041c0a020400760224070408010341d08104458206031181d0741860806110b420b44403014401c115280030f9600080040907071100d04013610070b232402c002c000c1000c020312 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 659843480 1250 659842230 659842247
    0x319020d2d0204051e0402280b0c101e020a020703080c03220510050c03090604030812162a0203030c01021308120405100509061603121a0d0521040303020d 68
    0x3e101d0300d1890b1700007a0160810754662000a1030302182e155001c40790b07220011003410142c0114541280001740b46070260410030106044440d0441c04000b00c880d080c002000030101c088640c070300b25402107140070019009100b40390003141c02140499440100b050000d48030340c0041911b003c011401100719408807203409041c4169007000e02420031100b2192003c6d1204c2e00100241c0f8800e20041200c400c1c02c1c2c8524000d00300551041071717282d413994000344024411610041650102000c80010390721204c3e0701ca0030b054003c400c1111000480914254050015007550002035007501c0b0000340c0c140c4c0c0b054158000d14405100707103501c07220b042d224600306031250b40001c44000d9103102404140441d191000609168882a00b400d900e081c040c0e20205445030808076691440400e40705040c0141600018410702c0e0244480080015100c480d0500c0380f004e055650b0140140c1e8940001c2c0c3c104081040ba07c0d4005070b400070030400720601078090402030361040c0000c40040c002c40f003043e404540160040f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 659844730 1250 659843480 659843521
    0x7180e07090e2a01051305061603080a0207030e040905010221101212080c130b0304020405130b0106050309011508070614040e010509150409030c030305060319020d2d020405 76
    0xe280783c030410100456850300038008001900105a0f0300040603554100101155005003da40c4144180781c11302070304a501c002c02c440303422801002800c0000c2d520414a20451034100c03400204022a41803841c020f008003071904004203680b0750702079a41402410940d2043d0b4031a00d06541c12038403002d0102201c404100f0003403503a12480c000c202d4860103012060b40c4140c079060468101f12503030486800f00c42081e8845490716000105100550071300d406030980c45001c00b10008100c034005d5603018201e00c814420f247c02c0090100200300c00c01000e4015540310500c0d00030f1001c101c1e44a01c030468540005201c0c0c080800c0e00781c1c0c43c1c1c2e40c8034014442070302c00705c03150310002d0707062a827808090000c2c0590080003d00d511103445030001143e80d943c85001201c40c043d6584034114401c900d40030f8110360f070281502c1e1080d13120b80684940c0410102418001c01d5054a910305150305030b01d80010b86d16403a12070904000b213042c0c01401184030340780c40403407400c0c000c071410304c0303a512280030030708010b00010203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 659845980 1250 659844730 659844793
    0xa0b04080309100e100801030302100605030307060f0f0212060f0d0519020d0602040e07081005100315080109080d150e04080313061b0e0a0807180e07090e 68
    0x1c0051600c500f03a0a6910954104441034404002c0098032600d604c503400c001146a032001807041c1941040318206188003083c040049909210000f99a4000c000000f8003032502c0c3e110340700409510b038100c091816280c4605540b00c000d030310111000c412003151294052441c4240503806440c20400791a00c03240c0100183c01c00750303501040304030640c175103c60036038002e05c2d50800c3d000021520700c0140020054403514819500b84180010300c01800035100400c030368070010081c0715a40d9070724500140c4010504001528809544031115aa049075102940035460000080c0078008500b0041a2a0054200030001c2581110394400020842d0103560f5003030060720000f400249040c0000c0d134001c40c1e60a440c40717a404e200d0f55100d0607195021385000310880405034000348079800c040340e900b1007041103981d01045030518000c15661002441000c82e40c014001c454046c030384a07640070103030030905482610038042e181d05061015081c0018140348134803c0090501500d83e20140c00300d103100304580f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 659847230 1250 659845980 659845987
    0x1050a020301050604330c05010c0e060a2a05010204050a0f03050703020609130e010b0a050d2607050607021509010c080708090c031e010e070f091e09060504020a0b040803 75
    0x4000b1319802d00c42228a251030720704545500e1401280031b845400c490300e5565408038610451030081e0946030311120841c14030000c800312141d5541d510b820b844081d0840d14040c0c81c0d9008030310030380f502031035407055800d1040345003071034401030000c19001403054400c00da401c030903c940e4503003201425441500c006403680d00859814401803620400a0040e0400103040190760011400000300300d03401c82c008001d02e83c0d510300f059403c0d400d2403030401d00200011142280da4801d10349801c5003080c00c1c004c5407000c070b1085601c03c5403038444440c103484d082e5811404641c07032850010340c081c1d92402141c03081c4a24201c0040080e10081050140c80c00d5501b40f90340c0e14485480f81d0034243c49040c4054407485880c01541500c100e82e403010480d104202c030421780c1103822000f12412840c2160b40b070344034201c1160020102130104807038910400003128061240003884451b0028050303400c80729100445c401324141180308081c4000c079009140624000c550745840c15907100c43d5401244a50322503288550000e2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 659848480 1250 659847230 659847239
    0x30c07080303100b0a0302120a0e190b1519030317060a060c030c03030e0d03290306130213050a0b040b03071409040512040b03160c030504120c0806010807050301050a020301050604 79
    0x13074000e4044600c103030030054140900038485002d0f940040b207604035802c0d5203d1040c101340d1001c0154041d21201d5110048003903800e42c48030340784080e006003120121000c49074100943c0d04e50002c0c03a43c000c0c00b204040001c0f280c5910b0024206410458485210001400419000d151441e41582114000d446100e13140c481c994040c0c40071352040d04c0517014140c0e510403000c00140280208007070f03200203a070005244134500c60790440e41e07413400108504401801840d004580c800260f0306400010324012808200920310014020003103c2641910440c00c144c14449130198641005801c07440c102c40500614444809140c1d8410161041d10b04005016004541d141400140103070018050400e603020218051105803c640c403a41c03211600013000010404000d02032207412042d1009440d00e0b00c18081c0586001b00580914064016002d881420b540c007040b8460200b10000c1902605842c45c541c0c0d10002151601018410580254201400a84040c0a0f132003128141d4400405003030a06060 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 659849730 1250 659848480 659848499
    0x303200301180e010c11070b040e010e0414070f08060a0c08060418020901120c08120d111209240c0714100207060b0a0e0603100b0d080408030c0708030310 68
    0x901081c40070b00d694441542c07200785070a002d8442c0c0301c000ca8036908900c07145480c0c101d160500c641e000d0300c0940390502c024130007106050101411a02400ca010704a40c4441c00d00c2c1004e4021034040401d10700c070310000020400004480f070400c0350201001e49040e95641c02841094a80c0c0c0300e00b100004503084001600d620713090707200820920f20f404001004030903032342c0404c100070001e0300840000d140034541c050030091000c9101c4041c0c01620003904007100110150799185c01002c040009a540301c0c00d80d09011072480003034a0742c00084c20048105402c2c001d80d055281c20385071004a440402d5595444889000185000d000700d0b00b01d035a0030b1038000180c450408052010500f202a40078190342d03146561f685002400e642400fa01c0c000403108400301c10481030b58000c1d8815801c4152180800a051740d010910480c902c01c00c00c00032800070035010002d034001e012184020f0080d1408100400c1c800c10004c060051002c6920850b480c0c075450302c0f0601d0f80e81c0030883c1e8082d41c91410380028400c0b03a05 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 659850980 1250 659849730 659849759
    0x3306051c2a1806092a051e12040b060a060e091e010602010606020c09010b03070c020a050310090b0708040f03050d0b090a0b0a230d0c03050114040303200301 69
    0x1600301078441080d0315a40d0320040c11441041081c040c42d1074000501c900f80c0c0e40d2184815111a10010500140f6650f18818160385151640c105220003c10003a5031010a11204001d90031346a808690740c904514400032503500a072030079240842000c0024400d4245010081c1c01e072031542d1100b80c01d0100d040204100b441f0300a0030f02c1c0300c40c00302c840c01041c0c411034251303040e01a1802c1d40000c11030303c0c20a034000b4500003070840428802d08001c9d00402440c522041100d800446500e0580d04151150000c12074003d142d40c800ca0305485200100c100110043d400a00200d00c546142561500e5001d02141c402e0400e82c0c010b016031609040010001e4064402002c000c50784040109160025400040d80c17024103c4120301c812b82c595039100400d14020848001a04100d00084e0740b032811100da55a0862a0f800420b0050a212801c142070180f640c4010004503400b00003402503000d007021490901d40c0c10388003140405c0c28005030005c1c00d10107400811011b4111444581140c1c81c04220002c0c828 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 659852230 1250 659850980 659851043
    0x302160b120903071e0b060415060806030114070e090a020f0405060310080106030309031506151110020d0b27190914160503010501050d3306051c 64
    0x2004021444c001001051604030074070044030007036a40246824000c3c01c0200040000b8880c41c500412602a000c454160b10195071940c500341007603681d10004240100076900c1c1040e100349000040142c0c1036400020319043d4a020740c6c0401c11500c400403244240d000340140441c440001f40070910082c02c7c0301d006142d0041484109003020303a80c0315100c9084824a800907030002c1d00100050061200d140341c0c82c11450076052040180c5880c04030754a50303110240c4004800c200b0070320b031200342e80001000100742c10b030f003100b43c00c41d03485104180c0b50b8001c1441c2c44446004546036000440c1c15043c40644034580c0e4562000d003001c075078a0900c0c0080a41c2541030006e00140c0d0f40c002c500c0800e924160380300f50380141000801c41c081d0b02c02ca0300d0302d2000071944018441c1e810a001884a51101c100b0a000b60381d01400800047d0ba0280b40c00c80700d040d0360382242d0554071a900c405046d0522a405c11003c80e18166251031392030801c4e01d1f218150316031030100070306181d10318914144080701c140400c0943c003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 659853480 1250 659852230 659852233
    0x408071a090603062e030b010c03020604110402070b15030c09040302060f270604050705030a051c03060b03040602040509060409081801110f0105010806161d0406050d08070302160b1209 81
    0x4110301c0402d500710090388440c2c2841817900000d04900160580f00d9000c048070242132500d00c4000a0b07400170340e00d0034010001030120708180c0c0700f45031544a5405840c0795951150703401c0060716150f010401801440c84d500c03031080c416600c400d0304608150360300500440d0503a025141c1a41c030180d43c0c114015003d40b5050b8042c40c24121011745600300c81340460119482c0c400b904003030900741099880d000303894011910907000000c144000410010b650780c0071150b0000c020b0b15020102105400404003a0301200b00c0f180b0002c104000c100711075000304181d46017140c0c21b5016458030428442111f008003401001141e04001607041228460264800a08141740040120815400b81410001194000b140c269181c400600c2251800c0c4156940048000c0751894160a500c9005151a01c0640e41540d01054100840d00540b100c1d0840700241c01c0192600c03000841c0e52401c0a0264840c2c40c040c0c0041c0200ba080900d8141114801d0f02152041410141420002c454103201949d01a040c403280c1e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 659854730 1250 659853480 659853499
    0xf0207030c03050a1716060b0303040e090609120f0a03090213020d0e0f0a08312408091b011709010504050601330203120c0408071a09060306 62
    0x20001200071014511030310103400080510700d04614081a41106001c00c90418040418818002050441059040300c0040b03011920200841d0442c41180c0004650648039010400400b900003040e40c01030034104121038011040721981055400344250005d490350701000401c034842e1280d0455603000f40001d04a20992020001e190201d03030000611112898075290380d103c0507001030084041d245144c0c1c01520300c280c0e0f142d0342ca04a134800c8001c15200310100849041d40d2068035003091143d481c904c03080004143d1160011400441c44051841c405c40402042e4800f00e4070403a9858094680423008041480310517051321100302c0c5115a0394100659010b061070720044038485c03a0300413001c4400000e010304140c2000350030003005030854100004441c034051141803401710600c1d1903401c4d4081d4030b03c0309030b0b80d800d0803425881105060490303910b141d02440400c00f0307080300400c01c540046086555460751200c40403142010340580c0b09018100f0302101d0003600b0408005d41e440940100802d82 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 659855980 1250 659854730 659854733
    0x100e0102012c0d1713051501060e0406170a061a03031305040621080a05070209040b150102190605090115080a0308010e040209130302010b040c180e0f070f020703 71
    0xb0a14903100325114070740341c0322a55141c0305005114039a01c3c00e1039407400000f0410210840022550040c08944414441c030800f403003840700900c0400340441a5402c0035605595030b2600030000d00d8000f0f081031203070f841c0640024403030704100b0b104100c00500102910707071031001d921204003c2c500040c5803803905c0404a9243c0e01980c040c001070407001d484030324941405061100380411546581c000501c2044d4114010365032a4038404243c0e481075204130401d941b00014002100c160081d602c1c02504020001c0500c404c000302c046807280719410144032240c0310142c8200490340d03180d5030750b000c82070119560700c84e0300403401c40d40040c2d51240d04240041a80390f00b106541c608824907502030810740d04610000c000f050352000361140140218040a0b107181400c1d00015038076038001d0722240c3c1c880070922004081500039046640308100c010f208001c01d01d5040000760800c85540d10448001e0380314140400c0e00030425040500035412621011030039510140d058072840c2002d400901075208040b400170 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 659857230 1250 659855980 659856011
    0x6040515030a063003170c0d140105060d021308030406050d0e030a1209030e190801050a05070c0b04050f0307080a030b0103090201050a0e0406090f051602030405100e010201 76
    0xca040c0d20500100e54900e00408071004484540d00032800300003054403c0d20039003045074001ca400000401802002c2c0307507503140c15100101291403560400810400300002603040e01c01030a034103a0301c8401801001301040800c42c49980034000c2c107920410500400c5004017803640506030610b1440c03403018490b0b80750303a08185503411951100001980016040c0b100e44558060700c480c1030000c50055003003250841001d030252100d290340703514140ea56041030040c1031143c040c072074811201402011401011000980041000b0300a122056081c4400300700070303102c144101407090b401903a542c1111038240e03682e2401140041c1080e03410344039041c01c04030404004d10081030801d03c82c00355617aa031260b4020180903a00d08a4005051625010401015036000380c02c4503540400d80c90b00841c0c000d403240007e0f00801154014598031442c0a22103c80410154401c9000340c81400301c03100303070003c02042240d0303074466030281d03917000045200a114014000c5c1e01c0c50404840500010860400b0510030780d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 659858480 1250 659857230 659857249
    0x312050f0702060c0124050607031413151103030f0f060303190206010501030e190308190f0c2d030b060708030708040b2d040503040302030a0c0504050105040911040902060405 77
    0x4e00390350344482102e40007444005090b1b000302e0010b049850170f440e060001c0c0040c0181c00d4080d0074448400510b11400181c00c0881e00300b0450b400c200360b003580d1202c19264800c83c810701000c001c60031100e05480001d00000940744990f101070f004651503640c3e2040100e00c29005004a80c0502c0103000d85204c00e00750030f440c1580464154005c0105600d000c0c00182038501c49000c03030240340c101a01c41072152031071051421035a5058108000152142094292040c541e6081c1403050b44c03500091a400310103907040310448074201d54640c2d040c94034080a1880c090503202f05024100c4009110350301803802a045045403c0004024500300032207926444419481114034200082180c0c1c1008204503800080a0f00600c038021109a4056007079241c1c00160141c3c00007001c03084842d40018100f10040041300c0c00f41d503014041e02c94a550f949050070041d441c5019541c4254101070010400d810035202d41c4015641008512202c51049030900000703055050342640c002c4070400c00428580c0391014403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 659859730 1250 659858480 659858497
    0x6020c0d05070c0501090305030d20120406060b04080304060f17010801020c0f030306030a030c0809030f06010f240e0a050a0b0912010501060c080a0504270e06010312050f070206 78
    0xc46a4400700761404000c0f204041d041380b8148483d02000b4030205100000f51032031040714030320019048176042080c1d0100442c08105080c00640002d4040b04104114030040c000c510440f014007100d0744400a410ba9401180a110b400e0f6005000c200a0544100201d4101c0001c508000894036141e0792100c142040c02d030000c0ca400c0e134001603a0030b000201002070b83c00000c0c02c1c502660650608100007600c8050001c0040d00f0405810b00350b1042c005041c00b140ea4000004003191108414510703503680364442485008683da031404000a00d1040100d00d03200d1002d0f007880300c003040340040d582c260b4004410300e80031a08440c00f51004512519200300b4400500070040b8ad098644c10203408200d5030b0078030011008016414100108036071500100c0d003d517501d920034600390302d8907203411003226140919407101820004d01002281150718400c100c0030302001d4480203110221144102541d142da080c440108a8440305100100d024407a44c040d00d001c0b00700e42d40c0c0314038003961038001404a80003642c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 659860980 1250 659859730 659859737
    0x809130204081b011b15020304030206010e130308043e100e030309060717070f1e030806010513091e140412080a060512070303230304060906020c0d 65
    0x702401a0b080070800740b00710100101c0998001101d5100003003003154200444952610ba00e03108070104040b0005001c0050038007082191203242c1400c0013591084207115040b01c100c140340102d01d220038100c480d6510107405d030312408003e854035911034401000d00c075280c03410f18081d0184003140506542950441d44200e50607040081c00c000b04001001c004d6400c110b09101141c3e5242e18241c401206840c0c0e0108200c51568940070141070607804210b18521300b84843c2e0300040c642c07080100404100300365070701883c0c20030512000d8a00140b400810000003402107286040061299032040c4000c00d21061407405500001b0750350310b41c1c402030b00c0344490b1101412100c2c107446100a0090300ca0201030305e2642108a0703240c00c00351038649030003280410400410050070002a24002550803034401003030003404008504035506000c9031108940e0104500080107490071501c128401e10000d4003071810600c417185581c48565910700107100b4440c0c1104caa030340034814049803080500c0001d0100b51541c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 659862230 1250 659860980 659860987
    0x200306090106210218041106030405010c170c07110a090c02060a050a02040f0905060105041d06031002031b090312040602030a0f0c12050c0f010c03020c0f01050103120c08091302 78
    0x74100701e83d9102e50340071003030040150044401503900c0c048140032461400e2100b4840d070310b440c01e102880d05060380500350001c400000740030030040d0540c010b58501c0c030f5550314280b0040c1c4d6004035511150040c0e0780c17644421340c1880340d80f01161920903800540c1c88011b011004180d030300c0b042c0e24192014000c0e40300168000b201003042d0701001d400f0f000ea01403100c6c141145890b052020180700c40c5258000c60a10075915400100f9a90242d4101e81c050107003c100c0040040354021030f025000701c00c0304c119006c1d000b0564501200b01c010b009407070055101070174510a907034048140c110b02d600285401503240c031070386d0982035251005800400151003650b001e580d031060386290180a140e80c00668100308500c014060001c100b000c101a54400304500e40269140390102e2164941115204440384952a0407081c00c00c20750150f000f0b140e021941803e449402003500106403c03201c0c00d210143c1103e04554240c1090742c4110550342d8060701c24030b1080d003048100400f1036515070b41805121f40c03055001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 659863480 1250 659862230 659862239
    0x1c03110a021f021519111626042c01080303060f03030d0e060403081e0f0a0b0406081e06010f1a120702060103060608010c02280203060f0609130f200306090106 70
    0x9015070746c000880d10603020700c0c01010b08000120010003600c003500d01c425610780074260300c2d44051420195510349501c0ca444980714000441c18588101c2c885440582240c021644004800c091604a0307503028081c6003180d5812040c08000342c002880a941b501040121010440c0c0e03900c261400351b40420010001c500e0300c6d00e000b6010f01d20281c0b2000c01e10800001c2002c0280204c0f8140750321081c01c18a6020907214804480003420111010540c03280c01c0c94808980541c0010f4410f948003040d100e41d5083c08884039100e91910028012010394040d1100180001203c08407449050304035075100318038011000c20f40c000780b40e000391804c00058225000401c00e001c05409284043c2c0380c440c008004800f448a0041d42e07807250071072032640f1900c00519540a1081112280c82019009001c0d10110714140741d02c541c0da85811030300103208017000d0b40800c2151800c188030079a4a607002c07941c0c0101890948030a07800c02246036403544400350407010600c003074500340090350040409100105003035080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 659864730 1250 659863480 659863531
    0xe160b0405210303010303260403080603010f02090603060918030d05010806150906090403200a0203100603150f0204053c0609060304060204051c03110a021f0215 71
    0xd54000c1d9400c0c06006800d00c50400b00030048030704491780350419140c1c02c5030010150b001241c41800d94496100c000702088203050708200c8551003903e045008001620800389440200d00660317146940090b400d08c0060f101c0d081c01000350303800400d904448401000c0d101c0c89585185d1120b48080100e68941004005040701008515041000d0440b070030400c0101101242e50000018150351103400244081000e06000300801ea641039031001030070303040c2402412030036690b0112803800c81c080c0c803542d124682001c202e84200000c4d241d00c84101203c54110241d5100680321181044291035402c0000154965402c035034407022280b001100b00c003a21900f41c2c80149090021000c1c00d41c9207030320489003000c1d902d0034100c0b2840c0d0b80c1142c0c140d440362070300e040001c000e000e04c0e04000e070860303404481e250460741c820b080b0b80c0c0d000c1e101c0e135118540d8102400c035203911540310140007500702e03003c040000301c02080c001c2c042004030030500c1103d0713680403001003250840a06413290b40380c002010b5142949400b4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 659865980 1250 659864730 659864749
    0x605060301180504031215031a071707050c030301141f09180f0603030207170327011215050f010212030f0402181e010909150e160b0405 60
    0x4119601415989030100290140101c0c020307001690703507580b00140c00c060203464104a0b254203103408001d500c1281084030941c00300741c0025140e0441140c0b26404010800041a20503030b21a0303070303101e83e10000c001d803808001406091740c01441010b11800b03034a04000c20140d402022241e0745069042680030600284000664440841d4110b80100da034002341c100c4c0200084481e40314100075841c19014200e001082905101c506903402c000000043c590f00148071403e03942000c004841c9403060316001c541c1c2e442980005444403444000654064900c2c6001000f544c00605212b2b0780f500b842d0640000700c5048641c00303c0303c0382c09650300780310504100102c02502d50f03081c001004410303001c0d0f00c1c84040c0e0200078040c1c20200b0340c50f80024115180d4802c40c0c1908541281c0c1c0000f5401c007290300516a029074080c102c0f018102000001d100381a6000c0d102405402ca0074208145d050403010700702030700d10b6504008091141d1035010142c2515040d80c00018102210401d03240d50511080001861 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 659867230 1250 659865980 659865989
    0x40b010e010b160201051c060906060f0813020d030302040e0703061e06170405070305101e0902063106170c090a0909020d0807060e0c09090d031a060a1206 68
    0x25424050741d43e03010054002d41036041e409003095a2240c0186081c0c0d501800d90718141c1c146182041c0000640040ca9044441a108680c5941b941c80c0b108910888035410101c0341d0f0811200c0d500040710241c28500d80c800302ca1400303403402500d4a920390319203503001c44080d40c80703100203940c1d10000c0140c0c240305c00f4020340b080021610051003038507104008092500408802c5410400329000c40d040200402030000296402000c0d928440300c50a44a03000b0107070b01f640404000529104148011603504c80c010704540c1c01060030742421030030700d1214020046c080c02400070481c0001c02c0184810155200802411a90b40e40c0660a169030031940c2c00040203003040c1c0c1c00141c03c1c090039942d6500c080c496000c1e40d07802d140004404000e800084d0030225142c0001d041c140001441109201040d001402c60900c81011501081800b40078000d010208403103810785038110b034001d2030302d061083e000001d0850400c0707034070403600c0d011800165580c0e2001d0014004100400d41c0604110a940507400090 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 659868480 1250 659867230 659867249
    0x190b10081b0408031206131112060420220b0705240c070c0e0c04080d020703021c02030a080c0a03090902030408070204111c020a030e0f100509070806040b010e01 71
    0x50315040140d44e0364014100314049012400000031960b0302c400144100d01198410240301c8a41c2600c603003c000c2d848121000306803400038000502504081c09240554240015070062011f014428414940c00c071241180c0004c1000b4948150a0b462201c0310004c0c1c040e106999585d1543d62404528081a001070420190899088600d0b15000e40b61423035800134124000c0e17a990700c182c3c0b506000d00103c0390841080d20700160180850300d45c0c044041c2050315007907800c40740120342520042c1d0303942c211444020f500c400e0380d072803001001980c0780d50601101d1000d021103140402c2c650785d0b60706075005004242c1c4240e20403a8004180340c1d001c00f50100410300c40000318030754102612110b90318030903c640a030103251944a0007490500003400c8071440001c0c240352180c0f248669030510041d501003503140d0300180c18030180351815500442c48203800541800201000d450327105000015200050100074540100000000c1c030000c2031100318419885034410040942c14a0007801a0a0040e040940c10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 659869730 1250 659868480 659868487
    0x4031119050d05220b03040c05030604151104050a17010606090321140a03090510110301030f0c080a06020a08280e0c030a050102071e0b190b10081b 65
    0x10030000b14500703180032610b10701181d440ca0701c3c07008605154819409180009040d440001d0081c0307001010758001c1e44145c1844805507590030030140d5402c1c0c10b03200503010700c412841804110303003140d002c8005550034070401e90600b6036403070002e0b008144503030040000c140e4804014180c0700c000e00c42c3c8400303003c0ea401d0022210b81903031281010f60709218501130810501d6161000e4032805107121505041c03407076180c1c070381d81d40418000401402c44004200c030f1520900c1124500b2030520702520101e082001603490130f5a07c2e6458111480d8520b03013040d01c19031070718031010031000010b0026a0000f4024400940e0318262404002e041c0c20004040c0d0303074410071005e5511151078001d6400392080000150108840c0a180c07459030400228108099051040c5140c0303904008044d009042904c0c000d01c1c800c4401c2d00f500e00e074010298403800f070003403038550007100040c1040c442c20010384098030036000c00207440301c11102143d400a103078882c03d00030845000400000000c0404c2d5a4050b240603c001400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 659870980 1250 659869730 659869733
    0x60512070f081507030e07030204051e0c0a0f18050306250807120b010e060a0c1403040803121009021c181e080702090103030906020706110721050604031119 69
    0xc500d43c0905a0000c254035101d07500c00c1050700304854405590010010002d5050030030800e840c10300c40028681c40c0c190713003030b0020718081000c400b980e10061072600c84086102d14514220792100c8d50400d5500c1641c0b6198010544d0b440401150b842000038031208003001c0d20048031503540d03002401d1920104202e020070800c02e990701030845058001c1412020403816109401a80c4803690b0304001500a038010a2a01e80e96610a03101d0022600a03040304040c450003004da280c40c0e100d107020360900c59104010005800306c034503207825031180703151014002050b00c6080b03450a9a0001d188030010810707181c1c5850000303045101c0d00310544895200e409102c0b010303954003090403000c2c1c0226425199070036140c10900404004840c03079180c0c003d01c00a0a581c50b45409482411103004040040c0300e0000049500350007440b00c7c002c0841610024052203180c0280c6100d0100c005400c082400c40400042000400800c1418011482034071400180c2d441c411110f03161401241c0d00e860920071401c0b4000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 659872230 1250 659870980 659871013
    0x90604060c02030c09070201020d150308070b071803081b06042301020702040e011506050304051c0302070213060e10030c050d03030e0a0b0610170f040303060512070f08 74
    0x908840e0142000c641001c95400041d091110a0700c403180c001c030005003002022503040d80202001d480c0360004222810484080383c0358207035640401060b4400c2000510042074100545c1a84680246800314402001c000e10546e0031007950f00c216004c0c1804520b0101007002042d080d00c0c910f662000401040c0703855118200c81c00c181891a4a1b0310004400305004546d080d01100c2210740c0180c810310220507455860381c0248203100c0c80c41401032110001041052180702101c2c0540c0c0c1041c001c04a016100807030b0f00d0710203440d0300e03a0780925500700040380040c0c5840c143c0d0980c41c403000c80f0004006242c549040340d2944000c04a412410300b01c0c80c20f000003030f0030341d5000054074015214900502c01c2443e00b9001041120210022841034820309420049036410f0f0710721032682568601441a0030030001d0700c44400001c00358401415103030000b1410032032042611350150080c0b401090a50f5241c01003000c0003080c004910290b00442803e0010f03108d050101402070820400810400c003c048401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 659873480 1250 659872230 659872237
    0x2030c071203020c150a050c0c100507031b051207020d021e12041e150c031110020f04081216080715060b090102010509060403092106060e06030f030906 67
    0x18203501c1121100c092051180d81550f8140c44050201c41c44008498000fa80b012012140e41035898107080005101d0f2a10700180e900c60f088040050002c0034003440460080d041c010541c3d02056620b00d0010300308107198180d0700381d99060303460307450340c46416102c00ca103500401000741080d940140b00c410501c590000c2c0c1511680f1100208a00a0340c0c045615401c002045030b03044001c180108012442c901c40845054030446483c0317018074800c0e59405081800e941c6043c11001003171040c1121707030201e800b03038644803082e003c000300355804030f010320001c07074100c0c0c0007480c0340041c440e000b06041c40311881c01c000e011841e02030740111500b00402c080c00700400c5500c150307008150b1000481c4000402c21141c2402c1d00051400400b84640340d1103100035441908840c500034010b6007040b0110f00c0e80c07480440e800c5e00035600355170f80080040c01d091400e42904e5001011100c0428105901d002194291184402401c0c28034200185418424101071801d00d128403840e030700380c004010448081d42e442044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 659874730 1250 659873480 659873483
    0x702010e0c1513080c0a09050402010e151611031e1c110a0b040605070503091209060c030d15050111060f0a060b071212020c070302040504020d0c03030504030c0902030c07 75
    0x195210302c4944010710380c0c03401181c08000301001c0110b400704540701d020540840341c03801561180529991524010250f60050304d010780800d46035541d8050600b84550520903072041124100d2034107469025110030803100c800292408048011040301c00d10302030084806c455205d007001482d407a50850b2081c0c84007038100e440b01c940c000c0307a6510003441d4004c40703a015804145106880210100742407100c1c19510444044a40510b0040090881030103502030300d00681c0303010f000f003100550b815079466070f5901103028990700103010300104c80040c20410040100d04030003400420324011050004a80a00c541c0103641030041121a096070f10900144255100d455a581c40d062512000315200040c04150008031000c5000103481040c0081d070b855103208410250358071042c41590b205407808034024120440300c107030010300080000d032030140c1005410500080a004a440c04c03075541000524076680202c0200f0b902050410038880091400c80091000c034201394030714580794142d040c061103113040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 659875980 1250 659874730 659874739
    0x100204030b06100905030d020105090c010504120212010b06041d280c050d060618140d080304080c0312010e06090f010b0a1701060905130c05072009040b040b0702010e0c 74
    0x200301c1c071140d01c075010304d01c020403000d001e9914511005030024060501207800c0d01c00d510400001601da544260225411501d0014214480d00032075400c000341c603000030040e20b64030f41d26100c024803103a4984000b0002810107142501c420801c40300814120380c4c00601e1801403a02c01001d00d0090703040c8103080c1200b00c0106e400010340d054460010340f4540913035602d00c4406464a035000c524190440e017001a070340c0360104d1024520703a42c2d110040000c15040b01694201c0300c00c042803400154544059504140701c0c0c0f10550909001041c21443c1d60058440f038149094400010440810b480c1c1705a80c004c601600c0790f0855141c10240e61101000621903940305420000340307002c2813441180405581140300c1c0c0130041f0b65941e031400811151290207010b20444580c10402060300c0984192038280030140c858a041080395202c11080c0941282c0c01c3c40d0700e4011400d805416607400d400b05102d80c2c45048496071904003420500c401c2c1c48020112800e582c503180d10404805000038102c01d950300300f10b4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 659877230 1250 659875980 659875999
    0xa08150f1306081002090906030610060f020307050a030329031c050c011a01020705041a06071a01030f0b010e0f01030816170c12040b0405011b12030b03100204030b06 73
    0x35016000b001e80c0d500000c042e010f68005a00c20110a800500032501c0032030394602e45440d18030806850300010344022940b1600c1c91410864180142d6030060031400034015a401d102080d202c1a01700f0442510440c006991600045081c0e2040c0d00b031815096010141c003c4004401f001082ea1025031720303c80701c86452551004c4200074880c9007207e92489540c00288032030319a14459410014481640301e000d401084008501400e02344108608440303a1100304151441000500016a2154030151441090300b402074004a81da103036414001c510619000c41e0140c41414200c140322010b81160014881d6a41400400802e0b401c200d41565007100c000d59a6251401032114a40b0300c10780d005080085000d1240020090003020b0101d245606d0161041c40b8081406080b49101da80035a4002000602040c407807540305d59102881c11603910f040d612446069100c0040c81c0c07808224842c0000d444010860381420280025121451191010350800b821903440001c0800c000301500d0144041a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 659878480 1250 659877230 659877259
    0x12609070806010e0c0f0d0b12010f0e0a030206010e071e0207060e0a0b1c020c0106030c08101404030e01020a081801030f0e0c041e05090d090e0415051008120a08150f 73
    0x5908c11410108004c140c0b51040c03a01001035406058410342c8401118034000c3d9140c000742000c90b00d5110f42d5410b901a0106a0910811a0b100040130b8110801c01000038615009102c865101e944c136200b19400400e205850310710020008040e030040c46e1b00403031500c40300b0170030b210380d1703106481505250668054044214a040d540240245100c101c115800d000700003050040e00700804c1d0543d0000819200005928202c1105607a0b0b60781a260450210400050200e031040030491500001481501c0d81c1035415210700e0290303004a1084110300003e090072422541c1c26110744d004d0700d0010354040c000d4904d410702c46520f804806015038061603d95013008482409450150203050044000b041141808644103aa83c00404e140c078001c21000328001c608400f40281d043d1090740d0052040b030324042410007090187c0f0007c1c0c503942400e00f804601044440703040c40b9681d5912444030700b0a4a0380c1c9000720081140c80040d14040c01d14005a0a08150780c85150b881910780009a420001c50b8505 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 659879730 1250 659878480 659878507
    0x1b210b180a050106120b060402070b34200111250b010609030b012103032a0f020d1b17040911040302041415012609070806010e0c0f 58
    0xc00d100240075500e4404c1c0480d05140030744105809030300803140c01e03c0e0341d9542010b000891051400c007400183c04040003071100707203c04468016039030700003405043c1c0702500d04100c0c0d84030544c0b500d1030002c0f441c507550b03248820009074070300802e07060300300028050000d1940c41c0103018030410401c4284c04088042c0d108400000d8400c003000580d01a01c081480d41c1d680034000e206c0e112a0000322030180d620400000c2c0c00794841e0b80031010305c07180c2083c0032581c1002e5805a0003482c0404c40b800925041c01c03800d001400c81d81c0110010700b11640c1f1000e101004c4048001c0c00d000f00d0892513002d001c030a448070b003501c01c201c801e445061507210050714082c0700a85405101406a503005090850810f10410400f0310344a001e00102d910a440c00d01480720b4019000302000c07022550443e43e041c400744580455031040c58004038043c054a100c000b00105070311f14044500044424029a90107244208402c14041002900500c4041904038190414180090240c4500740182d40074200105150409500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 659880980 1250 659879730 659879743
    0x70c0e070c020d1a060a03080a03021305090a062c2d13020109150206070804020a050424060320131205100b1c02090a091b210b18 57
    0x8000f04100c408040614001da52980500146000702440c0d002180d071364240740b00c404050700c0d80001050b092020600003200207401580700e02e1043c4440c40d40005054440503040c5000b18608076000c00c04e14107042824440c20320341c0c00c00300e462a00001845000000010f005a00090150750341840c82444104d101629a149554004403100c10b07802d000c00324110158440c0c405200383ca41c0f114490b541c51b0740c080089d080c0482000580c01500018020030b110356002680284020b044bc074541d0f1b16140807408aa0390003d21a40c11a8100d03511000031214030342c40401000d840c5000d001a04c108550352219a40700f00c942c407000038021852050340c0700514080d4015040854181c0652001c07414200c0d03841041581d21820646000c1c2594800d061007000c515a5551280705a22007000727030740c24000c198000800a100ca180e685801a000410a0303005040741e194803007820400340c1c1020315403190035400030780d0041e0700c203e4039001c54005211814880ea00c50741c071005403c040f20340102828102071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 659882230 1250 659880980 659880983
    0x227060f09040504060e031306090e040b0c070507271a010509100e09040308010302040f0606050406050c160303050301031e030c06052208030106030e0102091e13060b03070311070c0e070c 82
    0x800b040d00c00e4000c82c0a4550400c9443d5a0b03180030030705a4a41000072080c0063301d0181000c240c00c0002508421000c0040c11800e120744101c6020940e5900740d421110542c500d03081c07802c9108c01089101c00780a021341100c00310038250210240c40441e0010784548140201d950082059425000480e8010158208280e0001d04545000d01e01031070014400c4c0400d00040b8400da207841c00d00c1100211502c41d480a44009407902461719007010ba00740e560740c1015050104921031000e00c002c28201b50107410f002180b0036200c4e00c2d101d505501c0c0810f2100c40002e00c040b0610110300018000c00d610030340b029145600404001642d84074601c40e40244200d440d106204000200111010884040011412640d0599042240b1950201001e0903480f628100391f81c03003c3c14514120714841c1001504040d0340006140100410988036104103440d1300d58801c80c009000407007002107207a054080c25003440c181c0b81c810381c0b4008050b903428251444078062004480900300004582d1030244500d600c999 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 659883480 1250 659882230 659882233
    0x20409020616121209030f080a091703010501090e19050c07020919150b12090c1e04060501050a081f09181e020105071103010204090227060f09040504060e 68
    0xc00c982c100211074108908811000500140131200f61140600c504506903074103036600070700602003000403100701d84054600000c15a4039407004000454106000305a00081402e02c0d44940c0341c0000075100110340d62042e880e2a0300c120400c01016002c0440c503995010220340012141c40d14500e80700e6a0150702c50007500205036409010494141900202c1c41d01070540040c84041d00300c0e512484181c820388a031303c12408082c4600c4103000012140280e0068003441160742580035440010b402400100c0302400d100c02c10480c600140c01c0c180203c00107004203003490780c40c02465140081960500a21103400214925007100c0700b200721141e103000810004105114100e841c1c00e4004421030700d0704007101d5403d20f41c00e15175000b4002c01c40e48200241c05071152400e10180d81c40d0281ca29502062050340b5550801000c521035055101500590000880c051281413010194071a01c0740c40d1a4464820b000501550060a60090465840c00010350b4085100c0c0c0303407031418202800b50b6000c03c3c442c6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 659884730 1250 659883480 659883517
    0x280c02070512060406050105060a02070303030f02072102010609020418020d0603171b0c18180601090f050f0c091309061a01020601150f0c0203150108030912030405030a0204090206 79
    0x550b50006255001c0c0d401804204042d90342c600421405209100760034000d42c10014080004c01e0081c0c0c403101440e22602c5025203403a44035614103200c02503080c1024a90a036070a03000480550910489018280c0044114541421f0a080b200a0740c07007400140c607116000030b41c220080000790849801943d00540e00300e0b41c02c00e103480e041040e4100307c0e117001c04010b00305d800c0d100400c0001000c5c6900b07507002d07158403018043c80101600750400104401d41e40300795010140307802c1808000c0d26009200002c40061052941e129980503030f01c015020107500c1a1f98800e00041c0d00c990170440740d0b03545003146c0c010404001c5142c450054030070410b0142c401481c01c4030300029080e08641554800e28240d0a60303000ba82c03035005d4400c0c00070019218000003082c90000d51400c601913900707011000d00050841d4448000656044078094090704143c039070781c04c04a43e15407a400e1880e030038009d20300800c014509060800340480d980d5152502c001e407107240c03120f0a0805545904040f107007546600c01c12400c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 659885980 1250 659884730 659884759
    0x2a060a02030d1d0d0305060a060804140321070305090c09100b160b0105060403081c020f070c050f03241b0f0309061e0a0c020f0312010e280c020705 65
    0x60440c00e10780302c43c109003c0c058200c0c42492003841000d02c2a2401440340c110340d800e10000b19540c0070001d00495840d000c591007105288010006840d51200300c0d00045554010600302d84000c0c03030048c00640c1454100030038403000c1d0702c000c241110f11003401d41300038640d03549060721011030001c682d1010075403c41c00101c441d070070541c00750340760082c1e0300079070750401e682e6a1102400080d100e18400503003080c10600c039150190902d06000070034031640307240240c140f00a410510700343c0d500c0000226894031000074200081d0030502c4141038010b0049024001103030080b5003521900c441da4107401c201150314000101e00c00400756000e0071044c110940c07651100d80341002d09025900c02e40781030b410740c46644006100f88640030141044e105403071a0040c034544900f41d41401030320301c5041410075030041800c004a047d208002414500428103c0c0750700c0c5500d440c000d0031074031001a00151b002418a140000c0d11013039031050742c141c01c10311240003400034401a0128240480d540100e035100d10402480341 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 659887230 1250 659885980 659886011
    0x12270705030d021606030911060a08040605161209050111040f0603060e070c03051c0f0605090619050108100e040c180905060a020a0c050609010603052a060a02030d 72
    0x3600d90950403212405142d51050b82d459003400001c0300615903100c4180501c5101340c0005626500c01d072080c0309070810300b04c000790711034020000c4000017903541000c01c01404518043c2c641c000290300469941ea60000000415046c8111402c0c41400c0e156000502080b07800d41c410080c0140aa00c01500d641c0c03908913400400f000c030311552002906003180400c04080c0301034528041c0c02030b610384200c200926603082c0c90340d80103040003c0c9880e00000c01710040d0002406540b0301d45010301c0300011158100307010044c405501501e40e82c06003503503140701c448000d80442c0e1242516000d00304825035596207444080d040c2e03160703007010f0a40302c03506003480708100680350b541007a5800b21030402d1914840c05080d0080350203500340601654055030101c3c0e0700342655401064284100d24260000308001d4464500d048030549009005a54481f0100705004e020b111800320300750140301400c0d00c0900200f052448500d41d17442c20b07124020016524100710300030011142c00c1c0281c1e030014809000d8a034031a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 659888480 1250 659887230 659887243
    0xb0108060613050f06120c130c0f0201150e06130905100605030309100302031503032206230912061005030f0f07120516030b100504020a051227 63
    0xe60107403a81c00700001a108560003900e00c64100090034100c0ca9864004002c86c0481001a482e184d02a0b2010301c8566141e1100b080d00e0700f20300400220300c1c42c66004004010380c212990040c21641351586407108100b80c039150700c04486100e48118120b8035035100280000c085480b82c2590070303141031480002c0090101d00c510b07190010220410109544200f41a200e115000606901c030480c20319060b5044d00075400f03503420250403040c0301000322440001c00e165a000002403103004c400b4840805502d00e0400b68000609140d19250600600310325101c007404020f941058a05c0f0008941c240040e224940302076070f1690600c0440d0180d04044040651029050160b140203020b0040c00c0c104500c4002442c500d4240f0f10001801d4a900d0035181d0401600441d00c11a07a60041108a0320700c480b0010900c0050742c065128400142803010b07078600304c0700b0903500250107140180483c05015401006a130091400400040e06c0c41d40c0d45506103200050800080e8620081c0c0261030021040003d01d5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 659889730 1250 659888480 659888491
    0x60129071406011401050a0c0302010e07030f05060114060f0d1509051017151008071701051608040b041106030a0902150c120a0302040e01300803070513030b010806 72
    0x1c2d6403041c2d884200d100c074641001c018050108104010b03184107148600070002e003441c000e1000044c815004d81c440360030040c0ba0b43c000c1c0c421354028550541840018010240104040d00c24a05103400100c04100140112500c2c00b00101010480302e00c0031131142c00c040300707400004240241440c1c0300c124503002400260703084c1c11003c0103804040784014401d0008141060088010076400180080c0c40d00100c10041c0300103160380425a00058602c410410407016015500c8080c1e075918511f071a55003103540040c02c1c50b080035081e801007401a41c000303c00d25040307138001010207100e42c0d641c01c010010741d51314161103800c0714000040000d40e0440381d000941c01403003190210364052014440300d09a000f40c1c10740586981000c0c040d0a920007004c4028104600142009418147c0c0c0315500781c590442603002d4261007481d001c5d607040304409240d02301440601d6850a40d240c083c01d0321802c02a010060401051020001d5024040c498143c1400c006683c0000f80011030740c1c65104040d01c5440940e032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 659890980 1250 659889730 659889733
    0x30d0603060f0606050f0702011b0303020301440c10030b0a0f0f300b01030b0c1911030c0604151401080c060d06030b090d02120c0601290714 62
    0x10002034840b014000c2900b00c48103a41c032207041028030005051540d10200d0100e05000d403e040010f00c0b81d1b50301d0541d00300d441c000e4800584135031500120100d0f040c0400001000342404059051440380b11040c0040140328400c400407181100404051500d07400040c11a40002c0240c85000003d0341a0884402a0010f4800c0301c1c04940d540ca140c811000d0500413002d540446c0c010501441414004644103420102e485403034071501740c1034480485070040e0095a091140d40300601c240710020070403980001c803400e540c80c640325445495044c5c00c0c5481e9070030401c02c54040b00d007009400040040d6541440703428144c0c1e0103400c0600d0b00411034045499500307001d6040ca01c00990000020f10494104c4200740050503440c141c8904003d0319a20240a80006681e03411010000c2601c200c00244034002c103000409205d0070046001c5c1c508505110002c03d098410000131403010710100d48581111441001d8180c8008403500c001c01c0d5140340308040040c110003003004018402c10f03030000100004440c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 659892086 1106 659890980 659890991
    0x133030209091b100e010f050c0d0504080c01090503100513080705010b0301050a0506030a02091308160c061b1e0c2304050f070807050408030d060306 66
    0x848801441d488030003078183c80b05280e6a00c1000c000d04480e1200f0500b11584001c10030000484001c1c1040355064144034030500901c281e80352441c4900075a1403100c40799500400c260040e22481c0124400d41103044ca80354095401482961400b030082d219441c1100d00f500c000e42000381404e4004040322000402280d40c0a000e4000d85100c0e46c00443d0071440e00c0101820b441c0040c0c95005464071301000e0000c5e40da00002c4000c1c7c5c46a042c5c07000c0fa916529290052460b404103c00035055060000d030f5525808502c8522001d0b1a110b51843c0e6200e503220a0b00b2903011080811b031038a000310036803180020641410b4800000b0781600c0b111007400d0f0869803143c1c1052107507800010b0048080f0180016400022074100c080b8805840c01c00c0240780c010a61a460380c0d018181c0000e000b1b621002c40e0b002071040307040b50003610244045035541c01920782143c00070405c9100640700e135407802 = true := by decide +kernel

theorem cover : BRFrame.Cov 659712230 659892086 := by
  have h0 := BRFrame.cov_init 659712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 659712230 ≤ n) (h2 : n < 659892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
