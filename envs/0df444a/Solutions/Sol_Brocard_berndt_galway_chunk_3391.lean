-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3391
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:31:48.808925+00:00
-- url     : https://prove2.me/submissions/f3088a6b-7aeb-48e6-a027-fa38eee695d8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 609712230 ≤ n < 609892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 609713480 1250 609712230 609712249
    0xb06030c09030a08161b05010507120201180c0504140105060f0a031103090606120a1e14060705090a09112b050702060403032415090801060308091801060e 68
    0xe0b80d240c010400602d01044861001e88441700c4c50b0114064081044c1c90302894407481c2e03011070142003051250070017880e0703000700980d9071a030340240040340f5504070b54008a004081010b058205098185021024801e10101c000251a030682d4100403051045029115000007441070b41c2d8050801c0014254420401000d07103012002400c000c11610310700103500c4c550780c008990600c1e10b64000820040d8500c0c0c1f501c0d00b60b800d17030ac4203005099180b03440d482c1d40340d90401002c02c031100c0c84164980c000400ca401c0083c2060861000306581c031700d080500c00101580e0052458a1003055030020201310000e07948600e61000c03262030401403401d68404804003045900c560b8072010b0348003240d0909002c959500515100d038040c1d03405041e0b949410b00d400f80c01c542c070171144002102800c2224040440111481c076054800601e041c60003040340700700032a048c4940f6001039003103508100000003000001e00c090301c07001e401100c9403540646e15030880260b0701024032540000481400010009051143c481c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 609714730 1250 609713480 609713497
    0x180b0901090506040306021201051f0c17030703060e0c120f0c0903030711012a0b040c0f0906030203010609020708160c030b0702060603010b150703030f0b04151401030b06030c 77
    0x3909503200e0000303c0540160b030040c0d0b09590001080a070545010200e5409072904546c590b045204440f080c2c100d4158020015082c0400c41c890b846c10700c00884180810b51400d1500c3c03036a01d1514080c0280504840c0c030500c48409280d0000c100d581a100042c0c4044500d0f00e409104203035103201c07404010038400342101d00e940000704521510398030148020071100780100b6150700021380d5400010300c040303040d01d444c4c04c400302c400c14001600f02c09000c4103050940c0007459034800303440b14102111002d0f5642e20203100c5c0c08007248000f90000040d0000d204890003200200401a9118402000c0c0e220340c1100609001040180200907210044000c0d40c0c00d0141c20f004050741d88954440d5001e240a03114000507900c85402c0080038034013406a0982c42c04c0943d10045003401803c203100b124041d002c001001e060300c400c8500561103456215035100f580040c010301c140d16100510803910034413402502200d41a03414508041c1d402801916003184000d48510b286a07a02c02c2120041d8001080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 609715980 1250 609714730 609714737
    0xf0c180a02070218010f2123160302180c0912210d181101032a0c02010908010e12180310020d06050f0d0b25090e0106180b0901 56
    0x40000961685001115081c801c1c080c5141154101140484481041e911140030003848902c0516496400c00d404c1d129560b0009103604100d01003924560050301044090810340300d03027004110f0303000c500100c10044174002d454a0718159150140b45a4440b01200c100220100412949069060182d25070307480c0d91314031054800a9045015000c240b0315900c48804000708040307070f1840110481d03c5071150002c0e951854250782ca07415994007038110707205086541030640c1c4440c0d0324695031100340c051003100c4419200340e0308607041000c060150a035085003640000d16015011648420501c1800c0458010078002c0c480c0394140c08082180b40c0c4506402c408141e800503150490b13450801059082000485d805a00e5030082c0c2c0c4068111780c803540c00a0b10030b0305400e07040516521103d901024454205021450603502c580390000c80b20080ca14011004a05052071030f5090f034002d1445003034034950341c80c0e10b04076642e070b5a044034158803402d0f200142c03e4021100300021b058080003080801810704 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 609717230 1250 609715980 609715987
    0x250e0a030b250504050a090207030807050a090b04090203070206070c0b06190810050a2708030a060f03030e01171501110c04060303030e01050a060303120b0f210f0c180a02 75
    0x300c00d01840403002c001c040c080768010805221624144402e00003a044107a421420043d054400500c01540605510700b0320030001407005000d03200d007400d5030107084110070456865544441e178400952040351114014040c481c04039504a00c907855052100f90000c02854050702c0c0c00d810401c0e441c1c0441010f918003030f40e290740050000ba0a10842550250340c0310002464a03100b0b0380e0784260340c41c06181084a402d40d80b0503a440102c0c4802090243da0000002c2d601d135610406890000c000c07641003103000402904001040503840b21039412210002c1c4d0307800884208156102c00c100b4819103001419469034050b541095208407d8001c030b109280701241d00c00c500c84c07004a41102d0032a0010740c0042d80320844907e140c0c400340a41c0350030194180c07040240e60702e903840040c000d129204d00781c040c440c3c90307400c3c141440e51086010f1741c4403e8004d1064051500ca50660312403410b401c00004000d00401d55207d82c40c02e0040784040e03c07554040c140c1e03034121015014004421000401d16140e0aa007031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 609718480 1250 609717230 609717271
    0x60403030e010b1f120203070f0c080702061204151e050402010314090c09150102210705060f04061a060a0e1207060306030b160c060504020f09250e0a030b 68
    0x1507040e5036114401c41c00407182c0075a420001172203500d04000e00e82c6031a004006000030759900440600b460101031421111540749032400b0180c0d48514540690300c0113001c0f80e130004402d5003c406501507442006040d10300ba110820b50340c01d44424101404c04000390300304e462400c0012303400107903125105244c001156268060780e895801c07415030f114a0250300244d04545941400a11a84c2000512055001c68103a00300006c1d5912050000d00680a412100090074201c0901c10b881c0e00b00d900c50b00356049032804103680700c200340048809440260400075084650310b0b00c0743c0c01251381da402505680c5007a40040080d10102c0305040d02c503070003003415040c808981106104c0ea00150083d40e5001c01c01501c0c60410182c030b8000a800b100849080c00b0b0459000e40c1c0080204400c203500800115a503030b65400001e030320b601c2c040b28041c0c000100340d0400008041c07040070a51501d040700401328054410006c07c403205250004011b400c29607440041c4003098070790344010340c4560005184550318095 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 609719730 1250 609718480 609718489
    0x100f0f090b1c03020c03010b0303030f0c3601030b09040203150618010e060901061407121e0f02010e03070b0105151606020307020106120206030f0c040512100b12060403030e010b 78
    0x803081c03d40042c1c100d8041042e0900d8207024001024000318001d501794240340407404100b000160207442d140c0300c0054194824803c2e4181a00d5001ca258403152100c0584403112000030030607440381c1d00180c03800c1e01c18102031504841c1c281c010341d000b500510829002145040110350f014105030344c015184114162400c0072011514040c1280c850040074600b401800e0040c0ca81741078100c0810310106400c0100a03080450940b4900354005c0c210aa800c00340420566401c4001d0450348100164511800c21881d00a100e49042400d294000c014240b1185000c903102d001f4110f008240c1c10080300104841e00c1d0403460701102e445880c02d25490403004100070380051881040c03c55400d5004020400041e4080c0700d444010a410785075620f8051300d960006003903210081a5101c00c1e80c09078040303035203070410106039005080c0151a424100003500b08013035681d0201607642558508041109190382000300b001000ca540300b800501e0140c0360f5513402d401134030010640714055940c071811203a041d40e4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 609720980 1250 609719730 609719779
    0x11190305120603030405030307290f09060a0e0c04020d240f09060e060d1b180b06160803070e040615021c1e09030210020105100f0f090b 60
    0x800e494203a9034101c021010581c0040081c06144650820300c42003103251808022242e02e90b9000713002610210583c6441070111a03100095000c090410b000c00000500301403055010382034103821225031780d0380d9a2750034050720080500014542c0001051083e075051903000b4281103406a0701c04210308042c414100581040b50329031808c8021001401c0142c5014044108040d040c02003084c401e0500344600700c0c410a1019040c54061801c8550745c909010081c1204403224401c01c22803040b950791a0440440660700d0040c40c400315180c0725011440b8a000d4049590081d641c1c2d0709001e852a180c0c44002843c0c01c0100303900180020a02d231180300740d50b00d03c98a800f504800b0f2581511111046000740f8100a030100803c076401540f0308040c02603000364035035401c00c070b404080420583d880801151a00025840207400540e64140c0246894041d045540704081c40c00007200c541e40d07034103450702404441d44180444800301d484188480c00080d00102c1066501509900030007010f098035042c03060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 609722230 1250 609720980 609720983
    0x1509060d020310031a07020316050f060f06010e01031b0c0503040e070518010302090a090c02070803030a0903080f040c03060f1e0605090c071e032606090c040e06011119 74
    0x1283d01400d104010784800711420490f07500442c5a800e1800840c081c0da00d22424400b00e140d49401c3c1ca1450400004000072180805480141e804c582001c01c40004201070580b10b1a010070010000d040b003a5210b0300c100a860705810050272103240a418007598407012502c0180c86900042101080c58a41180c166000300f800743d03604c070354400b5249802d096002d42c0404e10360401d401082441603640d80c0610300019901e1050001842042d00c1c001030780b42855a40c40120b15010120812803205444da024010302400b070b07140c04010f6a40c85440340160182160b0041512100f02002c0c8080750442c0d011850102c2170315070004500d0380e0001a8429020b01c1080c000f203403925007006014504040060640140da41071180341001890f80c0c50000c10004408226080d150380b40c0c448007410702c10284810810b6802c4080c1c0001105115075004504080310b00500030781d64440410070041007541210b00f160185541d919003501c0d5a401101e0550102d2000a100d100700c941d548100c6c0c88200d80d043d04a03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 609723480 1250 609722230 609722251
    0x60e070f03150506030a15080703080301090c02070501123b0714010e0103020c01060b03040b07090b09011e1815030605040c090315061d0f151509060d0203 68
    0x41000340c0340101560601e401030408011059000c0101c1e490ba4401c3d0707034121940d15408200c4c2d0401c1d4000b21040b000542c0402441d1281803000000d1020200046d03050383c030459024400c0a80b8824242d0f51120307036108441c001900216102140c402035401000641d8400d07110400f00325450803140320f403132102a11074440395034084282407500810003681005151503c0b6146000c410200042c000c40d5000510381d0526400240151190400794040d9000d88090b150141d200d06003410b04000c0c0420441c1c0743e07000b04414203400300c1e0a2801e64161440c40c0416075031440441340c5019020740aa80e01c4580c50140503901c3e100d411f94400d5011683d014006155503160300550400009081d54100d51050340a030307141050040043c0c1e440032050007600c0e0020a500c2014185000c40030051101e90300034060149801c0500341030701d00d24400a4003a042c080341182c22030321192404182c00c1c070142c48403640010841c407950f018101d80710103031040400c003c1c0480d00700401d185200080e07a00440b0fa15100c1d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 609724730 1250 609723480 609723497
    0xf19060504060b0a030506040603050c040908090a06170f0c030103080f0d1e11070c0902030603070305070806040b0f090a03080601020316051c0f0e3c011d1c020301060e07 75
    0x411703074036202c0d482d03004c01c1c01c940a010081c95522129202c0f00034007451070003591034070669410300018000b21400d001c00940049030169407900300501007022007d40340004001c410104166042c082c0c08240164100e041c101c0c690391869495069640c4008017035601060705000a0080b19000e00c00c0d0b40010401b80d002d241c108101182d10401c9590544c00509440b8041c0110fa010641100801d81560040700b40180e498030f039900060314102d420350000b081c6100c0c1000226001a0204120340510b20910780455035407a448400083c101d004c4035083c009071302035803452011a02c00d0f2a0705820403170600690b844c0a00310483c014100540b17800c2604ea070743c031003400c1e045041405042030300c0500c160702d031070001d240c0003140040c282041032075060720411515403c3c07038010080c0340f080ca401040010740c001ca0818481c002e0390b9036008082445011038407004d0b2500c20b406c00d0f80d24100501074014000c0c000070000340a00d00c01411852416a00756580d000082403400c1c011101c280140342a40382c40b00b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 609725980 1250 609724730 609724747
    0x90c080105041104060801091e020d0b0405030c01060501030c0f0c060b12010905070801050702061b120a1d0c01210f0c02061501020a1a310606050301050f19060504060b 74
    0x1507454075804030060ba89088440d002140c42c174002c0194101d216503240c0841c6042b4000580450801c41d00941000321850501c0100b0030000028100b903442440248481075480005404a40d81809000c0100b8890884030076800d100c0c410b042c0540e4464034002400c2e2042001007841a01c00004105d29030395502109030038000b00700070100003008140000c0c07040e0300c1c2100000b074a90801410036101040381c01e0340091990f400205640c02502c0002c0100000d18046250a01400714001c001c4500c0f8244200305031002e9000c104100802e0041e1038880e80312580f404011502d194460295404507031310320b1b05803036a4805014003181810144d00900c461304060281c0703500302c06c10030170341382c15544140c40000000721a803451940d840d801014501c030701da4a01d05100c1c2c00300035100d8050200c9203028107100540600c1d50704441200d01400040010f692101c0516080350b0080c1c0b4850310107040c0d41c00050f1082c50451a03c002940c0d80480402c2040c0c1e16404a02942c2903608103800c5010b010503940b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 609727230 1250 609725980 609725989
    0xc070501080c130e220b0f0f0405061f0503030d05040219351c170c0f0901021612020f040504210512090726060604090c0801050411 58
    0x141c100e00340031200d515026002c2000e490a140e18407900104058581c0050440000545150380c1c034811305005c0082451140340c074816082085402042c042c07a6480410504400c0f2004c240c861a400b40043c225074175800035000305110f2840c040c040b80810104007140c180c8050000d403840022881b13011545060074410041800c4484400c4802010804000c22000d4078020b0f0441e8003c507401022500c45c1e6072040b0040051071100001e2405205502c9045500102c003000280442c0455950107501aa43d00700311080c104140c80500040d01c1c00d00c14100d50b003080d14020010840140121003084081809034070300070032540e0000c2c0340b02d68000201802e6051481141086c91b400301e904200301c0c541075917605190003456001107855003080c00c0080d20fa500400460701d54a40c90807845100b858034919060f5038188602074000d14003100102d449451203078101b0703c4441c40343c88021309000e58414051000809904005a4101000050014102000f80305040c02940611071041c0154100740600 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 609728480 1250 609727230 609727247
    0xc02030c1e1320031308030709030615030c0503032d0415082203020d0305061306081b0a030b0c0d09060204080a02010f020f0304030303020702041409061005011e050304060e030c070501 81
    0x2e40c24140c100100310040c5c0c4005214440755601c440119100e85131328004403080320f5aa000201140d1a080c1c0e0124401c06861a04045900c101150310721035032140c051507224081c4c02c103d8011040c02442c01e0010103003203c2c024595080010950f41041c1e0fa5003005d6803c68044000c0001103a481e5081c0b0901000d0444114104c4082001c1701100c42c0560340d0081d51500304901038001c1560b07034008a0815554148650200000302000340265901c1d18015912540c15010502c440c41702008018198181102d6042c2120f42000c14003641c0e0341d4003115a01c80340d01041c51400d0341aa20f411401c0000d440344050070140c02c4010041c4042c01103031001429106d460030185040d9841400948507406001048805a907894035000d601e540440c03000c90050140b8a400001ca07000d401c0c00c0001d08140090050b00c12545541054003ca55942c01512503d400001d4102e42494184204944a00604c0195001031107681c1c0000d510548a40d01402c541212041460f1500183d50400096a00c950032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 609729730 1250 609728480 609728531
    0x19050307080105090f041209171609091212020c0304061e0216060c022b1502070c090908070c0311010f02071202010c03020f010510050901060c02030c1e13 68
    0x5813540c80c00d10501011031940010001821601001c100f840914842c06617203009040d0110001d0864848024070360701c544000d00c64030005241c00e1400103883c0b1705402940c0840e03400415079a054040d042041351561790042c1c1c003000c80c1d45c0070040a40154000c10040c40200403a90b03ca040c0d10b04c0380651804102005c031200c41c11584140613401409900c46500801ca400d1410141c1100c9801d101003400381c0001c4c0e140e42c00311002e0210491100a030a0300240b0b0f42841040080d811700d00c03a40080040b402a132902504074010484240280340040e84044003640c040c1008034104040c40c1d41da50748401c0d1582084820302c00b0394501d881c1c0c41d600301e118003070502d040b40080c1c45414240075581072050368498001c0d04019242402e031080c54028020046081c003100d00034082840d05092504c42003055201d82d600178a960000000c00b00d21800c0384d148e00030b50040240400001010401146480c42c44031221440030b58450091959035a16043c2d8200081800208d408980c1340c080d0008441e55405c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 609730980 1250 609729730 609729739
    0x13032004020306090a1d1c020d1722050a11010e060405010c020d0201090b0a051c0207020315182b090602060c030915091e01060f170319050307080105 66
    0x41c000345544540780301da0b0100c0c0c00345d030014071600c01c440180704048602d8040041da01560b50440c0030003e0384194030000f4031858089030602d03d20700008a9060320542d18000714141400041a541224024030000d9103280c1248100c1401d02900d03a641010f6072505c04545000c10103400d0011541c0001d040b226008040300d0307107414a4981000600702c010300c00c50080c1b05c2c90380024000c045a01403802c2c10301030600716901d1174070380490035070141c00c5600c040d0303060386044a6484a00100503050084410450740500a0310a940c00d400903d152504080c0c2039210848000d0801380c6a24820080c0300700e807540b09401c00451038511300014a03101041d0141004002d076000c0c00b8803030303546c0024015410000075160b650750382d42c0f941d41130390404000241c0042a030360510240000b6150026182c4580d0150151142c40103581c1c060301ca00300c0c0d40758461070f02003c0c00360000700003c2c0c5441820703049941500e0b003a41d1810300018101005040f0901d60f0401080d004428400341940c0401041d024140035075 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 609732230 1250 609730980 609730987
    0xa150602061b1305060d0e03040f140301020a0504260111120903040b0f0f070204090b01241b05070b0703031e14060603250f0e0301060506040302060a051303200402 72
    0x3592600c3c0b0950f401420b01440c1d0004260030000c1c61548071074102c4e0490001d803511552a290385d90b600da001e521443c0180c052880e2540480c0c80c0601c222000000151103030b614141c600294200003c0d080c9598010600c80c4c001d522030302d400217004402c0c0c0030b540c50422980e14645042c00d0364117400c0291490f069070340140000d000303030419841110003d1107260389044d00c0d45120340d100c1c0d0300c0d03101f00c5200071f4215080500c00003c0001d0160980d042e80c00d6144134841881c0e10401001a5460108070301c07002a1154080b118840c01d11622031a01a003e0015210216103800d407601444d401000e0450000340d888076121030181c24400340164a40b00030030184040017451144e41042d00000d0302d0780384074100c0080800e61054080e000040c004402089520300f01c0e800f01000741c0f207900494030001c04124504481d0b041441d040c4988419106c3c001d0196043c18215024171100307400108082b010b2010420508603484520385c1110000e5100b6032140031004606d4540d5844d030700c48042010b004a0051 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 609733480 1250 609732230 609732247
    0x120c011812030e0607060204090606030f0b090114010c08032502120304021306030b070c0b0105240a05251104180209070302091005190906020706080a150602061b 71
    0x79109100964041c507009140c0d4101c0c0c00054807a1040b442d008002ca03200060001d070411445c1c0046c1704680c003644080041351044c080403029a064154001d500410070b000520102022a0f44200001d50624003039040710350035540d9030144d90054404c40540040300c0c5e50b00e150540d0700f00e00c000341403116201411600352134007070b040003900024000070f204c1c0d10a099003100c0130100d907210000440d0001c00c1d1120340e0030080c9001c0c0c2450443c1905956a031103c00000c101c1c0e00b0100c1c003031000c20303222181403480224107084070403564000c40c1d409410030804010b10305240b0608a1302d100c5000001c211a504595189060a04121280390282c02a330508084900c1c440420012040d841d40658241145586544d07049000348521005e90340d0001094124050702c59004016098503807505811896500c1c640500784c404404034850100142d10402c0280720031841400501d03001103030300304049000c40d00c00c0700782c160b03441d910b400035401640070104100c00e40c000c2c1300d120810000c072122043d14000c120b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 609734730 1250 609733480 609733499
    0xa09180e060f060f0405070c2d02040b0f040e07080d08131101110106120b0f0411100306050607060e101b0f022d0d0f0e0409050c120c0118 61
    0x40c40440200b1072500081c08503240c080850903810301c003c02c1002130b032400000180c45500e000c8002d48003001d1282c50740e19010031203581003140d80c140d0340d0080050000396003008040c0202c04071507a0840b503600600017254607640140d03086180201c020300315041c140030300b0500c0c00d40419010380420003114244400780103800c901501d0355421130000ba0a0001105c0143c1e030301403005030300e011150702e07000b800a9122110080400d26911950011546807151850020040b8013078030042c019400c1d43c4113010992030181c0f001b41403100503040c00f0541c035581d00002001c2d80c01200b000d80d4101d417500040308020380180504080b11603010700801080e1a01a00040001402d00100092010907454000000d000700701d000104109101050703c0203131260040000c120080034112524030610341b5810b001401000d170700c03010795034640c2c0d0003150f500c00c0400c0202502c014a000d441e0741c02501ca0a00d0380341c41d0f03800c2c4090112040c0d002040011401e100041c00c6505c46001040e40d030242c403c2c1405000340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 609735980 1250 609734730 609734743
    0x1403070912020102010212090d02010e060402030705040e0f0304090b010e031609020c0111071b0501080123011704030207081b030a11040b0a06020c01020706031806050a0e030a09180e 80
    0x8540d04484141c08070300c010f034028401d80500030364600d070000410004540000c1d64005194440d8024003400e10074240a61313681da8103071402541a04a00c1084c0602d082c560b01081c00780f00704a0840b21010a40c0181901b194415007040340007070b49800701d070101ca5800a1740b40d81e01d4401907008203103003000300440c42c0220300280074070313025250002a501e00c4118250015003101c0326440c1d2495441d8610718100c07440744251418400d0500d48072000080303a40c02080c006040315140d44070110041c0c440e00a000f00b0210305c80c02641408103498038416070350b40441c440b5100342c6c03082d0001c10307041d81800400361400c402c3c2c1d046810000c2008a03a43d4141d200403840c001e001d6072100010340148a42000200a800c1e1481c106801c840504000a0880c2d80040c00d4001d091007030302524402c40c0c60350412029100d002a6031008200515484000a410703603014590202e0b8007440080d2000d65105142c0c1194841c031a0745000541050341882594800b5600701c040c00c04c1b2041c04c00580303849080054a981 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 609737230 1250 609735980 609735989
    0xb12061509040527070911090907050a140f0309070512030d090f05030c0304030b13080910020a0b180106080610030f050f0604140618100b01030f1b14030709 69
    0x180c0f40c07400715400c0d24100c1342502d1210031403220140a0302410f4a869950030851048512007410b04c00c00c032209880940403103480724005064801265100300c003c2d640c3d980300c03242c164104041081e820800349501d50162510007100c6000580d41d08140c84203a191003c25049244111000c05618035201800403c8501c0b9400c16035001c501400c041c00c1c000b50100c61a80d000c1e180b07010005418400304000b200600503a880340c0e008502944800380201c9250300380103001001001c0030800500603140c510308042160715030340b0455000188640c4c80c81650300c0103541d4200c00c60010030311200152420301826014041d440000c11f4545014007007040b541d485440040e0900c0002201041400b000b0702114090310010b10031980d103803c0502d044a101c091078070b403c0c0014000d040c081046010000040e0010090400c020207141e01596070180041c105851102d051583e6604c401c0e40000540c01202905420403001912402c1c00613005004240d21300e54880242c5010401c01c4081d41d040240c40041d01c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 609738480 1250 609737230 609737239
    0x30a030f0204080d03090b01080607092303010c02030409061215150803070506010e071707050313021f18031703040204021c15050a081203040812010b12061509 70
    0x10140c90091402071046420003c45402443c9084041c41d030150418808a07100d85208442d80e03980e00280c940300c1c0c00030740710703000020351800341006109540c00807a20000c80004101403920000ca000a003103c4c060038480f009030300041000c0141191500c43d0700300414092000d4000c02c0703005d90343d40c828075030312485c444c49903541c6204500440790b40d101080007034040b00b0304503a501d460340d09081d90f4a807003d1064803041d079000b4000803050340c42040820109060448010169100c80340103940c02c0d0030041020296a01c40600c620159851001c0c50310360524402d0754101c160443d0200401c8000211941500005808001c00c0003402094611054103c2180030f251685c8552001401034800d80c03581005000719181000c0c1140d9440d03000b810310038010103142d4070321591503083c005102420f1103085043d0304184020340c5241c0700880150707440741c4141035283c98072044030b4a80381d005400380c00000081c1004a091100124070b0f94125400c400c086404108901c42080710700904d100d0314090038004c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 609739730 1250 609738480 609738491
    0x60e12030c0705151003020307051c020405060102010e030a0c1205040614160b040828090e0c0408070305150a0204120f141014060a0f120f060203010605041e08030a03 73
    0x6002c414409580c11103100724040030541010400c805d4841c2c2e032800103078030034011a40005a0343c60000350314080042e03129450700704260943c00700b0004000c0100164195502c61840d6a04404180003c2500101c1502c130a620180e090030a141900050319201c02030000400c03041c80010707080110400110170600095696041802508080e125012001000d900b1484140030400070440060001044a40780c0410340140501140c03404901200110f400704484403401d20550520700c2c2115840200a00d00318940b540d5462120700e0103000b40d0082e241d54104900818030a80030fa40015044401010258107080c02e2031241d00c40064508002070100f401c2c003103090708011000c50400b082c0d040c52401e40714400c0301c0307101c503101400310520043c551035851000151680b9014807950306481d102e2203064042030402d02c408400e100002000d582c41007110302204002012800154068203d9544030ba45461504c0c035040100c40d0b0351b158000c1e00141d0082c081c400034000005441c030290039890003107034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 609740980 1250 609739730 609739733
    0x503070503060c181f0f08010b03060415170303160e0108180a021503070306050603040f0b0601050d020706140601082a0f0301031115030f070c03050408061003060e12030c07 76
    0x2da501c009040342c10060091402c098500c0305c021810a40312580c898030908100d4120498400009000701c18541c8001d0000c92030a080c241c0c0504000707e070310615401030640f503424125404003690301042042d4000400c0042e103100c90a44074210324024107280407101c21070400a40b15000043c84262604e091000d0035201c08400c00c070a241c4c464000d041c8a0320440b801800c074416910484030b60001c07a09200f03000451f0b04104089034402ca41020740d002c3c40181503a500c4e001103402034204d5041003030074059050024001c3c4001e0036141e200f0380c0c0000745a4103200000400c45001041c035818001e52404100444105980c410008120210b48011006134107030034103061300810340b01503034201e0040008010010885603604402400302c46607025503004031259203007488202d403130201044120000c2064640100d0180d48010310905115051130f45504009107421003c52340884800c1d0b88502c01c2040c04140c3c030072000d0700000705028000c1e0820230094542503100142c210080100001862030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 609742230 1250 609740980 609741007
    0xe16020d1403040f1421130b0f0f03090106030309090902010503270d120f06030c06030203130209070e130219050d09080406050a110105070905041a030f01150503070503060c 76
    0x1200d900c092080103440c17401c40d142da600c4052900000142c1840035456101040000682e264000c242ca1645202801c0910071140b540011042000651007846104000840380e03003e14410020790f0300014019113181070040c9486030076484202c51528000103900983d0340041242da0001c0c0d02c130504c0c008100f440003c1c0b07488815080041c2800c1c081d03800c14a141603442103040140c201601c1c0140400310201051908580c107502c801006143c1c01c00003006900c4c040c1d0080e40d88132000b000d01040441241d001300b004200e086548000043c140e03210f80c40c0350f1a00c00780030a0964281c807401c5051094907100028160b0f0008410783c240b05000c205800e03881c601e60001e803482c950110019803299540c5001070b281e500889401ca0110f0707041541c41c034201505114003031150300c8035a90380d45490700c0d01d010b00005105e4856007000b070710127402421031203440410000a49000b903000014020442036030a011400c4180c0020b8841d8210400030481036071b0028840340c2040d20903190781e50f180700b10402003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 609743480 1250 609742230 609742253
    0xb060a05060c0a020307140d031101060b040b0306040c11031803030f0415090816050d03030906090b0a14190e0a05010c050301030201080121060c02070f0e16020d140304 74
    0x70750050700000d810301511400701d9910f28040c0b003503003100c42e044d41700e201c0f111151010140d0150400540b00201e00421300c10007108100f18800070000a006486001c00301c0585d11a4125088500d4004140400703410a4170451034a0a00c51805065803020710340300750f803a4448d440c2401c8801d2404066043c1d681d40510449500711281c1500d0360303a4039a2480481c841e00350160510001c100201e0000903d01d2010500c0000c8807038545504101ea81002d04014001400e01c5003541050b40c0c40400708005402e80c03280c8a2002d000c0e8030041c2d41440c0038004842a51922401c40c0802e4444070144018070301070704c1000c0c0310740d800e070003003c81c60380d50b41074900346450550b02c0c018049600b098504400300350042d005506a9000781c4e00d0313038641d0303884000511342c50042c80f80c54844c68400202010104070243d111500441a070310650b0001c598030424500c88120603040030232410845014400141032030303408100400f54a0014121000c440c000181003011110321001c2e20b03120000000c1d041204007001e5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 609744730 1250 609743480 609743489
    0x307110402031504022205120c0d0c1e0504050601030608031c020702061314121e010e100525050307031a150a0e0109080c0d0804050d03020d030b0108130b060a 70
    0x219190004040c101c52150002c00001010180071070f8007140c9030234803c02094590104100501c100441c2c1810710038142d0f00d00005030348094110401241031031459040901554006081c05802801c1008010448002400e036070705141c6440410040c46401100b43c411000015003040038802c410300f0701101074440e0707040c02540310306c00080e401c3c1c0d92090005044155050742404044e245030741c80900112074541e0011030700d2a840401012021405030100098002d01400086440c415501c8194500807805c2181c05801d41c8880130080c092201405000c540900034000c400e2103070381d0043c05031403480b01070700201c101600c40c0a40001c100300d02d40d44034902ca00141103100080d50402c00a44190405141e08002506002c00b581843d8419000c0d01e045c1c50262024004034040041044000705100f14115040c490a000000344c65840c0b81d1809081c0b8069005820a0300940e500101120008220365061046280c240b00403d04250b20348850700f81d0101c0d10b01420b0b10388600180000e8099800b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 609745980 1250 609744730 609744739
    0x2160b1317071a180f180106020a0203121306270e060118151d030703050c1525030e10031512050309100c050303010603090c060203071104020315 64
    0x456290350000140a41181d00c3c0240d803964441e24555544103500c200d401c09150f24100303001164617440e080511005484000f0054180721440380d2100e10046070990000016800c22000c43e070960409001a44000400c000118139251030a100703034400e04010700070841048401e0002d40440d40c0c159040b100e1030650300081100945e96030054074035201d0708455690004000c0362625181001c101d881d1020740703202180e402508494810100c4681d031803a8008401030381c40c406045c030951418840d46014500490180140c00c1009040c080c0b00315101c035451021500030059944500d10200301c010340200d8001021480510034142141c081c20450745840d4490b050322542c5800c941c040d4001220500b42010400391a40d44140700300030005041806000c0d500100f0100d6260300d002628001490498100003800110a4691500e9504240c00407800300390303600c1400b010b202c82414103400070b00d103500c02149010129992201004428046903000300c0e004070100342030b2100d110350283d88407000380 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 609747230 1250 609745980 609746009
    0x3020a0807080d06050613031502090612070824010e01051911070603091a100b0304030503070305010509040f15020c3012130f08070503070b0702160b13 67
    0x2054140b55224854224160707103451000502810018207503082c19407d9003071400c9203803640d280d0001d05480e5100c00d100c900e60070401c42500d6030310100904100c40701100900c1041c50724820182101d4806132214403000c800031800c1580c508070394651058031a00b0300e4400c54100d108001610b003800f8800c100d0186d00c4c3c3c1103001004613644905d0403440400103000321051195a98010f4044400c08140644a81128000010844255006c0a42100715103010b5860183e5840400c40140c0042d90700f1400036800200f0301072070540c14050940544000c4130307441c146080c10b0b51500b0f8211014a00104401100365032880c10440e5541956000c600034019103500d029074155105d458120b518000018013007051824034290040403d60390003040c25050f204650301d42d00721244034200c0803081240d9008549480c2400201d1040242c425607100e503000750749404003480c004c0d08624000300200115030040100500440c0c04070682021120a02055561180281c801c2c8072400c4894100303501c0e014500c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 609748480 1250 609747230 609747233
    0x1a031c20010b0a0501050a05270603090601320108100f081e010c020d0507060915020d0e0c03060705090a0b0a0c03090801020309070608090a02091f06031b0c03020a0807 74
    0x10b4100b040109811994a507250380c8800054030749010790842040010302c148560202e4003003c5803010a000383c1200c16850801450000682c0380e44100e40d0106941c000100400030759000070044450903403089852000010300748198008c180c48102094100301d121004943c072580980c4642018142c01e042c000115601ea80700f0b1996a000508510f08907610b0080c801071044061082d40c2402e181039001e03000360f415144040300c43d504005025101c542d40e07040010001170780b917002809444450500541c4440f00084010308a8102d403601b14a10340111010070080c1d6008140c0c00e03408001410082c1c0ca59046e040402d00c01003454001841d880c9000560b00758458220902080943c4a569810149503d441d03406090b804103650f64000b0768071109080c81428003440e8481e5011001e6803c95007a000160002040040166000403030600016048417006002d076a840000d0111800e040c0800c0007904200d2000507076030b28503142040902111601014401c0c403207450560f41040c1c01d141c603010f15 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 609749730 1250 609748480 609748483
    0x20a0602011a0108010e0c0c070906060207060f08040203060604020c12030c07020306010501090b040302040c050d1803091509030b0a02040b03040b09010501050d0228081e011a031c20 80
    0x9030044480c12802003954141d443d0710907403081d4140e86020740003d010780c60f61504a4a1604420002c034450302900d03101043c0b00000d84100002000300b0360007018582d1921502130142c03041c00d0702c01c60420852404000c09614002419600b001c2c09850040e80c034040703409000c1c00c101c03507001a219844030020070310012801c900300ec1c0009a0088091700c03e1a641c40c001034030488a10700c0340c0d1a100b8030910003007016243c90742c050741100096003400340c6404189030104040340c5603a549140c04c401e9601e580d40900d9845a0783d10040d0805580700110b55041403000340603180e5500c0014034a2050b80001782d000080c0c1d0301134500512032008500c4d201d06042c90400c03042d100884122407191b20f800000503030b5250150b20654140d401070128a51075440c04a002c00f0400a9842c0c0d11003001101c1c000116403004101c0c003894040640c2c0303200701c0100b042050305e0035100c17518000881d040d903070031303604600307940200e1144119402c40c07444607440351145105440030003264034080500c841d02006054501e00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 609750980 1250 609749730 609749741
    0xf05010504050a051b0a05190c1203020310030609020a0e0403090905060603040f030507060608031603080108060402100f03060f03060203010501022e0903050702090a0c1124060d020a060201 83
    0x400716014041695035010b540122001101d0400501d10581203481480c0388103402030580d1109450a10300d030585c030f2085503c0700c0d0078141c10280090003041c156814002c26090308201c1c0540c500d015440d60411040e2a02a01c2d20380c000a8420765a075482d400455851050140080c00900050307155484c040c200581ba5019503c280340c18a420000040d0301e81c030340348007117034407441d80201124102c0c0c0494808958a4001c030004680860362181c2c0810244030810140503480301840b01c07244000310300c0c0f90040c811003060340310110030b07408801030200503a5004a0400300e158207140841c401803154034114043c2590382d01591100303c080402009200040c0c0003107041e41c0081e02100d403095000c3c1002294011000440007040b0300e406070000c1c013010385411802c0d140c3d0081c5411402c06c0521340000308a0762041e1003070800070340e030b45007148041c903008030290b5000e00d081c0001d882d00380c1a0041c01e001c0389407600d18030010500c1d40030010b9802e035109845620b03a039401401034559a610350902900821303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 609752230 1250 609750980 609750989
    0x4030b100f08010c0c03080a0b040504121b0c0e1012080d1407170c0c12070210020f031207090314060f1302061804020f0c071a0304030818100f0501 65
    0x2400d08000c40c2c400014010030424000a0b41d4401681e0516141102d400c10050840d000258840390004019503e5004840c02603004c1d60707890030301e10b4140c41c0140c5452072007807200500c0c1500d02683c0002c00d0825500e901120021040b02104d40e0301c08203d543c00c00840e0700a000c1308040c0f420340c44280b000b50409400c2e0018500f6041042151a8240581012080724203034005184466031003400c1820101c15a00031a54503089400c020308d2500d41e5040c48003035a0814540d100c017099001c02d6251070700c4900491042da0014000e41005080c40c00d44070312940c46c1c0120b410000070045281c1c0c5208002c004025034112006c1c580d05c0800c0ca204603100c0c4000d8400b0b603000c0c074080d80031505942e0074652801c4000e074001e00c0c00d85402106100310700c2d020a280341c00d45d070040d0300307114259004405200419400c405200a8003140b401c194910400c00c8141c0109403041e030702071082100103034000e031031071380c203d00264070049a1030940b906072881c068021400c03030b40180c240304070200c1c451b084ea0482cad4183d8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 609753480 1250 609752230 609752249
    0xa090f0b21100209060901030b060412080d0c080702060a0b030a0b01080303040308060f0a1206150f030b09010b0a14030f07090b0901080a0302030a050a12110421050c010e03010204030b10 82
    0x11640b181c00a0241d0254400b49a48118104008032203580217600c00d81403076601900346030900e0f035034001c502d880e0640072100f0b40f07080d080060150b55404162259114150450410101900705100c0081d036919000b800740c40040d5840741d10f24803569042080700d2200740d10500300c0754907603107134600c068983d04280c42c01c42c0032440c500701107045850200724a0350401c502800c10440c1034901802044186401001038808030b6950b1081c0e030032030414190600c00b8040001c10a88841d16501e000c0400d11002054030041307901d000d825064030341c0c904040b0411541c1c188280c85602100d400020300b00480700300e4402c0f062241d80c1000403411200d400108820004903084922030fa07031424079079101c040450005005800c10881022250300a001800752508a4a045404c0403400198a801c8440c02c02043c150250049410020800750302e2494405a104022130242001580c0c0c0c0c0d83d50303d05400e07958074103024000c0c0740019262400d6050360002c0d0f4108421810608000a409207640401e00410a01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 609754730 1250 609753480 609753493
    0xd050c041e05090d050d2c01020702130b0d080a0e090709080114060a0312050c1501030605180c010305090c0d0c0f0b0a020705010e040f0e1612020a090f0b21 69
    0x440f1004a020201c109084d00c0e0305242002e403031038050041c16800c89035070b01007134180e0b101e051380741d180c030300e01d4a100c15100b000582c0c400d50b900401c40c00491a03c056000c4604211003a109a1192101041c480c0ea10070038481c3c80d0160740105583d068050b440c100e0b00690400d04002c1441d84c0641900d0844920360000c220511848502d100500c034101d0f4a00c3e00500041005c10018441d0500e5110301d04451800a0400601300343d0305082c41c0ca220300d01d108200e2030300c00500500c12a8030446400c19030700c00d0300c0d03605062460303800c0f515650118021810b1650392000244800303030034060345460040c000c03c2c03074104d981e00345481c50f07844560f07010340e00340b00b00c0001d00440c0d842e003c40200c420300d4005d6002003040c10300e00f200441c1c0100c26854015042070b199140b484054405005e01200312b110040604001c200516192150040640c008081c2d0808001e4030400340e180c5001c1141980c0301e030f03100440c00a40c1003441c00050038200007007540010451251102d64070150303555400300199602617525 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 609755980 1250 609754730 609754741
    0x903120b011409060702010e09070f03050f04030c02121e0307050c030309090f0709090e01051b04060504060c0821041e031706191401030e030412020d050c041e05 71
    0x2800071000c4407000b8018030070020621103142c100050134600c0d01c1450700030840050007003c03a00622080e0b8094010420030903c00206680500415a0166440568031940d2809440040804900d104040c0c061000f0b0b180440c501e00040c441c3d500c8601010000e00a012081040303941d403503100040585241c02400307000c144524002c000c41d2030a00d0010308281c460384540940c4c200c0480d01400030810311460754000521035046008610315044078000002c0c141c0390119240306d440b4622052954422010007080c40400d400c0815101036400510707006050300d0751858400c450744201003610160a408290800440c41c5425000b40314034403e044200020181d016040c0b08003110000040c0400d0445030a8600800c1910509074011002421032000d128819845150420319400c6020400146101c92400c2d5800d800b903c400181c0890045182c18502050048c40c0c041c9028000d01ca481c0c4072451300140038041018045c22000117004001309821004442040844000603858203802e00c0c00150 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 609757230 1250 609755980 609755987
    0xb0606031003021507060c03060509091c050a0e0607060605180c040302010c030c0b01060e0333060a0906080102090109051002070e07020f0f031b0601060e040b040e010903120b01 78
    0x1e008a48145661840c9401d55080082100c003403640e5600068082c0505004104d441c003850104520a0b00d001410314202028401c101d80300401c030141d503038080d03210320080c41845100065110100d1901c1c0780ca0b425068807c1700c04075504d6800a81c488008244d01060143d16030248044500841f040c0d01d03a000c01c1e10000f00030380c00440c0d4101c079004003880104055400380513101d500f00c0c82494024a420203a40c1c60364440482078120f4000a500c100108048d41010413881c050300c041c0031300900416944940000302069104505513540c0056000709186440b07122000b0060b1214640600c080c948440e8180c0c001d401ca00c500710b00098890100091908150245465000159001d0403810707041401900c2d030f40902408000c2107105001e010078104c0c4090255807130268051000d982e071001070400c0c4608003250714401c080160003010040040075000075080112050648000c40c100000100103070051404051064540d403c0c02c505170105030780040340c405c82c140d0990003040041078580045 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 609758480 1250 609757230 609757237
    0x60f0a05090d090302040903050d02030a0e100216020f0d05150f1e15060903070b0706240e0c071421030705090f0406050d0f03020c100509010503090c0402160b0606 72
    0x10b50108071202c00a00150a10f900a81001402401c00e1454541c1d4441b001080b42d0003140c900b91120b03540ca581c1e81c1c1030720083c0004960151404402e41c2003640e10200c8141004e140e0308005e01c030b00210316005000303445280414100396007000c20303580485a004450401201c0440c1e80300341d0b004210380000e0f80c41885c0016103980c800954141c01c042e65401007c0005200320b13070b000c294010743c203011801c6640c1d070400c000005806141a8592503c80d2440e2000950381e0301a0340e030041003030100355000100c00760450042210795607000c884185d242c10086611b5407043e0031020300041c0c401d000042c40a10b00044440116035440710300102514400c00c00c8002d030009071034800020318200142d4501d4685581c1082203010300503c002202580e0b10000354401e804040100d4603900f1121000007410f03014800191012404d4407103020b8810380c2d1034024000e1060901c2c8606022021000c0f4100000c00c0240906048c0d01820840d07070f821814580043e10800c2c00d038101c641c0c8580b000010b12508054056 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 609759730 1250 609758480 609758503
    0x1208040602060702120a1107030204020a02010b04060b180607030c080d06050108070f02061503072c0f090303010504020304080705120c07140a051002120f0306090a0b10030b01090503060f0a0509 85
    0x90034407801d546d0483e4030b12281500660180700c1c1110110260742d45200800300341182d90000030300b03406000c1c03e100a0303d41c00c0d8081e5000b46004e102c2c078030403510601007001124104440040e40c5990916095480c80300c9841c1c098036841c00410141c5001d9142d030301c210182c440903200c00720955140c04040318400809080c0d0401030300180c0110b43d000e8602c009e0381c82c031408014243c46009445080040c604400800050040341c0c2c0201c0f0f1440020301c4428460700000300140c000182c2c030b005070092340e403840103210346409268000b0002d001d2240c0042612501c039840303426075140307800428140003a80c010360102e41d003d028455001500f041101809030301641d0161210b20b04600d000200846500026000d00940c028860f100d1440740802d0000c000d4078441c0000551642800702c03d2025007180145000310842c5421610b03180d940d94640c807021100194640031904803500401201c0740080c41d030106030144240418440a000311045051084c00c40345401c00071980c070b074000503a40b02501c044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 609760980 1250 609759730 609759763
    0x906090207030c33020406090f080a080306060d0218030f0d0c0206161506060f050708120921090306090601030f0602180d060b09060402090a1e1208040602060702 71
    0x3a00b03400220300950900c0340768042081d0300c1441c4c4d91500341941c03688a009440f00400d9000a0a001d52500403003a40c007e0440700681206c034909140c40c10703694200041c0040c1ca41c031000300000b00315540340c1d4210342c0003001052081d52607d02c400c503807200e4141410541840790180c80350200441c0e01c0010180c00314100b540d600c1542101d04c0d02804030b01e40c003a0b40900300300007401082502040c034044201020000e140700001d480e0746400c40c000c201ca4030100260040200410a003000f04507500300356081242120383c50030307403501c2e03212a15203031980e8502c0c2060b4440c046041d1a00c1002c001000d003008501c243d080c5c85c00c581d685d28000c3d4954000b4000108076249203003948021590503400b500044400840d221005002d10000600c4d1811200c02122003d0321100c0c043d1071402d000c14a190840c0b000d803010350400304488002104903400f40118080303007000c8188000d42141c40c0010b6070041c40302c4904010342c4180d50800e40c1c0f540e03001e401214003510070180030407004d030b03c00600701ca11003032580c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 609762230 1250 609760980 609760997
    0x9030d0e130b06070209090703030915050919050301061512060b0301061b1a0406241e0b0703030605091b07030c02030a050607020d031a0f010e0d0c0e01090609020703 73
    0x1480700030700e144a0010340000080c071651005032980425140180c108000401e00d01c6d16500d0700500b6100369400040c44800c1c20401c17052030310303005420b81d20b50083c119240c202081e290030640c00600d085070301159042d82410400036400c40c0e01c0032502011800c1b5984c010070701d004c000c9014142d400c0c62003000d005c620100300400440b846021724002444078491104039952698a424071040e1880102800609000c0c1c188002c200c0d01d03125500714120038075801c20440040110543c42c0103203610502940c42c0c0454680a2941440a0034401400d1510900b07a00c0320a035090080040c9007a0040030300074001200420b0300320510b52403070345c3c501c0b0241e1403c03442d090b1035503000c0300d02407035407003040f6094401c0b4020300b000140140180b500c51003641d4010102d804808400509452801001c5511841c4d0601d030301d08951a41c2c03001d00d0b401402800d0098044d144800440e20207088c80754050000703180c1920118440510a031600e0407074119070b105100380c0f900c403014039049200300c00340180401c00e0352 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 609763480 1250 609762230 609762259
    0x10061103121308030a02191b08030601090f080a050d17010911091027121b1a0c0d36120b0405010e0c090a150504090809030d0e 56
    0x1001455070100c1d070841058602e500e140e0310064544c105031022505250085554030a09104070801f1402c48800d1820240781c01241ca0510049005480058030302030000000484a074000c07103002d8002c1c034103030103c8a20550b4555405032104029001210f01e402034603403a080c13641c803880744610304140c40f40d2644007592030101c000c002070507441041d0315004410311281010b661100789040005103d40c41d006507130070302814090b000c828400500146a4084e071701c14881c5440300c003504003640360b00019546030064100c030b0b101035400841d400a0b24030380c6d0b80c1d00010340f50344000c0c0103045041021400c4440750788410f9019502582031401c0c150611001002d0184803941e1030141d9411414019030b086641505d903030b102941d02400c0304064644a120702c052108002d400d101e4444c1012150020b010580b40c180300003401120301415103921140c0303030a9014607204814a20704010328008000300300210840c9400c00f03590300101c07101842030040f1504a180300d80a06100d006e0070348020080c07082000e04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 609764730 1250 609763480 609763507
    0xb0702010519020a0e04050708180d050a0e0a12053f090f09100f090504031709070f2727050325140f060112110a03060510061103 57
    0x80d0135401088603100e6894903640f00c0740300b603c0c00b0b459950783d0b0802a2402c0311280050792800d040c807200c4c9a110450081c00340b0707444020b07140a01a14a00202c240040c0c000041025a5036081118800710150162080200002c0c4420100100f00b944c1c0c0c503191040d107148082c8011180100d0303007200c09241a10f01c40c0301680d00411420700020081a800108600482c21184049814a8001c0c02400781804081e0524a5040c002c1940e07440500440c5056540246807100d000300144145a40c0004911800010b00c0340308050035070200d00020712556a08208545d00ca980203004904a0041f04101045c4150040c01020541e8058400c1c9142040c00c804103d1000d40906132807500041c01801c40c200001e1001d00c2d05d0010880110380060000d0801218540707000c02c860b00c0c140e00c414441302c000748020035618112000402200904181401c0003140e10f180359041a45c0041003400c0803041116540c0a6805a400c6d036640050443d1a0b10303055507203005060481c020341d4001c0c002040c4c0e00f0342 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 609765980 1250 609764730 609764737
    0x16030504030e0603090a060e0d0306050d020f0621250201090c1e0902040b070302160e0103020d06020d05100915080303041709031f0b06030f040611130305010501030b070201051902 79
    0x401708482d410751150301c03240116101c3c8a11110389404c1101400408c95140c056100a0501100c1100c2000081e45c0002c0c44000b0800115024260100c1c40545807074008400d4046410b01611f0701e15140b529504030360720822922162400c2c6c8031180740c03e9510b94030500c9800703846903016261000380d9040c00708102c2071020500201c03001d419000808125040c81740040c0008142c0010000d8583c8010311340a8180f8880700300003000859036880c204943c952a40c00941183e070142d4007114507035200c3c10864080e00c0707411070b8840414104018007480990804d404401c5690112040104c0d0754070600e1900d8201c0039124280f00c561040c400f040108000c0c000006000b861114058a4509084086810403160101d401002d034280d030003507101c418140c0035041810b90100e03046ea16502c2d081c80040f0081034050005001c103651603510f005410048802c40d8115802481c26040304c642c0c9242c40c034060f210034003017110a06050808600418014000c240c041c80c592205c0c00b52004800b42004000d40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 609767230 1250 609765980 609765991
    0x30601031a13050c3009011401031707080703170f01060c0b251112090a090c020a0b1008010e010b010e0d150501030b0f1e0c1806030f16030504030e0603 67
    0x101c04115003562808800c440c0b00380703800d00015200c40320703861089002407004011b00020381c907410309900b50300d03002c606081076054039404102001c08405000b0210340c18010880010159140050007501340343d040101d045040001c901c4065035a507921000d0101c5000a200c0c42e4040745621401c1400107810040c1c117903014164200c21003040c2481b560b1002041042d00b016800b00f400c5a0001007503800502207548224941d0300f940c0c0c900480340c00840c0491480380310380301e869669a10143c110760310901c4010419900658034021034108032200c4407000078240700e524641c0d8605682101b030b45038103000b00710746c59070143c6071906540c0341c403020300c0480000e2400484140f02c0d90f0341c450341c84402d1442128080c502948800880d0314101c0032032010814090012038404175451400100500101d0308564414014514551141011289041107600d03400c40540c2c041004401c120422501100b80340c800e0800030301440014500010a070121041038901600047c8840c5d846031803410f00341700454200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 609768480 1250 609767230 609767251
    0x60b0a0524090a090b0306010e070801030f1a0c0912010618020a1101020c0d0311092d0604030510050f040b01090203070c020310091401020f1801110a0305030601031a1305 75
    0x124800c400100000642e4100c04070580d50796910b0401c5c0d040801c19140508884414000203040c0340d00040c0683c01c051000614907444d00d08035004000360420216824032030004840340c2420060050749080c0c0041e412a4001c151803104940c004030140180c80031103400f00100c1150075000194003019502011040d42442a000f503c40e140070424402800c0081c00c103800b030550905984802800d0b656803d110f200da48034140000c1645690b8036055800d500d285e000207401032f41e429640f1f0000d01c1641a80d0729441400464004280603010440c402114102042007025640b10918108000c01c2543e001c0d0a0038030040040c003035000b190b40190b820075154100600c0305541e66000070320345020000d00d6203d00d0780f5100040b0030007001d643c60700c4100142000030750422151008010b000c4c003621310320070381703200c0c072a00c40080030790150340c1c01e0880f0300081086d01c1b101c00e138504001e420b039801610041e001034641703004070005044541d18040d8101009081010000d010107800019000c06880d00c200c0d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 609769730 1250 609768480 609768487
    0x906070f0b040305070c0f0e1303230c0706050403050d08060307050406080a03170c0d0b0d0501060b18010302090a05010c060605031e010e0318150d0f0603060b0a0524 73
    0x101d00d0780792503a8400d612940d00c4559030b094a1528000c5400b82d0350000302003580788507052025090080d0740d280c0c0f0042d00c07a030300c4188060505041b5140071800c1d01000f56084c1d2400c0504440203c00020182e4480240c01c4a0000e60340d003104841f244690b20002d0902d030004c03503640c0841d61256a503281c1103c0014125007001d9100d400041c102c0d1301940c4012643d601040080701010380009000ca0b1500f2542500303c8103150140c1d1807101e6100d92601088010750321480301516540300d2090b5a501c0350481c008001190300c1e101080e0056018800c007844494803044080090342c841e0084402018000d44000e12407840d140c0191081215050125116501d450b0301082a4070200079118050344409681c0040c03050881456003151840001c0c211160420009941c040107003040c046981c450a035079403241c2049600700481d00b0301410a0b81d200040c2881c410750007580094000c0c800b5640a07040c10001ca000c90710070820410100d10445411012040400c04484030f00c001040706420042010b031715 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 609770980 1250 609769730 609769733
    0x604021018060509030f060103170d09060926040807060f020f1b0f0d0c0512190b010312050c06011401030212010b120c040f030b0711010e0d0210060501050906070f 72
    0x90441c1d41c0142002900c0403901035280d207010061402c0c41c2d4102005401103504540321100c0d180d6003070f1140304007900006924011100d240d40701084180e0010010407001d0590302d00020071114007134041000003500c0c020600143c8008086600b00c6200030001e10100785007c0e800d0300c9821007060f2039030a41c01143d0714040050020b10102d0844201c107014101c00c050b01b001040220444880142d0040c500040d1401c0000c204195900607100c0848850310303520b0010040034686407880217060301c4d54441c44428030402c1030340200c19050b40e1241207550560110405c04581c6030007018401d104562040d4010401c0c8482128209020a018940940740015002601040c032130280c1c4800d02c00305001505104032611814070301e0f0800641c1ca07441d46007030710b0b0150751800981c680c00b001d001c601004000c90300d014045c000100013403001c400240100c180442d052503c0700f1603090b9280240c094072075040071114452240e1400da40e4141c541d43e0402819105000d410f801415046850311411400c510 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 609772230 1250 609770980 609771017
    0xf1c1b0803130b0c09010903140102090d0501050402040c0c02060a030506121e0105070e030307060f021306020609010b01090f2615090c0d12033611030f06040210 71
    0x602c1004801da00c00c20b819850b25040e4000301d001070084550030010300803410160ba120b03c46104681e0066420003808c19014081030082c0315104003164041c10320b132418420000190400c521480c000c4504001740c643c4c800041d6400319020000075400302c0e08000d0020b000f4081d1740880d800c80e202070502c50f062010152403514000520341180c0040404071070140d800c080034052941c1c01580303840c1084940101801103035581c010000018902600d80d449010f4928040c0c2c1a42d42076407800c802c1200d2a03940e0907020751501001c1d10f265105500341103111000e94002d402480c00c0311140060100c2003460140c0084062000c41040450005034070311068607858100203501c102c000c001030b40e81d040c0c00c0c100d8a841c5000c01d0158114010344000d51040080350410600e541d285040f8280402d54800342c03004401c0d82c041c1c100c008101c00352649442c0c92108000c020b40d45015204e2649400c441c8901d1081696940100314240e100e40e10240010f00181840c0b10348880d0f8201c0e90400a560804940250 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 609773480 1250 609772230 609772237
    0x209071709010228050301270c0302041e051f05070206031609060207060509040c030e06010801020307030f0e190c090509150a18020f03030f0304140f1c1b08 69
    0x40075580d00800d02410401c02200003060802c8a0b5254881108003480040c0080c04144203600f808603d616285907900103522084084010707040e8104481c82480d040600250454010a0468040e079441d100c0000302000c0341d6000d03940d0040440b910071821480080185111031070800401006001c03481c0141c8540f00914000c004404240500866000009000324810b034403c904640c480001000155002001c45804010540b00030a02500700c0905401030000004903a02c00d2103507000000d80d10320306601442c000e0725541e906001c5202c4401107541518030710301300140d49030801e0008070ba20301d0300f0301001c010151098400b0b18116644400b0102110f03422654840f40d47c21642c10181c40c502c14110481e4003624541c1d040046a11b45081c1002c1c8101c0460024050200e02c1c10890f1310350f0341041515100320312800041d82e00d01d0301e03140601384030b944281480e596116205454808170070200c1c1c08a00091944c60b402c07181e07034007480c049809811441245011407200e1408001081044008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 609774730 1250 609773480 609773491
    0x20402130302180103020f0d0f110d12030c020105090309091311090c040510030e06070f090801022b0b100e040603060e06100f05060a11010212091e03120402090717 72
    0x1503141c645c91801440400c0c2c6890100904c01e0500400081c00104014a18a00650031908400c42c01c158400460715007014074a0241c450741034041c0e0141140c3e410b40041c03104040c1036001b071160703848400c8003c0c0c0d2406817080c40c685c00301058001603185800c03900c20034880ca000d01c00000c640420000807031011013050344e0340c089038080041c050096050104600c1c400c0d0b80f144c81c0c00c01c41807040c003404c940c5650700900b20804000024480c022000d114040704005412404021966070020280d8068001d080c4520161811042180311040040fa807040181242c4081c00d01c0e844000d0081003211109448410960300550320303c0c0100102c0c03558840d0308030b90409800200030318100030500c2d0549450b903500c100344441c1a40010310541c0c4035402551060403403810260710504440c2c425501900070402e104006450a40403c0001e4a00040300c81851441d590585010a003014003039849100e080e1082150f100032902003801070034030740900e55201c40103240801c000b610340e6500380c0b1414070a070368 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 609775980 1250 609774730 609774769
    0x705011d0301180b0702010c0c12030209030111030a06031a01080607110102070c091e200a02070504050705070c0e090a020f13090309090b06071502160f0503031e070c020402130302 79
    0x400410310740910508403c1011828044c0025400380d07032b1080c0068441070f50004040d008100078145440c25000158004006040d603610380c90b01d441048010803181c40207a40b0baa00e101c40f49071111907150340c0281a50103c1026000b10703a0bc00e00162144a012041d000349907508000080120381c5001c11b24000e032080d40004600c43c2d00410b4613002103080c900c0d11070b0400e803508402460205c00c0e840c1c0d130402700f040c076281e0903143c84904005a0070310354070340d21030b5801c2801d1004004013036500200502c40710307100b00b001440068560300d8a408440003281c11005503400480800017520b8840044100390340c00810300005c00351001e281c2c0094505c1d001085000c00c0001c001030100c20176a006000c20441c6c2521030500b0000b182d114100c0850300c1455400d906a40028046501d250324500403640c6e0f0b070007001e0700a002000703140003650b9034021180c04500030781e280a01e103544002c10310001e0240da0b0039592240702040a4080100035440408912040800b1160000041c4c46d50780348100e0841c0c1012 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 609777230 1250 609775980 609776003
    0x4053a05040f06050c06010302130e010203042d0b0c07060608030d09050d030b0a0515071713050927030d0e0c0405090604232d0f0705011d030118 64
    0xe500c1992080b4681044091003c18004c05016180014001d41100c0d0100d0f204541c0d1030042d4003903802803c404503401c205500000803c0f0038040e21024464021000d8001070f8000c2c5a141101060704642d0f001c0203000b21100008100007403200381c00381c04103500a00000401a40d140309491450b404007151041082d120020704083c010140b04000348500c0e41c1c213090210b00c0d20400042d0760a010781c014288203c800c00b200e00b00c440c3c40002074174442688110507441c41c004450811000d0b81144180c0030b032001e40c42a020030036060160850b40100c2c0d080d0403400e01442c000b00d46080483c42020900040e100501082c0210035040c051200f200c04c3c03c00c081c1000320005030a00055403002481043c15901540c184000900d01d041840c00040525200d04849081160901d04100b542d83c0068035445509101c00b00980844035009505071860048880c1000c0c107074401a2244c5561081501065038991070400c200c10401c81240c070b07610010300008049000111a404e1440c00c40c0d001d903880005203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 609778480 1250 609777230 609777239
    0x201020601090627150b03040b090d0c030c020f030607090305010f0c20070e0c12071d01030b0103180b07080703050411010e0d0204060b0c100504053a0504 68
    0x140080c50150409660520079503041c100d403020400c503540b0b080c0e84404030303500750f0780d1883d42154001da503420090003510300481d5a8034180e0203642c00940e003e41c1e80892074004075010001c0000c180075032a090744c5403050702200584003a40c0c074240c1f0140c180c2e084907101040d4080ba0b81c2c140581e5101d550030351140c0785020b045088c01d40c07c440ca400c03206401685805095540e4076040302d0324800040036950b2480340c0303281940100e07040ca8501d0b840b25142d60012010300c4072601c480c01c040c201d181d0000510380308a55940108480c100601c100b4041382401d000d180c0d102e10351294102024800060601080d9a8160a0b00c85018086500d01340c800103100800d100c0c15650040c203842d0402c816142c02d0101d400c01d52680302c1402c2c58010007505000a9030311341e04040d04e80d00e850000b195002041000701c1d9646100c500740360360011711044003e0041c100f095110740524400c2d24000d40e08540244440d800d440d0110f01d10881d051f1a07a6903c100e100078104181c0400c147c10202e400c1d55039291030301c030340c40c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 609779730 1250 609778480 609778483
    0x61407020f01140124020319031a010e090109020c07050616020a1712031b0319060b070807021908160503060106320d1802102d02150f04020102 63
    0x5101c0c00319440010300040041c6038884072802d10358800c6034203200c510b402d2410f091f455441120300d0020100b0382100154406030305540414404034030040c03034100307013180e0100443d1464090940c032948814000014001036020b17502904401e0a510100c442d6280c03074200240c02908010b03100c00c06004030449887c110300308443e60000805456481c0d2120200d8455003584a10107980b0400b41c001e00480080c00c29511a0b0901204d000c502034130f10b03070341d0610040e03210325031785440d88904204d41020300c0001c45600d84401c4500464106070030794286171141e42003003003480c050240c14465510682020500e040d0510448400c2448400b200044030324100916013032800503400380f001d000c8600c0d040b04903010031001c1105a100c012615551032640001c23148614041c51107401242854019010004c180d41032000b80e019008640d0b05424042d071990884a032030842c22030701620381c07000411074944280300c0311012038a040380c010798000743c00365049014501b80c2103404a903c003c60109000640d43c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 609780980 1250 609779730 609779741
    0xe06150627150a0804031409150a170112140f0607120c082e03081c061e0e070201020d14010905060f01050910020309130c080c12070507061407020f01 66
    0x1c00e20301103040c103c05482c040e0600c4c03001407001c1d0130b01c0042c003101c40412aa003411500c06400040241200d002e44900f00c5081c0c0d0000c03486140468140d00300003042050410130581258035080c0b85031a411002d540d07038002d940303100741600070354450404100481c60051021610070ba41d940e458000001d0b00e58044801c0c0c480c2c211845090101280c01c0c403400b600511440f04600381c030402c40003508a10301c40c002030240401c0d440070301512030128400340004040c62074a15000541c030740900c1000c1d00c58444003400c00201c6040359403141500410820251851007080d40904070740001030801a1120050301030300d825140741c443c9080541c0c014404e42815104158010030150341e0394402c05180c2001900c1440352403045403158004c41c1c40b01000900c00c101f2202180000b03040c00d0034005245642c80040c201208801d000310f43c22a000851100c00c65054a1a00065072044039250b29000707000c2d0307226841104141e6080341c4a54600c00803500e403810703213405101d0302c0e80100520382a035400d050031070700c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 609782230 1250 609780980 609781009
    0x31204051203100504020f070606030b100801231012060c091e090e0708010e06090606010203031b1305040216030806040902060f09191202130e06150627 67
    0x8005106003c01003103000740610680b131055500585e11031010210741d000b0301a1039001000345062079400300c00c01800300142c1d4094522299900704807a11004050b0a803904501440c507100d01c44540b00c0880c2c0500603a941c2c001191206102c7c0d5940c82ea0b042440360f00300400300f5683c00e61154401800250f1001c01c50004020703c0048820040c144594440c0300d1403640318542290340c452840c6000000f0500241c401031040c00020420040c29417030160321040100c58041d8240101e400094865001008881c8101c0b441e0401c0c500840d02d00300708a025401c0f5181c1e1340d60400c80b202000c0340503241c40c401000061120b64111844508502d402800040d0041c1094011410228048010388400068071520ba10b40c107100c03501c0740d100ba0041608a03c0b100301100a0342030240e0006002c94003125110b072105e0090300c10361000d801403030800d81515070318542d003102c55200342e001817641c0d8400070ba080e810301002014180703410301240088075044542820b001c00b0410620043c88a40f80000781402144d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 609783480 1250 609782230 609782263
    0xa0203071139031905010e030d050103110609090a0c02010912050d0b0103061d09011515020f0309090412020c0901060e01081510082e03050609070510050a02030c03120405 75
    0x3015400046512000c04420a10300da0348404d505004021080d0000703070a1070104401c80382c81c0c0d0383c1c00121001901007031106803402c40d03e4500c1034410b810318504072440504040c146820307549070a00d54034014100101e00d101155603c00c3d07100300140c80d6003e1070b500c0382e040f80d0700d1030344586910380300d241220f0b23860411505241c505a02040744240060b02d0f1080c80410710443e548aa0b24294a903000d00042204002042641c51011076400d008240e210460300041d800c95600440c51410b069680c46071a010340e6014841c5000200000c03c44070710300a4a51031032054802020f081c1c004181140801c0c0c02050220782d17070141070b034130030b50f88041100d0b40890030848004404a04002258000038802100e804004450300000c0d2004581c9041b0302c4200c2c610004041d42044562032480580346901046546002c1d94000c01d107551000a240e2055800007003c03050400341803481500c070f80c6d00640301403066000611004561080510140c05040c05001d10700700503240919000e81861010328004268 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 609784730 1250 609783480 609783583
    0x91b030501361104080616080406050402210715090b070b06150a020109110f03150601030b09040b0402100c0c0b13050d0c24080a02030711 61
    0x500d044080006000d1218410200b10100c90300030140c004140b190000c602d4500f0070b11582c0b40079800200400c101c075000c1d8244c5960b511500e0252074001c0806050000080403003000c00c001c5511030b481709411910042c8510501038412550b4242980307580c0700d40141d03810440c810406045100c107295140c800f940741415100d420b0481f00d400600400001404040900b00050455125050a8a0083d01843e044c60b02c480d648507000340170b400e14040407a0750321384030038004015080611b03202408441c010f010707090010980c07003e82200b500c003c108604050703d5104224464858159150080d400340260f2540c80c41c0c14010b04c104045401100c1c010400b1505010003ca40450700c01130603180d00580c602d540e02e103400002584141307540c001590140c8141100780030006104070398000c8459480380c0800e100008030380b007030810504840c050042404170703001600000c5d0640c01560700448905100c40d41d4283c0d008018034140544250090715484d5182d0040c03142c10b104042e01e030a00004020fa00c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 609785980 1250 609784730 609784739
    0x1d04051e090304120f0c0503030f030702070501050a02150604150320060f041401020a14060f06060a091a160807150203100e061503070906090f05010906050f04080601091b030501 78
    0x480442c3c1d034080e005070608640d0800300300306c240e4040010103004081300c0c0c07030341304600c19600154400d6502c003003d40318151000600754015400d5034200c1001d6005013803103a00c460081355880200a0045900c0307581c0741c28000e03d040b0340c1703080e400180d4090200980ca1009840d50002502e003846503e41c81883d0038403071104044140e10480d026580300d8000d410328403842c000140c2c03825030b4101c401032800794072048180d2640000a002c9104919510051042c4e40394981401a05e2081200420024031003140034018256500d04010080c406c0da070181c0d02d400b541c2415030b507602c2805102154152000141107052181c0f0000c000040d5030500b02c11840d504004689541e5501144110500c481c02d04001501e5540c4003c0c03d517810034120b86625a80e482d040d00002c01030301031400b85402084005902081d01241a8680c500b51841a141c0313071360190800c030090782c007504000450b000b843d004120206580c1d41c103100300750007070070f0907140810031040c41042140c01c0705080c500c03c03041601c1c5c00d00401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 609787230 1250 609785980 609785999
    0x70905031005220507030614070e10050f130b0f1c050609070e1305072003070818060d090606050a0b0c0a030e0301180f06060e0709061d04051e090304 66
    0x2941492102c005501800c03d4541107042284075400505090b00e013039091909185c003d4083d40c403490b0240e46800e8a41d0764001082680c020380f29100000039420f010314980d514240000342144007189008881d496601c0030f107854181d1207802071290140d0081010300711072182100399000003040d110305000d40d1500e10301080c60240b008110b00e040000e50400006180c40f00c900a0b0103088010308184002d2601850160000701c0e055401e45019250391104a0107203400300c207480d40c0310307803119080e45085d2191104000507001243c05680c070031800c01c5042059055803140719000c034401c21001c29414030b0442040642c025651210103100300c20451045503503404102e4030a500c0e40345c20103202038400300740401d004084004a1201d062018400c507001d001d100c814481301644511030034406c45440b003c45c120b00160907500748020038200c220034006240204803320320fa05074011b084002c08004c00010b0141c80d0700b6600403000740c0a9281130800410041c80c02036200b00c3c4600114901071234043c03903c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 609788480 1250 609787230 609787261
    0x15020f0d0f05161b120c120819020c03070906030f02040c0e03010c030e12190f0212031801140705070b040f05030301170106150807031a09070905031005 67
    0x20003005012441c14030200c0c0104141d40a94124045903041c5022070b2034200d61810f81120300400012410740001215001c0902c0d1030010355001d4044011949000700310f520010503030b072049900607000d101f00401c0860450f1510481c151030ba0003000c041104005050605280b5003180c0e0140341403003018004503203400045031000398141c0d000074209214100c12100180c0341440240d055082180b10070303c650740360300000c940c00e910b0000d6400754006e00c140e40140e4880c0400d054200454090791858460003080d400b0305900700350040c0d60a800b14111013121f41d5204540040448421002200610009101c5d04902c0c02c25041c0c0c09007a4141040050150b0080d400001c0c01d810659001804012030401048030295001e0104ca40740d5031200d240e000104100b500e89201b0798601000000c1500c0942c03281c44c5400d030240c807000c0b07054446c0c4a00314040c0881e80d050210030090010304481c56200d1380c6285100c0e16403661040c0322903040004050820101140130740750306080c0b0b01030210b0600d021110 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 609789730 1250 609788480 609788503
    0x7020d051b2e0306150f020c0603060f06031f03140c01080103030206062e021e0102161101020313060e040c05040e0610020f0d0314070815061812030415020f 69
    0x1080b10302001214110040d01c042c0d00f2130340b0700030701265030404a00d400034540745c132841d456000c0c1d40d010034a52042c050540811130380e040d03100d0700c1f00242c00002d00f409001076800100070442501701301c0201c0069201b05c503007a8001c4584410306060f11100c001d0502444540007801d00c2c00d02c40c0c40d495610002d50700e01c000f030301d514807581c1541d00c44002000c04e0b0301144410740300d03992622804c00c218100603442c4c1000c01200312040400c0d00c1c040a0080040c421103511400071200c89a011000740c0310074130180380004059042d4801001801c9900800740c06582c0248030a0b503d0014900984080c401560703124502a014010140310a0065103080c400c11030380180700b928a0907408100800c04ca2030004c08072401203c502400c10401a03040d8190030101c440d546040d441c08243d02d6410084a0b244400c440544010300001d117844454a01003005055554a6403d40c000d9807622100164400681e02002001a800050204840e418079840013600041034006403400c040b9241d8501c1c0c60b0341d40d8214 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 609790980 1250 609789730 609789799
    0x4020a05040b2107050312030106020105060607030c1203090206190e0f030a080c0a080f071a0f1f09020a0201050f090c0a0612020d0903020c010201050a2d0207020d051b 74
    0x180b02c00070060404c03040b4000d10b030007030444414040d40c2e15982802d078028081c0d5401542088000343d05810507500305d600050b4907642e03040d014100350702c41200c1c4000c104100c204160320340c00400301594541010742855104402003840300c20007580064140e080301009240654140680d14403aaa00403038800111500907407642d941c4c01182c400c4a0070022001d4000b0100300020820002450020000c1e00e021403082c401d5407444000d0903005880c502c03084034044104501100040d4070701f1303900d03c18500401c45445c182036001c2d072075001180690308011a1000141e6640c1d0410441c08a060846500314a420000c3c000000c1858003098142c3c14134003899040c03100140d44100c4202c42130741118014094070404206641452034003e46070800b5641140c0103608101c0814144c035440c0c4244518101021000a901ca29400c40c01e8940f50091100c80d4906a003801074201584943c0003807901c01d44030b68054056106000c3c0801d030314044001c5041c0c000d020355022140d2214031000054100c040812 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 609792230 1250 609790980 609791029
    0xe01180b07031b060e1b1504170106030c1215050105090f04050c0a03030528020c0112020405090103141e03070305070f2f0103020c1903090e0f04020a05040b 69
    0x80e010120003142a100401c220320300505001090300124459000401b419840c3c640c0325000700404c84060381e0180c80d4180444c080000700420301040e002480c41d030310800000b249d019960346038142620b242e684030f0500c00003501d02c020b04015803040c8040c0a4110800d04124550400000c5a14070100402d80000c180c200d41c00314013030090402161481d0722006091a0351241c40e4540104603811003140c000181d07296101c0d5007240c0311010200f481c00107040e0f0050480c030f440c0c20b004486c01c01c2c0180340b44d40c0c840e80c02c00010909031100740e41540610302400c2c0000f00c0244140000d45446200c20420101824103480a420183c000c000ca07900d0a81511b0300503140d1a003030900da0590a01004014028000b02001c04015032082e03000031100701550240e240413805800c0154240d00c10a00302001e690481501128031000580900c005a13010340b0b00030800c01e46551500d1207800c010340e50756000f103040358100403c518289001c5805007105036410701c1894808404244005080c1585020f03508000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 609793480 1250 609792230 609792257
    0x40308061206040f021003050615090604030501060b04080c030a0c060e0402091002010903081501120f0b090406020405030c1c0f0312110403060b120a060c1e0e01180b0703 75
    0x2071488840c50008000e4641508061800801c01409904100e01800003601c2404119004c0e1040e144180c102601d145101200c0c0c100c4071069500084507558008410312010010440c24410f48002d000203101e010360702c40c148140d8510f001c44496509209038044130104d0001483c00e0000c20840d851400d03d000740601d0880007a019004288640760800d8056005207206541500b1a5164030b000e600d41260f103841c6d40250284100d403000f001d0b07010401c03260954500316400d500450001c0e4600d8400288201c407140010000c0200f0b0714107455068001c40d080c8400c0c035003400403c0003c50100c886045049106801c015542d03091030025000604004c919428140148040050041d5501080000319000d800e5240c160700140000d5442c0343c80d0012000103402d102d03103580c4490b5000701c01400341c1c038416512900035103100ca04102c104a450300f1446081501644054880b4025807038129403c00d1000004140c083c00030740070a80c507060018200003020107a0102c89005816240801001303c0d071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 609794730 1250 609793480 609793489
    0x1b03040c0e1302152508130e1e070e0f0111070b0d061d0412090e0c03090f060c0d0c051b0604050f0a050706080402030c1f090501140304030806 63
    0x31a8081c05803100300504201c8240b0220800040707403032085441c11500c4550b400c1081d02d500441110b6005001c042607100a100c100c01045551130340710306034151078040d408102030001c0384a50b000d032000c002e10005002d0350310380801c01004070a003000c042013006e140c801e0008000341d010394411030242c0e0301e003100d800b41039201d90f250100c05c46600040703460351503940190045946c4681c00c43e140144c68030030041003c2c141a007840c0074044603149041c9954580391100303080070f8060040c410a01801d414009403040154214078400c0c00445180c2d034030782c64603075180c500306020f040206095070001401c1081c815004800d0756205400d892001541c089480410b031014403e40c1180301030040d6060b900640075030005a054499031203241501d4000c0c1d030101b20160307280b400c0b01004000d50041c00c81403000e1445200259406800101254050564040072030700f89260040341c03201c0d5040e032144000000760424601c1004110a183c41c80344084100b100402c1800094802002c00503090081155544e4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 609795980 1250 609794730 609794753
    0xf0201051605150108100603020a060503130b0108030d05060d020d0615080a0602041e1802130509100801051b0d0e12190f090302030613051006030308100803031b0304 73
    0x10b0090865104181e0b0b40b00750140c1c000240710340342c40c81c868452010b0f10702c2c015000308400c6986c00741086c0c13061070030001c05440301c0e00018401d0541c1050342105502254404071024002c082400c065a0b9441c4011811025103d0041c04140602301c550080b0707005895442602505d281c01843c009102c210440c0b4201e80b90145600503401441012200c1044c48040c0e80104119000b10051251505000d90361541c64103184c845d4110305145030b041c07440c0007034541c0c0092215480c0c541650802c81d03180e80c009203041c8000e44808544a503815400e00c01c0300400d11969801550142c10341881c50201005806548500d03070031046030940b1031000303c0850b07074100030542445000b04016611a9a10b400c0100420341c0c0308001d4000a43c900142c8030350760f02400221054030b4000e006030100da91a0305114921480d0a10111a1845a803041410301c61b5544500d00295100ba640e5201e203052001c042c40c440390b0305400200b001e4001b0014081c840035800402c500000c51805070607207d0303445050480400d00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 609797230 1250 609795980 609795983
    0xf0d020f190308130815070311070807210815120703080403030c110405060a0302060306150c0109021206071b052b02010f0c0503072a0c150305040f02010516 69
    0x440e40200030042000f03000180c09441c03e0181d007050000e6842c2803540c1c0d141c2e0103139201c03030065003070f9000319982511a8001c1d54013445c0c0d0446403843c0210542c2c03050100e5000d840e0a4904044070040d617090f100000c003070b58114481c0d51606a4071410a02d403200d9400c20711180403403040c0c03980807050700c0b034501c240300c0c0e80021600310400c0341d00c4507a242030241c44100c1c1a40d04079005410342c00b01c51101e1030203204080c02444007030405c02c0001d09580c280301c203942c8054961a40f10f040b64000041440e4110018504000b40900109a400e00c0d0700c18041401101c2090315129000030003041000d41d4888601c050240109a0825240c100c0d07042142c01e00208080a089960001d810a041d80c03a01e1030389a618030341240d0080049403500760002040300c4000e171005001540030404100024482c0402450300124885101d096002c2c0b1103030714031030500b0282e0860f15500203403000c0080d01541d1080308000798103810305120601e015a90340d40e64011001009040c0540810543c07c1c41da0f052031140b0029 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 609798480 1250 609797230 609797269
    0x603071202130204030501230907050d2a0f0b09060d05040309030b0c03070f0503090d0e13020706050402090c13051011060f1503121e0c0a0308010e01050f0d020f 71
    0xa90301c5c0d0500038080d050080311002403550200c19028a252014078052081c250140508501c40c10b04080006040c4402026144185060034032042c0034400700d00c4050131900c1441158549241100003d20f0128a0388000038407001070040f6a91f40e21044100c03048100c00b504000b03440d035035915040d40c00c07043c5500007030b180082c10001c01c0700c0340c42d0302c8000b5409075030a501e0303107001541001001c4a081c07008645580d0150042d03a44c0c1e14041b8041c5041d007001e6000206403804940c014002d903000ca030000300050300c546403240103220650920031040d81c0c128040c030100500d400c0801c4001002c0040a12401d4050034981c0740055406220340e405071200c120504c1598010309040205141840d000d8806036150840322510280314580090030744010444026014188084948110004001403160700c0b1000302c100300c100201c040c14004450103e120380c0364030307078194140405000b41441c1600603d00441c904a280b105642c1c480c604a0700d001e80c1102c103051074103114404506004c0700c094010a24 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 609799730 1250 609798480 609798487
    0x2001140c13080316060513030f0c110d0818040204120807050c120a0308012403150b030c0a110a0c090c03060906090b091f0501050304050120030108011406030712021302 74
    0x750510342e411100b258010174003840252207410042000782c2030507500801142001094010440c0100046103d580c010307200e80b43c1000c04100030038180c48054600312070034400000d6124140e00e104002e4201218190b034114142801d100151380c020504100240065074041030b640100903007040403821000c809411031082181900c0c5c819600d42026008401140b00c220010500c3c041601905010460f034000c201d000c0b04404d0003c2e0000d009080182c0c5403203d052101041d0300950100441c000c108020680350f40720081c20004281e000c90b2040c01c03006820500e410000300b450075641d0b109481ca214000981121003920075002000c8503400810b00d80c3c10200005055406a4003090010b001541e8824550350340d507068900d510300800349041c2c0d0070181d890a0000d54810301c060b6600c544204000103501c0400f200401035400c0120980b10283c01c00001405075540038069a007031420309a54800040c203000d800640c80307001074040d140d01c8520010100c03080d59560b000e2050381d900001e104554 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 609800980 1250 609799730 609799747
    0x4050c060d0212070c020f1e120d02072405030a02090a090501050f0d08070b040f0632090c190f09060306150303020d050d0b030d2001140c130803 64
    0x1940112409850303080103180040c030501c2c041c4103c5c85d9881e034000d20011442007060104101031502c882403a010b50ba0031044510030362a502001c840d5462950003c002550308400028500040340c1c008010b043e100386200c42103054946002040140181801070b184d40d01c100954009004440819a0000c4d4240d000a06003000b940b1180c180e8000350b800ca0f041540003018404240900715004100003001c22121020502c1030781e905410038070480409112142c0c5e92114010348000e08a2455021840c00880d11017056140713100314456100311002c0c541e072422240071a100c1c004c80500d1801610340f500e0003121000c0c21503644001d04486006c00360703001c0d100c54000c40101813502045031100e280c481410102500440c00030100e80c1d040d0300619551103540c6003103070280c100f8480303009000d884600d03030552a41c051100d003890704125552058800f0003150f00e1200c8001d0310078040c9040c0d144c9550845640c02e00c0030260f50012074a00407075600c0e40c0fa02c03244801c41155078050100c83c0004a440c60 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 609802230 1250 609800980 609801007
    0x3020c04021b061f06020a02010c020621090c01030612020108160e0307080304050f0d08040612150e07020c0108060d032102030c030412020606010804021309020a0605071a04021804050c06 82
    0x200001c20b40c4c901d000c0a0340f194010f80e03407981c14280181c081f8112062810062400d8802010b00074002029400740010451820682c66001e030b8004405402c0f03610400c200b0f5906126160081031041400b064469107600080c1c800000030300f1050800c00201c40a008080c06200e440c074a41c00040d04481c1880e070360b0025291240c01c10301a8070b106007190540300030306181c0220500e1140c0d4104188034500b13490b2050039211410740e440c0b0f10052941716840d07582e68920b02c100b02d60050a00d00d0303054000e890000b0009083c11203c00c0f6003814040110180500c5841d000707010ba070f415038141842c8000406150030084030001010b58480140e0000040207151003540000e1030181d4031440071500d002108140c00c1ea10f4080403245540050b5100b00003801501c0c0100d03a0401001c0602030001c2c00e00e00070b0700070401301000746e0000e40200d000040c01800b0801884018400c441d0f0348180003005d42016800030794040c491469040720300d440c05021600340302040c02104c60b041c60040c80c269440c03a9540c42803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 609803480 1250 609802230 609802261
    0xb0c1f0b0301110310180f020f0a080f160e060d06031202100c0509040902060d110301051c050a02060918010f0e090f060718050307030f1e03020c04021b06 68
    0xc034001d509029464520705a4141500d0041c800a0b503e01d510500f4113059900459a80501c0300c000e586031624410081410720003043d501c0c024100569481c004100e015202020251000300304491080800c620740c0510b90060400c0a41840c0030300840a6280c006182070023a050b42d403c0c5545012000400c0042031100d040f02035215800b541c0859011802541c210b80340070088401003402002014100c0c51b01e80c2c442448940700600440c2030205511400e01124040d0f41410141540040140710a2418200e07265210256a02c1300544207000e50382c0c2c54541e00c064000a01484000c11000354990794404000c1e0022104420b81b80c0540e950024502d1686280c812040c8044080011403e000008074090b5030541c1440b0081c03081d52602c8000b180c201c064030b840741103515850203000c02e440d81c00f80142c1004602940f00742e40b0f012258100b004041a2180803540b982e4466005000000d40110310400311400403200107894010702c5004900505144a15040b075000e1003040086858501100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 609804730 1250 609803480 609803501
    0x90115050d0b04030309170c06070207120515130b07051207030203090d081f0e0a0c0c03020d1809090b04051c090302060c0c10020d030c02030901090b0c1f 68
    0x45a2290340e400c14007610400441c00075045606210004011030f000350070944c40c041c03003034100004000385038034a10a03d82103d4000da015400840901205a90410019020300308802000c204a042a61081d03903c0c0751003a8015003007854100041d580c840c0c4e030550001d2058102d002c00e104e500e000200142030303900502d00403c0c2e01d2010400304441510074800c0e203100c2c05c800c2e4010b0004810743d4000365100e030b0000f854400c0c4000c001c2810040e41c107001c1583d9005010440b04910701c1e00700702c20003000761919590344504002c607481c040b202003503000603082c6801002d4240701ea0018640f08064400c400d4640041d0515818010799000300100c08240a128501850545010007401c610105900280c440b0700c0c0c0002d444000203001520b8031800400030300b07424104175007000394040041001d070b141c4081c0045c050303000025005986070b05801007064595140c07006d503151000300c400180513241c09015241c0202d40c04039107912611810446da858a030044c1100a140d00c60030780c4a0409044011817 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 609805980 1250 609804730 609804761
    0x24030516060305010e0a2408010b0102061b030105010f020f0d05070b060301050c030a240b0306010212031006050f12040c08120f03040f02150f1305060c0c010f02070e0901 75
    0x100054024800d118542c140c640024450141b61551480000504401103c50010305900c04110840d860703445c004000070a0020004039401100b20006820050010300380c0d14448a113902d0100007540000860381516030900f001d04001d22200c5d0301301d1802e219042c001c0e405c0c0c824421902c1e011134201000c0d28406100d07800b256155503420040c182600c03c140c4141013109420710100c0e440c4a4660054002c401c659080075020344002e1160b1415504940d001c0c0165410000034828156070500030b00c4180241010107c1c40e508081c800755030304020301e2081400700200416110f146210381d03001c46070140c0410700441c0e0a4142030a1924850a003886220218850f00e04c00704507141000c0262074000c0d88400e803a5066036120385a444000081500c2240d0141d489280541c401083c00064000c1040824416031079005001d80e04d02c5c0c0244540180344103140c14800712250070800194421082030a10b800812a10782241c00d915100a582011310120711510420100600540c46244840c0c140a07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 609807230 1250 609805980 609806023
    0x3090c08030c210703020d14281e080103020f0604090e0105070f0c17092e1b120c050c0418050606040c090311180703052e09240305 58
    0x80403e501403065a4000780941c200d8140c81090074081d46603608201e220180040c44c1881c9014400c2c01c50442e41d00200b003132464241d0511500b580114880c01500c0c809103500d0700310703082100103002c44505110003486002a554a007105880c3e090585009040c45181400350701800d13114640644400c84002000403081d8555072505403141014900b119000071110552240c00e40c9001c001b607001060440d00b01d9060840340c004008600d8441e25104065800a5020070004600400d610020700d003220480132044080000704030328047e1000f00032a40d00301415500024a0201e04281028007142d41c01031610b80c48500030400101e40c03001040c8941c0544289507118010807003142c11401c11500001c800388000c3c00001c002003a25002060024550310300381c0281044009100c0d401c403015070000781c0f10400d1200c039444201c6000095010b580003141285144440145900118401c0800d100e4a40207000102882030b0044c941000200c00201c00040d1641801c1e90340302d6580f500400d5110124 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 609808480 1250 609807230 609807283
    0x50f06090a110f13030b0702161d070f170915010915060f020a020307031a060f0319020a05030f01050906130807061a0a030605100503010b0f0103090c08030c 69
    0x18842c0040301000c00c0c211504081ca1511200c02642081100c14800488083c0c0880403c8a0080300c40c410407956001b41a030300d8850b1b111116452103540f09074010340071100c240146a060b901425030100b5180741a101c0d5901042d0304030b9003414180003c7e80030038012014030a02503004580c00740c03050401110b080450760780309415002c5500c1004401c070f11440e00744003804154400c00500300343e415944110340c544042c54000a0404040d0b910403a16410f80c1c60074031900b2140c1040d0543d005404807035060b040801d02020130f45030b56405001c522030b080f81030034100865403134500002c05460b01404a036060409940201c5c02454280c411055511949000a4030748034420720040299a02103441c031704240042d17440c40e0180c0030204820a40d40c011040d00324030303070701c5441280008500038030020646062801d219130f400190760708550700070b03418000c156980c1d0b2500d900f0060481028a40040d148215060680c10740040e41c001413850b000005402c02401e80001d011895588074050116600303490 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 609809730 1250 609808480 609808501
    0x15020307110708150709152d09030b28020a021c02032a030a1d06070f15090203030309010b18010e1816030f1101090e0a020c0c04050f0609 61
    0xd511400d0415404041d00004c030710007910b0803981020050801004440c0c9440095100c2d010791034100001070b650a8500401014408202106115440f10000883e031410001001800c65000140c104190f98001c1880c00115400c0c000c6d24004444840c5140310002200350040d5000e610548010301c2100e04104195035401190300c00d80c42c45400540c42d000c00340795040503200030124900c2ca200d602c40c00180380800180014071a10707800b035803a00c06002600010040c0e50140c43e440314020030062102c400000c14400c104100d60303030003103444060305c02103110840c0a40200d0200035014080402400f101d4801500000b01c40e26003140d40304141010807035041c00c1d2090034850520004492004614a220401d841a141d83d256605589500ca11000b5659132108241c0c022108107a80810780c00520508104e01805e00e4000d00c1c200b003500e40b400d004001c2c00200600f072143e04a81c00a104244813804100e403031900c0c04080c0c4103010070301e0001117580310142c0c121101400b982c200390000d02d81404 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 609810980 1250 609809730 609809743
    0xc080a0b0f0d0f0521130e13031d100c0605160c1b050a0620071505180a0b07050d0e09011a07020a140a0614071e1502030711 55
    0x40180c4a003103025610f84900300b800e031950302d0903943c43c00340d0528110310103480384030342400020207091aa61104410044140d618440d07001002c40c42c10b50080c020038450010000b010144c141c034140d80d40d40000110303c1900100e2089a0342e00c024180c4403080603682100c41c05551030301840040015a5401912001c1030f41e8400c40c440000b0b5030103800d40001510ba2400794521621201036507800e60702d03900444c1d64121135402840200b410200d05500712088007840b105680420000ba08141d841c0c048140303050701c2000e1050003071010104500240901c0d0003940510007070000e100e290350b15911300e071048282d400080240c0b40c40c082e180400f000a40115441c1c60025000750010045a103400c2012584072000031182940040c10424100580e80380100c1c0b030058413410f007171007103d08900f0b004c01804551a51180041c4a551581c0c02c100402c544250761040b500240c81c03076215400b1040003038403980304030f0005040c40e02c01d4503142c03000c060700d0b0701840c400d040540b9401c480240310b0301039656804 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 609812230 1250 609810980 609811009
    0x80d080405210915030a0c020a08091011010204060903030806031b0909031204060c030c1404030318050d0507060905150d0b0f0d0609030e101205070908010c080a0b 72
    0x20311280008100b840c00c10020b02000100401807824882e4560029070002c0c510810040300c54000b1007032010200c00ca120303081c1e425500780010544c43c401d0380d40d9100140919082d40d442501d245050308140c90182c4c00c3d1000d003801c00c00c0210b540382d446002c0503062451500068001a20103030000780541400226100d031040c020118240c0d400c252004c12050301e42c01000c1a0355030009100281c15805c4a0560340d00588c898040865181e4009000808441002940e0070030003104558225680f80c02d1811101940d82604c0e243d480000424240018202d140e0700041d00b1025040f8078005103d40071035000d081d12141d590b140c2c940e560700e604002c5aa00003003135901410f4410003204034041d841c0d60004101440c081c100c0209000410000340d504503501e20103a60441d201c106030010180e102403540060314080b9000071001d40010002003c00684100100c0c680380e072400800c070401d02513079448004181c0c180c0240510503528030700401d02c9500b5200c0f240c885060400200303252034502c3d80700540d00b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 609813480 1250 609812230 609812233
    0x804120504060e0420120f06091608100e01032603010501051c11040f062316030e031014090309030c090a1e050411011d01050a021002040807080d080405 67
    0xf0358241041000825100354803180940304000c541780c15244c040060801403001c40c0d1a101e15107001c4ca04c0440f460001400c0500c07032010b0104028110755204050b0001c4000303403a01d200d01d6682c2124a6200f0711554201c2040481c1e20f0f400003003040b4098000c500c400034515440700c00d01062100d40c4003103000a009180c00300c1c1c01400b100c55140c0e0f1039480091401d10900b00400c20040c0360541c21780940c0160850301c580c10040c1c40500140742c01501079000f000060208401200700351680f202c0a010346d402081e402442d0207280b00500d8861a005141040c00505407800080c4c56a80318005000542c038170150001403400050704000c0c04026541010800780c058042c0440c2c11040102600e401803003082c4096481150006a400110103c9459126140001098145410300390190202c503a00c8074108500c01d8000c401d2340090032152204210207090003501c03010b902d5002c0e420442d000401107050b61021800117651400040c40f0001c8510343d1003950204000e1000455545070700312005407d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 609814730 1250 609813480 609813497
    0x3041d190e0d052b020c19021c022404080123010308220e0a06090b0d0209060d1a1e1006080c090910031103030717090303090a06080412050406 63
    0x603580200f0040c00300c0d641c042e0340c010b1050b0001545807a1070804e060400b035802d0f40031070790041303040d0308000549242407110081044460268009080458244a50300c05204200110b40440d26100308072a80a50b00306a10540a15441d00001c19504288941051907003046401e0003280c055074a1481d200203080072011140c1e085d0741340d80c852640301d4070310304030004075080b900743d00c1c0081c811101c40906844212800182804078002d400d070380030780e000400185d150000340241e50382c1d403116503081e556041c1c50b607030720350340d42c00300001c400e20500c03e0b02500c0c1d410b4039044050103c1c64040340741d110b005109101c0d03c65180414906030040381c204e540040103914080b060121900034800706a101d03c240c2c014a00d030020880120f43e42c2202038800f13600350150f00d4001c0c002c01c000ca41011180328000d0f0002c505003042c5440741480b0049014881d00094070015414605032030038012594030034009003000d440301341d40d04401451080111001d80304003c2021065424611443c11a0103e50403035888020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 609815980 1250 609814730 609814753
    0x60f050f210a051014011d060a09060f0f140913080f0c010e0d03020a050a08060a031704030519020a0303051c0509030711030f06040b0903041d190e 65
    0x480950038020890880c5007400ea4a58214080041c921081c0c49180941041d4914000600c141d40f0079018010610f08402d00501001c1d588a064400c10300000103110703140e880c1e03074000c241040d003150050340011303017000b1010a4404c40f601011044619001040c1985651001007410540e03010382019402100f4a0115035400f8008881c03014442c095a4003030f20b095074112181400e80d111045214a0344d450b0007041458070300c1400000444030782410198036021201e035008002d0701c1040803a00900401d400401da0b242c681059802c061544410402c5132a0364401800e621a089131200712107510520050800a5102c20701a44403207074050600c00b405429036805441c2c41e00440c12080d00c99a0140c542c0340c405d90b0600031540619001d9001e1680c440942c10000402824400c0c40c50003a031000350070102c142c1c80000da03c0d1b44590810000fa0440c1c03525484181148115442061191080d05c00c0340c024024a45100380200b44464101044002003101c5806841801c4401d05c0036400c074128000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 609817230 1250 609815980 609815989
    0x9040803130618030f1803021f12090309030c12020604030b040f0b070905030c01080c0306092505040e0a0902090f101a0304030f020609070b0a110604030305060301060f050f 76
    0x42a103840340704040b400c200c1690190300380f000606420f9000890843c2c0b003d00090700180c02c181c0c40f2a6010b800f01ea21400c60b0081048a41c151500444210000300b03044130580c0700b030000142507141410207203c4101c090500401314a041d000035614540c4900d0300143d07091162140707001f05507000c2c041078103191a548840c0031800000744260b0b18800740110071800201102e400078418002c079107d40d0312190405091500c0d0032410a80b03141801210350610262844c0b800640b6407040088840354601c0d0f4035407001150902262008480c005050b041c560311290b0004064800d440c1e030760030513010030783d50202d10000750ba04910703000c0d4219480d1800700c4c01502807a054150b100010949014905607155107403428400c50070f103400c1070342c0c80110500081503403102c0040802d280c04e00c01814241010140d40707440b1100d0b40302d040d100840000d042540036018200c1c03180404c0c00341017075400700d1905080140240c0b0040701e005101307501c2c105011036601100c070038401c1a00ca0291113484c45082480c18030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 609818480 1250 609817230 609817261
    0x20c0a18051e090a03031b0801090b0a05030303070503010e0615090907090b2802030405150319050109020903010b10090627080a03020105090601120b27150609040803 73
    0x54106911a02c2d582d0070010010710b2400f80c0015402069043c160b030030020222640320107180c070144d0f1100704640c001c0e9442101c8078151810198006140c0f043c910016802a00c1507001d680c050001004001c00070f50404007860403524611001c018590303919040041070410380006260b111801c2c00362220310308003164895400155400c2000c1c1c81030b01c3d004258495001102e6500d0407041d2500c83c01c060a801640707800b102812030008605003820000080d500b01c0d071010742d241c034040303002c400504202c911124030028480e2a410400455131524814800b0350b02045000c1d02035801c00b821400c41c2c2c141041412003401c030701d603100d2039070f00e040c00780c00c840341007040041190004804241403c0800b040e1059001004040010302200c51907103030207800d68000600704045a081000100411010442a440f940d640700428041a03902d483c1c41c4890151400910002d803e0700e9400c004500a0018a02c0d210a5403140c00c40c4155489404020b0108400c48000780544070500c0400e9000e401d04990 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 609819730 1250 609818480 609818491
    0x209040902120109060605150318190b18060702281b050a0906060f0f0512091609060b16020102121812010216031805030a060606020c0a1805 62
    0x10036030850540002d070304401c1d000000c40c15a50348a4840d401c0101500c00c900087c0360988510410f2207920a012406020080c0f1070701856400d8007400120020510002c41648401c425110091005040c802d107244811105282e02d039180c0356941d180f00f640002c1c0144118040d074002c10028141c68400352000e82c042250301784c040140c168520009400100046608850a140000c907602c3c2004200310400a58810b0400350324000c030070b018440c0c0c460320310b08401087d410071386900075004104840c64824801c000c4425036411043c000b5884000c9198041c0462201100712555100c4101e4000c4a800b0720440c8240642003102c038030402a042d55040700c07140140162040422154105151a88880a81c920324604240b4901e500d20f4035802540c6040381181c001c604101f003010b00300c528914402d401500f4008910540840681d5845111010307280c09030546080d04603a05d4a24058100d90040c0405402410070303130308903420003824500031a1607050303200340c4400c010f4400f40d0040801600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 609820980 1250 609819730 609819739
    0x3010504050a032006010315050610080429070e0108060a0e0609090304030c060507030f030c02060406110d0e01021809070804141009052a210c030d022a01050d0209 72
    0xc001326207034814029903000f14060034140d002100701054000440d200181503a1041c14100040c85405500015a5900c1640196841c00c0004030390b84095a400c0841c0305111030b08144010000b03020b07400041481080420f8032007541d207031944410401c544a60b0b002c0c1540c9480020000384035450312510580d04030362050f09480c074180d01d0b91650810300405400a50118000003460340030164400045118041c0c01d01d030401c503018248200a498410240005d00042e8880c5110314448004c2001c0328540081d8410401101d011f41c0502800f0f900121903d049100a95904054500305460058450308841d0340b03c2419950b81c1d0303100340344008032b02c043d003000f072143c0740854138441100d20606050a003c1ca008102640c081c0b05042d014252440b045c0d03403089101d640403401d54454410031000b08181400a03c60040d00c281450710f4500c16084141d8984140d13603000052a4010034404c00c540c5803501840700d0050426150b51860a2a40010340000c40400029840e001a82d0190121210050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 609822230 1250 609820980 609821027
    0xd03021804091b060311040b1b19020406080114010b0a3507030e10021b07030f120518060306010c0f030f0e040501050f010c0c1208071103010504050a03 67
    0x1012a04940c40b070b032812039004800000f010070075408550750200404042c0703010b014094081d00800c0f1b25000314401c0c1c022098000c581c281c4100890800845440841006c8800840340b60410394140c8108031010b0b80a54944013010031042d106010b0000d07240e20145a0318100d9191808600c0280d200700755010401032110900344003c14074829501c0c0c600b0700703c68158448818484402101c03200902038009140c03038001600800080070a00700d14180c01d8003001611120560300c120221a030712261000c00d80207950340481007007114060030546a004170802000c032480c00000b500c0900c20b0004c043d8168902c3c56080041c0d24280380110384c801410f01d0f181070444081e640b1112503daa0160481c0803800030080001c00c2d80e07110290313881d01541150309000c2d80d45868007290380b0b8141e000241c0d0400450031821000e104403da83c00700141b0b03403240354004040660501242c0c0c0d812860046420960504e84542c01d40703414054140a560090041c02c0302c0c910380da03026190030b0b482c06100e149404101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 609823480 1250 609822230 609822277
    0xa150305030415200c011d0d11040e010e061f290d020316020d0215040b0c04051f0e0d02091306060b0a09140d05060f0c07081809060f030d0302 63
    0x5002a25601c8002004090400005e8005040001b0411740254200103903203106090341d40d0508002c140941004006039030030345103808503004c0c165a00c074204031582413420b50a90f940001600d640f248208102d00000100034036405815130540340728010311280304400b00182030546100c00002c0400e042019850710382c5c400c0e135100c1642c004450810014422407010100d15406204200c8050b03401c1c4040d010b0302e03501d140100440c802c094405000044940d002600300191041100c0c0a000018550105600c02090507219800b85154120014040544080d0241000750095009517030041200520780d403916115040c502d040b820070340c0d6190300c030000002c01910340c00003040f4030910380d070315420001e017019a034094501c000440e1502a0180c29440d8010510104450750040c08003004100c0f10f4403030140c0c002c81c0b4000c044009c2c080820015403240390000c4a15a00c0e8400c805441d414980d550720010021001902904240c05402c2409020b170720354807070b9004000100f0301121015440100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 609824730 1250 609823480 609823517
    0xb010e011d0a230a0f02161e0506190e07210c0f09020705061b032e09020414040e030a05210a0b031c0215060d1403030a150305030415 59
    0x60b4403101c8040000f05001104140740900c06131100d04002c00e601d00380340030504150b00c082c4600090101c551402c803100031284581c50400506400c5002c64400c0d0806441c0f010864009261481c0f0301498100c180990410100d0140203c84050103010440214000700c100018a0a41d00b00c80080c4550000304074101e0310100c1c0030160001c4c940040e1107581510349140382034070103001c1e09170220312036030f0408040e0500000c43e0782c007207010b0218041891a0107044541084403003002d0007180b020242c089050041070380588200e5401d03400103104e40c0b803600117000441d001e142025000360020044100e829004e039008103ea40b9030101080d51070880c0e42298003c644007a500c0300e0b0b1181d00e03909000c0d1a17280402046014640f400010501402c00f201c000c0d55400780000070031030303450816001640d00d546000d08181155000001c025114180d08a180d4403030f841201d200150602e080192a6203070880d4055400ba07035030090007180b926050510000c00c4001c07042050303040010320007802600002d03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 609825980 1250 609824730 609824771
    0x50a0210031b080a060e01080a0602130305030c03130512060a020a170406200a05090d02180a140115050714010209121c0c1a060418030207030b010e011d0a 68
    0x1102e58400d240382c1029581002540c3c586d500180c2c0362004140144180f40001c559055810ba100e100140d87d110000350f442c00c401d003da800900140004a00c44055034404001090840064800a0f003d55120020400580c0d000c1c40703551800d0b0300c81800544508499401021800058104017417048003007065003c0300306c003c6508481c3c0c181c44404030a0304505003c0c00c1c40d01070000038040c5040c1a044240200580580c48000f440b4480e6101c00c1c0c07096407640c0d5050300020700003100b408030500c0c050503200c020700840d80d450258640c4250000800e02c03801d0100c1403090000c0d81e200362034141135031113060300c0d02809842803115550801184607699241058403070300b9100301010300342803031501c0d40d105420300c0c0c085104404d1200e40c03200100091140401e20310300b1180300c04010301c00d8982c140406d0040c0000302d280200301c5840094041410380000c0d403141103070700ca080501140d0383ca032013607030204040c20321500503130176403204080315120154504a54014003001c4000380c0c916021a50240404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 609827230 1250 609825980 609826031
    0x101d0f0d030504090c03060b0f0a14030705030609060108070c0807020f1809010b0f13180b1305010b04090803130807060203010f05040b1009090b0402090307270504050a021003 77
    0x902c00581003040c0b00e882c4c02508108030480c101007040c02d1a100038001148600c8041c81c6019800080344d4032441e000b111000030240041c411180c0f030340340c0818080c2082d4000e507070310780c403d02d0306100043c503075807203298070f41d108110507507440726940c1c40380d500e00d000398001030700c121381c010345038101d2440e507403103100c1c01e4000095400e401a85506241d611103084500101926004c0c1200540510507600c4540e1908540c41400c100001e4581000d01c9500028015070401000485c00ca030500c501180c2d8000080103c0f4010343c0200440c00038601000121a0f89040c000c00c50b040601c0040d0800d9070160001d0521030080c0044d910303081203552140304a9000360000720035800c032482c0c140020b00f40380c46500040841621081003150203054003400b00c604501c280b1149981383d0492107038580301e50b01940c05405014046600441d15171802007240610204140c56402480420301500e01541c0140750103642c20030044c213a030402d644c0038004a118018810014140c54105070161459096800351308030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 609828480 1250 609827230 609827237
    0x5010915051e06060f070303150311010f05040e0402060702030a06050f010e0c0705120906090604090b010f09030809040216120f091a0d0207030c080301060518101d0f0d03 75
    0xa103820394102212030b40e15105911850350000420107035456000440c2c0540c52601001501c810349880c0c214042c002400e030610440d00c3d03d2000000300f0401e825045440c1030b003601c07044803000014404030b1b0b09010b01e01c594100c2c48807040116000d0304140d03000b80600e0340003074280c030100c080300d8440a0944005462200005201200402921214000e1550071081d1120340e40e2601c0410b840300c9958a51541038040b501500056504d0a07a48020071600d2810014017070b03545480e038805054000b000402e0055010130041044490390500c41c014a03c10b0b69480400941849030035001e002c0250050b0341c0142c0680c55510f1003030003042e64411600c2081c4226a1480c4000e104010028111130705540a00110f0314181105001100c0c140240c0b4041e04800c1d10050711004141000c45243e07a40400180ca050000800466032960010080000300d49880444d400140b0060030301a40940c50188200001d4544c07908203c0340e0707101c032403490f06004020100310b4203400030000186011038418089011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 609829730 1250 609828480 609828491
    0x120d09020325060c020f1306120318140d060203090703080711130209060d1104030209090d1b0c03033006030209060409030e090915010e010503010e1b0103020705010915 74
    0x200da00003450710b0081e12007481c002843d108158046800c070041203c0e5148543d00500c00700500e103206030300070001445801c0740004028001c0c14003900020104d400411402404540070900081c500f600318580c0c100a031980d4021052900c4420080d080900554110f0040c03020000115481201400350345000b0003c1081004440701040324640c01190901c024a00604c680303c6076070ba6030402d4030f40c66400240017040061004181a07880d1140d500004c0d40010a10240650210001003640a900d03654030741c0710001c0707610088d036040402d40560007404030101c240e090000034441c611107082540c80c0c4107181c2c42c10100480c0c00f0341c1000d5032242e400f0b544ea41c0300c1c030420552600d640c880360071120958040008007900d842c0100007860a5000d58020f42e580d101080c403500c0c080007011411212454540b0695844001c00c2c81c0c200020700c5030912035800e0440096940d1004241484007203180c0501c40398500f119001034000e900b126a090b00e00d0b5582e140940049207400c84a40c844c0040c0c00c200064 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 609830980 1250 609829730 609829783
    0xa030e0f0d03050904020c070503030c0705010f02060603061501030b04060b0a0f110601150507050d031d030a02061b0408030f0301050405180a03210e0a02040518120d090203 76
    0x380904800414030071001e0401c0e09001c2600181151030202e000d80c1d015070f9500000100c18508492941302c140c162100203041201c041021610710241c48090340c1d160f05200592000300c0e81e030b040072b88040c0c2e419000b04000c103c00c650104c0c0d400c2c1c1203541c18140070a4851103e03000a04842c065405a20752040008100d02c0a951184049031050710b94107046616900100950340d030b40105000d00880800f10b404160300c11805882a00e143c0e95100049908000c40840000c01600400900314180e540030f01080440070804000d441c0c2a08031035004154668680f4517810803103060404003541d0701400c01c130100d041c02f01400100005d8000c18840c41c0d80354034000c140402c9400050020000f01a40748041e1a0400d001c50003503034168140c541805481900100c2c1075106003450014100240713003410703103102c403180400c6040b221402103500b00001e65a11140a40480f08003503000c101e03402442c01c90140f00540f01c041c012150005c2d600244600403603003c60310f070030124500202090f160004094 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 609832230 1250 609830980 609830989
    0xb0f0705010c021b010509040b06160b010b041409090a020613082107020118092f0a1b081b060906150f01080a060f0602070f2306031315021201090606080402120f0a030e 74
    0x6006000018541d4174082c5050430300a241803004241d0381c450051003000c02c046803010880d4428043d0002c000740c1c5e58000549507401003003a103200301c00141c0500d614084612003404000303058817a03070703c1c403191505990347d00445022041104422078007031400f00100c0d046441d4030822555550100180004c07000b04040c0301554035903500804540603003007050107815030380310000f003520140050115100180c9494541c61031b00030344002d1076116050305100203000d540055094001d000304000d45100c1d440781e0f106a11031a055440103500f06908100300300c51540708560321a4032015108000031a07940f01c6610b42002e400950141005038480c4070309010a00d60800003000074110b11811103c0003080982d14032174401204801e0344500d2012001501c1c604040010803403072680800c54560307103423030122840000e403c51407503082241b85980022441007942d201d00001c0d50542d480e2500c0f2942c3d02e6080000024004403001018050b02030440003014080000c840001d00c01e48454038445822410311 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 609833480 1250 609832230 609832253
    0x1009030629030607051b030712031e060302060406200307050a0308010f0315050402121c0908060105090a0903020f0601080d11150a0f060b0f0705010c021b010509040b0616 75
    0xc602c40d030000c0c002d00140a0300501255040001007941e10011800000103a00714018007002401404a074a0301c000041c3d40b692114200328003048680c5a07030803410040300111190ba0200030340026041009001c654050303038024103502100d065441e4449041075805044da04504070458266002d0a01e8200300341e0032809036805424a5100b9100301440c0d40c407a458000b00d0041281e000d503076030701c01140a549400440c5c100c8603401c40c013194507200b4100301800f400b803420801d25001448111003c03134500008102d841c1241c80c0100345485a460b113061510080c10103850840540c4038441001c0c0710540e06102c1c007402002c6100140415000303418000c2c0004d000c55076181303110340204026041e01324807403810326002402c5140000b0003a45c07081601005040c02d400000f801745003c9005062030314000000d100c041c1c0b2030300003800084c0981d101680d591070f444182c400c1114000b02955802e52140010b4510440002d101241480d204408540d10358055031820001000c1c420701e6209000e4402001b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 609834730 1250 609833480 609833561
    0x18010207120c030b0408120f06100504080a060b121c020118120c03020106080f100e24040809100f0201060e01180203090114010807030605010f0b0910090306 69
    0x2980750009080c0e40e035142d444102d0000031309109109001c04e0030703c480e54041d614010106049900641041706250102007400c80c0d406115445c2c04101c209114410000d0b0b80c02c80e000d0b400100708520351682c80704040c000d031503040358002088090f0305e4404031003000b550384900242f001c3c1410106d98035100078203683c05200403480d19140300e130b2500c0c0001d002200503004904a0300d09074120f864603140807405000c80364005a400d11920440c0002d046001c90741c1440d41b42000d908000c5003903400041c58070b07400c400d1a01071941d014001c3b0900c6400913801c101d80d0041c4602e100619040d9180c000510880092008000180c54014000b000c1502403003070502400306681038409540c903042c81d0030350794569a01c000e050039030040003148086100f508100305019007425044019a103d40c1056640c00447c80180c5040703042100001e441c80ba10bd8418043d01c43d940403051804107030000744040d64280b904072800b04801101c00101041e0280301d030b5030800d0480c3c0b24040081c89074500788401d0360f010010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 609835980 1250 609834730 609834749
    0x9050f010f260115060e030d0e0603041401020d0603031107050a0911070501091118070804030c03120921080f0402121501080a06050109021611060f18010207 69
    0x5000e07100351004114215225600340000954449a9551114100d45240152903082008214619a010502e4000d403245a500c0003562400001050703500c610541c1002d000c9096449600c03654107001c4001c6a00c50302442500f1421004010040d00326401080502031090b41e81109204040d400220410400d01d2440100030850400c000941c055050b4480c800040c0d0307032100160380340c821030f6069806607030f003240c0204a446003a0411119144801c49840e04c01c99190f00d40080070901041403901481e00c03581d56151995070760ba015202d01202090035801e1100c425141b1050510714000c0c0c3c205144a10360980b4880b0040040050081525150300140109a002c00c141203c0480c1d0040d030140e012249100c0e01c80d2503020b41810840600c0785503686440c000d0002c141c04000198085626100300001c111070ba80c0c9101c880d049004d00503035415500c040365281408580b24216171842c0c0b000041c540d0b40384c07510803404440d1035400640e44028004089608205940e014081ca0004001c03629 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 609837230 1250 609835980 609836011
    0xa120b0117061305010308070b09030304050601060e04091e1101030b010806090a1d03091e030c091015021509071d0a020f0a02010912050a050f090f030a0c0905 70
    0x190510a040c101407502440386000034001d503640300c20081d9034a480340c008009650312400c0030344281c5d1000c802661188103910100704c85c0040001224451a0084064a07441c0d007860f10032502c040ca1500119481f5407a02c2d10a030104008110000c0300d18280d807c151025117007071810101000091590a05047c5000d120103c00c0c0d0300b08040c1d80e440002102c030f00710540d9a00000e5002440e9000d0050000f4400034030703220000341d00200419140d10110390600740c0e64039804800d03003074030f4200702055091340200d18640c5141c00c1c40e000070340d0030001c001e0060342421340352802036003490000d0b42c1100050748542001019800310313881c2e290b04202c0c81000341070528100b00d8207500000440b14002001c00c0407074005901004a5410360300f040c441450036541d10159400024043c10b03400d2026203401c0509100711084500604c101c55240c100c0d030320340c58103140d00003031124041c6c0c00c01000d641d000602445008041d540030b2152801c0742d442414410304480c18804043d044803002000c10f050742d0f5552 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 609838480 1250 609837230 609837251
    0x20601150f051c050405030403110f0a0501050a090503060705040e0a05060109030201050a1106070e031905120c01090c031a340c0b010b0c0d0518090702070e0103080a12 74
    0x14000180e940850525a5950103600043c0d01c00d101c4540c200d0444030b24107003d00040140c0070005008481c0580c040c0040d170314012081241980000032010f80c040c0320311400b00050f5010b40003420614141e82007001c099540c400200e410110110b41d0200000c5000a052250f034038203451541e00b1078040e0f40104031a242c51000a4034544140c04064144a00070888280340e40c4038034240030b180d819403800c0e180142042c1d9070113480300001100d01846800b89000d54440315011440b104481078000c0010000010040e001092076881050b4140c0c05540300c144044c0452000d84000c40158458017040218160303400c2c0f030001c100d0018000c0c4078910340300880401c0c4c4104090450310300a0b84006c0300040c0402041c41503900c40c1410400609a41b80c0344000240010401d01403c002e01803003017030740c64810144800f10344a2040702054100c00c9803500c454661810145161907100030940101e03401e4588410305200c101c10240d000b1641010002a00c0304416440807081280b402da1820a00225098 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 609839730 1250 609838480 609838487
    0x2090306011413060608041403031e06060d090f06060e0906160e030f0703110f09130204060b0708070203070609260c0a17011d101e0216020102060115 66
    0x610a00b030b81c524200c144402155258140b82c0303100f110b50031081100c0c99545d02c0142c00c90b6000c8070141c611501c501c180410f5440b007c8122072041c0c2c07507c008416462416004040d619001500194000c0403d024400052840b48150362415001c1da00603070001202e80307000d0081e5403058000c14010030f42c1318244031548800290141d0000c03d981d588143c03811055a0496402005000e800d40c544034030f41141680400200700c5800743c86c0100900e0300400b50740c1051111302c141440e0b2558101c100100003c00040c28000105855480100b0205515641d4030b0798030b000e900007403015200c1010000e0b042c4210300e000c002200050603603060414070b052030842e041d00f42c0c000b41c072a110340750403541d40c0809400e007080c011001d51840040c40b003c540c1d92504c3c8068071402014244000039071030300d5540d40080661440c44004402c01d20010580c11020441c50703c05800702042c4820800d4481d0382d0895940c407680007070320300010010442070042d031050000a20300101a03016800d1100d10400010305c00d0fa2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 609840980 1250 609839730 609839743
    0x1009150e030406080405030d06030b0402010f050306030309040e01090b0c0d060603060338190b031903141e190c110d140106170f010e102d05070f03020903 68
    0x101818400c400717995034101142503108010355004050b1409002108010325020118041e60003aa01c0d000d5030101d0302c07000d68403403009980069060788140080440f524183c0c10641096030800c0c00410400f140b6031f2000c8001c1801e40d904460510046484080d0401900c00c0074003c00d0103150600c1003614540f038045408045090011000030f80e0340401c1c03e02601c1075184444100c664240c1002c91a0202140c03a0080c6202203032041d141c10304003a0201454001a4030045000c42c1c81c541d551f003541035a0544424220286101d4500382c180b140034291180e0400c0740707800c41030381c01c0c00710394a0f41c031072204d4280301c82814207000c1031040e110485008242110225401850700f03988070b031071480c03003400d04600e4540086c00c042555030a0100101d14480c1c40c1d84161484e00e60b9004440076200c401304154281c0303c4240307c88007141e21a03121190744441e41e801607010101060380706100d201d070340d0201c2070101c8030341058440b034240c0b607070b084c03018669000c0402c01080805140460504003800c0000c1d45508 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 609842230 1250 609840980 609840989
    0x402010507080906093a020303030703021c1a0117070903020913170c120a02060703110d140702240f1e070c122105040606081009150e0304 61
    0xe00810f0f0380a40c1d8548a048542030340c401003512645c44c0d03030203010003600700c452a04400d40e12103869025641001e409102d20380107900502450955480c403404030002d41014405414640c002c50b2002803107080d91103441c2c03204200349409044843e1400024021607051402c00c00c8034480c0008100d207507917210100c0419254102d48040300b40d102d100340700d07034420072100000d4110b540f031641000304443d04030004d00302c4a9031401030720104000030141d10018040c1b80842e80158100c41700003049248039074405040d0b044992491814030070b902116008036942c003440410b00315103000030f2100340c0713070100300300803034410300d800360090b0751103100c1020b401908042e0140407400c0d003620109800b0030f4420304a000003000c03aa02c98240303107031100c4020560f480c0301c40300b0b8955111080c840c0c44054480e001c0d91044041040007218014429a1204024000240191083c1d96244804651148140f0200054074421440403d28410a0030802900722003940010640c0b0301d0b11171380281800001c4151070403038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 609843480 1250 609842230 609842243
    0x1113060c121407140f1506030106080d1704030912030c03230702150d0e06070806190e07021608010e06010b070209060618041401030506100608180307122001050402010507 75
    0x100c282c1070301a031510080217102d03d100c1c0a0899059078246114010034480c80003100244019079440c00f0303158859805000c41b00003c0d100b1902c25000e56503403088075030098440d01d880d90000d9640c08080c0100a2201803c4000a44a40682007410b6203c20440551141c02e80f02201c1141240c00001c0f00384913400e0002e0107020307807200701c00c11031640d41d00f0b681101141201c14070012a04c8100f481d180d02c4101c880d9070200d5014000b18220b410011003511212203078000085030f041c102408280d031540c0c0289503c046115a581c1c150808183d005006c009090729000454042e030908121402e041d0141c20a078000c880c240141009651a651002e0704450709840d201d5840307292032034102e41d043c070b400340341a049400c0a81c001c80005450442d141228014002c0d60b2460702c0d00c0342d00410641c968807955000a00500100b0264240188906c01c55100c500c2101d1030410660303904038030720303101d210100080f4146040054ed400010b1001c940c0e6580e40d100200300c0c9242aa00203441c50040c500f020341203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 609844730 1250 609843480 609843503
    0x1406040903051e0901120923100c0831060e030d061805070824010e04050f091524010504030f060606030b030109151113060c121407 58
    0x1414001d41c02c90b01d03c0e14510070005849550103000751002c0d03000030402030002c0c85145031800034020328450140c49990002245c00400b05042d40f40114039401000049180250700c0350b50b804003800e103c0c0004040643d00d44c078400386032500040c885a841c00d10300750702202c031800c1c40c00c50bc210004410b00303036298009000201c221104400070b15500a504070003c8040c0791410210f954010003c94003425103800c0418021680d4900c030880d11503900366901c02c026010702c0c003051000e29000e00082004201850800441031620000078250742d025900700c100c413220308c028414020700a01070030410354403c0d48031034141d0901980f10312001505001004200e810026007000907886101100d000316008481d000c500002c034100f16000f0b01c1d1b1440340d0740129141822004040c02e042c0201c0340215080240e49280640c201060ba000d48030040020404800800c1001c0070403101e17861080103403403a40c2d20800a14514608409a04204c103c0d0a013407250143c0d1000c0c810b00a60100c1d03910f940d0040304000e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 609845980 1250 609844730 609844733
    0x1090b0a15030b071101050a1803030504111504080d11031b031b1b0102010b060d0504110603010609031502160206070c0b030711070b0307050a1b02030303041110020114060409 77
    0x79000035800003020407442c281400b8803075900140c4007128001d4a80200300603140d0a600c40d084035001880700344005007122101c1c000c41d00030b40c00242d10074040c0400c0c1400d0b214003c00500c80e003031101041d036001500410244104101082208003140640c1040180881400c184a07901d001d12004c1c3d8648003896880f80c083d0034000e2041c0c1c4c900c001c4451314903032007403e40700020b502c0d071541c48040300742244802c01c1155598070500410454400c064400b070300c1d004244e4a494041e04000340309a0303945410940340c0038a0740b00e0700c1c003c40c000d001350b0380da42c40140d007546884c40340c1781c9280c50000c0c542401404880b010310070451100d108141d04030b501540d287c185140c2a280c0721600c0d070049554801c0401000040c641184003410002c8540040d40c41440d2201d5150401d4002642c020001074014001412614010301041c0c6d06150b03400980e00015440794000ba00d140e01c115011038030420006515003550800340c030760035560f00e0540000d000480d5084641e83c0c0c1494000d28541c4501c2d22400c4140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 609847230 1250 609845980 609846011
    0x3031d09281a060a1103031003030201050601090e070e0301090f0c080d050903030d1a0409120e0303040f09020c15070513050303070b070e060c010612030207080601060903060b12030a08160201090b0a 87
    0x55034086544246c1c1c0e10307841e005104107030307041e0144000e80141d42171100090080d882500c10300305417240d202c00c13040701e512107800403110190030360482070b0150358542c6000003041000007150b0001d031040b140650400c1c2008221428400c8008024050180901c40890259000b00070707607200b181e0754900050f00d9101d20942030305c12000924000d4100c0c1c60079107074406002c421041102a010142c40d0f48444d56450828980c3c2e9200f18441d0030b4040e151070700305005640c0c6540092580440c810200c80d034103107166020448441003a1504408100300050084400c20039071012030050900320f01442c1020074641b120424030100500e00401c221015a10402070760358041a030380011050300003000f82684a00059600070400f0f04107401521800000080c0c0c2c89001480c0c60603074071250b03030702d11415155a40704800b4207681e40c0b0f80c66000c130071000b000001200400180c168826180d07103803212810900c41c0c0510100c2202009001c59060264040114458066054200c8060f0100007010a070400d04071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 609848480 1250 609847230 609847247
    0x708031c091a040308070212030402090606070b070f0905010906021f061d190207050d0f03020721030b040203011a0f0409060e090715080103031d09281a060a 69
    0x20b20456000c07140010044048040e948114800d8845505a031140a000d80e52105507007040314141504000190040c200f21140c1a00010084e03c05030409980b581c5642401c00c04851400c0003a00999550704050307400b500d4500244001c0c20700950840c14140000c2d1500c0c03401c1e45d4186440d1424281c4020032040b640010003c104807550748000c0c0110340d003c0c805005090320b0380d40a81747c2c143c40c0741c44070000314402c50791804d611400400804008010507556080c00f0b507141030500d942402a00b000c203a030358040040c2d003000c062051006816400c0081c080b0b4030351004150040344140014012a6030b541002c90384408202d03032283d00d81084015034009481346070054440c2c541450400213002c41c9525010703010b0368841080d15040c5454841d41c000c130840d15084880064038800041010034041c0c0d440c1c020240052030100107000140300460080802a80d41c200c10710040428130201a031031054140078602a643e051104103129440d44031800d80840c00a4811840020040403040c05880030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 609849730 1250 609848480 609848483
    0x10080102040f06080c25030216090b0102060708071202072f0a120308060405130c060509030708060105060403060b18010306050a06050906010c060f0603141606020708031c09 76
    0x290340d21600c0303000e9403425603402e21824020401301c2021611407803e400a44d001d04615141c0142e042184a5000c010301c0b862800a6081d80100189031160321012102c03031009e030003151800308000d4240c030002480c01200405440c2000307142424002034641c4406031b02505e844045015841f403c0c5810007000e4034031003040c40390355500200c02115094000401000d403040085420901c900e580d001c805401c102e0310b01c2d00800046009000039083d01d00f0340e01403600407041031000309114065941d042c0d03005009800420101e138000c03a00d40d605203010401400034001c000045c00440d49000045a05070007980002000b4a860780c1c01500b187d02c850b0010350b49040003021440a5595900700440204001d4582ea604503040c081c0106a030b0130820803840c020541039440c11100078a41d160b0304010000302c60714040464543c0c60001c0401d596400c2414030f14000809030101203c94041c0c0e1030700c1000740d030100040d9008548108002500481900d00402407150040c2d120080c1034580b000038440007a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 609850980 1250 609849730 609849733
    0x90702030c0a12081b0304081b0a03020106081c02152509051003022502030304050303070305120906040305040314010b10050a03050105061813020705010c020a0b010f030210081008 79
    0x400b0300340000301c584421054090b407901d1403903440700644c0000c80c1844284e03031150400c08101041c0040e0b40f00c030040003c0302540c0103c000030041c5200c81030901d03110184c242c0042c1c0d182e910502c042035091180c01260200e8521400c5014208040a5200c0c0707404804558400303900800030700e04500d003401c04242c805081c600d2604114a1000260800000e406003030301690081144121642c000c2c4220b80ca20b80e021102d40038240200807040c108504070703100498050100703220000301600d042014105151203900c40c00e41340c802c035030b51600d940307103000304010500d500500c10300003c079400108442c1540e801c5268141443c01c0c00034114090a48040c0722500079020080607801c050340031002e45408142d50f41c0502ca182d1741c0f1001c01c080c50064138010311040a40b004d500605107003201a540c40700480e0b4030701501700420380d2215804c403102c40195501581040c01c80000304070714641c02c1400350001d40700700c02d10301c5d080d070b00454580620a540b5806000070107000c60f160b200c01261180043c2002070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 609852230 1250 609850980 609850993
    0xa0308090a0206220e07050f0a120f02181c0b0c160b061306060e010507030201090b0f01171b01030207020409170406030605041a011b1703070e01030902010e090702030c 74
    0x1da1103c690790034444e12605881401280141500307413218060381e85581c40d41e04000181180030041c0d48022039003410321a4400482540003c02c5c0545004074803c4500140ca820481c4180c5803a40c41403014a4418101c00e03000e1200048424481c1802c0c50300002c0641183c6d8031040c10000602c5009000c21070607054071920382c01c1000303040d02c1700e01c29413040d103003150a20104540c18042c1c0381c56020340c9011a603032815040d100d5200b034024010b2a8048d2001151640180c2c07203200010f079054480e06031510b85000140a000c40702540a062800d07070b48014038090b80e0300700004003207490f0301102c1d504140d00041c0e0042556110f402551805800041c0029054003812081000e0341c064800c10000c00d0504000180910341403159408542010150740414003050004651311844407510343d1041500d07955060110b9804052510038488003610340c4d035a402c1001c1c000e04202d00b80c0000c81d040509092140700140d07441111003004072030941d4541c0c1e41c0d80f0382e04002e80c1540128200e401072482100e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 609853480 1250 609852230 609852247
    0x20304140a060b1e09160210141608090d080c07060c0e12070807030204050925050a0909020d171e300103110607020402040909051005090a0308090a0206 67
    0x140d00100420760211013900388a00280c0c1c034407514a02070000917510180d0300b0000b80d242200c0e80b4070b071081c61000707105542418a41d0302191040303407480075220203002400780402010641d8a51021003d0040b03040185007850300c04a0b607a541c004d50740070750042110410100e0f004a20802c140c1e0589980810300b07001e180b000340801041c150b81445284d120b12105210582c18400c0030a03050180e4682c880901901c034110f40903c4040c10000e050864284103d2001d200c0c80026080340c0c0c5040548207030001c2c3c04a10708020417000404c160802460185000a4500180c1e10203064124207503001c8500108109600107005e181d0191440d5040c82c1c001e9000c101040300b84240c000c00344503059007500c040b140414882850ac6003e0502c0707640f05404101c006002240612005040c0454010100d0b86007400b0350340400c040c2c1c0c000794800c4998644498110080101c2800740101c0180b40e50801c00080c5440e10043e43d0714060514007600740a403803408501c51070000c0c40068156500508499640c51a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 609854730 1250 609853480 609853493
    0x60902040c0203031b0301080712081e0703121103070e030c03070611010e03040806180f0a0605090d02011b030b060d0203010f0f08030705030a080606090307090501060f1809020304140a 81
    0x710740720701051000c5c07800d8240c11300f000b80540b030585071800007c0c0080303800c0602125a14240c654150f038460700a01c0080181e900c0306030000101c10200003603a4450196240250403142950704014400d818101c81c103980080c600d0503280d20201c940740c5031605c4049000880d061040000712160035000d1000041201600000f21030102e145c1a0700030007403622805000f40e16070141d80200440d035004400803840802040e00030380c0304054003034180d030b101150030142070b85800c4d25000120f450a84030003c0040c01c96003402a07402c50b0010703000a10030900c8044a03031b401d40d046094164181a601c10706900c07070741c40d078109039400450480c0d401c55403961a00061058400079100300640c003404081c0c04100d501c80441941d16180d40300b0010b40c02c1417440d680941d0300c200001c0010340c001006200c1c220700b81d44c082044030020603012200003140c0d41000d20060105509655407424405030321104404096500074020884540040043c0c5030781f41c51920b44082044040400c007030740329890740d083c1813084 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 609855980 1250 609854730 609854737
    0x610080a0320062505130501031116061b0305271005042102070f141804150b03030913410708091005071101181e1707060902040c0203 59
    0x30245201000c400c03131002c116428070910302030564259440c101041154040e410100310350804540407030814100d00e901543c00300c10030a003a51955241c9040054a80041021103001811858103020f5031610901e14511544e080e1511465690b2510281119031030034404820f200203009820702c5217040c181004210122007009400119801c11040308900340002000d408540e2618a210055894083d4455000711103403241d07504401641d044654100510042600c2184900d0586040201e62070000342180e0f0100401400782d13000f0400008541e603084140246207090f43c0000c6140c2e04081807540340c01e000c1e214040c2c581c001107000f0116252140d040400f00c0072040c00a207001d56070b0311400300e40f0b204090310340803101d030825a4030380072004194020603481507150502c8200101884401400c440b01c000c8105600c504815101c4204001c580300030704511908003200e1782030440740d02d40307140e080d240801c90f00e01c5041c00614174040060940140c440160014020800c2c400c194101035100da0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 609857230 1250 609855980 609856021
    0x1e0c0d020a050706050a0206010605071b0303050d0e0c01052a032701050310050103090c0e0112051b030d08040c030b0f011412060a0b04060905070c050610080a032006 73
    0x29a000109513148208245c582501e110342c01800341e43d203044010b4500d9406a202540c0808240c51282c0c5110541c0c801400210310a81d41e02ea611030081c5825000c44803140c52200c1a5088a19803a410343e81c44400d90f0745009248200310100c80341c0c0c24500d200b001070404210701c130b40000320310320040303802c154500c0c00f8442c5d6090004076942035600c01120030f0322044603840b03e482e1214000744115480780c1e000d403490034410703030080b81801d44520184010b04800d038405481000030000034410031006211160843c0041c405149071400300c3c40000c0e0301c0e0f00c83e040303844003042604000102485070310a00c3c44003c42c1c021003501c00c24108a0004040300809000e1803003142090141200b05013002043c644211001c0e44c0a030000d901d0308024803003d4070250050341e9101e529a47c021031800350500c2303214007681141d16815012440b9260079800c001c0001c1c03070060300c0310b000401000552030120300404482e42c10f1074410740c04203a00601c240309070301814000b10070b8441d6504000c0c1c0349002641070b030b0140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 609858480 1250 609857230 609857233
    0x1180602090909011404033c090506070b01031113020d02090a0506031018090203030c010603020114040b0412061806090c090905070909030e13020915030c1e0c0d020a05 74
    0xda89400f4001e0aa84c8240c50605404007040c0014022038840e003030548888510301420510310805202c00c603101e45a1110307103c070702e00d8182c1c0103541c010b4002d11200014001a14020305008864503601000ca405210141910740d040e901080c00d43d0b11080d16542003d03022104544448100844800a400414001d4029020f408000c9864505141624820744041285801440c1044001c0031100c030041e81c03aa03480c90720f50000c1d000680c0c00703101a00c40221000700000b41c452550000401d1007260305c520305109001002b02b4000d80e10140c0c101d4003914881007018034009043c3c5008002000c4880900c0b2048141c011200100540c6811505209004411000146445903449012286650b0008100c1ea114000420a10400c0d801c0341d018503000c0d082c041e00403500480070400d041c1448854650712540010703241010303d0714000304068582aa50f540d810f603d0300f50100b440d03500ca003c903180c201c07051802c9403003603d039a07040499480d098110281d82c1d0385419650060f60750398000e0300031a60b5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 609859730 1250 609858480 609858499
    0x4031b1401030902100c0302010e100504210c140a1a060301060608061008060d121e0507020d0204021c061502012f0706020403060c05030702010c090303021e0118060209 74
    0x281d88640584107150f40c00034a5403003005c0c1c640303000380c4100e00e1a45085003555204c54444001d00403d126264405a040da0040750b00e160a1902d0303c1e4112030b1882e003040140714800c103020580c1c0e0210340075020a03400300c14451605c2c003164941e45490000c003070090010709680341450500c41750414590090500b0b82c003e1121607200c2c20155181041140d01070342004d000c14901c1c0d1170f603100700743e20b94001201414442d201180742d1210070302c0c528010040c2010500904c4107041002c00c1000342d18107030b14146801c03030a00f40c15a00054031405451806881540c021608032165852184c0e00c0d003102190300300400032180d8502c5410301c400c482c41706040255281c012442c1312100300e24003404042510642d105440b001d0709189900c00d81282c402620110707401d01c00030001805a10810301058510340300d06480b4070703091100a085d5200e81080c80100078410004000094002a13480d16806500030b10721800740c04440c0c4a8010f118540445241d03444180c1c0c0394050000b2a80109548003081d50204078 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 609860980 1250 609859730 609859769
    0x60318080d0c03140a05041b060c060c1e080702010f15090207080d06140a12031e122309060f04080904091220070501021e0304031b 58
    0x285518a41029015032010045681a905194003251480035581000101e1210780e8024007540f0307004880702c15115540c0c005000601c4079984400d0b0201591382e070b48a440601344180203014150245e0010f000c81c0c0c070f9a0fa0350500038040c01116040b020303d050903e40c1c402d240c0d60010410041540c29a0142d4a03004100d1203400c00d80c086c242c025083c1800d511500742c50055050003d41c0711640c26103607041d0900001c0710010b07107030045034010300d040510040d800f690300e010000c228103070341d002d000c8180075180400d0010703030040c040545208441d0052598800f154071700b074500740e03260851104094508407144410341c9100c20035610340c801100312044a541c071190410b43e41c0c00d040e9020b1a0007840c5000040000d00e81000a143c0c08102030004541c03c2010780c0d42203032003500c00048002150002c100a04003928000d4601e20b00c540803001850058036040005c0e4442c2084156002e00082403401041c0c034500c02c10494005540c4890014141e05e000704103d8543c407240d000d80c0e400291003142809 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 609862230 1250 609860980 609861011
    0xf09090209010c0212030f0403050c0a0902071e020f0a0b030f10030b010312170414010507030209100809011512170a141305031c1205090d1d0402030c040603 69
    0x159801c1040e16861142c00d819000c00c0101d2490812034061440304001209502464034088c200440c401c83c010142e03901e980701040030075046a001480e400e40f040c01680302040c240c103145140342000d080361240c920070718008964964119010a0340291003100d0001d0404800130045102d00390070000100b160f00c2e1007240c81c00f00980d0b8403018041c0c905280050000c45d8100070000442c0013035080250085814404224050908590039102040d8011076410728010030b000385a40b00d0070618003146089510000626455840d0b2281c80401007048001f0f1003d40f001d5000080340c8103040c4140c24020740d1a89290001000c00e2f004a5000d52407510f50000c1c0c03410031090f230301803150680762040501140120742c203141e001180018400c0c601000c0010741a1000d102481091400c0703d20034220a03041d08024083e010000d503000d1400745480d0812852103408240a070100c2c00d03901c3d2422503042e090141a90440010221b154818400400e00100e0349a510081c81140c0340c945081c4030300726420003081c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 609863480 1250 609862230 609862237
    0x24030506060a080720010c09230307060f0c140715050f0a1101090609111207050307050906012006190e0a1115040e011d010305032502060a0f090902 65
    0x41d4007140226001c00c035814017402603480c003103a10030405684c0c05c8503403410780d096610b940440d10105448100a10003054031b41d00c1c0c00d070044060340c2c0c0c08007000c001c2c50219aa0744c1045c8a100c0030811800c41c0c003150a48900b9a195015070008001107200c003618a6482d1180c7c00c62003a04049020003c0c56901c1e68028001e071510035054054180c1090b1540400766103081810701c9a15941d545c80c50701c00001241803094000407406241c90100540d000c03018041a41d800130111401b5520000d0100019a800150700d82075480c01e4510750915101c3e6001a1461848030b0090b000350701e5000242000190000b500038840d00401e4804c1c00804d40c00362a540450303004504402d0305401107040040458004a03c83d44500c0010348220160584d45110b0101c0b0f802c00c4e0000700540d5200d800400c059902ca81c41506803440c4904a400c80c0d51440d520b081d5203215007003035108800c202c2d01025107030207814440b0852864002d03180c0b40d683c00007014002e002603003020001c0301040e400c041c0403811850f1071098 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 609864730 1250 609863480 609863497
    0xf0309060f1b030412170f06120714040c090b030112061404020d02151b0c040b1f0e03010b0a081e0f031b0c190602010c0c0c030b0a062403050606 64
    0x42c03851034699132650311052600c0071075402408101900c01c0507440c624844c1a04c100c0021034600d81c0f50400780200103c00304c2e04681e91703032070358003480d014001040790b44450002c1e0030003203600080c034074111801554404810782c408070480b41c004c0000687c0454203145100f034284200d004010051131008884864082520083d4000442c1484000103040c44200c03054080982102c0e10b0809800c217035601d8045102e10500c43c03041d0040c660000180c10038ac040c003420b0100c100d0300c80300074500101386240780c1d0245605050030030010205042250b03c00303604c4018403401c003420380703662291107130805a582d0a102100181c02c580010074507240880105d442c1c0c0100c41140083e62400200c0750b0f03201c0c42c02c02407817040170240c011142e03c0c110556403400f0001d00c0314200e48040d01990714081002e4210b0b510046040140000d103d0601c1c000b41f4000d82103070503240c2c4503840c2480e907185c0f80140b00041c0341c01e030051405980428001c0e0f46800c1038030f036044044401c540e0180a02e980d01424004a40240b070344 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 609865980 1250 609864730 609864781
    0x50d060e190203040f02030105092103041208040618060501180603031d21160806010f060c080d1a0307051c03080414060a02180126060301020f0309060f 67
    0x245034118400396001140c201703000385006808103909400003401c54100380c4002c038080d400507048021141c82c21180b0700c008054038001500b10328060302c54010f00e00005001c50100259000000d04004507a4010114007207440409000c42d01c3d10324004000f030001380200308000c5030b1180d401e1b0710039920740501700a49a06075541042c0038600d40030341c51480e19000250b54000342d01102444c9052508644000d10b201e80c0000b4807000080d1050444c0c409201e8002510603085140107000403402100500203c5940703103802903c14005003040e40c164010511046099410154050008400d07482d141c51383d404120166484590f0300c070f0403c04a032464129402030303440f13250704000100c0d000b88001648540604180c1500d03c9201c2c130254106801181c01d000c101f940429420000301c0c0720354280c2c020310001c0c01c0480100c0c20759042100c410005861402040c0020400070303509440c00e406681c00c0301610142941c0300d0904000141d1110300c102d800d454500340801c0022080200e00c41044920740c407060 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 609867230 1250 609865980 609866011
    0x60b040b19090203061c0c030605060a06090b1309051003020a0524090409080d15050d05100c050c071409090307020d0b09071d040209150105040b13090c050d060e 71
    0x114a010750130042c00036501c1006207802c181c0030300c0d20481d9034010302c4c850b800d04028070741175141c920207c41018215501503103c2300f1040c88040d4028000609507068501d825445d020700d00c0d107114140342160400e807840c9041105001000e4104810705040c1e910890b403c400c030948403800e011520390070031460001246160488891a4400b030000c1c80c545c2005030010598407060b84401c3ca50350703c240800902243d403102509d15a0240c0d5512201a02003100d00c91050034064403001c0c1e0700c1521103078030009180e448041d80390460041c0100d4218100307040175034030b450ba86c9203040000e4003108010140226420800106400380210807030703280503402400d880c4114400e46960108944c0140818100c0c0f10351400829010410010030501c440c100440354400c0ca40341c0305202e95144054840241e0800c0305040c2519130ba0040c0984003a540f0b803607801512881c00c5500106a80003507071040c40c24602d010868101d09600100800303030118062018042c06654440a03000380c03008440001c46040c101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 609868480 1250 609867230 609867239
    0x9151d12120a060b0a020709060e0f0601030218270a02040f060f020102090d301d030c060403050d020609070f06030509031c050702011d0316050304030c03060b040b19 73
    0x1403007841d00480d03101c0000480c6074885100091542c1700c1c40000d00564040c940403c0301500f1400340101a08540c0b022440c24103042d0041d4116141c060300701414990085175100c1250502e010000301c000c80200141c0c150380c000c81138803071032294844c0c8000070501d540001800305811350080350200c409070301d04035244a10b049401c880142000983c90b0455400304442d61081e0f441100341e4282c6801000803585007040400702807030110b0788800300560100d14440c2103150b035810407400d4014920b54072101e089251038100203420103240e10402075201c00082000700c20f100c4001640c84800101d6000c40d913040c0c85280203150745074a140b054404502c100312041c4500d0740300e5004240c1084c00d403400c480c100b51054824407040b0041f00b4240c41019950010040c40c40c3e0309014029514101e40d100086920030400b0b01ca44900c40c0b45025401c8002e14160300c406c1150030000c480046401840c1c440d0741c0b6860345000720290500c07a41c903030f00c168106030780303042180b40110481240c84d890000c00d080a9150 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 609869730 1250 609868480 609868507
    0x270408070305070803100f06021609020d18080304050c0a030b070f05091c0b0a09020f040914030d150f051f02030f0f04031a0606030109050a09151d12 66
    0x824007102005414041c01000400103000f0718000c07102040d015406605060350340e0b04141c402e80c46070046500c04146401c443d021206480b043e280412000b5a4030800c20303100c04054010900d9000000d07140c80c1d422030034030884c803001d5800f840c0300d0010340d8410600d070b03010001c3c10304244c04080c2038102082d0108040902405081c3d90b07000301800c0070f80c10090004002401210309a8640c41d0034103034100104108001d51001541c8841100e00402c00700287d0f070042211120440c8016000b16075580c0c03540c0500102c11941c0c907a20290800700c0b031b80c0c3c6e5910f460380070151940074595000440c54610214403c4440035660098410140c07a480e4030000d800c40c0c1d69006074021180c902540420440c1005041400c0c002b4607030a6611007a29664520303515081c1c0f8504c2a2001a0007000680d07418001c241c0d0310302c011641150b5400d00d0105480d00c40b214118000c05c5140c1d07006145c1c041450950716081040c2c0c100030504180c0850004501d0710000c0c005441d02e170030880d0280c03849400c100400180c074030f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 609870980 1250 609869730 609869737
    0x2090604060f0909260a02060903040b090409021c15050106020120030721021804090323040b03150f040e030301120c0801090303060806090f03270306040809270408 72
    0x1620000d1500c0c0c03001e2110301701041a01c032001220790b20001d11020324039010000c2d03642045841000b180340902c0d003c55540746004601303c40d8031490310f8403180c0c010340d5100c600100804040389407882d102d144a01d8440d03000d03d011082c401c0e120303081000001d251030041c4070306d00d1003c000d8840d6a4103070380c00380e4a074409540000c14507000c3c004018519484105007942c2e146020346000001641c800d6400c03810006020102200d610030350070f151149001075031140040440d00f85401c0a840360152030154030406000c0c0b900704c401003000200400c440c0882d0782c4031031500c0b40400c0c1e503440b92001501082c48280c0700240c0440d5041c2d40100300400c915803100320540d00b00e900450852880c1c80e194030045082d80c20a002c160700181e02c4400600c4002c1013401290742010840005054000041c4035480c0c99000c1d40340d428104030305800c90031007518021583c5c0c1440c443c00509441e800e143c50320300014203030844150180200001801001510040030010b5540c10a5107050314840e56985c0c0d40c030005a1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 609872230 1250 609870980 609870983
    0xc080c1305041a010602160519030b0403050c030309150105091311010c050114011502030703020d0503060f040905010e01050106260c070c06112a190b130302090604060f0909 76
    0x303c0701c0c12040d81816107031010f5018142d6540501402c2004a04201400b040742e0003551040310f003043c8000d040c505008050007140e40c003000440a41e511410141c549002c0d5401540d40e90000008100c1e40d04400b080f07100807142401e0b1018040e03600e0740280110100c044a600440f00305021000d004a401d92040301410b10381403600450030390455848a003560200d0460300703104212040140082d01c4c2201002c11482c1480c8001c40c01c09030701d514020365135500e1801d004140b0200102143d01611201012050100c0c0584140111009403030f100e40207000420304d07205a9480e01001044261181d942a4003611008903170400d10b802c004019407142c04045c0003010f0007242080248006940300c1081c000a10702038540b43c003e6802d0402c81400c0120841d050b518840340c0701c0c40d040b20f840301c00d5039a01c0d8401c03042c1c40c0780c030111114602143c030209072508040301c140004a884020001d40201107419644242c850042c02d40394070701404250740b214081e18200c2200e07880d0a02090f80e540d0302851800d07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 609873480 1250 609872230 609872243
    0x1b21180f0f040c0512060103050c0d0b0d14030318030c10020d090215070b0601020303041a070215100906080307030915031104060f030506030c0307120c0e0a05040c080c130504 77
    0x76551800160403a60504403000c040380380810707101a0019140c1c0f60b16031101003800c00780117a15001694845910072012280310866581d10301046e9a100c00c0c500c140f409500080ac00005540c0107090b59aa41044038603061041d2903891040030302d44044207a81c005606030b0b0042ca12044500021b0010390845110031009075a201255009a0784802031140150001c00c00d060341c41d21903090032402c20b0304c02003190f4155403041040c4070005a15201441d0812a80c1d030080807241c4800c8030803414000c07030600d101c1e51030134114107102c40c2c0c1101e00410b00c110759070200d08018840c1e403a0709a1b5140e000f40b10002d0040b6003100b90401a10040c2c0c0c401c4214140c203440c002401080102d200440c9402940040c0c00003128840401e0046030103210b5550010f4086008220380da0303104000035643c4135a401103132042e8012285400801a01001034005020b400201203040d290000803074004241c101d4040d5050840610001805240418002c0c0800d50180105245102415808002c4c1c00041c004130f60f05c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 609874730 1250 609873480 609873499
    0xf130c120204090c09060f080a021b0d0e030c0306010803030c03250f03060b180420040305010e0705090408121e101a042301051b21180f 60
    0xd4404600c018005010b40310700028484400c104003c080076459040007061007203c0302a01800b03a040b08109a101228030b801683d102030400d01960020788940c01701a4078480d800b029660b840e0040e05250784003d040d03088038242d01c0210b0405035071320020301c90035080390000c0000c01d01990001009650100301252501e46c6984640300c14080f49540000010000d510162a030b5141689402038000528428402e2402c0c42441200c00070308040000c035591040b9941e407140501c4d071400d02d4103078500c00da60312011525a82d40e41011400307080702c141c580045003c2e000c03007c1040c0c64040701c0300d802560071600c1c1c0c9040c10f916220310498420701800384444001d40707072400e000c2002e0302c004c0c692084a6008124801034034112128001d42e9820a814403044000e20081c0480030019031070040c00c40c24030f442e200c10001100010b9400c1c0c0728012502e03260f8039058115240c0e0003000520000d030503425004908220900100d900120300490020750260058121603040c40c2c5418210480e40340c4004011620 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 609875980 1250 609874730 609874757
    0xa110910181a090103081210120f0212030a05070f020d08040303031401273201061d01140a020708030a030b0102120a1713050316110f130c 61
    0x40003222003030320340d801c0d103818090000c2c200c07036906500304400a4440710915411640d4000c1540a5084003460100044000800b854103031200600280314452a01000f07140702d040410204042040c02d0340200780300107401400703041c00001c1320101c13000b554a550604915a031451504180389500341e0b8030806441c0044041032008006100962007078070000b0749040c0302040e010071081d0580c002103c000b0f101800010103a00c1100c40c4841441d40d031400601620ada0501e81306d8101d02e181c107400301e007a00b5900000340e512501509416a10540c0711081140c40c58404840c100c007100c0040703800140c0302e0760202e00103840c1c900645003080702401039500303160b11780700c11a207150002282d90001030b8488a840856503018010882c01414000c40c4a282661104c03024160b2a115400a84820211000282c0541171504c0030f00340740e0741c00170982e9660041c00e000313460291040d540603034002080e503001c01c84078038081d0300c03543c04100042c100e8803180414021600040a03038004007414004425120340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 609877230 1250 609875980 609875999
    0x2120f1006050108070905060a18080a05010905060a060f03060b040207020904050d1209051e070b030f0a050a1a060c0703060e030a08010806240f040c120e0a110910 72
    0x1980000000c000180c4a00c2c20000400700d181c00781500301030040c551818099501c42e070b003c45d2080d5065080c604886c100240d01000b00341420390042d1800c0c010030081d038080102c107420400c0800e01642c119051340d142d400c45c2408a0f2010320a410303c0750540001000011600d0700040000c1900400050900180303401080c600b050440382128103410002c2d94401e6036820008043e04607550b82800c001850150703032090b42d644103440d078020350f804075805e00703200c0904100002e074050700d02481011307140d0420454185055800380d81440d441428580003505046280c030580e603494242a070404046280c800500116034065684a5802e000b824408400706106000b0403260256002c011981c2c0c80400c1001441c480c01030304184044d8101c04180a824003034400700c1c01c540c0c04104094a1040c2c003c40000b1841d81d4400c28240d041400c08400c2c0b181550001803080040780708443c11311880e030701107000d50303102c02c06144000c4c14840340e038244038a141402d00030541c0c4801d5441210201507154510350 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 609878480 1250 609877230 609877243
    0x605061c270c05040e01090803010909084602030a0c0309090606020601151115060a031e02041109010906030b0d140604051c05161a0106050702090105060909010302120f 74
    0x2500c80440509080055003131034812800003142400c020800922255900105440180316908076551a1511101804542740403920309584030300c90060006083c002c2040c0d4401c02540f01000071880c00310b1800070741881210841101080c0d8091881d0400411066845910800c02034040100b81c9101085c0d4102030f00c15803000d0082a00180300e150315200800c50000800e4554000b0050440c00711200d20000003494190410202081d98959441c0c402085040b00142d002405506c026105030264802ca5603401d4890750090b6424010b69a0750810243f031845241d5281e1b0015000400030803501d88250302c40000014010711500380001e858946804444646100101c00d0f0000700902007004404c0108400e061104142d0380d041a09030100540a40101c440601100c0c001644140c00c12a10039031a40d2421000240b41d41256183d110042468110100072402510020300108141c500581541d0128900a02e072060341da086500f40515581d11051450340b038420700c144401c0005052051 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 609879730 1250 609878480 609878483
    0x605130b0c0106090b0d0c03021e03100912020a120c05010e06013209070e0111061503150907030201030b0a0803030c071716140f1204090605061c27 65
    0x443d10508000503130003164042010702d03124450903036101000800200e0501e08803074049900400002c0800000f881e40e24100481d558140111401906031110b81e0b4080303181e46000388040c1101c1081c680b800c1e60389107100400034010100e0750740c083d00454402c4200c0860309100b20004030307844043e40c07001c9181c020207801c52202040404219036540300f4000100c1d40c4084d020210300710042d0803201055031000d01401a00030007200c6884202d0613401001d505000c0400b0300122505850403409202d001c20240c0045407180c00b52030a04481020764952490150780948064840c540c40c590040d002041c45102e40743c0c0010030482c0000d944041800954420341000d1050b0ba0385542928101c2c83e00450140003540925050000b540d00348401c1c2c20300c480c1075501080504a1140903038030f0724a080c42c1501c20154910800010310400e10940c406001150f05000090244a46031401c2050b00e02841003400a000030728040b40c5d440b60030a401c14a08500020807400100c0e2400c2c86061464140460 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 609880980 1250 609879730 609879733
    0x4060815060109030b0109051e09061605070b01052106010e0a0f110915250203010e01050601080a0c030615050c0609030f090f06162d0c0605130b0c 65
    0x115486600350345022264801c4003407030b1181c40c0b40c2c00c56035011607129040c044d01d80a2640c07540018190712200311790700b00040072001c101281d40340c803c2d00e050f62081d04071540b025003558907c0c0e46c040300d8003420aa84009611440e2040540e00b050180440002d8002c00411041400880c0005001d81030044502074036084079842c107541361040b111415924101e600c0c543d034525018903000c1c1d4001030380507a140490115070304683c2c00860043c020a0307010719003c1d41d91884401404003e040c50031410b00072003510035002488107641c04200d01c2c2c01c89808031100741c0820740b000c00282c015031540e402070000000c7c6090000d5600c0d200c400c000e6139402d4009031000405d80025514155503400c02c10640d01c4120040210b241c00500213903910300340900c1c00240e008140400003100b079a5540000e50364080140e10740f030102110743c5e0a1241c0c00c0b40f0340c5504c1c2800e03a414884c102049035074441c498005180c01c8042c55807402d24183d02160b00c0d9000481d030549000541740081510300c1c03404024500c0190440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 609882230 1250 609880980 609880993
    0xa030b1503420d0212060a0b010914010504031719122901031107060f05041401060501020c06210708161809180c080d090602010c02070302040b0a0302040608 69
    0x159142c404510120030900c034001207155031102d16000380034032800c1150648454280c000607101040035190351485a0f03000c0e008010400c0086c01340e603400948841400d03a20f52144c20b0742ca8101c500360049942402d8001801003009201080a03a44410300c00c480d42a40c6503d4050080003450440a91084080014500c0c0e0020001c202e024040c41030304414061144408251210140a5080301c03580300d181490703101c07110134803810015001e03a2107581e0060018040d10f1045940b4a004107030484081710b9003134a503d0088070741c03003051103040b00781c03101a00282041c810401c20001990810300745c2450783c105004074116681c0e1144002ca01513615034032000c2c190304190008402814100e0540010002030340b038680080b455021060302215040b50000581c445e000325a4403503e0413804014000c5081700900103030840000510b02d0045615541c0c0100e100d4030f820080382600d41484035140180e00001052000d441d01e94070149802e800140100000359481d408079056410030750220314582c004c40d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 609883480 1250 609882230 609882271
    0x418021b06090a02150c011b02160609050108040618050d090512030301030206030c040f120606091e0506060c1b0f0118031202030d02070803040c0501030203010b0a030b1503 76
    0x50060016080c410103008549000c03000240c2d2440c003010082e100314400c0000d10180b02c140c07000c41d000c041140c0001d0040026141d0018101d6400000e040014030030b60801c2d80030602508403142c02c3da036503a42e800e04100d00d410300440e00005c3c05041500e1195072210b441c000b41c0001c6071943d8001e48900058002002605005441001140c0c030580c00b5050740c2004c40d408072408422030341542e5044804640307c2e1640c01718080240903e8129015001510b01c01003240182c1e0002014003c1c42100c0501880752a0260b400642e60410004c80307030403407500d0828900d88401d8028039408080a000c41e801d010380c0c0c0343c08903c0d000d45805500003c0146902c5840c407802c14030203850204000317080000403103400d80c01644400985220190104098131301080805200740f00715030b0180e03000c50b015034a8010604229800340e0040d10101e60704091f03181d0005803940a4000c1d6070403184000320703149c1040c06480040d006000b1262a0300c1d440003000718407912044114000e54010003c0c10921100100f81 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 609884730 1250 609883480 609883507
    0x2406150306032001140a023703030504050a020d0f0605010605120105131103151201050103020d032a06240b1914030a150b0702130e0307021206090c040207080a050906041802 76
    0x9120b070114061802010342c400e00454072110740162350745898001155561f9003496410f001c108000254003070003144101301404200b45080c040c480c05200100b1003640d031020180d485105e290107492800d2210001000300d45082d00503c07a0b1003900c00008a5854840d070b01d444240e83c4210394a28003c4000401c0d000c0c6401e007641d80da108194910001c000a50640d000030703418980c04100102007140104180156000d9050706c50b03501d0380d01d140d483c1c0e908202440c20704054040307074041c0c400700c01070038024103140d1074015910001c850013a0750b510b2034a0440d00e00c040658070b19403114011b000800344400411410003008601ca0320500c280001c41c2e1074401106202c011299110400b01d1006101040c00b50b03548000c00101081484000a0742c001c5544450b8110702540a020b503000c500743c0716515121002040c0b083c86502c003c000e9509000188003044224015010090f150060601624041e54015802402c1c07900b0001c220034206a0b1b103114034116004000041e03a034032a00400c461070070070703c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 609885980 1250 609884730 609884773
    0x2130605030606070809190803071a0708010501110c03100207020a0803040e01181d0105060a0503070303050d050928290708042406150306032001140a02 67
    0x44610380680703141004400241503015044024203130b030100003074140c0c0c0340c0d0f9005401e40040ca4007104108030303140d440001f0741e12500f110100340c4081885108600e8901181768510f40b041e001521385c2d4003240d081c18011950a06000c4107010b50f07100c0c2c080814801d030303070401c140000c01048610150751154584144840300140e948401d025034002c0c0018086d45403060100750545200390742000e1020b10709030140000d444110350b140014942c240c048940303c3c07419044680f0403501503c040180c150341f40103150b0340d0340d400d04c406000070340d0910458034000c0c1190481500700d00142c0031a50030303020300c444600d00040c006c0040c00c2400070380c0c483c1c8003c000030300301e42d04105074021112100300303891869800c034a0303a002050b013820000320070300140820410066001061409002d5501c2400022441c50000c119500503108819010401480c04034032070701421084c0c0b42e1001004050311004003e0300d0340040608605814001c5c0e0302500301e0381201030405840060141c1c0d0007400e4400c5229403450300c421 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 609887230 1250 609885980 609885989
    0xc011401060804080c0705090c0706060e011202040e070305070b04090b04020306130c0909110406030b06070f02091e0a1b02011b18050303070b0103050f280516090213 73
    0x544000041107201d8101241c070f503100e40c0241a195940310182800c904014864100d15440f002070000d01c00700b07041c140050440b1034810b01e410000c15499405520300e04009104040102e40304019000050900d83c21014139629047d02f100e100d19141c4d6280307800d01e1015004040900400300c0e0410000c209070140b6170703151005940c21071a60600001151848203448a260a01c42e02e81c40441d5610388a03c003004010448107504220b065030302d400104840c0d22511a1000103420464034608038a050307022650602d85c0301d805022214116401d000541d41d005000351404003011140d0740003c0000c3e20000d00c00d51f101c50700001d8009401e41195040c140c070405c008110b81c98101c207011400350551660341e01d1503c9080070384136080041440b00700e0031680c0d000721b6014040420701404210b80046401e040c1c903c90000c3c3d6004030180390282d40c0d0b03080e0212010b68108030000300000840400c0c0c8000005a0152090764160f0b0b03900c02e85030702203040716802414aa0f60000d010100202600c80e0f440280 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 609888480 1250 609887230 609887261
    0xe0402031b0a03240509010c12050c120915130605010e040b15040221060405010b0f07031b020301020318120703021c030617031e030601021e010f0e030c01 68
    0x10300d52010039004801c03030100034640203042000c80303062070b00c00a4080d072408845030203001c1032606c04203c501034400c0c19403002c041925030044400040d075a000e5544211000d0100d2401c028450711890600d42002e041c0484501443c0740d001c5034846034030545449400c83c240f5464010310310340b0f407560403108140c0c40340c5c3c5040e0201d81448001902c01c144c19401c08103c030f080100140040d00020024403da0704030614070b40c81c04c1078454418141b038849500c6007504a03010000d60307076204540d0307840d03224042130b1175035103c020442c5400090042150481007120145100310032005c650109003280e03c191034000a03040700c07100c0d09821600400000341e045000c0404c85042c03416a0b58060740c0d501d442007880040c8003141204080f450301c00d500c9036000b0b0441e5815501100303240e08206071258000d24040700d180b460030041c1c6541c0c98480e41102d0240406034020113000c02c0d1102081e000244c000800d10040d521400700300100c0f05140130304200c500040b0b0203140e0b01c01c0700c0203ca500311034040d00d890210 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 609889730 1250 609888480 609888523
    0x30f170304050d0804060b060d0516030b060a030f021608090916090306050c07050105010e07090807030c05010503180f0c090906070905010c031e05030115020109020603130503040f0e040203 83
    0x1400441c0c5060710540504251244d9203d501e000406064050362860304882c0108118140114941200380503c40c01c40110039000f91940085054070413126045403c120b08101c09200039210703900010100041400050501803914003a205d51544190140c0e044540406d0030941e80c6050740c03a142d04000e51282c01240703915041405807014060344800342070388d95240001003000003c0b500311080d80c0da00400810aa607102c845081d8081c0065401100094180b04040390400001070a42d0549801045102d0440c0c60b0500449043d4001059008400c52038454030310745000401a00a10391680c1c0007500c0c2081940d0144010808000d20640c003a5004030240700301281c00c201d03030b101900c9080ca000101c0944c117040907070780340c616a4048400c1e500c1031030389400b146034020041d41c161503e80c4800070110316220012400e070303042c294019602c400c04101103080c612440c40c0c040e4903181b2490650303080c0390b5200000c1104010550003c6000705000d0100021440d00780003410341700c900c9445a001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 609890980 1250 609889730 609889733
    0x30d0905100b0913140a0804031703010302010203030a020d0902181501050405101b05101413031215050d0c090e0708030a03110d0e07030309080d0c0602130b0301030f170304 76
    0x142d20340f01624403c40409620360007400d00c200805000b035840603803011200425160700d014102603201d03200566480e8081c0c156840c240c2e4220302103904072501680118155101c244034440254402003148582c0c0c1c1d0f64503d4000107031070305401d080c01c40c410003d01c10454a001030306450405600c0b44260f041100c03c00052200751760b52501d01c3d8503260503140152003d1103030406110a480c0069024009100c3c03208004013902841e004181354412155641c1300079211003881c50609a088100100403d13040f0120007043d01c041d51254607041c051403801d1007107954441c049080551301c10800d541e800d01180c02480020700d9030051440107011800100080c0c0c0c90044020f840740030700c855a004240d115040100c000c1d403210161110140b40002c10403007403200d15092a910b413540c1c442100850038541c0d00144031840403644124050443d2918100000b00d036407072000941c0b0480401c1e481c0d0440301c601168800302c1c0009140a03510a041c0e480041d512030800f079035507071011000d2403d440c808008200 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 609892086 1106 609890980 609890989
    0x51522080f0d0309030807140409020f030105030d110d0810051201051506091503060a090606020313140a0302010507050a061806150b19030b03030d0905100b 69
    0x244482c900c014181e0540d07101c0c81003e404a006e0500040c5500e0184250803050840d200306030b4549611800c402e012a00100c1c1080c98515010006002c1400c080180050104960424444d40c819241d00303656180341a002c13280c20071010101251141250242c0341c030142200421910044445025460007020100c0e941c08003100c1c3d503402e00350a41405021544d000b0740207051000d10b1001d80005071078a9001801d081e410261120380042c40540c14444c50002d01095030141d592005003054240300740405400c4054101002402011035603601000c03042200e50a0038816181c0c000d40c00d045050000851003e00258101001020314010301e07040d01104912400081000024610000c80d451a050081c0e0880c83da081100c80b6515001c114242d043e00807034a401305000d085000444d055400c440c03040244140c845000310100b00b000e2095103101160386c00e041240350500b0f070005 = true := by decide +kernel

theorem cover : BRFrame.Cov 609712230 609892086 := by
  have h0 := BRFrame.cov_init 609712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 609712230 ≤ n) (h2 : n < 609892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
