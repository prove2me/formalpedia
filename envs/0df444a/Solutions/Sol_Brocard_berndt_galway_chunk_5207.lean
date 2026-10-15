-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5207
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:05:53.567293+00:00
-- url     : https://prove2.me/submissions/ccb7ca49-edcd-4602-9f83-cdd61fa083f2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 936330935 ≤ n < 936510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 936332185 1250 936330935 936330949
    0xc0605150312120f250f03050a090203031e0f040806041e0c1203050f0c060a06090608030a0c02130e210403020108011e0e0118060801020304020117040f06020f1b01050105 75
    0xc4000e00742c103016a2500600c00d09109250410042401064010201c155038803106c072010304035160b83c040c0045d8503149145000ca4180305006074040d0400c100d1440880711214004c0c0c1d092000501003071030407040100440c51a0000d0b0004400d6401c904180300512100701803448001086600d081d000c0e52142e910620034a04600c02c1e0f0000c40314003a10582072500a0701030381c00c5804c040040c0e541d12a201f0f1002520307004111600214140740c0140801d42c0e0a11b4424172064458010046191115031242500d1000d1101004c070380c00a513510700180000d2080c042d5542c0d05031488010004542d20070a11002070920002c0d03101e5800044c041040940c0e40f140c40141114000444540403000000c00c5e0000d00c09641c01204007640c0b42c400000b06c504141c1c81401c6840b0310000c0c1080302a845680c3e4600b82c1c803065074085d0005045414500d10640d110000b00c0c1c110303120b10303000650701542d9a907a4003660030407030f003c82c0d03500c001064904030480d94007402d54180d10307034100800044d03062030005030007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 936333435 1250 936332185 936332191
    0x60f030b0408073206070207090b060705070f0510080c0a03180b0f060a17070501081008010908040513050601120c052101050a0e010f03020607030c060515031212 71
    0x12a8035880106007480350b050b080710041c9030001645071101d4501c030480024102c02541d0301142d425240c03503860080001142c40350048600e036003e0f01d9801d14100da11009408d2014030755038001d07030810400000801c05c012400051680700c812850051400701040402c0790703484c606605200c40142005080d807201c0c022520060450300300010402144030380c540100d4800c890080004083c0c1342409015004148040d10405080722002d903450344841d07032145450747c070240c50b10541c0c1c401c8006100560080c849594800040030302a40000c3c0e83e04012800e403000d4520a4400600014061005040450303501105141c0c42c0d1050100307081190000b08140301c1c400f107082040e940c0b05d4148180340c1c072800803210756154172a200c41c61600c103c102d40c03280c0842071040b503124190641c1d0000d240e1052030b00fa2812100e4000c80d03945828a503030244100c40d0f00c0301c1c504804000c1081150070000307580e44035460003000c09074a614248508141410300e04003441d2403552566206003c00402c00528a05c0ba641c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 936334685 1250 936333435 936333443
    0x18070b1305010c0807080304050c0a050d020d0b0403021603320a03140c030a030509010b04230a061802130b04120809040609020403030c0507050a06090b0a1106011215060f03 76
    0x241c6440c0c1070030304c1c80b494000c0902c02000b1041c0001440140040002c2c481a5041301325000a225659541008455a07200000a40040b0854200008101c030300807401d901c203000380151599400015800c031000150342d042241c02c3c1d6902c008480e030010f004c81403400d10600c1c1c8030000c4107011840b21203903a42c030003411004003003000210303200d140c00201d4819a4000304000040341c0d00c4088850000c0c01600c400c5030005200e42c6002d0080100c1d1501c0d0060403a144112910445403103a071075898840188014000c0c9285030310b031100020062141200c48104603a40d207001621280040309543c1000030b56440011403440a00c000e004190705609200301550784103541503617800300403000c5006031070340390300c446011403010500000707151b0000c1d543c030b00032845102a604075035120000c00024112501800c13001032110764041c090716503540002e0290701a03a0421a5001c040311188a152010981080052601c000c000401f04011000d21403055040d0050a01495013082c00301003074800c0c9444060 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 936335935 1250 936334685 936334697
    0x11a0901090b12100b27010612090c0e04020111011a0d0f0f0809013c020a0c030302030c12041206020901090e0c040f080d1d1818070b130501 62
    0x1402c540c0c50401003c09405014261095480c280180030000c244220780c441c0903084500007107140b1300e0340c0101844400c4614407104020390900034203c4078903200c1212441d03099943c690300320201e0201d242900c0100503511243c080c6140a20004190710160081e60103568101203030707040100303031030340440c40ccc2c1c41000e6032902412021070070081c283d050800e0000d084c02507002440814040c1150040c4590b42d42138840708917544001c041000070151740b480450750811450341d0380c0282c20403041e910001003034030f10480c2c15084c2c940d11340040204c1154811005139000089550303044c80c0078098802c0c4908105106420246880071500310354605e5007006080d6980011003510a0b8054803800e005800e810304001054a400c1488401a038428080c1c40307030002e0009030010350000300140403400f0001d150340702808403064038003080700d880c40100303050b80c0002000040e6082140c000f000c1485210009581c804d0031103801d9925080c04004d03088030030b1544040142e035401d1030a072115070f021030714207103401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 936337185 1250 936335935 936335951
    0x90c05070c03060b240301050a0b161212020a08010510090602060115050c0f06220206070212030d09031205070e2215090b0108010905061e03030403050604050f011a090109 75
    0x2580f404905c002822a0701102035043c0c14054641000e14103865080d41d26201668039807040410230f00400d5042d20249400306410000500d1640780d018250101d03084c1403807002140c141c0e034000d07600b1800300c40f4001040712004000c2850030351000e0700d8144250801c60780c442c0c140038000751902c00c14008c020740010b9024000c1203d5120300210303404402140140c9110465646409032603110940d0032141d000381c4038038a4501d1000414005a6040c0d004160516200c0f80b50b0034031140c0d4440290b03a6229001c00d10040c1d4188400380201e8407080d200e5940c1c1d80c10001400100d504454000c0c00c0101041170608050700035844502e0307402420329109003412080b0082ca40b099024101e00d00440c00802e14040d40050b8400890300030b4841e01500340c079540b81683e00c0342181c008036081111030961008560140c07406600f203080c0c58400c51103015050341c4c60141c0380d0700d45070700d407040a4500700c03066070164202c1c0030142c07c04e105031208410561503121844203542d000442882040c0074140d600e81e030319040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 936338435 1250 936337185 936337189
    0x90907033b06070c030905031507080603070503190606080a1106031f0609080607140415020109020a06080f09030306010f050a020f070e07030b030f070b070215030405010204090c05070c03060b 84
    0x308411071a01c05044865902d069440100510000301c41240851242d8802040300c0c940031030010100080f0b02c0d1081c0640d41c681c0c4003115a510050314407a058020083c012510752024801d18921314100030103485030002d9468040c00305c1d4615400900c9541002da61000003c41502d5203512a9808031a0980c4a4032510561100450b5000041c05050400b04d00040c500da0002040c808884401c2d0586d07200d9070342c2180c26aa144030b0f65040d08220042000b00380282000a0400342c1c1c0391500d8400010411859404100007590580004011a40032402c201c00044900f0115500280c100069411410f01c5800a803500c00344015640078401c011440038070781c42c400c020000d1181d00d560304a484540d030341d48400707018000a03035442c0d00003410042c0c2107255040c000381001012080f10010850240b901140380c0c010342008108aa005115010b54254640c80c03001542c0a203020b000016901c41c40c12041c1001c84641003070250500c05c00b072009401050020805404480e045280802c0e42580d00e00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 936339685 1250 936338435 936338531
    0x30c1008100b0406020106030204050a050403021e030409020408061f0b04060c060b041b02010b040b060409090c050909010c0f0306180906020d090c2306190509130209090703 76
    0x21502c00c0d0000c01c0c0018000e9054100508580c0255401c124586038880343c030069032400c030b4010740580d12440f4031a01507401c0c00643d2240142800c1940d00340703038a0304412010399006900443d2140d0206060241540d0071450003900000450f00c2d0380c442078900000c102e40c43c041d601c40c0d40c0c107204150044000f4131480d5009602010070051080100d0103420581c1100240c41c5000300005618292103c0034908180c4644025040c00034017080c24903140244001c05816094021501000c0d000340024460725554952405800100e0011407294411000109401c1c2d01d040c5600400d81000d40c10055452040000b00c9421103000010481c1c00490038003038040e03c2400c0c110500c0310304e03003984101842010003101064a046009003988100200d44120300f84101030700701c0f035025508000c040c8072642d600f07400d0502103c032810028100200310001075400c921845404c01070130340000392602d00d40f0b00750815a900c0401c1e03060030818500c440e0315074054440750142d080d20700f680f00c400703417110f04402d41 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 936340935 1250 936339685 936339689
    0x50f01020319090501110f130b0306010207120602071208090f150103020607020f0a090b09250513080d030608061b0f16082a0309030d0f110a0818030c100810 69
    0xf881a0387c1d0014203900340c2107688808545807103030b100235402140c2d901421046070f02a260590040c101c0d00e040c140002d0fa40000064110707400c5908124407400600700f1165642a803405031035450a074640a600c0341c5c20f16150300341a6895401c880c140d01e46000c1e144c0c10217419290161060707511451700384041400505056504e0750b0051480c8000901101070750002240c02e84140c401c160303a40c4400c0019041d00c64080b858503802c02111040c0c0b0b0082d4070a4002d800e00030300703001e0500d1650756200d80301410011114039550000e511000e0500c00070704200402a004140240d0585107072050b03a12034112030180c0c80700b141c0e01d03c5001a80400d284040305500300b000b50800c100302c0da0b0704414500102d5102c80400380401c0c401c094020102c8404c004000d40d230540718090b02402c0c0201141030100c8c0c00070781120301d100030300c800700742201000310003004401000c40c45018200e948002c5030194055851403d0020791203a8083d8810046a448a408000c481d0240e0309000c10a0740f940c000001d0b13803800ca9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 936342185 1250 936340935 936340961
    0x1806030313150912021003090f0b0712050124121410140915090601050d020307090e10050307090b06040308120121020f0f060f0a0903050f01020319090501 68
    0x141c0008140c50321000c59a140d401000e4681c40c2040740d48603149080310b0ba03542e101075072100010b10000c074107500076000381040ca4031481800204d90070035a98980808401c0e680c00000646806548a9500280c40307424058091034011602055400d4201c90016603403401d10010000c202810445421039900720442c00030100302c1c07040c910310700980c10024240b60b601c5080106052440400207a04008040601484045406000598948090124120000e8402d03410014100500c084100c6944051801142c856072500f01d03140c500440e511005602030030001e06400040e00802c0240c4d00081c0d03040841390702c21008224072006034000384040c003456001602c0c103940011440c03440d40501c9801810307110b5100714441c050400070106140708030a0440250001c00342d6111181d585407491401010560090426107000800c04066510b41c01448001021441c4030750b0030b104201d01813104081c80c03240d1b10000c506501d8200802c00d00c880c0311941c14095281c0c0c1d4564001480f100303401c004448810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 936343435 1250 936342185 936342217
    0xc03070219120809101707030c120c120f0225050a050d0915051303080d090213020a03050603010207020a120f050114070f0914151e090114070218060303 67
    0x70380c2016440c03a44075421380b5105042100d403002c0180e000c1c0c6110034081040c00ca540409075901d40e0b050780100f240107818428000240f9114808205a0107140c80038001980c03014030000080301801e003901d20022643e810103005101e00808004540c1d10b207000313010903003203921355824242801e50034180c41c141c01600500408012210341074020051108981804020440200305407a0846d81405038400b06a6081002c00c02003010840d004050042810b2046d0009041821a800640c00d0900740c1466010315801003a030401c0345406200c1c9a90102c019002135250200d00d40c00110550624000c1e62017440d00e1500c82c0d010301404964000c425680300c40200440b030b45080b401001e8410488280b400203071503140301008948564002421143e401c41c107441c0314007128041020b0143e6484200003440028011109494800f601043c61015250b562941c1c402e403400005003100c101c20310082ca035500420000c40107881d01d404550300c0451a11540d651619414002400e40c42000010152445 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 936344685 1250 936343435 936343469
    0x190615080603060a0504020112020d0b030d021011040e0105090903160b480d060b030901060b030c070f0812070201140610230415050a140c03070219 65
    0x1410494150141d00100d08403007040e954120400e042d1403080b84d0083c0012260654804c1d00c0038940c019041290680b0380100d9050b103014003103894122141d82c0000141c0c0141e80d49030b42d00740030b481a0004540000224cd25203420310381c400c070303070780030107101e0b003030040c10f4180000b03140510500580c0ea110146a041d03140d107880c00d0a05080c48030041c1c50110004040800a24644c08094002e80f10031110081341c1d04116403000d80b5041860f0075000020600c00c00f08044040550580315040c060300c0e4035004180ca0742010000c0c0781c00c4a402e40c1190030002010003d003c0d9104040054412143d4400c182407030000c1146041c01c86401001010845030007500c0910551503019000174402c50114410654143c0c3c0c0c280402c0a031000e190082c0b07000c0f540412403005207011200741c007100c0b8484040c0e00e9280aa84001084d003585950740004002400418100070316540507810fa030108001700201c0e4186028115800e4403441100002441007003180601c40351044004003071b04c0103009514010511003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 936345935 1250 936344685 936344687
    0x3190c0807080306100507031b0c08030424020a0807060b01180909030e0603071b1e05030a14040510030b0a030605090d0314010e0112031110270803190615 68
    0xd0410744131184148180b410420019102d002580da07459099941d5800d115042c0b0b90000d15541c412400359610f0600ba0b80c08502d40c4400c0008000800241440100055124604101d900c0310031400c1411504601205004242030310b00740c80342d5580141c00003681c0e40c0080300684d000744500c0c0d0407241c1580f007100005107100d243c0e0301008c03213030380251078107141054180d04114903448201ca03120086040d5030014142c0c20030701c202c40c00303206100e0707090480c00c1d1400080c4100342602c480c0c2c00b200d00d540002282d00c20a9404208518243e01c41000c4500341130400c1d000803c4440f40c00024401c0660741c00040f40c3c10390300c2c10b00800045400510400050520070580d9071603482c2d000c10600400d041ca100210f02c6c00a140790541254041c8660b0042039003002004030405c09001c1c0140d04000c03030046900c05103501400054804507000d4000940c02c000504c1d1481809039104007210110455040d050210f41034000700c0b0340c071908904454142340a5482100002c0480c2d400800a800c0100d0303800720301c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 936347185 1250 936345935 936345937
    0x1270e0a0e010b33040801090501050907170604031d0a0605190504031110020f03030a061805070e060307141801080906100b03070e0415030c080d0203190c080708 71
    0x1541030700007842030070201d00501000c400d4500c0c01044040c1402186164001d9800c03461003020f000880e035074034250303481004509403403c805092300c20742d41d05c0041c00804102082050010400d004190b80c0800b091030382c01e611900014009418010003421011040c10041d480260040d002000c10070215203e00c002481904801c400341a5080c00d6032400c10503d0150b019074040326400503500360b41f03a00000602441008a1200605602ca0f10500ba2070b400002e1014504c25500082c000039410b141112950070080000c0c20740250b2450042400311455220450f27807405181a20150354940741d0481c03c850345100b14440065421b404a13194144a04055402954420998030550b6079111800c541d603d5900545004006815903a01000400010405990300c582c0c54180022092039000c082420b94000d250105904610b5800500411045c1e400100c081c003601402050944001c0002035500d104c4c0c00101203c0751422208144541e200e182a5580b0740d5100c54500d4840c0102c1c41c010050b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 936348435 1250 936347185 936347201
    0x130b180a0c15030b0312070c0e010b090f010509030d110c060c070e010b0a020601060c02011206060c0311190809041d03030403140a0e0603060d06060b120a06030201270e0a 75
    0xb00c0b04004042c01c456601c2405070b0311148200602a0000850313210090303070b450b400148216000080c0001c0018140508810207000b49504860390395106032040410181020101000307040c0502409002004e0b00c000407503490b40c4105040861040d54410300c018542030308a08141d502c12070000780c490756500007003040812900c0b03400d100401a40ca07003100e07503050300401c501d920050380500c00401c078042c0700b481d00e402c40381d00604080544000c100003e0040d1201d98111401203945110b0f42c80816512501c2042d094140c0300103440f040307a0100c0300114907076085802808044d8041544200380c0c0d21984030301e13003440410308060500300f0440342da80c1c0c40744c20840381540456071901d00030b40c220300c407401203407000d4255031b03541025610081b0400c00c05070400307841c003a0041103c1a0140009070984240c001a1220318000e40c4c1f02c9102c403e5200710b00e01e005003403c5005d41020b5003040141d030401c400c107a44601000e03001c1c0045061000045001040e548504800302242c018001284096405612 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 936349685 1250 936348435 936348449
    0x3110423180c0d0b03071518050d0f020f0d02150703020f1617030301030507150302070b07080a0e010b06040e060112050c031e160e0303070b011e0806130b180a0c 71
    0x1082a5902095180c010902c94692101e6043d40b001c410381e84142c103508d800b040311411094040ba103401c0450f28030795000b9812a42443c03012640317000e5191111440100342d10890700301c4643d00103640400d035401c0340410607803840306022882c441054001e1005041c015401011142898100c180d61000b40fa0355110300b51400c0d402c07160084c0200030202c2181d040c0d03a00500100444e0781380c451403001c6008440d0101040507030030b00c004000a11404034682c001c140d1641c0d281a541010b5004404440080c802c004c1c00782c0c50050201001d88445040e81e00301c40244e50b0061080d940d24005941554401f09120b00075880c140c200300e0ba00c1100c5010b1800748581e015440d50301d10b4281046514030106031030300e8510401c402038a5540d40c0c451800407a840c8406000d03642464030340d13a9081030401080c2c00282a5003200b241030560307025078401a1000f8101107000348050300f4241c0040180322150036000d0403440810303000541a045084134011014510411551841d880c0e0402d00040c02040c09154 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 936350935 1250 936349685 936349691
    0xa050d060914030705060106260405100b06160611160602031501080403082a040906090f15030f02030304051206070201050a0e15150603130303110423180c0d 69
    0x1074001c2c1000001d0f14050366001c4000c0c84a80d080c40b8042d10481300d0325005615504070248246e45421940b08443d004612401c010034000a9151409098803035000341d150103000c0034040c1000403881c101e01d80140d99042000001c0400050102201501c00d448880d482041250009420085640d000318498100c5109103000200d0ba03c004440d48001a070b4041d00044136030001c00d242c0b44200000e0005445501c000c04c5d0240c50914110400b41c200c1d40c003a10b2a81e0395090200843e48007405201000d0708142c108000c10901050054608101408081c145141c00441c00b401c5442c10811a001740c28010040c8156450042c0d130701e130351044102c425000550030a00801e00701c2c482c0340111410042840702901c1ca1071a07201200460030002040d5901d18010020201c070b103910340300300039801080d201109520718407290a010b801da0301c94800120b000c06081200300104021231001d04c80d02c0f002c1c3d200140c02c030501c000c0090310800040418901d040c0d4510107000807440749600070441c0f464034a50034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 936352185 1250 936350935 936350963
    0x1b01060902040f060305152706120304150302130306231b0d0b04050c0702011403010e1801020d0501091a0d02060a0c0201110a1209050613030305090a050d0609 70
    0xd0350603401a44188400480e51800034003145000703130880e40c2d00c4810110301d02c6607030b401000003a030001121044920a07d0300b04a822807408101841d160340040c01b40c0c0e0035501400c81101c610369030300c40c510035030040b890070311003c544051080d0121101100c03140c000c4c0c0803640d200d0801000811103080c610680701d030030000b002d513100040008584103d8500003034031604902682c404c003182d8820495103203000c0d81c4440c81602c41d40c452107040d020301e04040065441d00c1807480050003a05400d840aa2846000c2c4010400305004100c2c99611480410b02018440d024025490180c000d089200100c141800004645000700342d21981540e14252002021000000c0130320114440ca9000690813602c100070001d1140e000b140d0806115106140030345000c00c0041009080404040b0f007252000304480e03401914640c1310071914054001200c0d981d10f0015a550030f9414010503100041c2400800302c0c00c001c4990764089004002c00014068003410452441c0a400400d49a6004c8a44c2e030041025 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 936353435 1250 936352185 936352199
    0xc02010c08040b0a09020a08210316050d110a11100b06070f05070b070501140115050336030c0f0a020901141f050306040c0e030a111201021b0106 64
    0x11034444400ea038503444901c1c1c94a40f101ea1401c80d000f002a448980c80359007100068039902c950344c0c001c00161b8003402c800078085031030f149103030000c0d007400038004814001c0c4819100781c0903400c2c0f0b50340524102a43d54072080012032000d405a14a190160140441c0070000e141e0044010a14465080c00f52508c10300d0240401e0308580c82c410348507402601c144040310000d8401012a4012406003045941146d0f941008d04d656500c082401c4840365100c10100304800c01c1c00e840035001d4a000c40305203100850307546009146e17000041c44814000c80000c101c07602a00050030041d40401d0314068041c0164a200003160742c0da1094100d440076118001c0c02408024010894011882e40100001e0003a440c0c5400a0b034000b040602c41640080015100421108140d0320303d103001c4155110580c6a01e01301d0b00704011100301c1000c81040c00b2170b45200c0480e9130303400302389822410380c44944030f1a2008140c000c00e801160309040c18180c8d40c8000b5410a140700e07040c441d4107003402039000138017040c1e4552407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 936354685 1250 936353435 936353441
    0x16030906030509032a07080a06051006080406020d0902100c0312020f04051210060e0103120e0f010f14070602040f060315061b0f110a06030506180603070e01090f0c0201 74
    0x80d180b40f8542003442002c580e000004100103c05a100500200b25416070f603c043c100303040d07688a010300380d100418600410901d03004031907100415155003402c00d841c081026009101c010001860030790f0014001d01c85001c1c40d80000c1c111744c1c008c2e204244415181c40701410058200c08143c001c2180020044100040790080f214050300c8400c180e81401e16000503c60740e001110408440c034042c0b20415009d6640a00c940c0c00200b07140100c0c010175515608042e04400c826840034410080c040034100240d0b203d5429618000d031080c80c041904044140c07084404102c0d481030882250000203040007407112940241069541081d026992a556440d0507403c0f200014280080e000503100108207603805140c0c400c0c02040324000525604000e641d400801d502c145008440000f83d2507807009080c00c1c0941e120000e001c550030100322904200c80050545800010300040749100840092000d80b8140000002042c40000c1c00700556140c00c0b41d24050706c40f0101441c0c00c3d82c03404084041300d601c140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 936355935 1250 936354685 936354691
    0x412020f030c1b012001150501050a08011e0b0c010b120a030e06030c0408010f0905070b210a0e0616030b0108060d030806190e09150c0d051902160309060305 69
    0x3a005028441c982051110b40705060f20100e03040c0002e52205071300c0070480d466110001c207403490000810080003458000c0d4056107801c414100f09052101109190300000d901c1d05403810003400c1a03c801e0148891040300d802500500d070070031030100d4980038010341500144000d001c02c444c1e860011800032003180d60703007825050140008500b2010314210b03081c40401140c010020522407417901e515005101e00f5510754902455020769100e8405043c424240300c400040e03c00581907070300d030150180800e007442000c50340c0442c407580d4120104500c010260f20800d0005480c0c000d480c054035001c0c81c1e80d624204a041c5020100c0d08142444240f58454441544620303c01452503216944c681c80c12038100100034070701a0020001110b000b00394003880421401001d501e00208113610b020b09440341080ca1000083c1044441c0c2024401490b00c1d0380103682e4008084000002e840d0740e050a40101c5180300402d60001d1031000810481003400c083c80180064040c3e240c215120b65214070072801c0b00c03c12 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 936357185 1250 936355935 936355957
    0x219080d0e011d191b05091302030708030406090923040b0901110405100305070c140703140703020f13060b07060f0e0a021c0302030f040b0a0207092307170412020f03 73
    0xd04d11900007406050042084090f140d0700c41d0019038440010425583c03041e2803c0088034142c5600a04615040281002138820480510308080c94440c000e40450014020b4051151321880d412100034226075940c00417140390b640881042c245424603580c02081550702030155400d14003a030f0301c0c18a24908640488002400c5000410170040003100101b20141000c010032401000d55804140380609550f640d084e501d0103490020724610781148034030203079002c1071902e41280008001603910300c41e00300c4103030070140d40c0761035150900d00c0401c00800c803940010501c444003141490500045901440c030208290404000b88409080c80c542c0c0d030a46640000c0d480700d0803072801e4040320400e1440318085482401280d0408542480c003080076000740d0400c0d00800400f280c540c04159040000d01c0050131403120820000c20b409106c08a5801003d45030009c07900c0903004522598818404c1482c250b0120a42c2d880700d007040d15204940c80394625226005210f401c086c2200c00102000304c418003024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 936358435 1250 936357185 936357223
    0x8060402060436020307020d09030809010305091c0e120604020f06090f04181704080d0f0c140c030c12030d0b0f03030406090503120301060219080d0e011d 68
    0x1a1451200207001d034030f0f4403d00e05294284005001204400340c59440c503400350000358407482c29050003884d000015540c6010040000c03030800214200c201142c8041d2020301c1c02151907a40c440000307250441a80f122000e1820509841e40540d9100c0c060059048040b603031032000003140102c49030f580d841a1030180d408000c0702c543e0b030168a010f000800140f040a07203410b00007084440020225a50144159143d100800031402046800d501d000181c95060f106241020b080c1f0003402c7c4d03120850240307003051104644007d07280d5405240c070b05034140d1303201950b6081c4010001c0003c1d200c01944201f28020f20411104456500e4010701502e688a191001035041c6405049100042c042d441d0a040d01300c0360b004162802c40c2c03030500040001e0700807610707443c07031141c5810145403501c0c0c0141d4401000340d4060006000044c1e000c0f9001d4403410064030102d44c0303092142011201842400030600c801450103c0341840307010b041d0000210340403c42802c1c0789a6160b41c0e419071f101e540303525240382c3d0054 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 936359685 1250 936358435 936358439
    0x40b2206090c0f0e1f090e070908030304080a170109140601050a050f0d02120906040c05010c0b010e1f090e0c1905010503040611031e13330c08010f080604020604 71
    0xc07050b0084024400000d08058401702e0810441c110b05180c1c09000380002e03030402007848054059a01240c20002c286420080c0d1480e203486140c4a00003c2c00c0240030140c005000309402e4814000760801301c84980e0341d5003455a441d591140180000440b1581d500019400141070703600800c2503507443c1c1400e86403d0325158080c0a06185540b003000c070007440960078041100d010300304004a502c9888080300078400c900703050400c0391245410f5402035040144103001c1c50300003500c8810183c11600c03c6c0002c03800d0b9031141800e04c0d10300391040040222091050100152951558010070341402c0854191000c2d81c42c990180440b001c1055450002d81ca002207040025501c2440215070140c05010001940358206810807039541c815500c1441440b0884141c42c80308030b000c8810f40d000b824000101030400d00c01e6990346400300620001e440b41440000e10060b4440d20b040010130380b107075054801c124101c440c48018207002d40a0207211042d080c0044080741c0300400003000360046800600d402d040c54 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 936360935 1250 936359685 936359687
    0x2030d110d03021c02030c040f0e010609181d1b010804020603040b060a03170307030f1505040c030b06070c0e07020d0203160c120b07030e030711040b040b2206090c0f 73
    0x588003d5010903500102d4107601c13100c00640c070166000350354414030203030380c2c514100350300e001203d55800182d0040180703801088041d801c08a29000c55a50f018006200745c10100014000c103034400384031315100411740c1080401c3c000480c1c49043d1091303647d000303102500007c0c0110742c0f20390f013120000e41008040000c540070501d00c00d001c540c41240203000e000381d140c6a646140c4600340d040c525030106000441840382017074160045801111001004005040d01240f612a1071903f034400ca90085540740241103005103e03800075403035010098542680c0341814500400355445510450626122040103d19007030301c0410340311442c020550045081c0000048801c10340480f07154205c0d10a0307010007002554184d0300f141103583d0360040203c0841071501038000380c00d0368140b58084101390020028500001d01e41c3c1110040d1000c140c600240042c016800304000f044442811680305030305000301903060341d0345040715007070411030507007844419658507050341660020700010001c0f40c000d005c498001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 936362185 1250 936360935 936360937
    0x204060f18021e0c06091c120f2705060a0207081905040312020105181f112215020c0a03021002070306020d06080c0f01080f040f06020f0702030d110d0302 68
    0x21081c401a0341100d400c90310590043c55100d50140802d6030004c008001d0b5001041c0030800004003080c1011694060080c40180b044440080540c10f66540300000e40307403076600b9130241c3e0b0748000031603803001035410466a1304440040c01504640030702c5102c0c0040d01402c854025501055445000581021005d4181c0c07001c0d4041c03c50716100700601800b00001085180308008001121a000050301c0c0c141160141400d07000d20454010560113160400902039040d511100100c4105200094581c00102c100304c0c18851185056030f007000d00d1085041d20807101c924a4111445105003060702104032074182d80300c8401c00e41c01780e8400003d07403080000d82040300318494082d1042c230684416513107a595850803031b0451075035170718002d699140501c1500e108016100d1008801ca44d1801d4800d144000201b10903070007000507040305c2d05480802d04010b0b24204082c00c46074044d4042d9103c91119201c1c0e089500104000e901c00c0c4030b07040414800b240562002ca01450f41e44010300300041034040241c0103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 936363435 1250 936362185 936362197
    0x21209030406210207210813030237110306011e03230d090612050c03130c17011a060c0601050f0d020a03210f020a020d110d06090204060f1802 63
    0x3a0f070b40c0030019040000d4940030407610403c3c2050300501500c1070703041c0092007104010300c2d91840100704490840071917000a100759111104030403400040340441a1801400a10740c4000f0080744071501400400020b4101580000826411510160781c0c0300e40800030404400b100300f27403184101800380041000303094020200440030180e510192510f040451030030f0580200a00040c004520612456902a0722000c40749890700c018422820003541c58401c0e403002903d080000443d10304040104000440d08100901203104c03a00d0601d03a840014602034510705451104003031101081c500300e864801d080c5d07540e51400000410442e030030041070018980c0310001c5690711100310321040c0c0050341e40718401409103105140c000780c20302c007203003d180716400c800804030240196000351070b82c21030380000c9500d106901201c03100c50b0328000d41054201811550034a540261142c1000c0060210580014426601c02e03642081110744d5403c5858000485018000d465503150500144034021a005080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 936364685 1250 936363435 936363497
    0x905090606121e01060507020105030a05060102070503150f070309050a0323180415030b360c03100501080c01031e06150e0906010507030305041410021209030406 71
    0x8a0144a50180300d80440203c90709200503c11a0071a924115280d0580c0d005005074140107082003902d0380080d0007800014840c4031415601c1c00081e5840c0c2c82000800020040607050351900d26507808075030000d010441e0700642e0589107102080041e8428130500e4819500320010f0109420030748d408035204c4104074014400240d294040490b21401100240b00100910b4030440c41c81c1e42d1801404103580308910b4040624a400d88100041541868450f5101d00ca800d00d42c034181d244c03500b51410003280201c102140000e8102405141d1100003844a074000c0c0803070840c4d140401009140d402e6620034040c1d80130b9500400e910118550203600006034260482080d000c43d0070407a03800c03500300c8189074041d60785030907690f0b00007100d9908244003d60004080e84d260303000345044400a00700c2c1c410803100804040da00c000040038462085117005980e03e01100792000c40c1103030164200650030896401400120000c0410045032000086500b1100035489441d03160400e070340140c035103d00e522580c01c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 936365935 1250 936364685 936364687
    0x120203060103151401020c190605030403020f01051815010312050c030409090303140a02070b070c080705160611031914040b03072118260c01050121030905090606 71
    0xa00100030901080090000d005000c0808042c0d00002403400c100c7d0244035000d03010b034200b8241c0c4003060601850903030f01e0a040290f502e031250300e0200e1400500301d000a925500c1c24042c056942c03843d00314000c503460010f0031595a036200c54005d02140c4800c2c03100070540880400036580140c061400350604e000c84500341c0e8141952110400151001210102d00096584482d0b00d465800081c01ca0340050601208605008581d81c854192007070140500c4180306518143c4010841401b04407610b5030740c08016a03e03280d045202211800c545400b5510200d800b001200c2d40720b04000055440f480d00340c400c10b20120b4a4400d096070076152041000148001c10031001c581c44041f81e00850040c0100d80e9040c0d28120060f801c49004581c0e5000352802c00e0414245c10b8121b41408007120b40d16400003034440c1900452122400038000c001b03003c144612012818040da0751044d40034034100c505603200004210711018180b2002100c0250040228105010510150500201840c0d020308050100307 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 936367185 1250 936365935 936365951
    0x30524090702031e2d070201120608010f05070806030a030c0f0503121005010f0e030d030b0328060b090c030f09010605060c0f012403020f03030d051e010e0403120203060103 76
    0x14104d11515400100280b00c00011490092800c04d808800d2282002c4003072107071141a090195964810541c0280c108550051180417a44a80d4007980c01044450020030000c10807900002c090001220700704003184a00d0000f811604002c83c0d154001d65066540c042d40d262a903480030b52034811204141c500c2d10044c4084e61700c41d95040c000501502c0500584000b05103408001072041070442e03429020044540404110ba03140043c5003155985581404600038100d038011070701c2c040e84000703018103d074040101c000c80d42042c1e11036041d00e0740c0500f000b88080c00245043c88200305040c0d50034400075100708005141071869081c85600501d460001003481c50703036100000d006412503010140b15402562100c04960802d01c11083c081d5405201c44000500ca4048121000d45e503100280c0a2030707500c14400c0e100c1d50103100300c81074034120103400c0086080440340607608080e10100440400b5521001203400038400305254419685070355480308401d0881b454101079000034211505241d00c42f038007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 936368435 1250 936367185 936367207
    0x20405150d151e050414070f0c08031003111906111c270b0307050a031b0c120305090a110f15133c17060703052409070203 54
    0x103800100000f0003010354454007030240c002c1c03da401d507101d03d100368a805c0190180128070010107a1044007401c04901001103d402990000955100184613800000c10001709419140d03005040d04e000c0c400307028101030303074405010380340190310383e0503000b0000b0001c10030266204c0c0e18800c1d507401e90101569510b52080c880d15081448c01c44081021800080c1c00e618014401003081d41144114500203511a1404022403001d2101a01c0b82c8208100080c0604a05010790450303410f040d5038410400c107a1440400080008406500845000c4098240c4210b0b0a21a000c1c907401140048041c14440710799070744403c0315407400c0b5181078220f000300b00b11840343d642d09680e46480c1c0307690b00038803a503403050320741c03541003403442a0410074040d0610001c09401625241c083d0600452001240301c1c0010303040c042100b6030b00c160303200903082440c1c02c3c104001000040390a601600050314140300c41d03205c0011403c2c440c0e41043d00690358540700100121640340401126070030419900559142c0690124 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 936369685 1250 936368435 936368471
    0x50604170d050c091f0f050a02030c07090e0c12070e06150c01050906011d0a0203040519060c02282d0b011d01030f0303020904110705150604020405150d 67
    0x80d88070b030302c98400b15030f00c013650401c0d2a03000f0301e134869815258200b0250400103003820000707070039600c1005004903850703e441b0700810441e00d40b101c0503001c40c0c00303280e0754074003510241c030110f40801c0090041c1c42501529051600c031151a413110500540149800c15441c480c0d42d00b00141060b034051031000e203020201c0e0401d402416102c0c01040041120302e00034007002d18144040e4000190720050302114030500070b0000c407581d003005c01c025000d60b0301d888038240145080781003a070311001d14204400d118100701407a40300d400b06100907002e46014569030a83c40d1066449200c0140c5a9202c056070040040da01c2c2001e5241c0740c261640c0ca80800c8c0a1561303484880c0018039048924415260050005000009203031408080c403072840c03001581907540b041a06004200001d084c1a000701d8a101e041da5150003c103101401e00e9070345901d5000c0350501c29a6138030311800b01c03580c01b929040481c03694107042c004c5400b91030b0f0142c600560f810f8601e002d115960310801883d03400c5940c0700f00740c030304003540c601c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 936370935 1250 936369685 936369691
    0xe0a05040602091804200d030507050c1c0b0c09010e0f040f060f1d0c071203060803031e071404050d05253308062101050114010507050604170d05 64
    0x2800c850748138a064078110b9134400d50980240c4014044011b8030f10980c0d01c00101310301080e8580303042a21a45185452841e003480141f0b6581d010891104850109111600402102d4000e0300c02106589940240c1d030b107a07200702656140019020100144a818441001400e080c80a44001454240c00c102d60048030300503005180c4d00013a4000404c146180b01c00d00c426480e049414002941c104004410307414030800d98024026035041d5003046149010b903200c1c00060140e2070649a1b60b181c400c4440031000c540c00d505800d1001408080b0320064440e0108160301040702c052541742a003000100106680b0740c02d41126148500c8110410601d12810200710071010684a2b070312060402d110764500e600c1d682a151007003039981420103c10790701000340c1d55010149090031092519850f010507400390300b8444c0202501e43e07010300540c11600551266040350043c03031000840402980045403144036007103024203c2d0b4440e002160200e00c811070660081c80400111610341210806503e0542d4012 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 936372185 1250 936370935 936370969
    0x5070807150e0c03010b0a0611100e0a0209160e1e0a23090c030f0601030603060c090504110c0a230f01200c1b01180e061305010e0a0504060209 63
    0x20b8a080b8600710740c1040308203e10074003100284112101034021607d10aa03034414034007007090210391414407102c10301484440080b00c04043c0000f00b1500703d0140d03240d5551004038040d078046800140d85441030a10002d00141507510202c07664885c004002500414009071500410b181d04c480b14240d803800080c1c002006100d000307419410b0010f516500240d50300f0f0115001e910390314100318005d81140201c80d84245844425411510345000480041206800c01040945490080c5100c250092103070001c85404440c140b02101400e403510f1028000c44410109950100c0c52210024801c0000b40a01440140c01600b042001c1e2440500e440c04070805100c00340d5507100b0b543d194540900705881241c840350301061030304d038840702c42c5942c503240701c030a1031805250318070250010fa00c1841d200d4a121082c514284203a83c48195001860401b030301c000303205211403041a80349070158003515049596900846080d07544408201001e03000007401110704503070030403424980350740d01082500721042ca = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 936373435 1250 936372185 936372191
    0x1803050705030d0e010503041707020d1406180a140114070504030c05011b0b1b0c0102302701060b0d0b01020f030f09120a03210b0a05010507080715 65
    0x41c20701810305003400c42891508205481c02101e4190340c000c41100d410a41c04450000c2c05c100000d00c514540c0600000258061140c01c052800d0081c039172013845542000718142c0b240e43e1110039822030680400b411017051a0001c02410703001c1543d42d41e82c0841a006003000bc1208030781c01215402c180c0040358058081a400f150074018030214900311005003500782010fa10381406c859420482e6110840c0040c030301d098880000d54110702c440b404881d00d0050069441d00e40c5c81e1004503d010390030108150414100c0802e0540c070f14013039402079104440c26440303922034588518541200700084204e03802c400003949000400e944c0c0c0300740b04000082079141c48054450b102905c2c0b078030580c2d085c0c3c050213045501c0382201150280c80070041750001ca61120007142e070396465074080350002c0071041c41d11030240181c42100e800d1642186900c079002000850031030a2800c0a2040421500d10003a06500700c26850014041540142e00504c0d40b940078200c42400c25180d90b45900d84201403404150702261 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 936374685 1250 936373435 936373439
    0xa1e050a09120906090e041104060b0406030b011b020d03140304081b06250311041706100e0708040204091209050909010e1504110603010b181005070b0718030507 71
    0x15900440b19801c1d0062900020243c6460b10041a0801c140580808103000402180812816050842c4855806071091003555590034078002c07650400d20510004c80e060043c51141588207040c0121900c000e080401c0b41c0860907000d01100d10041d11049050180c1004111318502c402009541314a1081c2d800a665602c031006910300c0000101020400390700103411311034946440b4000c92903a0a806031480c2164086c01422809458503001c02a41c0c070b1030000f03000c641000414a21903200c2e10050403510141c952883d22840309a00744500141d240196000c500454461603030f00b504940010400700d4842002e446030003103040c01007424004103c090204010b2410142c0c90380c0e0b44401c50344c008100c022500c07090292283d541e10000b90100408000050800000500c0191000809041d054403507844011070800350344024a81c0c0303080c2000000c031078017a19050302c03180702d0a0b01c01c0d51902e0134a02640e43d05100f07004090104400e01c6450003220000b10f10a0300d12200071400b079030003400024 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 936375935 1250 936374685 936374693
    0x6020a060b033f030103051b0f060703051911070303030203072607020f0d020a0f0804030b0123101b020d0b1501080c030103110907030618020a110f060a1e050a09 71
    0x401c1c0d0443c1c108030405100410200d01e01241e1079001001e901d806807800c070302150000700501c451400550303000b440480c07404140f581c01400340c0400b104c0010b11140b0480d1011003503564405411010fa01980446002d00002e8880e0700516009003680c1800c0b8050b2014101080510f5440081d0103d400e404108000d0700035410480d85a03030955042c094044503d00c0c8800948803e0141e00c0900103490103d880c00030890210100e0b00110342080e200c0721a075864000030741c91000704100000130032404084051251400040032290109241ca98104a4410003070901d0480c030a10701c280e900603484000701004c10a106003551048006130a0908100007010024084000c09005182d41a0081c0014400500c00c00e02c0400b20b03100840720b0412665598900310040c10b000e410640c3c1e58805070a0a620a010907000703000b44050980f5028511050b4024050751380c4000c00f6181c106a1044001c42c1c8801d400754402d28180307030b02115440ca52a803541c01c1c4001c0d200151421401d10ba501c0d07650400784 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 936377185 1250 936375935 936376033
    0x105130b0714030a0b01020307150902011409011706240301080106090501030f0206030912160b01060f090b0c190528030903060c05040302181b0406020a060b03 70
    0x100303509042c00d0041d5030000140c15031501000303113034280c440e64445001107941e0003081594081c44d0b010342c1c051541030810004001415650b0000ca000c1901d13902b1111207126000151a02400180e686402d40f8103804054aa030401c0038003e1504001c0340c50900307901504081c0404814002c00c105541d03213501d00901642110038662050010350f00d460b00500009050040144034960125505501c135201d245201d410400320400304148042c0c00140d03036030307a050050805840342c3e0041030070901907a41d884d019500c2c401d10840e003c001030702c1e0040520440140d4030103041c560b81201c00302c8035165250403003107901c205c11080584542d0312104083c901a03101d014001540c0640d460301c40701d01e80303281d60041c040308080d0100500c510f85405c0395142d92442401511700564006150966004401203c5480f244c03050314017605206000711890030500342a42100c0c2252402c4d0b00403d0640c10a031100c0303001b88100c0d460b09505014a000b40703010301e0118101040c1422207440354189158003400f581200c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 936378435 1250 936377185 936377191
    0x1c0303090b130201050904020a0509060c0c011205060f04090305040f0605040905070c1a0a090b010b0d050703020c0d0509150a02030d060e13020f0a05121005180304030210110105130b 80
    0x102d4400c044802c00180da100c0c05070341c15150141c1c0c01507218483e64405468500070f4415050b04104003080c220320701c03080040c81c548008000e03214400c640518042150599204031000740d040b6081700d401d040241007e51040c0c0441c1d00900d801c50500d1780799500e989d1250f03020382c4500700054000c502803201400034414580c021131a400c0039802c0790241d40d124a1002074900190100e0444400042d46000d85030700602122a0301152044c541e60b11070940d00600d41201140400080c9481c0004002d40d000384201c8040c04c85200050403081402ca20481da070341d000d042c406801c00341600c801810390600e400502201c86803500030f1500c60301451a040c1c1118407aa100610f0000c0c500e00b805100c5032800d1840021a8041d03caa614400c409404207071100c0e521b601c2181c001c07030540f1240c00e002d040890784141c110100101444240c440c0502c1c0c0d0f900400b82c00000d07046800c100410001441c00703500d140402e9000742401e4a4040074625510f0071201d00304c46001907580150010300c10401c250300a130768 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 936379685 1250 936378435 936378451
    0xf010f0b01030605030d02070e0c160b0115090b04050409020d020a09270309060503130b0c090a080106030c15020a0f031e111f180c08062d061c0303090b 67
    0x20343d01b03c51400003035450b007043c4a0200c40b11244000b2500c01e52903103040300c0411204845108180c1c1003450320310300d0f00c0e03c24481c240040083c150390000e4035125404120440e0100c4420300d082500307250400008054107902241c0c0710030645201c0f00181c9810003030100501d0b0903000081d0400da0305041424050310440c61911101024107003000294112200e6000e99007103103440d640b02d0f50307103880e0440c0400ca4080081c0c1313082c103910700f0000c035900c042008006400040d00d010030803950b180100350980e00d440c000100800d1840600744034002400c951a4150304d070f03d1040703c0a404041d2501801021049000d0b4002552480042003456206d0049209107e1529059103840f17028414292104144074039600c030004d44c00030000707541c500ca8000031500720061001c6143e095440c60408072081080c072074081d050180b04c001a840e010100c00c135040c488030003104007400d01855940c0b240d6510f0000d050550044c0904154200036801d4110710102d00d2090710000703240760b0103041c804c042c0c0078001c100403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 936380935 1250 936379685 936379693
    0x30b090a02010f2118050f210a0203070f0314121b121308040b0406050405130c0207060e060f0d0c0e0319030818060c04060e030601030c050f01020f010f0b0103060503 73
    0x4104113a0342e8480c0b90581107203c00003007221807a0034420f65403001e280c0c041d02502c0f5443e1607205044001c900c0c00c0b00e040c200800300126451840303c0710400d006030306480c1e016810600108000c00c10105905107030384c2c071a1400e1010005031002501c10b5400c107902c1c20320b180c5a08000c000c689007001c0c54200040301969040750501106101504040c1f0006140c02c00704007044a8402c00c00103014240e40107403200400840d1030329111640240550014401c881c0b00390000b0005241c003000394071540411061541c058003600341410b000b903d20900743c101654105000f04401240442100040c14400702880300c041156017203d00300808001582252a1003500002e0303030425100244442c00002c02e0341420060416640c00c3c0701c004000694142181d034074042d41042100b07034004840208142c85c86500d42c40310749918102490b42d1000240030082600103011000c0c4002d280041071140c40c0d22052045400034207c6000c49800d454504044484036911214540e88a40e014040d001c09808194014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 936382185 1250 936380935 936380957
    0x1011070b0f090d0f02030304120b0f151512040609690b0705040501020c0114070203010f1a062a070807060504140f1305090304030b090a02010f 63
    0x80d80c280716a203001031080f040c1480480070043c0c066644908160002e00f640d0712240e0714001d18415101c0f02100702d50084d00030b40084c83e048010001c05000700444070b4005d0046190005100c00311400d40b01c442c44410b014860b5007034007000009041e00c150f01c13036030021070007190078a0302c21001c21511400c907007119035000720b07140d0303030084003211070065210341c01e4505065110040d564107129408850840140d01c0ca42d1552030424403001d510002d9208040d001d0345562020001c0781c490080f40074050050b000b500d0035121310b62092402075111542d118106290880d164000303801c403080b001d107c1821549402c0f1141c0c41c245001069031143c4400e82c0c0c1907180040440780340c0c5498184002c8070700000124103001c19414020441d02014003451070490707020f580c4400d00509250010722502502100c07030300540e02103060039503618040482c082c00d040038a2040c0e0074000003410005002003010311013440000041621046c500c1d0050721a03001502e01c40c505030000401d032000c944018801e00c5896004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 936383435 1250 936382185 936382207
    0x110d020a0203091c0b06040c0309080403051507090f26060a2a23040f0b070516030b06130f0609090213060509010e0604140403020c09070e030304180b1011070b 70
    0x490303540030104480004071102c0d0388ca07081e801000f0800000e0400c0c40049004020410700103042c8910102c06a030603910b55403089022100e00c8114095240803080c0b552080103e035a059039020f0350084c40301582800c80c400079034420b1406404582d40c1940c03640b03c0303044a4070f0320105103210000703902c05880c841c0704591501001c0e194404454807a0b882800e429072458118a4440a5a02a11740082c5000841c0e540d034030390780710b00c1e0000322054915002b41c140321a603449000d2450340031254480000446591514100950007040c950a590741750f80b580010f501800c818445c0c2805030429080001c0c2901d0306005100c0248c41401d88a00010300d07100041c03110341e54582220b0704495a0710184141380d80c40ca0b002c10080c1c414203c2c03e81c40d0194041c240410590042094101200709590300082c0780e9403038030300300d03000c8068101c241e0b09600104414402e2070290344140c2800d0b039482d18003050440010000c1a00220700f01032420018844100e6222008000d000060051442003509420040c01e194 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 936384685 1250 936383435 936383453
    0x180f06040e0d080405030409091a01050603102102100f030f06050102071703040b0301180c081b0703020f0a06021201270f1d060a0605091603110d020a0203091c 70
    0x2140c2c1c818010b0b6039000804000b07041040320003510000302e06120f03c40007440c0c0454095450b42c000f0070801a5140081350900b80482981e20034070b101d10406078030740d240082e40000c84a00700030f010860b0b40321041100c00b58440744010304115015036034010b0080380144008085603104182a0130b000c0c03c0220401030beaa0000f4103000b03171001c440c00a080c3c1d1a00c140b82601c5c2d445079030301c070181d01c81c0b000c0700008051706014080c104c5a09103031130500c2101d800d0401240d84880c2180d42141841d16010080f42d000c81c84d40150803490300c41c0c0100d81c40546003000d903d10b00503040b0012982c0355000034180a401e2240484a8010021400203032109203214000c42c00c2c3c0c610003802c6103501540c407000e002c0c00d2201900306108010104154182c603510408515444200031a1500c85080c180700e130005140c1080821144035101604070022024115007040b809094801d00c6081c04200a01898001038440d01c020901c3c074038a9001159940b01c460107011200c0c020140c2c950040a9600c190004102816 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 936385935 1250 936384685 936384703
    0xf0907110114090c15070b10060f0503090604113114093007030309050f0a02060d0f1b02060403031b080a05060604080a0c23060a1b02180f06040e 64
    0xb982c4001e440b00413005c2013000d0003a040094140b070000c40c144070b14403200c4504201500c0d0706070344034000d2812203c001d5a4910040e1041341c4554031420000d40418103400003081d40340c1c001040050198483c0e2035211404010016803142e080400d44103425071a182d10401d80d506c0c003c0c80790519580340c004e14150302c90001c3c00580c20100074200402c400c40403600080030014907961046030700e540090034000e00800403041c080310180302d044088110688000790b5410025402012149000c05605074400030300480541b1410a9072034140005c0880c41000501c050000f50f6802000d8514081c10010280c50401e4103560000d8902e41001382c00c10350084520b0f603c604004400701d003680750140455003a201d03581c454902c600402418000f04054140c44504646140c400c041004804011030100010380c1a0315643c000da04111040d0a98040c0150701c2140c1c84c00c01450b51400a00e03008103412a500210101c1d414a000080248000003d0081504060180c90411004401140c2956288014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 936387185 1250 936385935 936385939
    0x5181c0c020102010b040c050a031a2202070f1b09060303050a0809150a02070506060f06090904060f0f020409180201022107051c020601081606030b0f0907110114090c 73
    0x4501040c0669000750000d100c5038a000e4402c102c0d201182400074240e80110b00a60f001074103008940840f0489480e003074100300d1008104440e400d548c0e100c0e10062100750060b020491f42c01380500d401103090b54210801c054000c00e41c0369100e0354081ca0303000c81c2442c1c6410042d196854030380180003096002c41030b504540700e035040140d299115030f1b0a01d071401e40e50b01804040c42c001d000402c4a4181507401403d46907104000300d0782d043d2611010080c195902403027185c1c11400c140550141c500d40070390720380d0700240034000025002040401010503280361f00100140107400103420070078051103200b40d80501a051440c1d008166661380001e40f118224484d818504c0514031929280c0c001d61030883e035802c0e903c102198407100c4089010090000d23130007140405406032800000c1c2c140c40100d03c90301b60140105c0c40c0264182040019002024100c0540e600846240c0c45c1c2c18081c3c444a0b0f1072801000e6a403240821103031101e54242c04d5854a000c00c00403804443d040c040a401c002403000b10070201 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 936388435 1250 936387185 936387197
    0x3050c040e0120131205151803030c070b010b070c0306231005090c131511160e06010e0901050d0305070209161709101512050105181c 59
    0x20401040e026090030000c441c45043c45040508000c0707454401040b252400c01d48803002550b4468002c040c0280403900601283c00101c001c495240011002039031142004085842400c20052290707e150400c456803090040002801c40a0007089485c3d00e00400f00030803414508038442c1c0e24040c0d81c61091000820860301e400c82c1d8540c45884910f841c980b01103d102c0581680341c51023129811134521720a450148a070400410f00300d01980c422183d80d4211901d100e19114942800d0341403941d99013038241c0400c01c1c5d9000c9e001030f000081c448001001d280460032825641001c00b011088503010b03100724140302200312644c0058030303070a0315981111030480b000483e00c411400c060302e45100340440290710170206001c111904801c00b10040c03044803136a4881c2511035000006444884007030340c801202d948003180035201d0042c1904104e42e00a11000c0d0040680d9481052480d0f2000c09403045a980e5103803000c02482d07090747c0304030940c40c070700c64002450a11a14a000d45003015200502010444 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 936389685 1250 936388435 936388451
    0x11032802011233060509061804060e01061e050306100c060f02030f043f0e060307120b0f090105060d0e0a030f030f090209070e03101a0a06050403050c04 67
    0xa09510540c0d1020103440c0c0f07000740e00c1c0d4200040b001041d801c409038408010081010540b5407055003998607441e40944000e1601e8002501c10481e02106903000350300544a00000ca8a03698004841e4020316140c0c85201c505d1911404040380001c8a01503141045002d00c2001115501c50400c0203c9034214100031200c41c459040c040042c011090241d0440ca0002091190901d01003102610407805080000021300030800884030006240d038102806080001d900800b254012211440d4441d8500704201080c00d5440881d4240d0422140240498007001c0e01c08840c4986004d0440580ba08481c103103c1c10103480700186a140060007214003441000c1120184c4420b02e90103800c00302010000c80d01c084100c1e180080181440e20001c0002905052054503603000500510105590052400f8059030b2000d2003107840840c4141d0459044c441e40821456201c0c9500c505000d00726004480d426041d2020140075078000554440750030081d0805c02040824008251044c501c1e030111b8022030141 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 936390935 1250 936389685 936389717
    0x40207060e01050709030203071e170114090f070b030609011a16060b0f1807082d091203040b01050402070807021009030605090a02060906030a14041103280201 70
    0x2607000098819803070b00c024040f0b21504480722038100d0f80700f101103c60403a258401604410702d01604018a6400a8002d110642050034640d98844921000040f460324001c80340c1c0144609980f00f204a401c001500c405c80c1e0000d01c480710143c0a403490840c910705111020a000d030005205d00300c0c190a82010754401c0d040041c04841005c4101c1d07504464500140c2000300040000c0301c10030344200c0400c41d10101c0f9043c400740710074420030b811240f41100d60b12082e055421150080010b4984510742ca148000c4510718404803080888640940c01145042410320f880e01012280d0700c504940e040c0200300028500b00115415506c4c245c8000d40c40354540c2c6403c0c046030090220081d407101e0842c04000d01190300c00084021a80550300038006601c0c0d140710305031644902c40c8042d400440801550703001e814003800642d005051407500060001c005141104807020581c0c04480c1c5500c0c0207a221181d1800700895500d80103006070005881c4014040c00b0154030509400034103110954051010304 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 936392185 1250 936390935 936390941
    0x50406062a0c0b0d06060c030c060b010918060812030903160314030403080601090b090f0d0c033002060601212403030912030203160c121101110c06040504020706 71
    0x1d540049041001034030b4030100009904107810401d441843d2190000d0700c00c0c45207504c43c2480b03425444004190a0360344413a8068200481024140314144400280c40300c0c2d100b4406200d100040c10005100e401c011b8503a0078803043e900d04598442c1c0600c01d00c80c401c1408822280c000342007515020190405250541301c03080080450111080040108004d140e00010520f00c40e010036078507001541e8640402d011a4060001b42981200003a43c00400c64144a1030355042140100c0c0c440c0d5030bc1e96070f40d03242c4410051000c041310f0400105604070900d90921501040002400e001624080c41c001000901c0138170b840420700d410140c600152120180c00780c1c88507030301340c800e10070102010704154590894105903100440c0000c1e110340c4006076030640c0309034408442d1362540c0a14608141a101409004107002095900080480e00040c001205407400303a02c15201d40c201824030302400f00090035184940d0110200c42e0040c0001d100140d585a0440d8180d401c100c40040e200c1540382404d00c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 936393435 1250 936392185 936392267
    0xe09010905060f06121f0b060702060703030608210f0304060f0c030b240a05070201091502010c030b0f0a09050703200d06080f19140d0e0a05040606 65
    0x114058041400400114205000c0c403541095542d040c035841d094105e65641c81500c5a1111891409000d0444242e0140c221507000c9000400160508029800051040e88000b40c21000329550380f0007002524024400928481e08004078409c2c000e044621881f82c80c40341e40c8108a0921001001604100e41c5610285118007401c1041052000085001d4011300a01c046684180c507a80742d219810034181e619405080b9050100b0750030728880c9001500c13541c0200c481203060103100390000c01d00c00080d13000c03820702e003200b0b60003c2116502e0702000b404450740a800c2501440d86606a00907907182c840880d0300f21200c603000011f1a50310000210010884110010301c104174005c6001c0b1401a408060244101192001c01032580e41d188410380e58803000e2074035160781d0005a8090030f00e2054140000c0850b005030b41d00080487c01544450601c0017514910001c0b600180c2c0d103071914103004459401801056a040084900700320014100280f1200d03451140700300f00843c04151a082100011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 936394685 1250 936393435 936393443
    0x50a020123070f0506061507060c051209060609070c1e210203030108060a0227010c170a0e03011a0d020d060912260601180e0a240f0e090109 62
    0x180395911443e012900b036080d01c3e002c0e1591301c40c40010515a1070184420b0181c8040c000c0840d180028607941c49029109003a0b182e07052090a11002c0450302c84020414400c40c1144040c04642c500102040301e0220040c015000f00800090b11000146180580310384442055040018140a0b07103458100d50b107802d0910300301d64420002c180b070002d4001003c0c5040e01c0f1640151142d43d40c651100c40201e020703483c800f040b180a0403200c0c0c0c0d01c03001c0c10403041d00140b4041c544030068501a031030f009404001c4019a003204000080c40c69010750303001c2e840c0307081550210000d004680c0b070f01200e0300c00b4145d400b4040c3c0c03141d0205020642159180308104068980c842018030144ca450704080050003c0c3c01c40d14030210305a601c001c1001f003140a0708640e40c200110001680e51140001101c80342c2c0e9011000c480e04030402004a0300c0c402d00c8610901c511074003000410805038110030f444c0c1b0281481082082c1c181801c0c41400100001c80d001c0e02a190840c600048680c3c0e03030f0442d10b0140c070300310030060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 936395935 1250 936394685 936394687
    0x1009052706010f0627080d0e0f0d1401020906070c1403010e070521010c0201020301030b0a15170c0d080307030e010b150c1c032306010c1e1a09120304050a020123 71
    0x240007400442d59008440d95501c0c8d98451459400a001414840c10090b90340903140903140c80008080c14840003255040000040c2041c2c0c1c0038002c25019803015400755a010200502007080d5000b07401c2204440c5810340082c020100364084456880616008042c803440e0544904d1000155204140c010484140028800b500e80350001a000b58420701060f80d45011800c000342c1000c010340580d45610015902c12480c0398a030402012003c180b62a00540c02d01443c540e050b1b0565034503c41c000c030b442c0036500c81c0790b40c2e0030201f0700030702252107081180640340d0409100c18007683d03841c01c0d4403440c01c06032020260359425203038505040078815540c0c0c2503180c0e0982c05a05180350b06500000d40c42110380e0b404807400061210a50420104507502c85c0042d03444032200c0c1c001014103401c400c000d0251440043c1c030304920340e91203551894000d444141c81a40408008030000d00b0071400c80d24130201801c00b07195080c9600e071161030b41201d01d0041e0601415507a4900b03010030381e000391000041608001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 936397185 1250 936395935 936395939
    0x151503091109090c0a090203010f060207030b01051c0501090c1e06080f06031e07080c09090307060b03071a03090607090501140c07051e09070302031e1009052706010f0627 75
    0x100000d400c280282b522007108210049a0103000281040c1900e804c420741140ca68a0b140802a5540c01000410000604c81c484040051024002c20306420320400c0b01c003a48605041e1088601c200075601500300403944c0030200541c507002000c4540141070800d00e442c45690b08000b1910348041c000d03e9016142c00c1a40355202000040b403410300303441d6040140c2e10100015000c00c10700800560304400241c00c1045074000161141d44402c09050002d0159401140c1e0b440750051298003803902c0715038418000042040c4072005000c4958001018188220b68070b09110008003180781d02c80714103016481c0010004204a03040007407100030280144490f002e100e10111000b07000d076071298031901603034030342c0b000c914024064001d0b24801e840303600b00ca034180f00e03644030030354449070300078000000c40310703000e100410a0641c50240f10f00c00d010b400e00720320002c40b04c240c40b0211008031440e00340564102c0001441100b4400c080302c01195803516190810a58541410101c84100c1c4000c10704601070181c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 936398435 1250 936397185 936397199
    0x6090506040f1101300902100903020405010906030f020d263a0209040f020a0507021305070f0807030b030a151103011422151503091109090c0a 63
    0x52203010380d115082d425410120341c001034074117010b02c5240075199801400b500d0b07819000d0000004c03004e03205000c04282540c00340c002c24002c5039060035000001304075800510941c01c0c079020300d900500044004100707031861516000702c52100c0c0d00c00244151a8240780d581848005245100e600d40017a402103060140c0c000100090340c4914512040340c4440800d403540307049100700417020500c00b0862250042e0460000302d00940c0507020441d4020b9890720361261400d00d030300c0076000201c3c041c0c580656404280c0100281008006040d0b05d5031030800041042c5603078071243d100d0404c00c2071309080286841e060001ea018200360f500082c2c05104000f00d00040c04800d0482c160a008201c5040040007440d841c0101240b0090051407a0f14101c00c0c200c1082e8108160a107803141400c801001001107011103072819501a0602c00024441c600002d1040302da42501a4a154015003410081013046580388002d111600c0a414880d02c0a20f0004001c44030511101c464841c00800041c040d6441e008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 936399685 1250 936398435 936398453
    0x20a05040b03131104050603070b0a03060b030c0a03151421010203270a020105031305010204052110020a1b060f020c16050603040b0c18041e110301210609050604 71
    0x200365401913400c440240141841e00c1040e00800001c0c0152005a052690002059021a8241c420195140b0001581d081c0510145000345011402c481e03541c54071400080507038802c045030f44070f217a030100c50800400701c444402180c02e910a4030060394160300000d180044054020345035480b54000802c000da07244009040104000c110200301161160b143c0c14070b607582a04c420000e02050080010800100810300c2c3c0d010528406d0b0009840c0c1030300c8401142c4038a5080d50415225030704110058900c40041c00244080a034100c0c00314103101d040c3c1d00c002c042804140c640444003076040c2d01c940c20f22265070410f012481c0321010075542d86030452202d40d5504c0504c00401c00600b0580c3d40800c0703500c0d14108a81c062074000400f0320700ea40f25a0391101041d80f128107c08035100109103101b503103841d00d000d030742d001505080b880d42c060354580d0081020342c4c84449080e0301446003080148080c0481d81c210310709a03a98002d01440b01926490310b14010160031001816603c10385003048100044a4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 936400935 1250 936399685 936399721
    0x509100c02131e02090406051012111305040213030b07050403020a050904030c12260a0b010905100f0e0915030d020c090112030c0c090f0605120709020a05040b03 71
    0x188180b40c2d0619001010300c21141c040882c2c603025520040b22801d001e8258015000c000c3c402040094840c0c4d0320000501031180002c80c0c400440c207100180300100c4494820309004c3c40c4407a6810385404c01b0880c9070200107001c0d01a4034850760f404600303070b800742c500320802c00d024681c80240701e901f50500d400064020341051000324424020403078082082e09002050f03500907545909d5409402c5021355444100000d024070003410094bd80103448a900c500291203889840d291210b01c0f103a00303020403407000760b40d947d0118606000300e6010130041c6880308040d0910400740c80c03400302100c082050003119200aa00303180b550150707640083c040c0c110002d5500c95400e50086040301c41003c1c00040a030b8480c0c0c0c1c42c010240e800f003940c500412004001c40700741c0c0340c1d40c1c2c4203241040144d402c0d50340c1c034000d42c07003180c00116906946030300d104070022161003482e01400c405c40c0c809540141d6410303c6580d1708258080c13503034016004244818014020001da401410102d03218a840b458084c0b19181030b01c03009 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 936402185 1250 936400935 936400939
    0xb0c0c0109170c0c01030e03030c0306060705100506041a1030150f030804030b0c09060307030605030721082505060601170c07170c010c031407080702100506010509100c02 75
    0x80c25013041035800b0b40324242d061801f0344040c504545d40d4034841034075030300020302668000c0010000706000800c01e015088061082d00000950b905080003440b0443c2e1304e40e210130b01918000c81d05542641e5a101505503461b445240071000001c0445100c400c4c606107024035440f030104a4561003200000e41c000306841c0b1aa50040c442081d030319960f400c203842c01d1780700142040008010074804030b00c01136541070b8002149080325203054651801304203164070445030680020341d201c101744403501e401d0105100400603185690098107180c140110b0744110214000c104110000302c819a00148010500103240800c0d0854244103580c20f0039504c40404071130450004000c0c003503002d4903000540c40f10b406000e4410303890b42042420383c0c0c0c2c400e01c615410701c10405101d0600901048003024012090306121540c0e01140562524114003071400028007504c040c8800c110810500e21b900107140804495030540100d22070702c84800503611032207503000e1150411403281e003100c031840d0013805a0740b5851003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 936403435 1250 936402185 936402193
    0xd02010e12251809170d0f060b0a020d03090501060807080609060f010b0f0d09060509030a080604110a1b02041b080702010b012309090f070f0305040b0c0c0109170c 72
    0x55100e407090702e5a901070704007100039a0f8034612070440030f40c1c0310791201c500c42e5103034590040c1c0b0351403900e805404c07003020340211617145e03082c0c804020920300034071000745001d1042c58101105c0d10b0300652208542030702d003010140d03074580305002e004094204a0003481c80c0e105403034410341c55180e55034071140f00720390740a058400c0c0300c007045006001c1c80c0c82d181280c0310000e20314103000100b0400742031135100380e01c0c99441c0303900d600311100450014417400340150300d9400115a2a5a0300030080c10550700107110303600c80c0b46402144511031881e40c02320b581c0c40140c0d1410401c11000b004024046c01c015003406034000d40391101c90001840e0b440c0c00d0310401e050356101c040301790750380050490036942c076103252900141000707904109001031310704080d080181c2084042e0415010501140b40e460044402d01c03040c1d00c0000c00d100c04a5001740c0810b0003e0001c1c50140054541501c54100d4244041d1903400320342c9001a19816480c000c0d40841c2c2216407209074140201550000b543c07081d0401d404441042c02 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 936404685 1250 936403435 936403483
    0x1090b12010b21010b13052a04120312050123060f090609150c07050a05030c030a1403070f0606030221120f160303090b0c0a0806130608070b0d110c0c0d02010e12 71
    0x803901d2150008507a0780700e039049c07a0030704200c04040321b101c01c100300701c0c00e006100800f112503104074040c682c040c0039414550130102205280c0000d02e001c071075400030f02964041004d00c214401038801c5a00c61030080d10815582c44442000c1107411108200396040d0b64808a02d40380c0e4903c01141d000d045400440d440c894181d229410160ac0f0301070003101d917074164001040600025400344100c900c0f0301c50441541c1c10300600d81c82d29103c071940d0040c21910655140010300c114613001010000d0398100040050b030481302d10f48841d07901c60080745c1c0c140d41d2031004541080c0290700a0100c401400155112407112105440e0180c0544403c1c3c6040f00c0d8181d01c000000c021421035010f0714a071582580c0c806c2510389030302d41030011405403009001300703954a902d00403c14840403c6000e008040c00081c0f02c0c1c2e01c9004809600803501550725040b80400100880c54400c400010b0400c0051021031700701d106500c80e44016501300001e540003540007010342c402c0a54001c80403c002c00150020f1300d0150040b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 936405935 1250 936404685 936404731
    0x1203150405061e04060506070501020c15090d0507020411041410020f0a0212030c0d121127120618010e0d021f09060501090b12010b21010b1305 63
    0x1500c220340050700621240030f98080314111007150203800070041c100143c800d4035400859095807050702c054455a4000900c10f0308140104420a26000a52440441c505000480c180c8583d05032103c1d004000b0301048810070b560b501d9000b0702c12188140032032640c440ea074403c554600c4c414060706d54420b000240007250000d0020030f000bd001d03001080a040104495402c12141c48503030141c1e04014841031020145440c03007004400651301640d02c0d0f4500c4100d0300005002a5203098407200200c5005111034200d0140d200d4601c61280c2c0750f0001c3c4402d05584001286500e000400a500184246c00600c00103000440e80401c5102e031071802408103080401600c0c0d507400600f10400700680c0222048c81e0400803d0103412000d038100180442c0944990700c451b403d80c2c6083c0c0007a90350070390754901d030116898580c2150804810090007448401c0307688002480302690841c000c040c051031052070a0a580f0b00b90710180c440c040082841003200d0301d07000941c0040104035040e16142d800c1509040c842 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 936407185 1250 936405935 936405941
    0x31306080703141303120e0102190c030804080325230c2e050103030e0f120c040e01090812040b01080601030b070c21170c0c03030a091412031504 64
    0x1000880c0007070700258460401c0000101d44d840703000d6040183c82c03c0d40714075007401d60140745820300d252000542c4960107644aa0311003800d450b041d0301800300d482e22040010307410150f06540541c1002d00c0e140c90340c1d5803040094500c2e030344556011038015600d0110302c01a03001101e0460481000e545c102d01d0705c0d002400064136200b188080c01140d030140c8086040640104e49502c160441d06100340101008980030805407142a001100402c070201c0740c0034010305205480e40f2006a04850a42c0c5a998200c02309488040c0840094020364444e0203081155500b5042100d001d5800994a6a0385c0166070454080c2d000c1601c1c02c641d229211000003c001c2400109541a80e82103200e001c2c95403140e040c00d41d9a44181c6808544000780201e5200502e802c0043c41400076a89440b1211000401e086175041c04c0e500070b000030b541080602a007440c4960000a0ba033b40000c41c82d00014214406007080748100c00181a00c440d14803d50386541a54800d000c01b450141c500341200d9001d42c18004200f00076 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 936408435 1250 936407185 936407201
    0x2010614011403090106030f0606141f11071a03011406040b030c0304110d0b070212040f14060c0303010605370c11041d160303090b0304030908031306080703 69
    0x1640390070070b584a4a010401540c00c02800c00000880e03a90326601c5410a010444e8107448055841c01c1c10400390801c04c1003006000c0d01120403d076010460003051180c40800c465030010800c00d0800180880010011a805004c0d000c030340703802d21040641d211036a58000d02032485404c101c1540601982040400e45090f00c100381041815681c07280710350308180d04012310a46e0510003c0c62040043c0d1100d4003c0720b20180110059522894150000f1789040e0340d1100442690b00308010812900c040c1805040503102c6818141456000510000c1c14600454140d814140800000000d10b550444020855500c0780707410344500c601d890f0b026658148002c2c080700071071013200903583c1402c1c1c030846401c070a07030f031180701d0040840c52014042422200d91001c003200d21090001c1820724060100982c4541003158100407444a00f0755900900b9070a4038030540c84401004404941018014075024010b400800e040385e40300c40303100003121104000c500c40d1a0204245c0001b02e07150510038065250 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 936409685 1250 936408435 936408437
    0x15030c300604081902010b1507020306060a050a060e0f03060108150703110d0e0109240e03090a0509040201020a0f0809011409031c170a091101090806161b0f030201061401 75
    0x3050111118014083c4c0e4078280c403001c2195a0741d61105030b00c1c0c0d501d81d030b1880a030150501068950210b441450f2500c2d4018001902c5411100e408100954409a00310155845498150748040c80c1502113a0100c0b020010142d050145000103d00480d00142c8084185070410244201d40c40318082a8100c0704c10035020455000100003403080c800041e00907074019035040000041241e50380d12944c04c0301e40c0501950460317480c80702030400c0c0c42016000e07080000800c4805140340c00303034000028418107800c0c81001c0c0542e000400080940e8024007141401c20380005140d013100006107000051544100105808100e04005a200a5000780b055030f03d20b600203001400c80300c3c4440f0002c4102400c0ba092602000a510710010780444280c000502174003540c0c0012903c1242c030311307002e049080d007a10070701c2c100000003104020407031000640341c2e00700440b644406c1c031003d41240216100111544038014501d900050901000910100c3d6004140241c0c002c0101d03070748580030801f4a00d4200c14240c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 936410935 1250 936409685 936409687
    0x6120f1e0506011d150702090907080607300605090c0c011109010e0d061518060e04030206072a121d03030f0d021b070914010b0315030c30060408 64
    0x35031181403178100c04034005160710340542001c0f07042d400240d00d40004c440d943c0312900044000c20540038100700b643c1e00038a0344e050031a840f64000d40d41030310f14141c48409045880180005000c081d9281e07102d64007034403010382001c9940c648040214401ea010300d103034258a628201000c8080c1e1000401c1d10b5040728145e40b1a0741c01d4010b030f41088540340704c0907019100966a03410540101e40b8040c1e25400404044200c4003908912100c0102203d43d207500c1761a40380c505408001c0042c1d400321380b03170358080550f0800d2159020010350790000070005e0f07803140d002002194500300900c41502c4c558490710300341d80d80e841c5115517940a007c007001d8040c0509605a401440020078020000010302421814604010308000c0c1c0540c00b21901c0a400005c84950f80000000f440003070310728000c04412055440c01903a1075450030a48040f035110052540c01b40310a50601c0d084a07540034808180421002000702900b020803d01002240304021710340ba100c05852900800c050b14041034051040c0e81140400f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 936412185 1250 936410935 936410987
    0x211003020409150507110c06120f250e090a0c2010110901020d030203090a030c02060d0c031b0c020d020105091c0c0609060201090c06120f1e050601 65
    0x44809031803020700850346882c00d0203d0700590141d911566115800940c5c1d4050340c9008529070b642410740c44110030340140405c000c200d030a00740c0b900308542c0160100389407412507a20451100a846a440449180100214208010340b035001c140040c52160842c1d401b6407a1300c40c083c450003104c0ca18807035400406c9120b0011015001d09407a00c0c10401c0000381684d2142080307400080450304d01581403040003d01281c80da0741d03941d0400071000350303d00a007000c506d1410000c80155940c42c0c0c0706c10041c00c101e25400c4000c110b460f0207081d69010400145c0510200442d2071024000e82403d03082507514403140d520047c09288510200112690058605580031944da001100c5070303805a007d40f60402e28108180300101d096030341c0462124000c1c1c04680d421070500300e00602100c22540b00508581c141442c400208046480500860302c40b03003440c4a0b035850030910207003d89002582d0240e0640391034012030100b01c03044444410010642010403080d40d03050700644d400e0b44459491100e003c3c41d4004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 936413435 1250 936412185 936412189
    0x100612110114120109061703031312030e01290a0509060607050c030a05012a12092109080d0309030801120218130501060e010b1c0b0402070821100302 66
    0x1446140090150103280c81214007141c00542e2081c0c3c042801785954410801100051250b00480c1e840e04030055032440c00c001c402e001c14030ac6440006400045800d01d65010785029034403410300c84000310001d1098401d0a102c2c02c401a080c4071001449020041e2803203041e20f0000b04410943e03100070400e44260b1255814004141c1003002c048409128200032100c0d556030811003108524400c50002c00c1084c2421080050540455010b11680d01c010a44041d0301e80c100104094410280381c00259108039070404940b500a4111003020b20080480361103040b0b640035001c041604c0110301120004511802c089040f91188100900060040d13001440006007404c04501050f00007000d00e500d000242055220300c0406481c400340b00d0300103402c40400c000080c01070300004c000200c160301880d0714185507240e05115460002e506e011030001451080c1c0540d1744102074408000d0402c540705c007100c1c50503240d01d81c401d82e0989558200306419040b56900791501900c604510741044c40140c1ca1542 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 936414685 1250 936413435 936413447
    0x1060305160804020f060f180d02060702040c030b040516031a21071a030f070809100b120303181b01050d0e0a022808030313111302030103051006121101 67
    0x7200704c0e80405c00c005020059610817003d0907038a10210701aa03a215120301070072030a1030090750624041c1230246a050056583c1806995030542c068402156808551404170020904070602d198000d1501c014486d010311401d01030300c01c3c0105900c081001c445682c500401c2c0c00172110391a940301145040004811402090f14209000c03600125081c02d0f8655000d60f6800300311001c0c410700094003104000e40010056000b5803c500a0305001d8040c0c10310520594545580d0040401401d032aa401e8503c00d0f15074100382c0354461400c50a99440c0e0501c41036008150046018180c001c3c0b051624200340c000c401e040d015040d0105031103152400c0c0302c400382400a4903401100d41d902d8080d19a200026031030300390000803800ca041880403038000301000981803404032074002c0061a4004d00400c1071401e0341d0080c0070000d030340003004603008400c4000098018010380300100070b0f00b030001c03000200b0000006017810100d0060309047c4103e58960071a0985964021000740a0007180d8101c0d00495000d21 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 936415935 1250 936414685 936414691
    0x6060d030e1909020901140306030a170913090369082d040228090b060702011d0a0f030302100605011403011a070c09090b010603051608 60
    0x142141040d102a00202c0d01d0304660766000c008191340021310b44030f1641c2e0164164443c03489941c4080c1c103608000010a0b43c0c1c8101410041901200c0e0800d01c40704510071054906920006048903a40d10b262081003028060060003200400c0300c02c501c402c2048000000700c1c440c0400c009140140c266070740c1c4441e0300084180340b03450710420811800030454580c01002c0169240f0002c2c94070140580000080070400001c002c2c551f82c100d42c1d0030030243d0340e02003010188480c1d51448005501c1d165400010403040500c3c24005904200314903035200800514200803c03200c0da04c03400c2102281d42c0d028030513980308242e00280050b80301000074580c62000180c4500c041c0026040150b81910b035454038043c2c410907007058000d41e211050070202180f42e0301454015050a00c4c0106d40309459011005a0740018010a1782c0118984030040400c406c08040d205580d820946801d825503480800354028001c0d00d00030b4074854607240c008602c4a00a000342409400899110054a00280070480b8070038009 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 936417185 1250 936415935 936415939
    0xc0a08040c0e0f04120206091009050c0a0f17060f06040507090b160606090e030f0a14190e030c1f020c031c1b0c0308090d0f080405100206060d030e 65
    0x709012035601100d03181d1600c0f035602e03c03034904a40e080c142451128030740425130904c115480142000000b040c0818102100c0c0c1c0d0804010074103e0292802a0401402d800b0341600300c060300b1400102c07210072024a600303c035074103841140d04956003940c1c00d4035007a04039001000c64a03080c0c042881d5040a503c85680300b11705180c00c0c070a41d6110031074002c0035402022001d00c101c8110b0780080c284007062281400909500030100306c07403071a00007a04e480c3e009101120360180000724507082d00700d004400d800390030682500842d80d43c030f64401c4032400182c01c544250700016402c01c00354101d0b050005118080060041000d190072172480c00709144a10500200000c500070f5460f14a40c50701c0030403842030149140842200c58080d0b1110090070340204c1c41c22000f00c001840c4a034030102e02e5071244c5100762074015660303a0f56406001c002c2060b03440c0900004001e00c4804084c4004d21802e20007810550701d08841c6e02e05149540344080344c0d030f44400e507642903028414210410010b4080c0d000789070701d0400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 936418435 1250 936417185 936417203
    0x1b0307030f1e1b0b01031b0609030c0303113307081504020a030e01020c070527070e01030929060a3008130515030702150a0204080a0c05040f050c0a0804 67
    0x14039139440c80b2034802a401100c4201d52180c044820360141c105140140440e8608172040c00c6c55500c440e034100e095880040d060045c54030800d560504140050b0044441c01d07880031900c00d005130356404002103da181c01051a1015000c5460302d4810b00c41c180c01003000000c0290258070041c2048002e600038200f050501d6640d00318042031000a002905540c40840050b2440910707150501000303442c0d60044a0881c4880110200c4a000d08108903402402503e0070f03020348070405005030010f1003100000b9101407120400409032060120300a00701d000101c01d40b00d09a2941002c1c40003246443c01624403d5640d44104052507020f0365408901d01c00a151108129809490f854950390140d400ca86004141d00c0003400607081107135050801c14031014156141d0f01c1c264000035280c118061001e030803807180b0000b04504501e16010354010b01084003d80301d00c681c507031514512100003481028080c07410120726800940442c45054450310f403900c3c60300e240103240c0740e0440b654140248100c80c1942d07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 936419685 1250 936418435 936418487
    0x907110f0703060b100f170a060b0c060a140121062004060e032a010903020a0603021201080304030803160c050d08060906190b0f1b0307030f1e 63
    0x60410074080107500031400000c100d4889414403070f80c1030345040392006000d00b40c84001100c5500a80840f610442c0c10182c1580d030f1502d6018001a01666118120745040490500c24455020420343e0003201300c00805c20841903510201c00b0003020074440c04010f89070512504044581140688101601c900b000080080812041e6060007103240d01c0701ea07a02c4d001140a01105810240003601c9150440080c00c03151444d80d048001805000d407540d200500c0c51034014210790041050700c3c0074540c004d1140c04020345a20009009401c01d06241c1203010b010303000040d40f110080100c5068070f8000241c10b1560340c818815540703440703501ca0240c04112860340c01001007882844090305084095030341c000385d81440c100300700440c080038141d1803140d0103480107410a0110407021508440c42c403043c40d61a4115040341d109540600e041e940038038060280c032100c220a002c0001c2881d07a10035110f968555400c1c840c102d07000c3c002c3c0b040812486c0c500741807115410303004404500038007000320301c90400e003c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 936420935 1250 936419685 936419713
    0x9010c0309091d070f1404090201121b03140103050715020307061104060e010e131116140d09032604080a031701052d06120106020a021e090711 63
    0x980c0390743e09510b288800d010340340c00718075003401000000c1c4105032408410a013170101e1300010416080c41644182c1e501c0003c07004590158041000b07070782044204100c08120300d1340c0c1e06144107030042d542c00041e103041c024043d6202c80c644124140d0b90488018002c06041803034001c3c0c0d0300d01c02807800e010743c4818045000000d1084c041c06500d180c4010002d5200d80c40c1440103003d441c240700710341c0d042c41036400d50300c0401c0d1030f80203100000708820800841d5198204000c1141442440005000510002d10b49010300c2a04100b001251540e082110b0310081501d000301d840440c9070200130003a140f003101c0000c1ca122202107200107985988495442d069a0740c0002e0300e0201c1102e01100460100140c80c01e41e04600980c40d40188000e90301d0481c41a062800c1001c90043c014016201c00400514001300303403901000e54454150380340e042c402550b11458085d6a274030040604074440c1840c0449003c0f0030416103a4140301c058007420404541c0c8542c682035411480e880c1d140301581c4a0742241d90021 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 936422185 1250 936420935 936420941
    0x705031c09170d0c1d0f0411040b180103050415111b01051614070f080717120a060609053a052104210f03030203071d030309010c030909 60
    0x80c0c002811890f40d940c1107405003000c0c0c60320fa00f0754005006500c2907400801400000034094114202c0348048010503050018005284c0c0e10405080c800d0003090101e00010f41a0050210702e1008500004229041c40110192070080300c00400b00ea484100341c0030060f1460304441c110003d165009414440c4011a0364041714074420440b280740e445005108068602403071244054400d4138140d00c400c9910301c0d060945104d0800d00400c0c400c0246444028401c440d02920f1505034000400709580c0c0c9103c411009541100c220005d18001003404102049002d00c42e040c1181d825440d52010940352404004001d006144080c55440c01c80d40c0c40004180100c1c94090000c02016a000c2d08180c60304120b890032829841c440106140100e1151035170000300e00b69421070f07a440d05021650000f5911303241b010041c5040040c010641040c1d080d04058144d0041d5220310995030390603035018040800082d4105040c0e1005406410400064101c0d51040080c000102d010b0f0500c4107013035076191641022 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 936423435 1250 936422185 936422213
    0x1410030f14030d0902100e101d0612010f290a02100e06070908160905040203030f0d0b0108090102070201080f060a03051204080105090303090d0f17150909030705031c09 74
    0x10581c2c4e000303d10110f262506803080041203924268100145c0480403511001201c41c14809100c00c1c14130241000c40c00e036444500c0341030702419143d1100e031403003000b034140341c000e000b0800e20800315900070486286501800844000080249080b85407920381001682c2c000c4054604601031644034400c120203502581c00782e43d041800400c401e190003480203210769003035088600300780c100700c8810700b41100c844040740070390368a8030000a40f9122440040d00e1840760380d080061200e4045500c4000303110544c080005240d00780ca030300c18150359060003d400c1740304001d40240861500c0000c0f984079144d0640032940818080e104408082d03c030b0700e50f01e16243c1840b051064010000505104c41c440a00460740c02118080055065040000844da10740100d040d0340703802c001740c15400060f51842428602031148900c3c611002074100707200710710704c500a0070000381d0084500e4404519a1180001100d507000c3d040405181015140250b04200195032103181081c00e4440741e04c14003090790550740c040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 936424685 1250 936423435 936423457
    0x405070b03311a0105010f140904181b0608010b270a050a0801021c061215090b070309050106080304050102030a030504020f030f0d03050108010912030e0f0d050703031410030f1403 79
    0x10545c50640010900d04051440300c0c02c1140c1c9100e0030401c1443c44c0180c8285127800c0ba8085680348829881018007480748202600701c00d4045001910894040304500c03d84881c2d07529020181e07200d401b81c1c2924071400c104060f2008004880201c19118011183c220703000007000c20681c283c4c3e800010301810400d40110b08a0703540041c031440000401d040310b00c26030b482c4d0382c01804041c0c6040f01d0844200b110328400b40c40c03508644848481d004c5150311040b805a0f001c0400c020504001c44001d00034001d9540c200c0d940c0d86090303000b044171200041070324100e900c142c0c001c0d0b1416210030021030140c10007400803a0401d81307a139901c5030150340600680f8040c110000050200d0b00c11100000d0542c1d0040c2c7c400c160b01d03450a824640450451025032802c03a480b0308001c21103804941695180c0a41012160356501070b000c1500321040d4014000c0c00704501907178041c003a061411098507202c8005481012950058040400000302103101d4180c0082c0901d1030703c800c1002c072407091829617011455840c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 936425935 1250 936424685 936424733
    0x10020705010e0405040b0f0c090603040b01080d022e1104081f06030206040302040209011209051f0615030b12030708121324090213050405070b0331 65
    0x300081d6404003400c502908215001c2c4940e00340703600c9811601c14007034000d170140041240020000a22401250341c01c400203400c2603980e1130103040c5249204001e0042c10b080c0c0c01580040302c1c02d24800074180701c5910300c000424018100744860800c040145085c24030a841e16810394080750b101e2403000d00014912013001c0c00b07401402c00b1f1100040b803107580180d80114a01305c0d0030700141c2c4409084c2d5059035815a0010303540e07480000141e90310071107a0910800e0301d05180307401040082c0070480310031a01d4408980024818030400e45820f4881c14018462002c000c03440d425040e078460741241001e07120142200980002d192001030841d80200070984d206040056031400f90030140c280079034844280c040481210529036074000410102424625120307084000040e061051a84020001d030740c01040190241c00342c540b008041c1c10101c8042e41c40303014030200029034417070308400c0303c2c80345c6440e0940b140c4614813251142c040c8540100e06e0300b4460030740510300c1c0010318500403860703128070200250 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 936427185 1250 936425935 936425939
    0x50f031206060c060a0c03060e15010f0c0314090114030c0408070e0402060d09050c04020d090b070c150f020d06292a01020702030a150606080f0103061a100207 70
    0xc0c440e409019000d18010002004580521080800d45541000200501242280c150b4604901804642d0007081207484410244100d1030001001c400030f010003070721b030440c3d40c21441206440d1204c00c1c1e079000e800314034582c41d2069030342d40403030040a80318014148081545400e280d0075040303030001c0741c81e280ca0b000f002400344417880c3d0403c403900c020600d0324921800c0d85040d601103034440c0101014822240d85840421080040601c442c1c0c0400784050000c40d00d0702c1031075000e00c003e026201030564203081c1740e4022446c9288a000c1d51103200d40c0105a40c42428840025900100b4200420110180e400d02c80940c6201141c001c3d03d00500d024503114a090402c861500000fa1100c0c0144032500c0040095078500c0c03a0800300c0201c16001c1080e040b11280b040b00000e030191040d108001d40c580640030942e4100100700c20148800d0002080c02c0224907254501540c0c1150103440701c1c2c0c1c007141408010400100389030812006900d240050b4005192140080344007201507404075405a040b603201 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 936428435 1250 936427185 936427207
    0x705060c0f19031202071106030a060b0f1305040c020d05070f020319020915010f0e010e03010908120a050603030f07031806050421020d06050c160602030a0e01020c0601090b030a050f03 81
    0xa0210241a0b08200311b1a000aa5035040d40201e174048065000da070b00440003e40150541d40184000c1001184195031a4900380c1d1030081a4005450010480c0d0607040102e580d080c1889981030001c043e030010a041403280e6011303070b061f03003011348126000981c003040354005860900c48aa40c00141d028a80c4090503580b0401010580003030a207454204044480c2e421aa441101c40c00f081c005170400460140703ca00040b985d921062074656015828641440f04010b000030040042c0c0040081560080c0c4441c00d4100a0b07803015140303140e042d4030900010004210040041c10100c0c424180591840c444500034004000141d00800c00b241c0042000c000d02c1d440803500f2064071600780404011b2100e0359000580f000480c06004e0499641c40000410044040b000c41d039908018003507a21b80940d00e0310f4134602950003225652045414140100d846150500039031b00c0e02641500500a26802c10003e40002e04402e2625507040c807660320104d022035018046030261400701c02c003842c0d03900b9542c24 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 936429685 1250 936428435 936428447
    0x10603060c02031303080906040e090703110a030f0308060d121110090203060a0c11070f06020c010e0d02040f020412060219051306051309110a080a0209030705060c0f1903 75
    0x141c907425504204000421408209000f00559520110540e240e00c07602020401500580c0c200741812030303404003400b048000c0014800d084920452060f03a40303040e00000c0c4096041c940c0300050014640341c01e5000040e00411043d40d000d040540300800e82c01868649a10541c1d04101050100b038100d80c1d0b8050305c01b818040c0344081c01411070b0600441c640c47d40401d50b9001c008050b030b107110f41d40e80b416141c25441130080e01049401c01007160381990b1105600107980d04988501409885484900a40365004031101c80d60003c0003020503e4680f282e17000d000140205030720000d45542c1c200000b2070706822000000d41102e01078100140c50300200055204c14944c42c28203003050100521902d00c41c0901d030304214094501d01c3c41e1043e1144c0d541864891020801c1c1c10031071110f03051034048140f03410114050316030000c4c2c99840b11080d4403000c3c006c1d0100e21551402941540000c0c0c400c1c0a1030604070003c12100286604940781c42461141d03060074005440c16031030b41c828038a00000c2c20306501172 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 936430935 1250 936429685 936429701
    0x201170a0b091b0403030c05010f060b21010e0712140a0608010e0102070f030f030b09070c061a01050a0f170f0126190305120903090307241b0f0501060306 68
    0xc0c84000e503d505034089002e602961100a08022003040c0c518200b00e001e4120b090100a024001d1142c20b44030311a8002c0c64021038115420f1135100c0e1000c0801080401d1418121016483d07911500c0e10380d010100c41964030606008800e949070b000c0311403c6060300312480d200e0070030001d0010361f40b0b0911518501f56401c10f01c180b41d040e03005000c0f03140443d000841d2041d260b90716007015000c004c16450180c02904103207200c0c41e4403159150400a01e40d420030480900c4c1403080720204070b440540c0070382c6c41100d29001a1940004c4042c00f0b00a1900e002d040410380c8621142844090702107011400282043d00f110801c81c903410003401008001c2d0f0800c01029103103d4007001e0024413800c658480e9507a18100d00c00092a000150780b80145030148044500c0340e28004030030070081c9018403226559901c5040840d000384070396040041c501c9445108031000304c0c4142c0006c1203441c082103084459145420925900c40241100d4030001410300d400e4010452207480080b0701c4d5465070030014201d032007003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 936432185 1250 936430935 936430951
    0xf0f060207030b0609090f07061e0c0c0306110c0109060608120a2f01091109060d05060c03060402040b0d0603032006060d15020d090c06020304150c0201170a0b09 71
    0x19020a00000d0a07001c050750780800c0685e42500940d41d0700a41a143c5400c000392105940148100071802680c011041580741919000005080b890b1140c22100c0c00d0075040003401c10000200140001400c41d0041c0c840c1c40504404c181c2404200c5110303a084034500c41c001c0f982190fa40b071003042000404d114280110302c000b030419052040944010b00a9040c102d01c0740c0407095a0366041c003040c1038003403a00062918084c02080300d4515031800a15040c05141154850112507000800e6807a1002e00300074800d5103c0050585600d580640041540001d03282d254816002c0c0004103a0000d1803010f444074031000394001c02c0c19450740c01e010f440030b00d0405103407040c1a00d000000e90070314000208540c000c1c0007500d189000040b1402c22404c00303005d043d411840307903000013021311742d80080c0d03000407007078038001e0064440b800d40c1c1b08409d0b070b603e100b14450b81007203030301544980c0056805003108010090040c141401c01204200a9a00b110421158003030400d40d0391030181c2c480d003444d000c015071010030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 936433435 1250 936432185 936432193
    0x13050f010e0a0b09011e0b01030609060914060616112e0815150c011409030d060b0c0c011b080a090e0610120209150c060615030402010e091f0f0f0602 66
    0xc44031000110224a0b44061b50b450716842c144c007299100e81c1c0414000c0030480d0703080010301e4840280901030a07400c07183c18560411500800c9061400004880c50701c4c07541c150b00c07440c803040c0d40d4035014080900c14020341d108546821100e84041029050401d038410035030601d01155031518007a20f0300714090204c0c0400d15110080c1c200f142c454a5490520070300071045940c5882800001300d0144c820203400d0750010ba526402e01c500ca0384008090580f4280c10a402d000c80d035111086010344bc01030003490b0540741e01020741480194007070510383d205a11601c0500d8003007400da44070901d90f40c0c4028003c0c0006003020004001050030b4103500b07500450700b1200b081900d104050010204500500c0d500219640001c0c00300c01d550310180140510161882c2041e00d4130704c01d80ba0252901c0b01141c006000c0d041d6004050582a000004c49104660585030030520031040028010f03080b00040a2a00c8404000310003d5101109084e900c020540d2484072039000d0b0418045180d000d0407a03014105540c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 936434685 1250 936433435 936433451
    0xf16090e070c050c0d06020d0b0618040504020d081611031f0c09031b09110c0709050c2503200c0915370e13050f010e0a0b0901 56
    0x10080308000d401054902e44020082410304190381000301820b0b01035841030010040c1410455a9000390a154401180403c81c00d40c4203000e10100f4841c2c004c501002e400700600d018210318195000b0f6030024006042203012400540ea603400550240c24404c1045e0488041c001c1008420b582020f4503807000d81c050000c40408071546107140d4400050280b085884035100c445152043d070000004540089000841e450303020315040301c1c007049024902c4c2c0541419404150000c00d0012a41181071020080c10750030316003040c4800034100170703020b845d03421001c0013a203603414540310042070402c2082030442c982112515000d002c8039908049101001c035101c1d521901d50300c02203521030b44a001924007103031301ea80b0302c0c144418890001c034100b42e009103a10307070031b61542e003000c40301101300f4080540720242400510003400c003511161188825181c1e00c0030018102c0c1d0b18050019805a210702d0840300e00d0100b0949482c2503950215864901342d0003030200106110500c14115004500c010081000c1d07030f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 936435935 1250 936434685 936434699
    0x40501050d1211120d060906140a0303050c01060f03060f05060907090302280305060703060f050603070513030b131509051507110613020f01021b150f030f1609 70
    0x14840d002c40c400e00c0031401c0d0405803030b038040c80222134605290106541d0713112034114880040c0303511300a5507600b518121001c2600d000c0c00c6030100c0c040000601c0b140752640396130303030032282d41e4020711f6010000c1d5211940060386400d01c0940c98040c601c542c6010940c24180240c0c0001c9810042441d48507060400c18062031a03084400142940d405540c800400545448003804419800c9618400040c1c000000000c5c404007043d614000c0e90256800d1007107a039250400c0715042010b006d03695000d4004c1012400d45d5000b040141034aa0348101c1c000070144c1c0d0f80c2c40c1c00030b00d55400c0f64040f0340c0200d407554a02c1000500700d005001020048801c101ca003205132110b580e5000312507450704400c0e9095000c140042e0240d00c90740c0c0100c00341c008a42613441e103449803850140080004a0044000511250781580081151503400c40d036100284030410b960ba040045c2141d1000101164003c00c0007034244ca0702c807050096115000041c0020301600f04250406240010100018100900240309101d20 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 936437185 1250 936435935 936435953
    0x5090c0109050d06090510020c06011509150320040603060512030405090403020f0d03060e0f161b0c03110906030712111f1106150d06150f0b0306040501050d 69
    0x3407101074662046440f0390346000f800a001ca603001401620407100000b1904505400500b1424610400c2d28150b9036640ca0071810703036525954610100c2c040312414442078082c40c1c8022281005440c1c0800d45022090110000b03039020096081602400a424400c4c0c60701030040c00c1c01800c0030340700003210503601c103030541d22402940030b918401c1050101050074148200f081810440300001a581440e500d518050000c0800d441100c1c0719900d15000a100400c420f02d80358810055a03048082004003150120761101014080c0c520394080010f144010606072000f400155128902c0034209665000400a00e44402000c1d18800da0004009200e4818682c42100c80346078041000410840c0400024810440d8601e01d030440003a0010100003c40e481030808070f82003c04c005884043c6c5541c96903d134000124000703903400c1501000c12500164499101000c44072605010580b0b16480360042080410300764022070380843c011050000c1440d10f4070400b4010b281c100d90300e03416503143c1d03075504003d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 936438435 1250 936437185 936437189
    0x20a1b180c0f0527011709030711040903020c04090302030415030e06250503060609062b05070f0c0825030e03010513020d02040e0d110613080726030106090905090c0109 74
    0x6011600d2910907156401000c05c0c0601b054501e40a01c201e00e00450183d030351303801510003a90081d03080004403c4608081c0304804a55405a010b401400700b454284405000c0108c0200c08501c020440054400c8024044201c05980e6070340c040740e500c0080101c1481c3c040c0152180c100100207282000fa000e04492140e0300b100c41c03609015032269106400a04180078200169810180003e0449400c01c00000f1000001c49880000c50315910360104c14811141e084070300101007040c03e20f244800b076004009800309280304203002440c084112400300078540724a410900b815034441c500408141c1c00c070030104407551040c0c000700001d24250714405240364a000d00680074150311a0701d641503498981001600384a64411070349691010240144801c0c001030486000c2e000e0350020950004544184015498001e0324860030044a0b8441a45d104012004020003588200d44041c0703407a00c035409503008001d42d86860706102d14007100c1d1025102e0040146845800c001500841e40c1e030032120b0300e42 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 936439685 1250 936438435 936438487
    0x506180c090a170d17013f0b09061b0301050d061104080f0f0a080307051c050c0306122a06070b010e040606090507080a020a0e09010e090c010c03020a1b180c0f05 71
    0x1603000c0074080c0810103030780d06087c842d003400c030001041d06103d904441d240c00351581070111813056a940031085502403201403120180303c0d04000410641c600040c00c80301013401540c001400c181500d1b810032143e4015444816150400c900c5814010b02c140440710700d0f80181400740017100680c0c3e03280061480003c04500500101160040303556100c40080070031552510340411190411090129107500308507503061085080c060f010709130a10200e581102103804440341502661494100b00d0303511f0710303c4981e90304207400740403000200da8100c494038000d052402c01840303241080d0414200740c07500c0e034003d0901d07103052105018910b94041421a44032542040c016180c61824030b080318052400c005603030340107420400100d011031200c05124000c21420003200d503080241f80064407082c20740309014015800c140741e000c0205901025860145585251480005466600d0441404010980b85d441507a4a8008851051300516070403814101818501d0920154100901e42c561400a40380 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 936440935 1250 936439685 936439739
    0xa0c0f020705210f07080c0307080709200703030b180f060f06130602060907081f090203100e06060103050a0e1e03040504110d0506180c090a170d1701 66
    0x1540c128862010f46400001801556100f0b41e8108007a5a1808540680c000c079016010400e035062800180f110200e514500141080c00c0c50201c903000180110703000080c00f0407101c000040c810203410010800f982c03098038005004040081030004000702d800112062079500070901011241c41c004d1164402d100b207694541d40c0ea1a040450800e000f500b4a031a1904041c80012a02d5074010031500c0c800c8240c0800c407070210703541d07846056a4004140300c800d01c13140400300c0188090810303000101a60300207800c40c2c540701000c0610a08540c0d250307084245070f030040c506202041da494028150040e08002e418050000e10010543d2511345080600300e40d8155244140800c0340144159001003c0051081007032144c17030f100324a1154040c005551050303242c1400500a0f15121503030031995103066102c00f103943e464014010140c0d00c00c500c0b1a5002d43e03c0340001509003c0554400b2030907484d000070703140e100000031010f44a039100386c5c10f0303030030700044c140041c03040c0d0008540815007010548070807 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 936442185 1250 936440935 936440959
    0x150822051023040f140f211306050c390a0501050a0f030f050907080f010623010e0d0c082b03020a14070c0e0a0207020d060c0918050a0c0f020705 64
    0x400c04141780c038640d02503000b08007945000c00c1c004100109001d074000c01c04000c0c0c0305880c13162080c0b4885d111901d80e0009481c007092100c1e500c00e101501c1d80d2039086003101c40214900d0140070000f40e480703681c030444000301d0001c003a102d101e081035400d103000162542c4031803c2c207120000e00705001e03a01113082000340542088454900c01c2c0c1048404004003c0108110b08103140c507180c440015004942c014481c0f00a5140122270500c00c0108980350510703581c0252105003028099400e142c2c82580c104a04140a681169558034186a08a00c1913480c1001c403450503003514244182403008200c014001c2c10310001c0b12144030001c1034244c00ca4900160307601c02030803060707845030341a480d600d55140020917034004202d1318194000075184441818000c50f518420540140e20807218000c5d0003030311041d01d1000160194002c14600b20003824081c050f26120200c00e401004d0581207012035940326000d00c00c030107070644103904200c0307201d1908510b109410203020390344079081c0c880d1900a140040301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 936443435 1250 936442185 936442193
    0x20105030601090308030c070308100609150504030b090a0c05010c051504020d14010509070909120f110d1806020601030b280f2301150822051023040f 66
    0x30940103554170501c002c0d03ca042121810343c040d00010030031804110103401084982c03030038240110882d080b9545441c03080d4103010329800c191440d0103640302440b105000c04000a013412203900c0c4900341e174a000700107403d62403d11585080160b0f10403070501119103506c1003ca4008920710041d0440d240e0b5805298643d44003050081c50a01d001034a5038000c201c10f100ca1035810341140c0e0103065000c0841d201d05071150400c8080350340b02e00000f07058100050091a000c3e0094000b00010002428540d0800910310301c007600348088990003c000903d40d10029003d0402110914050613403440203041035030560b650340c0382c00300d03024003032403040c034062242d0f1301d12500100059020042468024007151010306a190083c180d10081901001c01c1070031480c1032560b00441050481e000d405950a802c4141e0a00390b90f01140502204088030301000321126010300c00c504031756560701c0340e001004840c4042c010318044603c40314440312214240d0b050004105041d80e44103810503004000d1280c000c0c05450 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 936444685 1250 936443435 936443447
    0xe1c021506031002070f170f0a110f06070e0915092703070c0e0a09021c061113030b010605161227180b03030a140d0204080606040e0c010c020105030601 67
    0x11414060f40c00080c0701c2d010880c40c80901100648209040090308070820000c10850050403003101c0c84030300610060300c14038800e00c2d250b00205d940c2010341e064520741030041414a03000301e84002c085000c03015400e2a50400780c80b110b42c4200a124084405501000000c4411101401407000b891904000d250410b1100b005903401c40780d034608807503a4800b14540f11400800b107101c2c481e0750100c81000102c00c880c1c90301800e480248d0007400081c4c0d607240710b05041028001e110058442a07a00c2501e50f2007400c018009220010720307001704105107441d502d021501010160043c0c0c0400030244004489140501096262242d001000011012010604480361803400d410b81405601c00001180042000070402059a03c0610007200d00c00010700040705680341010b686405a01c200001c581030340c0300e00c8422064802150f045803a120300714940f0705c2643c000c0c0c0c010000640100c02403202ca49041c3c0304032000b80e01c10341301900d002c444a10020f03090f80d036803c2000c0e041c4800000040c21581c4124 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 936445935 1250 936444685 936444703
    0x606090c0f0c0a020a060c02210c040e150702072403023604090c0302040b1c1a0708040b041104110a09090c0e0a030818090a0e1c02150603 61
    0x700445840e2092041100c1c1c1d20100001c1c241e0042120340008a00a80309074403000300707d40c0103011601d0b00c00745010140300c060100a12500540281c80c083c03419680c9601445450f88040320051420700c007406506802000064218010f540c084682040003003414101c2d64440101c45903001d801c009148c0040c0c003e4881c1d101d0401d030102c411091800e16210000740312404556440c0c2903909186560180f004403052007070017078241c0150744010001490207800c131021184c1c024242c60741d03400f06101006062030728036070b0031580c014000445078100d042840e00e944c3e2004141c54051080c0c2001e44a00002c902c000d40041e04222405021401c25203858200581000501d81c43c19541c0d41c4007540142096914040d0700720301410408401c00325481050207500d48003000b00324988407850b6941c0c82ca000c2c0d00070f010658201055081030181d035500c86851900c04c008902c400b10b00c13084502c92950900c03222040c01c50040d610103000c2c0c201c0542c0019002d0b0601c14070300b50b1600580340c03500003a241001031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 936447185 1250 936445935 936445957
    0x90a030204110a02010e0c0a05040b13060b120a050c07020915131a0603040309050603040501200a3c0c060c020c1302070201050d09081303050d021e0606090c 69
    0xc80b400355041c54003001404802c100d640204a030600e4124903546402d480c0303010aa10804c4040103100500e001c5e44400d80c1d03440c00a001484101062100000307482c04c90740301841011000c964211060024007409902c4500e8200403c407d02d0000045103850089a501070702440d040800902c00c1803580d82c04001002c1c00900da40b041c2d060000c0d082d0090315031103441c00c00c1d00c0300d8410000a41e04000702070b203001d03542c181c864a00f01c509000c00d0248a40004200391074030b640b01d003164a003250840c140c0740124005040300686e280387c1004041d20a4002d5001f0140702a4401104201f82945460b9100c69035080c2c0a2010840b04815084880c101e070004007a280610b0303c4200c0d49016000200760b90400c1c01a103058209000101d0303010201c4c0240c65021f40454010001e9000418040c1e00583d2032911a4020506040d1210a4441419240c0d041242d50783d02c0f48940c4c11516030100300c801d1401c6814554492640d10700d1000c10388410028105601660040011400d0501ea03181529071140f04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 936448435 1250 936447185 936447191
    0x4020d0f0b150f03150718140114032e08100204031101090e0103030f05160b0105130b0d1403210402130e150718090204030b0c1e090a030204 62
    0x218203001880c100140c0781c00039084010030300074066003483e03803c0303940440008000c0c00c0100c040140c45500c1c4a0001d014008210481c0440b1900342c0350506203402070102c0d03d1605407200801000942019103c1201045101c0c06004118400043c15910b06080012250042007801450007842595210f41c03c0740342e150085484040c1074180681c0500101d030700440e000715480200d0001940c1c490024090741071002a2400180003083c0100a1500c80241508d030031440c0100841e4284058001802c0403a501c000e01d1004011500e00541940b9500c1d4200604000e40c5400e40c00003074501c100244004c240d12000040c6030001e2000f0b100703944840102c11648480003171084017070403840308103c81c100d04c10030b200c00d20304c00100b1051190040725044a40105a80e03070300c0a00380044484c00070581c1c0704109012104002d003854032604403004000480340582c0711070861402d080a18001492101c203481d0a21035080e060385800c00100c0d607240c64a01c40c90340c4800798800728480c9000fa401c003940040c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 936449685 1250 936448435 936448463
    0x1b050a0308030610080106050a050322080316051c1a062a120414030703020415290403200607030c0302010b0406080c130905010f020405190503030f0304020d 69
    0x10004000b10322411044070301c0005228900e01c29a0a9502030040000051083c499203e0450290005680005119401c00d11150643c441c00005041000d021650300d480423050101100c140f6582e000b074000b8a040150911015140094a403081d40014a220340d4403080000c0010b00d61b20308214040e0030141c055a9119915984000e88000400c5004a01c4203090011721308203a000c03c01881071a08140d0540c40c1034a811907010701041c0f940d032400d51601400d8800001a0390310f102d55500410310394401d04005261500740d0a00c60070b20b02c0c4180b140c01301042c2161550716118200d8003a20f030f0240c509580c04045c0787e05600b1840c080540d0982042001480e10241500080390741c00b81ca100358028055402058140301c00d032407103032080da5040d0340034000c0c0240d1842e140009041610161100040115958842a0075141d0220196141e20f07400241407000741864009100108481d680c1c0d8004149440042541c910554940d00e074a5000840400c04550790000102c2c111500510340c1c0907000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 936450935 1250 936449685 936449693
    0x11403270601081c05090144160203040b07030318050106120c05040b0d03030c110318150307050d0203070504031a0a050a0b18070933090506071b050a03 67
    0x1e201300d0345450f04499146250980714404850003004d06a43d82c0c2c042c9049423000000081d14040084101501003259440d80003e009503100100c00d141400512414100d01c001c4903110030740c1800c030854008010038001400001b0844e0005a450300c1e00040e400018411040c0c4007140a00051580d401d0110016200c1110010116068040e20400c450250348804000896803140e0505410880341500c16003c01d0280c3c0c0101c18880300b0341023000034415031040c0309046a00c91848102a02c0360002c20444906004500454411003200c040c0d1840c28880303005803c5010b050174000310103030000000b56145201d00c0680340250b500804445440c408410341218040c400c4407180707509450480080d2061140c2d00994102d00f01c082d00751607080500d00d448081c0604000d04420601148500c00603802d5040a04410505051180400d254a10300c01304220007012061312010480e0750f140502c02c0350b070344c0c7c0102c0c0c0c50a0782c0542c2d044014058419003200000b001d5006c26804251000000240 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 936452185 1250 936450935 936450943
    0x102010b150d1a030a1502040f03230303041a040807020d061d07140402130b0a020601031e031b14060a0606120c08040b0a0e07140f01140327060108 65
    0x4000c0b44144070040a083c0c19841800b203481c012903140d4402d0f905007010030158201420b04480030324002d403410ba100c10b00c2c2d025419480d0320484092820f01c3c500021a407115501e05196103401019615505264545001002890f55510034144a840226041046107000c03544e0159015203c0c225580103410400020000081d1880b00c0182c65248000080000700f00c07002981c40c49281c207802940e0080501c0001c1d0410b020403003c0300c94070f440205044041c9030141000c1d87d0558000d140540c114540280801c095000d8600021841d60741c420000b81c10014030f0803144840309107041d00c40400d003044c8030400c4000305c18941c5400b0b000207010b2018896003000094680316280c0208180300112018121005100c2030720005081c81d01180004030282c00301a00308030452008581c001c00c080c419818401701d603020300c032146543d21303c0801500744030910581c5c54109007058100541800c2c110402031100500f00c00103041c440c1103105144a82424007040607000b8011260b981da1654201075071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 936453435 1250 936452185 936452197
    0x50a0305030a050609010612020906160f05100603170c0a0c23010801030b0a11040e0a0510080613060b030f01110309070f140f040e060f01090b06090d0f020102010b15 73
    0xe480c186400039009003010a03580d8122105540c480d0070b0788c0c01103201040250000d0b01c1c0350f80d0286040289250742c5241a030542510f900a5000a41034445413410b14500300c44000b02e0b40351142404020000302d0003e41d660048180d6a201455442c1c001e051980d01380a0290001041d00c10302e0400420381e140c0f400c041406207034440f0425208111103c00554038510300f440010400500301300028003c0c6240d400510150f0b5030441c0007410a5100c3c0799070110030f84211150170490350b40e1420402840303030818081c00103142501c068101c4c0d080c0b000e6140986180034a002d0b017080d0b20f681010b029510b0170400c00c0f040e011001c008000c2000002d150104c2d6620a030b03003007042803080150100e04049880c4e0028211030181c000c500313541c40c819082c010080300f403442c400d900c07556402441446000506c0050311402a10bd0040c1042d03040070100d40403141b4030090603004600c2841211629142e5410028689070403540d80d189140f10341c40102c8c00350001042907500025a1504041117071420f0b800707814 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 936454685 1250 936453435 936453451
    0xd030903061802461214060702030a030b0402070b1b09040c0e040c05090120120f09011101050105060a030e070510121a2214011502070f1a0313050a030503 68
    0x203250b03410420b0945801a4606030101c4500c601804c0000c0d10505c04200d61007841980e2800e5003070f088500603810710030200e8801000d07801c0003070507415031a8188078041150104035802c5040c00c030b0b40e45030a8405138006011b01035030041c40d200720f08088452000d50794070b054018401e00c080078003141c2c028100480e0b440800d01803403c03d1003445041c0d0044042d10703885e80d0181d448141e4600d0301001c074046da448012103d007007402002c00300004008440d005048804200b40035907514001c540004007618018410400d199140400502103a0303108402c07542003080340e107000310740b400341c0007034450514035180d22855100d010005000382040d00004901d4064440543c00c0004505484104070401c80b15240c56500c81071030654500081d405440d003c8041c0d551110000f6040c0c0000c44200c01003100b03801c00402e0131000f40340b02c481103504101d124050000301c000c44102502e840c5102d0301c0b11080d095110010f02d0088001420f2140400419110300d0300300e002c54411002030305018007170f60f00a403040b03c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 936455935 1250 936454685 936454759
    0x1306030e010b032e060e0412050c0703060b03060a1413021c05071d040203030708030a09020a14040f0614060f0f0409020712050a0e091503060103120306050d030903061802 75
    0x201d2080c2d001e05c1100100c1d04006010b40d0555030b5035846c000030b043d61003a084140082071010001d4030303204200301c070040c41c82130a0000d10a0b80d02400c051502d0001040d40e03410314140b070341a0102101c5583c07500d801800003165146140c0451000482002c51a10402c0d03c03407407034800752002c0c03080018640007102e816071080c90b4981d003030303a004011217181101c020750140d2007000142d0000384600022b55120511041c001010850355001072042201d580c81a180c8040140f4403150034035007486140110300c00c01c441080350502e00161520480d4a10a04a1040f00302180c0c240403c2c001f00100c4414040c1c85000c1a5241e444a1003280290054642074500268034070317425815501070383c200e900402e1180c440e0a44500c80390708024a054004180b10100b000340c002c0038202e610304005c2c0ea40038611074826a80d07000d161980088c200d50300c940c40244070384481c0c1c180c071021a4000710b542c410703281c000b00081150002d4100741407154aa25038000c0d00320a48204d030b0b42000d84411400302c8894020820a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 936457185 1250 936455935 936456013
    0x8070c05012a02090604060e0414010c02161e0f060507030f0807022509110304150516030507090f03080901171005040b270108010606051306030e010b03 67
    0x251520500140c0b0440c68944401d03111409071414003145680300d17100070b2011aa0369210000100c01e00d0080e6011034440c080c820784030320606000e000d140c0c8100c2185c4024501c26216401d941660f840e244910599a0446107680e040014448280030180480e0504615801e0799000024015405034109400040075562210013991160000d80d00a006980c0106840442c581c500042c294040d04140d4654010110002d2610828090840462800b0030380946920380b9040c100124015003146150191901042081325900c0307401c4035010b105141381c00a0170760b80700d0409403802e443c543c1250701001d2000e94000308100c0070340004d0040000a90b562080c0d1070002070101c80c0200d055407411640ea90340007040c0004e06203a4000704020000806600881d802d80207200606065180ea03c101032503441d00501c120b11090180000a14551801500e004180178012141500e107000b4681015222620144010b02c250800e424500300181503800a040f240070703620680e006400c81810400b410020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 936458435 1250 936457185 936457217
    0x9030f1c080a02460512060409050604032712140f1f02041a0c070f0503030f0d1b02010e0d030510050f0d140105040c1401020d08100308070c0501 64
    0xd4074403803010382130f01158484a4038620700046608900a07044255220075805201201001d0070801c1c610540780e46039070701c01c1034500d0100400010040c5014605000b2001d0024070005225540a5010314242d0410b008c0d1115403126504038807104040b41d0b803020302c0410044501b603e810a034511034424000450450140141c403582140f4100c003141d0070450400010310100b0214905e518041c4d000107142a440c1d1040d070178641c0c46800f410824034030200d0103800030103080007000040c00000040c1c880d0b85182c903000075964815401044210070380425607c2d003903081038010781c0100004440144030010640d00c004d000701000c0c503941203144211b001041d0114002c0c418180601b000314902d141e4035007041d060020402400e9101600541484d00c10804200451140c902c0002d400c2c00126050420341400103c094284c2c002050000080c0e007084030580e00000c10840511031070505040c10f03a110b1480d10001b0109900207002e0410001c2c0100c104000141241d027502c5090b03c40c0d010803111a50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 936459685 1250 936458435 936458437
    0xf0f0a021b0f0f0112021c0e0f06040507090b040f050a0b0108013507180606030f1a090402010509030d230405012102130602010e07050f1509030f1c080a02 68
    0x1005400c41e04800e0f03100040d500c103081480c40c400541c10058035080100b0054200e0160480d0a09102a80c2d400038a441c200d00744040441101404020083c0782029100c003901d40d822072281d01d074007942d62071220361551a0340e0428510310014070010001407420a9402024026001c44c0740d000035000d40001c11440441d100300070b03c0b43c445c1028454030010101184c5e5000c41d078004141c1162149800020f0f00042d0a000004000044040800d916203400c3c07000c1d043d985031656609070141052034031a00c000d03001d1180c00c48910f080f600f100c2c00751250f00047e1030502c81e1310100c17509401070190401ca0a03400c10840c911082ca2540e40300c034000d103180c5400c4100d00890103003a000812088001d880c0381d915416181030551520001854001c3c042c50080a070f02166000f040903035112861600c00035000d1110030010601682c10b0480b0522800004291148202c1004c032103007000304100c02551010000c01103403907008012241110320800c444100034034500540800141d0560014401d048240 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 936460935 1250 936459685 936459709
    0xd080a180b130501030e010b03010c021015050904081b031b061509160908070609080f0c1c0309030f0c170a11011b050114060a090207050a080f0f0a021b 67
    0x1200b460469040c1001100540314002d15000c4940d2154030380c50300ca95007132240c944c02a25580090641c1640e504c9001c0075121000b880780c052080129080005441e00032079035038803680c00f01080755155400302d4100c2c11010325207540c0b180f500c00450040341241081070084954442031084440903601c2007000050644003120868104400902180e142e00741105135500214950a1045405468607099403504580ea4041300001e60b00b11801c2201c03035000c1c01054440112070010344000184840419400d0404094640040190444900078540b154030000c1c0a90fa128a484c8201000d82c1080d0006c1b4109005210402c0c01c050040c203451f020008090001070340c0186800700f507291180040d1103042d08107000341100d404801c1300318002038084c0300341e02e451923081035800c0f2030341014400e010b4000015000140802e00c100300001c003043d40007401c00e00842d8040c80c01380e0342e40846d400d00484c50164889a0600300c5010a00c0482290085a0480520403040d0a811100019020018505820 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 936462185 1250 936460935 936460957
    0x30e03040515031e04030309020a0816171609090c05010807141c09060c030b060a091701150b180a030f0303330311090103050d05090d080a180b 63
    0x201c0a0044400d815030050356102022004d50b000684030741e01140c1500d00304481c201c00290744c40068404600e0705207400805044088018440041018801c907442c043c01e0040540d50320381518040041202040b80087d001c50950360001096075500c280c1001d411080300803902c03035511500214840d40310b2651540b041b411551003c4e064942d500c030000c50b55000c00f080598402030401c81d40c18036000c0340102c8203160701c6420005a034142510300101224210351a4a106500c00c100c01d00c03040794002c040d0419182e01c0700f500d1044140c0030b420540102100c4010a01021900500146a800c6038001d8080f90040890a14107504000104911030410f0b000041103800640081e82c04070340f00c0e612060720401d1b0b214000350103001c04448152910a5101088008a0100010320800164509848014200fa28918071550640d9909034903184541c040d60204800818a0282d507612114900120781d08010041e40e5083c0308203000388086001880b58a04500017140000c2021803003080711008029 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 936463435 1250 936462185 936462199
    0xa1203020a0f030c0903080f070c14030307030e1c0803040c050d08120a0f05090a03090801050c0304030c05070b030a1b0c12030b0d02060a09031506030c1403101b030e030405 76
    0x1080003d40050000200c1601040392036280400040c40e020020311040e180f03a8005a00d6042601e0440800c15a5400000d00e580c40d40c8903200c0252800000d840409a050606801016461000c18003549030110380d808800d00c5181c20106008695000707601460095444075012501c503400d10422a030b4030710008299410810940e2003009542c4049900a900d890700801d140c00041c0c10101035a17001d4404054035040040903100b0142c10034040310090000714000c0c8900d2400b4410300e40d440c00018405028445800d502c07404008042c010440a8038600c01034648900b070491b04a00140f420217906907801d064200540c02e01380c05072140d81101944902d01d00c0316500c4500040b00586035484001e500014008203001c010303070303405014009024031a03079802c00992071400d04850381c0f0318201c1c0c54840a07107041000d002042d04c2c000c1c1c150a6400d049840c526085400000c070b032a0860244c40301007110700d0032010001056a018510750f0402142ea802c3c8000844e409025403079216601c100c1c6d5200710 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 936464685 1250 936463435 936463457
    0x106180e0114012006180c0906150f0403060e1e0a0b04080912030c01020a09051206060f1804060c09050a26030702060412230c040b03031b0a1203020a 66
    0x221401e405a01d504c0013540441440c54002141c078a00042500c0040c80366402d8122141010350403ca1403000342c004846c000c0103030400340c002c6080c610403004440071a03000002c0c041542c1c00b050040b60021760b4085020440d124491103025141d2080100c144503810b030017821401e40e010001800e02c2200c0d045828075034030352100c2c1d440030301b00d9200d1601a5003190782854143c0c100507051001d05443c00e025070001d40d803040c400c00020211081da800c840e00c210461309520201d05000100380342c2c083e00030360b50001c0130300c1c0c15000154060445100f89200000ca0410442044403e4010714101903680d142c0c078090710740340e00801101003250b0290144100c0320070b280c24551300a4142054507215403000307a80c9030403219000b052480c1d000c0e401c0103c0100305041c0c20b1003000f410341c440c504c074508240c00404480180a03403143e00e0b20300c040400c6100340c1c0c403001c05040a54060040301d0742d20440030804020180d043c911a9154040c0300e506a86240c0d21504c2000f0460203402101c11001c4140c1d0351802507e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 936465935 1250 936464685 936464687
    0x6091003120c020f100206040c0f1508040812010810050f07050a0c110607050f10110a0315050301051305011121100f09050411100909230106180e011401 67
    0x44140b19050703902c1120100c40c40010307240e8040100501c4119030140500786400d0074240b013100110f1b88650f12600158a040040345511800c040c0e9405040c6010410b42d103450524100b10b01801d01904070402c0b114000040c00e03d0006a401e60f003a04d41001403066680704c800c480d0030a8001c83e01c80c004140f04000000050348948100480e981c07048081d04001c600070004655103400103a0100c3e0b02d0340c0513094841ca00c0004000d140c044401c480703000d0102002c100c080c607046006104c101300515031255881704818000c0040c80b0050710015008100f9840c0c10301600110040026080c0e90035440d10052900c0720740c01c081100c1e880103c9000c11189200107415415400700b000380382e1040000c00e560b02003a00c64100c540c10004105181000c1840d0410b42000f0244001c091003080c0710f041c0001d002490301e13400c21400d0b421242d988200040d1142c2c892600300f10796a648944110304500c40001280b582e8026440f02035042c11310f007092030400e4450200c110343d0b01084c010b040d80d01181e162010904c0d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 936467185 1250 936465935 936465947
    0x6050915120f072d092a0f090906030b0103170c1606090e0f0c1621090515040e1302120c10140702240a03050609100312 53
    0x5210060800403181015a4205003070042038410100349401c00f20301080303070210348510610310840099040d45a150b000d00c56902c0354000b4810034100c00c2c0c136a11003900000c100404184001d900ba03440d80502c410b0180000d00b001c0070304840a0206aa90f040482c50816501c22001034079440180914681d00315100d21080803501c5404007a40403080081001003401072103021141d41c1c05884010340f1508040001e460030749075800100228901e4002c01264480000c810b0341c009010f05501a9110501c5035080740307040d8040805000b0354030641203121031020380403103c1c0d038030700c45a6075000070a80c5450802c851030010300c1400c100c0384400c3c002405449080380032103410006c40491b5030424066640824001c8485051102440d0400740e903c030a0b604001c4032444441c01c0500e0304800d45c4800a201c1c0c2c4a0b40a0410040d0003502c1e814050760054145000b0080c0041007512816100d10509030300034042c14007202d000f40164480350204140c800200f051400b42d9074040c2d50305074006080380c030455038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 936468435 1250 936467185 936467221
    0x30e0f030111040f05100c050309040e0304081b0418120e0409020a140111030901090608040c03082a0a0b0105060d1103011e1205060601050a09050916080703060509 72
    0x10555070b6800c810704120000c0c1c014001011014000c5021520301010000d09400046420045c0000652000d0010304003008442000d08202c0e000030303000c0c03008451546140299000b8440502c5081e4419680e1142803104040b401c000322010b00c0a113850001c100010002080d000385405a08043c0140d8140540c01401e00c01b040a03100141804003a0001550b50a8903400310302031013525079844040d541e1000302030424003d0000290f00d030106a070300090080b212803144004000c2c1200c042010070001e0b6614070000c541101540361030700d01d60a069044d0306501e03a04400e01001c481d02080f148900403d00c10700d4146c2000d4407116684ca402d003130064943c0070040d105c00302540c820040c1c1c60459110050340c0602042140542201805000d840210900d07811092080b075403043c8840004500062450703100701e003031a0103030726650320540503124903003181c003d00e61003900d80b020807541d0300800c00440255501e50b6030303403c42a211050103800316007203406816003114240c7c4c0010040400e2005c1500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 936469685 1250 936468435 936468439
    0x801050610200102070804170c0118060507031b0b01050a170c09060105070b07030c1106400b0a05011d07030b010c0215030405011d030304110d0227010f03030e0f 71
    0x120301722050751101c01d03961142d0021402400c1e0070302c1e1184512410885241804020700b001e010a0710884071524144140340324460401100280e15000c2622a14104910120241c00c41419401c1c6181c0308411010900809018854540002514080440c2d9070503080303406101500061169100780920744034028007940c18444100101d400150740200c101d032041d416a54000340d40c0c00f8012000341605e41c190400d4089030301400910012500f5045060b401a6514040b02c40d001484900b058001d02c0d02e03c6d041c1180c1000303581103024045041d441c64880c0c408440c0422440c5c2c1c07956544401c2405901c2c00a4502e03008600040c5001e000c1c1d13000007010801410823000d03151007980015001441c2006008134060040207000801c002405450714091002500c00d0740410441c3c5403507500e000052001d409c0d581d07040e000b40501d484012000c000141c02a200d1781f4421135400c4c410100302180d407401b00070341070f44a0000400083c0303450b079201643d900d0707580e00783c01200f49401c101020080d100c2c034039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 936470935 1250 936469685 936469687
    0x40c0c02090a020924033c0a0b041e0207020a0b04080303010519120f05120a020a1104051e0a1407030209010905120d03050417070f03020c010810090f091401060801050610200102 78
    0x5074105529800c50247c080c030920380901d0400481d0054501c3d00041034055400c00498801c0000c1203600e0b40c0c90300d190a1001a1100440d0000640d848070700e44c0868406000050f000c101d00300e0200003141a600c06440a075108502c0c50703031542000031a4414050910b24400307600f80003502603001c0d00300241c020005c54042ca0b080c030704900b806034849182d0b00007680c049181c1004200b03040080381c6102c0f800722401c00c003c0c5081b4000d0b40000b036585c401c42500c003550100180742c0380682d170701500301703100d140c018000d5516107001c001d0020b40c80320400d140401c0340d0302d00000e0f19140c440300c020740307262104000c0d2101e0084100150003400c0d0181041f0b0740b032a00031580c210940710403006000343c24003590190700000102c0c103000c2d04050403038100504120908041181c0105024001c408a8411880008581140c152440001c1020000040600b1580c3c501d841d80c2c4601504102c0903a01000c00821194450404002402041404800c0820241146151101e041b1202c043c0000c0e0480005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 936472185 1250 936470935 936471001
    0x20913050a080a02070501110703051c050f070807020f0d0210180e09070e011706010b071401090320011404020910030f0501020310080a030e040c0c02090a02092403 72
    0x10310b42c1d00540200001688603a00821966034010b51584550a4200103800c0880c19a100c040d150600000710b041880907039190080c41500c45c4086400765080d102e85ca84e10f0310458a4405076503401404280d1207054100c0840c21280750200d80e01103070310b40c01001c0320007079107500300159009452003c2001c042c000c80381c80000d49a801e220224812904400a001c001d41080030049005a041e0041c45080c0d11444048c844c846c8005105415a6060078002c2d48420305445c000035185900008010654284003100b401c140e00304031a0280301c82d050448081038100c40c900c0c6030880307919418600606000070042009824021300300382d08080041c1e07480040e661603840d0819901c407078010031100d03a9400000c000303110b84070b03204803401350403440d015051a030751a0710010400c1501c8140580b00316900e4104c2d2814602030110a04040e90103015101c081c42c1c62008400250000040903008001d06901c950001003030001d164100c42030343c86000d0454036055441c41403e20305a03d20445402c0c5440c0c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 936473435 1250 936472185 936472193
    0x1201150306030b0a050f180a03140c1009140d0c080c070e010803070b01150c02091512100b0901120602030402030109170d0c0f0f080c1b030a0f0c020913050a 69
    0x403403442884003140201d03190400711415441b0320001080449142402072003400c80352400b05071607603010342524080381800750590b0140c3c250710800f000e40c0ca452181e0f10342089000d516801c0742c400d0a005441d01c100480d10360031141e840350010402940001d030078004e0400001c400380b0142c00c4201e541000c0b9080c26850f02e41c2d0100d002d1082e0021001c3da440858403100b0403160ba02024090004800e41c8070001035001c0c0003400140d20039000a101c0c007405000035000f0300515101d0a4105801080c8100200015012a032648940c694442c0028105401851141082e001107412640080c1c40e50a84000540710740000b9040548102d03032554880b140500483e41900a40012004030940b05554204a912000403070720a402620280504102903002050300102050070750f14060070a10302a684884428002c1e102d192200000d400c0303a581c00002c107035400130142c070f651000ea4440880700030004101343c62201d1111802581b114102000a5002c030003580c03145800e600c100110355424802d80c2d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 936474685 1250 936473435 936473453
    0x5061c051801060f17070e07080a090203120c0601092c010f060f05040e0703050c0607050109020a0b03041b080a02040e0c09150a1418040816060f0f02120115030603 72
    0x40040c4d012400407605003d05000017808101000202d4010120286020942152082d000f48a1800d00a0000010300d400c40b0981012002c1780e8003c068881e44d124000112000760410306840c05244542e0002040c65078003071003aa40e65407101c04107101988200305181051800d248410301c800e54a07044860003516642c0180400344c0b071044404007030b41d41800140411039080e86600303052030340005001c00104001262001c6009420b88585983e051f80d424018050501810700a4201584030b900140f024180c0c005940039512460f0140040003114071301a1b02841a03002d00c3d90240c012080e0700c0014036280e40f02044030003440c1c2c02d490100ca21080040d90b03800f411181e00981551401c2100d02c24039001180c80e01500c8040034075440000e840010406208038403040074003400c6001c0106041c03202070000c4eaa800407824102c0c41c03035509549031074409070030a03c042c80186400d000b05404400c1850080d0341018807201d207109000e03844c1100300710403006005959400c1c5981d480700400031448070710b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 936475935 1250 936474685 936474689
    0xe1303120c09050f030a0308010306111201121b154e0c0503040b1e0c07061107050307201216140306180c13090c05061c05180106 57
    0x5102d03100298070309800d000300c80780704d0800d261003a00480d442c94002034001100d2070540e81c0103840010030800d07000340492144101e4401402c03c0005800001d40c0c0107801001e0302d103d51040100040c0c00380941da485503061410700503105080f00c5250703a09100e0744240c2c080890786102c1c096143d5402146409030f22141c0c0f44441000d08000030044000305480710702d62826840706007600c100105000036000610500003d080240540c951030b01003500c902800c3c407084484c2900f503c0802c52420480c5442d5280d44c0701c460204e130164100076440040b44d0010081d10b44064110002c3c5242010307641d0303002c08084400f00044002404a140241c0079240c40251103640c0120300024081400051110000e903651a401480001c032003030700c825000c0c1c602080203500140a02100e00e00d40c24090040c41c12307c11900e07401d0703402131b07031082280b40400e40d282c02c41c5410500a0018181590701e81041c01800e10030035041807035080601044c02c8000006500140c1d003c441c100c0340001c0c541da01a091801c3d03601035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 936477185 1250 936475935 936475937
    0x50405040c111509100e0304080723090606030411010c05030f040305210a08100504020d1413020a15020f060717090106030308010b0d09050a0804140603010e1303120c 73
    0xe4501a50b00d01e04120001c4955507221400d0220b2070310a411a6507030a900e0150382c0d550380c171061010344100e01001507502409800c400d4880345030300c51301240400c0300e02c0c4509250801140c80e24010305d003458600640501800f422461031560303942c841400300c40440a9050411855223300000304e40180003030190701565042c0e0700e50b650310398108549003c1c145602e2000406903901523240407852801100c0071600e423804c00704466921000340070500d82080c1e000503046170000a00d0255101c60b94400d025507849013080704c800d5226101c50540400801c10700940240464200b40402200194461030142061040740c0702018000640345c28440251010b00c0821140072000c3e600c15003140029501c40300f50b100170041d0915544000b05984418400c440300242d0004031040051300d5900071041140d081412100502154680309020758400d1003080700ca402070f031000c0b858910300f05044a048401c00c00c2600c000d0340369189030700a02320791003904400b0300c0f50b010052288070b5450301030a0420034803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 936478435 1250 936477185 936477197
    0x91c030201020903010e190209040305190e01261f120f11061606020f1b061f0308030c18181609080d0f0905040905010f060e0105150901050405040c 65
    0x250105060030350b50141c04504264106441032042c7c0051014112040e0f50103c4244046851b5400c080d107003031080c4400007110808207a2400280b5801c81514088440c0a0383c40c00e5000c8800140b0b5143d41d084544a845260400c10114000e8140300203040081e05159907071900b0380d0350381d018608503003004000c1107448a1001c02e0aa040c486800a00c40c030141c3c050381c3c0280b1306040d8800c0e940300843c03160300051850380d020590603e07202200303042d500c070807038240c42044900c0c0131803e42d140d503404211140221038038040a603d000f06072407403200341120340c07001c45035085031101896020a60440c04400381c510080c10101a0140c0e503804000c1400c4c030800341446124104007442213046480601071506000140b40108154100080c0002e00e0400500c0d02206c031101e1800100c034010141c3d40b089912600b003805d4101402019800340c140c000f40f1800800400d50355100c10507400200b40b04a07503101461050840c0540080c00c002e01400c0014585146090741300e50001e0101c4940707020340000104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 936479685 1250 936478435 936478447
    0xc03181c0c06061205060408071122050901020a1407080d05011203021002090f01080601090923090a031e030905060a020909060d120f05040b03010b031608011a091c03020102 76
    0x4880c40343c3c40203800c2c1c03a000c03080c1d41070340794807556030341c5002510082c10f00303400150010a0040c1141c520a50a01c0100400300b4540030199403415503032030ba60351a45603480d00000c00c00180052003102d500021540b80d50604441007044480c0d20342080d038003901c1440c010841c2e00c00207000c074403440b80a001c5040843e41d54041c2801e00030315080b0b980300c1e82c10307419204000040343d17607907200810b0010762000d1038501295074401c40100c515040b143d1040c030303800b41088040520710f010030702d002d001e444000e5030000c05581c03078070000d0b0382d9150b1842e0050081000b101142031681a0079a581c00e0f54111821301090b10415a034450b442c2000856601c000d40b41e021a01410300e241201000d41c000900301c41d91401010141c030f1307546080031740600220a1003101e400744503125015405440061000c40c007070b03585940e501d085001d865807003240c1c82248011000b145244c41409085028140c410700c0d2040050310340b107200860b4255000041413a8040408030f001c03a4840d0b1170060361120f0380d1082e170015803504 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 936480935 1250 936479685 936479693
    0x20c0607021c020606090a0c210e0d1b08310302090703020c0c0103050603250509060d050c0d020a05030d0f0813030206060409110a03030504030314030c03181c0c 71
    0x101019118003c5410040501a042e51080751a607004608001c00141c0c2c7c80034040d06598080124681c0507026004002c610741004c505d034400c1040103a8081a20003103036120004441e80d0340040b1400e200300c01c4101046000c07a01c001c0207401c10341c1c642d0048000040e02c1c4500e03140003009801005e02c5000000d0814021400c041300302542059407401c080d03060140c1204180e071213448510b41d690401d552500003507000c1e03404011000620340312840500312801008030103840d44220340280b60080700044041002070915041c100301941c4c0100c0034000701d04c4000704002080c4040002680e00c244605030101c6c0d5a5024095039415000e21b80b07484100120b4204050161100100103249513070100c5c202c41e0229402161442e4003500c12900014003190f1860440a503242d11151160060030400313011041540000c020006d5901030748804580528a22401c0842d00c01100d8503c50b503941131012501014062908040b608041c030151440550103030740c62507070000160720310800160240e5140c1d041c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 936482185 1250 936480935 936480973
    0x1090f080a0f030b330f031005010513031b0f06020105060109061112030a020706050c03040b0c0a0e091b13090b0405060d031b0c090e0d080f061003020c060702 70
    0x245840741400e00007080d4400000348101d00d51754030020b84100b000901a95a000840c1081440a50300c02513922044031500e506030607041241d080c0c03502500078101241e1503004406a488402011100500742401d540c0c0d0280d031000c800c4180c101c0000c00b4030000c20100780d020400c40141c002680000b4a0380380000006019080540c411424041d0884100d90707280340205000c00030070b10180c811556901c601c48030344024490990040c104034502028000c0040200c0c004502841c081c1c0c000c040305484483d41042140700c1d080f060804154101061001420f1402c00b159100d0101448101c0000d140c149140c01c942c02694104400c02d9403d0003130100705110710802d000074800b0b9a081000c0d107007213004240c800f1080c1801a0900c041e1007a034000d00350b4402c0c0c80848650340b1074010030b0fa003682c41c1c030742c40d0207003c0040d004400b41c054860031303035149841001d655200f1101c03040032001700d480d9a02404058003440c1c20b84410180c00300703c80840c4050401c59075008100a0f0b0040084844000a03440c103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 936483435 1250 936482185 936482207
    0x20a050901031a0901140d0609030305010e07110c04050601020f07080f0f01020f0f0913091208150d02150403050a0c0806091b01050d02120411130c0516020301090f080a 74
    0x41c0310369150707840f8480d2030b1300c00514107492a03400e1100b003240207903000903a6440340b80c0c4010310307117401c0107404001c1691507000f00381242d001452054040e1510a400d50780d440c2c0909040903603a10400380002c1c00c1c90b043d006984c0220741801a2400f8062028856092948a401140c1aa8054200b0350f10111042001070b000c00a00d100850030001100711001c4c0906c18010800810600480c2aa6442e80c42c2200140300c020410400c00540740d80349008071480d8914108180403420410000e180d5030101000c0d06440040201750500103c49036003081f00d200c0e034246075004544000c1c0400b00000d80c08004002d0b0540c020f00708110114649000720b40780c003100400401f21a0040309280065402000300080441d000742400341e00e4410201080e4000e00400341003080000c40b00c020b11040c025401501c1102c140b00b511075001248a14400c00242c610414401c0001a400c0041c3e1003005400c1d040b41b80b031248004c00204400026442d0305900030162201943c2500f40020b6910159801c18003442d2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 936484685 1250 936483435 936483461
    0x1030209031005071b0b01090b0a05030c04150b04060c12020f120c0109081210090506100315090c0513080607120e070906060e03060919150e01020a05090103 69
    0x214011403140482d80361030400c0301003102a901c0d040481d83c41030180c1c43e8031000e01c5201c15145190b01041c18610b40700350302032043e0070b41c3d0703403421041707243c0f500380f05c1091400d540000e0001e2018182a83c10b1000403c0c042900421a10101b9008207030901540f00400007000c0b00d6848130b044d158a0f060166200c0340d003080340c0b0250f602410940b0924003000c10f1625038120001e4080b600c50450218031805044040001840100d0001701241d140181034030701400340190442002c2c400c0c0e104c43c20b81086030420703a02c13264086104803107016107074442e400c2400c0d2840101c40768a01c00d84c0d00d0881d9020340300c0865000020510209074112002e000c01400c4000b440010010402410f060700003401400e1079800780158a80ca80032031b0100c22408100c00b5000b0031200c141044910760307460009100c0c1504511180c0f290148902140c0c82060000300802407402d004d100545030000703551103041074a500790305001181d465800e11040c0440c288043c180398006a01c505981d41012400101103c400c080c03121 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 936485935 1250 936484685 936484687
    0x15070203011805070620030a032406050f1c1418150c0702010302090d05160915170f0a0b0402120a150c0e151b060103050d03150306050a0515010302 65
    0xb000701d54000741d0803040725107904107410080100e524001e0111400d10441c2218440011803403204c41d4143d020104d980e00c200c0b280c0a1525944100d042c2e028401d00c42d000010b0000e000c070701d041c043d25000402c075406c0c905a0310382030100c0e41101d600649009400c00c5103070b901340108006580300c48001403d0004040800f40500d24103d400c200601c51014001d0002c00001040e9242103900940c1214003003c00140280d031054402d142982c0d8a240700c1008451158086000041a00c454000c1038881400c0f0585201094100484c1d1100d20a4001c0b09440c00c1c811a00c58200b001c100340844180e1502900c00c9030310900c2c041c0103010000041c103c0300d54050b4041c41160300401d880146801c180c4510500100d410f0646044c02c46096001030f240030f6000f0340c404100d00380405110001d00c03504090800606100014130740e0580c07100e100b444040d0064025100c8605070a01ca648210f460040c201d2403903444039102d403940d104440c1d0880d40019003070307945d0051002816150040f036410590901e425 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 936487185 1250 936485935 936485981
    0x506010f170406020711090a0e010e01060e010510021c0c020f060a050901086607061407020115140a0e0a09080a0818060408071506051507020301 64
    0x407200c52040140301900c6140d0102e005c404001c188121402c0901004055602d01d0030710388420401002d406070b05448a600c0c2c800001c50104c01070040b4001c65607518007600305a0310b0882031141603041408502c0441c040c040d503030200048508206440103001d99600801c2e00e940e44180100c07000001c2a5501c14802071003104580381c4d10504440785640e082c40e000c000c2c5c0d282d0f038810318000e5580a001c0e240071407031140301c00054a940d01c140c0c0071074940d03a814130307109241d10301d9035031410448000c4154240b0b4510340d98481d411940c00c000c00b56107200d0301001440c280600b0321205550700940705a0b0050b5126908a0b81c0006040108006011003114102c2007098a07400181400d01c01e21842006001c8070001a14003c000c1e030201a501e9000424965160008140202801c204a90100b9070045901100a4000e4005425441154480541840c0020355201c0c2000e01c040f403048644d05a840300008141e0f5103c440d0030a034203189100c1410340b00c0c401d0781704040c00d490403030350144c2403001d008841c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 936488435 1250 936487185 936487217
    0x109020306041a06180a02160501050705121302030304051012090b18161202040e0709060f0b0a3e0f120c030d090804091b08150a0e0c09090a0506010f 66
    0x280917007081c00250012380d106c0c03010b410380c50080c10220010b4600d51a210400941c00d410800518030014403054180103545d030102078039101d0030f070008003a403d64003d01c02803010b4244900010010051820001031524486010705e00340c441a030811105440303d01c0c1402520f4900c1d003944100d8180390000b03840700c1140b254001c404650103109600401845084100c159251603010358405450a400d0700e1005071510301007800b8051600ca5142e40b0303204c040e000510120030600361040b4420507681e0459416140358585002c4014540030003070311244c1c43c1070b110200c024202003c81c94007014050001c054442c0c007020300f0281112a510a802c06c1000034440c2400048203c80d4a00310f01d4100041c807110500b404981402143c02140400385411004080035860303290344401c0940a641e03104181c2e9035104504400345107118817070b82007014184c080c00760482d1081e00f0f82d03101c4c1c00b02c4000c508103689000000d03860b141c2030310070b80c42d08c0381c1e5203062109130359001403081505041c82c14114804050249 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 936489685 1250 936488435 936488479
    0xa02011a01110c0f0d0804080a02100521060f0306180709090c05210a050c090a020414150f0a08011409160f0203040302150d06140d060e0109020306041a06 68
    0x46443c4544001a913079403280c2d80d1040c00c1a890750f04803400a45482c0c0314015645c0d2407556038416485100a880010903461054089904170300100c01943d11803103030035502c940c0003400a0701c039550000b0541d0310135a072520104500e5101c0c0740c2200307404450b117104070107160070000142c00c81380109040c41c0c1000081340d041101e01c022540c050381e20300f01c0d9150601c008800c03030300d01ea18421000e0041c3c54034078092090004681e8100d900031645890541c07500ca04050891046102e0880411354200d0740b640300b0320b410070b400c1c0070b1003004110b5285170417203078240d0003090b6004071058004a06088014840c0798030003a003454180700700f51041581820b009411001c0c00d07014440000c10414241c80003000c040c800e100ba030700211740c041d101100258107441908120303044000d035003181714030704840003c4c4400010310141880e1405020a2020100c0f034440c1d6000d4403120341c2c5a9242c0d926003008800585040042c240324a000c0e03800220048581081c0207080701000e04800d100f0014105250b00b40c0a21207 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 936490935 1250 936489685 936489703
    0x207060b060a091a040e04030f0810050a03060902010c061d0c100813060b030d0c060e0601030804050f190306020316020105041a130f050304150c0b04021c080a02011a0111 75
    0xc0f03d20502c021040c4030300300c118030494000f0403031b48003070900b400304042d000340d828032040e9010340701c040242d0f641040c0e01400c07490701c0c42810740c81050380306e0810200d8429484581040d006162401181555403181ca05030342c5494000c00d03031841030840d9521003c9083c8a0900038400c12560b2500e40c800901c0002c050080280c41200203507000605d400c02c010482c2e0082d00c03041d0014042c4c0e650711420843c090304080c50407a0590b1030f43d080000d80d10320b03a00d0104034141030b6035001041a04007810103040c00f40e5080702c036280301d030849000d07410100504600c1044400851081001598031301d03101c100c940c1560340700500c10017568105011b00002403a2040c14440d0300c2d140703046801071540c0d224064081101c50100245c214500310104209001c0084010401d0b10403818211122b0107403040c0031260324242810192502450328045801440c1c403900a82c1c5103154140b07032a08041d007a03119480964000c99030040543e43d00c500c4032a10b4114414415184082424005048800ea80c65180c50700000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 936492185 1250 936490935 936490949
    0x30d0618060506040e061c0606091b0f020604060f0b2d0d03120504020a150f031a060f1810030b040605010e0d030c021c050105041a0c0f030c0d09060207060b060a09 72
    0x504000b25440c611104040250750020024131481c0d50f41d0707c05500800c6041c4500c0c0001b820031003480cbca0790f40101c081000340360451f030080c02c03950b80d0340d11600010244141001c01c0e06032102c040e400166034000001d00403022140440389032404003468007818800340015a8000c0030285001000300b40c201080c48100310942c8404515680e5620000d101c0560729003003014414803035460310b00010340c04008010410156103040205104582071403210307411241d01664070010421040c4107444c1c0e00c4c0003a1603104020380341b02c2d10b401e1150001503801400102c2d1440025560030401046143c90301569005120a003032a1a600e00c4640201d0800d02c00303224041d0078450001c9224046450b034075020585030b005034058441e51070031481c141e800790105071402d94515080c0e842440c1c0c40b0200e480b01600035159410a41d14100c04c000189032260001800780705001004d10142e400714003075018101010340306500041e644d0400740380600880f1407803c0080d014800a0150301c0303504c0d4001c0c10b01420b031001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 936493435 1250 936492185 936492199
    0xc041e08070f0807140105040905070513141026040b090c0a0b09040e0c0a080106170319260a0b100e060306370612150b030405030d0618060506040e06 66
    0x5c20040c0d0311446a540104616454507041011250384030000d80001c2040310043c1c10070340da036071856202c25600800220790014884904a4109014011f1034205000c41502d0103101228002c0c0c0142c0504115016941141c0c40010018000400c0c0030725000001c0880e2050a46814000080c03014014892030a0140b0399409034030402940030050150140c00c0208070003003641e168034001d0301130a000d100390590080011a00000b0032008030a680380241407800003c000d82004904960603c1030052041030481200d08030b8402d100c80143d894442e04101502181c00000102403090352800f4074211403c000202c4645000c50340e46a08903500b000c0300b1507401500c52480e01000c2d1140001c2d5001140010409403001401c60b140c80e00b00c000c94800c0c2d11940c3c640746d40750409200751070090716101402c1c14451421300c40c5c030300d14401658001740288212400c201c1144500002c0b20740c55080008012000100d03985070325000e0054402900082d940325040c5840c2000651141030007600f0580709442e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 936494685 1250 936493435 936493469
    0x60b18250318060204230d08070c091505090606030f1b090d0f110904080d020a0e0d140d020109111c050730050a0303050c041e08070f0807 61
    0x2110760004180e041251603a07100b01d44031442c006000354403500c24800f403a02000390009000604202142c0b2800014042041090860380e441c48181d02055045a55001e00c1402052403961807042c41c0102e1110200380d4035803814901080812100142924400e03413003002000001501403000c1c5400110314955030904c2c00c08a0110b1207503002e0f0356a441e13009440e00514406211001c40314005450041e031001c00d9240044040c4034000c42c084501409482d0100185504a01c4c01c1c0e000380340040c0e041c68110003c0706030100182902c0359002040d50542100160079000b102c0c14031013820341c81d02d90b0000300000400b0790740b4621303071041c1c07110b01030321540c00d50451103910700b98440c00003503855100c02500d00060301c43c0030080b103d4803000f0ba0302d22203207103604802011100f13005e01d1a10081d085001004464843c0e0b074100e003e01001018260715004c00d10000074030188940000c10014860110304005e035040200c10303860141035502c040b80c05032402c442080990700c0801c04070144c3d09100701141a5034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 936495935 1250 936494685 936494687
    0x61a03040312050709050628020a08180d0602040905240307031b0515031909080301030219030813051203160212012c010c02071a0d06050d060b1825 65
    0x405d075104036005440001d0600c000c07180216000c2064003c03030500a16a10301003422039603244c4599004008031402c102071000308810080e0003503d00c4009160b48589620740da01e09050343c0180d40080d401c0e507180c0d028015212030f030070b07240c002110480e090311070180c0406000035a40d05282c40f018081c40090000e100c648000c4840304000340c10081c21400a510341001c980310280c0c0b007115624001c030140e41140040703520601550000b147c100100c0c5003035908580820151100d0f504800341c20030f14941c40000081c0402018106984850b50500e4009181c8014402d440c4141c400643c8160400c003c481d007544044480e210762260151208a07002428070707821401040c0000b2003050380701ca206a616040d03003d4616034000300401c44024482c0a28800d416aa01e01580c02030364894490b002d0340003440b0b8401406041d42114882001c84d40c0340eaa0804609001000e62094903d030352510030641c42e0341440d448800034640112280c96481ca0320740c0d01020854000d91000c1c070140311a0356010801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 936497185 1250 936495935 936495947
    0x601020a2004140f06090907050901140103020c010f060816080706080603120c071404020a0f03150504050f06091b090d061d0c040501060e030712080c030409061a030403120507 77
    0x950f01c80e03d81c407251400c09402580303110a084413054414078050001490b801008640e4100702c4e070003e403804000c0d0f4203000203c0c1d080103030b035442c09040660902c0140d07000700c1c0034090090f00445082000a1207810702044905040c0800200c0ea04024448810040840c0c0080e0040c01c0b95042e01c0c1034042600d4032000030341828801881d0740340c010300214400040d6040030841c4e20407140040d524040140c40e0300b00340002d9010700341132000440c001840144403a4000d80000560014100741c070b078a40303610ba4000038103c520542c1c8909a501140b0100441811302c41d2445030403203200352918102c0c810a4840352030612503181d001d4040c0f070550390340e6001c02605070001202004084d061245050451200a90707400713071808014421070404000203126400342c0e4440c1070041e03016001c2c0031035504048030201120401102100e0030301040207100d0320030006101501c0901010003010407020b1501288107000790104210940c0040c0800030700c000a0b4115105072241d40e81c0040c007107214ac0d907001041e41c1c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 936498435 1250 936497185 936497201
    0x801090e07030b0408220810050f040b040201020c27070e031f14010905041703090d111507050301090605040605180916080a0303060f0b070201080916060e090601020a2004 75
    0xe521034a402251006400d01c41030191060307c0201d42012005d40c0159043d030380c0030784019100727001e4100400d020400c1c0c1980d043c0c0c01801030045880070701216000c0f54500e544481413030380d198014940e081c0900b00100d14148c00512910308038603181e40c840000303a02c91200d610021013881d004003000c0d16410890708020304c40d101c00080f444496a440c440745001d4002250100c800f2000207100c40200364460007944c0c000c201941c002e0200180038002561000f4500c4041d50440c07083c010301d00c42d803400b4002a01d04c580c180d035480f56121352402c240130065640035004188500d00700b032824407041d1542451003054002641090000391100400c40382000c81510703a0682040000c0c4e00895030b40000a0819143c81c402c0d07030200617a660780c0720340702c80a50380c2e070142411700c1e541041b202d0055803181b86040d070000d400f00b080e91074090010782c0c00080d0102e298820004140b90040c0081c0516103240711a500c03242c280041c04440100b81da4049041004040392140c3e41490590a800e9480d241d104000d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 936499685 1250 936498435 936498457
    0x60f0602300a0306140a030819110d0908060a11090904020d32030f090f061b0706081501200c18090111070b04030302030411030d0903030801090e07030b0408 69
    0x20303549551002c024040d01441c001d041582214050465803400c01c508180202e80d008001c5608000428034002039105442d04201d042100c000d501e00c81040f814002400609170b13546410300348a140202560400c1c10080130b486141e0300d0800f6164580042754120364521404480040483c0d84030300c0000d07420100341c08081c00505c07220000b200038140c0c040b00c4480307041c102e000c8803040070b00c030300300c8a80d91340710300303000307000d0030842449050403d0a00c14002c04540e60014421410300003000480d13603013a035209800c4000d80c0d112401c100815500090f940d90403002caa1004200800c191001070702074510101031105240418900da00d0316075041c8100010204010440508950003407500e54401e442900c90185952038075900e030303841c080f441c0c003280c00040d0b0013500450203540301d440c103500a420080040e03811500d908403603045642c0034085c022881000d9169151941e0a508000b0140c0c1d03816085000c60901e020428810b07000d00040c03680c11a41d01000c0c40000f65241e04d450007550142c4403a0300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 936500935 1250 936499685 936499687
    0xb060d050f0a180302100f0b0d03210b032508030a0504050a0e10271d011a030a060e0c030703050d1107030b150d170d060f060230 57
    0x11008009403400180120300040b014040511144244400c4414a94004015a0003500024011052500801722030319240034009016820b1401140b0a4800d0160840014402c03050402c82d01c0c0c03031648001d4290001541c204001d0b0b40c81d40c0443da84981d2940380b000310005440d408181f148030b80050202415221082d6900d94402042c0501140c0041c05003920448511101060350207860701d2040c403034880300354086401494940f83c103004151105190707096881070342611003244110302600039403103070141c1401c9507924200d0306982151144014200b0300f00c800d0444c003825030b400203a2001040d4100f0000142402900c00803454406210303c0c154150149040020600c800400c04070203480c41a220640811445001140c642030785000041070350000710f0210b914800c10b0740000103c0c01001e03152801c1038159485180180d8502040d46185240c00560700803032000d00d00498004003484044101000d09209000c0c3d01d070000e48181d244800016440045600300760740c0d0001106031421046 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 936502185 1250 936500935 936500941
    0x80402100c061d0703150c0512040c030203150411032b02030409050c0306090a051b0c160f0503070501080123030a0c0308070c0806100510020309060c0601050405280b060d05 76
    0x3c1e0751184001c0c030054440121280120550b000540220071003ca4140c0e201c502c1d240c04803100e81e8402801a000361400002c4000120045c3c0342040950745440000482148074a410326091030b45000302c016450098100703441104151040f0645802140f02c0b000200c0821518070408030301d5401a540084a010304242c02e203d664101c60b4001c43c0908030955403164180c0d01c080030001074403400c2c2ca055a00b4141020349404440c1f8890180c08403580000a80f03039a045280708001408413503070012812190510320400062508100044c01042d007801d04004961400d00c0300e6041034500500180502003d9445401a90f01801000b8005030710004070f4030700b00c1d26814480c0c07954001100403111010320110100c0e10308030000b8028842c4002403081c154803400c1406002c44454203100070810744c03005000031403503a55040040c2814810807030052180350324000410055800290501c0100c901c8000300a81912044481c0b03680c07030510a0011403441a5a008540e56218204a082e225861302c000c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 936503435 1250 936502185 936502241
    0x1e090105061b0a0b0403020d020303040f0b040606090c020601091d100e010204170d031d0616020c2805060a0503040602070201090e270309030a031409100203040e07080402100c06 78
    0x3075005d580294226082810445002e83c1e40744010794026121190f1071108000044000403c2680140700f014042615592023340c4002d6856100c4603c02680100005000592443c0b183c0081ca03500e20800d078081c100302d5100c0940764441901004d00880c3c46444460034200700750100e078000c1075502512020741416005044d192030390900480d000905002c51030503170780c100c55041c040841c8001c01818554803801e580c03800c5451800d00000075030149000503903907035465220010408540c46541e60010020f0300c0c041c0424881904818801c0c881807120001d2103a0103011303030341e210750b02120043c0d892105000585101102d03070301c0660f440522004010802c0c200b80d01c3c2d650030440a01c0e1403010112626015a240c3c000c03244600c1c4c1583c480380541004c03a11503840c8502000420303c050345400310724130100700c03261340300c19404015920001d0100400c1001c1c03049554428120310384050039042c2680003c1103102140744490400c4070043d40f580910060b0f6210100010324421840b01e0f100e070042c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 936504685 1250 936503435 936503453
    0x21207030c170111040e060130110f0a051c02032e050f040c0309080f030f18151f09150902070506070305041a04050102091e090105061b0a 61
    0x110001c4100c1c0e20005401d03002e050054426942c880c030b69131410241425480d42041500800d424100194a501407113842c1c040300045a4020818825440c402c0c80c011000c010782c2c601c80ca0f549120102008480c0340340315014283d800d00300c0c181c17800790707904c155040111aa40e060000440043c610020074015000076440c001c00515010042400a101440e803d90300b0404061040581100d2303505a90302c4545000d60021003444c06500f0002036080c260f07154114583c00043c0340308401d540010a118040d5110b4141e40e5001c016102240300f0790f03640801c03440c2c41d480a1400b03106440f0448020481100e000c1d102c08071603c0c00c82c0840180c40d60f071024180060b1088040c00a644208002e010036200420b000316030219403c075008041a84440100f100207000081c025100303100c085071310030b0341c01ca20000001c1c00340b405500050384500c1c00c2010844a0359000c401054142140c054460141d241c110142d41101c0b4216546134480340d08904000c00914611a070201c00d0140b080c0903070400c05800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 936505935 1250 936504685 936504689
    0x80403170c07171306140408010f0f051602030a0503280b040501150c120c021008090105070e0d030305090106050613140603010e04080901020a0b010801140c18060304021207030c 78
    0x591200c8880070740790000d0500d842112000003001d0041344c000e01916004200104060707040c41c240c0ca20309591124480c4c03c41e0101414226020740ba2030280c04224101d000e020f4014007801d8800100e80b50f4000040d58030320605141d48140b20740070000444611940c5109184c41040b900c03e5170141002c806180010892030b1a15031296103404004254000b8102d140c00280302c1c5900c441022450640f00d50703140300e00031040c3c041040b541c40c0c1d4040c0107072116080f00d91521815160b0403464103080c21054203465009020000300100d192808070135640718a44000c0580d0182800113031912007901081c0584180e801560304031000240003218001100010021240444403204a002e1200c0030451a44003e10070944c000b42180c0c00305c1e02040c2910000e100181050044800840740c5a0315002111400d0340440084d966841f011040011550442640a40003000784d07072404056510032000c000c581541e090148501000117411502c0f80001002070705034200c1140c08941c2d403440d10b56600b04040c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 936507185 1250 936505935 936505943
    0x30c0c030332040303110a052a01030c0509040c1106160e090105010f14070b1321080703180606082107020a0603090f0212010227090106080403170c07 66
    0x203254214681140c0340b54070303100e8000a555051900349541c50480d000e4003c280f205459000708401c44000031001c00c080c2102c0c0c00d109007003949904506010360b01c0001081052814941041e000388080740d840012140000720440b400661061114804ca40ba400b000607407510a110311000e0013007801e0380c0300e40c07400c900d13500f6550283e50b40f10b210280035182400f0300c200383c00f2a007030405950440d8003c5802e0000c0305602c03843e00303041902c1910b5104c9540001d0342c1049080100d01540b80c188800c81c4403003401044100758401550b51700080051041000400e244205980c45070741110190101d18405007690308608180400f0303031501741c010303100e49411035051030302c3d517258018404646c00c40c0e094070950b580003401160010314041d4150003030100d0180407203401d40200c401e500103035512942080100928000103072603c036200785d4020350011310348840022a08042c1001c00d6507444110144c1514280d2810141c5a201c62400307a401441c017180385080074483d80c080180b070b1031120014006540c02 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 936508435 1250 936507185 936507227
    0xb0c03090118021008040302030c01060b180102011503060e0a0203011b271404020d15030209010614250503041409100605030a09020102070914060901090225030c0c0303 74
    0x12800c410b40203844400d00082d042002c0c10b2003090741030300030311095a216004e0300541380781c414030210746800c41d43c440d007141171150b4004c00d5604142103003907500c1300200000c1c0003c2204000120211914180501c0003c00300c03911a040c14400d580c060140800140d4094000e015030100450f04c0c0c44c000340a0003801c400604510214a05229202c49c07456564000200c002140c60030700700820918601c1200883e081502009824403903081303032242440b092440483d00e62240e003148100301d40ea00040e403008041241070004160303490a00000c80382c506104403c000150400c0c6051249510318070580541540004240001c11716100d00211814080c2182d0b031040c2a42e4440d45610f00c80583c0c0500b100240081c0f0004600c0c581c2c4c0da0240f40c1c941c2c0140111040c0f00e0755010310400f52001c18844041104592040c00068280100c19602400314000306600f0f0041040495407144100c0b417101501c002b0380da00030b2007132500908141007000c2c0c02c28000c2c45c803642c407070501808484002d640c261110340 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 936509685 1250 936508435 936508451
    0x402040c022d01180f1401091a091509070b0904060b04181b050a030e0a0c06030b01080615090d0309081c020c030604030905060702120106060206010f1e031e0b0c030901 74
    0x134024400401076028a2a4200e8030345516451a10300c400603444c5103541da100107800c04a140030590340000c60310303400e40c1307615858007000b41030174031410405500b8010350704000d00c6007c078400700300302090b1a04200615180c010b00c90000703015007540d9009071b4004c41c0c00035011a00c40f4002202e034904d0403c84c0014410a61000c020850300e00700c049500c40096028010051268031036000348038510300310780c02c4810401e29900c60b0401c000c1607500c040702080e030700c1044416a5130400d040d298030480c125803040a1200c40708540f03e00c5d1082d074481e1880703010081c840704d08250007600003202030f0078190201c590005034201105104120304a02c0c07805481184000150351400140c040c0c82640d0665403500414a01810722031107421480049030b1080404c00600580d500c00d100709001082d4a0340207118a5150480d100c2803035900350822008041c503050b030031100f0300ca8400500f040f03c0d48038503590705140941c2c29800b1005039918000304512513160602c00c2410180c1c01450061801c2002002004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 936510791 1106 936509685 936509711
    0x12010c0503061509060a210903030524150d0f090f0326190b0607050705130204030b0a020c010b03060906010e010f0e0402040c022d01 59
    0x16602004210b0390349042d07011191110020440c2514024506003c14903c1c4520210801884103003045442c40c030340010403540c0648044101000340008031700d00107005d00340c00d80d0610011054602406205508121030440014005005a4844450018050342c0c1e401190605844903510388840c10603148a01503001900d2051100d07400c20809440c0180c120f00b1440240b28801ca000c0c2007806c400c81301c9180460700a40310510b02c00c901c10304003400402500c0d40107501a08941c1c00715281c0d08000e00000c0140644404480c1d000020b104880d82c50101e00840c807020342005024400324a48100b9540280305081c02407001040e1a003503800030a19041007030300c1001c00366114a004000001e9580003440c0903022254050303640d14906000160042400f03040684150703500e1502c040104d00070070000400380e402c2c04648000c0703075612103e10103558200c090840e0650a10003411100 = true := by decide +kernel

theorem cover : BRFrame.Cov 936330935 936510791 := by
  have h0 := BRFrame.cov_init 936330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 936330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 936330935 ≤ n) (h2 : n < 936510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
