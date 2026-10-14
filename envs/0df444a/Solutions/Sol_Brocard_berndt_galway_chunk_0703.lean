-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0703
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:14:02.604081+00:00
-- url     : https://prove2.me/submissions/1edf2bd6-21fa-44a9-ab5f-ea04bf0095f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 126258992 ≤ n < 126438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 126260242 1250 126258992 126259013
    0x30f030902100309021c0c05150c0f2b05040509060112050106081801050f01030809010c060903020304170c0a06050c01060905151206010e04030f0e0d0516050f0109140409 75
    0x4840403d489a0081c400c60034540b2101c002030003529541b1190015036550482c45582030300c02c5600c1040c0410302c005050300000c0481d031605d05a0030448450a805486180d2a03441e03045ca403003103404004440884e809556011261519040c1c1e59062034a4106400c205407140064442d904101c280b0b01909034506007445160f0107042c00f9100d4062901d400e00400c0c0611404909515075039060405102d082540b000ba0b040c1540d40c401c942035250492070004941d1004c50000150150b03040c09409018503802000400c141c41c052030221000417172006d00d00d0342e01c103841c10400d50004031401e01040814071650150802001ca103001081e001d5851440ca000e075001625640c05001030030f40c91070054a0706125269002030050040d0080b980761a14110744035074000c2000c2c0c2070110102d074290140d80300b0f0520103c490700080001246203c5400e169076221a1b40c00440018491a640803800f45021032148076801d10582d2244072941c00c15900c0002c240e240c0320243d4000d500d0f0700e02000082c407417516 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 126261492 1250 126260242 126260269
    0x40806090c041b17070c0803041202100603020f0108100902040f0518040b0106140d0e0a03031a0325150c030305010b04050a0b03060d080a0306050a0f060c030f030902 73
    0x40260340601c8007044100c1c0c1030ba569103004008855081c1403003d40108040300c00c03000d14642d504070369850482c10341d08040c0810000703062480000821007003180c0b0000101040710300d5422036401150942000045400500004c0e41c802c0106545085030762290621135030000030122120050b90713440c050780c003e0740c1164101e0309013545004d0051025007082e241002c0101f00425010140d800c01c1d84540030405018002c001c20045c40e05c13036856201030300f0411200003000020080080411441111f41c555000318000c0b000a4200b50081040e1013400032041c01129004024251108080c00e0f19400c00e039800380e01c03910983e841c2d00006a2042550800d080e8900180c840240c10403081c0b5000f01101e805800404001c201440240b10036100c2c4841c540540d0f001090040d40ca4075086d002492020021000174001140042c1d404901d0341d00da000701045800687e1803032011500e40d02d000301941424054040000c0030030030381402084c0318282e000044609402c0009a200741c540110f00a48003600 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 126262742 1250 126261492 126261511
    0x91a07030920090603010501031e050a0b07030c0e040b09070309050a060908090a0e09060105010c060b040510090608031e0304020a0b040303180611071802090402030f04030807050a05090411040806 86
    0x4102c01050902c0031000c1d078032031812002040a50b040d651a251200c00d48030350703071100c0e01070780100c4c0c02000000c10003134a407290040001d009a20f008071008010f840c41040600010b210701c1000d904608082c015003105c544000c0c110f401c56940d010044004240316501500d16105250981021a0f400c0c40f4280c107284c05400143e541d540980c080c00b0300b0500070b0b407050120298800400200308408505541034481c00d28200000e0103040c00e154010b42814004258014503010510100e103401d200364a040b42c180b410240300255848502c01d440c0e00a0320742070055441e0301e0f25034500203a60f240065a0261004080e002d0a98843d10035045c15006a00300724003041c40e00c5581c01c0c4d62116203052800030513003858245981c1c1c211900c019250500e520a425051880e80c450300926201601500e40340000644115168544040112200c0905680c1036000c11540008207089902c920101d5000e80d241c1d8684501d440188010700c0000e0550004103400110140000f180744d20f01803094a000300e1081 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 126263992 1250 126262742 126262793
    0x408010506280621050702060103060b06040f090e420103020d150e0a032c060313020a0317030a15050307090e030c070303050703030609091a070309 65
    0x150a02102c1a0040c941c0d01d60241411098a03800140c18000c1040d100c2510f4081c410644841134141c0c102451030301020014101002c0010280d40020000c0c102c03401a035040c05460706c0d000900040f0702c2140140c448580300700d80184540c03a01c80e08500807000f00507080300c051903403042c0d0500000c070752010403500144a0200c0b0308602c2036031448524050b0805c0d80c00703103602e501d154001400200500e000822003207020820b00540240341c3e00000c2c80c000300c1016075540c001c0764a001001e086580c040c284201e04100340d80542d000301910700c03024400c030207090b003441e6484810a03030305d400d5081501207902c18400800030001071043c2d0004140c40c000c0ea080c4c10b45a0501503044810b03503443d4881c01200078072820f400c100d00e54000405108480f10302c1400201402d114407102c1c01c43c03107007202c0400c80f407096000000400d503104005210f028045e9a04021143d21020b002c826500300343c42c094900704140c2ca02c00c0b40b90041e0004290444120b09001030895100d40c1d03444082c0c600544200440041c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 126265242 1250 126263992 126264001
    0x103030906090503160306050612060115020601080615011101020c030d0614030604020f01182402330903071401050601110a020d03030e03070f120e06070b06060a1404080105 76
    0x402d8030107010200c02818a034180030349021034880840c8009440c00d42c50f070000ca5000d4480c00e40c40701041c21750760152070007507850b40183c9483c01d100d800b01c54014820308000280380c03400801c945014420240103032f00c020414600444108201d0070803c0707a107550801660084501c1000280906440a00080340051601c400c800401b560039072881d0003600000b01b0403005940303219a00c5a08402401c02e00e0040b400b08880d0310507074080d13070002500555040501910010480a980104a516802c954454001801ca211240300012403008208000c024402c200c1c2860b40e001e030351155212003142c3c200181919050125280302081801a07551881445219680701d0b07880750b041e03181040100191015540850884d2112080c0613040540d222000e0242202c1801103910041c0c2020a00c400304415040805011469507810340119034034014411850030190140c134080fa4000365410901e03503070300c030a01100350b0190315010104101006909c0e041040400130704041c020400001030300c1e150 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 126266492 1250 126265242 126265247
    0xd0218040e0307050a1415041a06030a0c06030c03020d0c110d0c0c03020d020402070203060705030105010306121212110705030409060b0c030f0903010b13050609010509071403060d08030103030906 86
    0x1c2480075140c00410002012400000d044600c40b58451211844d401c05402c1d5a810070f41d86544644140c0d10301c100f070109009200c1403a600d80c2d428080b40414903103c0ca800c2641e20710218000600d00c030860541004298003d62140c0c0888949050261074a100c400142007118082241c88010030b50319450000c03540c0c1c0821900c0d0340c1c05200c1c10004400321940d242c100d421095440001c1c42a000fa6404000315180c83c5c0544030455030140885070a07080c200400790183d002401003900003442c082000552104d0190f150b0841c81c0c0204a0007600d01e01d142040b079030946541800004640c85800940d0102070950040c45658050b0026640302c81c104a20402a9040c43d801b0b15004482130080c10101440402281c5500301040341140d9200e4540003c07030b000d04004410140e00807020b03010803204040300d81100b803055008544008460782c841d0208800d000040c1d40000014400d80001d91007540d94200664014500070901281c403c6039079551b4021764801d07041100000d0034824200300454 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 126267742 1250 126266492 126266501
    0x6131407030509070b09190807170d020601030803060105130b041205010f06050612040302071208041508160e0310050c0903060a06030209190f090305030105100206011d0403050d021804 81
    0x807000003030418981742c1850407426004814a1310712600194422406451420201400074114541920101c3c2d40d60031000e0b07440e00082601da011030140a0300020000d2001c0381c0c060581e0340c00f205240c2503031034440c011211604840c10781a102c1c2e00c070700004201c452180e0003038001060916103141041005140183c2590705803403d01117158200081844150342d090155003070740e0b110001601c1c86540e0303410100c0c6041050b1744068a0704050600300000d00c0003860007401526500451443c9203203400000b110396a101700c841400582c03440308124110ba115628491003c1c1005003122840e16100e4009001c558090707984500d14003001409041c9400c040c07010710b81c80080d0070700421541c0d04d10f40210360712401c003d15851030400c0343c1e5000f0f081d040f003076404507200340c01444040210807258503000d0703c00d910a0140c94424842000403681051001451a041c1d540b03e15601c1842e45842000e0051001c001c2c00880c240701007440420004116071001d006174070180a1848000c0302c0701d4084c00101d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 126268992 1250 126267742 126267751
    0x90f1506050306060603131e0c030209070206060a05060c01021b0c030d0504031205031306020a090503211602010318050c010e061216020c120705090a090317061314070305 75
    0x90300030fa0304000160383c4201c01e40364440041480c2c4e44030580707545058840041285503200c8001d000d00c03500700078410005031401c2030383d01c00d1701c1d00042600c41036001e0743da03168100c4640340d1108032801c0500040c10180c0107448840b200b070b0300160a20490380083d038031841080310300301129804503080414a240402600714108884c0c02c01d80d10702810350702d80070100c01062180e00b00f07019000002c11072100d1a00c2c1002c050f250000c0045490708501347c40202400c01c4e40c13055a210f4130403a10603440742018030040807240c00d40c1c0c0c0c7c64030345014695103011491803040340c07050b814160f8a00f0410100413801c0c2884280510440103003100c0042c10001600b1400030301d00c3c40340039040c01e01c034810200340210000b44e0490707102d40c070b20350b8144e0700e5400880c90140d0b010803042d000040712907125000d450005011058480484a8130490758401c000d8400315100b080740900020106e122103180c03682c80b4404a41c0000c0081d0540360340c2c5000d0700540003034800300d0003402c402000000401c14610b40c14460346400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 126270242 1250 126268992 126268999
    0x90b04060f060f05131203050304050c010e01050904110706021c0606050a0c0f0f050304180f0c05030105130e01050c03060112060510050d090c0b0703020f0d0f03020d090f150605 78
    0x1071428000018030850900d4030382c40c01d00c0b6001807200190908600700300300070507420511010105192400030140e40068504071182d104501c564440c541c010714014030042c9041e901c1c2c0b4100302404080002030002010140c1c120b14081000344040b5146000614002d13810584165004d40c000e410700301110120303480101044014016401d40035407280c940711241da00300c000c8890810050404040180708808000c195110000340050100f00390015000003940703030b40c001c001d4030410610503401e9810440c054000513000304014030092520003490304010035050800180c80c0c0302e00446508444044c0c07207261a1140200c02c002c100e40e03122406400d5003c4c43d880030b2280710b2a11002c103106000e5464130105010000c80c100507411241d50025840c290064a903035000d40d550941581c255014038029801070049600b550035092001070490040c0d011a07449001009031600120029001160b244141a4492046102140000c4080002c0030b00a4240002d610601c12040048514a9001a01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 126271492 1250 126270242 126270269
    0x7170d080c09062107030e070f05030601090c02190b0105091f1503091a01080c060403050601120804080a050d0912031707020a0209070503090111360a090b0406 70
    0x100308549a080d01c0342c4450030366107252111020080342d0f890b5041c3c0e034020703544c2e0140c000802225940c5604619070703c1c03114005035050b00b5281c000c095242101401001c1c0c040d0b1007880100300111265201100300d50b60752058400c54928407550311000c0034482010b4864885010040c0309901d040e04900e45c0000341c041d559148842031300c0c0c1d800c0540d0352a2003418122211711038090322583c06500a62103103907200c1e060003852080c4c10719402403140c0a01806495201d1102e500900342068000c56042e02e812100904240e8038140c05140c19094091080311148020300c00091103480030405a0300c00d134429005008a4a407102e0010301d1b001c001d60211003146983c0740340c0c0d030209412905a0504401e99007056105a681890aa240c0582110000d40016186c0d04101d02150b000c4040e50003001130000034031408001c0344241c03046014403801d0300c0b40585101d8000310002481c03c2c005100381c1c4051040c0407001c00900014040c003c0c40d50041c000281c446a540d0b0341440c0910600000d0300f000f002001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 126272742 1250 126271492 126271501
    0x501050313030f0201060b070b091002030915090709060e07020606030712060504111c06050903120f060103140702010f0e01020304030c02150f1612030926090307170d08 74
    0x49241e031110708041c0a008104200e8280503200390000801f42c41c240342d031260303100000c1c070b013017030701041c0c01c0352004524002d03030400304503180007030088074020410200101445015028421828000908060b0417445104000200901540250310051500f182416660701d07280c54040e081443c0140010311a401041040c0118803100c8045c0e00708603000000040c01d96554507004031f440304c015180690046038100d10750000400d14005e80c404038414502130046071070320b80304d4079904d000c0c03141b1203500600994001a40c92199205413548820f05140204e201c07a507080d18161400d0080d00ea1a0050351074038540140301d14240115120300c500031000314558076250314004c0406483c038000130301c62004445284000100c1d141900d005403000c24100d940c030801c07442c41c2c4190582c1d411080300d051500c2d4008424082c0240310307940d40720350000d4080052070f1154074441b00c1c2d000400c0c0c2d0a80030301c10611001c44942c404106250291003901c04003590b120032021000d1420891016440c1000036600400c0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 126273992 1250 126272742 126272761
    0x18110315060307230a0f0303120203060a05010f1704051b2205130c0b030609010503030306010804140307061b080f07090909020a0e040c03020415050906090901110304030201060e0105010503 83
    0x14046031310070301e038403c0791a0200d058003034054503c0c0720320303130b07001e507000c10003041c149a041280c0e01124400d49504c00c2952442a555050340400c4a2503584030801000402c5154040c08200285c006030f031400a0100005c40440300300810142c0b4140c5d0301e9440160328500d42c82184440f2000f5100c102e603480e141e075100200d00ca03241c0c05800e1034403d4a0381c50302d0114a030030380c060700d4640328154400074245405131a1800140c80e0780084909034480e201c00000010141804021131f80204c1d8180e59824050f61a51100c65050f0900c1d111654240301c01c22401011603501c2c410408e03c001c082c40350b04160340c402c820003030040ca000b8110f005680380c00c41c1803102d126000401501102c09260012941c07a595000040002c0540c2d400108a030044900b003004000844070b1800540707100300c1d000c00816114000c01150541c80340034040d08051120302141551030021410343d48400e0000c0042248000c91700000b001c1e0b0420b403021070142c0c0d1240000c0c4880001046c00c1070140100f07182c2036080d480d02400d00d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 126275242 1250 126273992 126274003
    0x1603020f0109051302030603012d0504082101030210050a0207030b09070306060602010e07060201051005010e0a050409080c01141b07030e03061603060801140103080a03181103150603 80
    0xc0c82142058040c40036a40a004a40020000141080202c0e14441e00c030a010b5031040b00c03450301c01d503c3c0c0080441c2486000c42a200c1e84408199049142d0112441c240001e02d4040e00540784d6500900103a1802070040d00d50403521902104d050046501d5031050114541d003100c0c000040c0320083c000800c000c1c0e8000345445c126600312011021540300d0700011410080c1e242c0002d002d842c140f0002003a469015000210b620841d41c04944003550358940890803102c0642c1c00301040c20b00782204010645c03248259228184005114445050781e8400180c2195058082140d038800b002c2481c4000420a01c03e4802c002c2e0141914202450602c00030f80e5504c140d85070701c081840700403903a2028548180c00d0340c00f20920243c115001d6080401502c501c0144c0c002134200082c0c2841808501342d001800340c444c650100005004250342141d0341e00d9025000354248100701a07984bc20400300d0711030b0340d00d0180624098a0485078080154040c982002440b0107035414184400090108039200000c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 126276492 1250 126275242 126275249
    0x3080604050c27040203010f03030f0305011503020c0304050901060f090815010303051c14091608070524130e07050c0c040b031207080a0215010f0605090f0607150b010216 75
    0x38038041c0c4281c10700f80031414600180e81c03a034101c0d102000100d1408054071005059034003d841d041904142042c0440544409006080070745040c071040c9034101e8020f4014000e03910412003580e01f13054039a40440d52408090780480001850b1005a0060a070072640705000342c001e4402424a03545c01d64402000014123200060400c000001d0600d011005450210900c1c81d144105120a1101070000c58403944141e402c0c40f114001d1080380e41d0340d0300007942030204030b41024010300300061070f010420244540c0145c181440c40d2800301c4400e101d00c1e5140c001e241a00380740d1448064641804c04042041c00300415410911001308096044c007000001c0e00c0800010031103001c60b84d03610f110080f81c11b03c00030040f40035442d82c0100340c034000c20910300c0180c9042d040c00c4e4200e03620f021107a00a060701100c06c2c41070b401910b4a141003444242c0c03065004080c0c921028282c07100700c282e084040790301980105002c1e203100c54261029600360343e80f40610801c000c824070051124402440071986e49a42070321 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 126277742 1250 126276492 126276517
    0x12070804020d05060a05041b033f02010c02191505090708011d0d020d0c140309130f0e01050c0d0b0409021206011403030f04030b07020a120201020703080604050c 71
    0x90000e021503440c51410410355034420240d40c00d904001400b08041c02e07041d2801c0352860300740c035061415103e008082400b182d41103412807203030f8400007120b42854640412008060840e181c0039121954810403003006480165000040f110f40600d0024201500890300c40407070740c00e08100c20082103d241d20050078000c0454001010f4a442d110b844c507080007540130034403c1d42008561801e41c07981c84120349aa4090b40c081d02e01104184030100d031500c1c820389245000c1200c08902c0e20100d074081c8039240d4041e00b403100b128540040c0794001414558100c1e4828007440d11120301d81c0400c8035a00441e011480d10b08000d2045040041017401a801040c0c0c1c00c1300003540e10140301c2c202d0703a1244c010070f08054000e4080282002010b03e240d8442800b409854804005801c41526504000044401451a0228007030503e406c46ea10850074060191840c0114841c0f26101c2001c1403c5800540b4440100c0d0001a07503026949000b03008030a004044900c101d2500e001c200100541008a900070140c01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 126278992 1250 126277742 126277757
    0x160e0109050901240501080603030a0504120c03061b170702060604020c120a05032212080612120c0f0a05030f07020613090501050a09020901170c16060c030608031207 73
    0x400c041e034010072950411190125140200b00038044c800d180b02030584a0a9888244079903882d800e155507031045980c000d0004400b000b04001c84540c0f1030f072044606104450140c40c4139901d40310a0240d071f0390f881021100d0301038090384c0107010740c0008090880f0176032080c004981c0d14054001940b680700c000d03d81d6001d103030006000030b08007006000009c44000450420b6448115080000b04280c02c22290350354100000d0346100b5540c0e0501c1c2c400402236501c4a40c1c150550300082048076550350207000c45401480c04040d80e6480c0d2000d000c180e8000401440f05902e0719240d4120b5843d001c01000c1050540e00890b02d04400f09001000f1143c0b9020400314443c5c1e00d052070300c0420024400c110b049920710b0448000450043c04a420590480310101c0d41c8124031ba4a03028020200d1280141460108441019410151103804000756006d80d2000c030711401e01c04020304400f030401000e00c0448013250348154902a03150584a1038000c0c1c098800114105100c3d016045007504010300400300780207d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 126280242 1250 126278992 126279001
    0x5160c021003200309150115050702040e061e070315090c02070b0c0a03030524040902060903100516020303040804090f0b1804020109050105090d020105070512070c0602160e010905 79
    0x183d000040d0b41075400140c01d001000031034a210300d60300103a800d10030b41c0c025961800701c00905080090b041c0c45100c1d1031161281c507004000d4446602c07148040742c0068654001240114060040610990b58507140510418050b45424034021000340518145403500042156009540040c1016660044000207410100c404140d240c80c902c1c2c1d201101412002a29080c0040081112084244281c03400d00984d02c43c0c094540d140500c001c20f104440080302411401c40c0b47c16004103d5035030001e00528500324003403021a00b4140c000d40700080482c3c0b604180600c0e105100c036200b018a009101550441c2060341e1400f005204a20a604107a80c40e00196140301c03d80d6070025042c2d2100030303e112a0440d02d51451281c40400b220168046240b01c000020194021021100e03000c10051450064501a81c010b48198201c40010b6070144120240c0c016591280030041240c240502c480000c001e20b030000080ca004624401d421030f05110500c00c026201d48101a1819107002041c081f0b0140c0d607 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 126281492 1250 126280242 126280247
    0x20a09120204060306050405031e0306010f050a120f09050610120f06060f0f1d090d0309050109020402040b070b0c07031218050601030804050f0103020c0706030c11010203160305160c0210 82
    0x203c1c0d01301501d4186040b0038001044030000051100d0305a82100021b41403a10306d4101c428002211014007107420b03001c0c0045001d100d28028420b4031024200400c40b024000d249e4401c584e0804944040c503903984d580e10060102c10000340d036205200389440b0301c94070300b44081c034606000304030001400010789c002403e04100594000c0d01c00340003c20181e00540390703038180d02c17030030b02c28075201c4e1500041030046040c040b1701c00350140078414076000300100703803440d8401e200300d00821640354155440d558814500005030382e0b0780018070050641c800440d8480c0e055040031001654064250140f102c0e041040c00300180d0400824003003a02e09e000300203580745000c02c2c01c0b03c4902e0ba401e0002c202c0d000700000442008900400743c000e0700c000b6200b071290942c2500c0103600b00d100d4200f100340f081c2d1050004000b81c5103c0c1d00311010044c001d2901d00210f548450505081e0f80050391004054030460308a410075952612070f8a6001000d001c0020b0307490010070f800350181c04d4240000e0b001c0c400700440c0d07103101e90 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 126282742 1250 126281492 126281501
    0x70816080a0222020c0c040b0906090403080703060801090809030606060703120b130903110c1005030109021e04140108060d0b04020123070c0f080a0c0e040203120f0319020a09120204 80
    0x688078255036645d107a9070480c0d12001d181001d1440b1f01d2600f0403003681e81c105000c41c107124030800750103017046881c1da48007a186a400203140d10101501e0b40340c04945104207000314035115108803c4180c13038241080401d400c00c0802050301d4001c00e0b0901180021039805000b445842602e00400104d501c030340404503c560710f180c034588014604250075082015440840340e46400e5403c000d079407002c2d091400304400d4400030410100041c40920051181ea8510b038003c10780c001c1d01725810104410f00024141040c2c04ca54014001004241c400d1009540c00c00f90269110f501110720f604000c005a85841c2001c901410107410008215042091452403162410000d885a021503449524902c0c2c2180c14010740c0c0201110510ba2540029078604001192040e065006201c1c030007a0741800b50902c610000200b06982c544151000b04010440c0040100319100417502c145980b85029044000ea144081d06040d15041c41000200710703441e8440c0c241000e465441002d45540741c552f000080240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 126283992 1250 126282742 126282799
    0xf02010c0b010605071a2e0e0f15010201020313060f09061d070b0a02060f090304120c0504360c0315020304020316080c06091908070816080a02 63
    0x14000000003007000358110000d403500602c1443c031b440c040300b01d50300340c4001c403030003515030440400c00c00e2119081000c034081c0c0034a42c8600d521031a40e0060742e079055000c643c003094402e01018403d4a09000c0040024026451040c0081c0029851424101082d80714000455400b40c40c00f90354101c801020411500968072454110005100540c2000189083d484200c04003003024890881c000440407945010f6a014100c3c1c1e030040c0845035207141d40c00e14649030040c012020f50004101c0444c461101c50406000d40740108003816102d0b0901003400110b812424291542941c00801d0003058840e10482c120045103504144440d082c2d24544400d900b40035810041c81320b6404040c130303219085568003651055008404440d494104031960100c4034034940105c0b11507400a10701ca1301c441c20b1041c004c0c1400140540a4030003400303048400321642000307400106050704816010800700301d04001c4102a011801c2d08007620b546000c0c1020f42c0c804180310024016020041480103868610b01c807600d85 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 126285242 1250 126283992 126284003
    0x1a1c0809060f0d05010807210206030103060510170d03060b0c07031104090501090b040210090b04151403130309050105040b09090c1209061e010308030402150904060e060a061107030f02010c 83
    0x4ca58540f69640d855010501412020003e2020340c03201c8c4070351401d80104031540140c40c41d0316517400c46d1188406000b000301b607040440000d0760001200840403801102c089128000b0b4214051707808001070940d4516409003503024014408100c00c0d0130040750a60072664081d102c14046261080450054011441c028105518014912050002c000201441140300302c40c44844500242015100108907000d180d0032000180003c0c424040c0011080b0b5000c515800c1590002d12900b5124016074821035124850310241820442056044400c54000c0d100c00d0800c10300f0a8206032075910507008999080d80319400417400300c2e40c0310b4011030840d082021100500d400e0b51070280742c9107503200820b541607403a0020a100c2107128221007100075041c0d035807002c036007880d584a640802ca010000e400c0c06013410307081001078076443ea84920802004100c2841d92802c1850080d00704074106010341d006a00b0300c0020f1130707031040048000c6203040a89600411905a004d0356000480e80440c1c071000c012310 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 126286492 1250 126285242 126285251
    0x32502011e050a050c0a09140f0402040b090405160c060b19030b070f0f0909020a0e0901060f11011406010804060906060e04060b01030902010807211a1c0809060f0d 72
    0x684401600128802c3e00790000904c07540d280c15517500c00707501ca826030440005890a030140114803181032903190a10000303010205d01484071000a0480e401795016818110300025503410301c0c1401c0c0079040d44101184c1008200300300606001d0666091904020020390381c0d00c44020040c0d507070602d514008094040b05030721540e124130744009200c00543d036440124418641007000c00b131285242f14043c0035039031340f60500940340140c018044e402110009c410b03c100540c107200291a92502036000300301c650389800d010540140003800c07041c1c5010107048140d04000301c943d00751a281c0360303440c6c10450070300e0103035115a5141481b00041c560f01c44001c00160600358001001c6e0055451640a240181010003c491240b401541218110318000303000c00c0304100020652805030b1038020104c4034445225500f80d20060300070301200c21401ca04800c040048001300d1481c141851404a0b200039030303088210382480c80d15403040fa4010803d00611581c000900c44180e0031813402a101f00c0480c40c3e50901 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 126287742 1250 126286492 126286541
    0x2192301020316050c091005030d0302090d140714060304051b06070b0906040317090c01030c11060a02130f0803040339090e0c060904180203070308090a090203250201 73
    0x548681307005d490b80384a90507000101c0c109210b0340480c0c0080305d030014000c018100358907100781c0c0031b5005482965031200d640b0032454041015801000300c41c0306164040c1180600742070481080a0360052140c0c000c0341d0a200b0031001600c000341e410301001070070702416001f4075020000b030410300c11404020100000e900c2072240c04800055000e003e00c0c030945034040115840c9240c0d9503502003c40700804540d2140e0558820f55000c0e038006e20440c48903140c580e00c40b800c8921640d00e002c409903418003c00c0d40c00100c4241e166070240103507000c0c045466841820f03510705401e02d40e49001e140070151030800c0744801c00500749051200404401c402c040c1e4407a000d0620703815103010300e0407841200c0c08242008607080e046080880c0c0304016242c014501400e01d010201488024100030114820f654100070246025a40402ca00c80c000d41c80340c03e81580e158406014000922459070280d0071031401441400305120208811045000c840e010f54040300d041c2840403800340c040c040401d44484410255070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 126288992 1250 126287742 126287753
    0x30f0705070e0f06010806220603050601143712050d020609030412080c0109240b0a030b0a1509020406030b011106010f0605030c0c0706090302192301020316 69
    0x454802d1001e19905560394032080e589150115611400140c55600049084c900b48810880d84800f00f403180008800262240d000c03100560819036142d480100100020206c3d020704085001060741d860300101013450303183d4a403010100088400d02c048048541394001e00b84000030041800010f02800c4001d141455503d4003030300d0070100d0050050000055481000004803000c680e0210b0000940c90180e0711444c41c541c201d1060000595240c0c80c60001003458150030703840b41001094082c40300010004c95004075000703070f0401401040c1c0d6070001c001003044401c805512809032400450403400c020a82c044941140e00924510340c030100d80071607540c0e03055103c40341d1003100ba03e903c0a8128158103050743c40009204403010f01040c240d041c0b103a14401d20145421100c0170020a04200d90b01c08050b040c54142d0300300f1000224206c404006614208684501da003062a41c542052030810202403048101102c6401c120b94020100d00c1c0c0c075074401c20480318140300112b112100c000903440d05 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 126290242 1250 126288992 126289003
    0x9160e0604050a060b0a030905030903030c0d09080636121e0f0a0e0604090603150609140c0c102903071d04111804030906050f09040509030f0705 64
    0x3594051454400050480038032403190800b61100b448841d8201042c0b0001103000e00004031044549010a111442c0c40d501c041029041c0b5a440c900503182c0400d480100814101d416841241180e120000f8440c4101000484502c440d1640004985050a4103022980085a1583c441e514851281060304454071440601080050079000f143d035a02540314440d814003914100d03180c4264108003803085607028244401e07510380090405d90030150380d0300081c81283e6066100342e690034101021440c0841b02407040001401480320100f001864140c04000003c0009184052440000400d900e503150101b28140d0080e200c400140401c032402c3c01a054401440180d54485643c250400341643ca00400e8900544001102c002d16038032044a28100c031440251064490503204081210591290001c814015114075070710952410645401403001406501003420401e051007002040d04400040314011602150081104d8662214840c114400c4444500e010040000d41c0c80c1040f01c0442c9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 126291492 1250 126290242 126290251
    0x305041703100f121104051506030a090611160201110f011d010b04050c121b0712020c010305010f180f0915050907061b0614070c0203071502070e09160e 67
    0x3d1455125640b460b05401c0200400c03002444c44140d4003076905241003d0344410307484840500c440400860f0003002c0f40741030303200750b8102044646490f00c9005102003401841340500c4259031451800c0003005441038000b034540c2000341080030101700032400139010015030268040c090700800c2540301c66588035025182d44803008107103500f4201c4600311b85c0b900c0d1040a01c6211090409450059800740c040c031601c0c1b00800398907a586402c452040c45000312005095010301c02c00020b0b801e21b242e0718001e441c001e0405005410036080c034005104100850406204076655020521034024002c91010301a2280c0d00006820a1425940c00c0030300481c4244d211201c1c02d40c05041105480c0c00700e01c0c54032000c00380503540100d6403a01071095040303000c200744400c0c20301803d00012031055052000e14035500076240e000029414034006804d5207030910248000307014101e00070300342e000d0520001c0d445003124415414520b0803100080c01c103500c00d1150301d4001004111024002da1a00155506080c1c00d48 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 126292742 1250 126291492 126291509
    0x141c02093103050415020a050a0305040303080609190c11060702070302090a0b0603130f1b08010c020106031106092412090309030a02040f020f0414150304080406030504170310 77
    0x21a0321402884410140d0741c40e940540e642803030642810050414420100303400001c44c81584441c002088051110109152003a51090742c0d481c03450030000c10070342003d08500c0c0b081c1020300a10060302c00201c1e881104420002011407851103944042c0c030a1926145800c003e805001c5c01c2010960b030210701d24090300d1007100c02e5040350f22035540e1541103d61400e1215000075040021525448030b0381640780c800f5219000c1c24801c05515900c1c98040a110042580c41040c1e401c801e1115400078050003480d01d015100810815246407605400351309500c41d200d000e0080002d10b441e50f41ca07240e0900c20745901d01000001c4070303241003140402e540e01c425445049001003101151180c44040300f00e44003480011300400300a022038003004020812242501119a400c10101c95000b200c0c801030402401d05030540c2c20b10101c41c0003844000c0002d8402e0080088082041100190b01c20040d2020740f421445e0010321a030311031410328079010b04040c0803900010040200502883c0d80c0c03402c60291060007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 126293992 1250 126292742 126292801
    0xc090807090f05090303040506041509080a08040606060302180409050123060f0a1401030c0302091c050c09010e040605040302031b0102090a050102031903020c19080c010b0109141c0209 81
    0x840504e600d0717000984000340399070800d10108010902d01c030781d9070188113400b001c00140c102c03081ea65070045620034405400030550030010002802454440e040c01130020781015440c20a8038058505141d14042542c1c0c030072552401c400043c08425400395120441c0034031090210b1078060142c0b1650304007142c0b5140714403c03102c10180b0501303003a0064070440c1c40d10140c800c2010303140d50054003d0f2122283c0c2d0420958240908260340d514290640030524091420080340f14880c01c00600304550b912401e4021112000100185205d0127507055000d600300c1000229a1118641241184a1140a0f48139620715004420904a0650041a9621040760790f103034032507524001aa00c2e03015001e10b00d100c0300a03100c00302d03003140e01a07001000d940665070203940f101e202c4801c1c0e034241b80011117030598000c3e0000c5503043d10240240b04414144a003420141c10061501030724114582150341c6480c02001c11883e016409140705100ea5501d6500510004003860320740030702c401882d4502140300b1544c080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 126295242 1250 126293992 126294001
    0x23041401140a05011b05250509010e07050306010c0c09020304110906030a05030f0c12040605030106020601081c12140f061c0c030b040309090204060e130c02100c090807090f05 77
    0x7481c0701c011030314103031651150a2170203035a400301710384003450a4881c0d0003032481040c07284400450f41314090003850350403100c3c01e00303010a21445490513000040701c0e40d010307002e2000c01c2c2c0d00b1000380c90303020000b468060010303e86c6103803241c2865010b5200c0550a400441400208000107500800400301581e4003906550f6080c10141e403449400ca0140c060342041000c6589124084010400c5a450070b04448568042d4050482107602c02e40c807460014201100500c681230f418054140181100c2c0014843c995801700700788441240742c4a00001c1c0a5011600344a03101c0316080030321040004900c2010a18095020b03110008046645a10520400c2d01d02d031061200c04100d20000b0340c004103c034040e142035589120050702d0103082039044c09020303c40060303049410300041010f800e495a03546802269001403001d148042c4030480d240a04003011044c120b580095841030300c1d0010000401c10807925107064804150b00d4000380c0340c1d806800404950700b0500e42040c80005500b0324104010b0743c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 126296492 1250 126295242 126295249
    0x9040c0c0c180603021c020307050a0b090603191a0f010201060e0c09010309050d02030c01060e0601120b0f060414180603070b030405120723030309072304140114 71
    0x6110030000c24114030301e18240021096148111042e4150180c0040d005489070005200050380031080085d10885c05425011810309201d002c0080c903094510f94191070421000300424015000c00900810780400000c0c100416a0451a001190390200300841d10800b44c240d05915004a0260300641c41da103d800e165500c144100421500c00c01c0f5880415203860306000780b01e80c05512140c0c101a180c692460100300280300c0d20341020419001550345681c1090313074030700f50b50490740020b40c401004010081580d070040c5040c8003145200100044881c098000141005078240003503411490114011851803014607102481c5c003011110b121904a914044c040c04034801c60b0066010381280e80308200f0309400c03c02075900329200b00c0c00e41e000040c9511500545400861094500e00310100c1c41520b9284c035402e615080d0b502c14009145140b82030300f0311036900d0609125140365a0841a1080303c00300c02c0d0340150340503a900820901403070503440f000b50b182e03034020302500f185200307042c1c10300c0300728074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 126297742 1250 126296492 126296507
    0x50a0501150f03030c0c0807121103030702010e040504020a0e0109020d0501090203040c0501080c0f070605160c020102060105210d020f06010b04030c090902041b050d2702060a020a140309040c 84
    0xe03005075005071031a04544c3c0c00c5030900c03c0c4440c115a036400c0c0074030101d550740e400e100d0100600001d44042d010391840d03042014032488c2c0744010350b001e6003040042c500944d07440000400b08080503240410f85440c0d62020a0007440d250303000210407440b100010945030015001020502d41a0b0424441a40c07a4481113040744003d0354000c0403d40d10140822195005081c6d0681c0310100d07900352130034841c980d152100b03070380d00c10300c411202969940204110360322001c02d110514000f5141080e460710403a40040e54454040c0282072040a0408402100355102010116001034401c10383d02c0b81c1c140800702a41c2c88400b0342c0700c0c0b420381c012000085a0300c00c044050300c0850340c001096062461071b1501c0d81000b0509583c0c180d0300030713444042c2c08081d01484428460b102601c0d0340ca80c0e40d0380d001041448111541d540385c2c01180442c41900000612406218042141d01190583e9607150104001d0740b900f01202e000410120070304600c04030f505004805801c041c10181e80500940070182c108aa900 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 126298992 1250 126297742 126297749
    0x109050a080c04200403110a06170105150904090503091002060f04080a091d06091506030a0e030c1009030206160519030b030a0b010306060e22020a0f03050a050115 72
    0x40e88140140481c91500340c04c030740c1c078030385002d5100e4408800c0c4240a40d15541301d074000303075440502d00280500a09000d42200000c1c0250310713108405a8030290000c00b02403040c0b0904d031194880003040f404c035880780340c104d628070742c0c00078420880300d00c85151541c0c582c1c005652841c4640280d5126800c0540046000751003106a000c0310f00c1e00d951180d03100c0d034080d0040c1042c403080240707404000c1944100e1380e02080070795841c007000d0340070f602d4108100815103100800c02c00741c1002d0b9100520081d02c40105585e00462042c5001ca004030401c60003a18600481c20035500c0d0341300e02400303000341d40c5880d40030b028a03c0c0698251081ca0341c401e14000300d041707856a0f1046c00a041041100a84c1540d007a86002850480c40d01040c2c1045c2a000039181507003140c4103440c504055030041080290b540324500081a1034850401d0f40d00e4000a0590801451010301c0500300c00301d01a4021940e0f040100406480c071950400e00e8070351070782042561101c54402c100c0c5c00c2d40c80e000c12141404000c840c40c0045 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 126300242 1250 126298992 126299009
    0x30f010e060a0203130f081c020406020a1e0803040c03050607020c0a03030f0210020c010c1e0c0305071103010501090203150d020312090d080a05130603020a0203040e060d051203060109050a 83
    0x1942c440c0c0001c80000c3d0301c001d101d840d0300d61032031801c00c0005412810800303409008040058561441601181030341c064440f200340c0b8039104010030401550041280b00c059030700800000303410411201e5100d000301c6200401000c03800000104002c104441003130704152805482254120345d02c514003039a0ba81d080d0050241d01c02c00d83c0c141000002d10420101021540fa031059491208c07604210304203982001030f40c1c480d0f0341d4640d2428654554400345088881210310240c640090042c07101509407103501034050f04101c0d0005074142031019008241900000c007600820056a50f0340380e8200075001542ca1007441c080c4034000038241e103011004001c082c4d800034003410420319481c0080c00b00f03520801c5507642003502d01e2080c801003800b45020b00403004054680340c1d9240100d105100902c0410b4100c442410302c148928011a035001003a94151070034540c1e00c42c015100c40e000141c81e411650401803045c4a4920940003600a4402842c000c000c00e80300c2a800a40350002c111802c2d41d1801400003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 126301492 1250 126300242 126300253
    0x109110316030b10020c120303060622080a060b090105010c1a150402030109090215180904140124050a0602060406110c060115080a27080c03041202030f010e 69
    0x41099110307842000711018140002d0506100300843c09070b00c45200b6031405a0000403000c075440c1840302e0380507032543c1e0b07010107546146400c1d80040c07400d0103021fa2003803d400c401c601d411a0f4034101134000740a0101c0f01c0850300c0801003032034800003038648418414029041c800001507194003403405489055488a440505d401c42c0394107003c1940d000500300e40c0c4051a1400d2081262581e10040d1701802217464007207600380c880d0060104124220504040c220382c10443c00401c2c84844030390343e95040088a54030104e403102c3c02d140c041c03000d0507050b5070015403030700120303041840f40403070060364080c40b14144d559040da41c2c80c10440c40c50190f20a40d40035030071440008001840c2c0b41d20900c00c1c1707100840c0c07090505018104452a1003402d0b0400c1d03020b03c00003c4034500c0240c001803015030003501d0f0501404030350401c0071540004440c00c450040700d1350b520b00720001045028025910540391070b0f81203a464590700d81511003c3d00c44440140c4c024002c51308a014400018002c0c20301c4101d0f00c000030311 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 126302742 1250 126301492 126301501
    0x4030c0209150d0602030f010501081e071404092a050a0302030c0f0703050403140106050d08070302070e131707080405150405040c08091501050108160905040905010c020601091103 79
    0x111440010900246000420100102595503004030141d6500031320300180c0701d182c07a000d60060003406030045414001031a0802001d95a116610000c20218401c5010b00c0d46920740299184008410440c0c1c50000c0414045040c0136240d229004241c0c400c0c2400407030744400c22900b144083d4400c1c10303c00280c0201700030300c22036019400840d00720a802e5002440e145e110103420080c1d0b0000c2c5001c03030008134002000c0041c800a80003c07450b80403000c000308482442c0c60000b0b4244401c20034000c05200000c100da1007458000e000181c020300c5006140030140c46c02040429151210000c211011360b000a541c510101c110815110740590182c0c2143c0380a0401c1e08000e10070380d12803040c52050a040102003400e840f203020301e05803001c007501c4507140350620b050b00e039003008030fa03000302c0d82e01400d00001001542c2e23115031115004032011001400d00003036450100c401e9505500070300d4104c0d00b00000d81081040540c0201c160039202da0aa50241c0d0302c031a8040191a0b80f0024541016402d01c0030a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 126303992 1250 126302742 126302749
    0x20d06020a08060a060f2a0b0f0109051015050d09060506011407120c0203030418060611160509060613080a0c080601060c03030b01030902030d03050901110702031902031905060109060e04030c02 85
    0x71085007400a5240a42c0581d41285c0e03141142e07c0001211955050030501400f0000402d0712030240c0b1498000344440d24040c0c0c03280030440214810044800c0900c413480c000701d4018400c4481c81c0344000d00074000700c081402c20002901c0295105400035140249407004452910117680302c46920400c0b01030400303203004007180e4210b80c80398180c1e8580020400003a060300320b154400b6003151400c00216a5034a0b042c005400d0700c81a071409a62a009004169288085440d541068840880f2a15000d4588202140c4140542541c01134002541200444c8140b000900000c085200d114100c1c1e0340d507101c00a581e1120828843c140209100a5030800068083d8112203400745041c500050007001070f40009140840400142d000b1982c0c5e6000d0265809080c0918401041030080c2c0301d14208480d030110382c0e545007502c1001080000112201b04550301440f00c0c800304011030340000c0c070052580c20003540307a210070711640c140d6510b0080c0008042d40102451407003290580c848071104005034007031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 126305242 1250 126303992 126304007
    0x201020702091b091e03060c040806130c0503240603031201030f030203070b01090516030c09050105070c0302090408030a06091802130e01051608060f0d120507020d06020a08060a060f 80
    0x100f00c400502900d040b54031940c1e018010f103486007401d0664640440c09140c2021000342441c40300c16010041401810305c0002c0b07290b0001f0042036554500423103400e02800c2d0020076000306500d802903a18254070028042c10b0b50b881c0c0c1c1c00c00015000c4176142c0c2c4041540d20301c120f0849150540f844001080800c5036201d6240080b4060f0064038545070103030b554000881c0090b04007044480d5034005100d001008800444540800c90070100014081c40101400c40c01d40782c800d25040200000c1c00400300000c4041c080300640c0d028107400003a0030103140c51543c64208031ba14103680c40c98441c00140d070b4100ba000d49212406440c900e448141c12503020700480e071100c00601c19000f6140e081d00a0741d07440911036140310790020100442002c011400042c40b21f54050015485501d8101c8104003503070318000b01c2404154008140d0108041c110401d582c0c90003414400307940041005071440901000341c00410440f2890340d1000d0b050b40e50b40d810000d181c4407902456000401d91805008018028141c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 126306492 1250 126305242 126305281
    0x120218070e04090b0702060703050705180d020301090b040b0c03040305070204020706021204030e040c18090c0908070e0f0703090f0b061203040803040e06031f021602131407020102070209 82
    0x1005907020300c06201040541c3c01c2500202d4a0100f280100014a41c1c188080b5800ca10a45014009820300610041c21801080d680001c6980e4641c512070417940c81d40c000c201e50550103002400200303403d0424a003014022107042d541003500ca00000e000030000c0003140e02c00c641c142c0700c950520a080d02444029042071b40203e95642d420401c0000c091040d144051059100c2ea86000c0d06041d81024442030b03c112261040601c820400107210358003084030300c2803d564018100181581480c1411200300d60594005d103228010014046040310680014500c00e109081c001c005584486400310300b124401300c0c01802c600c18005d000d80004408514064010200408944603641c11758421819a0b005074443c01c200e81c03001404220307180b410402d080c2d000f94214040c001903881102c0380c802004403000001c01c1136500191004203003140e41e034591031079a0064030280280c84400e50601c01003c83c100b1788c003030f80c08514001070343c03151050007200d00240c2d014009080c1d50702d400d19509114a84110f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 126307742 1250 126306492 126306497
    0x91f060302180d0b01060311040f03020d0609080a050a0207150c020f0f03190210080f0103080c19060c02120906091c080a08011514030f0907030501020a020309090112021807 76
    0x1611401e5550343d0480d0410003030054900003102e504d4410090100c850500c50312041c80380a0004210740512201d840045940548110b01e0900c41440c01000400707590000509080000c0b5600e890541e021014008120a907003c03200c00c0da89514002c00e1440c0150003810000c0c51590402c00141050480c2e900080f801030070705840c5110b008002414192807025040310416010800d80035850a1010702143e102107003820107290404106d078490340d280500010703100303c1000074800c8150740c0030001d440c1a4030401603000719541d500c5c504500036048291b5080018484e101c040e80e4100216402c6070054031000b05010b14011113081030112014140602c1d02c10010030021480c003091182000300046101070340c0e0003407250305101c1002d50035100e0540d450704200340c0c02000c488005044040300c1d0081035648842c99503a8440c44680d2400800784c01c020300360350020a08282003600000580030103001103590f00203d80c0c03110403c50b8081c00c040701c0650701003a601040180d0810b0150020380007540c91 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 126308992 1250 126307742 126307777
    0x612010608010507270e060108090f011104050907081521070b04050a08070503060f060d230f0c030d0503131a070306050904121d12060105091f060302 66
    0x1050300c1401c49030300b1111140030030410441c4008007000e0b00c82130724070502900d482445850a090101c01b140c000207080c0d41c180b10303d00c4040342c0d6041e810010305c040701d4000d40003445040440146c1a0342904244550f501803440013020842490042d4107441c07207482c0500701d44040b000d00904200c02000120b102d03901c00c0c3c03400c0b52015400b0009003c1080a018811840759071245008103005900040f5440f9601d0768003d21410310241d03034041034240e002050100342c6680c43d201e030b8000401000c20400014621605114061502044081031003c0388040350140c412410302288203640302e0540403010795141d00070310722881d040d9010380051038100006000c0500281003d683c2d0b44083c41a04030318031451040f40c030412841650500070003029120507103c03480d070390500e640e0f0107030040c1c4010001018040c51541c1c076035103501c001c3c0303442007140c400130101b211800200d074000761540d034207004681c0900220340000c1d121030090040d6020394008884103490592406804034020b41010b1f0005082042d40c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 126310242 1250 126308992 126308999
    0x602041d2e0f140a050a03030212180904061407020c063103110306130809041e020d06030203011a03060f0a02040f06050d05010504060b0d051807031a0105011706120106 74
    0x6a44078009000e00b40f1600400380d034440104001ca403c1540400d22440038204148000b03a808900040303180400c000b81600c4d0458041e444418020154103e90010145001c10080c07001e1134000254905014003241420307101c1c11750407621503110500480c0c2100080001c00c10702c04200c2558400310300c140460b00c002908000c20b2030074104117130344161130480f01c007171191200703103030500005401054802848012210320382e01d001260090b5172005110b290780328000302051080742c1b101c090260354040115550700241d24038070000c180600003030b030007503103000603141e200c3c48400b202c41c40d4100024001c0c0b000340d4800c04810b44800c030040c50183c416800b44030015287d0441c4402c2d1024021b680c8800d505d401030400300504640c3d05901080c8250705001c020043d07070002008403036100303001034801b042c0c559516801c1d103a0b001801c80c61003c40d11507001e001042c494807003856040d00010061105091340c0c4c40d070044428001060900d0000424070703021501d1031504000d44001c000c001000401c0c090f54 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 126311492 1250 126310242 126310259
    0x40608040204021b1c090f0603022d040f05060306010e13060305030d05070e012a030504030b1e070509030c040902270a0c030608070915080303040602041d2e 69
    0x15000390391516a03203c6904080282c030380003d018400610f1b403801c0d0380c0b0140b07446201c4080200304e21500091607800102e0301c0010484610400160349440c0020102904d08203440003180e10520402502050040010905141410807603009640503542c0c10704507020030741007181da81c45d8911b10064881d40d415001000503010710151201150707040700000c2e146040200684210080201c0c28100207522018400d514840c401800b480d40c880c0300003640380805441c0544144c0714170340010344821011000c001c4440e034101440d40c0c0b080d4400400a8860f00c0307071201034410b40104546a64160048580c80d2520701301a80102801400104141002c0b0081040d81086078141a600c460706a05031082240c0c10406006003140e01b500391400b0881c0300e240080c45600c400107401044080350b1242054028115082101e10251031100b050700c3d80e03401e092402900a611a100d44907030001c0007003458242c0e00759000c0580c03040d82e90114400644c0c800768003d40c0e4030f4501c500c160040b0750160001055500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 126312742 1250 126311492 126311527
    0x506030313030510050a0903140a030b0306010f090c020a20060d140405010e0f060408090301060b0d0b0901060512070c0201050c0d020a110301090507060302181f0e0a080304060804020402 82
    0x43c060009400d4a401441c40700058541c002c1000842508205403017001903400420300800030142c000c02030b15074440344c4085001d062244092507140c852040013207010501000c0610841d60b080500300900c150030001640c076401010707809003114681d1003100040451054142c40b04c02c00050020385480b043c103101c50300700c0c0c00e03000032450b0703045903081001300b040001d00c5840803d20042e4000c10000c01c5442003259124001000108800700204410343c0b01d880c02d4015002070088800761945912801d802070300103100781180c4030b101c4c0d8440000015414028001c854050300004901201c030350722600190703400c40100f04103c4c10440308014002c1400c02c148401c11481d051640500014000c60908c2c80e00c500388850707454407903454000c1c400d0000784005901c00454102d400c0250304d55034201c008201d00411462810780040111090a550340400d84002d4000381c05038407280e1000356103805124030f00e05180a8024150b00401c070900140d0700400b1040d6020303100600261404031500381e002c1c100e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 126313992 1250 126312742 126312749
    0x91203010b1c0c11060a050c07030e0a030503120a0f02040302010504140a0314010b03010f020c06371b0c020604120206040911040312031a0d210908010f020309030a030506030313 78
    0x1136100c03510307200001018001150028281c80c810303c61400c3c1000c0d1000d80e44200100101801042005541284c9808411074021a04942540d48076400d111420320000c200b1501c240c0a2403903c042d14102c04010300c01d90f8241c90701039481c1c0741405d0505400003001e00b00d55803442ea210748900d500000040c224242c1c0d5554429400010074158443c2d4140760940b12010050700c0c03ca070043c042001c20003000100d042d40807100d030f4200b603c1a00040d042000d6610720340003020314054568440c440b4044c2e16084040403601c020300c2c0170001c04100310f088170b01000c1807000035804403040004012805001c040c240b038640c0001c00d861301d80380c0c0d9442100e0444182a031041415200800c00f0801e0210400c004402005070b4181400032448000744d40c4c3c1004e812000d41d0344640c2075048a0001e0101c44060141d100803001d02c040641d0070306450152001c40b41c2c3c80b8503562982070003856019a030090090f80d0040c100d00c00150300302184200d05401505006042c59014402881550503486944030b481c4001c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 126315242 1250 126313992 126313997
    0x70602390a0f08010f05150409140105090105010302010e0d151e180b0f04080702040c0c080d0510090e100e0a02100e0103050f1e1f080309030105091203010b1c0c 71
    0x40d0f0710304010203017502d0040d49045070301441d1108002c9403481c191051380040c0d100301c4001484076202e00e4583d0402e5801c0101d40d8196107020101310034020f055001034144c0e0700036202c404d03143c0c0c861003c204151800c0c80009014a01070404118000d4003030300031000024070101130406d0004801818022034003070140d4070030001648a070140502081241d0f59400c245807422a80e26803600e52544c010300e1040b00c000a0080e030743c030401694a18403511070301700610b500c50703040342d59070807685026005014295060643c00d001c03a240080c00c03520701e200340d183c241d920b0005044509102c5000344001e110303284c2c42140754060714045034010703550125000c03c0720318a5107501d20401c40000004080b40d03001041c03681900310140c14010b0424920000c40e108010840004400350703074031016480220b4881c44080a003121400c03000c9480c0c8404400f400b000641a0001c00c0380399a0208002d54401c030401d07141d06d00a03003c00c0103100d03110140d0018610000034000e000203411403903450408860808078510300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 126316492 1250 126315242 126315269
    0x120c120c18041103060402060703050c150a02030402010e030c1e03070515041503020f270301050901020405030c041506140f0d0606030c02010606020d030b0a0f080a05070602390a 78
    0x1c015490380d110f01c1500b01900141420b1500360b0104440340701d05403015050000202c1d5448108004000c03e1503c0c800c0c9006442880c148a01c512020390415201203002c28941ca200072201c1c10009032402c0c0a04000341154240700c00f500102180c100c05035400c80e0903000c0c422000c04c0c50b031660300d90f0140b2803400300d07002c9a945141001c0060909000940681054010001880c0c1500c40c142999040d98186803405c585d0801901d1900c00c0a2041030400d03015424141040481c0c1c1041d0b0140c006c840301070f0141d500080e200350400048603c658584a00349500c5007040c03048902c106940348a904983d04000e140141c1050071108a0f000406551045502c0d030000784030160f854094504880403a0000b80115400c00d1006515890011001410543e0354880007a590351400b035204010b011030184070042ea901c42c0740789078071744040d003070b00f500e07944150200002c1c5e0920002e604d03c0e03980e1049880c0480d40b10441c0300318049413200260141004121550b86285035a1849510001d140c02704a854 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 126317742 1250 126316492 126316501
    0xf040302010801120302030307030c031d010203150d0b070309020d200a15080106080702030418052a0405010e0f0405130302010501140f0409061107030518120c120c18 73
    0x1840b61405811901300400450030160000c0c0c0c0002c1500c0e002041410f001c91207912091040b8002c000070440384900342e003503e460b14140da02c1076008500030300628000c0340141d20340009020110542c07290042681c415140011150340c03196008005861000b80350880c68401343d25001404182e00500a5074001d0000c1450700d94600134256038002c00c07455400f03404000c0403000103060703410144601c2d001e0010160009039180d200380100c8000d080045103c0900b00003420b01d0500810049480c2d0a183c40010103070914101d07810720700302411170400d082901d00b6003040e00444501d005c2003150b40c1c00244103201d40f8210380e00c90064901c2500070ba03515a90140b01e5080003801c0da60181e00c8540c031407040c041c00110640b00c400035120030102c29a400f0179080707010b140c80c0b0000c04900f034008031840c901080a008144d403000041950380d44030b19500c1580c0d03c642d8104542000c2c08007408001d50321000440c90380c0e04008002ca044900d54100740c0300c0c003003118030114045168507140d01e504e00101d81c0400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 126318992 1250 126317742 126317747
    0xf07020c0f0102030304060c050f040311030d09080a15020d0f02031f2114160f0b042114010e0c0103050f010e040212100c0504090c020a0321060b0f04030201 69
    0xe40c40d000407200469400da0303440c0040d40301e110280000e0501900e9280105a860260b4201c41003440c2d050640c0e80e40d42e607203050080d05101d800304c14901c20302800218071825442000040c0a540e10b01c1d02030078001035640d583d00600102403010401c3d181c1c0a10502402640034818042080786420015a43e0310340148804001a071111115044d00803509050144c146090314465544000c90304451410404d420b01284840b1101d240c890326105e2640501464003e42d04084100c0e03500311060050b20340c485c040d110090007640240c041c404407151004a0b07482401c0c000c3e0000f140070740032074150765468080c40e90039284129461002507000028030301255915110321030f032200059415000740e50402d110100d460740c01800192280c485030290040c81d1409000c40b40701035600c50b6040060302c0700ca00c80544141c11901c920131109180c01d0b012031a50380003080700f41d512681a030314000c1524a00c0b851314451505510f00307003031041d035464002ca00c030b0b00802c0007032100c60840b400f140d40f510700d1807000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 126320242 1250 126318992 126319003
    0x1807090b190e060d0602071e050708010507050a0c030c0501060305010204140d0203030406030c050408150a1b080106031802041503060e070806062427190306020c0111030f0702 77
    0x100350a810030301c0d404010030300c03000300c415402c084102c540c544d9151040c20084007034000d41101900382d0302100200402810070008500e02c0c188698103584141740d4174070740d10382228022103050000c1401082150081846106c1240b86c1510909101c20b0b031900d00e0f22910b00b1101540c204942031b0303600107018011007210b0303040640000b0040314415682c501d164046501d0340258401c15082c07507203070039250303c049004400340c401500e9480211a07440041c03802200b401c1c1d0007541d144440130300d00024003040c01c0940c950305059803003584a070300540c3d1030700300110000d000001c08070b41c2480c0109003410050b80c441c001d00b00c441140d010340f082900e0460402504a82e10304001c080c0326440100104420500402c0540d84403c0840d8060600a42c0006042440e40440740c40c46c07901100003122141d080182c01d401e0008402103411025071020507003484000b001d180e001500d01c2cac41604040000941030740040c800444c015001182800c0021200e800799001a200c8060048466040021580d0704200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 126321492 1250 126320242 126320269
    0x1c05010e06030d1205061c05031c090209070e0310060906050a0e01030f0303151a0705060703050903120c091906030507020610031e1202250b03010b031807090b 70
    0xb40c500c40c00c0038180604100c0c0a109000c134081c2e1140b00168040c1e032118540041054900e00c1110301c8040c520708544c0304d0340136a1007800015000034022041c8000391041074220799014014107030300d4232019016a5940b0b101c1103095031620810580d030115a00a0047d4030080c039a074200414024105820055500280d400007081c02c2d6968004001060742c203003148a80c181c05060004200d0050821044070301c2c22604015454901c00c40304040c1c0011820013011114090019a101c90b140c940c001c03026110255502c00e416031003070001901e00410040d0407500a000800f0340d03886c00c0c07d044081540b086150200c60f10094980c401048082e401d0b001c0d5590001d414030107031145190039101403840580303e0002400340311840a0428403e6105901000389a4008501e03100d4110818402942e6144030b03007a0613401d02c1e58011002c40740751101c3e1200180c94a03010308a0540e070820f8a104d074250030003403030004e61072415106e151440d070301841580040d180070000898020070030001c0c040340d04407594 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 126322742 1250 126321492 126321499
    0x10909050702060c0703091d0106030e0105160e040b030601060e2407120e03070f050307120b06010e15030c1314010c0308130204020c01020403060507021515061c05010e06 75
    0x101004106980450065800050003420315100c5d1a0360070100c6950070240c00662070501c141030b41d060803050140f9038504849082c0d405210a004c0c0c9540c05003612015143d400000b00c2d104a075441035401910800060a000b030000142024001c0c0082c0c500034007a8400c0d0007141c1c02490589050620f80007a40040e00d40e40d0840420f402c007810104254410702501500c0c0741c82c1c0c602c4801903544602d07040400e408004013115003854442c0c945c82259002882024071a200340480005e02905120901c40702d65041201c1582965a89006441040358060b9285c1d001e03d0a5103000044c02603000510700891264003225102e80b0014001080e45500c0c2c0c01c07800454001e03456201140c0c2e88880440c1203d903040c80c05541a0301d8440707200c003a42064181c025032050010032101401c00c4150701038011240524010b10403070b03c44034000d90b101c10f040090710101080301000100380c11341d030700703c0b4040c0301034058903441c5004c40002040a81d401090021040c441c0c0b14401040b480c011844201d80260084 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 126323992 1250 126322742 126322751
    0xa1e0b011107060e0d020d0503030a15080706140c030c0607080703050601030501080322080f030d060f03021311040b030a0207050d0f0c110d12050a030606031512020301090c14010909 80
    0x10f00540700e00d02e030180076403180020f000340c1421510740115501035250300400f02d030303140e0404003a4403010305036004480003400203500303002400c600c00003100021907403d5240d042106d03801c2c0c41070f094036034442800f500c07040c0710402155030082010807410303124266603518103000d4240810001e05556005e80000d04250400005002082021048a000548a0801d410284414101c01d02602c025a01c21665070090290402075044080001c1c2030308900e0320710401050f030710f98810100003e224000690800c40d07003004600303611142d51054a09607850b01c2214189903403901010700591081358906202d50f00402c00e0010400c0c100408590000c0303d060003038141441ccc2100401d1500818009003445045d01800c4200e40c60f039a010802a0ba00711820582e00c580c2c581c0c018003070740d1101130000000303841c000f0005131302803080c0310762031a5041d44800141d20320b00d03100d50407002903403001c0280da040d540c4482d08070004603103030704100c018408c240d8901c415900020001d01500541d0780411001800c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 126325242 1250 126323992 126323999
    0x105030901090c18051e0112110406060c1401020309060c0c120315030f010b011d04091209030308070201050601020a06020304031b110301060905270a0b010e01180e150a1e0b011107 79
    0x101b070541524840c4060100c82c41d41c3d41002114417070315000c601d070017510713000c0041005a44020a05845401400d00c85100904040704500300d1200316107030ba542e0741048000c1412500c90000600899400c4411681000f120380421601c50740151501e54004060024180d95800c040c000e8a0f1000310600013082480c40890000c0d082614105c0c207070340340c070360011209106a03940d61700c40c8012580100d0a01c10340044200007910718001c500090340031400280c0042c0243e4070500810b4480d600607400340442c440e40b40c0d903810294101810441c00d1040308800d41980d440044003100500340610411581b640620042c1400c45a07990080c48400303040c0420800d220300104d09000f002c441441c0c81d0914103002100c01403c150304280010444000000006640000c0d40e84460607580e42602d03010550340e441100c0d004881c0454030800003504655541031420002d0718100d9441280c3c10b0f40401d040b109121014081e21100e00d4a841ca90741d510001141940c0c400f00300c4070074682101c001c0500303604 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 126326492 1250 126325242 126325291
    0x908150105040e010f0f0902030c09070903030309030504170a02120a0201090b070c05060703080105030105070c0f2301090b01080118050a11010c0209010e19020a09050105030901090c1805 82
    0x81401807600440c1ca07040701e144084001d42c403400c00b1400c0d41e281082200c001038480005050344a9050741b0078030880c07082c0041c81c6403103404a070050202c0d890740309100b0b280da50140d0150041074025401d01c541440b0025101c7c000c3c01803008446440005046242c18610402c111005040b203907510301e40c0b18609000041c6d80124054064400c40f600c2c45031107040c0b914019000401a030070507500300c071001c2861010181c00c000e038641a907104400a01050b078603244112440120040040c10700a80004440b021070710302c54045826003031a11400324800356204440d42510b80905007203408641e8500100242e03902031042203500d002051070400e10391010380f219a500e6109140180291000004000302d030b0780640382c204841c036130142082c1c04030360392220512400c02c0112000308600708100c4901c558800c05208030340003049162a64040c540c100401184d0340c0d0401414030209644e10000d8401040c1040b81c40c900820985880c08800d01000185038241e54024083c0d0f108050900d40c20302c80c03150b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 126327742 1250 126326492 126326533
    0xd02060615090a0902120a27021903081611030304060212031504060311030c09070203031f0905090303010f09021602010c022404090e03070b040b090f1605010908 71
    0x1034440701450300c0b44080780000e040300c80907900c0300161a1000402e0350076240702501c103510801c2d500e901000107200c4000385c6045103141c40301645802c0c000515040c01850406c14903101030014038100004a0384036a0703000b07403e9101c1803c0c01c0f10b20121581d100108044c07880c078450506002d40146d41000d19050000e595941009554049401c010000803045030714803640d154400c100030030502205a403030503d0302e20701300b005124a0190080e40d04090131410088a414002c00c455030040d4515580c410025100c503618120100701d0041100e00062000c0702c07070050500494014000d180c2c1e951400011b5032083c601c80d4401403d00e401070000c2c503c00007c0c3c58550f06826021f003043c5624007031a20020301d0ba032240000345000c0c0903c10000780140da800002500940c0d04109042203041c0910310364a940c0d0141b071000900d00e2a1540001d030001e140d4101c20798106031a80c0840d0104c2101c00e41050034036448a0500050013841c0008111541c1d000041800a2513400b003d0203412101c503c8904190 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 126328992 1250 126327742 126327769
    0x91401240509181c12050106051303021002031e030a0e0f0303010e0a0902130c0e010c0203030d0f09050d020a03020c0103060605030f07020319020105060a0906060518060d090b090d020606 82
    0x500d12a03040d05001d0703e0502a8032140404c620181106520004010701500300401c0410b1811307140c1130002c91920301400803030300c0a452001e0b040c1c010034034550801c40c69203144849281140014071a03c03111031443c40085c00401200030400f80c4900d080e0b041c0c981103a00d5a5041c20859002607003d016082e004002c9a040d0381c10200803400913590340d01c461000c1c0c0817030203009400c12042d11b0302030f4104841c1d900c0b190036a86c13140e503520801c6550308011140210003100103035150b00100b021401c084c0280d0301c0364114981c0700c030340800c0b07011b01c64454505202e00030a4060158220491a0707040540c10f1100d00102e020900b030030003a05040010040603070000414143c503140c9048080360205000f001590f420751203400f0711000f40112008020702906040d034549000d402004408540032050307000e8041918042da68050030200d1003070b0b2820820307000c40c095a40005007003112401c1282d90380510b4081c24010b01c046080360a01562891600c1d05680018045410141c288181644c03800e105103c803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 126330242 1250 126328992 126329011
    0x1140a08070e130c080f100501180b030108030c01061e15090312030c0305180309011b05060408030f090106140f0315070e010f05070b060d0501091401240509 69
    0x116510010182d40c4010000b4045500002c000c1030011020866001940d09150f56030303490002d52119850b1600812065810b000e6585044205000b554031600e904e9500c2c0f00d04406042420f69240c0710b01a65510070380050207142c03c0041e0310303071070072400340640f100400804407890b21a145005048503a4003240c040c1c500e80d400c0d910310f050341480c4100c682034091608807401184010460501174000d00041078944046418007000850111501c1100d40d42a0780040285103040c00031030044442d41d44903074680b01340320a091201008150704000140c0f1a92040f038407a582c9007099070322100910310082030038100da0304060f03040c40054034000000c54224015203004d0064200c16002a040c4950ae441d2a0b40c094000e00c10002c569a00204400788210b080e02d034441347da0b5101c4000ca55030b200c1c4120162040326031401042032410181c5000c0038840c01a07000203550180d40d55100322840c0394001c0d0b40102d03910f58a0603010f003410b40c1655160702000b100c060200501d0076012403441d1100034007140d45d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 126331492 1250 126330242 126330257
    0x5090403030b040e070f0e040f03050c070801020a050918061e0d0b2a040b090907050c010e0703020a0f03050a020f030304050307030b07080106090503101d030f0301030501050601140a 80
    0x8040c041d410200c54003074000c001384507110070541c6680d51052540304244040e50781d6040000c441c81149100b500454201041c0c02c40c100320758400740c030260b0084242c0758180c807030340307400040001081c40501203c000c03656409136600b030854100304001031010020480b40f15072906000156070380106501c80010088084115105075000091041030050750280c211545001001416450305042d03010790041c02055940070150030441042a00940c0640480c950042010342e8084c80c5c401c2900303a100e03400b032411501e4400019078035801c4d51448041c90b541c95002038014800c600d4000c2c444000340112000410019141d074492580d02e91510714003a008074204440710880d41c40c1441120090800502126041a52b03840e02d0b992121080340c2140000780814000301d5454403803000e1342c04a0b46c0040081141d03c040c07201c10307802032000c801d401c0301030b40058050b00711200303042c0041c0c410001c84408041d120742c50342c1805402c1d00c1000340214104a43d800e0881c80002c1d10009951452a41e45402c09 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 126332742 1250 126331492 126331501
    0x30a1410020c0102040f09021309151203170109020c030706150504062c06010c03081905010602030d0b0409030807140409050a230106090b0a12020307030902091e010509 74
    0x600305100d0400e80c035003150002860208800054000300100c4520716002d8402994450642c0102c1c000d04d0004020081c824038200700c0e0700c0f90341c1c20800e055007a414030081c0903681c03000d001c000c40f100444101c0c04a200d0b8281440c0340100c00401c41e00401e0b400c0015858483e5a03011140c90344150342d80249026658080c40ca500b80c0b0601d0b10201400001e481040503d072240c4414042205040500407009a400b00801c075050030303801018025a8180c41c1c80000b0304590368142d8646000410721807414051200b004640751050113054000e290310303000341d03a0302d011072403031041541c60245280b4001c5c0d0409844000081e403180c2d990364004000c0c5080c11428021106000081c030980d4040120f075401e100900c50b40340031643c0103000c0207581d4015807030300c114030442c0099650000d20070013002c00e0003000101303c10301f2030388010801101c09107040d190007680d084241d42240c00960704000003c0c0e88503404421414002c1517036400014100e0381d00e103105801060900c1c100d5050081c1c42c0180100c10124 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 126333992 1250 126332742 126332783
    0x1050a03020c011e090506150a05151c05160c0c050103020702030a06020705010c0305061207180b030a0b0f0c0313060c09091d0d0318060902190b041d0105030a 70
    0x2d02d40c030400b00c1602184c03003110030500c0c07024080d9481c0903500b80c0180000306040030040200701041c02009080032541901d003008109200500c40182403003854108800d078546a5910303614030703240e110400d0020f100c0c01c04081c0c44a2103044003d901d414030940e400e255020407041e01083c8101d8109203400b44e650340092000c64203000e034081004081d14000b01d10300c4100041034000041c0705141d983d0800c10780d552642005040c00700500301e0b50351078021100c00c2c0700b0710350307140f6a41040356011040482c0304081c0304040307803510035483e20a40b400f2240c4d60a005440320a011800d030841446200c0c1415400d113082d007403140c800403c800030180340e610785a0306230a6004118800c01440420ac04001960a0642d1062580d070302d5000f10740ca40c041e054410101d42e01911038000340941100c8103c000420503030310743c00284001c4105981c840814503078060180e88141071100503050349070640c0e0f165032500c60340030340c490400d507003c0d003001c0403101c0140700c45c0e20f0000da91402c2507007000d00d241e8a10724100f0344 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 126335242 1250 126333992 126334001
    0x2203110f28170303060415050f0f0a05030a050c030d03020a1b0309090c0507060b0a080a0602090604050a061206080a030813030915090f14210c300c01050a03020c01 72
    0x85a5940011000b10000044059803091005580600071010b0f000104d0030900d40074002d00340d00461004c00104035042484240b100e03280041c01491000e52680002031034180c00180c100c3e980d9000300000f04150400740705505840156040650600500c4400602100f030381840010b030140d142c1840710203251044100800a01d03800400b0020f00d4000c40d0024000d40c0411400c1d01c1c1d0750309050005082d402c00c82e2002c0b08840b500c1c0e001e4480481903036640d034041e501070391400b13030302000601020501e40c2d10703290407030020602138882e110040403283c4881b007550755540c003800c8e40343c004034491400f0030381180c00994402140a006082c2e14201e143c19070348061940c000c801c0000302c5c0507030030215a41000321031068a4024480c400403d556688905444c1d403041d203616000302c05a0050503001d08011015010a00301c1c00aa88640115101240e0052649486604c00c0003450445864520044010442089840025002c01041240060310610a540703200c0105a400140403100400a511 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 126336492 1250 126335242 126335249
    0xf0221041e03171311090f0105010509040b03030a030c170c09010305090a0c03080310080111041401170406090209060108041a09010b090a05041202070303090605030a022203110f28 79
    0x303c11440d04012910500784554000219020804411481490302e419802580b00703022a030503c110680c01c02c1c00446850b0081382e641c0790800c0d01c0d0010004207560074400382c808003002e640c00055050070184010701003281003040091880c80c081c00e0250b4070041070220b802d9442c0a080c08a40da03107402c00e806280c10103441000d084403040d41c401108211241c0c0007180240416000c14540c1e50f103521845080b80c1d1842d0303510f00c201d007081100708004640c4041300c0c411a04141403003221056000049000d500084500311191556400041c00f149042140d02c0c1e0400028685041e080ca0240d8070140038051221360b00301913038098070001e0b0312401c0942059803c900050003401c01420308544d210041c090603141240d41c0b84410804070300507480010305404036a01680da102d4a18500101510f0703540c00a00101c06480d001c11100b8012040380c10b400511a07205a044240c8034554209010344400c00608548104907101048601c0d5985000e00e0b00c0b01005500c070040c410602046400f2050042d50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 126337742 1250 126336492 126336527
    0x30e030f0c040c0302090906130638040803090d1509060b03010606020114010b0a20030c3c0a0b10060305010602030a051213060f0221041e03 62
    0x6090000c500003040c140300d0000141c506202c28503941e5000d074142c0c0150030f83c2d03582146560000413160300c0c0c892440e20804620620005403503031101d00e0a03015840c4d031070144588620302d00542008102e42c00120f84600903100c1182c1c00c00d802d00345140c0d01c0344196040340384982c500001d0502403010032888210b0502d4540e04c1006041d40b03d190500c0a400e1102d020340c42541313040000180d490041c010700814581400c0c28a505a00b88282038130a5001095546e00308005602d0440800810311341c5207891000074001980c403610705e142c51510740305c801c0442d4401c0d075480300665116a58145110110885d4000315370880c000140c003101d15010004801405466842c41408201128504241e007910083d03a01401107030380320700d4246c0e900c0c490300d0b0080c1d00007082003140074882285014110303041120140541048541611030300247c4035200ca118000e0350f0f00003292000f00039080350500d5a42c11001c1c0e49410381ca45074480d03903664204009500701d2856080155820144142031081d5200c0084 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 126338992 1250 126337742 126337753
    0xa050d06090c090f120b0f09031e0408010515130f090c030303020919080c010f1803030f12050112060504031701030606050103110903061609081b04061505030403050304030e03 77
    0x3081c020030079186407013099902c400e041404200d1060b007030f4070a4011a00400c0e501c0150b26040041c03a00c205005042134080d0105202000b0b4000c4c0620304407412a0020008a465900f860743d20303401c54601074018406003184215058868954100c01b10b10902d1140c000554802102001c1c40034056518008101d0824201c002c401c1540540c00f07008280c2d4181e0f106041e00b8603594030310441410b01e000f010415400b0800082d03c070b42c071441c41586100c04510b030008102058207502c40b078002c4c1c80d800c11000320380840f400d05042a8040c030621503004904c0002c1c8074952502024189070004264054112502d60000a09050241214108205548078815950743c2c0d20b040140003051540071712070001e400c142c507040c120201070003541d8001c2d000401800890302c81c83ca12442aa14000a980c14043e15203c001500541805600780360342e00c1480b14401c1100c010100011118560444001e0b800c19041c6601925440015650703c1941804e01641e030f621103041c16504502404072030395042c13298 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 126340242 1250 126338992 126339011
    0x1030b09010512241608070c0b040206040e180115060e060a050c070902120a06051e031002070c030203010c0c0309030803070c23150c0706020702040207060203090714040c050a050d0609 81
    0xd01c410304c1c0c4124603c4103100f0310200008002c80b80600152000c03c0040e801031011700c0494031401a1a42051004081e90715250760741e00c0c2d20003088001c0380d01c14003009040980104c1c0e044c080c0100c1c00d00c1402191041c44207420000701170403800302164241d02a440210b511043c580c061400c0740e00c01e4400404803a8115030b00c1603540041d40c0143c01d82d80721040184041f41408900f40606da080e58070040c4901d0300e214203000031031111595903000d250f140c8254440750403c004284010314990303000321444c0b0141c03402c40c01031600317585550480a00700482a05180c000c2540400c01906499101e9101943c0b500c448404a860014144001d04024402101072601c2003c040d8198501245c103001d0302c440300c580b0009800070181c11902c80b2442c000c10400c1100080d9a54001c00719030384010001414018180c481600b01d03081101c0b85101580000c0302880050f0390461110100001120244407608400900400780d000350f204040074810081070390403016801d900300c24040c02c2142001c1104244 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 126341492 1250 126340242 126340303
    0x9050109140f030a05092211090a21020607050708070e0108061305071404020d050a0c02120306030307231c090503011107030f050f0a091401030b09010512 68
    0x2500200c0da03280d2244010b004500c9201005031a8420015120f0f6070410000901b80b0010041103400c2a513021200b0b8120300b07072003840c0d106082145285006154968142100b0f1003890049034101c01a2112000d040d412005101a2981303416681a07480d103840b0740c414a0840c0c03600310f0175004200240103002006c24221400203086040b540032404948650300d443c12100c9820300d03810001740c6107410280c0b0030304c40004c03001200e54903014041c000600d00320300621084120354090307030170304021230f11011000300039681044003021911210f00001d02e141080e500080c0c1d80e1141070001441c8112000451407030b42d0f42c06449045180d84d040c1956844102d8070924a00024603240090201c1c901c010081082c1c00c0500c0790103040d46018103210314040071f60700c00b40d4100ca5001e44030310400c001001000c06c0c82c0c1141c1c0107044004881e0704ca0803207a505203601c038640301854035001c50400d45028407102c650b607030344401e041c11190103840c805800701c03c03c0440c41c1031004110703003002483c0e091480e02c1404d07074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 126342742 1250 126341492 126341513
    0x10e032404021011060402042c030a020c090f01090906020d021605190201120213030c0807081504051902120a030e090108010207081e070f0605060406140a0e090109050109 75
    0x1403084880f0002100c8940d02903680340b5520f10f10b69480c3d403040300090010b003000e6000c1d14400c2d480321030400d20942e2807004005001000e48510403c0e80003c9604000541c0400c42100c40c00c07021070b00d20803186403502040c4c501d1a014481c1c0d004541c0c60305c5241c010700841e6811641c0130845040103650b5032030b404400c100406088001140c0074490803200288600100002c41c1007258165100c40030f00e071500d0070743c2010390041a420b10031303000c49140020002d0800c0c00310710000c00c002000780c2116803612141e0750820300086102201c9100703c13001c01c1f002803808200e410844511443c0a1b40d80e10035800883c82644105c112810244034800b0600e05150704800750b000d101c482107034529010381e03c82c55464241d024605002308000b50510040c0314249180e80403c01030146200c0060034030300e060316440451664200d0981da810b84d030700d050100030300781801240054006071500c030400e0111280030501c400400c0c842c040390000502d002c540701e9203080d0009018590008000e0180c3e0010782031a40a01c3c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 126343992 1250 126342742 126342751
    0x1030204122102011a0105070507120c031101030207030c08030709050a090902121b01110312040803150a030809010f030b04020f03160315050603190e010203010602010c0c11010e0324 80
    0x644a00c8000b41c2c40e4414003921908918101085050300f800320015103d50300510303403c0350340b8043c11401203089400210003030210340c010141080a00e1840c240204038514a41d5600e042500411114010a0b00a00e008000c05d9005d110745031313a6920703100300b01ca505001e50480755000007203000000c0e900502d078016107903950003100e460b046d00c8920070240c0c1e0b98441c00052803250704120302c0030640b198001c0c2040036500b202c0710706403440d2902128424060030360440301150300106c0401030080300c44074400500414070080e9041c0e00310032b0035511446a13038014062610b041041441c100c102581c40b030f400c200c150041c041d005540311440f50314441c07008d420031100002c00d00c0c8201c0b180400b181c441d02030302d0b07200c100b0155202c0c8814244424803c0703aa00050060503080f940903140780000c1c645101d007030004800d1400068895040040007429501f031b1020302c6e01040b9281140c038001c6400c1701c0703c0030020301d02400c04e080680d82410110341008040031885000610f41c1d0341d20300f07804605914040c40fa = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 126345242 1250 126343992 126344033
    0x2b230d0606030203040c09020c03190216080a0b0c0c03160503041a0f0403060f0b1f0906030603082a0d020607170108030d090501061a0c0f060c07030e0103020412 71
    0x441e8684070110704a0100322000f60010300100c40420110040e540109104c0031094192441d1001c130301200b00e0725500103481d5800513804851800030582440e502c00700540a0207015040140e0552141c840240000e824143c02e42000129542141001c0084550900c03020626110014840c10880e460f9002440340d103180510b944200f041d609058003c5a022800f1004128100307030542c1c1354a03008001d81110040b10341e89d81ca140d203d055440042c10728030034145c500704404c4019072140c02000f04600358030003000d15040050900001700500c096a42c0fa501407122404020881e101c1e180e9040010715100986010b803880009100c1e90100c0e966100d030855441d190345405c48500600c0007403800b44110503482e0410300112003441d0356904100d42d210b0196001140c51a1503c075001c2440c501c8203909000c9500000b0421101034090041080a0b10443c000d80010328002c010003142d845190001410841000d02a0f809a07000398151400303080010000d0a170b030070f11803404c090445a603410780c416 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 126346492 1250 126345242 126345251
    0x120301090b0d02011704060f05040b070e030c010504090e15090706300902010905270f0402090f18011d1501030305042304050c07142b230d 61
    0x2414148118018540c2d0f5041e9203609244030921880c0440c00c0000d4004c655898403800504c0d6010040d00543d03001d01d00500b4441d21b07900305040082d00000384007001030700a41204240e00303c10ba80043c10b880456004160101d0001848801c1038140907040400b5a01c548107201844880200098801c0035180c003034407000c859013160544260040254030032841424440b8038020844400360b00442c40141c41030618885d020784030303000241105154000e20f590342d02c0b202004000c0e91010704541d5002070300b00b0b0100529040503004545018802440100c3c4155080d0124000420b8030401c00000c03c00400200032030000308500704c2030b0340501c1d41c00d007203107100307014a1030712581401c10098108c95058850b00d103050300d41400389542a001440140245444040080241d00c4a004462148204d0025642d07954038902e8900e600020071100e40c14594005921441803000010007183d0480c020b00d100c0c4413511422500311600c0e0580f013010720b20b1008044040320415100e0001c1e00046408010a11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 126347742 1250 126346492 126346511
    0x3080a03140c1c0b06160b0a1802030c040207080f0301030b1008060717060f03030304050a1b060f0c140a0302070602301b0d09030c05010507150e0f12030109 69
    0x16400d009014403c0740091201c00c0c1a4121078460380030322040d00000c0c1c08182032a17143c410704803000c0d0100d10b06039940494203081144010b0349100c0c0c200010aa0898542e41c5403036078001c41e5443c0c080300060381c003965001a5040030700c600c00081d10b120780c1e41e0100c45541d0b580c40349071100c0040016241d00c91404000c1c000031501080200300340380304501c0c1e40d40d68103200d03600401003071540d480500490340140100b04602c2c4151000d200851146018000a010260f00c038540704400b00600d9501c1e50481c00b104505004442d848110b08410452628104410f03420a0410000c81642d0b032620504034803452004804164010441e0002c0b1082ca070241d800c04e6006050701b80107210803540080110714181e041c0e41440742c0c00c0c8081c002d0b8072070455590345266800311400b1328200640301c000000c01c110f100d080042200358801072026004c00c1c0b8015061046c60b83d501806081c121544010850316064400300500040040702c00d1000150b00b1100302d8074248a503040e06030b00c00e008040f110760808580d907 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 126348992 1250 126347742 126347761
    0x8010b03060a0c0c0b040c050303070602130504060302180703020d2a031b0c080f0c0619091e1703010902070c080706050a0c03021c031a030127060603080a0314 70
    0xc01c0d001c40507880d0099130800395178410702c40907002002240d062180d000c0100e01034a0400c080d20949104840060f81e616411070205030840c1681d2000c6e10990a02405200684401088580c01c0400078410b000f503403501242600640030b8458502c10561900450b24504156400103080800b20400310780d00c00c0244550031419a02a0110f001c8001c80802e4406005407040101803101c0d03004086030b60030038180d80400c40282d80008040c6070640d0140b01484021403012508503001d0021410820040780340782d8410801035a0755000c0710062440e02ea256013801102e07034540c00c501c420911169525a11168030784000d40000d0f40c2558048e5031484003280d003540001e00c4c0004d0328a103480c0c050400d0b40520003110718a4000c0c1040b421401001c654001c1c0301480d025008804040342c5020401d00e009542840c104800030069900c42d82c14202e008507209100c4916200a0250345003004071702c442410200701900d002e07800140520400140d10000f00d038164000c1c5418040140c00d410280c0368030713044 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 126350242 1250 126348992 126349001
    0x7060b0f0406150c051504060509120c10090501021201030501050a0608030906041418070905010f1809020f040807030c08060106050c060c07110907030c080108120702090601021608010b03060a 84
    0xa0310f104140400d0881c03807141c019995008024803ca0894070100500d08044d00c0c81d05003034404030740c0c0304d44640501011a000340150916500d40d10541e5050030602100603035148501405480c19958490301c19060010a4040710441c3c4550750600c10256500d141c16802483d0844800709894030300400800d618001000b21600746500400d0b850030181000184003103042d1281c8940c0c2c1c4003400d00140c0318101411201d151040f401922902e289a280c1000074050a074071050500402001c2a21b80021402c1c082103c070544045d108016140c840110500307904c0d2255402c00320b02031003100d03000002c01c034403566140706172590f11040d00d58607607823030000340c98038041c1c0c00350311496800441c001010034481c00f020f046154040c110040c0090400c4000c2808000c058900100081c0c46009206405412424140c01401c1460040074200401840c08120380100b410003881802201c001c00d40e96032080080c0301c2d01001d036844490038a5968080d45000304180412140640901c0d0300040c2c400e5594810f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 126351492 1250 126350242 126350249
    0x72609060f13050307080106031a0702150601211a010f050412050c060706090302011508030405060c0f010608030a3009020d05030c010c08130f08031005040207060b0f0406 75
    0x2240d420074000c1c5298990640000790395204003510701100081650b001c00440c0000c0c00d1310000000c0044c1942046440405e01901200410042c082030100f544e50008802d1002040c2d00c54100441d02c0c1c110048868001040341c1a1286da203820103d030700e030000c80e80000850b14690040718040d80240380103541300c411602100c004100180010401d42c5000e01028100612803415550203158110024042d50885601903a643c0d6172015000200350702403159100c08680e50708003650301850101269582e110710f002d41030056001003a18215030030300300b141c0301500e1b850a00030700000d41c075800025900c0d0040c51741440028039140c0756420b4a810610300e1180b600301041040c540c034540321110780203030080c1c242c1280c000060f01c01c1c0c20b003c600306001070b041d4038103002c00229a2482c6104024000040641401504401e40c13040e01e0000780c41003140c0e80e00c1035010410325200d541e0a00e044612403404e612540c2c000c0d0000507007400300b0826510a4424a0049420b00c1900502206009c101e483c40c0c007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 126352742 1250 126351492 126351499
    0x180e06060d1403030c0901030b030f0309130b0d05030a02070b040b040614070501110408070e06061207090f030b0a0e012f091903050c0d1208060d020303072609 70
    0x140400c1a9050010060454601602d82420012500002d4601d180d004031072060b81400089190300d43c079030740b600812003002c000302e00401c843d102c070b405c2e0300e0b80320311407100018850144501e9481a1149a41100d000c00f5001004201d01d1a1a410059103d80c01180150014000c3c0c440120320302a414090f6000c0d200d03c0348646040c542428000e07621500601d0394442403580512854000640074042e4040d503101d602201d5498910b80307030a6030300c0e241c1243c00203041c505902080090760b48902080e280c10010040181c0f0440e242c020b8107944101c4543c0104071000d104180101c04c0c8050710540303601801401c0c1003007042e03180007000d4600300c0d20050319180c0c1c1c20102e5401f410221110103101220008081e903014901807104001444a5000891085501308151010814003200341300440c0803590135035500300601e03405e6403004050b8030f0340b400c154188540000400c440d500c80c0d40c240c81c3c0341a4041c044070b5031034246003421254400300440700314814040e035002c0340291a1850948441c928040c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 126353992 1250 126352742 126352753
    0x8060d030c0807080d020d0e0f150a0513050706080405190f020d0c090f0603120203120a151a0304110123030606070606031a0106050301030215160c080106180e 70
    0x2c1e9584041c81d4084841662141c00030701c140120741d81c40d8401008070415001d0009048207007002d10604101007802e820440d60448503413110b89000140305280d000d0720708280081c003a950700040300110003083e40302800520480340041015070304444079038000c0e030040b4201d0790980702588103062240c00c544402006212040c0e1500014103121110b00016827103020180302c06074880441d1402c40d52220310041e255522813a0410911903051640007d421980c4055403405101030345102880101804450000341e0718521088455140c040880103010340070100d009403040503c100045402c259010b440385082901e00c0e2403070f98069180c0d12004240c007200910680c200100140d240c0c2c0000348450340020f000c1001d400080c0c400d105010203036120b06040038020b42054801c001403c070581002d010310800300300520159448171a5840c1c0144040f000a035034020361008108612280c0b4401842c4005d010001700320f2203419000034080d68411149400b200a24003071940654150540c3e941c1e254014 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 126355242 1250 126353992 126354017
    0xc060118051005010f030b310e010203060303190e0d0c080607030b1c0203070308040e070807020111040311011206090204080d0305060f01030510081005010501081e0a051308030408030708060d03 85
    0x2900300c8000709000508402181c2c101841708c540310101500d0101030840000001e040e003101e83c0c4100d83c1207280410003103045240001c0440d45d6485103124201285000001074038055119560014404102501c800d07000d1010707140413050051240078412081c0104000195401c0c401c0c40b500440c0d000c02003954265154501e091150101002e0059030580112400407000c0303801000200010703c0c6105441081c1c1ca0034030001000c1b90000f41500701103905022016120218400a80341a250095401f0350558416001031f40c0e440140c517501140a4104200041e100c1c801e0783c0904110b50411701900d1584c04165022800c90b01c0841d45658032072111131100e8201d505c00d40c8003030b5101c1440d901020b01c0030340701c0300c1c00c1d07103059000200b0300d00307080e15003006102550f0300c00000c40d002110500c40c1450311846202420070403030b000704800d16060b03407000011410b404803a40091046d400c080510ba5070700300f43c00c0101103940700b260700001152b4007401141c45402c2120030015880c0e00b40c0d03640404200c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 126356492 1250 126355242 126355247
    0x150c090303110c0a0e2d010501181502010e07050f0603130309030209160e061914041d09060c0301051807021006090902010e01050c070b0c01020c060118051005010f 72
    0xc0750300c0b01c41c40784910403004186464082d4040041c0119041014040c54004100b05c5091481001d10781410401940c910107103000300f450034103441c800d003003c0040d15140040c4404114095115620030b0900d02181000550103600080c50200c2034020f43c1c03c00c42d151020b00442012003207003030360404020000103410f01c121006e05902240719107080d484140c0d5980004103000010b450140c2e81207505400340c080e864011007003102e01d402c1500c80390305240106140701420603056001c102071102020440c07a50304081022500908450030500d8105080034140b0510028212a0b0403075511510001c00d40d0303000c1785d40941c0d0490324000d0518006030f0070a00c00c0100408090080402c1d446490b01c2da200240940c0151030240c44810800107030034940340001000708506040580c10f1060800c0b40b00140540440c02034183d03042c03503103400c1d030311f04184507210300a1040c003260344034600620001140444c60664402408900900c0500558542d001d0401411403a84111400304908142c0c100c0c0c40ba0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 126357742 1250 126356492 126356507
    0x10c08070611220e0708060f0307180f0e01020403051e031c050702010b04110a14070204060902040810061d1e01090219020a02030703170f16150c090303 67
    0x51080301c0c00328010b0b886150001031500040240451004a200404043c0103101503034002000200d0b20203149081c851000f8110700b102914003030013404002540281034404001d5a001006400b943c07801c2c3c000d0140d00b5000511a03440c010341482e083c10208003d943c014000d070342c2504c1c0c01c0000340c20b05070740087c08540220300010809171503000500214803181c45c1780b040c2c10003807035503000c0c00704086c540840f000303013128180620f441c8540c1c64040c2418500044a00341c1c0e82510700c42c24000b20042c02005014868000d1000003540301c1e06150011540c031000d074001c0c004403281035044035050304d214181c90f019540180203051000050140c3c0b91001000c60124070b410801e030894112150060380c130388403d4a50240c0100c0001d0741c0000d42d900440d480113104000c0c01d42c15102418082d5155400284c8920bc64070000c0c0c103585034441d80610440d0f50404490161103c3d0045a07130b161010360900d000708054440030b483d01c401e440314621100c002401561ba500b41c041d0348100c44182965810354086 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 126358992 1250 126357742 126357757
    0x151406090604020a020f0d030f05060402031519080118060b060f030a0b06040503010c09050316050a03142503050607030903021908091008040c05030304030201120c02030d06060512070e010c08 84
    0x1485207510021200105101c021072580340d48e80e020a001d20744003502c1081d40c0c070113805907025034030400421045032084100041c08020440380341214881d80002110400c0f026004a030480d40381442000f59050110f008102d807030310408003032140406490402001c0e0244050444c0c1101040000a801c03c1c8258441803038100000c00e15410581c890000c01d084500c10000030700444d4860310240900d140802114804801042c000034009040c01e000c95042842c0348402420810f88428001d0004c07401e0250400101010b0a600c2d058441c6100b1002d00194902c0103507084c1c09100049203c044c80303402003c4005800d0340080a0300c120410071010310f001c0c10903007650082020300094205640d074000c01c0e01012440e40d9072110506150816100022117548101c0c801e620800c001c0005036000074048201d0841310a00080701c155440301a07045228810700011090f01d80040401e15942102c0500003004126046500702d0703681c94025903614020766030807030104070710344055400901c0a00040040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 126360242 1250 126358992 126358997
    0x1212070303020a02070e0106020a06050f15060d090611041a030f01050907020708010f020d0e0f121605010903030615090e1902040b04060c1b0b03060603040f0f151406090604020a 78
    0x20b175595400c0800071400d0070b810100c01600803610002c01d2005034040c081d0444400c000704603850074240e41f0358a4142c0c030741140501400300070840324800f0f162a0b100c002c4643d00700c0c00501041c1100d4050792081e40c880d00804a103480c0200e0540b441032030746019284070b0b01c9611112506039003000108a6008002004141144549003001c076107402c0038020401030390706807400035031100e00d02610f44040d191104200bc0d4507a000046442e010000001c100f092034030040c551365503c00180803854034030454400b002e0500e6007044c0540041552580c05003085070190b1031740502281c80307483c046400b840c41d0300c21005040d07801d401141403041e250300f030045801030f4078000618050351140450001d40255000002064420741c0329001d000c100154003000c0300001ca125420182080102d40d1140000f6000e58050f05005c40050b041101342aa6031540507040314031161819894542114a44440c4000d01b808a082226407204180c1440780325005000003042d4410a0740d440d01440005d41101c0c414104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 126361492 1250 126360242 126360253
    0xf0606130f0b0d0809030f1516051e0a0905091b03090309041508120717091206091f060e01090504050102070209010806011a0a02030d0c090f0f051212070303020a02 72
    0xd03078802001903d001c1c0b040c0f003003035210011300d420103050404000d0000c5440d040b0f04030f01e4095030b1482d00001c2c0d005609141c424504a000700045480e4000c60070b01d4800740c80c1c03100f500311503008100d0203031001051a0340c481031040d40717030424002c040000740d40400b510002c0c224020075080940000d03582c801504130880c4c0c24000b81c00001002d136025042d48082100030340009014081c0306108100040404001e0149410030070394403942256140c0107603108020000c40d0b029455036800088048190541c4200e48550501030207040e01e81c00c0045960820301d03a11084c8800c400440c1c0203200444007204500c0b4440d0f0718005429020f008020021500742d5420450030006a031540381d9940a010b140d001440d096041ca82c0a250020408801c4140040240040c0304941d034000300700c17000d00c1994540401c101c01a09010ba84656003500035680c803611076140851000100c030144802c56904031855101c00200340400c81d201d44240071340780c0c040c4008000060203e03020b600142110ba005104444 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 126362742 1250 126361492 126361511
    0x409031211120a02030705032202100203030702010605010e0d061d0a030f020d020a021c0317090a020a0504110403031d0901030b04060b092214010203011202030f0606130f 75
    0x800715100904007a00290740424001100d00c46280e98a81c01004030500314907501341158090110301008260388984410668a42c0744070202c40e81c06c854456010b071040ea5034860340031010f5200d402c1240c605005600c0c041d000290b03507110b1400002071030005040700c0a420240d4407414042c0c4052490703241c03c0300a8840c92940c0c8601000105006400fa55aa010030806000001e007000346280c5598115404101101e015a6803d0011040803500c1c141203140e030002490140c1d6019940c55910010070018801c200c0400c00104601e60041d108441d13419440e0746a10070001101c1c5103001e0240c1c62941403105000113401a000490082c0e08a2045180303000100c0020707181d0301c026081121032000010038007081100074000d600408504903003c3ca114175140c0e2201075440c54171404142c1160ba100010f90910040101c031224840c6940001c1d5502d41e100d400e000380c0981c0111089001c0e00c108640e600c1c0c00d4002081d40c0f40112030062140e050300420b02c0001026001b1080040d030324a54650300c10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 126363992 1250 126362742 126362777
    0x30f051005060d0c091203020d0909090c050607021f0801140111071716090b150c0a0326010b070b01060f0206010b0702060c0a030c020f0402040810020a02070503060405030315010e0f040903 83
    0x1c3c1b040c038032990080c2400038900100038a8841d517070f400072041c1800d0843d4000010800365209080d07440c01e603280f44c1c0316103680c00007404801d4803501441041d950048600c00082e403100d40c05040c0c070b281000c0345c0901106c0000449603402e1550b1030004035007004000f40480625a47e58103802070102040f624982010344406a4640c19580038800c1e084d6207040c0c0328030f1803c1485a4100d44035140308006d09100352b90b091546c5502500030000d00f00011940d81c101106138141c29412004a210100c00343c541c2c480180c002194082401604d520b06100300014002c4d20a8402e100400300c6036024017071a03441c200070f04403a42c010b03100883c0d100c00d092240d20140d1200b045507004241c06562201111107550040c00703e040f9002c90307514040e600400080c4181e0300001030450360719491110042e03035a89501412030400e80a40c000d25814050001804140400040030714041c0000c11031014103040700000545206041c91612500052000100641d62030281d200e00d040b54000d0504188603040d1a101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 126365242 1250 126363992 126364019
    0xe09030403150e0c060412060f0608010905060f10030521070611070213060501090512010f110310080105040f0b09150108071a030c0f0f0f0a030f051005060d0c09 71
    0x501c030a043e0b0707410b260448120104001c50058105403101450503080c090900c0c14100c3d10340d0080c212030b480c8c070591621242103034031660044c180b9030001c00c01803499103000c1c0d031603250030384100e4000e40c0b5403000b00d40c44001d8484100200c982c060018810440c6001c04405941f94600005190290034814131000c0741860096210302e6a0f20341049548005900c1008008211048400f11031450441c0502807a6002146c010545000315800c040c1e07046001109800740c05070250035488a03040c0381c5d1841c402403182003e0b5010f086008204800c0070b40300d00d41103088500403200a844a00d0058400340822004503a4039084101101600c80104a41c111014203072002c0e0302041c6140d10960003080000c0c500c0141800020081201901d1420030f900440800d0103400303034220a9040005150034403031180411078034106024403042d600d89541400180050500c5032001d4540e90402001440301c007081c040060580d13500074034540c10148032403081c0004143c40e02c081c206020a61102040c0307408641d12 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 126366492 1250 126365242 126365273
    0x309060a080f0711060a090501060b0f071e0825050609030a0212040e060f060d0f050f0603030c10020901230a022506030b040b18040b070507020a0e09030403 69
    0x46040d402c2c1880d80c480c0b40c441800034910020014501c1c640d4a5002000c1419900310580c1d040c0440c040c0e0142c00d1032401840c040c0e0002c040e4650005030040f015200201034150305001346000065491403017540503001c03500718001440300d44108903144003c1d00100202c0c41080c11018500508042030741e0b00361038900301707450032081a0701c007158801e50b07941e040003602d00384280b0720f20450400d0f00e0424a103101b220040c1099107e084008402403040e141d680c02d950103424000d00074029000c9203965000101400e44450015400000004580342400012610407418130b030700502d0341002c0b5101e1080250080c4500c1410060812001095079071010001e010441d4a4080d090b50307024106406403410b0885180e500000d041d40000f89844e820070000e500895116060100b08951080d0010340108114000745070310031a0400500743c1d1001c0030300d149214604ca980481c110b40c0b40c10005641d240980400258001c80308641400312065156055030400e1840c030480341015100d5660301080045010b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 126367742 1250 126366492 126366497
    0x7030201060e090a0f0210020102190e01020d030c080a0b040204050301291203030f04051903050a0221180406090e030a08060a05010503150d080f04060e040b0604170309060a 76
    0x2602400090340310082c5540002a503001028203403082e030780344640c220745100041c0c46210707580e11020400307000b0340480c0c02002c41c0c9964400030030b400700c5014101071081c61030a03005119215046602c0d601034030516100208540301c0302041d958200a07400070b821000034041d0003580920000a00b42c5090040b458060070401c07010301101e044221071315010490040361032140c0c1481443e015503410100c112900070f91429200c800c103079a07a044c4140742100181d854000d01c100c4010710790a05078400c015091030543c560a881c4002c141404a4400036100541c0c0b049040007080740008400d5004044000c0c514083d0004c54069551a1a04100c525101c0e0114542d000041d004011503071142c012640000304850000301d0600b0072000038054040240a0b601c99445011018100c0c0e13a40440080c08503403150011340e40e0b5040f81c01d09001500548190000704004001ea24200e15007400f441403241750183c02603051601d0007200c0050b480b221120f0002c46c6c0800c10103464903840c5d080042c000c00d201034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 126368992 1250 126367742 126367751
    0x10e0a2406360612090b041514060102030a0f030b0904321005040303090b0a150e0402100810030804090501030b06100f080c1204060b0301111819050607030201 70
    0x5801e07212180000140c0303061150314801022010010b828006098400c0d518120100000e070100800041803030f6400940000c540404201c100818624aa841003495210074030100d03404070139002200105856941c05a0014058001118814044a0a403c03210314020a6014102001c82c880b440250380550f00541810747c0c0540300d082030310a140d04449000c40e1900c240401560042e12030030382484021046890388042030626200790400781d103198110462200074202401c03480c000302400d041d40082c54141307980011340c003407042403c41c4c07145401415540c280700190100710344020004042078000c603d49040400443c00003400342c4050580b41000080e43e5056050810386084010310040c03080f14210f000145266108541e5800b041243c00d14400311b40303510140da80c80d4041d104500d0306140710b83c4100000d00419410411000c03009500070030000c4111042d04441d80b0400407103484440b144108103003241815814400f001c0c07002c0314802e24403600ca8000491070350140c0015030050b9100e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 126370242 1250 126368992 126369017
    0x7030f02040b0a17040b0c130801020c06060f0409110d0c0e090a02010801151d0f031002070c080706020d301a040204050a120206070c060c1a010e0a2406 67
    0x1c4011105041e00c00c00d01303030b8018600b039a1144140036004181c0b0840440c049a541d00c0c400b01000300c0e40c09440c076070f00250741320080316580c4c81ea13550b4100c40e00b601c03c885040e040411414240305840d44d4a410004000054100710144154201c882000310b5078600ba0500002e070078611240400e0040321508007034001900c00c1d000040080e101a04511241ca0087c0080b025154101382e01501c001c4001042d204442601000202e14581600c42c140d054024400c0c85003c000c0c490340105500d610408503000c1c0c8540361524607559440d1b40c010b48001d603020122810840c2c0c080e90080d040300d8a11510040080d18616401c83d5542200c1c00c4800305944030003331803100100441100e01210000c1d00c086040c14541400103a909015100744a07007034505031000740554a40c04100d61001d174015900c01d45041e03850344000c01c0700e6080001903e48040203c84c200e06441d030002d0240c100da02203050300030192180e20b080001004125402041c040c1000940c440355003100c60b03e8802824280c803003901103100f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 126371492 1250 126370242 126370247
    0xe0a03080c03010b0306040e070b0a0c060e1b0105030a0912030903020c010e060a03020a030603020402070b010f06050a0e040b210303061002010209180402010c060e01051806070206060907030f02040b0a 88
    0x80180c2068103407002480103110712100b02e411350f6071004d02194007261803106202039a080c1640b5410040d148480019480340c56900640d401b229184202c004110301d0300320f118025201c003400c0c00c04042c8070403019a0071403658840c40180da0030007450340c400100080b4503030f206440b1003401700114002c03907100d40d038803801c0c141c040c444036954160a00f0601c1c14150428001900342c07081003490400d2580c00700b621356109209501c5071000d154050302c215665401070400e521211024032440400414000c8080385d218464400e403600c110403038450070400c0b0b0080c4100005440290800c54220220308035444290750320495044002080d03401540e41d900300001808899210381422030f0031340e07004100130380765500c4030008140010314514440d001d6031220710040700e2034401140040d0842d814020007088250042d808140610507203041c180c0201c1c0c48110503500c0340743c02c907800360160300202d0000d50581444101913034843c2e11440d00190101d40400c540d42260003a4001302094400412040381e060b8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 126372742 1250 126371492 126371507
    0x31b0c01080f100303080c1201030501270305030118140403030f060501230309010b060406090e0f041e061b02060f0903070b0c0a12060303030b0a050405090a0816060e0a03 75
    0x2000c010b03061164980032a03920000202e610004040100c06000108944502c4003942c0c00c142c0752105800d11035942c2d040003406841981401c00c00145030000701008407504070201134040303a0503100c071030442e031070038031040000020b40031540300580d02c2c1c2cac1c90380200400502c0725920840c441c0d103001940138180c4c12007504a92803600660305102c881c5481c0c100080d540c2100c0c0d032480c1182005690b8035501c0b08006400352a5440d220f82d0000000310703000c1421a084000c501c2612003800d0500d8a6a94075043c11408a4050324041e0968040340e0354005c442c21006002e040541c0a01c1c030200c1d412458101100380000300c400340d0b10050b00301c0428812454503011021750820701e060f004505001f61750f1156044400007800c2c00b240450002110480d05000e000a4420f01c005850100880e5a50341401b4002c0c004542c00544111400400419603142c140b258a0164510500501c01c600241c3d90b06059079004040402548c0c2c031074241c0c0000078140c0e0213400400c210744c101400b203014241c035002d003020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 126373992 1250 126372742 126372751
    0xa02130f0b0f1c140f1f020a0504090207030903020901140103110a0215040312020f090f030706050d0c230a1106060130050705090102120309060103060b03031b0c0108 73
    0xa40344042e460b00150355180800d001d05644541850294505142c118034050408001e002a40a00302c09425008004101030401c107464130100040780d410f0b030220a04074822100314001027941480184500324599000d012030030310904003a128a501e9400203100e0003c03d91291010760f410540081c00c03135070b240c0175051a50310840440f600706604040040d48407004080070004040078603000505140c80340840c4c41048648032002c5644002c02541d8a50740d80c84409030078012500640600150f0a0004000c41110455540d041c01c011016100700060070b01801c60000304180d0f90b00710a03414170080e080c04101001010a955200c09014026060074980c24004165421900c108185640c01c4802c581d0340c5680c0908618920002c40e0132807107800c5001d100c4001183c980410001816001401030207814000d0b022612485600c0081ca0103a200442c0d54050315001a001000010700c1a04022480d0a00400347ea0421412054442c1450041001c02c0c040d0740c0078104080295800026141c3c02 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 126375242 1250 126373992 126373999
    0x2060f030703150f090c08040f0f020303070b040804030311030c06010308131d0f0c1207050307110303090c03070801090c09090602070516050a0b0a0e0d030e100e09100e07110a02130f0b 81
    0x3c1d190a450f00d003100549c08001911140b4250003100441da000d1088402a030b52100076a075460405042801310b40e00503000c21800b05600c440e1800000200209403840304d103100004001c0c982c03e507a95116a070304034a4005404200c0400045035400041400794546a800608070004d490b00402c1d8946081000c0c080300896103040051320f8480c12152105907110b45103003003c07603681d103d10104450340400c107501206180004030600100260128600340c054108070200d54000e501c0790b156908030b40c00c81e14010a41c0701c00460030000681d540d04003020301e60150200605001064580703500703140305480d0010804c8807249040c88245001600c24000d8110386045a0925010030005000d103504a40494440c2e191804088109403041d01101000d14014110703028040c00f012010704074644814040c1c0c0b040341c501e000a10754921909c1100c00715180281d9500080d200d40009072002c031950304030141c20340584007400c3e0158482aa00010b00558000002900c0f180d07800c40b001201c0003070064612 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 126376492 1250 126375242 126375257
    0xe0a051c03020c10020a0e1203090307090203091504020a051206010f12020d02010305130804140301050610020d0c0c081204080c010f020c060c0a051005040b1302060f030703150f090c 80
    0x3860f50014818584000c03c0d00016503e04840d003013552080300c4034903115440792400000340c17034541000c40a4841c07e8800d804549d00252200f8031503080e0700080390b207140340d548900d007603860040044104582241c009007101d0509501c4d0804a16001902c18400d2520380c400401041820344440780d40008121807074030742480d04450b600103040e0342d003400d002a04050f104d10200b66407080d6202038000142e0b005541076074a03650760054002c0e24070400159446540303460009070843c01d00c0707540e03410b820140c1d42c086e103400c00303101109480c1c800c1c1c00c40c81550b0805c000c0801040c0114108480002010019492a21a40750030380440c81d0001c0c1c08030722030402444103c0c00d80141e40004003148100f808507500c1c0e0b21019001d119916007054000d01804c40d100300c40c0707000c00480c006d03403115002e0f07800741c0e8001e01c440e030b00c403102360250f0001c500300250482e00410220301240942409103420814070b00d8082074001d43c040240d500c8800a811a0907810f0315050104000d21042c402c1641c00211410683e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 126377742 1250 126376492 126376507
    0xa05180307050703080a0e03010e1609021303021507050a050a12021609270f02150307080703020a030603061a011806021b0a03020307060306150306030b06040f0e0a051c0302 76
    0x161140c04a00c001071050b10003284881c4528021004020351047c05070003082180701c8003142c1e0340d89840680300d034003216818031004580d4038498002c55284181056001d15414030756820301c07001081c113101c10b140d588001d01480c00000c000f0700803102030078010402031600f0692402d154061012000444040d0743c442c4500c3e003100c203c2ca40004d4219441140d0010391a100e006640111131942d56100725003800c0c2d82c620004020702c020080301100c0c000e07944480e14140380000a18284019981c120124109100058480713100360010030340247c081c0750100b03000c2d50725900c0306c007980c1c0c03102c03441d81c1c521100404003e080d5a005110810464058918040d00c0d40362000c041e40319080c055440b402d8203820b1240e8841d54031884c0300f0318000c5502500702c1d01c8051362400000c004240c0c2d400742e051054405c0038030786c2c9940c0c8207025200551fa00403000c241c00c0d07140c80f02044000c18002404008541e2a040603403440d00061000f16041030091000d0038000003404640005540c00040e0181894818003010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 126378992 1250 126377742 126377753
    0x51006050f09040b101509080c0a0308070f02130e0d0e0102011a0607060207170a12063c17060109060806010e1009021305040f1119050d02030a05180307 67
    0x43d0b00180c0066412980c0d03161494410f01d202d81030303000504101040c203046c2c1003450703201020100b21141c0d241681d10030010301c0e04000e200d20451001422000c0c042c00746c880444c68895041c2d0b40c0520062040341d201e10500a0601920a0386503001c0d526003000240301505a00512051804072091000b00549194a6048081c080000001500400010a90f1810064154101e440d45904041800342164010201c4980b03540900d0380031000031148141c200481015010720410340b805503c2d01017086001d0025040d81d4100c4480084803103545000b2521110a4480071902404000baa20681114504d014070700c2c0c039106910000e441c0b1700d04a0304120000300858554152405020300c2112502c1c0e0b2036880170000305039008860503d10000c0c0c0d05034040d1b0b0800300b4100b141c0b026142800b90900781081c00c8121f40218020b9101040204101d14144559144a03100c20105051440c104030b400d0a458003260400c45e24094203d44e80d03030501400400500d1047c040c00413001c021440c101040c0d440 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 126380242 1250 126378992 126379009
    0x100305010311120d230d060f0f0e07080403020a02090106200f030703050310030b1302040c0e030c0f01020712060b040b06040803070204020a11030a08041211150406020f0304051006050f 81
    0x10040284c5c50740c44e03100c0d10050501000032600854480341c3c44541100040c4000c10303461240313800c4418082000140400340d9460f071401c03603452041800090f42c8041d801e55107100d0040044003140545000d0100590f60654154007078400b41e900c4e8091440d55007052640e83c0c110711500030f55544000158044144000200c0b18556070601d0010f480f41c1ba1808000d20148043d003004001d04c404c5000c104040c1440020502c42e240203c82c01e12852061010949051988641c4a501902302040c40d071150306010310858042075040c0b0484054076034442400080e410108030480d500c54803414203200702d10313040c0100b1442a10855070700c1e140ca881c00c0071140eaa0321400c58022f00550b0081041c00f2022301800d0440480c820701d1040d23a0340d4404140008001d1241190101d65209106d44c01c2088544590407086c041c3c4189402012000c09404156034106030040084508075000c02c035206000030084080d50081d40b1440c01071405040d915108070907102c1d6900a00d0180003125100b50039651b03007441 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 126381492 1250 126380242 126380263
    0x100305060402060d0b1e031002040509070804140d0804020a090c0c0b0a020702100c0c090510092a050a1205070507020d020f1504030c080d05190203040510030501031112 74
    0x3d25595601c09000380354043c214000b200d990105450742c5915105140940806c0c2a2030102c040d108041d40c444100801c80c05240101c83e04020928005198140507000c4190044c0c001c10307081b00043d100c0003007140b0709418900c4140000d240182400700310b06046003d10091f001585d01407205a08500d401400707442403000141c0030103510000328070b0703441c416411151126005000c04c41280881d990145c030707820002c8000c480e540c026a200151410031807003514000c00c056100c0d480d201d0716143c1414060b000b0f0751000b04c40c0c85c90041d12040b40410012014581c141ca80d1502902c4420b0040041c001c40c1485600d100c609041008115081d5800700448180075812a8a107440e0a000d00120381d51004000312250000700e4030118602c0840e0000103001142d1080c008805640d031260005504e801c2021109804135206000c0ca08030341082a02c031181c0f180341441240d082c40d41e11070000e420140d48041c0392000c256248010b10500c0106d4001150000c0142d0303c204103d2245542c00c6e0340e44641d0792 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 126382742 1250 126381492 126381499
    0x603012103050c070308030117010b150f04050409030206010f06091530051603020403120c020d0f0b0f011e031103010f0203040803010806011203050d0b060c010e0c0306100305060402 80
    0xc0c0450415004000f079941c1e0300320301002c8900c42078072480c0407a50755000380160402138642c640500d481c160140144d100308140900b05000d00c0c0010300c0320b20144c1d000b429502605400074000030074951180e11030420011b000754001c0c40302d540b40210005200415401a400704a00c009084c4030f4408110030641000c01c2c0b601e0641042d10348000442c1040035003506c401403030384e0106040c4900c0d11b03403504202e00910b2462401c000c601c1000d001a8200e11641c8001011300081940c0c174815140202554070744103001502c1d1380c547c0743d1259145030a159200300100c810164807401d20002e01c41304c607031940c0034140780343c3c02800360a00c262103414500141e1000419601d08581d407149151029042140a101115815074490405150501042e0024014405144604ca00005148195074884101c01d5010380361245048041d0050780091f001130065139410950800481600d440c0922032a0b4501200380090100384c3d010000705410444042c008450350b038002842031001c207101050742c0b5002503040b03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 126383992 1250 126382742 126382799
    0xd080f040b04021302041d040c0f0f050d0f120c060c03060b120a0b120a1101030c0815010302040312120e0d0f0318020307030b151507140f100902010905060301 70
    0x344c4041e019114980042804041010b4403041201e03684103c1402284a40c44010140b074403a000840214140e100e0004c508441c003504010b01d04090f0304c60020385025858240a400868440407204192444108001199900724000b40400c038440c001c4644510b00d1b05110052a12039990514000c0050385060110b290011800001d21a440301e518454081d001d130003640c84031480700b81c4031300c02d120068404e00c00000320340c0b0481d8401c3c416542d1350040d0741c450b030742c040d01d0b842445402d107541d108440d814180e00704800f10209249100700e010156640e59455600039003104c6000aa0700c04c045059003550100040c4c5403401e800c107034800e125504c90300e80012000380390312650550041c2140083d405008100780130040c0119514024440d10710b200390440034038149002c1c051051441c0b401c44c0100ad1003030026000082d48001d02461030760686044416514040c00345c54145029140300f00055982c0b010120210f5810143c00401800c0860f0344908542c9800400700042074105100103002055 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 126385242 1250 126383992 126384019
    0x90f0302010e121011070204050a0507050406050c010b0a0e0105100804030f1107030b070315060206060a050d030e151b03132d06020304050a050f18070507050105090d080f040b0402 79
    0x4004d85a44010004401d100d207403940c21841e0401e034070050090f03009070b081000184007080c071405900c0c0150006d030341e0310b46082d00d0120101d4440d005002c0c01300c40da540b9070025040550f40c40b10042e01400300c860000155514080801c60b0780d4944100034030a000b400c108000105e0740101500740246000c0c02d1084242e100014907500345038075904000c00300400103043c00903d542c107602c180100b1741e64042c141c03107554a400d401c1c0c0e40c1c2c2c1401c407031041c0c0c4102c0d41d03401070107030381081c501212206201e824514201d80440e00000c416a0300031401c4030f0206400f0840200003605401c0c13100311885148040c6180c40300c00c030000701d0040b1b8140103041c6000121400107005000d1045840810348080d82c00c421101e0b11000000d480b58414450070f446425051004907191402070118445044000c05581c4000e1202040c4011810001c20b5081485824081c480c08501c0c02e014a034400c5660300b0181c0107002c0611341c05860084041c065810201c040e50400000400c0c1c22803050300f050301240c0310000b0751003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 126386492 1250 126385242 126385279
    0x1120b0f12240103110d1109070f0e1503010306020a09030f030305040c0e010e0411031f02030405012d02250609020114180f12030415090f0302010e 65
    0x848000d101d810840011003511816004150200b804a18030b038a00400040512010010203080c0030190500700001002661460010030652030306204920099641026000040010b0170443e400000314118a8030050456402401451910000ca40584000100084d40c91041c001400f004200ca68001503041d81c0178010320f100c00c0150f48c130201c010311001c1289401000b0f0041030710304035140c0000210228222450f80c45444c181c540b060001c0c04c2c3c80d511602c0365034000441c1e400c2c0d9a014080e021111822408440300b242d5107000001000d030307882c1400c0c40e000b8212071464600d200300c5450b081804900c012102c004030b03a044c10401c0096141c80b0200494500024505100040720b880c0b85611000c00095411115105000345c0b45c2c0181c607a0f00101217281445040302001c80d0700c55404001d00e20380303042c468641400e6009030500080c03450b0141000d1840e40b00da0003031400e0007000001e00551070360209444002d0b00c4103180685446183d540085e144007007203000c062141c0a184051001082d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 126387742 1250 126386492 126386509
    0x7030c0203010222030c05010903080703050d090c0801091502030c0a18120b0108011409030405010c030903140f0f010204050303070308130203060403030509010b1207030206031e0c04061d01120b 85
    0x12240644565244d071454201508902e07807000f22401d1211140c00185503024040f180d0807250081030346460640d00340e508031501d51020306000c00d115503d80342c101c046200e100014001e0024040000380f0300303800b42030003a40d0000c407500445c1242c0c0104104540b011650f01503420440040c10b1180f001c1030141881090313183c40e60010525081c1e00e203104c0007402207100c02241200c00000082002500907201c0002506084540307005075481080200155481610540c05450192910400307042c2c499a90380003440784d40310240840d0b03100c004010b11704601480076070b0300c5107002c1e4021407920786888007290b00c0e400303600000780a0002182c0012281003101a48a010039401002c3e00c0e42444c041ca00600205003c2e25070300720070361a0550075079003420310480d1030500340c40c40e03401040140d15580c01c200075903200401120198028803000d50f010828005907501501321104e03080e842e6400c201b0300401480040384003201d10b03e10055a00b6859810000054030b801c02c1440210703c60741240b01003180c40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 126388992 1250 126387742 126387757
    0x18050a15090b03040305040e01060309030c02060c030412082802060703050a020c0a030206010e070905060306100c0206120f0c0304080d091103100501031b060203030c030907090504030e1504080307030c02030102 92
    0x1600b0000400003010b601000420550b045807180c0e51150741ca6600441c02c491026500602040703112844a02600c0c01c1c4020b0b01c250741c64807044070301d45500c4045079445003809200844518001085001ccd00c8840d22a01003800c07071010040a1000aa110009541c2c1c0c1000d80100245559240401d505404680444801406200032109038943d6440c001f541d60f07000344180c1d840d611100020403101c030304c104600780449800400640c115281c1404101e2405100389000050040510f0401c0042c3c03a078030003a0043c00c085920845807442c04d0741541800140c028403900303550300e007041008009901c9805468101c01c00ea0b80000354105145003d0040e520600d100300e0f414480d00c240200100d526401c00d5040e06d1140c03250100d14a40c110001d046401d05003d0903015030014800160b02040f08d0010319400200341003243c050690b80c5002e94121a03094070190005644640c1810700c50500861070b582c8008220b81172440c2901c0c00c0155902d07030107603071f42c010108122030b2041c41c155502501512400c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 126390242 1250 126388992 126389009
    0x310020315100818030901022a0904050f011406010c030c15060803090114070807030f09050d0303020301080105160926060907060f031b1101140109050718050a1509 72
    0x102d81c018070016108641c1180c1c40084c203400703240300040208000c03041d50400c0c40c0c180c005000c0012a8480c001c0002c0090207501101c80c00900100303a01c0c0e0742c040d92035016500500203883d017154006c507414255194808140c4100b502c00c17003407203080e9a1110810301d07042e82502d001251100a854200006203070300380494119402c02c14040390008001c0010198010f0076200d0210408211601c20301d14041d040024040c18414005100481d004900b1141d03100d14a1404090701e40c1c4603800070302070680303204058000a6000c001032000f51800d03c00d89804c101d1841101d600c110300d009004007603032014040d651052580300d0f051807000704c1c400c44c140061103045080e0340280c0740681c00a90b40b00030600c903800018200880100500780a0b11503181e02401c4000391300d1250418070410785010303581413028182c9642c2c030844915490018046580a0802240085804d0525500c02490702c1d9054001150f0000c60b448100020f0351140c2d102022aa240005002909200541669940e8903940003080303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 126391492 1250 126390242 126390259
    0xe060f07200f0a0e15061e07110f0a030210030b03011811010f02030d090201110616080a1512050316051507030506031e070521070905060310020315 65
    0x204258034804003001540603a000d0291078002c90801c10056420720031000340b40594404246070202c07629100d0324004000d012130f40342100580002210066040b400c6203090b901040820800086c0324030032100140c11150301e40c45031506070029045d80c07001c4c80020b2180b40e840608402860191300000c0360031030000d008101c034068490f401e00000981c1d92084030a0500c01c10180c4843d8010714110300c4400c00c0344d00031810a585511230303500404000c90183c1c18005518030300c41c6117503030812410f8400da10000b07145420322407014000d0270507200941011045400d09018404c05c50030b0314071071000c842c148030080d008054107007405811417103046014042d4691742a000c2061100005150324600b111225002195403094002c40c11075030203031040c0d940b5030844204410707540c2100040c1810302c0f98240036034a58951342c07000108505910407100711500e50791802442c4584040c0070b46ea0042020043c10b10451500d04e0009465050702021001040e5020011401c9541c220500c1e44c0d103444007404200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 126392742 1250 126391492 126391523
    0x606010801052d131505011704120215090d0e01030605030a0314040b03010602060f101a030a060e070e01090e060105160f08040e060405060d0c230a09090c060309030e060f07 76
    0x64105c1c11042d0082074603d030400035095105180b02c0010761003002ca200d1640d02c2d10342da080880d40b20b00c01c07188218401d941e81d0000c1c0d100c283d10f509000710b00545c01040540b1850704d01500b01e2850081e030324113061814404014075100801d203410700660514104d41c0d00c1c000481c2080850107113401c00121500048008210186c0020705036000300c5a02e0300b980301942e02e520180c0b0301c041c80c2e8001c42d12030115122443e00300c1510780024542011001101143c0d568481540280111046640d24000b0300c3c2134028541e99604402020090400302d400c48074145040310002e8240d2140c44503016400015041e82001c1c02141190040141ea000104a5880765a0103c40310030788419907000d4840c51a20300071070307140e150505910417090b502080e40100c040ca0204003008442450380f001c4103411010b01407101541c0c40078513200190101c450000b900c600c90b03043c103039048100ca030091003c0c1450803140b20086a08028102d11b14681100c038996151160b400d00415405a010000c000038007441184 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 126393992 1250 126392742 126392779
    0x9100b061c090213021c020702220501150305100b070813030c03021219030f020c0411040603050c120105060a050403120806090603010c080f061c060501080606010801052d 75
    0x141003030350080714491260055001c03413a04034400c42203a400b84241c1c210100700a8652a00030f000380300d00040600308460b4800400004551440004c1d9512541d20300043c001c01007200c08039001c610052804000501d0070b440c26103c505424010f007100c00102090400c04c0000e0302c012208003403050001101c10960303a00d00481c1041450000300d00c00d10002d003000703003550800100c95240c0c401030b183c0750410405a85090307032080c540011044c1140070b40101154141c465000d900980d4640046c40c0d0b54581c9424401011548050042c03812018200403a5009813082103180341541c008484c0d1603619460780d141550301d845564001040b04110010300080c20340c0190764180f01d014160b60f400d80541d0b65030101401ca503405180c400214174003101003032021656802d4164040401341100d4140c5202500c1105002000701045911a4986006005400c01808941d400680030f080c60011075041000140c4812490035800c0f20a404a0442c44000100002ca40303070f013124040c1901c5400c04042015 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 126395242 1250 126393992 126394001
    0x1409100905102c030a0e060702011707050f04121103012c1011030601140406090b0f04091404050f011515030605121b030c090c0a0207050603070914030609100b061c 72
    0x311710204002111102036400d101d8122030a4941c140d4552004c1c0c45000262035800001074007000c20880f0a01074a15000b20141c000c0c0050115800103620220a81c9000c0b10030034040b0140b107010b0390410102a00705010b03601050141440340700c0c1e000211400701c8070035190084031070031614000e091207000e0030610250001140a5a4284e0380c007814140c0f803028200c050b11551150100091b0b6943c400c100401d0640064402a28400102c0307240030f5980a801c0103450f841c190994000002c02c041c0002c1042c10441c541050321400004d00c07540c2c6094552006201741885010303060510b901c003e804040c403030760005000d400020b2006052203080300d030450b031324807505004806481a440c02d0a11a150000e8a500408402005040303140e0380e070100d4000641068401905500c6298004034083d568800030b907106d85640d646002445150400e4019000305c190466400781d00303c0010310054030004194114000c2030148041422800c2c030001c00c01074840c514040d950703640203100c580c0c55813519402 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 126396492 1250 126395242 126395257
    0xc1b03060b011701030302030f0705031b0c130b030d03020a03090614010f060809060403051c05040b040b010509070e0f0f030304030501020309010c050c1b01030b041409100905102c03 80
    0xa03411114070f00304281d400182000c1c0000780160340144500e2501841000041c07064070b105800b03036400d0071100e1500ca4180c0d008000e03074800303c1d0050041d0754518241030603503403200714040d0b005100e9000d401c804641c80320305a031030350000c041c0c0004800e541240030740c0024241540c40f84c8100640300d100c164031502e41e10280030302c1c054418030010015140303100380e40e0303c0d0007440742c6000350003151240d03a001d441540c09454880c0042510850b040c2d0b0078982485024401c0b40226044002480c01e803600644541050300860320504458081c0201e041e4030000c004803040c01a40c02c040e1003206140000d4280f0030f4040306a9140c03000145c0441006019005540224000002404950115041511540280140e8074269440019102c125821615a181041d40c0604000072500e5055010406540201c4100f0201615800501c00d542d0000c0220032503908000004000140c05907403116290310070701090075901526a0b1150364002e10040d0600c1000f1502d809200140c0c02c3c480c0305680b40c1d0041c0b00d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 126397742 1250 126396492 126396497
    0xf010f0b030c011b1406010f0815040320030f0714010509070b0a0c08090406090902310e010b12070e1303080f090f03130302090a02040b030105010c1b03060b01 70
    0x58088603541070004941c0e0410405848503d142c4c540443e2a08a480d01c0410030b4131555a51495090000380902c40e1a002c0c04502d6195070f480c034281480d0a241259103400c120500e2410350810020941c8200c40394007841103407040d4104088078010080c51070040c1c000651301176800244850801070500903000c0b81143c828000d000780d5441300301141d102c00440c800c2c4154810100302c4203804502c41c82c440c09426129420440c2000441d8010604646003500860406a40c80b40c102e815860802d0110700d895210045000050300e400781c038039400c528007a200c00800c0740c90303060400529400390044030b841030002e080e101000581404c902d81d0b811042c0300c2c4843c3d041e02400450717405c0c4d052007214248190181c481c9001625158040711781e1401c020443e1055002c2e02170924000c031402d000500c03107082d070038410110585c00d5004100d40c076540540f002c1c2d00c0318070410040180420020a4904690090030051955509400e004942c00d10300c10400ca8020080400030042100301e5015001c202002e9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 126398992 1250 126397742 126397751
    0x301050a0b0111030309031603030e011b1e0207050103020c01060b18090117060609130c081b03160302060c0703060203010f090e0610140d06021812070e07030c03020c0f010f 76
    0x84403103504c80c071090315148a40c1d0010800c020303a015003000e840ca000b5100f450000b403110305004905084a01401e90800116401c003d04485940e1100d2861728403044216248100307040850065981c800701d00c999414550085080e404200c001c0d170140b0000c213120038500e43c2ced4820240340728444203150190740740b1a418441c004501c85200240030710790390003201c0080480da1119010002c150328001c0800f1001c019800d0003500103480295a94010440a001040200c0c0e14038000c400c0343c0100341c5501e01a0b800a800460004031000c803004c101c07130f01178039050f40d0f4071078034811b20307007001c1840e080584000d0000000150310191030018a003200c0c0403000c100490003035000c1042d181e4a01782c6e6a020022400c10050000709002c4603c1454003100401c070818050495a60000b070707800c40e102075048000c80c503045003031341d08044480c81d10030850000506407490600600c50150400501003004160380c0340308422100e8000d50407502ca00442408444035040e203440c42d2406415205800407240c2e041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 126400242 1250 126398992 126399017
    0x506030d081012020d120804110301091104150e070f02010501151706060c0d1d0f060703030209040213030b1902160303180803041b08070308031302010e0301050a0b01 73
    0xa054882c018070302d0710000b8490307600c2d00d5815540310300c0d8030380c090344e01030b0103200c050f0001561101c410b0307922000758a03490303800d15060400f6400009030f070007002d0007641031034107480000e029000c0118422408031000200ba07040e423800d02111424a07040140f5081901c414825400d802c03c0348000c44100aa0090040b6a2580c02101d465014240e151011500840d03e1741e03032030310529003c154018009400c2504048011803031a150aa0201c80340010650b03002600641c000510034080718140203960084070035a0000101d00c0744e105400001d010598081010b460a5549404403182001c0040e48002441e8503070910300d103208010742c1d01032911288130140310a20b07100c600070303a050400351785910300040c8410f89059014000501600d905000660348a400007031300310700a11701842c040c00e400071104250002d4808000820341014269034401c0804100040b90f10045030f601091403105105103a500d4401601c924401c0c00303c3d540c0c107500b001c0800540c002e150b0b2100e0540c0f11b0999900c0c021002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 126401492 1250 126400242 126400247
    0x100801051807080c0d08090409230105090708060f070201090c03030f021504031d01020a06021b0d02010207020d20031c0f0c200112090503030601031a09070f1404090506030d 76
    0xa01300254004c03061034410000b190581e405080b8079007002d000440c8001d607940c1e0f01101c0002e61142031105184020190601c52000d1080c19804100c580c01001d4640c208403080303544800c0200307814010442c560020b109507200f90000c0108560000203410010340702c0c600178000c409618150f01c010b11030503401e011015405c869480c099509915180c0300c1034a1180c200c2081d05070412114154405d038141240020141d2005000c0402806401010800344454040c20510488134400c00c40e030042c0618400750303850088103404190702002d20144803011031034500240910310038240e0315000d07841103120488004a485561a60799581e440000c00c0706020585000041c410050f00f8040e0f8007600d8a001e0350310381c082d604d0306041410041403105d5007210320b0742500d03040c080890b420341000c000d00003d940c040c0511142600d1042c03030001d0318001070703001c1950070341d00400420410641181c04800c00c2c0c054030099107250100ba51441d0707259181d40d40e05000d00800e4580b2400f03131103100b8801e83d2561 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 126402742 1250 126401492 126401503
    0x9140a061e1b08090f0304180510180207141c02010608030c0715020309100906080106080112030305070e0612041502120a02090105040e0a0507110c060d0510080105180708 75
    0x42814042c9001044800c0d0201d40b044030081651032140301d02983c0141850f02000a0001051042035102d0407080600211080e81c2c80030301540c08030311051000340a40c00084000c0f00826401d035400689881182c10100e009070140304600c201c40c0948a030380c3d00d485082c02007001e000c88581d0024010a070f80c42d82107690328843e4a13580485070b00002c00620400502c98004030084841380304a80c02d144001d00010001e2464185050200d030006004010054100304103500410b040c0c100800c240d850012604140030480e10000c04155803000012030702d034010366810500b4000542541e07200c6400a4410300d0708002901c090388c000c01d4100080001000030b008886121760350700c195004c25164102034030043d410070306100d818480107101c0803c0e14288084060f2207020444000700d0f031400c14042c00b4000c1240d0b914031080b5034000c64010509a120720084880440f440c00000a06541e00ca08507803840440381c0081ca9107500301402d11265515144c00c0c1d40d610b5142c1c40a54203440c2e0745035404d03580c81 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 126403992 1250 126402742 126402761
    0x306030f191e080f0d0501060305102d0b0904180201050924031603050a060614090105040e040302060f090c0f0105030601051b010e15061309140a061e 66
    0x901d982030604009020300000c0350110034045092034521281d952000895041200d030200500c902141d0f049000160340101c600401e078a00b82001241840600240041281e00984981d14201d04441c0e042074590104548002e0410156000c007646072030004040394080404030303103d00e080881440c160008691020100f03581611600d01d84040704042c0f088000040e20510403800c0c8500000e814501071000440c4038a02081000e0403508a54a0280c01c8034070113400505081c0c50aa01032040507004040c055110341c0c102c0c1215228580040122214880e94009031100c0d180401480201600041d80500852400f60100016030740e5041660b44d6486400915a01241464054081754000d10040d5000441890041d00e08500b0202110001840c469102c8003030395034581c03c2403075540c1446104c4042c0c4000306c0c006a103040c10f80004da00b803000c0b00c5907100c2c4182d480000300e0400c4901d042c90009105401e050310740e950941d050841c014800f1485a0718040043d0310a4108840b0324070524109 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 126405242 1250 126403992 126404023
    0x506040e0112140f030a090b12010e06040b120c010e01050f0a051b0607020a0201140705060f0a0b10090e0a020903030a08041b03050304080708060610121407050306030f 74
    0x1940c1c0381900e039407035280d20100103881c8103ca03011400d5000c0002d0181c0421184208000d607698190708400400e4285580c1c001d00404c40280600003185410720308503411940d03c120784400c90703111007000800800c0c902042551000700c0011030414030101040900135800241c80c0c03403001112101c015140c0d841072000d10420880301b0055014198050006044505034000c185d83c8203000c14003000e80780040036144000541d1281c51301400319a0701880071840c80b0407100c80130b402c1512507a41d50796207110107813525079505807500005840d503841780d0040907078142c01001c42c40c4810648402421416060003071100d025a9280060801441402116041f51000d00214a05002d0500484e11a24081c03c100c072041011071031a100d600c0030f90700d1800650700400285170703114600b1440c24548200f0383e1001085401c02d5080004994a1854244508941d4101440f149140206800042500003000c1d8804001c18050103030150b8040d000d580316078000c0d8220b500100140042c140c0c1c03417080200800d43c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 126406492 1250 126405242 126405269
    0x801060509060112150b040b030f01080c030c010c02310f060e01030605070c060c09080c0d0308070c03030e0111041d060306060613050904060207030f09060203042c09010e0106050604 80
    0x4220540c1e0b00c6290444600f415805d115500e401c05130354150b000d035104150703145000c403d000444032074001c0700d8014061034009000050f4114007083c0ca030910001000c0c18040c24614041c15074031035a009034150300b0414014003141c9a01c8940d00240343c041c0750b6005481c2c0c0350402c5000c1c0c2a42c01d2103000140c40321420b0100642c2e1039580c80d080074001c01401c06041040c8103080c200011064050000701c088140c492003208c84c1050002c3c2d1800004c05a81c80c412843e42503142e012a1f00500c01d1608451a0301c0c040c54422502c1c20183c010781061800d140040d842c0041401c0703220010006482070304c1104064142e000310000c4a6103c640e01a039940e90715030408000714000e0320780b44005000250b400555036008030707030324000242412005c44050325034a80000301041015407100c004107190902e81404610b031414500029600e0085e80601d0f194910480c4407000f8000b2070719001c0c161030007060341c4504240341c54441b05010b031503904504403181d0308003480441d481c640503041d6810b0782d402008001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 126407742 1250 126406492 126406517
    0x6100308030603010213080c032b05030606070f120e0301050411120a02040f0203041703010f0b030a06030b040f0201031b0804110109080d0503040b01090506030c040507110d0908010605090601 84
    0x2216644042d11a6a1640d420805003400070340c2c42c81140000e2412074080c00103501d4034024103007009405004010301050b5800c0000807441254007191042602d407030810789a0791100d000c180c4900c14418058400d07214424280c040001142410800e600c0c103903150798007010810141826104c040e02c0040888181580e02e501500b0015444e03072030060824100c4129120b00c4e001705040b50624610390107400e400004001c00c1c462115800c154005228009601e550b240125580301d10550b8000c0b0318507410000082408407a00d070300040d0146400c2001d242075030501c2d2030580900600500100c4c082030802101068041101c1400b002d01d041c15282e085103507a403561020381040080d1045414083d16010100d030030308d01008602140540d64564036034038241801c02000b04001644042502c50030141082855140480e41c41c00642003a00d000c10b498035005400d44508401100c0400c81d4802c004107100c04545c0414850f0072542080e0081000302e4030740082c010800c40459061780405c03000103201 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 126408992 1250 126407742 126407753
    0xc0418150e070b04090203011e060203030714250b0601031505090402030a0c06050d0605190b0705010e061303030e0c0a0b03040512030c0414040603110409020102070504020d0903090602061003 84
    0x101070100c840c2a02c210350f0326801c815031590441d4000768006940800148452000f4480c040c0781c0300445403002c05c2041c5402c400075900e1000402040810804050800080d0345403801d450328840c2d0501380043c1d4001152030265800740003903040e1522426040400c0c075a500034826503070060002c1000a080c42d04040a12012010242c0b0480e01882940c4140001c90400c40450015140030f660741981d501200c0e02d040e081d10820b4018a11548400c1a26100400000700c020708585c1003139026921900319040003030051080043d035560342c0c00b80101700b109040700110019540e52098404210401c01e28840c04e0791080440c11048c1c0004c1d003034205004105220300519400340c4103c0c11100303102c84034403000305990400d40c1c256001c5040402d0901c01d469142d040b855802d40c003030b64208809861500e0310f4560b021f0040d0454003aaa48440c640f00703591082c04000047c0201070701c10756450301d640c1040401020550383c141e0008220100c0443c19a1011400e1401024040182c0c6081030658495 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 126410242 1250 126408992 126409001
    0x6040e070510020c030102070317010902040f06030b01020309100906140f030105190f060f120c0c02041808070f050f0303010602060606030a0e0a0b010303020105132607140c041815 79
    0x1000290320494105404d940d90900081251900c29524183e514900002500501106801080710301e4014402413040c4c1803c100d00d40103c2c1d68516020402007500030041c0c1c00c501c031701900d054006500030015540702da0030484201c00c072a8a0768440b22640210710310318089000b0700e0749645a9100400c010000391519441040905600c03000512620342c0d2440030012480752944100c0c041040b80d004403040742e0304030082803404d40b9504828041800585401070192040b410300a12660388c400e000500f000b10741e00c0d01100c29921940c003a543c2d81441c1045501c5d00c249030002c49040c82201e510f0456002c020003542c1c102c50b5150010900364590004020854200402d5905401c0e0765030a086803052042100b00b03200350140302c4240f0a035045050003401d40e03130018000c040d5a9030018800780041d003140444a04980b981c0a203807900504150b080085100c2c515014180b0050a5003507195000080741c00f10030504100e4080100c06002c5081c040704880120000c1c02030305806070380a102c405240c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 126411492 1250 126410242 126410269
    0x20a0e070306050a06020601050301051003020907080702100e010e1c090b03090102090d030c03020d030e0307080325020708060a0b0109031b1a0a0206132105040305070303030c0806040e0705 83
    0x802007042c0740c070f0b400440d080030340310351007040145d0044004001d94102807192540005880d41c10150f950f0850b008a100c814016151504012a440004400610038400e540031000380342810b105d0f04103d0700d1528040e00c1c2c030410740034890080c20021202c0e101d0100700b465a181c00d60f1075000c0030750725200c1c10000c642c000520f01800740d5020000c00b800c5035600c60840342007900c251186416440c450800a2030071800c000345c1811301d8078180015241103000001d84030103943c4481c071943d49a0300d01c0110003100889040c0307440d010054004c409401c03030300402d2003c26210340d501110340355911100041c0503240040070040c0410310074003040c00419107841c104118140e851004040f15540c0f1031140000c00c090782e01d902102c410218032581c006a050016035081407000001562070510b90301c0d030b0030300244100f070506507070001c907800200004d01480070b90340299002000c1d2045c1c0c035075900b800390141441494040c00114400d00148032032515109a184071751520008018590429051280070f100100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 126412742 1250 126411492 126411497
    0x8150c0903010f020703030510061d0117131b0e010314011803030204140603010e06040e07030b0c0a09050405090a1205091207050406051503130206090301090c21020a0e07 75
    0x4218400340d1000d0260403c0564184401a034903100c904000b0b048400207843c1d0866004565010000e0640c0034070b44000e03c1c2680e61456030040403040c01030340d115801d04110300c80c0d0b6850b402007010740b07190842d0100120f40a8034a0504802820300810400f030a903005044000c610340f00140085491f41c00140d900100c5240001030020381040e46002c100c4a00c01c044000940008082c00300d48481955000900007c0c0c0ba00c0d82194145021800a5080149040d004a645104080e072249040000340700a603001501c40020f402d01000080240e4440c520180c0400c00004e070000325030601c0c1c410940714410040160900e00301943c1c600b0000205841c0e41020890b051003e41020b6540c0403820f140c020364030004203110b52400c0300b40f0099941943c40284501c3c424007022a6004440c011a5849800c4070114a01c50a1601c0090064040c20741c109070950320f001061010092030030b22500c11340381a00000703095101c0d000741c100380390f040510000390404004a0100501040c00c110240c00103103e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 126413992 1250 126412742 126412747
    0xc0a1d060d020c010c110c03070b0f040509090102070c0e04080d150801060b210c03181207050a0506010515040e0a090203120a1403010509070c060e01020301120b06060408150c 77
    0xc101d902070780c005002c140480d0750348480340c040c0305030080040d01a85504402400280e41910700103078540741c5900c2460030039000060540c0d40c0d2604041160050031008010300410304101c5200741c002d4201c2d14013260031068090001c50b0b250f00d82c5150620490b48006101e107009080c1e11a03001804508018800e500300865000c20103540a0040d400030701001840580c4802c0c01c65080070000071001091641c0c521020180802080608112035000070508401480e43c46906030083c907004400442120551001c05d0081c10048085a0000c0090003902110041e0340c8500400920000280404405020400082000121094110364010240c0310002005900d0303401103418566407181d4241340076400240b801d076960b01302480c85804400c0440c164150340c180004200c1005000d0511018407903403030000010451aa000001e18124580c029034907540e4502d010702c200c10280d00d044903071070b414800060603400c24174182d8046aa00703000410616035103d5a0b1510188040c006002c460400c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 126415242 1250 126413992 126414007
    0x4080a050a030b10120615090b0c16090902041b08060f041103040c0e150604050103050402030a231203090601030219031a0a110901020a0206130504051504050c0a1d06 73
    0x21400c4208400204d5104d0290300007981c0d410300222800f40e005a1601031120300c841e02c40c0b992014012041d030703100070314696540700300c0c40f102c40c41c20642e0200030b41e1011801d100440e905a4940005e140c6510a036001d000926041700c04811f80f10481800c40b001407403120000d40c0c1483c0c20811000300740b1014200140c44003a0410000c00e070751089500307031005d5065100401c603c0340d02c4100c1039482039010701e91654259880700021100e10a40c070801d810551140c0100c0c0540d034041c071100d001d00e0f6001e404407101c41252188145098180c1012030054050000002d13800c040e03490071a482081840003a000d60fa00b107500300009030442190000c0201005140030001070320320014092902488940600c461500110060070b07544500301a0118490901a07801ea50360009294140300c0d90440c1c4031a1100800301c502c2602d00510703481180d0040c288010306c4840d80300d1804400c851001543c044c003032a070b1f80c011140303038510034155241c000036114a13200c940310300f01034001e00c1d800c00014100d0f0303d040c40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 126416492 1250 126415242 126415249
    0x30d081b030c091c0b06130b03031c0b1504090f0603050d03090615050105030a0c020319050304110a031e03031e0b030d020609031b0c0d1a0a0504080a050a030b 70
    0x30407220b041c0c0d0440300090a905a03e00403280c020108040307071074050f5039121552180038040e0064031150281c124a00d401c15044404c3d00580d940c00c4014007240d446000604203504d11101c0540c01041140c0380c0b0450401c1e5003420500a0806014042c0c0c2c0741c03605241c28882402000c4440559807007650300c041c08000108144040c00012070340d990045a2110341b41002c40c03c42c0d41c40c000c0d5101142c20340008202d540d800c08290780d03014014850001c0c1c138024484059040d4440c04401240441d00043c4401c0e219801c10041e42c040d50040200d07a401c00c0054003480001d40403400058035803440c11040181001003004040000c91003485c0c0411020314111102080c01c1d4000c0c12409400d84070501d19200741030400a207881c43c40b00c0d01c020203540c01c00b019441e40760300c5003402900081d1001c540400c2801c004004040400402800160051a090501c220451a80845001d0812081000c28440400c03809802d00a94000c0507180c81c0c140f080380c081e40c450b403150300500107043d150318a1884998 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 126417742 1250 126416492 126416497
    0x60c01060510050c0609010b090402060307090305060106020a0c14060714150406060503240105040903090e090606010207060e010e010f030b130e0c0306310b0a02070201030606030b030d081b 83
    0x801c1601c0391504c40c0c16a8406604090000b41040a1617140c05844049540c41d404c14070f40080e015100d10707903179441c1c5480c12100700089820150513031244900006250380c0c0000d42080c098010b428000490383c94140030000485904d2180361b0049050000744041159059601c00100103001242d0714a048a5006c0c88260000c50742542e0150755664200103500b000d102800d8200030030404000c965000c940308510005043c090fa50241d1394594280f010940124481307406800000314503031561528000b03041da038050172100035006000b002c000240d840e018031458111100142c481e840c985140c0c000450319891100612000c158880141004507180e2122100c4101005540480d1104001c0e030f505d850f21200c0c030841406540801c04200458422030310030031200641d03000450485010781c50b04c2d294205c4880b00600140f1421041c00190007269001b03128451007a00e00b4061150b03660310544c00c4030700082000b0f805070400d012012481d40b01e501103c1d8441c0211614a07004801e82000580f01c0c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 126418992 1250 126417742 126417769
    0x2220303020d110102030f15010c0203030d021e0a0518130207050f010c0e09010b09010201020c10060e010f0303170408040b1215060a0f050306060d05040f020103110c0c060c010605 79
    0x16080142c0340b000d001e601a05601203150396000175491400c0c10940200e01400080c102407540020004d442e0540e0712850315603450b50f400504176a12a800c04141074025840b1080060500c110441090744914060040c0d40d6007030f6480e00c516003030840c3c0501581440131b0002e845075014900c2c0b9440008200a4805041541e009200504841e00941c4039a800c589a03180041c0521070451090013041d0f80341c50000381581d0314100b100d80c807a000000140e000e4000c40e03050300824007a08034403485240180d4030600842d004580020b1240c0d98032248250112503500029002403c0424450001c0d0b02424a0540040c49100e0091925a488051420301d0300000c00b00c200901e81801440500c810100103464040e00484231145450701c01d02000c1c1001c0011070102003030010100018100342e84031001d071014100c801505000314602803038901480c0207190800c0340824074140b0001941c0302100b0075641803810990003002100000342c00c02c0025000a0711403045503481e1040400c1079200c0714842d403404c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 126420242 1250 126418992 126418997
    0x203100302120a060605040203190207060b041404150b100305060a0f0803040e0907080606010c080409020d0e0d0201050402240408030d230f0402010305040615080d0314010b03010902220303 83
    0x10f0303000c2c030303e003103000d49186500c001d108a0050050029044404030158031540e0341c4030780142d03500e00b43d24010010303000c140c1d16240d20500d4540d10804004500031280d109902c00d0400600c821905800c8070101c5004941c02c0f030b046420b0840508001e80241e000c25002540203001c24500ca65401101d075211000340c2180c10070340c101103820000c6401502c0ca85410401040140007120f082c44d61060b56108020425410000f1000420b0103002c5003000300c5029120b248410342d520501c00d40800064800b1851045051103180c00300390f203c0344103104490145a00504060007002055a44180c9031b07049807544292400401c40000d00c444204020080395680c9100412032581101f440c4e00501440b8001007280300c580400c2012008402c048140c0c41642400c000445445034100030009001055007904411103080e004104e001e00040c40c40707101d19003076400b400b002e0b03c01105035404403400c0c800c0440008060005109a510395009064200291000a0b80c50900b00d0b640841c04400e95005402 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 126421492 1250 126420242 126420253
    0xa0302030a1803080d050c0d0905030301051c050d050922090c0501090e190905060703050f100303020309060f090907050904052520070b0d0b0102010603050a06020310030212 76
    0x29540e000b081d8049200001d5010020540c555224034001e0701c10000003400d119651400210f18424240c00e40d9403400305001d04000c0c4c4001807a10f6a540d80c03080c0103231445421031201ca20303410030704004204212a0f0020141406a039101e90548298011480c100e501011586050340e4042c203000740d00040204018020460000c5814070380e4094a55401590410100213414800c0e880c0118030141c11400c4445102000601c0b40741400040c440200c008059004031002d00200c2c0e42d254200c28007640440e02c200d0400c3d112008078000110b4a0720000300542c0044c4141485c929001d0094554000c18012180c40c01d08000009200031000b19210408a01c0c0810030f500e007400e041c4502688007804104030302010410090700004046a28810000c00510940c41c800c640700000d0381120b0386d1a2803003290415511079440754059000b0b10084c0702020b250040541080d8414002c25084035000780c05410381e00d440b41c451170043c0d4001403d42d00c3e0000407407400001030326900010340700010501e01402 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 126422742 1250 126421492 126421507
    0x904050a0506060a0c170403050c090c0c0c040902040605030114090d03020702010c0206031902031006030b0303090a0b0c0a0c090504110927011104060504080d020613080a0c02030a030203 82
    0x411510040c110080d03040c0342504010b200c0c1c80c0d640c01c1354440c40321410030040851a61405004110070444c005018030000311780001000f50021304c0141d046403c454041d0280d40d00244000c075401840e01e100500c0e8846410f403582801c084d03002c000b10341e00143c00403a80d1034a074004282900d01800510b1a100c2c40602000701607407050040d0070745032403140346c20f51030302080e42c0008100800c8510060306c9502d0010100d80c405001c4005940c1c9080400c1055499141c41e420307030b00c00c9100314801c140202e03060440e8658189004011a01800401007007480454103194001000d41c104415140140c4038480050303003c1011542c0d188010041c0c01030201c0c640c5403038540149088500c0c10014050a00e14041c0310451840040351080c4407400703614407015031040340c1043e0240544491056180c4400940850720f41c1e807241c010001d440100701201c0d1000c60b5010100d80d2074108450070109100c0e82c400f5280001e480c0c400800180c400d524081d00380004540020f81055029001280580e20008405 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 126423992 1250 126422742 126422749
    0x304060c0516030f020f0409060e0c100804080412140102040e01031e0201170604020d0515090f0714160b070804060606260a09080304050d031103130f02030709020c0309 74
    0x3950000c2d02010001c0c10103145980f080c3d10f0815031240248035450800f103420f400c2d140c951140060940040003404050007070349d0081d07100c3e42c0840d00340303000da001d0130400550350380100e00c0705005542c03088409140500d84001c4d0708150124003000c13144c0070007144d1000a104070900260002d016601c0c1a5110ba51440c0307032515400403840310718130400441c03400440c0540e030014a00c02c200910290002c14540d968000a8020b1082040038400d840c940030a01108110500c16440c0c2c80105661080c0a0344400c03074075000703110045a14400150b018003035040c01c84a0a80542190360740c4900c021480310b030a40c1c59600e5041d04440060000b0100740c00c02003444100e02400c0020126820030131000014401c0b0864034402c080e41e1401c11032801c3c40412981070265019081c07940c4c01040c40344d142e052514045880300041d940d101c0000b07083c0003001c80402541000c8a000360041d441620b00103d10307940f04170f5503c4d0031100580c0c5c1405a04400521400140000d1000c510a032000d540d0b201c10310001c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 126425242 1250 126423992 126424003
    0x3040b1306090b1905041a07050d180b0c030f222304020c07030501050112030206060906010e1e06030108071a04030309050603090a150e06070215070f110304060c05 72
    0x300082003000b501c200400329000c0f0071510018001c1000310310072058030303505580520840c0e025400801d01e1881c0410f51100c140d0203850b0b0f851096040d034001d200150021100791507104444811000300f0b40080010f000c10030020001c04414400341d034141302c0025081401c541005606101001101d001c11041c0164108401d0150440c0b54921900c819000610b61968206441c0c417402a81d000540981281c0200000e600079640240203014079a1030b020303c000c941c40307051030840140c03103180c000c2085441c010000e02d10411b41030351840c4490100808200d5492030b00a2000c00c03c900d2440030301c005899480056002e028880300400f4034910b0a40300d02c40185584d103614021070018001800003035406508103040382c0044401039160b0b00c43c1c0395054101444070781e00802c0c0c0c2c034010303085900002841c0c0000e102c150141d8199041c81c0d50f022400d0b07031079440110106c2800e00308440080c0c8001c0c094581c03090070086a00d41003005280c030700d514502d10b9000382c200d5804640100c0501302041800c018 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 126426492 1250 126425242 126425249
    0x51c120212011d01030c0b07050709020f09090a05131709031e0f0102091509010908010c0e0909011a04020a1404080601030b0105061312080d050a050403021b0604150c020303040b13 79
    0x180f20301c00b9807541d12048404030a40c0105030400d5000074480c010b22804000e480080d02d44004119a81e48a0480419566018405090180d680c001c0080d10384c0c2c18501c10716105a00707048114001118580d2504200e0200d800351007480041446144900d480801a02148074000300348000c0701c2d40350701086c81c9061312980407040d0a07801084117401c9911131410484e140c000030a501500e8401150040e941d00345d10350480407032586084204808264840182011a0001e0b0307000000d9480780f21155080c2d4610f6240200c01c0c00c0301e401340440c1804c1c69030081000c038003035181071182c01c1003000882009a006a100c1409680240c006005101a090806e0700412044815a14100b56031052016500191183c001c48009096920040c0032410084450b805c040b820200040d240c020024802004103071402e5005100726020400780320710303070b10300345805c944000c2665050910f42910340503081081030f904402c1151810b120030040c0c4040001e071002d003c0300c1c060143c8402c814650700e20000c3d800e90 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 126427742 1250 126426492 126426539
    0x151017070e0c13120302010603050303070507170301030503071716060b040b030c09011208090d12140f0d050a060305010e032206050a050a0e10020f07090207051c12021201 75
    0x20080d0454605030f901d5038110380e03c0d1000e16603841e00504085e801040e5603400645140000070401550300d0b40071700100840d901c03414503201d440da0400031010f024002404024415841000140b003c9015103042d1042c1c1c0138129507141c40c000c1d845190311120007205030115545901c401040016261038080d200c0307803460035030091510840c0c07580040d03020302c0d06101e182d08072a00c4803902403d01208800b1100b0302e000107041d0384881e000030300c4c00c1c41d412045110b80900060001c042c0c0b07281e5419034012600c41d0742103d4182420000716500150007040050004260780f0396901000000900a004248070342280030044c0d038841c0580304a598440e03083d80780c5038a4101d407030103041c000140c2090685201c3c600da0300e0240c1e00c90054103810f55440356000c0405600c42d10b803011000c40701d0b50005a0301014010181580c0e030599540c0c28803000d030300682c00c0007045904040035144000300240c05140d41d80e0710a191201d150809180914104d900c18014448031505050060001ea00c3d1559440458941e64 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 126428992 1250 126427742 126427747
    0x50c0306060909090705040903051c11040618030f060b03060a0209211e01050a0b01050f0d11040e04050d201005070e0312030603011b02151017070e0c 66
    0x420001d2218498022050b100d20004008512808810043da10140c80041d008000b1201141800b81541d040581c03030f00e0b0b03a0001c00c0c078000e6007000c5502407544a400c5903401c03a800e090800c034041e0707a40c03004407813072482c5c0c1d01ca4054004081603d0091266507203000d08000030354080140b040c103080c403130010101401c650040100c8134544e100c1608074440d005590b02d502c001200003188560800300c00e1070500100c8140b50300703401001d44c0194031141c05804003000c20880c042482c0010b40b0f860240703c0b46800f0514040c000001001e2503a003203c03080290900c00343d45082e0b1a096030074040f400c1500c0c243e81c0d552100d404108140d0300725446100d040303442c090079122500c64203170156842d01204000090551602d010543d014041d0380e06000b4024000c4c151090301400701c0d0b60a00d0303a0411140c4611940c00d104802c580c4030003001c014000200c03a5805040e18400044402580e02800f6002929030b40a00100180ca025007130030f1400c2122049001d402d99038074151844802c12400742802a020404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 126430242 1250 126428992 126429001
    0xb400b04080705040504080c25060c051c020c030a0602071a010b0d0b0609100c05071401050301090507050702061b0d11030d050901020903160312180909020d12030b04050c03 76
    0xb0400102c50341120045840ea43da841c01c0c11280c014841200c0d1a880b03040b801c0c0343c42002e06010380c5e41c003003101900d0014056480c0710885100380303180d601526a0b002225010459480f0400b0202d0385c4100d0b00444011844000101e03240035520001035035402e50104000080048111400c0c1047e00000856545541040700c94503a512a524042203c141c0d04da0101c000d6856000607144051401045003404d0342d407442000d0300701c1004400484c0c480c00307002804038600f0487c8021445a22040c0c0d6210f0450382400e001c4401044007602c0f020a12505110307200c01641c403078005004c40c1542c07c0c0c0307258140141040350343c80c00c0d80800b5181d00748016203184502507607001060310701142000070041180d456007500240240300391110346030503024007100850003100c121a003204a0384104400d00c55901c038200200c4041d040c0c6103d400c0860b008140070804142541c0180c3c841a00050006842507510b9607800800d10078509840042074460700407855501d0a48a040c0d03101e005603c009146281 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 126431492 1250 126430242 126430259
    0x80a03020f1c120e1f0f14040305030414070506041203021c02210d0908090109090c0e09180615030d140304080a05070f0803011a12010b400b04 63
    0xb001d2510070155845403044c035400000c10030650b2902c0d10384803054180342448030481c080c04415070140e4515003010b40b4987c04a50080d50584650b802d41d48003811500c840e910000360002e0001c02510b2032052a10100d0300740c7e2010002c100038000540c5800c0024520b01d0042e040c442220445414481ca01e400d40c40d48070340101d80d403a00300140c0c10071249408a6407103551414040c520600d14205c1c9480d009104204181c0d0042c11814026250135807203071341e105401d41c19101c00c10305040000e002d0040700d0000d41881a02c031a0050507000f40c16180030590344480d8074240301200d0327290b404503080f00e10744054242441106041e22240c503248840d00d0680c01c5408042c80050030041c621903000454a02440c4a10300760703001c00d03500c2056043c1002da141040082901b0a008401147c1c001c41c0c000f89031450420f046a00042c0d4801019030983e1134140014056045a10400c000102c855803002c028009a04150303207031304010003503c00701221400c1d42078040d0f410307401c0000003080c00c05c001e020200303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 126432742 1250 126431492 126431507
    0x90218060108061210020313020111031c050c250309170601150c0c06020325020306070e030c04060906080c0409150f1b0201020703111b1504080a03020f1c 68
    0xf8410354824021050b112060303483d004042c40003050322417004c070a0200a0f03008044114205000343d803110f80c4644490003054991148920040da0741851072188440d916260304100c2d4002d4100c0c41050030308840350010701c00c6620380c0c0c0d0364040e0805695011000c06800200c020003800d50303203140c900904c02c8042c1155030754106004040540480741400030700248601c1d080d001595108420325107455494401070b5480e044180079040c0c00540d10502d020b070301103d20080300320b0740d0014011b142c25100d08405840d0610b40c00340c0c16405006d440c1d20b46c0720b613031224000c2c00000c101c1c03c0c0c0f00040040c90450154182051a801709100e039051921600201da40c8880e81c1c03d5524150a0028000b140040c641c0000d00300c0440c1c024817941e0703c9030203c92054043d8090b01d48640079807078142911ba40c50502644841665000456004182a51140b1400c11140b0b1420a1040d11810761400391140c1c0c50501d442d07440074007240140c0c0301c1d84482050180600030b074540003165254401040d041c070000540b111 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 126433992 1250 126432742 126432751
    0x1240311180a0f180501050f0a031104060e09071d10210b0118051006020706030b0d0506010806041401090201020607080901020d050708060f0604031509020a09060801090218060108 79
    0x8050003144808554601441500900010a1102009a40d150154102d056809404c076000c1d2606000042030f003040c19240c42044c0005010407030041c04c55070392500070f00c111000070b80c21a9035108041000340361a448180108002c8006120861400d5003607804003000307200965101d00b40034207008000303210401280a42c6c1000c1845690f801203002c0312100c030308803444064035040d0130b600001490801100e9203051161500300c107000c1907a4040c3c4203000610315210740f0300103a110031010000d02d4072941c451420b0190040281000881345d80b11586800320a070400005608804140030404c400440d42c202c803000e401000f84114403ca40000c0d40b1203800038500c1d401e200e0b80500187d07928001b0350486590000c817100420040c141900028103082040b140a401203082001146c12031a040060340c049980c84442d4540030b044c0001d45402400e1041c00898000ca018070011400800307601904000c2c18000000007500c1003940104240989022018080501c0304070500c6004c1e6030198406500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 126435242 1250 126433992 126434017
    0x308030f0601020a050a0b150f010f050a020705040f0209210607050a110f0c030c06041a0703031503030e041a090a0504050304080a030810060e09160507080301240311 73
    0x340d5540401030381002c0c41160001e040f07000700d021000400240300000e5014100c0680b10600e00f80302542440420309044440740e0110700300b0401e40c10058421070003050b0607007103841035405259603100850b040d00c149401c140360b0035801040c160110b080c4603072288603c503030b03041c4008056480038415689400b00075204404000000079082d48850040a4561605c0034400484051100c418945920381c030350900b1543c428010003180208a181c1181a501945c510750303024000c0d44540000d61910740d014a004601703041d140d000c003c1c40b418080b5002001140291a80c2d219025850200001c44484244c00008001211154080c544130140210380c07007503d2240c001440d03100e6040041c5940111390004d040b500c00c1c10010002c1551218020307000e080719030700007110399850f24003d40e06000d102c140709402c000359100041c0903c2c0c4408a40d05900c41c94180b0070300d0b0028a032141c5040342d0090700114085914480303440301d8460498650041c1d400d0620301000f2101114685c180340d84144c19030b0011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 126436492 1250 126435242 126435271
    0xe070b1801140f0a0e011805040e0a05031c0f02040311092806060206090607020a0210050d0f060512010509071a0f040e090d030606090501030e25140a030803 69
    0x400703074002d040d507603080720440403115110f61030400c40541c641e1041100340b0025181d031581c4100f950140c02c480c81d240c101211a081c0c1c050801c41404024001450f0b821018441c010078440410003c2c4000c003a03020000000640c200c2e4442c04403016a026046240e4505104010400105150b000b0159500b6011280350340301b503d49920001484041c1d05400c9403d581d01c030459040812943d02080c1141d4260b000c0c0d521315518101341d152600801c0701e4103030250300100358010044ca003c030013a0791420154140242805aa0000d0f002140d2414155003a155038804090009150240c503030589980e1080003400070340340c02120b2a44a4003284100c244040e045d120046125101d001078520740300365205403d1b202c584c1c410307a581200c4403d49445c1224012800444000c80c864080d040c1a0b48181e20740030032042c03030900110300a11103000d907144c15000b400803031201800120809800c02c1c06984181c907215090104003001006000e00c050b11582e0044c6080000400280940f80e00c9109142d6011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 126437742 1250 126436492 126436537
    0x903030411060c070e150613030f021210200711040f060810020405040518030405090403030603020d1202060a06180e0a0b01091505090702150402040b0a06090305010e070b 75
    0x140c1600882c9440e440b01e000700c80c404211600842e19a0348180100413050040c00c00106c00c1c0511442941000c1505130700405091012402e40b0382e2888007280302030f1000091940c09004a4140850300c00307600c41003515487d0348c24034500e844050616103403c058030f0a1400e41c0c0c039590307404103e0300960002c4c001d5071150881d180c2e428031544800006c0001c03000360b407480044125081c00030741c031174000c2510407490030020405217819400c40200e428104001907180c030f401c090401c0107071074005104408054451201100584441d03017080074480c800d044500711010000c0001c0d00704100144101030746407070504108410407004925030900d1038524800228100c400e420b2604094001f24050318180501000185000c0b89034009a03010700041492900030781c541d01001080d032010758000c40180e2205c52114000030000301c071250003500c01000000c1008410300400e04d10783c916407015011581460301013051003820b000d4071094003140c0003d85826421314041d00e0441c080d0058054040e850092582e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 126438848 1106 126437742 126437749
    0xc0705031c090303230708030405060a020306102d02030307020d03050601050444070e040201212a1101060e0a0903121a0312030903030411 61
    0x140381480c50340d1011070316010381c5859152085110100c1044040003100100400392081070703601d442c4e2409d03040141c20140000c142c07000f280d00410410806646188004041008900305040552141820380210300c10242182c101c4020103007224103a00d40001c083c511a0640340c1c22281c2c1985028011402d8910a03107495020170340c00c1c031081c00841c100079440241c00d10788400440c1402070020741c500720080e1a00001d842d8207100002480381500c2800711a025008201d503882c9141031550008102100d50044110319410480280814001c1608540811000d03013400041500442d0040d42c104040ba4545002007200b15941903c0cac1807040c06403500300e6044500f03c2040b60f035440e0090002c1c0030303010421410490084e1001d01000d41d203101d900000c4081c0340c1d0a021081c1d0320402c2c507242804d100c414441504041c02000407030800002100e41c0076900c0401000d40740303910b4010 = true := by decide +kernel

theorem cover : BRFrame.Cov 126258992 126438848 := by
  have h0 := BRFrame.cov_init 126258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 126258992 ≤ n) (h2 : n < 126438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
