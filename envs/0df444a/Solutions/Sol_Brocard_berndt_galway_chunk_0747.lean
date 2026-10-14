-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0747
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:33:34.660953+00:00
-- url     : https://prove2.me/submissions/866edeb8-e41b-4d84-8c0d-64c7f90941e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 134172661 ≤ n < 134352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 134173911 1250 134172661 134172677
    0x302010905010509030d0f110910021c1706101d04110f040608010e0c0a05070c0b03090106060e040e0604140a121d06070b13080c15060405061f0e01 65
    0x748070103003141c1d81640c4007101ea82002032150a22030f024020b00840462a18003080094080190745640d8026402c0103441841c062081c0c03001103100b000105590490081064410f19000300003030116a501c3d620710164500c07440c000b40e1146071400c0304655580003503c1d11141407600118002c0d01e2032581428690003565901482840e910300e002420211125142603540c0307508010000c2e00390740050384102c10300c4aa80e01088482e28000303068443d4440e1504140da25441e192800f8450501160001c204260001c0100048617605400c21011201d9a80f10414420b0403041030005403402c004241443d070b448000400d00007044c0305030a0745008000026510300c1c0409540d1207116100c06404c07040003c000c0d007800003040d0510080000c800c001200c03c9807034070f000f554540c00c804400504521a40c5a107032915400d03c007607a41160720480503903007509c0140c0e0801a0b582c2842d44203940c0c0d2401980f50400180d0182040000c950441c02d88828103080700c0340701310089030300441c5010761504003c80303e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 134175161 1250 134173911 134173913
    0x20909011803020c030601080f07090e03042310180506070503043507030c0b090a1503020703020105060d05071217122509090f0209030a03080403120905030904020703020109 76
    0x1940c03012000703510950150a42041c910304252030850180c00102e00c0e9001141004400c403400030740001201c200520228000900caa4000c1c25409503500c03c4411a10000c025800000185001c001119003150900c9496400d8041140d44000f83d0711002d2460b05464001c0c000c034075200780604207291240048034035103922898400c058542e0000000d64441001014a0300d2500c461149113102001c2401042d0f5140365072201c402c4020180b18080c40f00e000020703e0700390354542400381d401134400700c0c0381c1040c03c0340117940040080d84040c0003079006505c1c04022a44601c1c001401d555403503001002808042c0c203084000d441c022641408807224501d445a1014200d40786003d016003485402d5804050716185a41f0950300e800003104403080121300c080c207015540c0204098003500c01c61040003501c02102e0311004004c2c85416002a814484d1103041c01c2010b5101d41e115124502c81e0b0788042ca02010682d200041d01c445001c020941d0b04140320821007410680c6c05088818041c0c40041003010306 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 134176411 1250 134175161 134175191
    0x711010b040c030506030f030315060703030b0a0609090b09041a0718080601140d0c0303030c02070810020301060e0303070507090203060d061b1d030a020607230109060c110a02090901 80
    0xe00c5102c0e000c66100c50401c802032400740028901000800d018601d1417410014045040000700105445000082000030915101e50722130859200c2c00707405160100d403220000382c0300c15900e2088415090401300941c4035400c10b2019203010300e07845099514080040c4100c08110384008002c00e0400c0b00902e1124907070401000050020000c48000d00a10350602801d1041d1400b64201c850044003000070310f8000801041d03c020850b609441c0002d20740c68002400c030b04041c003d511081c10b911442c104000241d513103030f00650494107991603607040e107030201c4180b544a0240040150860304100c1c1c041008402d503400656108100614400310703007006568020449041c0c0300e40c1d0850412074070759003100f140c11200100d040c60850b4121b6016801c2c03400046e17528a102080280a500042030520801045008001c3d0307030140701102440e48880c221119008256201c419a200d1307040c0040612120b02030702440d141c3c031840c030000d01180540740c0c00b4844a0307423000d00410803c0d9a10200c0b500c2c3c4004c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 134177661 1250 134176411 134176421
    0xc0c03200f061e0609040201120903091a1b06040201020307082a010212010506040b07060b180718090911040c0905030601060f030614060403200306100303021b01080711010b04 77
    0x2040405000150480000f80000780300c01403116000d0050f02c0d00b03000c0581e07000311a40b902d001510f503001c24110740a1404460040481d803000408800094009071200c031520082c0c03211104d250003850000c40000c02940e0b4615059130013901582082020b00049036404004008405010a82c003583c0c0c05030741810616030100140580d40360358045400480a0b0342591094010142151f440b03040c5030a003008410f0310b205d5000c004000301d07958001e411054949104250100c1602d07003807a6401c1c5031480014000300c130b40d00740401002e2141c0001007540b02c11071080300105030308010359100c0d0210507028071000f00420700400c000d10a409000140310b41e410052203010300b0b40b580e83e141d039100044001805540480d0002003440600c0705112034162141b0007a80c0440350404103072a8242d1401c007408100c80080c6070450340600460b4100060034240c214035004483c829400c50f290a18400d03404100c9c2032010354410f0005071060041994144642000300d411140c40740005800540c1ca000542140c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 134178911 1250 134177661 134177671
    0x803131b06020607031b0509010c060f020a080702010c0c03031a041e0b0d0503090d02180408031605121f0b040905040326041b05060d090203010c0c03200f06 69
    0xd10302010611845034188070268020026080074402c0c1c1100c07000366040c503542d085400080050104016142c1e070304c20090b00d101507811103404c0000100501c40380019502c80d0a40e80c0c0860054400708a540d0b105100742544110182c1e601026040b06560490240610f0048030041505420300346a05550390310841d4005d0f04000842c60a6401c2d806120050312100c00000340315501a810300c03070200c0c0c4007108035a80e41e003003101c0030020005182b00142c00b1108013101198000c02610030030041140304001540221003001c10314041c0700031120120303004e01c03913003e403040c15071f10700300214115502816910080b5441ca020703800c0120384aa200210710341140d03005000c810b03116814001850b40000d030b1140005404107814032110001901e03c2c65014020b040200042c4040100d02c42c1c0e404444110380c042c210003031442d66100441408100a0103480a040c1d10a518040d04801d80500030404e15000580c036803a05410448120103c0303598881c5039480c01c40034001c00000d0504960203105e014814 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 134180161 1250 134178911 134178953
    0x40201260603120901020703060f0e0a03090302010210050c192114060d1e080d02040b07020a0e072a050a0515010b120103120903050d05070b060d0b04080313 69
    0x518000301014a4a00007000711606904100044c41c03903a41e02049a4042c0c0c1e800c01310101e00e8980242c028802820140464885405103008103810541d10160210403070317000f40e0031511155200950982140d1080d20240c084100810414018144520f2a0001d039101c03803c11100a82c42845e1045800030b800341101400c40e60350804801d00042c4450701c3d50060002d40d86031071021100d80d40c09204610101592145544046d0301004101c00c0c00c0481d140c240c050b0b0020340d203803030b07031008c40c0d00c155040700404034881d071103010000c07070900f604200c92840341500c1d684d041c02d610320380801179040204c600358043da00c844100d00c01020a6041268100440c410001890150202c1d4900c400a00042c1c00070300c0c5405041022110a180f02c07014681135a800c6140f244103400801d900341d54070084d6034802007140c06020049103d0300d40140c06085c846002c0d803056201d66580a04105a0280908000700310030b0760a0041008a8441e101075507100040150b800400090f5403590420b1078402e4641040c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 134181411 1250 134180161 134180237
    0x2220501090c0914210f03040f09050a09051b060d0e03190c02030a0201050a020a12030507180e040308090307051c030e010b090c0a05040918020909071d040201 70
    0x101d554402e4000b0010040303090040e00306801d10000500c0c500b14040c4512440d03c592a0040600d0000e1007444407001c06038040300c0c1d230b480e43c49081e20400312040c401c80c0c50380c502d404001000c07540140505074043d81e01901400940301036145003c01a04040c41e03c07074004100b4086404006194428580c9a60765000216110b4038000b5040396076216905003002040100700c2c00c4c000584000039096901d81c1c1c242440740d00c0325001282240f901c4039051002d040d40306602440c04460381c041d0312031401b650320f0356558140d5507030740742d0003d4407010306204032903212072484001000700e03105100c1a60410380841c1503034a407130710646846d882d021000350000100200032001c1d081e40c2d501445450f001e441c0311b500a01600302b10000148940b2402400c56000120005120f640280f09500310781c040c20481d034040081005060407002060120041280a01c0d002408900e000d0720014003c021075500c00002000c444031403035554000880580124103002d00302146e801840224100d01c04070f4400200f640305 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 134182661 1250 134181411 134181431
    0x21306151b0303020304020607061a01141c020f04122d0305030a1d0708060f0a050c030711033c04050f120703020307120302010507020c0d0222050109 66
    0x3448008240421041c0400701100d1070040e0100c03039081c1c41c0190503080050326580da50001c01c1c028402c0c1c1800a20751807522403183c03404004101008110320083e61040d12103c50300e00c0d111118404c1d464130a081c94200d8035880340c10b804540042090b119032414140c2810b07610010f0060a508440d0112100a2010b0100c1c010300038044208404003d030740c055440c801c0701610094210f20010300f116203000d8440044800a00c00c0e41c502d81c00121041084461459a907100f843d00c1c3d602c2554029102c0418102107010704641d409550700a201c06a0110300d0760b241e02c1c0c016a64911030f03000094040c081400361400c00c07166a00414a900c0c0c0060f15130391903400d000480c400300d5425410002101500380400d0080c0d8484840e07542440800380c03000300958084031041450400160b000070760600c03e21402066411442c020140441e2282d0000c0c4403c1c0c40f80041661199544840301c3d810010703031490300025182c10b41c00141c040301540161100407103013020480070303900260001e00101d515030405d40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 134183911 1250 134182661 134182679
    0x6020c1507020712080912030a02010906050c0702030c0616060c0906020f070b0d0e010b041a2d0603041505040c14150403080a050f0c0705010807050703140c0a021306 73
    0x240d20105a20207081410300301040c44944070b04d6004098944403012a0200e40e680b40c86190601c074100300c00c1180c0e00da480c42d000080c06424625821501c0a00700404071308072212000030f807850b01c0c0c2d00502a141c0c0400d54411300045402407150450358900418015000c0342080c4a080400c84403945c07204541070070044041d150500802404401d07034002d6800700180b4944d002500c20350b0840d000c010804800740d4901a026101d4100d030264414a811281d01d00c03a2141c6103504825081628020000c460006d00303040e0100b4452026804140b03015170001c25850010011a802803003500300c40c4071090740300418004c0710341c210380032181e0600ca400180400309640d4082c03290350800302c80541e2025032614000a540c02070348002042e00c035011400c890801d001d101955000503080406640f11505240030741d030b460300300e4070900b408540464003044600307100d24200c07103215400d5141c0c0030141b810030f918681d90f81e002190705603950295075200030069032405028141403098000204882d81810144 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 134185161 1250 134183911 134183953
    0xa0c020f0d0b061c021801050411030c09010305180a050a030206010b2a010204052809090305090d0c051009030c050a08070e13020d0614011e030605060d06020c 70
    0x62180d011201c22400003003460682d280d002c2c0c03090380d803910f40c0310044540204900501c00001d50200c801c0300d0190b11070844446240c100c95048905125109c407081070a911440103031903541e507170a010058441070354003030380081c0c0e00410442420140702c2d4840102900b03010045801711140e4201c60844014540d040120f580074001500086e8603248004120b0403202040400144281030210841c0380109020740c151001480c000e048a03500342c50048429521003a209001c0c11a41846200494003040602c6019146c40c2c0c152211f610306080350b02040800300e24100300321004042d50102040da92030b00c07140d00760350508684031074160900b50b1802c121031140540106000f03022020081210013400601401140c041000f4012540c42e01000d0400040035068082d4018070307003036000400c101c0284e0080701c02280c2c2c0084818030340d07201d2000d4041044108031404240c003180905101080c801c0d8403207a007052000381000e00323841540c0c0d00c00d000d981008a1008041e0085580224000c01c83d4503d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 134186411 1250 134185161 134185189
    0xc121a010e03010c1b021206190c020c01050d05040c1a07050106080c060307050c03041a0a081b0912010e06070206040c14090a02090301020d06030804060f03020304020a0302010516080a0c02 83
    0x24007298441345402000000400102001c00b1039032540b0b0400e40d00c0c4c0d55403076104820b002d000d0b02d41d01c0c646100c4252340442002a10301e103842c94603480c00c0c46c0d2880816543c41d80c810580d83d040c9016401d07030302c2c030380a0301001d4000e80342c0c1c1e46400c50004407180040c2030045040500c130021501e40d616410070b2801c50b0010783c00b0b0b14950300255098001540e43d02c00b2a64401d00904080781c446409400c1d191171401355401a00030303240c06400c8608418605009040d44517003a40d0b820b40182d40b10506800204e08010300041c0088060003940903e00e003480015940c04018000050108680314106140150036514480075130401c00c140000e009e151001c20004d00b160711012111104d031a4042071810400910113072003541e02007140f020350b40e82074040714100b1895142c184451601d904003441c0940c00ba100da00c01180003108540101406030003568440c0380c004100820f007a00e1900191032560051204501170407010080100152000300a42192400c681e075038140303802284140000041003040c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 134187661 1250 134186411 134186413
    0x120a08070c060b180a14090c060304260715020c060403030f090b1503010605010507050604020607032607120902010c02040207021c0503090906090f0402040b030c0402040b09040f0c0504090c121a010e03 88
    0x42000750301c7e074001920410301141590095942d07039440c144124110b0b070810f20440204084503800c01c010103030740d01400c4218000c84140b80080305680400e007c0307101d050200d4405401c054000360109002c1c0d400524829400400401c62002075039559a800ca41120101c155464207c10a4400d0409118140c050007080c28018070740042c0c0d8443c2a59100001c2000744a41800510304080500c1060000800c04220946400d46914402050041101201c0c803034001190801c4e010903404003401542c0d0b00c2074041c0c40e048172503030854084c000a5404882c06980005048512550340710f00303c0129020301d80500051502c81c1354450421900040c0a010f0f0f40c418280701c8240080041c00c0f107213903030b0000c2d4102d8000a18803501804603003080700300142e882d8014400b00740010600348a6000b455001e03401c541c200007144031158501c049071007241128002a07814482444004000d030720040c070001d01c42c14842002c60400c081802981c42d18940e060302c003000c2801101843d6040481a181000210 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 134188911 1250 134187661 134187701
    0x1513150f090e0a090c1401020d0305060a05062107050a021903120507121a0f03070b19020102040803042c090d031a03150702120a08070c060b180a 64
    0xc00014045041c42c0038a01c41c0701c20318404a83d00000b0356108002203940305554444955403420301d12403a6605503a4030b030140c0600c3e0680120b00744207200b60341c89840024030709041c4505100a1080c04d400506121010003050302c00580e00c1010b001080344124040d0351500d40d1a204031000074142815a44000000e24081c045540040d800a00c01060149141c50010320b9640700343c801c0703c1610030311411541c104e141130303921240030320090840070722800d00b910301c001014402000d2558a44052142d07203035501c4184059050f004c041d08591207000e15034400941403540f40c00c0e09a0071580150302c40e02d08030002d8080c036400d07100783c282c103902059000c107810300302c0380341c21b440c100c0d1074502005086c0101544d0315002c0d00c0200c0211074400c1e0b41b43c4042c0494080d03202e184074040d5100025201c0c0005071040114119600c800d8108a0300205559520016a91100e90042d12049903564080320126150140082c80b905d880340307030310303150380750045040840d081c01e0841324100c0d0009010744d00758424503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 134190161 1250 134188911 134188937
    0x80a110c0a0b10240c06290a0b0708070303050414070905070e06090a171009080325050406201c18050303030103021c080706060e0601080708070e151315 67
    0x4104140020b04d981070100d60040303540380c401c0041603a1640340c014505034815000c003038100320011104c18407055078080001070f04e41911000c1030207004c1000303150310010011030300001e06c41d81220b60010310030003a0914a100d0042002c4c00c03c2120781010101c1623030380040100040c2c0c0144d11518124060320000d25201d441c00c08030340305e420503000719082440c0c3e918400188003420049290420041401040f0003551880c1040d5140c1c006c4d10390310081604941c5030f46000320b1820005440e032285840c1e02d403500383740103002d817601c0741c0e43c2d031602d0558440c0d41e00b15180b124050201603415028401103000354200071070044c2c03034002404042100c00c1440c0c1420701c002d4800100f2a81982d40440c0d80808041850701c1c1440180c0e41007030010700c10360021801500b040f030680c1003074080c0c0d410440c2c00d09455455000440e02c41c0c108450340c50014619601083c0384600802c00b0041284001c1c000054121465007500100d80c0040c44d0a59511070300c48081200290004024159164510702070307000600c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 134191411 1250 134190161 134190209
    0x12030304030c150e0304080c0103051e100e0c0910080106090e06030102160c060305060919020d0e010501120203060a110f0c07090c050406030516080a110c0a0b10 71
    0x10003030004041c0100940e030320051240410340c248541403c00401e10801001450b21600c03500a4482d04074180300b40d200d0301040358000d0103407510a44001a00c1103549070004528502482c1c0682990b58021041c1004a110600581050301c19003c8582441c0e40d051200c0911446003541c00d9400c08010043c0014080d60fa40844110b08031040b20000410940f202d0001a009104400c924000006440007940070807503601e42c00001c84015850400c01d5a48440a0015403c4204e440010040f0240400c11051403240e02030031516050000c001075252501e08034508443d000e070420b11020100031071640841c58200300742c1e544156580028800c9503a20f0044111600a046905802090104004410040402620300108004a410320065035245000f0b0080c0e8464011100080d081800084416418001440400ad042da8a038546641da48589200800c3c2d51403095000303204c1044000c14102c0e041090991030f60003460881039a0070058400042d44c0c0196101d5540045940c140740300ca514 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 134192661 1250 134191411 134191417
    0x15040213020912030309011e06060f050d14010b1804021312080f0a030f061205150705090603040b160804030c0f061103090d0906020705090c0d06150513051203 70
    0xd051240540c84101d031074001541807090071480d100707502c00401080340c00d4070705402c01d8500e00c8540055040d5004105041c5040c1d0380c16001d2203011401c038a120b0440c2a00c030307800070001c19500f50b00c006094841c41c480c200001d0b10030b80c85484007842c04141007503420801c10203585031110803241140b030610b26000720b08201c041403048020700c21034121307040180180e1404548200c50000c50b52544c0308460b6001a0040a07003406807034030781f4500384e800b00f038840c03903d0b0081c0785054111008080e54141c01c401104447c50007041e1070200300341030000c0c0007a51030340c0020314042d620420354403102e132901c0115000810b1980c0c003540c041001c40c00500c000b00c0d40190700146960b4003c0c0c0d40c0700300c0103100d040c0348024149000050000307100000820220040105407035480302031071340d01d010507070799910000c0b41d40e1071581c0200340d0b00c0100d60000c160f0a20098009214400030b40d100481d80030703941c1a03042c0300c2840300ea45900118800098180e401c00143d0180c0001c1d002c01c840450a0002c41c50340595240 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 134193911 1250 134192661 134192689
    0x90b18090402060705030706050405060606070819021c020a020907030501260a0c090c020c040524030a080307021e0313140111010c020d0908011a012703030c05150402 73
    0x308800d4003003819501e9103404c942d00f0b2908202101d55650b92481c00e100100803c84082d945400b0b4103000c245507181004c11510402e030808201420000c10380342201011840c010080103510034440300300a02e40960010f0311942c58140c01526204c140c500521191f010b000b000c107003c051a0000600400c000c0e850701d05040c0c2c20a801020074000d00c081a10b140209800c07020313094135901000004c010b003464020500c0507041d5404c0c1c07006008004141300607150705441d603070445910507a40c1c074a2400c048900014080006040319445c802540782d6000d20303403064843c1d40c01030700308001030028a00e80c0d4400300400c01c0081e00840c50b007082ca0009a604601901407a001c60440ba802c7e140310307a110b0b03010340d504c2803602c4008000224240030080d642e000c94040f0030022038140e1070002440841031007184207100440d000034500c021000300440c0c050300c0d0b1041c2019031605004814040100c107490080c0030710711a8540c00c1d1030b840e90741040c0e0300d406480403400c04454003c004000c0180c6410b070f000c40800d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 134195161 1250 134193911 134193919
    0x3050a0c0f0602030c0a1d010516170d060f06050705060609070507150b030d02060f070509061201060201050402010306050d051b150d050708011221050c030a02010c090b18 75
    0x50000d01c1c21800302606810301620036030010040c0300a0641c00340c0180390016082d00d074070300c451020809215100b600384c0c00c0311740424000c0c030940c0400e00180d13460604a600c0b40e084405c60062118200c80c407a0010010291040c1d540d4000384100c10050f8044000342049060080c100781c0140d03201035840ea80280403d010340310300c0011400c000d000d101540c0907540e00c100351440e000300c9005038000a2000c003981e1403103032040610462a040c004907000b80621a800c0444d9907c0c0c1c0c1e00300b0192071a6000400c0745400c8241000720301c162900d0f41c0710150103800c49600119031030034240001000d41c2c01981186101e46a500402c4001401c00603060001044458809994840910002e03490b0782c0d414900d040d640e4800980b104ac581042c1c0e110703900c6000191511081a41c858181280b00b900b1040020300c0741042c10074000d03840343c00e0a16840e22800b14130b0f095190140c5100400d081da04008600c5000d40c0d1204a005034a84d0070201103005800320304103640c181281c0c6c14090041d0001c0340401400f07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 134196411 1250 134195161 134195177
    0x80c03070f091203021f09170a0e1201150b0408030a08060103060503100902090901050702100902130912110d020c01051303060501030c1403060c0d0509071a120a060303050a 76
    0x1c86029000e40d100a03e1021459000345100d0b08020303440d05070b01d9405c010040c1c4445103254031202c0c40d208218881d40c0104102c4040e0300415005007644c0c0c0701446c20001d02c51141d80171002d65480d42d61141d0402602c2c4004640c60040d00c900444892142d0494008088140814001681d0000903034070f1181251030724040700e40b911385c010b0f4001c114a0f0040d07a0140500302980c5502c92281e044aa10a0700c00d90704118181d550315035035802c13501c060701c040c8010b800c007480d90305c40305031507811a503ca6800200486414240610030204480502404503a07075408445c3c0c1040c0b03d50000b40d201d0003800c1d0140039002c0c2a2610340000c1d26030f5500090503051040116044944d5801005403070061a4480420002c950f1241080fa80012991241d0f4000c1c00c1855a140300301e080100300d06001c0d540c090a050304060329440818003800c001440000c907840758080002c0c01100132481364486c40d008090341c035610048c1401070600808000c100c0c4e81c0c81030a181042000a6001d02141c174a20002e18000e80 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 134197661 1250 134196411 134196437
    0x11010804020a0f060f02071202010f1d03030a0e0910060e010c080c0304080c1309030503060108090307020301060b03070f0c0804031b0b130e072d0302040e090303070906080c0307 78
    0x4008483d400c408084414884041907841e0040c90194607100349070215240d41c7da80e400803c0c032241c8002802400142c16044c00d40c14140a9150781c040503500c20000c0101c0ea00b0100030034515049154080300052400c1e844801e181030280d209500021080c0e4481c411504041000d0001074060940d20704005400d8440810300948a0640d2030360f030398100a0300e54841e038a001e42a690741e501800541701e4110340d020318004481c144100c80c5095030544850b8116540d103801554003140080449103280810018040140e4083c0304600140c5407a403a865280d0400200040c0a01d12600089040c08800c141c03a0b0b0206113000e0507101100d9200b1058040048a01c10100709000c099004c00d0b54648003080d0412058103085004041d80d044c949016495511024219883e480403c0c440f2a0020b801025400441240702d064180302e200342005460310b59034440d04000d40d1011500c800c0f03e030b0004002d20040720752019100005040c1c0f840c1081c15803c1507841c0326224030000d0b0030907003808441e200e048 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 134198911 1250 134197661 134197669
    0x3090f060c060f070e0a0f1508070905060a0c1a010915050306010909052d060c16020f040e071820030c1e0304120311180103020c190804030309060203071101080402 72
    0x101c4902e1702074284c1c0ca08594801c0d5251000300d4501800100200c10000c0c080403511800681b481404980da440351074610740014000203034000781040b0100194116060b011072080786c1d440941c000c01e111030f802158076107e03040c000c0703600e102c03e038040004403000200807d6400054545c10740d44009400524220300d450214a4181c0c020601c40710107824031a0311020b50125641c1d03040400480007a034070540c1c0d0b0409400104d1003942c0c480604070900409110150426104000e1214000f61001448030070945070b0301c1c40c0080d0782d4041844400046d81800014405006091400c500101200ca6002034021020248d000080c04003070018400b003817650003030b4400000c028002e161100311a94908040c24801000d0320180c050001090400a40c0c10300000481b0482c0c208801074140076205101703103001100650304c080f03103111f614401c2c4265030385406000700201c07201510841d0703a10384d0b8910394035001d44920000e0f48001c095420038040c3c00041240513050450003403092925541c2691903100103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 134200161 1250 134198911 134198927
    0x30a0203090114041a030103111f05030702010603061a03010b10020d050304060b0a060f0201050f09120a0207050a0602032d030a1805010f020309011a0a0b280203090f060c060f07 78
    0x440031024116018039002c45555000b541070b01d012745510703815604a034080c00082518001e1040080c00c000550060440c802c002558101c0d2062001007040c995a03280d02c41660202e203440b002d4a54114030b8000036150910890080e5902a1003200c001042c8810282d264220740002405000c0700000245c10080c4944c0440003d450080011803c19110403000380078103000c50703002d0301540c40d02c00407a81100c0c20000700b034481c0f04c90718010401408070507440455500142140015403003101c0c4080f400750b54424404003c1c003443e030f00450302e0711580c80c00342e400400b03d0f0702c00d203074200c1840341c15070000001c00d011030f98401044640443e640f6405022116250306a4402034065460200078400e1118160000c60040e02d158009010300f035200300540c00007220b1810025030008100300208401102c54003d848600c20b049070124940e07917072084030310320041601c07150001a04001154201442c01e02034280c01d80c0002e59100f81020902200190b4881e00540741c01a00c080fa40001a000c0d44500e0503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 134201411 1250 134200161 134200169
    0x80a12080907030609060504020a09020c07060e1207120b0c1c0b06070b0709030c0f06050d1d0d020a03090e04050c0d0804090f0f050a050903030f040c0e0412030608030a020309011404 80
    0x4000380c5c51181408802464252001c81c0f058101d40c0340011000558025211240820b40c0a0822646010425140800100c0400c2c2d041840c401c560540c245007404088028100700400c071783c4440151400702c91548000300801040003050107000d0010811401c2882d0010b0070840000704400e0b444002103c9003d00c1d400217143c00c031008100b2061581c40b89429088030b12866801c150140c840601001c0801a4010640003a905210600342c000306a04803000b034240250c02800711880c2e000803d4200034122075010056030050080000f09548003810f20001d0070310ba00d07012005d0a040c2c4e02c154075008400b5050340f0905051b03418000748007015048400424001104100020f07111039644041c1155001541885160400050b80d141860007902c2c89414503c2c0610315542d80c4a0f00c8001668028009035400b1072000c001144031880391203424007070f90062207122502c50301820010103691454103c004650014048001d1881d00041900c880110034208074040c0c0103030000180b403034040c41c3d05c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 134202661 1250 134201411 134201423
    0x7080d020a050904060b0906071b050301060305031b07050105030105130e030c01090312023a0203040b09010c14190c15020705060a060f090e150718080a1208090703 72
    0x2036154a2581080007030581e001c00344c0c0c0501c0800c1c1e41e1a0005928051503150680041d000c00030140000c00003103050040c06045000f16454985600c0403a003140c0301078000f1502980002000215080c1c900180180c6100c50801403565600b0440020500d001c18859940201d040d0000320740c184400b600411008070b4a081160384803100591880c1c040c11604000350003080c01c904280c10003a8280c000c6520440c0614002e1580e459a04500c0c030b040b06020700c026042c140702002c204c0d40714010303000541c0120b0140002c00920b06020301e1150840d10204850010b2007012442031900580c10300070b481040307601c08555200009c118000380d40700125000f00400c3c040340746000f0036800116a001d005118003400c1241d030b0030343d03544d0b01100031607109020302d200901e00c0013002c00c8007611a8100d5071501007400242c0c0c0c2c1240128104240032007044d1004400f10f0b02219002118125802c01074004010312001080e03420070544a070a80c5a00100c05c030070412076a9800600e107264200300038001158042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 134203911 1250 134202661 134202667
    0x1406090d0c050411040f050f0d0c09091208190b01020703050f0109110a080709020901031113080d1701030b040c030f0803220201120c1103040f0503010f06031707080d02 74
    0x840c000d0001c00e55400b03024416483c080540704a80540da0aa03801e441e038440c854503500d42820100040300414949199000b0940c40c45040001c4000640000414081328040340354800c52401c100d000c0c0a52116608000481c0304000c40f81058000140a681900500040000740000101c1c03d000391500064603d1007103d002180524055000810003070143d0411110700185078100140103c075481039005541c000381080c03110030741550082c01e0110301410002815046920140c0c001d420944040c60714403000f41003041028402d03c0100600c149030300e8865034440105051006502044c000a46000140c0b40020700704068000050301640c0c02c141d080301914864582481d2a03881101c60310a400e0900c00c0d00c40c05880c1c4030030302c0c88140e0350507114009a0540343d140c1c2e030020200288024204040340c5010020080c1c140000e20150200100c108907140c103190505081d202c001148a100314a0001c3c2040462016541046613071155481959152524188502e45000c1c1030444031041d8800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 134205161 1250 134203911 134203913
    0x405060a0e030106140607030f0e1309140c1302030a0e1204090b01021f0c0e1009060201050f010b07080304050102091801061701030503030112081207020303040218070203041406090d 80
    0x4910000c0101030228000e02180d0307120301030421524000380075150841b10504c49840000d0090201502c0721490b8a045081e040d00030303000480310340c0308565541900c0c1c0d4824070a412b22006011054005a002d8020f0140c0400c4102244802c0d4200003011041a070100105174006a503801207113200c200e003011200014070300c0e01107c800f03611601c103500e20300d071500e80d00305640e50000c54000065000070744032880d10000700170302d00089c2100070786803070401c0807903441d41d07041daa03031000c030352074225903503030320480c0030707400c00c1350181c01c403103003c1c0c50342d607081804d040104901040c41c4221005039600039074103600d940341c0d840c0050181c000c03100e00ca80d1014030741c1c1c104058004031881941c101e41140d9a0b035441d417048071501242084d402c3c000900380360010070051000d4000c12540f62080f51103011550f240288400160114140079103a010058100100f03000c194030300144405002c06000604099504060401039078034483c0d442100d8a0210421041c4155601c502c140c070300150300501610280101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 134206411 1250 134205161 134205167
    0xb03130c0302130b2718010b090c03010602010606020102091003020f04090501080606010f18031205040509010807060e0316060c03110f0109030212180d14030d020a120b06070f02060405060a 83
    0x502c50f5518000d1101401d01415004d0b111704006079000c528400c015aa200c400e032140d820b8850040b40b031005d42d00c1da050400c00b40c0f40c01460620440c1031607000c5442e175041150003400d56603d0750005046a00501002105a94014444441c081107080059888146250081841c05948d0000503840e1400c400080c0071400481c5280c880c04099030b66248a281c1c9140039a001a00381d4038100341d8229041c42880081c818207100c4042c40010709085050541e15000100925000d03089090f0581000d08104444c40e041070040c103610200310040e00a100401e540148100e030300b4440c1008012001e1a46014140644150340d51a08490180c80d083d410044840b03018021604080f80180300d1540d84a28081000d420340d07116805040303c000101e40351104004400b0801c007020394542242e6000c10551201c1000104906031401c44050303140c011b0a00d0203010388040e16610000181040c0c0c6041c555624441110241c0c1d6001e43c4d0f002048046002051250103150042d64121300009005120150 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 134207661 1250 134206411 134206421
    0x17060d0c120501092906040902040209060d0204080d050c0604060506040906020d09020306060f030c0f0315100305100204240306030228170c010f030902100e01180b03130c030213 78
    0x1001d0950034503842000401899a4505c005085140c41641408107810380340903000150300038002007000d82001c80300ca0008040b81d1058580540d090390000f802c10440c0f10a011000c8807544900b00390b81401c5076400700945a003c010310083c401e660300e0000a440f03642d50b80c0030104c11600003500b15140c4000ca0002002090f4200b8141d03c207110324400142d03d0711f8026116200442e02502910815940310140501da40e21070315400e5140c0030744c500341200c440f818283d461185403116500314020303140d820214146007107150782c2d81c0b600780108800c0c0920b25040c40f400008080c140b603890108008044110001c1c2496040203600010480864036a400c22020110400818101d5182c21035618210b4400c105400d00342070700381d44c02a4065246070b41c003c00c0d1f10b980c40d680c02d041c00302e8403007180e40c0000d07502010a49103902103000500c60070810b503848648400681000f5004400940c1483c0d01c0c146a400700030420103404488804501c2040030643c01c078001158040c2c100b8203004042040a40030301 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 134208911 1250 134207661 134207663
    0x106140d021215190e010b061c0209090906040c060804050a021005070605070806030f1b01030506130624080907050909011103010902091216030305030a090f0b0f0717060d0c12050109 80
    0x18140781032400081030601c20201c16200062103945003009c001c00d10710110a031a10389118a5a0070701000b010354032801c0d4014410000c40010381403034a4079141c00c1003501640d4100c10100034034481080002580003a02c0c58445d90129802c0011001c2c01608480c64403c0030402085039040c0803c1c80b550b04d401480050140d9011010344910860440d1a80d6580c551440b41040340c84508110741032950180d4402ca82045018010102d01e0700c090b0185001e55210354001408807032082682c841d140198504007560031074031301d03045089042c1030480681d20322060061620480c05407000c84c0307a14000b5401084541c0124480344c4c0c0700c1da07440c44400020341003150424050b00351041c101f8040d2402181424084603c81d6440715001d0540d10308680c03540004028032059030313442d05501e01082000d014a42568414003000b030035898404e10312156002d001d0541c0d41400a64080c885151003991700b0030b07a01c600d043c1d903c080050301030304022451044a900c4a8145600c1a240c0801d108064000308001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 134210161 1250 134208911 134208961
    0x91b052d0d1a010e0604090b060403021008010504061403032b0e15011d310803060f0a050d020411071b061724030f0102031003050106140d021215 64
    0xe610038801558030380104c8980c00d511141c100814048000960711200c0404c401404090416440358081001c00380e01000070f5001c51544001000b20303140502402c8080c020006032070b9445075a48001c40d58a01071081000318600e0003000c6820498140c48066542a0100d40d05214454440c0181600c41c104500c2038440321014038000308400c10403605450046004051511a07580e41c800680391071102000d844046891340c0d68003004861a0000b00c0200e40e016400c0070b5600c0c103043c070401c000300d00b02509590003030b11121800c001a58600c5510046940c046d24003040441c80c071180880c2511801000a10b0031911441c001e6004060340f01c903078280c0c0e810380c0711a2017520100c00c9000d8a494101c420092030115520301c100341c00417400312010700c0e250240c2210540348144c41d0540c2a6002112000f88480b2a140100b0503c0824050b20008214808103407041030070b00c1c0d0114420100d52103029004901040c0c4007a0401b40070056101020324859240c2c1290400c1026048042e240089840392 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 134211411 1250 134210161 134210201
    0xb06160201090b1207110c090711010c0e0a050f0a090203130506070509240c10020a12061214030408030703030911040b010c1403090d05010204091b052d0d 68
    0xc1c02c1c00c0001c031080c0144c0c407803d0303030a16503680d813049501c1d0601c00c0303042a060240d2081c0c064140c41c1c100d44280681c19035101c3d9842201060b90113400c440d4101107420401007004044480707034942803880e0040d80c0003560000409011400464840d284607442070781118030002c10401411001201081001d11071000d95069884062040343c0c0c40c001c0a80c0c0c071340c1c8101d10441c0c500b060901d51541c0c1c0368240d01e014815040072500d0080740e00745260181603005468001a01d00c131280d9011080316010720062508004050405410240d07465030340c140203003507903154091180b00c608100299002010102c013101da031420380346401000b6020726641107500c20f46040f12000759103000d019070814081c06940d40304004c0410744500b40d1035810000c034076185020030804460300b40c44005109907424014000565110719000c1a007040f600c0703030102066101c806800d5001386a40c010112070f81d08400a0000400c403550b501c481c4010b20070f10450760850400040c030b0b02c81e00d9070f1030303008903488541c21284400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 134212661 1250 134211411 134211419
    0x30201060b03040506071209050d090f09200306010917010c122304061503030e0a090608030f0a03060b160605060121051305030f030a061505090909010b0616020109 72
    0x8002d000a41d8000c003d600071780005140a0322654446589000c00304001c0341259960302c903282028009211540000c8003580180803880004841200a0800d1001080050070440491604100c50b0225044d030b0348002010840780d80c860b540010140c00e402c11364601c5540076a45140c000e0003138243d40008034800804a18489000d072080300006c040300d9100101102140e091480d0905008008640c280e9450020740102c48507900480c001d1803003034072590142121503041100b007000551040054a05281092140c1d09012060b00e151208510243d03844644c01001030b80070b80100c1e0007941c09004089500480c08030190041980c642c050141000382e07440304001155450529441e0081d142e071501102030750b00940340c1c00300b54403207203c402c8be4007901031559440381180e002111034031000b500801441a400214071990300101030342904001f40064441c8003070401c0c0503d0075561b101c0d042e424005001c1000039041162503403801000310713580300391340d0019000b0030200850a0780010301c82c00000c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 134213911 1250 134212661 134212679
    0x20c060f0a090206070803040c0807080307030e030708120f040e07120c0903120c050106090c0c0201020607020a02010e043c0c020102070804140607060c0503041a060a18061e0303020106 81
    0x2450b01500904210702d00841c130b4442865943c0702070700c1140c0b06103200500180445003404850041c1c065100616a141c040d41001440d00641000441c40b03900286810003842c0c01c001221203000030100307039032034981d03420b610001c04c54003451b0b1215001c100080200b03c1450340c0400303042c0c18120555000c11072042c02081c11609a1180c2c000104060404000d05801500400200070024170440000c80c1e4035464589440a44440c4402c6030040340805401004668040c048964001e505100a1160545540009110320707480c031880340c092f40da00c44c01620069007207480e0280903506c035000c2918102130f80e070400c40441114041254524600070005c83c2062040c001c50b00c125411606a030304140c00c100b4104061441c141d00300b03a01101c20020b280001ea014003501d019180796407203907030700c070701c0c140c10080101c40c00e5414107000c0f240a1420805603503124900702d019240d24054005407040300d201028014800d030b4110302c1000019451407030001a484e0844426244282d0092241ca41d81c3d0a1078 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 134215161 1250 134213911 134213921
    0x40605010f1d0a051b040f0302010306050315130201050d090309090507020106260102090a17060a060501050d0e070f030c170d14070201030b0a0905040b150a031e06020c060f0a 77
    0x42c0c1907002c280d10110341c02075030369000a0b4004e440125601c1c00400300b48014601944998020400514039080030010756030117100f07403002400190301030061303c00c0180700d52903080001400c05514204103e00c0c8015a44101c3c15120880f06a0310204804801030401620109881c807445440c02c0c2005c00180c407a6206000310790454821416141003421120400d811508030300020340300c10341d2f007444040781a5844040c038600400404403100080804904107a00706100200700500d00ca0809104210303990b400001c44a141412640c0003650324101a943d60424a696002111400e010200481800262042c441c121440104414490001c203035600b41c4a03500328803c9004145520940c0c0071180152000f40241d6105140c0028204a00d60000f61803000c1380d005030b02c1c000c0d520b500b00000c0100e0034a04540185440300034400c4a000140000d03d210315600000709170035101604441c107004070f410403140003603100e8070664944400002072030307440004960214400c2c81150100781c0407645417144e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 134216411 1250 134215161 134215199
    0x60906070e0d020f062b060902040f05060d06050312090301050109050105222a0201050601020619020a02010905061312090303020703170c0a0803061908071517040605010f 75
    0x4210014051a000c010621920041103504400104200c44502c058400d0303c0603861b4190360252a60400515440216072290b0001c0d4081441000280803401400042001300c41c0120b82e1607039a50040c160f1080a4900755001c81e8051143e640081100c2c68130f100a4800d1145c2030703000f00102d13aa01c1c011041501c90038481d058228001d940d6901c1c0380c50002c041d5202041c800c4501203019041c0d0f11001c0000720f803c007030010500d01100040000c50750f082c064140c12801c02d00c020105800c217080342d040c4220000204001a6500050342d00016000b0f4002c40d503456000b0003035420624115600000035111880c0071108003660a0071440d0007405500c400e411f507034042e0f004109060840ea9030036156802d50011045118042c03110403c4400100700800382c42c0c0c031070403a05071242026402e110042221071421030f0b141451100c01e100c072103c002035032002ca85083c201c409007510b00c000141e807410035091542c601c40c0740702001c11090003801d0f0050f9048440442030681c1041d568032112107130299040c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 134217661 1250 134216411 134216419
    0x415020a0209010308221410020a1a060a0602030a0e010e03011103040f0b0c0a050d0b0d05030d0e07050f010215071404030b06090601030c050a03050403090b0429090a03030c080714060906070e 84
    0xd407c03682480d881c4e42da4084840d004560004075917880e56130002c0801c1072035041c441a40d10410003d07050400700c45004105e03500003141040d072040307005091048102c0c012410840441458038244d9800d400000381120740e00070f00c60340c9080608040c1000310300c0d000c00341e580f0860000800c084038100000c60b1000d0340b490760303001d0030211141d211501418200c6002503011820104c020007045090004107a800f0801c0c0d400906d00042c40c00d001d0400506038030582c42620080c01000d000d03600414003800f0350318101805010ba03625a0760030380344504507000d0070790020004030b03010080102a490b058040d41003201c01da04140d40d29001141a0b4a160b10030a00141052004955640c0240c00142d081031113818800c8501c1d489035008003a580043d442400c070040d1450b1280c2000c03048112030500b0b100c8401002e45000c1c806c102281444580703103c0102006419079000e000e0010820981b1602d0358015801c0301c01048440c0c0b0290365010645800800740100400314040c0c0740207010325810008007034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 134218911 1250 134217661 134217689
    0x220807060203090a090b131b08060901050d262706160609020d0203010c03200a0206011703130905010503190b06060901031506020f0601060c080415020a020901030822 73
    0x10900c090320900384410b80000180c5062031f2000f0144c020f0403441e8441007144682054801c0c4014070304440540003078082c8400b54010300c0140c840075140180c060f00280010042039a9040c100c403101500341091445031004034075040c001c03000c00c0c00c841d00d424910040f03440d0107401a081002d54411585001440e070308005080c000030360990020610240014404120f030800c90300800e09441400b100c0b0070000e039032802c044c0c41d0003102424840e01d620100030441c0c100340480300042c0d0303501e0044c011024184c80700426280900420000c03140d40400c02d00d92140716641d240c0c4114050324003801254880c1c0510400658a04800031022480c160444040112501c4590034400651300c134240c000d04054440d200c2c02c40e4022501001001008150300501200c59250080750074903006070851020000c4030412103005c159254150b6080c0c0311030104002d07a03100040e00076482c0284884000750020f4107540008140044800a84401400303001d029180b4044003503007460310391140c0914a010b007444 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 134220161 1250 134218911 134218919
    0x90601060c03180e011e03050a0204050912120f07180303030506010203040905130b0603120307030b060c0d02010f0609020c100207020d0b0a021e0a0c0b0601020102220807060203090a 80
    0x2000c48400789070080c10000c0c11107000c4043e1442d01c0034113401c10056001944010005040c00d42c0300d006000d00400c2c2115403944c15a61803e0300c602c01020b000e40304940b58404158826414007010403034070900e0b2195595130003421a1007504401c102c800e552244d48801c00503401d9402754a80048660414100702007183c210f64040c1e000381006080e480c11444248400b0544508510402e80a00034002e40d8800104491038400f07d024402400340e0f00a82001e0f50700070100041c1411b03250000f00f141030208003484000d010450501a61001c0d101d54820380d08038840079501984908500c110982003480201d84440580d01030f0b00c02c0001d40309441e40418040f4240e01401c1d07001c2d04400384002c1c40f0042d07a01c0c80c2e46480720242c009a80540c061130780020107442d59000405207000c0240c00300c00c81400d0107680d4401515401003440c02070701c0b0420000008005038400c0d41240c0d0020711081304007111500c016005140b9825a000e5071096101da07882c0810031074000001c0d00c2e041c1000410f406000c0e428 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 134221411 1250 134220161 134220167
    0xe3306040507080403110106050a060c0b07050418021e03070509010f020c010c031b05150703050615040302040504141015080304031112010905030f030402040f0603021c08160506010501090b0309060106 88
    0x2558011b054076551303a1700d002c52965128183d035001810350b666420f030140c0302802d02107009070740540410140103042004010030701da8403007500410b0841140050325001e00c88241c048001c1c02110303007078028200104100201e40c1101c0034280405003079840d2100d241064030103036660f40071518050f0200f003d0302c0d1418002031141110301e40a03070110b414034880c0c002e40e070394140c6400292021174240d010000100142103600d031191590000c021282c03451800c01d030001c8907600f44101d00003e802035440784000f80034001c08600d18000080540700325468880414010001000c818400f000014803842c4000f8041e14000190760070781c0d402004e160303100070009080003561001041444250354032800d20001003002400038082d204413464440e0342c0d0b4a8540b0400084420b10502040f20620b03116042c000340c1c44002140b07801c03801c8809140341a6800d8100080d0301c3c000c2d040d130b404114100410001c2000b40100ba1141280e400307807610f041190700c4000324600c501007110401500d50241004000c002e02c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 134222661 1250 134221411 134221427
    0x914040207030e03120a020609061e04020303070b090309010306080a0c0603091b03050d0e030a03140f0408160305151519030b0a0b0f01090609090e3306040507080403 73
    0x11090616400783c4010102103400d25201e00200070074408007040348000f040c1c05115141e4040c007a200508064640380803a00d40111003818004601c03140440058115141042101c00d049c1d0402007800b19881d000905030340ea640b0245241c2d000074100323200064803070400601980b85c5907001100101c418200b50044009002e14001135034000a0030100240080c21124840082c50080b80036214640309103002400384404c56200d0740c0241e008800407004640e200312040301c62094422510f036038034804a0190514021038000034a81e01070b0721410301344110001504401c4a21074020340f800c5401005500e2800f1408940241d442e0196a42d0118186410103121525031180510a0201500c075100c01c2c460003022101d200d1419231f030355030744a641d10700f000400310452001d19000c050395092140040c44125244031740d40400d601c5002a00140000388450141c00c10048111352205510020041c030304007a8403450760005000c640403c0d61803d06008451040d5040d46400b00c013910355640c2154505 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 134223911 1250 134222661 134222663
    0x70801091110030605060313120f02060414030d23010506040302030d0c08070f03020109050f0105010812030411040207030c0c050f18060316060e040608011a1203160606090c0914040207 81
    0x1540c4c1d10408142542c1d40405940200000745050312142058540120100c1000d118030b02407000000005481d66400a02c0c81e5004d07034403804c90044141c0a8441625600a500e000556142040301042c2020700c9642c11440c10309151611151a9a03640240000c0d48030b1400040c1d01341d002080008045402a8584858180b10b02e000c545031217615291040481c105540840050351510200380130720004008031148050184020001940750840c040c0d901c00b15042130305d0030010080001024090006c0301c40c5901040904103560b100d0441c42d0041035060040000c50740941c60303101c00300f1036050295001c04030080c0a407085000c00500b9485081c0008001e04c505d03803600c80c1d5000d000300414402d69031401010070303440d28500300d9407141c10003041c0d42d41034200c40140c1e890507400143c1540e0700b81e980080c074202641da204c03100c4045041941544500700582170f08640341949903081000a900c90000c5491009041010401108085816075424811320b409083d440d590003240d45820360041c6101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 134225161 1250 134223911 134223917
    0x40303051606090609030f08090c1012020f031902040b120a180303020a030e0102070203060f13080f07020a09050f0420120d0306080d02060712060b160203070801091110 74
    0x70741400d903a12000c0e5502c501c801c8507a152901c1c0380740201600300d0010845507045003810812071801c0b0b01d50a544106000f07034540320340161152220380e07a0154003211520180404155901e40c210000826168410340d40d4a07043e10b101c80e400b070765100c4030b4400c3c2d40c19141654103082c50001400d440e400801000f0300014100d42e0390300d08100c0c860720400d1040030120300c241c40158491544d44805403c4030392413651501c2990040220380010380c0c01103034582e0310001c06446d254580d295960310500f154030441f4010844e82d000541d52410405240140c40c2c214400c07035403018203a403144801001d83e101580e00c1c0ca621000031b004100000c1900a55010b62207000e030402000c0d030607000c0001c2c0511200307140103070960004d45041001035030600074240540032140040c042000c1241000f90b450070b009002c40c0070050100c00a100054040e08850001c105c1050300640b0380786110000d008500c4843c10072482481740f030a00103054601070144d5900795400820426980301030400b480b1840f03441050315010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 134226411 1250 134225161 134225197
    0x15040507090213050301021603080c041a0c010b0a0807150f08150f0a03060207020a08060106080106050d09060e060a0c0f0207090b0d0c18050f15011b141b0d020604030305 75
    0x2090314244081d140d42e881000700c423802c1440710305000d00800c81c06004060420000c000a00c07108814211404075280d95003071443d50f80300000706d45030040081c0f041080c0d000b0800d0100188441e0000380400c00d03220f4002c0a41c0350f0007241a000e40d040e80b20494140082009a03000940c80710481501c1a01c2000142c2801101c0352050002440780120b50002c40e65140c2c0450b241095080900e88000580000340007440b06504102c8083c10400052044408214001a1100754003040390846018540d01007814841e81000100c050f851715822540030020620b0030341c1409027644075859a4040e03000d02e4000e000d0850401c41030001819800da81c160f0014400c11141000a0054080600030701c00110500f080c0b10408031820140c410280c85134854422000c14400d0700a5004482d03100c0440900f88001c8003124100100c203103003800d40700601904c10f511000380c4c0f45000402e000308503050403000c4501100f041d0007089042c80140d04007039000101840f051001030b010b44020403805000705201e5203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 134227661 1250 134226411 134226419
    0x905040c030c0f0e0105060901020c090c090d060f0f06060e060c010608100203071205010612090f050a03050a0905030f0c090709080d031508031c0b010306052115040507090213 77
    0x800e1640b2684401e9511046034020070a10380c250280c503001d010704690252500b0403010000756542101c58070244034082080108101c41100000c0315500580500340210034a500d080c41c000600b800b4038602500c0d070902180d401171485900c1130505031401034031200d45140401d402e00c10705d50080b103014500c0703658901c0081035041042096030718412040d071025a803480c1c29a00140540080319002d070115050400500000742c001d05a502e100d40805000141c10305281003da20740762031048090404c1c01841e5007036050543c06401050030b621aa00c1e00c840056844080c566581021711040a0542100c401041c640c5400240360740c1240e41883e00441c500d8842c40d03d1030401d06504003000129a0b0380801085800c203010038080141590310155040400c6140741c0601c602540d102c0021a95458000b030000703a0095100001801000d0000c1802403803000c510120390000c0c0e1082c81c440d200d546602c81c440182ca0400502c40e580c040060008607161109903406500b0500740920f52003082c2102103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 134228911 1250 134227661 134227673
    0x303110d0504050c0f0604080706050307030914011401080f151e070804020406060e01080a0b040f3902030a1d060307020a0b09060705040308160629010305040308010905040c03 77
    0x181c0070b02d005501501840702100100034484400324040f90041000313100c200800745002c2425012aa03d9041090f5250f850b804103c0c01043e11400040541c4007034a075038a042e0340154031202c0c0c10031503400d0007002c45e40c07108056646c07411b213201485100d600a424244401c110005020f03080920402c10f010311414028121030011000c07600030001907542d0302000154642030160800070859820000002c02c580d80c0000d01c864402050406010f031a001881010f4486038041d4108101c596410000c3c1502d1203920134a03280820144100750340003441e50341d50322000d01c039040c407400d00c2038000350f292041082c41600d840d103a91114a107a142c210b0304141c070f0b68490354002c6100b51501e03400b8290740c400614180c42d00140240504046038014420031500c40c0c0c01c481110281c1740c00400482c1c46040111000f20803d0304000010281400c11003100449400d00b41c0d0240e103102c031002c29801c880240e00044007150011903010340051403030801044041d01c0d07070703000070341160044101900d0785841c1d490350 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 134230161 1250 134228911 134228921
    0xc060b0909060717100618150c05010f05010605070b0405031201090207021c03080613020d06060203090307090209060d020702031c110c01050708040e0619060c0308061206040303110d 80
    0x2940b50072601c204007005501440114000c1c01100a1061504200c0345040084025000700003d0150a154400d12050329070811001001d0409007800c0d0180085001003812092101c122413543c01c080861900d101107010fa64140c980903a40c00342080180d4035045e0f4541c00141085ea81400708004080541c940d543e1064040c040e1080e0141e07070342410384140000f5030f10086622244419003504440060b600c1804990040340841c0d51859070361003807505000034411852001405807030118001005900800a01162101101a0f4820542d50031800e000d03071185240d403941c002c008100b040701d40d00895024051090015003207a4860100c180c1010058040c140d200f000b1030f40c1e0b5070580003240c004010070386603001d0a1800d2401c02802c1d90300c3e03050307d010754001e14494184144c0001ca85444006001ca0072003501c00d5182c116035500c030700c0a4000085c0380001e07800207403228000703003e41c141514103201c007140b070b04001d148541c0c0385d403000ca000381042c001c0c1c414210004c00a00c44076014501030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 134231411 1250 134230161 134230171
    0x5070501020f04060908060f0a0203070201061e0305060f0106020d030c05040b12040209090a020607060b120709020a09060804030f03090501020412061509140103030f05040b030106030e0f010e0307030c060b09 91
    0xc1a96035003800c2020340425100c4c1e106d501c0e590311a10411030768038000580703642c006910101c003684949070a6416400360001e03801c60320440c600d082d2080c00a00c030050884040f64052020f552140d281c240100000b50000d010f8003015034482400c80310007d10903441141c158801d8907000c0c1c05c01c2e407121208060744d48101a4020003040e00e0050200707501d0b103803090540103000c2d40020072040c26503a001c690f0b0303070207522405403555a0b2400c419035180c0337902079001d0f04807450b0300030361312026240c0490b14002d4216511047c0080e0069502285040c081c5102c60b0145405807161000d4505801084014008110048840e55020320001039128494644e8030342c681e100d10008100c1c84e20400c500e402c00d5142c0da0124080e039080019401c1e04520030300e1200e054070380516120807a054141815645480355070b0000851007400400003540b40e0b0708d0390001850001b40800e64419141001507a400d035a00c1c0400309070079400402042c00080c2c0600402d0303070f000b4465070004c5003a42001c40000da01e9501120 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 134232661 1250 134231411 134231437
    0xa0903140304170604021005090a03150f020307050a02010b01140d0e0106090e0a020118030f080304031b0f0506060d021005090a030f0332030402010807120c02010e070e040b0c0a0507050102 83
    0x106000441c079103680d0001010b91f9030701d002810444850700055a802d83c130b11000d811410030740c1d050b80c159986a0003000902c210701c0003e5540f41840040146650320880390540103511341202403044d91312400420a0ba504d080f81d101e41810841c2d240540141414002d0107640d640e60100001c0c5c280742805a00f60104003080035001d10980c500001d0000c05a5070b5501c0441c0c11005003d00008412420b000d100c140c004a00580700e603603074a01900c00d001498003460251040e00540002c2122008440c0050752042054030751a840d0781c4107104e400c4541d01e000a50010001441d40c20180c8500d0252070f40010007007081780c61640d00e8450084028100205074001145205a44d810000c00800d0040542031580300031641e1202440e12006800042c100a0400000201086d68240308042d5002d00e1081c041040080010080303001c0d00030241c12881c10b01500404000040000c03034024010b104a03004a11500d041e610100640540d60010500c1000d0020600150020075400d101515000c41545 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 134233911 1250 134232661 134232673
    0x10605100f1101020702032802031606121e3305040606030b100e04140f09010b030703261c0911010c020310050c130312020105010b04050607020d1103030d0204051002030a090314030417 81
    0x203203008142d0f01c0e184074071221003030400b503500000c1c51030751ba60407100503422540081c039100a41166000e01d00c040451100300c140780403240303c2c501c443d494040100d034310440c1c08104a980e031f0113041e03041e03403243e41070300b81e01003203400070707104190300030700c1384242c03e0100600000301c441c60380903d0207015400f07562030b1010701420b0007003000708503091003400004001100248040752450340c51880180e44102c0007004205141d107a00900ca0f180c00903600710041e40d0300c1c0b92541196409201005110461041e10003106900c3c22903615409a290b640c00700750054003400c1032050340f0a41c10040e003005003e160103e031003000740c0f0038607140480907400038503c076040c480919916210300030300359501070304543c95488080204110560700c640441d040c141d8141e81c2c0c000940074508060100b0805100b1f919014000050381c2001e03000c055004100741c4500300c942502ca584205001ca03500c1c050460341c0703004078144090900108a0400c03074240303842c0c5080b040344d00d0140c45181d4003c00d00140185e00c08540c3c000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 134235161 1250 134233911 134233919
    0x30209071403010b03011d220510020c0303041104060506031902040f0b07150605010e1203040b19030501050f01080708061207141e0303030403110a080a080712050403051b010605100f11010207020328020316 90
    0x300e4443071320346003006c80d4148001c034240760025001d440080c1c040d5140ea184001100c04a1005070141c50040c0b1440034801059070380c1e903650071400c1d44004402c842d103001003140da4100140c1e6109100a0b140180e4499607100c0002050040c0c01030b0030581000d60f848248000600a00c5210040a80c401c1d41c030f540020000b404000617050f51010b810013881503042d01008040c0e030f64401107181d4406418035040066460391004200b01464a040a4441d1b0042d080c02040501515420404460b01030b520162444544068010071402120030281d140d00100003140c082071041c8007c000c2000200f0645500e803a440e950041e5070750002e008c0c1c0b808143c105040002207a0482c080c0342d17a901580c1c0d000d0140d46442c2d0f5000380180b1034401c4100070013191441d001c640311025071041000e07100c0503089041420704040f000e004c00030b07aa80714200041d8600e0000703005942c107000b0344854650140041200782c00280c50041140d10420400c25050366501600000da602001100c0c0409007070b44101d0800c0e420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 134236411 1250 134235161 134235173
    0x70303090804090e15070e0d030c0f060e0d05071101050f130306050f0604020a020d0311070501020309151003030e0405190903080912070c030209071403010b03011d220510020c030304 80
    0x48170034070100d10315030104002045801800d0030b61918411a9042079880c1985010f441e0300c111003c02410f281000311072002008a960310601c00540300208480c014142210101d40710310a212004110404a82c002485da50048000d404003e80c0001005e0603c40390040f4804491010340c820759126845006011801158210280e04280c041e20250f161081c5888065070740c0302c066180f6005c150ba1554000341d0b843c0b41c001515881584070000303541c0c908054039090344d01c0300c03421a41d08003505c6200c04110714403040000c20048917032507140c6800c40c04244041000070700004044032946041c0c68010420340e25030340715040341c0c2803181d26800490304120190750701d080759842141900b5001001440c000c00e02c17102c10142240d604903010000c0741d035024012607525445074640c2d00c40c04004000441c00d5100710000d94141c40d0b6901c000e00c16140e40708407600314004199140140c1203090085259a0591130b400c05111b07501907022520200b000312503100403030b40071903100c402d84d8001000740810010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 134237661 1250 134236411 134236423
    0x1204050405060402070803180c130b03070f0f0605180a1502060c0903030412150903090303020f0a1208061f0e0f060301030309230d0305090112061505070303090804090e 74
    0xd8140d07030131402c0000711750324419580b002400440d199441c400740d108400301d04200c0300108040c05402d0700003221080c0d8100c8090042124001c0c40303405551408034860f132901c00c1c0c0604031580007403040c200c00d10f0315000f65060b6110381c500b02130071844901c62410503140c0d44600780082c0b02031070041c8203050482000a040103c00381c0b41c0f800b44101044201c0443e500003041e50203446400300c1003001e40d9a0b51500103020450009070202507414070000006040c0c02c1a004401c0740d000c0d0702030f10b0450245100380c0342c4070001c01c1d50042c650082104a0107042d4070800c08154080406400d201c0c076501e481c01c800403183d080c00042d00006108030380c0700100d0708080c0006012184240d07100c9040d0350660f60b019101000d02d00449540c40000314800500e40c504020b40b040584010b00021070b40b400c82e05008107641d120b8a40140404c1e10310b150f54a50980390302c58402240c0300c2602008042a0b90507040741e890303003e01e105808141d140c2c80c11501042601000303000800c903241001500c51400350551341440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 134238911 1250 134237661 134237671
    0xc031a04090f1b032306070903031e030603020a09020912030909010e0c0904050412030b15040902160609080a110606030a020f030f0f030d06051804240216060f060f15050c1204050405 80
    0x20080d040102700003900301c01a55206040001949a6075645480403001807416900180d80220740b014000340d0018198002d054450003910b12007480d2401c0c0120300c1d900c0c03050740a5030f5082001d030401005515650030036070703810203110306180746400c1c01400001e05a840543c0e080c0c42e007900484c1c040000640600c1417510510f42510801c0c0b01402d00c80d01c0f40b2280c00307180b00303a40c07035150001060746600c04180790500c40c0b254030000422501403c0e003020341e041d800c003041c0074000c1401c05224045085000540350f200340002001003c1c08a4a0780c20b201c090813200040c19018410f1400b0b85580340028411059020300c403800958588051842050588020f648410700411491001c5880028682405980075800c88980040480340c83e41544e16035080300510516144017040000008401d00c09484919000350810b101c90001040b2030000ca072124440c10b82c000486c0101040300004a101c006040801410300500700f0320f846180e2824441400c1e885202940002000d1000b0b10340b03481015040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 134240161 1250 134238911 134238917
    0x13050114030a0c1502010608031206040506221d0f0c13020a050a08060a0314160b091e0d0b010b0c0714010c080705010e010c031a04090f1b03230607 65
    0x2e540e450f1104501103160f4095050207181d01602640058001d4101030010060201120342d45d0301404104c3e4040c8405440c481e110300d007800c01080302c07442d0103a003103040c031001075a044e111440360045410050030000c622040e400d036a0380200048160900501090401c54400303400940b5140d804c202030b011000c8640e040031403040c800c0c41700c0b2541c402c09807081c141e018101050151074200001b180034803c1d6200915940c0d260074290182c0c030010400808600404950f522100c3d10740c14044001e00a820904c0d4000180d0f2403228120003010840d00150031010308160044000742c0c568094104e800d800200c9100c4000910f0b054140041100400030006600789480784044480020411502203e024000603400f184901c1404004c2d4000d04410814800030000e134080c041024003c3c1c810f429004084803e2a000c40c4e280742498003c03469140d074040d04c913038940d911035a13800d0410190f03007600301e840c1c07480c2c1c0da004000910504600c012600e000301100c00c407000c2c010080f500c1c0400080c044820 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 134241411 1250 134240161 134240173
    0x100501151101020a09030b0717040c170c0906150909010f06020607020f1e1608010501150305040c170307080a0e0909010e0703081c050a060303030510030b0c0307030b1305011403 78
    0x2c0c00c5d40c030241076403d40358400700414840d00c81c858200c1e41c90701e040d503c04007070002c03280a00c170412550b81e030301404552020034120403500030800715076201d0422116494200180788002100307071030b08040d010718180c00f5100751420f005041c000b28000c200240c0200c1210000c5540c01d120840d010030440354401102e20040490040c0324103d00d484401d81000140b890034090020705126a080c801241d074154402a000340c9560f54600c0140607280c01c0c49201010384026501589d440e2207409141c0c071031600030a078403059a20b012036090341c4140c04080c40e201070101740b000c1d0000030301200041031500340c41c4c0d0b1044030b1910100c1c100f00f6400c0005d044010302d0384c9014041d0005800c081001d02c01c60b5081102c00e0340b41c0700325103040010740149800404d521460071080000e0150207034000f1003943c0c001c2d90100311a9651031280783d1072070400d00020b070a06644200040a0700c0d90000299800000341ca0040340000410740451a4050705290107801182c955006200b0301928052105036900c2c120000d1170f03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 134242661 1250 134241411 134241427
    0xf0b040b060c1203060d050109110a1712070512030403030504020f040203090c040c0315060c060c0e03060112060b0901031515140f040e0a0f030905010923010210050115110102 77
    0x250b00c203018070f292030305410003100240b000d5413110500030310f894100e0300034413000c22549032080b4054068900c441c416814590003041c0382c265080403c0c2d00528801c0102a0040c1c000b4034101d140e000020b0840e10b51060100302a1b0303000c030507400f071401640f1a07200413544d400c00313204009010070784a1641c0e002d18814400c020080000040086441d1410f031000a4000e881010450240c42c0459030140c0041101c4c0c00010020341c004c143d1704009016020803c24803100d0801181ca81d01c00780139030781e49580301900500080c2144240916002d1041000140e03010392440410340c6804240d02c156004811485001c1c1401214004d03200300c1c000c08070303507880c1701410141400c0a41e010081003500600b02c80724502da09883e40c0e40300191002c1030f101140c8841000d031a01841b0070415032000c8000034441d80d400105035004048400507504107640910100b060701009010242d01e01072518114403500c500300c0e0792464640700b0700f40030b0130b007101d540c0f00c1c860002280034100203081c02c40c4140503072040007d80 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 134243911 1250 134242661 134242663
    0xc0409020c1c18140f120703020906030105010e0610020109061104080c0312030114220b18100509042102161d0c09010215091507020c0d1101050d0f0b040b060c 70
    0x100a84640a005164000c2c1150120703064400c4440d400303070814000796400c981d40710000780c000c04589c421180030145980b20420316007600c6c028824200209440001b007102e601d403100144d8114900c03840009028001c1c2c2d21540c054411140881501340c0d80050b0900c4079410502000c02040c0f0150300030071100240d6810161240b105226651120800c528800e021365a1030b03070404104203411038004104050300b111a0010034291010358440d526149003454101591000c1d0b62017090300e8040b1141c541d00e004140704000b0710050049400d04220317020251360900001b2120200c05156000300a40024851003ea82d6046600205880c0c41c2100290003c40403106103e0b0748080c80c4084242c44049181c010303440c19042a034000e004202105c104840c0c00d00001d4100729929401718008960f85442900f42d07110803d00303441d6074000035080d043c0705c08240c10201e04110801d040c50007502d000c0c2604035044c1103504108114407110b440b490744043c585064010010025003c450480c58440400805 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 134245161 1250 134243911 134243957
    0x10c0c140f011e0e0303070503030901061e03151e05090a02010305071404091d12210105030a030309020a15020a1101030e030a030510050604090b0103060b0c0d080c0409020c1c 77
    0x3e070400c4010480b0504c40d8805100b510039181d403000c103da849003020070740140a00301c81d0050382d483d22050315540400d800752142090032a034000c2d4803101c0d29685901c014020b805e0351000114460380d000c03540c0691a0241c0f10b00ca1180d100030014140740c0b000d920004040d07440c0500b0103810030508403603c0780c500107000c049404540c0c900c2000120140404050075200c143d0149003c458002d1741c0080d9014501d40000304007030004540b41c0e5800d42240c000c00d455103030b820b00903140c26a0050701010000307406503102c00074042c0020980f40300b0b41d6440d1111900740040450300c400507000004c20304200011044655070505003420305000503600100d04558030b00400c5400010141c480d008140c0704c00d00c024050004d40809050f4950300c5880f844c984c1c015100e030200142c00a450004009000980702040c0d80c64100c00102400000c000008114ac4044d0050009044c0e45020840000c1c1d4100c240b0040c042c401d25000a000c0005010010440600343d0655000c1800f440c860030005090030050380f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 134246411 1250 134245161 134245217
    0x506151804050703050d050c010f020f0301140f03010e03210402180a0b0604030305210c030a090804050904050706020d02030406050d0e100c1d0a030f02010806010c0c140f01 76
    0x344501941d40c504015142c00540d500c0a8242e028207120403082d40e600400420740004980300030300415031241c4221040303202e0481c0101d188030f414001803004010848250003030034001440c2c00003600081000078212890035001c1c03580d03075000081c2c2030755112880071b80201000482e8200303042d91600d9000709641d000c02400030300ca0000c2407000110645010b034010341c0c0c1c0343e10291409440b00e4682c6070281086c1d2010030383c82150600004450041c104d41c080041c03098007008801400c6458000c0c84201405500780120ba00c0c482c24080407800761900d808aa01c941d000700b0041441e01c0c0f62800190901c81d02c01449011500304100c00c0c8449074001d41203a02d61130b900d480c0000c11044009506040c082e103c00d0101440d0708290807030440c1680000000d51041400b890f40c01d0030110343c07040003224070046c840100640315154a00c1c002d076004a44042c0e10400604040000e00c0181e61007111550381600b040310031468505500c88942400d008a01030343e0020f00700140380300016442001100e107440030b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 134247661 1250 134246411 134246449
    0x3030103052104090c0c140d0210111e07110a060f0807030902180f0703090c030602130e010e09010c0c02060909060f0a0305031902010b3304090207050615 68
    0x90000d2000e8020320843d0700900000c40100850140c1e2000200003903e42c00c03054440042441544401400c0800d1300074401d100e5030001e0001d42c41c04009000608800744107060a190103101c0c800700301c1c09a018043d0a0001c81c0c440e5503940d410b40c64400c8400d40e113050040c0c0240c6504506000841d04200f015040c900395040058042e914040100d0141180c014025080f01003605880c2c60f40c000012401e004132104125070129988400742101264194800602005140c020030000b0802a9004100d00c80f5500344200c541602d6824070302c02090282d0001e0400b060960400c040c101c001c0c480c40410010f5850550000002d40c4c0006c0c880d401182183d070320420b100030105c0d8a41d40d0b007c0320b1011a2501601118a903aa24103020391640c01001c01170340c2c0201042a2040d0301441803049140a4030001c000d1040c0302000072004040d0544800000804110500d26600c1544078070050300082100550160382c41a00b407070002d08190010b0301c050320f000490043c54042d5540d00701400c1d40064010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 134248911 1250 134247661 134247703
    0xe10020106120308190207050303040204060501030e1009080c0304150207060203040e0f060d150b01020f060402030a031d0604141801081c0c020d0501050f0108030a05090f03010b0306270303010305 86
    0x1d020000c9417002c601c00c01c50064400500c090030001c1c00303c00b640c4221f0084608012090b990f000560a5665003141040c540d00402c0b0442109802940418032103030248001c0d03800c0070540d407001c510f03580c0f05400149600755540d0f01c81030000d50401c90000a810181f0145042c1807601d84010312611000c2e042480401c88000059810344882181c0814217812a41e075100c4c07034081a1050005124208059005000d007400a540103840011014050f83c0c0c0a4000c03d284561500d0890301d81c4500c41801300c103500581e07640d0405a0324240680054606400c074580150314400800ca000001c0840304050089800c1c0100424100811029500c8100c400e1500c400f040d00c8004407200f030000a00254001423140410051003070560085109941c00741c008019662981c0500750703070b40a020044400030324100f140c00f50a04000c02c42c0c0d486645c0203400894002440400207003810300c1103460407215200e800f1505000702c1040c000c4988540c1c6030001d14a5941551500350306c404a984000c88182001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 134250161 1250 134248911 134248921
    0xf03011403011e0e2b03150f08030310090c0210020906130f0501030606172206050f090d0306060c0204090804050a1202031219120e0d0e10020106120308 67
    0x3900100b503000f215001002d0320304080716211005002c05081100d862149091403400341186004000078803031840d408004050a01000318050501004551080020100300041d0902c080f130010300501071a60145451b4500707400c0d000d9190101d6446044464280081c00382c0325a00031031203082c5a50a4100569034401c8140442c1640c422811208524903c0f200c0000d04400302015000985409a90170700190707540700700496000fa58511540c2c0c0c0d501c0740401103509489481000d8003c0324081e030303030304040c2009626030030304554045882060380c542e05c42c1001002c60090024080080300e90404122043c10b1910061800f40741c2c1c0c038024000c55450304448103004404041e0340080500a19814045846d502c12200b07150300b00d03d08074003d00c5100d040500c2d2040480590b2b40503040480d584900300f40c0c1200403512201e5440c0303400720b402d9a400c50034200039002d00c1404400000c544070000f6240039030085c400039103440c000000441e45045801d000c15a001d58840c95070f940c0616040c0181c0d150 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 134251411 1250 134250161 134250163
    0x61e040b100503100605040b032e06090f02031b04121401020705010207050f0709051302060d0f0f0e0f011401121b060f110f030a05071109010303020303010512030f03011403 76
    0xc5504626403500c14004c811105480c40d4101c0c1d415110240c40501441c8030103000d255892025410040200e880040c020302002e0b8415003c641c0401d00f0740700824101da40e850010304880300c00c500c40e46265000802c10080c100c0071082c01d90b4101c483d01810b8685441c02c400011640780c420302c001c222070312805c1218038880c400d406442c031035078011008540d61620f92074440d503207004c9500c40d2100c9014240002031258124402c0904c82c04069034138400f825090b034208092980325203001915070360b4500b41d00c4034520703003481820002120420001295200215401d00d4a1000d02c9000c0641c2c0c10f044d044070f4203800c01c1c1001343c11180b80c02151144145503103050440f5000041d01d07901d500340d0f010ba0001e8100e03400600c1000c40821510794840c005119209a0b4440c0c2d250404011140d0042081050051007880209034090082961040082e012800036207065801e0384144d0050380b0201c0180701918103090100d2400203680c0041d46401c121107080e0445000c148509101d4600360043c006207614 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 134252661 1250 134251411 134251441
    0x806040f06050a06020304060210020414060d090606090c0e0904050a141507051201060c0f02090a0b0616350901120f09170a050d0209040204030b0f09061e040b 70
    0x1038003c041040035a202d09000350390350420312030b0200612aa1540840c0d030745a078400ca5007540c0303000b09410500740030b80302400410341c0036031031502c5483d0740c503100c140105596220b8240a4000c0304000308880e2548500108000740000e00540b20b0000c400070702000070800600d10701800d500440b000e000e04000c101c0300d81444002ca2013540d0311810841085803507907000c0000c00c0140c0b0343c6a80e0900598a60300102c03044146054003d05041000381a40054a0aa811541d01035882500072560207410f00206459800c21200c00b40e8000141c00000100841e0386907117201148000b0170314003c40c4c0882c03800401e4059001c2d011036401800030344807586901c03407108140c003220190400d11048848007115001000c403003005654000c1c1e02c198000032181d0140c102c410300714441c4d954506014405000380002e502504521350700990030840040022080c04406100b18800910b08500b843d003010b1150800300d000b440c00905c10b0700c82e240d0800c1d0098045907c2c0d045900560404545d90380c454551030100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 134253911 1250 134252661 134252669
    0x1030b0a090807060c0f050c0303041b09140f070c020a090207050a06050405060405070501050406051e04080a030807080a06030201090b07020409020301053309060d0609170702040b030d0806040f06 86
    0xa4400070320f10050000c25000403804207030946d12551207a48220301211580640e040c0c841268008002040104c3d0107801182007501c820000600210340e6407108404665a40031001100d1140c00301b0030007000d4000e128240d2048807070421610507405a40024800382c464003512035030507070109440b02030010400c1400f880c103600240400080c149824015614202110304903428410340d08040b80b103512034010b0b2800c0300e100b9228541440c2c1c60b0005030000c12240156500c20300e60030b201c00201900100868041940661600b10072402c10180040440d000201900d5045040c10802c00040c0d92010a40c411520241da205031a01003e10008010749101031020354503608100611980c1d420000c41c03180a103001442c00503072250b0350320221500e2404140c0582d40545a00300049460401da107500c1c81081c4a41e1002907001c0d015a580b0701e070742c07182c129040ca40d0400896000c1c118100340c4106100000c089004104184101c1e030000c1c003492008241d240110307220300c42c600d1251900d0300064054 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 134255161 1250 134253911 134253923
    0x90612040c030b150f010c02030c040e2d0d020c0319020415180e07050a050907020313060329090a110702030a05011a0d0803010306020f2502010305091501030b0a09 72
    0x3e42411020503070a500d4224946111340075041708800c4c42e60103144a003049070760141c0036200c154203007803c10000346211070b011240c034000e09074603c00e1160007622101b0380b418808511403a41d07003a0104507107020341c604041d1095500100b60070200d036a0008807001c0b10003020482c03003202e0340a40302060103032403400c400301c0588032503000c003080ca404d00e007001e840c1801c0c100004001921941d542650380c1c000f507220b5941c0220b001801401142006025158000040d00403a807030180402d0700307001024280c0d4041c1002907a94411050b10014405c0001c900360344036440820140d829400190b00030304040c0c06024030380c0e070710f90011804090380d005480d0542d0300141920100e60180c00e01324041d1504942203441445104200c00d5a8548601c00c40c5169401208c2c0e0703410340c0e00f1541e965000b5403122006945000d014440c1c03801562805211f680b01d00041c2c001d03840e41b9401440090195803010700f40c1d140e59009036040c82104007110303180d03604407034014114000d9510785407001401420404400307001c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 134256411 1250 134255161 134255183
    0xe0a0c111501050102191113021603020a0b060d03020c01080901150909060f0c02030406030f0f0c120c03020c030a1404080118110603010e130614010602070812090612040c03 76
    0x89996451820780c100c84080c0c00f901d83d40c0c5110308a001381c192440d82e000302100c0c0801501c10b014240b00400c0121650039460052034034030705030700c000b192601c0210114016440310a54400304891084403e410074015100c090201042c0e03a4007079112174001c900300c0e04005016000071514402500007840303d01c40001d410103103503224130041010300503207002a1011404c0007654558220b4a215662010266074061400c141c201001107010b400060100d0340c219071522a488250102480b41c0e280608031500d900110414900100058444c2c40e491081450703c18802c44000480200450350017540524000d441c031180b8a060070780c90f01072038110100541ca846003c805d104d080003281003556005500c2c03802c40d090400c0400c02c0920090181401300300694012030000d55001c66554480c07445206c021641d030070280003a12000100f64020801030303000d0002000f146406104d8042c2007011304041d2440c0c4104180424114841c1c01054a03954081200007800d104140203018041d5500c00c2d00164 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 134257661 1250 134256411 134256433
    0x507020c04060f06140915030c1201061d030d0818030403080414010908190602030a020d09050102090a090e07060c0312050103060b090a050609013506150a0e0a0c11 72
    0xd9841c40e401341c000459412603846001140700c00941e0281c00d4010100b0305e11881728001d481ca250005407071710300a80c00620081d01031102c0701903c980640106c1d614060030f21a0003001042d540e00c0504903900981101424040d01540645501e034030100d603101c2404200003026046241d031146610203000c0e00707004130300420402100703140d590a0070000d0340c46445094488070340e1902c8180c0c40c00282d8851600c003203c100001d0f60360300076540c0320079000780050a05084070210010340d040c20001300c4190b540024203041c140360030826a0040c109813981040110103050307007540e40f0000303030195006124003980907808040c440c41c0d0b01c0c0e0300d084020409101c00c3d6924a006000703401490215845000b107000022072601d0144995413103100008c01488440e480c0900f40d080c0300c03440c1c00800a449261035000348600403148415846641d180b8010b101918180b041c2c1080403c10000c01d80c4240702d1030b41d0420040c0340c2d5860301a004050f41500142100136a1402d95040e6107020121601d4003409450304 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 134258911 1250 134257661 134257679
    0xf06090d05031314090c040909211817070b031f060507050d2c0307050a0b030109050105090405100f0b0d030503070801090b130504020a031e0501060603050705030402040507020c0406 80
    0x2180ca40c0b044d1615240c0801e13040250f00c0300121a521840c00e01480100202c2d0030a42200c52082c1c02000c1c0d41030203840588420301064911080140800c400003510203004545042d01c10052112141d0044c0001d50340f1210f5071030391400e100301d105842010010602c80c00140041c0740543c00700c0199203d4079981c0e200050140d41082d9810b83c0c01d4040d840300c410a0364052203160300340110321010b0180c061070748121b00c01c1e06005070103030b260103100d8a84007103480c0d202e100e0114040c02000184039200c0d0b240808101c00d44005070441c6014000e03501c14403000520019002c190480d821b00c005c11000c0f0030080c000f004000c142007260348400070740302c480285030b002401075003d141a5500c0c001c09a894804640540740d0940300c07160007030260030789541e200c611035101d650440c1c402003c0b003065956944529416240310783c0180c440350b50460b800820032200340700361402495941400c1c01140380a501c0909a804001c201a0182d0746440025080620a0010340d1411000a10400079a81c81c4d480300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 134260161 1250 134258911 134258947
    0x90b0711010603030804080a0917030c0106090e0c01110c0d1103010b030c0919020c0303040507060f0e060301090b130509010507030b031615110d08070314060f06090d0503 75
    0x25000c03509891144031100d1040c014441070b40d81585550406071119078a4091360390006158a0402000c10800b250b0030b00189600d401d9540814011a2541100c000e92800c46205070701000c44249800c440c480a40740218038515500000d003451509084002d00032414a204000d04c650f0108441c03030348604215031a04420105801a0001c100040b48581455615000001017680c00034507980050583c8062200005520024420140c00d00d181300d4041c61071a0425a8101c445400c0100103100c400c0e4080f2500003005150703d004908540c0d610082121031006000b101c00040d220700404403182c0302c868142507200380d4144100410303d400c0012a0080009443c040d000a00301504200189000581000e54500c00041606100d1234080c1c1414155560b85a201c144207810031951240b103c00d1003400f5003525607880d840d00c540b82101004048400c600701c00340080000c181440555114408140c07100102031300d065070350f0031100000400100c4942d000503c284000150b5001c494101c402c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 134261411 1250 134260161 134260171
    0x303080708060d170c03070204050c0901110706080601050d1103100305070801060b091201180c03120305070c0b0403031e09060605011407031b0c09020a080a0e0309090402040f090b 79
    0x401e1115203540c0100325181d00c488501038003080c880340b072151500780c006000709207402d10401260b1502c0038035400325041e55400c07100480d00b00310116800d2501d582280c84103c1c00340c0c205029052050900d5005800e60301c0240155040010120b084071041741070350711a03900403060740000e545034a45440c80340c0e203008440c00222002c1c000d10301300152025050140400b5200341c211024100701909090009140e00c040000a1942d00d40c51450000042d410340342440b40e02801c242859641107052614080100c840d00d0003c161070442080491680090302421750350740880c1c000119203890a04401421082ca00f100b440c46c60b20b9201352104015074400c50f42240b0a00040c0140795a48006480b44414002c0b23a000720b407004c01059000a2040f11030541a600e924807071301d484540307500c03080302d61261030f0015021194002814003900b904400c0055216010240511462405500c46070f100e000b604403007070141003c0b070046411551103411505001b07001c2c0b4420080d909450400010b00304041e50 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 134262661 1250 134261411 134261417
    0xb0405011d1b090105030a0308040507030c15081605030109021809180f03070b040210031e020301030201031a03030d1d0109080415050702090714090a081b04061401210603030807 78
    0x10b078404040c1001a2420304803640140506442d08460302c0503503100e80014000c1798240035648003c00052408040000605440403070f22103003c0e224580a4603012016005d0b807a034407003901c0010482d0303038004100ca040d82d03100800541c440016485114030100c20012141e40645500101300031041e07214131480f20810310004880b040d0740803690350b80d200e2158180191500011400103800750402e100100d03030b003050702d280021b4a8150610b5196015101c484034850740f80e00040104107640e418080c60070748501c040c01940b07070301d00140e0000c0e0fa05e11411800968843d1604003040c0100d0502c0c8044240042070f1000340400c980c3c40c41d060322241c2c000d01403d00ca440c0a07411205c9564850750598144075030107803248450346c40e81c41c6c1c02c2e03440c08801100c1c2d41e2084d004008101d040d0307d171300e0992001800d08400524504060200841c08a002c4000ba240944d10703040d0f003080040842071414100403002e081c800581a10741a06070185004030200c84081810074000008260b07105481c54441c00c076540d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 134263911 1250 134262661 134262703
    0x507080303091506030c010f020a08030f0402040518060f0604090807050a0302151e15060c070303090602010209010507060b0a08030f09130207050d031d1905010b03031201030b0405011d 81
    0x60342007000e143c41552069055840080100c1e85035000f02c903501081e0303549004a498007140d81d41c40003e564411208101300210030360500045081900845802c40c1d894507090300311411b01c5502654504005165103404030786c160101d0080d0322987d012010040d00000a2540c8080720300b4425a1600304900850051244407942c044100c00c180b13003140505c44480b02110310031000e240c001c07220507010f0401603601028541c03403141076540c1c1009050a06000380038001d030910b1418044c003500007035072042c0c0035640104604003250ba849000c40e602c1d80c7c2d1001000500c1d4006001140b481c45454000c4403003448001840d62a602c44c84014204446d411110451095035200b0548240e00411800a01592200c001d01f0a458001e8002c2c42e006100622816844201d40b1100b92800b00178040d5056000d4140a00300300340030003806001080b1905900640c5403030080c0980c00104001480068440c42003a000b00f01080030a401c0010494520280064081c2c4050449612229106078841d0304010310317 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 134265161 1250 134263911 134263933
    0x30210141306270302101218050c0f0103050106053705190207050a091a060a0c0b0112080304080f0c010203160f02010614010302090112020304030e1903200d050708030309 75
    0x7610f003203068950140154100c401501810380700102c681010051454603410681803406022107511201390190000f0048030903541c0500c1215208004c8090415043c40c005000d9650810122084216080300c4810384407400d11a0b1a001a40c0c100710000d500d00000c42d0401036644040604021511223402c012803403589082a81d9540c0244079030754201142000c02c00c8026408d5200703041c440503410b02200d15510440000c4c50326071041c20f00e100807507400d400304014032100d08501030140c103141c0c00d2900c00700e4980c0c8484c880c030701000b0401480b9460008118094207606002c1d86c06c4c0303820100080d916828243d0705802e400080c6016000021902c141c02820140705001e130300101d030403002c840c84954480c880114044d5010f021003d05000d03020420b070b850040144011031041e8040e03500e02280050280400141c078040300540d040c2e180d016001400841c2801c05192110700c0b020000107000071140c00890344407007001001901c140184040050000f030084011071007041090305440010704a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 134266411 1250 134265161 134265227
    0x1503050106020604120c0f03020d0e0303071106070305220603110a1d010c05100c03050c0a0207050409031b0f05060a02041a0703020f06010b0903120301030210141306 73
    0x401d1049400690041c80850049118400030010080482c909602000e6098031901c00a2608901c2100143d11481d035103040c0c0c81d4440c0340340da41030f601207025610f0314107291a1000008420428184980c40c0051000700300760041c030490f88091858000d554800b10a50ba122044030258031810010034141120b0308040c060550441e407100400351501c15403014a075989452100d000101103050280300d40717050000c9a400c000b10720410045100104d40207840703840c014190340d070103480c2200c40c0c1814080a03200d29008542d04003070310005e55000542142c641005c41d40348220307401c02c01d060f0b00101211014084280012202c01c0d00801c11540152550303108001280b041e441481d500800644403240318046500003482014042d104a500c01401a2070450074803008ac0c1c1303c0310002d000003c4416050409101c2e0030300d0782001c0ae11282c01d640c0b442c4c0228038400103211006007003010001050041c400654260307075842d00f404103001049511144080d0546401d0341c00300b44c0b510b0840c3c1181c00c03140302e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 134267661 1250 134266411 134266421
    0x5090a030c031707150b1215090f0703050a110312120a0c090506040302040207110301021209070509040803060409060e03040807030212030f0714210901081008120703050906030a061503 81
    0xa4040c0a40035544441d15481008140b0701e03490390741c03264040b81e44241d01e5070308100292048e0310800d0204107904211542340c2c81d014241d41c4944a9820200d410804501c0100d65030b07001780e40102c0c21070b518555400001c3d082c1808408508941c0d04c002c1001031007002d0b960140c922400f6246010004a01020400d544120543c421641c2c410020441440141001d40140034403d105202400f00039900a002a007a80c22889149407414100002c010344e42e18200502002404103843c65051800c160700c0e02c94042c48020003040c0500c2c0c5502a42082102c03917480741c43c229044c201560f4656413251000341c0c45d0502071000340e00c01d0242c880e03544071032000441210610001e400c10703c1d141c40c9042e51407042c405201c011404860198031040079200d2451303440f040d0744903015548181da41ca105000901000300c00380c0310725403480d07140c442446104c1c40080d00318000300807214105e80783c0e05a858211202e200c0c036404190403402c00320520042200c16000b080545401074406210700101481c11807c6036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 134268911 1250 134267661 134267663
    0x601020f070632120a0504080301050d050a230c121b0a030614190c0f180911040f05030f0d14070f051b01090501090504050705090a030c031707 63
    0xa0003188042000a008400b070881401841900340701004403a80b80e003040c0a103c81d124242c079007000820001114103950001d0303205030030348030801440c2495200c841700c0b800140a014040c0750701e40307454801d2090400145880d40c1d88410140544440506410070590040026078054810f032b031100d60351480c0c9000c100b50003810640044c2901c075050310fa054000b961014a19401851620001c40425111300600007244440c80f81c14606080c0081019955140e202080e11110315140310700034140d0348030410600f4480c03185042c64140079524405a004200c03507000442e810b00c1c0c603e1089000b02690003610842e4503e0340d541d03201d0b59a9905041c0c41c0c00c88207900e0300c80d9403c40001111650b028280118005110348002401c002e61565102068510068140d0303566008400c55004070b164087c0105807420b00b031034110501413510001800038071007070242512031034072600081c0802c2c0c807070019509084401041c00216660b2814400d215003442e000a0742c592401e840d45120600b034610880e40f00c6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 134270161 1250 134268911 134268913
    0xb07030206150a0f06020307030e010302071a06130e0a120507260409020f070c080c030d0c0204181226010b130306020409140a0504020607140f06010306020703080601020f 75
    0x1540d400c02100c5028034890301c0706a002805190104021312031811036400b070500781e00103655070b019508020340b940020002d01d07410540104032440001d001d060300318903003040c1900300d601140c4071400002c580d1341700d4009410000b4500701141c4000900002e05a00c400d0240100c503543d5080c8450032107080c0708000d030107401c4414000e41d00d20803d01250065005002030303100740741842d445001240c140c0e8054040d00c600a1008111340c0144040458182e000f8074030a030040090340184004640c403070344803c01c91003d000044a400044d9100d41d001082c1580c203080003405071002501e0b0908400049010301d100091aa60003000b43e004108030200034060304c40e401101682c64401d0086440c0d0201c50004d03100902c501000000918030300251000d40340c1c148000c56010840324500d000c1080c003e110f0041c90707060800340005070f2102c00407140159045800d034054998040500c0e86081200c0651180e14031030f0000000510985901402c8164402c1d80c0c2c2c9001074503100300490341e92291003511906 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 134271411 1250 134270161 134270173
    0xa0903080f27060a08040807020a06030b0f040606120b040e0f0706080705031e13060615020d09030206030105060f1b0615040903020c1009050316030b07020613080a0c060e0c01090b070302 82
    0x18130385c01509641d03801403107074600f01e04c5c2c44c030954040340300070509034851400700b61582c004050501d48548180503036181514100301c041d00d0304400400d0340d0031415071100c103959200c049050517100e07500810540405541220a4101403d82d0340759600024810500041c00220208a8003403159080742d01500c0d25030401503040c018604060342aa201901d40b40644001c20840800940140a950024840f03003d04128102c500c440113400c1c450000081b00800c203030fa000a01c0182d54003803c0da4196001505c40c6600c0f00e10304842801d00340b09205400500c0c000c2003405001d011000607a0314803882140076607144003540c09060200b9250720010040160f0400d0000300c5180c280241d582002e03000a01d003071544c2075900c10129007081c2c1100c06200c00855442003d10030f104652050035045911480102000d1600081e00d000c040011080140004000100c2401c010711030400300090a41107401003010b036100142c1d4130382c0c840d002c40401c0e0201e03502d84000514114010155140300782c041d005014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 134272661 1250 134271411 134271427
    0x110709020f0c0a0606030210050c070905040609020604090207020a051f0f02011517011d070605070c030b0a0e06060102030307050702040e01180f031e12020a0903080f2706 75
    0x3a4000000441407200e081c441110a03107402c10101c400d440c05070a000891600314010310071444400003e000a10004015a0300b06407000108541114044000065030b600c66181c004040c0c201c01d00701035400840820081041000c40d4010b1004500c00c0713030119846580c9805005c41c4a22107010070a5000901d02d8202c1c3c464090114540c18103224400040c20300f04040c114003a0603c65004580e00071403290005e10401800d2162641480c150466860642d14880c041d998842150007031204014010996008101c2e40304184000766502074038083c05864002c0d8080001c100c000400072241c0715043c0412629400401220700030300f81a61160301d420500d03024080580080d8600280544d46d4090714643e003060601560941889242e88903042c1036503040040441c0007076008040c805201a512004603a0850582c502030001c10344003589411401e04281c07000b10b01a4005000031900281d100c4903c0e85000c010b05446201e40000c50000f43c25120f101d500d1881140c906420002c01c1040c50 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 134273911 1250 134272661 134272679
    0x110306061305120a0204180f030f12050a050403030b10050301060e060d0e0c0108070305060d061a041a180c030c03040c080a1a01050603070c0312090206040e04060b011107 75
    0x8107060303012440010516568a0100304000d000841948098004680c0c0074210314040c000d07070b980c0c2c51115410f004c04d0034042d1a080c0705070110b03400003801d00c8000300024200390301610400440f801c107076004020525000466001421040b182100064a402c40c070440d10f1405070a400200180799a03590309581c24002c05039030035211101080e504c003178207210390201d2002c0350243c3c2010741400005015181e982e0380015005c018080c241a080c1401c0c5403c11039683c84010a64403510340003180498102e2200d8000762505600f0f03480e0303a40043c02c04c1001300c003c0d041e803001e100d8404425140c8a40411183c4140300c0b4100b001e8a1400d80d0960401c0802c2100264030302450f005801150048040c0c0e0b0303500505880c00342d002c0000c540042c040542551340041c101112401400d050380d00300e00d1468494001001280192801018401841130f8180d561019512402145d5405021555125203400713001d2031042d421181150400e00b401040000d651141e820981d988000500030002c460030448c4034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 134275161 1250 134273911 134273917
    0x90c08060108190207080403030e090112030c1e050a022106010909061104062c0f101b0803151215070c021809100b101110020703050d0507020111030606 67
    0xc0303c0c070009510689080e0352120310092500501c6010266a00c41c610f2902030302c4180d10303030600c5200310504c0c0c004001d940a41d02c1140000c41d858500300f0031204003071a01c115061211203051120180c001c6500007042800035442d45801e0080740d000c002040584c507030404901c41c02d80398040b40d40001e0010000d160f000c4c3c011598ac0d17032041d9408520800c4040d4511160b8001f6403080000900c0e14a2900c2c421300d060b01605003000d45420b6004249810b0000b01e410641e4030110640141d610605007411217100e241d0000101442050041c4810381707600702010144c000b41c0b0b29101840d10700e82c41841900d009003404140e00c202c135010703207682e80305142e0f0040d60034001002002400801c0c4044401659110b44041000b41c2c61604007a0311308103e03004500d080350030000014400e20300302070030b030190790782000d0980071344480d01d003018100c03810320303900c90030045a8035803480f03c0b5001181c1941015040001781c40c40c0841c810b0100001c0e076031000100c0c2a0f8400d00c211403001003081000c250319003080401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 134276411 1250 134275161 134275171
    0x10020c0a030507050a050105071d0a0b09010c02031f0e01230c1b0105070c0b06031209130b0d111009060807080702031605061509060f060c0a2a090c08060108 69
    0x55030541541920750a0a4031409c485201c00a2070304021060044200c0840c440040001d55841c2c0015040c15400381c51b41c492002c03220b0501580321808421554100122109a41c00c4040900f40c0c0601a01e14030292603501115810341d400c0c0b10b0540d0081c54541e40340c045c4510100748909a603103989405041c0780d400241d5101c002d0346960300d6060320900902400f80074a160b65035a140a00b9907017040d802840000c0c1020b0f03c290400b101140c40081c0200581d410b44600301c03030009809400c0b800c0c0c1e0006004a494a80d046203d40c6040c80a020780c05010701d0101c07a042d5000c0461544041c411911080940035940114500c00e001c41c4029200d02101c56100707400340100ca180c5003540740c689410601c182000c5411b0362040c020008503d05000c81321a81d40e20588401c46503007050000240241140c00c00c6038081c48020420440000c030410404c01d040380c0140e00d084154048600c50324865000500040c82496204000501c5601620690b40000700079502c02c8220344600c0011038000d079000e84 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 134277661 1250 134276411 134276413
    0x1a06040b0703120501030b010e0921090315040f0605090a08030c1305060325021f05040f020d0f060501140f01140c030409150803090310020a0302040b0a030e10020c0a03050705 77
    0x4254000442c0c400c1c9170296020304041c8420350301d0521400751540c4010408481500105020000d41c9070660f0703d118480c5414040f6529500044c02203854400d8407803c0c442c05407402801d100c10f11022840c40c3d440180106c0c401d00060f5118024181c3d5102c102e20010001c000400000f0519202080038000700c3d60303507801c0750411703940e0b030b20001d80307550025208440c410143c4010a8003001d290381c0d541d10340da905800070b01100496040301c4c0d01d101499142d9043d100352100300203000c0101c07144900c203203d0350003000e488030b82d4102d04103401556490340040f695036183c140007280ca15030000c150580f4600013003040c030244111700c0044840c3c01114443c1e840d611b00070300510a1184042c00540043c00341c00c0000a08a80d1280b8a4800d070422540001ea142c0c0003080101c201f0b8802085e2414800c00990001d65a905040411030003441030b40d0240740519408659500840d030315422a43c0d003840c2010442d2041c10042c000381c4e0807846210110b9200f40d104031000030020780600080c1900c280144 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 134278911 1250 134277661 134277677
    0x108162d0b030106080a1a0f1302041205031c0902091909080a030f1109010203071202030903011409100614121515010212030405060f04062306041a06040b0703 70
    0x2203908803140c2c1007a0042c43c045601c090810940800390f119103a0460344100804010101e140085000c40d01c1c8180c8aa000c1c543c1e02c120b04000c2d0b089074048400030645401114000d20241c00c02c81e440741c008440c451030304040c0c2c40340c11001500500a940d030103900206240440d8407010b110141c80344021058041c1962905402804151444082e000e0801c00303440105003594081251000c842c07694031901c0b007420062052000704e90340041034500c0c0b030b41d212140460700d03d003400041e0301d50300507000c0803617143d82425400c190382d10031115403602070140041187c2344003505807904402d568440c007070305032504140540c0c2d6003e0325080c80005d40714851141a201000c0403010001c11407003049980c080f42c051542113040700d80d40d04004030f44911443c1c2040303500f5801d0035910a601d4483c00742481003425002e8020500b841010f42c80703803413800d030444d856038104040e00103144071a0000f00c0e101440381d45018448001c030300a20804906025000b08402e00c1d050030aa00702a05402c100c47c01d0301000080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 134280161 1250 134278911 134278919
    0x109090b0139061d01090b0606090d0c12060506040e0a32060f22030c03140d050703050606090616080712020105010513230613140108162d 61
    0x2100c800c0364860142c1d1000c90051886100c1da411300700302441a803001ea00d00700d200070100740c00100701900400c088908030354600e120000242e8800d00c1e0308000d89100102ca400191400c0c84143e04042c3e148540000d1019607070345001c100869040300001800364016000340d2002800320402c9000109000365402810183d229800f01905184c1a480740c15030310140c00d00100b24041006254400e401c9010800c5042c8210002580190003280003000c2c40405e1040b581090b01980301004d01000721412541c079419141a050051b14090721554003107481d180104050b8107000b01200c00d0340c10050300711454040c80c01d01c0350030710007481042690403080900403000014108490340b00900200d41c008101c5504007420011301100c0110f040d200b0b14a445540c100d2429047c010000d40700b0218031310700c602c1d6141d20200d81c00707215491018003010300d03206568803850358901a85041e10ba0741f100700e45209005440001c032a0f681405440018131030b0f039090314038030b04141c03c1c400c40c0d0006c040d0b101c1e1111603503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 134281411 1250 134280161 134280257
    0xa020d0e0109020411030606041203030605101e0509011706042d0c050304020a06030f1e090b060907230405030d051b01140a020f04150e0109090b01 65
    0xa0100303a140180d44404030300d410351910b0300904100362480e244140c954244000060030900caa44601c481030000014008103160003640248014080070f004100410ba42d40801031564a2001c811424426640d0344140345500c180d00b80e0b540c503c2c0685030b4820800c0c02ea075202060400007407036680d2241d01c0d10003111601c910828440301010403244801d1851142000940a5030541102001040002c0c010030000d603132490314034002c451190600041c410140600080a040742c42c080300801000c8601090281d10150300c07440100c2d0050f0403214080d1651810041c01d0345080e0340882c0040e0b0031142d022182102284100302c03448500c20f000c6d15066580c0003290808159141900100700c01185503241100c03016000000a03070808000c00c1800c980e00c27041007506002515681f502076020410946032410701c4221005070040308445241402c0c2c842008081ca00400c41c10303400103001784800200081c46001e039142c440c8051b150300083d1558080103c9040b40d0110f024503010b0003002c01d80c41d0b003440c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 134282661 1250 134281411 134281421
    0x242502030a051f0902010c03081f0b09030d0c0b041b0806070f09050d0302071e0504060b0405030c06030f070c0204060b03090c040c02030a0207030f020a0308040b0304020a0504140a050a020d 83
    0x220501c050052040f1482e03d580c003100d809007044001d00c4c00e1002d500b0040c2e0f4001c0c0e01048940c0d06090052250301c1e007a0700180418040c0e005001c00f011b1803180811070702044409480c0342c030402c80403208048240c0c40c1c100c54004e0341d228010114909070020400040c070519101c1ca041420203c404200d03542c641070285000e6045c1c9052021071011010345086a500103c11009403500340c2e540b90689145540c0251348881c0f40c82140459041650715001460307004d540e0074003d210041081c4200b0703440d01030081b900c0d40f052044520a01c92100c0c90301850905105607807140340d54502c2d0328000c1e601c0305400e80c0c10711310000b030407a030043e0f6038440810320180791400f8500404054005102a8071902c007807104690540201e0300966200307200901d031403540001c10a0940780d00403805221903a051010900540042c4c01c001c3c01c802000c41c1c0460b6406240e409944202d008480501644e81d0b19411300c000c40da01d060304035081c4002d1500041d0341d001d03983c0005400121098006180c5034098028504441d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 134283911 1250 134282661 134282663
    0x50303040c14010e1e03010b060a02070503190f0f0303090204050703141807060c060213080d091e0e060d0b0903070203070b03010605030105010f020109061505242502030a 75
    0x4080040078003641020b403244034100d040a00700480e0041502c000180c03140d104650b8a0b41d0401040600e0b41c290b1829000340c464140c01a009645440005001039202c0700f090180500a12070892890724403501010b10144040d0080403000301080c407900c03000e404040d11542a028140c5500340c140c01601c55100302d51040d01e4554000400410103040c203103003040050105480301c07440340018003001304085074420840341d180c102801c0c0403c0510b00311002e801509401c2003103004002000603581d8012134000c400b42c0280d55100405511502c41c1c801904200d803c48055820088091146144001c0300315000000144100280f00c90340c0c2d610f95448108a6100320f40c0d0300302040840c01c60604002c0200a40b01145d0b14504560600350011310601051141c90304002c920705003400074500030b41c48600f102d90062014003552510082020000740341d4451a80180340700d2101f003c46410305000c08004901e4180220f00e05030704000d2070060740100014106a484464034400700598007000616031035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 134285161 1250 134283911 134283923
    0xc030c0b010e040506090111180f0a140a080a0c09091a190b01020a11010c08040314010b010f0201092402040512060f0702070b03040b041119050301060609030803060d03020a05030304 80
    0x1910302440d100e4144030014100c2800c80c1e0509a59440b0441184180c6101100e9656025042d29500d400290181c08ac0144940c02621050002c10a1980740503190419002615200c2d440d41d40d601140380c3d507214410b000380407809c807681e041c02402c2301500304a030658025100e4420754415031509603001c0000340d4005c04229000441c49400300020f0181c001d44641c2400039040c400059203a5114500c046a03006041040b0800c2060030083d00d0780588000c1c1d47c00c0003d29980f0b03c20444824021308104602901055052840c903a041c2d10500549019036407000502035224140e044c2010960100741560382d0043e020300011400703440d0803031280152804e1400070499410802000c820180001c0c00c5203003150420081401221681d42c12a40c020f03600041c010003559403828a641c000c1007011900d68090300d902110740c2c0c0708005210310700550710110000c010b01c650391402941c042c5414440181942c0090000401600d0035030f4810313503034a00a00568030500282c0d920503040d944220341c203c0314 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 134286411 1250 134285161 134285189
    0x3030509060d022d040806010b07241a040509030930030702120a0b0708130b010611060115020a03030e010605180109060b0403020108060d02010905030d030f1415010c030c0b01 77
    0xb05080e030f201600892040c40b8482d5103446c0c1001c090b1030301e130b44050140c1414054001010420420307910f0f060410182c0500300c900101600502d103502a005400c0454040d45030441841000d282c144102801900110002e40c83c04034150240960b0484081c229a034502c0c405001c204144800c1c00300052101d04a409140d4581c10380c4100800d000c40000d14031416400400c00d070001483c886003281c0c03c21100e0603c00c1d100e80e1525000c034002c103201c020007450401d43c40000a656a04880c140003401110400c1d101c00760307243e03a2092100541c40003c0d83c0140d0010051102190180d44105d0000c0c0d10320001249561301c80c80842c89448250440f1003109420400401c070b001494814003000d0140e040030300d4541841d50f00003c0034900050803c510030410403511000b10783c010700c1a84002d050140c255208064810780242c01800d8094188160300d040ca221015903114055605119400744007000207100482d200440762208040d40880c00d20901d01c060b400071987e05001d43d402400100c1010031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 134287661 1250 134286411 134286457
    0x507120c090e0c04031e0c09090c03061a01140705010e0304080a0203100b0d02010503151806100c0507261b0f01020303150f150c010b190303080103030509060d02 71
    0x11120328003c01141e50000f00780418000100c20000c102c40a1882c92131142622045042420394401c40ba4807503803032076141101c203100b0480c0e18604841282c2c0100c070708019000c040c00e400c403528050440a039000904901484d10403000a40113403103c50f012788000104410050040b5107036a20039007061039554000f140036411841d042000780c030703081e0b88408140550726442001c211000f144000081c1480b101100003030340f0101480d41c104070341e400140340030714030600c11189071403064058402c103004054083e010740c0c1710713400303000f9041050b58030070020456180f40802d00d41410365005600c007500921401d501c240700208000031001c4030503d1241440399000034041161032418811400c1c195041030040000705541e4a80c1e014007542c064803001c006080c500005100c00c1c0c80821051030100d0042882642100c056012641c0791400303403008040e4010401c0301840c0e006280c880100081c05106c01403001034800c40c0502600003006d401242072810a220000590b0030900000072044a58482c0030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 134288911 1250 134287661 134287679
    0x60403050c03370212030706050402040b04020403021f0c0b09060a1427120412050106090e031801020a0b040501050a060b0a0c0206070c09020309150106030513060507120c09 76
    0x2018540a0002d032104210301c40900b02c04850fa941000000381420308040741952102241901001d00a4080c0c2c1d940d000d0b6854600c00604003a10141c2c000c618011001c03210381024421a42070b0303a0001c00228180c400c0b000e0000c1d04a07440744400c42000449140303c0c00041c0001c0c0c1c003d01400d142e00149c00240340a00c04501102c0c4141c0d080740508215200307114404a004a1f000066440d8003001041c4005810300b040c9048000d6a024082c000d00007400661000210410091a40714074020b02c04540c4d5200d15109a031860b00141000307800c20012061960004031808003091818010b4501300c08042d00d5949000404880c00e44180e5101c0c17040201c4c0d0415886010041c02074182c0682c00c080008070014003403400f188000380030300c00c002820028016141e0000e40100300307111041d035491400f101400c0d1600819a040764800f50750000101e03c1718007034040c0f103115040b505600d41001c2e05544130b2402910015041d07005100c00d41c2448440700080340a425990500c546510311900e140010340c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 134290161 1250 134288911 134288923
    0x80301080f01020a1d0a080304060f12020c06060910080d03091a0907090e070b0c030406020d030603031403180d0806190b0304080c030c010c1e03020702030c040e0c060403050c03 78
    0x44801ca0b44100b0141d41c21a40204024907000072141001100c5500e58010a0f1440741d640c02018280c0300c0440e0004805070301281284803c03050365540000d411004e90484140d006a600c103500503000240010321904002c03040a50100312600440c3e0b98903522000d441c14034514240000009403244444803d00c041c10b00c0e03c2800d0041309c220410b85250100304541c44041c01d0085881a40d29140444000881000100c002e0708000040603900e6902201c225a41e61180c844d03080540903112000004a000348a01012a500b41e1130310702402c6110381c420000c60b40018043c8203540f410703010081101404000d0600f15020310348800700f82c1e007482400c201d0f1200f40780c1e515505a04210b0024403502003000183c903000341e480300c80540c4808214010074150300941d01050b41e591b10349104641c0341c0d41d00002650300710340b02800318903400380e131140b0442c01e9204820020390541d002d6a101c0c4030600f4640e001088502900c0c041d04c805c2d181840010b00e29500c10361054505901a810f000d1080c036040c048 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 134291411 1250 134290161 134290183
    0x812070e0303190e030a05060f041202061003030e37050a08030d0f060e0f0f01050f06180112020706020c0118030f03090503040906031b06020c01090e1b0708030108 72
    0x1d50604a401d184510843d0b400c14020041240b20f03d011100c645041040120b100d40c80020380d060b510340204030081030041220165001d0740c0d40c91113408250700110300c0e1801020922101c000c443e0840d2410f4822a5081d82e0355030300800c600c1007180c82e4400b0784a003074804102d44201f0807651440e00c00d150200c0600394012a00c98200741c00308001c4d44c0f000200311040924911030120326441500c07030325002026540c1c0100e081c2030340301080000818420181a00c2202e5252510b103160340c0f01c10a00c88903104991182c0d4008404110b9079802502034045203045030030500d004d80c501c1400d035034210142e07000800100d640f1500840c102420800030700414200004c084043c514900035a10300070008071500d0356680c1031640d02d0b901801841010320446c2c014001100c020f0100355620718205440f04411070000700402c0760090003052003407008c07584105002050799280f0705641498801da00b014009041c2401c5c0705003656890039440340c41d8014005075402800c2690326585007481040c00c15580303500c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 134292661 1250 134291411 134291413
    0x18060b03090a030309080f0301150201141003300203090307080a0209130c090c0e1002070303020d0f090510020703020a1202032a09040b01060e0105040b0412050a0812070e03 76
    0x104010079150001190449541c051030049001d160780c0c24004c4582c0b080040c0345584100000011030240301681c41c41003440c2700c0390f008010202c29003455030100c03141501c1c184900500c0d108108046001c0884143c804094503202c244603200000e403c1c4240e0784110b13030040251b0804580980140340506c650343c024107545010300565030490f40000e10145000b07080510762041380e5008424850f0602d458405000d054008000308021103e0240c040758034003420381c1c4110440c81489491900c00f00780901200d078150006c1c41e9224601c2820344000144240b280100101c0d0100090141d0300d4421025204106030081c1410b1415030050000e415819080b45020100344008840162000500c402c2210108000074a2407420080d519442e101c1d05524107500c070a040c3c041c0000e0085104502d8100e48a5844220909480b02c0054801c1e0050b4440d2040d0b04001380301c1000342c0c00c1c0791141906901d10500698114007142e07600e0040399040880c0d407030020a2800c3c1040003a642003074404d148410124 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 134293911 1250 134292661 134292667
    0x60f180303090703060c0c0606060305040c0b090f0f030f0307080a0807050a050d27050606040b01030b01050909040206090604140901061706040b2b12080609040f02060d0618060b 78
    0x580d101d82d5034012440b0041c10b95981baa00904141d00c5204840700791584100b0600c4680d030343c3c0c03100501804084e2000d8a140112100010750320719078008a490f4114040c0203415040400c50802265070200400c180d01409141a040d43e040c0301070005056552084440703e8641c00300c20001080c60100030561410b0040400c01c22400c41e41010a0341c100b1400d40e040494041640680c0e40f995401c0320b33079840280c0d00706036a0b40c410402e0101e00c50b8403541c2e0640f000c0123250590310044041d2440840c41c80c2c0072074030810180c5041c1c18000d11042c1e2050011307041a182415107004075115a0060b4440c0e010540900d40301c0c80d00d440c000e115140100014900b001c00314112071031f42c207440314000d8042c52103141e94042020b25901c4141700d40d05c40413001f61000004825450f1200d0540840e5001140c91084409009044c84e02841b82c1600034880a0010240780d5180e55903000c03248840701d42680c1c84601407241c40d29400b0306000e0316000e00081e801020844404a805030b0a03200c0da600300681c140028 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 134295161 1250 134293911 134293921
    0x50411010905060f07061b11010f0507320705030d0b0108061e01020a02060a05040914160804050a0804170c0102010903050a030c0e061602090114062a060f180303 71
    0x82c43c20780d403e000208202c503984001a00d04035000344815200c0104612202d1412210540c20100b103103c0c0404a0000780a11091080c004040f00c0c002c417610000b0444c204a29403c464001c2a4a514520640b851030410b80c0404039047d260707000502c00722038542c00080c90030548041c9003d1405000400c1c00c0103105130810b20006a13240111104070310703d0f010051801c034201da02c00c0081c9181c454002d00f990341e640680000044c42503115005140c011070400e5054900e20300c019a06910404840b90f20746041c85030340900302e500c00c0c40900165003e1041407c020080f42c52200200010030030600c00f144145000e11603103080032160454503040d64500304051020079040f0084400724483c80c5000500001c104005558052160708816080340011070220070750000c403201c50950034001c0702c1580c0982e03a14071040f4524404140704580000051041c01a44141c001e0f840c0c01101031091015502008500d4082c070700f500c2280d440d40d511100a06011404c0c0d80461010081408040a07510318509 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 134296411 1250 134295161 134295169
    0x5010807080111031311090c040f141507020102071d060a060f090509100b030903030a1524030207061404030e01020f0717160b0403030e0a08060a0b0303040504020d050411010905 78
    0x700614030a68121005c84200400c04400003e01e60300307200424008075030074142c0c0c95854075002070280100c1210020720200701007451000c00031914000500f4070102e05047e1003441c20903084190b0486c15440380e0007003c02c604000c000349210540301c00509044618207541000704101856000909020146d0003007200e0b258406e158105940040d9800001903d800e4501041c5070b0341503112400301c10300030051007c00340c07020000710700503a000e00050020606036910100c0065091103180200030002c01829480f240306006000b420005013801400c01040d034803410241c0c2e0300324007440c1079650000204000c1507084140000d11305000e100411466000d406003698840a6000d40190079541e0160002d80074010010300001c80c541100c0e40150030396542e010421a001030004802040b5a0507480171181004c00002044640c180000d01c0c4549400e003c0c9001840b143c46e2164042c041008085041d4845000411240408400001c0d0a24103410441d03020391100b0003603410040d03046410881c59031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 134297661 1250 134296411 134296417
    0x10c030902061905040506161205041d0c0d140405010f0216080306040213030309030308060d120c0c080708100e010506220b090f0402040c14190c08070605010807080111 74
    0xc00e0400b40e9003d210003a001d950301d00a5500403680144000742d00c400741c2801d42900085144545060308400c01508801e44460003603005d03422054002180c0c03000108030003000190000e040e10241490154414011010344203145031a20350741d0b02010230310081010910030200c407120040001c40c2807034000a09014442e00200e4017402251003c400700d4910b595550495403d6566003e041c001907030b0320b250140000390b051000360081042d40e00003a071503040c010001402585d0201401414030013490003960342c1043c1540c240d41d0540c40780c40c0420842c804028a1000e0021a00100a9000c00c4a403003401d5034107207840b01030320741d041109000b000d4032020b0074000740800601c40d1619004241b00c218000300240d503540760340050304106010340780603c0701145001314000d032014020305a0345141602c2040315074207083d112450030064152007003c0c80f040d4490901e081c0c5030914035440709440342115500145800e48200d44e468004000c440000c1207940300034814007000744458802164441c44d40c1c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 134298911 1250 134297661 134297677
    0x801050321040e04230a03020715020c220606020f060a09021201020706020403030305060d051c0207090609061d0c04060c0c05061b0c0d0f060218030d030b03010c03090206 75
    0x689605038200c030100441594043c0c500305107072a14524080c108110104140400a03942c02e2414080b51103104011600d40f1005805800a05001d40f1f8003107241040004211110118055a202a106503566013401607400900303001c2e14251808110f951380031624550b02101c1594483c103c0d4500e5000e000c40c0ba281e00440b04840068004414008a00341c0c1440c880702c20555440040d07d1070030030015a0107481034a000303503002c00031a0380b600b062100d501c051500182c8540d00400c84064101215800703601c5a0032180b0650304419900c0c85800306a4489070003440c0d0711a01d5040922880a40114055105800084c440b600d07081440c4885600c2c8261700401c4104107070707040c0d90303000d01c2440306072403009220140400755680c0c040b0041d0383c06059012405015070044440d1040c4514021a854001c0fa40180c903c0b90140025500c0c0d4009600ca14892601c140280001d2045540e0920803e07291819940f004141041100101402c5079001900c0505051402c81d4003030168488a040d01c40907 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 134300161 1250 134298911 134298943
    0xd02090a0b031e010606021522081303031d0105042306070206030103060506012015040203070f060c031e0905130902040204090f0e06070e060a09031e030f08010503 72
    0x10101001103410700ca943c420340380034031040c0c60080e00d00140550244045070b071aa802d03246000c0d65400341d44a9002c059411181c0f1a54505400d400c44000802e5600341c0e51151203003a00d441d00d4040b941c21120490b51099020a007110002e4450010005d0b1060b0b480d1000d19000f0320b400d007803540400b0b18039204900c10705007d07a80e20070002d450b22050101c40b20726400410098813580e503072600c4005040c0c208c645500103501d080700c000ea50500e420b01c900310f13070700802c010384035092024000c81a1658020400d0f030349031051550001c0c0c20003500192502410023541c80610704100c50601901c03d040072141d100e40007009096007039100360300030740400c1519030841e901000710580410400107071030f40e2880a035002c0d2000400080b4004540e202000d1100302d000280f007042c0c03421a500d516850304894280c0403941c40c003942e20b140d10b0620b0081a402046062600c0340c0c0d0f80704d03142c281f09e802075585012001c000b202044030502d03800c9001c443c4102514a080d01c1c0300d40c1403e000c243c894002400740024 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 134301411 1250 134300161 134300171
    0x70309061103040e0423210703050d050a02030402010809030702010905010e0301020d050c130b070b0f06060f0a080a0605040507020a03080919150b01020304030c03021309060e070609050d02090a 85
    0x52070040c81242c0040c02c0d60b48582000c4c0c04c2c1820003594004e0b800740f041c00c2004411600302050703000402c210342c2041c94a40070120a0043c1c40d820002c9501c581c0c000c41c00c000381000b8001440c4013900c103041c0907089904006860345880c0c03001500d0414060701001c9250b00034000100142c0c1d000204000740d4400786400381c40385a0500c0070070302900031200300700c0f4071601b003604001c202e01491000e81541071040700d2002041e80e0791040218030b4031030040060800c00c00080090f403860262503081ea04400003030711a034036001d8000000103054201c1504040000c65038810702040041c1ca0041e43e0240504440400c4503042042d030203542c4065100d4000e040c088000c00155204c20305000d101000554010160400466031130b1441c4117010107000704948502d0448441d240e0b520001c10360b020f6030b50005104132102d04540802400c0c40c00c0300451000b01f40c440b1040000240707613010b0803505034459030050020605101000d040c1c810241c00150140c250442040c0259880e40542c580000c401400050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 134302661 1250 134301411 134301437
    0x12120708070f0b0601090b0a0813030c050a1505150102100902010915050705010e010b01020304060c05101e0b010201020c0a0609170301080f0625050a02151302040b030307030906 78
    0x48901400e00040e00480d000c1500310280b10b0001d0582c4c0c0f00b10000d80e11508030300e44602c44c00c50b0314003a210762540020312241c00500c2c500e40c0b088400114601230304000c00404460360380d0a1038031119003400c807a901c08499454110882c60301540d5003144d899034440b0341c1c2112400001750f966a45503901c1130003544840040003035900800c900c0700030f01801d00c409240709444000203482540240030032122580384c0030340d1060440c418803a00e030303500724140c0c041c44c602442d100d0111045500c2c21000d031558041c5d654148500d203281e01c124081a034170401440e59501d0039603454803ca0b0341d8890b0b020b0645e401004201601c000c0403a915a003140d00000c001004a998184548803401d64007801c0d05014001002040041c2c00145c03400501040e84102d070982d40d10b6038070007115080d42c419a440501600c035400c800990055020340300b40c441354411038080c0e0340620000e400a01040d20384501040b1180305420035400c042c000c80703c01c49410f0300150710b40b500c195002040380d400340c4180020800700310b281302 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 134303911 1250 134302661 134302673
    0x1081015030b0f13080f04080c0a03170307090b0d090302190201050f07050f0303040303090b1501020619020d0504110a0f0509040209040c031406071e0c0b0a0207051218121207 77
    0x9580103800c4500246c4407414207004164662044c050b03008203103e011440411440d01c2c0301ea4000b5254015581003c08021050302042d6800140030700052203609034001c6500c0700e20390094100040d49000104420790700342000303401d064441403524005510841c0e80310250360000216102c00c4551280d040e600c0303903030b82042400c007007102590460500000041c401410b9041e0002c01d0030710b00507079284006481d03444c1d0915507149480f0085016030048000200070315003c06810655003a2240e003d440e020511420f0812210103c40494103420503240801e91424452807090241401070200c848841c2400c0c000f801c0498002c3c402442030000760005020081401495802180d1200a40c080030310820081c2e81c039440700f00c0d5064000307894440001000540714120400d00c00640c0c45044288503191580c01c40000001c00c4811110b07002c010610000b42c0c100460300300040117200c55604e41d42410405c0340c00c44c581c2d0f0701c03503441440010075030a00070001040c0c0d042c045c1e03103401d802580c45480c0d00c0c0c09 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 134305161 1250 134303911 134303941
    0x17070c0206030906011a07031b02060d09150509030c030d090201030e030d0204030611030112200a0611070503061014010e04060b0318010c020c040b0f0901081015030b0f 74
    0x80d0003000102c1800040d0100041ea941601c001c0480340d51056070002d4286558040c0030005000140158404140b5008009440410314000780003686841d484143c0303502500c0903803004580e010318520042c2d14140070781c8200d90b0400038800207103180128041e0315036524000c003214204000e54883c0712100b1a8045d86c011742d800d4a461081d00d0b180d280c509000002500b052206032125401c092001281105040c1203905803a40200c3d222030000302902d03015150100403602c3c50340c2c0385400407100400e550741a451002017116941e105004669403002c0c6090541e0384d4080b80c0664030a0303081c0411a040200032000b6900c888442c2145420444012030703600100100f0b41c2d409c58605507000ca000d056400c025072044440b02d00703c542d8440d440c00218202e40c0d0a00201c0d0058010303103505050f5280c10380140a45a40061548100c5009203000503030010342079000310250b901514000701c0c3c4001c1c5005040f52707206d00395003002040b40b941d01d4210403040014415200320344140c0008030304400344c03820 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 134306411 1250 134305161 134305163
    0x301081b040e19120c02210c120a020102010e010b0105090d0501061e05010f080408041203090503011103011703040312030e010e15060a0b0906090907050c0a0f0312020a17070c 77
    0x1c544440d0207003d1001e0302c03401140c00942c2c1408a9821000c0041e0180102d161280e42c098030307001c42d11801403101c1c082c2d90b404c1d14865215025003035001d1040d650350401c0048003101440a80300c5c54a05100190844042c1e00d0005402d0341050811340041e07800c075050310700241007502c000303881079480d1404900518460b0044074000b5001c2c0d681003200c042c80b686041c1a00c0003a202c24020410204040c1e032300e10012a0b008104140c02c00041c8073710b454000802c20030740d00c20b081c900c03403c0c0c0c0c658000909442e41e00702680400a00800104021031585030064840710744180070750324141c1141c55040c400c0f0f060040d150181621054041d1120000754000309026200d042a5850160341c0707200030902d0303113042e914648200020700b804240e140080d0220741390b024000300800d19195000080c80f00c1003c0c010007007018400305105070154200280401e69004d8894200c01248036840c0c0340142055030b05043c0480802d105001064050b908442c0c004230f2006041180010381d942d5403002c480c0036071402c070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 134307661 1250 134306411 134306413
    0x30f031003050610060807020c21030403080304080d0b27070903050610080714010c021c02120f06071d090613020408030405090a0902090c0307032309010c03020301081b040e 76
    0x2013044101c103030200011081d40c8141d03541c40c603a034550aa00300d9030344c0284900035521400c903400d072904070b024101c1081c4158a0840a40f41400c0d039031b0300d491070705406c1160107944540c1e001400500442c000d204400320281c04440c5003006980e40e014446007896005130800b40c022138035010803103250107206c03140d0080d58000c0c00c44610345000241075a41d01c0251180314400d2050500100e00412200600861410181d6a0f642c0451468017004200e000e0004c1c10041490030744010300150702d400703100d540403042502c01403071020007141c1c109180440050198080094404110410310072121101303007007010440d0418496105e8000080c0003840001940c12001c0c40003c0c0080e007201d000c0007420441d081116240c602d40d6403600680c080d11480c4000075441000f00700003800c0900c845000d90f4100019180026102c2586442c0160701000081e260000f940c8507001c2202ea02c100740200302d5000da186c5815815545011500d591301c6441110741d00390100d056070000e695407a03540c844102540060 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 134308911 1250 134307661 134307673
    0x1101060f0b0903010c020106181116200906011202070302070e151503041a0a020d15030506100e0c0a02031201060f12050c0f0901180603021b0a05030f03100305 70
    0x620000080e8002d440c094040c1d4201268140c40754010322070b590490381c58184188048208000c0c80c8024600200c500c00c14030b1060041003c01d50621404a40d843d21403240c00740340c02e0300d294203608441c185c80c511030300c034010900801c14941d81c0302d07003a20840b001203680035807240b42914059082c1013694220300311110a020030072110030000c100140300c01c035050301c0d155580e4005403440c800c940702c215400b40490315070400c00c0e42144c1c0e2141c0102e6211748000fa006040c40240480c40d0140c0b8021503840340700d135090784070078030030700809224031a040703403404003100c19040c078140840c2d0707001100034100d001201d4081080c18020b07000b071007154604215528049869a12444003a003038460018001001484030b181d00d1082484501c122409010848642802c2840801c41c84500d90b0100201c0c504020b01c441e00d0234000000d516080015054686000d0b8481c0c06124103c42c071034001440d501c1c0b09601407104074002c03403000310464540000c1441c01e90740d01d60790064200409810b503440141644110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 134310161 1250 134308911 134308919
    0x80304050a121a041b0e01050d29010602010606110c0f10030216050f0118081204020616050d030b010e0906060901030204030b0702212a0106090e0309030d0201110304031101060f 78
    0xd10021141740c500749101402c0d8440b4040d20702c21000340251500042450320311408035850641c0500da41c0100360114515008030910741513260303000e034411009030707440342d40a000b425080480300c00f501c900d1030020328402281400087e4805403003081c0c5e601803001c1c400318841c0c0310b1081d011030300c50030804d241c5d00b000300100f880d1955036040ea4030315000c9203520384020729815018a072841007e480c0c00050450619507074942c038a0322400040c004a034450340401000748600303501c0c1003110290303022f10003808a04020100140030340b14900c1c0560f04002d120300318010740e6956600680d030850b1080d9240307030300c80440e000107a00a204a420149c542540c0c1c10401805a900040f02e00d1820848614140380e00e12442c8100580d0180c090740d82c1013500094440b00b415503681c424840f440036820008541d09540b1003200c021280e0000200c4240e820000300030310300d400c0400017a071910725640300800c5210308801c9501d6240c080948014208690084451080d8600750491400740c1080c50700e06c100ba80e5a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 134311411 1250 134310161 134310173
    0x2f030a0e2b0b191521150507021906050403020f0c0a09020d0603061107111806280609060905090c03011502010b03030f09090609010303020706030e010e0106060f0207080304050a121a04 81
    0x3013440345c030320707090011701078030001d2030007102c034142041e60088001e054050400d402c40c2c09060001c2494086210342042449101220100d2a00c218041e500006040c100307410000e0400b8406034030042c5941c040500e90034030b902e4483da000b0488510b40e2005844000000921028010355480684151b0a201b0510380300d9628400900310280b08000740c540440e401418031a82ca25030b0703000b4100101c4d0041c0007503294108860080310361a0140c14500c03103400c000002100e1410150040d00c00035520480a1129540110310072000e408102d0301e10105113414a004400c0d0f200500a2200c0740802c44a0344100c1f6000750804002134000409503511820281e60302420740d003203004141d06c1031072500d01184680c00d10082a6059a4041d800b52030710b1400c100d0f06a014103039015510807075658810742a20203800030f200d10000f070006a96402c102d002100d80c000e28040c40b940040e0302035041004204010741d030710b00151040f5160400030380900e52081c2441003030b95183d80c00602c800e034144003c0008103c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 134312661 1250 134311411 134311451
    0x1080303221203060f0f03020a03080322050309030c030309030303040320061f0518060103050c130b091009060e2103030f01030210020d2f030a0e2b0b19 67
    0x140845c440e07141390f94807000c4031007503454400a5048030403520309202180d100c2c0c1c01103610038031001940408800c1e107801e8400c012207069054410303400200d8148000d1605101d00ca075400f404070015414868658002500c03484040c000806001126030500f461764034980d41e500300700b44070409844143c90140b91164032031410022240151801407030100c1c807032400c0903800303500c800d40a891400c07550300c10005400502019120300c480307040600c2115000c1c0e00c1c0c00c541c5c41c007070a48a0803441d11150054240301500720044040001e020458200f4000d0a6100d0250028404115a24207010341c061494200301c85443d1402c0b030150100008121008490a0a40e03040780e2080d40c68003d5403681c140c0c202d0311010300d00c10120005071829400782503008a00921800440d240200c83c00302045850f0851840d40103480c0640416000d402030304240c58030310009a41d1070f4070100c51003918000300904440b80b046580e0000c0c40c00e880c1d5000310380402802043c5040110b016101081007014500c4401c02c0c5071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 134313911 1250 134312661 134312669
    0x5060d0e03030f060a0e091b0103060506041805010e01031a041502040305160b04080c01030e0c0406060f080c07020120070f0b0909160206060d050a020604121a0108030322120306 78
    0x1174074441c00a0521580400540710b043c407440038002d0035104481c14418594150743c4a810152120000310b1aa9120070080008084903040d5010310420600c4030700a90b10140d1007002420707100c1c1d0040011801c1c084807003103210b20b0441426411381e40c0b4540f200440d0000d052283c501031001c2404010404001b0700071400012000c580821544ea4202d0319031184210300941e1180d0b0404d41000203d94004d4000500ca501520700380c0702040e0605021600b2602140e0003400016010f2600340040d98000040170741080d00035842d5480d00d252a00082c0c860b0080a07013076490f8541000505a01000500441000d805880d41c0c0070b0b8480c1d42c9844142842c1c0000028a02ca4446070300810000400001003c0f1080c826801902441d55a0010007c14010564044d681401b5403922180182e44200040010300b6460418021715621810460310010804410f0030301d40f11290018000008004140c0798400c0030035541c90481c15a0308010950011a80c00c0106400b00020034155246e4041d0400e805072 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 134315161 1250 134313911 134313919
    0x5150715060501170712091401020703020c210a170705060702030c010f050f060607050307080d06090605030114010504050604060b030c071428080408030c070302190f05060d0e03030f06 81
    0x1d04c01c0036166401e5200c06664002c049100150901c0001d1180c0c1c0102d5062406810b000d500c3c02d140d01c48190990340aa401100140c10010310600d903480c00054140d5003542e011540613030140c4480c805a5140c4c00b0060151188182030b07440170414201c00c0407185a207521209403411400c0000000c0c1d500e8115410502c020b5081400007880c480e00c85c490385200c2c09a103440140e003a00d8034010300503140d21001c0140c9440c0020003800d400701d070494000b0080080d0804000030018a0000039404481d0950460b62180c0d050030f1304608403004255580b41036a108490010749920360a0018004008a60283d4080540401040502e2079a6009010f00500499410200e5140c42001da5154040c02100e40480f004403444000341c08410103004020394800c0400c41d02d080d40300c07075880d0314513041000b0064080d40302c60020b008604003020309102d000f8142459503081c5003042103a4841111501800d030044a001c200b00e007010300c3c203030000b0036000007030404d990b5a410b01500c0200002c508550943c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 134316411 1250 134315161 134315177
    0xf2b060614030a09020126012912060102010b0d051006080303090a080c010b181b0f0d0b04020409090b2a190e10050705011d0705150715060501 63
    0x200500808048900d10284440c861541e6100f01c1c65800401300d20809170b04029100c890490740d49160740e1481d80d0a549144040601d40c50304000d4103009510001c62280c12a200c0a14444d2185000503140c02c800d061503162042d44d94880103d0040a5240000340d10403500003100c000c0c041c011900c0d0130200b201801c18030440c3d07103603d02c1c266640710580700c0080340d0313101c82d09404c0840d200300c000d41625210440045803031480341d40015103481c81a00b001012460305420300c00d04c1700010f0300040c02c2e00c980c00e200c0c60a00580c603a180e2040d004d21028240d060b502c40700058201c1c1c0c1d40b50704840c05004c04181c1080303a418241041880c81408580018101e0380c81ea20b64a42d516049001542c080309030410207107001e4649828040401000200d1020f0204440d16114196100340c4030740b6011100b81e8400d07403500001d00b0542d003520303e61316034a035100043c40940400120082140e1003610f60075500340803035403d681d5020417170340308032100074117103014503103648814a43c01d0b0480301c1212801d0b40c440e41c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 134317661 1250 134316411 134316419
    0xf0e010f020c06061c0503120109051303090b0d0e010c08060307060203030f01030f0204020c100203060a060315050904211d031f0c0219060f061512020f2b06 69
    0xc102d1068035502203203684a04005821464250010352403400202c07586000c0c1425952035900c0d680084c0011140c001e0144018028030b86c9500c601e95002032005402405207040c1e81300a013014840740a41c4100920008240c1d0701d0070181c4d08041c5880b49801c0080144480420008058510030b0710b00324460f01505500003041403000064034000d0740c01c01c8001000340d10b19030300c1e1000c0300c1c01180c0483e0019020300040d02c1940c814400440301c2800c880000d82c0d60b00e05102004076400721500146c043c5864180c2c03034003900b88101d1a1005072042a510048103844a007880254400b1814001316a5424900355144d0981c1c01a048202d0440c6076405210140c2c681d0101920f0390718441e0700791801410180c0300c256220311500440380903a454010b4801000e070140b409a05442c1d90801507a0154403154610511000b52050381b008090040800c20742100b0320f100100580d04108901d01141e4000c00c420506095072001c80c2c44175010140040076603100c0305500d00d9040f441c18040d1124a10340a030000b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 134318911 1250 134317661 134317691
    0x130e012408060709080d030209010c0b0717010b0a0801030b1005030708100c0512072a0614090307020d0b040507050604060c03022806020d0f14090d1701051e040f0e01 73
    0x10b020361741c81e00040d158603204c2540440c0250095284c0c0303410051203c0e034000c04a003191301c42c6801070040b60340c0c000401080117002c1200d8003040e07100c41102541045000d403040e0b4400f0070541580d610140034203250701c400c403910221443c80c3e0409541409a06400211400009100c0c0ca1011105000b84a90b40c8030b0030307003510b03240641140400032503010400035107170600c01c2d02e000800c200c206040f031190140c01e2607030f0740b81d940000c0c01c1160040e0750b13013a44804251480b2540790b4412481c0e0300842c0303001240e074003248085050b01d0300284964050400304041000600c0084c0103801c02030540c1ea150781d45c40b030000b06a10300100007a070150180e8000241200d80c150300698890704e040c407a40085080e550356490007540a4800170803441e58494802440390305900402c0021002800048103c1c14440c16480c00d0166410a0405000b950040ea03041032000032001c0d4115501140c921800c0d5100d090307042c1c0200c41ca03508040d0302603d09000034820009980c00300741b02d0044e078002086034000030240030f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 134320161 1250 134318911 134318927
    0x603060105010f0c050709020c07031406010f121a040602031501020606060901140c01021303030809010204062102070210230906040b09011803060902011409130e0124080607 76
    0xaa0b0025101e0f0168060701d07401100b074160038500c507134112a40c0681e1303215110100d0700101140d9002c1d400900c4104123012040030a4144111910040c1c1034551501d07182011051152091402c25113107080e0b04000e00400c0a040c3c001c06180030200141442c1524090b002940b04a4140003482d10025040c4400e51000810364071a90f0003400284c60300c0151001950710a040ba89140c103105010851340749008000c0c00984082c420031280264030b1811845e02614004000b000d102c55a0300c1407008000f20350b44600c009200584172a615181c1003030503142e5601030710400300c010307400c40c1421010501a0383c2c050982d40c2d103010344482528405082c400602014441c9689466120700309000603c42600404024003004c901414003040f0149641d0f0070350f4207a5140e0348152080c5076942d02150540d43c20100481e400c46c07081c664145410180310010781c080b8030843c0d420020a0350b460050345444400d44c051081000c02c42072101d00224000451034070075505000e01d241c81d000f1040400c1145004002d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 134321411 1250 134320161 134320169
    0x203010608090f0c12010906060b0309070e0c030103030c03093602040302060702060313050f01140a0216060504110604030c2306030a2c03030a05060a081b040204080f03040e06030601 80
    0x144c01c00280e04d4041241000040504910380c0d50f9403256030001034034511407540280603900d02c0a49a281c139104050821406502485444040b401084560004181140d042d01e5041c02c06050442850034125128421900030000900300c0c0101c200010360b001041c4041240d010482504140c00300113090103a0250307100c02500541c0511100c001850003201441c0d10408180c0042c4940744180c4800d45040b4503c22175141d50395450104140e60000060fa059202030698070651500503400c2d4480d0034085000310160415a942021404000e20007189210307181d002803650b903d69490341408002400b15200c6d2108410f0560034036031301c0c405818400c10408000608040c02c40e80e4200303070600904980c401c091800d221100f6884170300e01e48100c11041000300c1e00c0c001c5440b0710b0104801c0088070030142c480d0388031701c1c0303a90400c200c103a50001c0d0011001c0186190303816400e142d440850082d0090b60055400b41c016000d00c0b01c810003000014104a441c1851111401e0710b0301810b0584a03082802 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 134322661 1250 134321411 134321413
    0x501020309060f090609150c010608060106080a0507110706030f0b040b091f05040207080c0c0d080f0c07120303091e020d031d090a0c0f0315050f1302030108010203010608090f 77
    0x40040000300300b83c80503180244010744181c0c030b818a883c0014241e00592198800011750200e01130f1600102445410041d04200d0005c08032035051080250082a004003c1414140c8840001d00b50910402c2c440440c40445001c0307508e0702d521024003070050450901b107c030a0a1400a12002e20b19140c000c4291048000c2c00520f1142c480150100c03502807801d086007400407240d4000180d5843e1031004002507400303802201e4444001a00c903c2c00c18070113102091103660590314100100b41c00508990840b503404556035524055600c00798285000c1c0c0e4400d00b10115a040207001b45909604280300007031203210400c82c807980f0358070300b115054617450000e0f40005140d41c282000034007496a04441643c1e001d08a446607002c800082c000347e401b10381c622009070b220080c0d04001500038828a840e2112410244501d0503503503840e0f11118135a12525100c0c80c5040c01007862501c07200d1501c0f0102c0044601950303a50703111703000355020794000e2013880c000038000d0300000c4000c0404541c104101000c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 134323911 1250 134322661 134322667
    0x512060105091c0809090c0304150209030f15041101080405030405040b180907150203090303031b04050d0c142b2102010b09070f0816030207060507110106050102030906 74
    0x28004407103640108000503007216038012030300f0680700410114070030b2034440c0e07400e40e9036000c840c0148000c002002e0038000d4440030910a0000140c610030304480410010a401605d881451340005d00d4a001c0d00c00d0f024441c00f4000d8403400200701620b401e44131318060381c0e900210304c440b10011550601c3c200d50160068002348000d2246180582000000c904000d0036a6880c03a03040510903501502a40c0415040d4421402004409862801103a03001004d001850030001e180e40441d44a12005240c0404a9501682d1a2044c0070790301c281c0c2c01800c0c015000c00c2c500c108a1420f902d00c000c0390300682d484203190070510941071030031281005200103004c1080c081c05115056201300000404000c0364a250b81405214030310310b914926803d015950760011902c010b02d04240280018050002c0c0100610001c070710002d40c0d00710f040e02d40c0240ca54400d50034511600c41045000740100940100703480d00707040a00101a070300c601c01c1c10b03a001e8002c00812a00d503072100113a030340c2d01c180a240750b08501e0038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 134325161 1250 134323911 134323921
    0x605030706081b1201080307030806190311060c0a051005060d030f0f0309050d1211040305030a080403020c0a060305091006030506061302120108010203012102060d02070501090c0b0405100512 84
    0x1400e04009180b0181a0b444d082102c2c1e9901c1d010403c0b401d0300054100d520126411080c1680712032640e402040c261000e1569034880720a00c080c5040600010389840c815003ca00099140c0d00101c0701c0c030044174401d5983c5074005150458407045c071040c1140c00c0c207041c0800302e81d040ca0580310020a056254070758920110440302c00b941e0403c403980b03001050643d201588030200e54144481c04d01c0209030fa5944181c110000310600c01c40307000201c110240c4005101c2400000c00000495507444054240801c2c60769441c6022840c01c907802e660550060782c050b0f4001481500360700003c0c047d6404800355101c0c41ca0181b14401104c100744400390003a40104040f0340b2034140b103080030120603034021016180402840c1045280e14083e0b00007001694000010031403581c0846d00d14198035458400700c0012901c0c3d4000036030038052603601e210301543c001000010032600b548803c2c3d40b10360042c84050415030303440b02a859500684205805412481030403440740380300f5000c031003110b2082c3e00c0c44580f640714 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 134326411 1250 134325161 134325181
    0x3050d0e090f0610200a0c090c0c0804090b150f09010305090604150c1106040b01050a080d08040602030604060302040c110f030c15131a060102010b0d0506060d060b0a03080d060503070608 82
    0xb417407000350520110649918110401e001c000a03040c0286e4000c0e05080c07628106504032000040444100805500008006406802101c0031152064000b03c0c7c03c001c000009841c2491200d003072020100c000616050008006010341a00a02600c080141e0342d2111265610b880d41140c0041040617002880c91034940c040c0c0c040d51030074610f1b1030800c03100c08040c58154075124041e601591901e4900c801000145090060b0002400c0c003500a000c001100940240c0b204e45c01030002007a45030040b00044841c2c680d60b101a00542d001002403160341d4170304801400d062045030302454140920480ca07809220004105c3d00b10880c1000113064003641c0c41003895217000080c2c80c290756282d901141030081090182580c03a0300ea114410301109082150001e42140c0c64070000c1d1b406070740070300c944501180000c2015603000708181c07180b100c884140d00d46030000b48038055005a00c20708609020003842020750140560118101c0108100c903103640803d0398820440c0700c3c0000181301d443c00940721040d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 134327661 1250 134326411 134326427
    0xf0c031a090c0d0213090b010e03030d020a03020706110d050606030603030f0903010902030319020c0307060e22050705070b01090b030a031b0f1202100b03101503050d0e090f0610 78
    0x111110381d00c0d00b0f210400e1141c3c0c003641e100300100801c100c0886010311900001d44105080340d602420841d01e0f02c0c030407902191322400303102d40c400300e40d960100740c1c08019070003901181c40c1550f2001040125850860402005400c43e00540d46154640720001e10241003080403607014240040046041c0b00074010030300101d52110b507a03140c05540b00c902040040e201080582075105407542410000aa40b4600900e058000c640d4a8482d40c070040040102da03401c41c00610819a0550719900b0f40b00c80e012500038082c40c0448421905446c0004128034950f00001805195105155040060740c0c0d580440c01034420740741100354035410521501000074050000c0c1e0150185c100e580001002d100d4a55603c076160b00c080a4404c41c01e4244c0c402c400ca90b05020483d014004000d082054500b00408265180c05509842141c9661000c1700351040b422079507003100860b4000221a06442903400084c81013000d940d24034002c1c08184080b6803644035102490f0710940014082454801c1c0b1a2005c0310031003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 134328911 1250 134327661 134327671
    0x114040e1f0b01020f1603020405060d0b040606050109050a03020612130804030b0109050a0905060c090a0305120a09080f030f07020a09050a3303020d11060408010f0c031a09 76
    0x12094003010102201030703141c000d007500c51802002804880490002e03040c0040c401000c1c80c1900403c018131015208401218103032074040d180011140c1d80c0750080340b040d800785200039204000755000c1004002d025003000050b075500380d80364214180d51301c090051003070640c04004d41c4000244101442d00b041812102d6000c01119000b241c03a120a031640b164541c1b01d5007040d81d02485090050000b41071501078103810040da070f20208610079554985907101d01000d0035503c4603860001d465043d0765241c100d41005550000c0c00c0e90701d81d005940e00b055403940540464400f10b590100000742c0908007094147c0c0c0b4494040140d881c00c0000018170045a004140881e0b008095a0300864800c0c8544a504e10410900d440019242203100680450340307042c11104207103080b440c0c0b100102d1803010b2400d500702d950588559092150740d290048641103030803480790300a100490000b50100c015000005500c00346c44040002c009140c078101c0541d40c9080203940200041000b1042906010740c21035402 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 134330161 1250 134328911 134328913
    0x2030702060418060e040b0412020f031803060c0c19170d090605010816051e03011506030e0706050405010c050703061a0f100c0210020c130203010e0703050114040e 72
    0x410040d50020308035030400d41181d807540c3e805500c40b00c003002d894464800545020b0032003040074602075564010076030300140b004245098004500d09454020483c00ca80442048142da440700705154003a440d0003d0074182070701c20b00c2a03030045002c0e4880c0604131f40032402c000b00500200e1440e580034100c14960400c044907081070400942166000d0000503008440f18294003185414003418405c0030b42f2010703003140ca5940c100b43d00880c42d1014660b00d55040b51810781c0c180321201d02c4040b0a0304203070200c040340c903015421315003500d030504d00500c415000d40e1600d0300c0400c0000f80072140ca940d5100c07a4022040810800c000900c030640c040c0344105d00c0c645c414000c403500c141d283c1da2920300742c5048444010081c07510024203070032403401c6904800c0106059441c42201c00b02000300800c04240300701c029000349031104d03810101d03910030b000c040c07642940030f0400440c0d8510100b10000070740c0240f0651307054504410100342102d1003070003110704890070050140c40500c440810840100201d8200d0692 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 134331411 1250 134330161 134330167
    0x1050d030c05120a030b0f01021f060807030803070f0e0f09090f120414090603120903030c07080d030507030902090402040507020106050409060c0306060507150902040605040504060c09050315040b070203 89
    0x1007081105100d640450640c80e80c031000c03092009419106d0b220003151083d111440c5005699900042d4042001d001202001c0c00140c07012518009001d2038000e80300d0b5001d851004410b0020940c002d40c0a414260307107040c2c04074414802102c2d00100c9038142c6034000d43e000d0300902e09150803000280c001c07038288107031507400313240f261424504068040786440c0350303c0114040041c81920a035840850b60195901000c5150100009032901d652405094550501084e40a040c1e1410020f0f104200212400c8880760364445840d82d0791140d80c850a03400003403d000020f140c01c0c0c82030150719007c6074090328517101178030745034208805080001c1038001150368803000041c031a0f0f540d0091050690003040001000811900b0007025074110390040b20510904211120000e02c40445500811051038400285889540f002a0142010f80e0010741c6c4107040005120511566034420b5060b42d010740c540421995a82d8181902c5102c0c55400700d08121307005000074041008802d01550010451044e20b103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 134332661 1250 134331411 134331413
    0x6060f01120c03090209070203120a020f07120305040204110c030a0e03160e100e0106020316020105091302091f020c010507050a02030303011805010605190f02010b090a1a090c0301050d030c 83
    0x4102e4540d08115000039495014440c15428664941d541100031440030b5440c008a540d405031a444020b08001003040d400201107007211900380955520726170001d5618038165800f40010042c000c02d40f03050303104524003881034083d00401c000711012250300c58007850030a505423405450741c0301a882c1c202c1d00360043c1c07100c2c10100d02000580c91b015207c0c407640303070307016003010314036895031f0b4500d900a01ca40c0f000220043c00b0040e0004160303588a00c100140c40749909040c40120348601a0304821504603445154490f09070f1050b4000d44001d210584041d03540714080285202402d01c46441100542c11101501940394810300c000c2c07910344e02500444480d41c0450340400c0c5940d100341c2c03007034820060006ca104180c02c6180115401407000740342003400c141d070b039400201e100700f00d403010704040c882054140b0440e01d0003034002c45100580201055402d292204810010300000754001c00b8001410b00214a903140c84002d041c0520391084030241140c2c00c0c2002d010121080c0e02c1d09030309100c0490360542c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 134333911 1250 134332661 134332697
    0xe070e060121051003031706152101092306090117120f09120705100305180106140103060506070f02040c1101090c0e15370b120c0c06060f01 62
    0x601544413000302e003551074694200200510650090740c103011800900744000341e0f54020641c0c4c1045110340030140e43d00000e00d02c1d43d80c4210702c00b0030b82039000e0b52803000181d03203203050380302500505001900b00c082c0001c81541c007440c294210740303041e40850f8902c014011007240d10881c65000c0385030002c40c0d0290f0b8559515050b0380c1c22815070780d070240320b0010313080d0000d06004a200c9292442c00004045007030030140010b15100040040c5030400d0b0740d80d000100c03000340d941c0c1e83c0907035080a40020040c2d542c942880d501042c0d09202042c4c042810300c44000354508100040315001504000702030100000340e401c100103419007005030000c04c01600c100d200d03190020300c1905426442141c1c0050001d141059140011500400e0200280b5140010014549441c080c4804056001000404002b0b001440c4411840c010080c0c06003841d44040209682d1540c10051400d0546010000129901d000c0420b08501c45c241b0320020171b41103800401c20a050490102448010504104203c650503039540 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 134335161 1250 134333911 134333921
    0x2040227030609060402060a031410150e0102030904020703091e080601060804050c040f150b040e0105030106060f0311040504240603020a02250803030c0c010e070e060121 75
    0x340c44491030000c940081015110a0040802040d0050009860104412602c50500820182c0924000610380095a120390b008040304c40c80640b0f9442c2c00e003428541490f085440c2e00480e1424000c0c6800700302e006010380103018544805a008510784440705c801c3c4806500056412000c1c04405007011030b4500c0608440a8815a072018a2141503e01a5a1803034540180d02c55000c2c01105010700c00400e00100f400304003c02c0599001c030b11301e00002c0a038002130102920315900d9808451703001c1500c805250082c030465117800c0300a819a602d50042508035030f618480c24010854403103100070082d020360071500004541044060070301e9640d6020a0640700c42800d84000802d0300015200020300c10039401014001c503141c114100300000d800a907036410194001081e4180b100702c002140401c0c1c42100014114050640c4d46a00304580b04405071303002403940d024a942442880040039000143c004121855014040c01c280c40318030040d1008998a0090340800300100c042c1100d0103903900030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 134336411 1250 134335161 134335177
    0x40e0a0510122612100506040e070809070315021b0706170415020a031e1104051909020c0606030d020d0507081602040e061f120209062106010e01080f06070f0903020402 74
    0x40c80b049460560f4080e003101030b82d0341100c0d214030005d000c10310944c1c0c1c14041a0b52b104032207090401d415111030740d003140380480e6580020240002406001c1500d00c0e59000703410b10341c480c008600f50050503135200d07a844590034051000090103100841405007580d152480d081350241d90000c002085c414100350a9230f0066030a08080703500c1d41c403c85030301c03001c40c0000a61002c46880030051040112a00f601c6803165200740ea12441d614040c06a085010744c00c0203005207820b204c11542d5a031b003000c065031104c0302190081c1c403d020740392115400074004109004400d644c4e6844514224141c1c2e40e076078040d0054000c12040c4504a260b080c01620b0340d11810101e501040020a01031030001d106000611402d00240c140d0050b1030410000030b045904c5211072143e0484900c80c8507900c403c003050480080420f03814001550703104d50181d03000d0201c3d800c1e0603240e02103004009686c944946603038a030101800318142c1d0f400a00050086031240b03050410210f03081c607201a150b55603400150a90b004031107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 134337661 1250 134336411 134336437
    0x1a09060115031407030c05040503060411040e03190305070c0506042004020f040b0c01090b160806060903030d111603030609050115022a0402040e0a05101226 69
    0x18041d0912401c1803281a031040c0c035050040304440361036003088400c040d029201745622006045d80d500e0048050f0b84c05003601074111440ba15250070040c0440e0385180030103002c0d078503000404400410106c1100e00c18a1403a200f0700840c400341104030020b1000800a0003003060a09400d03000480512007a4022802020324445541044081041c205c0114104500c9284100424010070041c00260703422525041e041d030361a0b4210040c90380c0908030340b99000307044142c0c1400b006882944841044048060b0b0750750303039001e85e407a0000d001c620710030598640e506910500072f01d00d0112440d0001c0c9000c003040302d441ca00300741c0c496004804c000e1100e801140403e486420500c54150039200c0c4600400440c1c2401070241135801000e9202c00624040d00f695a022a003410700000014014460380b4101800841d1380d43e40c0c0308181d140c003410542d103180c001400d1501103014500340d2030204041d60000c0b242140c990590b0351b501b1001480c000004800d0900710340100f032040c00b130381c00038082d4610380034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 134338911 1250 134337661 134337673
    0x50705090405101d0a0e0303040312050603060106090308070f0510020a020c060702150c12070804050915032d060114011b0b0a0b04020c06010b040f05030a1e1a09 71
    0x203400c01082e03600041c660300b080c0c102124100003020480000000b8400c0030a038044803500d4a07401000502101c0d10420303000d200000130303c0101a071007404408020402003040010791641010161103900c2817043c480091149881071000c103100c0340003000c5280c41407400703045004d881d03540c0d42e0601510481000386141d000c9409054030703405001900341406c044400385d1030182d00340e00088010804034031904030540c0100d0081c8600c1d4082210918440c0d50a56281d244c800c589490106d5034824002c80380a0341d03942000c01d10b0600d031120302e4040b011008018052203440d610710b4042560222124145c43cfd450800881e04002013031080c03a019210300038403070b007a00c2030810015060b204120907458010651288071030100d100b501801d0b400a8610b00c0c00300e0341811001c0041c01030b00890310540000d0080f000000b6012902c80c009104880b0103222035004a96604c0415485001c03a04026200714108440e81c4401c60300700c542180d41d94420b0050b84070b0003411884492116400f2110056140d00003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 134340161 1250 134338911 134338927
    0xf0d08011719030f0224040606060203030709060513030204050f040515040c03060510030206030a0509010506030a030207050907140a03020a08060a030f03120608030a0203030a060e07080c030603070306050705 91
    0x4041c100124030707021001001411452440311000c2402c0b0b040240c100301207074110040584c03080c00000d85000f100f003950a49000700c0002c940108600391030480e001c0d031030b02000048a500202c16030f445840283c03108102c00303140000545144c1d2140c0c0814650000b40c00c000310050f0380c0c500c40d103406020384c8600100c82d45802d20f030241c45c080c4840080300991200000f000f00003010100c0b00b4080e20f030b00540c041134903103401d680034111b80301d1604001d501c101c0110030440c54100c0785e03124900c40c000076002403190744c403810203154903800082c00c05001038001c140140102c2c04c10803202074109000d85416142000d59010025440c1c02c550a0880000d4001844000050780301302c542e07030416001c441c0100034a10316035503640c103075181d0403008090080d5640000d5210380700d5481100100445800e6942c0c2e0b8044c21002900e070f0344103c070188601803416002041c082204c00c0d01610645198071540441c0d15245111640d64000411642e4103210f1441d01000044103402418090751498642c00c0d150307001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 134341411 1250 134340161 134340179
    0x100e07030c09020720010c200306010f0b0a1d0604080304030302060106090b0a030b0d050d020703170315090a0b15030f0a050c0409020a0e090414071d070509030f0d0801 74
    0x3040e40b001c00598014050440462200c03090b11402c9910040001e00c0751034850010b80348071503080300250808142c41183c2680d1104140710740741c6035004900f0745041c0d07030700c0700d6068030612060b02407650400d40921a034030400d4000d21360030301e5030107544801640c03031400c031400140b0320740c400c0d0008109504003180400805404200340c501400c0740341072181c0c0390f03400d10400c2049406152420300030180c0310410301c94030f9218006801074440e04603059451004103000044d5840b81c20f4402240c4540c1305915800702000500c0079207009600b5003a4066000140c18104201c12030050b01c004601c60341c50108a070f586d5114014200920421950541c6030326048110861900004003a019002e080004000304804440308880a50300204c600503290910300c2d404542c07000c3c05908141d08000c0c904140414008112490050038605034106c56041d501c4800d0401c40140c0b1403403907480070b20a2000300b0a910300807009000c07010390150072920590050903866107000b07207407501140814041c100600201c50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 134342661 1250 134341411 134341433
    0x220b0106090f060806010c111c050106080f060609010611101b030c0c020d06020f0d05040503090301240501050721080405010b03031804050402040b1228020d020111100e0703 76
    0x7850501d842d045c03520381e001802c080000400100030300d00c4c2c1940ba44180c1c1d83c590860400c500e40300c2e804100408140380c680c1c020b161600403160301e0301c03402c0d90050802100240d40380c031429010f0288445a443c1020a90b040ca6000c215688140a012a44c94a0410503c10030b42c14030110b0b8818100f5003860a405012180b00607071090820440c450808050b0f11559400100d20303070300400c010303130300e05c0300031000c210030f000d02058000c3e00740c01e2500748814840f0000240800a008400800100d5500c05e101455860300c4100e000303080c203071080204490f60251001c0d0849d41e0080d032012240001e116508180140f130015100c0102c2c90307520034041400024815a03140e454164000d5150a0013414100d104007040f0210b541701e50340b108000b40c110b4990381c101c0034285c075000e003856901e128071140807034980380d60302060510001c002584d00d40d001e10034503242110036009080c0205c0f2101c40d4004480728000c91811903c10b00c544040c00483d50841c0c4240c00502d41d02c0d001070110f0300c1c190711340420103035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 134343911 1250 134342661 134342669
    0x40f0b1201060518071706030c0303130806060603040c09020f0f070b091c020c120a0222110301060903020108060a050a0b0c07080c090c0a12020d02040311010c0308220b0106090f 78
    0x82c001340c20804c440b60400000761030700c17482d9411668982e0702c440020381750140c412911501400045440d4007883d042440a00c19070309007500b903c0c1181d80c1c039400d000ca94081140d018111041d8038004004603400e0703070f0041c682041c81054151804000000da1101a8450a41111024009400c100d2580d00c00c0c010b03000c02107810700911500609e41003009648800315003526100e42111013003040d80460401911031120781c054285818011b9000d42810806c848114042da40c6040c40d501605101e2048110b9042e00c880d41c079210b2000c3e040d50011500c000000342003d802171440e82c00400c9950300da00c548801032a031084815621508908140d0800b0029031046078507038040c00c281c85403542d80c200301e40e511803000080c0a455039251082100da14403000d00c00094940b00140000310480c1980007082500d00502e4480a41d4007000d0044402c19401c940c046c0010380c0d0f100103d810318016094150503110f04100340e980003030710758641c2e04a0120a902c49000708000d0501040340040581d1004020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 134345161 1250 134343911 134343949
    0xf0308060f01080a0c1214010e1005010504031e0516080d1b0f03020a3806010c060f060305030309010b0108071806030908190f0905030a020f040f0b12010605 69
    0x10307621401c0040c000c40f0028096094480c0c50b00035903e4030b81e10030f948004103529503250a00206c0b84200c00c43c2a001c000b80944102d008444000074940d42c07507100d807482154010b03914a40fa0600d103440301054040400000c4040821000c85003000c11001c102903000d10111100d00c0740b42d180341c079004601d00300c4140051030601200c0302240881c00a1046201a0b42ea0010062002d0341102e2804a082c02062030000308503480628a0200c003183c409402c80c01c0c0d146101d94034500e1030324040c500ea0b000c00c088600d54009035440b03e505000400903040300d100d00c01602008142c082d120389e1101c1c00c68100701d491021aa540d00741041d159a4004070b01c94200226003014402e140c110301c0c01c1c40d4009043d000d000e0a06440d06a0101001200c0044452084800c51044504842080002c0990502d10280d00002e20030b45000309507403801250389800158011b1501c01c0d400c81c0c400601014100881200c400c2541e55840c013407c2d41c49092804412605407000001c04900b070004002041c51920000840 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 134346411 1250 134345161 134345179
    0xc010c0e130e1209040227030c04060806070c150606021501091b0c2f091f030213020910080412020c0f0603090f030f07210e09040318030f030806 64
    0x20542c004105400c0d41c03400140c04036550007042c00032901a01c1000000000c0005d40500320045079541945610aa0300480580b401c03049407200b04800e8800b1401241d1042e0009000f1030090f82c00307419038440c041e11440710401d1032058605103604542032980000d015820040b4109092640118070601500e0500c800b08030a50020400358800e58050004c2d0062240390401242030110300403840a0941c00078584600d0007a4140d079012840d410012003d01450042020841102c0c0000700703c44905078400002c5101c0f1308d143c08015811200c0c40c5d42058165080160701859200c605002180d00080d40300d0074444d050500c1e1241224404842800854009030501403490382c404241500e00042118050303266110011021704142e10703030100300081c0c40009414200104041c0c05884024060381071513001e0004c40c3e95000015040b400910000750b40c00d241280e45182006105821900914111149119420440207020a1a002a900c0d140854400010103500020300c0c0e1307200f0020303102080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 134347661 1250 134346411 134346431
    0x1101050606040b091003020d09111801060e0607060207050102040b0c07150c0311030c0703060c0306060207081905070e04050304090c0309020904080f30011502060a0b060c010c0e13 79
    0x640191001944104080d00417441054031a8040d2160b508075104100700c60a068a429003042c104510040e01a41d458002c5031b20003488288241c0c1252410303110644100c107010100718465120802c100d40f9260300344450000315800342701807c05800041403690356280610655071401c415540031704048442d848185080700c1e40104001c3c0c00580c181805140700c014011403900714080e040056401c0d03c2480b80000c01c1c4546a0041a40710720395882c104110381e12094100d8171205503000d03510041e884100d8034030440c1040251f140c0c1d0341d4010b400765940707036407940c0102c0d07075110080d102910543e00104040c0100c0005111309103040c842414200000040c940c0071461210700103101400c0a503002c1112002c0880940c1200d826103d4410341001d20070000c52007000c0c1c00c090381010003468110800120305a01c0c55020311080080035001041d1544e94044a1005000c402d00c8070b903003104e400d109500c000c079030901604400340d24070b172584005100b0a10500c07203030b00014200c0e0140e0508241d8829 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 134348911 1250 134347661 134347679
    0x30c160314060106051c02070203060a061a09011d0303070b011508070518040f060b160605090106080a0609020a0f090e0f0c280b0c0a0506010518060f0a05030607110105060604 77
    0x541881c8020811101c002040d02c06c804c001c1c010641c0107074140c055203080203d00140b640c8540d040e02d002191403070342d0b80740c100ca250f1418090b1003440c5000c82c45006140c45038400032050740902c02c60040440b490203d85a40c1d01552683c01c2c1d03c00b5001c0000700024a0581e5048800740c0ea000d002480e01c5404c0c5410207178100c000031804c084040c002c03907980c00f140c20001261781040b030281c000b564034255150031440292040c1c041491068075501c1c80c10307001c43d4034850180071308001c40d501c900040c10595000d49903003000300500c09041303905c8801d0440000d50b26203000d01c488001e0040b9000021017051406030395040c0541d81610006a801020390a003c071b03a6001a1091480355684602c0710510001c0c04002400c9400d800ca0100500c0c0170510f03024852000a104542c184120b0075030700d0607640d80041c0031011050142c0c803581c07811581c00184950803c0c2000e01c114580040942820565810119040000c2510800c2c0021060346d80103030410024010183c100006441d80c030714047c0340850f08 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 134350161 1250 134348911 134348917
    0x60e1c0804060507172715130303170403090b0c010e100203040b06090405030a03020703051308030903191e020d0b09030307030c140d0506190608100e040b0a0e030c16031406010605 79
    0x10400f60800000007a0b05911001c400346208494107440d117503241500745070280c48c80f14511007100000c071310001c907080003518000454056903040d19079003c100d041c1040b40e01103402501101285640c0c80c0003800c005001006504191403c4180c01a138909044c2404800c100009054a019400d03100912000900c00000c031072a0300c0403440c00686030702662070125224440c440b40e43c43d0300003040300c01081c4964040020b003001c880440440b030580d040e1000321271001d40c003204060600c4030315106800ca01050604d07500903141c8000c20701101d2001603600c0341e08108055881c540964408010071a08542600c1003050800782070511800c50f40d2016074022451064244071030800f80c03240d000c01c610f511040b485580c5490980005200991035980046c00a0300c1195031200c4482d81244c0001e80c0c0c001c0482503030050782c000d25040c8003aa25188603001401c0e002e866141e0900c42000264400c41c0280310021100c0b1212582444003480e41c02c01695002051900e051190002001003103016041400c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 134351411 1250 134350161 134350207
    0x12010e0c04020a0306050a15030c020601120201140405031b1504050d060f090506040f0606091a01030b010203040b1810260601020c0a14030d020106060e1c080406050717 74
    0x503946080f118002c4024104550180f03401851500001c2140555005640422405542d04000c50410340324126a81c1d0304c04c0c800c803200003041d0018140554482c10210b181c00c50103c0503e46016a03e0010074030b0300084071074490502d4a0555410100d20b80944071111821700041503d05203800c00d0001100d00d41103030002040a40c2d074050b941d00c521110341121509580060903207000d407406003462183c1100c80481141c416140c14804100c006c0940700b444a00341c501c4000040c55000e002c0150f000f00750302c810203415171205020010301104494000d00d0065250030b40f220b2013181ca08107102ca0494100b4000d01408014094401185184403079482d00c5000c680c0070584680354040180e05044600c180b2a0300147c0902d4049481c58650500050220095040700d58042050008a00700c41090184000090000c5200c160b43d00d071900c01e10381181c2e00561961f0b20803540380d49001d000c0d40b29a011402240c1c011030350304280250000b840ba900e020080003a8541240600540410164001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 134352517 1106 134351411 134351419
    0xa03050601030c0c12140310060908060402060306130b1305011d2404020d02070b1e010b04030f0f020406030507051003060f0b030601020a050a030e12010e0c 69
    0xc525190b450305507982002c0b9990035036030801741545c0300600c9020030070442c0550100b206070000650290789080a10795400d03152070b002030b00c0501035500c4441c6030b400c16403c000150305e83c04101c0c0c1d404a0115020004524050b0f1440014108980c106402904070311a0310300360626030784400d040e107001d82922001040c410110000204041307900b07000b2144a4140800c8104030303410307000b68200d0700a0005d42050100240c0004a0304410400c7d00c54580c584c1c01c0c0b02c030b08500340009142d001650402000d280d8180340b11980b5900c11440014107202d02180300c0c0c2c05000c4048000088258000d000b170040556034189599900d440740a260300c19240414081c20081c02131140344125646902e1800c8141d240114608150704010300c258150f020f40601140050750500410b82018803e40b58000c010740444280101c0c0385015400d820643e2500740d460008100c00542e14940e040c0c122 = true := by decide +kernel

theorem cover : BRFrame.Cov 134172661 134352517 := by
  have h0 := BRFrame.cov_init 134172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 134172661 ≤ n) (h2 : n < 134352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
