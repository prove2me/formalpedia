-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0114
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:54:56.496273+00:00
-- url     : https://prove2.me/submissions/c9c7f1ee-63b4-4ccb-96ac-c5450eae65ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 20323747 ≤ n < 20503603 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 20324997 1250 20323747 20323753
    0x4050601051905011d03010f0504020109050a0f09090f170a0206101217160f14071212021c0f0807030b0307090504050c04021303050106050f0604030b040213060b0d050108010608 78
    0x3c54040155200841e000c0805d06500041815418650b02071003004c4107540040400965400d00d4000144024543e03006680254841241881000001004c4104440d0071410201c1c48407018500000310b124544d000521180e417141822441000c960041c0c04a6100341d400c86c1d815555000c0d8065212490740300304060900009945408145c0104510030070309a2821301c240341c010a880c08156100ca080003e4802b207034449241c00400207500c5030491220441c1d0001c0c00b030503040c2404940e0240181100900c092002c400b0b44109034000c1c440507030b000088200300440c802c040701000d0701c0041c0000354000003811140018801e0f50107482144920503001e002080c2c007504112041c4014000503005681d10f01c140020b4022a56503070004091110b5145543ca0340e1516502c0c04c1ea0a41d0030b61b801c114800ea5104580490a445a07002e5400700c9400100030b1003951100c1c00400e00000781905e0078043c01d4104034010a050a12500030404005000000c03c0540ea0307a40d0384c3d608840903805845480e070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 20326247 1250 20324997 20324999
    0x1208070e01110f0303071d090105030606090a11030a1d010e030d020a0207050d050d1b0809131803030203091504150b150d05160c02030604060c02010e01090605040506010519 76
    0x5440b5207900c0b40010308a600703c90a102901c2e200d80d207160811980312000542e04c0b41e03000260885503c112600a00a5440e003141e9410900001d031515001000140582013050016100b8140d6802c02c45035000214800c551701d0808001520103061b69803604c82e84111824940d02604c1414801c1c5000203c03001c0255080420000030134002c0d40c0044000c5c0218815444003152654848081c10701041c031a000600380341c4420040641000c2c84420702c81199a28110800082082e00c2c00322091502e0032102444609a402e0407a4010490700e091850135211001c0b0311001c06415038002c2d030048046c1c0d801c50358007007508103454001d00c004490041c03c660652103807a442c0040c40d00250f188103c020b020315244003004018034210742011a003015980e031594107203c4a608400320b001d10400d8a0318003000c1d54101500800e03540d00340648001c0140b030361480b10781c100a06c00c0d40040140c0104000903c036604003418003e010304400c1e81d040d03800d4041c85000003000c3c030f00924102e450400005403000c0c01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 20327497 1250 20326247 20326249
    0x72f0402030601030608160602070602150105010507020d05150609060604030327030b070507030314011413020d1401051201020909070c0206120a140a06050f0d1a070207031208070e 79
    0x6074001810b00d40c145600c8400104034104240030500800d407051351080384a0385071540013482c0411307907440881507400080c0360240864a1101d1030b41034a000b801c00a07a1410700b4404551044422100a00b00d40110040c805880074030000c82c601600b82242c440c00c20b51510000c128280c8142e200c024045100308030341c50010191b21079255800070700b0010644803640e0741d1700d550041540480340c450000350f0004811302015054844c90b450f010810900300b00640c100005c80500d43d000b10300c40f62013200b0b401640f010914043d0103c2d0030703241541d0001c0c046c04aa50044502c00c9000380202031290240407030520401805100f074481c0790800900200a5072100001a100101c0c402e40590300721404024000307050b0390b29254280100e0b02c074000002d402010124020f003008000c1c0201c140942030400400c510fa440b10200921039030215a4400030201e07910b03180d0180048000303090480040c003020007281035000308102d01101d009032000d0213103035141e640864055204503030301c0001c21150a030568203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 20328747 1250 20327497 20327501
    0x10212030907061b060207050d02010501140a060503041b080d0305011a070206030705190e041b0206010618030204090606030516030203030f090d060615090806100504020a180308072f04 81
    0x140e800d031409072135801320141c1307030070050342d200000c140c07056413020018040056091244034010000c1240041444000e50300180d9100400d1017103504000000c4041010702c10403007031101400d100200c02e1564603688041242d1249589985a0003003880c043c0005100c010703512100000c1844088520325110b403d600300302c150b400160004040040c00e110800c04858403e000d10400f11498039802020007001040205590030707506503c4598607000c2c2201c00540d00010540d055804505181048907854175290210490a610107940b05042c0080001841440c0c2e100b682a40e02079000d40d8810b5022071400940c29606104c0250140d00c10402c1048802607400540307030341c0d00000c1080040c070b032240d2104d409a030004e801c006c043d6103880c80081100354004e039102c0e00801412010b44158502490003518045091007864000c6400092003040316205603540c1c4800302e9460314001585032a4100034010350081030003142c1075604030700b4070f80c1d8420710502908001c08140c140f0100c841201014080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 20329997 1250 20328747 20328767
    0x7050111010506061b070e0f010906050d380a050906101a03070903080c010605241b0c0909010b010f05120402010e0604050301020403151802030a0f020604090c050901021203090706 79
    0xa25029a03c40803a0140c40000918012a8441e001540e07650500ac2d115044403500d501181c440c07081d08200400041484400440e04240104411880100c0005522002c40b01c450301c031640200000801c82c0c10751803540000c1c06111540308a8030140d83e9209a00c000d1504c50143c1c09512044030f4105250304088001554080840d162020a45590381d0300c6240580141c01a8039007a51603a009229500301014031007090340701d0248107804028090303400707509442101800c4000d85802c40d040e0074500d108001d148800d040141180200345171048045e4002d01c6141003560000d0f14002d0711290070b40c454000d5504603042130411030a10340340d90f4010340e08482e040c2507581d00b0031414000058a032707800f0320107000203500841050a03022901134000048440d403203801050100c0c00d0b2029400350700d0004912584a92114203c0b5100c0c0c0c0d6800050f03458015035112216981c101341b10400da0b02e620202400769400700382c08440c3d083c1c0c0c503401c0e441c85601080343c401c0703200da00030b15041081522400c0606 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 20331247 1250 20329997 20330047
    0x302060a05040516090f05060609010e0904050a0f0b09010509030304020a060503060307080d0201090b130503030c1c0203070903020f030607051c0212010f030c091b0f0318050705011101050606 84
    0x1100d209113003c10203c14645a07000301c1200e0358039542c440c00003c0900446074030900480d60035207019460720018000001102e2098060b40b860b00c005810080304004c1406165000200c05500c0d52072880c19420005086681e6505542021302080340908000152401b071680101540511420244100c542e600001d004039454804d00400040540701805060a8070f18158000303d102081810000752045000c1d1001210941502c038010104070040240e80d0018041c44005a940440027000d01e00c841e085001c181084d4800002d10469035005444101180d209031f84100524201c1c204241d29a44211f07a00404076100b0000700c4d82c1c00d140400405031204011000504210b01560011b4580c8000d030044240030a0106d418802e02c079010b6a940020108100305000e5034101003000018581c101e0688414040210401034443d400381d004081800c00700743d10070000225500b00650354048910400b03001c12544448901c0b00041801090b100d804050603440c600000da802100b071890704a0405 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 20332497 1250 20331247 20331253
    0x3030b0301150f0f060e030703020402070807060608010606030b030102090d110604121b0b07120804021201051306050a0902091503071508070e04090f0b06041503050f16030302060a050405 82
    0x8005000140b910b840003510f188031121407003609151010b2040c6401e500003109000005100703442c1660000b6280c2d0a481e8142ca01684464492a09120a006160009210a0030040042110441580030f40211002c0741d0b8144100d4205209060803440ac9040e40358001c4c4c0b05c1d1402c00d021401201103440c0a420240401d0318040d598101c8400c40140c3e020100c075804403140000c1681c884c40304084020b4603c00600340e20701140344e95803003904503070f0202003403c0c0400c0000003020340d0741d441010540340d5000c00080c03080789880e030f805498004003050116811071070310000c039102084610440034050b60241079012187c0b0350048444800744040d120f0356141c460900041050480c0103940c844184054454010b5400c080102400c5e00f405c5005a5000d103240c102803c020810341c0c00d040d9a559000b107c000310302c1e100c18003c00c020307040c03101e2203002e99514600d000040107000039002d100d542d40c21f003c0d100e1207c00d08004800060140c480503006900420104600650749e40c03000750054031130030072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 20333747 1250 20332497 20332511
    0x120b09071707170d0507120306031e05071a07060e1c020a0b0901090804230306090d08010e010e010b03100e070804030f14030c070309050310020304050d08010302010c03030b0301 78
    0x41d0322001e2441c0d048003003180c104010400115510000c9900401c4070800a0000603c1006008005026018001c0c0c465019840c0300f2850034003d505c0b12020b143c000410014100110342c10040501075030302c0450b00d0744548000041c000002d031400411426031105028a8000d05442e0714003d030100707000d40b0140d405043c2c4034115901004980c04130b2410b258019045000b8a810562080300b0000c00030102c2d40d0408000200160f1110103c03000c0e6002c4060a8644602078400000d4002c582c0c12516014400c0d1414800050400680100214911380c2e540d00d050b07803900c07040440c4184c00c0c03041584551000340140001c00c40c2c1005994040980b56182240039660b003905030b9261010303140c41e0080340c3c00380144428140c0c0002c00c418aa00907013018003206014840c0400d084c480103100c0c07080c0c107401040203000c140c440c4000a005003401021541d01c00c0c070200b42c08000394015101251544100e1241030307846400345c2c5295040703d0b0140c640b249800015281a0060015181b1150303040d540c0e004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 20334997 1250 20333747 20333759
    0x12110106062001150e0603070801050c03040f0503070c06050c0c01051602061b030a030b090a090b0601110a05030f0307030e060708010b1b06070807020106090b1507030201020c030315040c0801120b0907 88
    0x1c0010002c101424170640c0707030306101c001d2500f481d1050f006100140d050804002c500c1d14454102d81c1c000b46c4c481880c03484202079040403410f40c002c203140141780054548000070321341d900c2406441054084015610f0850003000150b409101d80f0300782c1031200c055944040b0140c54030102516031509407024403210b081d070440c001803c582c4811140000f0903a28510030020781421002181d016001100401044c01e640d00c914040c10002080241040003502c050651501d003442101d21b0903902104403901c840341181040403039001240c3c5040041c0c80e10804050032040040d156005480c1501d4001d840e90800c51185d8090307200050390411410300700c5d1300e50030004017044001c1c414600760303803440b4041c1041030009081d50f00c590310001c000c908140010795160741d000851000565050981640c5070018a000e034064050a100c0c442d15000200c20044800c680320203042d8050300842c0e0030848038000d0101039445003000c0c00360303100f00031101182400141003410a1030708924140111285a43e030b800e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 20336247 1250 20334997 20335031
    0x30c060a030c0801090204051e01020c100e03060c0a09090207020d020d0501050604050a0510060507060e1c0201060815010302010c150c0917070311010c0c0302090412110106062001 79
    0x410a8006503856000098543d80018594090981204113614180c689800500600e0441200e0b41c0440c07000100034100b03a00030003a500c1e1944000d810140303000816034010f0a900d2081001a00a0140318000313a0840c0900c4101c4400340c02c603854807841c203828404e83c500250082c0230308a0308510b440740003201680c1e551850034905441003001040701d00e804e60a2005440014008801c0b090800c002e01840110032001002903801d01e151580e1500b82e1810030703d01400f0141e4018501d801182d01692412558000d81d500c01038a40d0001d204440c0d5801450f5914500040d46003101c0800c8001031005601ca041c0019145000745202d000d0083c450b40080121000200c0c03100210b0800c1604129512110f241d00700013a18990191109628540b258288029005421130420007052032003010849800c0303002003c0c540240000c0038503d41480c00a402002220000c070201d50414504c3c10002ea05002c4da000b591895900c040003440800b0100c2030181c0c9070038a04000355203c1e00c0300c0116038124 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 20337497 1250 20336247 20336257
    0xc030204060e06030d0201060305030d020906160c23030703030e01050d06060203030108070f0305070509061804050a020f1f051815040e0105010503130f0f08030f0105090105010e01021b030c06 84
    0x409481450030f104041520741907100031a20705590500e00f04001044012042d00c2ca0b90405400c050f9a03441c002d000902c2e5442070410819140702c2c5035190005000d43c4030481001d0703800c54084404040085800840015000c40c0b000c0e600d030384418000c2c03001a114407203c07404400c041c100141003507a8481058240c0d011034202c040164404001000148410488200106540e4604010a500315100c840c2c8911407406054061580140490281e441d2400064482c0400043d4246a81854a4003603214403010b0400c0c0d1041c102140054018540440c09203d1100749400c40c1003966086030b81038880c2e40000d100c03103020030700801010056031200003841300108034030010070b03a5407420114880c03460001a00b18904004040c420000d21059a00e80d003541c5680089204030305001d1850000e5800310712003001003180c100401400784d0340c81d2800540d030686204030f0f09400981c0c6c0f11380c01140c10750812070740c0500680c4000d00700710012034241c088002043c0301070103980c240741c41c41c4041400c1d6405 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 20338747 1250 20337497 20337509
    0x20f0708030a15171002031e100311040612140f0708030d1103010602070306020d180b06090c0f1206040608060117070504110d05190516171608040c03020406 69
    0x940702401842540110070070301401c805104008404d59103051503a55480212a408200d980040030604840806469443d50950b00701600103601c0e101d807000e10ba0001c00c0c401101c80042c0030303038942450700e002c0c042c60b0150f6684100f05241100f681e00c48944043d4030261518040c0108000c41c0300ca078500340b20010180650100560b518214828080c088414040d400e01c90303280140300600141f6800b15030902100d40104000d6182d083c030384041e03402840100103131440104040c800c00c080004181c40b07103100c3c500c100c0f0045c1c901c4c2c2c2d9034a110a079034440e5400310286404200541c4008000005910b0781040d005440041c01c1c9403191111031500d08203803c03507103400f04001d5480508120410400000d0041510280409175803101d0018550040c1c0101f401074030b0b103034000641500c00790402e145404400c1c14007440f181c00c2c6602c0c25941c0c1900f01855a00140003c0120701e1019280600113001d904807180f00c01307903114910300440d0403100c040d00455855038400c20000150f0f469005060103050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 20339997 1250 20338747 20338751
    0x301090e0c0603101a04090606030614030106061209051005010605030402030f15010b03071704080a030608060c071b09020c010209010e030d120b01090f0e04052103040303020f0708030a 81
    0x10a1038a81c80e200c0518a641d10031034082081007049005003803044100c0d40c17400e441002c040803081d960291405160801303100075180060005086a2681201c0e044488510502410801440030b0500340c4085008110110f00f5220120039404401d520442c1800d00400640b1101c0051181443c1a503d0a0b8040c0000407008410b00003540740510017001501e0040c0c008000040e440c2089030304602052003a103490714404000074003603d000e04059041102c4410401003289064034040c0c01580040c18251f0011740341031008602c00c0c0780005c807a40540722100354181001d9550399070010040304800d00300500e150304440000c000d1280c6c006002400b940d1000980c44040c0b280c0018075952010300241e1183d440340903c0c003550354103c1c0ca080101080e0b020040303260200e80b0010780f051501035000200d28410400006486907141850038041e6106d001500d004684a0040c0d05c0101d492034542c1e4a002d0041010a0009009134000c080000e90030380b4580c02d19005444d07003011608101c030303d01402c035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 20341247 1250 20339997 20340011
    0x705060711060708010b0307090302090403020d0906230c01021201030807020f18060f0a05120303040b06010903020307090c0c060203040f02010201050919020405090307060912090621021e030109 85
    0x40c0c21268800c1007403000310040c4814508080300414001c1e0600c120391000c0c00c004049405184a103100c4005140c000e0710800c0c0c9410103140c02551803081041180024405902c00310708584129038058041040d007078400b80104d40007140c01c600da40140c0e030413000e642d400c102034a11807101d032040714000c60080d140c441d11140240107005040d0141000705200b0205000050813a03100e0303003c101d80000d0290303901c00b01491490042050819107400140d40982c09016022142c03400000541c415440380d107402c449034035450300540b840402400f0003541604000d6044c00f0120b01980003007610000752518040d400601e4540308126401640c003075918495042e016000d558090250a800110000003408000740d007105103410001650382c002d224580b10b9002c107000c60001c005403030034180c12000c1045004401c0c6171032114407044601300000700350000c8001a04500808002d503e20522412400c4000e070101d20000003036200f4016454a4141081c0a070301c4103012002650180042d80c80000d2a1303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 20342497 1250 20341247 20341261
    0x2030c010f0203070801090b0f04020f07110a030f021002031201030f050c09010509010504020f0c010e0105060910060206070509060d140703060b07170328150803030702150606070503070506 83
    0x9160070800307500c41e6078010028042c03403507440140e45045034442203001481445841c00510171a501840d0558005c4c00810701c0e0300040c01d110001c0c20314510901c1a11428500d40c4148121078180d407001034285400180300d200036082c0001b400c2c880c2c01d030b548140c0785022944000c0701180d801c2070304280d41050101110604020381044003080c03601d400c4452003203a600d00703400900d54130814042c16020381d80110751021801320003001d48411140e804000c2c0440030b0f096103054006d12048450394030944d022030200b4068031042c03400b00259065507000c1d0803555240c402c20359a07075004900e1542c100f03500b0818586e0f10306562040040d01c0c86910400d5041e824004401016550184c22104c3d09507002c000940005120005003c1c1d1982c14018075510b0341e07906e0319114074031040c99056101452031139142a0007480d00394410242042c150000c454103984405d1166528003003104d540e80940e105c240034007800f03c8070600f0301e80e010070024602d0380361080954411782907403c003290441d1079600c104144116 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 20343747 1250 20342497 20342501
    0xb09030712050a080c13060e0307050607060905120a0206041b08030d14011509031209050604140114070209060906130606080901050606072103090804030b040b06011b030503131202030c01 82
    0x11017140c1c00e016040541d42000c001031400d05105410610240c0e000444031514244000c000900000f40034540302c201e00e003413043c042d100402080340c06008460f006008555100c3c191f600800060380204040e54071591a181c07151100c03410044040805c90700040c100f41d04000600008036110408074580c900103415140411040e049a14018254000001460f622490480c2100d130420414031070054440310070f5580006c01d03004650420300000e0041820580c4030900c801c00721003a41d8844281c0e03501c0d100811a8090340e04002c0d40400d1a9010030981d292060016802410040c1808070034101440700004480e65030b1f1140300401c00502c10400303401020300c102ea0740400d094900b140380806c2603407102410308034030714900041c038684c0398036035001c0d4071903804a03821a51148010790f956460f41441da1054508032012559850719000082055102d990722080034000402c500d035050030301c1c0d40c094600d6040282005083c406c0900000c000c19581c051150440003150091a61100c913404800e007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 20344997 1250 20343747 20343751
    0x9090506010602060601021207060b0409030903030207050f1c06061e0303030b0a051005030a060803070807110d05030405120102091306060f0503090606010c0809030d08060103060503190b09030712050a08 89
    0x10a44d0010810000540d0700414141c5400c0300500c00300e81d43d80040d1a0039002044400c40d4950420302c0e0665510030160005440d0003076a00039001c46800640e641c0401861400d0150303607582040070044004440950301c0035900e11117204541c0810f01c1030300d84040c40b4000258048020301e00504160400170325405224072031943d0300c1580c01e110381c0c90400011070300004170390882d141008800000140c0252302079002002a000c42401e0301d076214290b080c00f400783d80240030309607100a0300c6043c480303c030324251102c1080c4a42c0840a5428580307064200100024041c00224a83d5020403050307850f0781e94021021521a1810000038a490500e0801000450094062070500104100f4810071150028486a018100340b03400d03403203040380f8035003615240500d5032680d806100d002407600823b0340011030103100300b074281e0f8200019541c403810190b0703e81c2c1500001c070205d1a12600400400c80b10214640d01c0350000080340d152000301d507248141078000c14100c1c1c00042c0007242c00054075600144103a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 20346247 1250 20344997 20345009
    0x9140d050319021204082101060207090507020c0a0303110307060204170c030d02030d0506010c12020106050f04090f1506050904030c060506041a01200706030501080120032208040909050601 83
    0x50804881d14811500350b100504003404002020940c1900181080f561040c0487d0b0348410301f6042d60b442401035a80c0a039400b6010f001e40c203010010341e88034800039907100b0440005143e2011a0310390b407002d07500350002c41620303802c6010801128000c107600d40002c00c024900c03080072452941001c401a4246503220345803602c290020072800342255070000c1950104000b1480000e91900c410006841414040000a06403a640c02c50442800c0c0c040d800b00d0101d0300e00b80c40d54101401d1402c100000c65200d00802808000320a00c800003080d4a0319041d01d120101d020000f81780b5482c3d9001884201c0110340c02c80000340d8000c640b204100d45070143c6074200c902035405016140410b90100032a070721030031800381080f02c9032030341103400c00d10039402454000c41041a58000c80e1280c00081c0540b009008001e095824540d441034040307403602a04084103440800d050940d01c84d101c5100c20600c420b40c07220441a0a00307043e6001c5181500100001c0c0210f803000141c100c5c603450003d0070290140d2140c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 20347497 1250 20346247 20346251
    0x501020115031209180b090702070b040e0c1318180210030203070c1e020a0506070c0e09010b03070b030411030708060705070503130311011101020307050a0309140d050319 75
    0xc00300c03262000c403090302540d40c400014a1a001c111400311480c986517403204104040c004d05009451030325078010031040f0401d030392000f5541d8400340300340e940b02c1d4140b08034031140303000700001c22038256a000c0181e0081000c0c00c0c85440d18145a5800715032040d190012254048400c92204d80540c16114a2154007541031102800040540004144070514910b10781419000000521417502c9501002d41040e4404800c001d08100c61078808000c0b421542d00324059071749201c0c041003030b16080c3d040da245540d0202c804030301c060410700b008600050107040114559220000c0408aa5062000300050640c0c04804c03901c0c1d2826080004010220442c0c0d280a90003040c1c080c000c641c804100b282c0d2000190520940d101d000385045840c1d07108844070b03504692014100801085030001158035144d00907a659254808200c114a00300d10098070644007088080003000c00d5613010b5002860b400c2e010b0300307001d4028510360051a05010042e200080040c500108101d080c007a885c0c05001d01500c00142 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 20348747 1250 20347497 20347511
    0x91e080304050105090d0b0a050601020709050613180c2301030b03070b030c0c070e060405070504061b060906020d0920010c080c070b0408030310090507080403030e0102040b070302030c0705010201 86
    0x40d140c1c840d902400d410000d0001d000c1c10152035910500b0003c5910101d02e02c0180f6000d24440000c01d810340b203040c018014480300050702c0340140203c1d070150700700401c042c09660984040304020001d084050031010007040001000c547c420100d880180415480e840420204034070740c40312244090b00d414185843c281ca11035068800080f0078042d55810300090360340e516440c0158183d805540c1d40c4400314071070040007244400505810394000d4400703507000d01c010703180c2c0a0150307024010350090400241201864015030841c200110071050701655000900060907210704040e130340455050031605031034800d1601000031420002126904001c6116614411100000c2980807601d001600d000d2000c0303009010007005001d200c00401c0c2c51603416a903682ea40c0300c06074503504200e480311310b85424002d00003440002d41c0501c0d8855400d036586d0003079a035034640d400c1d0300030198050205202c4d9400c0c070001c541c401d100c01c01400118000d4000716181c5150102c568641080c0e50462411a4141a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 20349997 1250 20348747 20348759
    0x301030201091a07060507030204080102180a09060308070b04031b050f0f010501060509012102030106120510030f02011b050106080c190b0307050a021507050c0d0c030210090302070503070303091e 86
    0x1500c070400e038170000120782516840030450181c02907401c110341a510010361080b0815030700d020046d2003d015226005200c0d503524607502110150b10010304190410000320b070000e0100301046601900c64140221000300c450400580480004d00844050340611a041502e01c0200203614140c010741d002801150304000303008086010f5001ca49042c40080030110b000600c841e0001861070f801c48004640302d41e03560600822580c845002030040034a01000f151004072040280c806403608400d09082140f0349900440d03801d21b03008007245060403c4440e040006000b8000d000003002008000c0c2421071441082080080c00600c5060f64055103150420914514005690b404030f024145103071a400a030310280d003040f64608000030191014801c00c160b90b60000c0c0a010800e0030841295803042d20b80300182c03000c51407040f001d00580c1c8600381a00100e03600d41c0141e11410721134419605640d40d0b440110740f0303044198008401041c5841c0081c0580001100c01c80702d444041170801465900d408 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 20351247 1250 20349997 20350049
    0x81c0203091011010905060601080703020c0c01050d0b0306010801020c0c041b0509030708060f010f050d020906061309020313030810030809010f27060806030d120515030f03030103020109 82
    0x181c1c240707000d18808500c03001400e014080007980c03098060b00038030a0300541d1801c140c0350081110710601042d08030700031803603041c801d10a489000426500600441c08000d00655554001041071900147c4500c071400d100d0b10240a001e0082c9001c90001da1030704c01c42c0122500304140200010f01861400741080700c0400316258107145030160f0704125980300010702c0828201405070300101913a105250034016021907151305d07941210f400b4003040d40c08503103c2041021450089001950001100022556914040f4010003440d8030302001e0310351030b03561981c482080c0d03041144c0741d03c0d080002925610515410480c10781e0300c42640381d000c021035410759403081c8a070b0007501c04041c100641c80700c5d140301c1a4021803620110182e12a4035150b52104880364480b5500c00b400b41c200028002408100c00d414001010054a111034403150901c90f03a006040000340030061120a0011400c910640c007074030280010b080650681c0051643c80d0b0460001616540180d40f22540030402d182c3d060343da01d4003503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 20352497 1250 20351247 20351257
    0xc09060403020f120601031101120603050303060f1c060209041104060c0b060105090405040b06010f08061c0809040504150e0604020105030c0703090b0415080901020712051c0510081c0203 82
    0x12580700900500d5000850141311600c8015189446441d00100500c8142c036801d5110401c2680c808101c3c02c0c028000c2c0c0161051448000e0240d8410b202090b01441c0030601100c1e03400024181c140100e4068005242000c0c1107101660020340c00100e0100c6800d140c0651620443c900b14100e03d03041c82c003000241800700044024140006180200b1180e80c81081240d030f104400410601c100c1c1001c0c1440150703e03000303441182c0402c4002500c0c007640c41c0120030803445408000c0040e820101c1c841a180514902e8040850304044100103280301990340788525402940591752031b40b201c2c0100d42510048401415189003168028401c01c0010b03a4400d0440b540301040005144d04c40303d01d07240903602c0e90303482e40141d0350004c0d02050110704515513040d4150300440030782d1a00c07810f46929010908030312070355102818040c503000c40f003000940141300070314500c2c10503001d411511041c40200401c4840565945060109902d410801c0c104100b00508030103d04042a214200103180065500c4c070030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 20353747 1250 20352497 20352499
    0xe1215060904060906050a020301080c030a0c12020409051b12030301032d020a03060e0d111002130f03050312090309010e1002010207050f06090d020d0f120902030d02070e0c0906040302 81
    0x30740050100540c60f000306202c240c1c040402d20203030400242d05d00c0a90400d0045d05260310650291030700742d03d000502c0d00c0704960000600d011490030101182d03a440e04180050340c10584a00300280041c2c4100b051513808440030303008600c08482d03c82089030440d00c01c4210341aa0303100f8001800401d004040c1e12200d0f403500380c402e600708054280c891000c40520800a540112240d40000a00015170048040b01d851803003500c4a03180c1c403260941e10385407050021003081d4001c0d03590140e24060382d4010420b4013000c07070082d0a51669011600d8808d480c54000303d4560f00080b0b100000b220184414941001c400d20245047c0b0400c40d0000b403001000d24803461085e1441041d1400e418002e40c111440282c101064840c44041703008010781e5080c1c1610001d1141c424244124100c0b40f011541048184d40d039070310340014080130b1104031800d11242081800d1036550300c04500040c0c0e0100552003840311140c01900c51189080c0000203600750051008103401c0d0100081030280d60740c141190140c0b54 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 20354997 1250 20353747 20353759
    0x303060409020a1512050a020403080304110604030b0c090307090506060304060f1104030807020f040e0a060903170406051504050915040c030209010e040b091c0e01110106060e121506 80
    0x802400028032401032607011000c600c140c060b213035030700d940d1081c499242c900715584140100c5c1c455560030002c0344114880036280030414004030740000c48020100c5012000113010741d0500b1b88903265686c0010041e00c10000b10f202c0000c4485240c1414441070005111303018040100e443c201000c20b02c40e01c8010f00091116a403002e00d11318081103988898903000ea80a01c15484a1322407501c49655406240c06a01c9220080360b83d030b42f5807805003d402c5850307040b50041c2905001c281e03100000341c0712011040b803e001c1005103030490b403c07524680d1807045005482c081041e0800c0c40c01034641c45a82e41429001c1c9080108200609500180384000140440d00100099407141401240c9005640009511506620001401094034207405015600076004140c440c2c490000103551692440590310f904080c4140b01810b150203000665010801810300060341609102c07654212459078110300c0100c0c50440300c182881c2416901a904525000010044050001c852a00b00b10000b84154440c01d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 20356247 1250 20354997 20355011
    0x90402060d0603060e0f070b030403020c0904050304031a060108070c0201050f0a12050103080c0f071a090105120405060907060c151d151603050f0a0e01110408060601140a0203030604 80
    0x41007540010000c0d900108104002c03c0750f20303066600c404080160304200e101d0300c2d03404a48e400601e0b0072a0301596042d00100394052808080c0a00344800900583c0c00e8041480300102140d0291041043d145003441c2c69021807400d240054484400542520200b0845091220060f6004421516081c80d0500d00c02d44549012204442510fa909440741e21281020000070070899604060485030052000381c501c0020131440242d602c1c0702a11483e06040d00c40b0780318604064020b00209542d800c1031414501d0081e01c954503442c141015141240c45900c600d00300312041e0340520421010300f034540350181c2c0105854440e0311420040e44100c61281e40e8410342c8003800c01c001e01d80010030111442c196880da0000c41041e1000d02c90444841616404203813580044900c41c0c841c00f88906412101242a515111844030083c8418050400a5985e80d040c800840780302c80050300044c9070750001000030b1f2400038001488480e0060701300e84840414031000324010f401006480c1c0c4000c080c0c2e4001002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 20357497 1250 20356247 20356267
    0x6030304121505010803130b0f0c010914010f0b0108060609041b090306061203021009020102100e0319030509072304020a0203030703060b09062203060c020601080d02070509040206 79
    0x40c030456014800c1040c038150700408000030341c142d04494000c40399040015070380e920f85003074a038494031640185180266805129424207030010b003c0405000c4800c905111002c2c51540c2154402541664001600c03803001240d20300034021409113002c0400107001020750080042d20100020b00914810702b4007290f241803a85560f4000c81644441411204000604c0c0310050811201408156291424482d010400058048009000e90b0f030540c01041d01c2401e10015800a00c9210400ca045021701030580c01001414019a460400400003540d5182801450320580c03180c5070b2805420715050038104501900e01050030300803100310301c4010b16080e264800802c80700d1503c01245502601c081280e032141030380000a90b100314015102001403686a15421505009409101d41e008000b00005004401c400107454140c2e40c421440100e150b4485d0344100030360300c501c40c1d02401a80158010421a9000c11000d0461100703800a0400d103424900491031395900184081d016040000b400d20306 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 20358747 1250 20357497 20357503
    0x30b010e0111010e06010b070c06090302010f05070c05030607120501050405060109030f06140703060e0603070f090c0201150305150a02040b0d02090d0c060305060109081203160c0807030903020405130507030206030603 95
    0x807020381391094855641c0c44640d080e0080c0c12009007a01c40c2d007007a54000c00c585002e05441825650142c6556148404821048400382e11100c000c43d00c11510fa2000200d9880800400c4d005003199122290951030841e10081220f5050740600d1046060206011450360010158025242c10202010480d1224202035000d05042c840b1004203449100c00c00c1034181e40b6a00c408140c80d0800c00c03a2825485080030159901541d000e40481c000080d001004080361030b41c02034844081c80c0c000407807501c540c510104440c0b01c040d4826511f40e04480b15440038080d080d40d00951020051a0450a00381030a084066600541c50f40c0d50b8182d034009810200e41d13503102040e1040700d0707120b40100c001c44c0d1162402009041c0566120b40031a17040700c00441c0c01e12000c614010741906600010f425952209124a69079101a480005112842083d140414807540041840d607000391103020ba170f41e1851046c0412240d00504840521103034809200009101054a1084940499186441c1d440320070000781 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 20359997 1250 20358747 20358761
    0x3030b060c030d02031e0702060708090a0b1801060b040303020706030b0109090f0b01020d02030a0834021f020f191b05010605040c020312011208040905010e090706030b010e011101 79
    0x2880d100114410000110301e8000354401d06c0001e106034041c070100c2c034840700d05103029900c83e00941c10402c002107542c1c0c462041c483d4001000f01c00c4584850307960b16940200b042c1502d0307101c100840e04056a800c01001d02404000b003101c0112a4a00340c40d40e2402500c62506004280805848541c074018580c0714881c04130140103981401c004180c514910140100040306150b4058011000d403d0351040c00071080c1c40516500307889a420558a100808006012040c411140d0346882c0910007030324070b036451012003541e0f10b94006121200f9100800c40304500441000d0741c40070b0041052070b15014500d000d6906496400d02e4035000303940403640076690341d07003180b402e14070311941594148107003c4150048000ca03181a5000c1041d041070140490b20f91185011040c29885d60310010807143c400c10340c0e118002d80c06141441c2c03d180c0c60744010000d84500ba0711071a20b603a050b8040c4221036405002c50001488541000c003c0101d2007000605038411280145060054080080c900d540003074000e48 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 20361247 1250 20359997 20360017
    0x70b0a1401090f050903090a05042003130b0903070c030303050a0b031b011d0a0b0a020109050102070c06080601030c08060f0d0c0b071704050307120f0609141b0a0303030b06 76
    0x40310940c2c5449032007000b0683c8841e9111100d0810700821520ba501100312071b030860340035140c486020300344010b000c060502000c1d0301920b9050400d54460156840000c3c2d4000c0e00101002c8020300020b080200310024040c0c05000b0980081150034009464002800d00b100d601d401d0200341e03036460b00141c500401c07102200320b425006007206061450280040400324141c00d0300c80c045400f01898210b1008e4150700301d0640c100100d00070a10141051201401262080f8030001c11104010741d54242a41c11040b002c44041c4d08800040c44502c2d004503106911174420700e8108034008011a0042050f03034041c0c14140511010080c0c0075a90319101c44e01c401c000c3e08100e43c41d4046a0343c5c1d0b0310030403980c002072050300e03891080044803010440e50400c59044400c01401080300e1801c1c03100c13002690b00108403c035181c00503603949000080c030311700a21080c17502070040d071002e600c20501064108041210420041051101101d9055595090340000d0700d802d454001242c000b50b001040311880f40c3c500b05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 20362497 1250 20361247 20361281
    0x40f09051c020d0203030108030702040902130609060306050601030504030207092003090304080f03040e0a0c0e130b011214130203070f090603020a060801060203070b04050705060703080402040c0c030203070b0a 92
    0x444120074216010850022075508032103603410000422610ba01007070007a0350140c2c10400501001d460301e9042042c0d03460008181034581a90040c13108121000d42e88940251030721010100706122203031003059800b000a003020301ca28a400c1d1340003034540c403031402402e00f25a55a640c8141d2118580c50800e000f0400d520340556030300745004181c0d982d40103803048a049200762808580025408415541128420806d0001036260f9600301c3d4041c0c0302c0c00c1d11038010070501d00d0072151144d84681055031840745400000540c8040a400108104465409050320b541844c44400c001010080c540358081c0c250103040300040c00307600c0040c4c10015181d0145501c440c1600020a10f00c0b0b81d1b5100c00100c920031904100d6240d03a4003405e035a1804244650405600144000701c0442c0b046008554028415000d607500a92100c0020f000c43d00000d400f82c0001d40300310104011414144910101000310f8101543c82e44503aa0b802541c03171143c241300a14503020354020a800d00c000ea004070b402d05100c0091 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 20363747 1250 20362497 20362513
    0x81006050336060604060506070206030403120219030203040201020d0806030c0f12010e0708070e1b0904060302030111040501090b0c0601050d1a0c091e01050d02070305040308040605040305070602030c0309040f0905 94
    0x4060b0356410541d41e03241700c0c9140c1040000c841c60103400319525150b0180c021030450380c854038281ca804010a40ca50385050f000c0040340d02a204240a002d111030150b00c0c01610b80c18140002843c1000c00c00381c46c07090000c00c4051104640e400140c01300710300030444035002d0803e1040e0220b5a00c0040500c1e20020b0340c244040541c00b0900400c9440c00d8444950407500034941e03e0703460600c0c1e9801602c10b80400a4506244002e8241400060011441c042c3c00410b07416925070200c0c0c211141c00381c4103241481d010405006c51f40c0c0c8280000020305c580e0b02c009090400001c030254a415040c840c0328403c0d0481c2043c2000c000d044d0000d404140e58201041c00c86180c0815189810303401203200b0751080d1140307000142203c00000c9910810b08040e500c0c00d003030040c0d0b813030100002d40c00074030140c081c480280030001c0000d20003c020009000e00381d0320301d5125895403908601e85801d0340c00010943d082407021906095000060302c1800e101100c020a0384100009458001d20380342c17402500d58000c00e00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 20364997 1250 20363747 20363851
    0x60403050604030f02120304020411090a030809010e0f0612040227010302010f05030403090b0307030e01050910061512020d0e0f0105060f0301060602120a021504030c030810060503 79
    0x41c0548118081d885039040e0718142c5130102d84900c113000310350407902c0d0140040380c00360900d0f5020240405601c3c0741d151a18104c60000b4992445c1d5500071a000703080021051080d590088030700d5405403059624060900c82100040c100380512300c400f0b403495620400090035565482000c0100c10103a001e907103207526078034103881c2a5078801d0105a000c00c0b440740c0703500781c1684a002100e10070b07038066032071110140c1081800d450f690300c060845403c058030b03034101c070303c1542d0b00388109405405848014403e0044c512192025600760368017070302c0d803580301074040d4a1241d003040d1074161a582c00c02005030356010b0201502d00825000c85140d4080c4189220a58103060552007140142800c030b45100d441100340c0f040600380d80c680d006250068020300d0f020b1005090f00300107070140d0b3320140140e915001490b00203400304078084906800140c2c081000d00203054000511681004842d40e5981c4028204403014200d440003800038441070205140e0303200031000b51400c403909103003035403489071b01038000310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 20366247 1250 20364997 20365003
    0xc12020601061b0209070c03020102090a14090601030603081c020f030a0209040e060108031b011b021006080304060516030c080d0e0609010501080a080d0b06041212080106020322030206040305 84
    0x4015540416644601c441600c0403d09144101c9076004140030500c0d03640c030b0401c503030f0f070514640124150b6409102018241d41c0301c824200c05001c10000080300c2c18801420801c4000000e001c0e28145494110b042c804180c210040b6800315446520341c074504074510040d800207200703201d18040000404800c1c0b080b20703003441c1c00070400340100b00c8007445a034030343c00d03d00c6482d14428410000c90380e000f0420b082c0e280102e5116a0515091b12000040e010501a08222640034160320310005810008402c0811581403041c01c001c0d086000c000c60030142403d901420a01c21080c010500f401488400030416100e5406011900d903c00b00b00d40d19031400c03083c8030000d03003858803102c0d10900480c4001040d1030414442d50b4122883c4400030404151aa107171801107a07c0000306891039911081822000d03240c04008200502d000d0038141842580c900f40340f41c10b82d2107180e0040811039550010000d050380041590003550706890f50812000c40c0608407110003020340d00c02900254081000000e00c0b0001c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 20367497 1250 20366247 20366249
    0xd0617010506010f020601050103150512030403171809131505160c0b07081008010c080f150f060c03090a08030a08010e0c03010e040609020301090f02030f07030b0a05070c12020601 79
    0x814001c0c0420784900c8015034641c0c0425a0030300051380070200400c02076229412103020456801d0788000c400e0303161000300d1079469049000203481d900005040080203031b843c5c1e0080740c1c421400b4856007019403195844008800381c0b101c00e44584a03001c0030600107000e00d4510180c45503c620540c5e00813043c4c0701208050802120010b140340512070920080ca0301070300c21004602d0b405500303c1c08582c0c030f02c40b0503146060040c10b1860840310201011610758000d201385034840d41140c940198620b04282c1c4003015110003088504501d0010f0311184240c3c56a06e034500402d00115402e030385540d1401400303031450059500301d5a009140f90030004413100007100410b12030a2a5448465580e2280341c1c000b1070740c0081e00c49008c050010001000390072070100702d4a4205d48170705c1e008120b40d0010f40000b42503805841d0143c4003190002400710851400f00726488803194100050b1040a1440d181c4603d02c5100400740d1049076111030016454234840d03481c441205600518202002d400044000e43d50402 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 20368747 1250 20367497 20367539
    0x6090409050703030f021f0203070207030b07020c1f05030609090316110907020105060109030f0203011107110f0109050d0311010e19050609010912051e0d02090102060a0c020304030f03050d06 84
    0x341c2404030310302c50b1005c28000f10307212000400041c881c7d5510002d0000354801004641103019110380803000171114601c00b0300a00d15030340107000c41c450690030002800ca5181c60900501e945100b0340c1da10a400500b07a0703512a000312401d54041d65124a104e0462060440803000300d0b400103064010048c001405400500c1c0c240c827056280e076949a81a42200c00541c0c1c020301166250710100006680400d048003501d20250001c1000500080c6c011003a030803103a41182d149080c80040481410901d8581c664003900b40313800d090240c58803000c1540300e51900c5000c1c4c02c100841951040d414825013003401269074507011662a0315180d4ac00d0342207035009410459450042d080070a0101405014031408185c11622114259000800546642c0d21a0901e0800c8007160310542059070301e02c1c005031044425805c400750391801c14070002400d000c0c0c0100b80e010b9a40c0b07014500101660300000361380980354018403580f017002d21810143c139513000754240960454242180841d2200e04034400807001d001d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 20369997 1250 20368747 20368757
    0x5031f12060f0603050a02100306030503031006030e0105070f030f021303030203120f010b030601270f0f0b131a040801020313060c051c050a0207080f0406080c040305030403030c020609040905070303 87
    0x6140800261043c0707100140090b03124400500c058500782e50b408510020324100007541c56a01c3d9070341400c540088030707001c0900520103010040720f0b0f01801342491000c0b11200070012450b0414002e08005c1e0680f00510806685450724203500c40281d0444d140744524070100035002c2c1d603074a002552a440074055050041c1400c022480021810000905030b540188100f41995102001110f520000e503902d803150031480f410303003071400d80d10000a00c003400c040c2d1010303a0480d0a1400004000380341d503002c520101c000f0000424060340354007881040da01c10180c00e0882c00d80b880880e0005025640190505500c0041801030500f8102e404520091040009020343c840400c41a41d250041e0800c2440840740c80b00481c8600c0040d44c00b0a9001a1030400142403a900c0d48a0402c25080000c0c80e4094040008040c001203402c850300f43d80c050300c0e808105103002d055039105603ca02442c0700c02800c1c04400149501156610029a1000361010380100941c481c0c80c2089950740710b441c402900401d03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 20371247 1250 20369997 20370011
    0x8030301170604030207030308060604120f0b1e0a0213051005090301050a021c0b0a0b13031a09070e0a060b07050307021f0203120402060702060304120311070201090605031f1206 78
    0x6480890218442c0344c16402038081e2520f1924240c43c0346d80018540d5038001e000300404500030b0000848207020303034020340500c080c0c0c03000c0d4640125440c00c06000004202d0380c91b501c651280e0301d0740d200c407680100a80c0003d40c83e5071072030102c0c03900303090741381c0019a0068052081c0030b86503900601412048104130001d01c9181c0b10100080e0403880b569030b00405034030171194200c820319126002003406101c003070015540d080d540d4680e290281c002402d00ea5018004020070414002e032040460054038007001e182c4040d0800b00621603454101d88a15051a042c090000b4242c043c5940940020310506848031b40d50042403030000e88990081c00c04030310071160104480305003a100810000d40d4030658004610345010604500518440144220307480704040040000603241c4c08081c6000d544170340c1d00244524a03844018099130034066661664500c14040c000141c3c3e8080320708002c42d409400c05035078030740b2000b604102d03841c605010b2643e1032482080008805509008454040e030050b40104214 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 20372497 1250 20371247 20371289
    0x7110108040b070c0f0605010b07140708072306041403010e0604020f0f030c030d03021b060403140a02030d060311040b242104030206100506210705090301020408030301 74
    0x911041d900608031422140000d00203500034a8490901e60103072105071040c0c0c800340c1c2c2d03c0082e01c600342c014000203140410f012003000310b0741e1030030300704280b2420142401c0b90034100c02556509541c451040d981c100484204843e01c0c0000c0400201c0c0c002501503583d40340c403010f0820014440005c0c1501135841d001d9000c41c1c2c00004203140e80526070041c4003c0c8844a48030400000d80b00c0d502c7c1069160041c010701c032040c0d170f800b00901e5203410102c4c6c1b070258540501c803240b10038102c10410f1800d243c0d048402040006684844848100d000f500201a121080c00c14101e18500441079004191843c201c0080244098080c000308594012a0140b24120304082840303010366140d041214004200340072071070032024030f00140c00320464121089100c1d0039000c040304903e11040d1010b80c003582240b020b00c417009c0380d0061a01b01520080c1c41e03251604d034040284040b503600c04002088200d0a541c00320384814810381c201d48503100d004000b5902c40391a2100b81c1d071203910030711030a114040d840c0004080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 20373747 1250 20372497 20372507
    0x70e09070e010c080c0c0a03060905010c020f060c070c1701050a18030e15090901030f0b06121504020a05040f0501090e16030f03120608010e0f03031522050c071101 72
    0x3004180d40e03010b28064103941d455500d80000611703c1081c06078010195071525650440da0096024110108024090382041d43c00c4a000104040443d08901031b604080440001ca00c0d4002d0328a1501a903030701c4503402d08040c1550143c0018011403495a0410081041500150b00605180c3d004005a000c00341c035550300d0312008003004010401010003d00300349041d400c00b1010500c03114020349400d41070000611130b0300098008694000145248400f4803204480c1c0d158450f030151408000024003002c000ea894821204110341440d1420000d411901c0b0280840010400075005110301110203841501a103c240038903c925894846006030328040007038101008101c169245c08128210340310f62903480c8d2007d1040d4240f19a68484800c00c8040380300f0032009000030000010051440f030305181c02c0100c039204a000c01c1c1e0061003440104680c00b4041042100f00b00e88050008280c158028500444c5ea00010010fa1511042141101241300100241c0d4458488083c20802120045d42c0d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 20374997 1250 20373747 20373767
    0x103120206010f06090e0405010e07060c140d080103140705030d0905010e030a0201140c030906070f060b040b0303030613110307020114010f030b0105010c060902030709021c020c0a0201030c05040e070e0907 90
    0x20000d0305c0c100c02004030b48004440c080d00940a2400440e000c101010303035610b80f450a900c80c0c0000781e402c1c0e00090a00c0402c1007013801d1855080040d001c02d240700c242c0103200c0300042c00050810190030313a03180301102003040048000c1c840a821b865180c003801c14003510000d517500c140c07404240007000c0a445c81c9000702c0d103460407940c161110043c0d01000b6a03850b0558005090600030391004005920603559a01c0c00380080501c07590011003810b0641c40c0403029507459a180600480c2840042005540c01109403507004d0f0080c7c41002441d80c001107640045c0000d000d040c3c0040c0e07400010702815a50640044440c5000000c400704140d070f0369498035a042c0c030b8611000d02040703480d6005001c10743c480c03001e40111600038a4041685129500020304004013684100c6109a0020743e04204106585028854070300e079080440c01c0180342c2c3c49041c0c854940200c002e04051780c1c0ca62011040f0b000b441910042c185d100041603c82c540158041d04000444030600c3c85503c41c840010b040c14440c0d16609 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 20376247 1250 20374997 20375009
    0xb01050705150402120a06020301091404020f0108060402040308030406060e0601051303060504141621031b02150409020307030506040903020c010e150a0306030215030103020a030305210103120206010f 88
    0x611004940d0140154405441241c5c4001d5029000d02ca84a08100004069000b100016030f01e51410704490101c0e81c0066012802d016807070108000350751a8823014821100a0134176685555135200081e0080c4110b4000610703000c0302206200900200b640300e40c0a0350015035441c5501d440e544010351b0b4900403194843c1c07200c082241e0500008441e138200c240c02070703c940950790300c039040e6189a6091401146902002c0c9010305020410392400100b8401500411900d0650070465a1401811241590304040640d0100c40190046460700c3d80c44c1307000b40c812248481d07203d135103844558000c0d610030b41d8503000003818600400d18500c2c1ca48100b10305254541c004105554500c4010f4400c07500301c52416034400030565050078040d2040008208a201d10b503030016403a811441004403030100184c00c03c020080c00d000520050301da8103000000d9176010f00300141c950715440c501d550904081c84114141d200780200010030454620b440c02c4503403985400f503e100c0e0380c9680304a888204030384242 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 20377497 1250 20376247 20376253
    0x7080606010513170a020405071806050405010c260705060403020c0105090616032a0314070b010b031f0303050a120e1209130e06070f0302040503030405210106060908010b01050705 79
    0xc01080320210098005a41e184c42910000c070b0b9660005000c5a808460500210713003007c3c0340741100d0f5220101d170300c081c10403030500031b007413a0400c00002d00300111680d00501c542120180c0000d884142c185071440103860042842c2e5030011460410740307402041d80c08402522800b00104d400b50700079002d80c3c040c044050b02003424120381845a00d0000a01c410036401c0c010f001010b030703102490000c00b0321808050b000c3c0d1720700b410009280c02003040d2000b90441500c58014031407803000460001c901ea04403131421403161b48079100c0c0400e90024070700d101d04542c460140c07204000b04254024001d42181e11403030f00c4080c000310030181c808040e9046850380e40f01d26040716540801a04440300605030600019019a130902084a1300108503002c111201d03a1560002c1e0800c250141d00020400051034603207000c0d42418944804a90388c0e0256001e483c0c490b010880c2c107030a03100080c800b1188038248101c02804060343e00e00002d04850303c24040c1503003950034866205415409041180c80c070503072240003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 20378747 1250 20377497 20377499
    0x20303061005030403030216080405030f0c0604050d080408100606090503010c0c03030c0c0c08060a0b010507030206040f170a0c0507090605060403110402040e15030c0f030307020904030311040807080606010513 92
    0x1045402d07500080c0100c003130550034072403074110004074040317201c101d441600010340e9181418209803614031418a81c1e00c0a620a200a014075100c0c04182d604a604c243e41c080070200c102d15040449000e02c2c3c0094801e0321603030348030310245082908a81d01710b50036600d0300310340c8035111304c02d01d804d8840c0c044071500071038030304210707200000c2c82940030450000f05441c1c5101245000c2c0e8400803c9400d65110400942c401e00030b2040300015441100c0301d20400342081d600d01011541d0180d107445000b44064900b0401f04052001e00444460321403100d114848041d0b9a066460300240001c00c0748942550035210709140400c0c40c2caa80e200e00000c4c2c450040c510760501c1e146a8a80000d8441c858509400940038000041e0080a2041c40750081900000050303c0350703841c80501d498080c0b803010340d40c410b00000b4000903044d200801107648054040d00c003d4529030b11418254040d064031a2140910a0000760024500030041500f4098031450003c0e50000e442c0c0e0001122035005d080c040102c03807030034114 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 20379997 1250 20378747 20378779
    0x703060f03051c0201150b041d100e0705090d05010515041a0609030f010903090603050f100905060f0a06020c04050c0f03010510020c030102040e0a050601030615030921020d080702030306 82
    0x9403000140f81440040340300e0741e02c6280d5008503181503002168845020600f40306c00b500751005020803c4210454013581e180070485015022210321a0032044d203111000b05440c28030420883e52a5000604180b140901c24600b060007040b0441e148907091139000200c0815140034017801c0400d032581005601c03030402510401c1420780c00f00b00d2580d0726109030b16030703008010001c0c0500c00406010743c50b80081c4034075180014055440013404521811150f804010800c44018842801d8410490380020a941e400c0e02148000171010700f19540000000700000e0301c3c0398009080041241c007902c007804603032541840324149000303240c9640b0806000f800140000e08201c0451000042c40e80f046035425112180030a00b2a4065080001e54050910401c034400c00c050080030b8101d5400e280400c49117207015059080128482c482404154032444220103100340a6500d6116854109414900c94001403000e952812052900030200d02e14200041600b0300110980740300710009000283d001c00349070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 20381247 1250 20379997 20380033
    0x6010207090c0903060c020705150c030301090c2006070f02030403050a0803100b04180b0913081309050901021809070207062a050c010801090204031104020f04170102030703060f0305 80
    0x140c804041050090700080407418502986c0d00081c1690003600c1030b18140b80520400d01108030340342c1d40703120007003084402c0a00008220380c1150001c4000041d101d503500300c201d5590110700100c140004142d50b88a101c0c010120310580240c09a880791a144203040505036200d024610000e0841e810030307503040c008034a582c001190320000c0c0c0600302038065118403006070543c0054002c85542602c103c0c04010010036072260800d984d400300e50501580c0380240e12240308914103480281002c901048901c0c10043c02d4000101403c4000d1061040c0c0c54007828040c000c0d00400d0100b105c00003d005030b00075070b0504240d481c2c002c01311580030341122420540182d50042c1c81900c80e4003007086034442902d0000c03604010f0400c181c40b91029108046a40000510000c0706030803800300c00c0d10402003003002401002076046000002d40d009600c5150380003090324a4015135000c1032881d848040c0309500d140f0103500440c0f050000d82c400700021912041c0d0b200c00c004160000400c10f50003080b001c018003244c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 20382497 1250 20381247 20381261
    0x90b090d02060c0d090e0606071e080903010603080d0b0f060301060305040c0f030302060406050c03010f091806050708010e0a0507050306060903011d03040303091e05121005010f03020f04050601020709 88
    0x1d0700143c9010701c040511860030305059000c000066103944284015405e8402e0580c10030000c445040c20320b51241c5400e500316802134050300c0c04419420010040069040586462510044c000c0001a03030b01e00b000c10403580501d01004c50740d8544480c41c5000c0c540379503111144400904810f00b07580c24407106800030500640241e03581f40c254000002c14101d168010303400386100f07901410060415180010903620301900801d1000814070061014001102c100b000b181c81e0107002103090b451300003c0c10220f604641c8080e008a0828040284c01074001c0c244e40e04035800c4c0003603682642e40390392103007089540a45e018030004008101151491a100d0701919001e00000c000260300c11000782c4030a00300c0c040305602e00707103900081010403e054109e42000024822040101ca00c24008903036000b0910980c01428032945008182c4504050200541d41401c052064100044e5848a400032940c04486c8001c1344200c820249644107414503004d020b000e1501a00141981810300c101603000d0010b03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 20383747 1250 20382497 20382499
    0xf080901140c250609021305010311060706020c0102120403020706140306010305180d0e0a170703080309030d05010f03060605180114010e1c050c06130308030a0204180b03070501090b090d02 83
    0x4844500b202003203101601c0d0b43c03e1841140c00140303240c01d80c418006050401c002402d01185050b00410120707030800c41761100aa0100c84051341c804061405100a02500c03006101942c804582c850110700e0071504c5c240240c0c002e40031100309036035030740c000c0780c10300c4594400810084050022641b40c3d4002d0b0041078010034010703c80a034155440843d00d1501210010358400640c40341c02507990390811030ba250b4041e14410790805a0078260030400c60f6940014030000307060300300010000c0e903000c10034070685000942007007050100e940e44415075502c81034540425030f84640740800000c0d01d031a0203018050103512145e1404210f030320704120103900f0350803584030034103200000400040740c0c0d480441800d070a100d07030b2035251903030051400d00e10328101c0250306017801150300700101c0c009005201e036200c00312a4400c010300d0b80c3c0d5458140120180c05954000da851032402d01922042c0601c0350094040094240d00300c592043e070f80c500454440a45104030400580700f0041490907080c680c00b4901d02d140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 20384997 1250 20383747 20383777
    0x120b130804290a020a030801050a0806150a1203050306040c030506011209140102130e18120a03090807080a0e030105060607020603060a0512060114010f0e040e0c060a0f080901140c 79
    0x41c40801850b45a44800a0000141c01c4000b40c1410540c1003c21a0b025140c140d0b02c2c2d401c41802e0100035503454102405a5a02c1a5510880d014664458000a010f480c21001d4048000000d180250040d041500e40a208600384409a40e04d01c2c0300388906441080305075158180307500454007480c01440110381c2a54502140c0c07e5001001301e0900040c201e548010f121055503914000ca0759103031801c0505002410031000c0c11200400707800107626104c41c80e500310741603520f68141500f64000d250110700101614004501c01080c404510044d14020000c0c0c0c907400c80320304596003018200c4000302c2c0c83c564400801c2c0b0040c005070400304041c6a00000c090800c006150320f4500164480c06151010217003a407181e0011701c00c6015541c1d005d40f1580003801e002e40200c940700c0b009880c02c40707d810018003641d0b0343e042c1062210805c003d403081e8400d001d001d10b584c0d03224509000340042400e82403c00400d00b6040841c4849e0310512502c00e03122200c003950f00150301e0328001501558421609451f02ca0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 20386247 1250 20384997 20385059
    0x201020109050102040b13080a0503090909070503060103080a031416120e100b0310060b07060902040b0409050102030615030108060103080a0909060801020405040c08041203020c0a0b01120b130804 86
    0xb4809100038400b80c240303088640d0b03d8140b90320001e42c49140c1c0d0b42100801c0d82003410b1000008800005440003c0021900e00e2400e5542051a07481e04e41140d1125505200781c270300010a0202c000001e08003a1021390b03092100b00310913054012440300640300e5201421080d400f0300581407181091b0070b42c2d003030b42c3d15000c03034649501040f445c50f00002c3c3c407640550941e902d04040c0300d07140c108078541329402c000d1801d00074185000041411070083c1d0fa40505503688480319913045540c1e41d80450030004000700104201e00d0141401d900075001258a00d001d00035070780c01c101210620b034040c0d034101c503015002084070307030300b140d079000c010350030a00c1a1818813503403840105000c0c82500424018090300030005031a02c4c0342c40b08201c10750b5450324113242440503880902001c03560009061a40800314100035079204440014903280c03d2058070050141e150081c00822a06542e40d2040030050080d83c90740e41d580c4603035107084200c2d0b0304e1580c01048a4070030081046040d003a007031420f00b103801e2405021094 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 20387497 1250 20386247 20386253
    0x30e0105191d1209010201050f0702060723130f0902090616050c0306010801020a020c0f01050a030b010203090d050307050d08060d0b0601090b030a1e02090a03061109030a05070e0903090109120201020109 89
    0x4030405100d03d006202141c20f9426590911811f50f002ca80c9138001c0c0e00f030381851003002c0d48403035000c1c1507c000c001400c4c50b0340d106410303213002141819800c3c0a40da6aa000014014102c0540e0fa02940c0025948850000340300b8070317a0b009598500301d008080c0f0b8601400b004000d83c034816001c604840d40c2c020280703407099613502400024024000d1500250b40c0d0314200500a0420424406151040c40c81d06260304459a201050362000c00d40c900f00001c0305440640141d203503000d2000225031040b500c078050030400c0004070140202da0b03c10011134000fa01600019520318400f02c0b20389410000700ba0480000c0788802c0c0c040c94000700c060500d60071190315603005101591048500322103e81c0c40740c0c541109070306041102240c02503410b408500302a80d20340001c40c910305c41c0c0310180070f5907103070f0344003003034110207402103440e40c05004040f110703010024030380f081e21246688200c2c103810030100700094003100040115589504160340d882e841d05c0c1020020f008000610300103904640d0b80303004d40340c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 20388747 1250 20387497 20387503
    0xc03060204060203481002130e060405010605070206030a02070f080c240a0f020c0304060e0108070e030a1415010618060507050303010905040311010603060507030e0105191d 76
    0x50182e6070b0207103549041c642e0410100e41c4e00940d07540414034009072400400503400384100948110240c0c4003c0c0c00c110703210450700e0034111031006040c036403002621100c4c03030006800c1e99048641c401024005a9500810002210030034030030b16010030ba04001500c01171818034021035000c21305030350040c18070760b150700c0b42c06400c411401c044a0801c000949140e407071804008184015a24502e16040da044426050708000800b5050707000d41074498001400101894050740d42d64154001120349440d030f2032100415a400c80852640802e001c0300106465501ca40c5400843c2000079000704443c405561300e10602024104a00e03d80d80102c5201d082e15000200c0305500908a0744c0d01c01140040704000d68004c400765130b1284c4140a803c01002c0c1c0090f101200b51b0341100c41800c0b00050300d86c1c443c00c0c161004000703000803c52035445d04001008002240e40001c0c00780308644e400b004118071800d030305801c8403001c0d02c0c40704a0101d2490700035500140c07900006124594881801016109440da45107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 20389997 1250 20388747 20388749
    0x90810020f040b030406140c07050a0212070509130b06011e050706060e040b060102010c021902150f0c03130b1809060105130303030b0907020303040c0b03070203041520060108030405040203040c03060204 89
    0x206c841c0c03905001d01001e034001c2034203600008203003010f030b00c3d1164030303541c45a03940104c90b0028081c81c0404944808210705201500040c40083d1403200b00e1300e051410020060102c200c101e80000891002c07134440c4d4441c1c950201a40310b51120070b601640d0100741910075400c03240d03089520640380c0201045540311032205c1802140701d0601c902e000c2c105036002a0940710000501000c650040c07003041810744400401208050701607900041203036441c079140941d4418143c81e1103686000003414120b006000005159a54107182001c0032503450b00303801e405902c44c20949200100b080584c4c0710261030f0012600da00044141407862402d840352950918407400c40d441a40882e6440c00028028102400078036408003880c07010707502e140717050380d00c140705100c99000e4206068008000915803030b0007003040790040c006c8600590700a030316020b4000c2815802ca00a48448140240e60103520781c0000317506410b80d021480036600b05401c100c00e003c0250401001980c80400840300000411100c0c40108 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 20391247 1250 20389997 20390003
    0xf0809040c0e040c0e0609040509010f0905032d030f09010905010e031e040e0403050d0b0405010f060e0a211a090106170a02030706030b03010b09070519090810020f040b0304 76
    0x10144001060803c0104c8118400d00b809102c0300c4298603080d541c0380c00440304204022980054944c5071000384900510200e04d80b140c140746842c01460520600202034140d0b009298020440c4104a071400d50204104624000740220b051010840302d00d10000c0c21030340704a003d000042c0d40f29150b10341710301b503407441080110107070800100014403200c002c0303200354081c80b0103520b02e150a1900b8880300c1503020081024003001070100e40592100303070541042451a200070705c14480f550312221b0075222000580300da0004030f2070900c10500582885503000c070482d00b0902045c200b40060160041c46502c0c000d500310303052040ca02d900410400400f40460040ea02c42d000020503a05045042401c04210382103509940d0140803c04010303907000a042c41510144c1c039002c1741000006011a016190054074140d001c081e400400c8421580800589030780e01c0004680f10821400d640c5c00c0c0d4078260345000e48a0941c2101919019062a070b8004201c82c51510040c00c0c9020740d202003546c06504141c80031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 20392497 1250 20391247 20391257
    0xf070209071b0c1406090607030c080717090405070201090b010302040b01050412140601060c1106130306020a12050a0212160c120305071806080723040e04050105070f08040f0809040c 80
    0x24070150002d604510074680d130a85040b803a1016050000d40c0b04c1c06064070050411040c039200c0300c1007110f02c6c029941312640c8240c04bd40800400b40c0360640302d4100e8240c50b030080d0716103030001c1e0042d44140141c151a43e00318820f10403590842d020700c0060b0825000b114140301c4100320000b413044e0103180100300c65004001000325002e60188142c28a030b0306038846070801c05001d0300c4401041140114003040c85080b2495552030348042a402e404540f583e01c0640140d2012580c561a603030004015a5203102328542041035a451300c814604901654041c004202240300020301d400c1c03101020400c90301c0d401d040c1900710807030316645c2c034202060345051500000c0c0c464060203005c039000460300d03540c5c42408880302000381c20264010f0a400c1d00800450410051109800d10500080419040344120004865403540c0b03490a4503011740303041d50102c9803517282c030f000036001c40e101c2c8101d609841410b0350745481a850326140c0c5410344405510940308483c0800400e4040d68440c85200c07004c8843e40ca41c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 20393747 1250 20392497 20392499
    0x203090307060e060d180206041d060108090d05030a0209030a0f0506060904030e0405060a0e07020a0b1806010303140c0105040f030206090d0807050d090204060b041502030f070209071b0c 82
    0xe050601e9050b92080d0180040e404000c000d40c0c0e1070006691072070044042c0003550304800010440c0d0815640e0020350401000980854418407075081862460b11f555030b442c030710b52212801101c0d0444120740120154224001020003e03102e20015500592900005030411440c0f00019003040100ca000b00d80d42031400c94000e0400000307100480d0720007000c4801d40d002c0d14164601600080d54004410b10850380c0b140090300b140d45107030107400907010303441c088619403400403006035072071503000c6042d501b0381d801400162a801c40e40e0005600c2c0c002d04005020141d10b1580c0564061007142c0e0648002d40041c0481800f445003407044d9441036000300c031032030401005418042d040c440c02400e4400c05400c090124a1496000301045030801018035002c3c0d033307580c0c41e0980400100181c2000940c010308100300028602c8c0701030058010b86039108846031540031461801ea07174a10622980c0f40702d0100902410f005031510b014440e601c0307111800c3c08006c01c000740c4002003d0058403c0215440115500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 20394997 1250 20393747 20393749
    0x1a030403020601060c08250b010602030306030c0f060904051801020309060f0c070201020c0603060307031506050a050d0c120f1e03030506040603030e12031b0a05010f021c0b150a020309 81
    0x2942c010700417414958200d92098031411103900c40c06200340f048452687c00c02010b1140c018404a081d50840401c602c5da5071950070081d12640140d51280c820b104d0440d11501d1860700c0810075400c03d04c014031b0345140020031000e202c05050010107102c044020305410740c07104102070005520640c0d1550141c111403034000a003c0100300007500c00300032401c040c41103000507600002c4c0b40001c1c21048810a86981c1c410300004e1a10001e0b420040c030400004041a00000c1990400ca0980c2d60880d1110109070300c80d0240304114144002c080c120403000ca004001e03c410320002c0400050150807032080441640d21410268040f450405001c5803007201c614040c16031610074603401280441d0140840da14640f001032580400c814494400c17511501080510a402c0003100d20360b050362140414410310090300b054480141c901c1c141c40c43d50a200590a000d0030780d01c00c40e05a4030b006070845400f0080c2103900001400d0004d6843d41040c0d8108180b100141528090504002d1603030080d40d4407400e1030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 20396247 1250 20394997 20395003
    0x3050a030801051003020c030304020d11030d030b030c06030403020d08090102040b03040f060f0b0d080318060c0c1b0a09090201090902040b070203011d0a030c0f1a01060f020706050912071a03040302 87
    0x2d554042014030500c60241f1018002c01200e410540403550240910b12a0030000d807000200c4501ca54907104071110340c81c03e19099084003003490021000d4031b0000800f2414442c6a100493740180140c01005c413803d2082e004201c6d99800961401c001402d09403691100b9803161300684041d51300a020034403201c04c00c4803e0046500c1031000740c00030321030a402400820781d07072212220002e201c124040000380c200103003841c502c6400c204020491f8041c1c102209400b440ea031040c0a040c0b080d01810030300310010001001c0b07600383d540c00030b4801e400d950301c1c00741800d0003040c0804080f410000f0303803100091821400e001410150941444180d0365483c240304060031100c4035000c04056900324000c416101c03601240700440b2a4250400c0303c0da41c01e10307160810281d03c2500000700380740416a1030300d40306541c040d0502c2c1a9101a00c5a650201d81c41000766940c0a441c071170900015820080da2a01d810444591940c0745c08a004941c001074550300c12100d0040c18441d590074602c008800c10080c16410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 20397497 1250 20396247 20396269
    0xd081e0a0b09101a090d02030102030703020c161203050306010507121d01021504020d050a0b0103210206090a03050a03020d1a0102012d0c110d0e04061d01091503050a03080105 77
    0x51400f0680c2a03e08041c01c121240c42000b18540b1182c04a10340c04107440d100c2c01004006d90040c02159a4607106e070380580290020b1001c10500c1c41030310030143e00001000d01083c1030306c002c5d80302c40c409200d4550303007102e00340c0c0000d001d14100030050000100040b284000c50500c0e0806441e030705500900c0c0e030140c20b640c141d820140b03070443d40005405015800010902c6410680644042d00035001c2401c00e0f900d0f080c1c01e800003c2540c00c00070000410302c003c0d130b8040200d000b0f80994a080c00e03104840200d030b452405880000c0d0070780040100f200044d009800510401059040240c20b040d044056082150150110023403401e0a040000502e0369080c802c0c1c00000701c071101a40700541c90221607254641a03000301152781070380e5581c5134012500417200216a80040710450f44000192100148481340b056400f90260313041c1003002c01d8500580c20b00612081c8a1900c0b154960318022440c80074059865841c262007884003000710101d542841260346450003a10340d8000ca51416050002c0c2c0000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 20398747 1250 20397497 20397511
    0x30f0f0c080405120703081801080f010e0609061908031b01020307080106110102090604031b0602010204050d0209040f02150307080106080c07080901020717070609080607020d081e0a0b09 82
    0x59030303024200154044040d5016107009544041c01c0003840c508452920320642c0000d4400000070412044020b00f0080001c40b159003a603d6240c40d49400001c030301e80e10002c0c061450010001d500050341d80c101a80100d50100d002824403404503110204810b0f5140183c11a50494000007000c81d50300102058019180c0540d0000310300d145001c0707070024143d0f07038107014410402c104403016500520702501903070900c04004104a558550300d28043c0c0c2d042c84118120f43c1181c40385400096000d00600c2524100c40703002d0301e40200044268204500000010401c50b500903000c000703180540c8461150307101031190700c1e02c510f5403814a10409088910143d00c0603041080400801c01408016015110301d0395003e41d41540b1414082d0060b400c2c816160811044041d8051074003181c01800a02074040700e0360b9451744a0350a0b181c0c000e05454890440d908000350780444200004c491160040c154051071401c440b8040c14180c100442c5403400035245014000e44511001d50113241510700d164022217 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 20399997 1250 20398747 20398757
    0x50906030a0c0b0d060b0a05030a0c1112070c0f08010914070302010f03020c030909040309090b0f0603150a09020309010203041218150e0307030c0e0106170606030a1404030f0f 77
    0x496500c000080255000d0035030030000109526030f0340301c02c1d0741003600603082d001000ba4072040c1c7d451004100e50002c5850301c3c001da0802a40c1c4110a014040c11402c03010340340080c01c0c83c2100541c0c1d2540513031000c0401c440c076850b540c0300040c1a0740a4058000034204400c0041000602c50034800c40940303411420700580e4010603403c000503030300801d5001401a00741409605d41009e9903805080d80114054103420880718400c0104147d4025054026100610b108001040b191000d10074a00c5001e400e0f01e030041c0c0100046090b00843e112441c50380240249500358450701d42280005070b81050f0b56000f03c40e9004001e12080180307040c10801c00320a82d2800c030184003245100201921503d00c01c0d02e418241002d8100a0a8403441c141111864082c007250000c654915090951012609c0b550f1640c83c2900d0001c40c81903c210703051242260f41390b0030302d01186c17100340c10482036500240c82c02c80c0e100d030303251034480c442502d411246103d42e01a8540c0100b042c0382030400382280290b0b40780281000b07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 20401247 1250 20399997 20400013
    0x30108060f0919020126070801080f01020c06040204020f042d060806010206042a030c030501110310060302130914040201020c0108160c02060f030c03010609150903060519060f05090603 81
    0x6980900c2d6070b0043ca409280803030301c01c0c540c0c0c50300b45241000c59110010162012040204007500003088504a130141822100c0c0021400c018900b03e0043c039403d890290070440108002d442c1c81d40141404840d81c08445107850307a80c103001c8140c10380903001c03080c001c1c1c0405900c2107084d0021042c200104241d05020781d5510702200001e4031100c00420040001d00c032400c0d20504202d1020b840100c08948845003400035480e410511800003032840211340c10340c20098010514000241034a000b0f00605901700c220504150003940a50001e00b0720440c4140940310002c0c0421301406880451807a14240d50094142030000a0400b100042e200341401202d9007440b16030415440101c84006240c90f10200e0400c0c2480040e409206818407800c3d28a404418007244400a41c02141224050788542140700c0d80c41c0400820380c240d070700300c0101050b40004204049041500402e9101440303840d07218010a00e400d082049030002e0300124100451800f00740b05034107025401903003041e0100c1c0184505 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 20402497 1250 20401247 20401273
    0x3050408030c0c010b04020a02010f0f1109010809010b030106120209060a062102041206020309071a03010e1305011505010306090e1902031005040f0b010501030903020705010f1202030108060f09 85
    0x6807202410007000034800044844292030300b0b50211400e2580100159a03901201d04002d02901510384c0c0004d90528001c3c10700600400d0744500c82401d001e00002d2802c0c40740b0b00005544c00500145511001c2d500d6001310101c41c0d400b0300c501c40c0500042c40000907082014014080380041c01001c031030242558143c144512038000040100810090200c4500d442000000002900941e40f03d0000905600d85500800500f5009184100501401c80d242030f0b036200b400ca0001e1440d22503060314400108018010440d03000c580d107074010240c50b101e40d0b200d4400e5464908644100c1d5401e03001000c4010188801d6031306000d00310050105810a102040c0344d042400d8450501c56902c0c2000e04a021300300c4110740b014803c146000404003030410841c40c047c14078110640c1e0850045403460307803000c004610342d03010b4400e8411694043d40100103e5081c0300056891072b10724103508083c04003030241a42003035000e00046000c4c0c800f040c00b4040358140001c041d03d800002620078030241c0c0141d10fa0b2100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 20403747 1250 20402497 20402513
    0x70e01030305030f18070902093c180a0f06051306030303060501050708040b071a0405010c080f0702061305190501020d0506040c0f050d0f0903020102120a0c0c030c080c030c0601080d030504 83
    0x47d51329000b0b00590b80c44444001070340c1e8140101c4880c03d03860220805001c00406c034158041c04141030500c00c500a01260200316a50406105d584800d00704440130075411031055000051031802e200d03000801e603840760f0015240b07000e0348041c00b01d205e0f192541482015030601850005100c00c2c00d00b0b50400130166261581030055000340c0000540101d201410b10101c4c0011401f43d0240030030400c045d0409007403e80c0030b04410400a000b1034144000b140325022080309a5101e00c2c2954003030089501d40c2d0092a510419884042d034040c030903503450140020741809269103041c4264001a034509880d120728040ea4002001d4502c03640c5409101d0700800c0c2c200485c6100e8040c2d41c54080e550300b012184190090140ea91100411440e107809c1c041090b0b0154001c1030812441d6400304e0580c0e440025071030a1703401f0300112400044c442e2412030000b034058402511414800c84d8000d08080c1d001c140d2501d581c014274070080042e40600010880510103002082400308107181c240100e1a041c0c49543c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 20404997 1250 20403747 20403749
    0x60e0103020d0204051009031202030a080f06030705060307092c0106050a1b060608060a0509030d0903032306120d08060d03020f16050f0a0f0306050702070e01030305030f1807 77
    0x8141600040c0b4680d034120a6411a40a80300040c005008112000307030090000400d800210351540000c410084824000015240307045190380da007944e240c0d03801f103044c00d40600142910340c1504c2140c1003c40c6581e14480a103100b04240d44e1803101d0b041c60312006290751151442c4102d500e845542e148449072103008038140c1500c0e407609180b0760720b140580b03084440e002955a002c110011080c07803213041110b65000402100e54003003c90b215500c6440601c01200c0c002e07507800a2030340c401c00c44d400c49480c00d03070006111580a42000180b0901a000d05514075101c8840701c00d2030100c04d0200086072809404201e801e0032017000070700481c880000041e22002000e001c440c4150210300201d0f040500c200204620a0001d03000d4a44107890400291488002401917610840c1185900784035800d091500700100c03039049a00b00403051450b15000000c1a010b0828411405000320105080480c0044d95000b03600ca9600c82d0381d0383c50b10402c60320503410301820014454882c1c08121021444c0064488 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 20406247 1250 20404997 20404999
    0x2090a0909020f0f031c0306030c05012d0309080403050303070206090a120c0c0306020c0f0f0a0b1f03020603010b07060b0901081c020f010e03040311090601020a03050c0a06020403050606040b010801060e 89
    0x100180c40388800207031030845081008170040e411b0f0407404540c9981a04010101c1c0d204042000c4999120001580c088138040b0380d119a070880c8210822070040c0c40b00382c5100b00f0b2000e0400042e0030389140c84103105d07903106030401d58181d40004244141194100903207903100240308050107049a0030741d205e454802c02429000c080000d2a0111f206102c5200c002c00c004642c005000c643e96034250781000d807141c0f13245c00c0e408440e015822490306503031808243c40b0102984500034007043d540700000803901c0001c01500d02348001c80c04e05e0120042e00c170340c40194040c00408900644941040c6000d9080e98800c2045500135000480104800c40d0001050300c03500000b444020b61070202400102e140c500c9102041d10550b00340b0311441d174076242c00702c01401500e0150560740701c011801d000b4480d000f0703000d4034540d00682c090340306035002c07a1040300600400700030581501c5054201b512150700341c3c0c1194000f950070b504600144481c0b868188074a104149082c28024560342c035102010740035100c81c042c0302e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 20407497 1250 20406247 20406259
    0x3050403060e010204170d030e06060a0902220f091a06070222060f08100c2a02030a030305072309060d0f18020a08011e0b120a0602090a0909020f 64
    0xd00c0c10020079015200a01703064001c00c080c480400c80095503d40c070201f1184c020038a0040034807844031010811a11560010301640c009900d13003074400e40290700c03034061355070740c0c3e07a5096900e003031f191503c490580206244010101034608040846003201c030300420000174044401d180610390384813101aa094142c040b280f1800e1210104007501c02d400e13020a090800700c1c43c00002040c21420b20340860140c0d64880111001241121800012034102186100208012900c105032040d092104410b06601090b520000381d0b4080c1d000c00d18214840c0303c100d0221b81c5545c10081490b0380280d00340d88031128000c02821020206610310258800e400146005020002d910341104105401c180460b615000040080c0442002c60380c140b6001b498003288104020400014001014018082403000f242c0c0341c001030071402e0749020014040003419030303000342c842c0c600744c0c01101041c405104114058800035075a21401c004010445116070884802d482c07030405602c025858841c5104c0c010301054030720b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 20408747 1250 20407497 20407511
    0x4030c12021005010b13050f09040609051f050114040902090106081003140a020414012412020d0605100203210903070803010303110d030b03030a030510050d0303090b010906030305040306 82
    0x80b81000d044401c0800101c0c03d0000014490f10028020000b40744c00030350002250346c840b0b0400070120a50117455922220030004180492440d80c800715809110b06d04440105280744a42c0c4050000882c1041000d07030740b100100941035103e48003002028048808008641603940042e00020041c05070700c080184983c00130340190100e561613400345401500c40c0b0f07400d803822040c81e955481c003034408038080d6041540c80c540b000c250074905810790380304c0c0c680441c0d4003020100882104000704011000c000b211a4130032000c4986100401a001c1d82c60740110f215800c0405102d0403050540032582158401c02c10b890b81362441d08219004100040401ca9030341d1280c8911714035500840070050322018001000000300354000c0503000c0d40d000030000303070348441002a10a404403607010010640607042080400074070f51190340015800b01aa004d02da80c02038407000030940c01d410560044010a59480f030940a00024041041c0105100d4605203c01070465074001c00301d004510004103801d4551007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 20409997 1250 20408747 20408783
    0x901060c05030d0c0908030403060b031b06040303110a02060307020a0b01051215040512040602060708161b06090b07111209030304030215040909030e130b03030306010f1404080f06010b0304030c 85
    0x307001700061083e40300b00d0f40c9640e1a0b0624000400c1040c850074886d10072100d501c0c0c482680329480390038240000f00344504083c43c6841c2541c1c0401200002c441c1801219000c1e001a610030015500581e100d5005001000350791034200741d0200c06800c030318405ea8913030707840071919000000c109200050075103484a40d13448914003503140c450444440480f0a40101d40070404a0380080c3e540d20601c0d82d5540d00b07202d03413641284105030340d0b6400e1001d40001c408502e8030004210001001c5806481420000748000d815295200c2480055810200180e545094545208400c00c4032102d00d01100744840e02d8117155000007580c92241d4070009004507000c0d2a00c06601c1040816038005104034201448581c03070518000301207004040246128500141c08515410300c0c603c030b520000b0402034011340c0b40d5182e2600645051854580348400c2182d406402d40400382200041d0004000985c02040c03d21641c2c0300050038544160000c02c6200720900c1048046980075010310034140d0000130303074401c11420030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 20411247 1250 20409997 20410007
    0x40203100b0109030203062503060b0702100e09040803060316080606010e01020a0b01120213050412080603010b03010612050d020f03070f0c1707090e010b0a170c0d0c050901060c05030d0c 82
    0x5132000c0d6250003654108084000346011544140c00d0702d40c5a035860f0600e501c01030b07045070741c00d0040c000c1d2400d00344583d030014240510784100d000b00e40d0a080c4140003481d00001c02c05001120120341a000220074416682010000709a12410700b80c00c00f003429041131070440c0d03946001460541004080511107141d03034020700c403003142681c026a80500568442a10420034501c01004034010407010000003482c41d070a116403401345602c800d40c8007203c1d03035a240413200050007500080e0326540c1c03002144440d503001d210704002444038a44071041a661420141d00b0b040e0344100c2c101c00c5d074009503511910403002000311021142e1011901d511014103041a83e0f02050359041603205412a04000682d840001020340441d108038a040c000441020082400e94642c0c8402ea80c000b2070300300c018044928140e0011480820181c206e4821480d9580000d0306c0000c200002c0c0c6529410303007404c0c0510b0412194550141655050091300203550307a075000e07540d102d034641c10007079035a0380c804901d00544030b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 20412497 1250 20411247 20411249
    0xb01181409130209091b060a0e0f150403050a06060801050105030303011206060302040c051b0f0d0309020303090d150b031903050901021204080f0106140d080c150a0c0305060108040203100b0109 85
    0x1505614051801740102c2d41e80b40c200c103040b204204014442c026541c6011000c41c2c850780155600c208803681d0140601244186070300443d60700c00045e11180740505000302c0a0001236000350700401c41c540c20303400e0a2080b25203075042084940d0420b0010701040c1c80001c2186d04461484842d0070050409041035401007e250700000e52140c2811500c00301c0c19030080c080c1c0820703150280e010182d104010001651042c810200b0070b4203420aa10040e0034501a0707010240040c005015a45400b0b00d01000a10803482c0320002c0700e480c184810280c0c0c003100c552040c400d803110140d0040c5451500640e6103682c04003011230044c10010009030710440d0303034424060090080118030502d52615259016107407903401e8803000c150303550320340b00380007501c01c4921000055015011300044419440c0d511240007650108220150a20501013640c0340312150240091190401d01000950341d0b184c01c0c070003400c2d2207020b461541045019418007015980100e03050500c441c052000181c145512801640c3c0d0610f0707 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 20413747 1250 20412497 20412499
    0x90102120f1f12020f01110607050d060b0d06150305100302150d1406030d08060a0b0a050f180909060f0c090a03050a0602031b0307230903030a02010b011814091302 72
    0x4000205500010f00e0502010b1089442844400802e001120500c1548a00341c5896000c000401d03142d9000f80020a000103000720045990340c1ca6000d02d02303a92f03201d00c01052a541d6280010000c600350400e4480d0b0050080c5814032540c1403042440c81c44000601010707100381c000d503101030a008041c804070f40000d41c1c122000d2100707810b0040002c0c0000421101c070fa00900803101040c060700c0c8a814030303a12514000b041120084d0070602d8040e4141c0003e0726a5050120805c80c4213094501040030323003240710000e500d44c207100a20501780504502c0c09486a00c0755848002400040b40b142804103034024458800d40e912840150001a00d610444c0d0002e003090148504890901c4856002903206801c0344a803074204401c00500c800080c803007100c6060014003078002002100581d9400500d2940d244d904043c1480800780000741954450700d18040581c0d51450701030b1007540c0109490f52142c9804001c1a0240c0c900b01c12400070084800c201c41c8201d00c0c9000056455102c0e41c0280c040c603070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 20414997 1250 20413747 20413801
    0x7030f020c0a0506060406080307020102070b13080718060b0f09010c0204180602040302030f0f10020d090209090a03140a0507140109061506300504030908060a0605010305090102120f 80
    0x2c55030a019481d04401d5449a00443c10070802090400000088035220765040e402000d03003c0c40c00348006065001041203160001c4500b000050303485041040700051300b4074a03585e02c003045184a890003143c1c250f0703110b140c2e060307024401480180150815900e007a0420300300070003500c0a520016000b89011a425040728400d25008000d004840d400350040d244242d080b00c0441100f000c0c1c0b030b503460010642d409480d5010390302c000b80d04801500a808842008000454109650303400518000d00c103c0c0c4101003030b84852524020b244d4000f1700400514150303140315141215000f0020100d22031640007401e911483c003d800d8102800754024480790343c02003c1000340d80001034001002d480540325550010b0780c500c1c1c01c20741100b031201c04010b000e0004402c0c52140d1003c40180001740000400c1035050007507808c3c001881c01020b005440c07050112040c00111a4203020000d42114130146c40c150311a031040c0074080801400c012050303000500107140c10300076955201008154019031010000c184 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 20416247 1250 20414997 20415013
    0xc020d021f02070801060f030b0c0c0f0102070b1e0108060604150504020d02130603020a0c1202030c010c02010623030601090b03030d0f0204030c05040b0306041203020706090f0302070807080607030f020c 89
    0x20350b020580c0030607500000c00034059584c3d9041581c1d2104010b00002e01002c000b0750104580003e008010440703440044142c1c0e81a600d441842800ca030000401501c90140701c508202c060800003d400b195418140c04148465040180e99661820002d0585005607600c50201c1803c20040001100608000304255556000e03c0c888002a4000817106080000c100c500407804502078003e0f0b540d8418260344540e00c1420544600018080349103104040d4042005244442d080a000b06841031803190000306020b440d0241c20744d28840c500a18140ca61030300e03941d1400c0c2c0da9003c01d440d4111032a851000c80d070815500000f0f800e51140c034503070305170540c81c11001080d204416000380089a006a0a0034a001e5546003440b05881c105041260315070000000030300010015200e044001d041d80c940103003000e0f1a82d440d81c04031a4070041c00d0310110181940c4404141c1d0410854000c1c1000801820001d882c1c19062540c03020094009424907445400c02281c060a0764140c3d4907100b030348422901c0301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 20417497 1250 20416247 20416309
    0x4030806010e0a080703050d0906020d0e0a03021806150403080706050603120309060114010806060d05040602090a120c0b0702090f0903070c091d03182e021f05070c020d02 75
    0x90702c3c5c0e500c0119014010200303902c810314040c488017011100300d80c0151904044c1400308841459621105035440a021440403006d619803047e005000a108880086281000710400040820030b0742804c08210040005200042c1030006844c0c01c0c940c0000c010031036032580c400080c101410b071200da00301c0f200c0200400c140d4120000f8158122903140410005000d13a032001100c28900c1280c6842d0400400c2040c901c98840907404580e0040c0103080040c181000980003030400c03240d07907008a10700740300051084184528034404000502c582c445081ca0304c40d4a07804500d035200f000f4110407069403d0000201000703424021035044a500255002650781c81e060305800411a242c1e621001c24682c041d100c02c10b0f00000200c401d8000001d0344050904050001c01035841c0720301c4502c1c00c004411a1010640140b84010f0901d014499005019191140341540700701d940d810301452a424145428062030a030031450b82248a03806882102894405001003504125140144041461756030800420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 20418747 1250 20417497 20417503
    0x904030f080703060b040b0304050f060106030c090509070e060d0b03060406020d0e0f03041403030904020a03052d0a0c05070c0602070501110105041509020a0305070e01090609050f04030806010e0a08 87
    0xe4502589861003a921414002c4040324100d0045881c12202000148070000307142c8090340d481840703076082300c0ca1079000b0040941002400ea0003140480e40b02d142288101e600003c018020f0202580c81d82c0e42c2c0d24003008014500008068880e0085030001801e070010703035050300551600d6202030121880d41c206813070040b009600401151050038500004014400030200c0c403030884803481c000450405080c125460103c00686410703d034140300410440c6229283c1d4001317030240307181d240c83c000380d185400c0560b81c04503c00544825804503104611240d107958200784540c00030305802d80091380900c0b8040075182489101c038054111041203200084041c2d00260700403e80302c0c20707a02e400c1c1c01c000d001885420303038400342d90090860301d00c402102060203042d8002c620b610700007002c080b4031f50f682e0b840f0181488815004a801c51011500502100715240201c03c01030420300b20401080c600220366103039080c0c008d08014104808480816541c0e8864141c0301c1d9100b10003000002c0146e540d480d0955 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 20419997 1250 20418747 20418767
    0x5010903080f0c07170d0b030601030b0a060501020d050a1d040504150b03010b090a0b150706051005100c020d060617030301030b090d1b020301021209010f0b0406050315060a0302090403 81
    0x400c00344140003c0740b0b0304221056a655503403215000c020080030480001a03500300e1403640c001c182d556450700c11031b503a04118082c001c500a454101c801d08003082d0b403c0640d98550816030640d440b800c81c82105c540d0010445140c0368880c5800c01100090303000200340c4290500e50300343d0203410141484140000c442e2041e008007151101089500600401e02d801e8455840c40142d00c01c600034005000345016405c12120050000c01d000042c1b03c8445a4201503040440c003980d4160790b130342c2003042441100f51804007038003040799801da00404060000304892007952009000d500d03922110ba04002081c1c20070000b9016840c0207920702960204401d560350024441901e5680500c0049002c2c140089000328810b03600b592125040e410780c0320003000400d9100412038240d91300300250500c0c0d24801d40310902a803075000001c244019100b40c060300fa51083c0b248c0c0303440345180841c10021503070f0000c1e2001c174010081d0003240c603ea443c100020528071a030b500194014030841d040008155110306021 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 20421247 1250 20419997 20420011
    0x80a050415050c0105060102070b04260f0d020f0705060a030e010f0c030c0818030301270f060612060602030d0e0c0d0521030601050909040503160308010501141305060c07030501090308 81
    0x8174941c0d994004aa558903e84215111134200708420b120152404441011b20030000303048a041f82d1080d48590315040c4c2e0440405e105801540884038015818482c004148041100034241c450074240002c61503c41d400301d00e42403660b40c043d030201c200829008556011107610f401c00c141c00e00c20b10b01030701802c00401c40400098811000075204041d036520b28515404410046003945c0c281801d83c103e00d14031450011400303054108042c5a1001400391600111001c0c0e8041200e070700d0140050000c4401d001050b21540c1031201c14050681d00105075964036103c00800b00da01c45220100e0340c10407008440d0981c0001404446000380710002402c0e1210350204150b150101c4542c1459141d40d0000362900780c000349041161503024607240040513042801030040d40c0c9000c0d030351600040c2c8042080000c9010418410041245680004d072000805440e40d00e254942006407a6021060455029151213000045181d5411103420083e6001455004008000e00c000d00d04001d40507a004444031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 20422497 1250 20421247 20421251
    0x2040b1f02071a04060320070f0210050901021b0f03030403060c0801120305030a020d02090613080105061c02060a0908070803031609120b09190303021201080703030903080a050415050c01 82
    0x80c03c000074180110500644104160070282442e80440140c0b854040d00da034205420280071120060520007011400d100d901c500780d4895107031047c0224440405d10003070a01105021038000303070740c0102d034074030708058a4040741100c400366034000f030260100321000c1e6030913220200c0c0200410002c1da1041c4881c04590704e800315181e03a03032107125025110314140200024800d1010407003400c200d402405c5004040e0720007505024a403004a0500d4010031500f44410703940a4007040314030300c2813154075040941643c3c114003140900070144007132480c000009006900024036541000d22400815028004039002c3c0d0740c0807036480203155503d4100703032034440840d264002d1900045001e04807183c102c0710001034214550343c4648411a207800024a20b14540c0224010203000f605a100d110044611a450050b128072075015600100801600300300d44580c40b82c1410310209400a440108981c0e0140403141d48a000c80d078110342e5030117598004029082070102c0c20070b6890704070000e0b1041805007402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 20423747 1250 20422497 20422499
    0x14010914011a0102031b07090f020703080606090a03020f0411030106020706020c240d0902040c0f09150203030f090f150105090912040605090102010e060a09050d02010b0603070c02040b1f0207 84
    0xb01809140788000b0a40941d0041200c4c504a290601c40f6800c2c0340c80b40815659000d42d10350f60b52007526544840c1c010803030750000c2c9080030140c1203411103030032000503600c0070b0a000405000c100d41210901020788030342c41214859403107540310340111401c4c1000d00003d079229603680b02c000e95141c6041c0621009406010480e116030b0070154100e2141000040001006402859820f040d940c04940c0300744032952120a404003507256405240b840c80103940e5003182d0b030880c0c19401081e60760b0607040144440040c00003013241e15400002c0e82c0e08581c0d009025401c540381c0ca142d0610780b074000081c001e128024084002c4d441048841824100c1e03806680d0200d16544103240301d0380b03810324210501c42090049c4004d1112604c03c00107048444010300001485401500409280400446400ea25651034070b1001c0c040100038040a04942d6440c002489601030300c40008116000041548041008002a03003055541380d411501d20858040c01000d0b400b51500703518615285440a030070090b2044200c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 20424997 1250 20423747 20423771
    0x70204150e13031209030203070c0e0709121502030717040b06151303080309011e020306040b010c0803010b030c07081801020c0d02010c061109031b0a0e01050108040204091401091401 80
    0x822071801c0f9455a43d11040a60740b00c40d46004005541095003180b00611461000070302c95601003010742404d00c4802014540007030020100446500010380040301c800420b80002c100c10811815a43c1d07451025840340d0726120200d9080c21100c0d00211845020b10a22050100411104e80540801c0d90303a0804414400180556072146d09104400c2103500b085c10000300d84090003943c1c02c442c20100206040040c000503858a030402d8200321900359000081c80481d103010300c200102100c081c01d010102a00c10b8aa12841d4041407190071803003400000000c280807040f000b22a500f0794007000da540c59080200d00c183e0580b942848d814094410000000315514043c807884007a540c3c140d5071451b01c15030a41c0c0c3e000152056600c1e4015000042c00f4a1400303036401c0c000d65400c1c14540748211602d0075001c0412183d0740856000b40701d9800c07984c0040c015640e100c1c0103a030384a50190b8020801030801e1404500308403c41800315200d502e40f41018040056005501820740701502c001d000040c0840 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 20426247 1250 20424997 20425021
    0x60201050106080103050c040509030903030d060f0f0b040b03070905060f07020f190303030b0f0901060804120f05070201030b0d0206040603020d0b060a1b050708060106030e06070e0a051302070204150e 88
    0x170001416540c00042c05006524180e0441c81d0700110b40403ea030b05020510012a1540d0030400900807455120039040c0401000c0b41007082c0109000085010301c1e42c9400c1541084d445a40191110355800000040117140200881e0000305009003140d5500c40c242c810f060381c20381001c20200e12540309140b6009140c500201c0c1c8541b144111101000f2151031035800354010805141c206802c0f000030844010749554000d4094000c180940380c0d2031142c5010324008403450401c814507010300c0380b0143d4a1704540c0e80801500e62640d428200080c00c41d2001000502d00008108004d50050b4005000b09442d42e158014255103040310405118003003d65007002006c0c0208102000000c1c4280d007800b4001040c05050384116005006032034089403198219070800500340c02240129456070195060424104101580300c0f07080c0c80c3c940001003411707000444101a510030184209282284c250381c0078825811100c1c407a900900c00c2010403030012440d0303540e00d030714803030071441c3c3d15014001a8140421 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 20427497 1250 20426247 20426249
    0x31505060f130209010e030a03020601060807030c02060705030618011401090f0b0d02030c07060203010806240102060604050a0e06090c03010b15070b0403050706020c0a02120706020703112202040602010501060801 93
    0x40c00540b0400081c192003009420000e402810401d50032401c0071551002c4c4034648921340203901411940d814144040c01c4903401404074010075140a056200a6601003021900142d0320301e0f04655a480c3da00005040840b070035134451240d02c03050000103000024203c40d0002c0482070729080c102d20341d40c0c400441c2082461044540c1c2c43d90810100704806015401554000900300420b41890500d8481c8001c0780c000741c0010b000c0c0d901540510001606c8501d5841c0b98150104007a0760345d218a03070000f5118840600898001c9840c2c9012030604c001b04d402041c8031415250403140303d1f2421070b6040d80d44c0c018005001c0e009518003010349a41d07090a00e250409c521500070214176000003503403424000b02000700180c080150a000e80e000280d201e0000b04080c1d1030f11401486a40074600401828074015070403c0a02d40c80070318200305c1180c000ca0151b0480b50050940b252003043c210101b005c007104001000d071a491140d08842c501c0400340e01074003e45000b40e00801c550b82c1c8402d81a40c60b2482 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 20428747 1250 20427497 20427499
    0x308010b0a0915020312010303020105040606050604050d0201030b0109050d050c0405011e060c030210050403080f07082403011506020304090e0a0317060d06020f07051c090e040302030c0601031505060f 88
    0x220b040c0601c482c00c0208085420000207104407407405013150b050001c2c1c500300703800890042c3d444a05000910565020b11000780c01c048408902d418074000001d00e603c044410000c1c103040e111459081d1a80c090310f040b4006103000390100c10700503154603011351900b400c0398030b4500c514500b42c004181a940084075000b51f003480406100c81a040a03c282c40e070203803200f4210114414240d280030780b20721034050a40158800c0c4c84420090410755100c424101000b050320080140c140c08020780450040107480725011200c0c0305001c175250301c602103409080c104092560300741d244500040c1840d400001082164034114082015180c04114a42c07074003456480078002482d00c011220448800c441525000203004005400c07203900c0b66240401c1c1c2c0c03c0344000c218082000b082c50001d100c401c2c060b003010002c40d00f42c802c01d84088410041c045010b1409015687c0e0003660004040600030011124601c00303540803200c4075a500d18100ea03401c01a44c00203040d850800011402d03609040c2250304482c0c0c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 20429997 1250 20428747 20428757
    0x1030f0612032003040e01030515042d020418030f02010b030c060c011506031b080c070f050304120b01170606030d0806011202070f0b0c0f09010e210106030308010b0a 73
    0x1049880c21503800c0d400f000000da1035280c4240340401118204018001801050a90308043d859800d043d4100100c0ca50041d0042418200f0440020407401644440c1c810403c41d400f600044d105542c0c004107161603000350030500d00040c41c00e02d120024280400c0e51f10036a0340500180c4082030490a0700c60100700c0680503070221640000d0380c43e040b009054507034040400041d03120b0f01004505d0604001c0c2e406030380443e40c0d40c444086600c80e0410300082c08035132428030038902c0c2480c2403480d015224606010b0f00321011a0f501c0c1082100600880303006004104c02c4561400349410480f000c02c900388602317000302c0741c82010003401d1070b80407441d14030665004014003c803041e00442580d419000610080c1042105294040254102e01c0a025094003582400c0320308105880c0c2403820403005086040d41400c18495000c2032140135080710b030300800a01c1c2c044c40031000403001c130b400c3c000784507060500b00c01c46c00d9500e07182110551051044078001d540d24500c1e030340e0342c8450510724401c0b80c1c1c1d03080000f1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 20431247 1250 20429997 20430029
    0x303010501050702041418010c03020f0702060901020703051002030a061508070e030c03070b070b060a0302150906070605010b07020f010e0f120a020d081c1e09030c060203130201030f06 81
    0x140c002ca001d070070380500107440400e03418036081141d10b04000c00c990b1181d51041e00010b03003030000b50910881c0003002941c1030861614140d81070a44c3c4e54020700c10024403880e8006039070b96180e40300b40720300300003076038020211101d0801032010007020b504100ca60004032880c00000090102c0e411a15680c00207258031030200f652200300040b10f20074414600d86416110781c1d8800310940d14104543e800500d000300036540c441c0c5041c03500821480e030260500c0d01c148507412040c005030303071049481205000023000031903035020240c020440340d004454003d003000f481c0000018072010100001e0158901c21079840306a01000401905e11500000c412a00809401100500d50918009843c0c482e005002160304651486c0d000070b42144000800721404440403c0c0da01103244a10782600300300344c5280d004d010f002c8200c1c981c0048496034040700d100d030607110030b444410305029040751080c140e0006401e5640e450710f009140501c1290a0089000900c5c101058038448410702c82c040a42d80c0b600e120902c2c00e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 20432497 1250 20431247 20431249
    0x31b061101050c0720060f0c011802100507060e19050606030a030503010902090301060306020f0a0206130b0c0a11010606050c0c0411040303030b0612070e01300c0201060e130c05030d0203030105 85
    0x10501c03d220361228449400c4640e0005e989160147c030030040c3c0505c003207944100340c1a0302401e5804c46044039420007040381c1c3c220010780c2e98000900c40d1100030b15281c1c0d00e4850504050028042d2003405200c030340988400a05800c08108440d440903001c0c1040300e40b6130f01d5034024560754804040c0d000d0300041d000d000501c4420a6900203100480d402000807540684075107c04003242e1000500d404080c00000b800a0310640600c4020750040d001c1d60460081903017912080e452241c011f0052105001c0011100500c5000da155002c100007100001c100c027645803040030305680d01a00c101c078a1071241010ba14024541400b824040000c80c11229080c9481e580c0e0a4003e0250480745aa016000b400f4121802086401281c40f071000ca58900300c1d00460040050b0840d20342c40082c9621005c41100c174804480519669040300c4048440007507551082c420403801030509412806200c14450148000030380d0310b5006c0c0803414010059120314590b030318201a41c48204640380310140c2c000784010055 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 20433747 1250 20432497 20432513
    0x3030e06090c040b01020c0603011206060617060d1a090a030e030307030509090408090d0b0103021804050d140c01020c0f100204060c1209030b181203060a0b0309010204031b061101050c07 82
    0x181413030600446604c0e110303070400a032058109030480c91500b540d00340d501003070080c14011a00101100e06110181d46c044c1c00c1032151521004180500400c490200d81c020030800014201c00302030f049251103c10b08140f0310080c0c803121a120107600150443c00300303203903070300d0302008541d01e0325450f40f04c01c0d1400501d07005010031020010019030b140e0724280101009600d440100d03c1820348a805c80d00d940c1e40c11403040103940d1990b000c06500c0000d5400401000403400241408091000c0c2401e510b00c0310303100c0d080301441c421216240c13400d50000c40c0040c42c5800025a070100004040103944112500c1e48032007040b40124490200001c5e1a842083e01007010008900344003050761900c410960f850792220f40d061001510300d88441c00310b41d030244031250000e100000c485841882200d15504001000480014140c041c1c5406082e000010800c2e50780c09504803401142c1c8809162500c045824401100d43c013148210340201c1d0904c180b4103004d98041c03041c14400c0c0100791009040185546448032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 20434997 1250 20433747 20433761
    0x10801140a090f06090203131401091509020f1c1a0412050a0309080f03011517010b0918011e060804150504030302130806010528050103020c1c050703030e06090c04 72
    0x80f00380e98401c041000700c000d00065104192483c0481c2c5042500d141100301e0040641003c0c6099160141c44800aa0b5010b45691f0100340d5000104880425000184001644082196022040014490245103d08102d887c4640519000340322030710b03218152800001c0440e4010100141e180030540d40c180504007401e048000752a00140a0b009591a02600e80c44021503071104000400104100e1880100a10211000740f13031011641a000e070000d80010018010075420100200343c041c4c0649402010f40801d6175070343c40c00c64140d651100ca000c1c0032402c102d540150b40c01d200d172000c12654018945140510f910100100c16a110410a50000c15028100b142016000c01c958480ba40141201e50040c203c071001420007545400200100e14501c48542e01038081d0301c044114810007c0c0e1041011580700b82030240e51405115000f0381040b400043c0400d034442c814240118103079001c0702030f0461a00c06d0b10100000652500001d6a50000710384060b15684029194005800c0a801c404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 20436247 1250 20434997 20435021
    0xe0c07020d030c0c0b03010e090a0201020705040b01030b0d08040503060112030804060c0c020d140c0a05060d0b0f0a03050c0102010f0501150c0503040810051b0f03070e060d0501030b06010801140a09 87
    0x311841c40c81d1303141e2248041a501c02c40024030044014000c1101d40c00001d42c0096480000b410f4015069001175160199071017085c0c0720b20790301d1139a03008690081c2c000c0249040c0061004011029a26100069800c1801201e0003442000d001089041100540782840c40c1c05481c0d0341e04694891385c4050213401c0c1d1074044410482d07550030140040e240c290040f040984100103015858000c8038005180c1007040007020b21405928000b00200d48400007120804001010301250741080707000850450841240d01603000401000c001060260116411081c500d0990007804020007030040e20342545c03030030700030700b03071041c07054000c80308103902800038890071900c0f890642e8145652008420704203400d0544241d4640d0701c402c108602c080c903807040c10005090b035104203403c2c860030348001d0b0780600009224030148003241001100c0c658a00301520a400c1e4111018001d03903840c0d107045941d00c0b00c15180135010440c168004200410401640d811140c0e02070070744480b50789400300b401c001d08601e540b12 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 20437497 1250 20436247 20436257
    0x70501061203231902241b0c010608121c1e0209010215010807140306040305041a07150c031409060714040e0103050a1401020a0203030c07060e0a0605060301060e0c07020d03 76
    0x8141512004104d8800e2401c503000742c610b50040c900030480d16510300e03c0044081c035480042100340040b01d10311090416109424a88a004082125004018039003084001d80700c0e0480201084803010010b0030381c1074090b103102101480140e25502680e9882260003804a1f10780b140302c545e0b0f0035544c0034002e540303030510407680003003d4404c80c0c02e041903080c1c01a418a402401043c00343c01c002c81c096440c5200154000c140d9441d007038034024040e0080740108444892859401089120043d06441c030907038101800c0c0410101001a2000803d40c0350000300100c1d0034800c41c011b03a1009580c160b4403450b188400740447c0da031103110885228441d0108603c2e0f1b22018080415070a2000d6009030207107102d90b000381141b2949007440e480b00034082201e003080740e00400000d081954040142d980140d4104040b589400c1e0502c0c00d040079064480d4030b050144140c1c0040b40c1444030781d80000e800341c00f040e0020040ca64880101d0600b10100319051021100e04011030f01c0142088105078500e1030107482c03c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 20438747 1250 20437497 20437507
    0x90402040213090f06050d08030f07170c19030b030c01081e0a140f010807030209070c080a0e040c09050a0509090c0a08060603060105010306080a060504080409020d0207050106120323 80
    0x49190078030840c0c3c2140c0c403000d0b542d68403240000494801d0070301900342203038100f40781191580c90080074070004040e508481c3c000c502080050b0b0107980064005130b0b110100c41014030b0702030148881034000504a102d0b01d0441320b07085440314000e05c0b40411900014000c2e00d0364058480c0155051040a81711036550591740741e1904412490314604d601800034050085400024409030000c03540002d00f060b899501410010440fc81000501b40e003200e41c1512504000c0da80d101081c0c44610200c0800313440e04000081300e510595205444001c564003c880800c0303020320f082e40031a01e00c0c0f404d01a064100180500500c034610b0402010f80e88002c03400103d8600200e64001300c0d00e060442d6001c400d141d4060002d0042d01d2030306014150141000307103020010203240000242d641d0380c2280018080582c2d81b4003190910641c50f08a5000d080758042c155a82d90040303040c40d00941c880c540540303855103009030200d034080140c800c00c0a402d400da500e00b980c00000045000040780300d003820102c41c2301c003045 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 20439997 1250 20438747 20438767
    0x30c070501140123280e0105010314070813120e01080108010516030b0307080703030818030310051e1009060908030a210603020a030b090d020d020d05091c05071707140904020402 78
    0x44010f0b50210002c17080000c0c0d49050301504011034107800160505060491900a1600311015641c1c4440c4034605010300781c071038580c0140c81000085028100d1014440d14000c00764101e80f000c40750040030398454105a81e03a41515080b12015102c800a8003004056661441e00c41d07008440090710050680720f03079076034850740303103240081580c02200031818810070041c00703c4070504504007042000000d14510316040c51580c1d0203800038010144a102d80060141100c1008030b03002d0845840508a11820600341d1000742c015051841050300207001c1440200d100c030030120a0b038481040303640b1040000c02908240c02e008101418883c8000d6958442c000003580d0348407040e8000314080c1c1140e44031400e1032850141070200040b01c0c481551b001107940e9402c2ca40c0003581011075440c83c5041e94458040c0400140301440d41c0301e00310300e9600078940d25000c0c4000401c280302100c800c0e101050200c1000c5c119180c0302e1425100d84261016840e003104002c0c18003540d015445440180300610780050301c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 20441247 1250 20439997 20440039
    0x82704020301080f0d05040605040501050f07050109050c031002070506040b0403260411030303040b0103020415030213020c010b10020304050120010c0905040c09030206030103060b1203030c070501140123 89
    0x6406120f072640908045403075a401030042000d40d491920b0280e14050800b000585a88141e01c585410040001000036001d1040c9081d0781c84568018001e0150300581c1c248241d4551443c4421803003805081102402412907108451601d0b50003c041c045942d200c0c0c41d014114400144283d05110200341c9044165109080310308240404124100d200e0506081c41c1902050052005000c3c0d4020414840803a21514109044a9048030b010800345840340308041012a01e07400203411001100510398180b141e078000c3c0c12640c2e141030003000218403101c01c00c0035014501000c400036800400c4280003d511540c5200c44510080502c4503e240c20b00b2800c46c00c4074a40c007910400500031b5002844240344ca030003144045c544502d005a0302908580001e0308505c01032000403c8155a000d190119841d0b030000c00c1d0981d0b55030400c0e2502c911b003241120010b40d100e0042210070354a40003520720400024030b081e6059945410455040392095064031500203960410903510400c0d0602600c070021140b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 20442497 1250 20441247 20441249
    0x40c1106100303080606070503181c0606210c030b0c120f04150608120706110703050408010b01080f0601180b0409060608090109052e02030c090913082704020301 71
    0x14080401d01d003891418001d0074140302414945c4075032410040d040110f0300c00415075910311450a008044c514000e00010340c1864581043d640c00101c2d00401c6051296540c86207044404601504103224a40f2a959084110b000001003d8040002013400490741d62a0442d51200070068002c0c0b030060107890900801408942d203209041c9003030100402c100d010f0300344071000040d94005000d90360a00124548030400070040068283e004038081c410300c542604000c9000307012000d56641c6a0081c140180103501c41d00a8441c190b00317242c01d114581d44074208d2180314070310281401d0241e4440c0801186d132804c85903070a1854004904004c20310f030000c98000c0005080844d4001049494002c0150081000400940103649030000329130200742c0106030049102c240c40d8030701100e5240010f80c80c4401c680c507102c0c0005c59202000f0050a01070b890014044404111181101c80d42ca2049500540182c0c1200824440c1e0502c811007401008000c0c0c01c508005c4038030440c240d86601b1020901706c0c1c0013 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 20443747 1250 20442497 20442511
    0x5010504120f02010501061407020303040e100320010207030807080c100f0b0f181e090706030515010905060a0c0f0b040b090d1d0a05040903080f01050a0f05040c1106 73
    0x1458000e049550381082e0158400e03000e90000f408039601d421006041080c3d0038444028106002130740108641d018002c0314080c10402c0091040350074540c020381107201d4070380000c9594400c802041d062550310b101e4030f447c51000580c0100300550442d5900c04203030300080c60803210758030107201d2600041c401f4071072500c0140b40d170300000420325160a082029222000d0f0868081c18482c030109805032180c182900030b079000100d001125485403100324040102020184a000362504140081c0c00e86c045118812034030039503010310150300d9240c0c0184109601d01c0e00c02d800b01c1d0116504000c01e0510f44080c10303500d8007074246980d2280c1291620b26064003001411600c103600b100070481045900c1e580c40d03801040c1c1000401d0508071600010709681203649520400c2800e50703041c208a9515120300d0806018054414800c2c03500c180b80203008407c1c01d80303446904a40c124004642403c006aa6600f2910518200c42c0c450307292500b840001c0204e00c2c54402000041006182c516808200f05801046 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 20444997 1250 20443747 20443763
    0xf0c0206060118030206030c0702010e03070e0a060e0105030309191e05190506030a15180507030506011110020c03070b130311010c0507021002070515090102060604020403020904080304080705010504 87
    0x70384000014040401002084281d4601c3e031001e0015884850650b9403183e010304845076501d20034001030700c42c80810910164103101d2424082a02e600c07125046004000c003400a01a0f140c0b668001c2d40d04000074010250150b1040c0001e80039450f00700f4079000c05600c010702c003000c919203810880b2050340a004076081291702c1c0500420460030030400e02c0030110012603070081c0711802c00000980707034800648401c0c0c8854a4407100132011940e85030000041000c41a0503085010949490018000c1115040042441c180000e6495405101d02003843c0352107502916004c1c0c04c10030504001d4010418907041840144000b5000075030a9107040c1c011090f280d107682c2603110520300200720014081c070740356050b4100717442070251a8015041c3c8244c40e0341103d40880c52100e10204a1500d00594001e503808040784a007401084407400c000c000d0806c007030b030035035402d0742e2080140001e0340300d41d03c4025044100040028041450a030203590002c1c031812540c0d00e40300e03080c3c54640c00d40d003090308e05403a0300d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 20446247 1250 20444997 20445001
    0x40909050f0a080a0804050f0709050a0b0103050105030606010c110901090e10090b010513021e0405030705031504060b06160821040f030e01020a020904050f06010f0311060d0f0c0206 80
    0x981088548056818903004200382d000b665614207441c00340090f0541030100d03c1c00418100b010a004090814011000b100d05d03142c1d5580344000a40300607190303036129514000c0390002c00d52080c05154162413000e030080000751111801103e1255000740107403400c107540600c070031096940060b0345000f00044507020131740150108020342800038007211250384c5407074a100b41000031801385646044801c21074102075066400c403450400f038450000d00c95984240d40c09140000e14200001d402541c0043e000c81c0c0200e602e500516585401082c1c1403086040da0500060005645170405142000f01030419400e118001012120380340c600041207483c0c140200d00740b003e9503e0003548069600031000107041750305240d200e91007940c064500190411211191504469000b04207843c16194041d00790010b0746001e0070141d4850313600d071090308a240250f5000250544440e619042540e42103480a182415164100441030307004101c003515198907440800e003002034030320810100b042d281d005040da078 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 20447497 1250 20446247 20446253
    0x4030f05060402150c0a0303090c08061806010605091804020a0e0a05090d1b1104021e0301050405060102030c072304060b09010921020904020f0301090305070b060303030601080606071502040909 85
    0x2000401c3c002100340d0010f01117042e00f81d40000e42c1034080c0307426040c00180405030741803e008452060308500314902c6807800340540500f19031b40c1142c10541030400d9034a640d80b40e9608403010b100c0c84600c6540080c0156902007003581c644c80b1590401c1c4000c0000c0020780d5a10341d000c2400c0c2c000c4450000b41c80e85c403401c0140014040c00700030041c0d1050b00d00700c4c4030101c909206e5841240102ea029000c0f100481042c00d131511a5411101c40c454140050b11101c200744418085951003400740e14011401c140200300300f5400081514031959002020f0040c4500300b40300c50300da840f92050010016610714441508940f81c0d845581d0150100c001da861b50303502c0307680c005481c0103940e500000544090500298000c8410f00d5120010341e411a42c001940d111400020802001c2c0000c050b807551030301100d00c0405030000000c016061258102e40040d64594082684900080b2003181c0481c5610300020301a01d4148028271102c1d01c0b8100c0d50403815080c038500c9080313130031a4000d031039080d95450341c00c818 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 20448747 1250 20447497 20447509
    0xc040912090602060c040e1f08010e15150d0f02040c08040302010b010c03080c0a020a0606080f07090b090604020702061308011a190b0903070e0a060306060801020307022104030f05060402 82
    0x29150b40d000400c0300b414540721100c03080c171541c401d900340d8000800204051514460703803c0882e4145408541020341c42d1840c0b81d008011200c40d140705071194030043d542801d4124044c41c03040d030900003210342c0d80781d44101380418108880c00490b800800c0d80150801aa2340344144d030004051035640c030410381350031701d406402c550118403698140400060120002684800095030000711828003a849503604401030389040180c0000504103802d141002c40c80070341c0040c40c10303082c1a20341d04a4a4159580031a40221481a2249a046091040052400e081036001802210b1001d041549440603180c10742211a8041c0c01241c59651298120080140703c018050340341682184da03410300710301c00000d00d44410820700c50365405070004030b01d50140b5923051014800502030f40300801c01d14075040120a009141c1d900040724510318040d000b003200c10052003038900c114095001080070f03031681c6011400e00480401e8504442c0c00400005c40010210000c1c405620710a0000b848582054810454 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 20449997 1250 20448747 20448749
    0x40c0503010504020904080a090302032b050c1c120f09061a0108040b06030712060605041803020307020f060d0f0b0909010902010903030e03011103010e15040c0c02040b030c04091209 80
    0x8840d030b0610040c0b0025a07103610051340c1140d440143c1c1a505d010003103060300c4034105684007035814010100d91180649c030074030120300c050300003544020240781e50030021342d01805408008280c6a1100c84200b1500f5503a0500107a00d000324100341a00840c0a008a020340750001d001140c03868035110310808101717141c064407c0080c0c129404101009100d00001d20505000304040d108814400211718a0788007030211034040c0c1217111141d02040d030036042000c0600303268811940103a180082524141040d14a940d548a41c1607026501e8020207408000c688041140380c1540110b040009041e8074002e4465409988a100d5012401900110400071510710050008000381d040042940050380e204441c503003030303942c541001a10b1070500d5020a00401d02c80c0001d503031005000001258000090035091f10072408001096030300e40c1074405000039500021071880115440d4407820300103140c103420481900b50040c0490320b40c0c1190340d00081c00d944042d10103607540c1d8a200c58180c866540120480 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 20451247 1250 20449997 20449999
    0x314060102030313020919020708040602070b040b0301091517010903030b0402040b0417010209090103060b12120405010c0614010b1c020702060a030b04020909090c101d040c02030c0604030305040c05 87
    0x9401c62500e051144c00451000200078450788400001a11081c00c004444001740125902103480e0180b81c50002c2451f0b006004480c0544900c0324000b4a074851042100c00b6543c000c1a05810360340b8186a01000c0d00d55000d031200c980c020301d00082034206076802403584514040c00081041c00590a0150485140321b405501460041109001030710728441110112080100e44c0100e100211002c1c50080c0528013445610204e090000000c1c403960381c00074103410740e08035446c0318501400721030141e0316502103074a40c02903201807000700510341c040d04020300524081d440100f80e0f0048d8200c000c420801c2600088503512000c180e41c00c0a640c0c0da03105584548804c0021480d103c620380000310140034410480f01055103444c100c00c45508d854040d510b1420000d0640c0c0c03464206485a251034256269003180141c1801507401c00e11740c41000c21100d0320030020110100020500140b00c0a8251502030100790710081200c101c0031402000f82d2807003a802a80c0000302e6041c680351039600154285d01c06 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 20452497 1250 20451247 20451253
    0x7140a0f031101200319050703020604030f020708010203010b0c070807060203030105040203070e03030d060603110909010e0a1410050f010e01020312040c09020408010203180604030f050c16060314060102 89
    0x611484412611800c181e0740c0240381d03400039503100c9004031340010107809010013410082000d00d6180b407000000e424001c5080b0031107403255403070400403203080c007581c6005001030348040c1c0401c020900031109078a80040d24419545425110f0f1495826030340203034844099143e0014100c2e14036001848448007030411a4094583d191030030a0013950b901041c000c1c1841180d002000c25070040c060450504560f501400792501e5008074002c40700101601e2080001081c00c050708441085500d10850301e11400090016101d6403c0c0700d4100e59211000f40380300000707a034651400c100701d00c400007030b54030915091814241c210f0504081c071440700031100b0310350b05004404491b64800d1380c010041d2141103580301d284070b445903103d041c954420720a581c80103c06600c0050f01107080b200640003140714801c00308003240600704540326546d55020840c1c0c05000500503c04400d0502c1c81400280401c2880ca4121141d41064072414203504c440c2c1d0384442c020075500c869141180e22091040c6034001804d0000d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 20453747 1250 20452497 20452499
    0x150610080105030d0807020a0c06020a0204060e0105060d0e0a08122508060f21010f180c05120304050a060801060f031a040e0304090f05010f0806040201050702010c021f0207140a 78
    0x825a40c04240903007000307005031701000400c41072082021200320b03a0130140c104400d50b81c2d2840603444061044041c0c2c0201d00744100400c1c659040d1280034100d810107440549003110328840d00c4020704070b00210074810b0082c0c0d104000800c4144010348000d10700321000d01411309099030801e0b550100490304140c110202007844640e2908144025401001510301c04100e640c030400082c0d8140001098030840c09051401e2440c0000c158040114a4441c1000f089000081e1a11110015448000804c0c2e041c06600500c194240040601000c81d4150201c90030300741c0758400150700c0d08040d00504001510403004000c8507501c106401840f0001e0308080081d10f07000403524a0b24049103030b659002d03d0b151003101c2c02c40c55042040301d0090442c49010003201441440e404040e0100703200311000d00b402a01c002c280100c0c08a5024010b80d416181c40349844025401500c94543c84281a40c0c030120011765118255110f4440820115a55005d00440c5040001c1ea41146141001890141200502c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 20454997 1250 20453747 20453749
    0x1303020703030c050a060509060702070b0720180703090201030b0607020f0105090315091b0315010603050a020f07030c0501051302030307020d05030f040906030b0721110903150610080105 82
    0x10300c04181c940515160325002c80c0c50821070300e420485440100002c2c50082003110148001c55180c1c0148015426a05641c1d614900c00545002d0344101804040b0741c08443d031001017030841c100b80d07801d102400070344030229241241d0310a00000c644140100703417558032902c215030f4540320f82c09114004446403410034049401013a07040b88007140241c1403100002e103048142d5020812030324031648103042000c07613180003508161030750134141d4000320081145400b108140b4000c00d8515003c0c001981c0c2c2d05c0740c1c1c0e00e4500100c010b0000a440d403030350164204101221030301500000e289080c0070351200341e441d40f45880c046084a0006150703003170b40c610a41d4500300582d004001c80311920b8044032024040311040c100182140724900d0783c2002010001000144140c0e03e130498002c1700c0c09100500a160785042c2c0c1618800012802e20742c2502034640e0010000780c5650180c01905012004241007800013008249003135103088040310322440103401c04c6198980000d02d801c2c0307101980340400c002d51400c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 20456247 1250 20454997 20455003
    0x203071a0d050601051b0703050d030e03031f0909080a080901020301060903380f07030c050d150305010203010f080c0301020408030a1101110307090303020606030c03030d02070309050a0902030f130302 88
    0x41e094000680c494020601c41e030b100350150748408400100c1c6141c0b05860750300386651011035100464460241c1c08005071418021303c80c4031708102c0900d02541c515075502c2603000482e070390a4800d010a00e00e0600210300740d40d0921803c11002d10807900155a44282100030f0080c150052904011341e00410045c00981d0f0302840f400d003203aa1045d036640b04200d1a40504003503031203025100c00381090070101040e030180e214907040e0140700700503078020607030b11096001c500795010144200701061080003219401403080d400200b240303c036000b802040e1603c9030b40300c3e402d99100b030340136410f840880c15080c080c074001844003e5008208034021490603140c0144907480c0d009120380c2d141800010a480c20080c8000e400108000201403c2555030340f6020700080c0888105000950040c498440016003a080c0007580e015114001401181000c07020b406040c040c2d03102c56400c03403c0008400780050551940402003000d048100f00c0540c5038a030444401e60300c00d800500c1028202e50700140e03540030039004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 20457497 1250 20456247 20456257
    0x19080a0507060f090b070f020a0302070b2109030d06080102041a09060403120201090303051f0e1509010305010204061103040f09110f070b04030e0f0102030f090d140a0203071a 77
    0x80d09200d07071902003a0a1030360081c180c1c071540101450402401e80708219103031224500c1680d8544844c0440d140d0000104d81e191282480100981d0100c04140100110303840a081c4030b11031a1407422103000c80c0304894127022010b0b0b4510429610104a000800d2860f000304000b0300b0b0618000c6081038a881d59004200c0040e0b100c0c02d8800b103000508582a8607100100c0703000e10f400c8401110900e09210009001301240b50064001a01c1d01000c601c81454041c0b100c100c140380160052505410603200c201c4145019000801e4490b803000340645a45030300c1d00c828001d43c0a01d00040e151481c14901030694101d10043c00d125030010002846241d40c0702c0d014406903100c0030b8000488441c01c428002c6544241e442c08200e091000c10f5040410488203100391140d8440d076031311810740c40c0079028802510310f002e01032030150f041400542040c12031034001e0582550700800d04e000c206503980f1408400d0591512000c81500030614100c29401c0c01c12842e0010302e10401d4000504500070100341580c080c0d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 20458747 1250 20457497 20457517
    0x30d020307020a0203060408071a0c07032d020a0507060302030f04030c0807020402031305010b041a01080405010b0d050307030f080105060a030513140109050114090c101e0906021908 80
    0x1021001c40d0955200b0049501d880b43e010b012039889040a0a01607040e400c4400701301d0b1104641c80b0301074040281117002d140074100000d026410083c02c0c2d6420b5920014400329849440100603442045c04e00944240042003140d4000d048400c2440c20424201803041d003100d401e1500400a000042c6011212140d1154042c50510403071400ca15202040e8402c0c141c0283d07100e03001100f4462080403000904003210701c02e100800034101620b0034401510a0b0181c0504036680c00340d09414294040c8860030f501c94801c00000640c00100030003c1c00107010b08006944950011882c00b0400d504000003e070038100a08043c9000e61421001130903900c03840d21250708064941020032802000f1171f5619104030391100004003900f0f41060024020401d01c1e000742d80640c2000c00d010104c00d40300b00e80d180a104550082c2040403010814806514a03444c051010481d507210204080388244a00e0301c150401584d4488030b00c0c0c0f500c01c000b440c190360003007400180041780180c0c0d000611310342c00321641c1c070309 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 20459997 1250 20458747 20458751
    0x31e1311060a03020c0102040905011707050102060604020c01020705011109130b0307170c0a0816140a0b0c0f030c0105060a0b09030709110904020c060402010f17060103050a0b03030705070501020f0a05030d 90
    0x4542c00c4020b070043c0b01001a80350f00124001c14851916000315040c0d86626a00380301803240f1541603a510100d61046c1800360300b044000c91800c0c10f207078008000301140341d8000740c40d0140c5d6a81d0305e03003158034060700c1c062441e00110341314040d0b1800b020620000360039028140036103810940041d4485200f445108102c4006400340c0007805030070b00c40724241d0b20f4000d20420492717507207190301611010a42118100c0d88002440890710b0b000b000900b11000601402032030402d420b20f81c1100c001c3d802005920301c24402c0b1031042d031070660100028035401403078400106d01340c00c160303003403080764000c5c3c0d08030b200341c000706001e0844140c03400921001201c00402010441c00d10806038040a4491804042e0b0428000900700311008800100140680c3c0b0030790b118440c55241540840303030120030090304112004c243c40403600c07a41c8643c21940c1c000c080d07508005112403184000a28584c8010b0046a5540107481c007004a5a014041c44400702c0a400c05404403070042d64170300d07407241300f442c40c004c004503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 20461247 1250 20459997 20460007
    0x705090d0f0f0b0a0617100b03070807060e030105070c030806011d0a03060204030b0c0702010c08070203030d0204080a02031c0c2306090f06070c0308011415031e131106 74
    0x10000e01c450029032504062448850b45843c200b01844843c21140c0002c41801d0510001c1c81081008858030401c20304809407070184079010250014015540c00706503d4414103201107a11813083c0f00310780c0180031035180c400400840c50103160a440700201301d1070602101f40e04c600c02017500000a290700080c00d2030900600406030604031880c40c409200e207900240084008000c109480d8020800e9a014207020741242d900d81c032841201d4450b01c6802800030704104041c1000901100182079901d01c0101500e0030320300088110802c0341c110394090480c540c0f0001c030350001d600701805100ca505d8001548600740ba10141405026662819001040103078500d02094646489042401c4c41d820074902795a12030401d1034810755286842c1510b104d13113000e40d03c045441c85004102640d52a581070b107401080d6880c05185d443d448003056071280e013140700300c200f20b400c8440b0007004611584200c1401405103180000e03100c1c1c0005c00070440c40010032610300400104040d208501c1d580c0c0341c112241c41d0b0315 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 20462497 1250 20461247 20461253
    0xa17010f0e1f1202011b0302030a052d0909060f06160f0206030c03040b01080303010302030a1e050a03020d03060603060f050d14010606020c1002010c0f0e030106030206030901090c0e0705090d 84
    0x41041c100c0e41642c64041d0741c0c00441c0da01d41142052440034001d85c1d0710b00f108601000808910454840001c01590041001d04906401940508403d101d120300120b000c00c021011008074034154100b43c1e8400c1000a00f281d4585020078110750403c0c2c0076600820201070302d01c0868030070b00c2003010b500480d10803400c0340310800200b11041c070901e59000d800c0e5516030900c140740055603041668122074180741180040b5415a0000030780c3d0407260010008c180e203550135164400c081040e01045155407680050f5040859020401d0900285c440d500a20000a840000070102c810315008841010305041c020016001c1d004c0ca06020b03240211080c090500c1c080c90310000c90284c090319641103500342400000d602d900400c500c4440241502c55800d03120f6105403c03070032110149400000b03c3c0c034151482590500c40c680e080d030820400703400014899101d40008000f0b41089608040681d103905040741081318074808840100f1010240203824100400041c2c03050182e04809401114188114024 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 20463747 1250 20462497 20462521
    0x2704080d02091c0506160f030209010903050319020615030709020903190b01090605040902010815010908031b0d0c051906150305010c020c0307080c150c0f030a17010f0e 74
    0x41a0700003004442402032031400714860443c62401681d036401a40f0005001000380c803152080310240e50750b00f180400e84103000b94029004481e100d030401400700030200009204200411151840c9441070030b525007140c1d030081c6030060082c4042c03001090154281220b8800092174000d4851020b005600e600c65800480d1406035080d21042074008004900c2c001d01c0003032007282c0c1c140d950140c000c0c49000d44503c02e2000f40d0744400b100900055003000050038a21482841c983c00f010b05240a504c1c0942d2000c6040c0382d50407000318130fa019400c441000080100400000314660b0b91070410380e00c0d0305c115484070b5865a50703500010119081d9a014401040800c0d840720f00c19002241000b02201d40340c2c249036009116203020040503109a000005e0703d13140000d0f40101b25211000140b81c11445c0230103100c0c03510803401c60480d4015080c4003d03007c80c00305102034171a0109a40c002d41d00c43c00c4542000f080c0f049130541e45145800c03048010301108002040c0d07401502d2541001001c00e4075501082d8203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 20464997 1250 20463747 20463757
    0x2031b0403120e030a110409030e060a030e06150607032003040902030109141009020d09050303070201050f0a020f0406030905030c01090c0512030f090f0d1703062704080d02 76
    0x8404040058044104107200b0340c2809011190f540790444544100d05145d40c1d48180d070381c00340900c800f14418040da0300c0c007900064021442894520120002103010440039080215a0030200e91141c0340c1d01c0602004000c1d0310351000f01c4840d00c4a03c41c4004003c99640c0c03140340e8003d400c1000740b007480e03603512a100145d0301020f910441140d5a550380d031a0710728002e4100303018121003d0b082141144448400702c030000d00500c0c2526030600304904e01081f020003944100e0040c120141c50b42203080c0402c9081c40a0341c852542a00040303070f18a043c100d4410003d00003055007507490701c10300050390b84004440a0b101500d04504002500e111b1504105155001d29100c01500350f080c02c4240041182121901080b5035003038404920074051800d60303075142e01461005803003810090000190518007c3c000e6181e551000e00400c5c0300c0c50a0744c64005910725559148150b10340008240511340c10070340c0c0c01c00a20170f0484810620040740409a0a107010040d00103001010302041d12807a801d1164111a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 20466247 1250 20464997 20465041
    0x405100f0618140a090f09060e0303040303060602060c0304020d03050702030307051005060a03020607020d02061308030c10050609150109090213080f010603050303070c050c0a14030607020715030203 87
    0x31085603a07034900070403414500314a48100529460005000364003100200c2d00c501000380420780150500180b10000c01038040ca0140c060784810044000c1a038500c00d405543d420007000d180e0760320b001e04010301a110a83d002c1000c40d407002082004804203202075a4000358100c0f452810a021400c08407224010220042c0d4503000020306c80301044000500305004c45080c103414040c40d0340d500200014400c052201a4024208106900041c5007607402503000c1ea100900c8182407510810380020003806075000318216600000315001c22001c104810306041802c2030741800305180c4080030403c01040507141600c510030150b1044040d0b8016640300e4060a40003200315101c1c1e0021450f100e1050182c481c0c082103020301103000001f1081030050300c00703036508400150701d962640f000c2203030340c2605010161018024034940c608155500350310980108100e040480d4007070450005c160800c50040c01440c107640c0403400821100c8403814480140c08282e040040c2c0307076595070b0748c1800c0d00c200d851070072 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 20467497 1250 20466247 20466269
    0x2070302090a09020f1504030312060b04030804061d060a0305060409060f2403030203030f07030b04020708250506070309060204050409050303070206090328020a0203010c1e09050906040510 83
    0x108a1503025880401694021205c0309450301414040c804084192464400e603040c0400c400c1c000f01e40201000d0121101a8000040459542c041c800d043e800a40044500c0100000c04111081e400a4807240c080b1303803030342513440511404001030001c0c13103400a11400d064640700003070340310340d40c960141401c0c0c4d03040441400141700c0340c0d908a00515011556000b00c4001c0108252405900d600110a8a5141d0015403464480c0e6103122076a5400405400800d6102c044542c059243e50000d4121a44141001d07078a802c0d0381c881407103020b030450240c003803000c0c210f032030b2440490400958160040c03d01e007800030722141542000c8003e0302c1950803440d04181007103a103008200c4000000c51058459030300340e5400c4c0c1c0315a81099140d1048902400a1040180c91282507409449400d070151400740110b80700800e01d07074042402e542c0080c6c4c481d000f18032285584150160b0009900450030075500c5c1501c1c8260800307002609110b070160010380540e42d40c1e0700160800d80c4001000780548038103011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 20468747 1250 20467497 20467501
    0x6030f0f090602041d1611120408010507140901080402061b060414010516090303080601091509090605030a030804060902030109080706050709050a050f01110c0d0f020f0910030b04030207030209 85
    0x74040e600900c03d08017031500e100b20558102c60500026400360813801503810035400044401c548003000f2075252440b50203002410001c800031917004100814909002040e140b606000c003a00c1c00358070080103d0120000c0080005680c1c1c0903400320352195044800d00d07103410240390400070000110080c54280d1040344280418002c0c0000703a484407411318002408190740304401c0025051484c89260b0108014000601c0081c0c09040b001f603004406152100855039234034600b00a1403000b10444012500d692004c7c0005403250041c400580f00503801007040c01c2c40c41d50010402c0c80d0050018020307607070b900e02d0503045641c01c5d006514030070b4005900644034545820010020322041c1c032148003003400010009068200329201c0b800310b40c402820380c08a041c203a40195200740c000310714580c05014040c0c0301e915a0796840703460070ba0980140c0305201c0c0490103205008007821002c1760b1602c141e550004205001c00705807400400e076544010141410307251850182d02e88480b94000035400021803003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 20469997 1250 20468747 20468753
    0xb0a09090209010504020702030a06050a0b0901091a04020421050f060c030a0b09010e07080901090b100302010306080127030507060501060809010f0501050303090f0307150201060e090c03030406030f0f09 89
    0xc0e0161074001c49400c03541d82da80700100001c0344104000250180c01205902000c544290b000c40e03071040442e036020507115884070010b18180c40980140c2e80450380c800b5442c075540752500164400b0542560304520309824244081c400c40071240100710310035601c1003202c00b0030000b44041c10480c00d814040340c0c9241070407400c1802c150012280301d0200307480d0a0f000c0c00d2a241004846040340c0c4500341c92a01d5894040c0129900000200307000415034030f07440300701c0001e09410503841c8110441408040341d10700710b10004042d60b0131a441030550740c1c100450200701610420544c0c869400242c50381e0414002031506941d14000c4002c05000340f1b250200000d00300b900b00807a284515110002003015030001241802140c20a009060b0103500038001c402050422040121a41d9002822210744e07981e1203000f02c410b91802205003005075150740c001c00280e9a035000203508801e050000e041d0319004000480c2c0d0701d0240d40f098100309902c0310440080261554816621000417502c24060721103281 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 20471247 1250 20469997 20470001
    0x20406030c0210090b0a020906090d03050306040e0a020f1903080d02030a060506070507050103150e0c1b0a030e09040309051306050a050d0201080c0315060a0e010201050c0304050d120b0a09 83
    0x161405400f0320f003200415110709109000c0010f6010301d81040741e0b00d8070160403000750006554160846820023140c4941c0e1f842e4000c0884c035500c245d90320b950300d15042c414007059800304230200007154416240c0c440141c0e40e480d9402484582601c9481a00d04d0b107a000244000c12988040e003071141c001164089181c803a00191301c1601c5d10441804413568410900c4201d1050046c0900241c0215034140810762298110f00300e12003e10000d035145a4890301041305030b900640b58110803040016614800c00380c800080c4001040c0000600820388054901510711180f903840c00348500ca03c0b400050816006200f40009008040c0125000001d0000c03a18014500c0e070044611403684460005058030301040c800000540c10307035a029964681e121400390039000900180c01c1003200d44212180c0d521444c000c0c0c003032100d40d941e132000741c94540c0c1c0004e800c4500241001d45010010402c1001017100000d5072120044545018015502d1190082d07008000300701d056130788001080300000c4c0c054615 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 20472497 1250 20471247 20471261
    0xc0d0b070f1715010e04150306060504020309030409050601020a0f0302060712050702030f07060905151e0103020f010f0e0307120c12020a29040f06030e010b1f1202040603 75
    0x40e4540c01c15041584600351004a0701c1d44019040b10074940000d42c0c200b01064481040c014181003110703000c00000c000070143c50080460101c070b4140300d2820402c1c00044c0c000d05000307160503030b0218070f9802c008600b81e4803442203001e070340c402648480200f40e007030b44200542d400164105075100f460050501d0000e4907187c0a0321042c00103040042415440d00701382c45100e0241038160000c2d440c00701c0b451683e06242d0080304094851030784e1000704801040d402d10540c82c03000000004e018280c83c126110711000231426100401e40c0d59480010f00040c1c64038114940c3c040024240681208040a01260000d0100c5030060701406003000000b808003903030244d151180c0c0308d001e010b18415150000200c03c03034023401c0080d41c0700e00350100030002081501c9500c8022144510313210200c1c01d60701010710040e80325502c0483c1300d008c1f9403800c01441da41441a02c02e1141d140c0002d10112800200154202c5552201a040101103c03207400f10076002e40c2c111703602c00c6801d11095448982d200720280c0201030b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 20473747 1250 20472497 20472511
    0x50102010e01061401210606030207021002010513060902040b0d03080a0c0201050f0f0405100908040504060608070e0f01050c010e0c0906010215010303030c0e03030c070305160f0302040e0c0d0b 85
    0x820784554110030041c06600c06803014900e02071070481c060001114103584450b43c05a00001180c0003034042c0125008074005400c072030700c0143c1c0d5103401c6c1c03051141c01901c2c190401c0440e49407905002912000d00b41500b48183c026070f022500400c58000100105000d1175056842000c0e52404802c040c0c100450702d1140440110070040010040d8085c0c2c03d86804a90345000d0708000e00000c2d1001c101303039040d141c00c58010011540406100c01e4031104560106c14251210307180820100014030380307400b680024001d1762501004508180d4805031000c415030000b14807134101604000001d900c00e105031200907503a500248490849491703259142c03091a0b03440d60040280d0000100b0a50000502000070070000d01c024070540e207591002c9000f8030640078100c0811003c28002c04290b502007000c0e2800b4100180034000d12403951074003624112050340720700b44090340100c08208000340c03e4030650480b501a9400700e1706043e0781c5807050134041001ca49a50245c2035138041814170403c840308511a100c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 20474997 1250 20473747 20473751
    0x30b040c02010b091014040207030c021504080706090602190302030d090803040204051015050306030703020a09140105150403031103040e1e090a02210f01020301060216090b01090506161203020405010201 89
    0xc85e4040c1d081d5402c61030150101c2c803a801c013081c41e900e05056000b00f01450003441c0001c502d00c0140d001401d0000c00080c00181140007103000d21552900f030001c1c0000300307000d0a1842401d450504041d459400003126840d0108800440d40305150013801200c40c031404000f0208210030306480c0030303a1642c006841c1030740035a2514000801510018110302c2c2582c601004003000c2d40c005100444d4551700003410365415015906002005842360b01c0e00c00040d000721400800c9161410103c012003010581c0710500c956204c54041240b401c0303407070466003035a41502e07000e210120801c1c0114030310310540d44408400000c820411010660300ca04207000c202d5054800ca03883e0300c610405940c2d03002d0300360307019510a001714111450303803901903242000c250147c0141d4a4505581800a0880c0c2099100c580540c0010395105164910703201c110b0060260234908000c04108000001d141001d10301616000b020001107100543c4043ca0080d40500c0d803240c0e64111130075190311300801030b40003845030501541c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 20476247 1250 20474997 20475001
    0x90605040b09010e09072c101809060b030307060b0102070b091c0302010b0d03080702010e0f1c1236050c060d0b0406081c0f0206010e07030b040c02010b09 68
    0x2203418000c1149060006101082c240d08150502203100c60140400003c1d100d04d410004805400244203030303240c15081184801100000c40c1801810701c003c0c17020880300c0b800d05080c84055140365010904203072198000480007001d03d0710700000d004850034540d15110224521003000015000151415020307400e5030417007560f58024101c5e40c0110040c550b030042041d82e000c08002d11130400103094074003a10000c22020000f00214416112103401a070000d00010200005c140c1c09000d0360103c51075000081600703045420320b05031901c0000701240c0e0600000400e030030b4401d1041c0d034a24003400d60940208400c40300d1440754694120800d1540c07024110200c84d8000400081440d00c8440d504040030345035107c041000c001c2070f0382c0080c0c565a6004d6803040030000d95241c0f44180c0c00500049030042500020f801000704101080e00e18a00401071042888285164007181860442c1d4650000c01166210038200341d020700f44442c00603801505d080300d03501095078150801c2454480986600000b6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 20477497 1250 20476247 20476249
    0x301140a060f0b030c07080d02070303140106050c03030c0c120a030207050c060901023c010b15031905070203070807051c09060e060f04030506090601060e060316050a030e01020a0207090605 83
    0x110340144201c540980042c00010b0444a1001c020900c06e841805414a011580d8210408a80158070250300182d95000310050041010003041d0150009003081c030709180701c1510040e42c81c030005100c100c41040110712040003841c01c1109402d520042c11102e0344a01031150000d0082d00300742001c4d07440340301d12102c0300c01c2400c02100f1110a4001a030180130070000c012803003071480c2401c60401c4180701c1c0c0946039500315200d160644054160240001c41c001c110302040100e42020850b200322802402c005008008850300744240c040c0c8015080864950340d0389000382d0540c0601d2802501d00e203400215803013000340204210303002084e140e641d07039050121500101c61115807806920042409003484000a02e403140c041c00288451142d150b00e42520f87d5503040c2040d000b03407850641580280c1c010f005560700480030b81000c14041e01e010381140f5045461600c00a1405625428450002101c2000c244690000008800c00c0c00096645421001c0000c0d9148428400d0b002c0d0545421000308103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 20478747 1250 20477497 20477519
    0xe040617100c09050a0e0711010608030a030506040203010f0509090c0409080c1615030e030408070b071a060603060405090307120e010e010203070506180f0a030c0b0a09170306030304050301140a06 86
    0x713030f1340c1c090803001c0924103120700c25410680107070203203040c03001901418232202c038240902005044c0000c00b540e155416200c1c054151280504a684140c2c01440180400700c208507644e070032110101d6981c0829180c800225040c2281e5101040d00103042a00040c1440100d80c0100b000c0c10a0b03034200c1d00c0103410304846080c540014064540300480d03444081c1c10741840380e0042d034903030110801583d142542e00c241407071520350554030201d1240d0021808100f8050b01e400d403103202c480c00e8101008540303000030003e422884010880ca2040b0760315400321760210070030010317600c00c5940a81c000c503001c1c2d5110780242c0034403070541010f8001007102e007001446501c048141c070804d5520100429594540446031600583e0125240c00b0a216480b060000403a0401516404a00a80759031542c001681054100d00304024200440c041c1071100c00400103680074040e06440f86460740709034894a4001c0001d00b1071188d40d11261703144d17080c0100d1003040c80c022140b00e40501251081004166079641c01c143c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 20479997 1250 20478747 20478749
    0x10509060108061f09050613060e01020303041515030b13050105060d020d0b0601050919050109050a0501020a06110912060115020a0209010b0a050d020d1b020606060405010e040617100c09 82
    0xe002214a00f0115800e001c1e8004c46132001450f09200300070b2030b1150042490b41d00024510400750750718400400c201034000554000010b400e20140d451890142c640410079050101d20241081d07030f6284401459185603803500c003540c3c0c00003441103242041d101d034000c400100e071400d0ba0f01e5480c2402044280c60304030520240164040c003840308150f15600c0d43c0607401c00081c010760500400300000300a45c0d80b084016035484100810b540c00c4076081500042c50b109030703a00140c0c020b0004030801c3c800c2c1c1e80c0004003d000d507039000070041910052081400000d000303112400c1d40180003202c2c80c1c01140302c04034000d0b058030706071310001846c00e1860808036a6610141000b03900b260a8038018060845410000d0044400303506080b4949456949000101d9014005603071010313545002000d100d091940e01c0c0e4041c1c1c4000e00c01000a4180600040c0f114421031090078144080c500340c122160300e41c2c6c0c10400c005d083c00e0310310045002000c1c0450b51150b8051f08040e1400d8170b84030344903810074083c2d59504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 20481247 1250 20479997 20479999
    0x11060106140309390105040b07081303020a141905060702060304140a030807020d090b0414040b040204080c181504020304050c041a0a14240d02040e01050906010806 72
    0x400c8604908040d00c949a10203090403500340600e01c00c0c11a0030000700358002d40d00d0708200640a0340c40780903e1040c14240c25507544ca04001e0100000c1003102039031000d6501490300024030700e0780c81e070445032458022000c90340000e401540c540400261032080c0300250148a00990b000d00111124090305800c0d001180140c5030b000000f0321112001d42000d20280d60300c9442944404144405400700c649810300030902140024490010015141d506010303d07146d28005040c10941d181c1001000a00c9020703d006d80444803508a80310b041e5640d03145c120409444028004542c0d072520755040750740751302c8894040360140103c3c001f01803105070030782c00d4280301b00803c40c01c40c0d11030300507641000041d41c80504185d030389100e5038000e00c900382d58074071405080d405141c001d44800c003c0c040501c600d5141c03540c07103c509104d0709880d20b0017036101e00e1500c4002d00c400013402c2c40c0e0410007041c504642d01031440108a2030f8030124010030315070203811006050300c0088400581c0d65a40714011501203a0485007070f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 20482497 1250 20481247 20481257
    0x3090d020105011809240207030f020d08061507140d110714090402012001060303030e0d081803190807020c040b060904090c0b0a02060412030b010206180102040e0703090311060106 79
    0x80d00b018600c81d0b00810885101e1b064104e1680740100340c40c2e081c070109140f2106066130011381d0104150b04070501844401890002c3c01d501508d00c54040c10021000740803a00820720b10165482c0300d0400000c03120080d41c03048290391140e00751507034203070766445140040c40420028940c20181301e00009541c801c640c0d10520742c0761160490018018841c0000d0130480c1480680d51012804480300380034a00380d4000300000142061460a0080590740c01013551010b5801c09103000303031019071140109038000198581031110342d40c0070020500c1d5101e14101403040b100c241620320b0105900c920024000d409907401c07a01c00c80000340c00c00084807082c0350040d0340401c080041d00c0c0f00e420950001020b40b03001c0c1c039001c4015640d07250003032819032081c0c90200042c0c1200c000c200070401c07000c100d100d80d46840e02e002c01ca68000746002035543d100241c42d185251083d8091044046d00940454024000c00810b000c0581803c0c00084c02801f07006104401181c2c0c40031800001d0320000078124100d5841e0341d070f4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 20483747 1250 20482497 20482529
    0x1020601051003020a09050619030c090503030a0c05030c01051303080a0212011202010207170a020405010e04080906030a0b03160e070f050a0e0307080318030706022b170106030203090d02010501 85
    0x41d0f00a510100050b0203001c001e42c0001016640d5001500381807a03102030300c400485603028024210b810410a85082c0001d0303400511141e2800029120008050709101e490580306060042c0f40d401494000341035582070600700000c0401c44292000100d1080d250601c15841c0c0000d103c081c0d010f1000c07040e40354000c16004100044883c550401f2a50040c010340d0b030b8441e244c2c2043c1407404140759120703115601466042701181068800e00d030051584d4a15401c040c140b607034034404030344600c0c02d40742c0c4642000b0010654000b5141d200030f001c56001001c482900030000c1e82c503503041c080c81c89021200481d080004480500610050001d0001551003a2030420f00711002d0361154454040980c05204806022800c3c43c0200000c1c6020b42c1d10000040131030105e8030030140390190540040045400940c01408011080740d40c581010a03e81c00e000c6a0802409085034480700c0c54000c000d00d0442800000303034498243d40114041c0c59120b080e1100049002d03800e9080e18028402c00c0180380c840d500c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 20484997 1250 20483747 20483779
    0x5030d0e030c012604030206090f0109110d03110109050604061407091a0705060f250206240607030806040501120302100917070809100c030806090403090815150102060105 75
    0x100504c20405030310407548448100441c2d0a2070503504560403409a807000b8140208130300d041081561903480301009004c0c41d50715a649050524000b030506001300411603811041502801003081070080380d800070450700031b8070704126945141c01c0c1c0d0181c3d03543c0e00d0074030740c40700841c503a14815204500c1900e8001101d80b401c01401c610700c094183e60f621000c400c3c010302c0009481070110a001c0c1040301c88003501401c10807a26150300c110809624018007444402038811038000c6140355004241e807516112602111161402c0500340c030501607805440004c2150070150400e00307060140b2000d86003040240e0321050110b1a034440143d010700983d21208170000320944a0300403810051003407684070400c800745a81000c003500030800440f070141001c180040035042010068400300c0c00d5140c540040c82a03620702400394507019107800d01410350200060180740c043c1403014001c1402c802201c0b444085240b055052143c103840d9800320300c00051110160790710000f8124140c450040c84007101c0350741c41c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 20486247 1250 20484997 20485007
    0x1406191814031b120d03090209010501050c1005040201020c0409030c11060306010e04020f090a0609030b090c0f060a031b0306030204060807030b071d1807030c03050c04060c0f02130605030d0e030c01 87
    0x6580e4550000343c00c1c3c408600042c041c440c520205d400c1d500c0c0032401741e50b2441003010280058000e01d042001c01d01800c8071045000800c88102c01241704c001486454500040f802c0201c540450390308141002e80050406070701130888041c2902404018080c0c17202e600800031207200603542e9500241d41140588428171b050341c0242860700e66254110716110b620703030200b12100e00691103d00070410041c0108148201d268410354442400e90141803603000a000240d0307000351a8840038003e25010514070b0400d0f000e540140b07030320150760f808540d910b0560f0714010701620450108074011410a000003920040007d42d120640f030344039030341d1350040e40d4981044a2061214481c920b4000401c44807029036200c1c0304c008031981f101140d81110b00d18120300d01070280c8008442001c1010320b0a010861181e0b0315400361419030741030b4503001003042c00b94103211031062142180a5400640c002508681920701c0d8000c200f00d403019000c3e05e004000e0700c61f042d14007240308100c96805070001d03a4003100643c455 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 20487497 1250 20486247 20486293
    0x70312050f07020a080d02100501080d0e1314180102130302010c081324020a03020a02040f0f110a11120409090c030b130506060604050109140619181403 67
    0x312040700d00701002500044d0300800950b108041300c0c0c01c07400046600b994148265900b03c15045818041540740c10b8036290703112030803031002d01040907140d41d81d5100d9940c0300705404050108081400303c8500b1000c3c0840c000b9041c2c0704c0081002000344045026041070007036032107044032070228403542461500103503902c1400c603000300c401c00c1c0204000d416000c1a5000741c1c026101801d2032002c4415441120b2000c440c801d04030b40295401603040381c0002c3d50004070050f407180e0544003c40d0395003c80002e0800b4100110101d01410f04002800c035400c2e1000000d0705102c28143d40345c1501524020881c0c1e21504200d0151001000c01c200c1800404800c2d041407440c280301d17000c440c0038aa03590f1210a134014040d10714080c0704040525010522408100075900404212480ca191514080c000303490034000b0f01c02c050f00360030a4101e002680e9240010b1b60190250200110001000c84800070006c40c0c003120b0b02062016284008071344403c04800420008102038000e0602c10348507a40f0320580c11030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 20488747 1250 20487497 20487517
    0x1051501020a110d0611160b010b09030a02150c0712021305010b07030f020a02091e0105090105060909060d050f030c0f01060614090d080c100e0307050a020904080c0102120601020c0307031205 84
    0x40d0700c80d80c0f1b041050400200214401e0351104982d60b00b5038078003c6507044041c0d2040384016014030070070400351307001f0408002c440e0381160f03294801c403101441c03c00c079400703418150104c038091540005184035810a6450801d8401c48096860400e0b046060084920a0140d40380c4084281300182c0001d008294469000c03c00303004450007191650b000400c141003c5444135a4100c4417240c40034010a6041c900d8054070046840107010760401020640b81c0c0545d0500d140701d00c07880707c04603c2980b84d01000c00380441d0045d090380c03248403010000e07903501d610030f100e21421032040c0c800e025424417040c0b140a06640c00baa4500c061001000071185407500000a4943d01072011550080013480c02c03801030081c00c41003000f5100004403d400d0400300c8000004c1100d058108000c100c00040011a01da0700b560b0f0304994071101030b195401d101c480c0e4003071030b241c178541507200180402d420512540e586126090076400c45401540c1a4240340c0c55410a2000505424404000280980c0200060040240 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 20489997 1250 20488747 20488751
    0xf0c030315060f0e040506011b0c050604030602070c080105040203030d020307050903010f0c020705011704120203071208040b06060a080f07020a0204090b0103060b120a02011b05010504030201051501020a110d06 92
    0x82041c0d4841c070034015030301032400701d2140045401c0c0c140c0c02070702610062004a6003008a85003100004c0c0007510803503801000f003808c540405081146404068000d040054940d68485440f46070050003584a02001e8402184c0c6420014040382d0501640788615070140c0a1801c0040942919002e500080d0400051010034402040725803400d1003900d01c0d081d88a0f0005c603610560640290900003a41c00007810420281c901000880941c0b185541103944217110f14810706040c2422425405443c90040c4003e070300c042d8001d902680401520701450044038500030303948450b07003000103034410701c6511804109403500003440341c000740800361741c000c410707006032445804107074005422030b000d80300c00b1540110794900501c02d1100d40d21840301c4001083e1840c0741c4d43c0072803880c42c030703a200d041c040e0080c100452030f940c0d0b681407100726120712000c0d98004001d201c03e0800b440c020703020b8081180d903045100ca02d8811842c2a62000880a03449900064a00d0018510f2010b0040c60100035030140c60640d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 20491247 1250 20489997 20490011
    0x4080d0903110a0f0210050a08011208040302150702030607090627080a080d060b0702010912020d02090115030c050a09050405060a03080309030a020c04060e07030b0f04050a02040806060603070f0c0303 88
    0x1034000d0100107022841214022a400c0c131600c100000c103600407408000b0460144140703a444c0c0d07004548a410f445000c1c40c80c0e82412035a240c40d01c824031843d00000d422000a10f000526030003200b000d040d05c640300301d040d1142a580d500c02190002079500c0380c4c0001a10b891740001403400c00f103628607255400400da0010480d103ca914a1a144060300100c42c03e601c00928000c1d078588610900001d0032007800c2107813400314150002000c1c4000c5000d580710550440f5544001c6544d005010b50701540d000d8900f0745070350303564022140307005070107030700d16000c130b4102000134140314460002c48aa170811911218801790500d01800001c100040900d0340280c86100084081115807020b940324540741d40007159500300300710000b4184155412018000ea08002003842102e0405000d642e0100345031070001940341c428000914009034610090790018946000d0020310307030081d00140103039030352801240c585458a40130f024480c80105ca50034002540c070011080d11714419076514102c1802880d010500b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 20492497 1250 20491247 20491277
    0xf020a060f020115060203031918030504030201030f2f07050303040b0105010f02060702031804021603020709060f030507050906220b090a0203240a08060103060b0a050904080d0903 79
    0x2490a420580200e400d040740a103049038240a1145a4921060000015440c000b406075807404003034400520903640d01034034501502541c0c0030b50344021f00440027125155403800c019046500c41d010070b07800242000c00910001006001f07613903118640d4800a0304428a41d98403a6003030180034801c0c04050b00c100080307800314000b00b010314059401210700300d02d10352600d4000741221209030004029900b21700e0805c00e00d1500402911080b24021790260600c00315580002c00a20811600101410b81e1619110516a0000d552400d03103030142030400003151500441900d202c071034070000342558003101c402d1040741041d82e407140e00120f002e8500113a00d95000489402ca024001070422080d9580181400d54a02260390507000344401c0c03011861400c3c04030403e1560352110301c1000c0070074102c201c00d03505a10b40c0c2c441071b0002c100000c00d0b28101c0d616841c051020340040202d0920a0001c80300103c0c40349403040341180a140d101c284c8502d4050180c0c862000780c40c9010081c2c09018618a0301800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 20493747 1250 20492497 20492509
    0x50c13180915061401090b1602040e0607030903020f01090503090d050109020603040f0b071e21090b090706020304050a0e07030209040518060a020406090e0406060902040b030108010b010c110108040f02 88
    0xb00360410034081041410124010000ca0b40d0800036810000354030400c02503400c000c4100d43c410480003039520b00002c014000328001c2c0c060350101c480c10b80f2034441000030322a815488500d0340c03031103503003500c10258007810a40d080c0c8151038000307040c9400c100b00d403c1e260303d0000070b113226052040001003000c84442d00050590381085800b602c5580d0750040c1ca00412001400096009031642444400102003020504d240c0507074082c0032007400b0103944010103841c080f00d2960004070300e4040610100040d89000407074041e06642d07074195032003a0100400ca941c004400e42e0b003070381c402030051021203281644040c40000098500d10501d40d081110341c0d15500c85010b01403160800828000a43d10f03041501c0d460100e00a15191500b44140404e00441c2c2d40300d808401201d81011184000b5200c07428054014055540628000c81c400030340014081c0c50078002d541242d900e40000c001c1084c420005454817140503400034816003005040c40b1040d8041c0300410b40090148403000956203040c2d01240c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 20494997 1250 20493747 20493773
    0x1020c1e03030c03280c0f0201090b0c0703020102070803091008180118050c0406031e03020f0a0605040b01060c170706020c06070302042c010317070605041104050c131809 75
    0x3d0a800005034036442000c0494000703051301d04061444030341818036500612006001d007005240540814141c0f0a40e8810100c45015010311428140e444ad641403026230344511600c022400341c0220315000600301d8000c000c0c1d40004001411020450312070120131280080c0c0241582e01c1c29441c2000c4030541c072824031500d40d41030003030bc00c5502c9580c034908000345800040d0440d40d01c9141049824400100940e12804000600901042c81079056145c16401c0050b2200320190502c641400c0e83c007446207a80045000d00d0150a40791450b07601c40714102d8400041d4500138204980e0320782801c1c80401c6107002014076a01855005040202c4c0048240c14107100b9100b5000007034000c6001c3c0500c3c20815040512103030b1043d0481a400c032100c1180b01207440503c400b1b0003002e280001400d0031400d9808596250707502c410100700d1490646058072040d00d00b500e825005c1d610303080010b206200403008540c4c2a403810b10119403901d140901103e4051f05620003a1410364641d040e080c002400c00c12040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 20496247 1250 20494997 20495017
    0x9030f050d03050f070c02090c07060e0d0f08042609040906060801050903040509060907110304030c0e06010e010c0b09030d0c0804050c04020301030807060209030c09040602030703061401020c1e0303 87
    0x1140c15030080340e006064603409000013010303910440a10801c1e50300800005c2c481e641c10b442d100300c16903c4507010902c80c010b1540c080c00c1c081c2009400c102a440100700382d40c0812050300c032100001d5001d10b044a080b80704590090041c900041c0c0000c6501885004401c14407070f2000f81380c9001d40ea10042000d48000f10320880c1d8041d1540c83c2400450300a006107a03000a00c00b00843c14245000d00003088428041c0c9200d000724002004220214032403004806202807a9084075602d0390f592524400e804124461048603800329000b2030840d6114000400c1a00c605035500b000050580d00c6503004100080c0c544a61031008104c50048503d550083d80d8059036a502d801800785011704101b81803416090685101d18410030050001486680942f181540c104600585440c10b14000c039180c01c0515510070741c004400c004100400544e034005510800c099135080c0b007a5541c030f40c03c035000380d00366011080c05070700404555040c604000141c0c0300c00d400d08a05a004c90074a900c08070b4119480342501e5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 20497497 1250 20496247 20496253
    0x60b03010207241a13020c1002040303020d030c0512160e12010902030c030105090d080a02070506011203030b090411060903030405040603080a020f030a08040611090a0603050a060b18010305040309030f05 89
    0x400c0703c0603d03510809545050814900d00d00d401c0880014003c1011248040800b40d400b1a45c448000c07400c00c8107a03400300030078070110f40d41e903168100a544c6080140441d80024180102405a07500c02c038182d800c2da0759802d880c0110350310340c645c07951034007840411980304010861415080581c0d0700914801030740020000022600c4150044c182052181c002d414000c0c2e04000510071552000196052400503601c5c00c00f0b026285c000050029114151000c1d1103880f41030004168040400c5104500038030a40301040030904000a01c0300681e02140c0250558220102c8007105003401c00c010015002c00405880c07800e61214002001c40e42290819941d0b860041920241681c04010480c9000300b160700031814911115402408201c00610051450380c44a24505c003203051102542d14260000b00010000c54a4400c01801003d084400d20300d20b50404a0000b594403624048070084400b40004e40d00103d4a40e00640240201800031002c00c0b081810001c003181001d20310850b500c1c0700b500a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 20498747 1250 20497497 20497553
    0x706060b03090111250c03150203070f020c0a0311180405061501020303010807051306080d0f1d0d0f0203240a0b010908060a2f0d110405090103060b03010207 69
    0x1035821180c240302c240c54110360400290310900700e41c1d02440244100200301708081c0b2441d01e00050429a07650000700146420300108a10841d550051482103500ea40c500a1200c2014000c903910b5146101c000c0e048600c01c00c090002c160614584440d8490142000e40006410201241030f11012101070380c140d00140240b010201010000310380c401c1d0f0034030003507003194149a207194072850f15100f020b205ea400e80c1c441200c1c1030380b1600071034010406181583c10107040700700e028000400012410002501c2d542d1080c200d58021420342050a102501c1101c042c03403180d485402042d40070710b00ba82e05120780d088880c8018a205c4080f034408807020444036441c2000d95002080d200340e044224140411048103110078040002c01540c89214030300d0100d640c255081f11030420a042030300301320a03001d00846004001c0c0070480101810003241000b00308007507001100e100603000b075020f01988080710b030004001040b02070300100c04c44034000b1300041ca8004155950421241840f103030103409125003c2c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 20499997 1250 20498747 20498761
    0x1f030e0708030418020708040b071707030e0a060302041a0903072c060301060302010807050310090c05040303080109020408071a040e010f05130912030207030309080304050102030f070309030509060c030706060b03 93
    0x60b2044c15111524029400e04065541e80b01041c050b5014405420030302103801c0d018000200340f0002184081c2907015524911428000c2c0608042c84000740142e00003000029181c2c0300f803084a0031101a4120360608071415140060035a00416000d50705115080010400d900e8440c0c514010aa044c900c401c020111154500708000004080c68070a9143c4042000940d0304004040c0e4440d40d0351502950b42e940d40c010a402484068124402c120300e480040754440f0380000c000c1c0f00752402500e8000060b0399840e06801688a1070040300c0564200034420001c0136604030b20300601c112110600744c202902c46c00d0010020209074080c003180031400d0710070061410900c0641c2c500004103e001c0c026201c0d50f0310b5502401400817203e404240d40041c00c081410b00c2684400200340d0b01c000c1456580c181070600c00d020750800c1d29080c00030781400d0b0204007900d0007481082203580d81601c0e054100016035040143d15000300c0b0540d81540401c00c14580007903002d100c2c042c003400604800742e48a04000c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 20501247 1250 20499997 20500019
    0x203070f0203070302030715091b1403010501120201050913020d061703160305030c09060301120605010e07120504060e0d090303020d050a0507020d111008010302010e0a03021f030e07080304 83
    0x2180c40825504100010400300741d01004891110703030031004010030742d416460600003c0c8000c800203000b244442c00b00041203649108000f00326104060000e4015100c0300426080362002c1c031130708407183c410404a10055001e54090b11180340001d0840052015107070b4800161313400082410301056031038a084c080755030110010420051040e00841c20221419000d03103428000b2500901484008000505000703040000c40d02c2c0000041e200707503200c1d41d40e039103504c2180310141e600319103031030918001040c80522070b000c451141e01c031555400c1070400310a02003001841c0180080e12150b8a07000f00e018400410000f0200c00d4031141d64180c080c0d403440c100241401e03100400b00b01040010407000c10b00c0c560010980e20140c0d01124140f90603120b40c078005541100101074541c0081c0074904034200d01e9004080365040728001c5c1c03035103044003012400300300c550381040c00001e5002d01e100d01c40406081c9107201031b045158080c18000340c145000c0c240c0d60701e0410641c1c40703122950300001e4140888103031300d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 20502497 1250 20501247 20501267
    0x5150901080a0c0906270605060703030b0a0909020105070f0507050904050a021306050d020f0423010f06030b1005030406060806101703030912070501090c09050a0b0d020f04090c03020a09020307 85
    0x82004012090034080003c5842ca5506c5240034401a01c0003240c8284a96604c0400188001820a5500e64032850301a001c2e241032003400b4460106800300040c0700c540340c02090109a4140e41d040d25107034031942e81c18041d0400030703025940384c030420b03802044d40c0e200d50001c00d00680c0034100400280d55584100700000740304112a8240a05040081082d0303115241032070241c5904032034000414194202060003805a5162603100600d90508240740c1040c00300300d541a03640810780120746549800c81034055a40b070609454020050410303090209224001541d0014440c8402103411a41d41d03200c00c2c43c0c800169048094882d011200b085144400303101e0070982c5103c007024500350700d80038800b43e485040440d82e00c030413424005202400c0101c00e50054004947c0320958514a40e1245034100c01001e00304c1c3c00b140c3c0c5900d00010b8000501d020407401d103006a00a1011041684000c00e000140844540407282050400000320050703a6000000007c2c0681180050701c85c54003100c02403141e201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 20503603 1106 20502497 20502509
    0x1605010507170409020307140403020105030a0902030a020a060201020a0207080a1104090309080a08090405060603060d17070605090303040302070b0a050403120504031a090717030d05150901080a0c 86
    0x481da000d0343c0140129505e00c1e00b042340070034144a039445240806404a80140001140c0c0801c41c0c014001040c0b0140940d00c84500c1680400c03c0041242c10000240c0d401040944000b9410000540200006001030540c0b42c074a489140e81c10300c01a000c1406030b40c03a000c450042c140030300c0380b60005000c0e12007100d101903210b00300a882d64200300c8603d8812420007011502501c0d050094a00441c030090034040808001d642d61103603d511040071176005c000030702910020071031a200f03c0344036205010280d65240f031703d8500203082880e40d40003410742a0040c421401c0d4181d011082d181501d82c030100c04040c0c003900d840151036502581c0e0006082030469420707504503001c40800d05e40a01d04540c00c452125840b0031500c0c149004940c0c0700c0886500c00c0c401e80e485080d0716002144c201644d0200c40e051401c0328008140040c4090300141441c0d48524900410000c409040d8402414 = true := by decide +kernel

theorem cover : BRFrame.Cov 20323747 20503603 := by
  have h0 := BRFrame.cov_init 20323747
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20323747 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 20323747 ≤ n) (h2 : n < 20503603) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
