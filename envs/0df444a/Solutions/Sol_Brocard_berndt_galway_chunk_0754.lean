-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0754
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:35:53.112843+00:00
-- url     : https://prove2.me/submissions/2b827efc-d857-4067-ae95-03492df9a7b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 135431654 ≤ n < 135611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 135432904 1250 135431654 135431669
    0x1805010b07020f13050a0c020d08090601091d0102040816050603100303080a09061a0102010606112a03011a03061506030a0209030a08040b03091002040302060702091f09061d0402010207 81
    0x20f40100d640c80c0c44104000302c40311012482006680f800c5080c0c00091b0104e54454030060040142e54180b03030740500c0b2550b0080315130200811107a82042800340c001c000c034890340b04001d036107466501500c900900060000d442050064160004e09134140c44131190340340c001c035204a00500420520401e00707040c8400b225090b10788900d00d5194401080001c0c4041301014000f43d0032b0014800300740c1800c14100025490070b0303000300821031b91190221108600c80d810510550066040003050b036401c9076024203909411040080c0c038801e40d00c0004c6c215142e000035071808026052189090386410303c9000e902541c4000050300e4052202c00007000c521006142005081d03006c03c103018140c50410100300d2450744800030360f940e04d0715000c0c0c4088540044920300301611915017090701840141c001c1e9402c03a50301034280350401083d68204418040010704c00d0801e5900c0380d48141c4c0c14000160904010641c0d90b0002500b5030400031050b124040d40f03044c0c060100c03503d1040c0401030b40c2c0040c1e0b81c800c4402c0c2c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 135434154 1250 135432904 135432919
    0x10c02061309020715050609070e031c1d0402130302040e0f0303071d0109031509060b090c340f050c060a031406030a0302030f28091805010b0702 64
    0x920014100307000d111004010040d081c0303808680070007903078010840039005000d5520b001d00000340302c506a80003101c000390002c580601045400b8000e0f80c00010000d40103054031900071484124100702c207610300b01400080ca00390a5110f109071088583c0b0025130301514107610340000780100a0440c0141d100090140c1e0b07840c0c0d000c521503001440156401040f000c143c036a02d007003d0741e008011124030400d07078080f49203100032000158044e256440840e03610424100f0604000d1074000020400301d1802d580e11612924000b040e030383c9903031101788981040a0065159656215031320940c1954464058180c5800710b4003004000402101d04019580400240001c0065141c1a41018164848142c11030008030b807201c489500b6420807a00901c01c18540681d0356240c4081560b034074026080039025030020442c1c1c980c25103012004002800d00d580e4885a61469980d402c10451440441180012900c006c2440354182041c45a90002c403009000e00c0554105250802c09218000009115224 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 135435404 1250 135434154 135434177
    0x31211070e04030e01081f15121d0d1803021005071209051201021801050c070f08010207030f02030403080418060918020a05190e1e010303020d080a0b09040201 70
    0x1010400400600086124030703240741014a8003418a403419420345000c181a0030014107564132131140400703102e2510480034a01c034607010300119000011034185041140815100c0c04451f194003400040304041030300741c0440e905410b06039050051007120328040001ca0103007911400300c0210488141c98040b83e035000101d10288040d10a40319514004201d40070340c198400300a9005130004084441c1034400846518002502c1400c03403041300002d00c40000e680468162552240014000300004082210f01e90764458601e1602c0ca801907201d0f0701e40d0b039000121002050b611000007080c06145000541c05c01d4103550b55129103000341d000d6005400e20b02c031424a00d030102904500003c00350740314100204618400706e510000c00291080e8003a80307840c0310004003424070400c0007400480713807a40c0c2110141401161254a0006495240c200c20700841c000c0700c0c1c4540e401c03810f0085129400800440c441400042c21107100101700e40149490100510455224821415071207942407811943c106c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 135436654 1250 135435404 135435437
    0x30801170f0d09140d0302030703030504020a050301020705030c0c0a0608010608150904060c0806150f0c07091d07290307020717010204090b040605180a230415060312 73
    0x14540c1e00001160721a071440084640d811010b4801501c542e000d0100880b1000024461490101d80c00140180d00403c01000801c0c03003540030582041c13004010208044e61040001c2c00da070442c20080d20160000a064160b0384400c11543d04e00c0e0300c0503620109920b01d070600141c03018505101c1c500c280301c03001000801620751036902d040f0f07600000f8202141802c11381018001010a00c02d2500480c881d40041503aa1038090101c10300c240702103071101d20780423500400b08410742042159401034819000c1c00304d0900380074007601000b060800d034910411140242400c0c0350009035842700100310038413807049148000c2c4250000c003902a001c030050792038459000172850590725034029608403203095440c0510203419002030048a41d803420500403030605c0f1003040110b4601d4440d00c1e900040b05030a61064204010105600c0644130000088041c2c00030b0106400000c601480c3c49401c1c082802c0101300615113000801c21114410104605421550ba154116180213000d50600074600d00900204 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 135437904 1250 135436654 135436663
    0xe070207060f0314071707020f03030610020a0c1d0a060806060d0f1a01150207050d03030c02030d05040c0314062406090a080c0a0b0a02101109061602150703080117 72
    0x40071300c411400a00c0c900750f100202030703030058011055142012004114134a20000b0181b542d050b09001030b40c0345031a204200914070a2200c038100550150001190200315110149001000c803c112415061003500003602c031110000c042c81400751412009105000001035039560101c1d0903907407416141410300780308400401d050402010307402c41040411a00000071443c604a03198441c1074002d0305203108069031500d006002d0a80c0000b40c1104020110340302c0d420021021042d40156841c150581d50302e1400d40300115015035540904010400801c89011940320343c480240d405060241001e500e80c4020305059039074054501d0401400f0031040c0d40384012034594881c01442943c40541c1c0352003c0c3d886424043c0401e110308110300d40050042d50a4040366185251640a81101181d1200c101e00900040444078003007001409000c9185c2ca5940c02042450000c868540444019204010700d90382444d4102108110a200e0000041c2c0c200c411241076415411054808800051506180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 135439154 1250 135437904 135437921
    0x309090b0616030e100e01080f0c131202131406100201020d0f0b0f0604030206030109020c010209040f0f0c09120201050c01150e04050f0109030503014104060e070207060f03 76
    0x207004401d0b0441d0101500310860110000d01900c0c44840f00d44950f4007512561600301c0580c0c04150120300080742000645801c139400400000700d03608010b41c07210141a216040d803c01800000c0ca06104815464504002d200840d580041481010010798082c10803101c05000b01c0d008080925044800d54001c0d0161100170790070000c1089248240c82e5002c014050003110280a410819100e45a6082083c110750603250054006450b50b464081300200950018808046556081c400c1c0100780da554003035605080080c640200705800c0708040441101e5069814100380b1104820801894009240300da5505409091054031035040f0301c2080d0141c035200c4a003004407e910000072030080f5001c9a454003c900a00450300f00c0c2c02181d03071644c00c0350414480600030907424001000956061591042076110780c10340e210040d411007540210000f200300f20000c8400e13080c1900c800c00d0815100700380c01003964094401042c1000f803406910f5800600a00b8100058105210785090094200004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 135440404 1250 135439154 135439177
    0x6090503130302040b04020a17090703050307150c0c02010e04020901090f0e0106091509051011010c021b03010603150504020616030e01080a0c023c07061b0309090b06 73
    0x98451003140c00664100745404100d214603e40403074180e440c20240f09884200740c6603103030705144030301d49003076480c0404004054101ca48503100b0040001881440038140c11380c41075080200c4801e6850750030096a403040c01c4c500810403d400300401503a4000c0242140134020b60b40142e407000440012110701c601c641000b03150304200400040e03803241d0340034414100d400c070380d642e28000d9845041c05129007010254400010700012024081803800e4070020401c051a428000c040d1201120b40c00c0c20f45000341f0b6000c015810603a40404480c5007400751344208003049000700b20b45411a80c1e948800c50400c41c40c00e0b4016515800102152142001c40d50704032010090594006054030340205101c803018001800180502c010910410f480c0c041c0760000980340c3c01a00100000e10300ba442402c80b558900d02802c240e1800e190f8200140360310751044030b0001310140c00502c1c2418005441800058017501224041c8001140429488460481a038802000c080740800300b800004846004641050342c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 135441654 1250 135440404 135440407
    0x5060711010201060602072904051008010906051c1412040905010302130e1b031002270105040f0e07021515040b0306010819020307091104030501060e060d060906090503 74
    0x106025000c1820554040309a0081c428251540012a00c545251091a908441c000014075600001070644281c1d00482106103040c680d840c00024079000c4d282c1c0a41740400c44840061086c800d0b01e0003514003400054680f0751021420320b011a40382d0b80c140c2d10140108894901010403810b0030b10515506c80e1510250a44981e110a440e00040c45e00b840105d100b04c0740340c20204010a0240180c11101a03c640031b041a14030b006c884074440c644c4a41419454010664a02c102242a10141c403d8100203000d03200d0304d1401101d0801d0a620309078205040c8403007400b041200304085408402941c403080341e1010181c48024041c2d140c07a60421100140c00710300003c00c02c0510303082000e03903402d01e0121400c0c81456400c2c07080c95200d00d0207005081598001245d21b000046543c4c02c04003103140b0103022030f511180d40300402c0045a11908000200040015040040c42400d010344000b9003aa54140d04050030305200041d00304803a010000d0132203850314491800e00c040c560103000d40e160490142c9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 135442904 1250 135441654 135441667
    0x10081501060201141308090a050a0902040503071a041505040305120c0c01030902091302010512010305070305060a0606080609060402190201020c0f010b10081f03060209090708070206010308130506 86
    0x14051020034000e400c01076191140d444480c0b00140c00b4a401790781184007079105450f107620741003919400030745e000b5008505000f0001c0c1d01e071101c810800040420050060300d40e401d060801d8100300d000d501c01e2819161006801600d0480c890449007241d441300315000740c0406070103082d502030140303900c040c090703005200c48080e0031400200244100090300081c0d407100b400c03103001582100e1800501039088548403001843d4820070152a54000d80141408c83c28111100c0c08051840c500360402c03112a00004020000c2040400c011a04100d01d10303000d0103501c0c03d001005040090040480e849402403501007171803929554111391200114907081c8040c00f03408030003c2d010758020304521115101d0399610707503604d40d010f02c220150300034020400b8800308510541100c0c5400301501c10741650301500c60242034078501d403844034020340c4141800b5886e4a141010013502d000000c0081051109190410251b59804140c842c150fa07445522592109005907210602c80c5442d08a40d4001c01c002803c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 135444154 1250 135442904 135442933
    0x708030a0e01081e0703020a111c08010b0f07020f01050d0903030509061003170a030e070914060d050a061a040606050c100b0619030b10030203040501060b0307171008 73
    0x88886090302a00e81c0038650710313501c6030143c4030b1008051030318011440f000844c5649109030014003881d00b09241c400415041941d41c02e0800080341e1070780c9035003609864505002600700844900400d0700f661101c2c10b2804040c00c1e4641c5200380480280702c0c42c8034207401021607000c0c1e000c2e11110b0300001c5040082c032100b45030203002400c06403042c0310b0781c2c810403000030451a0b41246071816242c0c80701e1080e401821480e100030040c0c005001000034592641c9891801100402c540c40042c000950b010035006121070420300004e101818a17401040080300f5500400d40004816250680c03040000031350300001232034a00a01c1149240682c009d007083c2c00007519603400006806003e0141040d40c0d4420300030892401201c01902496030418024045100031285c0c03440450b8400d1000e09001c20070504c1c4034001200e0100f841b4095001c00d601005020500000340315000140c001d48207071030324505001c040074203030b0511041d000142e0b036200400a400c850312540790800038072510301192692826040c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 135445404 1250 135444154 135444167
    0x1020106171f112209020c071703190503040f02030601060e0310020304112106010906180605060d020c03070203060a0c1106070806090a1d0706091e05060703020708030a 74
    0xa111200301c05407a402d081c0c03040300c0c82486100c10340c01c822945840b030480c000c000c1052002810020104010400042c1e101d120b0009008482c100e90243c001c07030342407120300712581400c0721041311694004d103c0b10900b40d4201c0d08030840c001c3c450800c282c990f580e6182c00d10224541c0c81c00250507018200000074040d41001d22000da840c812070503102c250034203410607c00c9010460b005488813a4120154086042014505440382803800501075000d07403560354246052001e0340001c030000d544007000c2016120b401002e0183c10020481803204519002c00034050340205c8440c880103070350015200802d070404000725505698043c083e1000c500e0304c3e440d404002e200050740031001c142c944444081c02d1001040d0103200b00c40546455203070382c07180c0007405842503005180e01c90041d5545451507a802d404440002c8007801c0e6002400b109003000401841c0400d036038851842c082803030400074590941d1000f82001d4072029034080b501d0b101c441c01c040340707464050340c03002c0d5481c00005800043c1c0d039400784 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 135446654 1250 135445404 135445423
    0x4021b070807061106070c02120f0d0f051918230108060d121416210e0918120301060e04050f0402010e0d030e0a0e22050312060102010617 61
    0x10706999000c1ea032090252600c100071a4035650b180c201400242000c1d000745081814240050203d041440644100350302e02580c04002030007640c401c011030020664001c50000c40e0311000d1511034141410304a141c4440d401c00c00030401402080103500941d400c03910f59610042c0000c00c51040048005000c1c1100d2141411103a8001540f400c0000c2072030034482a94050241d102034100071000a0303000454a000342c5001e0950308810821181ca6454504c201828096000d10840c180701d01c100182c3c440700203884489503050000e11416a2900d59070310703501660081550f21982803140b10142118100038400048252403440800040303003040c1d21103010a41140c05039000c1056468044d80d60200c590119002030000d42c079010703107240703504002101090061090a001030030035078042c0002d5454450307030040541a122003041201582000c1907003040e6031864103980170380c21915200e068a80c030079171145036003803040f550102c0d2941e4400d41c071040007400f03401808040d40c0381a0701e90030b80360310003003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 135447904 1250 135446654 135446669
    0x3070b10090b030a060b012001020a0e03010c02070b1b06070c031202090a1e05130b0414010303020a0f0312090602040302030136060905010203090a020108090304030c030b0604021b07 80
    0x40001c14964401e214042c4601c5004005200351019136650b04050300448900c28100190429000c440342000551303005210707840d40000d42c0340c080d020700080074041e00c5a2114802e03030401d83c400050315004209041941d0820a00aa446400030900d058102c1d40c204043d10074843c003c00c022b0032a500c0300c6c40d40003da00c03950710400d0ba48040030454042e8020a420640e011502c074204000c2002d40c0f40000c80da180c03100384903001185d81d6100040325403200c1d17061010fa898491041c030300503107400d1088030420142090600c02c154115140250f54880c0c01c0030040200b40004c9100701814002d80300c00c061584010024088070700103103041c80181d0030a2004901079801c00200203802c003010002c060182d00d103002035000f880c0c140e1020480303125009900382d9005030f0701c240c00c0e00403a401317000031481411030030010b001011480c8001031030b4400003130403644207400520003440002c0c01c0c1c200b864212600b0012507010f54507000f001030002e102e48105000044004805000720b1040441d01c0c80844098 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 135449154 1250 135447904 135447931
    0x31b0c13050903090108040f020d05010510080102070515101509060f030b1f03060803070b150307030b060405040221061501022e11210604090f02010c03050c03070b 72
    0x600500001ea41c81aa0300380c2c0e03290018000400d5952050403410742c010b0281002900c88009500850f034141c503410700989069440d5001c200c644400b48590302c004002c020b00071441c1c00e0060b110240c440b228500b0307030800b040350b11000c11a0a04240580806400e42d1100b00c0b80c0c0d10510100a01028000d00c601d00200e0148840c910754580644560f6001190152004188102001401c0e40c0c0c07051044000040c1561518046600755081000c0c18440740300b0814240113090840d541c03c0b248164400580c480e03031220a050000801c444141a00075109490101d556102d80c0f0003e6890381e03213001c581c4807030341c3c0d01c80700140c0403000002c101d805182e22900c108a4940c3c3da500480e00c51100d910480c41c203901600d011a42d00703020901c0c00002141c00d100000d00f050a101c16480300390b0202080420b20300d42119064108011341d280c540d00968111010402c207030700395490410b41c10015202a0500c4281840710041c5270140b412203920b4802c80c01504ea44d17449074a0a0b10305508151041c0404030300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 135450404 1250 135449154 135449179
    0x204020c07090e060a06051804050102040803040909051c050f0c1915050709050f12030f03010324020406090e0901060b0d02070b0112050a080307020307300306030809060705031b0c 79
    0x80c5ea220300c106480c00034208400c14240b8000e0850034a030050001c9070959420440090303850b80c18406080641440c4d80089841e05036424540d00d00100c0a01f84070098420312003040006410904584002c000003400396100c202c1c0801150800c85100910907104001000b404e003044944d09649501c0700110808100940310000c0499081005005e60707a044003030307154074100e00d14007901e1001d4041e1141040341e1420b0b060102d04c0340c2a40080e4411900d481040030300750503400d06403012100c0000c0ca41d80844c102071170134074010071005441c86407285030171044001c9107144030290400b0300544030584103039a0741c912407800310000b90302000003620031000d10b0001094050124500c00380043d0031030018080030401d91920406075101070000e5081d481b0403c860000614001c4182403d6506546580401203041010f40303c0d001104003440d042510b801c90a1000a94600070382d004498291581900d8007054a030a40c50341c4960500d4070a80c040540f141d51040c200010701052111054407298103030070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 135451654 1250 135450404 135450421
    0x31e010609180207051203010e0c0f1b160b041d010503100b271605091003150e010308070201020f1b040c0e04050a0507021c14070204020c07090e06 65
    0x1428010800054981141086600c2c0102d00105501060080041c50054103a0300c0c6032401d140c80301c03000f410102c0480100714041d45009810f50040c010100c0700c2c9085030110039244540b103103120000300003501d1001440014000c10449200110742c0d0288040182c90707803080e62064020344514940411079694018140e140700719a107040b59005030040140c3c04143c803175900503066480c0c0030f9070003001450600080d0150511903240391080c8000c03801e09401c00c55216503504c9009140d240038010100071000d400e4a81c444060064059032400241d20080b001c141c0c40c00c3c07507155201002314407800c1d00200a0011600082619500c04d800712143c0c01007180c4d42d135072184501d03031200d05079100000f503084071410903070080b010101151800300414030308500010700f141c3c000e940e08007025540303e0800140d1501080061080381d508400c2043c1064080c800510340c4086e075180c111a51000b1810004544441d01a074404075140340503115169102d05221000749070094034450300e4400c401c08502c595 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 135452904 1250 135451654 135451711
    0x5100204060c060506040e0d1110060308090904231b030a0b0a020f09150703032417010b03010e030a030c03090209060d020d05160509010503010c08061905030106060503 74
    0x6079200e46850b20240b0580c0c030380350001d01008025941040d00d0f01050200c00109011140a602068848a40100c1d031680700d50b25040d030342c026051046141c03070310600104031036809586004508403841c3c0788650b21486c0c422241d0760700703042001d440b0b04081000b050310170010445907911040c5600c8035940610140c201036a070001c04202030419500c45010584030103c507001000790240c900e401902d0620840041040a600c02003118001c1d20042046410103505002d08065290500300712009101314480c08808050103216a003800d2403102c12612080200f9004114000300040080100c000c1c1c1848103900e036440110204000b91401c020100401d0080c4544c0784e260341c01522031180c0c1d0340e440c03051000100d003061301680c1c030403003640c50000042c2d004c00400b0030359603038000780d195458541024021800e0b41038010a04c81c0c0d040a50060100d5440388090340d01040440b440300041c60300c0d207000c00b1023000d2500b00c1c98243d403c2200c007041082e0808011801a101038840a00401c01806005010f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 135454154 1250 135452904 135452909
    0x8030a1103041415070206030c22050609010c0302010905070816061b0b040519140120030601030b180a0b0108070c050a02040b01090e01080606090f0906010501080c07140a05100204 79
    0x142d990002c0030860307500707041449400803181c0d042c104c0d2070086160001030b05900103c80c5841c0304200010020b4038905c1440c0030010b115803003031280348500d0804000829078042c844409041240c2d08158005051003500880541900b101c01e0b1400182c42e80b8095807140704445502c2500d220303460303000a9080c0304810b45941040543c8c03100c0d0a0ba086907640a035031170005001a5421700c0344035551503180381c00c4052103a9052040030060060001801d44a003941c03009102400c0c40c00503458282002507270f1400303d070b81c06202441d000403a11800c0d03000807907452044100c000c00001c40fa040101e1106580c0c084802100240c841020550b91084102c4040740c14000c0101290400c5035080300606154012483c4050141044c55245480e40003591b01c01760241e2001c40d240c1d00420070300c941414072804483d0400c002903003800003443c000c01e420799124018420b0030704200480c0000368084038a041901c0041d988407044208825199090b555505004a02512580120030b03403d081c117032551084904 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 135455404 1250 135454154 135454169
    0x206030a020a0f09030f030f0504171e16090c031112010e15130507090b0c0102130902031303080601030b0d060e0d0203180105090406080a03080a05160e090402010306050a08030a110304 81
    0x200e400c3d40c088403032344100070846040c4001884007141420281c0480e03540021660f004250500d880300c100342c00c900007000c2107074058000805419515001030140419641100c00100711410804412030040030120f105500503080850102d1040d0260001241220120143c80c8a5a1184140c4003c0305103050107080d0b00840c4108566141c07113407070300020b07801050b070b08028008a594018001141c1d109480f5400980d43c005444d001c0480510500805007a00404c00c50035884d050000b021594810b0001a040c44000400610b0076803198002041e084000740c0614020200f034580300014020031141c1c085507001d02d8080d404801d10001c143c0700149030741c150003007440380c070040151050741c0b29004c8160030036207604d40800c80c6c02c400c00603e20460b02c20307920450795142100f060400c82c2c5010303100100402d58400400c41c3d0b2580102c0302c3d00c1842c401c032800121a1924030043e001030603190f10407608a544003400085504000c000f8081c00007031516185842001c06030002d40701d00c07450240c507a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 135456654 1250 135455404 135455423
    0x221d160c0204050a140703020d05011505070212011104090c030e0c03060112050f01020c0c0102070605070503030103060c0c0c0e06030c0123030c07061103060f010e0112180206030a020a0f0903 84
    0x4015142903002607401c2280100c00144554002c07170829100300e011222640032130340000b841200c5001c1071040c58014030b0302000d100c00024010100810900c102070b4081d2040b10041400240e1074800c0d40a9111403048014140e50b4994462502c0007601014010201003803a200d80d05070380032000701380f0000112000b0301400d6280c0c2003410840700d12400403010b8606200c4d0030328088982100344020b190070881030780100b240d0310001000901c5d00809400c4181005130a00c505800100c0000a40741540d03844840404c1290380c0c400d0444508004107409000c1e0902d201000513001c03000e5218a00030300301501903070131040400006640c9005040c184050941041860a10400710b08000d0364105411030070191900300c4030f80340d01050b501c007110008110940002849090b00c0d0050203d90200c00030300744111003010f0600082c00081030b00301581540c075110702c14035502505041d0014000795004201c40d860b400c04070812002500124000404140380c1400c28a585001b40354800480381d1201141 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 135457904 1250 135456654 135456677
    0x6150b0304020a180f050405060a0606050c061b0705190516050a05060a0c05070e010503060a1103070e0a120804050405060a03080315130c0203190912020402221d16 72
    0x44a282d4800c4c1c0b141c64036075104480000a030003030090740d01403401800109102d0400518040441c0c3c3d040e07200d10280700381000b0000c5e0b680780100c3e41ca0340c85030940084407084620303c00d20826900c140c500051070341c040c140e90300407500792442e95010514065070031200c1d24082c01e802121580f4180c0116940710f20241410080ca2030044000d04260120b03181034001000320780d995500d0042e46070440e01c40b1484507001440390341001c01a241d40811541c3d418030900400401c00c0020b480060000f1041050618400c6181c1d103650507200c2c01000354002d540c000c0061420f003002941c001d80240342c800c070304120105a1519105000c0703419290844010b038699202e62004424031b8804640c41600010418000740800700036118044001c2c2003038000d11740d5800340b048041d21001c1300607031510602c004c0321b0050000c0d1506010442281e80d054400681e203c0c1d0305210032207056032007901052480f18400000c940310385a491403088514001c11002c900c1d440b910714800d045420200781100081424005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 135459154 1250 135457904 135457919
    0x3091d04060b0f06090d06020f03040b07030c020102031306180c090c1b020102071514030a02040e071d06090604030b130c14090a02031f0312020c01030b0d03030e030d0906150b0304020a 81
    0x15498298411f040051400760041882c41143d00100c509071484604101041029905805641400740c003601c000c516516013032410041d0141e1408000c5c02650703891010100415002081d10b000030f4000701c2c04440a507070b640706080502801e420b0500001c0d6600c11040d030405103440d1400c5056416000744c0089810301986103000101c6412020400004403842043c103038481d0300031401741801c00d102507911410310283c030020303503c05402c4600700201600000f40030b0140104a60940e00c08440880c1d82740d40075000240c0d01d02603a000903201d0f10a28007801144000307020f600395602d12510707100c0c241c40d503584030740c0c910b0510030125290403031180b10000b41040d0403a80115401844080a1100f003454440b45d100f0603041501708603588000e9580036241d0540401000b0384070b040901e014003401d2180750100310755100f2000300030180f6840b00340102101c28180706460220b0043d08081043c4040e82c1000c500dc0d003a50183d040d803a00c02c951021440b00428002c403445641c01801c6480894a402074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 135460404 1250 135459154 135459169
    0x9051503070504090207030509010914030d08191a090612030307030f0603141e1908160f1b06050901082404020a0804020316061b03091d04060b0f0609 66
    0x1e1042008010040800c04500342c0c40607112103400780e500c4a40b6200305200140110400781c0146100411030202c0594641d000914503c010040707203040035698487d180c0340d01c82e03494150041c821079814003581da00c84402e01c06240c00c0c0745808845603420f9494400602035138001500da8101150000c10000754014000d070404a107146818000142d055683e45588031056a2102e00b24126080403090034078203c444005421450220000340080c142160303828040303007030140401400920086100e0b403a0300d807807c1d504448150044c0c003400d00d03450745141018414007541001134000c207a900010031840c0c8114162030b10a181a1a4060075031902004652840c891900304000322040c0050351440c2d40750780c00a40785556170740c0c5544081381460700c109030401008003e0040d4848020fa4108035071344d4400100c00740c581c0000450305804400c1e04080700d013140503401c4240c002030480382c0b280310807503074201c0720344210302401c010003403441a6000c00c100189081c0316a98480c00c20f012414892500f41d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 135461654 1250 135460404 135460411
    0x2040b180f13080a031d03090d0213061d010314060f07051c0204060f09050d080319020405030d0509030d030501031101050c0705030f010c020d03090804090e0a0b0a06140109051503 79
    0x1100c00b41c114819a030303059281e4400340c2018000b07070b140c0c0c1e00f0700500e00000c0015030071008100095414600d611010914103400b0f690080d109aa40c480d41e218404801c1e4810000361840304101003582501c000201452003085c441161503140408447c00d0781800420814000d0040b16155102c0342c070b84010449884c0c210038406030401e0014034404d00c40802c54401030000b45401e8a48a036003004881c40600b544105600c8507004240700808c4d840080c503c54108c80d88003c042502039010400c0d00ca00078028055030700840d815100c1c4284076010150424050316001000f1002c039884190b40b09022400d07180288002081e038010315a20000035802100038080c81c400c880215914261340304002807920b101c4511280c510b95480ba440c0c208294140541101d1800c10b080a0040031000d07600d810301c504c25407069040240e601c00d0344608810041c00f0140483d500402407102c2824040c1142005040034803544000c090808840043c0354007450040085034402000e4101b0300082d00e13800c500680c0010b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 135462904 1250 135461654 135461671
    0x50412031b03020f0d05040b07020d0302030103080a0c05030c0102120103300e0102010b03011d160605071e02060307030b03060106020f10020d0b03060907030606061b03030e010b0a1202040b180f 85
    0xf0b001704511500244503051145004802542442c2006c81010f03041595210420b002c040c010401032000c680742500f210505692850800d0030247e01c0d003440b0b8290f01075800400035075400040c2d00714150240d42a014142ca0294611203030a50051162003c080c0041a040c0032008070070041404990040f5901d0150f99010f00000c01c0e0b804002e40000d013104c424642c5050f040c000804402080d00e002c2204d0400c040009950404071414440c0160240c000c100740140740c1c440b0b040031a5881740301490704090782540a8803950f00e0341400c00c0c014020340000d038039582c040e11501000007841c600c00540c5c0c50003903400ca409454000289400403002c2d622000c1d01c0b0b581c858583c1d00040c3c0548080122600c01c00c4080c000c1c1492504510300340c01070383d840740c1c04041001500820b03a40201003940c000b60400e903044c100041d40142032180e207030151a40780103660b488030013240001440e00c001c43c42011164800c503420003c2c040598100003c0c80d08140140c089800180e00040c1d007200790070a00c5401020342c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 135464154 1250 135462904 135462907
    0x30b0f1c11060c0102040801110406090b0901031d030306100306120809060c07030b0f01050901030c0501050c0c03010516030f020424020c060307270501022508010e01050412031b03020f 81
    0x4580424503030781c44603c044001c0d0b98001001c001d180c2c802c1c8500f9121007480d03011a803415241010090801c5200e0090781040100015496011380c002c0e40032000e9540102c00b0803c202c15240807890b180d40080328054043c100c12111200c25921a02c0396400f5991071a81d090302800c89503d40c96000d0700708006003034101104000c00030311a0380c2001104003d510440032480980742c00b2000384120710040c3c0c0300f58000e1100500510004204500c02400e840003840c01945030b01c0b5040440d890700000c0c50344690103500c4d041c280040d82c42c48035407466801200d0345081c011082040c92070401c030301c141e216154405054a14014882a5940007070304491802d10455401020b11000150f0b581d20030744031500491414054402080e844403401c2c0107508910b2617a0b4951840c180c0042d485031740300b4140180b8040c5000c201e201c00d0180056850151480700000c100e20901211714a00034a410750f019a43c08129156135124144a0b01410003501001c210303680c3c82030344504040e00a90000c400310502000c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 135465404 1250 135464154 135464183
    0x30606040e060c0d1e0501061d15030601031b05040603200702060703091d01050a060f140c010e150403030e0d090603091e120323010e1503120406030b0f1c 68
    0x308031000da070300ca403c06175001655501d0413402404501210401c1210030026100007105a0b4644028140312802d07079a080f60f172980c80c1e100480091100320b8898a00c029041e0501030ba080d40407020b03100392109501c0401411207040b21102c0309140c00080e20f00c0c01c880030814000141401c00103410064883c2c00c28541c419212940d0714804100d2a490594002011004100b545810000103000700400e080c440d0520624800082c0840560760300c2d060131510009440b0110102544425000800241601c144081116000003004d2050f281980024100012041c4400c808560303400104a261141c1342e0803441c2850503006011540c006407500043c42000d034260310300100b400211070b441011005a501e03000c903405021941c0e42d018221201d134003406540101101c0f04000342c15aa841180c0821130f584080010070251510082290540524000509400c04042c050070603100243c90500900508005004542007204000740d03004850b6a1030304010300000701041c1d00c49004108184d031900 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 135466654 1250 135465404 135465431
    0xc0d080421020307050103140615190206040501050105030c060a080405070f0b07020901080d0c0f02060d0e0a03030b0303070b07110a0512070605150f06160203100902030606040e060c0d 81
    0x114580d401055a40101c1190046103020b0144802600c0b09080400410f081031420220100e0000d090038000c9169880740908418500c00361041100e1181c3d04010b11080c480c402500c41109070f07400c0341e0640c00c010000c996441d020403102c20140f000351119051040100c0100d8590300041c0c001d454601030b400000c64110b4044402d8406040d40801c00c0d80e03104118030501c0842d500c164882a00741d046a12080700e0b49a120000000941c1c01c9010011807020900004000e0b11468940e0120b051508500f42d41b064400b2804203009800303501c0400c1860560003e064480c0305000c001002d0114440010b51164081d800489400303071150b084842e1a4416904c1510f0050005443c40e9100c3c00440d040041003014001c065109880d204010301c2030600c0b43c0401e0071030a0603c0b1981c46280007140f20344120120b224841d4a10b60000e040700c03004070003011441e00401c80c400c41030303000c1d02441e0000f440c6800d080c040c13450f4030059000144591703620f40d0002d510680040d0b511010041e190740c0c00c0725840 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 135467904 1250 135466654 135466679
    0x9030b0106050712090803031503101a0a0803040311124810050715050a050f0a020304032c0d060203220309030b040614090d1107080c0d0804 62
    0x918490702d032180c0d80c051500300032501c800880c040c40108804454240036103000032090700e4105c995030503a4101c45503a400041d0520200d44159134400d494020010b2001c032311042d501c0c001e8201502c0442541e6100c001042d224400da0102811280000038100194182141d40134201c0382c00b00c1c2070701c0147c64ac3d01d9888699520541040400d406044007551200c00310100f002c100d1000620000d51342e00201002c1a6030204045c003540070f00802061075000e01008110007141142e00c400100280d2510300c0c280801040c00b40c403e000c1c0c1500801c00152060716903c2140e00440d0180c650b407901401e04101801c1110030076040481c80c0030003d10680c010344511409400c0300d0701c528805600d03460181280f1180c40c8140414400c0c40381010020300109411410000a4a0300029030600c565200d0505401500b10501804804090102008603600001c244150500f80c20340d2801c941c903c000c1e421039a100024002d044c0f00f0342017140305100503d00f581d0249003080c41908070a0800303a541d031048000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 135469154 1250 135467904 135467909
    0x31c06030210020c03060a0c14070804080f0106090f0b0609040b0616060905060601021f02030606040506040b0310230d0f0203010204060807020c030d090501030203071e03020909060901080a030f09030b01 89
    0x250740000e0403255245400d001b1a030348a00c3e00b450401000d091084024060380744076041d1a19480000703002010303c81100111800351890104841401e4003180300c19008000b0751040100851a0928521300410140600012903000400c0c4508001d90b910800008002c5c480c1000c0d03100c0b03810048455184445c10200c0015400399000181c2d40180741446810102e00911443c11908000540e8091040415514003010070407100103850782da0319408038200b440380da009035901990100f000140c82c0c0c13500b80110302c24103401c00c208140c50303561850440c511040083c42040c0b034401071b503c4603043c24444000011903014500d400300485a540200e403ca91058001e100060f410740200440701d0340400940c80207040c250000c116084103c6002081e54007140500e0381096000800300d42030620800c0726540c00c5245503805641800c4881d0701800a60180440030b014402e103000003001454540311580c1252060701c06028901401d5400b1140b94060401d99028000c03011404408603c8070600c081c007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 135470404 1250 135469154 135469157
    0x6010f09081e100209010522120f030e010201050709050d05070f031406010b120402010e2403011a04030803040303020a110d030606110c030d080705040b120a0605090405031c06030210 80
    0x340c024185804604141c02030342d201c0411401017007840c01c0c0d43d034090100c8070540b8104041c040849202e41150306080807541c4504200111050044c1c207000360b50b124402d131301e80320382c90f02c19050150000583c247c410403142034003c1a4104020041170400c00c501501e0300c0d01c40d500350754203143c4401a00c0503600703e075042a11440d54503400c0c1d0895074802c000c000e025040c1d4011190031f140a4602c80c01010700000c000078100000280e003240640c0b68200d080b41c403052002c0000f03441c00305101c5480352a40023446004052404d0f04028410070b0044402c64060300c1c0c1100c141071569035251001c0e8080d40c4001074070300c1040407009800c400c004042c0580f81c10000c840e500410402d141c2900140240030115204845800034040c0300819600001c0f9900d8029290074062016a1648c1055031180601d900140181c6400115541c031041d145605521603000c0c6075040001684030014844140000c9900030b000e540104510400541103550420b1079083c071030307070102c2d00c0b50300c0303901180420b50000810390 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 135471654 1250 135470404 135470443
    0x1e0a0504050910090606061b0b13030504120b09010b010509010c06050c040b1b011a060d0b041b0207080706020d02030a050f090a1d011a070f0204090b040812090c010806010f0908 78
    0x20082d44220b0f483d00500010400841c07091231030709c030180601c4d0064100b20001ca01c101c035040403d801442518014420300c2d21400300068541841c00c03070b0300700c120703000c1e6000d520307116860690390b00503016150812010380d1080c03510b40c196030321a40100000303010903801660500c000109583e018000b841c1210303401b080e40001200c1c078021142580e40d498200782010030f41401502e50381c2c035000140d4480700b00025010900c1c1d407040b0301280040040680c540e18103804070150541058000079003e00302c403e4401180c1100d95607400407603c0321008101000181c10801c10030400c02e102750058a0a088140c6800d031422603550006807c00f81d41d940b0041e8400d900c0c00b0014404d060341c0100600401d100001d00915554000d6841c07014451403200134404c08004606000f0b640301c035880382000950052803112581450f0070040015001000c1c0e0607407282c081000a51041404141000290b4041c0c5030ba070800c1d211880103640c00c10702d1102110401c012100f0000f40c4480c1040700c90700c890041090721 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 135472904 1250 135471654 135471659
    0x40e060403050d0b060403080a0f090f0f050906060906040e0408040e1017300c1b030d020705180415050a0e0d0509090c030603031201030b061e0a0504050910090606 72
    0x83c0161043d0004091251806203c2000400c8000b0100c60000352a40341c02d0141840010082d64030803802d070410040198031400110b100d441c202500c005583d400c40da1044150386500800002d44a01000950401402d010403c0b0102c0c000d17901903005881203000ca418281c030b45000309101c21b402c23100f20742443c0441c3c00400031400507000c845030b501c0c42c000103081414010072030702c2034400c8203500d280d84040c02100294007400400d002d07941c0f0250510309903400d8a80910700054204040c11000b0307c64000d120500702c0c41400040e07007408549003d40100285040c3c070540601c06640204181c54121408001606c1e0302d40d103120f854814003020000190005001024510380042103078410240102000182d4813903590a9038168004921103410380eaa03a24000407a09501030f5840540c030203030380d50002108000f2605c0c0740c144180030a4030400c07131a482c81038410001108038001c8582002c0d05000030f002508164000c1944124020215105441e0f0890424102c4680381804d07101d066450000303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 135474154 1250 135472904 135472927
    0x703140708042d080f09030d05070c030f0201030e03030406061802040f09020706090b01080304031b030b04170408070e060406080c10030e010605090106050c0f01020f07020d02040e06040305 83
    0x585412400320310345000c9618080c1e6070891540301070040d9614074050b80740c80341d10000c0055900c104103a401190191a0410300d0381d0441c10381c1104008038031174041e07850090b115a11030020ba90030307280c02c0f1204240d06442c680764641003140030030b41641015207a01d84a0b8a0f150100020741c0598461200058114500025540201c0d90b100950f90b20a004000411220302e046103d001600c200304070050b601c1140d880c040c00240702014000b020b03100100000030f81400084044c0086038020000001c007040d0401750000c1112842c00001d010705900c00101e80802c850303440c5640f20500540f810362405855041a520785074003541f08076140d03c40e80302007060300d0400d40558030007424440700410480d1094000500c1c000c0780500400c04241c0c1e52110b1080117002500040c000701000f409104a40d6112440280654418031290009201c3c01c0c150342c0c020281403080b14540709400c0d00c6281020155420040c0304240e030007050303038040c3d00c2c1c042c00c000c00d5805016181c090b078444d40b60780b684c80d01041407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 135475404 1250 135474154 135474191
    0x1912080a200904050a05061e03030904150e01150c1211060c1c0b0d02060d110a0507061a0907050c010207080d02030402090109090302030307030203091501090b0a120f02060c0a050102030703 83
    0x2a443c0c800d0030304040c0007564403130141c0c051841e00000395128001c4000800719140d40505c40c000e0f6801428411b00712280000e00c0304040585508142204ec142c1c0c880104d108000342002c243e20001d0030300b0040f0008203c4c0060000c80285035072500c00b40b00c08240780803500e42102580c100c118010001400e0a20b070301030343c907807160461024106100d001440f030009500c60102c507101a018280019002d0001c035506d521030f04100114811403510741e10b44040043c40c80c3c02100040351b9103490b0142c00d0003a8682d05000801c0d041008082401c0d030340d103561049400d030308094540c142c590b40902100f000209002c01508036108030720070050301d03032400d401049400101a0b000d0340409140c50f441a01113035012003143c1d40030a041c200507960741c946c03250f024038090300c44062107130b1082500300200c0e4862075a0000d9034424800c5411155441c2c17245080941042c015100901162410100d0b00046c00c0c910081d001e010380c040305840004109444103400c0ea0f10496440c00025514034000102d0242441d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 135476654 1250 135475404 135475411
    0x11d010c03090c05090c12070f0f020303090d03020c0708120d0b060307141602031603120e01020304050f06040806040b0f0a050402010203220b040906081912080a20090405 75
    0x28042c04595401d44404800c1c08050107010f014048160000d0010340c1000d044903054160b40410000629016070001c1c28803a0200300040017400b5060411941071000094900440004c0702500d065200300c2410360080d4009014400f0a004040d0006626441403042180451300040840e560340c010300c41600494052a000e035114407000d1041c401c00700d42c840100384141003a01c04c0b00ea0b0b5500c008a108a44001c47c0c80000d42c5440b41c2c4c81e00c402c40c85040c00305481164800c0c03103490542407003141c0035602c507040182500d00680c414001000310749000800d902c0b5080000c0c009074038043d101c0603003034201101100c05031b540c2401e4809100d4404240c04400303a0200b1031500800c5241026030000f51240729151121500d030364807010300c42c001b03e00d030004030004064040c0c070542d0316623031010300c0c2015107079620411840e8043d40b903c840c18450309122032200e042c1e01008084650021040603101c10002403d10f500d01c0d80e417050b2902042440d030a0201403400801109a00c3c1e03000d18080205544006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 135477904 1250 135476654 135476657
    0x906050a1203080a0504030e04021c050c09010219141515030c060d09150203090d032a050703230702040e070e060d02010e03030313020a060504030210050c010b03011d010c 75
    0x10070702001c0380e80310040d241c0000320a0000715854803039040c12170300b11440c05d001c298010310000314409030220b0319800c0d204000d00b119003070240d55218528080710b4000c4410440c050380044000900c4074080148101d84584030702419024003034881d40300c03443c1c40181a141401000d6820a01c504140c4c0210103104e105001c400804104c03103080040703035160240100404a0710f85841c1a8407c100d641442a010303152140c80854417442c2071041d940ea1040c03406440c0d00030914042d64a8100380c640a01d158906450f0001d0541c811300100c0704440907800f0740f4081d001c20040c01a507201c06045190b04110b600c42c071580040c1c840300d55004100442d03003d11207001003070313001e607204009403034503200c07a5075010300111200004405240016206904848402036040c00300100f0000100c91701000001ca241c000d64010803603035194041078540c1e00c198000654003000c03104d4285400d0717100740000d0061101010001c1581c01c81400400d00755041c102c0c0b911510821080490740d40c100034800c183c00071004d07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 135479154 1250 135477904 135477929
    0xa050c0a140c03040f0e2535070e030105040b0402010e011e020c04050c0315060a0530090708031c0902090717090d050d0e01150b070209060f030c09060f06040906050a 73
    0x42d040180f000c1615070381150a002103000c185030300e02a00c0007030301500c44840c036041d1004190b08c00d41c40e8041604941c4207011aa4000300200e4a050510401b880f850380241498200d4030f560b001507030010b0342c01000504000814030141071080c00307034541012020a41c0c0050090b642a2410001520401401551210018810410100c000c1c200c1003a04800035211140c1c0c0380c8070142d0444c0c15105160b0800c0c0a0280106030102d03041c0c45200b40c018480075111882e0b80742c4c4510343e100d9159145442080c0c3d10b83e02c00e01502422200040550342c404c8481100040c409a0b980d0203c0d40c44182101d540e4041030603041000e0380c0d44201000349500c01c2d038000140803210324200000d840b0f80200505015110b80d1188000280c04003588100d4206150182c0d00c401191b450782d10381d0395584022801c80c0a20014030101c2c07202e013800c030341c13a250540b401070207081c0000f4150140106481c0043c6050350016045400728503585901c0700400181040c0d800100c1d5550808c424404150803a40c801d0014040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 135480404 1250 135479154 135479191
    0xd06051207031709010c020d08130f031202060106020a111f02030304020f0927012d0b04060e010b16140c0f0907020a031b0602160303050a050c0a140c03040f0e 70
    0x900c2002886d440d0350498051190081c80e041c87d072000e000742980c0000c4200c99405c0410342c04607a40032801101d100d030400311103081e14010126198070303081c03048402590060b040100020300607400500c0b101c030301608400b0307003410110800c081c4001c0e8884120168100000340001c2d42810807100c0c160010603541a07005080100303d0400b52564400540f025102840100c046214290400b0310590a6004160103a0641508900c04400d12042d504d04080c0f5107524240503041600440c000c482e40700b201102261700e00110500b0740e41c004440f14900348525114600007a5101c00d40601c034150500080440702c8054090000c1c00380c01c0701615108026000802840303a600007054600c0b1a4107240c00c05948140031090f401403460302800804e01400464400b860644407074905c50039900a175400d104035102c08143c0400c071642661100c060750400c21070300070018010180e0103074800c10750b0601440d000620468505503002500b10603045c0078807000c10000700074901180e6402ca85a481400000503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 135481654 1250 135480404 135480407
    0x402100309030309050d0207080d110316020102030705060705130f14010c021503130c0b0c070506090f0409060204050f100207061805030102070302060a0c030e0c04020d0605120703170901 82
    0x811440020416888092080406210760000181e041d4032a003105c040c1281110060346680c0c003802120001c0c81001035251250384986d0080140d04070050145140c0035085089102480002c3c0e02039042d484100715400c0010b204001d882d108a11a0703480070b40b00d5a15000e40c3d80c4583c400d40c0aa11112500e840c2407000401510300400702150900b404007810340b5510200b0b076203036901d56004080b040e0200c100040d00c9082d00040b110b40d4480d07940001c4031038513031500041902a1040a44103940300000c240710781d0134500005c1929020040c00c00c40d0780f104590016082e542c0006c412034006030041410081030424100701042403a04a410422081e81101c1c025560045841003804100015404144480000c1e91120151002400a568442a5041c061f5948400b902c1d102080b9180c00703a0224521b21903c1152600408180501076110756101004007039000481c180f0540780c1e80b51000912565541a55000c0c15074140c0034140709841c40c02e0928204589609041c4da400702002f00380c03d90fa = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 135482904 1250 135481654 135481669
    0x709050d020604050603040c080a0305091008510307080a08180a03060e010209030c03160e0c090a080f16030c0e09010f0507020114060d080306010f050c010c0507020909060402 77
    0x2104c0540e10703a516036540307051150201651f0f170301c60f0342a401110901070904d5805402050f04007401c0e42d040b43c55407414482210755080c1207912014008030320200102100501c880302410846020f6961100c02903100c2c00214400c22210800044c0c0d03501d00c1422443c01c00b80000b0004042d284060715281e0350079120b036405480303000c1d88000554016802d1a070240e9030b651b02c580241d900500100404450202518000d43c00601124482d20400c25411028070b00040da0443c148a0030515406076840c10301c0900c203802d0080c200714000002407048918a498118842c40103010b0312006150111824031080d0801444070810f901101000c002400858082d4440070f04640c20301040d0b010700c1d81c078000141d0041001e6100d504c00316007030005003c1825415088040f8402e480b010f842419140c0d00d081040740c1c030f10098020a040c40500c00285690b0095200b649100610b09021349445826007100382100c3c11888260081240881e6110a41c1010789115a01802c000700174030490801b6000503060 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 135484154 1250 135482904 135482909
    0x10941030306011809090b15100f0c03023a03050105060715290301060608060901030314040807032102010b03070e0c0403050303090d0806030a0b010b0a030e030a080709050d020604 79
    0x500490700f00303040e208855130329064020b08007a00c007000440310500c1c1016243c501525001c0d98042d00109000c40b61400001014400c02c494440219000141406a50131424820168254011145078a008903102003e1050000368095043c2c5030889070010030300c1540510b07060004242c5088010f00460300c80300e0440d0391241c0c10001441c005c401550310b080150440c0010302e8078404031003040e45900340e010410f10007503000c00c81c002e225050302e4a40441e0f03d40000c0320000c0d4000710311401040400d002d03c070b074103058204c47c0542a1606840d910340600c1c1810a500c1242e91203c0d0000402c00070340c9100088064455030f10007071090f4260740f40001c0e0f07070b083e10340500c0110082507004110a807191404541c011035000060343d440f854424002030303c03141c00200718004a00d00f00300189040c82d000ca852501e10703600c12000d404503403c0c084105000d40154078048280b43c5d50f50100a20804100701900448a4650b0751382030314902108000d000c031040e544103a005103c942040320050340d81801341c500b0f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 135485404 1250 135484154 135484157
    0x1080718110c010c0f1209080d0911100e040605010906051b071d1902070203031903110705060612011a04020f0d05010e040303060518011701094103030601 68
    0x80718030846140300c0507807140c808601400c0d842c040162800b15003181090003c41034546414203a0206030007660150790f20450001c081580c200442881d0008590085864034040c1c0410340501c01c2c2c001c08036400b94201d5130b0715000301d04542c214141d2880d2030700505014000a117801c994142c03405002424500580c2c9081103031100b010220214034204000765801040b62010701440d080000c90303580048075041c0c4000320401d0051040f101c21001c01e000711101c881e40034004503c1d208040b075500303960310b22113400c1e00704154039801e00d0300a050034a005410a14000e1015105501f001c0040040d0411641504141c1d0f9041040c100300780345803140d000ea1510b1041c2e0b03025039910389801c03141c00d243c42418007442c5c50a01d010300204401d46024500e038440d6100381c8007002066180ca04022806800741501404003284070014041d5130381c00128444d4a280ba0740000c901c0c82001d0b070350441500403445e107013450301c0402c1e85846180f40900da600085445036604040100740781b140b0f000d441e0b1200826050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 135486654 1250 135485404 135485411
    0xf01020f030a021e190818031902010b13021207020a0c0501030b1513051e060f071b14010215150d020d050607090510020102030f040314040506041202010801080718 72
    0x404a806140403001c04e201004513a8521071000d1102c440c1010458400004503107000160240c1c0040e0710711810301072030000850030140890a1190011804241c8408554a9041d801030035240c0c8a144d028024204101584a10903000b805110640040400301107621000e1a04042928001c900342a150207180108003106e05002144101221030021340109500040d299444a161000036003901d0040b0350fa0b800c00107811240c000007500300040150700ca0004c02c940f1201d00765490042c40d200d07106a030500280e0300f101d07103444244030595002c0003550355800181e084035030341800808501485050803082c1c41c2440b412100c1e000380e81821a502a6041c406c110085d0340e601d81032034454643c01000c403125480c4c208001800c12001d80b02d0309000d280581c4101200c24011300070790380b007100802003155565032161021140036902c9031010088440c2040045000e88030640140054a4807107007404009680e44001000b11105910448040c0c004900503c51100c028450a00e44100e040010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 135487904 1250 135486654 135486667
    0x30e10090e040b040507290a030b0d1a0105060c1c030222060909060e07030b011b0503070c090501050310020c01060e04051e0f03040b07080903150103050f01020f030a02 74
    0x2511109826082040e50512103000c000c200722038543c04521883c0b190095907111981c0d4402c400e28041d5440005d100c205402c07034003142100c0550f0160480000910300402c00c030350f242d070204c0c6840109410680e01d05048a90030000400410303401801050141d400303d2400c44c3e902741d819121003494810b4140106914126444644a81c0586081403042061440c400e60302c40c058612440c6144242e8000c41d81035840014560811b00c2000129112840254010303a100d10341100103100180b10141032081240c2ca0f210350358500c0c60701d0601c4e603108034029079851542d0b00b802e1186040e240d000a05983c18000140007030388010a41404619a4040158881100451035805019150000707840c07603c940c0304010078018006000750069014408840300158076004050316207041000d590115071040108025440018000b840703c180140c0143d4200240e0750002820b10711040c0400100d440c1400042c0240300c820720160352036181c2c00001b18905240389014490a0100070105a080c0d6804901c0703 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 135489154 1250 135487904 135487907
    0x603030403021206040c05060a0507020108100807090e0708070f0608150414041101030b013608031e07020f09060d050129010908370501060311040207030e10 69
    0x58034059580100388102e0300440c0ca11141d40d5660031101992100c906400000c2d460424004990701d5011995a6614101c1c1c5038005640f014006408241c4c40111984006110241404050041d20000d000401c5020043c3d421034030304400d9800c904070540120008116011074840c1c04003c80b0043e042c403400b01d07a52280183c80b43c44800745115041810281009030340308440035001e2080d442010104214403082c00110101d4154552160215900b803a08895611040040c2d50100400e2450320000f02c1c0c00d40d1840220703003929030190016900200d047c50444555201c42c11210041290741c40c2000b000da00052500c2d43c4a881c4e05014116440214090f034031a4030181c00d10079003010090105100300001703100038800204580002510b20189045c60f0f61240c1c1c8810100d8214070b00900304480040d40b140d011b50040ba020310006054000c801210405da103600b101503e0281c000040c01500d03500304901d1109001e0381c02c511072841002080e0009401c129600b00c684070035201c0348141000103c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 135490404 1250 135489154 135489157
    0xd1d0607140c15040209130b040201030b0d1506030c060507030e0423130311070305100b061204030503010e15010503070c05030903070f08010b01050304050a03030c18060507121d0108060303 83
    0x149a00b035000e03010403061554101004070303000da482900c224403d59161418845141d1110710010900051700d00414013540c0700b03400c00003540d1402850801c0100c5141c0e5140b1248023002e80e910350458076004208244180001c80000038080d5040c100d16140c1c0651380109204105035101d88195959003e075041924106038000c05440301e00200400e03420b060100c0e0445040c100300440c0003851942400760445004108007084070392000080c0300c1c9171040c480c520050a014884250040805d1060807009000c042d040d41c002c6029840e0240e503941000c0004d401d01c1c100502400140761910f0b455865030340d008040700e41c1b2540d40d190440c6138200351300d0007a055204140c1ca281d81445510b070080780c51141045c080044800d010002c0122804002c01074403580011140641560009035501c00420300039008030a04246500c0c01200c0402207034040c0520303a500c2d4101600142c00400e030401004818205004030740c456007817003000d01c0c038962200d03a0403001d2164800e04000100303010840382d850410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 135491654 1250 135490404 135490417
    0x150112050c071713050301060510050f0906190f08070828020309011d01060609060c06020408010513061404020603011a09100e01080f010b04050907120e030d1d060714 73
    0x10181c95000d10f000c80303c81c0030750800007404500c3c1481040000b0a03141c14451002214409800f0300e400170700001d01a14503130044036801c01c198804001d884010f03078420000b40090005114000e4121070481e10051001400e0840350043c00114028401d40c01e4100d800d459025080240301c1840b81c5100d10103c95002040c061203014034000b0060040e980b0040d0098001c01c1100100d501c1010904400c1da400d0391024030031400410232b007100070310495205054454585025260262429584020311821a9002c43e0102c5142c1e0b0700b11a480104281c50168541d030800c9142601028100b0750000b842e54441031244d11605186043c0e010085071162042e1103810b040101844051003142102038901508011260300090050700050513030324060207854180c0d4a0300490790301301401c0400340902d2500281c040e80902001c2d1058102c01039240c086c2c00c00e298500d034061601e410302d04030302e8415580c0c0c8140804000000d0400034040540c00620b440d80040f05140c083c000d8034038504a0b1900d846002d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 135492904 1250 135491654 135491663
    0x9060c010603030e0f06040b0a26070210180c09050907030b042312030c07210309020a0603060e0a0f09050d050c060109020906071407120f0605150112050c07 69
    0x1c20000107240e00076a2a0044030700c1611017070000201d1340c0800c603240c840ca01489100711400d20440301005d216801103004041c1642240c2d000001ea40da10001c00b03070b8100c0e41980140e03c0742c080d210080105000d1a03510a0103e02c01100107240e903541d8040140b8980112102d05d55205c002800c1c00c40c04020b504003c0d0b4224403003450a0508e82001001b08460b0003100041c01001034142c08590000a03c0007647c03807401c0249425074651703080740d880c01da00000054503d034003520842e041c203103190520840716410984000410849c54418400c03424119400402810700c0c2110402a00f070321340c8206580641844800a81c082c0740d40206c05c002c03c03940c5e402500c1841030200d2031402a8001005254403a10981100c500381e90380e511110a078840c6070103070342d0000010301140000032440b294080c01d04440b102070b035951700d8071409203141e004112030003510280b801d201540140580781c880c1d0341d000350800c3c410311014585880060484a1400614210256554000f4140c005204182c640032a4172 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 135494154 1250 135492904 135492911
    0x40903050705060606030129070c060e010e01020c0f09090f010603080a0306080105060a05040e0c030d05040609050f0a030b07030f15030302010e0616030e1612031403010305030f09060c01 82
    0x50900602540210700c04460300c0c0f08000c0031a0491500d00700b0f0b64102e91042000c800580c1140a250300c01e02c02c4004c0c1e0300080c48040c041a4001851002c81001400182c2e0351101902c0100c000146000038000fa101d0554000320244d10302601c40a40c1c544080d0401ea514281c5512070703242e040c0c42d01e80719100c410100e51900a000c801c102c2c0010041000e202c840c5c0c2d05000fa551509900c500300c50065611942c41003002e0410012820300340c1080072207216400c10340b90000c1c201004641441c003901c402c0b00000300001414810300f40c00058040140109644440524580704040742d0356600901000d4074249241c00002d50b007520070340018401442062061214401201e6401184021400128099401e1610540500c1030008606102e45119003660152070200003041d00140b909080010060140702030792040202c5503c0d1300301c020324400f00c50f41c80300310507818000c20b01070800460b100500b81c10001080070401c00001d4038079807000b164901c0c1d070341c06020700011064804c5d07048a071186d50030b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 135495404 1250 135494154 135494171
    0xd051b0703080306090f0c03040b070e280e0903040b0c070b0a0e090603031206190302030a05070f15440a0b040c120504050c090c0904110918040204020904 68
    0x6502c0245004070000c1d1450042d81d1101c2c02c04c6600c02104482059406100740001400314038141c0030715401c0843e03401e10448034580303174010603070f140c4580300b070440d100400700391400748000d0b410411401001040101c54203418614540b542302d00c034510844c00029070102c0c0600d9112018010740c0020000c600c042551440c001d04094140516892114829003c2900091650501008075020a05050201c480d16584c0108000711003581c4407041c0e241186048000c07006841c200005a03225006800038620540350401d11000f0204136081110900b201aa06a0b031203500489901951400c01d07010b0007152046079144840c410717402c660700861030180750190680481c29440700d0301844068a0510140390210b0030321060b50040c0f580c46001507040000c3c42c0c4546c013998003082d0418489d4095510000c09100094106802902d04540b03030117000034504606d00e4248603250504040b03000c01400c4c007005000007620b4510003080721034250b1504000804640d245da040361040e15000f4001c000801 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 135496654 1250 135495404 135495413
    0x80d0201090512040815101205010212060d0302030714010f060b07020109270518120a0e01090308040b0c10060605040e0f0108060c160218160309050d051b0703 70
    0x403200020341d941e005602c26900450660b000b00d40a170b500e02c1d40280307801c01c0154038129000800074000e0f2200c1c1d02808000c61000c008004203020f0310700403400942c803401164803040c00c11070091b140c24405c0b4003104036000029004010380d4107440c2c01c095010144541f00310480d01620004564500c2c1c14604880460324024074800381c81000c5c003e0f80c0d0b000c2410785807a903149581800c0c60a820300c8502c5003880640c0c00340d591f00210390064040070b0209041d04040755a5182913451000301c1d4550384041984502036a2114540a104200740380942c2c20350b1550b110403019115a014001000000040c041003481d070420150b803941403e500204100d40c0d885000501c1504507019102c4115450740c00709020b9940900454180c455800c05007410362120b50303042c804c1d5400300c1d585044d120386114148025948091403400c0881e1100d044801a1804401d0008208003000801c0141880c0001141c0416400241101014042d08000e685c941e0640c8a8001000d80b12040b100329100e03c1e0008001c10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 135497904 1250 135496654 135496661
    0x506040c0305061e1504090609032c0922020d0507080d0c080405090402131401180c0f0806130218030d0203041505030403030b0d1419020a031209080d0201 68
    0x201d018906440c000d4076803284c0300c3c1020312208080b00422030b01c0004200390402d400b004156903403004100080f041896952281034940340790045e80400c00c10a940a99031148008001b88031510140c81c4e220718110100080c0f004001070f00810223240c403405460506401d22054850464000740055051f1000d8600543e0f6814640071780001400703807425801040f0f00514841056030b42c8a0342c2181000c0c02c00041c804801c90050086ea031042d2500c4001140c0c0042e44035424038001e100c1ea103101d041d818602298610480358010804182c5003900380364101d940040c001d146803000c1d24080d542503c410b4001109030840804418600344002583d180b101c41c660911211148194107480c00b00922440070fa03164021840b4055290103880d03414031040d4800e0009562051080c2000100d0485d8180813400320f41c490719088558a214a40b21400c500c010001100f428521072100880e007c8940c0c0403409003851782c03200804441c80212004141344c0100c5021014103c500110ba90302d9501d904001d01a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 135499154 1250 135497904 135497909
    0xc06090c01030f0c090b0c01060b270105070f020904020103111818040201090b030c041d0603010b120d030f0906050f1006090f14040b10030204030c050906010903031202070506040c 79
    0x401e24210301030f140309401c2d0096035a0b03001c1c25207502c12070500c0c00d584130032140e002108000c02035684810110f03e951100e001360000f0003030b41e40e0000d815030001c40c80e081d803060100075040c18000148400c01c0080c400c030700026440e550507141500c0350b07281d502c011390140102190080c06204080384d2001c580305a4040c2101640d011a180d456401000d40f480d90001ca003a07a020780050100303035042c840d4002e103030011508421001902881c0c01d40d81d650010541c5065107050710415114130502405140c24002d04000c54000c5074200d5055a50401640c1d5484040000c5018941c4588000030b44607401d50011f000b140e04001c050100345007031400101424812140c2c02444159603901060b2184a804290182d03030245070036908103400d000461460351100844181c1c80741c0c4542180301035484416150145102e181c50241c0ca0740d04600d081640359495801c40c600800500d01003017003581c0d0000e0048122901401c20401000383c14014401030310890600ae45244a49400e100c100103e07c41745908 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 135500404 1250 135499154 135499157
    0x50705010b092d040b24130c0f08070207090c0905090c030910050702031e13060509030c0d0503042601020c03120a090308010531020403020a12030504030807080c06090c01 75
    0x1104540043c2c090645042c2c401600601040000905c2000000043d8200d5024440c4c0620417503981400035201928034102c0c2034440303840b51265801242c11a001c21401003942c14001341c641b8062000039a0342c46d261083c10302d000d4030303642041d04140c000c42c0e10b6405018050802c80080c640001d21420903032007920103240750b110743c2c0c84400d50303030101d03204030380c01211964050340ca4180b0f032614074240003c0104050180320020440c00040d0080d40f11141c00070a41a220b0300e031942c040300c007018202a400c407105806111000d080c000014001720484d010b40301e00c4111a042c00c0d164001c40b800340701c041c40580d022984000b45c49484040000090a900315002082000743d0343d44d4000802a282c801400502040e8400700502103450031002c408030616040d07455102c607001c00c1441c6142c400c901842c825a00781d0000d0240107609280c2d40c91000303046082c0b1900c49101c1c0f01e039001800ca00c918031010b0604071011944c4000c00295008540b41040f6500840d1140d00b4201103036070f22105c01c03008560 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 135501654 1250 135500404 135500461
    0x130f03030e100c0f0c080a0615050d02060322080c030706050106170703240609080f032802070e0f0618090a03030b030115030302101104050d0201050705010b09 70
    0x41d6280a0040034203808955884030042507480c0d13520366481c060700c0707011a840c1000c1000441d82c180308002da50400e80c01440c001c160740c030840d80d0010741c11185402c001e00610580c000c10700542c940b58210390304030100040c001c5404260460003c0301c40c040303076802444c4500c0003481040d8203070000302074145240195410045a42d940784203440103a0980f50340d440c41d691160000710018000c1e440400310700030300584280c5040281d402082180300c075411a80105d10a0751041c40f00c1740003001000c0a2849000040d4604101ea00c01c1510040511180c02040b8540e001d09503001c9100f400f5880007070604c200f4440a03410f04502c00100008110f03807407030080c2c04403282070742c113900c205040d140140313080000b82c01c40c00400c1d14110003800c05220351503007564886040da4001d000318001c0d140114041e60107040310340b9040b90708805440c04046440c01e455000c1c8008d1115136105c2c0c0c0e0150086509007041a6200e810780780c918050700603100d00a9102000c141005181c6c000091f10080003201d0141c2e0702e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 135502904 1250 135501654 135501677
    0x409060605130b0703030603020909010f0608030306061603020c0604090c02010c0930120e12030306011b030c0b010608070215010803070605041a0108030a0e04050921130f0303 77
    0x200c1e01e60150640c48072104140c00002c03c0903505a0000303111032400b0f0701d0f011648a07202d40218200b850141c4090803e45c1d580d0942c0b8290032998803548001c3c01031100a1031079400c1440014589000d43c0700b10444280081e14280c2c2014000c00040c40004005003065031a5640e941d0701400501480f00d2601c0954201014400c40d0352081e01444141d40c80040180c0c1025081c4201b02d003044140815032030250b440c100c038140447c00011070040b00111542c4d0710b018a100340301c284030210300351003000c040360307802801440100da0308401d101c1c00200d4501521004d181040c2411a100c80e02c104001d0060300c503110000c1a0654000f07081c42c4240d01d190201c66030400300340c0c0e10030a050400d114080d0160018881c050001c0c80e0342d005207400c58041c02d010023000c0b85030002181140340030780c0318201a030301c0050040121900b2005484540604a43c100030701d240460640b61959030f520814698104c44004003000b40c00607001b9243c0107402501c25501460700e81d40c60880300d480600064000c11081c10302c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 135504154 1250 135502904 135502907
    0x2150a052217061e090c0301090c090b0604030807020607060207080c070e091513051c02010605090a0203090d1101020d15050a090e0a1b0b0d05060901050a060c110a0b0a0504090606 79
    0x940a9070290b581c2051040c080e13819901282c41c007615400d0180502210000166802d0040e2045c4a00641c5108841e03850800120701702d0b0b8102040320300911081c031080001c9001030b02503410300c0d601568902d580e007035545800b45c000d12034003100500001c40400e12140c10b0000003110401d407002001d09005030b4075400300e42541c60b407a401044000808900005e8040c2d0790032450f0704d404500c02c8080740c944080103170b51101c0c920340d00000070300181e654a42c20086860487c002e80d421001715142149142410b8040716100c0c0d01e101c2c2c001080c0a400d801080c0381002c00d504840c0300042480c01084040021044200d010480e44102445011025808038030412944a20240c1c0c00c119001031110703018035030b0307102c14460409c2c60035035810103188400580401c0c03210040000e0010982c00182e1032401c0d1040055244040e045240251824032091000c650009500c500390b0b03070403d840d00c0ba240d0140c2d001034010319940d000a8011040400d40030f00040d003007006041a50071513001070000340c1d1034860 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 135505404 1250 135504154 135504163
    0x18090308180703030c05070b030903220e06010e01090b0a0e01030f140610020f010c05041502070b0414031e0114090f0706030c020102090405160311030402150a052217 73
    0x403007511580203920708000190003414462215407050041c0c0d1065952013a40c81001c0e00102c0d50400319403c0050201601c10440010195034201c04c05080c4003035040074240680240e004064074180100c21a03a0140eaa000350b4400e0010000402c209035103000c0d080d0300030103200c0c40d140d031036020a040c580403264030907640c06900148644101e220203241d0341c20041148480c1000144030950003940c4040300c0301c007001e004420f5a0011a1a00d5584a02d40354a464490901c8402c410464100039018450b43e004902182c007200e414100b010303801c000c1d510000c0d040c81020250801440c008a5485100c0801900580907442c03040f82e1202490340c50315001030b1941c14100403030149401240050040a0003584192609141440018245059000420110340007611502c0c05807070041e1502d42c68236414019815800090401c1358294203003980801c80c015110044001c100401007140301d0b16600c180190345140c2c0c803201070784440034100c04003d1401d0f00980950000c1c2d21500102e0502c0000005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 135506654 1250 135505404 135505441
    0x903031512021f0c06020c1b0402071101261e0907030b01051c0b0f0615040806040206180306010902041509050105030a0f150305031b1219030618090308 67
    0x1000c0488640880d42002c02c0c43d0751055038401032281c40314075940860802e2000e0034003c10715100a040008580004400c1c2d80c6141050910903401004a00c0000f8103c2c0c410301c8840c5820b090017001109904469104042a00380c040ca92005010811800c2100d054030300100c422801c040401030340b1a05070b1262204447d000c041d01742c44002e0300400c250b00b0000c1074486000d490a820610380012036648000001d810f880280e00118101c05005640c41c1c0382251303401c03d1200c04100340c40c103480d2500c181d031180401400030f44510004101485920503007240e56108103030040644260b0340e190a40794000350028007444050444107104503004134002d00250040d190140c40c0d85096a03507001986000c0c00c89200c0740c2410030344a9442d814244000c9003a400a9440349000d541c840241c0341200003039100e610b4030220240e1000c0a00c15000c80020100c824014020f5569004400d00b40d0090340501640d034007400c030501000d400b90012410030741c021301c4c03541d1290b9100a81d5480f102910294407200c0c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 135507904 1250 135506654 135506659
    0x7060b040507050a09061809020315011e0215061512090c030c01080a092409060e060f01060818060109060503010e010603020105180307090c09051c0b0c09010c0501090303151202 78
    0x80c509003d03c41c000d05940301c7d042500b42d110003120707440d41c80d881c0c2a03820540e0305080f10700d400841d0710519030f0081001c001244c41e002e00300c1c03000d056801000303544031120036000d50000c441c100400c5a90701c50710b20320b000741451032118035600e034056107071664140700440b84d2107668002c41c403804040b4030f0003080b11a20100d050303440f0340c41a2039910304071004050500040b6a6201c04450803c0f600b0007903401912160803258000914031030f2030914a042d00c0b11403a604005401000c100811040404480c0e815100c141c6010f101d559a186a82c605444662103240700502c80c101c00000c1c1d0f0612a0800b409844060b4001c1c4503450200711828203841c0c45010080c0403a2041c07083c0c01e4042442010945028030003801c8a10240d901d002000407503442845110000703200d0381d01800b081c1040032805501d00c2c1c5140e42154985290780b40d20100410151551107100743c00180802542c0c40b85070110300403a0400000c1081041c1c0b850042d0060820b0703244582d901020100000b4085882c1208181c40b5801 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 135509154 1250 135507904 135507917
    0x318060f0206360115031b080105010f1208070c0e010f06021b0f010504051c0b0709030503030c070201140c100b0f010c060209010207030c140307093b0307060b040507050a 75
    0x11129200e20300b4031a04038a034040d41da902c00c0c0f00e80d5045c00300f00d400d00543c010f014458021140342540c8440b003402d5046907165a041000410075254200030040803a0403130201c0360f8050001d407511507058800e00e0700150502e00440c02c0420326410b40844c1c14100c64459200300b80c05995610144e845050903201c0039921600909080c1050800c0d0300051841c400c149803081c079141c2c4620001d000c46a240c00c51011500c02021140c2c10084a0a21690440030509000909515583d01c4039600c1c800100002c0c0007003000314214007164001c5101c08103103c1600700a58441c0016030f1030640d0340340c21800c942d41c80c5040026020780c50a1904010f043c2100607550b2100803461601c40b2000b96101c01d0005045104490000010480900103000a00302400c04806120f00309810503280070213a030001181b591405c1c0106400307105c05090718283c81c5106411000c60124200729000c441403d0351f8104140c00001202020044150f005010341c0d02c040701c041086444210b021545400b80307458500c00b00b0305 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 135510404 1250 135509154 135509221
    0x10206070f0e120f1207140106030213090c180509100c020312041b180e060601080f04020f060a0e180403020a17041203050702012c010c0318060f0206 66
    0x100300c1043c144204038401210440c82d20340b404079250200b5a00b503200084070110706001000340040d00060032048520007400458116000240204551022174030b034540c0c0c134100602004400c41c3e00f40004c00f0315664401940c9002000c2c034010300021503504c50725000e40005442218803038440e08000c5030090707000b1404c240010703440710b244a0002d80203864045a82c121a0080c11070f812010010f0080090b02c0312400c4952803402065680c100800b401540202c0700308038103640d10541d9036500805c1d8100c2507280c0e807203e0010607604580744640716084200003412824482c2c02042c0084038003030076100070000000c40c042031620b00105483c002e0040c0c00040748080030481144202c2100d0080d28000c0c2d1400355500c0715030380055021007003100031170004a9400203540e0405178a40400c9030030b07548594009014070a0007043c640c0450018140311030104000103051180103c407000000d6044030001041d01c0d40790161003551101e42c52001480b41800280311007a2542d80340c045425541c500304078062 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 135511654 1250 135510404 135510409
    0x904080301090906022703060109020414010e040209040603030504051503011802070212030a030c1202031302100207090207060905010c0f0207090506010c050604060f0c0504080304031e0818010206070f0e 89
    0x4043c44080e00c80c95024421030000c200380503000c040583d545030918650b10404401c2c90305114050f4040c001c010b1050004200840e0525011304140c4024640141441205c2d0000350090003914441d035005450700001200301a0084000c2041d0360040303409001c1041e880c1c44c5032000e803009000c0c0524520403481407100d520819005000210b200901c0340450041c02c90b00c651031034100c800f02d000080d0f00d90f4000c58076660002024464081c10302002d40c0303146425413248a01c0302d4070200090090066150402003075100307200c07002c05080a080199520000b90a104011f011030a20956442d4a40302a108260740210b83c1c44d0f10030750039a0090f01285240c940da03000100303001003046050020000d002000110240065840b4510070000081c2c00c2c01d105005d141203030729242c07103042030003801c100078040100e0000554048940c0040409504001000410050055444010700041b000f180740034000318071980d522245007080e0f007207400554900e04101c81094210a200010520985007030741c660 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 135512904 1250 135511654 135511661
    0xb0103060515040b1e070f020a051c0201200a050a0209100e040f0c0e16030b0f03100b0a090912120b18040201030b10020106180c0203040e130f110906090408030109 72
    0xc10a005648000d180d024000e2a11580300e00c05c21900d02c0c100560860851624102200180c0710554038410038200c0401c50f0341c5001c80d1154081d042c00548059000e40b00b140c21344ed4180580d610080d20190403061800543e11070000c081240700f5410b460004030701c0740302c008290003103c2c04a0b2074030003162030359103800e92000005401614022000d0202040c0084011445030159590a0362039441c00c08400b401411600d0a02c031403846008180721030040c40d6800076205000d80d000d40d00000d04450781c0310016160015651015250303a04121030300090244070245a88609110340729403044801c0c00c4803050440c0d00b50328a0b6a4010441c12490220452070b2032200d92180c410b040c000745900004000410315400c3c0880040182c0d160b10302031201030a51800142010000c3c5014804810103000113504c0c3c2c005e5001d01c070303080220000000c054a640d08400c0901c6904101c80c0d203d582864203040f1025094030b4841401610b50300e012603080d0a00c003001c2d51090360041a59401c69003005030f088003a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 135514154 1250 135512904 135512917
    0x204180203060f0631050c07140c03030d021b0708031b0601080a03030515090108010203010906090b0321040e010b04060f051318060801050a02120906012702040b0d0b0103060515040b 80
    0x3c4410444c004c5c02c40c0303c00e201d210700a0390341c060303002c0c0c81d25400d107048a085141250045600d41141000c900c2d603450000580311008076000c405a1100b0310340150524254081c00140c090f4458840001038109001c0000d122500d222841030a280c60100099651340c4820700c2151442d51104204502081c4a60b01c02500000809501090300c500d90b00001d40001e02a0040d07550307a54000010814000d0b1840f500f80148103052040c801500504000398039102600c10990a07c4841c403501400c50803148201c0e00034102a595405855846070703e03034605e5030010f010703000100700ca4850458100c0c4c0140d00741e4199224455010701c29134180380c1c0c4991f08181007030780351210580360403002c0782150081c026940300f030304001801070325a207004002c0081c41601030150505604600010f000c40201540449200c03100100813000004e14000400000e00c942c0d407190440c20804a828050119250001600c2070800d80c1c007803045645031070800c01a000c0c58080030500c62020041013142c0c400f40005082d2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 135515404 1250 135514154 135514219
    0x61015031103190506030a030912030921050c0d081c15080a050d0509030d0c03171303090b0a050409050603190503030403090b04030804060c0f0204180203060f06 71
    0x40145510030000c8854209945060083c0c0000001c85090311040c41840c1c0e004204030002d0040100d6070700c02800085450044101008401085200341405408241d0061195155221321400c034003482c5c44003c08910310482e80c600560307406882c00c0c41c0c22060364003000c0d04030032124640340d003411010711601e15100121244030744900c0d80c10400001010303c00000c080c84006820b452030b6070303d071503810400b090f081c003414000180124500d94030b000a0618035010141000307005084503080a581d440001d0580008080780001001424041a400e00311054800e4490000894840500e500240244d086203030000d0b005010800808a0030303000740360420406800da80d440c5950240c441000d8900035401d80e00d030351002003031208042d8451f104000602114011605250450703881c54418403892064030300b04002101807400340300e594a424540c103a4001c0c803c0040c1460041e0118254100c520181e10030b008076000142d01c605c2e00c511107031145600034400c4141a11070081c14400c010151072100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 135516654 1250 135515404 135515411
    0xa030e061b030c071a030709050907052a010e061501030b011b061b052511041514040e0a17041e0f0605090a0512010b03010f0e010e06101503 62
    0x14210328203100410443c2c507550040d188041c144441008988107548800803054000c008100e46103600c01080c05c2a601c088404041036140c0070f03003c03200c500401a110144a4000280030b055090900c940140000c56034000c2c441c0e41c003540ba0407901c480e41141c44400880c20012506403540c480d030300220101c641414415444840c80e0618650340500d6036040358200d59801c41001d042520400c0450225101d1402500d00144900400e401440b114002c4822041c29004a030811203040c612020001d03010f03004100c1c4108a000050608289104031219074510140804207410580141084007503410010902d1500039518090082c1e072a2000382c0c9199010b200c0810103035140308081e43d4140808035039260260500c180c80720712003050b6001d481401020450004140c40e00721204044603022248a40540d06400455014208151030540d240d46440d0203038000101c50b500074851184130400070400c44440b8240c1a90740c00b801e9407201c000d20104a402c000c10700155003000c084081c14034010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 135517904 1250 135516654 135516697
    0x2090907120c080f03210604090609120801090207080f030a020f030406050619140405090309060a090306050610050f0702030c0d111915050702030106080d051206030a030e06 76
    0xc840401d01442120078003415001008050750420840ca41d81e4111000f40d46019110603083c8070083c0c041010b564981d007814001203403a0342e1030f400342d01420341002c400d01c000310880c83d040740e4903100d0989500208a542002007003000e128425544065800701c4090b15102e8110101d04007908000c19002070650200a500506102c0307001641c001c1c1d214280205290904104102d601e125940c41c0806145202d0010000d41090045804503444295030000b010384500100f5411b510500303640d26040b01c0c0000d0142a4542d00681e100201c9014070000c0040c0c0d203440c810009081620704124000a0007480008902c2c1c841d4030081c903445100904a5001320b011314045004801001c605544944600c07502130940d080404008e43e21010204008540e607041080321401e00c0900030300d400401c44080352600441d00c1c04d602c804003070300d0010b040f00c043c9600440c2c003c009174002d4071702d8401c00e0240008100136040002c3d191b8007240e41521102112005103080c009a6001010080940c0000e44d034507 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 135519154 1250 135517904 135517919
    0x10050402040b070c0506030c0a11120c1b060901090501080703020c010903050a0219031e05040f080604030216050a06030509150405010f15050d0201031d01020c0318090f0402090907 79
    0x81c002000310400c843d032189030900701034031035180e0707948628000c401c1001000040340d840300495508100d141440c008088800c51010b281040d4001106100c1c0000030720304038801d00004001d0444045070040c032141c0c1c51031006105c041d0154450035804160220014012036004d080c00310362040580c0b9006081c00d4401e00c94a00b9918031700000d4021a50001e0b016411941c1480360801807844036080c840f641000da0b030000c101002c607851071007803000920b920450703a602c50011980100f05038544440e42c1d68580c0c4e0381a45230001914120050300c1206d1503032016000d50a5800c4c201c0d0001000329287ca450100141d018100080c009170081c01801c4225503070160ba486c816005174090000000e02e0010203c03080216000c0c041d0840c1050800501007001da9035560103d04103603420700e000704200c0300703080c17a1034a0048403c0b40c6151550010900084000001000c0e28100003c0e82000c0403501c00e200038060701f1402a40d00c1094801d0101c0010007600f4070241094018203094100c2e94034503511183c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 135520404 1250 135519154 135519157
    0x618030a050a030c0b15150f1308010c11150c18041b0e040b0f04090f050a120807030501230a08030f040f060503070c14120703050c100e1510050402 65
    0x40c1100816030408a80d000d000c5070102e11a0712100c20110b0080740911b0200052041828952124008500007981031100304a00c0c29124152000c1ca850351001e80c440006a02900300301b00001d002968186d940e00581e41c000456a003440ca2501001c200c0341c072403030100719259004403605480103000300782c0280c1c1901e540c45400720444d1180302210805207e414010040b0b40e24400e4540b08508141c5140241c0d51818902d028010301113400280d840450f25003403000300341c2414040d00c42d0244d6070301070042c052007001c401c45e5800e403555961a203a99110341134048803000c0c064003a41c15000090100da02d01241c50036628400010301d03000c40941e55100d03c4d46180e01618002c1d441d800c021400b0404032000e00d46140142c0740d40d003803050642c9001c01c0020246080a000940107070000303106161030701c500b40701c81ca48196084030b200341d40d00101d0a000e07043c0d9006800c628801d1040c601400c00c035070418480d403022040010080e088240781412262403441c0c1c082c05801d40102a60800521a0b03207510 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 135521654 1250 135520404 135520423
    0x60d0f03030203070f090f09180506010608090c01020102070b0103030c0f0c08030901031a0303071509060606030203040b0f040305040b0705120412020910030201050f0c010e0d0806041a0618030a05 86
    0x641c0540e80703140a00b001011041542010300034010940001e00450307804100d40000d480044000103004c0d100c1c02d40040d8800d1900a000d4254003c200000c200e1651100007144500f0765103003254010740707080d0012801c07881044d0001d40440b07414801400024402e14440c0e0041c4d002e07200f5054070040d1503c81403a40c40f900c0d03000b511254000a945402960140648166105440c15189584100c040407030380741e1092400c010801c0d107102401c00000e4196501c102c0002e0781012040006584401d400b5009600903101903030884182000206610000344043d84102e505a4030f45003024640707080c902c40381d008144100d40a024500481c0000810203018000401c401005409411414010321001000142100503080b10b006420300150740c1042c100c03a10010103160643e80c5402c0b20904d9401040f031250504894010b05a81c444000d9001414a002e240c1c12242040185d210b00b0f40011040b01102c1a0742c1c1201041c000c07080c9201405400c1064000d0140c00e07100700400d29602c41d810700e140320303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 135522904 1250 135521654 135521657
    0x241012050f0f060115030908030109090f080406050405090a0506150d0e1906060611030301181e051b07150b041506030203150904050a14010b1905041103070c0b060d0f03 74
    0x8034010001d03620360b10b010307800c2405c040c1400c00c0f00010700c1e15080d52520050090a0300d640d140c8200c5401c00541c080b6a0480d80c2c0c228031416125911560000c2c050b500c40d1003054400c140020206400c56194071400c1d020b010000d0141d100ca070740020025069800c030f0000da0080710380d6106002c000680c10b100003c0540108800300981211610700780c4200c90a03504240108905d03e101d00c03207000301c00030889041da042c41e210314218004070b119000180110000907034a040c0300c00c1300a0140c0407103402c214001c403400845c4c1d00c0150400c0503890058003c5060181c030303061140c0400d0038005000c0e8408586460082d002040c031340380c0b92508140318843d42d404000000e60010420011003003504e14100c03905d0003100c00b40918180790729420343c2c0d90900440070344039601003180107084030002d40c0065164403014040e40d0544001d0780070040031070303c00c0c45918011130412000840b0780a613034044a118a40d280c4038403c0305a919150880310860092040e90413014448512010860341c00c4004c00d8075201703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 135524154 1250 135522904 135522913
    0x1d091504021804110a09030308091c02010b100518061308070308030a140705030f0a1b02100e010603021503040501020c16061e1e090f08241012050f0f 66
    0x1903005220131244a1001c040d4030040601811a465511000c0030040305e030546171000780c03610341c0d10700a42880c1655031a112000c5a040e02c0c0c0400c1038042d0402084c0303100c01c895005101035411000d441522032070110001c1c42e803601e0b215280c149003000c042d246203c9801901c1500f03d0311280e000d441e2040702e40042d2000e070f03030100c208101381140e40503040581045190645080c281104060480d004c050500c0e8a082d049030b001a031200070783e0303204004410301250b03011034002c502000a03440300d50091404140c14203000784480d4030501409054104c81d8082c0440c03a40007001c403901107280e00f01900490305075401b00328444d0300290030403aa4496440700c0c6409000240780040203402188155940701c0510f4600e0030120829030401d01c045030f01c4480d0038030344c01e002010340c504543c41c65194005540c800381d03c1d179003c40c1200c000101a40a015490041d20162101410b02120403004070781c1040151400902402480780310360000022912640444e40413030201d0000c00d00304440d90f4000da405911 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 135525404 1250 135524154 135524197
    0x10050d2105030f0a02090906010f0203070501060b0a0f02011802010c0201023904050708040b2e030b01121203020d090b04200111030316090e010f090c1d09150402 71
    0x1080310f006900204584021842d00c2c9204000c034110700b01c02002c040c14020f680414100c03450081c000c440d14150310a000f00041c0d0344501b090b8500d81c121941c0314000900f05500400304600510628a002c16050b401c0c01c0b001d071460f07004654841040d6000ca045000d003c681403242c8404100306410942d081407400a480b6482c070201101062680d1414840c84c2800e0900c50030b03d42054031180c00c180c0084100c04541c0c0c9500700306402800203190396007c0208984181c0d403a55040440e041524450002200c441e6a070f140d080c00d0312201e900000d481900b514100c0d96600e07029900802140c0c8a221000c9041040350301c4051081c401140c0a0fa514085ea405515071100c02b0f0311503000e100c0090800740c02464420b01c0c3c156407400010000501c82c1101c002041540d4061400c1d90010051590500707800e6856101c250318007001403240012082c1030112000a0600481821306500e00d80d48400c5030712011442044580400648401c0e00c0f01b8a10021406903103660005004246205d56014030014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 135526654 1250 135525404 135525421
    0x51c0203041502031e09030f07080711030106080303360c0411040b270613030b09060402010f050d0608011104061808030a08090c1008061810050d210503 67
    0x2d2885090740701d072041003000b04d00c40c0101c81080540041600144141e5212800396203140700b0440000100e42c0040707250b0080051140041512501c103000c405c00400e100000c1c0f5082ea5568000c03410179030418000a00750381c8014001101c55010342d036142901890743c0c018100d16211200c1d1024180d00049a030f44035605140c01841071040b2000242850680f400203400200d02840c2405042a4034058a9100e003000c0c0050a4400c854000c03c00390b550800d0038020344954419100440d01040c0d10030010701c4264010500a10454040e1a6241c1b09405d00f4405c4500c3d80c0100b44841025989550105a070381003481900c1d00d4003800c06040ba0b4035410080d02401e00900203100200d1021405001e00101c2c6012064525440381030400c0c014a4868140171030800c00340506094006d040603548401c041d600c90085800341500740c03084215080341820482141408550045000009082c01c200e18149040040b018900508415103000b28003001c200d21000d0b807040c608000b9101003384a09078 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 135527904 1250 135526654 135526673
    0x105281a030f180c04020705030705160f0b0306060f03060102160608100909020f0d020a090f0213090e0706081902040311010306050607050606060d0f0f0c030c0215060f01051c020304 80
    0x351501c0c1c01c1d01040c02c00e034580941c4c804040300303554022a004208001002010401d43d203039070340e0004c251143d038040e00c420300040601511a6150100c40f400c800a40000b0120449014400142125291801d41180340d80c0030743c8040e0102c1d04500c40c03002525513021650111038084d042031307501c2c5041c504040c601c50a071741c107454000f5403002d841c1c00c0d402c00040e070359440440721000040c0d0b00001145060b000181e00880d15910028185051100c1c0e820100001d90090080c003c682041070115500c800110040741c0e0128923038112648411000d10116024210789a4000701148108000c40c00b1404039000785d070890ba20840b0f9a02464241e00059038250042001400c02510100d0130b05039952189640c440c2d02a0080d8041d5000240040c0c1ca208141c011400c0e2518003541400090144850354000307001c1b00324400d0001e481c2c0303000701185034070206100481c1907021320129000d460b0542000385a00200c400c4030f0600504108525007410b2400740a00c200034a000c0058492a00b0304244100c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 135529154 1250 135527904 135527911
    0x1a07020a1502101b12050a1104140310020a05070f061b020303010f0b0a02070b090f0d1a0c0316050906070b0f07110d08010e0723041701050105281a030f 67
    0x2c805540d1180301015030200317103040c07000d002c3c440c045620307190101c104000b890450402c035211100042c0216420506c6000c00d81d440e0702c140c1c1241c04000a004080003280030b00d032a400001442044803e002c52288034050604600490707000a05008420288548460070242c0c18050780011004004410242c031900d8002c0c860900d07514a84070744c01100079220344180c06140b49605020911000e0743d2502c00c50540309240280c004900f14005041c1405907d0107021840d9003030b40302e84002a80e080d0480c065034041c031800e4441c1a01e161900000741e8031504101002e07904114103114060200d00f81c80301d50350080160b2000d000c240e0816003c020600e06045003850a550b12a01400810a81c443d040c10304640540303c0549040e00d42c0c0c002100c0c1d4059121407a1801c0400a40c201501d0440d035004001b1582d403441010610480c24080c07500b65602441281c0d4020300c00410202000c04c001c1035410040341c0c00c0c180d18001d9840d03480c10951003800340248003000c0340102c1003041c40000b210a6680 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 135530404 1250 135529154 135529181
    0x180501090902061606060305101b1e030e0c06121803070f0609020d02120c01110c0303070b0c0f03090c01080c03040b061003150b07020307050a1a07020a150210 70
    0x61400300d0b00812820b100b01311903030b0340c1c82014034603a5003440301652080010710b40c440e080c1c2d24882a10080c50700a010884c4100f80000301820300c84505501070440c0d4180228000b201c1e804240c18004203030020841c00e826164039020b02d010100306942c5c4e401c010040a4081188075129003041e00c040c2c201e0400302c00c8070001d00e41c0100141d4010402c040c3c41040c0c0c469100e17101090035004c0d4030118080d00c110280080d08803100074501030329070300c0210340f030f185241c0281c1c1d44204500b007144c0280d90b1020000102ca8058104000600c04100c2c1e4540c0c1c554850001141c19107044804098140c80d82c0c03007254080301c9038002130b144144035030b400000c15400281e0009000d003541090b845403000c1c6400076001c40d2150110b2450f145007680a6000b150041020b0072841c03002590f2110610410740c01413204070b00c09c1c01854800300b503500c1d00c00c60f4a000c1e80c0c2510304a900440c0d0340065154035500200303050341d00c040090000608249070400c90003103010107902610b44607110b18105c10035150207205580 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 135531654 1250 135530404 135530411
    0x10f0311101209080702040e011b0504051e0406030c060302040e070309080a0f1115090f01060f090f020f07050a02040605040203071202031509090a0b0a060e0403030c0e040618050109 80
    0x304654440b440c6426034001c0c200008003080f113490028040d100e00c1c00d00030340142c02d14003201c80644041d441407045d0385a251400d141084ac00204035118421800348a0b032180d055148041c11a084c90700b0b04046a4000e07000080b815100d4607043d6883d466607200000103500050103000c2c00109031001d0790000050b0078244002c42c600e58032820720340038036440e44080205c0c006108454501c1031003d40034980d0408196856030034a034203801c032900d800300c4040721a0301c135500101911003c144500000c543c042c003100080103080c0386c170120181c0b01040d607950416800348001c4005404030002400054490300c010448130b4842d105000607542e03103a005a10661040c010402101c0c0c21102ca00b040d206110360060341c90f5220101c290300100e6110b4444e030407010b030404006010600044650025004040c5e200c2682d40300c05511080d1400f0340036242c01c01c1c1c6450081000079000b40c202480105043c00d0081b0890300480101e011200c42c0d500c4102d00782c4504004500301184c62186a02610000200b407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 135532904 1250 135531654 135531679
    0x1507030e0105161401061707090b120c120307080a08010503011a06091003020d0207051e1c050c100c030f0b01030b030a030e030a0b040302010504060501150915050f03010f0311 77
    0x40043c0d030b10400240c907000b01c50700441000c98003988240b011b44034001c006e880640744080107950b205104c1c010765080c0c52519601c03501d58900f448050326040c0840d001030401600c01d03014440c0a0600c2401140c561206000da03c00144504014000301845507a40b41250740c541420182034860b0b1400407d0381a82c0c1d003c3e0050305441e400700300c0e05488010745a18040a404080890003413107001310b080311252000c500c00d0104200856503200c101e00323070850b1314039004402e80d049454206a1107030300f00c0707541d16400c480130700750103400a041d06501c0d034002d5960300140c13805c3c100c0650310070861103c0040c0d40c035040b180048031a4411201031003407c1c80d0030804a02100d010a0740c90340300d0780d00a8240b104284020b501c1341c0d010021a581d00c1c0e40003810400e141445e14010b07020b8030080e03604488160401c00003151120030600300e51140744240d580d0204844c03030680ca03c460440740f00b1078541040b0040000c1d11300001e00b03400460080c8283c1054805541c0f80d4148051014003c0700c11034440d00007043c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 135534154 1250 135532904 135532927
    0xc05030a1425050405030f070608010b03010e070c0f020303031807061404050411160501050402010306050913030825050702040507020c03030301060f022406030715020d03020d06051507030e0105 85
    0x291010041180403000800341c07410041d50f483c0601d600c810360510580705c1c811030408000c00c40008948547c0c4900406036240d80c00e240450009014140e040e429803070004002034031550b00607052a0090307100c2031410300750b90042410b40c0d000320b41d154031340203003007100c2c0003041402c008150080010303180903651001c139100f00781f0300351007140303d0315109680b00d1309688040c40030301080301c2c60141050413810303e02d56a031501c980a06400c40301640842c1c0b40003400502c50130f105140910514240c1814420b00d00d150394151001e41010f03050b0340c2114400d080d4103141c0d4000c0b00340c009022501d0385071641c8a06407032041005640e0004c00110442d0004201d01a9507140001900e054804ea8240403500002d280c00032450b01c500c00c642140020139407042685044007503851a1f006242c180c0a6642650301e031403100b100d400204800b8801030b40008240420b55210b9802751182c284034030804159143c1d900c2c006103003840c1000c01040194000603c500406070072550540f210300080c248079040ca0101d0f401d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 135535404 1250 135534154 135534181
    0x1020f0d030b1c030809060106020c06040b130504050a02040305120c0a021210020d05090f120f07110a06030b09070306080a02040203190905030a030e010635010c05030a14 75
    0x2a50001e054888a6998940d075881070712101008500143c40512007660030b008141400c2510b0301c100b18040d030400071841c5c80c400314041c01c0f00c51024045500d0300e403030854448800d0f480f034044051180c0403d000845e00790b840313003e600c2c0104c4003403101607201c0741541050b0741000c0d01304203c1c18030404208407411400c6000325808510640464000c2090100e01c861b5034140380340c8420701d0b20444c1c4005503031422404a940050701400d880c504075480b0440c402d0348c82d560f41c0340e078600007800c040c81488855401e03052800145031703c0e031140501051b140c0d440d101291200440d60020400310b0744400591201e4148000c2c22a80721040f80780611250f8586586603031100c20ba40006030003190000001480c4181ca80309554618600107820032031010f860900a071607402084660b000241440040c003160a01405003405542440c0c1c01c41006421003141c911116401e100e03000100c100340b00000d50210070a100d503900c20040398442550b80e103042486e540c1102e02030710342c0d201004124406e00034861503020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 135536654 1250 135535404 135535423
    0x6030515190306050c120a0501150203031902090102011e0212060603070801060c020f030a030f0909110906071103120c0114010305030a0806120717010f0501081513020406080309090601020f 83
    0x5900040f1502d901c090016244101b01c2e801491100440c00e1146626145d44480d040341c3d51003504000072052200126104c1c842503809480b031601041058170749890b40d0b4002c1c441283c05000010340c06a803100d10401039200c0801440d51541c1c0400d09586072942d404000340c1c464401c030340b100d02d9450002000b07804600e040c0900710810254420b0b0341d00310344405601c00c0040b40d0090403a01c0343e01a074500184241c0488403c0d40010780b840340d00142660803401409000e00035101c0040c00c0111402c14080da036008460240c5c3c039000891000c1d240c1d502e00b884011841c40d86904034a45e40d81d5020401800d5480010120021440311001000411004410783c0c1c040c8030301d440c049106803104030004042500308a44911030740a405000514201000d16004041c10003000038007039071040700350700c0e41180c2d024860790b8030942002e4034095190030305c1c403051540500d200c900b01e410300034590040782c03c841081d080300c00d0701d900010b074141320303850106a00f561000d03007440203000c1d141c0103011054440d203962 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 135537904 1250 135536654 135536663
    0x3070303080a09172706091c020d21090501020601050f01030e0109080a1809090206090120030d020703020609010614040e010f0903090518070206040b0c0c07060305151903 75
    0x229181410070000f40c0c0c03500b00b100b0007082c5454480e07413854aa100f008005c201e00860311a0385048030f10203414101e042d41c0c240d00b801801c21039480d141c0c5003200c240282056040341d000440e141c00c0b1000485c868249003c1c0c40c0c2c100703580c0842d0b43d0031840280084143e40c1016042d580b000f80108015a83c042c000d04402800b0b02c0c02140d0244030701842d81c09414405001421300300045040361410341d110f0012808a4104541c51414541d2145103404848010401035007000b42000807100ca5400380d90502c2d01c1c1c081302c00340000701041015045045030800b0040c1e1404540000360392060590400c0300c2c503000040792000304503851800711046240100c00c40d62500031038a8813001d1001100a500a041d00c0750600401d01c084441864018081d098600809111746208242c04a509002c1205070b40b0840301500104000e4569840d00c4102c008014041000d154003045403441040c418480c0100508007600c0202e444e0400b000050300c04110b03c2e4046000b440400300b44004a002d00301c00390100c80d0072 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 135539154 1250 135537904 135537911
    0x30306061112041406122802090f04110c1603020108010806131106090301090b040606060c08220b070c0602071e0b0d140c120726180d03021803070303080a 68
    0x44d0004154903005003034158035034810035401c205c0842c1d0308002c0007181c00a01c81d4501d83c080001c01c407043c120302859001640201011324001128203050b03000c12640c3c68512807450420a100080710302e00595030350148440017800004000715600044d6142c00b40201308050300342480d2075a031300100c50050403400f8042c6010b070451070f442034941101302c600402020300240601251400c0030310307800f00266811540703103103032000c0000e0803481030711100b140e645d000c80d21610740035901500c40601074440d010061000b108105c0058942180c3c40200400744c8299100e07212107141440c00b90910246500402680f88120300c2c191240301c841130030703138265203458003400d0b100c041f074440c00f0300200000c05007105c0e1905103d040c030a850039800068003082014000040c0c40340e881031003c590b8a080c03c0d10561040250007001b211004003000d0150380110007000c5031481c22500e4041920701010281d89501180c1d0010b01c042121030200f42c0301440034400c1d001040d20134503640d4020601d0310002d01d8044031699 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 135540404 1250 135539154 135539189
    0x601090617072a0c300c121202010606140702040f0b061b0d05090a0306020a0c200306011422020d0204150e04090b07031e060303030606111204 63
    0x70b01c044001d50f15070500d0412212220701c5648210500301c0f482030394200034030880040e40c20300420607410700e4143c8844d61034007440084140c41c8440380030541180c9980e149031001c600c0021640d15450340d540500e4818805000306180079013100c0c100d801032030800081d00d500708204141384089500d6680c0c19100003403d60101d251b034000401c9041e82d4650701c00b42c0001d0010034059415102d00c0314448040c01e4482038084500240c03040c0c801c04003c5900b24012410401c04075540741d01526542c625400e0901070b0030155940c4c4030f00144054080700c4c012406524503d030a040c1040b2842c0940621b41480049566010004101c100c402d1500f024001d0014140320382c001541e015220903640307085095482e140c42d400e8410a050410141000103041803190980503d4540505580710307821180e1400c05440b009000c82c041c1100c224501c19900d4140102110050248904401180680e500140d007605122000b4040a803105107509194016554004001c00d44400c442c1280c40101200c0023040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 135541654 1250 135540404 135540407
    0xf04020f10121401061805030709020a020c030601030803011706060303070602070f05070b030a0b09070e120a020901080d08010b0a1b030c060c0e090a06030f080a030204030b040f0605060109061707 86
    0x310740208142000d840c9405404a000158141c07a17041e01d80580c000140c88220703004240300e02c05c180d03040d0b00031030040202d0205a4010030646103540b0696200c00621400f007440d109013a0310444440200100400c044004810f14903034404813080500003500b08480000d68900920303402410702e03a40003402608010880308004211540403013910f40d10b0340d0b6007012001d6070704200c030202481d40c00d0082c076841c0c42c42c01400d4148aa40079485003180c152500003440441c100ba8107a40e01c40703105102400009d65649255107000f0502580101420041c2200080c407403c4103034080f07510541c0a100a403002c40e00305440ca4004c03e40300c1c07400b481c2c04000381402c0b20010b2030aa00682103619000316450850b07402007140c1e000c0308090303076031555584802ca500c00441c0c489200c00b522130118150840001103030717400140350403030241c078001d0304080d1642c031440f450000544049623581c142c6242003080100f9070085592210003428881c40c00d500d00800030703080002d520102c1881810510001d10290b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 135542904 1250 135541654 135541667
    0x3060b0409080f18100206090105070305060d062403060b03070b1e0c120705010b01020c0a0b12101703031b04030b0a0b041e0b150c0d0518090c070303050f04020f10 72
    0x4113030017442c0c2210201088000f9456100c29201e1800395401c1000003a0b030345000e070055034000d00b80503211920401d010f44419004082000105400c001c2d95021100e00c40914140c0b040a51302a400005054030b0800c10140741c003040d0361041104204c24032500c0702032001d040c1b406070320b041a595456683d4500401c0d190422131080c86074410007202140349403c0c0a01548414240300c800c1e022142140030920404c1941c2120340315034010500e041140c5412400b100e4006900804510030b402d1080c1d413500c00b003018221480c0400441548080200601420040484125402d00c150b90070328041c1581c8600c815401c00402000480d0345546040c85c840d1240d522100d9124bea80d64a54602c000f800d4890740540360780c540c25441400b0085460110035280000c0b00c80d00592540105400c024a100070b4a50350005c1c0c135107020540d0300c807001e6500760310340e08007a900c41e18117511005d035038840500c0c014040701e40103800710780e42c00f40010400c40141c0b0340e4808ad403081142141d441c2d035070f020b910318102c42c0d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 135544154 1250 135542904 135542947
    0x32107020307121b0803030a0b04090f0b0f150a0b2101320f0f01110106080115080a0f06110d020403080301050f0d0c06081305031303060b0409080f 65
    0x16100d12a00000c11101020610564503c11310324550b500c0d0341c2010101c001c0c41c1c10301030044250001c0000c60900d800a5001c2d0b09001d401130000f0441c14038986881c601904826820b698414081040148800011f64020f03401010070320f10240e80c50341c42d400b00341860040d00a9800115001407120702007800700310b2151a00359084500d20342983c58412003010700e40740100200050614821038062041040c680035a0000040d166a0a0b40340d03039810400000a02850315052004d0a920520185002e01a02002e080c051001141486804800900144c05580507a04a0f044040002c002a8071150540e40540d013008001c00e03404072090600c0c010344248440b074890207100003000000c000294000d14100c420481e140f400100c1f4800620003c03841d407150080408072805002d0105a001c1c0034855000b18850792642102110f0341d94a84c40c5601450641c01203050000302081000310b24091144070800645081c081440107603190149805a048a64044d00740469007441c01e03035061090601 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 135545404 1250 135544154 135544159
    0x50303030a090204050108120304020f040b1f02070f08060f07051303110f0904050607050c10090f1110052a010212041b0501080106200618011a03210702 67
    0x5803030515140e00030003003070201403c901aa09140002500701c030085444842188600401440e69544c0e500f0410032051000f481507000b9501c00201e00280c584050b8203035400d21408582004202026020345003000545c004800c00d07482d50014072443c000414107e4205206c90342c5000c0c0f5884000e005d96003030154032201c0c542900360120020a01000c040e010756030b91002e9070300740c510600c6101400000f15040790091f0290b4031800c041140703688524000e0003032850740301c181d40c3c4480228601c5070581e580d0260a68a080400080000b803083c2d1000b035480043c0c04455400c045844590050702a019001500700c0314812900cbd03441103111180303080c125403000c0c40d00840d680d1241028501030450143e40c16500d40d520b1420300380c02c03944a9070300741e02603540503100c401c09a868100111070700399141d00b030f44184400f500883e500303401c0b0411a0798064a2068019504003294440f42e07800c40e03412040c04074025401800d09003050710f0202c2e0108613802040c0e0b00910100c20048826424400d082d0002d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 135546654 1250 135545404 135545407
    0x4020a080d0917010903050a08151309030201050a1b0315050a0b130803120406050717070f110613030809070b030106030f0605090f070e15030c0d140c03130606050303 73
    0x544165115100c9030564003c000325440d2903a21128080c200c42c034015004000c07a00401000c1403c40c01000905d90014000c012600010780c2c0d0b0300401c400003440540c2c487d289440d03400e07080070035070280900e43d440441950100680c08036040624002100d000c2c1c0302c02810365800034074412500031031b024400761801030100309216694800d0910b842e4417545032022401020b11003c50795010200c1118201c403003104600e02e29460719190308004010182016061040840c0580c0820b846244800d01c218035076120b9124501506401a240c000d00c440c0c1070f8403541100301007102c40c1c00b400d004142c01a0301440d208905940d1000c0403407500000c1d8001d44409880071000103403581d80b40e081401d9075401c0c290140465560b4034240702e403041c0d06a58400342c00b09001c001948007446100c41700301e044001002152121406d2005010f103502c00d4a0900107103400080c1d2100c00306130ba02030a503820180c145100980c2c0f9200710052624000684034400042c0c0c43c200942c180b020070f81006021300401400d40b07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 135547904 1250 135546654 135546673
    0x61509060f180103050c0105030c120a1b0207050a0902090607120c02030312061f080a0504020310021201030611040303020d0c030513141801050109030807080f03010b040f0909030c080304020a08 85
    0x703010555007440105e42074401d01b00000c440303503c81c4040d60302a016815071130b414240c2183d141d4004860081071101d0305940c40481c401004100b04000c0e01e50000307a000b4140303240c100f2061042c0040c06410141c5010b00402c14103100d03403112000c032076469401482d8071134003c103040c000711108813641c040654907200114201d040c0610740c43c002030203060219010550130642542c5903150408084645007c940c070300e400506c1c04007060300200e500c644010180ca40180309a0782e0041281c1041140140c8840118018404c00c142ca00c42c5011040c4030894441c02c00380b86a03030081d0b44400c2c461100080140d1482070390f0402d8015816180484156602c00aa250321100c440f44100882212948581c88400340c070080300351000c1c40755050383c00680d00c5102050441c1c031010050f6000310011943c0c50030802030b4119492120020354003a040074100e480e99540741181d54002003c45412241388541340031069400241c1000002d008550b100e1a4140c81e039031756000040c0c00341300c80e5200015034002c00c20315 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 135549154 1250 135547904 135547939
    0x2040207080408280201170702070b0c031c060f180b181e0105030c01050a02030409021b101413060f090503210f06040207080c0715030608061509060f 66
    0x4241c400c00c0800318410750300c4070404d03026000c1d0841c00401790100b007588500145035010341440035440011401100c10356980c94440d10038941c131011140a15800c0481c030b144040b10a401c0069401421410070700056090107414044100705100e05040e43c04c007a030810f02090340c2030300704025000703000780020724003071070f008864550b00c41c11514860340031000b2074192003d8054100c0f40c0c0c140c4002070002d100b10380c1030b14019075075540a031900201b035101c180400a03034465103000030180e02d010388810704c2c1030038422a4142e14204403544244002410020b8004c40e50b00c402d0100b41e4841403207054901e10414a06010004110070904c214086003070581c540700740074000000300701400302c0380722180000030600d440b68600c0354251407410940110002040180c0b82507006042441d005041c2103141c00300c0a0041460000b19600642400e80c0b88103203118000d03003600c108070060080d14040c112600d0b000a2034561540c400c15800d00c00c00312000401c0b010340b030342d50740001c0e824000b601803030707035007041e0a035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 135550404 1250 135549154 135549163
    0x10060308030a0f09151802041805070621020a050403050a0507170703030206010e100e0106020c0a060e03030a030c050c0304270e030319090206070602070b0f06031902040207080408 79
    0x102102c5003400e00040d100b005005210705090b00c2d801ca0141d500441c1080803490280c600120403800e003c0411805201580d103e00c01c251042c034014020318014042880d049061080c48d0b4018820b114130345402500652980c2040e001d125104c000040e621655030740299014090703900081c21510605401c0404c01c8000240001030b80d50280400024503843c00203680d03030303102c103010007030040c2c106400400c4042810110b450304a503408401082c003a07200c860b010858802648000d006a04c0700c9140960703810301c100400c0140c038480c5410300c2d8510103680807958072b1055080180070907031388815580005100b54103403504081144103036551266195505480d4005045c5641295115020002a114080e104000500443d900070f1030641e5900c482411406901c1056600810740700c00a100c0181c1d46c800c000d00c1134908c640401a1288814284803100800c01420081942a14018040c080d500021921000c0c007810110b03200c43c0c0e01c1403000c0f501a00030303140c2c01410014041004a1802d00204 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 135551654 1250 135550404 135550411
    0x17120c03070801090b0d0f0f050109210201051510020a080a050a030e030a0807050f040b0412030318080904020f0408010c03020405090c030402010e06090612040b0702160509181006030803 82
    0x180c0b408aa0390b00c07014064100c1e010f8204290340240641c3e0460b0019020305002074255001e03155551145a841e1100303400c0d80e0700d21500700c1b8440e40c000444801c541045c10b4040420200d40b000300100d08d0304110505002180e0080c546c8508241d01240311482d00c20018007070200d520450403074035080300300c0010340745420505581f00400d0600400c2a1561800400e540404003155170340845034944100c1554558000c04003020140810000415186d4900e40148018408100c103000100014100201241c4246484d000c00200030548100801e10300002d82d522038408450059982402070000714003803140b07501070100d070b500f880110800c00c0c0e05980904111102900c00300c11540d24500c00021500c01203c00034040f807400c007100c50003824490058044d889019050b54508601c100310345810140444044802007030281c01c02c141154180458006c3e051000b00404015062000040701401c00901c005803000e807448909000c1c210800c14600c9207000c580080217502e0b1207050a100691088 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 135552904 1250 135551654 135551657
    0x50c010c0f141c051306051b0f15150d151503050604050609060f0a1d010518070828050a020913110609030c0409020a0b0c0105010302280317120c0307 66
    0x20020341c00f03a009000f211381e0034a0510801d9042070410310240c0306504100c10694440c2212080ca00544400304880da6403030301c5040c003c0035071409071102050010002401402401031405070242141c40d1041d1008001768089807400b8205401c040c1c5900400300040102c9c000429500000309008010034428020350040701903404a559210b5a180c1d0fa000648018541e100314100148401607141e204007040c18000e6005281081030350401425114281d4941c5180350450780c0c0500c282d84100b00010090150030081d000280d003400c4541c900d00340303d600b20f01510b07206116033310401105114440302c0d1a401080074049090030004c1901d05d85074030034125240d048002144c0c40c9450800103803650001c00500510044a0120601000c0c040452040707070070404040c030116400c41c4280c00303404c100780d94100008a07980b550040041c0112003000503021319030145007100b01500409100380c280c03a04034429103054a818420b010043c4202c030107505034071f004c080030f000040c05d58030021402001c26 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 135554154 1250 135552904 135552943
    0x7090207050d050a080708190507020102180306100303050c010209040606050c01050603010921020c0301050c0703080c0a080103080310030f030903050c2d030304080106090219030603050c010c0f14 86
    0xb2603090b100d43c821381510a0124081c0340001e10000e116065940c0c2c40200f191024130410210070300d00c001d80d00c0689103040940d4020401b80004443d41c90300a800200c210003c00d054109611400d4000e015404040c08128001510140e102000d4044503802c0c600508100700c0b259480c10010040e402c03c1440c210954202130101f2000c0c03405014007003c064100e8030601440c0d244000d001418114070b4201320139405041c0b08520395580030711465105070a4550b1581d51003509141c02040b00100422001100384144103031050141d01071080d86c1520f6001a00030340da6101c8138458006440c40e6840242038000d82582034041686c015905002c0b6031185044a07a205204000c0140894846a801030388880882e020058114a940c0b24041020044c060707901d8907480c3d141c89820340e9583d03000b14040780d800040450021312070401d131040b5a00782d442c04000890869448076200d91041804d503040000e61020304050024074092a9202a0b001c00104c400500781480c141d2644d40d01c0d41c02c803252001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 135555404 1250 135554154 135554173
    0x5010e1501061e020c010302092421191e0207030c171626030a091101140d02070812090601030b010602160e0417030a14012c07050c0709020705 63
    0x6901140040c03101c10f80e000351290750301d01c41c0114025040340442a40c450415628902c0b920413040034484840060117486941d8103a09214401c00340940418680d01d5035420208030244d880c91220040d00e80301001e0100e4080c102803030328443d41c841c007441e003410b9601c00207820b4105600800d098810382d220781c240c0e007000c010500101e60580601c1c01401000c0c41c0502d00080050004c841882c8080c084207051f04100c15a03c00d04652504111902c540c1c05540303140c4203050000c900300b00400070704c0034a0f00c016880401d21940c90309016406c041c11805130003081d004100488502901c0030300100080c03040302d628254180ca0b5484100784025104a5102e20011580e2840403c40c5c41c44800c5143d800180340c1d107802000c00345884000c0064445060010b10610f220603d0401107000740300e40d582c00300300b40c40c4c600c00c0000c44040607803000c150b00b40030410300a05404103c500204024080101340c0d17056490744400e45076407040700f00e00c8035a4021648003150f00d00341540640035250049044854400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 135556654 1250 135555404 135555437
    0x91b0302130c020d181d0910050108070e10090c020312240f030c0d050a061104050108040b060a0302030111180a03170705030705030301060f080a0507050d0905010e150106 75
    0x4400d090b00d01d0043e0030594405950600412144030380303140c192004007035a5070321140b00542c8421100401d45c6601950b00f841a410420021116641e8040004118075458907004964032140e602c102c2500c130954000142d000382c03888104100030310850006101c10100810002c3d202c0d80441d0124841348581d07004960031706210300008829210341903581080100c0201081010014610b185515110750044404191680c41400203402c1c070480041024248038070340401510b1381e62050903071000b800d10042200c0c1e80c0c845c0700c0680203900710b0341099071034681c8404503402000d5038102a41560a2441c4030380e44481d07190082130525082d001280040131140c0c10080c200d407440c8009482050803c0b9040c0c000900310b0300a0418601c120100c81c0b9182550742c0360303411034200342d000d240410b40e0b1010000d54182c2040c41c041d0b200041a070b040201d480d01c0300000c2c0c41ea0080c8027110a8060f520810324041040c25031101061a003001c003140c850703162100300f64454813000d018100c00110104847c0e0041c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 135557904 1250 135556654 135556661
    0xc090d0b01031202161205070b0a030b03060c031501030c0e030a0318081209040c23030a0c05070c03060507050d0e030405011808030706090f0b04060504030206100f05090703091b030213 81
    0x1024180d05d0190300e039103421030a05240596910603103140c00b4100c4001100c017042001000b00e040076031030126080b81d10208040c10000002e000e0582c48130100b0801c07802c8134014041500107103090030005442403601c0d03821a0f030050030301540c0d600361083d0156482819003004441c56048034100224800d01c0d101c06204d911050501182212030340148000c1d030311440d00344c000d40002003540c079001010b03520740b8001860340c207411600c40e20313001000014411001094004c40e980182c95052080c58403c1e40e82c3d800b0001c048901c00039280c1d5a40b00e020402043c82081150b0410714144e00602034210407282c610307200c0d8010711405010440908035500050f402d0740e4004111000340b00994141119500c1e80b10107041d000790700b03d0741440048404000075000c2c1840c0c03800f490083c5400a2a4942887c001e072030000003401d0901541000c800400c40e2092114806058900070341d1a03282c00c2d224100305902034500d0b40001403010705011180c418103c0c98020a4080328021030b074100c00e010502d02030344202c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 135559154 1250 135557904 135557923
    0xc1f1a0310020304032a0c050604050d0f03030608010e100515060316120c050705010501170304030321060312090605040e0a0e1f0b01030b060a08010302090c090d0b01031202 76
    0x59000501811041c0e211540916401800380c24491007590600200c04004c0040320b15008140981e01d5070311b400e0107900c020520203400282e56640c5802d0404000460441c0000b0004044417003040815081501c0b0750441d00041100b031009000040c010074540741c945a1501d40200c0b10b0307181c0300002e04044400811207000600281c2400d10f5501e8420585501000c101285028402401c46808410942c6e205526140c030003640c956883e11074510b042829204180d00060392441c00821200d01a5004030880e0221b030b0707141c248116140c40c0312038000c50313034618400048001403601c00b0002c00e0200d215860700032903041d962504111921940305a40600841c0070300d0020a41c43d10000f1500041b0754043d00c241d24400084a400394881d80746451039410710001038036001d455413042c2c0e20b60b5800d80a9264824421102c4038203003042e880c0000c0c8483e00c148000391103080340c031703010500054a6070105c41800d00080d01d48022038001f400c020654507403e100c200c81d090040c071401c0c1c2c0060b03c041a074440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 135560404 1250 135559154 135559159
    0x3080a051b03030a060e0906010f060309050118080301050a060305160e01020a02030109061e09020303030f04020a0e0c03042001080412120f0b0a050303120703110c1f1a 74
    0x180045280100c0300340c0c00aa118000d10060119800d4818500308041d5101d840d0f41000401c80344d0506100c111051b00113400c1c244503521140c01401816111404502030780d4143c07500050008503030914134058400744510500180a490350501480004001581a1042034580c410090303504e450403811500201c0c4c2011880c810040342c0601c1c60b00c1807220b501070200500c12201d9061854000a00b140e40301402101d46595410301011200c414002c4d1a4942e080e00104000c0d1300d680d078001c40e407644001881c2504100d4501c0000d41155282034011010303100c1c15081819615045510b406a03900558042c0c03602ca20340101200c0d01c003200000000c40c20010b80d2204210b403903d5460035260101100c3c1e420a01c8224049419881c1c0c461007002110780c0b07101401702d001000c05060000300e0303000360400c0d4003c0e042081041c10061400710041c0c0c01000d5440c001481c808000b4040302d55020f014014003181c000c411040109610340004c0d0504108a04010019845140c845280c9888074005094 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 135561654 1250 135560404 135560407
    0x310050901031101030621060f11181e1f0504080d02060403021203060319061e1406090103120f0309060f02030a0501051f08040503040e090a0506090105060f1c0c090b090a02040308 79
    0xc1c0003403032340e41005000001d241400300d01c400e21010003c020b50802c2c0c2c80f0482c480342219030b901c00c3d0700d068110401546904401c1848940390000440c014164044000d00304d901220449101c2c0b9110303004490040070304505a43c02d024010f0030094035842c05075001c1e0014400d0309c06480d0056201c070b08032400b800b002001011400d081404c510515003421000342d880d039507070324402c07501d500e81900d20100b4040d002200180d40c141c030921500b4a1000a003002c1d000358903c90050000414000c280c0c0c44280485c245048410704c0f071039086019024180c0001c1420381854900c607800700003900558000c0c6112032047c0100d0382c03520f0502c200245141e204884815030402c205810501800c040c94015004005591500761114151014071000b075810248603405284403200380071050189640140d041c03170081c0610b0424000041e4a04a121803a82c400c10b0760300d18801d0020f415088100c2c003142d101c082152125500c0402d00c0040c40016422805a90803000080c104405ca100311015030f0745c07101d1201e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 135562904 1250 135561654 135561719
    0x1b091203090f080304061e05121005030a0b160e011e0306030c0f080f011515022a04060f0e04030302030903070804030807141501090203100509010311010306 69
    0x82440502210003a014401656004aa1403400c501c018001e405941c00079075503a803800c4001499240460039040418000e001040d01c100e5103d000c0b294122220039141c40e03162104401843c414409601c000c0e4144140710b4101c00f00940400040c0c41a040d00400500e0142c424005070f80182c5e822030640d0004581c100034415170460520611695000c514001a0700c1e03444c1d40d01c60641403042d4001410f2001686402c0215660400040003188280c600a000300c441881150034030141500400c00c02c040c802401361142032007000304441081a10000c42d1280d980d500001c1c0c404086c00a0f010300807420200007084414002d91601d0072030f106c811040b212a501c40e10220004e4201030310000042c04200049004110804040e202441c01040665918142483e0140840e8041a5540e80c00e81210070380c074132071425500c4104d04480785950050b81e680c1e1500c0c00300007a2103464100c990703c02c119030000f0003402040210004484001c0c3c8041100310740714426070b0390500c0c5041000840048420310f1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 135564154 1250 135562904 135562919
    0x80703020309030f070609020f01050f070201052107090311010309081207110706021006050405070e19091103090601060e0a03080705010b0901030303090203100b010512060f0901030b010303031b09 86
    0x71540a2100340a40e400c2101e60310002101d5030180a00307032102c503102c3c02d0884c1589050740b00c42118441c2420128500140507451826078020004080e05111020440605061212900700e0840d11090200390070703464005006030800d01d541c001074480c003010814800c01c5500030310540048540210a1302c1c1410000980d03100740140c003e101f9010041341c11000d250200f001c101d0440a0041c03600901850840703280c442084074565407000e8440e80c2098107004840741c00502011a644040d148108415000160750f0300c100080d90106071140c0c47c1c203200c182d800d00c81703801950003000400140c412907662450111400c44d40c00c01c3c1160321203402e41c030030000500d06000810010b48070320b0020500725103080004400d20401d038404d42c08aa156180c0108614040c002c40125100b40c00e0200004d46020b00004c065000320151a1202e01040d0042072042c0da40441035010b9160007041c2c4140d945c0c4a1905072482c00c02807204134042424002d422504e4282890714090017801503452403e020301d403030517 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 135565404 1250 135564154 135564157
    0x71119030b100f0f1403030f160204140a060302210c2e030608150411131104090b0901150527120708240105060702030f01290904020108070302 63
    0x20010035188000003800311440041c04000740075148034941040c1c81c00da0701c05e070290b01d400000c505c0b03031f00708000b8610303c2d42001003036941c407540d0000807400d10030300d40c40410000c0040e0752042161001c24410841c03000202d400c800c3c103680c401d4030f204007002041003134160509400b0003960700903044801c02d03140c80c1c1803943c45892200404000e622501070403010040304001038050a0700026151802030010200411854240b000410443d0140c0c0c0341a031100c138040c8005102c1c00c0d1049086031011000e42d40b49810079038000d00303d41d11040d500c607a2151814000c004040070306001f45210000040e445041660a0300102c8090701c0d824504a2050700a055456000b4108241141e1140700403e0b1134031940186840c0c1180107000744101070800011070301c2c0070180d41c150042410190003001e42c41d008a07240700c0c112101980c00a89604280c40024145040e41034032296039803038107602510440d44464a0042c030905881a07608120f80c00d410b1001030881250081e001c5524040232610b0248650f0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 135566654 1250 135565404 135565411
    0x103060917041509150905061303050102040e040323090603060a090513021e0607020d080405031525080601230c01090b060306040c090b0607021203071119030b 70
    0xc0401c6240c85105500082076006500006954200d0844400803d41c12078070040141240b945401072015100c0d00007010408580200c5002d020046105840854134418200203181c0c880001d6444603180c400c241e128ac40201e8007980041c00007943d600800380e5041554810900e85050716281800020a02c1b02c0d96001a06094020a02040c0058528224442c82d80520100300410f00c0016042c0108058000303810031980002d000e106d1070311041d503107060488020650594080803051079608080c9014000c681c0629094010701c1d01140000f0419403070103100d0034281200750f614806503e00d65070002c03000618040840c10030004206998041c00c0d0500e600c0524202c14100c2c4102e145501d246900032065004080e91a030503007008104114501d2540900240c000b000c0500c1c281c0c9404031418064401ca00e0310380e03501d00c8100307000d132100801c42d00002d0300541132074821780c49091101d030baa9001d0101a2103138030001c9079000341c51608111800f01401c109902230700081c00d60711410300da0034014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 135567904 1250 135566654 135566663
    0x1090e01060c020d30030e070512010906110304060e01140103081b01061e2903090102090405040305190c08030c0f0c01090303020901020f150c0d1509020a0e01050c030301030609 78
    0x704110700002c1380340001e0b2503201c64075090021754002043d11400000d100e180301d801454140b030010a40c0c81800103200c821100d0403200100744007482c00da200c1c010005060040c1070f160619003240200445800210b004034400c40d410071208103080d120a080b00c4183c0034a40c1183d110200410104040c28058010303101408101c02d04410748950103800c489180e400301e401d4401b00028400900c454000c0c84c0d000300b88095103100341c010180c2c01402d956030104101d42c0000030102c01b052100409506441100c100075204001904181c18042e026402141000207450b401042c0200e200e88103042d078900031644900c3c0705045440d075100002e540e80101d915143d03075103c18483c0140a2109010b421982c42c0284c41c01603071482210002814152000b91242c007a0340100340450350300e07000c0d0344116400008082c0054995103680071080c040d00d540c40010120702940b0801180c4641d640d4000d141c1610300e0340307a0360b4042403400b00641d0180142d41445c00c0c5a042400104042002c640040042c0d5115 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 135569154 1250 135567904 135567919
    0x206040c0909050c0f13050a060623030408072d060507030e1c050f0409051f0b0901080711060907080610081b0103150305061509190b0a0906081b01090e01060c02 71
    0x80c04112041f9882100e40440150301d4190070051150003c48010865107401114a2500c00320348001a86110290001300b2400b800144c10b018880140d00c0c0c0301c5a003a200300c0c80c860600041c1d5100000481650082d01c141d850900418141ea0280c8035040700307454030724003500d0340c0e1400c0494100c814404140702800d0000c00c10540403038069040013000541a81c1400003054240386400307a10f082151b200000041c4803034034040c01410a20310540781a10400d00c1c1c413003100c0c0c4da400c008071740442e6005c2882006100c0c40d0244007500300081110f2045e60812022a1444e94800004440562051142d81c03050b400200402290341c8041c05420103510781810041038020002d0408248102207a1041c0c80540218041c00841400321110b035660040403207601c2001d00385200c0c41c001c41400ca000c1c0c843c05550b45c4070051026200d003d2104000c01010008220090340c2c0d0711060f841d502e044040760215404d45403940480d600030740610050300e1403171151501ca6800c1c140e0544141030080c0b400d80e8405030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 135570404 1250 135569154 135569179
    0xa021003270c050105040609091104050409140d020601060906080c1b030c0601090618020c01090203010f020414060304051c020f0304061218021f030b100206040c0909050c0f 76
    0xa80c0c450411000707014480300c250454050405508120050b0030603410810100700410005602034516405c0c0d45240e5000500c1d0800d850101d0f40c1842558003da030000d040c404642c0c2070004286040900f00e0709401a200341c041840e000300e0725100240a81c02c0894562441070040c507104595450340f003049940c800b49883d410200c00142c11801d8640c85601e58400140030b00d81c200c05004003401810492001e101c42800e0003c0c4078044010307000c1941c1e0082d404240c0c2c03105c08600350088103130380ba0080e000b04020315100c000f590195004d4061850030150b2038810703211500b05039084070310541d0840080d142c12461281000d0360103141084100440c451104a0a4001d10030300c014401001244c9800f409840320080810a68401c91303498075203402c1c00c24420015858026000b01050003c6070400520405038506600801803224041d4201ca001c13805890f0064002800d103000d580030b4641d40c8042079490190f2000c0e5011010020195040840c46010b44d01384207181c00e0499000a220380c1c00e144 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 135571654 1250 135570404 135570431
    0x1a0c0f07030921050d03021201091109131a0307140103051e0109020a030605040b010215060604030c03051e0d0909090c05030d0215060d05030412081905041503020304050a021003 78
    0x100c41990031078812805019881040f000304500500c10015086c194103200220980440340401445002c80954660243c0d241d01c41c030b908100c80301440000e00c4c8050341c0081d401c04000821400407140320b50090111400c60751319000a01d00b04441c0501c9000303031821021b0004401525019010740079088001c11107011043c2d10121440c041c0401c006c00503150f48900d1401000c1d1882030344114041d030702d843d040c0c0c0c0342660b0114000c00070742c2e0003049107030460b241d140c00b00c3d40e030384244c1d0b1000d005030b0040080807082040c0402d031450100201c40d64410050040d03a1000c2e240c141340e914a5011410403c02000b02030310542110300941d009801884425981c0d82c0400d0400080740840f60060700301c1c0c0b001c0e13014401c07240e41660304890162404407403c90f06669a039603074440c82c041c1042100e9516442c0082046144c01c4540d49428058116812482c0d00d101a045030030601038001e100394110b4012000c036100b032007501d01c1140c01c1002003000406580a006039901d180c401801019121152000f0783e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 135572904 1250 135571654 135571679
    0x906062f070b070f0606090501080606120c0301021308070819110109030212010c020607020c061c0f061701110f09090405160623030907050108070201090209070c1a0c0f070309 77
    0x14003620a44041e0fa010345000c008036420780e00304041080c07400c8d0041c01902d800203201c607031001080d01d1404107810b5441401d8948000d00f1019641580000780003030103403a140c0b04d0a000c44d01c0d00c00483d4413464403011042c1c0c566021040340b203004482c80800c0c10100782e0440d0030700d49046c0181083d4604a40300e0b000726555071f50070700303113000113a441d4a202c2c1c4c2e0940d8100509988900741d44094079800e000f500000d9090320418040b00c0302440c89000955030f00d0656070154010709a940000c01c24141c0c3c0341c0c500c5603161a40e500e90b0032a54a8960f8950f80d4000410488031510304541010f071a0040c00c804006050b180030b007050301c440c860364600c01207008003100440c001c3d014a4417140c0307811061044501d007103528000382c416105014003d2200c0f000d00010b465090752400d00340005244d403103081c102d006000032071000c1d520900c403205000110340c100101c98681d902a9541660440b0100d000105000050315000350540b8200300ca03007100702d810009001031600c2031820030100c940c1c50f01c0c107c414 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 135574154 1250 135572904 135572917
    0xc0606050a06170f04020906010c0201030b031e070e0402010e04020d0b04050103050102180303070b18100203070e0103180b040b180601080601060f110604080a03020415090906062f070b 81
    0x41082c0d19075200d03400c950604441c0d4491321001d4000c00d01c2c64594041790466202414640c140201481144110fa0007504291981c500180444806042d944607a14108503802040305243c0039031b49000c10310488076101280301e030744c061310344402d804054020b02c0025882440c1034030316581c1c0c1c1d026001d103969850017190b0096001d8000540c030ba50740c01c02c5014551014401c01803280e80300704203040c0020105000b1342d610001201c01c1601c007104100c1c0c0380f03081641800513036001c21720000403c038410360800213200514400382c0e000c00aa208000b0285145001c80c0e40c01382c100b40c001c000040c00251a480206c0c0d01503a40c2c0d40c2e0004900e08480c54514126081e0000c400179000800140b01195020450100c0c040152529030100b40d01249a95107420000d0130180c0309003000159000c0450003030301280e0051510013228200e1598403000280141c48a0050341c00d031600300b00700000c0c145e10138010801800624400c002480c600c803808170700c0038003d800d035404907806000c000140d0641d68a024040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 135575404 1250 135574154 135574157
    0x40206030411041b1206060806040209030a0206130f06080c07061509062903190905010b1002010b0f01031e0b0406030602040e07090906141009030b01080a020a0902090108070c0606050a06 82
    0xb0302141544c064405980320805032003031840d107030302040380503405101c040e082041a50016510340050340400e04002e54900c019401c980c001480704078a4038000b071030504035007241401195050b1506012540c0040584030a25803c2040c0018000700300341d54030100d50381705400e864802c000e80d50310118041d00c13090703800045c0446007550314a00741c07080803034040407151580760b110785140b42c01d04a410b1402c0d0143c03c04018036650741292020440c0941c089030309104014603481001030030340f10007130182800c0100c89010700f18a4446201c0c6501030702074082c02c92000600d40c5840c8001c00f0382080181104881c00740c1c82915244008013244a0b44020405401096410401850b111201810349030490340906d00b01c074500b80003004005c1e0004114292100f04503442200f08172a03102c201d03020042c0d5040a40402c8003100006a03021000440483c018426105000856503890700b42080740034808115022610300000214030078031404014901d2480341c0400103c158680e000305810f801d65401c08070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 135576654 1250 135575404 135575441
    0x1030c08030f0f1612090f0801050603151506030a0506210309010e010c02120d140406090b09011707020618150f040c0e0708040606050603090c150c1b10020703050604020603041104 79
    0x1003010f010019014003000c0000744544d0070008040dc2c3d492000000450800894001084600359000e00c2d06942e410024541c5449041c8a00020003c08050300e1031441480e6a020750311602c0b0402c0940056440d6030000b85003401004c0005403000c595042d503070303410403000b408448010b0790340302c0b0324041c040008801007403070079000400681750004400c81c1c03941d080f2050104200e1241e0060110307098403003000e81c0e5520740c3d40c0c0724010790744c2c003078040c800701c1c420710100b0301f0401d80c10350000701c407441013036034406007606980b070a00702c0e80d00ea40ba4001005031507808000018030ba4654800040d0b007080c4151900440c0c1035032540c4140460744290340394000034144500b40018048113004210203048102c98051850400038042540d580c0c620540034005c07580d0900003540c28040e41c5c16038018a42c02c40549010000505191810240a00dc1d561080745112120807049100048483c1030301d80c00301c01018151603070340812116420041c0300700d440191561841b05036494070b000380350202c1d840040c2d0300d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 135577904 1250 135576654 135576659
    0xe09060f030c03031201030c120c23060a2111070212240403201c050c10021309050402060d09050c04060e040201080a1806020f12010e01030c08030f0f161209 69
    0x19015004d16500c18601c10b40d2501649c00483c141e210000b0440b01c003083c408400b50314100c4440103c0ca128a45554084008110700c0710310b07504143c00c000c02c0000101c0c1c80c041d840011044100300e0305074400e45460100700303120f9a00103050100c023000d034075240201151240c101410038070b05084102c8111556082074103060008045c3c0210450f404e62180c4400319544000c41a4015512101c4ca20203c02407900c2414022a250091084518147e222002d9030010b100d8090090041e50002c803881d01c01944248001402c00300c6807103414000d65000702010f2400c4001c45a140180c400c01074241e4660103031001048a95550b40b00c1c9000510f400142d0808524050001604600c00288800d0480d070401d1095041402400350009031103500c0320f80140c4680345070844149c00e008407848240c0c04c041b80360004c07503182c448d8010103040340d10031040d490000f074891000c5a1a40140c0b400c4006141080c000d140c4801520700c094401c480714901101080385450325009440a203400c0044049801040107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 135579154 1250 135577904 135577913
    0x3120f04080f030a08040b04030c0203030a11060a020406300f09030e030114070c03090f08010219050717071104060324201c0c020c0f010e09060f030c0303120103 71
    0x420410b01030b40303001d903041108a000c050401940100020514807003100081c04150280000daa20740e5005001c1701e0300c80b49683e1003c0c0141034001d100c03502c0c502c038150000b5018800c1d0f000b10780503100580c0d1074010a010215190090800f10443c40c80c550101822100c9142c07958403580700002c0c60694080313400d484070300f000383c4280a400001070003039050085400380c0c60781601c2c186030130908507e09004a4200d0341030854460b0b86a800c240e042c40c2003940005810310f0150041d0207038555240d18030229902c0d01c041a101032103205001426030f0400500c003030705a22554041c0c6511401445411030144030500000c048910540049074106100c00a981e54107110003000c1c45040c4910f00100010500341000020a042204c2c3c544900603000542e00034225515584503a40b125103d410b102540340300344041e4070742c2c500c0240b4602640c610070201000d90301c10090202e64200180944600340c42c0c5400380900d0502e40d2402607090700c50f0746c4584555450030401080c90005605c030000382075045141 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 135580404 1250 135579154 135579163
    0x30907081f0c0c050706120212010e01030512070b0a050a020403020d2022090f02030f0c100504061e050c0a03090806130b0a0c0e0d12030c0918020903120f0408 70
    0x1c0401c2005854903c81c4001a000100702c1e003954124101350803001404240d00019200f0280403100440750305000007a00e900030800d141c140c034410303829111015024002d20005e4000d804015020400030408680e071801207500c1140c12910400c4d01510305a204d0300424580828142c046424107400807103a0783d40010140510502401203400341400c41401e922004d0008040c80404044c60b80d46034041c0400c00a00d20b02e0024940c090161001d021014244076140c40580344014014000c42040d031510a00c00c100300c809841503921203030340c035514042c10085200040000c10003030000400403010a0802000301140e542d1003070703949030007003070606d40040e0810703030080c0020304061590074000001803208141550300c424000400a016034a1003012140400c101c040c1e1074100d6801440c06061016600d0021041e01c01514140309039840f0140480341c0c0006886035405401da990400071011b0500d8001300000c0c10000c049070f0060304820045c03402c2e40d02400c031411900c10001001c00034400c0c14031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 135581654 1250 135580404 135580421
    0xb090d1e09030201031107052407030207020a0e0405070b0409150b07050601030209040f0c2402150c0d020409020f0a1106011d0a090b04080c161802030907081f 70
    0x48000544820208001d0507000e800d010090505840303111a941d09000c9000743e5002135082800c40b0200840713042c840d0103040e0846020141c20035031400160005000e8000c840e01d99501505e50300505242040407046000050006caa01c0d00840c0b0b00054806087c9014002811400c040014a059000e142d0380045070140d00190000c0c070305208000c003250020170f0745811a501941c0180c5290350354904145131201484005100140341c910216101e4240d100e4842c0e5004690b0007040c0400d0902d4003665564011541075a000c0480000181004000c6020300099030741201d0141c01e0a459141107400d03604054045504040081036a8007101c0e0720a0362031401000b810302501d065410300c61494405101403070f00400b0708840300302040d40208143c0c0818071aa41002405503281440e00d0613005a5101d0140f507441c40c819685104884019103252008440400808123201320161034010041c0d000144010384900070701ca000101c1100900c00450f0000b08404c4a281d40c5c555060319104950000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 135582904 1250 135581654 135581687
    0x3030507090e0103080f0702030f120d05010e0402030a03030b01030e01050408090a0b04181a13050f07110c090915070f1409060d1a1914040b010504170304030b090d 72
    0x54010000b02c1e107248106e443c80880240c5213941e0300300341d001181c9072440d520301c1441680b007030503659148811101d000d014220401c0b841404966603881c0001c60302e06003590041d5040d00100d095100080c040c0e401a09803070410705020a04d141c03107100c9542160800c0f903007a691414002024615450410f00044c040c10500c5092404c02d42490201103013940a0701c055000103655049010480c042d0008590016800070060303805a10714500c004040c0074161403525a00d40f002c40420701003130140300b051030041c42c0c5034001e00151042104000c1030481c040e00d10022401600303000c0c00c0c0c1d0041074104078402c000b079803036404204443e0b503002800c507144810303c131169120a010181550742c5100403a0004a00007601080720310340784825000c0f080401c56907030341c4004c483c2030078080e08261890140071150401004072413502040244400e41d1018101d241c0001c404000c28011205440d190040c000300c48400c03281019100d07134900c0c150b078405840b01c91540e8823012513583c007264445540290302018 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 135584154 1250 135582904 135582929
    0x601030605060603071b0f0602041e080c0102120721050c0c040c090e070908030309070e09030f03040f0302030d091103010b010f02060a1d0703120f050304080d0c12090303050709 78
    0xa4171000744050855031019048000c080b032048148612001c002c1c0001d60020011580e55036200302c2a1454180c80629418501c00b41200280710000402d40c186068030680107410000226105440a40d02c46041200c0034101e020803250740c0065202a0381013150310b511901d0391201460401e6161000e81003600b8402c5042c04891203240b54061414021660300a42410481d25445d00544a5158036000320007184404010080302d2000004c1290859204002d025600d8542e914117948034032070110701404500301000400c0005250400745090f071800780c07058a0400748060b00d0801500c0e410602035810010848010071540780078450051070380030909080d40401c10901c03000c1c1d196440245860f18040d0780b110303001d022201e80b102010324524400281c038403040d12480d102203107002c041c00400010358901c00d1010164003480c1180e008039084117006080104c1030350290098092070340c0040401210400d004104000c40c040e10000c01d103c2e44002c141c51515645c0200582c1345a0300014400c101c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 135585404 1250 135584154 135584161
    0x90614091b060c01020c0609030406092102010c03090902030109060518040f0209090a0b0a06080d080c09061305060d0524060403060c05090a030c08120703080601031a04020c0601030605060603 84
    0x60194100c1000ca07010389010f511680840389090090046d00c80c00314690251208002c4221000300c010700035103003103031030303032000180c079200c000801c0b00c0c481201038a038059410440e80503602840b41910720921070319122482588a010000c00d98000b0307070211800742c2d00e03500c0910452070328800c21500c10b800510f01441a02c1e058955521503021000042e00a13004100030a9501505102c803420058020004041d68103018510720700510061054904034060303110540d40703032842100d409024058480210303080c0340d0b0b0b103000c003e103d9020303102d10700b500c4600f9000060b1301e868500141c01d148202a60000350303460a082d01c81c81300106000e8540c0040d40e6051058165501c0c1c2080d5002d0766000540084c21049015081d6543d100d0340c0f40043c0c2c4840e08420000130454468201c01c242c660001c00c1d030321885d52403034003003607940114200100429103000028002d5442903110503200850020014009031100000c1000c03030340040c020651681040c001030003801040d020350764105400b922483d10b54603 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 135586654 1250 135585404 135585433
    0x603020a05040b03030306130b061c0f0506060d050a0b040513060c020d09170307020d05061005100518210106050109210807051005070f02100c0f0e1309061409 70
    0x413001301f6091150112050181c2c0800e00d0b81d111104550014041703c2d80c5003014032100d4194035020403490b403414200784145040401a0064501861024000c181040c0c4003409120103440f0051500c4031380c80d030b54102d52500da40d681c064a4081c05105103e003048001ea801c008040e00e8043c403d84040d9841070714100d07546035205c80400304807000414141241f44004221a055204c2c3c020065030200c0e0052450307050203000304910340101c0d1100415840a584c0d0b00038001c02d0641060203070046038090250340d1007142d80041601411400424018201101011203120711070075400c0d60301c9aa5484a080c0700301c0d41c001c055803000d030640b400400203940c4082002c8452450042009201d1600403858804000081000c0088003065078420310440c54041001000d000c2c202015000501c204072066a41030810b114003000d0240703568a94100404e24082664002c941ca011160072040f0b200c03004400c100588501414144545401712362805214120409884044c008074102c0d00688000007a44 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 135587904 1250 135586654 135586657
    0x1110307110712081207030b0102120702010c0c0b0d060609030503070f050a1a1e090c0f03190b0117070b0301030611040b071a22080903011e0603020a05040b0303 71
    0x44000d1401d04144008100a10305140d1194000a6011092810b8000f08003c540143c007981c00304200307250055071007240440949154482d1107015810a900b50b8038580501030081c00841d0040c1040440c13001d45642c3d0920f180d82d581d200c01d82c1c2003404600203020000e54021100140940e207440506541503445030350b242e10650400600003590f50151108020041c0b04503903003290131034543d00d0141071140c040300720b510007161184200380102c0e81c500c15400032200d5882c020a50800103001c4038040005210481d561501856458410000c00d241c2020001c826001c000d84600000040c5524100c40020407120010300700b161130300a40d0050029403c260706803030441e900f2820115020700303138190840940c483c54000784800f040010707049040c4500407000760480081d03e919034989555280a181c801d801c40b010064480c419004418040350801c0e025100a4400400024004800e055200030321607049001c00e00ca5501c0c0c0b0010415841d144480000510098809010f050400030020b9100e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 135589154 1250 135587904 135587911
    0x2090a02031017030c1908030f0c04090e010b0a06021504110f040f0504051b0d02010e04110406090608070f0905060c01060302060a031505030703050a02130b0d0b0402030d02011103 79
    0x1240e020002464078800d075110980100400c04001c1d40c1030f143c1121064407a030100c0b11000c07192040300d0300114440400907860721099000074402d42540c4500c034100e503100b070024044140780301040c0070201d0310b11051b00c0703500402072001c030002528075182410301907507480c290b000302c0654100d1024004803034110000507034015070040c1496214642e084c0000d0109007a103c01d035030011b28000d030311000c01200d94000c9002d00c0c0140103c078218103127002080d002440440015804c1800580c5202c015405056501d41c0d0300002400031078061004c04942c00140c00651050001417034a41040164640040140da002002481d203121803c61f01c94014184141501c5064015100041e01050419007940100013450340281340a41e215802d007001005000c0c41e504c08aa4201c40c102e0001c0d8603d4009030580440c0d0348038000d0b081d0380855400b001003001408207544000c1d03880b07440520b041d079210a02c0401480c480e20038440a4105801070503d8440301c0c050b18410b5a01d801c0184180c02010400d9035032 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 135590404 1250 135589154 135589171
    0xa0506030d08102c09010e07050d1a0408030f07050304020a03020d03020f070905091213050f120d020304090b06090a050f04020d02161205070f0609111206040209070207030209 77
    0xc8689400c901c0c0381c0f0121541c0c3c403030b40020080700620281c40740c1c1801070018140c2c2c0143c130300e051922514000c07400c07944290a5174000c3d41c850603040100741041601740034194081d01c4106c80d00b80d140d05900400080849007155004800020130040380c0504410940044617858001e0441c0381c5035003c0784d9600400d001c064810b510341c0da0107404040c82084840700301241e513029580c1183d81c407291b04015000580d1481541d0140c440102d560030401d40540341040e141c4401c2c818450714146c00d00c0000780090350f0460300650201c4003034039200d004001702d84c140c4c01c103540115600c502e882b00e0710003110346603610a4850142004504107550328843c00d441510800c0380d02d450800d1002c1c00141c000c1c03040e80c500750415400400c41240511781110398450090150f01c5030108481d280d00200c810740b040090003021203c00100000103c0c950b5404400454450014031003c400d907480040c0382c00c0d1210071f004080340d00690070070086007000501c2c079802001500040c00900c0c10b550024900351802081c403038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 135591654 1250 135590404 135590417
    0x5040302061e0c0d020c03030a0203040b0d0b060f18041b030f020d0f1406030106061b02010e09010b03070e09070c03110705090405151e0118110f0c060a0506030d 71
    0x55080035200102c0410708040d415950b200840c1c0b6000351568540943c075070143c056210f0140c201c1c00c0200855004100a9025600d4580ac000300f20120340c01090311410700380e0399003090313581c0e503280e00005014198803101c40030b031180303c0f881080c421001d40038031181c05036041c00d502480201c0c0052000843c0f240c3e9080104550003181c000000900130a407024007814100b240d10100101207038025004604a50410185c175502c920901d426901c080c4903503000907402c8600d80203200e28000401c0074030303803051520129081c00c450025120080c00c0e0016000c101001050010403070300004e50036107030a0203456841c02c17403801e03c6000d0500c40e0b407603101405004441034000411042130040380003a05004100303241e5400c050820f02e17901c1241a81140400a400001c500c1c0c0320507235501c41110141951b00310145a08003011008102d550305045407005807681c54103000c0403040c101030301040842040b03140d03c42d42c64003099441e1400152804490524040520420fa100800c4068001e0020f08084 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 135592904 1250 135591654 135591667
    0xd03120b030a020406090209120d091a07020d1a0702070f091509050a0c080f10060c02031e0f0d05160204110d0501061e030b01091e080102030414011103070504030206 73
    0x703400d0401e26907009511500d04640801c000300141d001d0624902c05541000400a440c44200d41c1c2c1d030540c0020b440464408042006004c022112440040d070001610b02c1c01c0c41d1444c0c0c00301c0d2402e084140c0485d68029500126001161b940229592241c81440140603030ba280c8400700b5a11030507409002d40c9c298070307035455224800e0030042242c002d08404808001c030b841c103141030400501010500e10f00050443c0b0100702121120341159004000021010f070300340e1725008007030b03840b0715448000302d0309401035003d40c15500d14482801200b0a407124003401036040200929410943e45030400414000706000aa0240c10039161040c00303180e043c1c50005044150700003400050141084444078242020000310710503502c090f6200d01c2104018200c4800c0c01f10800c290103a0300f108079000e0004400c81400c0089009582011114208032031500502903210700c1c0759401e90b40221800e4801c5000c8000103200c0322824810000d000c4107400b0700a00b182001d0f04c004000348280d200c00b03849010045040e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 135594154 1250 135592904 135592909
    0xc0a09050a02070227010618060f0c200108010603020c1e0307050706180b0c0307060b191d010605090d06020d0212010e040b01050a12020418080c0f010b0d03120b 71
    0x44503c959002030911102d80c01c2e8000307012078801440380c246500d0307404100000b049401200c2000384c000c001c000d07514030a82449001c40d005245049400c0c1086000304030728000c5021640d40110801c80a002680c07106010700000d0030702d85043c0d1060381013500c100540c2142c1440810101c0403041a0340c070184c1c00c1100150101c1c61401078590140c00b900540000180650700503c080c61082034501324441019a02c500581c014020740a201c902500104240f000180b01c65111650b03042000380306403c0091180d203030f0001104950810218028500e1504451000c4104003500410300b92420703038600005ca40c04114841c007010001800c2540101d110b0750442c40c503406441d070003001030b40542c20542e0b4440460001c98010766054401c441d01c00004141030410030001800d480031041d0350249910140d007030000910a010b44090a80c001300a81e000107041d01e00103120981168005240706030024100300c4c21920f254540900c00c840155952001a40012140c190b89090010010340d40c84801d01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 135595404 1250 135594154 135594157
    0x15030c09091003020a0e0a05010906051c14060112020111060108120a0519050405130509030f1308030705030901170609010306020a120617070909200102030f07050a0201030e0c0a09050a02 82
    0x4002c0d03000105410104c0c21446c4502928031a41602100f440580d80c0c0340076070000c640281c0035090b0000368400c425a180300c1c005503140b2905c1e12030804d0600c02040208510700f03081003a080b002e0a000300b9046c00d415503900040c000946071001c8080c1a155250492082e03440108140c0791124420100318001c08030300400c1a28400302074060008013842040c1801411a880360081600c100e0105141911080e041c1c81070511403024800111b00d4807140c9031002080c0d4008450200b1860b8601e180030031041c400780040c0c901c161091000750344404180001420300c0324104d070045880003150040041c0d0769542d070041c5045035000340e0b0050f652020010212420703040e007943c2c43c01c1d0030704203180012490b8031524030b44401102d030001d03075003c940c03605021001c0c0c62042c2c0c17001e41000c6031003d000111b00303003d1016108821050040b00e10b0881d012030b100046401c5003100341d4258004080140c00d550b00f5008208802c201500901500c454120008120400a002d1800c08696900001e02150072560 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 135596654 1250 135595404 135595409
    0x7090524130603050601050a06030c0e0118080a0b040b0609090c04050a23040507061818020c0d030e0705010305090a1101211e0504080a030e030f0705030915030c090910 74
    0x1c0e014000141c684c245555130740d0084c4100383c0100c1d484440080e04070f100381704e5505140340f103aa50b14000105400111006101600c4130704c26190240d8000034074a40c10001c01d031401d8810080502245070508203c2d8001360300034041d5004403203c030704018810001103582d513001c400866000400303448401502c001040c40180c0b0041d007001920501010b81c8100400c1813055204800b1601619100c01d03048900d0702011548070360040c0500028801d0003280c80c040d0b901204501c07401400c0145880840c1d10b05044107001d03602017691141500703500c440038410440500420f0905110500300716460340d40e5000b0b40070001c5c1c003030703c901600c0009903071042c403160100c111194134040d02800f807203071101e0007400390101d40540803001045500c54405203000b0144641e401420440c1440f02144080d00034101ca200d190105010400a0280c0b480002029100c201c1c000d40042d5200c4410000348920089203291031502513500344108481418000220784450744180c0e11404135031100c015a03081c000d8a034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 135597904 1250 135596654 135596689
    0x90606030b04031d010e030d050d021e0a020706030203060618031c030f0e0d230c06011202030d09140d080c010507080907060f080c03150a0b0a0207090524 68
    0x10061006050f130000040100c68a003000b04603203101c0b040c4c010b4030001c40300800c054054004000021005000308080d0248114404015140040c00103c04140500307490790346503040f4000c140301007410360400070b21015000701e040c110300d5418203400081907402504220303080d10200321402c15094900f030003620f42503295681594016188038034082c000c3c203802d050740c500051070b04500c070682140005080d0f1004146031261400d00d41c01c81005188950b200388060340c0b034401040f803580e0000c81088014000c00101039000d074502404d20400d81405411420f41c1d081092418041c01241d84510090190a4084645140c041628580042c0ca80164820b402165103414200005030b90414007041c0312f1400d04040c1c45143e601c412050b58420000b89406c0d00003821100040c0b680c0c007041d00255003096a441c0b00812201d8010700040d581e014035002954848004641c040300e46404000c1080604901d00041c0480e1401c208505e03e4007100480c03281d065584081005150740302ca854084407001e50 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 135599154 1250 135597904 135597923
    0x90302010f06060e150306061204050a0b07081801140126121306020a030e0904060b03031903110903030f03060f1c02010815030c0d05030d0c03140a060e040609060603 73
    0x41d0580130b440c5040c070b040c00368064912020003130100c50f88401144d218000040c03040d810880d0b04503505003c880300500c111102e2180c0396140011448000800c0e200d442d80b81d5405801c1c0c540b400b07085010060750030034002c881c1c0c100f90f8400b503c3d200310240310741519408222100c1d00c00040c040d038074a0403441000c503141c170301480e8900d071243d20510f80200f035000081400360b84a1940c907601281e5032a80e0640c0074000894030458040c580c9801024240c0250140e0000700d000c508072000642140d10482c1580c10604c2003080c0d01404a400d030050014017024900d8041c18400a400072039240d02c10302d0810110260000b001608035aa144001744159401a00b03c510190304910f0048000f4098103043e4049509a000580d000e001c110444a5442c0702901030603010610130140320b001c400e01e1408a07107501040c1302d60442e800c3c441c850214107507160f581c0801e1040d000743e41c03405c0380c20014041001340d03414030313005200c01c500c4143d8164000342d00420000ba850309504060005003202e41004080210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 135600404 1250 135599154 135599159
    0x20f0603040c090b0d02010f11100f2403021c0807170703021501290c0d050a020c0f1c0c03140a02090c040302010c080c07080109030507021903020306010b0901050705030d0e0717060a090302010f06 86
    0xe65034404411233224801032005010f60a80c200311109291000a60000780c1d03800700c0c49082c26080000b81c3c2a80300f18003640c101420766841070b490000001c43e0b4040c07100c0229080c400d141d4100844003101125034070b41c000550500c68003c4290000445d400380d2503801d0103c504031506110101c4020950301c4c82074a00049010000a0007548506a55801031051559480c000d191203445d902480c10024031000c024107100341e550f008110381e0241a18232041c0b6120000208401c4000e0030384640c00300c3d0242c00f008426104008100c20302900070101c0c42c40501007800107076000380607207480c1d6422117500c80d02c2d600188003c40c50005030740c00a55080d424529540d003099084000362030098400c032140c14540c035041701040649030145c44040c7d855480340004000000c0160010100c1d04010b1400c5440c0c0101919158519441610160b640700e40c1d42081c49281c200c10f003c0340018060b2011510201d01e0000c2c0c8007903944001902015620b551036203182c0415000758040208001300c81c0c01807011b02c0c5d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 135601654 1250 135600404 135600431
    0x1009030b010806060906040b120a0602091008040b040605040c12080d0e010b0a030b0a06031b0806010e04080a030b27180f19020f0603040c090b0d02010f1110 69
    0x51061104a41200142002164030040031400d144100d101030406165962034008000250000d90f05180d04038075905000d4801e40803d104003200c4600030a030150b5100407410921030000c81707070b412580812261f4018040001c5404a8403078009411034030204c0c442d141c0c0d0401212542d003e030302800e40e04102070324000400000c00c000e80301009a4607000c2014100c02c48509098943d586800c0e0ba00c071840c01c10600c0020103000780541c00403001100000d180f6200d03920b80a0000c8881086104110018010802c50101300240d5002d483c03030302e8201100741032a943c0d0080600418800b0420b2681303441d100000303070b03c43c200904151031160728010688414460144010b074029507a0b40c00e01d5110318204004140002a2050b042d082c110040008111607550340d441d10b451010200da0010800540d54940c0d507600b000386006070300a000346110305240180f032008490824107101c0c0200401d01010300940c1e0489400521505941071142c0c10700b02c60404203080005210510b03007220f141c440c181071400b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 135602904 1250 135601654 135601667
    0xc011d0a080f1f09020f010f0306090c1e02010b0d0b13080a0f110304050303071104090615061d3607020c1314060607030212030f041506051c1110 64
    0x2402900f900c000d200d240c0d00d22980030341e0b0114502a41184040150b43c3c00c42d4841c603030b030401d065054500011465114070030002990f88401e0007400061070414000081c1c11035403660074401d003080c0000c1107016a10b0b0041090594020005040d050311000018401e808911a1f10101c1764410070f23441e6a800c20520240444404e10850f6000400d411282e0221010000c225001c1d00c000030021070802c2e00a0703070780718101000b006183c0c0d0001d803281ca44500140c0c60740100c0000962031810264202c1c1058070050402e601e070034240500040c1704070803040da40c40700800310504003854034042d503005904a0342c80013500ba00c80c011241c0e80091800700408241d0210f03401c0382b01682261240321228180404000795080108805030344418200822520700d481c00080ca515032290041d510703a02071100d19111582c10484100b071002c8800401c1108014980340c00f000070002000e8100302d020309000c040b4604002c8440e0480c00151542d003a107040c045290741884070b0b4013006000c9652800d5000008200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 135604154 1250 135602904 135602923
    0x30f070501050601080103020915040b190810020301140f0d020d050303190504080301060e030703050a21020a0b060418060f0c020c0111150a060902131401020c011d0a080f 75
    0xe501e00404140f61358803031400e007812250000d0070605541c5a99200c001490f8070994107d51066071800807003650b031a0f0502d04213401d2601865001e02510780440103051010059984407410720420060001c07003206020200101000d5400c8100c900e12030010901400503580040c2d407280a0340d24007801c000e4008019403040701b075810a001c2141203c0e041d401070720030594006001c0c1c1024001030207180e1051402c060001c00040c104d84442d6540e840d0175091502c4001c09503101c4107000c1c5124601d800991111611840901c010040c0710724030389401d0301030103000c1d11003441a52200348000205941110403a030340f54200c2c130204080907880c44100001c2040c002c02c0000342c05110951a507a6000f48010414a40224080d2144070b100c414030902161000349407100c181d558500c007041d02c64107403026141c400c1c800e40d01c01c00c5d000d0502c4ca8000107400d200312068110340c000c65038003a86907403180700789004c2c3c0380c41d43e0f80301f64500c0401c000503130b140d80d075804c0604141b00d02ca500c20038094002514650 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 135605404 1250 135604154 135604163
    0x82203120e0d180e0105101707050301031a06030307300201090501051e0a020906070803160e19060804060b0907080f0105032e06050a0f0305101a010f090503030f07 72
    0x1c03d8010f422a0040c0242a0f00c504602d21a0034401001207085c03601440651111525000c0d1519001181103890038800303407001000503101100520402034402c03035840810140d1000f190043c5482800641d0341d102c1c2010080052050800802d090005034807003c5007900d452000801440e20784030008c2c000c0c00d0320002034929600b0300b0041800c1c40611101c04182900800c1c01803600d80c1d940d204e20303010b940100c0101d03030854000c2141c0f1020440610140d80601c02c800200000f20716030342e0b03005001400c542c40c80e0b40304081a228081c4401e040350303a089c0072a541c07070421a12651340c504000c0003c142c4024640c0d0040d40400c10081c20790f5100039514811400d0030040348150744c0b44d006050707890200c0c0e1070000da5109844800c0c2140c0c060418030103d402010100815059129030116564000da83d00c102c01d01ca812000a0007041800d02c0010351908450100300305085188a1090b01d0b0404003881505114100f0385801e541440341020700050940a01240c0d030310b2188403105601540140d00540303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 135606654 1250 135605404 135605417
    0x90b03011109061315111b0f15090a0902030901050718210f06050105010f05040303090608041506090b0f04150b090105040b04080703020f0102030c25050d1a0601082203120e0d 77
    0xa644c000e51410111f450802815040c1000340c04000d00a060b98030346041c01c3e400809018028541d03a98202e040040c0001d20009038a0b410102502420340e403028108609101c1107111140c0d4940080c0e502030304681d6812021040c00281c100e51511821107500e0240158041680020a12880340c102d00d0403210280d0711030400511601d000c84440c0a9804000d000400320a401c01000d4840e0b108070b03070400e0154090349903140c01c01c250102111603681c041a04030380c03190200700c003914000009408034a025502405a4000c5540d070043c0042503002d81200302c8004942d21900307900c030b07000b0384000e06070007010b075581c4940b9507200507a01d8129200803486141c0500c032101c525403000c01a02d00f6414004005c0041d070310342c40c80310701101c0411071050904d2201c0040003d2965200801c5044103801100e4200581341c02400c2100400e0740200f806050210403418030900c4503e102c0701c4000d081d00000d0140320004e03541380807102c51112000c800c441c031303041100d007504c0400702142c0c00280c1842070f252070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 135607904 1250 135606654 135606673
    0x4020f0a0f0503510108060d112106090a0c0506040b16080903120d0b030708070b030c12070e0102060a11070609050703020d0b01090b0301110906131511 67
    0x4890343d2000702c4001c4a03c0035400007502921a44e078815082c001185484084041062101c119803040391881285042e100031001000658100391066003000040e500c41c0b001c1101c90f01c42d84690300c09401940e002c1c50518880d00e07407a890301d0a4007800d08510300b090301c0c0c10341031103307a05554a44054098443c00c010b0800000c0d2840c22508840803240f500380c81e03605240c1180c030880c00c2e80181071415210900c0412135070300d45a5040c008070300800c68907298240c44e240301d4000c500444540c0100f1034042d504c84501031003407903400a6000c08031355604644641d255901101c440140c02540e08569140c8086c80c02d000c6078540203076103001201004e07402c0302c0256841c001030405440d1168028a1f80007010030095010850b6a0440540640101c0071101704070b45d41d9011a00e881424002514038811100040c0b1001032580520301071010100c0013485445100e11180d01188207a840982c452800001d59030605007104401000a002481d02c0c0d0b084d01d19084c1001d01110080c0c40403804600900c0c550303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 135609154 1250 135607904 135607907
    0x40f0b0a3005150303030a0c030e0703020d02061c0606030203090f01090c0611030c0d080402100504300b070e0f0a15080403051603020106090528020f0904020f0a0f 72
    0x1d00e001c00088000c0c070341c11459200140002d100161090391410b4003c1c8980e02e441c2c40801c01113001c2e0081c0d4600054030003070b03010010300710348032100d801044d500103c4040002d640c3d25008035500b103404a4845907a69411a8803010312004243e16924041c2841000540e140d055030103113124041c0101545d034160340690040742200c2100500503c06003951005201c5148125000700b500d804490483e803030b102d1900c40c038070700e0403c0c400c4185001804c000104021420182c000e80094186820a10700702420300440040100d04140c8003a229580c0c4030a908100c142440e0048419030000b140b006a4100b9603401481c4a014050450160a0046201c0a40d0030242a58401c40f00ca690740022a0900014102c544c804080c0c0f06034204407080c00072030080145412502011032094000045061910300c0c0ca6056560041c200c4c502c000341d203003824148000460b1030001c1094248001a9592240d020448031400b803428401e070850301c04900d441201d002038004244001c2c481e19100c00003040280c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 135610404 1250 135609154 135609197
    0xa050c071203021c06121e050d0503070302120405060a0b150702040203091606020706020d17061201060b07140601090b130b0d0b07020a120306062102040f0b0a 70
    0x30041807460303155460765205120358003400c80a1100c0100c070303aa10712018820000d4030340c140c1040c140000107000358000c000d0034200c0460b80d030400c0346419141641d41e40360a9194565807050200744000000081d0016200c0e9045030420069004001081c0c14941443c0e907944a0844030141840e1410140310b00c41e00d0041040e2a50201c020310b0070b854107401d603007403201030b410203080b058052040303256a1403000d95010802c4040c090300e5005040c0d552034044000e10f0084100c81c16410320190300507004040ca01c1c01030043d40b240f02511001c02c000b0404400d180144840c0d4041d8850580110707281e0200038812554217030403132a140440b8000c1e602c40006c442115003803000294450020811010106900d40080c03807a82001880010f40c40ca841d1100e070143c0804517031440040c2c007d100c0e00380400420301d01400b0702207100c1c81c0030445141071400c040e00d41011940000d0041c4c1145003000c0242155030111805441400c00d03e4880554982000702d543d004203c107540404c00303090203002c00050201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 135611510 1106 135610404 135610417
    0x9041d01090b0403171b1b0106180e0f070302091e07050304020306311110050a1e08060f1c03080105150c0706210608060a050c 56
    0x40d00420000003c00c07100110b0480d80c0034003007040c0d8500d070702903020740246c1030301550761031803c2c040003404e4209161b401c250340c00c100010880c110030000d41c0c00700d12241441484280487c441c80b13500c0d080165104e40c1c2503406542c04101610b001030b40560402c1103d44040bc0c4010351501714141414101c403030340d003c504004280821030600300680340e40050100c4485000d0b0320343c508101030389650b400d40e100710500820399520521070302042c5002582e10040c0a04000b200002c0058820382040918202242402003180c44061203241c100380c240c42c00e961580324544c4d40700700b00220084090345864001091b40c8958143c034003440009038499010f42c86000140d80760004000d08001d004c1c0a59006000911100d2611000062400e040e26000c0c1848915034441150300b040181084091344201d6080030700002d0390b0b09000c24005e0040c202000c0c1070103a81d1314400ca600d054400c86 = true := by decide +kernel

theorem cover : BRFrame.Cov 135431654 135611510 := by
  have h0 := BRFrame.cov_init 135431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 135431654 ≤ n) (h2 : n < 135611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
