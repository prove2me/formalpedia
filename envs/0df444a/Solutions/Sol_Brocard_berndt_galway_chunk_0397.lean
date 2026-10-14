-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0397
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:36:24.347235+00:00
-- url     : https://prove2.me/submissions/38abd99c-7b0f-431b-b021-5e471f8d4996

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 71223023 ≤ n < 71402879 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 71224273 1250 71223023 71223037
    0x120305071b061404060507021e0a08061515031611061e0a09020d060c0909020f0405040605030f030a0e010302250501060f0e0a0b01050f03010305070501020c010f0203031308040902 79
    0x101004010804190030183e50390b14000c580300d07010704044c60048042c10b0791061010091181c10b52444501c03260105144801203e100034004d40b4066840c1d0540c1c0c1c1c6d980318203441c041c2400c801c442084441c0d1510b118002c0d031403d070941180e425625812007400c903040c41004004d0500074500681c5480702c404000191040282d05200d0030500c0c20940480010200508160b0609042004070130141e1a5444098800d903400a40024680401c5004850802194000d0309207103000040780d0700140e0304000a003013596400c69003048020742c1d03401055565036161400c80e089030410310601c03081c28011180307544040b00c1070602510b0580c130070881188071440c80c0d0300c81e41606140c2c0b03414000d109091044002801c800c920443d0218107161404404100c0184880c00140c4c4611f0000000c2e40724a0907901d00c1c4036095086502c03542c50b4030308607450300c40364080c80340181300f100e014215035840b031441da0030101c42d203401661854031080d00071585009140300a840a1000b00000a114800b920062200e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 71225523 1250 71224273 71224313
    0x3071703030115050406051e1905040f061e0809010b060c060a0b040203070212031306022a030708040e0912040611060109150e07090b03010b0318150112030507 70
    0xa030b0b40c181a0a4a801e500d150719007010042d06000c2400950781280840b600701c8803000a01c80f9080f449501c4280c54401c50008000390070010050f14540d9070032001500942c0e044031081205640c0321107048030035001c06002c410320282898010b50300d1368042c2c004142c015215400209600303081d44045012907108016049407548a50100b001e5014244960f000d180c0302203c06514609202c0d4000313507126840710140c4803850001000c1380080f85c042129110701c07a031000065445030101c0162108440218075404044264030ba40030311402004001c0b209499404a511400c15083c000070310a000e5000300301d90310510a45019080300b04044011b0001000c0c566540075110200b141c020b410080180c3c0820913107403c000280f0001c6010768500c0c81902c4000280c8503003503881c0030084551060780c5d8415024108008000702d43d003d060802503104a540030514004000d07049441c950390500d01a088070b01451200040c070000d51070740a00e04245001c3d00c6d119040c42c1d003585400080f28880108001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 71226773 1250 71225523 71225527
    0x1120512071101080906060906040e011b090302100903080d050618190c110607210f0506010305010b0711060c030912010b09090307030f030b06071203050106080907050a1403071703 79
    0x340d5130303014a10701d81c0030350307003501034222805c00c4000301e044100d02a1100d071042d511105902c400340c20075408005040240031614130740c45402d000241c415103440c00140d01486030b1950341c5501c5801141e00fa42200e0b403100d855440c006429860f0002024040e00b0395510640b056041000c80400c3c10090f805104c0ba60340d00000d8180f0056940c0803103103800000e4040c04040c500036a032800c07020030550340c84521408d0107000359180d0705031500b4554542c880022014a0060040c000d010a036220500c1080e081c1c90411259884408004035030150000040a4101103100390f03441d0308150029098002c5080d048904000c0c02500143da024844d04882d01c05030754075a100c100b203140c150b0480ea00003500304081c40c075119064400909800340c4074054014191141c42000d1141c403800100e40029400580d2020540414100140641005c1c85824005603842d40800c003040c00c0450140d0450300020281500c0ba480c14440c0d075155808180c11560600409600040640e02500c190003e900c004000d99 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 71228023 1250 71226773 71226803
    0xf04080a0b010f05100203030609070c050a050601060f0302030108030d1a0414190b01021009050304030b0c030f0604020f07260a0203070b0a050121240204050301060806060303030112051207 83
    0x140d40c0c1d030f07a03551041d0f200e080381c406215141ca4000c01200d401007001c0d540d40d48560f60340c0005464a00b2011b00050651280352078030014000b01180b098162859507a500044221444080b03040c0d00080c02069090380007040a0824401541d0004000600000c13105800303260f1000003034112000210398083c00034407001003104014900314140401a02e001c0c2c200250010440000e586030300c680d00d01e03d0704a9542c10101c0c01d115040058800a65210381c8420140ca0035a01c04031041d001560821000204400820002d2401d802655041003c80a05a040c601e460310384d110f902401000c00d050200c0c60341a40c41c1c0020341e010060035005000e80040d503981e089490080c150040040240c40d26900c0c100040c422205440001500c2c65400300d41c01c2c40380603003400d0042100400d83c21210031440401281c80003920300350003410840344100d0003040000e40d1032481c65195001101c440303505400c1040188035646500d02c1c0780b00d229000c2c0c801c950f03140c100d0303e00c121019800b00a040d0340b841460900b070303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 71229273 1250 71228023 71228039
    0x5070c24020f0313180609050a060303021b10032406020c01020d09050306042003010f0b100302040e0106080403050408010203011e0914160e04110304140303070909020f04080a0b01 79
    0x2d4003941d1110000710315002e4031030394500d00c0c9a094041c20900080d0f1840c42c01c2409255000200600160503007080700381003270240039008001e2440110003601441402e501c8030f020080a4078014a400742105030100c8603003008800400c800f0507600d40742c2c40712464008254449003e40c0000c2c2c0340a400074200072211000280c03400b5100300365442084407140003844581c801007146904540c0c09035904c0782c01d0062455080d102000028070642561030018070101064007170308101508501954014a441c00c07148044041c0e1007213000d40b500c003030301400c01000514032900019511034000d140007400c007500c132202d00342a41c2c42039104900d81541c0c0780705060142203090303070311004107141c9404000404c01c2301c0c00c104900800078080d0429540c19040c4000f101e000d01c1010800020080c010440948079151060765500140c2e030544414172010400b070709501d000800c43e4003a00c1c440d1600600989883c15400107948880d00d1512019420300c400240c0c0c0504104000c00d4610400a00a4a606080079 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 71230523 1250 71229273 71229283
    0x80304180518030a0c0602091e090105010c020127051305060301110c0a150605060d02070b0c041a030a020f0406020c0102010b0a1202010c0f02030f0604030306050109030803010605070c2402 83
    0xc00001440e81d129031040c42ca00000071241c03000c00718200a5440400780c100034000f03004003c0c00c1500454101d5829000b011a61202103007100e040b2442d202590700c800046900202e100c20082c085031007034000240540345151b408100010040c1c1604e4800c4c0c989010844494460880e0781802c1c1c0c450007841450700d000c0c000c80c044540c006441d0b41c180888103c000ea0b854407115405803205001201d60b9200524580000020b0180134000b55a034060920500c070083d40015402d5031740d4101c0c0c4000c5021040c04004a40841d02c0e4000e403680c91030103a86d1860400d6201615204041da070030041420078141c4000a40018206a001782102858140019003525100060a44140402182404810241c1908200e0f10b9028a040c0014010714a00800080150310010303600d44075001001224580c0090502d00c203520a907020300c485039a0b00010b603503416441c000244065810700041c4200c62182d4003030501d0902604101ea91a56200c40d5500f003451495810500c0c0c03025941c40030422501000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 71231773 1250 71230523 71230531
    0xd08010605090604031506030c0b0a021009080a0503070e0301050420010804170a0309050f010203190504080711030a020a06091703090a05210607090f05040e06041401060803041805 79
    0x81082c903010091000540c0d07403156000082006c01c0c96041d000e69001c940e440680030f940e20280441e4400d0301c600c80f0121325040b10350040010b2064140c080f0b1024054028200801e500803a068104a01c8810580d440d0300028613200800159000c404040d40c2c0901413030303012780e020f03400c076005161103c115480500c42e02d1001c2d0b4140040740c011700000840540f100c0d801c8513038958440ba15800d0000c0d00310080e26207880d0240403031082c210b1500c04200190700450060f1540010f64081354240c502003411b803007040710050b100303210030b1204c2008100f900d8135240a041004007960005451540083c44103034541c3c000d400041c4502205201404810800307030b96a1070008025820002c00da00060007502c00c500505001d00007000003c0c4240c0141e0001c1400b820090382a900649000c550040080306513104121021000c00d00005850500344241d15203010000c0c041d04203580d854232540c0d0304100c0d130141c20007250b6807a14001001802070001e8405030000340c510590010084031403102b501d001074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 71233023 1250 71231773 71231777
    0x3050606120604270c060318030e0910031211060601050414060f0f0d090c05090606070605060a17010b0f1206040312020d06091b08060f09060a030807050d080106 71
    0x100044071503642180c00381d0311880880f03010070682804480303070742c1c2c1e05843d2164440c03082103d40e9003803c001c1c900e003449046d10704aa504010344038010b0300a1443c2c08449a0150204001700c8480c3c60354244510169401380e2080701c0060f00c2c0b95680d440c1036041c12000320b5500040d4481604a06040041c00f038141c2106007487d0a130300307090070300301980030400c0380c92a203d118003400070f9211802c1b0251400e0328030135448003811580b109503500a642c068001d10200b224103030a1000081241d02c2e0001e0042e0190f0700c007500090801c5d1741c0c3e940d200006c140203840e084d8003244101d400100038410800c41c05400d03d41030000b1408400150500c00d1208680b200c652007210700484202202c0800120250300c01e80503c0d04150404034891140001c1c07040c20400c25a0a0902601040c088050340000d48030003082d00c511204469404005c8441c088240c3d405680f1488444e510045441c10203201500900700502d4200301564030341e00d5210551203c541111a07070840c481628a103038001000340e00410140c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 71234273 1250 71233023 71233027
    0x901020106091e020913020307020a03021002280e0901060c110405150603150405070c020102061006020c010f21140c0403050a030c1406070302041712040608190f020a03050606 77
    0x140100b0204003c0d51502c07050442da0110303068006540e185100e40781e031442048119601e08180e2070003522142d0f0a45c041e0054481c481018a04842600c00c849190780c040800918080c1c12845015146062365075041c104030940d050444283d03510b40009000308035a480701171101c00700c0d140c100300d2100c4109180f803041d85010108040540c1c1c03010005582d11084071780036560317500c0d130466401ea207103e0015550450301d40030030005d0254108a2580056000741c081b01d251341d4407980da0a49500c00da01406005802c0303081810b100e54040e140c84040c1d18001d04044441d803007051721b00842d269554601c0001c0039224003001c0440e00c151a25642c1141c0c032481000d1419096898180d902c0c13500b194003c041000c060502d01c04c2c04440d0841140c05551001074400707504100758010041d402902418141ca05044114203001200040c0d00001e2542120007600b094581003094907841402014030039604e0030031030203405010891044034180194880016124010700900804680c002080d1038040c0c002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 71235523 1250 71234273 71234291
    0x2010e03090315060a1203020a1104020a1413180213120c120602040806091e07080619020c0a050d03060501090b0904090302120a03050103050f0a0b010e06060717090102010609 77
    0x7001c140d110503c3c03180c1034140003036202c0300003040c0702c8202680071820303e030255205602011341c0403e211f180d0b240104404c4000425800c100070880c42041c2c2c1110100744004084d80007a00e002d4003a0810813084209138550760342d0307000d00110364605520b18440203a400201411001101c01d1581301500f003100c60300401210396907502200407824001c2124240b4400440c004002d0150101c90180c810f407801e036071480c200525001e96070030318441070406c00a208124081c070540c000480d00101c43c5006d0050034541c988104508560b2070390803a05069a401b0020b18050b09420010181e40a12032001000c181c0c01c1c00200500703c1d08503030000c60420413036982c100304c60081001543c1085104460024480c43c092405034501004000085002d40d07001c10002c001c1509540194100c1e070090b0107a40307000030860703070791512115282070061040d41400300501984d8420090254042c07030143c0124a0041e5a80b2200030300000003818038034021000601e14510359080c0184801401604024410080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 71236773 1250 71235523 71235529
    0xf0102030708010b071506080d0908030a020d0e12070f090c030203240307030204060b09090903040303020d26010f03050c0904021c03050f0408030309060c13050409020112050c0301050102010e0309 86
    0x188521501108040340c0b83c0b0031b000d200100340b46260566070041051550303542c050740c0c40e8100407280401082440d100016400000710884a50b01141d5001c2c01410705000d40a8036801c059007801030300040804044003002208110110103055807100e85039403030345403407441401e0340d10001d80e14042500500c1032000080c5070404400c412020140f6413400300c10ba01000c00e1400c01540d0010b5849800c201d00080e200000300d0040c81c01150943d0b806c50709585040f070090b600d215a210040040c0d210440a6134020320407040c6100405581101191141c0326000103610100281c2003c1040051203c04004101040158842c111130a40c5c2c500e0301c51902d60000381c00c21500581241301c0d06294040e2404051181045030994020b40700360b5601e0b1911040815629013048a007103906200307a10105c1c070070001001c162007451120300d2484009a08003401d00c8003800403401c007281445100740d0540d00f50201350049a21550303200f56030580b250301d8071000a007510310000c0e85141681042051317070f401d92 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 71238023 1250 71236773 71236787
    0x6090a050a03080a090b101a030c040501050c0a05061501030c0806090c0c030c0304030f11031501030f060603080703120c050a090306050603070b0f0c06060906091602010f060807080f01020307 84
    0x660542040f030103960b42d00003c40c0140c001000004d110000b0881042542414940301100350f074601c1011041021441445400620094482c0100a9800e00c4100420f6220780000d1582118040c240d440c62800e071340d40c2603c1c00d00d090340d107420501d0302e80010201e1540d01d4800d42c0c241100620341700c0f03d54200072012078010344c0f0107045400a0f100000307a141c42081c00b007085629111a4104403692a90340b400d081c0403110b00c00400700e0b200320440307404070810301d400514005403071221140c040050b440c507504ca06c5d0701010f9031800c560203929000c000012a81c00e50150042c68000d0710ba074440d44400740208000c81342d410301c6a005002c820703c04c0c002c1195201400d00184e943c0118000352a403280000245408140c1c0d002140514001442942c80105500945845503503081240c070780d515510204000c4000c1101c0072034204082c040040d2002c03181e041c4415501c0740600002620307400c00e580300001d40f459038100390030562000c142004030902c208040c0c44500b00b0000214154105a00004c00303075 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 71239273 1250 71238023 71238043
    0x170a0203151203090d030509030d0201110301060e0f060a0c06270204050604110f04031101030c0e010521090a111806100504050301290103060602030d1107021003050906090a05 77
    0x41880690304400020b0070030031501441002403581d407441c800c40ca002029a88030062040c043d004041c05000c07018014020100044400d81c6954150781c00d2810840d00180100a0160301c800d03071441000c0c0f40c1c0c84e041d00910540d88240d880a0b82c44404e810100c058540800140242d00c6141c0c207140003d9a099614541d03c1354111804200d50b2607120019001d00026a5400409400002d980342d181d020312000b802221b108407144680040c08c0c200641c2107811510018004c0340d442c00201c45598400c000404501c1007840984104c04051485521545001ca405400d40d43c44118000140003040c04028040e010032034554200c1c0b019150002140b560180190340595410b0440c1d0b001940250152809071801030000c10014840006000b001c01c200300c44906d4100f005900c016195210b40611015075605030011031401019442d030700d0041c080c5020003c10000240110b60050352013004180402c000c1d950085080d0070704045460515101400c4400203512140c049000148003250450b05 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 71240523 1250 71239273 71239279
    0x30606010e011b020301020307050a02060109060b340303021b01051003080702011709010507080c03042004020403200907110c130e061e07020a050601050607051507170a020315 77
    0x280c400a40010f1120700c2002800030350550000c000c0180103a07100000c2d10200c00144c7c01c44280340d0781c03841d804e0121510390260356000a410403103a048884032a440c002c41981910301d00928040b42d80002e4545144030801300c000a0f0001012560414000e000414500ca440020440c6080c400040c416a0b102ea10008203009004070303449065a00625054150705a024070100c05031928054032402804c049840e0b03404240440041100043c0c0d89040e40e100d294040c00c41482e8903040e881c01d108091006441a9000d80c0030000400051642820340d80e20070b60348000310140d1580d0208000380c2100c010300140c00c02050a000910f04840003429240b03107142a0303904600c2c40c4030004004060b000754214051244904020b10000b100c0502d42145500315001400005444524040341c032007003c0c210103010741d0300982c01408649440801072800c184503008807820303010291080e00c5841c3c02240c8060114008070701d0100e5800c01000c00e80c0d03015000c10b000f1807441c900020442e850ba81c0707070507031940 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 71241773 1250 71240523 71240537
    0x1501211407030803131a060f130e030c071706040804030b090c0418141f1505030607080108011803050d091502041403010e010207020d0b070201150e06030c030606010e01 74
    0x1405001880100007031070300004140d603a417034000b2250054403004007044600030741c40048104c2051048000a0141c1d10090100000c1c05e000c10170021607040d407001d4003456668600e501c24003060100000c01c2005089000391803003901c0c052418040708044504000c0c0781d000f180401c400542c02c0c400721810f880d4018151072840c1c44548505103884d020640f0540c0040ca0650024000c0c03010080c0743c02d01c0b6210355401c03000f01d024200500d0702d9480c81034000d84010070741d4801200b520640d8111051085e911081c864603241d40d00c0c0060302c1c0142c1943c1c000e004c00c1d90b44006020100080c0238410100a101c421705d81440202d5500509a20030800d66070316240d13441c4401010003160b0360004100000448065407602c0e1641d9869011008039000b95100703619000210560038418020f440e0764540040c0030301d12103400c50300d801000103030007009001155641d4200c0d20706030348c140c1c0c4910040c0a00a01c0e00e810740c90a081418074143c42c0300c4030f00303129510600400202e03a9100090304611602868a04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 71243023 1250 71241773 71241803
    0x315190b03100902040c1701050d02060d0f02040f0605120f0a2901030c031509050402011701080105070f080f06061617030a06050a061d0105040314150121 68
    0x400910036015103940c5405450501d0344104410380244001500844003003000402c0003400b5104221900700500022643d100100281d1070300072000c80015001030301052800099800714002c54103007401c0f00010f02c4d4003003014000c4444040148024004509044c0e14103407040e200b025498a006182640000350380d80044d8000c0d4041d00f10b5040e045e90b030103802039682a9002254610400e840181e0700203803910b2280118180329001d8401140c0f8091b003400c8846003081e0742100034040040050303040c8400d00340c150702c1c0c1c01260304055001340326a000004950500c0d15005080700e103148503100801600c0b806011b0401c4c01e61407141e4010804443e81941c551800070380c81c540c82c1e00f0601c0a41071001c120030042054003041c00131449051068000c11a640c1c9030810481864183d01416001030030301030380e010119041214451507000e050400500301566680d880740401d8003100840003e0300000f45016008035880040d074003521801450551003110b841e003803c90b070304150300013421001500c8269 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 71244273 1250 71243023 71243071
    0x607230307200f0610030f0f0501021303050102030105010e0402030403080a0c091701060510051e07020f1f020c030c010e06070c03120f0e010306060c06020309010f0204081b0315 78
    0x30724100b03440341d104030351994842c0c90b416445072000d404202c018011003000a0a078203c802010302640e034440307144a40d810f0540c0320107021400d806000c1300d056500704400c0d80c81d0010414404002c620803000980e0380e43c14000010300380030460603414002c41c01401400300284d041184982c0c030400412000469540e0414200c84d2102c041c0e1142112088009908a484170b064101105542041d100005204000002100d25220b03808425865600c010542c1035215800001058164001480408507890200004110200f0340340c00c884a0070b6030468020789030f034040c030000c481540704a0240c014000c0d1400003070304000150041c54880d500026020041154210652001e10740040c1128480480103001070407118080140202252103c50804030070361081c000d581c00d8450541d51205440c0c5150381d240301030b4201511126455485202580c0c1141d01417001d0401006440300030016800ca01400340400e191949400780a034001c000c941711400f5494010942080c841500e02e01c002000c9105 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 71245523 1250 71244273 71244287
    0x2090d02040f0204030605060607170a020721050c01030b06030105010e010309050604050124080d030c1209080901031104080613080c070312140c0a120507020603010306020c0607230307 81
    0x10007540300b440c00c0e503103509400c002d0b805001600e00c40c9404100d55190701040200c41c1c080c1550083c1040c40520b02a4401200c1401828400000d401164201501d85501008680240803000110701440346050148031003080009440b03031003800c0802c40103c1c9a40803c215100500680c3d0500100d84c0c042c1030980d1003a0b20000c0080d41100039030700142890300d4054003a0619103800c0135001c64951050001c1040c0380d02a500b00c8584c01e00504010342c485105901400c107911104003403001205091011a00901031160f42070b10a800041e6104080c00016046841c5080c814a4850040c4401d0042d06800500b01d60402c1d040b040b81c1102403c1417819540c948544000e441c0180150100081040b01c05a004c00c002490b41d00e41810722403d18512032311500a10700484519404a41c1800108040d41e8481c802320134145046443c010385a0003059150f8001e070700c1100c0250b40040c03c0a6000b80a00100742c03c040149058040e0b460034400004429200c2d400f00c4928400003c0413440d21406502 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 71246773 1250 71245523 71245549
    0x230a03080c0d0203130311060903070b1008030a08090d090509060f0619050c010c030c0f0c0314181306030525030606090b040f0c020d050c010b061314040603150209 72
    0x720540d664030742002455817850903040c08074007060100048034900344020a03800d2042d2180c000031401c1085540f13034015129000b4140102050101c107010035040014001005a005c164032400154101894036034070340300c42409400200600c86ca414085c943d608588140c0040e41250601c19a04080000494a11642c12009044c0164428003003000b90032502074020303d10b40800800201401d40f10075000e4410146804001810800c0d00714502070040b284000964040d244c1982880c43c0e0b1030486665034003014400e810300ca4a0300c0004190301e403090312011410300c4080184001495a43c480d43d88030b009405180703a00442c4807044d07003032003039004000d4011038026406124903651651408010305030342c101d082c012403c0c601845007003050340c0100c0d0311101980c2d0040501a5150760304031159040106004d05a549a03032140c991503490350060544210f400d0305400001f45803090b2103401e0443c0030b400b0743c0203030304000f01040400c03c0c481401962605c082005650b40300c010001814001c407004e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 71248023 1250 71246773 71246797
    0xe030409020a11060c090a0e04030314101a0a1b05030702130603020118060807050c0c04110306240a0f0c0203160510050f0f2a0a230a03080c 62
    0x124402462542c403040c243c0c50010700c0003c0d03401648544c40380801c1c5200319130390386800000e40482000070040408009030702500034a070015202c4492042440407840c20b9a20070201002d60b0300500101604150011500e190400d0940c030b0488840405010000035500a40000984100f201d051040078002c4620303080e0f0091001044103890076040005190b680000d80c005001700108940b01c4603c40c003004150307070241e2a82e403c16075400340101c0301d03540030a00800d0103025028265105494038085c400b560100c200c8030a4403032030000b060200c601090640c2d20441314000c0c45601c01019840f00b191030410051078142a41800c801f0243c07580d040c0343c0030003500761048100c1ca003c0d0902d40721001d002c0d5030040344c80a0120301186811900d60007108800380320f04001b0048801c49250050081c072040e000405e1151244c8040c0d1511121180959170f07001c1c26401c1418040c040002c22075544248203844600100000054501c8607541c1c4030810004040c48005808035200c28890825941c40c0220a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 71249273 1250 71248023 71248027
    0xb0106030c14070503040f05030f0a02040518010207060b090c0a0813020a031218090603050303010e04061b0f0305060901030f0b071803200a0623040506030a0b12060907090e03040902 80
    0x18542150340381d100c1e108403000088407d801003001e1401140c0328014180c118002c081c1e10480f50200801424042c1c440f484c1c5550080c110045c5010a0000c0c25006000703110009060f070a820a201c903500005284c08000101088001c011540100103950801001925540d41c10b180c4d01c0842c04c00e0840360000b0b010001c02801400903540d01c07003511403591301500038454030745a548416009a6406020040c81c9400038001842560030141c88a44d000b0b003d800c0c0400c8020006e07507001e0b10b401d451281440094581c0b43d24160b101d401d40510b680196084d5507082666140d521100520036500c20010240000a07001c94070f0705220b070405d410800d045a00010b00c155603843c01c0402d01c066000e00a41c00d200e103001042061401010030011940240c540d0128041620400d010885031054600800c0c00240702c0812251a502d000d14400c3d50f0441001075803942200c100080385030f40c41441d00480d8814001c00c03602c1800403504c1d1040f941c40381c9010904d900304015150a602498200c2a411480 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 71250523 1250 71249273 71249287
    0x2070b0108010b0a06052d041706150a0311040e100e0a15020301060504150212030c0301170705010e130b030f1507030b0609062d031608040b0106030c14 67
    0x660100090035002c42e0030110150ba24a800c0d40d0381c0c02000c000100c0100702c2c0c00b405a547c1007050070080500460354480c4d00d0700d6203a800e840e912039044081c1c21310341d5022404124849000d02810b000301241169580640e03859940c580c02d81c010041c903128001d584622140b808444100268050600c0501c0280142002190f0681d03480e00603860555440b008500444c41182d00c91003100d05030b4806aa519142c1402e01154084044803120b100d070451041c01c80003410b0458000265024010b1101c082d0768a500d42000e0414400e04a41c4c8095503411103103040005070380140301d0a5000106594a0141030741e5264003e0042010b21000d43c1c15014110242665410100d036022100046400b004000d491b0144220111008103000c907802040400800c48245082e001404105541c0400c15031803400c419161103d012030840c40550300f80c40441442070740110740031403110748503c52400c544c40d89800d8580c81f16005c410303c039050078103076600e0002c18890720070303007001c0c0e02901380ca0b85e40c039510341c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 71251773 1250 71250523 71250539
    0xa030903030b0a030302210c0601060507022202090411090a1404020c0a05030703081609050d0809040f0e0705040b010e0918030c070303020c0105040602060a0b01051902030316090509010e0a02070b01 87
    0xe1147c0070034000105840a46070540c0199095441900f1a540203044e26800c00400f500c2d00d9000b00390603a40440500303100e041c04c84100c2108103001c1c410741c0d40507885e030b9500018402510012a09032600601c248072020440d166007131404100d035070803803200c5074507602c0001140003032103802244141401622104028000d001009000d103d1190307950070000d9a54403680704000004810100000e221907400704144e29005040404890142c0c406620780300006000900300c03080103404a100685075080a01040d400340032200c000d00f425035003404040042400244171107000e440e07007031041c41400041084c1141d00e00161071381100d4042180d954450005545903035176041e210881c0148507600240d12a0751250041c0e40c00c0340c607290000c2c105615840d41d00300c040c1c640484c0303c0d410003a0601941c41c041210141c004583c14a85d0050f5607207082c440c1070503021144140104040c084004001c1080d62900f81103541103809118840110303482c3e2a21000c0a445500030140242c52401c002091003a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 71253023 1250 71251773 71251783
    0x20a05030307050c13020c07120309150c02010801090c1b0c05030327011b0204021b10061a0c0703030c080405040504060506030f060919020a0806010305032d0a030903030b0a030302 79
    0x600464a40c0c00700c81201000005030321a6401c0c031206504001010020305009c0301d40d40100d54480c3c01c0c100f0300107480c0c403038511301440a640e07124009007440152005658010021501400300d5090502000b800c0e034a0140c010700152038002d03a1003d00e1013661050003015184140030b40401801d0702e5440340c2000380038481c0c40305503180c1d078080d101e6080810b07074030742c000c2e142c106c22000c440560400c1c80a050702008000c2d081080800c3c03078002580591300c04060103000062a0040c076910024a00f03050800a025480020042802000041000502a40000594400300e035450b207081c4640444910380181580655400a900242004144003c00816070440c41c810301303096040b0780d1a21140a0b0b019903401095559194640000b428010f5402d01041448c41203070000d800018180e984038107840c58040c09074400d40e00350f00040b8904d6008105031881c0303103a085814500b9900200c100340421703214410303079621406041d96240700e84101402a0402d605003600248800c812a60f82e08000c0c2d199 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 71254273 1250 71253023 71253043
    0x501020f060103020112020306130903021e07080715090e0408041503050402010c0b130813030b07050c07061b020d0311120c0a0f051504060b0a050105180409020a0503030705 76
    0x2602406028004038000050032078100c0c0c3d0142d660071145404190b0f220001c2d80058080e0390010560030003451892042e0041d007138058403030fa0043c400380c81110090010209840f0407002079810040d41000000000a6104140d80384040c00d1282000608415103111030180d00c02a0380c0c400c8a4200000d010203200a0300c115418400c400017030000400e0124100c620440300240498068800070f400320301800c0300c081d840070b003860482403401140e465440f401e4004030208460101c85260a00800c07200900f0243c000002d414503d04084145d0708440d22840140124005c02c144040d070150b010381004110503010b500680f4240312080d80c4c0c1001400c0c05821001c3c03010512800700c0144990030010100e070707503000c0c4c450007411481c943c540d00c0c11300c2035124000c1500c0d00e1050445a62007000c04c0044035010f0382c4030b89800180c0110200c180102c038145540f01c1d80c103201090007904808000c500d20225030b081c08580001d546142d61001800d40c401c07070342000c1e0b0584070100c2e20500304800001c1510382 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 71255523 1250 71254273 71254277
    0xc050a081e040605310923041e0c0506041e0608010b0405010507050102040e1603050601020c010c03030c1e020d08060301020f07020d0f0510050a050609010f0b070c0e100501 76
    0x100450014618280c2c403942c40b40c100018010002014003802c0e0f407607403204080480c01c0001c0d110788000b0b0760303011142560b00302e01d010650300c10480c80040740c035100030b198000c040c440740041440e00d030b02c51000c040481500c1034010200b28000f06c0c20059402016805041c00428803911681c50f0030300d6541411080e220b0100b4508070007400f0030028007907180581203614022a691801d41840011105034122103011256903409010118410144009880c410b180c152144c0c2807010031000010203440e400b03800d075415900010f0030403903666400003000001d1501420b0205038110144021220444250303503100c42004a10b8856228590200342c6890214483c0d950036481c1d150340c1c0801d0700703e1148160b81c0c41c0c1818104100d9006081000300348004c2c901403034104440d00400c0d1a142c0c04c0203c3c9840b062591a603403020844070020740c0c4280c0b0b82000044c0c5000e0442e6040c0080307401c25000304c2c014801802004500d1004000407840c0c00004ac000c4001707001050300b403111450444000714014a40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 71256773 1250 71255523 71255557
    0x611010b0409081c0e0708032709130503120708100501110303160c050708060403080a02090904061a0604080f060c120a0b01090905070c060f11040b0306010c050a08 72
    0x180c00e26007401104003036034221a00d00c1c03901c001c00c01140d0020208050080000d902d400340148858000d200300c00081088802860350b0f03a07807600c02140045050070519000b40040340d00ca40741622096030080c1d0028020b144014800f00c1400c02030300d10700805400001c004041801c001c4020351081c40140a8206210110727021602c500040d140d4500361030925031540c2c4140f00292260705207036060340500202d0b003052443e4440c0b07601c0703003070501c1441c0c0c11881d802c1d4070400034441012f80c80318900340d006029140841c1401c80c030303a001912122000d017000d0035041d1140d8041c554500c1d0b030011a030f400c40001301816a02d503a620170b50340d2101d000c041d0950b45801048002000c000c1c002086071400d0008010b0130101e40d644400d00e038010190740c9100d82c100003500001140b12441c40c0320365030068074039440301d13400e61a1034034141e016103003c172074244c505d1828108405020744000e000d48044d1080e50903025141c1c0d071800b00403204c078034001d4000740c864071400340481e062050200c0102040b01c801c0758141c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 71258023 1250 71256773 71256791
    0x30605030c0103091a100e0103051c050403032313170d02011517030d05010806180c0102101a030610031703010614030403021c0f03060e04030c0803090106030804061101 74
    0x1d021103041c00d0300582182c0307400c2d10390700c404004c50175100c0d03000040702e4400c07410b80e407584010308072001c5c01d81013215164030980318080f101300c0500084508801e60b2a0443c034060465900034110002c1408808881c000c104d1b1081082081400342e8105041c2e1403d4554035036914444018207085402070007086014411045403140e20600989110501200b1066803082c54841c03a05d01e0202c068064855501080c414491241c02e1030060314001c049080c01881c0606200c0c100c405040344041e141e80c4581d10440c0d1001699801150003c0002c0c105040000c210641c038400025290304108035980c1130007040100440c0425900742c00c02030360301a8106040010300c01c107801d42184401c2c01584081890542003c840d0315049004541c418030138410380e280540e0b0b8615903c0300b420044071003800f160700106900231140e45440307010002c00c2001b0141c0c0060400351400f40c40780c1c81c40705001e48546000800500500d009400440c015980420500d075226070790400140080080000d80c5859401c0090700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 71259273 1250 71258023 71258027
    0x5071503020d0e19020d05032502190609060318020a090e0d05090603040221010603030801151d12070e0403020a0b010b09030606040c0c0501050f010306200a030209060f0703030605030c01 82
    0x120010f501074805051380740340c56000c20280e60391054088a052004220805440c2580100d040f00d03140244101d41c4503044900c100700406036403030303565065002210410822aa0700030b44860803604a828009121310b800080c1054070350b001d0001a402c0016080700241e051280d0740030680044e80502514501d003c04c0404031042c1c4078240b80e0684c0000c092000c6000342ca003480030b1070640600344058080398614081841c0c00e486655005802040e541c90041000c0c0305440c0c0544103c504e6490014144110b00d00d820102c1c00ea0f8642d1980103401a880c000b03a5050200300c4803018100e6512040e07118070b41490000d584064007041120303000c10080000998101c040140c620004000b00502000d5581c0c4080c00000e0a010443c5c004220b182096680170840030302c1450f00465524603100c0c02c0d50b05505024098444800b5040e40740d01c05d43d40300c03142d2491610150340a039140e0b40740140e40c0c0c0c030b90840054a02d0280c442d0110300b030385001413241c040580683c844002c448081d000d48a200a2403001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 71260523 1250 71259273 71259283
    0x2103050106020703030c0803070306090f0c030e03070305250503070507080c060a02031c06150206041e020306040308040f0606090b12011a061c0219080105150a0c05071503020d0e 78
    0x2804151b10b202c680e000100120042d5500c440300d840c00044460359400d450741075620740805601400e0f90780720103403049a85401000741c5900320320002c5103050710a0358010301521840c10b441e030802884045e80c8070070317040d8651000e600d41d0300141107030b850f44100e0821b66142c01c8a8030800d6411b00c11106954000d00303255060f01c00c1c0200e240c003c2c5007080310b4806100e12a0140082c0304000e030750790700d10104600b14403400083d03201075594020708251520f03207403402581d00c07149140c1044d00c04400d8881c0c016a400a0107590080c0c2c14600804070b922a032174094604402ea036001825031381014030124100e511544280d12080c000c5a80e004480c103112358003801c032080342a07812222044100d810000382003100c02864000c8445100099564039905180120b0700200881110302c1807001901a420394803504842c0502011182130200d005a80d5036034802d807240520344402d200b443d40b08401030050911000c001420090194402c40d001008010002d5022050100810b0315250301441e22400c0003070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 71261773 1250 71260523 71260529
    0x60a1101050f0105060703050d0f180203060c04030f030f020a0203010504060c020d090f0b16062c031801030b01020a05250e060d06020c030d150e010905040b060405090a21030501060207 81
    0x11100d4500b1ba01d50310211143d6016800058000e612405092300100c0d03e403044841d240780f900c5203520141e00794410103040800c05091083c0d103100030311040c4041180c400f40f44000940c0340c00c2080d04014880c805908009551078080d5155103003400304000d00c10150044220110154252a4100e20002c02641c83d0341e03c50158500d81c148405040c401e8012031002886054540100c40e00613440b0740d41c0706c80a40d0001d10300d503134158054840d8020800d0105400c9224100d00c04003443c100100385584200c000c50342e401d00c80c100b40d119442c07000503900074814044c220703401500b61500325402c00c071001441000440e204030007001e070311030025103441c80e00d2030540a00e40040500480d014151200e50294110050494143c001084840441301d540d11580000614400c540d803011480d02448001400059003e440390506020404c00021080d500c07040d440314003120005207644483d5602898103511905c02083c1a001c2c85041d100f042e400740711105110f1850382c1c2804540c2c0ca8120072070316121f40344 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 71263023 1250 71261773 71261779
    0xe04020a080103030e060904110d0b06040e0415020f270103020a0c0b040302030c030c01060807050105030402031509010b060f0c0601090c0c0314090411090103110301140906040b060a1101050f0105 86
    0x107001480040e100303220a0b0040103004107a0b500b80115100080c1c02c4422150001080410000348401042060f000d48c40c0070113802c613140781c01d05242100c0e030000c0340d00043c4000c10440c088030000030000400c2e4180d6503c603640c40d6075651034420f03520940c20000b5004100d0910b030071442c081500590312038002c403294042980d0320f049520003603683c2c458400002401c21007d50109205520350b43c5401c00240a994030400000705403103280a000b00c0c10309881380c0090741003080820410000d601d00250341a02340c805029000e4040e5141c115560041100318069a4004ea0024144684018503406000445003a0058414030b999641e0100c5c1103c900803520b0011074030400d0210086402076540300c4503c03503450345452800a418001604581050b48843c001400100304402596814410300298181d204222491541498840c07041030b5081d0302c02512500034000080c000342c90f1500140c46078a00603140f507032107840c60b120107403d084410b181200150310307101c0050135440c1d4100040f81203031005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 71264273 1250 71263023 71263037
    0x1090b0f030402150322050a05151905010303140d1508030d0f0b090c030a09120809010c1103030105041503020d0c0510050708250c03051f270302100e030403030e04020a 74
    0x901c0796114000050b06c000d0b0780600541c8400408a401440006207540b03900000301c3c41e03440c0985080c20a2222404000c80b0a03150100601c00640c00002048403c81450741203a11744586000d00c0c000341c01d001c01035401001e00c0303040000b403c010000241c1400e00300600c09200d0040f9140d69070040387d10400c60550b01c18240d801007428022000d0066401c15203034100412012074a4403100010607401001c000010050820898507403403e100d80d0345100740f02d01e0090840200f5805055071b070301042c000c051040da99400d00c2c0700320081e500d28040085501070404280d000f1141000340e061516441154056400d655245090500ca04215400f580c5e001940070305000806c0c0301042100110001036415903410b441404c0458070071810030004611800040000c01000041030350252150740d40b14001c0f90400e0406200c51003000030300c604070000350068207004042410124a030541d1180015501072801400100f40440400108282c0740640c42d0384c25403600c1c40b8140700c12407090381a0a000582c1c1c0c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 71265523 1250 71264273 71264311
    0x5161b0303021605030a050d140f04081c0e0a030e0102070602030301061d0409050a0302010b010c0308010504111201181503020618010519020733030b01090b0f0304021503 75
    0x2079015001e03c0d900c3d6000b007030400f049503840500e141e0003107000b2070201d0000b00b1181a5400d450041d041c5182019010002d80e0400031043d01150ba07001c3c00041c140e034004201401e5040060303c0403c0c1d0310216400902081c80c44ca028541c50388050b5070305500091141d0b40c404029400052080201c1d14a50300840c5980c1c60302c1d10807203c02d4006e181d03180741140b17030001e6101d4035070f01c9000c0c0d510094024006002c0020f21403a0286c00c43d41c1d8901040e05100315011854042900510070604450301070340e0100e0f00b1062400c000e00e40e807040700540c41d50f424078000041112240c80070106441c0f11801c900300002503c40000044201091100950042c0304000303c400181210710f000e18034120604105040c50744505203001b25071032030002c2c5030060740201800c01003414507224815216080700d00801e0f4018515544104803840c0200301c5040c507480d4400c2e60700316407040140b08018014040401e03103864501c0c44c041600d40c1b0a4400b681301e8900404a803010742c2c4c0c0f000807640582c1a800c503011400c04c4c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 71266773 1250 71265523 71265527
    0x109080a0c03020c041b090503060702030d1104241701050901060f021002041403060604060501020a0308090712030305180105070f0e060d0203100312050708071716050105161b03 78
    0x140c4003500b10114014021140c080382c0750340c080d5000300118510304c6105540844d20080083c030259020610a5000300144000b0b10b801108450302c4040c00d2001083c0084100c1440782d1621540e4000c0d40400140040040454049440c400d00440c0e55a175080312000b0301c81071040325450070701540d81e1060032070004200c640d0145c6040000201540180c8000071030404001d41240c005911605213280c02c40d00e01041761800780308c0c482e8010000c4504208003410b041c0000d40c0c5000c41788001f03050007a19400b05448420400c5181d0041581c1e0b0039918450101d40360041c0a013006071068004a20489800e02524806000b950703c04d8040d03544a00c1c3d60241e17400d080f50315509c1d040c3c00e15045030302081040d11610890000310b1040c00000030003558a840d501d0308402c03842c4c070010201c0810105218400004182d40c04490941c1c7d08031003141c211a1f51110001030340d1103044080800041f001c240d8004100c01904801d110304511b80514604604281d401d0340d403506580d190410842c054030310b110000e8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 71268023 1250 71266773 71266787
    0x6020705060702120115090c0302160303051909030509040e010b030a02220e0309010207080a0c0b0d020c0609010902190b2d040e01050f1e010c05010f0f090c080109080a 74
    0x3a000400140b0b444c40c0d080300103801c44601510402c80071130803400a200c020918014914855a180740862800e610400001e1420240071001010907441d20007284226040c2c41000340022010001001402c1d460f00c2c010305140c1c00209100e010700c2c01e02411a18440c010701c030340124008080c0142109140035401c001501c1c8400c1c4aa005807190042c49601380310492140750fa901c9007070b0000b141d032502d42c040068a002030580c07280c0040d40c840300d44180007803014031a20781191030050b0714a41b00c4c0207414a582c080d016102d0b000c0c001c0e01c81e08041014108054001113130490003655852060131744c166400d0300e152600d0040c110419810440e5924030101914108200c480102801080050030b8cc0c258900b0b5000354010440c41074107c0c01848285004406078250700740440342004a0701c10b2800c0440300450b0f03588850b061003040f1100c00d00b030000a4108544103002a20200807200c1c940b01c50300e00405203e441034820307540c40e040c003080307511051103407104260b0043c0c503560401600d144129030308 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 71269273 1250 71268023 71268037
    0x10050403120603080301261b0315040305070b010b18090604060308070803040506010f12111306091d011a0d080f0301060305090c010e090109110705060f0106020f06010602070506 78
    0x450300d01d025006144062080b000070318410542d2036540e514010b1a1521218100c04240d500302401c1c1c4034842d98880040c403030701d0510f02600102c0400c826540041e0800fa800001008034181810401080651010007001030354820301541c0c25503601c40c41c108166000d1450320108084078030803070b00d00f00e10704522950f40c490300040c00031a0f01522a580c00d030081e00318100c11209254040144420454107102d00c074094000686601c900d02d107084800081818030301c0024150820b009001d104d69280c541c0e40591109180805100642d9244070041c000c0000e0868214100600d1190a059800c1800795a00c4885040c05d48801c82c1c074020200050910244811034007828204050014012540059402414940c4000980b868042c420b41d0800250000c074a0400c140c62107410423982d61000101e044d0b4015020008141448030000e541c9849450b0028060744944804c120700d80800ea82c205041c1d1300c0603401c0da071004203041d0381181d40d49000e024134000b50b00464003e01240c141b400c081d240e6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 71270523 1250 71269273 71269277
    0x20c01020d0c080f0403080a0f081005040c051201060906030f09020609040e19030302030f0106080f150402070503070609022107090c0c080a08180a030203040b0703030605190905010e010810050403 86
    0x3415101c8200022075510940c801c41f40d108011404442031030300001d80003d50845801c102030b16183c800c100e003d1980c080d0003a14401d0795122411401e55200b0b0055880c11402a0450319007961640c1c0c0140c28032a0b00d11660b030000b400c0101a000141c0c00d80a0091407039405403005040600840400010300303410000244284102c0b11103c01100451801e6468a4001c6d02c0040c2d60382441251080b112005030004024044203009018814103c0b0b0209540540141080f0f8103100141002902a110b51030002c2c14078840400c801e0103001d0b8175030002c0b00301c030701c2200d03a0750303410726400a000b20342e00a05c414038a9a411100007000101c0180d00071001120700d51402404880d20365803000c1154100040d4480011030403000c0000140100c243d1180c0f0702e030010000d294401c030300e9070001d50300d10982c002c1ca41d5200300031460000301400b90b00210054523009103412122190050682049206807007109012800c110002600304a1104110305aa42440250220004c1049a03c1c0a40006001142 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 71271773 1250 71270523 71270527
    0x30209161d01170c07020907080f0a050a1503140709090201090902070c0e090105090615060703110f030307050c0706090501080a0b0f030607050c010b0402030603300301060804030f020c01020d0c08 86
    0x1c111041d0642c107413142c0142043c00383c840c1041c1c014010b1101d401840c1606012000080c0402c4403c0710414943c011070030780001ca1160f58001c1c1326005086191000c001034214480d0100420100001000345100204101c4023111390300e0361070340280e03010302c88041d000c01c584900a22070302046800030811a4010013449040503a01c038040340d1481000c036420700721079668105000010b0004d010480d0070078156550b542c00c001c82c1070300280043c8034941c0c00130140f0005950f112451081440004441d0341290207507a26031401000281c4160b000c2c0c2ca5503240b90148010110300d4030b0040c0c008405840f010f95402566a40d01005140100941c41d541640010107240d01d021943d400c21416100740e00d1640d44a45800c800403009007503c103007000003445140180200a9031b510b00054551500c91140812400041248942145c05c8442c3c0c80c00302c0706140000010130155007200394240100d1280e518100381900c42c040032603c80e0f49041e0740e140140c011260801c4424840d600c0c5852050040c1d2180d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 71273023 1250 71271773 71271797
    0x90f04080d0e0607090e060f0a05060903190c030506010803040303090311040912020c010e0604050d0618050319080a020a09062613030e0a030308040303091109070207030209161d01 79
    0x2032402c3c0003180d003000003a8501d0802c4c00307854008281035030850415689011001070440024200c20254054203009403404078820032259003c00003440100307883c1822044807d05030814814540c81c600007030781c041c480c13003000160300c480c00000c0f5011250599104400c0b1421540c50115007401241510303400742d25130b10310318041800302e009034141340040d40003052950b84001c00917010381d203e1443c50340305445c280002c00040d00c8041d010baa906902c9000081e00036a02800318411808007070700a842840040b6030b21041001d101f01d0344004008684890700300390742e07000c11b0300240d220740c14000d0005102940e04100b850301a40021031032486040d03031101443e001b5000e41140d0002204d10b032612840400d016424507400000040c1c03215400c1d0f96504900e825230f1409415000040c00040070103035244203000c140710900a00c0403504e90700600d82050b80c00e00fa80025500d422500050341304003103d1003c1140301c20075001141c6080304580300d028454405808914182103e207a009042c08007101c00d1f1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 71274273 1250 71273023 71273051
    0xc06030408120703090506090d030c03060b07020f010201270213020c0d0c0302030d022802070308070b25080601200703080304060204080d110f1504151d0a050c090f04080d 75
    0xc54070803c0482e0080c031186c1d48889c4001c06841514202d40c051529000042c09900e2003801225001901641c512040e40a030000403401401c240f82071039614036204250355029001c000140002038021070b041c4002703201003a2040c1c124810382c00c40281079445101c44009a50041e440c03031081600a00560b41002044240c1806076880320038241c00920108000c0e0807a40000b04c4c0d00170460b80988014500c55045680303204081c49040c8000d01030b00c841c034000500b501c0000c012000050318aa01140092010803000b406010099400c1c074042055000803020394185135884e211003554440040140f00d280d81c4480340d503031307002a105942e882e40130031020409500812505803140159507400c00340007400c890290a04101c8644807045401070b042c3e1450560351950340580180c2c0140406408118140c2010010045a6031482d80a07843c0482c90041b1000414070220742e5002e0302c01d56035034000000030400040411130303c0744e00000e14040400d010a100e01c0142000c04440c6c1c40000e0002074482030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 71275523 1250 71274273 71274283
    0xc070f051216020120121b0703030f020c040b0901060302090d020402030414150103030203090103020313150c1101020301150e01181404061e03060c0c0c030803090c060304081207030905 81
    0x100742d042c41c1ca080d160310840d40c1c400c0140b015070800d00c07103203198103e004400c2c0c0d407641c410700d007494002c0c0c00109220007220920403a20300151140b00444280c01da8901c1c01510000c41381400030701600038400362464605203405020314030a0010045070300c0f6070030020160000d400c076014036a0410b42c82400000103231110301c0194040c0d03001e502c0c40e014120704140503a1800d90305080c89030180044a00400000b9000000e03651810001d08015840f941d840b10400d0708082c9041c40540448100c118031030034078005900c9501603c0550350b465080c0400190114240e03c4288034000c0c00d000481424540a80b0a4441c072075100c40500d401c03115124806400c042186054011008201001c65070a465140500c01d450040030101d28504010070344592201c0c40c007244e84000347c091605c800c000e220003881106030010f0300740d010556070034050b01c900b00700f425500308440007003003445102c0c039038600c618200c0103891089600811f00703450654140c0100d4001c05014000600b4140c490704441c00140c42401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 71276773 1250 71275523 71275537
    0x180c1b060105030706021609050411100807030e010612020402030403090503030d05010503010c0e010f08070216060203041418240409080903010605040507020d0c1104090507030b0c030c070f0512 85
    0x1009040380c1d41800c00305401d02c0e03100c0c0d0042041d5480f0801d104503d0700e00d807040f40c0454420030000141c90780d45041034080d1580700c0c0c4820b83c0c402d50ba40750400da01500424131a00852081c6d60420040000101c003500701c401a01500c8810085800014011f1610781c0013140c0c4a440b81c03034503130302d003d94400201c0d1840e0811050f07040026110ba0042c0301c282000d2141c2130b1981c3301c900c4c00300301c0500124000303018801c410940200304618200020b1596000300704900c04c0c6400368001ca590103640d008006d40f00d400c28010780080d4040000c2c3c9481e246400b07102d40200300f401c000c5501c6140c45081d80080444618031032110344281d9408850050390b624400e41c04014003405a43e82e0300d1034400200350848619030447c1e40320b50b182c04107200009a0000701c0381d030040c606050010807504241040c1600780d40400e00c06074402c0c1000405801c2107408141202242d00c0b4202d06001601c42d684d5901d0940001c5502040b080014050003001c60219854101054014030540740c035003a01c001c0b0700c0c05a5000745 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 71278023 1250 71276773 71276827
    0x61712030a020421060f110f030406090c170f01020c1c0210060e040614090309010e01050904180302060c16032a0606150305010510030203040215031906090b180c 71
    0x115200c811710009005240418001120400840c00304140c020b081d40071708010380b40071200c04070001d401c0013059445100d2098101004901c800d80e640400008030b4500d03c070105190051307003064101e441050081d2400072001304094658900c440030400020203c1d040e0314000c5100d00701d114028940d183c4910005030410000e0743e5650303c1c241c00d2110903214848900c0700281d406004100c048540882664040314003482c18002085401004a1709070040516103940a0325000d0140c0c02844c80402d8080c1c0d6a11030340907210280c2e41c406250015001d919052840c480c900d03104400000d1003105119100d10b1114036541302094200c070050081c00c80d15000b00e5407656a400c003480840484401c0c50303900030b200e04e81809950b05000c00718411102c01d01201c424150040045821942c1d18002da8450601c03070203d094885c644503400308504418001382c1d5041a18050010507030303030300e90301070640741e200054440901e80e081c02500c0940d00798010803940c2c00c3c3c0da05100c0e041c4d00360700700c1b0201128042c0d04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 71279273 1250 71278023 71278079
    0x90f0b0106030b100e0d080d09060e010207020f060406090605090d150b01020712022d1806040b040501031211010605030a03020c03010507090e0c0307090306020f0a03061712030a0204 80
    0x30306028074220440386600c1400203600390302081d07988506c000c00c0d180303900617021902c50040c100a000030b00340d9901d0091420341405442c4550b0131055000e045914003c5460040401c0c4c5801844110b00c0b40c0d014080002e130504106004090180c1d000b8005450b01414000315041940c80d040790f045400e04a43c10030648a1020030130660381040f2801c0035103801a0509038140140d400942184042c0c004103256120110020307415424068030660000c00c013402c1038503d43c583d01064200d4460807291640314034500200b46e0007034202481064142c941c0b05198411400c5440000d030b424070101a035040103992546404100c3e1b44040c07051407100ca100760004e1200c2d960751010982502d800a0401c03040120f2280104041400d02c1c0a081d00705040001c066a02c3d00d070041c045440c1d1200303400c00b400f8a1300008054994090600050809140c030b0f40e0b082140c151580011810801d4091401105070301c5040c2c00400c0950030300085421440c42c840c014500790780c64200780c22404e0b041e0645c003011000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 71280523 1250 71279273 71279291
    0xc0402042304020a120504020d05060f0a050c0316030504140d090602060114060f07030302090607080301051c03120b0f090703090308280203090102070204090c0801061a0904090f0b010603 82
    0x11001118941c040200c03015030070250440c0c0024451200390780c1901c00503445602003419500d912401812040d0054180c807524608181c400c03034400c2040d80c13810041c82c90300d000200c0d90132054003030303078000c1d00200d100311000700c0d80881c02c034050140904181c5d2081e100c500d4012070031608005821050340b5075111160144e1920340081c1c24070a05074421000d80d0303002c0f00d0a1069564601c101e54440e40c3ca031458549031061810201d000b4041d03070b5400f941103580040c1c8041841707440e034099030480d0350842d03a001c422240c1480c0a0300c2c00c0441007004020540450b25030703101c645103411005100101504084c403411002000a0030228203540305000300350748000b820b092550000d01d5a5000e10340f00c6010108585016a040b58050790020389030300da55011000c9a480381083d01110844c540007001809410960300b020090100e4034400e100c4950b2030305100044200b04804203541c0569030301d90b5507041006072030610003d04003070b150803100a0205c5100c240011744103115240a0b01e41c6179400240199 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 71281773 1250 71280523 71280569
    0xe06060306011e0e03300a09080d0207031101020a0215030903090d08190908060408031503030712030c0f0c060b0a03050f03040e1e19020408030a02060f01050405040b0a0b030c040204 80
    0x1c60386845003c846035900103410f440c1540c070466003c0806218159507800d115008c55032001c2c1c603041040240516040b440c1c82d10b600140e100280da01030095918805005401640c0d10910030b28025000b09004443d04401544403025661140360b00f0107407451714228174000f43d44403220f124111203002010440071219040c416001d03240e140e035424191034071400c104425070340c0d034001080108640340000c005030700160915840c4ea10075101070f0499448802600e0010070b10549803900000003840c00307110f07200c640e200d080184461251922245090751840e19404068020300c43c2c070300d80007079030700c00b0000008004109a41c1d6015914000d1500d541c03c01f041b00c0303403d1401074a9480f8118298040e1101c034080c98154607081804e91451099501c03e81030910007901556101c14540e002c0440c20108203a004a240c038401d02250011000681e244d0b002c0004440c007e0381d010307140a54184c0016600f0159038050741003100002c08407484060550000f400741da1098001440400480038243d503441 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 71283023 1250 71281773 71281783
    0x1060e010e06030102030403020303150a120f140c0a05040e01090f03090e16140328060f090501080c06030c070b010b0409180b0a090c0f06030c1202040e06060306011e0e03 75
    0x218120005d41c40c42c181600d00035940c0c0805003249603e0084031000d000e040c1d4030383c10720a004051030700a44800b18410f060030304000c40c80c58001d40e0881c509a19030785004001003052a220071008110140160625091100a00c100c0c3c1d0030b00260765840740b0301c1e23011540307105598038154801e40d50800f1841c1084643c098044000c0c040411980101200341c15464002d109889120a08005142c0341c0da1401ca421210104c1440307003500070010181603c41a826541045040d94002e0076914071090751203034040c0441d0300074800c4141d260803460f0180d0032032401d04025600020b00e50181403c0c10482e031154904e84a0031781c00242c901600183c10404800240a07020043c1d007601b51442a000c15030329151410790006080180751907890010904001819001c3c01c050000c90003036402c225110180540241840d0008401148121051860f1412140210740540d41c3c2e000e0a42c003251a041c0912010750805440a03060040c04200ca801d0519078104901030759109580d1010302b400c154003814100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 71284273 1250 71283023 71283031
    0x140c03041203020310060509130f15050307080703080708041e05180f0a0c050c010f050a0501080d020a03140903150601140403020306010b28020f371401060e010e 71
    0x100d401413007003010b402141003c60003152158100282d540481c2000646000d01380424010381c5440c0240b040b9042101ea80120005c8003880c0d0444c00312920748042541e108101c2c8a285142e0b030000c3e03c1440001c00c60805045054031603e010b0f410300f0b46808051400f04294409017280e42252a41041a0f240c12500c15036210510381e00641d490a000304002949100146600c0c9052b4984c0c0c8280c0343c0f1441501140d030000420780003008030742804460000030300130940d00c059105003080004200383c0008240c031009100a60020000088203070780c2940c45241c070724101407046030103020850031500c080c0407421681680c0040c015061800c0310014140c1c1607000384020100d4800e001c1400161070001e05903054a0410261503210b1383c27103091888540000001c03e0200302405840031501c950005a4141000a0a41600d11802d640300c03810025059203455910840720b0030045c43c0306400312003211078031240940c803d1030b2164803413182c044c04e6884035404440311584030f400420850803886046900 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 71285523 1250 71284273 71284277
    0x1050c04062c1513060801180b040b0a090e0d03020c0c060c010b040e06091209060a081308030c04060305011d041704050a06030204080105060909060118140c030412 72
    0x4040c103041c0020b04268098598455503004107840c10302a81e184004640c007020018560451042141640083e60f0002c041e000d020200000010800d580501d075200c0c140d802c810700c1550450144250203010344103868031030360071030f9664152103407680740d4803a450094080c041e8003180310b62100100c80d1400c40901c02c2c1804044c41401301d032448030303004581c03813512a4045800320b07110031101c10207030300410300031090791f92140c508100c107403000e00045a11032081c2c0349001034030103030f10f28409056000d10610a0a0394002e100b003000c1040e9074069000c16400140072406001003586941c0c603600340764010b5800041d95500803804021040e032601074240500f1810040c0d40700d02c070080620200f8108040d00052248505a035001c41c44940001503c008005c024200d000390759a8080c050002c1d400340c0103905240d4280f50005409050160707441c0d0103180706a00500c0c05a2800f40b0702c032144c1910701d00480303e0a4690602401c140c61030210107019100280805a0304d0a00f8505200400303401907400c81 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 71286773 1250 71285523 71285527
    0x40812060d080a0c0302030d15030b0106030603030804060e0a1703180a0213050c130f0521150c0706061511060709050f0a090e010b09060d15020a021501061101050c 72
    0x1807030001500c83c0840c090500d800c602402d4a016801c3d0b0040c81c0c00a10310301c0c901005600c921501c440603008490003142c01c2082a600c03400120300340c440078000a0042414100843c1c00500c00e64800c00307100004900b03550b0030080d03e9840121484903202843c2480c1c602105200700b50380782d11102120310411200034040488a40c0c04624008005000303607a18550707450006200721842d0040350f80b0210640042c105c00d946038907030803022140743d00a150084460845141c46410f520340d40b250f0040648000340001480c10401711000d003002010400e03141d00c20b1241e50005061401110b028209200140d00586442c0100521030001072020707100c41da200d00c0520451582120034002511010390f44410a0391600002c00c8020040c1d40c00241c68500e045d58020fa400810f6105040c503c00c100e52192b0161030318401c0121a0021401c00f9001e287d8212142c80c002c0302c0c2e1b9008111031182c81c016038040c000340381194020300c507007607100e1800310782e1000300e4004401003031040e0b941c000d0155417214 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 71288023 1250 71286773 71286799
    0x120a06050a03020f100201060b07051c030216110a09020d0209030609030a0c140a14150601260613090f050d02010213050108071101020c0a0201020705061905070809040504081206 78
    0xa400d588018200900402000c403032507102620070342083c0d000c9c00d00852700a40d1f40c6034501e00039a661640d0382d451081c006d50100c04c0d4087d0b601c03074001c99090300d0407018100022605500d40c50a40c115500c4c54582c071117858407001079204200d00140a8004c4400d42c016103c0bc90740092500f080002406c0e400141c01c2008200c01094114000c114420740000b00aa08808000819450004c1101d070107400c045100303001e0b01c030746040000c43c06441b0201c05111541030701d80800540d8030404004500c54064050800780715031040320241c550740324100800a0805005050b40b200c1122443d410560b601510080348009008040254449903081440214540aa800c1e030680400c151401004d04010350038022420f41c5210310313400d004c201210b5000f19502c1703101d000300715a40e1001c61001c03070240c0130b140c000052618200c019501d00414101d00c50003665034001e800c8401e54001c4500301c503a40c03c28404103080b07031030790710130a0711403071003079010756604c0115401068040700b008125a02c5400c00001d60 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 71289273 1250 71288023 71288029
    0x901050d080708041a030106030c021203150103180305031605031005040207230d231207021207050c130b0f0609030c0d08031837020402120a06050a0302 67
    0x4a900542100545031540b402e8549800c1610035540203411800c0b8114104403082240c0d0001d60403281c4645040004405001c000d07a145c43d88020b0280c2410014400540d02c0c6c0100c04900c204600d0514001075905800d01c09100d1008035500c06500040c008020444070140c445c01c40c10303800055003441c0f425407030304000000000c0c4060080078002d94012405404205580d0040032040d0b0b001070391064611810345c009944c03800007880201c00101310104400401c1d941e98a4040c0304c8603d0400d1170f01e000b4180d82c4d5071244a0010300400118451284850f90f601d144901900d80180324802608200407a41e0801c103913100d00f640b8a81000d480d055190803581e8500c0114468594151500f54407505030300002414142343c86030094101e00140c504100b0030100d20001c40c815003001c072561081c244048202079803800c0c0340a9221686800c42d6031014850190814551040d801100113014074603d039011505030380140d011311020040030024081d141800d40141d0b4040c00041e81c4121001e0328503000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 71290523 1250 71289273 71289289
    0x32805181005160b070e041103060418020604080c010216060e150910050408010c08040506010608090106090c081803090102100509150103050a1209030c0302090702010e0d030603060506090105 84
    0x5814441c01d1068400360300d0324000c600343c4000f0800e5140d2100c060440b4204284c40000031a0103e00154403038484150b0742c582841141214013032080102e0030765844005100051610005944080640b294030f40010303500da00c0204007800964010340494800c0c0800a8a01081d100c01541e1001c034000081c40362036840400000b48501c100c0d035441d46203030000c403001c031b0604c144542d0641151060b0202e4010a800100403c1140d011400070400015031100441e00b06034261401070440d00700000411240b4801d08841d50001e00c000d00001d142c50351408640b00711345040004902149007031040004201da0704248400b81d40e410720140d880c06102d100000d4440a00c12001c03030a06503070b400400c901c01400c2018071402960400651400c2d43c490030120340e60802c484048681c940c1200c6490600703441012501e048951150318000100d0540e030130003040c142e000703040808542d620280481090300400083c00c048100380c07400288075043d8107040041d980000c1140c1d0240c50340000412403611240c074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 71291773 1250 71290523 71290567
    0x80603030f071101030e030d06081614130b030114010302091008071503021b0102090a0b040f0b0c2b09080105060a060302070c09110d0501050d030c03080711032805 72
    0x202210030f031044900581c018134a0002d0b140e198072011944c03034040000c0c0c0d4004400d548400d400c450200d6240103151a440760305004401820328003070110703811405d03d00c07541c0a010100340c20114070315001d200824211140101e0011070b150b1440010015810075203502c60b04649400605000311b0308201d00c6990728806031251030f845031001e043e20409141310f035041d110510f860b89900c00468000c1190103020350005d802d220f1043c490340b980003408610310001c40d0100e580d002101803845190100b001c0c041e07000106c10703180300d000d01d090303000400c008441c00c0c800350800466800e0114030300002c02801c0d05d1007508841140c0c4e25100a000d030542d50b04883e10101c1f0071703d1038056078541d014030b084c1c1c80d50030540d800388041c0e81c1001202c05403511a203014100c0c0a2240004220580e661001c110001000e044083c001c54000038108001c680f06a18080e0310525500f80750800f441a2703081e46140d640f00d41d1a0103128512160303031710428202100701c0343c07007003031107280090924182a800e00c0c0c507802108 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 71293023 1250 71291773 71291783
    0x12060708070806011b0605060a15020604020d02060d051008060a0606081f0b0d020a021903080f0406060f2402010c0512040309050409030509030f01020301061b020411030c0a080603030f07 82
    0xb50010300b1580c4600800703c2010a81601c040c002e0080e49071050142c01c06403101440b4114000006c2564a91a0300c00707150400c02c1d40c001d1140780c1b107079002c0c41188150040180d0700070008002c66102e1140e18003d6a02900fa0301c030541801038a001c03d25800c01781c01910069000c1d0030200b0801000d58003882d210380182c441e88281c138804400d0751280c1414000d0340c0c4030502c07082c03000c02c542da00c0c10303a030742c0c060440d01e242034081e20300c0d80e00c9050307552584003075511004001c0381d42c00b00801c12f005246216035921a03c24000003032100d0321240c211551000a0703000d61048218900d40441a100e440500030341107600780000c0c0500600c244000d0b119005010400404160081c00502410300c41d84680c0c008040103081002240190306000f0000d80c0326454080c0644a5400700d10071012052007101c0c1216041e079500d0f00d40c043c05401d400400d0f980084140d0740b0684480590044442c0c2d0070046000348810305215603281800207018005540081a152094000380071003680643c49904a940c619400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 71294273 1250 71293023 71293037
    0xa080603030c06010f080c030a120806010201091707021c080306152a1c0207062001150315020702030a0807061401080d0e060403080a030203070507170304021206070807 74
    0x400401d2450007901144074692042e03400006030303400b1003040a0107480350300b01074480030703602041030555030344026900602074603009540d00c0805200f0b021f066003008052002017580909034461440300c85601c00a900699400910801145000c450442281010510601001d601900c6000311030000402c100c1c0558600344018550304a235000b01c914101135207902c0590000859101c0e545901c4100f0604c11611600142c0452480e480c0303c1a2000d2816078010140b090404c03a0445280b19010004030b010496590b030001408000e02a440f40d250150115002f014954201a4082070800c0d01004d50188104461000741e20702041041c06940c00103603140d5500d6079403524200502101c5400d10360407a41d00000324a0440c041104240606583d40d1301d48400c22500401c0258451807100800002d020488844c402d40a0780140d94420b413176090950030144180c0b02c0d00300d510000d00c5900800c5d4400070411046103003464100c95682c00d020000c088a01e01110f001d070a401c00940380405000d02 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 71295523 1250 71294273 71294281
    0xc0201050403080d140702010b0906010f02070305100509190309140a080604050f0d02010b0d021e130903080a0c051608090316090b010e0604061404031a10050111030a08 74
    0x80e2084400071079200e03903c241d84d405070f45813940050103a0700b00300f20490040000306c0c600c0ca1050240c18031408000300310720020b40784c410040d174480c01c1d0141550700b076014200000011450a10020001004074a0040385500c2c00d1b5451504042c446090a245400c040c4030701c0021170351000c0010195042040442c103d801c034240051001000c590202041d44a48001c001c10003402242c4441c00c1c10403181201c10032055030340103909968001c0b4490750407041810030580035181140b61100707241c640b20008580742c00400003040e200c4064117a18240903850f08000010164029500d0b0790044a05404001d544c024000080c080d104508080c58401234603092032081c040d0b800103c80c122600242281e04414030002640103641ea0340c4030700510a490015403007400e500407000c0c1801481c0c014000d618260610300b003550340303046030011518684004d000200010b0b48050381c40c4040340394a54940c085283c12078480b1000201c90304154104010301c5408a08217030000103460114000c0c0c2411903d660f2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 71296773 1250 71295523 71295527
    0x50a0609170106030b070e0a0e06030c04050604090f031e0e0108010603150f090e0106080601030201050f1e0703032f1903180b010302180903040509040807021e01020d030612030c0201 80
    0x2156400c050702d0801c1217000e000650390040d480c11411708059030a10300361695042030040d040ca08685803a05508034030b680900c545001e5120503845200244001908201030f1a0a1414510b080040f00890710004a02c2c0308810381134a902039041003890b02856441c0d203000020943e140601c02c80040c5501c0f001c0050ba0b5400c0a80c040015040c100107a00445603110040c8002d440900b0000d4455407a0140210750a00c01241e114140d0360181c4480c3e10b41201c85414031290b501090000310304142405040d07810440e00c000a15940c0e02a030390110310a68070b141883c121421200c12144911300d508004140c003150316060b2019a01c007800107894900ba42001500503120154006c1542403001c510202040a0308101c28103a0703009a442407061051491140c600380380585902c00d00fa4000c0c0002c01c554a440010244c0c4617100c5d010702c03420700c00654042400d14141454941e680c801120f040400303540d0400042e580000740745000d001ea9890f00340e03140d2058100140c040c0c00c001e0180e82d941c0075a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 71298023 1250 71296773 71296781
    0x4120e04091b1a0301031e0212010203070815010804120305090c040e07090b0303030f04080304060902060d0606020c01020a0b161e210209061813090c030507050a06091701 75
    0x10b90001400224004141c182c540c00706410b01540c4011054003101c1c200011181044d41c0c140c03503010005550302028081508402c0f04c240500300d0b40108075800d1840420428000b650180c0f600ba2540b540d103090440e100e14083c01848203250402c0080802c020102e200356598a0000b201402e001604d515621090f600b0324410428194015081511076081da0314001045022203044402c104030650444003059203078032082d1034100c0e1003007002000c0760202d00402d00441c1c00512420000a403040c0c158049920354000c642d0560503140e45200c100004c58050045500140c0244007a0ac50701480380c0d16080381c0c400c0a8000e141101611084502c1140981640a68200310402001115128180040030039200f122122034140c80c005644140d050b044c02640c50b569401001340c1d0070304084c6204000311569401c5c400364004001a0031088060043c4103510300d1500500d00c81e03414508605181c2e107401e87c01da100500030000701008000e0f159001014200741d9042084030040c0b0019010b039035001d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 71299273 1250 71298023 71298041
    0x5060a050a1d030d02030309010f020a1d01030209040501031b0509060105070303090c0b0f0703090504020423030c040e011d0303040f030c11060a0302090906012109021908071d04120e04 81
    0x40c803031813001099031078000000d103209030350141c003e001c0c1503080304001d0140d00590343d507480030417420708128038a40d2003440040312009040c5001410032890341c00050a030b0f0f4003070740142c0755000e400f110741403600303482c07134645000d0941501c0700260360038883c0000f489442015405410140d6401c507980c01c00141000740c0005041c100c14194503400e4a5444280b25800b0f450100c0100301072080001d4070381018001d440848000c1c2401c000003440c3d543e0361034807480f118205554140a0061820500c0e55503101d1504082c00210002401e00300522512642c0040b802640074554410f100300000140e01c4103d0300802c40d4140b07091021146a40b5110384119116803c0e10b85c080030208002d01410703499400f410030414203c80e810300742d0b11242d00540d048150304202100311125a9003c050300d2866411452540d480506404246500c0501400c2e800010307410071116904140410410680317172000c4000490308081c00707807200d81881d41d0395a00201101c8640030500c0300d0081c0380c020035a1658090030740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 71300523 1250 71299273 71299279
    0x603071a19030b010f031a04020f0c0706030e070f0e0c1308010e0c04060b0304030f0f0212040308090103050c03150d020f030328090e0a020306060915031005060a050a1d 74
    0x111002035403002e00a490540407280c0051001c4000c903115a229000d21100c440041440707200380b00e00001480083c0d0310244000010300c104001001034448200080e800400e500d6400240313140c2c22600d420704140095000850000e44000280f00100c0b000103043d41041c000c984450741c450442500940d821255800580a0752a000c2241c003151000700d84070102140c00c42c0c007005810707180d05c0c8802d064001507401400081c1440841c2608601800512558032000c4c0101c4090302250006c1c1c4a030b0307603c184c00860308100301240219583d6014080e10742c000c45515051411441d000202c3d0f0b000131041d0341400e01c244086502c080554032544d04080401e000034054a40c3d0b00070042c0c103225101c0e08050703400c0013014642c4050381134502c20f980c480151b40c02001c480c4040d44500e40640c02079080580450f5102404001c0c9014a40d42c0c0c0e400c407404125138185098503072904903808419200c0035400640070350b0382002a142d40991200884101c1500341c1803c3d10490041011404d41c2b110607064250 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 71301773 1250 71300523 71300557
    0x160903051005090601120f0b071404030303060306140402100807090f1502070b25080c010e060a1b08070507030e040f0e0c040207110d03020f06070801031202060603071a 74
    0x40c4079203280d00000e1003412aa42292502d0360380710180c80d88404082e0000e03010780b20a000d4040020140f4860f6030f000a964541045407050320381c0800c0c2c840d40030764070488c042683c4d030000b0410820301e40644285c6449c91810660740d450140c002c00d441c4044070405004000c0c0e1000081c0100740901c1141d009016072103100d4901075268551900903100e842c144a01501c140913000584541c55011940b4070030b841244102e1b20059161040c0f00c040e0807900840d000305040c042c400240d08240b08010320342c010ba60080485040c5140b04508a40702003903d180321005850001813a15004859903030400f4561500907a07643c21400c2c2141d000300b0050340e041d03015080c0401566603826541015003060216820b0703404003190752041200302e21a1400003841c000b8000c5440c260f500e40200d8045003039000f4010b40d0900114100280d050041c2101d0040c0402c0c180c0c0c00502c140000040d10551100b50340c0001d090f28100303040003d40c1c80e600d510400b4a008a4840201050106075054442c5100890003040d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 71303023 1250 71301773 71301793
    0x601090903090e0c0f030c04061b0201140c01020403050102030709150503040b0411120109050d090504020702030c100c05030a08040c12110f0607080d050406140408070206030411100e03060117030316090305 90
    0x4103a0f5400752150340d0000300c60030104030841c40c40c81507000901f40d058641c0380a200cdc0202407110983c10640300182c0a55084c040000403440a0001b1841072070305603582a07040327080a2610114005c420040001c2003c144200000215850701060700150030044c01c000d0391143c80c000403e00d04c0480f070005455400c24005004210000401500120b01078541251f9030b034880701800128003c040d40694150f008c007a640509043c00304c016401c00c083c070319001c00e4619480d2a19482d44d800341441400040c6a4010081400b40c0314401c00043c20402c402240481066118500704142508405120f142659007164565a83e03004503103440381d02104d15074035200410300c0140284000c84003030300c078107060001d1003800540c0003070402d210390b500c070943c5030038161513030284070700b58100030001c41340d808100c04030f81481d80d9809045003603008103a4551203000c5101c0141030078a0b4043c3e10103444a2840844022421004819642c4c4184820622580c14044400456a12182d41e00141241c01462118 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 71304273 1250 71303023 71303041
    0x11030a0b010608070216140f09090c15070f030f090909030531030b060103150b0306040c09050102120313170409061508130501060e0a020a020601090903090e0c0f03 72
    0x1240c12602c50f034075420310076928a01d060340c545203422550840e1800541301444200d0002202902140c1c001c0c0c4040c0c00c011101c0d0200d00c0740c0d001030f50002000d40c00381803824039500d031081c00c80304207041000004bc181500d81c0d0740c0103010400b00200a0500902c14008400184600782d850300804800c0710a121481c691f0030050322603400385c004190b0211000c03040d08494083c000020b018441250f544101251458540d420112006040281050344819401c071055480c6c99074180501604ea25050352811b03c4400c0008540c20381a03000300780036002070100700d9a078002c50a41407061a0300e0741d80341d40782e45440d10788220310b525080003810b070680d080084071302c01100c8001c2c0c01500e0a0a104001d070035114112420100c88111004002900c0c0000140300040c031003000e0b1403081d208a00109a858403003808a02400048070b80010701580800c40c4071003994100159801844505410410940240c40041110703507a409410065403203400450fa03030311411000c48525108400d00d440d100c0c1016452 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 71305523 1250 71304273 71304293
    0x1314010e131a030c060307050a0e0607140d0809060a0e010f0603030807020d03061401110c0d031805090f0c1b0a08030601090801051005130e011d010c050c0a02060711030a 75
    0x1d4050b034108a000800b5508002403142050180101040e041d0781d94103200300d50960142c2c402008000f444940d410f21612810042c0c8000e511903400f4946941d40e05070701c47d02e007007448609032003000140030902013929408200c0d15048692880c002c00d0328003140200c103001d00701d80c120b04540d00d4030307086001081c194000500d50003504640d084c1e5015980221044054401900404808540203080880d0315805031211004105031481a01c49400100c3c0005c0c0c0a01c0915030203402040c942180441403904a01c03000014110444ae0142c050800c00580c10840f10f0060800500c00c81c00104481041c4100b0103070101c84000300104c071203180080c50680215001541d119020600415011545000600406200d4000801c0d4109410701e0501041300c45404400300201065a07590008000c410178006d0701c0c02c0380f0408600a4007003c81d50000750840c1c8090160030700f000b82c1800b2010300c500c804032700080350035012a0500d0300d40e041803d00b00601c0386d21440284c1e061080c884076108218145c40b03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 71306773 1250 71305523 71305541
    0x1b010b0d02060c19060c0207060c0b0604091103060f100605040b0301180b0303040303121a0907180801060807150f0c030e060d0501060f0f030c020a0209040507090c05070c09021314010e13 82
    0x82540d48c4c4d20f5480c076003600d10910350b00000784003c0c400d40006065060a0780542405401807840c02c254803804000b0070b0130f1a1040e80d0700f49c0200042000c001c80300d051407210400504061900c20300c0c040c5042d20b01c01050006009204a040390041442c05144454001c075620700c1c0b0007400e03650f8441c0e803894083d290348403600350300350094108900c10680740c1940311411010200582500900d96400328111040702c1e221010001d100410100410644400d10984c400780c15a00300a205190900040000401406110000701b08000d5074500d020386c1d11940006820b41e150511201480280c00050214001c4621020882d850100001242644a070804060f03c00649510b1003152070041c00700d040d0342c01c9441e064003503030118032548018200a005c42c2d5010380198290350340e01c0d40b120089020785020164600000303802286003410f100201141c40300800e030704e00c1d0843c6412059203e10004200b036105200468200050507421640205900e041481c0001c049206000403410403500400602d2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 71308023 1250 71306773 71306777
    0x1c0c060506061218150a0b0f10050f030a09020409080901030e01090210110708010504081c15140402070f0605090c060f070b041a0a021b010b0d02060c19060c 69
    0x24020a40703905010003200c014207100090b50340c107903480c080c40308885400b0042a119078403400011130081c00c1200300c0346010b1041c900c4089044a030071010021501040c41900d845880000d00f002c070100d4000c0b0858810b242d42c1d0750455182d6544030080d40c020198008040d401500b407000f09d03810410382000400c2c00300001d89007040409a2142203500701d9540b4407000750080c2c211071007901018081c04010504000710000c8a203001e49651995007524002e41d000c550400000c11100914100320119503200d00300003104010074040301304400710000091203104032141b44020707144034a0702e50360112549550002d079400c402d0151490b0900041070210380d007010310701410380d01070428500320342111100480340b450303281030030100c3d201c0c071105035005031003220b024030302c0d00541d61000360218002d8800d81c0c0250f40162601c11034070040c110013100c4002994564500325040c3e160f540d40340e004100807901910f001e07483c1d115032843c0e5403401c440c09403011040d6002042c078a0400c10307190040b440802003070b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 71309273 1250 71308023 71308031
    0x100203010f0b16080d0605030703150e03160803060a031a01060914030a020603090703051207030315050102100c14130510020d091203020c06070b060102060105150406030e1c0c06 78
    0x80c0346020028040e0301001c0b00b050740603810030f50200d241900039103407029241e03000080d030558900010307203011200c0e8400c454031220f500162508120301e20039441c507100e4000c00386d460310780c08070001b80440c0b482010041c9020008030100380c40d80c490300504005941d0110900d040402e011400306c8402d5001d2095000103101c00702e01045024110341070030329400b0b001c0e0081c00b09003215401c1009540006100c900c16100754500040441c2080200340d40344510110802d50b1141c06041c020180c982e29003940c000c03881d0030b19007080075990004a000d07808071a01c800252880640001b210300074640c1c0c81030041300d5400b13712842a1850020420b00703d900803181042e5401200b80c8c16600d0f0004108441c000c5008003008000c0005203180021031244684141c4062039a04400210036400c150015074034414510200601540c04025141c09420212821803440068a1502007144210301481c41010b459411400c0c030220100015124080c200c20780411803020014020541e217200303042039640741d043c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 71310523 1250 71309273 71309279
    0xe0901080d050a05030a090c0b0310050906060702060307090e0907080f0c0102031c0603120c050d030504111207050a0801091e03090302060c0c090a06080d020c09180708100203010f 79
    0x100180140080700240c070752a08005190000340c03001d030001004050b0803030304d07051600001b407070a2a030400909448000141ca03420110301c0340700c0c140c3c2941c0149000350151360500c800d9940d54421f0b110481e80c12200b190350b0f036503001c80442d07254655a000704101c003840020300c28408004145001940e030510112601c0c010f1001c1401d64645100d41d2190140c3c000b085070500003a844a880d0800000700900801c1241e62a030340c5242c1c0c0444407601000085900280404019061100c64001e100514003841a424261034502038601d8510155226144a81840440e0201030202074001c020003080b41d82c0c003507601c0e100c0381e000c0e1910a8040300c0b81c14640340c121084a03824013402d0202a09540c481d049681981e09021959106020f0001c107845100d12034089075a40c0810144591480e500108a0501e41110ba510303214801c1c0c0307407205640001d1820f104640310f090303a69511440001200100c070030049105414590f0750340060b120703806100010604190b09030010360484040c10810442140d03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 71311773 1250 71310523 71310539
    0xb0a030c1409100303050703090803040e0403030c0302030709141210020d051003050d050d0f1e060518150d0b0702030406021b0607030e19090609050a06050a0603050405030904020a0e0901 82
    0xb074100d07003d1400c40c1a421050022178881c00c050041c04d0302c2400c1924203240c440a20070b107141c0066000800c0600780c0ca041004165242c0145c814202e180d080c15403d41c14194800b40100025000d10b4001000c00545802d031a65942090603c44000c0015903001306404d50007007029502c2030a0980c4e4031820100803030141d0b0000310112080b641c0280c007519403190200c5085561b684800030075030126841e041101600c0c01680308400d80078001828546810302c800c0c5e4420256003003588034a1040792a0403040c0e01001c0e4040b0055449603048500a03200d18907800010742e902c15072400a044000034408000000f40c0020040060314040d400700d68400c01e02d0200c0b00b2400c0450380c0b942e60041c1c001e01010700028000c1000062402000348140001d07a180746030200391400703e80c0312120702525506d0400c80c1290385d1081c0380e00003480c00418003110341031101260341c000346481a80f0805584d070380050184039050007902c0900c0c1009005559500082c40014400500407542500c40c0358a03400016540c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 71313023 1250 71311773 71311789
    0xe120a08010321020312090a020916080f13020d0503160c141507060b040902061c06120201170714030c030601080f0709060c080405040c05041707030c14040b0a030c14 73
    0x280550300642c90105841c1c013481b241100070b40b0720321051207400c80140040e03403170300b6449100b00d000307640c00801001c0c801c034024401d150140025100b01e00b22414421301e2800d00e4110f0241907015130300b079200c01d103103440d103103281d4800c3d5441d10581c800b100898500b00000c0111240444807520503596041640d0400c01c24012001c0c403460041c280204561000030b0a80e030044030b40b581c1d0007000011030307901c1074011502c00d510000c00c3d2803201154903840303404400c42e4441c4001030040390744110000c0503940d0000c0d20445076014090440411007000807032043c0b00300d40180c40c51402c802c81d0381d200d040030000c0c0c1005400c241d0b18140801e2090001a01620800004a20508440d0790300c0c4456032038490142e5204480c04070980341c003042080701040544840c026520300d07040c260360b140e90b82c1e86004684180c1d05c41031800c0c0d42180d00956801c00102d4000c180300350550b14056100040c44c0e0303610000600403e00e8608258001451203400000e102d1140020001c881e815101c1551004401c0308106000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 71314273 1250 71313023 71313083
    0x30804080a05070b040f05011b02090a0c020118080307050309070918030e04020711060a030b09180c0105040602070e18011a03010b0a0b0f0706090c0905040c1d0601030e120a080103 79
    0x1000d0746d18200047d40c851082c031090900c1c00304401c20410203c2d000700d070140b4021104040b0164035040b400101540c240b0410448000340070201c0b20304031f41681c88030f0300e43c40040c00400400c0800320210f54070741c009000c40c00c001c000c070000030000c40c01820650840290701c11020390210303001c81e030340710481e0425008450100e944000340f904014440701c20061280c021041f507404055078bd01684042d40c070348800450042400401c9400781c040e400014600e01a01d090302d02d4108002400200241900002d0040654a21150350009a6a40c000d14100560010b2034100e5075800d1903000c09810145241e01c58a18400340c000303000d01a241c20500410f03481c20710941401c070a0400200205194031000f5001c030b944605004103104426072a001d090b01080d80050200c1961102480104549001640020034241c42c51320000d140340d615250042200030a454141138588240154140041c4941289014003c003c5502c40110030300c000c0a0040901049aa4002d040c3d0280c1060401982680b40c1c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 71315523 1250 71314273 71314289
    0x30e150415030c02010e07090608100b010f0302031f180f050c18030c1504060f0804020603040204150306020d02130503030f030610030915050609060a050a0b0703020304030804080a05070b04 83
    0x800d01d15048214010b00d0241d421900715540c82c240e40360002018064080104403410002c80c9039420321400340c0c20445c1000710604800d00c2c000c3d80d104282d8010610703451800300c0307090068403956154040164020703da51100b114416409000c03507241029805d19a041000b00704c1000ac2c1340d411000c04040f10400d40790b42503035401c1031105800010920750a00c07229507018080d0b50001151101140c244100c2c131454520200d03022405000e0f0340e600064100215220b46000082c9042c0340d0080381349440050310281c01241c03108980c41d02c03585078a14100003140d0241046540301c80f405950f000941200c812241e15100c2d80000054501d000030a0701c403042c0c4a00702403890f6460380b008000d2911101840d41080c10b4503846600089514003002c0013058030a8140403810389415810002c0c60340c001800170748101d070074010034052070b11168411015030724514071480d0794640c103003000c2c3c1c9180580d50004099010002c0d001c12000004664202014406c0e404c41d42081d840d071142e0b8200303001e9070241340c0c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 71316773 1250 71315523 71315549
    0xf090f06050a1109150c01060b041701020403030503040204090201031b080105040b0621060d060c05090a05190b0a0c1b0305060c0307020309102106051c030c0f02040e0604030e1504 79
    0x313030343c03402c50452140b011214410307610742403078124104e080d52a650300c1911003c102060401c10b00080c1c161511070009070000840c545411540e0240c50350001a202070b0256949400e035504590003580020801401d8410320003402d83d0f040d5009007518000d0258034003585c00c00c08401200c2c1098400e0300d04043e8108101c001582d84a0160711003003034014240c5900954421001002c10450302c2600156911566441d940e40c8039407082c090b15500561010740207221408514000b00101050384003980da1142442d59240c011403070444106100c2c110141c00704a031500e088080500d200e20100c00c5078403e005031030301c65546a482d074015020403140103001d60001c00031f1042c1e51070038181d80f4000032110b0800c2862503506c0000c4081000c401c840410400350b44180900040c034284046400210340c2811915860015a40017030031008420b1009000d0ba8005204408559440d0003071800050720404071207203481c150030010b1044000c40780d82c1e4081e59100c0480c903a450298001c4800390388008910304 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 71318023 1250 71316773 71316787
    0x71401020a080a030b0d08040f060912120210140a0e0102030408041e0e0103060e010b0f010c020607020d050111030114010e0901180905010612020307090225060f090f06050a11 77
    0x4955510100f00301c1c00b05980e909250b03016585003084580968040c108582e15281066000c1e0041400c076041081031219482d81006000002d506450ba000d5010380800034001e0801c1c02a807801c4104041c0c1c45d5031509090444403464403003003040340328642c0340d102800903c405180d00d41c202d100c180d4000d0034804e4200004c0c040e0407105c1c61080454440d1720116008a0342e24902d0040888080c1c0044034a90340700c0640c100025424003941805190482e200480c0b8906900041c08500302030f2002806504041744400555495401101e800d5406c48020320001c80da05550244c194003d00403008125030155203109039510030400c1c038030024030140c04205a40d00344074142507010b40640c0c141c1030301603c0340c40390780005000b8001c18000b054102d0b51404011024810181098507a401440b40f052048c04811100119a41241c800c000403e0340c003a01d004003810040c020b481580100d03614282015043c0d010086000e11820500740121001c00c0140c032074500c00303400c2d00c11000d02c000307602034240940 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 71319273 1250 71318023 71318033
    0x61006050f031504050f150306010609090c0201110a0305011805040f141903020106060906140307030b06190c1109060306070302130f08030406090b0c0a030f0306080102030a0e071401020a 82
    0x1590805a07203c001141401920000b600b034030401c07207804400103010414041c000c0308224808241c00c104401501041d07045c080002d001c40014410310610070386030071990145c03030b000b035007c603069403030424100c2e607640d041101c05000381c43e003845100c03406024a8a6001c0d0304406100e514040e580c0100b0072201d100a036255580082818560800d4600814011b5000821200000502c040c4031360004921585454409891004a5072240e400c2c4648440e00341c60307036050741003100e510168909002851903003403004580e07180142d51100740d800122900c000c6103075402101019209100c0c4030314542d40901d04041c03140c64403060b2102901640004003088680303020b034000d04501d050024119502950701c2c2c0d2030154000c0349a00c00f8049400014090001d0f6900408100c0501800508189000110b1280b03556581d00b550000c1e040004582d20760038018425000040200050030080d51282041500c07580148401c00180545204c1c81100003006030003d21600c0c5002416005058410519190 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 71320523 1250 71319273 71319277
    0x30103031409130e01140105040207050c0d03020a170309240f0705160f05010f0b030604080d15080c030f0c01091a0c0d080703230c071a01090b03061006050f 69
    0x1540fa0f10400c400c0d1140e010031400c0c4120308a2940003c004a001c44041000e40480141a0400c0b4040c034010409070f40850030002c1c260f180c01ca01a94014034420060804078104840801c0042141000b1541603988400c4500554022802203055401081c0840ca411900c0e04206c0c5c100284880c04000240054501801240d4401e0503814400d140c9004c0580300c10024551000840b40c20442c1c10b035110902c070703003485491002c0510b52010400030091400296403242d006100626503000080c080c0140360540c1c01015030b4013445104444042d8031200a41d440d80c00c1c0c07450140c001c1c4229a6000c0340e030180000ca4400c40081a1510a043e03400d0050400746500c40480c2e01c60a00002c022141d00d9003c100403005104280e6607810103182082000101612003100f440440f021070004640c030300d520551601074201307900c00a0f25035190a03d1034101c8c3c600c900b546404148580c101c00020b4540010740200151320704c01c0301910780a545000e000d42c0e41e901a8043d00002420620203c0000585440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 71321773 1250 71320523 71320537
    0xa270f0b090111010c020106032604030b0a090605010e060310051501030f0207050703050610080606060a05030603010e12030702010e010e0703020d0309120606260c01050a03060e041202060105060301030314 90
    0x3601c240c1c3c040c0e0521646094070340804411005031764840d010030038001c001c1c180d41c004008030800d404c4102c040b030614200c91300550002030660303009540411010700242d4001721045601c045c00340041e60b5520040064824200d0700e5500074007900b120001145500d11456105201c8170070b040c0131303c0d402d1500450040080940110546508005d00d4000c00c42c2040000000c0d880780c0010310440c50940d200400c0c1001d40da000b80c40b47d03400070f020300c60340780c2d0b40c00e06a510b04183c038680940ca90b560540020301402404444001d00d00940c0b049020403484000150300c1a4844d030024001100d1924005080741d0b0f028900140c21f030049001071006140810a0b086494040c0c90542422a1108a4040c13040b00b1000c0c00c46d503041e40d9400c1005060000c1d506400c240b450100400c1c01000400e010170740328410600414108100042d8a48486001e9030011000d06440030000c82c15252520300b110311000842440d40c094821a00009414600101100e050341d50681c0c802c40e148010510300c0c2d0950300b080e4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 71323023 1250 71321773 71321777
    0x13031a091f051503060c041e1503050408040b0c07030b0c04060c020d03111501180b010f23180a170709050c0d0c02010b040e01051b160204020a270f0b0901 68
    0xf040c00403641e803c02c0100e0040241c01651983d6500c1d0000c1c0f002e0001c0c20344200385542010500400882c8218240c54000d4500ea040100700c940e100c0c40c0c58003403441607411102c0480d80115503100040740014200b016244540a031000e5034550341c4242e1018015441840300240350301c0203c00050a1a0f00072420316482801d1030400c41d042c0d4a2141d0400416500e8090304110b41f200400c524a0304400c900f01c43c04541d10200202404540002d192041c1743c0c2d1208284aa04c41d85445210851008103901c09014800c0e580c982c41c1809981498104001144c0c2c0324008407003002c02d061050700820030032440b00c500241139261801700c511014040091101c8446002842402c101d02c1c494020031055582503400060b026584108100442d40c010805020681c500820801002900d04040c0890340e469454592985001b0240c1d844c0e1b144450b1000390000d00200740d2a100c940c124000645814242079403403030070600f4104032007070720010348100070500b840c080e070811843c048007008020011041c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 71324273 1250 71323023 71323051
    0x71205010b09040b090c01030603120c0c050a0807090f05010503030703120e012a03050705180402091302040812070506040b0402040e1c02010f0e1b030313031a091f05 73
    0x1000180311480841c1c080d0307403a00104c0100b00165405110030120404242003c014050441d100c0070500c02c07400c0d00c091f0500040003507520074040c14405080040034020516050070b0380f41c40b0300c1c2d5100da03268400ea50069050000258490328140111030682d0740c050000d5041c007195031401c449050030000c207050382c40d5035140c0c0c020541030f007801100300d0860580307010402800c1c040707102da01c2081407a0004042500e002c0600c51074560020454048008414491018a50260004000b407058941b544d034001a0281c2582c01002d0395000b42c41103a8455058514003041000701d20070b01e01c20400020156000540024005010028003d8109001920000e246214124064640a02003001c07182d43c2410f4a080812258240190384034511194010312a0025409440d562580a9900342c95402407070004100603440810640d80e0102c141006819881c3e642d060004000f03c040c588200740da00101e0002d110808000703900c0324a03144c0d10703012a200000055420005080142c03402043c0d07501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 71325523 1250 71324273 71324291
    0xb09040b1503010905190c080415060801060e0103051c05070b04080c030304050604020f0a06090902071a0a020a08010905071719091a0603060108120f040504110a021b0307120501 78
    0x1d80c09580a094500400900e0742841071540400749840c0d4014150542042201203019900025064116521429211080e12214440800f900f9107804c40b0541d58a44030300010f44010180c1590f040324003d6040d122840c65141c0d951080e10501c1d400180130440c1001500300090104098680c007901500301035040803074028000341141d2090b81c05546c40e42c0454140f00c00d51906105000d000030342113440049492074a030300076041c1d0307500784581c5815aa0101d0035005100b142d1401840003108035141040e00c0c5464500b00000303400c4088000c4c0009c610100200d0070346003e01c5800d014030480e4440507103000f100444644003170002001c10403006a100291409554180584055503200b034259468480034540c1d0b64110041c0141054401da0094004000342100403a5091380e1000961225603114405000d8824500c11540091b400c40e00e0072050701843c040010251440682a6094620311014100e0051070b0240000f41c03180d240c3c1002d0805c10003207425450714071403540310b84008100204 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 71326773 1250 71325523 71325559
    0x20a0e01120201090b25050c04090f03080901021c09030e0604060c050c0904020d021c020303041d1b0a0c020409060e010b010212030f040b06030c04110409150b09040b 73
    0x9800c1c0e2003620341c48035160710102190381000c2c0100c042c14a001c2d10b10700b004914001d00114064140d0f0244d000d4000018500a02801f4044000c0c10000640140200c00b4a8501011482c00180040c2c0004107000b0202e02e80241c18000c548043c1000c060010048082484e410002d2a41d10f60032014400f0b01c2400e003c1913115038026200034a42525512594611410020700340038001003010b02c070f004d101003000016501d01d0070000c011078060f214a000e40b0404407842005010300301010b5414400801c0004428500c444040d0b0402403510502c050754a030001d5140100701c0c020702620341041c06002450900c0d04c940781c02111a8001440404c40303030059100c41003195031180b080030340340c1d444140076a85940c0421811498610000000386189007044801c3c07030020000e4001081400c9210104001e0365041021800d0480028401c2000c84480700110840e94454420305410300c3c103018040e464054000b0086044800c5241c50320f2400c1d1244007048020b05940115030b0340006c500c01011003c0d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 71328023 1250 71326773 71326799
    0x13050109020d0609090b01090e100203091e0a0f03030f0209090c0904061d01050609010e06130303020f0c010207090c1b030206060102060604060506190201020903010f150803040b0a0804020a 83
    0x3410030060399940c03101001e030150344541c0c00c080701c100d05051820000a48040304113044413050304c0000342c403800130700101d400d2640081d560540540044280704504d440418000159003500011000c200714103100a901c41201e680d0180076030b100041c144012a000360402c4820100c1254018501440f10700040c1041c5000c0e600e08150b0000271401c5003d504080c4030700e2010341159007c112a100031090445a0144140191030003074002040e1200280d024030304491818030001c2c15a03031520151907207580108040d12055005202d944c00b03001180f0004070fa107840100c8103a0181040078141002080078043e6040d0020070044c6207400482024402207501a80724840e602400356820840002498200d002d0015407040c2d291200800c07140d0b80b400c0888621a01d9000c0c1c6000c5c050144000f0f03070080c003c400341c883d019424410000c1005040340d120307141c40d40240c554000060780f141072a541e00d01841c09641c800b078104002440302e03540501400d03903100c0e10040902c0304071038440c8401034000b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 71329273 1250 71328023 71328029
    0x712030801030b0907380414041109010c020405061215100603050c0d1e1e05010b030637062a02030705010c020f0414040b0c07031409130501 62
    0xc8000006004100f100d11155401021031001400107906062007007441a1041c07001c001542c400040b24201d01c21070403109410b1482e000744054456666055044000121a2080e88a030346401c0f96085400290390940d03415200c1a0750340011740701554240700c010b01c4007510469216440300c070912045d0314100b142c50014410359610140034109070105070748101c5590080030038941443c040004014404094800b081c5010402062594099600c9014800d00d0380c41e400080d414062511080700c0115180c114803030340341c00c080000c0c0c7c0c0c0c1c0d20002003582c00142d54060b031081518200031503060301194035071414050700e108480d0000d000110500d94842913031044010400c403002807540a807a40305000d00003c4440074902040c440b50340069120407071400b0b0340f414030042200c0d0000795181e020b4041c86e4003501400402c40d280b5030241c1711035101011102105c1714a8140700082214440c1c205440106a041d110100360740038800382141a90840b208054000d0f24a44a0b48090710300c4d03008071402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 71330523 1250 71329273 71329277
    0x1909020901122d080706020c0a03030b030f03090a120201021203190b0108040f0803101a0d0501050105040807180e0303040308060a27020a110708060f0a052205071203 73
    0x902c003602e00e0300f2036140103501009a040a109a100450b0f43d420040040c1c41503403094072560f840d0b503d45040e0000707002c0c0c000607042600c1820607a500301a0180e10001f06803000702e040368884e25280b130305113a403880f854202c07540103007840d00204214410160a5145148140140d03105088003034548125504201c80c00c1002405c040a0807064001c0780c23180d400c0707031031080c40c100400d45403644a01000f0b80c0700e00d4000701091400000600644406004032000e801440c0da2000d030741d0110780484c00660066450300304554581000003c841d80a1411107088130780f49030150034868034100721415000160543d00d00b4041d100e10b00c1e036410b0700302440158481c92003602c030036403217085c21020302c280700505030843c45c51402001c50549800402d03085a010500c0c03e040003503907803118010101da2850380036250000c140720340840440e4000d004102c40307114004802030300d603c035601c203100d210588800b9511940e03144540800d07407a900c4484801034035464003d0302103a003ca0f582d00c8041c172512007030003020b0340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 71331773 1250 71330523 71330549
    0x15051602120604060207110108130b071103040305010221070909020a0905060c060f07050a05090405100504060b030a150b09060d0e030a0f11070302010207170f01020a050408010e151909020901 84
    0x810401c22070001001c0c00d0007843c1c08270389443c2c0003031114081444404017074415501c210014240354418500110103081d114150703519513a40e4642503000c0e410a010742403c140001011080800c0c01c038000920801180e502c40700080d1421351500700941c081124001000402400401d445e120300300100048160000284203925080040000d040000b400c81400c100041003200101355205082d100308500072540052142c48446008050030701b1940074070382190500c400000c07000e0040b00514840d803c0c03000144040388541844e080100442d008010340100c05110842c40ca00b00351019280310701841d44009070412071005910314503040350201d10f00003807000300d081324180da100a09000e1040c0481c01072014605503800070703442e0701c0d40d80102c0019001d81c1c00c500c20031401c100184485494810003c40d40c41d401c0c0f000041c0305501a0181c45203d40c2403203400802c12400041079401c070912400d410040380c0314004c001c0140801c5c104110a010b032120755110150380c401100c24001c00c41400608 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 71333023 1250 71331773 71331787
    0x1d060910090504090f022701090e070302100201240b03014103070605070f0803190606021506011805010e01090b033103020a0b0606040305010c08060109150516021206040602 76
    0x4400341d0780c1040c110324151092410601d8020007050100c8c15039501c8100801c40c4603200400f070346040d10075031001e940701102690340440b10313806500050403490228090303100402d4195020050040301d105d500803504040004004842e1840c0b5112111a4402e000c409078120220000c0400c1d42140d107041346d04d0200d807000031100e203010441500100070a040207403d11a035610340083c000001203001d004480e00100080c5405030070210702d003800000200c20090300380c6a80700213564403201c04184c21143d11a1002c03920960240400304038561640621640742818034004544aa060032081c6051200240300031401192420155100340000354a403001c0e80e41135400002814050340c4801203400c1801d084138040380d03020401c42e02c9103401c0b9549403029258031001c1a800d00c42c51744041c02d107501e07200184801541c01070300140105000d903038500c3c54a458200302150150100112000304804009040f065002170010441042c0000c103030301002034003401c0321406c00e4012142100d015600050780707 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 71334273 1250 71333023 71333029
    0x2a150501050d05070504090201090e09071d1603090201200c030d171b0d0c05030a0516020705090a0609020307120e03070f060e1f020a1d060910090504090f02 69
    0x340140400c071100c00b41c2c080241c5a031030b01c9070554090f2038026903d841c0704030305590240d550800144070640715240d681c42c141c0e85c0036440e4040c900aa46400281c40d107411101e40d070b403044a60144a00d14841c80003581d54400030f400401000720100c0c14082ca140c05284020342d95459030340781025030300c00381983d840844e00305428005690407420900c01300e000d1490241c034101042e180d0142103400144c0f43d02107900c3e03181d41507004160301610300c14104145900c40c580e118010b14010300e035401061143d03403201c84a0742c8441c0744a8560307800592001c5d000f00038510f0100d0645030810f0035042c00060180c0c4400b805000d90748200c4500010804001b40140c4d01c09007445442c0500c00000041d41c1066243d03a84c5241804400902820940d11000700460030711003400442200e02207010218040080302039050040d4001901800102c2c01d041580b036062141c10540078072140006040398a0904d0001c20081e02c07401c0004001c04101000b00c000c2102d0301c60f4454038410602030342c1c4d911401c0c1043d00c10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 71335523 1250 71334273 71334281
    0xc030409060e040b010303200a080a18030209061323061f080a020a050c070609050f0406030213050c0c010905030d38010c150501090b06070b072a15 65
    0x1060ba9003202d5040002046144c401039054aa0500e40040342c10403001c910b80107000003a10a004902806000c070040013003102c001c10784060b940d00d0b000c1f19032007510030742400c6101502c000b9400501c2d140008440349020300c030194014030103a40024a1b0059036140c1049545940d0345012622070410901085260804d2190005882d000030154003100c100e00c000c01030318010300104c1a0640104000c11014001d10950700d115800801701c0b1107440d914a001800c42015202d00d03400382604024001481c101400b440c1d042e6a00a81000004414003103110000c0000030051080040c0c18418500381d0402070003030f4611a0f019030011900d07840554800030481d8004155000c9040d02010f0303071407410340a042e40111040d4202c2c3c6e20351289420800586074441c2021005080031a1650940b82c0c26007181c1c4028141c0c2d8181c0760411565881005010051003000d40142c04840140000303001a88a40305c1c43c00214030040031031820b01890704071280201c1201204459031504040541108841d2b441 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 71336773 1250 71335523 71335529
    0x303010509160e010e12011505100c03080103020d020d020a03060c17090a0f1502040b030109060b04030201050f0306130e0d0e0f0112150b070309090c05030402010e21030c03040906 79
    0x4020750146244074000751030b240031800007605004034800051116a248146c0c404820402e400a2105051108890721111094040e591040450b19448203100348a06880c080703c642c103441e00d08840e4255003c001e01000c2c0010b080743d0140c500200500140c07580c0c107042c00103500c2900b004c05d0f4045051400703410701418105200340e200100d0108020b090000580c550425000580035001100b503050840d07542c42e0284900e911305000180008000710810700640c104c0c1c1030035004014041d01e41080008034480d5100290000da4140302e05640c01d0726000007560081340c0140300708116840f05002c0700584880052080498202102800603039404c2111080c4500080724241c800440581c000f802042d508070310104169681c0b0414807080340380b03504000240c180c1c541095203410403850001c00702044c9008400716542041940f8901c140180107990044d1b80c140c450f60300210404ac188000206c15a242510040114614905010f0103100814003440d0020141d0381d22814080c0b24000c0c2c2c1e031198 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 71338023 1250 71336773 71336791
    0x170309010513120c0512031501090f0b040b0a11070923011a0901090e10080f01021603030207020112050a0515030a0f020103200406030606031d0717120c0303010509 72
    0x100d144001035681c0300c2c0c82e840040c0f0341c00c0c244245409030400a01c0c2400758440081c045400006004000c1042c14520002c1c031000d0341d030418074580b41d40c0ca0b8aa802c109109006100405102c10701203900481c018088030000d51600c600c402e0040c1110310f2406400e6444000099500c1c0130b81c20039400c4404040710001c22900d50001c903540342901111242c1840810300014400205021605030703c941c80c3e940c0207040d040a954058102450004080c02e090b100b281c0d080c0c40350180c030401000060080c3c0f801120380c402d0756000c104081d107090740039502c00d1070100c1c100070b081034900310b6080051040c40d0044401107800984c0d0310b0411513a107030802c07034064810b100e548601010000100c80164485040d642843d001c1a1404210039901000b2480c1d101103407c201e001c00c01064407580355204c141268610b036810f11501c02045a0210300ea42000c5440350f168102a0782844842c009400c041206200303841160f4034482030380640801c503040b5070f0114504d60000001000685003007041035400c14480 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 71339273 1250 71338023 71338051
    0x60f1109010e040b0d0209090102090423040b040204060306020d1a03070b0f071e0f0507090b030d2106031b05090106080f040501062309090f030a03020c03071703090105 74
    0x2200010344400b0b03020155910940c2c42d40b0b100c0d244c607240d440310002c00f035138040d00d2400241440101076010750040c40451340a60318180802524100240305d443d800380340c0301f0000b61941c80d236441c0c00c610100010b0050760429190000000000e03460300c010180a400c080001820042e21540c410440002103522072095010150034840182c082040307940c0040ba00380002d503241c2c983d18000c5108004200b84480c0382c1518003065040c0300c4d0764000700307107890700c03070029107000c0c85c2c99410200442c1c10310400c007500b5074400540b0542c2240120700c1485d5000304000c1100c0404030500d010b1040e07070140c4e001241c44800013212141405001042a809410200e030040803540c1009001803c00f28001c0c1401c009191600208081c003100794010805000c1d9035040c0291400b407125202041440078000314082c848440000b9800440454071820208098029510b85540c3c8042100079400582c244a2035000410038a00001e1910762801c0d0344100d07017940c0d581c4900d45003000e18211071001f011a0181481 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 71340523 1250 71339273 71339287
    0x9060105041a09030a022205010503030703120b04090c0b0408070803340b0c0414120c040209030c19030b0112020105040504020a030207060504080c19050604030c030507060504060f11 80
    0x40320010640600201a01e0f00c1d000728800083ca0003081d1080a5004007044441a54a043e43d12a070260303010a01002e011690343d840500d5643c2c407580300081c000404801c10103840d0f81d8150418010305038003c001144410454440b200e0b0b0403102e034031104c0007400c00581000f4481050160344001e0604030044c43c2041070180b0400740e15521011000301d00140b25941255583e20600b0441e0b100e508503003081a83c0c601000d160000e0b5000d40506107011810f40400c040c50716000d4007284200c0507080150080d040c0701c00600000c0c1d0404111581d16000303880400d03e560700c501c400c07413950fa2103414445580c0b0f8039608090b200408103810100600c44101d44e141c0141c5d82240c05ca40440c0c90a0b94010ba40f054070040c100d0080c0240e51004102600f020300348014400b500c0040c00c11059110300740c0d4030005902810a01d104d04c07810000301079800400000e00401d00500b17000c0700142c0a400e0071481c0c01f0315695000e0444000b00c5003160283d40d6103868095546180c411504100c031440c05207480c1c082c2c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 71341773 1250 71340523 71340539
    0x112020c061506041706010f0803030603070501030b04020c03190809070308160c08030d0608010e03040e0109090303020c0f011a09060d060e210705010c05040302060d0e01180f020906010504 83
    0x10008018240d400d5085003101000d4543e6000c950007411110715048829a0405079141c03600001c0c0702c1c00940c50100c7d0804a1a0030020040300d010700f4004008004403440c00340154050991700c038500e5800755090000c046405010700042410f129021281200b010302d841015100d000060031903c415030241d041400001c84010440f001d0103252007038030030401800d103403481c0c045900c4d0300035104030702001c140d00340e0048464001305c00740c401c4a0028400c2c2c03024100d12903070340e02482c814500002d003004010005003d5507400074901a00074940545001d030303682e109900d0040c2c001a0100d0503035440144180044001443d80135812088590107254203003a0006070f40c050103810040e0210303545201d800101841000328003010f4486510614174418801c58003803560b084041c0560760b82d400e000d0000d880500ca0f400301c0e42602d500800035403c020105404400610b80d15400e01d44a641e94040b8801e00b01000003202681c0c0c0c4a2103002c0b001c038219205010144070041c1400e4103110b030912041c00600 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 71343023 1250 71341773 71341783
    0x227060307030e1908070c06030e0d03150803040f080601060212070312090209011509050409050a0b0a02070804030f03020d140a0c11040c0203030906070f020309041e11090112020c 79
    0x120078a00030500c42069070001c1c1c00d2030744e129450860003220b02d010b48204084040948110f40c003500720f90b80c42da80d80f0b0700150161030100d00581015000800c2001c21a80030350700c100c852000c855905459292520380f49071469001c3c0c1c210362025015080200004c0300c0421403035001d400300d84080e20124502d11039560690003805130050500001c001c50b00800300c09a4001c07960310b90018952540c0b543c0d500541c9210920703100140001544041000c245420a40154661658440c0090421001586440303400078009022000b046800700558004100004013410255005840c1007410384d07450f180203031810f800801140180034010001840c5004401d040e500380c08804d0400c10f24026040c6410f64248040300c003019030041c545195004040e42c000702441c4104c801c5401c070389440d210064191190748105a031000181d104104070145403c16401c030600c111820b441010f40f10300d14065540985102c000e42c4500980081400700c150341c1e002050740703005014000118605116142c0c0e041e01c43c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 71344273 1250 71343023 71343031
    0x23100909120c051006030b0603010c0e0306270111090901050d02010801031101090b1602010f140f0f040302030114040203010c03060305190f08040f05010206070f020c10020f1002270603 81
    0xc029080104403d00009200903688000d18080422101d9280c0ca84003558110654420340a98a80540070390f40601034440e0054858004005183c290740e0302540741c101501c00d4203044881d2031513098400400009000d19070081d0556103080c1d4941c00103109211604805900c458407908540c3c800b00c0160b600000e8450550341c0000d0345a007501c02c840c0059400780d01031741c4500303035401002500c41c0c1d1140250703041d440094400d90314010219154001101d02050b040031100c1e00c2c52080061000c600b0610000340808005059070f00d0902d5500d0f00001e08507007241c580b5109000e00c6808003c11454280302c0c0311a80125410100f01e0b090660310380d165191402c001c18400b408990003003806201050b4085019070760300800c0c2d5650395840e405810901d510340e220307050240c4901c00103d02c0040c003911501f041c00c103003540140141103070802040058003c2d030760450254001c41a03800c5c8005c034180407264070990480c1d005070b80c4404c500000003032401c00e10350b0306902201d516050082556100c00300e90700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 71345523 1250 71344273 71344277
    0x90f02090d060f0b0a09050109150509130c0506030705031e0907030201031104240f05090603040210090302040c030c180f0308070303060f1d0604090b061002012310090912 75
    0x751040d202c3c40c21004160281003150702070101e010001e45080503030001d86c140c8a4084051000e020907010720104003a01e40039a81e4040081070000300c4415825011405c454008c2254500d200d543d8030100f00710307a0040c1e4150000400002c10400d240d4910100c98909030000e075004092032818404881e00da07a0300b800020704058640e10741184494013a410340700a82160500080042c18141c40e040e03d0310300284000c80401d2300d002c0b0380d01c034642c042e8064520121001c0c114034910b503965800c1100008000c2c800009004075070801001507212442802c10844c00744e100080d442c9441803028000c441003d00a0340040c07079a40041c0040542e00e4283d40c1107a91024240f901c030489454141c1c00703400f00c1d4020203d40080188001040052182001410456084103524586aa8061100340c4140f040f001c1e04503101750300071640c9800c040d00510802c425a02c00098100c00240030707078140300540040c0243d00442c00d014800342c51107402545004041e00d8008005184c0e10b96208000349a500c940101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 71346773 1250 71345523 71345531
    0xf0f020703020102060106030e1203070f18060912080c0607080a0b09040512031b0a09050103110705070506090d2906030a1106030604020d0c030c030e010c1b0602130f090f02090d06 79
    0x20500c07804004c00e40c90807000340c0c3c056848cc07514070070040400c1403010b1002e001600107a60b8407451850141c104060b5501035546a650505010315100d5414410400b120680f034200700340804910180800d5018100c1c40d42e0784a00e40c24180c902400b90b410001080b81f00e00c881009000014000040c410311000c068144140c80360380382944403840d906016408201c074240021040c40300c5902507901c0050b900300b600e04000426180c9481c600a0080c944002c145d40c0c07007400c051102d032600707101070840444010008400410196a6070303603401c80303140b101725010040020141019441d4000c1540c452420382c01000141d58985036080401c8240981c0350103a00c0020216141da103e0350110365010200301c40078000c40004d164018000d0810300007101c0000d280058103188100107018292070f100e060b03a115640a540c203501c4d00f9a08204160880d1225801c100e2224a0519110f9900c000c0c00700c04800b5907c40e140c1654a810780316814a80d00752140b04011700b0603d40c0c1e8020012072a02c0e00a40009 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 71348023 1250 71346773 71346791
    0xc0b0618040b090703050a060603060609020301080a02040f060b040e04140f0a1e06020705030307020609011b1209060e0601031b0e070c02120615010e061603081003080a0f0f02070302010206010603 86
    0x541064603540025089000300c0d1f04890078070103150084400c0b244909010854681c0d155000c80881c04280500c01d096001030000300054a00794001da410841d400c600010f816540e1201703a2400d07440390b03001102c048420801c100034480390590700000924004090840f6010303401e520b50b1203581078400140000035412800e102d41a90700110800c03d03a0000003156100903504143d96070340c00843e1303004014442e050000e201e40106001d0850310b00148440031000c040c28800c1990f22032511000040f000307a48a820501141460080c2c070a514610f40c0501396070350560030100c0040ca03100341c007188031001c8484100b104501112025510201500d000c0b00445c48501c0003900b848542c8400c0200f038070501043c4080f070031500001444149090300c504078421030310020701006010349010f1f110580d02c0948201d0100340035072503459121191000f9012940d40740d84d100300050700021480000194003850000001d5084840d00140100318001030171443d15560000b03694650500841c42015151100700d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 71349273 1250 71348023 71348041
    0x62114060d080421060e0f100b0409200a06080114042c0105150411040510050d050405060f01080f0a02040b0607020409050c0103050c120406020708070b070c0b0618040b 74
    0x1440c080c00790754a061884183d02d401d0703080703c4c449103401540c07020728042d010310860800058240800740810083d0203071045071b5682e400200315207618140c110380c5070024080000c1c00840548041c0c1501c03202c1c1c0305a104030034140203045d80c55030004024400360b03030014040821f25941c18410040100c4010902210700d46440d0355441101c04000702400030ba14008000e00d8040d0413480c481d40041400103084150741041001b560380d1100740d008206002c01c001e00c42400c1c0703110100f10391011303070800724544030044da80b141c100c41c000c8a041e21260442814801030700c4840c480c00d4010010240101142d01401c949152100d0302d41c00d0083c0324035503a0810100da0384401d000e17034010640043c0200301790f07041c5007009a1201003e900e600c1c0004d207040001001002e81c0b0084da00301c58101204496075694903030300c1d03070002c1d0310001c419a03c0a40c00e00054000400702c1962501c0f40c3c41c00e550301d050000f0a4581071400c086c020304100e2040c0002110007040051030102a5402900031390040903a440360140303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 71350523 1250 71349273 71349277
    0x309040b0d0b040506040605070302131502030c1005011e140f0f0402040f14010306080a0f030201020403140f0d030507020312060d0210020318010e01140a030b060301062114060d08 79
    0x103200b0001c40b0100414400046181c0344140e010b501c050000d41c2e00c41508801b2403040b001e10305818107030424140310181607141c170483e030310f0341c2c3c3c1c0101d0f45800700081e1035500d40348183c810307035040c03d85490040c00356246441360031151070200050406410b04009001c03110020004041c0c0c058444910b03000d4159491101e03103400b04001600c00c555440d03e90014801712082d0b030282c0001c00111618a08182d4403030312511045580c0540501a1048103503500032103121400e000b0380071903400f40000700220700c0106504d403000045c0c4000f404420300038154241030155240503070092510741010840704507000b204607846464541841801079884c1c0c00011a04180c0900180d000080d0400384242e1980010041a9500294030041c0c00300c00740c0801110300101500c0000e00050303540220128401401015040c803e5007820b01069150208020130210780003680310600080d1042c130083c0004000d40600c0041042d80c0c4030a00103020a815214050000584550f020b254410440c5091000c2901 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 71351773 1250 71350523 71350549
    0x3030f0a1815090302030601050f060f0a0e041b17010303050a03020a02120705031308031305090601031d0606040f0515010f0507171206030a0b06041503020307080a060b030604050309040b 82
    0x6525140d000d1030312801003050f03107140030480c0a40305850000c2001e140644800110580c000c1144e40717401c1001107590a1900102d00400034420600a00c03401c65903903004444c0c488244081200414108100003440c0160038810b07260f44070121801070020070360081c11034617101801c3c200540d662182c02800c91810401da80c142a010102054a034100302010008060511403282c2624a0a03207500040e51203105121002900c1480094200043d06000d20419030188050500207080b40102d0200d05000810803010140b0740c201d80c1c2000032515051248421404040c10704020030f1411903441840030103100c54560500c2110b06280b40c081d44a0300445030313095880300b00c11a40e083c0c8980b1190076034108028109a50382d030741002910350b0070001128445250040c0f1082d940752030328000d100041480e07044031200c1c21407214001c070150700c1c10440d61000f0f0585c4d800800c00c5001a04100342103815000344244130350040410f0101083d0b0000903644140c600f2036001461445010000700d000298074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 71353023 1250 71351773 71351789
    0x11205100308070606060207060203040b04060309030908011802190305060f091e03030a14040807060e010f060617010801050f010e0702030910030902040c0203030c0d0911030f0a03090503030f0a18 86
    0xa0000f0410040750400c00803039500744c0880c1e680755210002643c880c012401143d512401c1800f080061503c207810104446008cc100826503030b45980841d07094660034080c038032130201c44041e07020450030084074201c00030740501c00700300c00c042c25555410349810001c0d29800040c505000410186001488860042c40b070203540103418900c5224030310b850345c00442c2c0c1d00c084c0d036140c0602c0c20403030b40c08110003a20890380184220b2414510356202001402c81038140351056585664082c01c1a00c94860355001c1c00103500d1303a41c00d9007128002c003186e0340c00580182c040c5074106001d0002c80021a400141540e900c550100301503620030408a186002d05036046901c01c2c0002044d00c0202d03050740c80310a03441d009940c18000490f40d0882640d50b44400e90f50748003003079000c01c1440c1c1c401c002540130810710381c80f032600a00440c000a002034988007a0b1000d0000c2c40d0030090308441003540203544d2400a000a402843c28402e10036040d1200c3d000780c5140406000c2d84540b0442810501c0f103c02020302402 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 71354273 1250 71353023 71353027
    0x908090d0c140102060411010302131802040e0105100f080901090c030c030b070206070509100903080f03011508151201150306061e0f050111070f1503050f0402011205100308 76
    0x3070904529035041842104180348101c040c0d65800c3d4404a103803841907402104607000300342030400441c000c1d4004180c03154214412200072491050701c88200300c008200c540e0150300c40d07051642c0b0100c4201c040e4040381c4a601260290380e18140c009121500c003a1031400c00c0746042d690f00b40b07031034090a10391000078111214040c02200b0000103070b800340192130140f07403100d089a0f500403041ea52417038252070b00000f1510a20034900c03e481d268201c4170840c6d150346010100180e69a88044040d0818404010224008001802000d1440008001514491505030600d0034500c1022010411180705e490003003540f11244890441c003508100d0301006c1600108803140c4d542d00300100188414001c582001ca498490003a0f0091140444000d0f02e1003016240304d007a15100064800044040044040e40102600010840b07a181d034030800807c5071000d0700c00d540084407002000c03250028503402075414130b00305200c0981d0f8000000d4a0501c012000000c0980b0f8208001300402c000317620082041d100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 71355523 1250 71354273 71354299
    0x120a11030f040e090105060a1e0807090506010f02030a120f140a09051009020f10031103010303020106080d080f15030f010c0216080a0f0b13080a0f0806010302031603090809 76
    0x700300c001d2040300c185010500c41d6803101041c00f401e88005443d20744e80901404814440281064200c0d990041648e200d01d0440c0e0707840386550304001c626441080d109e40c0d90b0782000b0303980d41c2107158801d00306040e2001d9480d00d0958000074003241e504907112010307140e40d000c036540050000e61101d502481d500c007840d002403803c1071514000d4603440c00d0449807401000d46900343c1c04881e0003900d542175802004d459000420b0703018000310420072004001010b8489103049942c0200400650203136010b64000f10341c1f18104015185002418911402000803c0e420040f002c000400c9a540004110b00180c420008041c00203141c4110001c408825510b001d001da881e6a400041416200d51040844011103907222040ca0b00c0f0800030b40040d040001d8109140c0005101b8250340e5440359103c603611381d65100c01e8882e0001601300c64102c801140c903007040300d0122504881c0055202c582444d0961075843d04454410400a194100d20b041c1512108900b04011403801542c4084502030400301c52212 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 71356773 1250 71355523 71355547
    0x9060209040f0e07140402120708100609060e0607051c0e0306010806130311160308071a060303251505180f0a020d0213050405010605040b0301020c120a1103 69
    0x803041414070300c11882c00048016402150041d50441c00300500505949131030403504840540e40403d10650083d403c00c511a200d103003011a0754025002035590b8002894045561005504250825014000d000104005d0705070b020300b840c0d24090043d9222600c400702803500c01e1070040800051018050401d0b14541d440303911a1100c41c0030f0314200c04640c10b6076030340c0300100c4d1a03017003e41c0c0344030080307803088000b201180c01009810b028100c650212001c81d200c2d01485d011310f12950300f0484049100050a405005246803a040d07480c5009012040300d081c0314000961305d100c2e8030307414181196100240d044d120010034200c028144c0007200101440c40580d80b9100030b00048580d1540340302002e281d000a031100140c100c950b807014074000d202d940320316000c100d0300b401040c1040340c2c88512070f80105000400c600820f8095840f950010400608120800007500c105243c480d00980c4180a00701e003007000000c11051010f40c062480780d0780c0d20482c10480390000b2640350740352544000540310880365 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 71358023 1250 71356773 71356777
    0x10f050c07060e10090b0d0908070b15010e03060f190605060301081005091204051302190201060303020d0e0303040902090a030f0506010305010501061b120302091008090d09080d0c03030f090602 85
    0x1800880340f54609054a00e01541c1c030342154000c944903080180204440c400e42030b4081d0660300d0103642274034284107090b50313400304580341110250460b40e214800e81c0c0035940c2000c40100d404e681100a01600d1400c131240d03521200d0000c00d41207003000404d010300140402544140064030020308004d07038940c2c40741c901070340c1c1c4e0f83d40308801e4890390b00d4200000e480c80804260320100e456a0701129140c6842c0004115010034480c0044580b10390821160000e510907060440b0800160b40020400d01d02d14140681040481e15078103041c44100c040052203650f01100321000d413040d8400068484082e500410034020040d000200161409240c84003400030014401e4100c03480b07280240000d81c6c032000112968880282d600c0e0001c08100380a00c000f0300d0035130034050414168a401800c15a00e080000d030003406a06000d03000c1841e0030f040c080030f0070b4180803065000d4030604141103210b25200b2940c0c1d840310b050742001c04000d456050101090705c40e41000e00c2c40300310010140940315840c1420301c025 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 71359273 1250 71358023 71358047
    0x50d08060f1c0c081513060b13091502030601050d0e16030b0f01060c02060904020717040b07060509060c07030f050c031c0e0703031b08071b030218060d02010f050c0706 74
    0x20300b42d00f400040c804800550f16040350009041ca400580302d000d0300744601040303d007040300d0303003a00c5076010107140d00c4988801c6000c2ca400c080206500020b4101811040e2142400940c118010410400d4a903008011501c07420b40141d000100c0c0540140407d0a01b5460390300c040034180e20740400801d01551040c01c5000d00050156042c10745d81c0c4c2c07030056a80d003444201c020740121060121030000d00d0142c0c06031055a000d411194143e07540c46011418039400758202c114501c42c089050800d0244900c43d240e44420400000c01050034600080c031168054610000c0411034080105084248954142c03101e44a1180c200d9403504407884044210401640a125400d40783c64090407041100141c1039046070380507160030740d03c4240c0207813002503401c1c58501500c480c0c40c1003143d500040d40500d000498074800064441c091403d5204001210610501078003030400070324240019503517030104000040348c1c2405c08009070744401c4807e407090f0164030315a1456001e810000110faa03000038a0080c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 71360523 1250 71359273 71359283
    0x21201020a0f0f0801050916210c0e010513030b0c0408030708041406070213020c0f1207030e060705030d0b01030b031516020312012303030d0c1209050d08060f1c 71
    0x5180e100340f0044404100900c03c040e07001c00f040e1b0104646110210480d00004004c1c94060010343c15185060390346c1d00141c40d5078108503a10484d00000b41e034404040200704100740380c590302e4041b40065840c100011800060022090b04005c158030f440f221044030010855281a80c0d200d41d114109168207420502c641030280034601c2000002d0310f402c0c01180d01d9254002c100d240b614010540d020001d4101d0030141600d8401c40c0c403c04004407081280c8100480c81941281d42c5004030326008061103c81c2c1909801201c086c411840003c00c0441030720076001000000080c10071441780100c01030001c2e10070b115018021002040c041902440c4407034846d00e0703107031030074040e078198440101d039a44a184011402422801d0041c49484d84601000a1442c10502c0702403804082e400000c0c119801a40c82003042030342c5c1e50b511000ba90f0441840212448014010421503085072212a00e80061b4040b0740c08100c40e41e0002542a505d400900f0081d2002814011880e44076115080602c4085242615 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 71361773 1250 71360523 71360537
    0x906120312070302181f0e030c1809010f060602030f0f0918160206070504120c0902030c0a0f09050a05060a11010c030b030c031c050d06150e10110606010c021201020a0f 74
    0x3803c1ca054081c0f00c055506c0e01c40c803260709000c0d0048812800c0d07504100e81c10b004e058646045030f0303a05020b2400c48080060b1010841c00c101907803500311395402e00c518000e103081c040100006c40d000710544640004049250340d03070b0569442510b20740d2180b001080e51209801c401081d01860005005201d404c1100c50400400b074414000c2c0d0762064100c4910b80014000c0001f40454480708000c10034462003028418a05903c8018080590701304441d43d80d005180842e00d1814964007100c2401d4134089030600c0b02d0860b0600005c1241040079001e0b05024400019003015210700c221407484940f03001a0080000c0c4050130802006002828030040c401c0c400d45400042038900814211076200403075618840083c1224403c0d555500116400f00915a840000180c260490303405d81c0464000d554a2400b004e190b903040040c0703129032100c0e0108022801e00d00340901d401c000f504903000f41090a00301c0ba18440c0303200040d0081c05600104015500100302c118401c1e4010b80f080d4052112621622 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 71363023 1250 71361773 71361817
    0x20a0e010e0f1302070503030a0504030f0e0d230d020f100b03030403030806030f03040e0f07020a153321170307050c06070206040605070e0906120312070302 69
    0x107404504002a06601c500c0340c24200781a40340c480e002440c102c415001c003500b400c981c0e8490900319003049844500b41910346041104150380034810f8020b84881d03042ca908044d0008020581e900b41e03024008103c1c441c40290358884083c5401c200d02d0024074401265105e40030741000035216440c481034101c0300d01c40c0c40003810101e0758502404060303072800340041d81410326540342220b4620f4044c1685030140100446040b0104091004101030b00c1619601d00f100c2c14441158441c6183c0140384100315003194880c8000205000300f001c44003455100c022034032001ca803c201c5c0041e401c14180120400d0180c038101c2c15490140c2800040702d1a1821807501c61030711090003e210b540300303807008007451144a084043c0c640081c0203182c003d121480c2c85402c1c02d0005440fa890080d01744e81100c05a440041000f00b041002d000307141c1d0282849c0b520f0817883c280e0401142c280d1201a003c0e51046c0032000145600720020016500c441d64002400c40d0b09040c03269001c0c000354061501100042d003249500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 71364273 1250 71363023 71363027
    0xb041b091e14090408070219050102070e040206031302150703020f060c0703020709020d06090501030809030c040b10050d020f0f04090f0504020d020d0507080106091a15220504060603020a0e01 84
    0x31000c03503464403002c0c0071000e096420080320650041046034802001d00c6a5005615005001c0000a490f41500041c403410701001a00d001026400710140d100c003502003000503100d60094036000000c02403400040344051002a907114162422000d40c22004a98101403641c0010400400b00412080c0c3e141a2117100c01d10340075100c2c80304081e0150788051010400100194010320358811841c10004140c1e171608100400d0721001c1e4800e460300c000210790341100d0f280c18050318a26107011502000000402008a0f1000e07504900070703407e01c0400700b484840241f05404855001e90b1040d0040e65568945400301c207960040d0042d0b02c410303881d0038080b04180480d84101c0d0301658001700700f441400103550070455240c40349138003103c80b405400b01c0020b45007130074003c0b58040c00c51180e02003102c4c080b181c130100e0412a20711465109480700e201d02c480150389002100c0c603c211440602c41101c4111458440303075112644040d070414948500000e040c1c1d855409804818000d40e28010050114001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 71365523 1250 71364273 71364329
    0x911040602070b030c090406030609020108100e0a09031404060804120206010303140c0a0b010b22120308060a030b0c030f0a0c02120a1103040b030603150702030306040b041b09 77
    0x1440340942e100c00001e024080c021409180d200d01c840c843e091409464401080c180c49540d801265a2520703400320f0303001c541e00191100d52000c202c1c14000410780c50300c10b0040f20418080c1003a032445507601c81e20014103100c0c1c0811001e403003044552a82d110750702c072402007103e1800c80b030584244211002c050580fa04c0440c62034120f0750550360300200b0304242007507403602e54440051814180301d40d9050760001040111030b607000301030050f001c5131030b0641c0759050a03101d2042c1c124804080881002405076070080400341c1501500751400400700d65590340864030315a01504050080c01b14407040003107061901e4000c5204083c03659102103a521140f003940142c4070070080810150f0408141083c1600403040980360801652500720000415000e0843c02c550090304080c4042c80000200300140c2020000d1440d000300b881e00c50841444c0100b0000e4590002030703c20382c4601d8507082c00102685d43c54100c036018004c10758980c0000c0707109039005071030610a84110811f04003644003507019054984a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 71366773 1250 71365523 71365529
    0x3020f010503070e1903140708011a03070e060d170703030c1e121b030603050f060105060f0702190e070801090515040905030d0501030c0f0503030301030309030f0312050a06091104 79
    0x948409031080d13401004030200348206031642424000d040040800c08070340c0120107810501c03002e0034003e400c100020382920b100428601445000300041480341c0c80000d2144101ca0f150700d812105911400e00240c0982e4810700082d080c4040c042035403014121080061510340d101e610104007140d42d07003005903550300b1544108502c1c4203541c49003510742c600075012520716940390100003603d621001880d01c20411840a1500000e80c1c2340340a10030844104440c025091200c80100b040e58036240020b0f80a10540101c03904a140125078501151112943c0e40701f14510600d604030866200e18000b81b62407401c50b00c42d00011b60740c000004101010344100741c002d104009040b1281801c8500b41702c040d0002d01801c50349440208400318403ca107501c07a1901840c450301c01d0f002e80380d1400501089a00907900070a210390810001000080d0f00642800e00b02c0f50b01038001800e840140c01c040c0c55402005104826460800c01000a0010680d004a0943e490b409040000a1404c0c058240c40c0c01140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 71368023 1250 71366773 71366777
    0xc160b0403060507020a0602040f031a0c040b180d0b060103180503030112020a030f0308040b010602060c07060b0d020d0803090d0518060310030f0b07080121060c0e091003020f01050307 81
    0x10040c0702288076030304419480243c1d40100ea11382070f0035503219012030b80300f603104504c03102d640b120a008001050b40d01102d00d00041c0d80021517800d209c00307504d4051065111b180d00d10383c4009201021a902c110300b00030f020f5402003544407820141d0a008030744580480d40240041c1c900a040e030001d0352004d11910700d0365000740c011411682040e00240c0c40e107001c00426603001e14803010000c001040300052051b610310030350360045241450310300003100e0070040e008070017035404c240c0c10450311103192002d80c0d12113904110003081040420021030710584540c00081d4014201c045500140186e0100440c001c55107a0100c940c24101448200d030a40641e041004054204440e0700003940b81850142da042a441c0e0351148406039240e44c2d0800420017a54210368070404e0801300100c164000c0c0b5418010082d841e00010f4413984040000c1d480c8851050041c0181d5a660314900d443d441400700790140080034080111a0a2030154129601050304c003c034407400712103c140c0d00e19440352007900d000f4440340d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 71369273 1250 71368023 71368027
    0x40b0f0c0a09060518041b030507021506010c060e010513020a0b0a0503041b080f0a0b1b0904091506080709051506030f040203030706020f03090f03041211040906020406050c160b 78
    0x84040700c0d01d62101e61800300c4e040c140102110b00da0344a1040c5004030195aa21501f503944901c1d01a0568000826810075034000081c210030b40058141165801030302441d045c0504546c502e081d100502220440012941c41c100400408010144607800b0385030080b14208049940c54600b03240900ca054036405c0007407802c0c80814006031072844c8803008805a00032525015441b8070a8503e489084440a00d1540c07008001209000d03940701d196801035425211541d08110f0844064a28461042c10341e000e40d0f035411000e010302140c5080018001500c4106021480ea030f9203a00c0c1d51405580120510985444049005480c16888040014001910745030543e030f52020a102e90b14402030043c1d826000412400000400c18401800718480030030481e9202e0070a080c0b07841c42e0032001b40c1d10400070f80c02004280f065418410620004a501c000041001e40c0c6100116010303040840c0010811400420040707a0507800c50b02804262241e42c0440e44104820202c031100d80c0464410a1290320003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 71370523 1250 71369273 71369279
    0xd140406050901080603010b0d200405060a03020607050106170a0b010801150302011206080312041401110d090302071205070806090712140c0915100c02030714030a0b040b0f0c0a09 79
    0x49213901c1d481032000f0300018240768240041380f607100705c0000c221142800c0101681011400040d564013540c02139a04009030703d04900841e40756202c42c080603108140c0440c0100c1000401d40081c4090000a642d241e609081e079403905d5540d940f00c24048500303044510000c50141414480c10f034142181000701042d1525507001136501a4065402846094a408020481c010300300001d000c1e1105104402000f40b03045c1c2495091114055800405070741010141c4260320f03140010350306602442140041c1228403458160f00c0c048855000305001ca041d12500024088041502001c50b8500030540e8200c2c1d0318017490b580c40740d203540900082ca002811260000c21998800d2080882c1c201045502c14800c01000071440d40045818182c0d8170001f002d003440d6801c2c00030a0580400043c00c1c20780001c080c0e40e00081e00e500f4107000d0b900282c0040c009041c95a5003c1140c0d20f00c0581051100746242064105040e50500880d88a4072041058010910010022003295054105650758102d810300b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 71371773 1250 71370523 71370527
    0xf03190809010203121015020604050a0602030a0e0105041103060f07050301060305151e030106120c0e0703090b04030c120c0812070504050402040803040f06080906070302030c0708030106020d140406050901 90
    0x3030110740c114403090105619090014507401e0203003400f0900c42200c00c5c0307080f2000304045000c080034400c40d0084028040020700c0002c01e488400c0c2d11010150b20303a41d40c180184000d04001180c020b40e9800d010603c0280301c855801e071720f400f420680a807082a5078241025043c220309540c40f0380000c0040004104191080c0d00480d004142842d0200798043c844000a090f8000303942002500c129200c00e6100a20b424030070a40240075054410f400d00d28a40c8401d0058101e600c14008156805000549064440d41c4208042c0e6400440200b81d4109810000c00307031300600100315021030f0300300c0900700341501420a0845095218001c1e52924402d81d002c0c02c640b0401500140622400f44004100d030703600c5001410180242c2da0007142c83c1c41c5400004101658241d02040500400e5020301a01340f202283c50342d440740f070ba4100541d582c3c940d807840001501c1407402c0684105030200010540d2503001c690481c840b845541c03104a08008100c0070321f000c2c421031254002182c000c2200400300c2d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 71373023 1250 71371773 71371777
    0x20306070f020307060614041a030a080c010e010213030b0709030b0c0a0c14031e161202030f041427070c0312110c0609010204050307030b1314010b0f031908 69
    0x2036940b0541381040e00307035500e07481036500513000090100e00814032100342e802d082c41521301c660741e48022025140e030341c803000c25203426091101410305a40058a1a90342c4c1c07003500f0150031000c0d000000c55481d4409541c400c0c0c41c0040340004c464a143d00310122729400e1180003007200350398015032510403544903114600c8580c0c1c003040700c0c4024010000303d000007107000c0300e801018190814000d15590440008001c12148004124407160501800390390b01181d10381e4004440c07a648054000c08849441c102a45140580c0c0319070003180f4000500444c0d458900d2031510f40d00c2006441101c1440014211076070060000045031001d004000c0018120700c0c440d2100c4c0c1c41050190800d21100d1a2500278802602c40094031a400d100f00018a4185100208041644107480c0c00086007480d080000080d1514594800030713054509003004211440300900d10104443e600055103a28120300342004c034040c3c0f8642ca106ca11034004a614841d0b542000f0544026031402c4042c416003401041e03942d00441c0e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 71374273 1250 71373023 71373047
    0x204031104050406140c0a0906032a05130801090201030b09060f060a050d110307020607020a030537120b0402070c21080705010e0c010314070e010201020c0d03050406051302030607 79
    0x82a19140b0a030210100b2003081703030142e18001b000d95a64007603010b0240a82d1b5840d030001d8101807a00c04800d118401e8901044000c2d0441851401110180402242e083c00303400342614404058600019600c2415803142c0c0c8114404c0c3c9060000180c072904111508008a41403600940c1d00c1c81e07600700618101e0010100c0c00303158240b00b82031406510780801203e001e90102c000717604000050000903901004140d0b40080725100a20316031855980090490059442603510440a05d0705907050240e1042d1405a01070410141110b142d403e0034010510000c403d4038007130051030803c004050742002d00803500400e80200e022041e003850501507a40440d1202c1c41504010741c43e940c2000081c0c050001442007070700400012074030000200b800c0d41880300c0c0348103190615142141d03695840d4905240654005014103120b03031141130280042c0d000e0300c1001824242800f41360b190015054069000b02e015a005501c00c21071030f950301945000c5c20151036030107581750b801903000a400300d03c43d980307031016 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 71375523 1250 71374273 71374283
    0x210509030a031e090b010503100b100e01021e060f0603010b030705130f05011d0c1804050402010210050718150203160f0506010308070201170103030e0f0105070803130c0902040311040504 82
    0x280c0c000074840f24201c40700010100c4400c03080000401c060b10b010010003150000e03c42080041c82da000001560b0140000f0001040c00b04c401740000c11a0b009004941500080c006040c400d104405500b41d101d030001c40781c8100409051012039900d040510031040301c140c01030024541da900b050700300a6903412160602400684a14000c03011804900402d402040c5080303a030034181f03a06d100f9540014500400704194040c05103c484c0e03042e0070f200104c402c4030500b030b50001040c0d201d5000407030401e188941884080c0e81844141301c901d03607000540d201e000d0501c00c03250305056182e09006140e04500f03e05640181d00c03e1112910441c044101c00010030b109998200039149140d903014180403003640103503003811000c603129056582140c0c0644640c6076840817559a0340c1141d60140400841c0da0078580101c4401501c1701d6284d000f00308640485810140454030707403074a5017114501c0992084104c5244441d0400050003600f43d00031b07542500d0b84400c103810903100c24410704c0020f140003842511 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 71376773 1250 71375523 71375561
    0x7120207111207060215070917101a011103130905060111070803040501200706050f130f05010905090103082b09030306051504180b011e210509030a03 66
    0x182d500e003a0716202d0040d000010303182652130044084d050966403055505003c2c0c0d0b0800304007100350301940c010700760348401070340100408040c4110380c98802d82d00400001c00c0c1ca080d07105140c030107410ba5641d42640c8241d88400100c4240705c040f076102c3c0551400d8075105815003206120042c107a4003c1588080107241c0004a1002515103d140030300b240d1001620380c0000a0038000c0d56401f5036205110f87d0304840003001006030802880d90740e8482c1c031442c000c000300803a890810043e00d10843c0e65000d8682d141c900380340d07114405c1c2c59400b00c3c20b103d8107021480071000004e140c00d103c03440604a80c1c11807115030400310201080c01002c1030b40c002c00c2c05a174000720384007030480800d0301c03684240c0c1e0701035900020f000c0c6c100810b1180d104134041842d540c00d201031208100d441d001c0c00c15040427410850000c603046c0c200c0c50050380d5880c040f180030340c3c40d0159480c00b200e000754009000d101421500d0103007030000386000c41520881d03c0a8403022003e420402c00341c00f066021b80c0041003c031202d4420310f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 71378023 1250 71376773 71376803
    0x506010c08030c0705102f13080f0d02240603030d090602030a060807270b04020a020a030806010504050d12020f10020a020c03030c0304050d060b0418050f010507120207 74
    0x40704a0b407040300d900d0100700303012640400340142048036012003080c514042000030318a040b03200849103000c0300c0c1005440e8102c0860030356a04001650116142d40c0c405400540d11034500c2600e5004103000e52040f440362603d002d030301d184002075061340e150341c3d044030059a04080b00000c00055004250541521007000402002c60441c803e040d5018007a600060f280d0a0545014040d01e2082d44040c40d142d0000e00d0901c014550032410380300300100705143c0415400c550b034201014100c2d0f0003003a42c0c0503102144082a00b0b8010942200d0180b296403011169500e00f40150b40a008a0280030307080300140d8056000291480d5481c42c613010540120351034008e10400702407416001000a82243c1d8020403e482d5884c0c04110b03490310440120061401c24640040f6a0b82c0c90040e03100d5a8482c0e03900b11081824400300da44402d4140b200500180203254080f5940c0c1079030a01a03808488a1160303c046510014041c815140900225511560b8080e07a002064010390000c040070f0315039203546003c00c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 71379273 1250 71378023 71378033
    0xe150310020307110a020907051602150a020d0c1106030604090f0c08070e15060306060408060a091109070206010e0a02090307080c01090803040e0402011d130911010516060506010c 79
    0x803805460240540e5a140010004154001c12240e194403503000280d0240160703500003e06502c000c2c1443c05c42e80b02c00130200706460740d2401c4040a5000503c4010f00802c41d0784450080140c0403054088400400c00070307000701c0b441c007120f48000e02084803640200355186005401140c00080042010032004141e0300c034106c03510b194032021544040c1580f0704105041061100d40001e113035030380d80700d201840d082000c85400c0b6007400409224400000004626645010a03500500914421a01285084110f200003005510300c01d444d4007521055000d030074604440101c0c403440c125401303030071103900c0e14224001d10607000d4202400290240301c4d29103603441c10400c0b98000c0199230020700b12801076600142042d09c294200c0c0c240c42d042004107008900134480d900b6000355080c6824001a11241840315548014640c5203600c1280e40e480c41900c003000790442007480d0f0107480c0850202c940030005403850f1203620031104c1030b514061440f03804200280d01c41580400c040c180060685410390715 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 71380523 1250 71379273 71379283
    0x150a080403121503170c0613020d081801080c09010e0f0111010c09090506040207030c03080c041809020406050f010c030c0501150303050721080c030a1d030403051204030305040e1503 80
    0x241d02c18509010800078070090050b0508281d110860a0b4034015001b40d025032030740401002448401702c000b100c282151a280c00041005030849500c1e51210045a40a0601d499408020b4005a0340c4c1000c6404400780c0c808441c0152016110085c040020780144003844008212030390610a8507000515032403828022140c00b1030840ea21101d50b1402e1036601001c590020b80054040c43c414402c480c00a50080d00002c1243d406003810311017681d072000b41410718840c540085e5001544141d0100b48550030703411148046100302c81c140f21940d01d4009004000300310369030b201d00240200c9142008030740582042007030385004200115166035070140f56081032050f94412000503d00003490014001000011045503400f01720005140502e03000003020a4009480000f0000c1c1c0080411010305141d4082941c02e45e00034445494400f684426030748940140c44152114011502176020780c6400104031800c1d42e0307050f22041e0506080072608058154014400c07004102094100b00d25940c0400ca = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 71381773 1250 71380523 71380541
    0x210020d09020a0b0403050705090c3603122b020c0705190302060f0a0c020d0b07090e01080d03020903030c0627030a020a0204050a090b0c0406030605150a08040312 72
    0x10100c1ca2041c20700c144080030034258481c41580c070080c0010b000191020401c407007115012202d92046803501c0c0c88126452007101d41c2015200c011a6008461101440a112482c4070840051005203040c0f018540c072840350b9000c240c0040742c02c114020701c05244103c0848107420250000c2582c01d00c80011a04a81c4256420405984400f000300014a40044880c00d000000d00f01d20030318924581c00700b80305000703d0b100400310840c08280c94004030f110741c060b480d62940090000031407101c1d9045c102082001524100300103000280007060009900701130034100e40150340145420b0080040c00c5009400004040e64140001c111848101c4020403000d0f0140e018201994500d90110196080100c0301c6104034000c1d070800d02800000340d0300400c5800040d41c055801003500d030f0310454040d0090010a1000307000032000c0342072161700c88022024000340c5e4840d8034200325a0346c03034000f00300002c60003884003107880710104880ca00c1113201d0707a0070325001b81c881c0c00e1003080d406042c40c0d0341043d91300701c107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 71383023 1250 71381773 71381797
    0x1e0f050f1b030109020711030d170601110a0b090a080301090c0f0c02010c0308090f01060320010309020603010909060b060a0302070215130b030c07140303090d02060606030412021002 80
    0x10038058840d0824044039041400c464600010303150024001c011800140f10300501190701107119010f0000082000744040c07401800e90304075942d42c0c60041d10042c12001c2e80320000b541c880005c0d078954060819004104040401080c94a40f1a6505154a8401440220320340a00d622540000340360b80701450107440301c60720101c0c0c84248000005c040244003131201c01045244542c200141c0d03002080701c085241c00d450207035659a1400032091804c0280c041441d02d030341c42c100c4c1c0041070025000c40680145100240f07500c1200ca424011410f640c441d24010390f1203241000108100c410700d42c0495041072182c0408240302840030001585504030000000c08203400159082c03c40c90004418100244100b580f9814140003400b510f80508442c0503441149400001054004002c1c40999400f07030b52003411513544a010011a40d184d03003003074548140600c038a0b62005401400030502e28411800500303401d04582d41c640b60488259005043c6000394000c032114800400c1e124002040074000003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 71384273 1250 71383023 71383031
    0x1080c070b04050307141c080f010501080403090f0902091519050703110714030609010509060a0b06040e0103081c0203060102030a0c03180303020607020f0303060307050405040512070c140d020907031e0f 89
    0x4120785c5540d04590307c48908209164003000001040c40c60410305482c1c0a00c4e120500365600e04e8150345007a00e940000b0460001c000c0300141d10411600280b4805406944120116030400070441c003e000703100c0d0014940c00120181d0203024450f10150110301d0103860b00c1501544400c81840c1490030f590000003074090b40c000341c007c00f41410008160400064402080700340b42200d01c2f07035203a6402401c1041d1583e19003015031200c1d40c48500f6203003e081c40111080c0c59580d24070b008100c1d40e00070b4075608845003051541c909139081e0b80c03003900d1184030706801a602d06141580d00700c850180c120030071424860340305d0380348481050000580e03001c0c510030340052005003014100030f4513028811025080036030081080008684021440c00219070040d14046010f4840d4608a400c158251403441c0b84010007049890a00031040032510445900e0350401011345c030440280310142c000034070060340141490010503881071023607021444d04025041402c88120364070b140c0744144c8800b11003250b501750315 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 71385523 1250 71384273 71384293
    0x8070b090717061509090a080d27050601031506120605070e0d03020c100201060e070c0c0927020111030c011b0905030706032408150601080c070b0405030714 69
    0x1054800382d1098200c000516684c901001c800b0000071034992800d004415410201d003030300108001e40072200d54491982500c651a51001c01c0040c690003075a14200710388016181140c40301c1034001d0541c1500074010780281c0e820b50b11203048400e100d28100124681e40d00300010520b6019813165541840f800e0040381504006400500c010b40c040c40343e40c80f4a90001c503042c0001d1b00050b60034a01c600a0383c00541b4100c0c080c000342d0040c41c0c1a4007180d88030105000308851560300c02012146584100c00401c0e0362500e030031940d070403904002c10440346003506c10500b42184842c801d0701c41415105142401665402100040c02c41d004101100759a81d12926500000340000300c50140402d030504d00203900c6850140000d545101510814060646e5140100c0c1c440748140740188065903401901c0c2e00d040e580b8260596078429800c08103501d001d4000209140d5071007050324900a8400052460410003641c0343c4106421018004503003e01c4200040c2002034038030144d032030401202d00060070750410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 71386773 1250 71385523 71385539
    0xc060c0201180f030b0603030409060b0417070609050d0f1704090509030903060c070516060c06050601020115060509041409030903060a0e1e031204050c10030e03040b0708070b0907 79
    0xb902402000a1042c0c03000d080c007085841080c02400c0b40d8020030451256102c040229003076201d160415080281419000310b41c0f040400d00a1003100c42c4180f1600b0044440c505054443c422401528009401c0d0a800c1106240001a450f0307440c3c06000c00c2c1c081c1d002517980301c094042c0c5500d18044031081c08941004268000c0c4200c0354404480070146251125000009844550041c04c441071072202041800034082c1c00c0001e80b811040c0c0c10301030301110ba103907080034100039030710030741140d01c0c50812001484552043c05040485118100100b075068180740c81524160400342c6802d030000d6403118088c3d82004210b4030300d405000c0b50070107117a584442d41c0c00c0c1030600f031000b007290441e607041c110766034144080026000c0032440c80c440402d075000400300140c0c0c19845210755503d40401d4010920060243c0480d00140d081e84c1203d0005e01088040700540684009501c400d48a401c240404c10104903800c00410702c19110718009032034011244c2d00c085140314251404141e130791140106020441c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 71388023 1250 71386773 71386787
    0x230d0f0e010203030105060a030e07030503030f2421011e0f1b05030f22050d08090c090a050a02041815050109080d030b0f0414060307060519080c070c060c0201 70
    0x103000e1001c0d51442d0b0405002c100644201a4010308065a07100f40414006041c002c580c05164001e068940d00e040882e21828144010740700035250b0801d0212000564100c00000e44a42c10094004100c103401034a25512015039900c1d030407000e54949040c1070010701c0d6040a60705100030904002180302c04500010f0880341c3c52811929521450794092100301d820000307a07540310101c0c110b131441e13507903640310b50924084900b0f400c20602c1d94030403844002c00031302180810000c07000b95100ea1169542d0300301295601020350040740c0100d10b12002c1020b040242c0c0000ba84900300c000050f00e85540e40c111581c1d5000c1d80c05156070030503550f038410300385c1241d0341d03800300c005050901c0c24030000ca08186000e51201c07400d6640301c3c11703d503980440010545a00807100d041f0000244104140b079044403c5203944401210f60b0b500c03901807140c011401901507020380702e0071200d8000c04100300303002c007009907800903020f081c49180d210140141c40020302180365070000340c41990748040c81d52201e440003426075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 71389273 1250 71388023 71388047
    0xb010905160801090b030102120403080f0f070507110d05060106050a0f02010b0a120f02120a02031509030412080408010507050d050a062304020403050307050c090f0403020604230d0f 80
    0xa600380c5054403000d98002c1038603040d110055400240d54201d480001d0080c440c01c103426001100780000c10062503042460765204045446410000b5643e242082041170001c0300d490001c64024030144000c101c00900102109002601c14080141c0a889071032030068242d000c02c000800002c0c041984580c40f16a00c00310a1060000f4004416040001403503849607003d83d0f080303c1780c00d4071010140300341da503043d51100313401a0900341081078146409441c1c2c109042d09074040e01c540540100344084000d0001d00c52290352010f141810f013803800c04280c00c20413034016510000c0074080454010028030490380230344440d459071541e82c0c8520324058103607800100302c01d032810301d071000410000c034060030f44000146040b41680d00180a0740c0014000b4080c9810281491002040c413108218001684484a8001300c600e40c840703940c4d02c81c01d044402d8003141d004005070000800f0400240301442c03203140240d04901e08081e030041d8102c00c245071007908514040010001c000c0c11005a070010300403014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 71390523 1250 71389273 71389291
    0x2409020a1b0b1306140705090a0803090d0f030903051506010e0303121513112505030702041a09040615060306032409050a0501050609010e13020907020c0301090b010905 74
    0x710400546a0b54040d0354024014080c85281420003010040e150340414560364030407401403060304045c00020003d8002c0c010140c011109082c0200e04041c0c00001c0d540e40c550010413a0100c000700c2d541e61241140c20f140c086040c0000c0c0500480041c200340480004058030710000074661600718001415481e85901d51030003030704200581d030040b020744001c050f402405814009180817800020410341914042605141c0c1e03d000900e01c1041d07115001041499550401650340c640424a11312101c502c12a0050690b40200049001414203030485500710540072108003105070300001194041030103c600310b50b40c581d1031550340700d1030000f20840c00103080070b0318040103940d0449d514402500020011105003800500f0707402c409040b0707500310006003603001054a80c08071403858040c1c060300c8251040786c030a1134108004280a52180c6203144a100c1d068000d9020507070f1a020300003d00b1018100c10218066a404030140751424011a10140c0c07040c00c81e10540d40c5411035420840b0006011590 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 71391773 1250 71390523 71390567
    0x5010506030906132405010e0109050702070909020d0204021c0c11070303030e0703061d0105010801021309020a09050907021506041407050a0507060c0c030f02010516032409020a 78
    0x15110b4001440f01d6000c10030404a4a1080880c24410301d2030b496184001084403011102d100c000c03030300340c005a04980e188a00d80800740d80300e50b41c2e1020307134400302c4c0d403000142d001e0b40c8200305a940c0381e08101c1c004d0340058103a03420b00031a40c000c68141d80c031101030011000c2c0074190400381c41c503039446590701c482000d290801e001c5070851103a50300c40c4010b00c009400c1544410543e5401c02c014003445000350340c13000c1d0030030041000386c00c440c1d807050300541c40e100c2d69443c100001581d01c2042c000c407183d541000b02030344101c4e400e042c13005000750004060182003042e6400007003090340320706c40158025803040d0000c01e01c0300e241c4148004039140c001d203001c0c0a03034201074451208400c2030080b140c00c4045810810384524001c0c4c001c072024007494002409603402d00d0603681d00c50307410184c2c080046010342d032460801402900c041e82039900c15681859102e00d122404c452841c4264441c405c00400c00e51042d030301c10410070020303201c050540c004d421515400141d01c2050307600301c0e501003411921020b00705 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 71393023 1250 71391773 71391781
    0xf041508100317130b030a0603021009080a0816050a03050309160e01050603060d1a0402090a0e1b06090a0801020d1b1715030d0906020106140d0f0f081c0501050603 72
    0x2825008101e80c0c00e60003e400422003411a0034040150406011a1070540303490385030144100c80941810302c010390145440030042c00b4030341e21a20b40c0200342e90ba44002000103007000c1d40d4110712580041100000d482080c0c20350400030304180010352105029544050b201c0c02d01ca20f110381444440100044150002c910800c0414401092a41107860071503a191b1640e81d00300210f1003100c00d40034003d145194080c0701001c0c01101490080c00385000760f80140040c1e88080c0304000f103603400342c4c1c20101e503409a4120310b9507126a440000340c040c0040c060314106400000841d5102c1c4c084e42101143da50080f400f14103540041c82402d03850f20105403000503490710014040c0c003101d806000002d1488081000403908010320381d0900381090040c007180c1080f81440001030401c0f0440c0500d074015401c00c1c10025103030780c00280243e100503000306014440501640e0300c007140001070b002240c100c1d503203102100104440501410510300029424046180013003a00300032103c2c141c011600c40d9105100780 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 71394273 1250 71393023 71393033
    0x10e0d150f05090703051c0311030c03090d0503150405070203090312090301150302150a0e0a0603050a111918090507080a2a120b060d0b030105100303080403140f0415081003 76
    0x41d03900b107624100b115414032007030b4100c0c0a44a101c5030027035412000400d0206050804004611400c0440b040d00e6202c800040d003140c50b440150390b21545061506c1d20110249400d51119801c0005401200d00d4692402c003c01d041140b11000100c07401008100c041450600b80120740500d040b44001c85541410b5a0010351400030401403281d02080215905c0006400b0390303148403121300f0080c800c0782d8080ea5081c0040c003401c8202d480c42c0c801e5081c0400c104a0030b0a0a080ea0014414404c00010b1058100002c82c0d00f400031040300810314804101c00078103140a481514042c00d2155103e8850385459041842603c14446500b401500b04082484501404000b10b04a00300c80385043d02c070034890007080d04080c06540140d594411000600200f03c0c030010b51203c403900c00242d00030301080e6204003005101da0290706c40500860428800580002d1042c40203440c115100c3c00454203110440f6110b54054010b500b00704000654000c06c00e181c01e4004155590000300005507002241c00c41d070796 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 71395523 1250 71394273 71394283
    0x306060f031008030708220305070603020c340602030f0a030b01030902150d0e070302090601050306030313120b0c0307022104030b1005100203070f02010e0d150f0509070305 76
    0x2968030354040200c0410540c2090b07501c520000c040c000c08881d00e0315614280b4000590080002d16101701030f00d61080d040c03000360401c1001320b82e007240190002902d485400d81c042c2d4050b500b0890580554070321462400100242d105060074081c500c6e011100300040707050500e01c520f4001405640c014460541901101c0040344c0d0050303450300d00811070f8403031040180c000c1d201d1044000e40c06900c84600841c00a1498060441340b21484002d0150b20303480304025495020307070300000e508040c0000006449500400003160491406070440749009070f4494085144505c0c2e401842e100c42182811800744035203a100c0301e0b000340742d40070124914201040040d42d521200c42e00e82ca0020712241150400d083c0b620159402140c12062013516032500c0b080740141c4039800d0144078400c180044000c601588000140d4103038950003000000181c04680056505207016003d0a5100e20202c00103800554542c4104000d100d50f2603000c114204501600010b40c0d4004000c01455400b40e0401c101207400011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 71396773 1250 71395523 71395537
    0x60f07110109090c031a0d0f080a05040308120613050609130314040b0c0d020d08010605070524040201021b06120c09030609030a03060b030c0306041d16090b06030606 73
    0x410030380a00410801070319603201540c070010a1501d45549012450b8040d0407030b03040d0b0110b0a00640103c41c4810400c80170503c8083c0c00741c8015452076040300001c12038802040c441380036051035401e01c4d983e03550740400c9911070321100e8800c400902c140b0445007400024281524881a07061140346401c1b40400c20140c070003005a4100030550306000c0c02d2600a4807413108080003801541d680302d417184801c4c00150f00c0405151b000b4030038526180c2e081c2c0d1011412040c03110469841d250780da407030b006046034a60040c41080d103980c0500300c05200500b090f20801920b2440c64a1007103000e25241c000079041c21040080340010700c0308044d110300e2a03601c2c0011a075003501104000c1800b0b489411508820340682d844180d0184902814000140d070004058840100c4981d01400415207407210001d650006580108007004140041030a5281680005007500c0e091881040000b484003001031030700144040f0400d60418100092010740740314040c0c40b0501b00113803410341c690704101c008181d0f1880744d04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 71398023 1250 71396773 71396783
    0x41404060b1203041e05030604030e1909020a0804020103050f07082e14120c0f01030b0607060f0501140409050c01030b011e1e0f142101090515060f07 66
    0x10042503401d0b0340d62000c0c0c200e40e020410480342c1351a01c4541c0c01c403d40ea020001d80300e0010041000003250703d00060b901c2e108a9142d41d41c49403841c0a502070040f4041c103451445100c00e90408042205211840505440103d5903a043d14038145800003500311040680740c955079180c03550820080c517800403012038100701c01174820120680507403045950b00c4100300e403d0206204913a80003c181a22080003100c1d00401c882c5000524034a0000503a142c401001c9541c008590f000341652560080d4002201030340054040340c03404a048d62000101c40c001c041d0040400c0e42c0e0001441900800c0b4401c1e440c1050541c3c0c2042040341d25141d2950711304041118504154885030580c58a034424000a18040d1040b5035031152600403a801403d141710701b6050a001480e82e2100300401441903511550b40c17442511452001850401030321f01c158050441036448054594074840b4541c16114041e0003420700307401c0010380d070600e00e0292000e4511b002c1c905201e10400c0c0a4a8521031b42541143e15081c0c0c40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 71399273 1250 71398023 71398031
    0x1051005040b070b07030c0504030506070e040e0f0604060b030307170c0304030b0c071b030b0f04060e0f0f0c0117011829010e0901060c08160c0303020d090504140406 73
    0x120211000c0c401c0760415141d9800200d004000c20848030030f400c0c01a46151010300c02000141e200315443d000b10310000e040c9600803c085242d00780144545083e04602610202d801005084080c0c64201c03803410b2205a58402c40c100b00c14092644a056107217034085019500d400c41c2500ca50303240200500d0750a40700c10b000641d120700350350100201d8008651048080c6001e03d008182d1142c642c11101044d80d86004105001d80e480ca1b0240c1404144c07544803144880d1619415200b40180d10014400c8030314591303480341c10b030105030100b10007040d250204000f04280324080364800d0074000e40400103418021011040c002e80300d03a4001480c15517201c041508902d024080d5054054800b0340031529200701c1aa61900000009180c100b107068001c4c0c82c0c2c403c8a00340e04041c041401824840c8500186070b4205041c0042c182e48001c0c1b1041a003a98031003c05e5005031503140000d002c5a2046006d07a0014404440250304001214003c100442e0304006144100c03c00c81c44110005000921203656 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 71400523 1250 71399273 71399299
    0xa02040b040905060a0f060206010905010803040605030f060a080111041e080a08070303090b130203011505031009050a020a08010e061008070302121504050d02010e19060c0c05010905030a12090b0105 87
    0x50a0b1260f00280111b100d6402c0e032541c0d455010752512000e0041980050a010020a00d4980003003103904845036565a585540c1c1c5280d09480b1846000c4c04280d40103080303080c0019112000d00030629a800c102d8407c0c0c0d521032904180c9069203008210a007101c417007814041017804408585281c0441c0c100812650b00d9541d46400c5009000000000342040308900c24044003440480c0c000113014401d030001c011100404003002103030041481410fa155000d509103800d104a50b40101c14114400c0c02200d00f81c82103640003452401c0d29402c1503000da95a4005046000d5007048a160030400c2304591350384072805c05945646901c002c2c00040c1c0a81280141c02861440400c42c801a0500e402d040e50001d007031925125848036002d0313142c20015807c00d154020300040c00f0582540103502e406642122030351036076550b0041c005029011007804003966220300801e60031b000703600e0b1041c4604080d543d1943d42c140050109102501c040300814030388001c041c0003811042c461070541e80200e40040c84450 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 71401773 1250 71400523 71400529
    0x816050c030f0c0a0309050607050a0206090301091a04050610122d030207032d061a060307020307031806080403081803040303020c03100516050304030e0907170a02040b04090506 78
    0xc42c403030303001d4004140040c2c1c141c0c0401c004110020f02520a50703030b0320075160755001001410300810f58080c0140e04004034080040c6020801000c0c13a800c0a00080340e001d01e16140c2520044000601000d0807411408010803c0410700100744d008200d54084d01040e41481124400c01481001c028010030030f4140140c06003590350070100061403d1050100e10b14024135000391030fa0124030040301d007800001c4219840818400c01d4183c1c15020300044c0242e801c00f900c0e01c1d0058144119002c209854042c1c0f07854044d12070038000c5100c0c8143d50019542c50440c3d240041891042d0445003500c18880340050000035401070109801540600c1d0a0714a86c9a1200c499802126107200d20114800000c000041580110310507050090480c03e0b2400810140381d2501540c0c0304503046d020101e802c20301c0c0507207207006d040a907400c10b001e07240c003035200e008a001081030010259100000309500040d8804505170075240d0307990014012009605040c507000f060440c0b409030b40612a9607540710f0000841d562 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 71402879 1106 71401773 71401777
    0x7060906120221010608010305060c0412060209040618090c0b070c12030212030a06140301140601110f1501080709060b04060c02011101060803040501030b010816050c03 74
    0x11040044000950200394058903071141801d80594204000403d64040c041c1c1d6100c200d03242d415414290b00d000380c000c0002810800c20042449a60168203000d0707415a840301c0050b0304e40c403182c00098050b00240c0c0017041c115500a100100707030a020340090940c24003480001180303039181d8444400510460720054140c0814a008001180084129419860082c41a40d032081e0b07082a0720590703988155001d0505680728403092202c032254400002c241030f400c4000300405400d01c4000c103026000200014140012b884824614142c24010f001c10144410150f404c00c62990440c051484028003c003101e5100d0303004007080d111074a200c0c800640d0721107261242043e250041c101d82542e03900808a0403c00c82090080691009000b850044e04641000d10740f107504010006049484050845040045100510007072510761617501c04080007601c0c102ea6500c41c100c1a1620794 = true := by decide +kernel

theorem cover : BRFrame.Cov 71223023 71402879 := by
  have h0 := BRFrame.cov_init 71223023
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71223023 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 71223023 ≤ n) (h2 : n < 71402879) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
