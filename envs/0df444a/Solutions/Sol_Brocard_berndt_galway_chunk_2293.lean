-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2293
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:16:38.677612+00:00
-- url     : https://prove2.me/submissions/b92274b5-6a3b-472f-82a1-367e1a52f34e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 412230215 ≤ n < 412410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 412231465 1250 412230215 412230239
    0x618010f08120408070e071205072d020d05090f060304060b0306090c03030412030e030f01020a0e0f06040e0907030f0302210c0d0f0905061206090609040803041118070801 75
    0x810807a4240d03a20f018140a24079a40701d0320740c851419a020f5100015051038401e2101c40800f040000090006091400c3d0040c003505214404424030001f1000f00d0a080c071000340c1c880c80d01d15242d0003130071401c80250380546480c2c21001c85181c002480c2415620f41d0303070301c005c02548100d210b49400103031200d810301170518040c0005c201942d9a44030500c40303e01a5000001e07101207a01c00c00c90241091258071342103862a0384124001e400d80703c0e2078210244410b044d009070000060039134804614009034001c02500010400c100d0750001000c010a105e0f04602c4048240d00034a40d41c1282c010130707078a9071744104003607010406800680002c05640d6048000c103040780104107e5201345428003260314459920b800d403201102060001262400104034000c49001c0000c0200900c0c0350f464036441d000b0240e003c0320407540c2511803268840001c0891805000c0c4030b010329045401c2a0455682d80d40704c00b0403aa0441c5130951100c50007a00200c8601d038001102c1c400c44e200d03a034040f0b555140030210000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 412232715 1250 412231465 412231483
    0x4051b03031e03040303020d0e06010e0a0b0a122d020306010501050403050d2f060f0601050712080a02070b13060608010b3304150206011a030c030618010f08 69
    0x20a07042009211030140095803202c0086580700c01241e641c0e101c0c0c2c6001e600074440c1d1207a4240e11408c11040884410000c94071074102d031980d0103401680e40c0c0b0011181d0440301f2a0314040e44c014900c0c0014010800b50501402c41c603885280c40c45100b0340524100e4030304003a50400031482030b072182240800c6042c1481084c0c010b06003800c0041c1454115903400d6150b14510200e03808000c1b8000800c03140045803000c0b641d026400c40c9040c00c5a01d207107081d042d100d00e0226001e080c1862004003040301c1c0d512840440300c1e0950000d88001c40500c100d0000ca41900700a800074003078507000d00a140c04500d0400d0410300403012041440380405180c6003080540d00c0950044100f03914000408070207403603641320760062480920702c5080003c59101c80915811017500d286040c1300340801e001c1205030200305103003489501a000c07554640e99603141c2c500c01c000300d458004036101051010031152402500030b1134220800505480c4d40304003045094400400c26805244c3c030b5040300ca01001303460030a000c0949 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 412233965 1250 412232715 412232719
    0xa290a171f09020d1103160b0a020c0d0327080105131a0420040608030c010c0908240a1806060f0e06090f040203030c03031003110301020703021002090303090904051b 73
    0xb600341c0d0005801c2203150700c4e011702064903001c4155480d0f6014000144000c03a1400c0000e581d070744560110201d034008003c00000b5100c3d004000b001031400c800c400c0079003a40359445d541c4103a03680707456200069205494481e101c3c00c80501040d001400c2c06040d01c200c28214442c0c4409105080c80d83c100411026030745108985542407102195440501038a85c2c1c40c0420001a254400b00c0402c000705071030307400080540000b01c0c443d20340d00f03c103401055100d8900d03598502055100e0200c1522441c0c0011510706010482401e8092000c5107440340e9404414264000b9204140308203080e41a00c40b0001182d020396115010f009405007100c8680103081100142070080c50144003150382d42d0340c05813182c04140c60480002d41151b50070412034062038805d005a035100d081c030300881840f000c070600086801d6884000c070394025050520980d100f0f6034265000340007c0e1255409400258042603115805d0f0100b0800780105032a20350446010b00c2c0700d0802441c100c0c190b003c101000b40070480400d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 412235215 1250 412233965 412233971
    0x60203130e06100f090b1206030607090e0402210303040c0e090f07050f0409082b0e0c1905030a050601140105090310021315020303040204050a290a171f 67
    0x80115126600c1400802c040703800c042d8031000b142c3c0130948842d03110b80c0c82156a00e100103a800c500208002003640100002d0301180e02c140c4030441c0c10780f10b0322014091909040d001c00d00007005440c2c0746401002c80039281c0d0f81400281c100c024264103513402110240e40c860a0700c10b042004100c5e00070030035441980d100c058500c00da8024145500e070b000c1449030a1241e4200100e01314540c1c2c899001440c90740d4800e002c039507079000b510001d080c0701140504514000d0010f2a40b01e81e404080e0007114541c419010103070180030069000c020b003504e00c00c007130140030b0819030074017041d140c40400c40d101c042070040c4010852980b410443c1c0c0c21500100140c03a040000a000610704c13901c00140c0f141456001000c050780701c0c01140750700c1c2c0a16507607a10980303100c2c3e00c660900409a8004c0021400b45000b03a8092000f5501c000d05c4000752810741070000060100c510b480d0305100c2c4034003402161070000801c0b90704c0d010f955515001c980540d88d00220500c1d0095072040c80e0101174400080561441d0304018 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 412236465 1250 412235215 412235221
    0x90201020622060f0e03040815060306060f1e120a060b1930030c050d090e01092c060919080a0c0510050403030c14040308031f08010501060203130e 65
    0x1503241100603280042055840c2c08005111070780603085039001e40700d031801b1652100e94804045a480403030b008004003203006400810002d040c0811210300c83c882c0580f140c2522502c95091101c80783e112a608401b070031411201d00800d5403100c0000c40340c108528002e1090124508041c01110130710315440f031080100b14070806c000c65403401140111440102c907440900944503440300d0801440082c901d0080c2120f0030310041640180d140341445004070700300c1d20b8174540e80d030341a62001c03414007501c0000c0030f20f00c004000101e100e403c080ba007501c2c0d11000000f80c00407007502a03c01a80b451802d0180d41000c4108080700100300921104180382c820009815505a21a503055205480b003600c10403249015034402d0040070001c6c4d1400300312444c2d04100c42d10301824014010034032019507400091540c61803101c9500140c058809503500801c000c5d28680310742580304a0b021b0403802c48071000144d0200041c2a010a104440c02001982c005c0c1d5076406d60500e43c4400003680d0740140350481c1c0701c1028 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 412237715 1250 412236465 412236511
    0xd0f02030609041b0807030b040b06040506031c090504020c010c0f080c090409021804060e0f012307170a0c0f090e0711033f06130504060209040903030902010206 71
    0x203083d00143c2042d4009003c0da0100e641c51400c00d03043e0403205e05031107413100c008200600039500d0780c8124006d003916409a1100c404000a4610650700c0c568564408500094100c489200d0152095020b00308503d1295450001c07034103030f03007010150800b580d550f004082c1005410404075121502e840c0780074030f01c40c60044540515400384021090203299241070010464a4a20030401101e1000100c103c162500b8601030380070b02070314007540c005400303804522281e02307005008440301c10030140d002e4220091045908050198020140001c01c2090350621000440305103c2030b00590080304045101601da07000640b940c1400241e40c4100728511100300000c01c3e02c0440103030090401c1c5089506a003a08040914500070b5030700030b05080d0301d90b5000d030007111b5030040c00360b80e120b61006a8080c0300560905840302c1c05c100301e0310107400085210302c82e800ca00e01544042c1c1d115100d080014100b180007408a41201c1f000700c02107000c01d42e2014600195a01049400d9020302e6203000c00f0300c441c038002e034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 412238965 1250 412237715 412237729
    0x2120304060f021b011a0a050312030a0612050a330e010b09090c130c05160f0c15110718020f0910081902030108070510021603080d0f020306 62
    0x4040c01c03503a40d50340c01c2901d6400c9501141c1d080c0120196130021034010b81e500500030701c04103c141810008507a4030412a040011190301110001409400c10891603001e801c1241d000030500d11445039140c00104800040c1d9145186540c003450003011010035138a000e00b07090900c1403120003e1610295442c0221032004201058140007900204080c8100c41015014140c1d0030022503010900808000101d031001400041584048404070488100c0c8604001150a074480c10400038100708040c0b003111703030610415540c40e071203107010b030b6100811502e42c0c2c00103002640140c81070300c224490b200c00d000e60020101c009112501702400c2560720740209203400c08884003034826059004146006020502d400385c0e580c5810113007807040d0707000d40c52800070f0084c103048450059600c0c050030342d02030304400782c402d8034140d445050040410714103000030481c1e0713244035a070083c0840c46002a184618000001d07110300951003511660344031004608008151000001403041d6140705104100310756648030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 412240215 1250 412238965 412238971
    0x6130312180504090303290f04150e04080c0a030210060512070302150c06010e220b040b06060d0c020a05190b1f050a080c040b12030d110405041508010c021203 70
    0x29070000c1c000c1c13003c0c0307000e8025000c9a4800030014141140074072100c00c8615640d044503504584402074515a0b2081204484420202d01c1041c1d800107024003802d0000c0c10050b800500034401a41000142e0b140c0c140341481d083c86c06c50058102c04107085a40d0110b000d00b41c06804105c4004501071140048030b40d50345070714030010307226200320700304104055408030464040701c480e00107480c7c0940e101c0c145848608029650248040e9036042c11046074440403448100040d40401c0e001140d455a071184019854003034030135507120001f0001c00d40e103842c4c81e00c01e2024425940c0c010301003410040c10110b080414101ea04440c1d800e200d401d0000182120f1034140d407025042280d102c06d51651010041491825008150132560020000ca01294005030400902c40c00301c1341844061000c100380290b0010481008009a00900800700885410b8000d0b0036800780a581540c10250742d0000202550041441c0c41c01d40c602c08682880403000a02814507400424001003914180007103019007588802 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 412241465 1250 412240215 412240219
    0x21b090a0c1b080c07060804020603070806010e1c1b1a0706111c050c09010e1e030d0f11070b0301060f03060b07080c0d08091e0a02061303121805 64
    0x10300780146140d016400d184803a1202465026150036145041103055109025028a502c200c000024405111f501e070b461003541e0181c8914255100d050042d18020406080a8144800624070794540d44a03c0034410940b00c5011074640d0034161401c0c44014200d800c1c50040032014519400d03c03503680c0301d8010b040b9168031890080e80e66005030400200500000c100c44040c010300140300030204c000302c40060780c0d02d080040200525206c50710316030080c1c800c404400d40424101c00708a40b140c030307140180c80141d003c81d01240b82c90400050009040010399881440490050030481c903980c0e900900340300690f181d410040540600b0306504030200c0c0414840e0f1403c0040c4034101d486031900c03c4e0041001800b44000740c2c1e480315650710b0100003503046844188540c3c892502440c03d25442281102c2c0038200402c0544564415522041c1c4a4083c545d2510898429030b403181e401a15060001d24400d17100c031071140fa03202c0c00c1d0300c1c2069000c51801040d5040103660710f0100d100d014040b100500300c80302 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 412242715 1250 412241465 412241471
    0x140103110d110d0c0302060307020303090706020c030709021b0604031e180e0405030408390a03060e0703151506020708150709180903090b250c050306130201021b090a 73
    0x8600c1c099a0000145d08001d400030030120605c051150000040c40c0034015103029541c203580c07206070490baa004541c42e06a8554404001004440344070b9000f8803010401001e00c40b160104c101d40f6a2401c10281c4003200011211421420026290120891442c00500d40b20b001900c0305941d0411103074003400780582d01d4405001103030800404000f220018800701e002c1c0c80d20020540400300742c6c251034007440001c0d4035448007a240c04c102c85008140031301000400c0c2d80b0307146083d900c4000003041120981c0c54544101000440031496140003021032004100001c568848406005400810964800c40541d400500c090003890408a540307000800b0159a0301c0d100d03a201042110400c1c0306501c821207050113880c2903141a1510b4004c14000c9019440d400304803540d8032040485c0d03206940d2100c03c044110011030130044e8480200102450141c2004070446031200c0000e410074109503000115178034200704101c02c6503014860780d40300d2130340342c4200307000270034a200496240140240000d02c0d55907 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 412243965 1250 412242715 412242739
    0x18090105012111090a090b010828050402010212181f051c18110306070203190507050102070206040b030108390409120306060e19050d15140103110d11 66
    0x40301001e86044d058003c010403d096520011040208030b03280c0d0701030000e00d10b000000c0011500c001c004005012a240e505c001e143c40644250080c107019000700c0c11401040c0701d0900c0721045201034102d41c01201910351186840038200400f5500c1702112401c2018171000c01612541c100d81a15010b00f910003803030720b0881c1104e0940c3c00500050109030000c034103002000e003d02039000741610f200c032025400c271140e40d00c80d200241d940b4014039041000e038402c0a403230b0014251140c005403144a203d0390025050100701d40c00141190003c0e04120104000800100035902007085910884850001250000b901042007101d1007550b6003644101c03da11640340c0e42154403aa401044040e400144c0301c0a080302200f001070180100740308540028000303080740b819130300d8101c26001800b500f40d04402142498201400801d0722280c40541e505d1010325817440e01c003c811f004858480c42c249003c0c4e07400e0360651030050f8902950710011402005241e410400148030130306100c0750780d0012501805022 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 412245215 1250 412243965 412243991
    0x102130911070f06090b040c0302030d020610061b0c080609100e031213020d150b031b04110c010606020a03090b160b0c0c0f0109031103070c061211180901050121 71
    0x2217122800201801404000c20007408690300515003940e01c2201a114201c1300c96804903601e003030079514030715074890720708013080081d00814440481a9049118081c42c1c2c00940740d001c0744180d0b541c40158a501708a04001d00c90b03105100184408141d820304001c0b54183c203007002d50b079000f103a000c460400740b500003041c8191058a0454682e5600070030300044940c0070324054140f020401e144110141c101885c1200c28500803450102c0048950300c40d289804103042044060402d10b401080d10400801c00c22003141028000c0307001a00c0190000d2101c071b44249002400c00e0b0b8160301c6294403050501c09290f40c0c00d00000310102d1582c201901c071040352283c41d0744808921512490714407034880e2851070b401c840810340083e0b405901945400d241c3e23000e000c00250b04d0f8840e0030001440f4140c02401848803c2c02241044030300c2c2000c5500040c20350801071007c00380da0000d00015812020810250240d10746031070380c28007410081c80c22006914030318801c1c0d0407a142d800c400034039403074540c18060044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 412246465 1250 412245215 412245221
    0xd05070c0e04050106052103121e100f380c030a0908160501020a030c0507032907031b0305060d0c0f06080f220312020301080102130911070f06 63
    0x14000d03075400c45115041601c2d0a0f4001d0030b86204140c09414668841803d020b8440c0910102c5040e070400355140000c0220fa030600c0e81c2d0002c1140348541e814160700340341c0c0085010b441c0d10903843c2c0002c03683c2c2c0d00c2c1800c1a0942c207107060b50144615282103103540400440788503000c25641c20b140c40d6643e01c00303110f0400d004a4001c1c0c2d072021049220114102c100c4036403000d44071003181e9009040d80d61a04004910001428141c011a03000d039110b50f154100280c03081424007034850094050300c04198590745ea100402c0103c00568010f684265044094506105105078012130181401c004224420b0b003032008600ca01f00c03044040c5a9950000340d040d0b01c5505107414121750216074000c000d82ca58a005042c0752260148400150301140003418a41d4480107035401441101484ca03101c0102203040c0c6101c1291840403010402040c1e20841c441040d030001e035018000300000543c85248940d10050041d82a61001c0700380c40c01e00001c0250b2442e1441110310b0103070000f401002007001c0c0d08210000d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 412247715 1250 412246465 412246469
    0xf08090d06020f0a030b10080f0915071d033004050405040c031e0309090507020312090607020c0121050601020a1a0a05130b01090c020f03120709050102030c0d05070c 73
    0x50700740002800b41840480320001c0c02c14002a0700c00f000300203100d40510801e240306910603804030748071801003085035503c0580c050380448503074104d8161950f43d81002684c05c60540c3c06401248280c04c0083d00c810041e00e800c1045030042d402052040c0b4071102e8a841d0841c2d0041107a80c001e90300000c00c1d144003034a01203c000d4280074000380040c1c1030a1510581c0b1100a00c0140c85040080c1e140080ca01c05417000348218076059600d0421450805036050010a400703450703403065200820007041105034441040f031040d03404030003030303e82464401e1010f81410148065507041190b85010030310901c900801300d500e540411000014a595004010b038906541c0450181c00c40502407a0b1410032201d10780114840c1450440034081a16101015142d01c60306160007000145004018055646036500c1054000c485104a44000b01e0300007681d820355010240d00c6200d2402d100c10451007d8100600030004c8c402071000f140b602500744402d0740c84001d4148104104000010a502800407854000c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 412248965 1250 412247715 412247723
    0x7020a030816060504080a020d02030f09041508010504030c0c092a021203280204060f0309061116020f090c03070f17090d09050103021903052a03220f08090d 69
    0x20050a05046c1032101d90401d001040043c0328250503540c1007440031050b035001e03c0c0800c906508080138201040b020b80441c20075506908040341000804007003d000d03ea004034081c0d100d103940c800c06824086004c2807542c00106d542418580c103850f1182c4207060845c1081d68081d10401e07805156a030880c18501031085000c00840080140003001015542d100100d94114444c0d0f901d00440784105070580c05a40702d441c01140c8086112a02c4034001d40180740150b00c20000001c0f181d504140407091904012500c441c8455510380907411410021065240003000b1500055a0300d44003884075058403004000d0005c01031048940e0002500551030144212203c40d0f00c94079034a40180455134441c40034402c40300040814000041d0740d40a84200c6240c42e031032010400c410502500190060403016040391222942605090000da002250312040320340020012a5a4206990b101c5050300c0c401ca41080e24025038031520700010030306450303c0c240b9a4000c8025840da85050002003011907800c2d4090 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 412250215 1250 412248965 412248971
    0x40807050703080d050702061902180316140a0e010b070501060312050a033b0a050106030b040506100b0a0c020402090904031817060105010302070807050709020d0501080307020a03081606 82
    0x4010003c401e800f5107488201c0240402c05940c2c2d424040b40d42d2201511840c9066520080b8200c116400c0e400030a42481340d400d4418014aa4001091601d12154842c151044a212092010804150301045812403c4800e0000c690408000d40c01c014010321400c0f10f10f20002179000c003004400e4101e8401180c0200d41d040030400c50300303801781580e880140c0d1440042d15150300c50700b9275042030100300014040900040003000c61010100341880c016004254203100e01040b200c00907400b4051240914031804008415083c5440c2041c58180c0142001410000c2d00000b070104d100b0b080c050324941d1a0a10388003c40c5070060010a000344650f841c02c641000540d410041407503007280c08800503182151070607121a9a540850440301c582c0721100c0300c150411340040050713612a0300074124907030155a040345441d002d540c2d030501d04451036110100c020b802064244844030030b48640b034010000340c005149001259800161500454007000f04103020120301103a000600c1d11411042d01e42c060070030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 412251465 1250 412250215 412250219
    0x903031303210209090f042001020f0f01020c1501180209010302071a0f1f140102071503060f170c01030f0f0204080f1605010822082b0c0c0201080408070507 69
    0x102a610000c403040c000e43d070071782c085446650003105540c81a9000044503992031003500003107440c0494890241d04501c5085401c95540500380003c244143c1040001660359441203440b5080c1042c0d10f8050342c60403c607100400c0200790480e50360000c40341c075083c01a074413610301e030040e802402a60800b070b010b55000c02c0f0001080d501c0c218a54050095160f08403015a598110f000312030400701c036251880b14a0b40010840ca1442042d14a103240e014019260295110b8040ca402c44102840c214000303030301c0c4c110800c0300d00300700042e0a0103001c0c20910030105031041000295200c038080c00032410582c1e07502a032124150301e54041000788840030700940d40c07036566102c070f941c1c0c1310b08403044000303140070309040d604501200e4030403030381101c006840d007440e0b0341c0d9005890940b0950101d020451411503034810000030f00382d100101a80c900046c41401a00d2034003c0c0990300211203d21110f18500d4441421142c0b6008021503502d56030910740160a80c1d2545841c140c45e00a410004145200d80280 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 412252715 1250 412251465 412251527
    0x4061206090c022506141303020303030903030f0c0a2c040f0603060b3a02030102070c0617010e06040e0304030510060e090a0b070509040b0a0602240903031303 70
    0x6109207100f14041ca029440030b040c2d6412080b2013042c844c07080401c0305d44021420216100c8042d010455108459010040d034a0b000b00303065034021618681c481d0400410002118074201c0802d40000c510311190f41001d101e070740041d0a0003140c40400414071521502a1000380000ca404140c080010f0400c0c0007100104a01001410302c502080b116941840d00044450408001003621051000000c41100084000c120240c3e803101415540c10b15501c4289005600c0074001060210701c01d8503141d125a182c01d400400341c82e9203042601059501c0001000074241d480304080c0c21a204580c0020f00801ca8150a495445207a000500320300800118014180803a80700744101c0d4141803590401c0d0766600c1c81681c849003040002844501d281000c0341050384914054030b094a00600000f5140240e000003134411000e83c0d02000044c0c0c08003210110034a80e2890b02c201551503080108580e0074000001612404014491000c40040c80d00540a01d44200341190801400f120151034118081c01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 412253965 1250 412252715 412252723
    0x904111c14010b061801110a0602041d090a21020304030f05010507020c15030a021e0d06050103240b09180702160609080a021203040801021c050604060b04061206090c02 74
    0x4a103902a500c1e1400c03403451820704004848000362002d20765440e8411240040d07486201c1c2c5191600f651041c2c00948000552520040bc007030301c243d61707020151030f10101608512403c0189941e2194102620180028520305914281000000140e06041d10581022440c500441d8009495140e0f80700040090180c10b5110500505913079003992001145007050001c4086200102d41107804204001088a003981c0d0282c0310422000980024440305820b003c0c50075040a2010088991707221410005982c0610545a21403a803801c1c0010000c101c0074104040c480302d1080340d1074880002030120356a519207251699041501050400500700510002c0d0b540c000c0360101102004880c03070102d0080d0086c5c002904507100b810060204180755400e008101110407103215140c88140700108044c1003c1c009002e42d00715050407881c1c03000d805c80c080e80c00d82d03d002d00428040c40c0703040810b02901b00020300b00c4066903e40e00700038500040007010780008111590051603602d00d800200103043e83d002c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 412255215 1250 412253965 412253993
    0x122109060e030405010906030e2d0c011404090e010b060c0d08010e161d06191e0c1b0509100608070807120905190c03050f0703020904111c 61
    0x10020140d0403000c075652440f841c02114080707641c0f03440411459200b900705030b841d40ca000054072000d0002c81703181403a82c064a03540d5191540346069200c40c00404100c003800c812424a03104400400c01040e401140c40342d40651500551141101c412014094200c19203618020704259903170300101c41c002e51100980c0e004180040d240710000200141e20700d00c0b850040d224460003c6c3c40700c0c681807081d1104c440305106000075084c42190380b816640e80c98050400d03948000032000c0842c0001c04000c2051a1809155022000448040c40003583c84803007030250310b0744080f110817080240c541c407120b400d8242c0c1c41164813510010030848003202c100a1001207030752507154440c0b9a03c6280e0140c400c03e000320703860b50010310310011000c0c0c10400e64020440b0740740603000740c07043d480d5182c05460300014419010390b520107040000300700f0400100100c0303a00309102405001e50070308642c000341640c603000d80081c1c41e44490414041c400d03507403040e0120300321050305000c1d1910001c9181454010540d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 412256465 1250 412255215 412255223
    0x101e02160209040b250503010501032a030c0306060c0b15011e0309030305060d050c060f0c19123e03160605180a0b04062009040c1704122109 62
    0x442154a5081d00300c245501c221a06038586d05c0c00e5038207003001180108502404026a44115141402104d403403258036080ea055694000c5030041ca2001c0c0a401d0b244203510000c10041808002d001144010b0501e40c0c00c0342100c180c010300c002d40e6500480d0542811204849011100d5002e0304041c0d415510004845100341c070140020f030340c0d210030041e03903c2c180c2c50050081e8004001c0005d083c40d201c00140300344e2846403a40350030300c80b85600c0a072808100901404100c00302031848020b00055004105030300810745010800c0d54608007101e034a0181700400c034801044e0300c103005180c114100701420000200070f8104c986810400030b080c164480b01d0b40c401d884051030003000c41c0041000f90304241e00040300500a0800c3c00c0c041c1c3d10040d07191002401541c1031030b51450502c1c0340c03030b004198401d0042c803030300661a15401c86400308000c544035605103206010844903468203c0d00e07002105d50f032207504000c600d002030f802b02c481950301541c2c0e2500c1e041c20f8040240345400160640c2e00c07444c0301c0c90103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 412257715 1250 412256465 412256491
    0x3150a0f03170c0604110102031c0510090c09120c0510020a020a0506031b0708040f180c02070501210b04020d020c010e0f03090910030c06030c02101e02160209040b 72
    0x400741c2d03000518851120108404d4104c00005000f003814103d41070a4000180b040740d2505000b003054400c03100900c5805562191a10103000103006e01d5800030000d014000c1003000030700701c040e8002d0243e120a115161100d640b141a410a100c411044230f001441e02030500400110310030030080d12401441000c0340720306201c20002c0b50354107021003030300d10480e05004840800c0c0384210382c40045400040007194000c00420020403010017004120004018407290300030042200f15029098070600040401154000381c01001a0703079110000c1201e5201020003810207903a00e116804c00707060128002c0d074009000040d8468440380d00d500a1200d0b8549000030412409541124ad484070310001c8a0100d80d4000e00031048545042015280c00110b4170040f01ca1f41a40c0e0303030301d078448041d441e445000413030f580d03104549505da018404002007000403041000045815844940b01d112482c4544107250341c00700c1c81e4400c0e04075481c8030035030300c6800400c0e65110b86003038030744980300342400c403640e088000c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 412258965 1250 412257715 412257743
    0xc050a1a180304060c0c0803040906060f08040b0f0901090b09030912060108031209100c02010b0405150a03031215141002120301090b1f03050609090d09030803150a0f03 74
    0xd000300c00e0340c490300340401851500740303013002c1141c11101c1600c0684208507500000a041c01c001c200034801000401c002041003450300e1340150500d80c04510060600c418541040005450200001d5002402c00682d03c0307161604032106004003207604006106188032014824080b50001c0541000401142d160441c445490551500d940c028400c40541d40e0081c40200300c50403101103150307880b03c00c1c40212039042c0c1580d0140026102092a0365000d40d65039005d80c145030401c1e018860b40880c0b500104004100520081103800e101448040c04001090030711090f441e2080d0040c4040d6191920501186510303040509900c100400c3c03106d09c28031032890705000742c900100d01001102503881a003800d583c0b0300780100d0050080b003640f2940c84058154005c0c5012030b0a04180d43d6510b80d80d8000409291071002d2100c1801c001d0076080c06030f80701e000701e2a07421390b02c00d1072001039076806519951281c8405940c420301074020040c041d8000c101c0800411552200e04a1380110b03802070740c1c440c0c1d0080d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 412260215 1250 412258965 412258981
    0x30706051902120f030103110405040305030604050403020f0a110307060306050a0312020a060507050318010b0f1e090103240507141804150801050a0c0f0f0c050a1a 72
    0x100161140901080c8107208a005401c4281109050039103140169000e52a442c2c20600f4150b00001e4010940c150110041c0148040a440b1200c811001c0d03c0070071042c02e06490140c0035000c024006440340e5222400102010f10034842d02e2205404182114407820306032410301d92840c56050540c4c000c0c8208a00040d40502c01e000c0c2001725100986940c00242c256111255002d2805800c2d00651250550328000100c00c0d110341c6116540381e80d03e80f03449060a00e00b544c00c10742e620611014a0b0f041002d200702d40c3d41c40419030100f6107022a441c400c03408418070006401c0c404031682c164010340b014000824801020703550701c11002c8070702581c0417044040550380203c40059030000006074448908a66951808004040480d0b6250507104c3c10801071000505071451740800500080d40720504002e8104240226504040658014000b100002c18001c1903040c107024a14104007001081c148070f03901692020007101d801c01c0603548040b5282c1410142080c58003254101c0c4c00004000030304c12 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 412261465 1250 412260215 412260223
    0xe150105010f121116060c0f080a1a0604030302011508060f07080c0c010608010e07080a1518051b1e09043e010f050c0303011a0d2903 59
    0x30312016125181c560301680341c01c41d20f14030748030b4007420b840307949903200842d9600100280044040011488009188034500801580d00c641841028043ca40507003034600d135000301486a01ca481244000780300e0a80d0342200e00d81001c5070310011f4101e480060040149a03064200340c1907000030703405030007400759290301441e55a48121103081d003840f004070104985174420305c00903400803582c1c00070509088929110034210780243d40a40007680d9584841420b1040c240143c4004205580240403c00540d403100c0c0886010075002e049819607a071402c1c420900013030100e00407280c0010455000180b01002800040042903400b4481c903404801314141c034854011419030418040d110384400d813200e9882c03c140142000d00802600e4410305060380450286200d2810118104005100c0c400404000340501084807031042c100079040100c0000400000704481c11600c088920481074105000590341038002c5610192140c2d003050841c150200c05105540010002c40c04410b0140000300100350b0380e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 412262715 1250 412261465 412261469
    0xc031e03120b010302041d04020a060905060403020d0c0b0a03090614070f110708120d06060305010807030f051615020c030303101202030c0d030801091107080d021e030a0e1501 77
    0x142001d41032010020403500071008211060401506050f290140904007444425103010034089110070007040d440d220384118001c22280c10402000350605020443c0703803060303000c040d01a00801c0c1500c020403030000081b400609403182459203840756000b000380a0726202da0152401814641c81c1e10918180727055041c01001d030358950380310790321209509a41c0e20140e480b039405540903080d0002403240301808145e01031840c00312440d644620800000d0204c90312500a1030801d490030300180004400003c1a10599400c450642e140007200d00c2c00510300100c2e525140b0350140d8070b010004202e0314880c00138405c40410340039921810441810b069030f0740821686400e1512600004105160040501d0220240040c4c192038620084401017012103c1500c42140040c0c54840100681c0c081e5104d00398902d4005075880c0d10b4840c06813246030f424054210542805503000810a8501c041c4182c1c200010226042d100d0300c03494100300c040020807003001d28070a280a03500310580d00c0080d6402440c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 412263965 1250 412262715 412262717
    0x121b061312060e0d0929040b1b0c06040b03150a170c010824010201090812061207030302030f0d0e0d0e040b0103090c0e0c07080d0b1201090521090a030c031e03 70
    0x3585514007202816241c2500148601104140554288007070740e60004002030300030102c1a5032760301d01030218000c13200480d0036444003d80015001e0403256507060708941c1151444881030b61a07403510000511000c90744003000d0b600485203038001509000a04d00030480310313202e0b0180c03020140d40d0307401540c1402d02251a80340f40100e03070305a85a01d16068042040061061000162241e95943c0780ca01f03507401421082140c09a01c820803015181220040500341d4284018000e00c41c5145d4003c5d6490041b4062036071404c20100d80203194030f9a0b41e03c0018144004021a000c40140040280004c1c6010b9209d50089040c003051540d294001d010310010a50f000744d55481036071628205044403a0040e0402503a02c4040083c1c8002c202c0e12009401a801240c40c0001c00c255a6020040300c2a228668003075240d05105100e0086040498500440101c003103611a2288100e1038071182e038401d055089620041260003c0b0512603202845000d80c2d1181551070713044000b4554030300b51020103280c010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 412265215 1250 412263965 412263977
    0x203060a06050d060503070e010807080a03050a08061203070c0f0501020a110f0117040b060901091107030305060102070807080c0a050103020c2a040e011a121b061312060e0d 76
    0xc041c8528001d00003a243c00100040d510707103c000090510500c0d0380448414803001c1d006004244052121100074101702000b4882d40c0d41540e00900316001e02402d89051102090014200303071580304000424800701e50a580c1d89580928058005515500900b02102c01002d0007003855400060748654550304080e002095281c001d080151202901103860304110f5110010013400302c0c010103a0380228842c0c148000c19150100501c0008070050340040c100d281411020451203c121040301c4174203802d40f034041019651080183c4c6881a43d07800f4a849100d0700a001681032008586019004130444d44c049400340e40304011004d1340500000b00388640c00030140d00039000c3e03494000412803a07400f0503107501c18910300001011900240d401c5c0030165143d074102000c070204810307c605111070840d0242c081d41c0c03015072810782e226203e15849030f04c070010394800940b80c0d403030206031085001c0c0381d040d800146894204d010103007607080c0800c441c0d140c105400c107001c4d05800b08081d240c2c99880c0d078030700e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 412266465 1250 412265215 412265219
    0x6060b0f0c1c270801020c0d031b0c12032901030605121f150f0e130b06010c0204020d2409020304081206010c0204050109060f0f0b0a051b0d0e01120203060a 69
    0x15407410407050020310720380414000010b4104c000e00281c03808010007400707001c50f4000c00c80040e09866290104200c3d0130301603007841500c142c100d5100c102440d00901003600e80e00c1ea4035000c1d0014a5541c44101c01034081c400e620304425017020007004910400c0e40e0610180d5501c0081c451103152141c032044250304031aa441c4187d04403440341c101458001c1e030020412500004a11b0442a9140c000da03801c00c1c07051006010300d180f05411a0341085000941420038081a00c03042c030001d8020340000e0400c41603400781d509554179501582c0b0508140f00c82002100c0032840d240c402051a403118060040c021100042c4000c80d6100f40c3c2e10854001c4002890601142c2404107000b078001c0c0b546041c800c82241c5100541c0b21841254041e0a801c0f030700217610760a00640d40c82004095105203600e2103065418003102d2111004e42d285081182030180d22002e000e49044040c00f403907000140e103842400003600d41641c0c8601440782c000c000f030301d030300820384004030006e800ea20046480780d802c0f980150007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 412267715 1250 412266465 412266497
    0x170a02030a0e030f0d0221010f211106090118090207121404061b08070606140f130c090510020d080705090f0d02010315060507060b030703021c06060b0f0c1c 69
    0x14003c5a5290111031f14800745200c403403480d0982a0058451010300c08000e00214091071030f43e54400d80030f034802c41c84101d01a0354030040d15403802d004c64095000400e942d80564016007010301b0314129076184200300d5480303007480c0d4000d400a040c20349404096800ca401c2d03880c0075541c000038030320f01040407614050505105841c24503200d980b100c40d9012412a0101041448000d04546ca10803803020440a103469210440618460f000a00c181540d003000201b642e00c24006010f05801c80001050350713001d400050310b001d07001d0ba00203a00a100c0d04034288000394040752581001e8180c6e2980d195a0300e42103030854050143d5400c403a0808442c44080784945086e0791801d000c60b02c145000306100c10b4600f20b51050030080d901c07200120740080f43c2c0740204000d1f40980f481403182900100310305491500003690164100841000c03080d402c41000c4203001864018202400700825800c0d503c5c661440807803981e5000070440c0e9058000c4070000c3c0000545004001c046100540d200300304101c00c0c102e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 412268965 1250 412267715 412267717
    0x51005151c03020304240e0f0315100807030f0c141503092803081f2303072d050109050f060c0a0b041406090a03030c170a02030a0e030f0d02 62
    0x3106400f0b42c4018000020102c05601c400c2082e8010709204140b00c00303401402030400883c40c1e01140c841c0e18070340e820410a44000034031a4007000c144c0f2200b0ba090300c0307251040c80062500c1d04254464040e10101205110030f01e02032171a400d02c100d00300c0b0321440c0d070f810030241e40c60ba038180c0c1e040d07119800b1480101030140442c09141c001c1d2907007050b07440c0c00c006920000584540d011a401c8555810f0856006054005060319800800d09004071006800b801616a4441c1c07540907080018140c2c0f51012040d01482c40d2071181d031b10b000745c100d5480c030392103009008400c412510030010f68240c4000440f10034407130a043c4803c0ba8010b03112001094101001c211898003540c2c40ca682114091016441c548001c100901c41180980801450b50600c0e00384500101507080410b811507028405008060300002840c900c0f40b0780605d400101e131a90706000321034410035040300342c40050600f014400c1030300496004601036400803408011442d052902a5240d0060720148000a90240030340342f0881c1c080d030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 412270215 1250 412268965 412269019
    0x405040b130504050f07060804050304050d03120608060609060d02092e03060506040b060a02070b07171b0c03010b0303030117030c0a290402030a020123040305100515 73
    0x300801c801c940104041c804450701100e00307549941c04501e90042c500b00900102d0007030030346803510140c030b07190039120381da5070f4400d91241303a0007104070f00000800c1c54411040811042140b220601c03080c0c0e82c865240759201007d07103485115000c010040740d800e1404800c4000c48a07800b42c00d035079041da038595800350410340e044c000300c5100c0004c40003603141200040039a4003a42c070901d0000f41e2800c203101800221a130000c9020f008000c100b180c00741490300001e4900460311045030141e0303070740694078240003070882c04509400d07044004240c005a40c0c80310032804000c0c40c0300340101c0d9507004000301014265a00e4030f99103905034004000602c80a00c02d6041500c402540c041100c0c81c0040c11030600746016041001a210b480c80021961a80025071401c09000880c00c0303030b4403d207030070107030002900e40d074030315030003d0510002c00070340300e01c0800c00b280c203c8a13141011205500d850f0b60f07080c40c60312010000f03601c0418515002c00200350300200c0c0001049004064581e1240c00c104042a82c8090010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 412271465 1250 412270215 412270219
    0xf08060619020f1501080307150f0c080f0a1506110f0a0c030b060d0c1809050f070806011508072001060b0c160602030f0d0b060a03021e0307050405040b 67
    0x1c0000d503001d841902080030403194641e009000e510119a5480d06140ea0120804030550340040100130b120350000680345880e400c102c4c0600c580c05c0b010032000007445606403204d9120304000d0141c00c101e800140c020302c201c1c4641010b08460f99122002c0007118800d10310541c109040010030310406208803400780b401005003003200c259000000c80342d4a44014000c3c00c84110180103000d104120301d4000d0581c2006060b01d2003070100c8520740c4c030490515280d000b00280e035240c040f2030010f031b0301003230b040103000540040c10f503998402c035211619218502801164420302c5071800008490913a104501001c0d000b5035191485901c13001340440b5070032602c0d1601c40d00642e016803900242c0c2d4083c85141c1c0100141c410881c1d64140320424282404914844c00c0d55420030440c00304071094000c0204c9001e04444900302c1d43e00e10342c40c001d00c0010b200c20301c51140c00070740100b1880c000d90f800d0741c01032040402511034a220210701d05501034452108842c20400034000384420800c07810180c000f442c90b8500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 412272715 1250 412271465 412271467
    0x30607111b0607061a03070f0b07030309060b0d030f2c0613080102030c0a0905010503060d0b090f0102190315060e010c0809120c09060316140a0b0f0705070f060f080606 74
    0x41031311900d054820341d8120050b580c00c1e6030b030807011382d1038104407200c001d180942d0501900c41c44c020009009000c0c0001c094145900c6416441c20083e5030351102159035002000d44038258170724100140788900304103030340000c900081c070000007616000c000a400002c0007070100e04401c5550081c8a10358000c3d4510f014100845c1001151004082c000365100b000807000d803644072048101c00401c001403030340c0101e040c08000c0040c40b4150300c41c0c6840304410358012418000781e072039004030395113405d0035a20440f1465202240d4101441d00d110785900712135645580074400c000f803882c03980401c02d405110b0440494080c0f4044003180d40921f8a1801e12801020310301d05162541c804070b8807859010138035040c1c2e608421140d032283e2801110003600b107081a4010407018403011040a411031450140c0c401d00000c070703807180040381d4031a50b0f184c000e42090031125455040c0d01407005a00d400c030000440b054000c1c4480440c4012032412000f080700c0b02640d42c000c40003200039080d11a904040c16a40c0c110700 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 412273965 1250 412272715 412272727
    0x60f0f0604090507080a06081b0609030703030917010e06160509090702060f010f06050a030e0705032a031f0b04060b0a022d0d0f030902130b030607111b06 68
    0x61103a010384010940d000000c1840e10707101e0030082c00d41e40010000d4007002d143c68130074004d0800002d02c0811580f400b0700740380554490580003032241e004e8400c503280e00d445006800f00030594400140000c40e00e1108001d041a034034501003600f85d4407a0b02c24002654800000122030340882e42034201c482c6c02c0c40c10100d290489100108a11080443d08440507901103401c1c40f0700c40c04040961401000c642c0c1a6011903030420b00b00402a00c90000400100760b1a2120071260b080140001001424010216049128804ad030850b503d480601c1100d40941d036248484034906000c6107100c2c001c1250158504a099540c482100800c4104030503508656102c1c4013050441e41e42e8024030b28000d071a001040d4108500d0350130b03109034491700e000701615680003410395940400040c2500d00c1801c035007800351407807100c014118010f003110340000c2c1d4411050401032525400c0751b408035189000039015070348a50b8030f04600340c6c0c04252028901c0c030365a005c1c134540c2680da1446c40403c000076200800d5613107086 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 412275215 1250 412273965 412273969
    0xf090607030e060a090e07080114010f09090606030507020f0610050d0f14010213140603040311030c0106060309032a0b090709050f0108071a030a0c09091e0c17060f0f 73
    0x70700101c1300540442c8085200f407000c0c40d0b01c03110150748840149070001c1e40c0d40c18020f000b2004c0044040e12818403040620801040b405102d503c0c0181031041010000c19a60b950000c01804080e42e001d000342c051106400e410040114549101741c3c01705411241591409050002c04e000c01c100583d680542000400700258400943c6411403c0c00f0340090b03191028078046a05401d13059000052030b8040b05203041c0c039522090166a84030350513042c91007141e40700340d5005085218928402009501c2c2c91404520340340c00d41e0085412a02030380d520722401e80d114a1103002d900e8400f05003004154020500000030b0241152a070344405c8078820b98114660703c00b2000195041030310311203241d010642c014031aa50040048100502c0ca4586003a0013030600c80c0f540c5001c1c032001c0c04480403561128003a4450034051602e8900403d0303502c90400a0b11030700c4105180c0640740150009485051005424100e44a50141e450000140d51701130a00d880d03550030450500c0000c0f118036000500f4810b049055 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 412276465 1250 412275215 412275217
    0x70509011d1f080606070b040f060204031b09060b0301081908090d0b061509012c060712030c030515010507060605091305010c2a050c06130503060c0f090607030e06 72
    0x45411600604a402d5160070191070940020005401550b05001c08404603a1000100307400c076421045051484449060181c003030310598001034103240c05c0c40746070f40558038008541801c5035180c9208210441c1c54000761074161100380300704001544543c070442ca403912101801401e00d4440d102e8246031451110114402c2000c1740400d958509244041040508245031054900b160348224146800441c10028280c40c070b04c1c0d15007201c2c519842001c000c501e404030150381036289004124540f146860720709080042521800f140001c0c1c1080680c12501c1d0203401698001e070b01c142040249581c1040044a2540100d1010340c0d800d525114000384648441c2602402014074032014003901700c8a0401509440400300c0200400c1400f001c031880b000840604400b0028405031318041c01402c81c203100340b500403254402c0ba4000c00014501c16000c2c141c20400023152800d4064a550342e07981c860710f55445c010306c4148201400200000714003403421500a200a52003418500d080c0000180401c80c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 412277715 1250 412276465 412276489
    0x1518010311012304090f15121406010b030a0e160b070312090809010f02030703140a0309051510080606030303040b0c130806010e0c0c0c041a0315041703070509011d 72
    0x50720400040c10f05c01c00d5100d0040702000404480b0031700101c1d51071103042c0311915251007001e03502c1100380e2410041100182070f0f19216040107080b0740a550b141c5009220307d600984200c280c1e580381c00c0c200d180b41140451030b01d40721503401c0000101c040c60007a01800355405030200f20200040d00d00c048404040610609040300d01421034a900c40400300009084000b00441c1030303055620900170000080d92000d80100b51100403407034a6101e140424040d8003600d2035180050150145900309592206082015445108416280100c00d40d41d0f002294842e0380c25510150150003c000150201302c1d4800400c1c0c10026524a280c07421f100c009403220251001d402010703068011000400c05480c0240d01c0c00c4c1c0109500a001707150030705005059503a20090200c3c54012910b520101e5000e440381e0307410314008440581032b0b5440044084540c045400304031030854400500c0e80703100403184034840541c1d01c07400c3d171a15020710345401d0304015198403482d00006105501c0c3c1010b16a99600c1e0007403941c003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 412278965 1250 412277715 412277777
    0x61c0504050d1103041401140d1404060b12060c0306030f06040302061509331e040c0f0c0b091c210c0914040e0102070308151801031101 60
    0x548240009004203c410100f141d0b0040e82c0c414041444445c0c4d001400061304c1800342040300c6000c40244840e1f08a004803c101185a880c04007542e00c05136021400f01d1149124500c1042800802c00400c50100c03014030031507100703a2101c00020110350340040255045940141210003001da9451251701e00f170003c54084005030440814000c000d001c110b2071a0f2600c000300e45ca5007061406198640ca404c1045140720344d8101902c0b05610001c0c049448a4800300b03029140c42c8071f0040c0903180c50200591100f030180140c2c905007659800034030844584403002d00030b41c2c5004000055032600c185c0c110014003e2501c82c040da550032200314031240700818800b0382d152035909881c403604014114102d03049110f09038481c18881c140d010541c0c06801101a00c070702e11801c16401071404003040041070000c600600e55880001e45005054204080c01d1080610b003480c801c16140c0e04090043e40e007a010050407400c407100c8014000507801c045400302e01c803010b2501c0340c03000d96031b010341d031882c40b262010500c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 412280215 1250 412278965 412278973
    0x6090911121b032b02010b011d011d060d06050111010b060403020d0c050d06091a0f191506032c0c01080a140421110d0e010504080a0501050a1b0e061c050405 69
    0x20300c4d194080c000c444a0000909020b42c07034001108200c80d0780001d0b4117106040201e000d41c0440c09110b0409464001000a828141c0b1000307501001401002e0341d00a0340c0c0421201e0700c040c070320500c050055144c2818040d1600d814030307296500340414400d00441c1150104400300000c1075507140c01101c1455079008000101d101a50b904028100324568060b11902c066070030304101d0352000d04c80c459500414100a084c48011000044000030b01c618a00c00401c2100c01500261103981034010341101c090803401c0e43d100e45040c0358102c3d4100d003811203800c06600b002510601d0796028229590741701d50f038690089800c14082003580001c600072a070031070b191800100c000c2803402c0c0191040b80304281a00380025100c5880780780c1c07a076403c1c0c2400000c040100b50407039220181d120f401520f0040c20050200d035407400e402c0c50001d0103020308482241840d40f616407645850080302c1d0340d860b280801a1110320880a6950502c4600c0d48400c1010a440c194400c20f0700051441d0f01c40c10f480b9030700440c060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 412281465 1250 412280215 412280293
    0x50a0b0103020411070b240909030c0640061d06130804030b0402061308031905091c0309080d020c03061003120503040201090906090911121b03 63
    0x422a48001ca12811204003804004006004c04100075008452094038114006810030000142054141088d800041000500000e0380000010300035040043e41a10791540d180006280c800c038a04000904524500e00000e101455090240707001d040c0d41030f20346074241902c0c1c403000c0075543c1c110010000b0078211030003111014818000aa00308400111040744008142c641c01c141d030003140806050fa03a04d03400400c045607a00412212002c02805441c840c1555500300749480303410540308643c04001110b90140030038403403011a10180c500400d045c004986801c0e4016424000807401c03010b10099000c080b603400c004211796000644030354018040900700c1e20a160410001404c18003010f5041c103001e00000d515171000402408080c90060b4507566075000403501124154800001d080c58188042a9510700786c001901c00c60080403484a048501818844412040900440b5a0300044007418504841000000010400804554a03c204030011034665602c220310321549401082d06 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 412282715 1250 412281465 412281469
    0xc0a0206010b030118020c03090405130c052403060d021c031202070c030807030c0f0b060f0a180906061505030f0a0c17090f0d090602150108030406030902060403050a0b010302 77
    0xc1a001d03210507010542194503011255180b2500c64410f04441c94000c60b1410003800300300150b07840120020000e02060500741c90998600320381c40e0051754400072148004c0744500b00760703409140440d854107030300407a07100c4100d502107030b900054546a0301862040004d005662024040c0d80c44841340c03a00b4200600c094076003c2e200302c4203c0c540042d00780c014003803440460b503203416840c21260892000ca07510703006403400715540101203400030f142c0052014541d040c0180341d91121f100703407015188080940d4080c410030040d0005449541000050400d450342c0b80b403641d03040703a244a41f080001054060700c4028194800300301261100001e4000320810004010303136a586078002d109034a04009080c40d24000500d003d00145654800c031000e6404200c07080f40401510000d01409400d0700d40800417580d004051240c00c0c0b14100042c403442212030301d601e1003080c401e4102e8000a000f9807801e45030041c10b03005000c95190603640220b0900000000c0380092240f09100d44c03203a410320f000c5c0c2d815481 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 412283965 1250 412282715 412282723
    0x1b16091505040612060e16091b02030c061f0e150a1211060f091003090201200a0b040f08030a060807170d0305090f01020a030915051306020315090c0a02 67
    0x7001d81e100b5420001d04101c445a519001204180c1107000440c6004201500500c0c003400021060b0351051008800540c0c0d10503540700035000054004d204000d0864900101d030390380608034401009812110120742c0188079450004104918020400d01c500c0d51010440203030513003140e0840443d8500c07400c411203450400c03d070b03901a10400102e0611600c0945454070080501444180504000182c1c05100406001a1100310f4030080656651114035000100501038008003280892156090390348400a0210304600d00710008004001005842d11250307818400640141d6218051420310341c01b242d001e5006621a081d181f00c041082c0d4a006940c03072912005501c03840042c00344180714260034501040040300c050341da140200d0161100c103c3c0c40c0c24014014240c0c0300315840000c0d9005503980503042041214051910072180c0050414036106652040701c40d0541242e84007103401c006282da501940d0848400d0f800303080004c80d0304022035034419050b07503001c0824801044072075440d40d0401c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 412285215 1250 412283965 412283969
    0x80304051507020303010b0901180303050c06280506040e0124120308130201120501260303010b0702130f060308091f120f020706180b070e01051b160915 67
    0x726403102516160500a450340810700800100f00c00001c1d030f104003030303102e450b07c41580600441305000c155900d00d80540250300142500c0e00c02e0080000080190301007401250581040c003003514800030388001c40034020940144800e0303000f6070b1218141107902c400d00c00c101088211108610211800200344c109101c0d0a5000001000c1003090f0500000e5012030070320f0b04164100600c440c0c0d800740d440141c031aa4404204d202020f441c0000010317201c0c1ca1031039103d4160b21019145401c080345104865200c0c4024040c0084401013041880c0050414080309003e0b00d0507800c00107085d10510301c42c1015074619a0043d68040004610702000b03107006801e45098000400c1c0400c00100c210300c01505611610008a4071070303a44203110801c015240d0100e54400754004000c209400500181c0d91001c0007800c4156500780504001554840c02940c6503640d050058540340d00746075a1a4480c0d581d4541ca402080f01c1d4000c203540480004100c400c0b110140071101e4010550504084a98810b03c59036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 412286465 1250 412285215 412285243
    0x70c0f05030f03131412010507030b0f0613060e06160302060f06030102070201090e07091a0301151706060f070f030c060f0b060f0c070b1b06060a0311130e010908030405 74
    0x4c1040c0c21103424020003080840d00800400460305680b9800101c0f10090000113200d294245820090480c0e41944031280c416401c4650003002c2c940c0c60f0a00100740943d00d180090518200d00510140380950300041040400400d03403454a41001ca032000d0820403500d003100940d0058041c00004210340051a074007500540c005c509103032183e00003d048491030b200d880440c2e08503001149000784222004400340151108948400c101c500380c99146600074491002004004002c030b040e03162048000d0348a1402400c14210030703481d98800c01010754080c3c5070924010100300f00d41000192545040c00d43c4034029118200250407504000054440c0d01c040280017a242c680321504655405096406407031000d140d4a032034a40e44500d143c9000490341190803030610220765042041e14420181e807003032403000155130fa1510344800703024009083c0c1c00300500c4011014000006810110703081c10102010001c00701d501c4800180b4242100c01080041d56035007400001c010a006081002c0c4c0e44032a00c3c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 412287715 1250 412286465 412286467
    0x30405011d060304060507030e0328080106020303150120212104140a1b0b04050a06110a06020d0e0c0a05030a15090812070e0f010f03090503070c0f05030f03 69
    0x103030301d002400500c0020070040400790f0b81c10108000701c5c842c0c3e00001034041030100702d990b034401c51201c110340b00c48c201540320700b0901840300075202903100300123460403a13006400560a58858100d00c0d00c803004201401c904109203041c01d17440300500c80c0d45000003030344408050308041c42160821680005860029100c840d020442150018900924a5034a4000740d06500b0103403590310703003081e0425114000f949070b4414031501405010307500c0010001009110940c0382c40310360300c2e042c1c0750b103d004074811650f0000c0201070400606015103000031305401d00c0001e568a24403a682e482080743c00c1030a41d28001aa21309507554520b40420012550740f5046072581c000038a05000280d0380c10420600038012204411404032485141d0408065249d002c13a1060322941c6603405080304090488041d40010340e081c00901171070600003014002414107075a6001c07010b550a03415005451051000c65140c8001c01116001ca0040400c032405054001011104185000200740c501081903402e1000c0d604 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 412288965 1250 412287715 412287767
    0x9020c06090a03020705042315130905060601080601110601090e0d0c12030e1c0203030f010e1e1f0323030f03041e080315040e12040b0309010b030f03040501 69
    0x1400150030411100c1c102c4012802046410550b4030b03514441c1c04607840508d0040034829001034024030f00f00c0c502000d8900c0040480c403c41c0342d4090350b0541e400908aa041a804035005500c150035143e4005018140001d003020107100710b40c5014026408908900d58a500d000c0031410f042c000140c406602d403074402c1d0401c402d9180c0c0821900721030000014182e442c0c0c0700c1c012010b0300380300d1000060901300b15000e070345851500107074503503000703c0318003c0404940303002042c0e065040c1d44131801040414058201c0c514110301c81f1405400240042012a071440c5000110f40e4080030b0a00c00b440c031540da140121440001e1501c2200b83c0b0000717200d2960410f10101c404000284182c0c4e5100d0b42100d00400c414102000c820016840c4d140080d040480000030062001c0d800400452401d000b900c0411030512805403680c2c0780c10507180c14101642c030802041107c40301003009550400b03100c40000449819880000303103400045460f842c07954102240c00c201560f0441e04007400c0782d001d2400121010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 412290215 1250 412288965 412288967
    0x3190206070f0e040b011707080403140403030e12010f1a10020303090a0f0201050d0f15050604120308041119031103010504080919050918011808032e09020c06090a03 73
    0x10003e4041500903540c0c0c0794101c000d40c1c491055a00504540b0310b0180d42418a1040200311a40031102580400e200955041c041607001003100c08403034142da40d007902c2c1054034003045100b4940080c280d030305640b20014618000c0b01e40c441c2400301030710309070f005c071546100d0301c00e01114440101012040d0f420500c00c201c802c80b00031903c84032a40e032221081c4502440f520060b0340c0b40c09418183c122203490271194004402065000c10950580c01e82c0c1403c0b802c0c1e546040080610030b038005c3c00130300381c1750141020019002d21402a0418400d00c0c43d4980b00c58104007240300c500da408260b41c5030041590b010400c0c003003050058100407405600904c0180b07004c0e01c0341d4516204210707103a4002d0000d05d6071082d8800c00b00d0041c0700508070051403000d01d0b08011105a072101440010a1082e5103480000c00008001c0103502415681c4807110f20700b96a03400d10080038400c4000c010720f0079605804c2884c000d42c0b05d1107100302d014001c4450300680710035008144514203500204400e29550169a40c0001304e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 412291465 1250 412290215 412290227
    0x110c010806132901030e0d1d03030c03031f090c02070b0d1407261905100b070c0f0509060d11010207240e1512071103190206070f 57
    0x3036001d41c1c0e02d4050307400c2e101d140d10040403045500c0c1400412005807120081c0074440842c0010700981e01446402242c803030701a242e001c40004c05c004104100c11800c0c0301c81d00c04902c080c40c108000c2c1540c0c107044d12100b00c5401c6034021528186100c0d1022008161104e02003c0d81e00500340f072540801003800100c0307000e5030b1007855014859180d540440c41c100704001541202425101c0f510201c5128242200c0c09480041950036008110b5211001310020b002c2c01c417940d510910142c8014200b4008200781e100090001a04402c0c1040c0004008207051226400070034050303110f0741c22201c0ad18540300380d02000d074206802440c410403180051185c0c540c5c5134591484059004403154411051800051b032400030141d03c07011100c5c003500c08100302031020100403000900e26440d14034840044904010f5081d0412811074807a50040c03011070f04000030f0100040d40315081b410000c0b40710015104207031868103c010340d0302c10003c03c804044441039050121903040310f080e040265400348511005018 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 412292715 1250 412291465 412291471
    0x18070306060e012402030906070f020d030c02030601060f080402101704080c0c10051c061e090506060c070303030c0e06040b0a0306080d0e0d11370e1314010204090b01110c0108 77
    0x4144002705030541070241000c8a42e114642c0102118030010b010f10b0051311449803050309a200380181070000910344c0c0182c1c0d0361000c4002e40e64804070180d4941e804c100b450f0f0a400c002c40308102101100001424620102e03d000d24040d041c215210702214001d00d28002d518400c141c06460a4201140c13600d800005488540c1c0035040f004144901c08a208001031006074004403091454490034108110480c99400c103070351064505000030b07569201442458420740070304107407d9000500800219209074400b89041501c1c0c0352801000c03e401c00028003d03040b41d00501e020040006491601517094860200240815800303840e0a10032001c1c0505581c0008402c50701610280c0782440410a81c421130a002c0302009020800d19000d602c41ca0110510b00c03038601003049400940006494015040d00e421228203410701d481e50f0782c690907038030b85070445228100d03031034241010b002a41e0082030000c0e10203130040c1540002c0d40d0090000041980198100342000c81d0810710f00f01180b0799100c15260740c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 412293965 1250 412292715 412292719
    0x30c010c0203160b04300909090201080f100803070c0602010e0d091e090207030503060102070e04051c02010e10020a03110909060402071b140109091418070306060e0124020309 77
    0x202650311420f204a204c850050017a0148050070400782c0c5089034802c080c182180c6c50740c0d1f0010348645609102c001c4560740c078400f0b400b150b15200025040f00241030b20315070227207003101d0b85004144d640c00800d01c1c64004403400c0b5641c10741d115041c03100681c244103040e002042c020003850768001c003030800782c814070313150041a59016107504501408284001c42600410b00d14000b10368520b010b090040558000360b0f100c50043c0947c00700025401c0d00d454400d4042c940100142c02c40307803160707046110300c1f8043e030a40c4c0080d07540b50844440302e03100920001c48041c450402c0566a0405014024100c0c9d8081c1c00805c0340b09001e02581c40d160300c030740c4402d40e1f0000d0160390043e6200d01c181401ca5600c6255424449001c1c070800c00410410b0008000c01401002a241c500c54207031603400c000b040c3d03008074248610404080c0c0001d541c007008a400501c28202032015a541107450342c0b10310b01618002d0304440e0381e0b6500600100200c8680101c2c1b08007400702952811001954014000d460344109c01d01c01e4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 412295215 1250 412293965 412293983
    0xb2d0f0114040204030b01090603120c05030f0a0c0203030c060a0f02182403040507060305071b020114040503070b031b0a080106080a1b110c040e12030405010f0509030c010c020316 79
    0x2191160f5044070040d6411090400480d03944401c040c0280003540811521882c5449041c40b40500561605007804c0d403040285040c14110108c00401f80c03c51190b41c0b0811050000d04000350b10107000800116514502504080c40c0c0900f0900a40d8a00c42010210307520410031554203001c801028a0b0b450000c40304103180c411010304030301020b00240280c1072180c50004c01e1200300403000a498040394032a0320b00f40440d5035561403d844090400001400d000300400c0c00400540c030603048142070012034683c1170705290711980400d1421000c1e4000084020000052103084140b125040c11020071805a6a1500e052214000c107088018803c0d02c040c0080c0c00081043c0311440d4118984a81c3c40000940c00c02e0350f00c0c04014080310800704085035500a1884418050501c0d0098540308420600101400c0040328109186607100500c1650155643e080040b02d031022030141c14000c01c004401192600c090005907402c6666140e505025540204806040381c03402121011280c1e0300a9507131 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 412296465 1250 412295215 412295249
    0x6030109020d050c040c140d361101020703020a090b04060e070f080c131a1e041e1505070503090a09060e010e0907060507030302070507270501030b060d020307030b2d0f01 75
    0xe21000800c080e1075000006800d89c040f500054240e080d241c82c40c018248070340d0702030b0164016a219811400080d40207800140140303d5051243c201010513140031b0320004035079582c0d0f841c0c08030405080d5580c80001f805808031502c1241d01001a030b0b0010b01e480006894101416400000034030701e4820000d030203504054600201206000745c815868408003040f90a100260300603805034040e01810001511030380a4030b008640140b6100103440102400800b01c110102c01554a600002c5085500303100801011065844226000c0024646d40070042245400e0081c15480050160000020540c40a00b0801048400a54072044500c2820680d5503010282000c80207481000701c00b800e64460407800041c10889500c0c0d06040302c1e80d0102100350f02c1190b580000c2954030a10016022900e1840883c8152410302c04944411384020300b00c40e00b007a07581d0365451011400b240c4e02d001c0d90140340b00080e92100400d81010203030141c44240341c020715000039034002d80e6006020300030b01005a0194 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 412297715 1250 412296465 412296491
    0x21040f0506250f0807080a080f1902090303070c0f080601150e040b0a050622080102090a0911040e070f0216030f03080a020c12030405010e120301060806030109020d050c040c140d 78
    0x3030071064024a4885d070b2001c40f4206140294005007580c07000a40c2c0c54005440005912401801007000c402c09003450004000380c98042e40080f1495a4103000030031025000451075102c0c20010f01124416014140c41d10800b80e040a01c1644050061015802c0c0b0000290b405031540c0d11507507080b1000640064098080341011840740c101c5500840700190420518000303401001e5a00b40340865100110f884a03a030a080c0d00444060325001900e0b032000340011045608450101d04ca0010400e082035903034080c02e001c1c0c48040e10800302042100300d001c90401d40c1070010307521420a030300816192a246a80f420070052982d0405000c00500d840840d80720030480d012913104004500450700200100749403088954410f5400b2074041d0701e4100252013100300030803030748201540100002e04503840c000b411f072031820001b0120366155607280f500d44010ba48002031080401e002e00c00405058002a00340011a0001504941482500b81c114254035a0340011500351110a001c0800c408042c100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 412298965 1250 412297715 412297733
    0x20708120a06050918010b06040810110706090308070306060905090a0c020f0d09080705040c080f09070902070f110a0803090105070206070606080a0b0703050f0a0902010221040f050625 81
    0x8441e5100104d0300030701607011744040e01a1910400d52008100c0f5400c5070b810000184510311440c3c481d0780003240c02500c01080d69018000103288200454a09401a80d0381011156003981c1200402d550006101d219030380b500c50300c5d02800c03440c180302c3c0029042130005260b074200144010320140d1a04078851040b0b200b44400d810201001c41214001e10204002901107640e502500c0420321503180700244c2480c1c6030098420300401ca403282802c0d9260103840c0407040100600140b83c910495400041910441c4014045a4010700300c5501210507403615002c0302c0c240640e40c510541d00340c40e051041c0e0714040119400c10109090036a42c80e5058404542d144c012440040d0060f407600200003840c00010513031b59032040c4500701c0a003103580c4d06001a001c6840a40b2804900c400d0800043c403a940c040c1e010b203640900500448641c0341e80302094103809044207016401c0b416012600700320040c2c403100b0b00700140030b0407103942e42000361040915004880c2207201a0b10086542450b1040c00600c034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 412300215 1250 412298965 412298969
    0x601120f0b220501020d0c1e08040f170306010e0d0b010501081005190510091505031003201311030a091109010608040b010504060803090d060f091a010801020708120a06 74
    0x422100d007020390f0422030b000f90080541c40d800d10f030a00107000700b110312909400c101001d0303207180e50340709005041081790000030051044484480c0c1030200d101080220350040e030740520003003d06640345440d1000509076022010000c0c081c0d252468100001104458480d040d5071080ca131000150361008800b81c03504145d503000a412041d00004416080c03580100740094903030680d14003000c0c0e50151401c032244070051150041002803018000012131003000150b40100303103401d910f8007490f240c0d101d03498440c80c03601e0140708040c2070305215213250408140c620142d200d4501d0811a00081140300311061000404003110076954050380000c0041d0a916a800d0070317000f814207205036031030b00c40181902c03800b80c0c1c0c107544580200000081c01d20b840e004401c00d440c2d601c00654100306005007880341001d0118403c4900390f0312400004024100c600c00c03000001e00840c566082c0c1c00f2290100034075580181c01000c00369004210640c0800c801d6004c90380003941d620781c00c0c02d40e41e4036544014000c2400c0c8e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 412301465 1250 412300215 412300261
    0x50d030e031212060306060f03100905151e07020105160507060905150109050c03040f080d0b091003140102090f012709020904051003021003021e0307020f0601120f0b 73
    0x100b1003554507903c0e51071461164006408451a54031400104140d515024042903415800351040c070000012941103110068450b1040310f8140f8041c1007061640c8104880a00442c5400b6050340400c40003555501e402c140d40340000c01c0241001301210002d0345401c0300d8001402000100c09040040c164050000250040c05540300324031501000c00d03d4103428840e0350f16041c2000c0101305a804004100c070b01855004192440ca50210f50354a00c4540082250500140c1e0743c00143c45240c840c03440361446070000042081c0e0403411441c08141c00d015102402405030302c1071000780542e4655000b90305480600342890043c00801c2810b0116510b0315840001c1030440c0801d00051202e41a0040c000841045400340240d648519500441041511010794001e009084080301d041c042d500030301c1d20580a491580030300081400d44011340d40151010401a444840300c861381d000240400e07405040c00c1d2005180030092500c40303039554154003901502512044001c500e030b5940200c101c2c0400854 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 412302715 1250 412301465 412301467
    0x507020409030f0206100b072a08010509011a030a2414010f12020f04020c0102040918020108091f05101212090f0302090a0903021f050703060f050d030e0312 69
    0x1501d0000c050f500c1840340180075105030004a0985035034400690103031801007404600b81546510750b20300e138004006103140100084caa10340340380400310742c5046c042d045040021441d8101034850a084444003006903507000c4100306041c3c155900841c5510307445030446031070350303c00c10300b0150b0f032030481c40700540c1c06011450101d03906000308500060380e040300c601004014120750b4804100151150641c03000390f0110010604170810700d020b41c040d1140c281240c1c001402c0645485408044800d0003002c08416059850704004669201140f650301c081090060005001d446124050f04144c0c0104a50310300d031148001101100e0311501a00100100301c400d842142090a20700130401d50100c0b06d4000501380840032542c6540950110105d96020709003a100f650b80140d544000c24511200b1400c5000e5600641c46026200c80b28103416490814001124200080e018040303450a82c0319005141c0b0740390f000c00c0240d5828030410909030301030402a040c1c0365054002401e01d03500714800082d00c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 412303965 1250 412302715 412302731
    0xc0405070203160c0513090327080d02161e06030506271e060d110f060a18061706010e030111030c0720060403080f040506031e0601080708061005070204 67
    0x101d511240044960586c3c0c03115072410000005400e0b5002500c000d008191804842008000d86008206a041e00c1110680015840d24580750408800780120300050348200e11060a4030600f000d43e0004150840d9410f965811158500d2a5404e2a1203140241981d600c00a4407545039408a01c44030a0b2080400c1c10b03041c1c41010a180c0b034002640d0840342d10400704491103d20381400401401401c00924621684c42e080c2e40e81e610300300c8004402900404074411000b0303151900780280c03454005c0e07038403044c0700d003c82c0035000210300d040355200004110940000c04502903090400c1a0041c0080c43c01d0502501c8020102c0d0140c00e800c0e40300e6040d51800030820840040b1180581722280c4200040525100a180103110724070481e1740301948907408000c1000000c49507401032200044081106062075680c8000501030b400484a400390003440c1003801890455041d0030b60341c403850900308220a81031020b001030808400a0109018983c000510940720340503000703440320158020000c0c0500b00e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 412305215 1250 412303965 412303973
    0x9040f02030f06010e010806130f0e01020910020304030b01120203030c1b03010605150f0304140a0521030714031b03040f0b07050705030a03110d0c020c1c050c040507020316 76
    0x140c03048440c42c06005010020480561007141003214800c0140e48244480d01d60a0811212074200c2d91a000c0345a40c0380701c5e080c442e42240c00b651442e210310100068548848205202d5441e0160b24040c0840d0000c07c014030004101d081114150f07038130314100c0c04030075440e032020910303520132111000c2440c0b06a0615141b01c03c01c00c1311854010f20141c00070700c603603541c0d6828001d6070998902c10743d0080c030080c08507181410007079000e994080c4c02116692407088100d0460750416000f41d005480580184090a028004015890b402c01d03054681e030f07500c3d51402c402c00a003480020a000071015070700001281494581100bc007298524014032942d403410070380f61104144d041107038121403001d42580011b15860107642950425508500510f1900842e038404400912403802c800e1001c440920011060320200d2140c01c4000d40302d6001400c1c203c0d1034004102070045a072138000c03403203002214060002413001c6a202e10800c000d81c1c02241c20b40b0754450503421405902c4800120f070200025040c240 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 412306465 1250 412305215 412305217
    0xc120201090b0309010b130b012007150f030c0801050102030315041b08060f0603190c090f08010c030608060601091206180f03090b072310150501140c0a0f03030209040f02 75
    0x210f0301194058164260000c071107040e0788c070740c4103900d0106d10542162444503241c0321034410070380310400690701003039211510032081c44480c3e481000061030000c0b1030700d0001d8061113605c24034259801c01040d25854000001d42c0c8c0d00c4003d24180240002c4440071160761101c0d080751168161328101c09640700d00100000704504d20440d9540c0c07042100c0384904503281006c4040b2070241164a941c030707807416082241079002c0c01380c21611a080083d00310b000216101a0b0100802070000340001003000407031520300030305032030043d0000442504400c0c103010321a03800c00300c00c0e0115402c05020801d01030090070508000c0090f40160750384048140c01c0401082412448140c103180f094451000c000e880d191409114000d01d84001c0262291311113040203007030484100c603034030341d2402d04540284621000b2582900c1c0300c545e202440680c40d80c0280314543c1c104d100350307428400b485140350400c41483c02c200d81d00c9400702070160a4000703034a85041454466011500481c0380a0000d0106489402d110802 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 412307715 1250 412306465 412306481
    0x9020a03060b0301030f020108090c040f0902040510050f040c0201270c0b0a05040b09060d110306040c02030309030414060d1802010813050a110315040507031e0c120201090b030901 79
    0x1a2400a0200b6102c0562090700e060700e403c43c090581d9581658015030341002c0190aa02c040d100c0c91144460070740d00c0e03000720101c2c2d9034069000700301c501c440d02c1488295603025010034810482541c00b0b00541c0c0721021b1000302130408441c00725840c41c1446040e801003410032000341c0d0441514841c480e44491403038002c180103100e03154284080b45e441448104500404042e100042e6080100704024480c25011300302c640381c0100030310310b000030300340001e803c82d0380003a06051145030100400105180a124942600c80d05002852462400d05259601c92040740504481042d54000c181c1c40d5440d01d10945054054803d010403000c412500403401010813004224001b401040000d0800740415040707000f5254444000c0201030603503541c140203040c40c000d846402d44140d45010201d01e0440d40a00d020754005d2004d0400c0d142141041c0140911445403881c40c00741420000000a241036415002c03143c0741c0141c0002c040700d5100403a00d00c0c1559120906800323001c024004002419485500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 412308965 1250 412307715 412307717
    0xd06080a0506070f110304060e040605060d051602030901021f06031415060a031e030219060209090109050f0403140702120c0306011e0501140d05010b18030303011401050a110709020a 80
    0x1c54000804076005d089440e40840301e50014403040000314010181d010104100170b1021807030607140e5000c01e000c1c0c0c11a4129010240e290001d001c840041c07129403c030881110310265241c0000340c00040d40c5d481a00d0051181814001c14001d105011a0703c075101942c2e0022050201ea5100803216586480b1800c01070300d8400035030f012904500c1c0649501c03046a6000c191840b1031170076038088600300602400264190b005100740742c9045010900c0c2108810f101721001600c500001c02440001c2c0b41c140c000341e41351442c1a0600c4000c030400703821342e50f22641c189001d4400d12001440e40200c0c0c02001c0c0008e4000305032071001c03a50440040ba1820a4040640454601d07030b0381c1e004070744c610205112104002c00d0684100384a19480340b40d0700e1600541c0d05a429281c403910300020022100241c0c07044400503008a1042c03030a5000700400c1c01e0300c403411001541107506000c4942207031000c0351441418044e0004458400a00924582c1c0e040f021210503a500030303950b04800c102950040c01c07844 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 412310215 1250 412308965 412308977
    0x303090c01030501030309030f060608060709090501050d080702090a090501020f0d050915010b0903070302030304060e0108010e091221040506070908011e23090a0209060d050c060d06080a050607 85
    0x8400c40d4824403a0034100c80d01a40d6000145141d03407508034944281c0a025214141c4848011410200030480300e401005903980300c026461428401c1c004488040c0c002610441001c2c107038a01140407541516400c81d011144280300d0b460305440d0720024440188018459400407610006806000020f04600c450807c401d110130354501f1101c5403205a003580141280c125800140101007030038000d09104900901100c000640302d4000914641142d0b0000703000400c08440260f580d640550814010050041c03003100c141004c6d00115210008100c800c2210304001c1000400000499070380d191004210801110904103030805a859400c1103030090302103403d0b840c00240a142c144a0703070341c0c070810303156404480f4552450010050310030900351003601c840301828040452152100030303000c0c02648000745a884024418001030120080080d4407440c65149046e010800208088842800c2140c405a031000460560b0000b84540d80049a0354428454400c040220010380c182c09910307d81ca8030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 412311465 1250 412310215 412310233
    0x31c050a05090d0f0e04110706050702010b01051809042d020a0b070c030209060d08040914060d03080a110c0a141e1e070306050a0b040f0c02030a120f020309030309 72
    0x4a540c54900c4104070000a035401d03400034803540b040c11170f0402164003d002142d146500c19948100350498030003070b507149a448040c8a100c40e02486140e00526083c00d0884c10f00c20a0b03074152041259048034540030308000c034000340821045c1a40b00f4480c110200f42e030982c0c00004203414411310811102240101e03d1820301182c481c2041050303400c4560f2005088107980d056500b800154000540a95041071481718144005140170018002801d146100081c0f114858041114030040c0940301600400640c141040400e502c500c0f095409100350a02103660314200c0c01c050010b02c141c920045690042522030800c10800c140958100b0720b8440844000c08840c000c10001902d16641c02002070303100d000c00325040f400c480b1154520000290548050f6a640d440e1701098230400c076103941d4015901c10080c04203107813501c90801d110318130040400084a00400196880c81000800c8081c010321401070100c440f40d40d003112410741c107220000d64490078402c48180e80d0350030588940015026400310 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 412312715 1250 412311465 412311481
    0x1080f100b0f0409020f0411180603060607060c1107080f060609010b041a160f0210020105090316050f01060305160b0c030703050a05070f0308010504110f040303050a02031c050a05 79
    0x41d508041c00000d000880b101c5900003084000e040540c3c00b00d8000040410400c1e956456210b110400b40c2580000b0343c0c1c83c02408007503508061000b04580c41400c044c003d024054a41600781c401481d800440042c8a0000f03100a0701d01340303440304080c0380610540c00c3c0800c0315038011810303202907c00b040496480d52070744000c11100d624240240400c84409100c20030400d8240f000701c400c6040100300303061404040341120a0101100401590882c1c07080e02e11000b14200740840442d0b00002c0c0c070080005043c15070180c2e07203078441e10310030620442400482d0400c0c08403d201005141c403002000300140c655078a03090b80c8802d00328414508022041c500021003a003040c007242d424002c05000f66180c21561340d8140da041c1c0004410b41c081080603c40c400005100c0720b00410014000e8480d0141989014100030550b544d40d000c00d88040700901185c1c0c1b041c520002540c040d40d500d41042910398030b241c2800c07441c501421452881241d03041440d803030700082c0ba920841c001c12203903074140034650310110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 412313965 1250 412312715 412312721
    0x11503150e0c1f2601060906080601020d0e0310020304060f0b01090b04030b07050909100e090102040323160e1e0c120c090a06052802070611070e01080f10 68
    0x14034180c00c90302d1422448003459441c010a00c02c00010306289000045441c000411060400c81c513102c9024424014400190000c47e14801400d10703241950f480d2402c03c0000f92a018441c059500744a07a80c4c2d6024003c0c1e90910011011204000c801c5441385042d09044015002c0c082e0f0008505151540791107495104070580825100700c0114071340780524580d00c03512040e0300105203108102c018020500590344410540c2d00900c19034143c600010301703280414111100280140f149a84100302c1080044c046850004421070180f011801001078450580d08001161003205450004108041038102260901c10300035215950a28030000040c1e050004070102941c40d05108a000c0c801c80c200404101c20f816400781d100450b103810032040e1300100710105026007280e03000c1000460380b50402924043c5000d64543c1c400300705800c001c1241000380d150130070750141c10100f1014801c030160401c01009880018007402046a4282d030b5036500b29501c60108200111081c003821058946070780c800c3c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 412315215 1250 412313965 412313983
    0x14070506010f1a0304080c12041d0f150f06090a06020f060601020a03120203041b0914060d0f020907030e2d1204090b13180b0709030803060111011503150e 68
    0x74600134030f5500c45440c0c090403034100342d14410645c42040c000d0302c6007100d010090002440d4024074480b020f2080f4040b408090002040c0c80303151411b074010081580c0c2c4100346181d183e2400c1c0e928480301c1c05018082801c522071655490341000da024070000b0b00b1607000910003220000c3c001510f00b9900e074000126140c2000b82c0000d00004c0c21003203140c980460359402590428410040e00100190030040d9030185082030b40075400065881d500d1540c0f01224004c00c1d035000030200c0d1121101515a510241124070004010380521032020000301010701960004c80e0003080e40c42102c03031170742c0c061002d0b880e00c2211407074550301000324001000008000041c00340c041110f540c182800d007800c10050318028000c2e82100c5500003220810307040300340403e2041c6281c1d0501e0a404003903200b0541030801d1041710203800c1c00d08014034000f081010402401c142c9400540901c4d06c21941001d404c0c003280541396101107018420b803048400000c001d180100000d0350501410140508074200c18540d40700c0c5042 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 412316465 1250 412315215 412315259
    0x9130209100f020c040905061504060b07030e0d05120910020604200d06050c13050a08030406030f0605061602100215040204020a1107060201020a080a062414070506010f 74
    0x840340c06014901507400d0007801d104603c121081082c030744002500743c0b80c0340d0409a8281d0401e100b840303c040000000454645400d560034000c051408602e01d0300c03445016405002c1264002d03d0b200c5554901c0990310081c0d81102c1120703503144a00307040740c40c181c0c0168451440303201540002503003640089001442140c1004000707454a0000e00b00440001e818004a940100198868400100d00d4440e490146201c2480540c8030f8111048060743c520086d000b4500c10011500c0821480034008119070a480301031030080b80030741d150746103880a00504d4110561212002c00c2c4c001c01d200549041c021031030b008441504102404440580e242c20a82040b4100c40c041c00d000240541804d80040030100000e20380f00800300d244d00c440ca41007207615000f100050b50005210201c035540000c8071504040210010000b00d85400c4072460708a404040396402d008124035480036141c01503e4803e85543c46524290341c4039880d01c3d046403250070034000c105050139070000c049421f00f00400300500c40140703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 412317715 1250 412316465 412316479
    0x204180612031202090604030b01030b060307031502091f030911120c06090612010308030405010f0b010c031b0b10050306010f0602190c12080307030507030e0c15090406030809130209 80
    0x840d40b801c948140000d44a203654035001c1001190b240c803a180107000031402860724045950440c6030003c603914019240500c0b89c0d200030780c01d001081340c00701110301800301124010781e01c0103180c000c40ca2001d0300740404035141629a81c510308458041c2c0211005a101c5d002c03146000d00034404000c4407d050017889000da03440b06030480e01030304000008118040c802401c0905100e0120341c43c40c05a142600210780c02540403041c802044400d024040b00074034444401d02c0000c07158000205560020500607080191800f00c90807100101e023103291240d44c1205000301c1503d081051f11800420a104240c007a01c1800b000003a81030040047c0d10540b042a070180ca00c680ba040f0840d5180001100705540e100704100000607000506103641c4c1245103d807000351f445c0d1030181009000c07280014940424181412888005414041042c1640080803680d04a102c0d004162442c10b600404004903041403420201000f40302441010b0300b01085c00b00d03141300d4000d00000050060b40240010a500011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 412318965 1250 412317715 412317749
    0x9030105060301150b0a051612020f01090203060601140d050106090812040315200304031e0e031c1b050a050705150412150c0e040516050708090607020a030602041806 73
    0x500d205c010010303900a071902505040c0e82c2180d01e5071611600e03604491142d541c1064402c02a0103214030b12100ea6008002c20802d101d0303402003074950100800581c100140032002001c040310500030303668018040c9004001540c0c6810020303020720350034020002d2070710400d5810440480100119015654445d55007804101d0808101e401381640e00c0c0504001440d0080801c2502620300103140300300e01a13643e1000c000321400c0020200030000c0003100801c50400d02030f0704540c03000103400f04510000c04040f25100c401c0d0381e00b181c00310a42001c2d401c071104100401001c0c8400000c000107060b004009403031036555a50708020218021a0300c040004c801400104080c11086280c500302a028020103801880703540f80b40412521018027030408034540d101c069005003010304c60103070710141c8100781c0381c200121581c001d010ba0280282c0241140c0001035001e816403919070980344140e83c0684a42c2d811601d03460420069003283c011012041d000312400d082d000c1c0f1b20301891040790b9041004c24140c0e4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 412320215 1250 412318965 412318979
    0x10e03090f1f0e010e0405010303051606020d110d06060203090d1401061a130828020f12030309060f07120506010201090b0903043f03020a02060403080903010506030115 74
    0x180070206900071448807807000d120600d034540c0190501641e44036150044403400142c000703903442c05002e008a18084c01400000d03088001c8460240c81002c0307000484c0800e00e00310f000f81c400c416500c16810704200010500c213200380e000d08030360b481e01241032143e10349130300f4102d0340c0c2d0150342503040c2c1c0310b41c81003509004591003803845042c4d05c50110001c98015200d82403169039924024015200c000f00151450f54002000c41900141c2002c10250003018900c410a419840140c10002501d40308603100408656810f00c60869042d4003400b00f0510710450a14030b41c981c2c1003251401840e000f4000081e030040903050010780b080041d9142c10103901c08a0f4810002820000d00e024150765035071000c00302042e561401d8071721680c01c810007550340341d06140710560103021030008030351520601c0440c2007945828400017034040420741d5806400d040642802c91070924150006034104d0340004c1e002c018001080010100da034001c9d00203000a88030034060500701d4203c10f12015000d400000280050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 412321465 1250 412320215 412320229
    0x3090303051b060f0402040b1e010e030319030c0219020112020a031404060c09090504020616230a2a060e040b03070b0a02070b0f030c07060e06090a0b0108010e0309 72
    0x80a016410000390102c4845814a0140e040c0d840da400c1620b140100801c41c42c0901546407031072415200002c0342c00010760004004540280e015040c480c402101c07010a490410650340141d942c070103105090300310705e00041c000341408080c040050291001c00342c6124801034201d1140d41d41a03480445410a49000e04000d40040b2504000c140d112a03500040480542500303005501038100069108100400076014101c0d50f402400080d0030001000003517540d003010340320303100100d440010050351545080049103c00016802c004420640c0c51809400c00140340040301d80300345818031044024000d004486615a80c560b03850040b140f50510900384620300d950394208010300003180300c00190740002e0030300e400d43d0030100d9107801c00f103404101b03250304000e0030004001c4040784a16100c00030810034490310000701880080c040c00141c20301045041c0d417140c802220100305540141c00c0c14a40300b501c0317061a2209031144001035001154442d810312881d05650301c82401940340c507008209210708 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 412322715 1250 412321465 412321477
    0x30201080703020c390d060c0c02030d0306051003141303020705030a030c11060307021b0604091109040e030306010228020301020c0f06150112180510020408010b06070309030305 78
    0x305502888900a40311080012000f0280c40021741c50350760a14a2070441e1400c0c81c20504400940e9241080e00c140d20340790200b0030040d412240c04561105031000559502440800c000d42501c6515410400542e040e070048080d40c0c1c00b01c0d003018251000c0780e411410f40307810320604680c0400340f4000c21a007081c41d640005955100e0f00543c0c507170590300c0c00000e05000051400b40d0104880140403820805800c05001c60034004452040c15410320010080d17854452074210054880c0102c001040b13070f03940300d0035500103004030a0248070581e01c00710b580b4815040101158002c40c2404801c0810039404002c5d244503030810303401411000107070b5628072420394541c2c0ba00d2006602c248070f401c2c0542c5003800244a0744096000501d002e200f940f191a1a00300001c1c44510008800311012000da80d04c0b00c10304040d100c02507400700e20b103660124010040b0604071f02c010094403d042c0400c00020180d009441210301500c002c000003040c850a111051184800040006000c50418070010307000b03001900b4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 412323965 1250 412322715 412322717
    0x509060d08030a0c0801080105040b06060310150323060f04020d02040312020312070908060c030c2206090504090809151c051006021b09060303071509020420040302010807 75
    0x10321440d294840c1c0800340d200740d64504503152624240030740250080b030140c1c01800417000070400c1d440c19403070700c0003144801750002c2c1c440e540001c00325103c0c0d40c3d05200d800150525030924441d0710040c01000d0024480d4210030141c00380083c000c2003090b602102d4a070700c90392001d8102601e0740c01440070040254400580a1440d560900001c40803818040443c41d075803640d40c004681d2070340303c4e5045102e007036001002c00c0100595440d09009084021401a40080c0071070f81760b58898907a40b103454542d0140d040c0700381c00c050b03140500c90000707000c07403200c030341251219111561803130745803000e00080c1c2c0c090000103002004c00b000102d01d5030130200f54244a802e491041c0b2400c0c114403000d000204d1001c1030401c0a03850b03c039028450000e0381031030624000e01041c00200407007040444021140380d0904059441190507000155064a062044845103070b0b116040700201c442e105006801040310340410b038003851804580401c104507180810000040c6440200d003000c1c0745d0344c011152680020b02c800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 412325215 1250 412323965 412323979
    0x180201050f160f050c09071b020a2121090302130612060b0906060901121535120403080708160b16050307090303050f130618060513050906 61
    0x10040000c1aa0742c200e624499480303401100d49034180300789007801501c3c200d4420360702c1e50107002485802510b051094080c004000480240c1d500008400c1145a40011800e543e034654240002c201e03044451120f500c520707036805582d045e050311203201072132003500340000c110300801c140003524021803000d840c07043c085030209038540c0b20f21500004823145c010407140540c032014400c4107454038040c42035000708141c40d001c0c1011b401d9030000304400501d400f40c017100d640c4c0b0030700e54400b0b0020680c810094030700e00200000c41c0705890310950b500e041030b4914441407400013010704400302000c00c000302c95500c0b0360003090600b8103544076691503902444045030341d03040401004070100241031440300d580d40140e18403000c5142100b80003800040d950909800c200b000c1007042810340d04400d440040d65094501207440307850400702500d0910400421069070b04051400103811640443c1c000301159820208040e0141d44030003c0d2440e0044003954101540168010b1006090207007200d5030016006140ca = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 412326465 1250 412325215 412325227
    0xf190504020c0a120201110d020d0f020a0c030311120f10150804030e010e30100c09060503041a0903090d061a2d0d0b0f04020112180201050f 62
    0x103040380d01c004400d24068009165060900814411206a16010f800240800c01a0040302c201c00e11901d1190102d890307010540c0e009904c078560050410801600c402c40d03881c0490071010b803460340034902c210700007030501e4000300e6983c40150580d01c0e10010000c41c01130702d0b241d5841018624200038644c01c1921081c0c40005181000c0032864010b041c0310b500e07205483d00705401d000b030121070004501c5051100d201d103109450345907441c007218468424104c8295074020300b40b9448002012070385da03c5980c803aa444c40b400101050380400c0310300b03101d074880c41e100c5699820250f074503000c00ca50141c126003040380742c0741c0d40c40d144191301c60784000f454003600e01d080031880004440b2000f0f0322043d07460560351031400481c5200c103680b0580802c42100c2c2c0c0342004c0303036158409201d06904a1250301032006c021035030b5095205c1c903201c08034050340440040307494a00050250344254003128180e00088160904440c034038120f22402800b48075819100007640c1d010f40040d1500c0d4801000c043c3c0310f280070042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 412327715 1250 412326465 412326469
    0x3150b071e170d1b020102070c170111190201050610120507090e090d030b03030c03220e01030308060f010f020d0f02030c100615020609030a031503060203070c0b0907050f1905 77
    0x1004000350444000500900f41c0c031999240c0350004e003541c0c2c01e683c4104605008250318081c043c048a18106043ca084d64500d1551405480c0c3e500814000080200c1c04809400d201c0ba581c0043d480c030303a4001c007d940da8072001c002003146801e4402003c182510341901d19140140c20403503202da180d0412941042c1c3d01c408030f2031340400840d440446074000b4501054881e0340760040701d050725011402103080c40021202aa140d2060740c1e9607210ae5210301c40c43c1000000c6050040b0010403140198103425a5682405015000c2c21070304588500302c0340b88849844e600502191102040590080020009202042d10001c0701084c041055102c14001c2d205548400c11480030100d41a10002c5075043c03612450325416040c5020740c0e010340d08090200b02140200000340c0fa120341c0180f03408102d15100b4924a107030700c0e103541c10160405000000700324107150031078248000184204004c02c801d646082503071361207040c140203c1e039004210260092662809180b94811201c5005880300c04590b00c0b00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 412328965 1250 412327715 412327717
    0x12040f06140702032718090a0204090b0f0615250212010e150c0a080a02040308041d060d11011116080a020109090506030d0f050c06040303150b071e17 66
    0x24611005030b00014800e00c9494000c2074489501c042d52140320f003c540f282d00018846d01d150807607401c410b00d1072070003c0c041d12020003260081d0380d00648204030000312070600885044d01214a20070000900d40401c41904140c240000344d2494503403c50f0070321801c2c4055580c1110703003e0040505449080b40000035030380700340100e804c0440390000010030802c80f900040c1404004140d4030390502e91001004411070855044400002d41c1d4507082d111680c41e40c000c00c00074080c0f07400203050003a002c603000c55005c04401400d1030b00441001c00790070b2543c501c400c000071814902c20091058403002e10880300b0703501400300700c03a44074034450603107441c5c0740148520000c9140725031269046d03502c44060841596003009040d4094112100c0c240200d140503004255610700d0710421400700202c019948400b14414000c3d1440c481c0c90700309603401030800b82001006080203088510071260441030000c0d9006641d0111840c141d0b01951044140c05400c0c80c0354030f400d443c018256140319443d191840000f030104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 412330215 1250 412328965 412328971
    0x50c0a141614030303060d020102030d0e0c040609090f0b0709080a08041502030a0801151707031d010b0a032603010b071a04020303071403090d060212090312040f0614 73
    0x10004100d0140359012200501800d544840100040b4002c2e095a545000c070403079070f001400382c1c0d0300c0414030807900c0100c1c60352180440c000c0d0701510303142e44804022404a411800110100c03028001d15450306080000c036100464010800340d007040310b030380c006641d0500140e400007443c01c2804203143d40d8001c907410104038500071140c401c0c0024043c00082101c0407940c011400134402142080000d00c2c01800d440010b00404203070303201606480c14840e102d15141a0540c078074441c0c034501c81c04c20f00800b90107040c1c000a100d611309000c1c0c1105225007014131607011403143c02411607072598a5a00d03220b4203005403014940b088005240070348020348151006500910103441516500d0702d0398148010000c21008102c01c001050205000150303a0010a64038225000940084d0010f0382480042c5148901031401e078110b1401c1610600303011081d03002d4100100c0c6000c0101c2166603904a017626485000c01030543d00300801c0c08200440c4000c0c0d01c881c041840342e800000e000d48210314880b2036140032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 412331465 1250 412330215 412330253
    0x60a080108060703110703110a06020703020c03060702010507021f0b0a030b0a150614160b1518010b160302010f020714010b09160c231c050306010f050c0a 68
    0x2000401040c4000c128882d408886850200035011a0b01032008182c40707070800c05800c01614020703181200d4028018603a04a034040801c5560300540c0c44c0c040c3d2a06504c0881600c43d02903c00002da02c1c90042c000c4922400746540502069070a6000728210130a43c8090305203200e1307a6040105403511001c1005020310700680c14072042c2e01c0c100d420802030f560001d0016814100d03404081050540208021400100f0a000d03140c590f140a8280a0701d04244000508007400300780038020603c0358800c0c40c2c80d02d40070075254807030140804004403045c243c0a201e2104400303010440d8441080c0001c00d029216846840007080c4103032820340324030a91700b0003c029114070108428280b020a0240300300c101130b00d015681d000c1d4500d0500d000000104008407180c0500000740384920800c480d0b1f020007000b00c0b44280341d00402024810b0026034981780c4c0310820103401100d01c1400e0311030303000708140e03071127054141e48022032028500021203183d009080005480d10072190700f40001156004500910120703 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 412332715 1250 412331465 412331477
    0xf091221091416050108060616051509251401020708030c1b03150606090607150b031612240203070c030e0a0b030402090723030f071403070f02010b060a 67
    0x1c0095410301200200d500d54010f00c00d002084aa41c0180d1301561080e4104c442d2600c0702c4810b0f002c22a07030f4100b41d5006001d801400743d00b01443c041c008260380105444000c0700c250100b110081050444588050703a02080285010030000038011200c084458061050729001c0e0381d0382ca080e91454000312042c0300560807461040c801c90310809420008000c08500500c0f4124400360106146030024003414096840014030000e41d07107400c0d00b218103442d804001340a10f890800500c000a01030964030074402e0040c079000c0c0e61075000c25040746003a1909640e80400011190f41c4150181d40c544502901030350300f1100c82e440b80320b11440954460101c0d6200e00d4000c141520300100070303141170841944680c01c4000140000c0013008140c0c4c0d8000d90607200c242a5450390442609ca50a03401450244040c1c0040c0d4881c030100d02601a50048085400b002440e4580c17010507a100441381c00880500c2d5000d100140c5071521034080318107080f04038000001c220321a50045809a40105140008500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 412333965 1250 412332715 412332743
    0x506041113031101030507120903030605060a090e0a090b160e090f0405060f191107052509020f0304110406050303030126010513030507030e04140106030f09122109 72
    0x180d03540c02c3c0b01c0703030b01e00b40f030100200d2500382000740400400c0940100a640d0b900c002108040c080d40c4030a01401008010341e45901741d030038004050303081c58060304000380b03400c5001c0f81203004e0034060307029200d62100c101e0304260780f9204460301d00220f40c3c45050401c18556100c0b0420f4854400082c0035800c8501050807078541401e02c18900b80c0050704074410000301008200c44044515542c2201100803240840c05004903000d1004038015480081c20f42c0c014244071021020043e03242024885055080c80c0e030040d601c00c5030300101d000c0d4080c0040050010400580042d072700b0409001544001440001d4040d128800b05c0e146070003d801481110340800c1c41d541c0f01c101038482442d000000500280180c1c40d02e0f2005209628001200806108010602c02c0405019111409070841c1c00b8000704181d200f6034503030400c00c2d1401c1c8501004285058468a07008007280650014250440e01909084048141c203c903003a040d05801250b820079020340c0b0100c2481c9008042c05140202101c0071140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 412335215 1250 412333965 412333973
    0x150e0708010609050d030c1a01081204050a0603050606070507140415050f010f091215061d040b060105040302030f0a0309061701090f0b0d03020a171c050604111303 72
    0x4015050406124116004000b41e90780400a01c00303442d41903a071190400050328007955028555a00140703948648083d140101e403000b01d41c54122112030045510910400d9840411032041e402032582201c22004140038183c06030b008542c010034041c001c5407510005c0c0d120355044c030809802060700413810344a0386c503d0f40303081e0043c4482242d030382c400078170060314010000c2c0c1c120701c1d03101401c0e0611115084206c00c0900601b0004000d000b20902e2400e01a0700d40b622070075850450100300015443d00c080425110800681007034005081381007800c03241c50390f448000c0240300041206040203410000800181c4043c4115000320381e07094001c0c18628198a00074080212076000301003001105020703c7c3d00c081c201c0380a24110b03441980001200e107002c00d00e103409005109881d9030084161942ea00815500080d00070459010381e0781c03402195405c00e0780320041d2203011048008406030401019880502d41d0080750400c200400024080e400c4040803511904030f901c01c520388881112081080c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 412336465 1250 412335215 412335239
    0x40609020406140a0306110c0d0f08070801052202090a090204050901240309050a080412030f03060803090108150a0b1c02120f040f020a0f090612080306012115 70
    0x1500b0f405080b83c1040f1504030105400861030720000d04495218900001c10300c82110403101411a02000e442020000c940003a14001c3e4109500d40000c1c602c1c00041c0f0031030710a00d442c5041e55002044540c158040420214920038808002407c1e0390f420400d01500784c1d240c400c48070003042e03580c1016860301d242038200300300b00e00140d2104403940820011445000141c219018451109060006010966040ca00c0c50020b10f908020b1045130300140120b03026003c01d1410504a2299170b0702c62160205c400308034161000343c030408000303600030f1103021030760343c003800c02d2035070020103082400009500c1c0000207800102031341c06030254a20000300100d0b10030794003040d1010b40c8043c074815031815621544000f20800d0041c9000f919810344004242081040c0c1c001c841580d8005050b6000c054640c2c0d00c00b4640300042c80b8100c0081d1030500d0010704000e603c1c40d1021030a0300400c0f400d085903111001580c0c0500a410705610000009200b85424a001e10a070307555046860034400c0400d04200030790140d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 412337715 1250 412336465 412336469
    0x1111b0c0405070e21030d0203060916050301090207081e0c190c051003020909070f0917030711190b0a080c1603032301080d0e01050f04050d020d050105040609020406 73
    0x550070030b070802c2041500003240752240c0e00f082c0c54032840100c842038100803501c81e002c03004413240070001d00400000c0b800d4000c1d5001e050201d80e00521500c0303408038010803030399208040020823030600042007281100e60180c50400d0107070903820b28001d071004180700441045000c0d1500e01c0d0020400c4800c0d10400c0050960000c00c46507402c00510f00c0c1d8031198054160740c441e140c131a40c90807e04005081c86a0146e03041004050481c503402d0038002e0b03014200c8c41441180c100003400754100040e90980841304103107441e8948002d035161078807a442e5a035071040c4110119800440c95000040d100c00d425990308000d19925198a071100c0103814000d0064401404082e10034809200b040c1980f4a010f001110407070f850306000903482c9004030620303c00e901007859980354406e14000010b60b0840882c005103014115620107040400e10b000546982c0690988121140c03006d0000380868107000c050200300500041040310410130781d030703070329800d560040b0390403100c26407a010f0100450400d0300440c40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 412338965 1250 412337715 412337719
    0x3090304030606081c180513020c031b0c0a0308030408090406050307030f06050f070e01120f020705060a0e0303070923040e0f062206090609080c060117032a01111b0c 73
    0x1001c44602d80c000182181740c0c0582823103200c0030f9905004c0c409066040342d01c06e040402c1582c0c0c072b40540084d44580b00c03a50b50941c2c80b00d40a04141300e400c0e441c120b498642520ba00814041c21a04d90347c841155541103041d505810568804012400d958204000e6000b103220b81010140f03d12341707213014401c0c0c502c007504110000d100c4206000200c4d4000404a107180001c0c60042e007803034068103100c03018040101c1c03092005440007800c403003400000b20350940f2602e6410424090160340f0301c96282d803440101d0750340c000940301c181c3c1070007047c000d0100e10b0022070000c1c44414140d4a075038001411200000254103455020f041c6c9150010307006e00105600840c0d541056030b80036492105846030303440c042d10062050342d41d0b003050b00c1008a994400040103800c042c00b6619412145441603545d4401e006210025180d10307550f8580840000403140040360002c140c004044007280b00c80e0700d1900c9440228820354071456141c11801a203005070007044580c0702d80006030a0a80c40050511b846031709014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 412340215 1250 412338965 412338977
    0x191203050c09090406060504050a06030212061003291311010c3207060503061e0a090c11010f0501150305090303150303070f060603020f031b010503090304030606081c 73
    0x320700540058180c9080d1001501ca041c041c3e07442d440c148001341000d401c07441d4081d1600051004400c03042d4072040c01d9030b10a8401d440c1d4414143d502680d02d81040751500c054064030203003880051981c108000703400178480e051000c81c1c040f40006a455800840342400d88201800018080c000f4041140d01688000c2c20555203c5102e51a40c00e402c018101c1002801c20f4130f440460002124094200d40740c03a00141540c08440e00d0303c0300102103034400e84d40a489000c0c10311800040b5515031112202550005111180e040d1402d0140703000b0305000a849020f102501c1c045150240c001e00070803001d59160b0710005199070600502c40e4440c1d40c1c0c180d14008062402003001983d0304000101d0340c00c40070b030140044111180c0c1000038918498000700402c885134113000e4004001507504540152413003261498081410041816980d1081e0851b000000d51003080102d46035006a00464005452030f00340c3e46130035203e440766416150f069012200383da21041c400d8003801d6000840300b60060441c5844 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 412341465 1250 412340215 412340221
    0xc0f030b0402101e1107050a0e0108010b0a06020c040c031823120306190302060417010f02071509020105040504090804030b130525151d0402040609060c08090319120305 74
    0x4c04482c504500c0d41c1401d100c0b64004912440c0c00402074000100001000300c1d0000783c540e114030022a50a11a201d51036080c8140211649032002000d026590240c1c01030611040b004108009880318110040c00d141c0d840311820749894003002e05018541c01209200001c0044011050b042c4001d030f0031460b5950040850420b049041c0002c80390040c1703046550044120b440d2440c800003246a50000b58099400100001e44401e5602100d40a1201d50700810042c040151740100381e22444000070030352441c5100045000c0e0159014010301e6006140103420280c544003c6000c03141900025100240007140810400203840762403680841040c5400e107a0800642d101551540712001c03110b800c41f019454500440c1c4c80e032208200034902d0b0703803c2219100e0244000340002c0c80c1308083c11080300c84006e141816042c940201d5046400e00d9545810240c5000c81c100c800d0b010061041b0703100070003000307407034a1540e0030444a0903040640c40c0103070030503247c0e2030082124000314046009041c140410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 412342715 1250 412341465 412341497
    0x405181011161104020304120246150614040b030a080c0a0b1e0a05011a0f0f040617090c0a030807020118031110020102090306060d0c0f030b040210 65
    0x64074202c0c0d40320282e40340400d0072441d00d03800200b000782c190783d0050310120403c002d014042100c640c40c80c400c1d80070741e0185000181c000302048a20440005030710809044c3d580320b25001550702c8074110b0820040c504003540d43c0d81d803032a005c0001030400c0001e51511414403d05a900b035140a2044007280c0030045a2044404261900c0c103400000d02050720124801d40da9402c00d0080710405940311010001d00d02d800b800f2100d4600000d0381c56041d001030354000407006000c0d4410903060350281402d45403002c010010781c00346540410401800e24170306100c198007800507071000e480649819154101c071200301c1102c3c41404840100315080355807101680300b6050b140d0640303840580340c022600a0b0b441d8403900060f80c0102c0081d00e0290525001f201c0002403005030415084406022a0406078016200904a00381c0c0a03c443c1254550080300206640303103400311813038070b246102c1d60100b2100e1f0f580d0040c5100c28401c0b9801580d9418801d420171086261808000801e180c003070800e00580138414003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 412343965 1250 412342715 412342717
    0x6010807030f05160e0f0a0504030905091005060315030c0a0b090d1a090d021b01080c0c0115090b03101a01120204120809030c04090f06020a0e0405181011 68
    0x30010b440300c0c1103103840301c0900905010841803c54242e80c2d0310942c503550201d00c0305002c0102c42c42031043c16550082030880b03159014140c012501580d514140c03604020030800300e0700000d010400c00c4c2c03580d01d030700003010380303482d000b40d80301e4a180c1d8011070b803c4020200303150420202030302c890f103c0c1e00928010b2002e80c41560988840c424280c400e00c02d024140e191651040d02e0601e2a805d03019848000c0080c078070800102c4d202034000c5503080c0d07080c0140c01484c0c10800001d4800303d50100f50408e0000f20b4003494a03010b0074007820070304000302c0e03412a8050001480704007500110400c503216802c82c4072508041003c44c044a00300c100800c10980c0042d1065003613405484264108240700091108045494060f0ba018203404620303180520703c1031800c202035030301154500c0e019016060044078640f61600c91114215000985695010040d646540c0254400c02c500e10912105803903100c40e90701c46204072845210800c65000826440c0491036241103104441a1100c6003054200b107240d000c508 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 412345215 1250 412343965 412343969
    0x20f1e0a080a03061805090c040b030d12021909030507080601030305160312020f070c0f051c15110318070b04050f010509031002030105150c0a03120e16080d0206010807 74
    0x1410941c0c58044015040f8003400d5164400d4070303141c00c2c400300070800c003046500c003d0050b50741d50100c4085008400910042d1540d10041c168142c210300c400004150280030780041c03100e0003050042c903044071507c1220948001680c0180090051072003842041410030084e400b80c0480320041c100c3e58910340e0014038500c80c0d002c1e1180703a0861452043c081500803410020718422a800540d20f50041c0f400c082a035800034103054600220b811000501041030405020a4800142c00300c6d4048125080310410b10066000440388071311a0114040142d0191007402500c600c0045000c0d07a0341003103001c5441c1704000c50005200c0e0380042c0c008200f880d080c0011141110810744035a103640d4440001070360507014084025415000e01e00b03201e40c400d0f001e5402141038403800c94074052040290750340ca490501801ca1140c0741544210034442c0828003481080000307410008003c00c0e5110f190060504104200350204804150b00c4401d0005103018042c44001141501c01007085601d060704541d0744041c94 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 412346465 1250 412345215 412345223
    0xf07020114130f08120412020d0c06020102030601030b061c0921080621070501110703061119021603080721021b01030c1b0302031303120314040b150109050d03020f1e0a 74
    0xc040e44c5400c5480e49c0103072468042d0030030b541404807551100f01034040c4d4012214a40000e250000303d16041c03515000341c2e40b5003074840c610b101d427001c80c5080d0000140609101034070b03442c016201290304240c20f040c1880301c0f00300030795a040355400c2810078000b070068038440f50326500d00344400c060702500c400030b9400115502480e010860f040da04440a043c8000c07500050320144c10a1510304020000070018501c0e5280c032641052480d050582c220789038000d040800003140c500e100d0400100301480003404240f40501003c5803032101f040c0581980410004646000d81c120300c841e20340c08a005040408160000c3c28184190346e81c000c8001d0803960312540f007480c05c08e60101c0760380500d0710810685481c240502042c01e081c580360f04004614030f1640544400003428445507003800002918018082c035840201001c4139140c520042001d08101c0030628104200010001034a589181410b0540b50190b0054031810b041c03d142182441c04110f4114000c9660700002e52080400146c2110714a0b00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 412347715 1250 412346465 412346489
    0x1140f1603180305011406191e0f060305060a050405060f04020310030b0f18010204060903030c140610050906030f1f090b01030b0f060a05060f07020114130f081204 72
    0x2403880d0680d440780019a415281030b000020210400105500c04d01904c01c1803001c201c025980c5d8010841c041c88103103a0f000038801c3c04202000020303d0aa10038030140c801a0240d00c1c4503803120044418140c0aa0000001949604c24045a81011132104004d0041a00d003480185046000319010080d010b20842c012034ac000002501307036042030b9010b005594042c2d80b16141d801c1a10040010400036905940b0415070141c00e104801d005100b20760440b2140d41f10208510b103552001c2d1501c11491005640f0a1000d0405a0b00c07101c0501c0034510135001d101c1e0000e0020b080070306210840310001c0c411070281c0e00020669804420000310036506034424000c0003041e800c50140e403030240c11501c03030041c140b500000002c400c00c03c21184081c46040c44400865550342d4003c00c101503030368a44180368104104001c1c0c0c42041c004100102001801030601201d8a068803850103550740c044130082c100070203a10000c1c86450baaa00c110b01c014280c480050808040d8048500b1092242d4865030b0f071031201c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 412348965 1250 412347715 412347757
    0x8011809120f140403050616180315021209060109180b0f0c0706050103230a03081603020405130603030801051503130f050f0f06070f021b0d0212010b01140f 69
    0x446040c810948103141c0f00c0254a0303a40e80d2415a984960545451008800216030f0b585103600c140360780c003140000b081449150520390b490f00110034440c00108034015408210588005050500c213078012044040204901e40c0b42c0444078040b41d50007082004481c2c04c0728200d901042e40d80c1003072600509a03001e4581c590300c810301840703901e2180103401440e60b41080000010300109030441c00c0900c001c1868800580a406082902c070160b2050090100c0c103041d0210703061140c0c0300d03400d43c0c2e01081c1d400d0041c81d00ea10340300000d40b907155101503800c0858445005004042c2c1c031414031801008103441c40000100322030a034030050b010040c14110204000c03030303d04003408500b100034060b194002c4141c4200e00c484000c0030340c9880020b0820b84a030300c48d500c00714404c0c4d0f1064080361080325455002d00200f1030b1414071045031a09058411b17038020010444000036a032a15100341c20f101b044000043c00c15201000900040c003c45110f04d01d0703050030701080c055240300b1011a403c1382084040d00b40808 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 412350215 1250 412348965 412348967
    0xf07050a0e0c032a030f0615030403030905071a0903010c080f0c0d091a16051c180506131a04021807180f0e0109050403050a0c0c08010203040308011809120f 69
    0x4580521002010013030901c18001404800f402180107101c4590f500038180d503910284101c244048180210781c2a04000140210380b007640040f41e01072081e000c0e2908a43d41c1c1421800300600a0750a060691000903481981c1c0b40920a00340006414100b840300c2d480c0440b10460460001400198951030024043d4080038135030b400350380000d40c0050341c8051180310046c0154121030859800c211100303030521101f03c0c2ca01a03c01d54178040c545a8200303151400001440001d817030403254034a88001e03006545400a001072000d24421307021491142c40f46074150070008000e20400484424989a82e03040c00051388841140020300c0301602001401620b40100448910300c44420002941d90094001f1418800c0c00000300110740e9070301c10100031079803218048403c5a002b030f0b0b0002d003c10410001400c02c0ca00846030542c00074052401015820395402455080ea4006c5508400144000300107200c09400001d01441d000d105d6901089001019982c5401041d92642070400b0300c41d204030b0502801b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 412351465 1250 412350215 412350241
    0x62e0507050303070c14010902060315040209100201020a0f140301060f0e09010305070510022d190609140f070603050a020c01110c010506090f010603020304060906020c0f07050a0e0c03 81
    0x1075070180480c1d5680c44c0c8448003c2c80f440c82c0007011200c5843c0c1b2210580c080405000c5e015126800400640c6180c90b81e452499240e1480c00c10190000c3c0c0a00c00d0307251a0356901c400303c601c08155000960b842140c410014440c00d20303416140d003030081c0d0200c0e505a030600c81c800d40e810b55240c1c0c1010841e42404980a9400300c012055551340107560701c0011041190119000f011500180d4094181c0c40181328280d8445503120070a891340001800040010305003003900d8141d080c012402e4403002080c0342d01c804d40044107000250713041b503200d600f810b04018002045ca1060303030080380581143e01c96159101d8403a095441403204244d201c9000c903400c188594125104c3c045400002c10800c010307294111480c1d0040c48850b00039520b400c1c001900e500b403d03d01148291a03044048040c3e030b00700501030b80290005442940c04a5440c00c1140000d00c01d40b00800c0590f903e80018018104c500307640030715207a9503030031440c000c1d4410901041980c00d04840c00307402c0850403001644030b9407913400c030300701c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 412352715 1250 412351465 412351477
    0x20402130e04050c041506081f0503070b070b0f0c180f060a0801080d0239040203040f0b07030e15091005010b03070f05040506071506081014062e05 65
    0x501500c40042c0020080d00040008004400350703004d1088180c0d282d8a55800e55485c801c010120740c00ca800181c0201145030080c0305244200d481c44101a282c0000c41c6c03800c200e03071b00502c01c20307c800240c4405128107054000c5d88103d0695401016180c40183c0030851700407060411021624a850740a944c1d0315a00c1040c001000640803a40781e5501520007484000c0030b2003440301500509002c00502d910104401240b56070307282e12002450025240034001681d090b03038009442a00c070360441c004d40e4880c00194003590041040188007801410079a060f100d020380707010141850301c0c43c40446020041005603c19500c21f00000b51030f0388005070242415001c2241c41851407403c800406c400442002035030050400e03550b10b003d8424004020344182c8142d0140300e600610a1042c040015889840139925100744c076001b256039565107881c50301e0300d0b044a143d600000d4407505910010540c0c3da68455000c030045541086800d82421403c1c40703e220922030b21040c0034412042140760703001d0421510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 412353965 1250 412352715 412352729
    0xf050105030a1d0c09090d08060d050102041211010e010c0c05120f01050c0426030d1806090302010f150f05040c2a031e02120a180902071b1202040213 66
    0x20500d810540f51510344100c4080e00e403166920001150b584030000403e106040c6072503c55a0542d1695030070001000401001160503640170000494820401072008039502c2c8120741d900c01480500c0c00141642010000c05070400c01201c0000021803210100f4104403002034554400c101e00d00b080761801c1152140e081d81c210341c2040305000c4184c0c15500100100c41d40e84d080d05103403c2d00c44000b154000305d01c4a407062540e01c24021103e0072011640091984c0e00c94000e03441001d12155120801d45e030b2081400e0700580d40d9045811818510390249010041039800b0007110941030070398075405400035004032030240390f541d028980d116010f421090004a4818134001032102c0c1c92996020030b0780c0300780049001600b61038140140074000030340031820310010380180140c071000100300c00c8950020000c0004103c541808448980c0d03814001c0c0010f044140009031741c0709041d00b070425909418020002c4020044072040001e1910304010749102c55049a001d82d6031120007001030a82105900154 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 412355215 1250 412353965 412354001
    0xd1b02090c0304260324090f100807120602030604021213030f031b030e190506090d020a030807120b0a090b04141003020d05100e030c0c0a0f050105030a 67
    0x2000d00c0301c10030040d5100301e100b940c0e20b04e40707030001507210b03241c140074050b658820440034000300b00410300071049032250801c0309000b004055445000500d86000c01c2c1c1d103d1811030349a409000f101100340300301c90050b04101009200e25840d1003240e1151143d1040060019035001c004604141e8403034044403420b50010003004401d050210417895503800000742103000c100801c04c11540140203024911442403140700051400346840c07402c1e00a03010707228800145008041504000031107040e14800c0c031034007840042c041450101d0b051840c1690134130804041d5400030030140700080d48801a81e44c003005510f0160441380702d09540c81c3c05411003240302d5502c08506d450221b00c0c088594050620341c6001c42d8180300d42e481a25810005a07020742d6510455410034000b4805130800200d17440005100f9422641000c110740d501000303d40c0d103120011000c1e080080d00760481002042098028a01298a900002d00c0c1980030098202c0701d01c04c650621002000150f00c06050750720814001000142017 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 412356465 1250 412355215 412355221
    0xf040f03030216120c03110f150a021615180819060c0305010311041808160317091903020a050d05040501120204080316050f01060b0406090602010e0d1b0209 69
    0x42c1d103c041d80c00c1c101d90b402c4a00f6000240b00844580303c5054180c01990341148941162210200302c1140020389401416018074030040d80c481c00700c250880a1010540380d2500c20104d00242010142d242c0c210019166001c1805203210411780a500c000c82c81c10214041c8000e041d8112442181d9440b1801c2c2e401100300703842c0200f000307500032a01d242c81007004106d030f03440c4070b441641102c0c1e081c08058a00e240225198160342016442854045081e0f40d642242c2401e40d41c400380c1f140d01194001c0f021482e0b0b044900201900440076032008000c03403600102a1070705001103030b510700b01c070300303501e45405c445191302020b05000b031010742c0170250401c06443c0702c20704101c3c01620960140c4079141c006030204801c02040300661090360181c62406010310b1400b94514040300c40d6000c00b07001910300e40942e5055038052042403084070001c11980000319140c40ca402c5010780300401c190b100b4425a414158501000000440c141f402505d10741055420700e0080700c844000d0034044400250008d13085824 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 412357715 1250 412356465 412356467
    0x30c0d020a12030203180319030f0c2a0e07050304030e0d0219170114161e0903050d050a0e092703070204110f1804180f0308010501020d050f0f040f0303 67
    0x1001d100c0c083e400301b03150321008182071640c6d03884900b041e1302071400409103410010b0310550190850803031071319095400c2066901d8417500b0300c22549501407581c0c0307500921240c0841280365103004280c080d0200070a41b078800c0c406050391100400050802140000c1d0341150382c1e0700300a450b20a6005061550701001d0341880480382d40307460290288400c40c1142c2c0400a400c140908120004120306002464403026000711f40800c80e000c2850038404808002000355116011070031941c00c05a8501107000d140d4102941041385820150042040c101f0040310300c1600302100c15040070301515400103d40e01c0006042c03a074207080e40711522a02c0d40b044400e01501c2c3c00805048420f008460410022520310342e02d40310f5100e25004503400c10418000080c0321803142c030b480402580003500103e070b600c150610507142c50040381c0c0c0450305620140c6050080c10b0b0b20440c000e015140a000519140c0410341c03025000b0301070506081c0100200144801220000c142960014104001410003003501d81c68 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 412358965 1250 412357715 412357717
    0x3021c0b090906010b1b01320c030f07080915070906080603150c0c0a0501050115170f270d0215150f12160303050301050f040209030c0d020a12030203 66
    0x1001620030502600030031460100890b45138102d52400206070300d0845c0f000013055403141c0340b04440741c3c155a100c190705903d8400380004d0b41c0000c04000c41901918581c1314000d09140090840303401c04c4c006000f00309800b180c06003030300c1c1c200f842420001c1c01696440403151400309402600c0c0c00d0700030024180f1803000d4005445400f0340311581c03030f00c90240d41d403041416603a4281d034040018100801022400241e5524010003201c0a144140d402e51021030312010300703644003a40860200588030441d21540399104265074520b507542d00e80c211150602c40154890700d2005450348003401414604500c0160b060058048450014801d4a034200e140c404c01940300e5140c1c0c40034048a0407204001034107041454160440360070000d22800701403001e00b0134070601c0c5c241e02400708550720803a480304496941c82403940c001907200340d856550360f60400741072240c0c02080b611801e01450060110300300c3e0340d4000c544c1f444800000d65001e00810140c0c000910354840030751056498040103000c04040c10b038040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 412360215 1250 412358965 412358981
    0xf12030d0e06070207090b06030f0414030a181202220f0e0d350711100b04060506160215070c08101d060601030e160b070506100317070303021c 63
    0x9000e8403a420703541d11000047d40d4002900c580e21840400000700104440c01c1d480b074203d401a446516223000220312140385900c001c5002011420021480c10100340c8c80c413090002c0e003400c1c0c411020300c164030307800300d41d041031612b0742c9070f1000c1c5070328410300031040441e40003130018401201c080c80f6010f00c0e941d4803a00c44200800305e40000c0d40e455040c0c4001320105c1c1d5150802908540c0d03444400b006480801c01d01d1001030200d8003085400c014074649000200000c559400061500084200909042001f12000d40c0e000c140141011711581c08903202040c05140342c5501642d07540309141c0540310b08030503403055000c01400c0d0080340401040800d030008016140c100740c400200140d41c0c3d04682c1203203080c0240801289a80054009002940f00781c100c50380d42c107514030482e18001c0e00c00615041000e10381c2c00c0340781100c00c08641c44041c0a41000126000403501c8030b41c00030581591101304410200701d81007260040d000a9000c1054803035412955512000030504200004c4000d600300904012 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 412361465 1250 412360215 412360217
    0x6030321010915030f0308150405091b22020f0f0f0d0b030a0b010302060a0c211202040e0106050a0e090a051f0e181e01020705070b090f12030d0e0607 66
    0x3001c00e941000820f1284038065a421050841c088151558110788201d0000c10816842d0020403549406803190f01800780030b0700b1404041c00103100e01001e903080c01014956181c1c460104012200042103108000c8001da902c140c20240e507ca036186104083c85c4158014140781800c005142e40102c9030344030140c81403180444051081400e0002007503078038103640340050440e2410800401c0145000001071403400c20a05141c690b920031500c0d83d01c1200740e0700402405c0300300300c0b04044250641c440340c0d0394000c00c654402141030500384003100c195501c050060b00b0a001b0005229071945010f0500350b00c1000c1c005242440c03038507064030000c0151000741c41d8008405410380000e000b80030450b00e000269024070f402403c2e59a45c2c41d1031200d8149140e41c82184030b01510082e5034000000541c0101100910b40025949030400c0c82c0c002d2400040364414410200b0900c0884055603960345181400c2c81c0c01c50360b54484910341c1c100c2034118480c040c692107000b490708031054600320020410502c21081 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 412362715 1250 412361465 412361471
    0xe3a1707020601170f0309060d090c0f14030303090606010e011206060c11030c03250b070f0507050a080a0f060f0507020c090a060b04030b0c070206130806070f020a0605060303210109 80
    0x40740b801c10794130106005400d0171038100f0b001b118550700b451000fa10060142d5400400c112105840e665241661600403946600400606201c101c1c404480c404d00b44070190001c41c5580303801d443d10354961801514181c100f1990903000f10721a80b0450500b04d20741c815140c20403481d035a4104c043d008540b05182161090030940c0b00b6809841c0104611104c010090301501100005680005007002011580400601c070a0f00c007081e44d0b0b040c000602480c920a0940c0740c0030412a00f09035190100e10b900c02131090300340710750910031054003164840c02c4650020407801c0480003441c1c0300c2c02130b0044020b55400f5502d45030800120950001d1400001c140686000440352211804881526910701610403074950801041000414541005600807040d08115003400305a50018039103920400e0303c400c1c984800c51090001003000e00c00d0540045c001e003090325561500d054082c0d1980040b01c2d0191405643d440011003944050003195a0030740122100c4054401c00f11001d440403400b0f004e201c8003245 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 412363965 1250 412362715 412362749
    0x9021e01080109020414040b010201180302060f0901050103030203070305030919081c020c1905010e060c030f070c0f0219170114010f0605070f080d09060e3a1707020601 74
    0x5040c4c4200c3d07013078a6422019811021842d4180005030000d0510641159680c2c80c2d214401e4a107000314010329442036000c4d00b841d084c9011011444103010300340c0801c41e4076101c01000000e80010482d4007095140c144540c90346d4510400500b0200281c254410104001012008001a01d4000c0001c806407201c50401c60a0484038503040b80218410b100c07807548100203c4404103180901c21610a10440011500b000003256260030801d040c0c0301c10304400c50102c10300050212681c4d94071780c840600e02d000310070b040040d00e96400c00c40700e480d000790003000c0c186128a0010480440d440282c2500e4818040801c0b0f000700703c0c0e0003840c922680304040000200086501103540402d5021a20300d0350b220780c203140b55601c81c9440e1141d44001264070b400300b0025162180360314010a4065401444001000103c658699052802007144061070f052031031300e070a07407080ca16900c0385400b240424013109401c202600a40310b00b0400c1c0c0a008140303149200b00052903034001180e505880c041c0000c084c1c450 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 412365215 1250 412363965 412363979
    0x8070e15100906110c0a290d060f080105191a0306070210182303120903040306050105060a140f0702030f0f0705190311130f06030302060c040e150409021e010801 71
    0x400c032003000c0e9020705500030810000e101d1800c2180c00039900384103804844043ca80c401f0382640188040c0200e07a440703030010400d08007560030ba01c0040c2076800081c81036252103030b0031001b6082d020300c4900040e0350343c40c625058865001c011451500c809421200c582c1031413000696141031088501110380c1c10700440c5021881b01031461a141e6501204bc0c0a070000300302d000162103546540c0b840824881841404a00042c0844a900404041c0095540c450039801d10b581915130580209008050412514680702c1d03000000100442c60b04560319103034514525140040d210f20b0030060b50511503001d03100144400420314001d103240980855203502d60315403c0c84511103500d400305c507081c68490410004295104400c81014100408406214513805801021104c03012500d010f55030342c1c0c00301071080580400c070941e004900200c0c0c0c00c1c1414900f0a0098080380700800d1141950b14030707a1000415203590b01301c945902e600600c100c211140c813a442c0402c1c0c1c101c610b070190005040c140006401c0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 412366465 1250 412365215 412365223
    0x50a0315050405030c0613290402040902010905150306040507090303020d2718060b0f070f05030d0234021f11010204090b031608070e1510090611 64
    0x4039402650a1000200305510304000c1200400030f50300d82c0001c0010303404401c010b10260388030b482841c110001d8424281000200c0d6490003401030400742c10441400d0304c0c3c5003590242c0780d1040e4101d4010820403800c0c0300494000d1000d40c4241d401c00b0801c200342c4804446100a0341c0301d098191010850f6a40e060b501712500d402510000e030258010030a0411454402c20003400d1542c003900305031090100c150108854440756900c56290041c1c4408066410002030042c00b00a00c0b81504040c10b00140010001d0346200d282002488070750401c148034200720b001e0040d6800f00c5440c400031901c8040c031514140b00700d09002240c0d926180403100b0081d0015161101185413500540441040c80c0128048440d4240b0001d0203000d0080e0443d0113842c404003400100f000c0d0138032001c0444e907500f085044c1841c143c4820540400f00e03900c46018000c1c0072002408408556241c070b11042992601c9480e41c248064842d800e9402044070240d00c0c407081e820a4025040707401c99030300d00c13008150344002c403615 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 412367715 1250 412366465 412366469
    0x907111603031205040c03031116090209010f030b100f12150602070e01031509080702090c04050a121208101502070f06110d050a14041203080603030a0e0904060f0e0610050a 76
    0x20414026001f8000310744541e81a103125400784088500c021004514800c49080d154092105a50001382504855134400022101070140b070405001000c51200002c00030031821010070100201c40800c0d40741030388543c8060900301e10304082009580c131160b121304031121803405000094824070303000148034010041900e040300d8010300c4a11841d403940c4140d5000d082001000d031030340c0300d003400307444056036031410320301d010310b038004912030360f071403a0405100c0d418000da405100c4e6036200901c004003081da029000c030802141458801125078403d000d010404442c0e41080d80a4280c1640303140c0d05a80010341e49007a078644466505440e0b070340e075a04440580f81e1b24510005500481411040940104003620003001ea07410440b0385401000200c040c0b94009501c00540003d002c841c000615401812690f041081a0301842c9001d05488000d0b049900c1c4200e40380c000c03050080058103000c40c44d40201c20180b040c14081c4140c0440c0d05900c2d82c0c1e0032064031a1500041c0c40b16000440d4a80700701c1c0801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 412368965 1250 412367715 412367723
    0x51215091c1b12032304021002011109040504032a030212040506120a0b0d0b0406060e040b01270e010b09010906140402030c0408010c2006010608010302090711160303120504 76
    0x1030b900003950303480d1030010000400b105041d02ca641030049910303020031510a201381028210a50b152500401c0300701c1000c50f4201e425645001d0704040e01000c21801c540882500350f90203d06074550f0b01d01151008200c080040010b60280462942180b44040350483d40d4004e900b100c1d180c0440648843e10b5208030300c580c582c0800700300142e60000504444a41d8000e00c00c0000240090ba07500c007040c151840000b08903554500d000820040010911901c0d0181000007100c0a99242640d00d2108840040c0500203104000c0441c43e1503800003246148420b0008031818003d0904040b4504d01910400c04401d07c42d513507890000c82d200a580c40b13400100c0f07031200a504152400e141c1440003e5001826a07068843d08000c04114680c09008160082c0010b50701d80070041841026a1840b41041e030316420345412100040240c02e9100800505507501120200001d1b110944252503002200000342040d0080b03259540c500d00d00503001c8d00440340a91540c243c0c61210700304080490300c0c1241c00078 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 412370215 1250 412368965 412369007
    0x30e0a060c02220e0c0301110304031b0606091112060906010503160e060c0304050a090506030a020f03010b0406060906020705030105090d0c0c090504050a020127051215091c 76
    0x120143ca081000d40c80310900030800a503012003040e0981042e65054003044038a98000b001c8014541800d100d40e50000401d94401411810995002083d85c0c5000180e28207141c0340312010ba0a01007241e00c000028000880100b04050402c01c060712141c005e1101d546020400d00300045403401c213855000e20850b01651042e203195500c080c0804030085c080a1241001041d41e003510803602c441c0000c0001c4d561400046844a01e45010056043d940360040040c441c2410240309058800040840d0784139030403a0704080b501902c10100380101203c036882c0364403c0c1088800514541c0108a0714113440c501c0d42174461a640329803c1c982a00c4045d1502c04686c1d000c0243c05121602c5020710ba401c00e03100c1e442040310250758201c94000d582d420b64081c1c070150082d07058101150f80181c4040b01d0a02090040c401191500001d1002c0da203551080500074040760704211200700080c4090255040b650301911150304111780302035a513000280b941c0d40000042201c20403040d00800504549490f101d00803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 412371465 1250 412370215 412370237
    0xc05040c08091002031503100501031e0317060f0405130201020f1b1903141f060302061219020703171e22080c0d1d030d0e030a02040203090307030e0a06 67
    0x720f8020344c802403400640f8400c1c06080390241d902440410b080583c81d003400303d01d55045062040e5002c1022010100303080600340c071100007075004840b08010340e00300f003408859565400040760171240c045030415405803803c010001c1c87d62840104c00c000310300030f170300f110f01c0414240d804a80c0c4030000c4001000313200516000c016a480c1c210b61428141e0207559051030169540d5035800030001d11541e6074030098011954118030340c0c41c0d440c2416500b1a180740203000300d51071600899801c0c0b043ca03d03240c07001105103000944280202c2140e64000456000442da903d14078200280460504402d1031101c0c03401d00d0204080200e0f580d03403020000210752040d08517445490100380c120020101e904884602d107008080032901103400f50100d0104100a8103d071490208024001c110b482184a0402c01da806d00079103a4034000751140401d400381c181050380107942400a4039080380740d0002503100c1c0c000030030010600808401340284a20944911341c2c0d40c0c00c12420444000315a00a00000892032036075 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 412372715 1250 412371465 412371493
    0x40506090f06040b03040f0b252709091703040b0c0706090501050a05090c01032708091504210515070c060504230105010f050d050313030c05040c0809 66
    0x460704151800404891409545003051003880c0c0045806541340200240428248007120800c654070034002c9968242c0d002c001d06080281e0344011481d04108003a0b110300712401d1082266110310401c07500c00c1d00040d2aa0fa26241c0081d020741c075811103844003100515003460701040140e90040c0d070b125a05400e1a0b895074100611a080b052080d03440316103400303110f0017040c8207224150040d01703d91404203a5207044400189404200c04006041524142001e40e2107015a400c1d6005034403240700c003002c40480c0342808242170041c527100b941d00095410000381c00c0c040c0c1c44003c10031a6407096103074080200700404050604049103001c0c1054012504c482c0312200030100307640d4000001e04140803080000c7d02c4035400c98030126800c031001b4a494800302c486440c8203d4503685060818020700c125810202e110748410f02501c036240c0201504212403003040411304c01d03951010f681c4900f103030001e0340c1c0341444da4825201d4401c1600503450605e070100446d02ca1814140b0640f015001014015400c0e18 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 412373965 1250 412372715 412372729
    0x6020d05031b0936060904030207051009080f0606010201060621050c0f0313150b010c12020a0b091f0612030e0a09240504090c1802160f0302100204050609 68
    0xb414a41c0824000204d03056007070303039000f410001071920a100e04d1034086640e0703070b181c2a04041c18140c85080390307000300030029a001910000f07a034015101c49143c0c0c0510101620000340640101c1980e00501030000b4484100142c41449814241c0c020301045a03a8001a1002e4242c1c4160b0208100303801d102001705c80c0c294003c20b4001d180504400d1400070203c61401c0c280e0030541e0b202c2c8036000c517000460306000d281c02041e81d0b996400403042029201e01c1c40040c14005403c074000340005010740040c0c1c5054000e0103008a1141c1150400f00c039460440c00386c0383c079582e00c140d1907501c19800103040d4030b40c10384501ca5202a2401d40000180c015540e403000e44a00c000c048110b58040d003610f00129415649010f4004000c00c16035010021210b46911003000005a070440c03400340c0d2609a490005c80e000402110450b14200166185a41c42881400280c490500c14400004040304001c04201019003650b64485c001c0e8280d50f828100d100c215010ba200ea44101b03540000107204503181807030601 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 412375215 1250 412373965 412373977
    0x200f1b010f0e0303040f14010201061707062d02060405060a02040311010827070314030903060c0a1101090b1f05060306040b13090b190501080307030f020a05120406020d05031b 77
    0x101101d0a00351b507124045407000700c58004520010440900e40242d5030240550805018000710043c0f8229420b66055035403800c0344115010003803408041282d00c01a100c4c80d44e015200350b4031051214000010103036031154152401ca807988100c038005081240c0302d20035102900d074007541c00d003400715054004403151480605024120748541d001000b08160307141e075a5103c281500050850540740d418045103103c403240800d140c80e08208410751495502080580e804800c82c06200e8445203000ba044444c0320107001a00019840c00450b0000c0c810080040c0307114428158106a520b41380f030794078443c018001d101d0307190050310906c0802c00e2840c2c513800000d002c000113032030090708620200c10041600c1302030b0016074070010400140443c490880008501d00800801d091095516020961796a40303c0c001014040050b8040300c2a1017a1080c040004016085412226841c03185420303001e05610910846d80503202d41068071542c0d0313000d07800f96842114403080c0e00000008940d0390300030a5001c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 412376465 1250 412375215 412375219
    0x60b0309121201053c011416020108130c140907030e21070c120c060507050309041e02030f0708090a020d2a060302040e07081302040c200f1b010f0e 65
    0x541c9070b01d4030150071203404100170b01a0004520342d2080c0d4100142100c0da0b84440705074400700400961410410207032858541030b42c286440e80071550341d1901100b940b02054001004607030b101a000130905010440a41d11103801c0b18520300c9920346002c15400c90301a00d41c0b014060304205951001d82a401c0804500300b01180c2040e032030501c10303030b0f00c0d0301c00d480503500b084a00682903455001031010040b40140500030609029280030344c2900c60035a42d00074020801d202e240c50740000800100702860508240380d11200c10b6450b81891003426105480c120740c024005102a000aa0452000280c401100d5009401e50746111a9511038441407814036018001d4150303065043c2c208c0308100f07039080d40100b01543c0c0050301c41e8148480748041050150220080100e46001c0c070811090440322420341139070460b0b00051481d1101c005607085178000a0900b45c4180001200c2403010011134010500c04010b0103030b0301003000315100e80409001284420740040c0c1c0940703820180a0050580d00085440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 412377715 1250 412376465 412376509
    0x5060d110423011a03091203090111030c0a08090102031b0708071a01081605220605061c11030403020a1e1b150e0310090201050904060b030912120105 66
    0x11142c0d40c20700c80002c03a0031000300034107100010000c0300311515600d038400314080784640ca1410a00d505543e81c2c009440c01c001900b000201140c2014800d5121500009000d042c140e141d240c143c80048190300442c40355008100d0300c0f000a030720310030184200d912426001c200c507250401c60030114a0b0542162900700d41000042000d00040b994500240040c0d28410b004640e681d030400651900b85004240308203d00742004000340056a03e001c8a280ea204c2c90300c4200b45014400443d170030240c019644480d82112000480c0340098401000111a1440c20402484407114001200c0b40c140300840300500160440440080043c80c030101c521500b4821000c50205a140d9803103401012442400005921000ca10708024003480c40f40c1641c8a040c803802e0001c2c820410300d010035152200c60318455410750b80c0f00340040844e809030003503940501019000300581929820018541c0d031050340ca41909100d00d083d0f400c1c8000300390044691a0b102840d51450691800701030101071030300000303000d4004007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 412378965 1250 412377715 412377731
    0xf020723090921070c03030f020a1a0a0e06010b03010608100f180c0206060a062a05010213050319060203060109090903020c0f0d030203032e06081905060d1104 70
    0x149548105005541a101414104100f81c2c0700b003907034041040d42401041020b02c41e4902180500c110181125010304204c00c2e5207090040882c1011002500103280c88030906003c2a00305c1d9142d0310602c540e440c0181000250003d0721042c0d80c4820910810755180f40410052007020710440f140e94000044c900324000c0c03962030f6501504010004d400030502100c6c007030516017401800b401004020000d60018190a003485008503400720070601400060003030030280f104001c903842000340700c10803007007541c400080100e01e00309020b54070580c126003030b1061000c804502440d004ca16150300030b402c107410004000c080ea40e40700184d00f000b040301c2d041c0800304500060740c3c9a00e0041d8410603110b0350207001080507a50030444582910b15001d03004280600724a000250001f04482e082540016142007640312040c5130128114480078030005100140e10000b202074002423058010b88202140c3ea50600758001d45008454080342d07071948c001090101540407803604000904008401b40c000714000f8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 412380215 1250 412378965 412378969
    0x1b010902060309030307140408031b0f0f030c0609161404090605010902090a09060602031c060b04080d090e0417070c0b03010b0a030f05150108280b100f020723 70
    0x1800840f5043c0a5410000c02c0058980d03000c2c500040e84045400042c3c00c00703051242c82a0b59000e001c11100e4845414440083d01090030052030080390100812a103550a00903200d684a03002105114030318401e410102e03500d0180821503c144024804500d20b03081e0dd0045140e4085c14240041c82d08031340c0d101c80c02c0012800382c0c0500fa0103084003020242c0d071122004284510b4a00a038480407130146001c07000d0207550750100444181c03900d00301514000e004a101034400401907944100c850b120000740c001030f003c40c040703030000306202940c0b03800600c9540c4501046c00c00f841260020410820041d21105100c500b40c0603084860003441100452074546070301c50b509600a800c03201e00031074041000400ba540c5401019207883e00c12605200500301160003104280040310918140880c0300b0025060700c504400300c03a00400b080301d11002c910760240f0040b004120310410a070155442c04150003c19002e44004d03a00201281c0c002d1000d5840d00f010700318a00b0540d14108240040c3d1489903000d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 412381465 1250 412380215 412380217
    0xc0303071e0f0827011d061305030327011a2403010e1b07060903110606031f0b040908040608100b09060a0507050a1b050a0b1b01090206 60
    0x1829a5403a8041ea451090240300c0000944070140400c1040e020040542160301034005a00513841d000a443c4402e03481a41407070703001d0200c0d0911050b40c42c04004031003504110b03096035110b4245030280c0c0c0050700d59070030400c9501060b06010f07105600c1007010940c4503451500e0300c0d892040782075402c07070078038207510301c123401d6402c984c075966003e400c00c080b14046031404c030525168000a200d0503902840c42080405194003052003000b0b541d1641c1b43c0001d200d2441044e040d602040907c400b10340e40c600b03a1800d1b00082550800a4000074131901000000300c0c00014614081d400003070003483c207189400400d00c11800510307018034a10344c071030f41e0720480c58450b409079080c80d40c805c04c419602c8500b428402490108001e000d8981010b103404208010044942120f01072541524101c4da01c1240b04000e0360303e440f600b0001030030751054800798024000803d51503505a001e13110402e0501d540c0d070041104a0700507000e01c040b8440d041100c2c2140380b4042041c031840545060000c03900301b410740c00054803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 412382715 1250 412381465 412381471
    0x706080601110607020d080c0a02070306020901111603061109010e040903140703210221041a0c031e06030714150a0504140a1202040b041d010c0e0306060f150c0303 72
    0x340c0e0006c041012015000007600c0d61200c20281560700304605108001c2da1201c4510000d042c66030300144111050344a201c2d40c08440c00d070a811202c07900c00c0024031400401c1035210a8a60310302d000c0429070306a44040031a1031010381691000f0620b004002000001d1021240071010710400c04016680e20603803101800d0914001c1e00c8160600011038101c44201031101c3c54565858410441c450300e521002c0740821100c0344681680742c15584620f0a8a45906a60300d80030302c0040c00002c11401499003030056114191400310000403034881310302c80ca100074080d24619455041b5400c14080f0b203070101013203d100900101708440d5400c030348038075280640c0180d6014001450000301409070a02400c0c549506840540c0c01000c0340b0310348084410f07040403841c2d000f807003191210b07180354050351103030003a070450b020b4811810f03408045904000d00801c0c4e0b09904071301081c1d030030103c000e9030301d0041907581c86011b001c3c01c12001c03800820704000071840140c11540030742c0f600340400703c1129010000307148 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 412383965 1250 412382715 412382717
    0x3060a0903030e06010b2b0204121104060b0d0e120c0105040203060c03011a0c0a1403041d010b07030c0201170106030519021e03060f15030f180706080601110607 71
    0x1010038040c20000d0944503a010310720450f501040c010405550340300111140090300c10a80d526001000c24540031400011180c941c0f068004640804c0042d191b8082104c85071041018841030a01d940522054410512441141030820701c195070101d82c176070308000c6ca02d04030340041e00c2c43d000c3c03d4a24401c0355003011801030b16a1b95207801b007000f1420300300300060b0401c2c103004540b401c5600d010308a90000c01401d1403009480300204844550780e0342003064080d420342c41a1a2510030000d65501c07a96030300284500214980000441070242e4122114241a034510043d5a0b01c2d04030591019904251042d204034100244822030700900c00c11130b040940a000183e5000c1028200031b00e4071104600102c400760380d0284104000302d900c0d0000f405112906401d55000ba0712aa102800100d28080f212140c58200c80070014403411269507000a600c1100c00c10100c0219031210102694424450f0308900110ba10403038051010500841c41d90340d1000e41494003907540107842400a003401001e40300700c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 412385215 1250 412383965 412383971
    0x1501020a060c11190c1d15010e060c0f0d0f0c0f02010e09010816141f090503070b120106090b0d0b061605010b031209010e090a060f08030c0f1b010e0f03060a 69
    0x140c104005d403aaa0001001e0b402040000310011410010304914081d1540e90820103c007107103106079024132400310390060020825502c46000ca8400390300d440050403101c0087c003134032001c5a805400f0364028141c8616603a0350a820110565072607040040160059060100c3c84040c500380f42d80e0302d00144d010742201d80c06000083c034a0180c0742c90407a0b5603041606a1070000444824586418a1503d803003400f8000241e22070156000a603074120442c0c02c12601801480c00c0821410802d01c003d0490741c0240074202c0c0503a0b03070f40501b1140c8903410700030303c034004030100100b07151162a5000400418801443c0c00d00d04a42c40100c00400707100201c00716266516051920201e20741800703184102d016003c001c030b203020f80e040002001d1010240190b48200003a0780440c0496649030701500c042c2840035a20303128162240c02e030603a60380080300c1000342440742e034010100c02100818108501200803520078200e441800041d140d03200c600c100d094000d120342c0b001c8040d42e581004a1801000410000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 412386465 1250 412385215 412385263
    0x131412030112060b010206011409100806070203070203160501080c1803030d0e011a0604060c030216030f0c060302070c09090305130b030615070b0109050c04030c030b0109051501020a060c11 83
    0x10030513650407030103190654200e00700400900e003401c290008040301c12260690160b450b0044081492215001480ca9102d0300b0104200c0903000001002d102d0f008404480c09c001510080d6001586280140c1d0300240c480004140c0501082018001c1c000c2081e0008002c0c1e002640440d01d95004000394802481d103d00550042101c20310a28048100080c50401e82d80d5880c000f066051003130b889444200800764080000745482405001c0e10384007801c604103040343d135030304102401a501c0342050f0364540d00110005405400392007240c21007a40300c8407821030145068805001031031803107c04e40c10300804010425940400c1c10441010340503c1341c031252641481c105014003800c001507030b0321a5280030030a5a007c611210314884c11110002c00200c1c8507541d42d0040820b81c003999100030925805440c0110410030b01300e590505a03800998108415590500040303038100e00c105115000d40c002c1234080300420200d4000901da00203a09100801e4090010503a10700440008404401c01c003070618 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 412387715 1250 412386465 412386473
    0x303080106030221130209010b0a090501051810090801020c06010e0a23070e1002060106080c1204021207150216060806060f0310050d0f0201030b0306131412030112 72
    0xa001d48160b00d01141001e01d0310340d50107070625803c2000c190b09003070000000c00e03002da4460303400d46480d4042c2501e08256036641c0070280c540c0080520b940856881c21003c1982d501c42c20503503980072115460b0120310034640b000c3c09020396045a6140800440d0380021070b10745800d0000340340780b1301030303070000d080721361400c00c0c01c20401001a0103040c4040c2001482d0094607000d0f0140a00c100000781480b480d9240c818003911541a8900e6458101c1e8900300024451500821a14101c074a1703612401e4099648992545007803041d00450440c074a411000b15015080c40f8404e03042c1560a11304440d5201d40310708041c4c08105d43d40d1403001c010b0703000ba00400c0c85010350b410030f0030040c01e0a04108156080080020b62180030b20829408050004000281c21b001d42c002d0f000c0c010130002c3c1c020340c21001541000c0c03024421105060f404070f401d01040c042d8905000404500c180302c01c20200c1010032a40d43c913300b10f2400502c0a200c03c0c4691030039040c14101c1c20008500130b282d0100b1403121913402d450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 412388965 1250 412387715 412387727
    0x3062e09020a0c33050604091b0807090b0a0603020703030905011503051207030801050112230a29011b060e030307021501050a0302270a0b03150c091002190c0303 71
    0x1e075500440741400c1e00300da002404c00d1941e00001180d140c01150f26500e9a02090041903050005000d00320b00385510b81841c0320318607a12042c1d654240554151a40f51160402602c4d03c0000f042e4004583c0c0e00100301441c4280e001d4841d1a00c03074030700851208e49a0b1070f81c9094031032000c0c440f520310341e002c001001044001c103c50340c118007607000f4490600e182c0d1784016107140c41c144201414032603500c410201036040c9902951080c00080c3c00e2400420f002c45542000300b40071206104250301d040000803202a100030071611440070300420000624803c4011903010701052640401604003a540c180060840e000f407010610400006644038079125100070310b003112080c0450324031082d807001880540c80701d5868000341d80d010388807898852100c0d6201c12149035170b054802500240c82d001d101c403400e220b0f00803ea080340210f044072070100d0b017410001070481040d500c582c1001000c11003807480f07044c43d01000145424600580d01c40c0d080810814050f83c0d00d05070200e408001c110b605000701900b1174 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 412390215 1250 412388965 412388993
    0x30a02090901171b0a0905070c080f0a0305060103091104020d0e0f100b18010b0f0c010c080702011104060c021c150c0813031704051608070e0603062e09020a0c 70
    0x56440001320741820085400510b4501070701081a031a54000358200f40181e01d840c4040f54020200d90b55031312681d240d107000360400b030001400242020003068840d84071b406800c0c000d03078110344020310881030881040025031020b080028425254001c181120b407041c070400c1902c10f10640540142007600c4003007002c0b905100c500612a0841c10b040701843e80c4002d400f24151554010810b5913201201080d44150207006c80307180135907007040b8184208662154842d80600220380080c840003550401c2134040b805603018000010390383d41e1200c005031030100c034a80c03120004c3d00100022202140c6851915004000554130416203030381d00c5100d00d40d44800220303480000c0b80a1202c0da04100d580003000c14103448140a070300c0240201081c1404810321800c06128110150464a69551035486450300c4140c4035542100c10307003d001495506011903042e200d5558454001c0201488580c81e05d000007490304c40881032511241e011403141d01510080004405ca52180c0c03000b401b05140588114802c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 412391465 1250 412390215 412390243
    0x30e1006210503030f070512151009060e150f130303080109052509050a06020703140c030d260403030e0f010e0c0132120c09060a05030a0209090117 65
    0x35011141c041100402566003000506019519076182c05004039401c0c0540c69111440e00c041c01c0c14494400c0041040910000d4182c0d00403101c02e140d07135015a44070405105240105e00e039504c070f0410501c0c02904000c1600c10b540401e50420840115001c030540011250443e941c0782c03a1030600038107030070010440c01014840b8003444685000c0304640560b003081d107038aa030040ba101c50400865401070720104080c0c507010f02011505175491030001c0da06ca15520050711042042018003400e2070b000701d00586e00c5d000150081143e4020910200e5281080c0d440d003542042d840300500d5862a448441640500d000b82c2d0081400900b0041207801c200d03118000200f03030380c5445000042c0b034401144088200c0000d0a040650003030481d486000d40a554240c5d40b01c51541002c103050326001100604220030031400d60040c107a440d1100220304d84109801691301032001d12440f01d08a2203540196440718001902604001aa07004140003403020703000300340c00800b00f484c0c0350700c0301c2402c000001040d091 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 412392715 1250 412391465 412391519
    0x190e060909030a0c0807060f09110f04140105061c11030709120b0402040b0d0206030406091e05032a0a050708011802010804020906180a050a150e0f07030e1006 70
    0x64883d02900c80141c40800a005000100d0980240540c0d03074825400c03952103a6040c07080030107616100c090412004481445410007580c0c03d5180e00303051144001c100344e070b500c0351001642448100310454100315581c004800103800c030400f40e283c26000e045001c5002885050301c03400c100d40e0140011000750040003504841c21018000f00315010312107504590151b03400150f25220f407021508944010f41c0c080e403c840c0020a10041090719440398807224003c06c00600d0800c035003084045c00b05040e00003d083c507842071001d50010690101d440fa4814100301b01d103200d0b00c0c0c00d894a80e0a003030044106907081d030041c64041080b10b000f0b0280e19521800b035103c21031401c10960020b0301407000031700007034000c0c1340000001e00b1940b070350040e000d50304e0078410105a4500d0059103e2000d0034048402502e15410039410028442034030f060041914031071001c4000980d103002c65184021002800038003095261800e441070031806010f0421506003070f01d40819454104424508007140c0400398403980e1030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 412393965 1250 412392715 412392727
    0x5100902100302030712090201091502060105090109090b15010c230d0513170c06040b030a1802090c0304030e0a0803040e010b0301062325060513051b190e06090903 72
    0x2d81b0000030344c1d80e2003007014002601c1e442c40c001242c1607405070b002a5400b0200e01c41101049800085203412183e0480d081e030f03800d0b030300c7c0c0788113505590100300300810300d08104021031b42d10008840d1580007000185491b40120302c0c66141c0e41401844403098040703581c5d481c4840c4280103000d00195100402c4c50a0a52500c000d00b140409030050500c598110b560000502810415041c800311134820801002d07580c480341c546c8070840d200c1e030095880400742440c0002c00d044030596001d910b5607854004110301950364681500561a40c0000c00850400008800c0d01c100b0303981e9041c070140038004d00c90045448509105400fa05e0000681040f4090f1000303200401c2003aa0040c3d405281403804401103c03810341588030036405000705030800f0001c1a205002219841140950041d410300591060107941c448503100c40101074101c2010700623800408a021044410800044d00f85801800010002c582e41d040411000c00f103410034010585001d06001a5250112a25410a20312400b03149404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 412395215 1250 412393965 412393967
    0x2205070207080c060d0f050a150f06090501080414010504050309040b031c0f05040e090d0806060304020d0809130e0604050d180306201902010c090803040e0a09051009021003020307 79
    0x18030050340d86403040764009280c45d8100e000390443c00482c420340a00340b00905010412501501e000c0b0345107007407a00c4210002680c45004030210003221503d454440d07404c3d0400d001111a101c2c0100180d17109460040a8510801c0902c070b01480355004201540e1a6483d4000704003e44424502c114424ac1c0500d8420390010bc0100107803000e1300c014108045009036200c3c095a5a0066511142482020a0030030440000110b034090280c500d5275a0000150b44072820491140400d075006500706891000040c0060315040060940d10380017019411148005040340d0709503602e035540500c4030317007001e0b040c442001005c1010400c0007c40f811f140ba2400f00d1211070f012852000d220103050b164850912038049001c0f01440d480c1070b42e1800301c2580c0c0c2c070900303d0400c3c582105081654015840c0043e4aa44684541d074001c0c19180748030081c2d80b803d45030044c080000e4801400c45001c40d03550301d07103030f00002d10200100038545204160118041e246801003100000b0500284400e16004000f040101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 412396465 1250 412395215 412395223
    0x90b040320030f0d08070201150b03131b06030b0a080f12090a0f03030203071a090a0f021c051b011404060f0207080303070908060114030c01050304060b220507020708 73
    0x5007002001d502400002400003460b044101ea00070926000c4c07100c54240590b84613134014824000c50300244240d1504018008049140c0d00c2010014001403021407000700152a80506903070140c100c4916034031401d4912959014642d1201c40031990310015016542403045d480c00040100102500c521024140b00688829036518200540000010700c41003995034908203202400c2258451030b0140d80300d00c0c02072742d281d20081e0180c2d4108061002c0025610a03179030307500d101c2c0080801401440c64159180449004c1142d02203034440e80d0b160500f032031417182e1510064140d014400906018440406102d1820308003030700b050401c03a40301c0718118041500411102100c10305d140400d029080f18000300e05280f610b030440c4000c1d020000c1031141c01640718620005954404042c1d4000d41d07620440702404003c100d00b5149c250f044840000b00e00e6001e040030310762090090f00045180c15100c00040c50210305079109214040c2d5050100002c13900900c151030303205155000402400f4202180300d951 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 412397715 1250 412396465 412396493
    0xf0908041a0f1c0b04150b0c19030f110a020d08030402120a06050a060e090a030e151603080f0405070308030a1107110909030a0801120606081c090b0403 67
    0x561440400007500488141216603a004030400300b9150350602c5003610b90070084560140d4000e042080b0440b03685441e101e86095400c2d24001046441e16149403200c25420801d040d500c54000c802044ca0100101100c1f040b045209544601246a40000140012025550b905140c0d80f003840c8600060b19140300412007507070808509503c1c1da603144002142c282600050041500032030301d141e0204141500250300031a85440b00388403080e107420103c281da070000c036020111030340400a01c001003030190031050001e2001a112910741c0420b81c1d041c20890780041c615250090751181c138101071691000c060341d0000d80103541d01d5603d05040e2204d6584803000e0202401c4404004003213452401d05500011a05046050b0982c980c1c5040c203241c1a511b0591711454010300111002a0840202008a546a10305600c0b03c80069090262039102021486411184a90b446202142d585801c000085a1444030949580da450800500810711010b9602c180710b0a44203000c10310000302c2225080013 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 412398965 1250 412397715 412397729
    0xf01060f0c020d05012405030a020f041a1c050111040b1b031b0a1112030d0908270a0b0f090f0a15020303011406091806120105090c01030f090804 64
    0x120107840e8000036582e5a501c960003000f80d803030031500d10302e41c60310829803541c40254000d214883e255508180f68640303600b003400a40c000d007900c104d8541d80c41c5c00c0d4001020340061595400e422a0003001152003800e20303190030040302d180142c0705810800309026101c040b0104da092103040c140b811815200a0007080d45500e400d03c2c5d2030b02d01041d41c1c50200241c5004003454500e00400b100c0f20700c0e00c2520f4900c508802d41d410000c10b000d0716058100b4a40300ca400c00150b0004618190703000810078000c220840301110307a140700304005024405c0000111409031884084154460303048010090f04169550104840e0502030104c103400e04040c0055a807122001c0e00c011054171300c1d0800107194090b480c0c02c0002410008d4103110700b0951300001846c166450010b88010200941040220a0051041190380b1041c00031642d085103c070a201c094000f0340240204410645030f14038203007561000c0b22101c03142d91000d0300d5050f6640c0e06011705200c24403150740030003000b0388a403500007281c4694050b0750 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 412400215 1250 412398965 412398977
    0x1090c03021e04150315090f0b100305010507030605040c11060a0e0c06070c05090a0b0a03060f140f0702070603150e0702031c02181f0f0509120c0301050f01060f 71
    0x8800030190425000c90b0ba4001c0040100030302101038410034002c80d0005440202103001c4c01e030b9a000c1030b485803a04158020000c5030440c03c0740d0341d074004401c800402c034900301400c0c0741300000055400d00075540100600c0c1c602042a90a0205200c01c076400440100108008850720404082c404903049800a0200c0c23000f05118840c10340907032400341c28145849d04054002002c8007030100305c55813407059440c115500c00303494071481e00300b5094840c8040c0056020601010400c00034081d680135044076402820046100a40c0c1240100c00030313130882d11004e100c503e0000704049146c0c180701d0751010781203a040c00c004407980034088136019803403805410000c811a1000c165003500070025150b03000c0350428032031040c0d0b18001400c0080d40041180c07240d24041e03403220070329618058560f1400e500040200342100320025004540e103108240d00401845000c20803000561112621980c0d07610f5020002e02c8400041c001b81421910000c10181c210181040140851603204514806206c5245424 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 412401465 1250 412400215 412400239
    0xd09140103230a090f0807030809030309030a081302060d0f0e030a02031905090604091a0f10031509060306050603160f12030306170a020103111305060304060f05090a0b01050301090c0302 82
    0x2c8401070013810806089000348051440030400705a00410b41d20784240d03504415900e40b90141645ca02064802c80c0c40c1c0d80080c0700400c051132040c0c2913913501c011240600d40c0240d41c1c6401084040d403260000040041c0c54078040d0020351030500803a0403460362440210700e0b000907400001d480e0700440a208032250401d00c4940f1040c1d1151041ea021500000d002c560b403aa07580380f64000404a44014810705000280303c01724a1030f04c403c500b0034403c2d000e4104000c1c2c00820f038084004000c4da000d00e0074001007005003c030f40b5450b94400ca10155100310360011b65800d00c00c0c209850501d068a01c00d041444144040c0410012507418a040740c52420001c0c46001d20351405070081d2690b6005150344035958801686044000103003005014000c0c1c8081000003000891140c0038405c10400614031031040d0390400c242e042c4070000b168054007c41001072140580c5004d501a550140e44460050344000d540009001d803070703aa4140102822802000702201c1551040e5040c6c80700c0c840a4450311450140d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 412402715 1250 412401465 412401481
    0x5010f120b13020c0f0d020a0b18011e1413050a0209130b0a091101080f06060a03060b161a07080f0c0c0a0506071709030d0b0307080d0914010323 64
    0x34510a002081c0199140c500d071800c0c06a07601510103005a03035210f606c001075085070001c9196142c40f9044081043c580d40c40d940310402003845011031910640d6124002490040b5001150408644a10010034900c04a000f02c1340c0c60345028218140c05000c101e50076001920010365a40010b40c150307110011551a03110aa91810b0784200242c684070b0900708002d144416580305070387c030501c0340301056007152000c2c004580c07201003280c074101009000c02c00304000380b40070009800c0c0c2e000c81d0701e004541281c44114606040c0c101600503419a602c280d003281c100020005049000010001a82414642601e0041c40500040d0801039030044810201b031068668071b08440c04200302004603188401c1e9854416a202d0f0100d540350300056900019541d60202c004140b400f58012400540c24000162540e0b030081680c3c040155051091090005001400303200041b19031142c0c0e100d18005c64134104d04d03d6441d1606d500268101840c1c20040c80a201445c010180c01d6a080c00040c0225174072518 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 412403965 1250 412402715 412402729
    0x130908070803040606030c090219110307060609060504110a08040201050a09080a0b070311070b010308131e060219121101110f030402030d2a0309090509010e0705010f120b 75
    0x200160507038000200704410703c0165007000c41101e201308444200300e40d8403907042c000c038081c0c12340310724a882c800031280120070322443c818034a001540080d240b400c5d06541e00c0d1003c8a000f94130010741540c83d09030810080c5064401c1b90070440309090078500c0c00e1801c3c00c0040c4a554010030080c1404400f054101c02c0510030020300006d4904074048603501800e0341450310003200200d60800c00a4107100144407102a5403040c4d8441980c0304000d1242a400c40c2da610a090f0420701c00b44098582100c00099a0f20721915491140b42020b50315090040c20240c00a040c40c1e104040250b504804201081c001070742c82148070035011844c980401c60f818040e050602418030f80c21901841d400114161941800c52070042d401075108034103d4070740210381c540070b80700b80303100419000410f03c602e103100e1200841d0007035905415210b031a103c1b40c90740d15507924404869054825100c180e64640f44449031400412104002c0c01090902901c55560a10002c1040003003900d058442c9485010170700c480c0d01d50384 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 412405215 1250 412403965 412403977
    0x50f04090c03090629010e120109030804030905090c0405060904060305070605131e030f06060302090f400312050114030d0903020607030309050f070b03010f080606130908 75
    0x94081c001c1024a000060180485140c01d4984a03e002e107901c05200401d0b030780304900c112044648483c4c1d00c26100548034202003000454000e040f00e112400c0e00c141c00c0c4111004035202c0d4035401d80500345410014200d84060300410f00a24050301880a50350082d000e50303040380c1048404950740e030040d10216028005903480207209109a00c00410150742040140800c0d40301025050070f61507644c0c0032481021410009400c081003807a40c1440421042d031462014103005078004510980e5030780c04214060310840d0fa040f4404400c0f4103201ea142d44034008003d6001104100c072150b001036140c034520f00c948550b12040d11a4101c07640b0010540208100121400404420000c542e510100d01c5030060000c41558880d00611190340810f900821104055a80182c405400d00e58584d509800030072001c1300c195000e1240e900d1200c1441c40c2001400701402400010907180e51520b41c4003048044550010101500300340d080004030745070b20089641640c00c100001c64030b03409070b0506200c00c0c0300394 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 412406465 1250 412405215 412405229
    0x40309091107020307090501140d02061207050408030c01020d0e2a030703052b0801030309050405040c0e0916080705090604090602040512030a1418090a020d09060501030b09030403020a0303050f04 86
    0xc05c000248410745603002d14103c0e022000d00d1600113607250300b009846040d042000394004420b0180d100d03c40062400c20780e01c8080e904183c0e00d016155840035145400451031038249a4001441980c805da0318090020070040c607030010301652040e104080000d50041400012844805000340c0050f9420486040116041820f60308140b80d0381a041c0c03c040c8403440000e012134200c0d50100700d650b01c04c521440c100da030103655812690f0f0425007080003902018109884070f08904401042c130385d400e80300a03030080d0460001840d18280c040c800006e180c0c21a4401289a00030400401541c0c0300d81a003140d00100c1200c00240c022030381c0c0380c440001c0c09281c01c1586c01800e00419261110300010007441d6509498a8030911b030144112405200d216646210f003505810803441640e0381480f5003685d400485071200036061000b680b41c240202c42c0801c0055800984410040080c011a001c90030707040b10080000c5c1d45400d0840c0c0100b520520710784002000c200000802200a070711040981740a4665 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 412407715 1250 412406465 412406473
    0x3020d20040f0b0f0108010807150314010801020703030e0303060a030611071a0108010e0d120c2307020f0d0f02010c0f0210030912020c0f060f0d0207051c080403090911070203 77
    0x2010340380b004100802034540200121412850158007803031400e41290404001800001d0500030754a080c82a540e11903021f1541340c400f200c0e4103003035440129002e810903000040c1c4a034403900f001001e54501e60300e0403580da003081041c404141c0301e8440030310540350043e802107001c055006041c00c05200b0100050b02032001d49c180c05240180d812203442c103c3c1c01030781c028803085803005c24854881c0d100c0c41042003c0703805021007240c0c0403810340190303919995508080c0c13a90401070117039030b41201d0540304a040400380002c0440840c03401800c4014181802c0e0752710068600d00c0e5a580c8006040624042d05001c03031140060100809a241422990340c081c00b0f881c032001503110060060407009004640448294005c05942ca1000816610030080103140c00c0300040c0c0e100902025900840383c05209210401049403100114002081030314807400040c080d20b42d041880601c0501e0100030001006495020301012a6100c50031006070b850b6080001a0700480018844552042c50402501801 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 412408965 1250 412407715 412407731
    0x12230408010504031403150f010309061b0201150302030c040e0727050603011509020a111c0e01020d0512070903051b0a050303090108010905100f0f140a03020d2004 72
    0x240c1034100740d009a01c039842d003c0144c0b5480100b4138680c08219071040d131081404d1451682403a14600c3c40f172100006050010301d80009484c0c5009540b040c00c5040341d003980300380b410583c4580c240304185540c07038200c020401c0e0500b5a80000d880303402e00e460f10342c41661a11102e819040c0c06010040040140e800c031210500c050582010010308042c0031040068a0840094854141806480000c0342c2200b4000070311420403aa61000f034006140c0e000c20002984180114103a04105011900d001840140141e000d8000001c044c605580c00c2c1e60f04541003400d40164440c1c000d0180c54603103180958805035965502c10444171005141d1001d4018480c0350f94080e2806c250500c1540d8814054400c101503903114001c1c59540c0c481e8072103203400102000c0041002046a44c00340ea003007401d00003030070f07038060355104419802c1c0503d0b0001142d4200c89601007218404014100f01c80300c0b0103403100c461003841c5030005001c601c0001400b40100141c10700550300b1000307003038040310007180080040220700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 412410071 1106 412408965 412408979
    0x606020a02010c031b150501090b09010308070213090b0912030606120406090203031207030f060522060e0a0b0f090f07260c090102060a09122304 64
    0x24444500c00c0380b50000c2d021056172a40111080705d0b544500001920499806a0001c4245071910f01e10700f10b1511042c907860304580d008030b00c107070300c61007503001040962103c01a00c07001e02c1d14100c0b1000400c60800c00080c080e04014044450490040402c5080c0788410f0f1010f503408107042c0008121210300f00003040e03029100d9007000c41c00d40240e80c0442e1468121400304c00381115400c1c2004a407034ec0c58800d520303032285c6941c0d061200c42d00c2d000104140103e64a1480c00030a84008000803000c0c070340d005040200710314406103125150504120300105601850180714004444507010320740342220721a40a4178102a50a40a449002041e5001c1401544100c116010b0824001068444018403485003403002c04090392254401c000909004008160080c1e103407414164001045100368942d8003905c071b41c20a03a00d44000b00c1805143c0c00304001c49105851400a00480e2013 = true := by decide +kernel

theorem cover : BRFrame.Cov 412230215 412410071 := by
  have h0 := BRFrame.cov_init 412230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 412230215 ≤ n) (h2 : n < 412410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
