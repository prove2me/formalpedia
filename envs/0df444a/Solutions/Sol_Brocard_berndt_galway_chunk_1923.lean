-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1923
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:10:15.245056+00:00
-- url     : https://prove2.me/submissions/b7665714-d543-4c5d-9780-780f9fef727e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 345683453 ≤ n < 345863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 345684703 1250 345683453 345683461
    0x23a150603110909010e100f03021f020f060405010e07050d150b180703020a0e0d020d060203071b0c030c0b0304110d020616260f09090405033a0c0503 66
    0x200204804402074041c2c9034104522045a990341420300c2c000c0c2521601c1c401c581c60700d07008850b800e50702a8040e0b00c1c0701015100030300050361151030021a10300802d080c50f5541820700f208a180c0442416281c2d40d0740201c03002d1105101040d0010241a401c0c002103445181d5030314144004002d181034080d00c940032609210300e900c0c1058115240c00c030001071189800d540200b13a0307001c0c401c000307854030400b0a50001d4103506090700080ac001501d5800c884a2480003096008602d4041c60010010002e40d400000144514040c01e17407504611a80e45903803130340f0a220310340b510303118a0360b000c107032511141c0c0c00c40003da440c424000c81e44070356400b108280d9809603a2050050005005408030fa1081d014000014071045a0300c0640c0300703502076106040d030528150300000381100000340744403401204000000c0d11505803002c40b60760060542c1c40080591b80d07820301c5030035030041d41c0841001050a050480250303059403082c00c0d080340d07921060040300702c9020103075044407604140003010440c01c1c4005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 345685953 1250 345684703 345684707
    0x110c06160b070809121923040b18030c0604090f02040512030a030c080601020a0b130506190f060320010c0b09070e090d02071206023a1506 61
    0x40c0449280345500001460019500c54500410440e800300000307450004204040c0402c00520903c80d181d080c0350ba25000075500720501d013080d00384141c8140702c41880c108080c0400e58401102c0e00f04d00107c00c1d511507845d800000740940c42045001c142c003900384040103041c600400c80604c0032070b000b862180303802c0c580f59000c406081401d09414040342c1c00d2000240d02e0301c806140c08104200b040c099035840000c0c0e000035007100d10f01c4400e18100030741e010400095980004440303038103039007140c148103c50b690008415048480f0b500000c0c807601a00003400322072800c0c2502503007c0040d4440c14400ba60301c840400b0200c4695102c0589080c01c0c40f00020300342901001e400711500710604d41a940d2400303030340f0760104080b030035074400210351300a910401024141d4040541c00900740e2014045030b48201c54000d40c0c030340c4213014203d10b20403510308440030860141d0490301e080b0292100480c44a160746490150030042030090280300c04040c18520059a03a403003100e02c628407000440300902e05000d42 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 345687203 1250 345685953 345685957
    0xf10050405090c1903060504051030050f0304060915080708090309030f030c07050105040515090d0c090b01110105040b0705030601091a0703030617060402150d09050604020a06110c06 80
    0x4a0348000f00b0000d0704551004c200034180420300648000c030f80945003030103000807920010314451200190400030710210f036a507400310010303403410500c0ca11241c04918810325904003158006009101e40d001c203400f000d001101a0048030b14035100c0020040e90b03000808250483d00182c0000900c010700040e14007401805140d81000414045900713061051f000f2070301d01000c1d80d81550460344040340060900e40c0400c1090050031080c64024141441d08000c242182d050380e140074203820700890036803025102c451028807039980150100e407049a8072001c8100515451402c24001030040580789010701050280c0e50040b40e00900c028060742d42c030501120700d9007000c0c0200d030400000d1030b03000403a40c03a800100281a01d20302085613a0b20058a00a01200c0701c3c1d6001030450042011200345046001c9802ca46c096016108a0280420f40f034081d84c041c4039a4070002143d901c5d014204007400000120300e4460340c07094403986045521a001580c031010313201300106c41c41c1c0c020200b0031814117080c80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 345688453 1250 345687203 345687211
    0x5030106020d0c03110d020106080708010c0504090209010302090a0b04081207080a030b0a0b0a020106052803080f0702060c0114090106140d02060c01110a03060b120420030f010b0f1005040509 84
    0x5d040b0b0500704441e00c403907091415945040740180c0d1501e8003440341711020300641c0010300d824802000a5028000c018095020303511428066590118030400340b41d009070100c40c0d02243c01040844842d440b00d904c0701d069000350003130b1076a501c5015001c16224448408480c3c10307641200382c032401c00d1086c0340f04401411a100300d058000c4803504000404400c81d60241ca0110701c5e940002c50345c6400c0409004c0c01c00312100507030b95141d420052070740101c00b00310740c1380c1c0c1580d400400041d600d4452001140c46403042c07100003904014005040d402d144010760010348038160840c0720081c1502c41345201790a851050046a030304800708101c0008918043c50303036031001071010380380d60304000100000a0840e9090003100b110100009150340040b80d140c0708543c040c185000c40c0d03600b411407511140980d100010001090603048105401418605548580300c10f14028102d5290600e05403000e40a4000480d165004025030040e0b540645007102609101d50882c1d07071072038245031529007002910600a4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 345689703 1250 345688453 345688457
    0x4030209130203060c1b06012616030b070e0a05060f0702010e030a0f0209010b0c030a0f120e0709140402060322061406090a021305190803030a0f0c05030106020d0c03 73
    0x301c8040050300e05011440c0b24205840d0a1511900703a011609003a001c40c0710500d226400000c014441682054141daa1022041404406244440180d00c1c60280541d00303108800891140c00420050b003408100d10030308c07039543c0e00c070b205140c0d6101303010207a5403501a250b800703030302407040b40c0e600710300c14018160391401407528030007802641022a0400111440a98074080004070032400e5052644400340105040151940340603c0d1301c940c241c4a0240c46414410452107030529107480d4420103002d1001c000c4a1420490444940380c9039680c1c05031446420b401c203041c48180101015038240080c41070b41c018000500d19903074884070210042208100255501100480c880030500c0c41c491200503601484940072035090110400ca2480f40003085052114010400c010000d0069066101210800d907444454a410f00709014105419900141118403012040000c10036440d001214001100c000401000c102e0140403161840700340100303005640321203103591001d4030410884542c18064 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 345690953 1250 345689703 345689731
    0x30a0209040803010905060603040b061c0206120702010c09081b0d050f03040303170403020c090702011d1014010303020a1103010605090106020c030105160c0308090f0f1c030c0504030209 82
    0x560028101800c251400c0d5004580440180414909441000c1d080001140c1043c2186007503500c02c014142c009202a003c1c2681d031030324040843c0015221070301172380c9c020710440c1c0b41c5600a50314401c00d00201c0c5e4600c0198206113062190341c2c0903c1d40a42526140c1d13020346003074091603c0b009002c108100a00d500a10f099088502062060200303626008507280074542d550714605000340360606550401030701c01e681005001c00a500003810101c0683c3c2695518125614030300141c0c018501c80d220f540d094410350310481d001a0001c80c1500740080f090307008000c1a40102c0090b060032809000c01800b503030024204801003800440c2ca0352a04000600126044ea241c00200321507a6080e40494090303404406080c6031032400380202540100a010004440110f0341c4008195070460180035041c0f00004c0d0106080b003c05001d054031300300d01441280d00403400c1c241016030b034095145201248403d50a01030304014802d00405400400a40e501350802d82107408010780803402400c1119400e0034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 345692203 1250 345690953 345690973
    0x809060409090c140f10030b220b011209030e01080c0c190209090a0c17011506020a020a06020304120602090f040501060503060a050402090631030606060f05030405071403 75
    0x70364040d0b00806885a042030402d1450101c0c00c0e840c40c00d40001952081980c0140a081903c6e071942c2a5420340c2c042c900880e0030002d50000c100c58126001c100c48040f801c80b030420345c1500c21600018110300007170b61500740341000642420101e9180a1000b0006480d61040c58540e40c85050b585030081c0041e0843ca203000c0c4c0e40c590f154604900d40c803c502000c00091840000c3d45071500005610005540c090b10140d034140d0f42d060029500c074020390320300c0d46280c2c6081e10400170035401324910602800c0740c0010380c2e0b02c4501c080d544190101d401c078802c04441d0408185148040145d50407900381d081f94004001850383c564001c2e4003c138083d81d811000c0e020001d201580c85005083c02098603448541c0e590600009000c000a11a08030f42c1c05540100070284450725914111050413003001ca0300701544200ca200c10b003070000207201710030540170700000c003000f84171040d80008200c58540d1103901d4100c801550903901800304550140054002110130401034903031780b0119074042802019140340e108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 345693453 1250 345692203 345692219
    0x1e110d0b0d0605041b080a2013020a0e13020c1c0e060304080705011107170a0c061a0f0a0501020a0605060d051209093402030915070c080c0a0918080d05061504080a08090604 76
    0x400c165800028a4cc2480c005483c00e08421801c132007450001c0a610742021203500940e954002078481e45116050f1000d03180b000d115404c00c01071350100804881d134908050901c3e00c116004098143d60035460102050154401c4074101c0e001682c2c80852140c05110340741104c11160085100c000620600215000c0001c3c401c3c407d41d641801c0c030302402640055854240142c089040400601445420409115903030700001d00c0200c20360b00000c041215621000803e5510080c034000030040d200d808804822681090003070501d8000c01d45003650385030758542c01e8503000d0a6200f2400008420421500b03a29100001d508840c1d24040c01160f243c03c8900c404900f009000c412040b04083d80840c0e0207040014104480c4001c0c0340100c02000d100c661500003400305203041c4115072000380d0b01e10425150b0350280204070030180d0045101a142c014008002e406040b045502a1042d051409060180641e042c1a681511500c1c0e002340644075240da20f84040d580141d44860b405903092100290100c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 345694703 1250 345693453 345693457
    0x405120a0807140f09090405030c0d0507150c050708070501090b0702150a0606020304180e01050c07050f1f0c020111030a1e110d0b0d0605041b080a201302 68
    0x401035461140c1c1d460308000052152284900c18400640c0030082d8400d408410416100000c00440b0482c5041e20f0740d1402c149984101d000107005401404211004107800c0806840414002c40d82c10305840010322614048030603c42a00c0c000c90010722100012611400140c60820b118600003e40344090780c40d0140140d204451100051344040350f0900b01203151380c85190808500300047c0711190405c0b0010b5124000c0780145c5d100c86003032051018848080e40c00081d42842540300803c61030400c821860026400454280d07518480c030307a21007401c21000512110840c00c0f50040e01c1002103007106030300c050070010007000115921900c0c20403801003024015409880c0702040050015560301c8100c254498014141c0303c01ca140483c0000750405070f20442d0041034900300006540d500400025410441c185400781c60343c1e241c2000c1004008001040b0f01075049440d403078901c019950300401e5991038144400910300100d0200d800c102144d02c8440c5203001c44024240103000043d0f84a0004030313 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 345695953 1250 345694703 345694717
    0x902031506100215071b060e010f0e030a02071403010605031e24011a1606090224090603040c12030c03030506010509011d01140a0302030604050c03010f090203040512 73
    0x50660034007400000e02d401c0c0440c40700418540041d010f8a03014401248854100411807414024406100310304039200b540101030242d8440401c02c175120010345140e0081c0060b60b45001d0951514060b00301200c8000142d41300c0d6881940100822410301000da8404903600030829003564032040007007207a40d0103110640742c0c5140105100c440e507603404410b6140a0b11500e0403010384018612002c4c8014004c100765041d04c810500190016400c81c0c0300501c140b0448103d0342c040c0060304811000c21455410054081d4021590b2a0b80034030741003078041e400130b6004010386540804104440c0b641c2441d6000c7d5038410302900c030740004c950741c07880c801039219400c0c8401c42c000b03520f4401d500c0401d078040c440c04d9000442840c1031030170f200e0312100291071004100d08902e402c6410310080c580a078032400f4801e4900780018070258451450107405006034005a8200b8480d60408000503406903031841580d040340c1d0307410f0038200b519281c5a407000081d800500b00f6121806403660381e40740c440c0b281d0020051 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 345697203 1250 345695953 345695983
    0x20111030d0b1804020a03080c07150507030f0f0c15230a18230109051c030e010506060a080907050d08030f06030c090a0c0905031606080703090803130204090203 71
    0xa2078080204000b40d4450f00f9580504991400c000e00002d0b860742c140c2e0070f040e01c0e440802c0564841d48484640d01e0500651700c10000c2d022088a01149281d01501901c1e400e8800d880304085a41180b000b036990181700b40100c4001840405000045246401289000900e820740040c400091405403400450030114004d4440100c10601050310306078400c580b550040e41d032a086240100350b4480f40400c031090401804441944203d0038041c0b000e601c41120700d039001d0101e860044401112009082164041d407002c03038644017120a80d00c60600070b0710300c00c000082509180030100c00c0240d0f628900075141c10350920a480002c22942c540b81c4040071014084e090f026103030710300641a40a04107004002c41d001760803412050940d504c2d940c5502c3d4102880315000705420b02140343c00c440e82855584010741c148205596040e41c801d040c6058030585880795a046078070743c2c68003000d0702a82c0d000b0030300405070a0704200007503020b1540d60103aa9240d01c000c00200c0d51110540001c3c0c5841060018640 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 345698453 1250 345697203 345697211
    0x1e2d080d020a1803081b01150305060a0b04150501050304031b03050d050606160602030a0207150b10020a03020604030e0a080d030c081803040b03040501020705060f1e0f070309020111030d 82
    0x40300754001504040d140420070b4408606801c6541710381c2d0070b003e480010000d0382e6462414112244d8290031207010201c078400b0503040c0981c1c9041c403903540d0308292100f5400c03a242070340141440c10540641503c00d10000d8414002034605001110940e000500036000c01c8180b1031030443c00c0030302d0805201001c0c0242c0e10144c8590041300800101e45029280a10680e070810100343e03042010b012501d55036410081c010380325038400710140701910581d00700501c19045040b0b80032400701e5030381c485a000791050b0f5030407500003407074142a603440c24420030141c003582c400d900280000c1d2260000552290300523210034031051340d8085151806030040d0006c40820780310804e42c16560ba00c0401303039074081400c1048040b1600500501900d078800c84c01480d00c0c9400002c0060140f1009404840200d85c1c05012203c2c03e162200c019074613140c0a45498114205418985000001c42c0c40791034061b03c044c400e040403944035140b00790000c104003013049061121001204c042d5410070b1000d807203510071003070000c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 345699703 1250 345698453 345698467
    0x41703040f1502100b030f0d0c060515180702012a3f0212011d0604050c030609072d09090204141005160f1e2d080d02 52
    0x41c044525a42060580225500611041c1a40014804915040600e001650850800101e410820415139811186c4108400b14050a522011002c0400e01851040040e03882c0c0c0d902c0405400d000d0000300b94441020801d441c0400305480046400800c14000002d800c0c000c1401075010001a884440c00c0c64084004012a250040e00d0100e04209900d2034154207102400440c103008289001004241c10003071010022555950445100d0f9a4501440c00b45680d2998010000c4840000c02c1c64070001800104590741018022980110900790321203045641c1c0109018184000034090810000f181c2200d0142203030a1040300e1204c06502e1002070040d042000241c42046141d01c10600c2500c104000c0040624000f003e01070100101c0e1440704004c50441c0c01c851602030b03000d030012585181d01454040014011500750003030700c40d81102500c1440100700358a0142008005000b004c4514040f00200100070404043c030143c00130b07000c0a1010503100e120381a00324803101c00c407003980083c0f07030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 345700953 1250 345699703 345699719
    0x614120c030411010305041707060209030f0d021b011d1f050901030b0303070203060a050601050705010e061005040902090a0c1803050604050c09070f030c0306030f050709050a1109120304170304 85
    0x3e0000c0d00d400c0c00e041c4441c2c101a56014950801a50601c142d00b9021511000700003043d01100e101d030b00020111943c540d03846042c0c2d502c41d206076001202610031920780b880340c0d40d01200503036424041612400030318540070b00080740341203000c0456a0b000c0800940b004100c60203e90180e030f5094a43c1e9084c0e25604603030700140446490302125440ba0f8028440400140e41c00a101e90348481c6142012407551600340060b09c4602608100411319400c0c0000300306421400980c45109051018800d00c54640d9203081c04101ca03c50075020b9040b091000015940c1141078201d911144441d150a0451600c440c04010380080f441e00100c41a800c448180302c03d00c40d0420018a080c030084409c07040a05100d4000707015040308040c92700916486544c4425a079000750b010800451b001ba45001d2440000c1c030b8582d88a006d24058502d0300761414010901140c081e1140320540d807410011a07280c90030321000c1000c08900c903110705400317100410000c611402205141c0c00348100060055445034146219 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 345702203 1250 345700953 345700973
    0x1d09100302030f0312060d02010e12060405152e051305010510030510151709010e0610050a06181205070812090d032001020a0c03180f0614120c0304 65
    0x40c40d161300500800d00b0544000f5001600118200c801c00034660807440162030050059000c15032007210b4480b1410103182c0451114800c038410010355406841d090410b0102d52000d03100101d184482c03a1520041c030b911071044000401042c01d007400030700e07924170000704003080c0c00c218444c2046d1241c004010703a0411400000341c1c4051814240030034580f0080528085682d84a0342c00e0349507035064440381003400382003034590010442050850b58030b000c5030260701030141010790070018071410000882c0003c150150360306403036000f003d0b046d102d490024100d81d4081074120060990106d082c000070741801600b01c0b0031409200750060a01c40d440c01b4085420400000d03d00040c0c11410000d001c016a03402214101c1c103545420b22014450780c4001c421402e10f0713040d140344001d6100041d034491403a0010600402d0764400d6803580081146048000c481030218440c8490100300e1000c14040a80508403030707104005554042c6007044082110515114425200102c0c0300034000700380300c1404881c0030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 345703453 1250 345702203 345702223
    0x606090612020f10050f16080a03051e060a140406090e010b130605090703090302390109150309030507050307150612050d08070c0b0c03010f06090b0702011d0910030203 74
    0x20f032a54140f00c0381e01d024205d440f03201052190f1071000203007031948010071b4400d1400d140e088210582c0301e00100201800611003500e07000c01030240d242c05078a0300800000b240f80b095030060704002020349003291141c0038030300524015500070f48540000c14004094455446064106800865a040e40380c090091140340e00f184c8080c441d041c0f00f070070b20454072000030558100c0154078000800603d81e050403420150282c141c0282424044c04000350241040f245003510f0007401d01200c4051180c40055034500b0551064440c01d1451001840005d4040c1d405204c2c85402414079030710b0240543c1c0c88070308551003a18210b496140e40c1c0b0b81d180e03c125641c030510000c1c001c0e540107143c0400c0c080e2262507803044c0c003022920800900d1030001d00c80501ca00d148040030f40d032041600d0340034140f1544070f03007040e0800d010700c0c400c03400c8820000882501c00c0e0f03011001c4800c1e901503c4c1c5450400d800441d48040c01e070070402442c0151400e00083c645403188010700c1290028000c00d00242076104150130041640 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 345704703 1250 345703453 345703459
    0x5070f060f0212070f0f0605060a090b0d060e070b030c03010618050607021011010218040506030a021503040606030c09020a0306141012150e1503070e070c0606090612020f 75
    0x302094241070b00000c441c0e05014505840707945890350703454000b40c140c2d1150f20081c4403004a03040c0c00c080280c4d541026004460881c1c62003005174540308600103e55180303103555408074110044c280429040d40c8100155521802900c642075280c48d030040b019070003034a8040d41c081c07000004101503503200900d07007514840c056400c0415031800001441501400340042e00c01d242c0b86620801a50296041d102c40c0c5c000a8001e5458059507030041c0b20603440c04082d50301450030080051400c5c54041014401f250f40181512040c0344144150500d5400003001103450b20358800010010822640304180148142070380565150820b0400070140c501c00e502ca85106c110600809045e640e50a8078a1502c44041c500f4000e100301e000707162009400c0b004941044500d04100c081941c0080d1b6600b1449070030725488028401500b501455a80d081522900034680090340c04901d405d0301c64080540540d00400e00854900e4840c000c110864142da4071809030080e10036610b80450801d21a2030151150403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 345705953 1250 345704703 345704717
    0x211905070f0f210e0c03150105030a0b071701380f07080405060a020d090f0f0605072a05040c0503010f0605070c0902180f0d031709010e0a05070f06 65
    0x203100e0203802012003688560600100021625058440c40907100103072141a1040c062401c48218a0385c0310300c5280f02460203400b48064800205e645041680e04803000a0000e1495030f14940710101c0d0420054110307401c0010200d80719041c0004551101d002c0d0040550300690900e1500c400032411044440c0382ca010814503181c1803011130748500340c1d03100c0d1151301e010396a2000c0070300e82171100e88120b4200c41e074450808141d20100560000d1039100181c036680701c081e82c0b2900c94013210f4140c14688a18007602140001c00c1c443c8034441c101a14440d4815150860400b50b50030301015102c0f14440d1440b54400c0d00303c410840d0b85458000e000400e40581000c0c2c1c80c2d541821802400600d05000301d00a1010002d0368204001e58142c1c40002410200401c5445103401100c05400310003000340544120640b0514540502d4001c90420159034107880303212014410100707604a03518001d00e110040d541e511a4299103070800d2090606003845070002e001c5040c2401441101075000e0b4101c8820824a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 345707203 1250 345705953 345705977
    0x1806010c0209060a030203070b0d1107080703030b04020702060d09030e18010e0711190614150d0c050a06020f010c030501080a0605100f08010c0e04020f040b21190507 73
    0x428003a0100d8050b50150304a56528010a20700420340c1d00094041c46a40d00026030b1070054000380006581041e000e2142d016511000c21442c0642c11018004240070804000043c1c041e80c42202d00b82c0001e480541009010b8000641e2504041d4080c07040940300c3c00c803c0304040e0f0219002c0541030080303806804803400120901a51041405504841203951000ca4016030040d06c49460703203196002101c1a401c041c4c5510702503030041907070131251a400c29019a50212021012601c6400100d03040741101d0a40300c00c00008000000d01500c03c445101004260340e00da03000c013040540000cbd0020114481700030101400c45442c0842c00013010701e000014401440c0102e04400000d40100011440f52905065500b119406a000c444030196044c0d000802c210103402c10702c0b404240d0b807201e4038042030702400e0000f0303841841d200455820f01040b0904c44519000c0c094011880910b08008000c020b801c1c0103901d21070280c0e8001c0e0001030f80e515882d6001051f010319980000c10303181c2000d0041d2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 345708453 1250 345707203 345707207
    0x2010f02190305130b09160e070f2d020a02091303211814060709080c010c0c0e01030f050d030608062e06110d0503010b0a0810030c030b06180601 64
    0x10041d40c0300d410107846401158a6002440c041d0500d02e411020030f200508100d0b480c40c0c0d4032455043c00400da076540200010322495041c00c03082c4924065190000030008440084800b42000d1030351200d01a24030043c600700c0c843c1c0d42e00400025940e0740050501c0d03540d83c0104400582e00170400b001c501c4500c8145000281d20455041081341160f040a0746c003102c050070a805816104c48a90104034581c02040c18401442565000b0810840664440d0f8450341e01c11aa0007210340102051a40300f42e1244105512509034500d64901520395075181644484401045030030030303070080d41c5c4145c240030940e0034001c0601c43d40340085c14504041215524180760340340c9a61b4020b1620b56203000c8030000610f680c17140428000c91450140300d8999107601c40790054000340f080501c8810328030075a41c001c154a800b03102100e05030741e051000903042052460044a40b2003006001e40704598280000100141c952540385000e0f42c41000c070030165103418820f2040d07036030b00781659203c030500a00511601b40d03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 345709703 1250 345708453 345708487
    0x1f02090a0303140c030a050a030e0c21100f050a060608070c030302090d020909010c09050d0b040204020c0f0717100c1209030504080a0302070e101a0306030703080706050702010f02 79
    0xe0b81420601d450140044461600e8040e00d86050654040020041d282c00c0e0310070010320100000b41c07401c1280700032141c0e14aa40300441c200042e08443c0c489089901c5600b04544580034001940032121002e94640b41c0000342da0403a01c4109056881d0020305c5180c04140c05244042e03d41c0745400400d51402110003001550702c0c0c44050f050641c000750071265a124190180d00494015010307001a04108086500034000e180e070b5080016225503011a1600e01058804500f54211440322441d48454003048001e42c01010007100f58072448020070340150050021400038021600902203100b606420305003001da401d040c56207114501403800d04041d4100c2d030840c000c00344a07200042d04409a2605907540d10407038006441502c01c17007010404040c3e0004128003a140003a8490354561281200f8400d6000c1da03000d1f04d1a41c0002102881401c8441c3c40555401702000741181c9000b42e498407235200b50341c000d070010b48046444e0810001c0f00d0f902405020311117200d0000c110301d00b6144c1d1096840c52 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 345710953 1250 345709703 345709709
    0x715021504050c060a0e0f04020a020c1509031c080106020105010513090303201c1a091308030c03011e080318060702090a0608070608060307031707141f02090a 70
    0xe2440d00c0046400c0c080d003040310000ba843c000d04201d9a4141520700a02012401d62070f40f807080780651003170ba160342018003c0d2050301013203400506003102c201c0d0810800340142e540c9006012814040880c5d90f80d410810b4080c2940e0015407070262148400e40104080d0050f040003082d68185001000303d5158144210034040800e1000200c1d003002c0d01d01240604080c60031511012203507008080341065050080c052040c00e800da02c1307000020a520b1509407034a81401c120a6206440100100d0038503a00c80c0782c0c004006060719401d62a50341d0303580f42e0f41c0c20503a4089200740300800144200c105901184003010a42d11001001d40e1501c4851503407440b600003d42c00ca59980c1402d05d280d52241030559250b0399000f8200740700e0345403101840d0024001441070300103501c280c0e035002500750f0080e12401e000e02d2020f4050b00010303085071107246001e290700e00810018401008998042817403079841403d00d141000240c80c0c120885180390117403142004140214510410202c8445d42d5844d00940032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 345712203 1250 345710953 345710983
    0x501020601140310050a02040501030e150601031808071b0e04050601060f02010e011d06130305040b03040807060c08090d02070e0103140c0a140102060f060f130216060e071502 77
    0x30512080102e804c181c80c0a0000303030700074180740902034508400d4000d4000d80e9000c0c0d8040003840c20f0048026640c14031010380c5408248424042007039544a50001c00712206401d6170106d0200c441e6440c0241f50307000d0001a5481c024480c420f142c05450003507160010100520b04004a0038103445241c0c40301c0041c403401c4103015890b800d20050600170741040c2e15800414000300b1030340701288025100e030b1501d408071181c180a040005803540c125180c100c82129059a40c2d282064101302c12920103a10150050b00c80e40d00511501000408a000341c141800166584d0306160810044031481c02000d03000d1503040d03401038801404100c940d110710340d0440742c00038a00490b09410704101802d054001d2442030308010040400308140c0c5800d250906247c000f83d080b520144d461103802400c0e0311043e0b4416500a0780d00c83e43c03585515120041010040381c110b001481c24112401c1982151a141c0040350283d841e105004e892500a100640080580d02c070500070150400340025100e260003503904c03034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 345713453 1250 345712203 345712229
    0x909030d0504060b0d0b0105041d030406120f0906020903060a0522021906021c08040c05040c0e1e0114070c03020111190303050f070c0314160605070e190501020601 72
    0x30700c00f4540240d040703403c003c1c1001d0a07000c05801d0904c03074441c1c00d004886c092800d110302072072141c06000c0401403220051010b141405d04200c011200d49000071a21903c40c0e444180410381c09505114030503030035224440060381c99032440705050802400400c9074440034903000401100200503240010408450302d004207001e081480041e08941e4800c52132002c5010484001ca005900050309556929500411140c0600e076010201e90032001108c0050034a40b9425080043e410503401201d464200b40c205005107181c0240031071350062901034040480709120f50000c9917560007000380c40441c5850703443c82d031030032000b500c8030014030075644002810004000c01c0000d050b40d040c48401d1106041c095440700b4400302d800d0003405020700380c0b09203030304018203008510501c0c09020740001075540354880c40c1c0040440080d81070150071071080a0580124508604000b444a204d0113220f80116201c5d1006a0003100c140284071480180740b005113103084400303000da6038001461904489108079216 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 345714703 1250 345713453 345713461
    0x1020705041805030f0304260901050c010f05150f0315040b1e040605010f051009140303043308040c05100318050609060604021215151c06050909030d05 67
    0x590340c000b0450010740640004a80c0c00c2c01d1004010045005070701a0300c005034980800002c0fa0021070b8511000d500d1810104810800c0c1e502a802a0210700450000050400011040386055400450f02250080600000f0b001c0078035204e807682041ca1000d5006114001e2122001c0130758120181018001328500d90004045c0484ea400e400a4500b0130307403e0401078102880c02901804007030240707031035045084501140d00e080400410100f0345403652070f003109524199180c042d0b4010324000f40e03014003003000046200d01104c5480300c0340d1120310600840c04100c80c040ca0740c1c103039540c003459010000d584050102081105403010240d5400721140a5090010760040d001070040d8203484003090a040407100c10301c40003051062107017942c6000d03500e16030b03a25410002280700702404511200b80c00804900b00081d00c6002e0303100403001404072866001d01610b003500707a801c40c0c0d0140142d440d02001d07841e2a40c5803401000c00600064420000b1410a111041e44078090f41d5009401503a40b68001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 345715953 1250 345714703 345714731
    0x3170405030d0903171c090219121101030c1e051c0506030705150d110d2405060406080402040207150c0207050411070b01171606050a18050102070504 66
    0x840050800a049420b800d03101c04001c0c1500a0900c0140ca625100340e418081d8403020804a40c00c01d200640031041040261510034000c041e54581030741c010342c81501610942055140b040c001d4101082c0c4003840d40424945030882690401c0c9644c1010b0500300445502a0011110b102e00c4944a200405074144030300300700c440380a54031021316182d00203401c0107640d5030300d680b120303015040646c25205940c0d120300a000803040d02208190780f07414100045a00c1e14505e52186140075001c60b20145007160145958041c0c440c680100c4400314255170f00ca583d0b44814040708001000d0603550f460825182640181006500401c0a4004e0707800080702410007a0415089000b200b54600802c02601d00200081d40d9012500416024900c0c045180040060300d10580b4501544203452421903130034218a4a401e05a18920181c18410080130b00041030380503c414000d414141d03145901d44260003001071040d40d4040c250300a911602d01c0a0041e40d81c0842c03980142c50b030540b400f082d008205600c0e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 345717203 1250 345715953 345715957
    0x60402101403040f3e0102150906010602190804140d050703061514030c060f0c25270203090f01060e150a0605090d030519020c030706020d08010317 65
    0x5810050a000041000f00290003130f240c03074101e014180d01c8000c00c071000c3c501c039099a2407040d4002c1c004502841d000e000d2420790031030050040184103481c8503813506440b6103036811060350701900c2500040014014150b04005003c015984240842c46082150f110040b06206500030003e0720000700907151056143d20655011580d0300c82e041300c109503a03c0c00c00c9401001c120902c0320349043d840c500021810740d01c0010a5040000902625042207104100300e0650b0004c800e280780814240034242d24181c09104040002980030b00851201c14105207201c503030881a0003400441c5040d0f640700301a5014a90700041540b42900c005a80f9241c2542c054980141c4443c1c0c65965800c102010800f0044c03150701c1d50040c2002d035808030103031184104004188826000713136030000300305004051030f91815810a803a094003d08081d407603c020140042160b400d050000d90140c5d00910440300c01d410204401001816180f014140d94158254002c10640062002030401ea200301c5809809500b1081 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 345718453 1250 345717203 345717227
    0x519151214090105090c040e0316020406051327030516050f0129030102040602151003020604080a1709031b18180706020a020a0306051009020c0c031e06040210 70
    0x18007000c989005802c15010300005c40322540d10f8001c40d04480401c1c201401103411200301d482c040c50800300c000f030303001c0d0014142c0c4100340c3e40b207911150b0003d180d8403501100070000070102c4020483c80300c40c41400b007076500c90326446080401007404540c00320b94000180d8844245180f03d0283d068028248680780000703071042c2c2081075280c000b030f0748036104246800400d0201e0602282e00440e072207208060803030096204980158100c1d604810300129030903801c9501504400034150150b80307c0d00400d400d604107401c03640c000d910810341031041c441c2c0316909164002d003080001749011014404261941c2402c1da20141d00380100d17400407030030713580d01d48003603807040b24955114501d10b1b0040c3c091800000c82030f05000d00380205040421000d00c0410b0300d8411a4020308030140c00791035079503180c000f024010030805100b58408004a24182c05000404d51050018020f2403505c0f66417007018184440103082e0286d03c4500d46084054070b02c00300300654000d404452810340800117100954081c66100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 345719703 1250 345718453 345718481
    0x3220501020d0204080f030406080c0a2d0206060904020a291612020d0e09252c030a0b19090827090103060c03090b1005191512 56
    0x101da02c0d005a0a030b9800b400803208a042124103090700101055281c0c4510300030a800503000b81c000076002c01c404030042522802e1840c0612480e03071280c1102c049201e8070000d140e070014030302c610303000c1c3c0c07540c10062960000c2089440081a0030140d0004060380b100d48160304e0180745200c4000c0d4800040354000312a00c400d203810a580d01c000b800058100081a4000c441c895007404004500510005401c4805491511017450726602001040b0382428028045c0c400510301c0707522904404012800545940c0c1d9540311500c060f001c3d030000515440502001204904007400601c0f0319030b0f80083c46504098105150030440d44841d03c0b1402d4200c200c124040206062104200070440c030b840c014010030070128169000509080481207a4072001340a0380d621062100050000c1855075014802c4807910381000910a0a180d46000381d401d401c1700c94985505a10030b08000905080c41c0c0c500c0c0641d121010070189900305081481d40c100c011070705100f000b9100004450248403544060304d0700040b4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 345720953 1250 345719703 345719707
    0xb0607060207080304030201060803070f02041e090c0503371703040c030201020d0302090d030f02070f090204031412040909060b060f0c0714030c04111e0a170103080322050102 77
    0x40c104903000b0344c402d8904500640c40c04d48005840340f4048103440049912030b00a0440420940030030003d0000002c0d010744500100a084520a52910580701440e00c501d40e8080014504020103081c032540e8039034404440d68128425464060001d00c48075084241a4000c403916694240407100080200708048881d400100740020f0122030002102164400d030308441c124058040c040301a07001d030642103500240400e0034030000902900b100e265a0034076104403180c050f0b40c3c000f5850034800300d60002c183c8560004040c0140f1480448101d070708494200141a65401880900c1081c4501e00c2081540d503650401001044144d820a480042d8010f007915152140503512003a990f01600c44543c4905c1803240008072001212002d59001d80000c0103041400b0b00d41080c071000c0c0400750f400c030905801c100280a501c0c3c103000c9100841c0700c20315041640790b903c41400601803c01580e01c00380d10f00542001080000c1004c03007125400002207241c01038100301d40001c005104902c0400410b55400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 345722203 1250 345720953 345720967
    0x70c08181002070905010617040209041a070323010317030a02090607060c0e0f010e040f06050a06050a0206220f0203010209090a320402040b030a0803070c060501060509030c01030b06070602 83
    0x40064940f094600c03c1100300310a90742c0e2441501c2c4441d41030520380350400610006805440c10840a65202e40a0382c04220940064020041c80c50003c032010404640e03a43c3d056618050b480381030480c0404c00c100003012550440c2c60b0f940302468040340401040100100107181c0e070889030180c0d41810809090161500018541701000d41070548170030000808000d5958201c0c50041c140340701d5194107844042901da020420321002e4800a507600e9040e903207c510000300d035180c0d14242c10040955660309500ca42c55000001d007001d5002d007031340c10101041d03450482441c090f51140980182e101e802d103070001d100c61002c01d000e4010280c001e80d002d1600c000300250407450b60071912508000002d080422202843c0d04c00b080c45c5481140304c480c103e440c00140050416a00808c80160010100e40440300256070307500b01980222401c2d000544049440340c01c002c0030340039945c050710b858102035051185220100b035441100c1c03000c041c101511222010b034140c403041e0443d1001d5030484010f41d5120380c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 345723453 1250 345722203 345722207
    0x4050309091006030b063f010e180a1101030b0114040902281b0c08011d10020a090e0c16080702090105010e06091519030204050a060e090c030c1c0b18070c081810 71
    0x1040300d48924400180c200c9850000000c03402c00290340d40841c0d903034441d40333095004400900321400e4035070505c04400c0541c903284601c0406000142080f48000d40d81e0755a0120717041c0c8a04038421000500800e02540100c111703000040004550f001407503944403c5031a0074140c9450200d90300c5034056501e000311152100008009002445000341e0840320400c1c100d00360401240704000c0308030001080b851080c82480c001d039691580065400c504641080042543c41e04580082002140d2040c4006841c00840c10a070440600420003424414014060600803813154860a81210300c0381c80c0d42d031800d800121412013a103100200d00414900c1d00d81540c140540258410b000e014490940c840d0000303540c40c450f00800c411004003034122002c680b1084400b103001d400c0541000f0300900d042c8180a0b20034244089242500480d100100c2c015110b403003480342e10905502980d0809201c1c80400410a0300442c0c07408800d1351042483e6070380c43c1c5c05001350440303412160031030341c4c4140040e013141c005503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 345724703 1250 345723453 345723479
    0xc0c08010516050315090a0b03011407030e0102040b0a0302070c08120405030f010605010507032307030c02040b01020f3a03051b09011704050309091006030b063f01 72
    0x2112a00b040c2c2142c00c100c01c060721076000440d0b205880580703140704081141054a5040c2d0040481030012801084110009003941c86039a0500760060002c410070402c59414040d42c110107030340900852403d0306081204001344200380c082c80905800143c104100802ea918101c01460040e00382c07000500d418030140c02e0f640c4035204681c847c2c440e02046055007481072151100700c81050711030500d0120750b65403c0d50030841007400032882d42009091111000b14a000038a4810b109036203240c030310340c181d20400044603000d469407070440d840b851900e54101800100500d00c40f8122880280403181d0000004040c034103800480044601054400b0a81340c1541016000750109100c102c0d41c102000a154003d0081c0700c050390000d0345030440c540c0500301154042c0c0d0824000d400fa0380c07038803102c800896615081600c42d00c0300d420000300100201607151107080b02003801210700e42d25000040030800882440008031560911003580f0101e580e4010890902802000d0701e004501c0e9a035481c42082c0310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 345725953 1250 345724703 345724711
    0x3030801080111031005120a12081801020a0e09060f0315090d020d1718011e240b0a0905030f0307060612020303030a050603010f09050a02040b0103090c14010c0c080105 74
    0x550f09282d007541140c075405040d40d22680c804460003414501d00010051a24a02e002c044898012065041e000c181c07462a0800f0740b04c541d44840390785090884203080d469840c0c46100b001a4410b203c0b0304240c81d881040111003c004880c24003040d154400000c01044051407401da1600c00c50b20076100c4c107008400740f60312801c42a4282c03098180d61001c2641c03603801c244c0d40d000001d00e98200f504003040c0400c00003900b00ea0446940180302c01044452821500c1d088d0310244503007015481c1d074072240d80c940600d1416003407602114401e10f082d10b10004c0072600720300079016a20000300d803d0b6000340c030074020312004000007021641840c00001f0026281d0344058010360f452410901c010600c403050443c1c40f11019400740c01180307107a0752941c2600007000e0107003c00354155214018890707400090700a0b00c03500c40c0110043d00c00d000c01807040204039402078807090f051504140300d4601084185141d101140c484a900004500b00100102e5880d824004010302d4a1070014000c01c144505510040c81 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 345727203 1250 345725953 345725969
    0xa06080609060607050a030804060b0409030512150a051c0204020406080414031603030203041103070906080c03060408041815170606030a0803061005070c03060b1009080c010503040809040603030801 87
    0x210351100b00900140b840792400c0500940d000740c407a070300003920a50101c0d621a004074400901d601c500c0d0b0005056881d1548142c00142012500d4041c000e04241899004000317001074030541054003011551041951151138410481001c2106482c1806003020024039402402150348980f104005082c1d501d090b40e06a8000d280d500542c030704050008100c0343c0e00010700c074a90040102507a0128081d42c0014411590850740800c61b51107034400300700f414060302100c0c40103c2d0381400c2429091405001c1060345119610134003d02010a102c501100e00356844515021001d250180d0000c01030480a00c84131455554940700043d4558850740d0422000c24013026101551034800401d540d45840610144c8848010004203080e450403841c43d03810103042d0b040240c103040d016100c028840300c055000b514000c0d1100c1c580c03105803504180e402540c51035400c00d41c00050821002d03d50303c15182d00307050b05110000001c03c0c144030080041c0d0b03411075030042c400c0c040300e0303164640201003c10a1042e002e07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 345728453 1250 345727203 345727219
    0xe03010b120d0f030e011b0f08041e1a0a0e010f050c04030212150403020d0314040213180b040c030212060c0a0e0f12010603050c01110c04020d3e071e110a060806 71
    0x41c080d442400180d000d681c20460703412f070080d10303050381d00082840c41508032200e00e00c80c94841281d040c0741245610420380e220300050851034080b00c06007034441e51800200c00341e180408110504010600b0789040d6a010f482c01e15070403581002d6140303030002008903000c0844000c0104001c260780001c04030b0480d055507500340524140c24040118000c1e05590080d40241100705041c14500c0a510400e002e110201511024144a4981b00306402041d00c003504c40c132400c801c06100f5414940c40c103001e001c4075000244418600180c0800e02402140740b00c00420140c400c6441d02c039a0b58a0080740c551000815644600d004404010b008011610048403240120644e1070800e44c080c02850540420040140401e0410801004025482002111071103036031801e610b210040e1200040c01249a0400558914400e046485980c50b504285940f1448010018500080d0f1002094417415859034800a162140c42c9807100107000a910030350740201e084000051490391003060240a040250345600d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 345729703 1250 345728453 345728477
    0xc0f060f09150c050304120b0108060f0105031002090a03021003150902041208031321120203042a0e161101090308010b0319020a0e03010b120d0f030e011b 68
    0xa285190703107118058040c4414001d400265008040e07902c1020311410540380b8107038980c009860544107a45054841018000060000c6141000202d0300101e40b900c10140643c0f4200000365140380a122010007141c0214040340551034a0540c0d9001d180d009000c2d00719403484d1800240181001e0a03c6400740030342c094006001c0e226442140c068030407000304201c3c102141e844004030755001604010000d034100200783c0209807160100d140f02c80380c0361204182401050802011013200d0030108480034810800d0000040285200700d01c07042600c8003100024507401c2c400c41d02e03414258000400c079030075581000352420402c0b82c0c440340d004e01030716883e007400001e805250898000e2100200031844000041c072481c2d4007800030356030008011941c0c10031444e0000120701a604540a10400300315103c400003881d160a0080402c2c200b81990040c050140e000d0700d03150348184010550050005030341d101034102e403298018824690b0100001d005c0500a80d40300d98186115907491400140301010700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 345730953 1250 345729703 345729707
    0x304030e040b090403050912030c12090901060806090105040513050a050d3005060d0501020f0306040605010c0b06150d0911030c030f15061f09030b100b070b0a090c0f060f 75
    0x143d40195003690700ca5040ca9041e00901150440344091068944814000d14011004c10072409403907810a0062588484100050086034001038111000380045c840410040d515155a0306044840464020899445d400c0303810441c0c122164000d000c07400345023454000e000c1c000412002984655179050010000d884862900802c041c21401e0402031300383d0004200d58450308240d80207500100301c0c1d00410501e030b480ca42242d11480c0580b0511101108012403031404e841044c0040c1820f080209070300c80540e0f6100c10b1840c0c000c2c4001e105480c01c050341c070804000402500e100301c80f960403c00854036681004210180c484d90381d07920038400c1401e10900c50402103800844543d01034001e01d80341c502c40b0428805004001c00383c50700f1a640032004c650100030f00c0241540c1d00e840b03881d020038650035400c0082c3e4a000c0180724040c1c1e0a5403840800100b44180c0031070b0009501310030ba0049a44650394110301415007480d0144c00c516002d2404030f00104114a10f0b42140c009807200c00c2484070694007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 345732203 1250 345730953 345730969
    0x1104150f080106210311150f370605040e0601080d030c0c12260a060503070f06030504020a050301061814010608010b07020409050d020a05190b071101020702060304030e040b 76
    0x8240010344c61290440198000e00c894240c0544a4103000c4810861900c0241c50b015145101440b02d2500e402031011a10f48401d0560b0040000b405114009101c020145515a84881d0b20400c42031203a0b920034000c03000341d210720098000100305121003c8868020742c1c0d1808207000f40f0082d400703404074581c1c403640288a4822550141d40301d00e510622183c60744640b030016541150140400315071850140320804012180c400443c02203503001d41410241102100e1103600018085da010f5241071200e4030a0001c04012241503203404901951648042105912698450b03900742d800c094001c14096991086020017a90300da00400820350310808440c1c11440a04c01c08001c5030908006020309903202004222850001e080851003a080c0ea03503ca04e40700549035403d0050300140e100000300a010302546882251005c560080240301c1e44403c154108050001e5050264000307490240702020b4060300c400540080c003e540b01c1c581418083d101c0050900c604e445145021940d448910301545 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 345733453 1250 345732203 345732209
    0xf090b070f120512040b041b05060d0b0103060305120408150408070312021902060603100e1b1903110901080318090606040e0c070317010b0d091104150f080106 70
    0x1161032254030040d115148400c4404200c501001004c1128012650305403400902070340c452100c010807454039007029041d80201000308c41004002c02c030104030300c3ea260010390300d41c4941244006105076a44c0e0058004000c1d540c4010061300802c01d602c1904c294503006002107540c1c40c03060396405d110b1485803941c8002c040b50010304140d0240450b0011a02c264088038012052a60062038080c005903070742a542602e600d100010307070116080103064101881000000d1445140a02440d101212503640320070445d0000c2c400399101038070f002c1e40d5960f403516548001d00e61245001c00a41c590800c4105039048054441c0204c80e0107000107000e101c000202c410401c55612480d02d4562400704114942d00083c082551010052001155035141107420600404a50444645d9010b46140140805041a036a02c204240c5000104010485002150010554031000151141c4907282401580c01d240b440c0036002440e09013031074014032000b5500c1050350b200ea11041640b40d5100c0e82d15003130314401c0c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 345734703 1250 345733453 345733463
    0x2409030a0903060218060310051315090e1609060e060a12030c0615090506090606031b2802010504050f0d0509040209031009200102120301050613050901060f090b07 72
    0x70100003188540c0e0103002e0a50b10382d82a200c5200c0b05500080450700f054540743d100b40340b038400c01c221a260146620b41928070f400428810114036041509151809100340c15805407074200900900105000c3e00d020503058070603140601342c8072206000200814094664464580c07004a059444c00001c09011500c2c071724030300b00018040b079500f2900ba04900d81e003164081c0d16000456070449916215402030300c00c0c1d04000480b840d00c041000701403040034200e1402564104144507040a140000110300307140716030b030b940c0ea0742400c44107c2920170101003190450b58200c03103011400ca0b030640019003e140184120f400300d1070003040982d142c0700300e542d03008003140c4100300101950070141c01602c95102d00806880e41e941841441006031106480d048400403905001a4456000a003403034010071000c0c4024144c0018801c0310b4501840180101c81c4205030101d41089403201d025420005003001500850351940d403108003a1034002c10009136004101d6410010641c0c0e444502075902c01c0341c02c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 345735953 1250 345734703 345734717
    0x709060501050922090c082a060a08091510031b0605041401050912150a02040302010c02040923031902061005040e0f0102130f0504020901120e010e2409030a 69
    0x404c180c1c405424480b81c4803002c80361100b40080110f96a451080010316401d00900007540e020205224805840c011101110110900c00b10950f141c0c002a20304c0c42e221820842240c0c1c656070b1800d440c00222403560708202c1591420010011010030096044038419102c1001c5d1101c1074a86000a0140c0e02a1070001501403204000d03c2805140b0070b0440301041c14041c0c600851600481c1c198034189105440a41c030030002d000200300403e102d80d901010080c0b0441c10b003800e41e0f00080201d240501c011b845261100103031000e0181c4c62584038003080150200c0400c424081410035101c0c1c0001c40301040c004205a002503a031400813034403e10440110316071000301400c100401c002000c10025124507840b030700240003103c0130248014158050159003018400d0303e4241d4903290030100f07820860045005021501159030031940b025031184402c039001c81c0060420328854014008601841620b214074441c0d41c040d4880040c800a141002d4074403282140c0e0743c16005540ca00c40c099218001880c1c13 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 345737203 1250 345735953 345735979
    0x6030607032d06050102070506070506190608192009160306030c0806270d0804080c0109061401060207080a350c0c030615040b130e07090605010509 65
    0x200c1e50000d40c0480c0404580c1c41c59880040101a90079014820882d0842d51220705120359a0104961002070200f1911540b50000d0355985c1d0303440e0b810240c10754800d04031804507414a220716401c0a000f8040c2c0f2002c840c915000c0000614180000080513980c0f420003149035071124240da8a034150400015103004031755107690480003541c160303000c1d60400305079a44902100107842c2c030f00703800003d00500005144905025204020041841200e10b01c043d070b100440c070404480110b82d06032601900d0074188241d5643e400c02143c98410410495915481d02d102d10007004240d40c4800e0342c03504208241045a81c0b2148142e07540c40c2c181c09802801e6001020306000520403540c81c1070303440c502103200101100c0f034000c9a00345000056030136030000d8011680d906113000c10481c0322041e0300c00310010140350900036090b90803404070a180c14062a180c502105017a202c89402d10078058000404002090300100116204d81090246152140c20560300040940c46042607411143c8020010803c0c068 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 345738453 1250 345737203 345737207
    0x1b020a0c1a071712090f060703270c091509060b03010b2703010c080103050f1b0f0d050d090302030609070e0c030a09120302040f05010207030f0b0720030403140606030607 75
    0x1000c01c4041c0f034120020460885945001003020707000e01c1c0220001d0000810044107282801c00c0181880c04061901400341c2d1508201c40d0000300c0082c400c405a0090318240c10303ca0b28400c0b29810481ca094285840280b0011b030341c50364031080300c82500d0304200c2680c031a0316031880c0384420b210b981010b000501401714207142c00c0e49842c0d961035281e9808104080c001c00800d0a6803964180700740810074510041050240c21310007608490006d2020f400800e04c10300f41c601403401c00b041c0ba140a8403501d080d948050300c407080500505a0410210340704038101010083c100c0c03c89002c101d000703001e1b950101e0101d4100207044000d40d0000c100304a86955a90742c0d00f039103074100610015855840d020f80601241082140a800404699000d0703613039400c01000d0041d15045a10460440d4800c0d00204003240300e08450b280020303444408a0260745541404480000f10701e000420034030140500110b12542c0000100212445124104940e0f41032424850301d85030125030ba9038250300010001854a8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 345739703 1250 345738453 345738473
    0x90b091609030c0f05040b030a02010f0809030c06010e2203050d050a0617250b0403150b09070c060606031404020906040f0903081803040b07060c031b020a0c1a07 71
    0x9024507041c0e04060b520b4580b00342080e42d60380b251004241c020400e010b80d0405005402078007000342c000b040e600d60179a0000703051a84200c24001049100404100001810300444a0318054103085407400c0d6164401040591030640d031a2181103012801d401c0c0103481400c1102000c2c0d01130f15168102800541064013a203c010510342e10540d03030f0100814401e2001400ba2080c941410040c510301c0c8000c100d40e0401209400800703d03d0b400024100040040d0070104c81c1682e40c040007511500c85428800c902610500440f960700c4082c13241040400e030790020f48030035110b019141c02c3c050340c0d40d510400d070100c4400c451001c1510012000150142c140542a141c02040103480098543c00f40e9418108507140008202c000800140c24400362102003d010240d241c0ca24000c0d52800c0c4c034040000c5424403070080028241c1e512000c034080124025401001002400441c00900d0312400308002d441c0d645080044031f101462060216142044d0071000100591082070f4500d40481d503161840340c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 345740953 1250 345739703 345739741
    0x60801090c020712030f080a0e030d0e0a020a030b09102009010c0501050a0204030b011401050304030c110a0b0d051f05040218060c0d23190e09150109090b09 69
    0x143c0314560001540c0160540c462079914007982c1c440c3c8200c030351454010720082028011401070360800d00d800b1220380780402202e002800c0d82e040010031148900440f420640c0802d400703036010b4000c03000017042c04001c07030202c1e1041c03c9410540f190143e06074561000c503000150b50401000020707007a0400905040f0080280d000c1c1410040d0800f1881e544030780c00c3d52000c42c1e0218031aa0042000c00030082162242405800c810300d0b402c43d0f0006400c0020301ca40402880a41080003074000102401403821841e500c0304409050620307200c3e01c0341c0e00409a03601c40700b103080e2030602d050700240000220980b000302e0f800504002502c21464074040001030b42000c0003000c03d00c840a0350b50701c801d6541c1c1d402840708414030390150100b00c468440180c059445a03203400024030076080d620071655901c00c102e40480010030010364214540100441700c03224188005a040b606150504c041c5c80c01200c03806000134401da885144403600c0300e410405a811218070a5009443e480c04200403401811182e040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 345742203 1250 345740953 345740957
    0xf1506010e04020d061e080102040815040813030f0c0819030302031005030102040906030203010b091b030703111b011b02060f150d03080723031501020c1801080c0a060801090c 77
    0x1c0031307411481a001c4034400d5201011400032900300d0740220301501d12090040c101d010003141080d203000c1100c0e85076501d000009071501d2041000a040080a0064401c0032181020200300c1c251246003089003030fa2100c9041c0c9031074410000010380c2400000750542080b5618050362841441c40e80c054000c0c1d040a80500c610b00c0f40369501141984092014100030076403070502040540c43e50060500712105092280e018904a1040041c0c02103000181069180c2044505550784d444d25070480003005034811207078900c000080d681c0c200c94040b4288452298110b8001c10a00c09040e0050030301038158280030016800103800103500d855501c1d40c4036400100c4032a800810100700000800e10503543e00202d0114a00509004440b503010420355001c0140101d0000e4803481c507540401540002461801c001e030f842008280381c0c2c2d00c28801c698440724090084000c001d040030116014450034050201507100300303c0040414609000940102c038580d88400400b40d013446a0030340070349100088482 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 345743453 1250 345742203 345742207
    0x150f0c0f0804031e0507060e070b03010b1804021b07060503360a030504080114130f02180a0609110702061b150c0307020c011403130201260403020f1506010e0402 71
    0x910a00d40300351345800519643c1d80e07654071034985c50404100d850300940100140d03c0b4071002c0c015482004101d038191000b1151070750f244d4403c8602803292040c0072a9581c1c00030300118007105122040c1619242c00f40d4a082940c8000b600c4c2c280c00c031501d02046800001c1800240e0203680c03a42d12129103155000340002052441c02c0b4100c040500d002940c00084000510000d41000150420301c1404c900184180c440c0000382089800091103180c10040609141d0450003c0c0c81190f80e41ca01840300120021107240042c541400044002c01c8584101d00390207003400ca260750050324503002c88182903801040383e4108a200868141d4034040d07640c0603113551251038201e19012079000b00b001d11510414500545e2440c01c840000d0800510503a540d0620101e00703103000c60080482c0999612501a4520344100155400102c07500da4001c2c030004120150b4011000384100690586882540250225070a00c002500d043d961600e03022070743c1414400700008a81158441c6011510b8540001d00140c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 345744703 1250 345743453 345743477
    0x51e1c080c01060b1c05040317191505011d13020903070b0d0506040e0d080106050d061e05012a12110f07030c06090602060a0b01020109050604150f0c0f080403 70
    0x1c0c21a00b5507000031000c54800304001003005c1e042c0750200d40c41096040144458200b654000e0480020403603072490705103001c0001030101f9003410403d40d07000c400d0101071008070f011650718840101c1c0d500a090003e01c450f113001203201000e240d003810408002d4181c0d40e20b130100750800002900807944136030703050240b0500003411070365240140840a80c8000d0014450910804200803202a40204142c82d04806040d00b00150401240d9044035020b0030115035600034842140c00a2034a41c0003101b2858a007820803800414a003181c0e01911020307242d42003140c034a420680443c4000c807100b03c40012915181000064490700c40004820f00c83c01d100d060201025082400e050141c083c0d07070341703a600c4071000b042803010940e00301340140003a09000031200c0c20310340d0007034580c1001030001782c0c2d4079100c0c0146800369100358001c01240e42c03c001a296a41050f2801d582c2c816106440c08110b01d00b840d800c00d100c00344c4d0f80f040e0812501c05440d03903007400d0359064081d200444000c01c00c1c0c00b400300341101e81d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 345745953 1250 345744703 345744727
    0x20301060803031f0e130210030e100905010b03061303050a0314011e17030405010c0f020d03050c0c01050901090312170a0903031404050d08190213051e1c08 69
    0x1460103480024281c00b81d01c03504100388654004c0f1607021030360079000744081c400039210300412070f0090f07501528a9020200104002c5d0b024110040445025100c0c008480303081403c02d51000000b41e204500911455106008060362007000740c8031403210207580040b0a00090040c801881c43c0e955a00317011802c400300300440700104409900040280411104200103a0342484c0c0034000740035180d000300c140489051005940340075074000c0505001e0000365660034000e90100244015900506d41c2074240c1c03507483d005165801564414140340300e8208425010340c000c030155068440103030340320503a8600d0340e11106040400b5507620700034070031403020072400700c4c240c04140e5105020560000c1901000c51500a04650190b003125040103400020300c000035501140c1e0016489862403c030a0340c0e20f03040c44d1400b01c110385000818080e1b01c0041c0c0c01800c28000290760303045510031100f0080c0300c0e400d40084c0d41da80c13005450340c4c1c0e032000d01415491070000711040d02003c00e9028000090402401c8080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 345747203 1250 345745953 345745957
    0xa120c0902030703020c10062312010c050c070b03090a060b01050c10021e040305030405010c1707030e090f0f07050a0c0c09050105040b030d050906180418031e050301050d020301060803 81
    0x5940000c0c0c5c00040000c1c00c83da042110301101d04205404000c4c1c1ba28044002d010b039141c4403c03c1980b41481c1403a52050340d994892204040c4000000704060320711100301030011350005140302c0880c041c1c0b180001e004030000e020340f8820900c03900640806002661100000c00f40040400e050200a1003080740180c000c1060107603550801c140143e80c0c1101207280444804642038902101e07070100000e00004101100b51011507800303091120f03031400da034500307034800303103600c04c0e50000350b06000c5001c900b4180c0c042e071100701c480001c1d101c000c01c507120600340700142c0d0700c21140001c18000c9040425103407481140181040b1400345012158004241d44241054401d544441304894940300140080d04d4244a440b402d510220010b01480520f5000a4051f0050054607440750f10080b808010404900101180c860001882045403190307400b640340b559000c4c0c1d0004d8000603032a54108a0300004241e90400d180b6640d1a500d00790780c40e090410170004c418140882e0507541b211000034122000b040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 345748453 1250 345747203 345747211
    0x3080c0904140f0103060b031f1a12010902010e09070203031b2215051207080a020d09030804031202160b0c120c03180109031b0c0e01090b0913020a120c090203 70
    0x5070741041c2d9417540c1041015903d602030040d1283d00f01d40180c00d00801280c00f5861345948003130300499842030b4006603d09100c603017010f05d500100018108803440c44103501c0004514800d8035000c50f004060030a0007800282101e501001da4070400110341000140c0288005192801c0541803a0203d0040f2540d68165810034149601a40450900845850100c1562034950b02c0c50241c0c02e261000c041d640125002400400070b100380c200114101803002e4046a41100007440140304601391458000e08183e001c071400c1e070000d44030044200c48107100d80200c030010500c00602d010301003003584a911014102804141031500302700051080c40344d0b078800a0b0303c5042003800f000c1c0c49240c400d020f401ea5044030140307886103034504030848000980244102c0f943c0304a410410108842c1454210141c50140c0c210070219014039000048859203908261307180d0b0070070f4448540544801419651501c2c02c104000d40c000c04c1d52505000c07065202d1580b45044d800340d642d034841d4540e568010000c0303a00a813 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 345749703 1250 345748453 345748471
    0x1409030c03030a0c0b0f040c15090b120103260a0e06090904260c06010603050702010902090a05221115040909110a0e0714090102100204090203160203040303080c090414 74
    0xc248600521001d90043c0e51308261389280c0b80541c4e94840c7c2c623409003d01c41c400d0310040020144984220114405045180c040d1a601d809000c50b24500210911044448030b070307101c2e2007814290103820100340c0c124009542d030382003000802068491143d074000c2250080000c0c40340b0392941c3c0c1c400c88802c0c0200d0080a841000800d03000c030030004200d8880051b0b210100c00c01010701001c00010b401811680c2610700044e1a8a410500b24094250400007940c03000c001d40078003e41400300d6101a0142a865041407030341c00d2420300114a24482c25000342034030764540200300c1c407410007484885110042043e49480e1545600440701214141501a00c00c007045030501c000f541468042e00c8090400c2818a40407440c000310300070059840c090481e20300c030703c001c02d00490f40d900820007000c4440e45031070290345450311220401c0094200721116408010500d12485e1014002300403101580d425994030b5a46968860301ca44281e840100c84e150002ea4503030034903041c042c0402180c1e00450082e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 345750953 1250 345749703 345749717
    0xb0402160c1208040303140c0a0605010509162114090c0315010302241c02090a0f0b0a08130c080a020102011401060c0201110111070503281409030c03030a 68
    0x80c101000c0c1c0d2400c642080d0442a9007690b01400310300c240e41503400b100d51620304120390144036403d1400a014006c003884080c45000c0700c1008010340c94004a040e55000c0d6054860395458003051400c5507100b00d03046021a42d0044543c0c0b81c1d0344545103100e4004c043c035001081501c3d00c00551103000c1d40440360000260800b004188051a040c0503c00c1da0488600005103a0350554002520309403148246028a00d44140801c17030100c0c401040c0e0b1120446107100380d114070012240e400107540714a20080c0715101c911700209043d004035480038240c41d40c3d582120305143c1c1070700e0240c89540d4050000d10159400c40d02d040005000300031135038007500042d0050001c06202e8400603007991310901296032445080790040c842585d02c28003017503180790246403403c990350281d0a070034010702c0b917000c0550701c2200c00942d1030244a40000182070b068502d0250210001d0035084010000c04095401c0c000030701e80f080c1c0704080541241c050001100014203880c0740e06001741c00030b4170750781c81024514003090708 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 345752203 1250 345750953 345750997
    0x1015090e100f0501050d0b09070e011205040c1208091e040516230d0504051c0302040807061d0a0303030f0c14030604020a02120a0201060f060e1509040b0402 69
    0x15010040d410104540d01e04220030b0510840300c4aa41e0780d406541d040210204441400548030b0b003180e4490718014040c03050a0603c084010701c481482e40c110780c080341c4c42080c1412020b01d54802d1500c640d4005110038020703810480a0900f00036903c10988007100144401d0841d9039a00000b002600d80485280c003011082505100540d1801040d5080045000d032003904e4460b001801c0d038080419031b0146100ba58491a040e8040b40180340100c80b000f4a0310007040100100059003544989805010303201d80c2c894244103c05a04ca5401685a90341054408014990050044686000211104503440310010000c0f41200409070b005034000b0b03840e540180207241d2140304880010070356207800092814818401c0103e88005008a40074035400161900320302d10902019611000d011280c598903140510000c1c0a4120340c0140c0071002041403000130344600071030049013161806440c03840c0700c0a0b840c5030b82d0080c0d0814203615800c5911207010403150740e140c0c4010045480307102c048030300d40c000d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 345753453 1250 345752203 345752219
    0x90907031d2506170105060a11013b071e030b0a0c09050f0618030a0803010308070201020115081f020f040602011b0309021e040912030f0b01080c12101509 68
    0x303843e600c00303000e00c04405200002c41e01d03220003083c103407003065443e1651082100001c0760003002441c031440d007035403900c803400c0001c81e022114400d480000c10250100c0f0b0401722a010b07201e00c50f542d00080c0700c1d4003801c0104006021442c41d038000c010340d1001d200501d40e981e150044a12411980402141d8de01d00403043e005400454540183c0810b43d05c0d03010212012010034002c0c42510307018080d48a10b040e41a080b86d50800c10b84000c0c42c1d201c0030003526941d580c64541c1240d000352604902550800308640c041c0d5403601021b8044500380030040c484010000c0318205110002050384540c1e58007008a50045503c0000400091465900008246605c504501503d1402e101c2c0d01c41014105000240981d8907001c1080c409200f00002c0f81604820000043c000c0c810800003d011403460602c4183c1250154089007500016100c20301c20203881c4001103c40c0803044a003103c01850601500041880500f042d95001c500001c41e0f4500c15160114a032b02000b00090320301c002500303400c0903c03202d2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 345754703 1250 345753453 345753523
    0x8060118060f080a0207080a0c110603130609050a05011508010e0601080a120903060c050c010506090c1c06030b090304150f020709051f14010f0203090907031d 70
    0x4400440c96448603820072000401c0481c440a070103003081954000705105200e540d0440d8803013513010034401e94440f20a01d025008040e014001d403800f1080d070364400303c3e038244102143c0c03290b984440c0600d8039419640c1d1320301c000e10002d04141c0c1c49126029a07600054000d11980482c0540b1407811007529252131443ca01703484e5000001201c03600b0010041002190006038090700a5105415081700b1480c0c41080341e6054540d400984030a081c4000e6551301074009004081200d0028000e00654dd658000c2c8007010300c05584041100c0f40411291403a80303203202c0f18012041840d2008601d45030f8940719031800030707825620400c05401c0007404108841d42d0b401380b0880980b203420100c0e8202c000203c0a5281d420034455904029180c2000489818003005017000a17060400101070441d12000706481c030300c140b515480c1c0450216035240c0e01c1280000140d4251030801004d090b200c1d41c0e4a0350441c0900080d98120343c0e00b20800e603840c0742020302486001d17a525022580854903440c030402c0c0c2600b40e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 345755953 1250 345754703 345754727
    0x90f0b0d0b0108010e160b0319020a05030105040e030a0c0305030604090b010e06010e0a030c0b0d1d0a0302010b03011107140307050d05070210080610032f040e01090b090a0b030307060606080601 85
    0xc0e511405090342103141c6d618045044482040d100c940725510000d40181e038441c4142c628007810305c00113061803171a030454040d505854044d1401c003e15054445001e41e40d01c40c64541101041d901d580020000c1e120304002c690106000c1c2000c030b00c120312039891a55010b001c2c2c100110f0b02c202d540c1000400d59000350443e0350002c084503850311591840c1ca8403440c00d2403a005100c61004009204140c07000c9940102c0009451960040305142d01c1c90303a419140d020302c440c12401542442d8540859290501400000c0c2c0c0301d40810390b02e0489a40c1d9084864006407100040c540820300c494070101760103106000d00f0960f1512039030359884080c41005011240c00c1d030440b040c01a42400d11040d86c4607000d040310407030907034100000c1c4101c3c410704130a0307504020303911841109542e10030307042840c0318100500101c1c0c24584050400d0b0740c8404c03182e401d030b8005504c0240c0080d08040010018403072034000d102501c80203801e0303a1420485407501426101c1c44c0d001040850111010b00c042940d0069400440c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 345757203 1250 345755953 345755981
    0xc0515030601080411030c0d050c0405152808030f030f010e0c030f04020121020c0f07051f0e0603010312081501200319080f0a0903050301090f0b0d0b010801 69
    0xe180341c0030002801502c40500041c1200042114000b1562000c0107003502c0d90300000c0604600d540c040c900b50b0742d514550b0044a0059041c00c01040c00f520710710250565108004040481d81d001d1401030400d00c40480c060785003021241400007401c1003081c001000c1001c40007020039030b24030307110300190050174041e400340490400d1901001039206042c805e076500f182c00768070641c1450703d4500040b0b07100c1d9038a07c65a01041c41a580c50310391031826074014035018a94505881d902c1d4a400d510b180c86082c80c0c4109600100b0b9001c41000390403000720fa8848044581c1000b1a4280484c1302003401034100340c0040790451903620606030142c0d004586181e220710b641259220810390000024492460085c0e0b0f80d02c00d42c42902c3e903041e401000d0054840d481d500403140c00c074121541c20b0081c00340806640d4102191039040101d40e10881c01d0140c004d50a8140e103d17036155901c1e00400000401ca242c103650f510303a586c0c0c6030000f0f039541e0384098111264051074009003254100400103084030010344480741 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 345758453 1250 345757203 345757207
    0x3b0906060109061b02040e0f01060b03150301050402030c0d031809020405090604050403141812011b020a03021c0c0f03080f15090406050a021207030c0905060403031e0e030a0c0515 79
    0x804000c4030350310202d080d030546021444424444405140c801680c40903208c6500f85040410040c078100b025510039507510003000c54140d48001070600302c074000d45000c0e405030007184680806007005030202c0f14451003440d000c0d1f41794450540c5c5644c00b12072500881ca550b1340025041215240ca41441d64101c54201d90400140c203156030064050300f403060b4044601c500100d03500d800c20007207503440d000e41d10300a003040101255500405000348902d500981010110840e0019124030000d100205142d1680041500018a0900381c488400c0a800c2408000b02400100c00103132000130104034481c800d4607851014201000c03015100400100a1105010604000e005594400e41e1f12900300b41c1203000050551201e130000d001a12455007070200104034001402100c0e0b42c55441a41c041c091aa9141c035002d48500c200810340c880d070f03c4050001108060341003800c107409640b6162038030703803401d0601002d607620300401e0424521140a070340c401041c00080040c1d0070040d07090720004011481c3c0303034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 345759703 1250 345758453 345758477
    0x80702060c12130c0911040f060309020114180a060314150109090b03030f030c07050f0318120c03010c0201020c0c04020a05071e050105040c031202073b090606010906 73
    0x80307803400000704221554680c103041c000c2031004084006003d054458010f002c1011003460b0200e00b03a10608c03480d0200c02d0003850004a0034032074810b8901081d8140e40d038220542c100100d0494942041e07602450404038491b902c03026a40300701d42440100542c1d2000f0035081c5501d190180100c0000b00540341d02c0181044610441e033b0b102c0d141c10260f55a803440001c030b40c00c2c0c41c03020a2a50003401100c01d107200c4000240408210080085c109061041c2c0861b509803c00406035603c0c0e00900402d503884000c034011054032440c0c02030140245d01c464004031021000110000381c25112003851000160b5400121207201c20801c0c850b11901182c20f0302d003980b40c041c0780c0b00020030381d1180d004050400f001c9078580000c051000050703141d415420100030710083c142410148411003043c03208842c00c00c00508074005660000c40c100742101c94029500745090900c0f035003418981205030b030395411807001d8602e8800355a00c21201c0c03409002d13010010902894031a0025100742d403030350006000d001030382e1105 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 345760953 1250 345759703 345759727
    0x6181f031d06190204080a05031909050d0f080c011b0306050904051b0a0b120f01050d0507031101200105071412010909110402160303050a02090a0308130e010303080702060c 76
    0x10f0341041a00b4541903195100d200304100034082c80e04158440d009400000d41400700010182483c440f8040c910b420b446000c070b00c01d48080d00310b8460982c00a102c120080e0100b0700c8085c000056501501d12985404446400503085820407210304041030100c0303d40c030481d9075241c42141d02400382607884111505158442070755410f400103014240d030071f00c0701900c070343c503200c44880350700414030740201716120801c1c1074410418450440f2205201128100009101d10700340300310014940e00310000c0d021640c150744a43c440b02551180c154103021311140020403100d05c22600c07541307504442000103150704040d440207096400c010300e0500d401c242401080c10b50001102c005044078003909000544546500d00714070000c4041c1c46031640b140c4040347d030300d4100c2c10079009807207480e10030786e8200071958900600b0403c038024001030a0300002c100400340002040480101070000c00c8800030f00c0302991b2409110742448098104030005010315052140ca1038040000ca0f4006807040010390420410340c2407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 345762203 1250 345760953 345760963
    0x507090b030c03154903080604150b03061008270c0406091e0606050724050106050408060f01060804030f0c1509020f03120906181f031d 60
    0x709640140001010035640b03042d84031240c00c4c0490140810f01d4010682c05400950300740300030160300c05031000b40c0b004600c41d120700140c602480d400380013000f0442a80c60841380c0c14030052240d0b410a603602c2501b401104142410030051180802c01e0707030b4030702d008401d102403400b0903160a81401028424400b003002010004400b44e048040d9244284030868410b510300110082d5081d0400e1070040f010404008a0300710005140c800d11003030607541a44154041281d12502c94140016402d0043c140020f540071303000581c11614400345c40350400c40c240c240d03044034801c1e070005011810004040190759420b000c00380c1d02011882040c8899071504002924160000307200900f00051036034502655230054503c000083c0d0000001021810320b03a1482c0c0080842000a03482103102c80b406100d0b516000542c80d19149e87e02c01c45608081c1113100b0b00c89103821800c6100203c02c00840c00181c1911025120b8005155000340410207600800018003240c0b0230403040107800b6103a094400700c2400010f4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 345763453 1250 345762203 345762211
    0x7080705090f0c071a070206090c10180803040f0f09060f0603050606270f03070f12150509010203061215010b03070905210d1b060b2b060507090b03 65
    0xc034624090351810643c407035a00c2250001880e190a94542c41e42880e07100009910801c12602100c15946445c0c90700c80d0303941c4420b012903901c00d44030611001d62a12861100b01d4001c14200c201c64030035100c0411a0070364006030006505130031f1520f0104013100c60100350a009089141007005440e04002c081c1001e8400307409400c09164458001c2100e036104c00003120351070080800d20310001080380303881040120049848504c03406240c43c41d22050702d1302044071400c58401034240503445150140c940500e0201c450140ca408807600c540321188415801010b00c62003040000503070300d180810030444201100340c241c0c2031b541d200054104000a54a0b21036040d911021843c83e141d646208040307410700040d0700038542050050300c0c03c601c018a01c958600708540e148055403400042414115004a011a4036a040c00c84030a02180440e2096201040c0c4401c06011014411100c1800d8540e0000400ea07506031080070303c0c45107050180c5d038072800f030b041002403922151541c40e0407800785030307400090 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 345764703 1250 345763453 345763471
    0x3090303071b05030403082b0501060e01020c010e04050c07050a15060b09011b0215040b07060e030a020d050d060b04080d0908010b010c020405060a091409102007031101020d0e0708070509 82
    0x9010010441800c40c2501e03888c0d0b055011140e2001c0030a0000181c0000e204a4000c00d4444003016519170003c40d85900d00d220603550b9984441d848010040a4032015083d2611040100304c12000b25400b804031222060044203804030354903076601002e003200c80c242e20009181200f8000c0350040e0381c0c80761f654083c00d2401015590840258000504900b600141c0c012008200140024810100e60058840b5901640040000d021104a4a1f0300ca00c03130b10b610500103810001d0300d48062070083c0d001d481c0303c218980000410030740b40e0f00c905000b64010f42280507203500403444a407401da4040c0781c02c03015001d8038009101c6004903500103002c1062480c8000e1081c1d40b00c0f0001a07050300c0f0214180010b200c0c1c004280b0800540410f00d80841100342d0714900c0f80d0084203c13540002545014145a0740b00b0f0384400440c120441c00d4810143e04185011000c106a010900b4070300344003400a8070741000031450018130072710080150b42c908181a032000c0a00e0300049000c100a0740c50b00241c5502050303003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 345765953 1250 345764703 345764707
    0x5060304030903030806012a0510060b071e0605100810140105011119080703080906010b0306120a05060f0a290f0d060c0915050c0a02012303090303071b0503040308 72
    0x116005231156411040b4030348620345136400344003c1e0780700307401c10f612818019070945801d040d2030641d42c429210035020f403040581e401c100390300008004c6041d1030030b4041100250010402c0595411042d50000d441114101131910000c0c031241c90148045907243c500003408000c00312442c800304601040c1481443d0602c16081381d401c2030b201052101c1c20803820704800c560111402440d0100d910f030001c81050740040c0d552400200b0131070000850034140c9226045507811680d80104115094030f140c144031203030313000f003c0c0e9200c00204100040d501403081d07100811001e00d8a0002d1038100c810550304020702200215140d0801d0a11a407075042c010810380b04c40760004100c0c408520826000755000f800c540c602061086c9455100b002c08040d260982c961090411012404071100e01031112011801d40203c00d4050042d8000c0710300032950150419160b880d20390300008007403203400448038810075400000400104581c8549801c2404200400810801c1104d0322159500d001d9400024400280 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 345767203 1250 345765953 345765961
    0xf040b06060f0304050106080708150a021e0705070e09150402101416030e010c0302101505030a060504120206090703121e030e160b0702041a040e0d0207050603040309030308 76
    0x401e011a140740c0648801d1554034245480e1060080006128030425801500b602181119000c07649003985001e406d901201a01c41d1030f2408000e6100b900b0314401450804490354820410320060100382d80600082e00d0341c0c0d0315203022900300d9840141400400c1e085014810400c06c2d41360311868002c4d030141d9500c11b40740032001095900101001941e00d4030200882c800ca00100c0703281440780120702c2513544141e1501070301d006441401c82000d00130056000b5041c41501e0205c00da006020480e0321001c4241c0b80c0e80e40d41c002ca800d080b254a000d4070b8403a01c80c001c00c0706010721801351130341c41ca00b9403000700203038a8030f101041d46400c11804000c2982d03180b07500f405040c51040da0700700d00725455041c82208101821501070001c12401208020034080d081688440703c0014503040300319000c14200300e14103280d030760030007000300740148589100c205a291030014540704c80c401d05808241d440000e2600742d440d0240a85810650303400309100342d4040040000080d8001c1d8060201c1354541003a03221912 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 345768453 1250 345767203 345767209
    0x171504021203040e07020d0906090b071506060e0a0806040201020303130c050405100302030d0f050307050702012c090a0b1309020d05101a010507080909040c030b0406050708060402030f040b06 84
    0x6200400c401e207444007040c0803c01c070480c0e1410901810403a000c48203108520300c0c058035090358520404000c1034a2010400038107013000000e0407510300c40d590306403240e000340040d40100c80702d9030403080004480c508040301d2800c0c40d501000141003407000918130351600d680000e42d00e21005280704442c0d50a000001d040007102d00b001c8020b420000c0040c0400e2500e0075070080e200b00c0d01c0c40300381e01c2807151203140c0d0002409401e8096820b18155201303451555807490513612544000812810040c80c000d00b1400704400d00300503141142d0748460b400c00359210b542000700c9510090612000d062500041002a684524501d600b52000340000b1840b0402c5000181e903d8223280e50141841c0542c1140c0069199a40c0c4184106c0052001d00c40300608054011201401214030040083c0010400f0079254a0828105940103100e000040d0740d03941c81e542ca9004c011810b40d011034505450784144900a6049400d03250b0105055501314158139151042d0000000050400780040d0300300300216107261 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 345769703 1250 345768453 345768469
    0x1503121b05070305060411040903020d080709080105010f06020d050c0c0103180210110714030303192c150c1605030412080d050c0f1209010204090f020d0617150402 72
    0x5400500799840c40f907480c03c1198941c0003c03501200e00f1504064155103501c0c0510070720306132942681c0145a0080b400c102a0340c0036801070a00824044848000100a4002d02031a07018000708510035811038a081000b0b454040c140358020180501444100b0902000007501403907040300340b80205820740c00e010015140d088400005c1c6d0843d04640c124580315070004803c84c0e1800b900b404403103520b0b41e0740c20f00081e0b9452984246901d5082040410140c0141c81e801a8091103410000600002c4020b4a00c034459a1001d0080400c0f10032011a0f4042400344050418680b000c0e10a00307584c60550342120241c850048802c41c0400c03004058402d100c1c6c100243c801500e900c40420310814001d0800b8450f640025010106503410000013842840b00081681e41c002c41d004001420320b40618400928a81d006020050f80e43d400e003c0021180079038043d19114460b02c10700180d0325030799403003040f054a003039802c6114120400002003040035800140700d00002040449914251079503c0040c1e001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 345770953 1250 345769703 345769757
    0x50c040506030406090c080f0307170c06011509140a1e030203030414040b0f060f160c0605190305061f09050a03060b01170f0103170d05010305070801150312 69
    0x4454048200030811000d907100c0054940900e901182461f40e070200290b5030f0340028255510f1f50414080d150009110035040c550751083e540704e05042c0a08050328900d8104242d01181103a19003101c203805054001c510b00340a00800303900408403070f507203202198040341c440c07107403036645241a50740c44190151454240040e66000303050381c0d51580e482d4aa401c813411441c0c080f912491900c800760686103400b00e11903059000c041c142908140d17242810044680120503003240306070031280002d00250030401c901c0d026200744d0311a60b450340c43c01421089288000b0801304103051030b10051096517030b200200e400c4806480f1012490304074040c00102c802c01c4042e4001d41c2c10840c0c4000200c20000650801c818806080c3d0b1019200c1c0c12601c4403a040c003c0a403138002a40c551a0010300214178007075446203e403944201040e24004901481c101118000d90007502d440d0880402444200002e000350407003180031520074010a82940c583c00052180d0011800501424901004a100381c40060380c5030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 345772203 1250 345770953 345770959
    0x51605010e010c020f06040b01050607050f15042001020705060d020f030a090203151506031003051f05060a051305070c1a04030f08010b160203010b100201140601080103080a03050c0405 81
    0x349400071105000e0300c01040b4810150003a030481417a01000001e4540c4144d40001003180720740d10b81400d00a4036400b620b03043c0c52a010b803501a00c1e84600c1000301e100b601c8040c4001d82407600c0d050520710000c22501298042040202c0d0702e940c52070b80d00041103029514110b480703969079488002c600000340b0807503126901da84804420407907203824503030104000e24020340030b41c0c6401501214552103207a00302c8a2288130186403140c040a810020003a5602202002c8204551382c2c49455962500c40c0ca505049507400704c400c003125070481240a560b401c00401e9488004031404c00300003c0403040d13902203000308ae5560700000341c0864030a200b4603003c140c000003641c5100c09161000d02e8003002c1244d040d004182d132950b050b4480c5102e1f540c00c0e4121034050000c1410031401c50400e00d01e11400303001c2643e0540d2240c0c40e005059480d03c1041e1040c1505030000034200c076006111a4a0810060000381401a481c1c010004074800320110359041c0010301d4000b54994400011200e940500c1d080070313030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 345773453 1250 345772203 345772211
    0x5210d0c02070e090d090b09010909022a01050106050d0b0307120804140d020d030c0221072408040b18011a011e09050d0204091208010e070c0b0705160501 68
    0x48039580200b10765059a80d41120003003035944d41c6000c9960344400d241c50000140c0421001c2080070101c40142101900515010910658808002c0240d8005400350300d00004000810594442c004555803010f125820092104c0c4d803610700c01500301c0c0907400790300c42c2c8140c4990030a03d40f581c06006010181c800903110101e210752904124105400c45e00039202e4104048011819a180c80f00c01410300c50b600414202d40300c1c18683d000c0301e8890116a00320380108141c3c80f0203032690004298283c10200030001070603000d18001400805d50010089480e03021030005220110302e40c0131102c0c41d0300035001b00c0c100e50f56440e00400700d081846200c11035031041d440c10100342d0403c4251800140700f081c01360b8541c01811100400551619a554200008181050420040c03810101d01981a2900007040060211402c1c0c8551000c245c6004005001500980061000403011841c480d00300d40e641c81d203049900781d01d0341c41402c0013501524000c00c1c000c000c21010142c0741c4d204541d110031a44031000740 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 345774703 1250 345773453 345773471
    0xb01210e070605070c080a0c061d0d050d030b06031909050f030c0307020f01171b0403020a030b01090606050705030708031b0d0501050a0b210601110604030f17010305210d 75
    0x41541c0c100b08022100d0801e451000580c03540001126421f9603042444414072038501042030703e4203054219805c0402140e01c4050107556200b00114048078000c401802d400c4441c400d009080320420310000b88140414400d00208448190a203068141d880100060a43c1325003080d0740f41145144c00361035030380310008000e00002c601001511080380b085d96150420303441c59005484101c0c11000002d10510500005034079071351104d806440510003503841a14142d125000304070b444010b0342090742c03407515040c01005180700c2031049000030120781c0781c05400c0140c03aa0700c130350701ea10400901510b603203800700100c0e02290600d260110b80e80e07241860b072580c607640d41800c84007a1509108180c481c030803c07000000d60b460b028040320307110b02c480301980c0f02070090015105004d51024282170b041004103014885080000c101d4140124025185c0703940013128180c0040c4100e128200710615895090010000140001071030018115144090100c4405c0d0780c9415003903000d03034100a00e000342884505 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 345775953 1250 345774703 345774707
    0x8030304030e03060a020c0303041b05060f040e0a1b050c010f050f0f0a11160c0306050f09010b1005040e070c02150a120b22020409020315040c030b01210e0706 70
    0x1403403060300d081d002d1350800c0d0344600d002c070300724000c07448243c1c265001000001e000919071030a900c0480f11441c9803a156689500120b046074001c0380c06000349070030005003807203003110001c44164080007483c014411204e803000102c10808808030160207120300441d8080d040b000a4211000494a880c4100510310b0201118800400300740c0f001c1f00355440c1d2101041d0400c03144d0103282250100460114509022007071207100801400e5010384030003400180c08000100d95008140c05210030340840419414500107042c212903008403c2d500c1268988600b10526400005680c102c4031143d80c041702565800401b40c503c82c03402c6070000d5000d4848030144002d81c4408014007070802103941d8401c09141c060110f03401f02e411448040341d001580307658a088903051484d030600f104121130350150400760703952440e1082e1782050383d52515800c0d030000e03002998101441000c41401c0301e4602400101004030010700540e100d01020800c05a203c0d14a81c4a20fa0366001903c000000408032620f06581e4040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 345777203 1250 345775953 345775967
    0x40312030b1306240e0f0409020d0605100e040b07030506010315060f030f020f0405040513060e0c12031801031a130f0509030a0f2a0f030908070f15090803030403 71
    0x540104c040c00385401e005000880180803451392860301e4013006410007204100382c081c0031071499a807140d1210000c000684610040e0300083d445140d02190900303007101c4140499039260800c09143d400e450800000c11803207825182c000c066403c000840307841e41302c0102d020704040139039680d40b52014600000e0655100700c151100000e142d9040150b44040c502c01c60680c8202902c0c000321000038441804140307425071140b5000004228400201c2400743d0303c8105684103000740005070381010142039114280740444080c007002c10000740d840d2200e1070145c0140244070002c41c50406940340300006400040c050b034100382e400f0050854140b0f16401160740042e0441201d601641400d01c1c000c503264050000503541120625250303e01c154410003404c450021b000307041c0d10210b02c40401504090012018554081c81c05002c62880d1103074a403e021301507101c86d912840f116803020f001007002890711111041034038480000000340e202600400c85501d5000e42181c90113004c00801d201c02c068002003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 345778453 1250 345777203 345777209
    0x9120d140f070305060f030c1203041809060506010e030604110a05150903010f090807260307051e03160809120307080405010f09030c02090603070b0a050703091a040312030b1306 78
    0x9810300441e900c400a0103112082c0c52502501588034001d030100510380010301d82d200e81d842e04d0449003050b5440ccc0c401d1556000b1050300d59803160350307200c42d841071085600840fa07102500382080c41c8940864008207a503820700501c09040154040d009032280d0340d424144400a000040400182402944006105900c12500a0b11a610345849070710003c0c5580030f007452a0b50444021070810a450b00d45e407a010403031031806802407452110600e12043e45e80c01540c065941070b03030707604d858500d007506d801e400458100c01c00f0585201801000301d40074070b2a00100f1030901e240f6001c011743e190b0844143c80c1081946122142440201c20048001d40c4209094400e902035002441080007080001c4100d4100700c03005800200b08440c500c0250a2100605804c402d0240031074403451b07503910394009143c101500e000009200054484140b551208503036000e0414a40c281d14140c0804840c20301c144601d101c01060383c440342d84c201420318040d5006c102520b074050040d0107401d003a40149001055140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 345779703 1250 345778453 345778457
    0x8031b0a09080717070303050d090f0606151706060a0e040507030506180c03070503040f020909010b010e040b0a03170c12040302183709150b03030309120d140f07 71
    0x14000280e0003441040e014004d1003035034064092181552011180c56002c004904922515840098001a8010f08141845005440006036281000c142040c500e041c0802c80301044180c03001040d40b41c5007800000d8000d0409c403601556812200800e5507018224480c00340c0c01f900d001d003044643d41c2c1580003940324010899043c00804407400000f486004241d4801c5100e41003400003401050044c0001d42c2c0140c01545190b032004c40d103900044164008513040d54080e51245646c98113940c0015944800d401c04450a0041100d0080400c4103941c1d00d01c8041c180b100220150440821b02e181141e4004031042d080c5d942038250800c01201941c05840228052201c080c00c02100c0c500003c00c0c1030048100e40b013134840f0303555410380c40f404500f1494184041d88030740403044540d01566103d001d04041c42190500c0c200c00b181c0241c0803c0b210200381c200e00940040080004080300800c4441030b5080408602d6100c640440c0c03414010000f00c01c0c0807a003144e6a8040c041c52035038062615204100759 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 345780953 1250 345779703 345779713
    0x1802010207150c060506121c08010f0303021507030207020307080601050118050918070f23060301080a14030912010b040510080a290106050c1c050708031b0a0908 71
    0x107a480d82c450042800c641600040012984000148076034100b075800c1103008022204095015202c10f041c55641c4410b042c044d551702030501310840e040020b40c1e00410301880ba1441c4a495610b0203521a5200394411041d04001c000007081c450180e41656210340d00501150207482d15001d250355034800a00540b8041400e0100840545031500600810780703102401840f41a100ca0751a082ca080100c40d12a02c0750080c5500801d41001900070384001b06101d4903045403442c0b00a28800070123850f181d01500030340040006008001f0000b8846410396402800c5111034202880c0d41415402909070355540304a90041e008200385054003e01d13079007103003107a041180e612102071035200c8058600c1056056000320b00c540c070118220790342412a03110070000f10100c4000043c04400c0366a400d030400004103070f0200e2251940300c0b0411044a07000c20b00309288000d4040703400b0180050180010050040f01d0020026882d414140c1c11407003904640e4000c903481d80380201c40504001c000d805201d60794416 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 345782203 1250 345780953 345780959
    0x304210509060c0115083d0c02060703151a0903010b060c0d090914060114040e010b0d0b03061512010b03010e0d0210020f0306040e1005240609060d051e01081b01020105250309061802010207 83
    0x2420314040844601d1010ec2ca40b0700c00e10340703281c04107410048015501d5541c6010001454550030014030b2201445005080080c81c0e0400103070031642c1c207400c2041c400d407038407403041c1c4c200c40b0700b490b0660441d0090030080d000d884195403c02c2144980d8000711560481d01f40002100303a403001c0507103110502c50300280050071110b4213241d40c8200441d5500218007014423040800d041c80605150f22102d28000811400c01d200b000c40d0079654020704518a90344203101d403008060b4103000c1309012080b009030551038481c1d41106000c03a8040a03100520a81c4d803114101c4140c3e070100f02d080303013003507074018107110390702d00484d040d458440c41105000003c50001c2c00820f0502d00002100d02c011001060382d03040c059848400702c007c0c10700500110548844400302403280081101003402444108010402c0c44440e54080707065a12a03500c203410b6a0404040c00b41c1c00002c00e1040007008601e00326000c030440d00c0780c011000340ca102040504013600d045140d01050074171055608a40c3c0c000c0e000c6550360f82d5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 345783453 1250 345782203 345782231
    0x320706030c030b0306060402030c0d060e042f060d0e0d02010e1c08010b0f0906030a02090415030f260a1709030304210509060c0115083d0c02060703 65
    0xa0f40c4080b0701d0b415001000021000c2c035042d07000e50b4005000b4032620341003804a015000c00c440c1c0c241c101550b4403041d001000100041c0116110034000d4101291000d0070786014491803503404804414421038003c2002c000720055544010a8101008100d40c10300401c000044c4c024040000c2a040398001c03210300c0324003441d2701241c0b1501110a50782d05d0240740e01c3c01a03158510b400010031154405004c00c203007079199487c100a94040d0704040401a03440d480c441c00c000455041805c418071a148000e0100045051152200c00960700580701040305091821303071070442103a540e0b0200801c2004200c0f007240d6948400c90f944030103d00c4c48004c680b0b0f01c0f01a034a55880c001110010841100c00c000b100703000c940101c0010a0010305d0030140d04208440e80085c2c8941c02410390303c0340b00d0b035681882c805005000e0136a2001000481c020b041d00345105088800e0060a903000700b02c10545511408101140e09024a030401c1c410352420440c0000565000351540803d0301d290300060b08066803089805 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 345784703 1250 345783453 345783461
    0xe040b06061e090604030206190305060f220e060106050d15051516050703151a010e0f0a0b0406020609060c0a0504090504031701091d0118320706030c03 67
    0x10b040510780105104101480050f6444900358980020060000000507260040501030700c0391400c0c080d140d103012950000381150b0004041070301c1230342c0050a00c02c89407103003449080203401107543e81c80107441c11031542010344605403603400c01c0d10501000203000d55000740600052280007000344960302c04140709003c20a50342c00340b1070b80030303c5425010360b003500c0502c02091014000001400342c14107a4981030305290481c1d00603550007140080706861036070399110790008a40b003c07410680d000f03a44800200158101d1300745070f02030030303061450030043c0ea6280b06c0c20004003e0b90301c0c00c03070391940ca401c1c000b900c850092712511049d11992000c20b9042d086801602c03142c581942d80c0c0e60501d442e082640d009010090015414021404400e407103040d02e40ca820b50280c2000c1c480461110401240f03c0f41e46194034810140036458800b9605408035084820030903160085c40e150112050b281e185c4a0ba6940081d1000e10122460249010004040389000880b041a18100002c000d100e80941c01d42d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 345785953 1250 345784703 345784717
    0x201050103050c120f07061d061c02090a03020a14270601230d06140303071e05010216060c031a0904030305091f0e070b040503030307030905160e040b0606 68
    0x3608910f40000b820309045020000c082d444400303c1e0102840502500d081258a400070780001e0300c0921034203007a5901c81e4428100c941c1c10750303c0928000f21041140c0c44c10641c4544105140d400040c4045140e40391601c2c2c0d40a160000e284a0040b80d5038000d24101029140071a40501d80c850a5000c04000300700b010b0400d20040141e81d505561000011601350356041c503140d040003003400c500b0312440180d6000e001c0f80303400404001000780c1050341c89402426560041803195108001c07031000603200c3c1301d58034001c5150600c4a16400b0140c0761140c061b0040540c2a5140d5000d244081d00388031541c0c104042142240c0c5003001407108103060f01040d0141d084000350859841c1e408600001e200c0c0d0300c0258404800000c0c2c50201c000070300380304584501e0070700e44d4003c50385a1204150104060010a00410881042c54600342c0780c4408203450b400010084024143e807003401f034080c41070500030380c11080f100c07070090380c0c00319220f014000c49150191415101e048075900012120305001d0308460030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 345787203 1250 345785953 345785963
    0x30609090c130b0a09060e04020a150212090a0e100e01080d0c11010e030304080106030b0a06030c12051501092c03161106120f1003150b18090303010501020d0201050103 74
    0x4010742c1140a5805405000c03030740303034000855041c0003420607030a20802020340250881d102c00e5007003900400218800b280c00800600f02c04603070150445030006190b0f42d0100c100c0c107145031610110400140003440c603600c0036814111440030043c0b01c003003211a90064410071100040903988800c4030a598054146980d004680c100c01d00c4000300b03800f1582007041040514201820400305800303c2e045030400e600003416607455110610402442010f07103940034400720420000705280d9211450b201c8280e00c503222542070070040340741c01e001062103407441c110840d104400195940760b202c2001000704e90407090031280c903070140034001c51405581204d0080c0c000001e509003100c04002e142004050b5000b00d4070180e050a111110380c449001514600d10034000c4d665080c545070080c8500710a0050902503942c002c0c500074400100700d002d81c3c2a1500400100240c2d038140c2e04085850369065003244181c40c80110100181c5910010046041e180d0130303401c0c0d90544000300c80503402e80e07100307000c001e02c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 345788453 1250 345787203 345787219
    0x3150b030906040807240515090f04030507080408061003030305060418060b0a05041b030b06210a2a14070803180c180106180b0d0905030d0c0203030609090c 69
    0x1140700382c000b401249001d00485041401560161b20000d01641c0c0048000c0b40c8038130401c02d03040b0610488202540c3e040e100359000340382800621110800041000b010b00c10301080301003d200c40e02c0140c8c1e0242100404407519400d00d41e07109460740c0b01601c000c40000b0b041800280e11400c0034041e070f0488680c680b080740280c8174103a68480103441c000001f56000004000c0000b11740d42c0c0c50160310340701e10000d020420803a400200060a84441c002c80b14003503041006035801404041e42084500d00b01501d5a079059220800c807a4040d0109600b5509005030048a004901c0c0400804083d5114a511407104040300c90000a0850203003100107841e10006000103600712103684172000a600c42c240603501404400701c0050740705e0038041c02c811a200801001407145d20b030042114240c815800269036002403a042c00c2d103c0510505000040050b02d80c000031081090800030344944c0014000140300040360044002e50729002110001d1182d400100441c0200c0e401088501d480b84010345641d03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 345789703 1250 345788453 345788461
    0x3030702041e1505040f0e120a020a0b04051e0c060901031505120703030905010e090604180803070203250201020706140c15010e1f05100c060c03150b030906 69
    0x100003840ca240d02e4074040910301c0b60b100d00280c1030380316511241580300a0402824204010701c0116030802081c14001032400310400d0510300c000440500c0d18500700d44081d40c1e840300f410b00700c0c18a0a003000050020242109101c20060045030020703c211002c00141d000d01e00385036066564800340125035412400130420301300e4651181e002030f180c603c25040d51010031580e03030010030719040481400050355040a076051081541c0000701100401c000d00e407500d50140314030001580d4130070181c09c0a2155070f480c0000c103007840158000001031a0015a0103071240b81c2282c0181d101e41c811000352260022420302c541c420245040344038130145d0181c1c0144a5642041010707141c00296040a402c4410b060020200c5c0c000d04004c105e000c2051000c003403004d03500d03150810501e04005040c4450b8440800301010404c480b2208540449500b1158003000d01c0c107101065038030401246010b82030710b041404070303403110380c0541001a1050314151502c010b650790b088100740500050b2504403691300040042 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 345790953 1250 345789703 345789709
    0x6080601110304050a0f0e0702060c1602130c0503370203090f070308190c02030a0210030b0a0801091b030302030307050a0504050d0b0109150b041511070308070501150503030702 78
    0x1d0401d1003045001c603440d2680790000101c050840d40e00c200348104011100740545820b01c500150001403500003401c0c1801c0049425089001d9035880542e888a451040000e5549482a40c0d03140c1c500c0a804000000051000401540c002c07220b1041d0000b0b8a040d04106804946170144221042c14040c0621020080010b0180d440036002c10854400c0401418090005111680c002c2d0b00c1030201c01c1d50b400320241a218120940070074031040c015a10034600142c0c5000c1154070480d40d040303803504e088420804e41a001054420307029a0072124080f40401c1d0484150b000743c446500507049100c00d5038200c50060000401d03804000c0058006101065a0038000c801402c440d800314200701d0308054955000c1a80700c90128001c0d00c0d81110b06004000341082d83c802c3c08080c00da916851410a81440d81154491042e4072480c03072180c2201d2a5013120b40d2203050000050690710003070310000c03980c80c1000c454035008500140c9581d4079200365005c40c401090800022070380d000d0059424020326400b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 345792203 1250 345790953 345790967
    0x70506040b04020a05060f0d06140d171c0905070503030304020307030303050402010905040903051201060509010516020415080a050c0a24120e0f011104050d021e04021206130606080601 81
    0xb04980104000d4004205135813503101900342080c90440f09034980c0b485051190965100c0c1d48070b10400b80050203081915101c070380d1071182d200c1c0c001000043c0c94020459500e014071504880b000201c0d00483c0f003540000d81904060700a5004000301e030313506c940b10410580c582c4000d46000f5030651200204000180c00b0307800032680180141070800c1031aa82d01d0116007650307400303042240090f100044002484118007102d83c05010740f0b24280d070030500200d002030b000c0e00c9810402e41c440d503841c45445e000c540c1c5036007104102681ca03a45034a15940c1e80d14040d6580c40c010303075044402d0b0042104005040c10320f94108070440700040d1301c4041c80300303003000043d0300c0d20f604810800c20070000d05410030350303240346006920160112000905e60824450b10450840c1d00b07801ca0003040080820040010f9907031190403202a40d01195080f1019100d120f00901050042031b460350460300102d80c04003d100308564003407003100e058604602403142d1115903401c403006400303070401143c00c00000c03c04035445920 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 345793453 1250 345792203 345792211
    0xe09040606030609080c0d02071a3108120903060703050a0f090b100605030f0a2403050a2901092f0408070f060e0d03050f03040b150105070506040b 65
    0x68009034482e02c0707403652400d68610350000c0e02c8202c1c0024881c50b46840822a8403040041e0703101500c031490506010000104a0348001c8180440219041082c441c9811016800321055190301d40b000c0b100b14a20718840490f48900328040c02048182048201d00504a03820160002d020f840c0554623004264000c0902504204d0704a82e96211424186210300c02c64504900500d10706210340351513080300c070110045420034000c001c800d100b400a000c01d0b41c1c5185420a16814010924048418400c242e4a404407407400b00c1807090761000062000216200014500550040410361800304120301d0189000003201c01384d003400c0c40100308414090340a074644920181c0b8541001d41c0d10500b40e9407240807c00a2009503000040c1000000f4040100c0d00081c500c412110b1071a40c50400007400c104810400940141c01118600040620610031503e448150400ba13036100c1c1860b052540c0c41c0041251400b11000003848040004e42c018030688040c9036003c80185030039a01c69550350712003c0058 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 345794703 1250 345793453 345793463
    0xa1401051315091e0507031e030801120305070b0403080906130f020112110a09090b040e0607110a17030709060815010e0a08010e03070b01050405040201050d050702070e07200309010e0904 82
    0x410f901c044c4a9030910f1614400e010714018900d007411402c200c2d03c0380200f90403951101102d104100d0000350840d01c039a04450448225074441040c904080e10f10b0f00c20000020700c115100010401010382000600307006074000700443d80c040c0c2d10040408081c0403260f901030001040204094015840380085220f03412801c01d02082602907000d1906182d00a48920408600080c500781300040c0c5921071603242d16001c41d0b00380062500004001d440300001340036202084030350b0041c03d0600b001008100342d059407100380e0410660303152001c0341d0a504284d07601c1c0001000244000340d6240704054190040020300c846207004c2c0c3c01c0340019242c80f141d818650f508400801d00000300b8090070320035100d6407245000035541d94075243c9040356020505801061045140800707000250b41e02c40107460b6074940303602c00054591940b18050b45002226801001014404400c01c0101d0781d0224041045080380c60042d904030800801841c0c49019420f04c090001e6030170707441c4025914051a031250454020307 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 345795953 1250 345794703 345794723
    0x21b06030103060e0c0303130306050c090d15090f120f21020c07050904060b1f090e130204051510030b150a090f0306050103110f0906040e0f0a140105131509 69
    0x1405c0401e00750342000c580c0c94201c001580c070070010301c0800e0242039484505800442d240040c6400000c00640921101030b1030001f0103150b080d15048035500c0542130316004a10030032010840d00d8103517042421101c0303000014803200b042c4841e89024a65985c10440d54419101c4580078200d182002504400c048080700e1080340400070310358850070110390055002d401c0206040c03050800303004c4c10140ca18644c04407440304d03240340581194003141020a640c1003500506c81506c90f00d540c5454102052806988035150805100074440c2c2581c20082000c0240c40f01f140c21203041105800b280c0003203081940210540da480c032010702c950401080340b4000c40c2071034260942c07103190300b100c0b0245c039400031180c0c0c9543c3e40c0140140218640c0c0c212100390101e500b6405031038080045074519002408080c040e0b130700c0700c04044030840d080c03001101c0c1031640b1046900448141c2046041407561032554006c551a000200390b000c1c0e05000e25000721904590b0759031000719280000c600030a504101a2442c40302 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 345797203 1250 345795953 345795973
    0x3030f020a080711150a02031903140a0c18050102071802040b03070c02011b08120907080f0c0a090c1b06021c0b010305060a060903081c1b021b06030103060e 69
    0x16400600380481c080c00456039a913110205000101e400d01030392140c104801e020074820b240e80003040303c4080103661604480f4105c03100c0c003a07014014103069040130a12000070010030141562082c200750b4010366540180d502200c28501003001d0034080d040c0140c005074814080d51103031160034110180e00c004014900b640d40e04d1240c0254100381c84000002d1400e03110036041d907a100b03c004c2200c941c10401c0b90018403007942d400510b1310a0480060702407640000181000c2028420799000381031910641d082d084100394a25101c114001085218a01e951400324091442c1c0c41040901c200b01d80368401031381800da9140008920101003264034031707001c0203c400104000006806030002240c00490590840000542642c4c8002d2256028410209082002542c00704052044030f8120081c2d41e51181007154400d40c440e04007076110f0b451420300180b0208030200074020041d80c1c10603403c2d5100b010b40360303402030800700021070100e505c0401840144003142840d40441c4403105504112410003076 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 345798453 1250 345797203 345797213
    0x50f16080408210411030106180f0b03010c120608010e120705161410030c080105060f19050301051002030a0c1203090c0f080c0d0c0e0727140603090703030f020a 71
    0xf80c8118500f1803407040500703020130842441c492003046082100207001084c01e00e170207140c1100603e03409088554441c400d03411102860f90000c441400090002d0002d80318800c4094104108501c6000e86070b4601080010b21041c1031141c8d548079000d88000d000008a0341b000400ca640181009032440d000320248000010b40e06c080c000018030880460301d0b22070f0003100402000402107000303413040c9030804040143c4540d0010281d03054580440d0700e00e03100c0c0d40c0d420b04845540508070755408542c484000f030050454010707018604a810880300901c1c01c00d0a035008984a0181141042c04901040c036840300280d2070406181401d011403500242a0080e920759441c0110035601c10300c2054516030b011300125109011050410743c05864120144620355507841510341a44038062340e030100280441c107118031440c0814801007a0284070081d0350601106081c507080984290904003030f4800e0b94150a0030f00d8410381e841800780300c001e40003241c03131510306481d9800d803040501d0840c0035070441b20300012 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 345799703 1250 345798453 345798487
    0x30c03090f060201090b0c0c06191e090c0f030c050103020711091602010e151807050d0515060103270602040b07031706030a050703142a0103050f16080408 68
    0x459002051000d520b051005524102800d0041f414004001d0800641c00003c2c0480e0030044005000d18011b2480c401840206000130702100346c0481c602084070750038265044514024040c80c055809155a182034100070081888000c040b8444000c040100398060b90181c107005005801e1a1030f449140300c00590b100d1812121240314032a02175010391070710b42c2403060080100e4500018052004c02640c24070748544c0080600164501e40130081907100003d0243c60020702010b0002e1400740c901c0e10380540c0b04c50913400011211200748000810640c0700340200501d8a041c0c0703820920f640c00384c90f0040c0581c01010010b59000d5000c0000080300565803006042180c020750720204400c6044c0e4500d0f40c602c40140855100b0f6102940302408154080341450490303520240004070b17920356400081c00d2100190082080c00995403544030403c0c5034200507007468009130380410403561450900703403014809440800b0b0b20140c0d01a9000c00300d00400240c1d420a000d41e00c000d0030512854413a002c41 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 345800953 1250 345799703 345799709
    0x19150302031003080a2708071e030501060e0108060708070c0f020111070b0c0609010b090c21010e040302150702071203020a0804031412120720060405010c11011107030c03090f 77
    0x1a80041b2160300d030a0560559010072860b01c000054103458a0f25803a6110028055003050400110009214221048407440216440300085c0306456489000d0118010240324000030f901a0074002400548280c2c1c18070b00c80c50158071b8000081d4a1501e844003c00d20001040741882545160f0307130b8000104100b19402407105041d41c0d03607141d202600c41c0b410224007400a007010381c14502100e085a40b141610355000039105465500c620710700b00c0705c1d1004014070000610b0300701028000300d404d81180f20198030843c001d4007103500001003190011411202241c2c03480c0160040c01c0d06000c08583d031109481c09a010748101d07a0b8505554507161019442540100e0b50081003400c520080c2030140107a1307100001c000714940c14110031101d201e00d4194010300042c20408601031700b0b940d1407409030407144441c0054007181d0315480c241c83e12070b0007025988030f20404107103004542e2010143c14000d010992154000d01030400c03009940030346c0d051920f62011018044031150214030115505030b01002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 345802203 1250 345800953 345800957
    0x3031d010209032a0108040f0f030512090a030903080c2a090606030717060109091d01050907050303070803060d02060a050304030f110312180a0506040219150302031003080a 76
    0x9140b500d0780c10985080d42d03840610b042c001250303e03400e140050007070103409402028207000925035201d141100c00200c59901c0204001001200b034014160b0020203441070040729180c0110544030780c03000740d6541000d094024001070080c8030a10005405001909041c000300c02228130900c1c0c41c444030103c1c50070440c06440c5d172104c0208004420300d0a0001d680d080002540c4003491410413020081001c0181040e45021066450214015034031a0b0180d00003084c4442e410441011100380d1404c41ea007110103410190341c28480482d0740e203003001c9603100c12104000e008600c1c00402d42c1c1c40d81c0d62504020105580507004051440150322210000c00c040c04565451503a28a498a405420043e00504100410468440c0c13281007400010846403400e01107400b110440e50380703980f03200d4141c4107010201c5090081000c1c0e07400300070340056403602442c4200c0c0e002c0c0c21400b5030a038610300760b0301c07503c41c06207114090f40380608607038000c0d801150441e80d9085142d050035241d03101c030704480d0301685da0200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 345803453 1250 345802203 345802207
    0x7110301020d061d180634030906060e060117040507050d0b0106020f0a08160203010603060608030702030c0306090303071d0307061707020a0503030606160b01030803070f0306050d03050703031d0102 87
    0x5080d1125129035101c84400b6011036540c00417440d01d90340d418002c200a603040d90144050102d188143d107900c52031441d040c112454107841c01c1e8018080c0c1690300c01100c526082850100b810f07100340784200c0c4904811b0303543d05055441061690b24591703000d04140c4050081402c0421182c41d40c0191420450145802803915450420300030f18200b000f0782d010003690080c10062000601c414200e4a84c000d84030280c0710011181d000183c01020a64402084c2c14074100c000a400c5030040301405d001400ac8040d00c004107502014103445d00ba045500546a4000b040028100d900503042001200e094206251300020320f000403a03c0d0070003a40180c4049003004401000300b000501c500e590080300e0344050450309074280e444560301e00002d0607682c1702e070001043c4520094500b50300c20064a4014441898559482c103240e1410740c4140c6009002a10005880350300c4c80c0030b4041d81c400c5a0300500b40b00c0113001962422140c03500003000403001c00da240c0206117800c003800d490b104018405d4400060f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 345804703 1250 345803453 345803489
    0x602030a080702150f093a03090b1b270405090309010c110d0c0308091c050c21250501030e03040e0c0702060f030103030909050105030307110301020d06 67
    0x6090070703100400d4801154011342c0421301c080c04580c030050b04250164829045074070f9507020f036400c04031403801e58120303480c255444040100c401e501d100000002585098403291070324401710241c030310248000c0c0004880201140301c05010030364401282e01080c80d181c0c00c06c683c1142045480207034600400400844500030441d910745403281c1a088010003000310301e0005031f030307001030651080c012000e821400006900089a29440100141180d02c6803603014038640324984100030313410010301c441c02104c00d0b03041100240071400503146000d400a004004810411040044000c080d0b01031400d03080710540884003000080218043d0303004205480854810b460f04001c61401032039214034105810280608103051002c0100c9040e600103140c02409aa03c01c50103403450702c50031100a410034400108246800b038001d001d141a248a65a071a05071030f0795250000035100c080c014154107030020041800090780d900c00d45041202c002d0000350410003030391900c10440e0960b502112800c5d030020311203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 345805953 1250 345804703 345804707
    0x180308040e06012604061104030302030301030c360f0207140c0405070504030f050304081e010e150705180a09020a02100203150607150f02091c030e01030213030c0602030a 75
    0x402e5000100386031040300c0e04030540583c2c5511880881c020345820140c404101070010a03040303094044d00c00c00b8a0780d0b41d030b46c0d2460000e40e6940b00340b1054548190b41480491903544031440c840f4946502105004602212a001320b0710048491184150595481c40b2003040301540c006003801a004182125841d90100c01a5003402e211701083c42c815132509042140c1540c12005480c1078941110428a0b10403071442c0061640c810f80d0001103007407051800c10400101150508507104000c1d030024009040303e0140b00f41c0d9007100c5680b000d2007140d4030002841451162000c0c2143c010510300c41d0001c80410004100c03942d2550308004030142e000160300c844d0716010000c807200103007240421842c502d012041028684005200240301c2d100000340c034004d00034400710140c20030000c0c11081022038012074581c4000c0d8402000d40303005c0c0452283c4082c032611555800305480740c1540f5291041d51000004600039807015500404040c46c4da0000b1000c5210550441d001d0301c07241e002155103810320040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 345807203 1250 345805953 345805979
    0x307060e04050603010902090a0e070810050103021e010837020a092102100c050316020112140f1b04120204060b1e07031115010e0915060f0118030804 66
    0xf41d000780c1c10035040c140181c4504891030780c0413907120300005488445600c818100801c651140c8841d205090018116841560115041343d200f11016801006a00541d000c80580280b883d40070a11480001e4000c00c1400c0c1c0030802c1007114481300c50440002100100c8440800b0200191103a022500c050f825030449400e1003d41011079023044d4101d606140610708860100d00280103090300b94164140c0c5e405032060058065208081d280c80d40c4030540e01c5407603c940c51900364009082c44d0714440c00c0031194070510038507410310000360500e9030300e242c05400c41003805001003000713544611502c3c000704038441c0584040c00b80ba400e44c590b41d0fa91170040200381d07210ba41003052010741c10000c10310414101813000d02e0582080024545884007400c1c00c1e1651110708000340740030b020f40d04600e0701d00c0b0702c0c40b80c01c60306944403d204540c0340d846214805a9421000c079668440701038090202e01e05240c1070307008080c45079052522980f40441c00e1100040000c15910440380c0c000b000ca030500c03d200468135 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 345808453 1250 345807203 345807211
    0x612050d0807051e0a090e040602030f0a0b031020070309090617071406040b0a050307021b03120334031a060d020d060305010e0a110a050315090c0307060e0405 70
    0x10b0854181300e13400650040004400803078050300d050005420390b0907401022550020603c21103c620a0300c0c15050240103540111017204444a00200044a6400c03e1013410580c2602500070145a900350040c40700a150b403180c24800c01c16050b0100710500c200c04001d100540c817940c0c441080d1030bc0d00024100750752950b044100b401d0f8041040e40410310000420000326001d160024048441c80c0380403605610543e0800c0095a40c00501001481d40080056005882a9007100c002004c0c1a98908105884401c2680c0c142c1003400c1040f0b0035070381038000d946c2118a14010003c81c030300500b0004d10305140d00983c038121204880441d8081764152291004c0303406000720542841c1030401c000791403446100d41001103254040341302c0882c0039495005001540d4040700030481e0401c40840309589084000c0121481203110280300c0c1141400d0003120101d070342c041c00800c00024640e5440c1407640c00200400708610410346c05003856901004000700900b0940c81c0c3d00d21001b800001c0c08260b9900030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 345809703 1250 345808453 345808457
    0x10b1507080a050a110307030f0f03050c090d03020309030d02010e122d0912060a060803040f052b0b0709091505150403050a0b1501080108060a02030402040612050d0807 74
    0x484a200803801d05001c46485000341d152641d039445400c0c1c02500c2c8003000b5010009030344008240d0100f015000031059081400070b807242c603004081913004800b601c034126103d0619100038000b229560400d016800202c0e44240140d0b410b129040e00468503104003c508080140c0d11040c43c02000f0f40188519030040155090030f902d01036900120040804d9508042c1c801e000036440d48100d800740300020f0307034410440200003261038070084c0d01c0306986007000e40c1c4c41d610f900e00d08540007484801c0081140d04440c086179103588541c1c40c0c081003100103104001c11103d5080503481540301002c1203940050007620900c0102c0c11070400c0903009100d559290400541680b61800c1d8028405038140000d0494404503882e01081100c5403040629018a601c010801d00c5991141801c0004030020f4521642d5802c0301f060341c42103c00c00448407070b070080c85484c05681100c40824104c1c9260b07002154441d002800100b0900d6664130508000c2406005c2500c1c070750410100c80780090740c0041c04581281140c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 345810953 1250 345809703 345809707
    0x61208030114180f13080703110d020304050112050a0207020a0f090c030612021002162403060b04031403090618010908013c0c0c0302060c1e070c03021002010b15 71
    0xf16100086800160003081c07040341c000001a500b020b0305400710b205590103501d264032041e080c035000d84000700490030341d80030380505070601c504070381300000b900e00700c400595074010020304100c0400e001781805028040125000c1098202580312886800020300d80500800010b80c07501c03411030f01701c40410709107074101130400b03800700b001c11740c3d000f03c501981d50100c410b0340c200b8102240681c6011030740c02190032140c026260001d141d0000c00c0b40c0e102041c14401000903a0700100c003049048603000d00503480c0c404010b00003800850b01c1209210078041d030084c202c903e032603081c5001a54503004445480e401d0070354200682e502d0350b88031020400401840000303000c2400c8030260681600000060102844004c004201e00b0301407001c1d4207504144440010024030001ca50001c08070b000c1210160090720170b01d004617000d82c40c014129400007440c00018181e1440b021050001c59004490603140304d49404004000360307680300f07000c000c12400c5400005074010b59100703000d1400c1142184408c20360007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 345812203 1250 345810953 345810979
    0x1c0c03020c04050609072d0e2e1103160c06170702031c06030f0302060103020901060509150c01140a05090d0302070b0c0901021603050a0b0604020307120f061208030114 74
    0x900740410340c108080b1f0820140070501d1501d100946c03071091030501c0121041080c070030141500000680c40313194080e911800c0c0c68104591341400b454055030006901341c60066070040e410712a039005144144c4140c1a0392614260700b04e034500420390b0b15020b844041601100300100c541080c6241c0c0c035030702c001c811022246007084004c0d459001e2150080e00f1500e00c1c1124180148080d40844003540d44581000701c900c2840c14020f644404c2400124003a050000004c40d005002e0003e64051540082051020764070200d500f502c2a00117580c015905c1d0b4a5403201034600e41c41140203442400485000034961030318285891a0002030003040082c0352041001c2804642e12882c1c86a00100d103410b5282d8500d802e90040786041070007a95495030104200c804002c000c0702082940001d80150700c0300049132640400c020480c4820341d600008a134000c19000c10a0410f500702081d000c0c3e14050000d0306540c2c52001d038041c000840340882d000741d0700000600100300e02d40361a51114406842c0c000f04128 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 345813453 1250 345812203 345812209
    0x110415110f0d12150303030216020303030a06030b091c05070206071a04030f0e0102030d051503030f0a0306051807210c20030412060f0b0d03023d020c1c0c03020c040506 74
    0x40d84e8040034007010740014041e41b04501c68031404c10110b50140440f40d403868550368060040c0400e00080f10b22900d51310200e04045c100242c41c41104254280311000c5559540b425542d80d44400c008a0f00054207010400c045910401c600040d031000f83c0014420780b40c04e260081020508114240500c070112600c2c0400340da0001c25104410b0084400103401c0e154490214514254040300c2941407200040e202940b44201028280450f983e0b10241315013511101007014101a020800c0081d20f1440c0000700041e01c100309604c00d54465010b40241840300d28041c4060314880031451010549100001c0700c0c800d0111882d007a070341021005142407608100080807001641c400240c0703003070340b90101c21180c042d40b58003403102200020702005207000945006511800304a490304100000083c1c09141e001d490344100e8420220031109114210180a01800035042582443c070644280c2c1294001890100c3c01031034072035019103034084075980718580245442c003c415198000c0c0e0030b0209100c1692 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 345814703 1250 345813453 345813491
    0x1802030d050c150a020d02030112060b150a030903030905061003021207080604030518040609060e0f0405030d02071b060216080706020d0804052a0f04110415110f0d12 73
    0x42d0030307440d4040f10b5449803c00d0002a005814100c0c3e00c0b98400000002c20381d140c4120703600140c1c40380c9014804903c03400c0402840008100304008194030812895640600c030f6440341d81d40b00d201303040000d2112003a440c1e1501d8080c0c11103500d00d140c0001e00b814819031410a601c21030f01c05014000302211403c00c0c0d0390390385070000580700a0921101190035407144042100b52405001c0142042120540e1101c244001c2c000078852601c0e542d17001d00200b40030004880610b88500e030020015880d004010400030300079405024199182c40e00580c41d00304004031860000001c04041c2d0090166298562100d07410301c2d01940081001d42c084001000303402c0c1c0220340c0303512044150500c41c9850760356090003070404035021001e0681c540c0d508200c03c0a00c04801000b1a40c4106541c41010040710000740012602c0f5004004850241400304010b0603400b010392887c40200d500e01980c44401d000e94903840c150000e691202e99402200191b002c4a6200119424000c1d400b0000c1c01030034181100e4100070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 345815953 1250 345814703 345814723
    0x2d0f15030c0302010f051e030103030e12150a06090501090b09071106010e071413140f06090402070201020309090a0e2b140f0a0207150504361802030d050c 68
    0x1121610700401e43d1035004a0507036443d807d81c40144100034801c1c6030002d16542c401d0208401196013007041d400241000c0c0c40041e502c50b41c090040040d0484941c54224080c0000d008512261310b4002c0442d00c00001d0041c103001709031001c80824002843d07000c001c0780074002051b4a007005041d4180e030464400000e02c0d141119071001d4421840d40355090700b02d03441212581c2c0701600c0c0c800014500904401603d249089511108035013a02c60403c0d810400e0729003204842c00d82c880010302c804102da140c40c4d4010f202c10f0b4030500403245070182e00700204400810448600c2d01903540e46041c00107040080c04101005002a000c00048620b01c00e442046c1c1e000400f950303c00c202e900060b8010182451081b034144004a083d21911141d00e40c800039a20100d5024800400e040380c00d0501045014400352802d0710030080c009801000f4548841e814611030b00c2d604001040019805441a1040e10a40e41c070341c40045a80d9440c40b03968014180340098041c034038010000c00300421081240046100b40c2a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 345817203 1250 345815953 345815957
    0x4060e06041a13021e040c030b1e0d23010c0c080d0c0c171806030c070206130b181002060601081605070501020d15140d03032d0f15030c030201 63
    0x2c41d1070740c2d24801c54110b80040000e40000070070080340c104414142448150810890342442102020031084041d520039194540d0030070802658924030741070325402c00428060207030003800718850701c3e100e4206038098001802088900002d141d05044803e0080b02100307070306404d2015282010b6911010704d40320f090507034403515546030011061a0f200e54011640d06410a1100d10740311207000861045038400f5401d07a8056441000102c414200042540d11480803c400c082c10008180c003400b456a006580d21141200b100901040f0b07281400042c10745c1090303140c01000005070b054203010000d00e0040c1c0000640d8001c508011250387d00c54605030b403100e9586e0001c0c210440c20305c4142c56034040c003100144070f5400403485101181a50b481f082d09169110b030726000441c0e0354506504510008462035070800300d40c0014401080c0a13410102c860aa408d104042c1e841c0d5900c1c2c010000e0746001402e00034692030312080c82c8125414042d50403a260b243c403545019624560712074004032168440241 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 345818453 1250 345817203 345817253
    0x17060303030c031e0106030c020d0c0807060518010203010f06030b0405150618040504080c010506010503040807030e0f1314070e0a05100e0901090501060807052b06080a080304060e0604 81
    0x11441032666041070508200030130b4001540c4070003024001d0312080140000521034815103d8100d80700b2400c140041e030b00820042e00d01012030b2244000f92100601c4070b200000e8042c07100403807020901c0114000c0c20160303c40c000490400303100400342c940a0240911882c108400e021002c40340c60003584100c00e08a90003580d906038282c0d18407540c0c442580340c41e031140c909410002402008801450042010380c001c018030f81c0e68000545075070205403005446401e05200e0140040d00503440005900341c010040400622803074002107220035161400050940c40b0184285d08000981d9201c1e00015141444c03954000540042a10380c0340d03034400d551040c2c3c3c103445c110074850301408101e07000d07030f070080c00b020020340c0c681401d1000ba14080c07042d100026540c0b000202000c1c820025611080c0c080c903107040e45006071240a2081072028103840060720b55542000922031003c00c4140311451040014544910b03141c18148100d030007094100340c040c3c0020b0100400540242201d1408000800401d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 345819703 1250 345818453 345818461
    0x1030f0609020d0209240d050403170112060f020408030a0305040606030b04140708011b0e0a0b0c070612090302032508040303090302101106130201031103150117060303030c03 77
    0x80050821503000600340e5100160540750300e4102d030003c101c0d8030001d40314515615800306205003100c06454240b03c5c9924280904100c03602c050f00b015800500034680301c003001c183c2c042d55504026017070340301821a441200070501080718900441e500c41284070382c210306061400302259224480e141c04042050341e1080003030704129555200c640903640101c107030145454140b5014600b954035203c51040751083c0d940000320224140555802a5000c074010007214000070825200760700c040031020790084000d40c0104000b1044006040c041d401c182c010011349240c074401401c00e03200f000c4540206810810007101090300002101c2c10100101012250640c244071004444401030070300403c0c502c0c00140010905502183c81e40c140d90003100d003000d1000403a00e050b14103003801c07000e024907600301c200010803c02c0d41c00d4400001038010b05001c0790303075213104074254003541c011074501d600b02442844e1580c00c0e5a119441241001c0520785520682c1030050011399607000081c255008160000005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 345820953 1250 345819703 345819731
    0x1211010c020c0a060c1e0620090f0d0302030c06150a32120708060604050105040b0906041a061b0d0807120c1b11010e03150105040903111b03010f0b0f0103 68
    0x25a2000c1d4130106e03007280c03241d8076000014000103c44100c0503030340d0001c01d01c0c024038400b0488241c640e00900304510001e43c0c0301400722080c2246001d40c2940000d1041c0d111420003800358510039024024200d050200c00000c11501c241181c102d41c0c907003180242080c49180d10360a5004040c00c40029503080410b0040000e8440c11402d441e1680700c1c040d40382d0014940400161240c0035580c00ca9043c01560780394010300048601c1201090740c00042c91000c5100c41c140307075010080c2c104061220030604031031321001c40d849600c02030121092502c00d05400d00d01000034015200300d07494a1810010310f00301014000d140794030b02c041c4119640e40ea01d89018031a030251103007214152188030700550840503820076901d1141469140da01040c1c039204850074900e400314100c2c15442d62a2600061030b402c100511005200b1500b08906111071030302030700e061900400c8003032803080d0210f611240c10000f40c4140750070340e40d841504040190501010508e260b940d5411460310f00300a20300000c40015100c10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 345822203 1250 345820953 345820973
    0xc03021c02030a060302150c0607140a0c150603110f06031311061215040c020106082a0603090706031104060e0105160c0906031a010b0405011103071211010c020c0a060c 74
    0x402503011b0f8107d14260290300f0100040c00465041809407046a0342d400300c15a5400c141485409a25204100d4080864012005800bc26010303881d205048100108040e00b2200160400d40b009056503070010300134541401c02c1c4075601d405440080c1142031008454282074100000102a00d500c07116400148d1078000c1139905050301000021014100f00c2d18111002142c880c200f405107003003d0395401170300c0c0140207030003c48110340014111030315030074a0a003440b6901544c86001d024a62140e01080e43c07090040e6004010748000b034100e1915120000c1d04450841c5c24440e0170020034001000b400e90400040760301c841080c01c10580c1d0340320f40907091071000100e4800510282c0b26400c080303864408c0c0d03403181042c0c07841408956074600c095400002c20200912401004400c100410300c1954450303103040d00d1050718041124100007090f41c401034025a6000d41c40d0018000007101030038100c090142401c403d0143c000741080702d81010100c0c01d10400750003208144000e540690041110602c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 345823453 1250 345822203 345822209
    0xb0103152007020301201902030d110c0724081807080601061403012102030a14010207020f040e06070e0102030c19020a06020d02070312210f0c03021c02030a06 70
    0x4500088603441d41040380050704400d80590083d031070070307440c4094620b0041d040c40a404049a886003440707445881110800202c03060242103000a014280320342078240075503914480ca0744801d940794914108068646a00c9501400810007801d40e00c900020f2400c4030010035036660300e0402c5031666884103075032030f0402c1d8a48103d140c0c4501c1d41d0002d030f8143d0204c0c0744c0381a56032940d1240b41c210346286202d01680428021706095480d40c2c164621411010b0070440784443c03000e030944145004c2c640301c0c240750500d80b148034505030350000b600d1400c500d0291424000803204640800c1615491031842d0780d561402410001400f4880621440580c0204191655801c06104840d100b005ea403684440504080d00228010482c0c41b10101d00940040703401c81800d0460b1b4020007546207151103035400303040d03085014814851445140c4900c6009001e44401110b84540041070030300d01c000c0110200c8425404c0801010b01c140420500b0121602d000003484215503000f507202d407140c2850000421481d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 345824703 1250 345823453 345823481
    0x61908060901030314071a0f0109060902120f150d03080a110403050c01030b1201060b0403050c03010209010804080702010c200307050913020f030f0105041a0601081005090a0f02130e10030b010315 86
    0xb004100b82808c004040740e060780c0700030f101404165075440d881c20580c00b81020316035500007941c0005103040c410040041c0d01150003c81514607508450206801414002d4142c0000301c2d02c001b003005000d11405152041a6601101c52a041c03442d161942c5680c403809c5118105901c4003850740700342d40e41c4010080300c85191402008900d6498003403840d59445844211014000c442099000e0304d0180b090300e071100010b85620019981d00d68492446502251040707040c0159020f1000209000e04410801110f28100300709804200f80205032074105a68444d030720540a0310104008405260030304902c40c2c0d816a02031503a02e8103480040e0600c192030700c00f01c000790304e400100014810324020003070886e03417085031140f50394440380c1c011980b010b0202c0d40d08450303c24808007084030342440b6107800d501042880780080e80e004c05509550990703101c8859103544000115060008806a1100c15045a1003c802c41301c3c5a2850b41d48041c0094140b00182100c240e0204540300d40060303802400115801e4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 345825953 1250 345824703 345824753
    0x70e0c18040213031104061508040f0c03110325050f0d08070b07081803160f0501060e011d100b0f0c01050f01090f1e0b0301060506190806090103031407 67
    0xc1d658100030503c0303622080d210000c502e115850941068815841900d811b502001064104000d060b60200405042107628141c614000400f003050a4900009144112080e10048000008140c50f10f0628000c1e80d9070728000980d211204289414218120f030400d0310407a00c103072154000a4030302030428401520707a000015070b4004110768443c400d84a620140c40e1604140c849070240340c2d070300910303200130071160388100000718014440e20321107000f03207200344d0154100d207405545450030340d01154012213151541034010301c60350304603001550b002c0c0d940c14280e04071440c00300c50030701000b0140d1055000d46080094460442800034003160306c2c2e10b007440028070040c2030400e1208404182482119010b51800802e0511102980140452075466041c0f490360408110003003401802c0da48480e6505650300e507400a81515000058611080c010342c040d40039014107800600f544900030326803840341b1030710001440065040907120100c521a003c84030b4560140380b82c40110b090b001f0612684810035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 345827203 1250 345825953 345825967
    0xf1418101706060109060518090a1b020a030e030102071a180d020a032a030e030309030111090f0f1302030c040e040807031d0f1c080307050a0f02070e0c180402 70
    0x1102405080217a1301c142c100b81d03454004964500500d4020301d18100c00040d01c0b9410b1610b00b203429005000b00c0c000003031003442c445210710094613002c44c100244e00401c03045806d06401400c400c40600d0290002d62920f0183e50f038000a025a5040e080741b81d144201c0455105168032005120303540d505012111581800319010396603c8900000300c0002e0300c3c1c502c40080d4071400d8003150b001e40e09414101c011181c030700e990071341d009141c1d812861b4051100340244840344c1e400340521034002d400e801d0314a0361514454103101031009920029401048001048241074490b1408034465611300d82c001070f2652120781000d115445075910004c0350a070741909100900070000d0050507040c0c800d84500500150400e402040700603001d01c91940300010075103496490521410180c0001109214a4040b03580c9030703158405600f042d1401070000d0360208501c010b15030002d074249001c2403e0700041421610300304104c500103500510103034401a001c102c07050b100c03400200303414080f03100030015034803015 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 345828453 1250 345827203 345827249
    0x10f0518040f14070e01121101110c0a060f0e060c060f070504080a03050301290d0b030c040c050415020102091c02120f01050a1a03030d18080409060f141810 69
    0x944c1d02541c04941d148000000e0303a50084041c024402d40d02c24501400350a01c2d5005480003603c0740f4068200e070068020341486960740441c1100580350390b8803041402c11103190000d14007131b001d1000e140501402c00105441e80f2000613510343c072203800c3d110303a8120b40d0b0b1710904403890701507540006241c0c0b041c03950303174400c02da0004041c5058501c51306421190039541c286200c480e0601052010558004212803c80e00303032140c000848000300a011100c1c401a41d1011a0484002442880001c2c42c08501400380c00381100e500040c14449100940c02c140c403c0002403018010701144092041c2120038910841d2100c0b139040f000b10342260b00340c2e16903000480d85680640b400703e40f1120102e2070b00d91220884242c09070241200040a40214248800c0f040010000c0c10380b1802011300b905030440c0300c00025512002031015249500f8007003140d80c40c100740104890081e803c5000d2008501600e2500b40c0c403081c1540303c54044407010346801d0b460b90a800041030300c03903030440c40520406405400ea850 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 345829703 1250 345828453 345828463
    0x41a1c0b0909010911060306010302130e0103022809020921062707030209041e050a03030c050406120f1b02031801050c10020a03111b06010f0518040f14 67
    0x628107a40d15102940c1d00e040403400c0b07a43c03000e001000d07441c81d0344030b00700517040c68070241d944080181001498400081c0080b02044680e03400152205c581f98010300443c03d105c80100b551000c0e10503404621600c820302c12200c9181401104032060380890f8118899a900240000f202c000d61743e5810010b00000050791182d904a0744240809442d1000c500c0c0c0220354501c0300802c40508001d0800d40381075034200090034202500584017290164080720b906841d628205007030a210350010b05100301e0901d0b020301510003648200041c02014030042009a130000b0180342d0164100e480020700c02d0480800100900080700040c1520702da1600380303220b4a40020040a41148206400705401b1140d8011200d6100e40510002541c0214000c00c409a24603000781c005002c8908011841604241d40404550080100b45c041e8071600401c0c1d00c09000113100c0f1501400c0c800c0444050642004007142500111204074040051248005418899004805440180e10001c0c04821358015071841e03540d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 345830953 1250 345829703 345829721
    0xf211b0302180a120314090a080a0c0b0306010905010f03090b0705071401020301260703082107033c150501080f04051b0d0c030308070f020111041a1c 66
    0x221180d080c440c040c0f4505000c005088501c0a100842e0444850f030301202c80300d196207010300e1190810b01c0f645c9080c2d0b0b5039543c24005001c070500200001802d5040c45606a00185e0116000460800902522f40d80c4100c0100603107030b003070030f00c20110114214100c0081c6030049002d042c010a800921421651100040070854000c152100d00308492284a6080344020301c59429240382c50315429410b0a1090141055240c40b00e0942e1410390340c035103d070802039001e40700d003240d11600001032100f41000c4a00711030300702d562464108074203d09582c80886414a84100c0d0110088540c07500460071154814000300d04140758043c050310360012005030090556008483c08140004006901d10901903001c51049801500814051136200c250324240768010031b5090b04251038101e080d02007011008110015072103a5a001940e14000340c0c001c002d505645000ea0459045c0701074030703007445ca5a0045c4c0d01910380c0307035411044001002510104920600420003040c600e90224951a40503a502101003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 345832203 1250 345830953 345830977
    0x1b0e06030f030408060f04080d0f0203040b151011210703030b0108071e0c021017010b09210309121006050a1d0a021c05090c010f211b0302 61
    0x41100751400071a164020741c0202c181c1a0b0100740040c0700c20106025031038226010b44411454000c4030503401040c2c81d01c144079078507026000800c2c03108005040007416401050b0004c0c05c0c0342064140002100060480b003800708002c010010200080d00c1170008950700e0403000c40703c0d40c03000302202140384e2a40049906401283c0f40842c49100c65001e03c0045101d4001a5101d40041a001e046041a4068103d40c1d004001c1c4400d6a200162511301d60b000007e0701a44030400508440380e0700c826041416009807220355414002810651240c00d17520725550310050303d031b60040c0c11101c20149540144c8092075400300da0f254024814100120ba6000304a070346075018014140c81e213040c01200201403051558060a009140c285040c00381c000603000702082d0005441c2c089c902e900107442600741d4200b44a041c1d070320824480800003c02c03001401100a081c54441c2d807070b48030b0300940b540048145050062111a142c0319803005141d005c2c00c0270103564401c28104080100004000b03401030b80000d44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 345833453 1250 345832203 345832213
    0x102180f010c06320a110406091502150c07200d0602070615030c0305010f05060604060804020a0e09030c01180503070209071403010e090f0703110d03050c1e0d0512060d1b0e0603 78
    0xb0903800c46d07000c85080e40c421384c4645580a1070070742c40c40015480f2a5140d4118025aa00b51850813403822486000b0314490f0300355a158a140c1c02c225000760408078600a440381c1c0d54840b0006511108942c402a940004005846509504125018008820588208009406d000302c104691741c131114080e80e005100070011803007a1000442111403d4030303450380c0720400740400c00031340744100040359029201a22031104581e40711612244441c080e10b414180350404a0442d0900e81e0034403805031100b09220204001041949a032600c900c15140c020f8061402040010901401540c42000c6d2060801c6000d51320740e51400703000401030040d10b18511034010b20708002c1c10980005014401d503a04002c101403031044a404114a0441300c207011028800188200b03107040c2014890a0140000381c0d00c1c039500001e51810300c0e1709051a10890b41c05004d0240301280300e561000a003103038002c10903100000c140116040c8150152100d4542d102002c401c4003022402c0c140480c2da0394040c1030243e040720 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 345834703 1250 345833453 345833471
    0x114010603150513020c01050103080a0e030109080d15170a030306050d052e02040f0617160516080a030b0a3206090306090102180f010c06320a 63
    0x1d081d50080400d4403a401d00c0040203103c40e1404480c00e580c05641200010b251841d00c0300e90a0075203109034020f0b5640000451031418958128001e1074000100b240204002c01070355072802028010620300c041410758415a551a01c000d0002080c00380c91030010750504440d0311225150786901044040700000d0600c14002483d003050b0144c5200390364804098039412100c5120361a082e031800c080302146040c00a88012056903038402403000c0d042c0b0b1140c88401e5414000082d0215140203241c102d44103181c401c0065100002001d56681091440c100350355201402023142e424100c0360f0003402aa40c00103d02d01600c0d0168882d2610003404e48604d04240e5440800c840005d652030102001018141c0381030200c000483d11144c0040030082807d8101510034000c0f9142103411901704081c0c1e9400282040d0804003074824500c03402003110303003040d01c4a0f0070000a105d003000790b0340200170f01d1321007800e4281c244619941d401c03050038460a0038041d20b080021020002002d80b060891146414804 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 345835953 1250 345834703 345834707
    0x60b13020a0516060b270f0403050d0504061508060402090f0709030f02030f070b0307140f04050904030c0b161407020d03080903070804240906080106030f060803030901140106 77
    0x10380c0780140580c644506220802c00c0c0d411008407480801c407015981c0d001106010303030b6030910440010181405000102c0c5440c18405001140a04245445012a4104400030b50301200321810070303d002c03002160b503444070720b4404094503540304a007a8499024001041e800307c0015031520503070003102c0180c10740d00d4059408840c2e450948024000904008042c800700e10052429500b0600c0501100c0034a01120078460a20340709421084101d10000180040e040d0300c540750300040c54040c18140d1400c00b1640c5560841d115603c100ba01813140300c1c0009080c140038600b44040c454001c0360224451038a80d96038042c2c0703800b10280b40d000ca8545000320010361020001d54442c0c640c06000c5507001c07085514183c885c070400600082042c803040001c0000901d000f8060802055100c1e450590800c420704904001c0d00801c0100007084001c140812809500940c564116850343c1800548441d0000180000d802aa00050410b10000040c0040c1d41c20552108055070380c3c1035076894140e600d0f1001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 345837203 1250 345835953 345835957
    0xc070807180c0f200705040c02010606020d170f091903021f060305030304060504080c030a02160e0709090e030c0a080d11031b0307030902040c0c120207060c1e0f060b1302 75
    0x3c2100000d1544000180440e0404044100442950f00311160140e13604001815100048243c80050351561800c00515404102c840c42040e050308010603462050394640d506d022008007072620b10302100d008605010014840c0100600000014104860a43c20069503a144110f160002e10130b0a0b002850b98035420310451044c1c0b6400720140d8a50b482e181c9071701015110141c025142400100308445808200b0002460030295540182113000c405a0910710034040590012000300303549001c11403033310b5102c500d6800b0344040440001c0c10346880b46007685980102009440b4a00c52250b134403062100090280c43c040c0ba28003018480711480030880d081c04d000694500c4140950100784102508021001c2d650007040351a000810340280d800127400d40e840844940702081040c0421030500c40705180034140c9500d10300041400300d1400c44000c040d072464050207002c0301004802c011030f211481601d1100740383c020f01240800c80e004d09100d030040a006e1822441b131218010300341403090f41802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 345838453 1250 345837203 345837227
    0x14030304050303070b091204090b01080117100e03190801080607030e0a030e041103040809010f0810380d15030201091e050a062a12050c070807180c 65
    0x8065800c4c5166a60b036950f001c0000b400d40e0010380101e420504100c9a410060301c01010722200100301584554000f41c40d840f41078202180c20900341c103089545043c0041c001030101d00701800050304600f103640071800c60280b400c0c101750741e40512040c0c043c91644041006d05960300c901c2070b2015522148401c1d02142d40c03400041e00540c11669400c40802d0040ca00f003002403101900200d40306045010426940d4012a011500000007045500fa996403280e810902402d4600704851355080c00d210752801045644154210f2070346584d24010200000301d00840c0074001411018040652500190065006403801d0b4902c0340c039105541d0502d00001400710100c0360180c41d6a03160341e08042c840b10301542282c0304c0201ea1810081d0000381500c1d205c030f421009160f165a0840c540c5060f02c6466103005d0713000003803500d2054000284021034070303104c1c0b440c0785603446041c07503581c41d01d81820b950700f8108980c0c4421001c2c050a440042c4807a040380410b01c41c90740c003410411500d40c04c401c0c10b640d1444066 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 345839703 1250 345838453 345838459
    0x60b0405071d0303030907150908011d1501300c03050c03060901091104090303020c0a3816020a050106060512090313052704060204090605060408060a0b010c1b1403030405 75
    0x2000810090400c4452300030556034600e800c2514a4507040707071900b510082044440310200107100d2405000090000e401c2031101c05107003030101d525140d1025006007002042d020650307a03d201c540c000c0c94400070508074041c0d020000014482d543d050540d00c413040040858042e000d03580009680303500c103220301a07e60354000c940903072500b450414040240303283d040c210b041c9a800c11202550100401c44040f90921805880b9640003040d6841d56280c00c40c040000b0900e84c1e4221702103008291400e0565103c415203c44107805c01030310004a03d080c40080c1c029116529190001c511070768400002c100c40d6a01c25250b00305500c0d82c454141d0741e48900711142a40500340502400700c0d1801111002c2c1c60701040708102442400031002c44501030042c1c4040754040d80c0014208109034040c001c040003488201c560780d007441e240c00d07600d503250078004164008060740c0301c03107030401c50b80a031060003802500b0110402e03d04280c2c0c1d560345554800740c040d090000c60358020a07826844d000084505840e03001d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 345840953 1250 345839703 345839713
    0x102030402032e090f05010e0c031902010221070b07020a05010b01050705150a020d110301080c0d0b010902030a021303030e090109060b0a05071e120909020301030206090d060b0405071d03030309 85
    0xc2104070010134a01000721003104030000c200700410000d024034201e880429000d09030074240030041528100c0c104540800f00c11a400c06040980c4e0007164002040d0b200c0c036182d58003180d94054454851080100c0240941c0c01081405000f40e8002416070441d8855002046045030940c01036529016214006005600c54581410b030407821003030582e04041c100b4005818984e410000c0d6081c1c40302b0746e10318181d06101100400080e00c0070000c0440380c5074113944c4080c5140c200d8403150001d11050180700741c80381d00080414600001030313044031109021151143c0c11035840b4500100900b911000700751091360240300100d5400000d205120845450404140c9044104001a10b554004240c19079030360b11002d2140713058400070351013034040e50320400c0c010035404546a405000c4001c142c201900c200d2050006200580b03480c0125520741504403000a0714800502c0d1000240138200f2006401604050078000e05580014408141c9030140303200d900c0c00d0002d232051560380d00080f21480b0340c0d6445 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 345842203 1250 345840953 345841033
    0x30c030a02031332120f010c48020a0e0141030c042406020c03030912011523060306030a08091807050301090501052205060301020912010203040203 65
    0x944c046503141d000003610441d00307000f0322920a810000c0000c41180103035140d88003a00f040ba84901035100c61041820480b0001400e0505042e9540240100200003880604800ca80e00303e41c0d0305030003c896004100c1e5075140c0d252000b1012000003846107c00321b060343d07030440c94600701031400040b03228610a03200c026946425003c038441d8030443d9240740c15005109040c412a08c0382d000f14405990034808040810245a544424403002680070904542107035030452410360707010003140e010240c01c40b603040b880881e107a061401480c440101012881c6024000038003030a002d440840c1d41c07641004950348080620082c00280c2c401142e10136816001050003900092000c8042c041c401c3c80a000ca48401d0300c952401e0f00c0c016000d5613070402007540400100324150700c80c080e650150200b51a680c880301001030215400c89885003121407900e2719100000c0d0107840943c165903105034000d103803900e402c411940c00c50007540b0541b070a80c0a0b014000000289a407410042145806114011a00101 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 345843453 1250 345842203 345842279
    0x90203011d071d13150801050609060102030705060c07020a080f0604171c0f090507030305090307090b01020c0904080c011806140c042c0c031e01180e030c030a020313 73
    0x410b800c440307914603544005d6148001c0941c10100d02500c0850000a00350404a041050000d0005d001904542c810013580c40041c40c0800d440e50000d94240019496034100d10000e05c13020040d4005035001d2252a80303600e442080022824062070207107160100e143c0020b0030340c1e100c034498000c0140c00083c5044c902030300b2038500c2c0d0041e5100c07070040340f000401d1481d0b41d540f2800c018169100340c000a102003403109441c80d013409050004c001e1030a08008080c00c003c0082d48840100744258810860381d000501071050799001c98000107182e0008105d5a450314980801c040321200741661402d141070b000c00300c40c100002602d40900c4100f003070309041c1440e2810864055204603018221000c2d40f006c405404031007104054000d1080044103510382c50400b00080300f400400b604c1c070380300000303d50040240d5186100b102d6444103882c1c2000c16a40000a546481d40c4191001c41d142c0c3d00c40000c0d603904442c3c0c0880601603e43d0f032840706682c11a902c204003091910200003164a807500300c84441c200308 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 345844703 1250 345843453 345843469
    0xb0c030c041221090e0108070e0c030403090812040602160806061302040506030c04030501150b0a110a0c03050d02160302030d03022506061415040303030b0604090203011d071d 77
    0x1d01c00c958000d0b00032600d0f403c03440c61442a01c450800300340155014045508003203a401e0141a801c40101503140c41c11402c031036294005080b058000e007000000c5030500d84981800c002400e02013044845c6a0940812000746a000b4370448005004041110580d6a504481141109c1410f0007c084549800302004503180e4441c1c4003002c0c89900f0440025203441e4800598403654441e1a6a03841c1c0d07185040440c2075851660410706c42d403400d00800d02c912003045050f1031b103281040c03070100300010030480748a1034401031903009070803090030302000410402c00040c1350300252650f50031340d040500400d062410a0445000080d03068120321b480820300d501ca64003611072418040002092000c072045914810a902d14050340c403162941000e00642115410007166404283e0b802d800d1303003505401e102a0360203540401020151903050508131640c8500c1903c02905041400b1951b82d65552400c0c1500f0b1320303100031401240011030011f9000d0f8010600e01c501d11021440360f03000c0c40240301c1089860 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 345845953 1250 345844703 345844739
    0x2150609060307090c050702010e0904050607051b010204080c0406050a0b0708130b1603140f0409050901110a09030501140408070605070207090204030506091204050a060309050c0405040605040b0c030c04 89
    0x6204402000840b840c843c06640045d10484d00c0d0300d550354140740001040201c40049450254400340c0c2448005a0700184c0c02d54080c9141c130f0300c40d03260602243c1a000341c1166681c0c1d00d030300798000325000c42c0031000030a05074007602080340c0401101c1c0d902e009002c4600e2181c030940c1c01c554010b1119201181d802c80007400c80150151a500e042612244142880e4005010b0904800c00e1803542074205600103415055079030341a0740b814200081c0310705609a61080e8003410800986840104401032825000302d05030350442c1c07242c0d985030301e4910401845220988020341d010f41c2840e002e6403001801440391406150010f6004c1d140c03034107540b2164094040074010000318400c1880010303121201d88041c00181d403149020349070720f007455031182d440c00c66210000d04003e04100004c0100390380d214402411100d0604000c82c1501050504509080c001c10000750424140001c000811640b42d000303074032139031017005621159252000100361b075000403a0082075201d0300300001e11441241c41d45011030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 345847203 1250 345845953 345845959
    0x1050f0f061204030309060501031406070311041e030b0c07050d05030705070206030411100c05010e0606030705090a0f050c070618110103110708040b0307120207020306070f0e10020f0d0215060906 86
    0x4104051f5620030489500f40c0c42a100e40801d00329580e4030340010710001d50844441d290501a889200c0c071200c406d0b00c184e1280a000d83c008103510354440c0c0402c841100190f8100c240e1100c0391030301000e00c0110f6030240c6d5049a0b10300444000132182400765090340e0040c401960798504005441d03003404000e50010380b0540e1903070010825034145039242c03036400b61104055624446807202c0d615045094614080700e00c2d0850308200200500e42d1000070380041100c800310b6a06942d529408101c800038014508103075226400c050400c00031260f010b00a1078214030a81042103001c0d09688035007500311300c4000c000e1591170382203840800c56120742c10000c403c201500780c0c640382c5000c690319248141c2c050b5010005102c400310810100a40160b28808038089080040d40f4080780342c1d00207a02c03540700800c44000c1c00039076144100b86600c990016040c100e005081183c41d0300168034041d50f1003002da40d81d62040d216a0070f04841152020400c40c1d01c100c0000034002c41a1100c40c204000880003c000c5a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 345848453 1250 345847203 345847211
    0xa08060702060c18030a050d0323130c080d05090a0909150203091e0f01110f03010303140405060c06100b0c10021e0d0b2409090a0f0e010501050f0f0612040303 70
    0x2410f070b030280310840a1510507002071034a07a40c40140279081d20942480014440b0410080c280845c5100c01019032013504484c0080c0c40c180740c0d10340300d00341e244aa000347c0300510030007500c509000e0b00034000780102d9170100d03044415a03940f10f62620a840d0b1201c0020241f213002290400300f000c2c0e5030059500030710010103954000030541d0a40300c14200b84018031207643e20200055102110a12a590600c0d00c810341c40d9182a0104103908900c1c0301c1840b0040070000915100801801130790306880203050001c040c0b030707038500d40784216980d030f04000d03542d10004401600000800085080c11910495822005010301c1581c0c007000400035000603400d2000305849910264807240440c0050814902581000511100030014030540d10908142808140f01c4104c0c0b18000300040000d55081c800115000a40350751031311003200140c6180013401c1d02c01404c00503078290001044d0800b40c1030329415a83d0801e01c0d0340300020420f05844a0045a4000b601008198280900900311541c0301d8001e05000c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 345849703 1250 345848453 345848497
    0x20a0f022419020303010303020d0807030b0603160305060102010b0d060209030a0f0f050d022d1501060e2d09070c02090a1a0a080705101403010e04020a08060702060c 73
    0x10250301c6104248444900700091499045080200c0012071450500c021810341d8195503000c0c0d580c481c0b1141d11024041c0340d10000700c901e4841d401c40807180c07401800840c0c8901340012500100d4800d0490000880e0921000400369481442424003c0300d005000740400d451a440e4000254400055950140500c5252001040d00344440c2410b1a00c00e66003540d0030a258200141000600a07041c021904161150480c50f100404134544214081404140014001d0b4460703260039001600c03130b4420024480000759280d04615840180c500c00d4901d03a245120340c0140c00c1104a08232506500e24101da04148140e0410405440e80328249003490080c0340090340010341e103450121607010806488030702040d200b02c04660407040070741080e184060614201282c45071140014007406009100783c10700c0c0098103100300488059401d00c0c119065580d41c40d403020004400d0101d405a0080c010440e000400740740002d2168440c07002c079805090395466142c2112003d0b03000ca000c1482c3d40100000e29 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 345850953 1250 345849703 345849739
    0xb03010908070c150509120c03010f0e070e090a1101200606041d15070c0b040f1e050706080a020d021303030806030a11060706150e061807020a0f02 65
    0x20080740291051078450140f441d2000200c3c007160040d0048070815640e42900f990800b094841c0750404456008015169800c1207140c0422591f51981c9982030010010700d03c2c4580e48180c2c440303608001a00d0b0303140d84903100d40301011025180e1198907448180d036107021603c00c0b41018104401454a800f01c00040b551a1400d00581c12203500340d50000c00038081e1b5403800707102d0602140b0603074820580c4040025072031500c444420f000c11406100d030130005030840b481141e00420b01544281040c0c158100341c1461007180651013001c0b07848906244a200c08208030000e242c44403a4004010103c190500408490050700a400d840103540c0034803852003041140e00180101480c084541900e443c43c50800810044005c0d0259000e50000d00c414004034051190001400788103540e5503135505140c0c5007110080c428143c02c2d42100c900d012000c1382c424080e203012405040203c800100407902094401104941500ca003000750380002000000a0b0340d91a034001014001004d035000100e0244807 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 345852203 1250 345850953 345850961
    0x60b060a050309010c080402010f230c070317030c04060f02030d2f0c030f031003060507021c020303060a3615090c0203040b0c07090f020a080a140106050c010b0301 72
    0x40c5000314401100b0040400b038244120b01d500a032a1800d0440350415070000303001500d403031902e10100004888244162610102c0d0000c00c402e881441a6a079001c4410184d11a0040c0c0130464900b141246100c62003034175442941d001d0030407928464075180c68504242c4410706484021003d6000a2110007102ca2941c49a003541c58105500c40450318060349982d040c1a01c0a039400c16890002c0c407101001103000000c1d18180c104200c0c550303a032a1600c108062207048075500003010982410304001415502041c41c0350000f07150511708041c402000f100b030361a400215241c6402150700f640c20020891482c1e941003a407480c8012504000d60500b1240c0e280e69002c800412200303844a80301c0c0c03024484400198000c2036610410800c00d68641c00007503d030f118500c5815050300001c640c0c0a550f8000303009050040c000322008101e21844502580301a4001440c0c0a01080054000440070300050180a00c0803102d280e1541c2c1c1c80c1c2c00c01400351681e0304900e4041c42e482d075030791040030501e8509101d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 345853453 1250 345852203 345852217
    0x605030102070c0608060d050615040b040c091505040b07030e0f0306090c0f01090b04050607021203031501030518060406020c032118150402100c0f0b0916030f0f060b06 74
    0x48050f240d5082110280000d1005002c55002d112003481c1000841c0d000314a49410201d19881d100d00000602d0000d405454035204051340540780811750a10701b900704850f2001c8490011030072860380b02c207030410b9805014034400e104540d042003100c580000e104082089850390018074402100b145000800c3c0f03040400c441080c01503020110310085458804040702d503405092038880070540c104440340e000c1c0c2c041c0780704441c0504c0d00401d8000455807016400b0070058804400c403a16031038011000301048240580d014003180c50500851626502c1d0420030380c1883c44d01000b015203881d1903490600039030000c00c440c6240d0000340f00c58402000400c0949035903008225469280d8100b003516501940d491841071141a84100c000c49030034003c41d03444d00e0384150100c0c0c141389100041003003a90070400da000010f08503040f0034400d00420000c180b950780607109420458604401a64800814000074000500007803201001c2400094800c03e03424000d0303114901c0414072418140206820b904040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 345854703 1250 345853453 345853463
    0x51302070615060e150904090f0807060f1107030e01080a02043303060e01060e0d14030c1b13050c091f020d020607080601050d0b19170c0f100201060503010207 70
    0x100c0e080103d00e500c01002d04d4591402c4840e01140c4002203219012803060300c0d0524000ca0b00d4440200603c000f5400810019420981441c0c0da14200d15150001b001801201e61351f191400c0029096030b1441c1e070507140e401d589505d40c13005205e42d000c019580c440d03006148036646034007080041010002000d480440c6034400e210134914407a00c1a55500c040f00c050015410546420b00400101f00c0038a801411503d05041100000c9003950102c0c134002002180a80b207a8025552140009000001011006410310585000c41c1c1c29407540840d4100c89a01683d101d8a42c42100d401072485038401904400012210303881e02580030040b4034007104c1c0714014180052080c10f095400340e0140060b030408034480c4050000da02d0811000303041480040c01641c1001804a0000f00089540c0d0040c1a03006005040710b00b003842030407100b03080040a0084900c803040c40c0c0c0340031075880300000381400c4080c40207140f592148110740500c0f000e51011a029811503407510f100140300e407002e00c014403000380a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 345855953 1250 345854703 345854741
    0x12060d2009010509090d050d0b190311031b0f0612070507020a0b0307080a0f0213030c05040c02070806060402161e0b06010503040f060b0f1c0302160b040513020706 72
    0x6410801ca00e40141c2c400c1c1e0007030703540b0400c01c610032a02081034160782c80c1a0810035251045411103800405003810180c0d00300240c9850040c03003904601c1290100c03840744c2d192041d4401c1403001d06443d42c00041c8402180c1c02050448005494420501001c0d500040d01007810700e0703c0c05001e41c00100c4240c0c0d44002040002680304158105021000081c00603008407501c0c50400c00c10080222900400f05e080700c0e561842000c00e071640d250100c1c0c1150314200075007103845480717003050351203c9054800d0501c110315100448402c14000314890080745c100401821056480d4810701c0040e500c01180104041000c640e01d80000e0310000c0ca960358480003c1c0702c0c840d81d41c114508151251405010a81401070074410880080e400801d905036241c3c1c0444e0101d4402c0b519000704120a95803000241c2c4081c0c862010341847c00490542c00d90107009508886810000c0080303060005464041c06203164000c20043c0403500b005030340030407140036088005143c250103454480464504008480c0f0080711 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 345857203 1250 345855953 345856013
    0x1b04150201230f0c0d29010912020d030207150302070c0608040f1103030d240f120f033f0204060c110d0506160914010512060d 56
    0x1091203103120318120000e075609008a0048200700000004201c03000c90108503001810301c03044813081c0d42d12560421001d115200d8041d00070301039004c4400e03111441071068803041c00035610a060850071105140c041c030320b0640142e000d21113650001d89056003903100b407020010b14003a4a45070301c0321420b0071b6500140c4500440c50f1299200281d54000810096414140004581210107003401243e01c02c200f00d5882d45503101107403c40c02101201d241d036a140891108410100e0742440149a203000f03000c1040c1a01e65620140107c2035001d456440303d003402c0038500144640d0420b0b003986009050009a4030b610783c694214014030700c0c500103a02191900099695803800342a683d400341c0480007035042508001c4000c204080092015060a450f64442c00143c5c80360b140251455411505469140c0f91081142c403210740c80c0105480006c2d0304600010300e1042203a01c5100500c0140d490a241003114145070b12031860180000f80d100b03e9243c550800a8841011181c1a0058244120321140c5e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 345858453 1250 345857203 345857207
    0x80103030e04060e0a020d11030115200a03050304060902091503100b0f0409111801170304060804020d0203011b02061807050a0504020307141804180312051b0415 71
    0x148400410b4000c0d4100507080c0103095521000d40c1e030180c00050b0040c0c039410611180e07000341004039030488a940740040041031036100b0360050811030b010340e00d81ca0500e0350503035030450702c000c1640e118141e242c000c504000006031143d0b0066070010300400d4003007500c840d41d07000039080f40400e0301c1441c91041c82134400d0500303080500854903003115242080005410003404a98107216450001c1d11480e80c400009082001c4070071144203551015020840303001191401031080003003805242e44074441c841a03250a29000001c4030261002542c40004a403119424001d00310904d0310120303415500d4241b0618000020034281d103008100f41d00801540c14150740c071151404241184102a400140e410701aa4441c88014400c84100350303001a1b407540d031140202c61041c0c1200c0c1c0303030482c0c510004000d44200c00500c03d224410760122030420501540310a050740c001c24006000300030514000c00c00070010020f90040340c0c007408a903e100c881599001d4105410340c81a01f041041d06611311349840c040e9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 345859703 1250 345858453 345858467
    0x190e010908070e01051e03070501050d110f0a11060103030c1104060513050a151d07051902030a0e040605010c02090417070f0b130506010306020c07090f0c03360204091208010303 78
    0x92103511b060070608840010a07181e03001030240c5814801c000542180c2d040d556400034501c02e0244e2201e649a0100003403a4040381d000c50f0300b080000e08a03640710344c811880454038a0489515071182192850540c1c0e518140544501589500c20b544800000e480e1300c4071344161110405141c00051249850350400c3e04950607151920b04170382d070409043c0703e140c14070188410071180a0284081d9540c4000c01110785200321400032814821080310ba12069400001a04640150380c9610306400e000c0b005000403540e05108841c0007c3d140048580035080c06e000840e0000d00444451340c20403211182489154400401114141003800000003800902c101142d0440040d20b1401018819030b11055a2444180005840c1c40d40c00500e00d442c0c0c10007007111100925000c03a00b8401e030b0705079204600040c40e43c0141c0d00e0100e0300340054282ca1a4040d0b2419840c001e841c21000707604001c1880e1a1804e0705074250480c2c100b5950071003400812040303006220260244e80e1444859815450010f10b81 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 345860953 1250 345859703 345859729
    0x15091514040305061b0a0905011d030a0b07032f0d0e0105010f09050a02040509041506081005090c09060a060f020a15060314010506061902190c08010e03190e010908070e0105 76
    0x411040c806d1080c0e0941c00380c0e19800300e91007403034011402115207100d4120360385014117250740b40c030a00d80d0b400c08000c2d660b110395214400d192800c05c081750002100c0c89241c1c4441c21a9000f5042c0414048000352191010b0581203288001c0001e8402001e00010b08441081e0882e202c212440b2500f00240b01c4103000300c903400008070b0015030600346000d02040540b80042c00041a400c4590105034403000710703500c4540141400c200b11603842c026400d100c0b00404041d04ca0003a075010304c40b00030849041101d1858050f85014108492840c07801d50101c0d40e460221403845e0441c001c034010130010540c004010f5480306881000000d0b494958900480310703103510041c0c022280d04000c00c01c80f182c0c3d20003098480408000c80c0c00041210140710490400d4010024201e0310901202040305008103603c1020036601240c0c000c0000f10701c16a030650340ea014542644d2100043c01a180c0b40c01481030115070031400307040c100026025154403420381800740e02d800c592034000140d40100300c6850203100d040b0741 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 345862203 1250 345860953 345861001
    0xf07170c010c0c0b09180c27090f19050a1a03160e060a030f030905040b06090a1e0b04080c15252102161509151404030506 54
    0x1084050b541c070b16090030064400c0303c0d02c001010605450b1619040c00d040c803540301b08440142180707044018178840c0d40002c6600c0c0007803840015410b01702d914100c440881e510005080c1142ca544e00144841c80d0400208100a600307072548034070403042c00501846001e420b04100209180321500a090408038400c1c00c03041c480e900804015100644e41200d49090700c482c6e17158a5007941e905000701d0324812059200801034041c010b642c006041d8001c01110940300c0859051122561940420207107004603003085070f000d066240e00b0092000584404801010104010200c0d65aa0b040c1428190015880382440f600085c0c1800c04500d819100e03079840c1c0307450507003403400e02103404000c4d1000da4844411150541e000134003481805100107241c40e0710325403c10701d418224080c06009465030080c541030f10100040060204034945102c002c4c01d012141a0b40307030380100d440c06091000942113189044107010a035a0340142d203000d110014005103000d00010113280c100814a04008010b00c003200d18 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 345863309 1106 345862203 345862217
    0x21605071d24061303061e0b0f0103090507051c0b01050102070f051002120412050708030c280c0308093111130303020a031107030c0b030403020f07170c01 68
    0x120b801000c2046c2411640700307e40b6400d0b00e04c070040c6107070b002c07a4024426006501c82e501145c41240118100d546040d92017000c038030802840351864100032500d054400c00c1c0540140403a004201c28401000000d18100480b0740c200c140e401814803451200c05600b0700c1e54404c01c1501070b40c120080e44030355a2541c5582159907221049030495190158010029074280c2c044290b1f40c0f22200c0d8000341c40c03440d5090b40300c0b041c00b01a40b8410a15036602202550204980762540d2000c0c51040b145240c0e00d03c2204200900880344100c140b041e2290200f1040040d441041d5410b03080030040310110745070020104100d030074010751085411440084000000303160380002c03103244a40c06510f64004580070615095183c42d0103003c05080c041da44281003100c06180c0005640c002c7c003c1c0b068503080310b640c990f210b05181d406e41c45121882002014840c01010901803800300380001d0802003 = true := by decide +kernel

theorem cover : BRFrame.Cov 345683453 345863309 := by
  have h0 := BRFrame.cov_init 345683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 345683453 ≤ n) (h2 : n < 345863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
