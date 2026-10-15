-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4785
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:43:21.864182+00:00
-- url     : https://prove2.me/submissions/ce7edb72-049c-4758-b452-b6eae5e7592a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 860431654 ≤ n < 860611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 860432904 1250 860431654 860431661
    0x11010213060f0203071a150d0f060513081c0b0102071211040b0a080601090c0f1d060f040603020d06060203070515100b040602060603120406020a02090a0f062603070b060103 76
    0x40c590b61040b245880301658861880c1c051691450300d50010132018130001c64445101c018610f00107686290071414070b86c84420405c02c3d480c40152031660386101048080c80c240d02c0000170240c010703c860b13035101c07092010b54148030aa0f54503420b10341c0c03510720404020741c80070400d0011078130016007100000c001501c4040c070030100d10032352a5115503542503112031038542601c241e00500e60a030180442d5850714903550150ba45127081c80b8100589802d04849240d0000b80031500c20303d64000184402c0e002d1808206e0910404000345048900840c000880ca030f41900108104080c1120500c090b0340d64250030b076680d0282c131100420680009855081100c4440e036899402018106584025583d44100c240c0d81e5001e90041340068010404100250804001c80c150b4003901002e118509450040700a4550f1035541c40244a109040003050445201c2d403c00f00380c0c1d0000c45000c215032503071050b01c001e095100b940d99202000e10486008065800030058400a0340c0160000a003540c5040044004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 860434154 1250 860432904 860432927
    0x603150903093706030c0806060708090f060c10060806010303080f15040632090c070515150a150e010f0c060f0c0905040e070308091201110a1101021306 67
    0x100b00320b5400e20002c1c0f40c001e043c04840c00e201442c82e0049400d14400a044c1d0720483c11000902c40c1703030030a2140039204c0c0700448400540100800e40c9071310030840001d041100982045074060004106e1600c03107035002c5140156278903018810003906039030724001a1642424400503010910740d000250040070f10001c5541d1244400c44551150460000004c0c03c840c00e927003040700e0038040000d0385007801103806000c683d180c001103081c2d501480c12400042403903d00a04c2080d103480d020500300d080107420010681c0e01109010391102c6450080d49020786018440e0f48207220b07a80060b4001806124404040b440c0c4a0359038a009040300068015950750342240f0f820380800c00c202e4051404190540b069202c803002009003c42c1811508000a00e60780954000310301c1680b070f00400da900004006080c0c0100c80e403010500751034000c8000020000c0e0440c0c0444003040d400e03c1681c038840c512550062178400c420751a0304846043c0d441701c15080380039245010015210940d01440164000d00a8652 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 860435404 1250 860434154 860434189
    0x15090103021305180601090501172e0603170702030705010503090312041e050f1b130b0a1d0105040f0204030201020a03120f060b03040510050403020607080603190b060315090309 78
    0x100328410030400c4d4580602641700108032030382e8000500046641c242c3c1011407444140081100500c0084c0c45021640d40c6184004014034010403202408080d4000c84000c54000761400581c06141c0040000c036886102c0882c4680070300381d004100d5600035401d0b2802051600c0080d410007000d0803070f80a4403080500142c40402ca00c081105010b86441d202800c2c0502c035002402d001e031040c60f1a1440c0c100c0301d10b003884510f0040e81c007480c40350312450102040c1d0300500070003007a019000404144440c0241e08204201c880d62034403100103a007100c1d1601c1c100caa00351030810500900880c00c004034000c500000340141c22403a11000441c0c8507450308a2585440c00300002c407010040c2602044446c90f80c4104450200801008180442400300c000ea8089100d0184154605550001d49071480102014144901100031403d982c80410210350b29200480c0c200f1510312050030b140804903021114184030788a82c00c03000710314141c00c0c04594050041c00d070065081540320401c204c0010740e02100c0c400c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 860436654 1250 860435404 860435431
    0x5030c070602120c1b0c240904140708070905060306010507051c0c02010e040c020d0c030504081005270705040c11060127050115050c032115090103021305 68
    0xc0d10203802804940a5661000110350b05c06001056100800300a8403500c3e4940040b2000e006903105c20700d0481400004c1030b03000e41e01d03803030160300c0f1210780c000d110798190410325110040c600309000f61a400c0c0610003946810505070b5074080100c8440506d17001c0c1903004401880492040d5000304058020684140140c80020548400104110003043c10102c00038030880d410100355600181442c441020070b803020b00080001c000302035640c45079800305504001c203183d401000d05109205130750180507000f0507500c088020030100d03001b03000e09a4603401d0b02044030811081da48007072241d14807950803803c09800d6417890318003004001d00d4101003043c24400c1c0341e141010f100f24103010040c00382c0020340d4400a445201e12400103903501508113003134041e00d1320005000940d890100201180107614200303a851708200c040f10308502841a00344100e80189941e09110340103840319611905008019181c404221020499201b6003884080c0d00252640724034801c100c0144c110540c000fa2114100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 860437904 1250 860436654 860436667
    0x51002030403050714210f03040f03020a08072613060503150406090509010b030601060c0206030a091203060302010f0f08060402070501090506010b0a1d0609090916030c050f0a030305030c070602 85
    0xb25014055103681130f05d50081a0601d00003a4518032a40820505c001d4a5040c01403150500280d48000b4002520b020a00b00c1150304041c420003107415500c0e4040800c1d5143c0c0101e20713250b40e64100308140e4520a40040341c10140304c02510003030707400100c09401102d250604d8000d090390260701c06030250f29100d08a000c100b0040c2c8442c0126001031102e0b120015141ca0f00c8141c080c2105c000b0561948a03801000040000307692040400c1c0c036003038040741c41d1079807612400307121802080200c100410700100e40034403241440e05580103d044a000381c03a40380310b501040800b00d9911200e40e00100102c0d1140000c01c0803401e01da8003070700089108100000b0309420a07155076241c600240c1c0807070340d240c000040301c00100e60305c6421114841d440c2180014000f140310005401070003050b007040d0140d011b00000074042e103010403483c0084503950000400c82901c9040001e80d14001d03020b09030180aa10f844007400381407000d1008122905075840c1402d640350700214100c10741c020740056548640902c503c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 860439154 1250 860437904 860437913
    0x460f020d08071e0503010f0e01030f0b09100c0206090606030d09120602091801060e040501031104050709030204061d0c030105060301030f11180f0604140619080706091701090510020304030507 84
    0x5100c0150341d2504c034540c0b03940c07402413010b141001980002000b0003151004100007241840f03108840f03540101811010341d210386070743d85000100701410480a04040c280d40e41203030003044460062030241d055989694410081c9903070364058480d490b0018005072010081c1081c613440071007810780b0800f40549014146000981102c00d40301c103a603081c03444800108802900a0141410310f607082d542800650714644800b13407403599488940c0d00031a111400551103a01c076504000c00303903a00400411005031203031640c05101c0914008004840600401709000070b10b0744041d0ba04840c0010007151443c2e00356507134510710700701d240c4d02112210a07241c0c042002c0d540c3c041d007070003043c0c801111188807031600d45000003036894081c0029018920380880c4d80c028a00041030745921203404e41d020300080603015060854148254041d0072035008900000c01c242d64404e00810403168040c1c084d032541c1c68034848803030880702d43c0d040040c100d5000046000b984041a0080e584c0030b40613090480c1490183c4d100c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 860440404 1250 860439154 860439197
    0x10c140d0902030f3705190614010602070603111201170a1403092803140c0306160305070807090608042315010803090105040506460f020d0807 63
    0x25082070600c1c0070250343e0042080c5c142e020442c3c82c100f90b012961440b090329040d8690000071203c416407071040d07200e14144561600550744441c140c1d080c101c0a5a03494400070b4440c1824007a18000905020b84085040c9008060303880400b000c0124200e1a4a807807410300c03221070070300d181080318040d02004c10301052046c07003525036101c10440910350303032080d842c00c00a42c050b951040d8103140c510009200b248039141521001502c1d406500d02034694400310f505031034251502400d5616100b44020003400e459030b103000070b04800081d01c081c00070341c8030f0480070780b10840104c400c0000a080c042d070400c840c42c454050140c00038080c0c040e00550800c144039007403403020102d00c1850a6402907810000444507041c17032500405c96a0059800c144d0004002000d81c4281e01c140b0784601008101680c04002822848601300d0140700344c0e113080c1c28501242e141d10020745190641c0804450143d810250003050104030b0b41d0f07855406402c01e420140810786812401a0240c0104001c0f001e552016298085 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 860441654 1250 860440404 860440423
    0x311040e0603010e100504030906111b130603030e0415231c1101120506010c14010b0901030317090703030503370609060801020a0203090d171803010c140d0902030f 72
    0x500110301b03842c10f8200941001b0f80c5038030400070844c4101000107402c034041118050000d4000c03480101c00e54210001d1708850701542c0c0f078200c0360725001d00002050f0b080808010182c009a6050000d02002079070244124144e10803203080c01c007904859203600c4c13415072524403001e000428480c50081c4c0d11040243c09a000381b412142c00c1408468140190380080380c0c40844400c0c450140014944640020700901500000500441c0c841400c0809880c2c00c1d04070910040010f04550040e43e0740382001059205085100a03111519001140d01c0c4034021400009072601a1034484c5951256a00c01800302d640c1d40d00704420a09070416000d242001520140b2003030b5560794080b501d50b091101003401c4400d143d01480309680304011540c1c15640110a42d0b2188004032603150041c4194242000c000782400070320203540c1d000060b80141103808101481810030254000c01c50569200320507a09102c0c04119801188018040100494000d8022142440c400380a03204c500451040803031030f01029030b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 860442904 1250 860441654 860441683
    0x406090606060c050c030622061b020601170613080c010b04090b070908160611101506030e0105070c080a05040806160201110a0f05250f020109060311040e0603010e 72
    0x30380d01c0005204c410400003440c4c0c0c1007180605614100f140d051588440340e0b2440c041d0f00700c5041000c0701030040e164805900c40d018004200c8204c0c42c0b02c800251240802d026524401c442e1210108100f000095101d01c1900807100044080c0d0043d103600700340d50403400c0031144564030390f0701951041d151805900e40c0d0500c0340e80da00300c0701c0c02c000300060050394581d0400c280035440108204900e01a01c0c81600840711a401c11080044008800314100345106184800181c10030142149904e0b0042c40b23442110101d030b404100070580f10712014203a4030705440100000b668400700501181e10440144000d40b00390410038607041e95440d040e030402e103048450710100150124000c460640a0242107540100003020a1400c402000301412141c0190400000c00101045240c007840b04e003000d80050241c40081194810024136111000d00030b621400c078005110141c0c0064014001d01a003032003050051041402c0c035041c044060541c84009244a50541d00c034605003001031400e200101240940c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 860444154 1250 860442904 860442917
    0xf09140a151104050424091a090403030612151a030c0103110405101e0201090302060411010e06070605070e0a0f0909080d05090304060906140307030903020f0d030e010b1e09040609060606 82
    0x207071030704003120743c254040105141080300c1000013820823000c3d5a075500b021240c8444a4440341011001007403990000a10808103100d064140b203040b9034040d8200c103250400784042000f05845540c05440c90301c2c2c40e034042c0c0c0242c224044546c065040090710f0825161842d0426584400007000694140300343c0011911b50102d01e40c0d5810032182c4040c40703c50b5400280807035070207960001e6895400620190081052084105445c0c0c80b44160f00114071004280f281c44104508100c0c0040009490242c040b5072003220301030300b078108581c02030f00302c1c2c140103404071301c0f5407401d240c46024251108080f240f0200400113600b80c50184d11455016034000f1000707585440c00c3c541d000e401d0403850b400990a100c1c50200001000071480110303640042541383c0030403040314600c0c0070317441c0c108560305a00c0e090003058003590560350715034450008403031110020311101c4120018019984030b0080c03841d4039120065a00c01050500328403541d000751040c0f41c000385480e010b4071008200c464507000f0b40001180c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 860445404 1250 860444154 860444201
    0xe060409170702150406050406051b0d051b060c1c06090204060e09150603011202030114161805090f100b0d14062707030f0f09140a1511040504 63
    0x822a070b0f00c8030003400340144180f80504080001c0c0c1280154441c03403003001000032f4105484c0c5035001819140b08000e02c02c40341703100050000074000790808411060f4200008960035070030340b000140c1c20301920b42005018074082c1603801c2d1a8900c1a807180123000d0300d40302c0e4000a80b401e8070b44000c10003403050343d495544c10802c01041102800018000101454409902449603035034141224111510513035002d0100b100c030b10200780545580c00600201090382800c000c40090580c4003c0803107072569130f50320011090104541c2e500b6006005254000c80c0c1c00c000503c008a1040585030810741c0c00103020b23a501d640345400100395016030601010180c81f18140d88002c3c45040e101504841c0844107502a004684189403e42e0010081c0070341c00c0b20070801140c032007030103503108440420b04010244030000999040c84081c10901c4000c40c0e0241c0b00b0300048610401c0491644245a4040f83c0b52184020002035400034190000d0010740c40310041100042942c1d41e4407804658021065102450344c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 860446654 1250 860445404 860445409
    0x6081c0f050310060e0a080a03031b03091a0601180603091109071b15060e0f09150a0902061308210f09013608060c130e060409170702 59
    0x40c2000e94060080034810310001d502000d1030b01c1d098800034030308102151100030016020007070961200f44180908807030f2005040d41500440701c12410038005c460000702d0000118200d520400e00504412008500d2a00b00a203400130940c12540502d00958821402540c0c00d0181d01e4692007000820703030300c6902038100a1448024040b101040700d80045034900b1039005000038850030742a4403140140d00002c07081042c0040d040c00408036a440c2088082c2c0c41d0140e44507128070a80e10090007611200c0013036101403001481c00410f03c081042c1408689820200501600481c44200e034860021300030200481c502041c000010800407004203010405480360243e04945136251140f89a010419417140c00030000449040500070b1030300c24085401845d228240d42d04d01c00465603450300035001c5807000c101100502056554540c10389010780ca1315070030440706201f09620084602440c80c0d08101d0070007040e8402d68018400380010481032001c2d0354606c0326a00c158614103004101007003100c25030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 860447904 1250 860446654 860446667
    0x20918010c030c090902031b0a111207030e243403052d1303120302040e070f0c0210230f0315011107030c09050a021e090406081c 57
    0x1c082400c0810415035a0f00d0028440003040c02440e10f01c9800001281034500441c1d074203180008488001d41e22030480e040d0051070040f608018090502c05c0c2c00c0f20030046401e550440f00c9280d030503128100740e5441007040c0051103c0090a0030100117008680300c500c402080020010030b4400380b0380c860046d1000480c040e00da0031219601c8980041051082c0000f40c110044440d00403401c2e60919400003800c1d4001c8181c4040c00c0d0410740d8500114440800e4482e0000390400e6a124488165800178254070031412806148254401c840d041004124114002c6c00b114005038401e1403c0384141c080d9801041c81900c081c0315640018800e054038680f112682d00304602511400011980f92144642803c1210b0201810b0012070104c40012000d10b80c0c01800d4000001c141031003a0307a500d03035403810030002404192080042c0d1905000000d11840800c1c0308442e406401c9040000e1000c0c95001080802e8004014443d045030369901d0109820404200f51903094070181a030044401d035504c40103001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 860449154 1250 860447904 860447921
    0x70309120302090f06030a0908070f0302071e031203110309070501080a0e06010e13140609010c030b18071101020f040819030f051e1602010327020d02040902091801 72
    0x8141c818071210003d03a0390300c41601c0022108a41864981d25000c50703410084c40404030013000e1601c001207407020405e03030084103100705020350207461020341d5a41d0700e80160344d000b46540921fa518400180009545405405104021440c0c002880c400c031740060f12440e07005594140c281d90084c2d004201941e0702031030190740a00c40d002d0034003400b651a203c444e51810180104207080000d040012034440071086109041f6421044424200355609101510b801c0c4c15201e0108070350829451001d0305009014101c201d65001e0003d66072000c14000c08050321001400748070400ca001ca8505000314424005030103a890443d1341c1035030303032403411503040d1610450070050500003441010708004660020301d02c584080ca81e0038110307990700030070b03074420822200c56a0349410307a4004a1483c3c9055500b81618540907c00c6e2030070803881130040a0440594500c113580c01c4481c183c107401e08010b0074240508418207102400120740307249150f000417200d41040b90702098501070300c0e001c0344107000c090107982c54 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 860450404 1250 860449154 860449157
    0x2070f05010e120f03040f080a3c0e0f150a0332070e0306070807020d1d0d030c05072706030b0c0a1803030f14160609050703050607030912 61
    0x2403c00b4400c02400360a595050454011000505001a01c0c400c4900a64012000c507502c80d901c00001d8900780c0c070202c1e1082d0050322501c4119086c0007880c00c1c02c420002010035070b0301c07141801c9011940980c0500c0c101ea0420507002415800340c940142c01000c004a83c5049902c07010900b90040894410f0349140030b109000a10a10081c15070780c0252103000710400400c1c415954042c0c050310004902d500c0540c040c8909003c00003d9580044114010304070b0b41d0a841940c1b1000b0707030132240012086001c0f400404482d905426500d40f945591710418400e041030b480f15a0148c452a003440441d504c0041d000171031024891011408825110354161000000c101090940c0c0f038681240d0001426a01d120341d001952041190242d030402604281203d0030440310303900e0785802040200002c000501150303050700741d0710f0f1101c07150303055030104941c503946486c1c0060b0a07228003001d020390030b000750341c240100c00740800807030710500c0302078400c51a82d1404a80e80e1214501290b00c101c10094850 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 860451654 1250 860450404 860450413
    0x624030102090f040b0a120c15020c032a0a081e1f0216150b0108070e15090a1502061b0a02030d0f06180e070602010603230c0402070f05010e 62
    0x301541c0e43d00303100701c0f40b14006490010341e01c003482d40458080c2e51503030001e0400c2800ca1641c40f00b000f8001d00c04400b9541c0400e4490080142d142e02640e403441c0030128030754160000c41902600256001c05000c2000030400b014041000030b1010505451300d941004115400c00740d400820441e4009000810192440042a0001501441c034660424001e0209641c580001c0c0c808007040da018001030f800758218480c8045001100c0e031243c010302c0180c609030f0106601c0c43c0024059805943e02c0f0b09004000707070040c1c000640d048001040b9603c49091154011703444040130075402c1e070303044103002112040c0d0004c01e194203180d0019a103d101c4081c1518514008000d400d41084e8040140c075410100c0700c81c045030100708070f801d000c0544a0341e009640c550a2540685c00b003c5c03041d0300710681c000900340a0b9000780781c03204012420b1310201e000252020715191f0810380182c01c130300e0b00d01403020701e0f00f401c1c1c88c0800b030b540c2c0000b810b990140000741d07521000e202c030341405d000082c03017103065001307241c030082 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 860452904 1250 860451654 860451667
    0x904140709030311101b030515060a080406090c0303080405070803040308182202070b0609090a030f0302070c0e040b0a05010807060f0314010902122a1b0624030102 72
    0x10191081c5000040c1001440501020401c604108240040e0b1002000703101c004041a03da00c3e268071203141c89030019041c20041441c41000385490107800c04044c01030391a001a411094403080c00107001211415601c01c0d9144c0401c0b08419400b0140d44a592004441d00f85414114036010315a0032645064008100c1040001c40708030884920300302140103046038180c0c01e400280ba512451610030802d07070103c41c145142ca0011b6009080161081d0000038158481a0a0001a56049038040455449002c0d6440424003170226040c40f40c0c86c3d407601501c2c0c8401c5d50780b400021440ca5000416000707202c02400200b001e654042a03118000d00c004100c150b1415086a036541250310400c014492040717060624244a0740003104c4c6e1030808403e044055941d140003000a5000e8180041e40007a40310110f00030551008d0085800c0002c0062103a94228041815545900c0b4039190810030101401c1c4204444080c04001d2040d8041502c0c0301ca2020000a81c00d0010026440c03d8801c0e441003010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 860454154 1250 860452904 860452907
    0x60a0213120302030d05181b06040b2809090c08160509060408031804060f0b0d02090a0503100e0f0a0b0109111b010213050607021c05010b1509041407 66
    0x50340121aa071a450030300158803410107900b0340c4038101c4140c218034200803c0007010f001c4034181040d442001c604552070030800902205211030b81c1b40340d1542c011002c0004020075805500070f058891102d60005a03049000000015000003522809000c02c0701444108444100340c80341e00e203254141c1c103001025143c45441c0ac00001d01c4c0d41d40070014861b0109003000b032511040203542c0500f010b001243c2d41c40c0d081c03c0440005201e02000d192045007440ca001c035646d0800c1ca0382e802120240b174929801d02c0c101124500282d0803040d43c0e560000b0288000140c0350b40c0030071030000c403000e4200c40021900f11510445080400c0d0a02d4480160b00080160000074403180d944c6046882444000500d81016415034000f07110303001da15201d9410000495003c7c110650042170100280e0103001c00e030039643c0c814040c09004240020750311032000303114400d0340340c484481340e840544150000140c46d005000011041d150448442891410110f04503003281410300c070f8001a8001051010703904d10f0a502e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 860455404 1250 860454154 860454187
    0x30a0206160e06120a1d01090210111507120c0f030f06050a0501030513050f0610090b1507020d05012c0c0906060a090321080f060109060f1209060e060a02 68
    0x601d207800000c050006221a0095032011071002c13a0003c6c814542c0c0c420320320490207000140c40c04d13417240080c1d0b88408050303400b4102200025440d140a4088156040c8440c2c02e2244001c1810013808000742c45095002c1039489441d42101c4c05813641625520f01c0360380202200c48601407881c1076494880140116600c0c40690b00132075109280c003140f2907980f80c9001c0c451030360407040100305200d6455103a48004003c554284203200c58403550040f140e40346c07049400d4030740c0002e009400082501e10400d000c1644001003080c6800500003103200142503032810b084400d1110498880b040030000c0c07084401141c0c1d80700c240411100000e080ca4418000080c03020703074028018612402c0b0005034029918082c01c520402150031048080006514070300d00721440070398051030710028500c0700c005040180b20074505401410b041c1e6945c0d02c41800d1200035038001d1036600c044000d02c1404000400f803140275000d00021548031744008201c903c0d2011030640742ca10080c3c002040c450060055443d00760b419807 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 860456654 1250 860455404 860455417
    0xc10050f0a06060912170a080103050607020a111507120201020a030c020f030a0305100e1f0617040b090111030421021f1a0301090c030203060c0c03030a0b0111030a0206160e06 77
    0x8006030205c211901d0210840c2d1482100c5000c0c2c440c02040c084142c0350402036850480c2d000b002a10b82d2036917000000c0780c070343d0442c10b0001c10481101004403168280008000010310000001d240b4194444d210103000382d00c603400d6200103130740008654022503814040c0140d5814140014150401d003041e030b230740c0c6034013a0320300080030107076510001081100c2e1441d84c00c00810003016484198101658071032800c150010503020000364103031000400911035282400c814800405105d502d032921799510f02d0300300d4060700100c410340d201c0070f074104500101c4000707600861050901804075100c1c4603503282580310116003a01990807030092201041c0100340d04402e4143c4407080080e1100000d659074180c0e803e00c0e02403980540c40c0c4042c03c007c01050308168400d8900803822910303655150050b034103031403185100243c0c0c0d03500706001140440c419a0440c040701c0d40141041c038004c0303903c4c1620070702d1034015094410040e880030b41446113800300c004601400d001c0a1030003191a201440c0070501c1441b0b20b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 860457904 1250 860456654 860456669
    0x30912050c091b0f090118050904060509070f0816090c0219020616062a0c0303050402030c0306040305040e0c0a0507020d170c010614030a03230c10050f0a060609 71
    0x140000d16070380d011920b40c042582020311515100e8884c22001c80c5941c01c100c400c035001c030780e421b100ca814504e5040320000845000410203403459860b039030380030f001c0e01e000703403004a07039204121002c41d49021100d964400b4000c0440180701200040701401d02c1c80103203174007042c0c83c1482e0803110900940d0100d82d41c52080307c0010302c1c2403410640d1009c11050700c2450301c07801c2c00400010144080109a0f007103001300d00b00c034011011105829109052400c0c0e00001c0b0040031a007085000c40009000f23402283d885400101039980d608056408179003800c0c82110103c00003400001d050040c8221000650303000022a07d003076040c0040301e100600548070350100a4416211002590100444910f22003507034820b0444203900c40d110a40c2d054041c0042e4010700b0844a030b442c408032524140080c02c481c8031134142e13441e102854001c0358850301c0403013a89017400c2082420803080c04480d0041000e00d0014101100015130740c90003081903110701c04081d1007070000f0303410000e0070443c3c140e21a03900c10665408 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 860459154 1250 860457904 860457919
    0x105070302280c080c21030105130b06160c0f0e0907060804030206190f1b0f021513030903050303070e21100507020c1e151303060c030b04020d09030912050c 69
    0x5c00000e1800e82c680f5070a8100340103814420b01844610006541200e1007503030b040e0494100e50b26a401034903001c50005402900601a490791034406a00000c041406124042103032501c5000700d0911040c0c542104025415000074005900c1b81000018000c1070a80342041c0301c1d003002c6d60002d4980c41c0180094442c0300410021048030b05541c0c1c440e040b09a01d14401b041034000d417080112003000304c001e0143c041034200c40c4050040b400400c010803841c5404000042a070340392480d4003080c803200401501000b000c4035011001600c02c0000314080d04c495220115000750040c10094040e00c603c80d19080c45c00d0ba0461603055190005050303014149003c0e002c43c1e02e9540d0a0f04a01c0c02c1d243c9181c00782d001e032104000200c80321b06140d000904c01c4040d150324082d441441d4020000703101d00403290744c800c43d800386c0410101e0211f03404000f5040083c0b80c0881c2c038044400004060b40c03c14079601c5a103584e40c5101e1820140c000316003130001d1241c000705a00148550321256209c144c0c07400101c1c0074000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 860460404 1250 860459154 860459167
    0x10e120607050714011401090e0c012a021801030506070f0c032703080304060b19060509040b060301090e1b0d0b0603030c06071706030c09270105070302280c08 70
    0x1c1ca03000304005800f880c0204641441282d0101806e202031003515000d616002e04944142801305480020420603103484410002c440400f850b0701017100030702d5410340410404c05005030358040c01c910200395041074203e071075411402e189082c040b0241c818004d001e51040c0c100500d40e044642c0e9100da58041c20200301069014440c00403070481d44980c00d2806005040c0481044186000f41d03004502880080191000840034880524800b003a205061074114900308002442a002030403c408041c001007040e0401d007004c01c1c1d80750400c0e04100c481c1c50b01c60a02c64850041007114100a41d102070a1101c0301c0e0303149010868441c1c40d02d4000d014142c121000442540f4104200e0302140c00100460b0620f01c0d00110080107440501d9911084049510110303d0700d1070005440590800c00604a0035030751507003000070b240c5218400000a2202502c401d808502500303104543c41100540c1300983d95482008070803049512074500348201d881806604a252a40900180001e6034002c0066a4a91 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 860461654 1250 860460404 860460413
    0x220c0f0b03180a021c05070305010204120308010518010e07020c0405071101050a0b24040308070302070f0e06060307030b2d240301170a0f03090e090a2a1701050402010e1206070507 79
    0x285180c0000c9c103590300000b80024691010030314240031901a07518910141d0325201002003209130b468001d500c0c03140e00801401404018a10a42c004015004450080d450140441c1c19100e04980c4500032904c0d4041400e4003035001c4c01180d9109524071801c10110305290700203500d603500e40c6290500c681009004406c5610000308840c00707144c2048509446264928000b55502894020302003c1c00c0380050001c1c85440640e6a9802804010081ca007140d8610700d08400400c050b855055110380010403000c00e2006280709048d5800d250144c2e090900d55841c140903004ea01c12807003c40300411181c94090741c01d00903069a043d01ca1503409a002200d604c04007600e0010f40000107017142e440c41e5048001c02da0040f2018045030100e10100280c0d9450b117142c02e8451403030443c0030303003082c10f00894004800c0344041a200b084042c0c0c52000303e25521010030800400305003c08403000d070b6480b01407000750340e009005011142c80c211002011075040c2c032070040e126040a452541801000b051050400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 860462904 1250 860461654 860461663
    0x3030e0315010e0105100c11090703090f060f0e031806070606051c0c0b0319050c0c12090a0f050112020d06090903050d0e06220c0f0b03180a021c05 65
    0x24031404070708410658440d090104101d2007841403a2103192000c1241d040240243c0c2d80c544030719041131110046000020034040701100040880b401c05a8411090300015446108100d00078001c180000b18622542900c10842c2c081c040102c0040e070040c407081c43d800c081044006842e60b030035280d40da112143d510b400c6014010903008103a119260204500701207003490800301a050040b00444141076454000a40074070003940c1f044c800715850050203402c1d01194008070b401219407101646007400040055003814000d00a132032a41c1c000154401843ca46044004041d00c040f5581140c4149880b0010704943ca0780400c4007581d54001c518000c54611650025009140240b4103105c14031003454010010761028800d06e54132440c0c04010040d807240060a03912500100782d8030484001c80c28014450000130903c02c45550348c0d02a804034454810b0085a0000c02c40460100e40300c1c00c2c80e64100d4991407444000d498260310400780907025944212820700c488860011071200e0042e02d04019080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 860464154 1250 860462904 860462923
    0x1a091f23190221070c050606091b09030c1504081b0d1719080708180709021b013b03041202030a0c080309040e0102040807033206010323060103030e03 66
    0x20030360741c40100130a25030009040c0031110b00c10020b0b140340341c0d83c404c2049006107007550f50f074542014070400100720764a20700c001c01e1583c80003000c40361158444400241d02c1d002542210b02411800f0500300700421081040051501c0640500300700083d40b0000700340300c1c3c1c0540501402c8501c9542c01c0c1506100e20104450808501d004203400c0c205201d0300242c403920003030b1a0754ac00240118005003004030040403803018410880d0180002c03602e441c003948083c1d04028030480460300340b44000c4034050802d00c01c41c0604c048114084001c21282060b03c03c4004150700c0c12551543c0c0344036444d00b240c0010044409071400c4a004801a03001400800d140c40030f10b0900806540f179402c0081500038000000e0503132460b0841781404222440806da60903401030340700d444000c0c0d00030395060000072000d0814a440700d0410710b070170303064040f540a6858001c0d20072080c0089500310400520034040000c65506a4240c8e01c44100125039118140c0c40c0d9404d01480098100f02000713014120664042c8401d950 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 860465404 1250 860464154 860464207
    0x1a01030b0d051510060810060e04061706041e030c020427030909050709051f03020c0a080702040c053c0406020c0301181a091f231902 59
    0x912114480c0c440c0d81c40300144e41da07841e0704d5819000015001d209804240c4a110844a4454441e203071410a80321303075001c007030450f91258840c4004101c68444107100c42c847d41c60400185081d0500b410034465000100301101d505c00c0003030b10144007003500200081082c075815a80014281a02107000fa00803861070101040ca1a00810600c1495403009600c420307554204e000b000182c49044054032010103903c101b54008009510560303c0fa00c20404001c22100c0d2400d0140c9000b02d241e510740d04108a04000b1034014a01260741c0c0154201481220342602c02800c0143c40c05603661105c806031000422101112454254686c50701d6a504440031307484034807242d5070364407240c0318440130391200d000c120b03001d0180d8030380b002801740810003512004203580c01103880001c400d140510010320301c000502c8600240b140400320200000d21084882203426001ca000aa0305042445103070240d0081c4e5034515000c2d0581c09001c40c1500403500710303180c00160117005940300500c01140c0d507a42c2c946c0d1029507 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 860466654 1250 860465404 860465413
    0x18021216020102040b07110a0621151e0911041a16020603070f12060e07052101090207031106060a0504150503011503050f01020a0e01120e0105010b04050a0501031a01030b0d05 77
    0x702045540d07400301f046060708541c0d52990940701c00c41150030205108030b9060351070419420000d414519804002ca46451014410b41d894681503a1411204d000341e1a8081a407805000c008e100618070400984501e0705900d546468544030120303030ba40321030b8010105508400581440640c4401d448030807081c0e40507116686a14103000060080b041240380300b40403a4003030250b0140d9800c0c034031890b820b48641c103e8003845a1117028046640d508125000690180c000c01011100054503414900034071510b040543d035907880c2c1c9001410aa400035a1900c0366000105001d000d595500f151020b0300c4060780c0000b440050007000d01c440c10f88982c0102e806500c0e007042c2c040000040954141a03038020b00440b042d801d080c00455080388581c5000c10002403c405030700300c103503100d00328034800f00442d003002081e206071103981c1c9801c41c3c000307a0210070704880024042040303091000d06800105424202000a01008180080b074182c07864074003810180d8a8a504405a55180555403c00e4210044a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 860467904 1250 860466654 860466667
    0x2211513020c0d020a050307060b01120911040b06181e04020c0105010e06060301121101031b0206060a170604330504110406060e0d05010617030418021216020102040b 73
    0x300c0254000b922141c203c1c02a4100800c3c058000552002950381c854021441e001d1182c541030300a00a840500781080070080a404007150745000b081c01d00c0c0d0080c41001001d0b042481048200c49d0304e820640d00903c01848103c10b01880950002170790b8000307444803a458601d0800300384c12945010f0903580d00c40d00c00b14103040c280742c05500032810385e0f501c1205803601d500d581080020030301007442461015404440c8420010304d24201c2000c01d0382c03060601048070100d018203000ca5240401003400141e0010081120518000e02c07030f0f40040c03038900c0080d603510610840032620751400400240017407482c0f44010300c0d560680ca600100e014134040c1c10807581c03801c0340031000151100751000c0e1036108042c0c05040403460144603c0d4100ea90075103880290b40320350b0091103121301c4120801e030781a541c1d4100c001400c0c440c4410b00c140c280c54010185587c0c9050540e1110102c80d072039000c1c0c079024410702100020980a50100d5004140040e090519071610b5004178003901c41c58000201d02200441c04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 860469154 1250 860467904 860467939
    0x703060b13030512070503070602091801120c0e0c091c0204060605030103030801080c060a2607020d17010803030402010507060209060d020903010507110d03090c0510080f0a022115 79
    0x45209070380c403c1c4259442201140040f01c0c070340c00340503800340c4a81c104103c0c0c100041c086078010100c1c0d2001502c46228107403a00c011b1000c1141c26071041c016021100c065404010b254a09000508105001c0140e2800c21a24001c0240030390460a03016a0544032144050380380e810507204081c0d0300800500030303140c92380340051903500284000c401040a034030001c15020030200d0a001c40800c00f5007070b50700740b20120b50100c8000309038944043c01c0801050541000684d008440c912401064004258070303d080b120040c040d06a03120444c20001040c0c00500c8403900110840c0e800580920f0301c2d0703071a6009814240b00a115051032a584520000f07088080d1008030340280c080e00004030020011a40c4106040c3c80c80d00b144840100039400c10300d01440c002e80a58030090380036000b031400c4200251a00c0103c0c49418010310760300d0200c1d0040b001c00100c00c2c1910115a1300540000303042d81005110701c2407500303904950443d169412012400103110b07141c0c0d1803464190980040002d2580354803480b030b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 860470404 1250 860469154 860469187
    0x180506040303050919080337110c0306060307033207051315061404031406090610080a021e0409120207080a02090c1b1c030b010c0312050703060b 64
    0x3014000e00c407141200e03042a222403421710813150303040c0c059890160800440440f40d000f98880c45201c0c00601000030001d40001d0801004403000c0d00c803050f840281185041c03810584030b55583c443e5004c0701c10804280c40100b24a030803281d20a0b0a141884c61490303101d41c1620504500a0307001c410514500f110ba100000d2120071144180d5528004000894400064400c03d50300f40d614030b03000c0241040610301ca09803e003410080480e400b4141780e100d5460b004429482e6003049410303400345051001066043c8240c1b03401010500096074054a807400d003d0303c4000364400684502c2a01c141858149040c45040310005030003041000b00404510f410707112054420300c100d005100e8000080340303440001401c1e40c0e4807a0014005059643c404110f0880703940110a202d120f10411002034440704001c1000102503007401400c240c04503030008008040751403800c1c0c070504000c04d03500c1b0500441d40002e1900703203604010601007810343c0c0b60300080d4003406065005143c168400900342082c50760258 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 860471654 1250 860470404 860470417
    0x6180405150f0c180609060406090314061311190e100602030a020a111203122d040f0302160f06030b06030408090d050c19080d110c0118050604030305 66
    0x807822086440c0d00103228188082111000c4115070300f045180c1d0981c40c1410388002002000340781030b14061004007c17801c039801660000c80844c10814041c0200185000008014000b400090280303150014464100200b0700d0b4014115035410a0652416102d41c0f01541d590140b40780b00c0e103a4543c0c1c0302d240303c0514400b19040c210f02010b003100410f00718170200841d481050141c2c010202c00400d62642c0c288100110181c1d0352200f00f001058081c2502032020705010800204083c14500d06400043c0b99404090244074003020070040001042440c115000d42103500005004400c50b0b40b0f18007a4500301d02c62080d18042d5054545c0003501502c91181c00d41503403456030701031064064010601000f4081928024440103090142c0c0507281440000700910303034003034000c0302d02003009800416051040e1181c24070341c9002ca9038061015036410806141c1071984c92402c4038404120704007080c1c5078010ba0300014104111814000e0050f01c44010000207844000e003c180d646a03640340c0a000d1342d0206 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 860472904 1250 860471654 860471683
    0x140a1b082a1e060612031e091507032307050a0602130e010503060109020703120c02030d05070e0906040507050403020603091b0d080a051b0f0115090b030a0b06180405 73
    0x903051030541c040c450359860008816a0003000b00ea15010704204665402c0100e40c5c0d11440107000380381200c842100c8200558070b514030550741d0352548000b8440e1041d0004200864445d0410030600000e030300c4440c5605440700c080111101c0c15082c1110030280c0b2030305a010f800d070320501650a051105503401840030509040d504810140d545840000c3d002e02441245d0703058000000402825081d030b00144041e603c2440c081e070341101110444012120100c18400040e07002003503444e82c0c0040c0340315481d08000d00341001b15040c05c2c01030010b03030110001003069000366190000b00348185d0181e01a2400345500400017500e900d1b00170001c40d41d492414185146a00520368000e2581c2041c1c0050208185c200c00e0316403804404140c29202ca0744a10381101482c0868041100e8000051103105980304c00032001040e8800304200041540c90300350054104079181440d100869940001c0c00b44446078803038500e00140d42c81c9000944440c01c28045404545d512408020402c4030104185000b91800c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 860474154 1250 860472904 860472913
    0x6080622061e0b090f03071a0c060109180228030605040b0a0e060a020c07030f06050405120405030312150a080d030c08060609010c05070302030319140a1b082a 70
    0x7542c1c8101520091080d0341075a02e04106625032070500a50b4051203c9010b01100c0d54665107100d4481c080184072400300d1440d01c0400c181c84441001d0001c49e00500c11400700b48442213014902d040d01241c200b0000388038400220380e40d1600c04402d90300c0f82201b061015214151035980c1403041c098081120f0455070020040700091098589100c0c0c0c2989540200080200341d48500d0b140b0000d5202d110501c03d94401d900300040041e000107a100030251041c1004070b0301d4189884e0851904031044c801c1c41e00c07000e0a1005020310740300082598500c803003e0360600c400e920b45200080c1031070390b011803080d00104291800b00740ca050008101c20110390350790701001950902a02111010340540e01d1356440401000304140642c843d500082d02140110700f980c40e03403956a8000791643e4001a0018015201c203143e0800b03e980225440390711200b8050000e01d03005072036400070828000d80055003005002c036840c140038054000181c6103040120030a6400c10040102808040d01180d01180e810344078 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 860475404 1250 860474154 860474189
    0xa06030b01090608010b1014030a0b1c03030c0806090a02071103030d140c070201050f09061b0f1501030c0b0a021e010203010e0a0b0a05060307020f01020706050609011508010608062206 81
    0x108207044201c2c1f601295915400d03034900c40140607881c1e0020700403a041c0b903113501c10b0580726661030007001e494500300c0c60003100c1c0000c0303032070302500b61089a2403c90a01008004100e5240c596480255021352560790059660180d0315007007681e13281e0388407842d40511000c2844800c558035035000103d443c5403844901c42e255240902180a88a41080280012030078000c40e40501307031110181002d0301c0010020350810101c0b0514480d000403444120030b031507115401e540101c05051208040401c81a800030302c0543c1152950007038000c1d98412003010300400641c44104038400d101084280401c5914200b090400c80c9149020390428004c8910320003240d000316243c500b0300d100e0006009405042c2c01401e92400040007130710b420091a11b4158042e405290b003050501384024a2068410880082c2c0343c14904d0034801c100005810450190300c001c0103140d41c60743c00166007411500d031441c2c203c10640e204404a400d18008910100821414000c5903240802503003108054803a80c119802a828 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 860476654 1250 860475404 860475409
    0xa0e0304080a0210170f0402040f020414060a020a020319030905090106170a0f020c0a120c030c110105040e07110f0d0504090b0d081303110d12080a06030b01090608010b 74
    0x1086200d062031581c00242c0640040c1002e40c0d488a08203143d09150044051240b107a0000d0b60040314034160050039901007000318038151207003240f40031052004508090500c4c082280d0200c0c070410162107410302148910300300d8801c024503464664007800759007005075494007142140712007a02c00c07070100e101800080f981d810803070703800da0407600300c0e0340c400b41162082e00192074107200207400b10b0344003911090070840200280c002030120180410007000981940c0c00c0034600c04c0301c3c1c0300881e420401c4030500000400c2d4080341e880021f90b000514445407003403500c01603c580c4101c3e4080040030030748104104226400079600500c180d030810694000c0301c0134000590303d50701c7e09014040400c0c0140002d1001c6441544030380a0060702518003032640000e5200d80c804e076000b908a461001840e500d090040004030600d003640310b04165488041a0f1440c0c3e00d218101031952054010003111000040c6601140c0e017001009541165048101d0750b100c101500182006008070562982480c01c20452030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 860477904 1250 860476654 860476657
    0x708031209010504080f0a2a02010201051e010e10030b0c0910020a0305030c220e10120b13210801050f0108090706030e120c0d032403030e01031508060a0e03 69
    0x903544041101e01e400c21b801d408104a80140803d94104080041da4501805104000c1501429000c5052540c580b040c400207080d60002840b151110001d403680b83c044070b10602000d419544900411045541c038040c0c000003a00e20790340040c1403c0c803440140002e005404008001ea4001035410000c00e07030485000741e0b0b642c40100401000280d0400009800101c05406003806800b84e0078400800c0982543c56980d0038140d40000012943c40018000d40030507070f0900070010400719000002c46000f584070000300d004014507040c41d80ba00c8030f20801c00c000c140c28030f0501b0540c09401c00400c0142005000340284c109009003401421a1f0003841c446600412000348254010030050800e10b0070804100d01425100c140704006203d0320030150413050100000c4e0102044210086c40c0d044902903008003500c2450101044481100400c80d141c55528001c40080d60b03003600700b41c9451201000100c004000680070380c000c80310400c2c00414801c40104d079280c0a03e0000c001800103140c95941b840c1c4a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 860479154 1250 860477904 860477911
    0x20f0f1e04060e0a0c020705150f030c04031e0605060d1509030c05151006030603020f010e06040f060806190806041115030c1b01020a0509040b0301020c07080312090105 74
    0x1844000d0441050250250280d1021101400100d5441e9a8000038100303603d0a440820a090f16410007481c0d03603904022500041c807088404666603c13100b040c0040a10903e482c4046403880040000c01c9804140201c0d00155031101c900900385804445905440729013140403a409800d010100e07e5602c0e000090001c190740200d010304200e07028800f29001082520030490038440401d5416022907005d21230a4401c0b80b5110b100c0701107160020007a008402d46800003018146450300070320140e1a860480c201040b13003803c00030b414810240c00601d6900407644042d0a0409a1401060480d44120041d00405003074421403003481c0c03201960320442000c0d00401d1180d521a90009000c0707000240d46000c00352025200281218411154440903402114110300b00d4000054482546d544190840d030348040c64030085041404d0341070000c090303100e8200c82d075110b25200c2131140125134080d81241c10841c0580216407078266034118090312a003000442d0390b550681c040000c0c01200060049610 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 860480404 1250 860479154 860479159
    0xb090103290607150c120b0907081623070c1224090b0114130501080c01140c030c0604170f04031416060203040f1e050f030a050307030309020f0f 64
    0x24201075a0140003543e00502c81c1640c040f44942100c5540024601c02e600018500b40e5070704500600b07854a600a8880a806d01c5008508a004100b204c5034444907198110302d20403400780442c028118115030500700c0c905441a11208219030403c00f06904004003996442200d04403501aa101280308170010450f00150645200c06410400c0c0c03880d071300810124615810000800041a48403c4d0151109170081450103514855568480c40c0c4900d00000303c010000d414001c6604000b81103131242e0394404c0550600c4038480704c401d400c04031281569030044000003101c3d00c440c00048690703a2580305803001e840c401004982c1c212a00c2c0304c0000c40b102904502070007071905246580c0d04940188015964a950140e60910307250ba191480b910702c010b0149a0040d40c44d07509100f011394080301da540c0421607495038040742442d002c1c003444800040382c2c001c55590310300c001400040380c108440040300030454003000138080101a016401181041d00030f032014a11480c0c0b503028421018000d1003030a5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 860481654 1250 860480404 860480471
    0x4020d030c05030f04030b0708250318061a0f0307030308010e040204090b0709031101030b180c04030c06020106060f03140402040e031902030d0b040507051905090a0b090103 76
    0x404280a0418201c04602c10301c02c82c1e2505424440045041d04603400454402d08107000b40999194030901c881d4104100340380304624003104130080504800c0c50342002080c5611000803c0e07108103414107820b21140c0240080c84944110300d0069800380091110303d01c644000b111120050a002032901c050301d80c191140d01141e402c00c40381c0c805010005100300e82c820348480d02040069036016401e8095a0301d40c0301d2040c3c3c98110f180ca2014411200807131810545060809101c650352410845c2c01c100205c81c03403004a445000411040e48a80d80001d80161255000000c603664154400012a0115520b1030f02d00c108008045068441c8406180c403655040e0703002c0703005842c040c1c1c41205904201e41c1140e20f850140d0024140c2d0344038008a550250b0808184015000214040c603143c201e0115000c0080d403030b0084002d426401202d40071071582028182c10303a4818040c01c21a061f100700146240740c1699100c00b01c0c0510391200d0007444c00a414040c100c000c101345060484d01020092004d0b6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 860482904 1250 860481654 860481679
    0x5070e0105031f03080a0c03030b1905130e0d1d0303120a020903151501031a151b1e100b0310020903011e05090d020a1203050a1b0207170102030402 65
    0x83e0b9005002822014280c07600000009007414008182040164540d05040301e040d003009421aa00780019034000c40c0c0540138507410f042c001050000740c807000c86640d5401040c840350800205166031504019100e49085129120b40280b8001c4803102c52041007401328101805164490141c2c03886804003950b02c2c0d010580800d41da40103480320324405001c030307241e070005443c80320340d80303001650450810801841e54031035659045c01540b20040348280316002c40a8050041201e6524001c0580c40d1b510b0045610341c000300c3c0c03103050182a40740701b2040b40c0d501c4152003e000000b140c2c001c00c0b1010b62048049001240406001c1d601c4030350802000340101d5001201c0b01e00103940031011056140d58bc03031054120518492480d40c03031590401400040601d0104806032404480120000941d0b20114010000450581e403103500c000942c540460103448101c0c0c100003900140306c1e130107048032004801038403075a80000c408080300c52901e201e480e128448081c0030700f02d100556010f5004845c04028 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 860484154 1250 860482904 860482921
    0xe15030d1409100305070f091a1c1a09130f020907200105091908161712091e032706070507060306050a0e04060903020705130e0105070e010503 63
    0x40c141010401d00c034040c0781c5050007002400d4101c61001c0100071070f9035202800f0056034003080a2406450300d06161803401d04080801c85a0600d10000010007100040d140041c0f0941c43c0344001d0060280100f03103c0e044143c07140c2e000c00e4402c03114441c000c4454600040704000a680400c14180c0c02c1a075017800c1200f65003e100e28200018610410b110b4100d454513a0b40190540c9c40381c24400c84030002519061001c0c15509040410074407202203900b401c08480801d03100000c484040036901400e0070059002d143c0100410241039001c50440d101040e0910520706c0702050910594001c0d0544001120100c401c08403102d0304030041c211540f080c004442e000441c0d1003403c00d100d00eaa407601002c0006180020684d51000004580903007042d501041110780500885002c0e0000b2600c0006440c200050014003c1d002000500042d80b1000d101d000e150080c4403501c003a02c0d015001e8030091b0802c0754840080c2a41890350407441d885d003070008248510640c1d003812400c2c0305070340301441c6803101d240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 860485404 1250 860484154 860484167
    0x210091d070201020c0a060b090c03040c0b0903120d0209010e06040b0a0806030304090612200d06090f0b010f0f0f081e07120c0311041509110d060b03010e15030d 71
    0x90100b959401c110100500300208020504a481000701159400000d4240f01321100044d001c128a24070a00c103100c0018682100303003003514042003100c0e484006410009190503258566000d6090000074140c0c0f1454268009000794442070300c07100d24140b46e1005200203840b0381d02c2090071681d8140105440c45102d04c050035080b81d4014101d030f0502c0d0716036011000300e0304254000c11800600010380c10070400341c0e40040766620348100174800900d811101203002071000c1c060051001d650f9a9038801005010500b100c1d078a03030403e0751340e6103560f101e11280302e41c00c000c3c0c003030403001d0845080c00003500c1110904034010b4540e01405007145812091072100a03210a2200b0103ea0040c17074404540c507020f07648019510340c02800c0315055145182041400322046c481505d009500f490700a084140c2a10450001c5400000c00000c0c01035441103503000900581120306032507810103000242c00314071013010394182e880109038441c068a9951106011101e00d0404c0313074040d003040c0c1d00310f0807060003182e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 860486654 1250 860485404 860485411
    0x100503031602190b0c0f070509060108040f15060f0506070f0f020a08030f1206091b0d021303150606180902030a0605031509010507090303140a022103040210091d 71
    0x4010380c040b180e204980d1000f441e0700750400b4110030008102c65110400410602c0a5241e41001a00040f4100b00c082502d241000382401d041c40715690101e820004c1c5100791102032900003080400c1000302c4051720010f0511403140402410341a00e002c1071600d0084100c60701030307030b1200025410207031075900c0100501606000fa41e001e0040040041e11703801c28401070030300380000c51040b940c0340481610342c0d0000e4000742508d030040350030f1810031031654040c41410365000701400780c2544610071105c0603000381c0f1510301d900404940403100042008860900c400490801e050140075082d16203d040302c4841002c81c2c82c41c100401c0f0001004101455401140c101800c1500840c00742d807204046458285003004a0207155102c00c2000420642845516041642413911800c00345c5191401800d64107ca581420320341c0000503c3d8074124001c11003c500054a10719001034010300d010001c4054100701d400303034042e003019011582c100b441100d000081c0c803450900501c138000d100e0402460032200a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 860487904 1250 860486654 860486659
    0x111005120a0506130e0705130905030f25050307030e060c07030b06030d08061f09090c110c0f010c0b130c0602100e0303070f08091002030c1e250515100509100503031602 74
    0x1440c006002c65405c1c40100cc0204050014507558080601c000c03c0200303d54940b00c46c0c0a4160800b00000307107010003110b80003501480c0c4040a0b060801c0043c0d81e07481030a0311100d003441440800070800400c4001c143c40740104070190340e01c2490070700042d90004000c50f201032b803140c118040100c20b14007840a50030700d14180d01e0840340c0a6280d41c001c2c070868100728031074008600744213031080c8405410000311300f940d0000e94250401d03c04060000e41328800700344008050071a5500090001c41e0500d25400d031058000c0f5500c44925640e0358013070b48544540003401c2201d400c241587d41d41240000c00c0701e006a00030707520081510410034045075074a00281c461040b500409480000c1000030b4000745004080740c01c0e4290365038800300c50003010b4002105c1a14000c003070030f0212003011201c03104030f13180501c0d2800d01d42020361001d00e4941c0c01d0001892040890360101800c1c0899880ca5045100c10b03940181c44000c5a900c030302c145403045d141144100c583c1036000700510030000794802010a2085e102 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 860489154 1250 860487904 860487911
    0x151403061003020a03171c1a0f0a05040b04140a0b09010f0f05012d411b060c09090c0304020a06050f07150902100903111005120a0506130e070513 64
    0x10314416076070f18503442503607d501500c40b03c42c180d00010350318440c2d03008101241d10f039240520380380106258904510501e0300c074954560820506880d00c6d0401c100e51001c2c0360514200340f90041d02580140403610103103000f030a50b02d001044030341103030792040d00fa00e10802c1c8044250345003400450343d0400c1c6440303020784111603500740301152123405035040325003401da298680044881e004010740c001200749a450601e024401d2a0b542c0000041c441e24250040d40955a0321601c5c61050f04042ca041c1104418910490040110720601d031009083e034030100f156030f000d081e15034034194515030000355800f03503110003551420820140240d0081c541101000022810301d617403a102d0310080a966403440350042c2d140c282e08011843c2103000d03c081407503503042000180f41980c6444e17140e2a084610140541c0e04640c0b1400400c2c0120f042e41e1a00581d01614040362808100d010080c040603074065008103061500c15641a44a010301c9000410781e03002015110f14100400c622110346510a20b0056075 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 860490404 1250 860489154 860489167
    0x31103010617040305070605040b0a241403070b130306050a0b01020303070f03060803070c030510020304150b0a0b030103060b09010e060d030c08040f030b070f050a0e040906151403061003020a0317 86
    0xe000e9103102c0c1d8001c0c42400458a082c4c0d02f62001d560341084030811808061440c0c2940604031607141e02a600300c0400f1030240100440801d29012054000403101540841e20749041130b00f4150001c02ea0744980c1040c41551240000d00003590320f00460140540c00c184005140c06106503040c80b5044420b15011807201d654020306070030b50b404940c05481070079600c0c20038414007008100f00150110607210842c510300c2c1c941c850a800e885070b61110703103440780c40b0306103d02c455540040680140041c005a41d55a580d00d262080042927071003030f031038020f041140c000200c080311a4882886418050403204042c881603400b21558404041d00312410380b01032202150100c41e40c00100080d506c200841d050a0400943c064482700345a01303441d08000042041a4100c0d90002030100c034000c0c255004201c1940901d0240e000d000030b0001d5448003503081d4000510743c01c140001009030304c810303030994105490780306d800e0303140c40d60600000e500201000400c2001980f80c01c98405545084c81c4141d04010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 860491654 1250 860490404 860490413
    0x9070f06030903020c100804121725090506040b1614030a09080f15130210050d111e1e04080706140307080a0c02010e12040603110301061704030507 65
    0x20140d40225002aa50395540c0341056010802c0ca6002401101e40802407a802200285543c0000300014681c00c4500340c180a064050b003a00443e00c1c034028110b80e818030b88840090003005401004c10158080181c08180d1a401a01884150351024002902d03240c20184840c3c03250f405400d9604c44041c0c1d105c18000420701c0642c0da66040c18002001d50f5881d464041d008000080d40d4000c01001c2c2c02a203015110707114002454150711410540e0b404440e40c030448379a0410300304000c00394100f82304c04076100301c1c1a480801460b0200540c02c08119079480e03840305141030301510030955111202010807550208004014054100c40f040c058100e4884940b00d200e8550050f42c0212040c1d807284a007403041641091100749044e1442d01e00c0d034194548010010b1a034040507103101314a40e591270034029003503c00c1d0008600c05070544100c0d0b0914419400300c2110b607006200304400030340b44c442c03400010328285d800c807030488000d5590188500c03410540c13801310400140c421828400100244030008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 860492904 1250 860491654 860491679
    0x30203060a020408010605120a0320060a0522030207030602032205070305060c16030c0212070609090b10021507120504050c0f030304230301020f2d09060703080907 72
    0x2615101c1001d42c4844c03801300b440303003502e02541240c1d201d002001d02c4006c2072040042d40c0700c60030307425240140d4103124481010551002218000005024000070090603c40d59000640034101c00006800019294480b4400540d00b9450003001600403440401c007280260b00516002600c0241e40100803280a40c115641d185107c011513164204a0301003050007401d11110764480c2171106c1c0303a0b1902d61032043d0100d56108038035004080c070032030f000400295100c00c4c47e140303200302860f01101da22680b5024084d101e400c2c00c0c401c03800c20900349403181c451401c00480303408480d400b540040034000301d000701541e40010001c02e80070400807611252041d43c5a036006580c02580228041c2c401c0c900d1010500040c084416501c0f8002c1d40201b10400c000126102490504d40c980c2d83e0310040c0109003000680680300d100071000f8070680125000e0880c40144d035100d5800445481c80001b0f000c502d00710011070b801042c03115903010f2428006c09021a0041402c60741c048004001c1c1e42009031900390301c032100b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 860494154 1250 860492904 860492911
    0x60809100608070e0903040b091e0316090b0f03032a0d08190b09070c0303020c0a0c080d03110306010c0510063816052803090e1b1303020306 62
    0x1540d100040410002d00d030b13140c1841d007201c1d10001642c0f4007070401c011105584104076445d40074a111001c00d18059150304070195080600400b6210013040e13000030800d04003614050040302e1072600141d00250b00d4a0303940f181d002d15001e000386041040c14803004c03000f401d83c3c0b5641001141c40d46001c202c111024420700d11b41ca2510713211000c40c1d0501c81003003030000031240d08141d909843c1c030000d822569240302045902a11514100400d0700b003603e011000390240d017001c0c02080c0300344c4a0840800c014900d2810650301d4500407200b108150b10011003d0360344542040c1d40410040000c01e1255110b4a07901310702034014000c9400150b1558540811103080d9440038002c9422141d10581c0c0394840d140c000244405580d046138410789001c54045248181403111034142da90ba4003c10402a0510454061601e494103054240208030300d01200c540038850f0480c0020300310000407900c1611000410b00440b050741200040142c203204014140c3e001c55082c0d03044407140300e8000010fa40c00c0082034070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 860495404 1250 860494154 860494169
    0x150e070e07080106080105100905040e01090f0602030414150703180506070810230405060d0507030308061c050a020d03110d05130806040f060911090a02130801150608091006 76
    0x10b0307562606600500e10501038000a00c22001090090405c2d40d00c00c58060548604480000b450912880d80c640107241100340200103400744e4040c1c0d01480f01c240e002e14800c90040113091640b6aa07d00002d0f00c0d9800b691941c81c80718400c2c00414102c40c400d6114070b0305541c2a0f0b09454044446448a51510004894038000104030b401000650b11916144400509840c1d156001000011000107940080c2d0b4502c503000d1a07966000417075558507142000c00c0e00da0001c0c181c41c02e440c0c6a040c000e117007031801c8070821300440c160002411400c180303141007e40309030010081c20110406900300402e5191944007038081100c81d5622624000c41404581082002a191941e030394562801c0c2c5203410120354400031030341c0c1101e82080007041030425421491688114000745d080001d141c0000ca1000e2420b0303564028109604116001a060307000380401d64240901e002056030f6901050300361642a9481c010100301200104a2030b8081c900c402d4000c07070840103507034900742440540750803a078241d8820301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 860496654 1250 860495404 860495417
    0x20c090f070e010807090e0c22030605070e060406030f0b060301080106050906240a020111070807110915010e04090f030e19140f06120a0e0f0307150e070e07 69
    0x200e03504400c00e40c02c03002007820050400d00c0e00e8a4041d1035200244510306ca00449080061541100c0361304075001c40014002c3d0300d90354821b1448108941c040d50200b11003180c50100070451403400303000da00d510100e0003410946002d04040044010304200d030300c941d004646a5071a4859940c03000c002d10301071b1075850300004949103003008220500c0e501a088038040c3c1c0c400c07283d5107041034211074481c03000e00c5000282b0f5650b66908034100d00500d1a80100007820343d0204000c81006150801040014043c4601c20003101e99141041083d5000b82c0f803241000020b08071110495000388010b80c3c01c040010800500c200b4152a2400e00c0d8031848021000141d011303551718030a18200c203542440340d15030050508075500380403070446e2107022400d02c28840d1000c10114081035170344ca412240c00c060800c0d406196130500312840005070000e40d07007402141c0504400340d41c020030000190359000c2e0300100801c140740034400043c4010404440021018010480081004d821035440d050151801d83c1d14031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 860497904 1250 860496654 860496661
    0x51311041e0b0411030603032d0711120d0c020927030d051003030e010e12010c020a121d041802060a02030306090a051512010605030f031308150f07020c090f 69
    0x20044a00344c0b59442c0400d0340c00d1003402220307140041515143c0c03250180c400c0c198101e00604d04178020b05410311002c00da0000030050100318540307101e0518010207a0b0010804012007240d81d460f03002d51002c103000601c0c07425103000580303030501107281c002200080e11030504090303050800c4601030030001c0c0030955100260600310300105208269020081c5621140000d003981e030004d00c0c61120340540707410040b030a4484104d960b03071420b08081010020000300040f01d0304041c003949818440005942da04000c4c07400710f8616004035600010700100034101d84c150308410040000070010398422651080d010b180e84001621031100030040640c15800031038132460110208444010700400035070401e8141001d1100d403501c0003469842c080780860ba242c02e80981d49141600528955222641c944550701d5180510600400107040f00800301114003086602c4031031803691391b150300e1071101c0c00103a4440007485990044a1940c4c005d12030b40305a0303a90481d1400018000c20041d00d0181140d02c420050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 860499154 1250 860497904 860497909
    0x120c03021c2001092009013311060a0c0509091305010c051c0c0c0b0403020f0d05130b03060f060703090509040c0503010f0e12071a0a090312051311041e0b 68
    0x840d9001006905e155540e10f03800d020903902c04044c410303441001c42e182e580300c10b0340c501c50469070b001944000d100c1001e00c04039a401401803c0c41400101240140d502017142c2100c11f0003040032240e90303074486030b05d800184410b0114883c00206540380c005034054500340000c5082c082c1e400043e00b160707122502c45001c40c01d44040200003d5400100314540b5001c0c4090701d411074444d0180a070031442c88580c542e6903080c00c5e41051010078010790640166515507188039005809448944a203141d0b2803119a241e0b0040c0c5e45a02c019168180e1150340c06941058a1821100401d0124401e10b848000e450b610300110b10141b0058a0440780000f264405000b00e0501348200c050511081c001030100c041c618444c1c50b2030311401000d00b0300804002802c3c00501820028080750301c407200d902c000061812803a25801030401c50b40841c009900d00c21041e050140c54022903000b2034903200780c4200c580b03196070f802d0042e802d00e0420a820a45800f9048600d040003090b01e0307c285408030f400708001c80348604 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 860500404 1250 860499154 860499173
    0x1704060e071d07080703021b0129152b02031510091e0f08100501050307180218060c0d02190803060f040608030d09120c03021c200109 59
    0x100e001026012112642c0d003902108401e41c0012490400403c00d40701c20780110040c1c07040c40740c0341c8007281003400d0b10890214158040400743c107040504603002b0f45d188608006225450000690202e88007012007103d0214a000340803c1c3d070902207142c1860703c100d02c0401c000c010400e0380c000cbc02e903002c403c000c840da21310b074002040301074200c660b24401d4844410290821001d8003454103456030740b451820b246585582d11202400380c500300c0f00c1c1015561840700e42c1c3c40044811b10781c003881c14400000b405040009100c0160384107500c00412088910010700001e41065044075811001034503000c00b140c441d10000c2a002000d003002e00f610038034403040079240220204100c50109441e131690340104000005807038028000b291150300c02440d00740001c015008542001d80d45010002d040d8000349819030100455034864280f03207118a140b1301043e074242100c0d0340080c025070042c0880395640c0718280c0a0300140e01c40c03410301c10107540041d620060b21142c20f07650501c550703650b00d0a003000d1104049 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 860501654 1250 860500404 860500409
    0x6040b1f03051c030b0406030b060a0f0b0d020f0904090510060807050d030e0a030804121b0e180703050601061101140124050706050c03071b0c05010c031704060e07 72
    0xea14190500d560341c1e141e91060900720810804090250b1018540e100e0b070004d0859510007002400301c00c1d02c03810510240d5006540043c82200300c5480080d0714440c0c200301c2c20854050b07110950a01000d403507680040e5022210040f945002008042305070b0341c4607c14032442c5070003140140407950b02c48400790100c07007250300171209592000c14200496900c2c07100081901e641032910944095240020903054021508010286280820041140c110609010352410b00a0044610741800399440a0305405640120b103407044110001071074641c143c01700348645000410031110010b6480c0c65290401c1c0d0203800000014890403000600c00b00700740a0006008411b900d07416455240c1160100d0340303140d181d00d00c540c960500c82c0003070f80c0500800581e4030541c0c1080d0244001e03d091000903006d030f4412191070303012510690300c0308030b40d108190409a2081e84018002c404d181000b0042d04c200c250000224100b181050b64101112000180d0034041c0e40f00385c502283c400c0c0380340110b509089854 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 860502904 1250 860501654 860501701
    0x1b050a0c140a0f0605070503040e090c03100203070c0807110424080c10030c05040e07050a09090506010c0605090c030109050c0922110103020c030c062d151206040b 72
    0x2e5500380241200d41d80c2c61811507440d400c2041c0c0e030705028941241076005d258401022a2144004c0040c074080109141c0b81036003040782950150707080b11070701e070040380420381d03003000003a03e41e06900f40000c403508002c003070440c059240d0002181140e40004c003a2107180f1140009003100c10741c1c1032414a481a00c00001c3e043d090068031021a05c0c2d80402c040389820050401015181c0703401e201c100d80941c00300c0b000380a04a50040d401d180461018060341c2c0205005000141183c03000076203401c6900c02c40c0d0003400141d46a9040880e207440d150040e2201409003904e9004032001c000b5590303070074070948131014800ca0190050086000c100142244000c01c070381001c0580b82d5500950064809684029562008054212610b8400124000e0080c081c060f403180c0b00014060641c8000041d4180c801c0704030045903429001c5035004440c00d0b44d0b0303c4c1c00c00b0221240300c8000c544680941030660700e9090001c0c010b001d04004107000b6520700001070300c3c00d40c3c8503445a800d01090403070039004800c080c0c0c9207 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 860504154 1250 860502904 860502919
    0x60801050301110d090c0e0103080a140a0f0f020f030409090c150f030e0703080a120e011802040207060209040203010308030406060602060f062e02010605030c0f0a05011b050a0c14 79
    0x5584041d0042c49158010040544ea131540304041004040d01d51b8060b090f5010b015505603100d103070410309540300f1250131001c0b400d0410540180d407081c03400c40b1800041030b0344c0d204146007283c10645445040b40604419400303040f03150494101c04002400051a00c1e96002c0790b000704034102000c902445070018204000c0e00044d0f06e04903a002007403851481e5851400040d10150010014217040312a08000c246040004d201d0044580c80b070b10101005d410310381e00b04414201e25840394226100c00300030404103034840d6016170140c50140d016041981c06040e01600d444500000642242d0007600200c503110b1012040c4418010035110301e00250503240000e040b20300345000318400e144002010b040c8101910f00441c0d4107c03202c07038079403e1900e08a5002800c0c0b03a42052020b8040c046d01c1c00340398000e01ca4000b080c0d0721840c3c001d2510182050240c00865142e051400440310502c0d1141c2c84c1301c0b40c003030450590f4005a01003001d213420724010b0700c0505003d4207000400f503440c0901c440c810f104409 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 860505404 1250 860504154 860504171
    0x90e07030804210209010b030a0c080f01050d06060806070f170402061e0d0516020f0c210a050703080703080109020702150c0f03130f060513120204061e060801050301 73
    0x81108941c00d94240209482c1040e002000c90b1200c0211908005d400460400001a1008024010310701804030200284402d5402841c02c0302c2260040702c041c8141221480100010309211110351300311400b172036021070015210b28556103421420b81c0c00000061007c061807070802c0d030118240340c1c0c920501c00200b0260601d0340018149000f0031130080080005015044100c074041400c950f001815001c0c203100c0c41c5810070f0f00410052400e02c119000d4010321200260394080070400094851004141c400c01240c0c0208842c8007506280e1040601d20491402101241d010400f01c00118400c079895a500c46807440c004101401c181d0040800314018030520700181d0707802d40c0503086552070701c80d5a0b0b16140b500d000c807072a0441c030b80b55411030340c00005068400d60294000074003d40e085100c442c12425a01c0b8001c440a2044118006050108045c18070880b82095610004980024004100151034070380002440d00500103552480307200030410418190003003006801450214001c100100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 860506654 1250 860505404 860505413
    0x93415051801030e10360609030e030a0f030e04090f260c03070506010b07080a0f090b0c030a0e1e0103090c09020705342c10090e0703 59
    0x1503640c4240003070111240c0204143d11951141080703c041c030048804076910000d600d001411014214050003201c000c001919200703803007240d114a082c52140b81c1c407151980c2c80c1c131001803414110840c1000842801c04105a40030050600341d14013030540490f801c401407401802203244001460301960800c189500480c0700c1191400e0000c2c0c011503c6e1500384800c4021814035100149890b026000104070401640400400b502c03090f40703d0b0701221481d98070340350707010014003a80a0050a1a030100860405c4d184600f0368850031a8450514050298031440724201c0364101c0c034540b00041d400880e481d010307540c0c4200c54200a000a035441038a40060500010040701c0d8002014141902c580902c81007200c1256100c006004c802c0b0115180c0d40310746025600ea490314034410351500c1c00300c205459011010301c031001c640c0b03071700c0c3d44e441c00301741e16000c8070b042c86030b003407043e229610022042c0c0807011400304200540b160300100c400001b030b681444c80010880300c88241107074050340291014400203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 860507904 1250 860506654 860506657
    0x65912032509030c061d210105010e04080910090923060f090a20040e01080706180608060d0203010c03061a310b12010527010501050309341505 63
    0x2034800340b03410300d80903440c0c1c4030714030700c412481850503080f0219401e202115891081250005100c7d18000d00850f42c2e00c0320244c80400c0140c6024000000401806142d46441503504800340c1d420301b007440c4015591002101250280e09585144526040c6401044140200c006910502c201d072610200c280410105c0d4a04d4401090306044a03511503c20103040164241440d002c000521856a5592103c85030704d40c0700d00c01c2c0301e10b448510881402240742401143c259002031141541e81d900c6529000048804841c09450140c000b040e9107084800350318203004a800c002142d4a001c05d5162400c600a1020f415000026082035000d01038505060034100326000342000c002c600303c1200c14203d00422807000c056004082c0300c40001101060030340c0c40404141200d400300c82050a00115510301c00c882484500c0400c0140c9001005101541c0a880615000003203007040fa001c040d040100c0f012603c813180d24803501c141c404980761008901c0e1440e144080c00900c405102000140680a8841d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 860509154 1250 860507904 860507909
    0x30b010e0f0723130e0109141006020a3c0c050105090102191e060606031107110915031605090606040509070c0807065912032509030c 59
    0x191100246040e604e02940300148094502d1035542c030400d5942d00303071290041c041103c02c0c4008655a100041d01d1040b42e0f41400d04031003080c0c0140c100d006082d40c94400c480c900984400c410a0303858028050594418010b08150782c4012007031803000f007181800b09810344c166000904024081141320400c0e41e004c40d10350038480082d035401110703402c0b518040001100045095a02c5203803502d80100340300e00c90b00207404031009a1000c0000c0c0501e20004940c0d07105080d4003a00e488101e2400c035081d42010b0740240d6120b40b844142032a1003400d040001d00700007802c021105110984d2170288050300c2d0070b000d1240c12400480e4414606440c01d00803580340c020050945042c000110041c2003409403000072a0703000d86e48100c0c100306130440180083d1070aa403005000768840100350384106c20400306842c0300c20025104480c1c68085012406a01e010151919002640d00480705e281104005400245000b00034051040c0e000d245c0d141000240302d14440250410070111071001c0000c10b202030070110a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 860510404 1250 860509154 860509217
    0x60a0902090310050709140906010f0503070c020301020c070303030f02031323010c090e0906090c0411120a0c260a0203060d0c0b0901020d020c09010902090a030b010e0f07 75
    0xc0740c942800000342040601c1d11062105800c040801030150780c01602041a610400914400c0012803418006840303c210340c4103020274540c0c42c0064000380aa0040e590108191400070703105c04003039000c2800d82c0c00c015400c10444d030140f40140304042e010702a07100e484403503410443c1545404031410340c1e180c10105015104600703101001c840c560320410250041b003041c40081c4081443c4000003020030b10540304080328801c500c070205802660110b1094014138211004220301e0b050481008000c0c00076920b41c0c0c82d004001c1100310891010400c10320712030030b0101400600d500750404090701d2000550f505102d42e01c0340c3c840c40c01d41908030603034042d00003441000058490b607030000071450801c113a41c400742c4011021500040d44004400080800344030aa0135250440f01101d010307651005070a101c42e0b0320002da04014040302d0310b41d130f018110328000103212004955507a143d80d01d03800c100380c000200001c0703060100005240e9000005822003d94030740380a15807088850850071214003607203c034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 860511654 1250 860510404 860510407
    0xc1e071409060d0210090b040f18180b0c0403170c01060605070b010b032e031b1a070c17010e1e060406320f0603060402031009051006090b010e0603060a0902 69
    0x2400b80320311341b48000341c0032946495a8070f43c1c17983d100484070034803803040c1220501c0400e42107024801d94003513803901e51903240c2612016001661600c0700c2103002011201000341c20310001000c40c4d480121700d0400c4d004081c0f8142d0320305a00050354256901c82d003100007408000c00207000040c0f0281200ca0466025546a03030b1651288240a070f2048401c4060411600c0c0d131803c91071003000700380507940c112441401010003040e1145030010f080d040d0ba104004580e04803100c80150581544005c1686074414a180040d031522494410101c10305915100056956401c01d05001c41040060700f10149078108402c441039001140306688a81c01000204000c1d00d540b43c0c50b15292469080030b00b03107540c182e001104001c041940502f1034900700c4510742c86484943c0030440c203003000f04200e4000d0383c0160103082c3d817003400302052000d0041c40302d04580a201c0e89241c158081100d00c50310004e0520300f4808100d007240740e00014100901c12040512030101041401490780c0d038820600102d46410f400503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 860512904 1250 860511654 860511679
    0xf0b1209070906060e030c040501080c010c05102a0503010b030112030e101d0d0b270105070c05010e010606051c0b0d0c0806010e0702030702060c1e071409060d02 71
    0x3505216640e84900c0c0d41900702140403500b90740042c50720040d043c050341140c03060ba40044c10007058440078896a1025082241307081110752165990403000ba01650440c2c01c0c00402001203001c441025110000920100b0981d050785400418010700c2c0c4801450124215414072000c100c1e10312041c4244885842000c0210040500032051103046910003061101c0761100d81002804068a114100c0c44081c0d40d455a500d03903240c9503000105442d00988001c03c55a10321403640322030f0003c1002c18200c44613030301a00480a030309004040c840c1d589691001c940c130303020b41352403825074010280c22444c0380d040501c144810703a801001ea4040030040c83c0345c003014071109206500101455060075820410013884442805080d1a42000b154610421548581c0e6030f00c2d410707a40b103001a0b4402c00107070002c118104c09071412901415406515005592138001e118580d107401c9004411001d00940007180d04100343c034202d0480c2c6501c40c03404d9441e429245890301c0000c09110380b282001707208440e1070b0490b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 860514154 1250 860512904 860512921
    0x9080309011b020f0405150f22020901050f190311070f1209090e0705012a020d08090d1109070309030210091a0c0d06050607020609090a110d150f0b12 66
    0x900d84d880740280c0104010b06115610080c10154420003d004a800b000200c005040180074960816560351114103959144107000b00a980500308060400006102001002140e0300080c20490800c2003040122444160050142e82c3c8003102950040414000500441c2d1200a00c400041d0b2220280254100c060000c1c0e542c084c85410000c0868039118403101d441c2000900d440076140700340c94185005809001c400c05800124800d0042c190400c107000006080c80050005828818001c03982441c0c07118001c5042c10740ea000b000d17a28081030894140660900881c06504200c942c5803d1000c4800c40e14080e5990440001c1d04c40e109a803109181e0600039407000190142039105407190032814100320300c01c41904603030540308020340f81100020700c0b40752000444400c3e941c083c0c401410070341c6210410200150080003800751540314120001c0c1e03202d082004042c0c100d00e1071030002d1401502c03241c02c501e02015030401c080600b41a20240038440030801601e409140d1900402082e0383d44000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 860515404 1250 860514154 860514169
    0x6040e19060b0d2c061005090403091401020312070c03030f0e1e07090516020d0e13090302011401060903110406080a1e0213050703181e030309020a0e060109080309011b02 75
    0x401c100143c024041c2144840e03000c00c81d903000b014001d8952000981f50003c00885050645004010030b02e170341030800403401100390070484d0000c140162401c2c50030445142019000458588002a804244007400c01d50144034618820303034002c0041003490600c22520fa03035001000f0000705a44c501d0000e20008079010040100a04a451014003c600748510007400b610038800641002d4051210314a80480c8614560030318134000403d810303a003d0084001034000d0031707e40780950855494038001076600548407040741c000e00e969076a940c80103103103052840509088880c00c3c0e1242d07080501c10002c00900085200e484c40c1c00c41d41d04202444460108403c20b0400f40000b50000c000d10781d14404860307190300c03052161905860600501074403203000c0c0700d9494500d20061000d08800c4804d00c45100d042141004540b01c0d080000b244800c80d000034038222242e900c90f01c1200b80c41c0c400c01c041c0d0759001101c08002c120305d80046080441f42d0001030041080702c1c554840c01d81c0c06d503100e0015962040c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 860516654 1250 860515404 860515451
    0xe150c030d02030708090610051c12050904060e2e03060c031b020a03021e1204120302280209041707031e02030f1b030906040e19060b0d 60
    0x202280d99074103a0040c1c44010350411149030012880ca00c0010342c9000011621601c40e8019840d0011304604200402072290704220b000090007680b40d200d480081c03194208150380d152580c5400361207026034402c21061700c1c1150060182c0404503414414102d42c500c002d40c0130414400402c0d40409a010600b22107d50503620203852581801c5a008681d42c060340b0550310607803220071382ca00c03032900d0003c1669510381e100c40c01001a80305058500302c80401136244685589403070184e4000c40c84c0141c1c400b40382e030001d400400045020005c1d0b40708058041000490701442a094124100702c2c1517442e0442c0c000480c8040d0184030900006410080e690b00103042684004102589420007410000d10481c850004400b0306240300f00303900300c454000010350318200e030003801c2585044124001c03041c00014250b0428850700c814440c1000a03514000980003400c2e41c643c6810b5a0701d401c0c401e0f569180011640d1040f201c1c0f83c0502802800300b04012650060000400404d40442c1c5d0b0515a0340c4d1100710 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 860517904 1250 860516654 860516677
    0x100e090403090302010318150c030605190801060608060a180f140a05060f0625050703050604050c0105071a270a02031002130e090a080409061809030e15 67
    0x2104120415402400440030340303000380c0c0e04015032411800105440464028050050700d01d040c602c600584d41d0303030850913284010b8500403840c3c0f41d58002085006090108004104006200134050108240301303240c018801d5140c604114104100814060040da008200318805400074032003c3c643d9a40148801d045909400c01c9010b41002d50070750255005e50b0325007a030b541010007094541c507110021598a060041c056854140b0101e001c11035105120118a88031004000403008104148201c400450041000d000b292416280003402e000d404a81d40381407010a1000b04085140c2032040602c582002180d200240c07140c280745050510b091020082405802d000140c4014003c40c0440340340e4400e50440d0408000c4294040c240e004009a180345000074040801c00402c03004601d50b0042d48200c152840b09580c2e4941c41220740c0960085010b0948602040003692071860503c0740741111398800f004800040e03a40100b8003400d000321580700300c0c40a0742342d510008e03a1100f16400d039a1309 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 860519154 1250 860517904 860517919
    0x314070e010809011103150f310b040e0c010f080f04080a050d1e0b01170604050601110a03020601050108061207060e0a05060d0f060518160509060a0905032109100e 72
    0x814080c00000300e220310007030040741071180c0c01405041034403003078100e61030045410001d4100441527040141d40030400b040c9107611001000c0309512a4071648071201121405020031090020001d80b0718400b8410800c104079021003084501c0c4612005140c00c642d11400f2960b071407130848002c03a401d001e1401d019032854076020f0790115400d10804036180d0004010406d00202c81d90b0401981e91584110321480a03000741d40000e0a2440c00d5070020f0350152050610a0380c0e1494403200710b14250200c042200580d100d900140000d40e004403540d53f00003001c890161412006002142d140c0401c1d1183c02c003845015112030145a0b02c000c09034016120250050343c03a4100d4a40c41000b8003a103d0108422a21304440442c8501b0090000d806c403040300c039071703461064440c01600e11600119080ca002004014401c8201c0750b034504005140c00c4000c5d42c2c03140a140c0c201420542418802050ba210280955050f14802107090b0b0546240031812500501d164400c08000e4070b46c40791041229500444 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 860520404 1250 860519154 860519161
    0xa0204050c071a0603010c0e210304030c120506060d0f0f03020c150d06090501080307030c060b090f16030507022505031c0e0a050105070609020a05030f010204060314070e010809011103 81
    0x41e80080541314800031070080c0100403d161050341c0c0002d612211581120100d03501c40c3d940c14200180d040a5110103085900d49650b0b03484080d040c101075000610100c24107a5001c3c24002c1c104074541c0c000508950342c5108520640d1015103800042500070b159192081507901818003d000040c01c0342405070215018450003031010000f40d22907608051140e2074080b02141003501ca02c1420f069401c141c00031480d00485840a9507652400b00c2c0071204507803104044080c0761254081e0b035000d140041d10440d050308229202e180380c2040d14100314105403400c002c021104e6030000c0c114208190b4108075002d0800030403101810168180c211a825100700b208103030403800b14108626070421389954044500400c0f02c104012180a0320a150004400b07220140100705a039010341c072814401040044003c1c0e0b6000800d04102000f0080d0070681d502240c1001080d405001d180d0510386a140b80310000c1c580303900003801202110100da4100424200010140002580725144524166014030b4aa15 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 860521654 1250 860520404 860520443
    0x509010909021311030f091015030302010506010c20040f0908070318030209071103090a0e24060d0b0d1506151d120a02040e1b0a03050a0204050c07 65
    0x4400341e0202d004600c0041070403a0f0008600c50030405004259819166480d40342d903c80a044000d0100a01402000d4000700c010049100f140000c9211448841c0003510f075090190859500030300340c038180500a0801e03000580040c84c0c4180201c0000c0c41c500c5448401c0d00400c0c0144100c0341c403098042d10b00f1aa00042c4901703000503212292107982c4078000654074040f40c0800d441075200094001043d140403d80c214001d030400420304402c10b0403282800e00a10005030400542d910446076590b001c01800580108070074900d002c51700380182c081ca4000e0102c04149641700b000303054001d256540030140403d9480705400348030700d034200b03094240c01070603440030b400100602d1140341000310540382c0a1a0721401040d4825424000b14030032403840064005000459102d40418200782c01220510b00041e921440b8000d003070002c006c0204174000c0c05030b0400309404c034079410789445010100800c00000b400040e90460710f690503180441c1e281c850911811441c02403400080ca0260300d1303002c21501c40b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 860522904 1250 860521654 860521661
    0x51905040f0b041d0d1b121110021c0c03020708040306020910110a03110319030f050711031e280215010807290406020703031706010804110a05090109 66
    0x2c1803ca43c20428003200c000c1540700c1c0380308200310a2040d0000c1041c0c40140303000703100c8042000444a8000801885039652010310000c83c0c9085012401e82005030005002c10000000c030f0322000c003021403406002d04c00355242c0200051b440341055480d9000c0100e070303e10035016941d901d0350240001e61240c1c0c40345080d0001c3c2d002b5042050264000070851082203100324208011824081c001d84144812901c0032101442c403413050150910007005140856408101e0342d03188074a0b0b5580c0000c582c0c0b00e02400c0b606440012703203100100401ea50450385980f0010040312140c0000c0100c0424080c4008510140303030080b0304040d07024600c88000d1150134903492941818104d019801e654217a0710700095900c10440c05e0185040310340c0143c5c010f0112811501201c114000b1510b41400e451102903e1900c070780c0d1044e003005d001a0011201002010f40014183c6501040b00281003130b50701c0d00070002031400900a0019000d06030850302000c42d41c54901c8200c001d08405040a14a036841e013803000c0c040c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 860524154 1250 860522904 860522921
    0x14030d0623090411040203060a030b09030c12040e070f03060b16050c090c0405010e03030708030a091e051c12051f08060103080403021210050f061201020c07051905040f 74
    0x442148604079040341c030706080010720455208816908031403d0b007041c040203400040000382c202110f40b0002c000b05251082c0c05100d014080e00035035aa0621150b01c50408803075800820041030148000d0100301c840c2484180d0184503480c050010550001046002d40859413252036081c50004140074800c6060b2112003510b80100100c9129642c060140b005d107690031100502180c00c184002e01480d032148840010401005084a081013a10340309c00c4201e40c02540c588a00984d02c207050340411030381c403d04001c5021503900d207000c0f0f8541d44d22500d407105a03c450300700031418030301088007146010b26480c18908142240801940c5881c0110064261800300308441019440c0d030700041600000030040d060320351040c8000c5c00d241c0345030300b40b014107814000411540e01400d41c0380d4071014410300c5028429400480c04101ca03040a8081c808000d0003000c83d0000c90340100b010944e44980082e04c0e1044400a070752010800788400c0d4800100c9000c0d81249a010342002d801510600c5103030081100c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 860525404 1250 860524154 860524199
    0x130c0f030b0105030d0915091d0a050702062221081504090f0f1716030818060601080712060602160503011407050d060b040312031409070314030d06 65
    0x803039980310400c1654a440031400c110000300340c00010f02c00c4042c160b101c424498028281500400d0f01c0b030304200450843c1270f2019001c111208104a50b0075000e006d16a000120750001c7d29050404516030f0b078090765801c0b003088400e00342c40c03141000c000401300419820341084c60b403810f5602c1e10b040003e10300301d410703100a08141c562000c01d5005281c144a140321443d4400b41743c950301c01c00380da01c100510f5005802a43c4102603400a5580c1c40980002001c91100c031541d800f030038001624001d8418a4060800300000e0100c141c0c140101800003581c1d41c07c14800d0800b40c580351b0310301c00119160040f1909500390b85091000014100b90001006940349001540060302c4585030000d042c02c82740141c00315200c0c001058007084031207000d0801088002c194980100d801c584610b10364074650301990048503240e03642d07038240d070049038075100f08a100000b10581c141c5509280d2005d981d1109140406071000500d00500131901008008a500e0311107601014060196902040001070564a21a40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 860526654 1250 860525404 860525423
    0x51e10031e020114030106171302030703140d0914041805010c0e0307050d12050708040b0f03010512060c04090f0f060b030702060f070516031b0b1803091305130c0f03 73
    0x6085130b01e2800303580c1030352402d50303400740d550003500142643d6160180071001c12200741c0803850050b03141845664051800384a40d5010180034003911480c00610040f41801c0226090b4207114084107048194101682200c0200c0c0154550742c030f01d6071030302c031050005080c0e45c80d200385800c04641000ba40c144040d170450945140c10740d0b94007070200484032410024950282d20024151160241c070140160700c3c019206681400d869504100103070303010791001e00e2600c0005c0010010345c60903040c0404c0c1581c09802404590400100702411402607001e1780c01900d0700c07040e103032095001e10391054401202020f001c1c442c00d56907800140b003030343c0107842c400010300070040087c0d201c0c07115040c0d44c2c0c05283c040d40ea5038078162250400e51240300030210f00700c0070018403241c1803961a00c2c0801c2c140c4038900485500c1c0c240d08020416040d15441d030b080e040310f41d400c24040700956a40301c1100d00b0040c0308218000c00d441d55104005180000e410000801214020360041610010031360781005803445900c145 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 860527904 1250 860526654 860526677
    0x309081b061803120609040510090501050f0703021c050a240e2208090109170d1806080a02090406170c1017061201110a03020c0709051e10031e0201 65
    0x1c3d20303031150038030b582c0c8541c502e01d012403aa4109110b815900500800c2542c41400d55280c90b0f81c19600e5002c01681e16039155400c0c41241e2440c035407075581140c25420704501c3c00b1000c9101d8001420f40290350740c00166204001140500d15420a45840c0420061902c0e0504074404261521605001e0000766850f0b003000503030b0303925101d003000034407003803264502038505000e03070b00c214040e031150300350720b0401000800014410105103c180d840755442d4003e803820201c801c4c8010805d2400000c0b01c8003000d800c4208011064210700b0f010b4214403e818050396560803440400c0103040c0a07030001d0030015605800900c040f50204241c0d1446030200c44051030710f000a2011100c0000040d411070303103d2030510103d1118034041d45900442c0c0c40d184004030300c0d4001390b03504002d81e03004220450013180c2c00044c10f024000342886464041c00155104200e01d040508401d1000c012400094900b2a441000b2407101c0c0c00f002091b0001359030140102c0c508030141001e44d0020000030804902040c54450381c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 860529154 1250 860527904 860527951
    0x3020115140603040f110d1a0601020303012d050303071a09011406040c020a06051509010b04061e020102130909050c030715050a031103270c0f010309081b06 69
    0x101e68500007802c00e41580c40310344500241035803010007100c1d00a59500030b00300320780390316007940038050080003045140384048042e01d101940050110b41107400400050043c031009181c00c000301c01105a456041c0c0440e15000c0d1144441390b000942c0c1844086614401c10801046010000e0700f9036451101c981c803a05006400c1c1e8404180d60701380040810002010790526921441800c052841103640c00c0d038080c2c454200b21030b001c0d1030290f004a074400d050324403410324207011401010700441040c5070500e810750090041140140c00e0a981c80d407040c151039014402d4059840b07001941c2288108142c2c0c1d402560000c04a48201b1602d50140300c41c60036103490086000400c840d11014a440a48155002103c243e4840e590060505035a141040c4122200c0d0f401340d031180d800c46030000f0324840040f24440e803c0d03c17180e0409909034400c103070110b40c0da1200c8550800503a020b09000c03d008400f80b600c001e16000e00034004c0c4e500d409046081410000000d000c03400303080ca800b24040d04031802c401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 860530404 1250 860529154 860529179
    0x3250c090e0709200a0e1807030e1612020d0501020a180504021c23040b040201110a050c010f03181101030501060c1707060608060c0301030308070e03060a151203020115 74
    0x59079040001c40c0e1260004e03090000b0505100545420031454010000150141045445c1914000004400c12110300d4252103215407403540c000040488130900009442c2c014154090325034284d178006052800c5450300d01e620040190701000070b640302d006081000306061b0300030060400001c501070303001a06041034821070b00200d6110f03102802c040e4403140c29101a0500703811408510301882c8022400600b030642180c01a0f200d2585000107060900004008000c0910340340c0203a04010031210008100041201da460b078203081000c0c45600c1194144d0040140c4051502510388068440082054040c60104040001d80b801c22450340c80d580c0c1142c90311885140100700b0743ca425500041d1313403080c001504030f84d03100d1500414507035115627100c0d0903c1c6007030340c60215092012005000301504019103aa11214902d4080b030800034690000303554090242052200c6640d0348002d01000812103020400344c40c0110016071446490300d0028002c200038092119940c039181404202d05c0d201745c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 860531654 1250 860530404 860530421
    0xd03090b0f0c09010305090c0d0609021f09060e0a0e07020a06051f06050f1909240509010f140c030406090e1006080a060e0408030609060f0303250c090e0709 69
    0x4401d03041030028001175008280280214059114409503541c042c0c4d034030f42502c2440c520400001c503480c40d81e8414440e00b80c203a2109a001035018180180c0040d84c08002c82c42120524a000410954840041241d07440d143d0000c82480c01d1650800404a80000340d0340c0c0c20600c18039040001d41e45941d07410841c9803a0f0440f2075126003010074104905031045c00a028807a0768070540600d800c0c81c1c6001001c1140c0b2540c049800301700002c0d8100441082404003030840d40c00081e00c0401d5401c0300400070b004d842100c69260522101c041900032003403090440c143c246c152443c120303a98201080e52030b43c1d20340191081100244003840085002d07002d03400c4140c00380c14001b240558150600300c0c152500c3c0f1005001140031a43c070440010700700c400b00d00b098043c1d030151018540e00d0030000c0600440400050560f40143c0c0c002010040ba9100082101c0c3d070341d8211042c074600b070308110f135101c0c21448400c040984580805c9001003102d550f00c0e2700c1000e01c00342c00300c121403100c0d41e500281c2e021b880c0b003071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 860532904 1250 860531654 860531671
    0xb0301060e010c0221030d020c07030203070801060e06010804080c01092411040603110f030717131505090307080d0203100f15030203070e041e0b060705060c090f030d03090b0f 77
    0x4030070b81a0a440483e24045e001d0009070203a0b824641c0050140c422030f00490500c081c954840c0d0010429410240315078006044a07030002c0c0010750074030391040403255000d0300c0c0d6070402107044002000d001811040d00c001d030503494001d200e60041400c0c08006605454445000d0007640c0c0a010f1744c50840d4411075121245030030940e410145840341c203070024a003e40046102c09010044100d50401d80c400951040c020b90300c406038100d000d220700b941107640050400c400b03190404000404600703a107039540c051a42d04d0340082520342d1760010180c154020500018404003010407610800d01494001c2c1d80308000c0c05008043d840d0ba54134003ca00401c00c0c2c82221050021404480c030326500c2500110b52164445c203015038080c00000200d81114017102401e021018000e42c00010aa214040da4000040c00c941d8541411403036141c1c0c0e522044050408854464001840c80168072100a11505100000c05980e0340a18030000030380688804903049030444080c0000501d4010000d15460044448 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 860534154 1250 860532904 860532919
    0x204060518220b1b0405030604082101120f0c0810090b0702031c05061804030807020f0d0e0126011d060402070b0f06030a0c290f0a0c03090e010b0301060e010c02 71
    0x402c02c10313541d4402c000001a40354181000045804c0d00c1c20051140032360321400440b580c542040300134003044401c121685011012082c0108422121034140b4284213030002c2e42042c0360380c1d80c0c0ca808008501141d01c940460b0254425040c150138290340001e480601032007040145944541d0200e84a200340440c8909030001c80b8208111f45a863380f0079035220301d001d80071001070b04045448640c0e109040354224000b801c032070100010b07960f040c441240444004030003040310301d00054000d8a501c0302c25110b181040100c82a45c510149a400c24124503a8031400d0003d441d61503400215012184004149800d0700d00b5001c1490342c2010300c211007480d90800c03c500c5c82c540304d9000020440201424265151040c07000d06008101414a454000d04410800110380d031855880c681007200d0b800c003140d010140034090780350b0115000040301c0340746202d4600310011510318501503071612102e4100412048410b00003091650050b0001c6040e261940c580b850103078264001180c4800b030040c00250401e20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 860535404 1250 860534154 860534161
    0x90e0a1e0b0c07050a0203070905090f1209060a050405060f042409030209060d170307031116170d0c0807030b0f0a030b070c0f061b1d0d0204060518220b 67
    0x501c0b80190640501c120306a07000016580c000071728000031900150040c958ac0c0042c07094a0070200000c1010b04800c4024060b550b00b140388281e0140a09001d190090318006510039003284110f088401400c8000c2605458800c801600500354000d40211001e10501c1340c0f15040d11541803168031591341c0143d840305040d5003076909110521034040c00194110989112040c0040c040d800d00180e1003001c00c044e59101d150103500101a03c0041801100c0c600b03040082044951451b080344803d2500030346a95401d241180804560388952009400b61614080b141d80f9820340c403810650041501da80c061104d0b8401c40c08002c081c803101d0a8983d80202480010000070340e0380000258088804e0501d039407040165290410850006501242d40b01c0e500c669864070000494580b84503240d1525040c86a800f00203420415509401200384c80743c60300040410441d65550801000b400c03028240b94542450342c5101d1060704020307035415400f8881c10480441400136100c1da01161600641c0940d2180c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 860536654 1250 860535404 860535421
    0x90307150f02060f06040c030b0301050f0406060b0f0d0e120c03040e06010e062217030403020a060224040f0c06020c090702010e12031009092603100510020106090e0a1e0b 75
    0x5e07c81c8013010038152034145c5004659800c2c0702c2e041c0300381400030300c02c100d51401d4503050b01150011b070000a0030520501804101085110a54601502003440064504041540a0b00d805a80c41c40d00320040e038000342007028103402001400440d44007907000311854958000549002c00004a07207508040d0500080d0850100104140c081c801171060b1411050b468a02100e40c0540a0110003d0f030380c0700050070011807e08034000c10091003a44050181c40300320121007543c90302e01c5c6c1c80070341c100340c29800410103001d9590140c1903c19070010840f070724681d4820f0301139140d020041c019413069042c00c2c009425580103000d01e101c0400120050702402e808440070701003e0308098440c02149c240c01e0000b240b940080d1041200c601d00604500901c00c00a088030120380151221140b10740c5014800c0c000d240900064080544100700c0c0c00000c0454810412801002654007400001c0d0420900e2402040046184840b00d8001c0e20503544030044c641002d00d0080c10000b001382001e80c21000104120b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 860537904 1250 860536654 860536661
    0x312090d050a180b180901090207030507230a060e06151513050d050102090319080d0504060b1e0a08030f090607030c050102070302070f0801090b0402040b0402090307150f02060f0604 80
    0x90080b0340700340085501c0e04d1103c08950489202800028500d03020843d00c1d207000303c2940d005002420b02540b402e40c00f55801083ea02030603400601c0004881c4081c81c900000c0e44509400041000495165841d1800c0042c060455544000040e001e2040031805079100d40351100d480c211302800782800082c141d44902c01c00e620440420800c001d0a50003c940c5540700c080220030a4080e50001d601ea9400f48101410030345110208901d05180c07101000008850070103072040041c0d50600052a9910790070004040c0c00e6861002e80e016440300c03506442c030030368110010300c1c445040d60596100c545582042d5039078411200f0f87c50200109002d07005007868400020510103109290206585403141d81d01807c1e03820881c0c045003da0006802408112045090305000340385190080c0a20105500c0f10559403034003500180c09542c0b10b09107280b0540790740e0100c400580c406801c440a6541d101c4188241002c003085000005456440003c4400d10020340d1741d002e00880c03c08548243c81e580e0822004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 860539154 1250 860537904 860537927
    0x90c110c0907020f12040305070503160308030712230c0a1205040302030f04060f12090809041d100e100212150411031603061509030803061807020312090d050a 70
    0x1c500c51300780c3c0480c45900c1488069010b5010704880c80d00c03603003185400303410106507800035802640000c076103984408004074080b04907038010481d15907907241d008048844010141041280b20700308107e60180e1a60076029203d9a10040c1210141d03482d00300750040f4600c102a50303440001c0081016048101403584a660054070138011030340340119801104403250400e9010030041551080c1c0c50941c25006503d944100001d60801c010b19002c1e41d4411815014200d0801c3c050359440d81c5c4a07001004181c00c040f00d0210710000c55078040c41c200c00b404054211158044c4060281c60244907a0301d05a0003551001c51000c2442d00e00e507a1140d1040095400001c003a9500503240d002e0b80d13098400e007100650003591518142c0d0000e08001c01d001c0c0035a59a03600c4594840030b0a035045c03030141d500540810a4a9200901591725110f560010319002094504802c484c1580c505115000e43c000005000240040000280e956207501c1c105882d008124078000c0414000c11080035864441c001e001503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 860540404 1250 860539154 860539157
    0x708071205161b170a1208040206191404080127050a020d0f120905012303160203040314030912010b0a0b0f07050a1118150103020702030a0602030c04090c110c0907 72
    0x2142982c42e04841400024036018492503044004140c050004100086c84500c07450300b07180c0301c1400d09030f0204078244195080c4100c1000083c0e01c0c0740c01d0521545c071818100c482400d880d9211519004014020901200b4003043d401c0c2c03030604121000d14003000d40354600d8002c000790070244405e80130722100641e0f50740101c5101c1121420100041e00c01c900040d43d240f09070b40c80d2180b160400d80054202c02c154480e40e0000e03074480e910701c0440448031017100d500021091003031269403808001a80346010355040200000e000d444d00000102001020b0031a24604a40c494008140c41046e982210706807031146800040580040c005490341c14000c0c00380030b9011070f0952601440d03807551030401003184011500f120820f1051045464105002007061502d01c180c00701c1070600040810540f2240d00006041c15004a070081c2036690511030300b000644c01404c00d5580346410704c800c01c07140c1c1c440d000b103a80b020314203950190070703501c03c4922100b0009418010019007a1034820800d170f4180082c070800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 860541654 1250 860540404 860540453
    0x705090c0706022109010504021e0f090c12060d15090c0909050609010e5812060506031f09020f0d0f15090c14070807120516 55
    0x500080b02803000700000c10f90030361030008804805041c00d4034054080e01013101a81898140000350f0740d80074918030f900820f0005981425298004660245880c0086981c80402c8004000480342484010716540b022000c40c10b103943d441300200f1101308900200a02111010707081c118481020fa48041001ea0280d00501101547d03685c006003034950101c41104c1c0d5420030710502c1000d51302406120a9044550064000c820040c1500c225141c200441c0501c145402240000018181c010541442a0140030707140f400225214450110120000040c005021682c0402040109109140940d40028211440c64032214100c0b2180e482c052001003411164220000d0b607807003584024603401044070195900c0300d061160724011559072060b40c60300907042c100072102c0a42008441c03420b5400c00343c0c00044c034200e4120b0468400c10300880b251200c450000f549020b010789800034240051240fa0424800840c0700400c0303a050181382100d024a80740b0006101c0000c4403580e100d03c42c481c1101300d00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 860542904 1250 860541654 860541667
    0x105130b0a0c0f03030c0206010902160201140f07050d1103070b16030b060a0e0406080601030b01120804050d0b0604151a09010e0301140613050702030304021201140705040f080f0705090c 82
    0x1070700c0f62010240100d001c650f8a0080c0300640b901401102d0041c840c0c0a000c42c2004841c0c1143d5204040b54a402410407a00c01e00d50490800b4140903201158026102e140e220f6410385089503580e140302c08490040382400c2000e1141941c00821190a50f07072000d42c82443d9218004a01001d0b10f002414009060719003000c3c1211f80c64820240807181215901c90a080342d803042400210381007a00220807641100e001400403850010078141180c60b4001c0c026000303c01420300241c10300881d00702036837220442e16541e00f031101c4103107880d005a030102d03010080303821150005510f911340c0703128240300785042d04e843c841c0c4050324101801034010306043c03481408160000280c01c4454400c038440500080400340700311070401c000c1e107044d01e100d03190007000503080030900a903890200400c001c1c800c04001c01109860002904000c0030075a1160015581d410601c402903c1a001402003a41402d54410009419000000c003040b03440d442c0e0018101e507030704142c180140b10b20f0003003030b00008080c01c0118 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 860544154 1250 860542904 860542913
    0x20f04170f0607090609080109020603040803310212010c020a02010f14030108071401050f090f040207080a020c040f0603110d1a180705060a0503163b0105130b0a0c 72
    0x400c3d2041d100366a4545089081c604090110f54550300b04021681c5002c80301d82c0181c46900c00c40f034005d07403c0f0039407544a649000c0a00c0ba50204c4a00080d01c0503012070813802031404101c03202401d14030849840c4030000040c66103a003203440296554005134400e503da4005540a4400180c800c40c252504003061548030004140e02d034000e901420440d48184010010101c00f0524155448400d192140c81d0044203507804405008160a040c4229403000da5000701d583c940c0d04031030340c1941c805481c1d40c9441e928800030b9107825250b1282030041c0e003001400d0003000000d110703003020b0342c1d0310900c0c0c0d0884541e1102808203284140c1011201c1404140d070019100d032a481e01140309a00c0d40390481c0c00d454614684504041c074603409140100400d208940c00550828241c0c2d910600d80c420f0f00602c4085e00c407044941045410f44600031074082440070028021003d450b0407a068100801124200306900446442c0b240c80c203055402101c1000c148612001c040040400308202d107406203070382805444 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 860545404 1250 860544154 860544163
    0x20f040905060415090b01060305060402120f040b091f0203090703050601030507030c0603050601050307050c0a061109120319320304030e04090809040f06031406070210020f04170f 79
    0x181564540d001500f000200700c20000644001c08500c1d4061101745c90719640c5200b00a01070040310241074980001964588aa0f03050b1000c1c80000340d01c089541c01c2200c400300422506542c02e59141c29400002100d50fa00000e03013040a009400720b07a1b004000c03241c0140d0003500080c0003410f00380900303400000890400c110712030285001d071001d07000d050b15625000d60075541c10341c030600034141458100001680c2001c1540d500920341d042450796100c580d4000d0b41886d0100d44010086890020f503c41c0000070380014041142e41034507140b100b11486ca4240b666801241800085108200582101c280c4178680031a40a418035065100c0090701595840c100e00c280014034140620201c200002e059110340d004007903541c1500e0800c800c50b40c0e070700e4070440c80c441c090315107002c0c984134100c1300800500c983c0054021508202507540d050105003040f03440c2d100030307502640180700302045000c0302d140510840720526081064680b0300342c41c10b100043c0c00e208913015240d180c0100113000b03034803d20500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 860546654 1250 860545404 860545421
    0x1220120a09032112180809220209030f0703050709020708130312030b3c030105010b040302010201060519120c170a06110c101a030703050c03150f070309020f04 70
    0x42442980003c0510080014214450036444a4240703c0382082c01c2030203616071192642c0150a9981d41d44900d800304042c15850034000401c0c1201505107002c00b810b0782e0141c41c07591012000d981018607107103c450b0b0b548445001c0540320340c00050302048030a015a00070540e80f403045a1042c20480c1c0031a400d49a184c280e401900ca0709510400d844083d0740c1442403001205088038840454100d08009045009560b000e801d000303d802c1003000c40d19224203900e4214080c004000340a59a100e130429038040d0454481240558200704000c642450001030040d0f80b096000c02001c11140761800070036990a141c1c005880c00c10700420007042c034840000d0009d082c400b6400007801f1301ca085e845c0a00440c1d0503001d024000742d2042c8a040304c0c1220100d034202c1041070840d404550224070030301d40c1d540c01c049012055494451040000100400410341d00c81c0c255044050342d40504882c07980c04d041c40c1c022110046641e26101c0000d103400d00035030010407403d001420600880131000c000c18211042107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 860547904 1250 860546654 860546693
    0x41b0302090f040203041a04150e10110c0d05131805040b060619050903071d07030506010203030105061b07050402030c0d0e030903030922091220120a0903 68
    0x100246076003000e808103000c061090f2000c61462034140c035041c3c48000c8003442500c080c00c2070b0020a00340400e00c22840f4010046040c1080802c1c112280c40d50780704510210740310301a041a00310b20f59550100300b56000d049145000e0152104500340c120390561000142945403414024041075200700c42c441c2c000040d1a612000400b801c0c54109495610002001d60748600420801c1c0b000341c1001c0c16600c91030700032a040064031240344c0b5000078200b802ea904840303001401900000c034070700c04105a19000701c1a43d10700304003a880d0500120f80300c2c41300f4044d0582107001000683c02034444144c0c0e007584a40380005a428281e03c0383e002500341e034025290184104030118090010205d1407041c0c202014001d0001d5240a0100c0c010984a0091401c214420720a1003481152544005400113000c00198020810034185142c54161100c42300b009000042c00051505a6410030700e803004070701c0d5102002862031040381d080c800305a50080da014001c0000340c0313000000042c076000040000c804507 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 860549154 1250 860547904 860547907
    0x7050313150b040e010504020f06090604031a0402210a0b1f09291806311109091611160614030103240e06090f06130b06090402041b0302 60
    0x25000c101c1034130391401d201c03145030745000d040c0700041e61079410441d61500c05450b410389400380e000c001001801141c0c0041d0441154250000180c0182c4d010544254822140041c0e02c40002850701413000c03e048142200c1d50203d01c00c103002c10021880e480d400558144200ca10071503800742200c1c06811540130880d215144e0800c1610303030000d00c06244d00c60720008000102510a400040c003000c0c8160902010880b543c004a01c0319184c4940c503500c080044800c207484103206e085a601c0500000108400e250b147c900850b8008040504a80807218000c1204c08076031142000c0401e00d8149614140c1805100c0d10002c1c080c140900103201104186403c4401007840c100c0060101040d400c02103990160420060001581118640340a07641c5800803050003082803d051000b0062810f00002602c1001d04103e06101c00181c0d540500c50110140c49a03910350043d0000340c04a01e11008020040a8001440604156042583c01400148046107004a5500e206a8901c0154030400040e40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 860550404 1250 860549154 860549171
    0x209040e0718020c0a060c020c06160614040209040b180a0602030108300a091703030a1d0a0b0c160b09120412021c0c0b1c060303080705031315 63
    0x1c0e00940804a02e1000041d440d200c20031400c10740700c2c50441c1006052690321022601414400c000d81d46024002818003a9180e00b07910000d001c03000465012692182840006c0c00c10300300590b02180512703405000d91003075441350740c0c9070114400010086c4d513800000c031002e4940c001003000917006032030051b440140e0b00d5041c80052428407420214070000d07040481c4000704004541d00c0030078248880d202c0b0498450201c508111a00c0c01d259001d09510010001403440d0000048010350003074081d00c008000d03107800246040c10f070310003000c0085682d40110550501003071480401c117500c86050b414485c64040700c40360203a640104c482098a15588103800c000e0b120404011900281d8100410b10b401c02c0e1800200c0202c41944850003801180d28040301082c5811010103005269404180160855111140084150081c040401c0d80b24a0100c0d8400030340711a104100503643c040e40c9401150791010b10a8442c6d81c03010348030840c040710708030480000c64150541000c00001d085d902060100317 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 860551654 1250 860550404 860550419
    0xe0f04050a1e0e0715180f090b010f080615040302150c1203010302060a050a02010b030708010c12140a1d24070f0818030409091211060f0f0a0209040e07 67
    0x212103030b00440900d260250102031000d0000300b15040710000c0213640d0140d4441401218030660380780882ea200340b001c3e0808200640e00300008402c1c2c2c0d021000801c04400d440e001100c1c0e1010305d5080300c01188011007c03480a0031f0403440121418944a41945003030750300d50105482a450022520b0340480104417100e10010600624100c1d52680200e01e085505540004050f4414007030301000380130000400c0c4070502d000703401450440c800203003901c0b4902d948000c058064040c0c02c4042c7c00250a64030b50041018181c0706400b82100d100700f2580f0a5500c6804400007040500071208594042e4002a48205401c02c00e1031122081c0001c142c29030005410403040000c03002e00b20b0000d00107640d20055a86070310000c4c2652003c9008052004a012120706d18154400c9800210311141000c0c030300700601c41c000c1042d2007102d2a5a560007a01c00c550401c86843e510166191800c000350000070610840c542a2070542001003680c00514107882000004d0444406402202298200600401c03114 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 860552904 1250 860551654 860551691
    0x80f041a03090d050a050d020315090a09031b200612090307060507030e0604020103150807030507140102280804090501140316050102190f060509030318120301060e0f04050a 76
    0x1103d80d0f042040c01e000c560070001c1d1031401000c0c0541200c1e54080006071402c0001110003a00f90030240a48a490810f200c80001404d0102000e50200f101002061403002c101c20348016a2604108202290080500803180d0150310050042e44050700b841200a10b0319000b4646005045140056980e0000d9280541c191034000346030609251802107000f12a00340454100d5000c4d60919000403803402320300d41414440c2098006585071b00c1902c101004000d00014404150755006801c0540042407400481e40e07000301002c0d81c06184074501c55041c00500d0300d07043c2c11380c0718482c0b0b25450038145c84100060031504240d00506c1000e10011450180b401c0501402e000ca038804d00d603d034003503030620001035035078910a4040560b001005140c03c045c071601e40007541c21264484000d0016052440078103a40c0d40041e0340c0311090410000c40104440c100107000e0302d1010329418090b040d68600b8a05546804030303002c0d0541c0018055550365203a035034510540d40700b800e9120000032044241d40020703610 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 860554154 1250 860552904 860552923
    0x308010807031a06180712110405030304061103210a1d0721050613170c07060e1206090d0e030f06131a0106080601120b0d080f041a0309 60
    0x1d4028000c01d00108004444401440c0301104810100d5101c681c0855401521024403c000314007880500c0700b950f5200c0341000c0906460709040c0720745901040e8504079442284102541544104070409c19a4001c05041195540520640381403401041c01e89121542e24046040c041002d40b04002c0000c0300b078402c110b902c0d030010300302005503002844550756075501c50084030452040f00300d40142c1141050382c00e410040d07100040e28007504280c4948a004812131400f01c0b83c0104000c52540001001c40c107803001340000d0700044c1011440c000c070a44880b0030111210f0f41102410300346444055040103100e0140c0d0030b48008050000907070381c1c018000b0200c0702c0104d200e03801c0051060241240010307829040749400150450030303030442c60406034014040064910190300c00d00002500c03500700115a100b10020303201c0040b5860540d0001040301e200988443d4000050310070340003c41c812070090601038804003109032816072548840740d20070344100c07482000d42174000308103c8040300038891440f5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 860555404 1250 860554154 860554169
    0x6060f05130302060d151e080d05040504090f0203010e2d0705063007020613031b030324091103010305060114030705060c160501020c01090519080d0903030801 70
    0x600740080400a40001c00b407101a124071404609200d11804a510014546000091003608595508441040601062400d0308100d00c14840003403a4640880c0000501c249583e84500d0300381044200b0000345502d80c001d590001d105c410707900061318241302d001032415018004000d148441a4450142080b20f84c41c01c010148030003e1010083c0005004000d0725800c940254540c02010902c2d81040d20155825224402c0382c0e200d411071403031286200e0301802243e800d0301d096a807010b00348500d0b00c2e44544018005000707500ba526031100020301c1200306900c130380b601040220005107503803801c2d041201c165611450201080005464510540090010781c50b035041c10766140d500c3d4185c41b804148030b19049035000800300c0301c07296000e00542000e8400288526101c070400381c00d40780d4419488800c8035040c100c03004041195030000420a440506c169641c21845040c10148006d801404810710100115400c001c00c450b1018064000311802d1652a0006a4954140240016011781c070100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 860556654 1250 860555404 860555407
    0x170105030705100e0d082107050414091503160608131a0903071a0402010e0a0b091c06090b04030924050a1211032a07060b0d05030c0106060f05 63
    0x2006031580d482070f402100980c14000c0d1144c6112000c03414004002c2c200a02c014000540902240000050346010140c034041c05461941d9081c0c0c00d403954890b602a2080300d10fa0f501c400f01a500d080e6018540c00481051351014000c00b100118bc5085040f24280448203481c0c40140007103680904540d86c000b1001e0000c0d101000350380c45000ea0100c50b0070003507510903c8040040c8102d84100308498003c0d0340000102041c002030b4580b03800328001900c00304d001401130320016030f141c035151a90200b80e071422039020307150280d400c0c2001009029040115282500c094111010130b0451007001869030060b01042120301d014a0700928203085504550302c1c030340c001d81c41c1c000c2c443e03070701900600700450ba420314030740d03e440e01030040c2d5144d1004003a110a01d410709000840c0038003443e01660044030101a104007030b204080b107001c00040072419004100c0030522015000c95120381281407080c0018202c01a0403203161521400c540c402894611569101c3c0d504025250340482c1c1007400716090314045 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 860557904 1250 860556654 860556659
    0x31b0f040f0f0b042714060703050a0c0e031c0e030102040311091008070623190207050609010206060f0d020d080306030d140712110102401802191701050307 69
    0xa00c929800041403da8041c021514003049007500051909241036007c8680c00d10b8030840050140200301c5081e120701e800c00c000602d006014a4404c9502c03800100685003c4c14108100303406d85203820002c800b044114004181c1c951000c1c40140041c0d4007400a02c00b20f0031005007405005180940000e40420303044030100800d1001083c0310050790302d6440c025610302818203400c3d211807030381c000441500d0b0000503007045000c0d500c1004d06820b00c1c540c0030307256410303944c204029490040c10003407800340c1c12910014100c0c0c5030045680d014040700420340000142e254020070860404020200c1c0c0c0038600205000342c0345007c11441c9180c102500e00200740c212544121000b0b40950000280b058100e016603481031270091501e1018018030320001c40d111404005030f0800c60184001d0706d0320804440240410004400e0217a80e26a10040c03801119940342c0801681421070980144c44503590902540c5110441542110680304540d580c43ca070004800301c1207201c0da141a0f000501c2680850002c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 860559154 1250 860557904 860557931
    0x5030408031506071208060a090516110114131b030206120403030f051005180105150c1903080117010c0206191503060227031b0f040f0f0b04 62
    0x8407a0b00903000741400d201c042240740460300368058114000e041c80c2190340c90000c441d601070859445441b04513200601941d880d180e81e400c54400341c1c0c0c49211040010301c0382c00c28034040c041c1c842d0704400303d80000548040100c83c0c02e40091050307402d20200040e41010307400f884420f80781c040021408445c40000985035600081c094880c2d0303c410720703030300120034000f40506001c2d40c085541c5900d0b1030001c2c1728502e0102512104d920441c040c46200340c0c80f21a910404103055028141030ba4405881c41d030100c1400104903004e5001081844214811031040103640483d83c00440b146034400d4841e00070725410000c00010b034100d031280c03103c2036a142c0300c0d494060560000740250840030319042d05d025007051a60a4016000f04c00c0c08800100422000004110090303008000da10b0300788034100100e401014050504450980c94240d2641c1301109519103004121054042a10000c046807982d40300940480c041e11794680c1d054403290340c0d030440f0b044403004901900a101030202c8003007012400c0c9042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 860560404 1250 860559154 860559157
    0x30f030415021c03180218091203040c051210060b030601090501020604050c09090a0f1211070303020c1e090702011e02070807110114030a05010302031612120504150503150105030408 80
    0xc0e034100358a88045d07040d40902c50341c40c55401c54014004010070143c1021440e0a0b1006075905000d0f8891840c0070022251600d050f80d0150b80d00c941c0d41d03c0c5140c41d000401405001c00000c0c2c05142c09150340030107503441103124800c002c1001a290f15140c1c034140c0009000001681d10040c155001042000700280b13000c00c54044c2c042c0100c2d85103045840b81882c1501d002036011000f007042c03804281d000c041c404130040c40a103000305507488a050b44011750034103031922042d00c001001340e4444c0500d090140703010400d01001b5158092a160780210305800540c01c0e0310140d800c0c10150359152800d00c0e0700440c3c0d0a45400d4480104d205500d0400c8682c0d90318024810020060305041d94540c400000d60703c51200c00344041360b03001441c0e4985c1801c60180b0001c12080c80100c0c420b1280340c080001c3d6802540740b00040b5041c2810205854030180c580c0c99606899406400030410200004111003c201e01d0030300c13039040e041e5076a030b0b140d01c0c0c9901040540b02d8103c490700d043c00014820040020030200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 860561654 1250 860560404 860560453
    0x1140d0510090c0e1003060504060603090618050d030f021614060a0b03031c0e2d070b1602040e06181213170c1525032c030f03041502 59
    0x2c80545c2c1c14401c001048009040a80005500030709020001138441d40c1900070060301c40c0155420031041240700d102c1d0b1440160b4140040598101441000f06d090190b401001c00c8000d60350054540380282202050380354141c0003c03200d8140310090480e040301c00701f02044c0d0140e200c82c004c0040740407040000707a0f00d0203281d448507010140503022000c913403c2a00310141c2c1c15010021078103165140c1c8034801100031a12000d1144050814060b5a00403002400000329892440410715080c007010f591100b600d81c4010607608144c1715001c040c6248030803c81e140c4a91031507546202008500511541449040c03521030b40100000e001754502141d20344688411034089540c0c40307110a4481c0040c50910030002d01d016801421203c0440166803e08014402c0070a404010713280500c01107038114030b403146450701400286070728010380e8058041481510210703006031055254081c0103800a440c0964070b00503007105402c003103820803024074010f001c407181109900192076000c44c0c1050000320b074100c56 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 860562904 1250 860561654 860561659
    0xc100c021b0a091406030d081005010804081317010c0201200a180305011b0305040f02060a0c02030a1b0806070503162006070801050a18020901140d0510090c0e 70
    0x6250154480c2d80703038140c001c000d002c400e500b4041d44140c485515121309048440601900802031500b44051248410382d00c1280403000c00038696050030011220310f038005104503848101044421168442681044010120600500ea00e12200340d0703080e080d1030f10100780209681c18a4119030400c20890390303444d00352522020494a4480114003126140c030030b070b0f0382012609283c810200501c201074110303210100304911100c154004165048040303520445020700012a520704202c014500030300140300321807240c41c001034404980e0300000c1c1000c0b1117a4045554a5070b440046031620b19080404000b000c9500c0680310f90310b040d400251891200804c00032440c60101148400d1902030810405140c0e24515440c49001c44c9404241d51090305550041c0464811b500004991801c00ba401040d41c0f900e0342c9540b01e04141581410103900091f20b5036040c0000c0b19013600714a500200075000d411272010303010506050182188030060040e4010610316400d006400213206d820000742c003d240c005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 860564154 1250 860562904 860562943
    0x40f150938010f0e010e07080601031e020a120b180403080a062105010501171e0304171506010e01080106300c0207080a020d0803100315020c100c02 65
    0x74901d2001645000e1450442240c12240c008111500c2c4446040180c80c000146920740f82d890790442810082c0c01c84d10030000a0204000a20304e5209070004110541c1d8000640c181c6010700110340300380d070803505d80c3c1000268510f01450703207101540941c3d100304600760b400e01d00e4180070b0610b101220f040100050103011480000c2500c88043d40c0c0400001e01640c02e800c442200075506c0d5694a901850041d5555802d01001040c182017410358500350b450070200401c003032014070503100e0100f500f48204564502045c000052a04109070051412207079070805410100c020001000c5a031101511003070401075040c1045407666001142203054800c607040c041d0b0f801b8424007400c0c04c0c0d40e15408500c2d00c0c102461900034222031581e04400c0040c0070940039a80d4064480e0440c990320203c40402940c8034060743c00daa8045940d400065810610540255102a4a075140d0440c111550704449504940c0040d0201821a0a1003018461202000180520078039550001d503103401111003d10a8003c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 860565404 1250 860564154 860564213
    0x1050304050c060f070318051f090905090102190212070609020f100806123013120c170a06050702012405010f0807091802070209040f1509 61
    0x1002c0001c0c110782d0100030003040d03440245000c00c103250340100383d01702c0210300c044000c001e19200c00b00d443d9003580d00181405400c504200c010415806081d18440207110f035801011500e4500c038000c080c41481044005a0b82c0c0f0156401c0000c1c44078851083ca0854001000c0000f1228002c401c030707001c1680002e404103600400f400041d4071542c07900c1d0b01d2544044281d0507400c03915040300b104c5101e100d084403001c011400701c0e00c505403034085100a40d840c070700040048000000c4608c0c6254a100301118400b401c0001803400442c07140c209411190101e45030406c5c2d0010011301500e150098504c03807011a1021405594160f6110240708000f04042c0c2c0311000261003038400d40c0b00966422030898043c0c00540c070301122640294043c0111800212420301e92148076000712041c5009150035510701210b00d203010f25010024101d41d40406000390200320349005a40c5460085000310300800c0c250700412410303e003480c2850150341030b4080c90790070120f603000813503007030039000102c10384141c0001c0040301c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 860566654 1250 860565404 860565413
    0xd0803072705190801090b15010f080a020307110d0225050f010c06020f180a06080405060f070c0602030c0307230f13080304242a0312060b071b06050901050304 70
    0x20341d90340101322550b103400020828040403101440c0070340a84803001410006160045440440c03d00a84010901000200c0c41c7c0f401298002e561281441c5006442060411195410002d01408980042c1d0015003c1c14a0501c8480e40d94610f80910242e24843e138a01008500b000d1000e8800b18107000380c40e4618800d000241d012501d80c5925881c00641e46d0078208200210310055030845809400c0006003c16000e014020843c06550404e004161983e95004003c0c0365131001840c2000704544101800c00103441030000e540200c2c2007148480e02c91602c00e0008280c404124070b0842c151f4066100002008080421101c524220050907503984101d50040da00074003030f9900c844054440010300140104852021040b0310611044019482c90b511400b01c03150320306041304a212070441c070300c0e5046901c043c2c00c03a2180184241441c09040c0d01030084141211196400001d50310000241c04080000300c00448031105800e0242411003424840300802601540503018148180000810b0070b01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 860567904 1250 860566654 860566699
    0x5102a02151309020456040801020f040510020718021806040303090501080f060a051c02030129010215010927060204031a0618060f0d0803072705 64
    0x8100c400c0d819076070790b99100301c951405410142d040c0c2d24500c1300c0a48900d8250f01b00807841c00c0070713050380300d1a0020240445643c0a00d1036407080ca0001c060030080091030380006c0c0041c1c420381411428407030711540b0340020300c100c40710076800050840d0406d210038010551040140c2417403070040c2d100144c881d480f441c030030b00301440d000b01d2240c0d2041d00031030000100b40c0c0c002001340549d6400c0c1d07100c54140c0c8070107400b0304980c00300343c40c5162f001c0319040e010301c4076003449894107c9140500d8601560f00d6601c1d00400d003110508800b181c0c9030324054100c0085113140a00e882c1c000e101c00e00c02400b8595001520704800740c410701500360500d440711405821403250f03041415080403081d00b0464040712130702d80b0034025442803004640d511407140092140821080101d80310b1400546920300b582d034440c0f038335806441c00410b0b495001041800402043d15030006134a40144134041503a942d0a01c1d50029000300b40b110202e910410703807014140e0b00104800c40e80e8046590583e004110400c00300e0025114 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 860569154 1250 860567904 860567909
    0x818010e070305030307030c0507200d060906090b06300a0503040f08010513020102150a0f0c050306090901020309150a0617160e0606040b0903010605102a021513 71
    0xa100709100401403040103c0114004c00a0703441c10000421030113000d941710301440c0310191143d1048420385a000300b521108485101008040c2da00001484d501c4404440300341e08140c0707010781da03200c2c90010840328000107508914100d40d61608140901e580320107003a4816200b1904c3c45c2c08200300c40018000300001c1d90800d0f804000d0381c0d102e44d240c44d03040312107201c18072411074a50b081074049460260701e807011301030881e01a03002e01510107140b10a018030a01c003900740081079650751b0b8a2b0455603c948111040190b09a48031507a0742421800c02c01445000f8010900c0343c1d1042060042c000d0000800610300412421060010303a0742041840c014200d9620401e10303440e04440c821020b0b4000b150209201c0c4000c07038501400c80c3c842d980402540300480d140c0f9017040e0100024801b4001101c00340001c9040200080740361501c0e240440d8064a64006880c0440e032034001c0139034151441030302c0825801c1d6142c013080d01c2d1203d580014100b0003580031004103111000421034541081c40144602 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 860570404 1250 860569154 860569181
    0x90a05150a02010c0f1403060102070801110705060f0906010614070203030a09031a0702120906040807060918050906070c0201030e01090b09150108030f0a12050103150f020703081801 80
    0x241601804209040c1c1c450040e0030019480d20f8180c020407801203003034034109440e903541c113080100c000f42c1d164065032001c0d000781c0c15840350a00000d4101c1c001d0054442442140440b00d40724001441c042d40351000c058803114031440440d040008403c00000ca5078112401854802014050084a042c044c4600403029403d03000001d18014140d801c603100c0710480f4031551810755002081f55105018403001da40207001a00010054040f043c1e07000080c02d1640d100900031450306640340c5125107400030315071041000c41c405460401c000c1024002d803140104600009000c0c03482c0040c00c494070390320002c12080900c840000c02c2401c1da40701e035008008845e4128000c02c680012403c2165480c001104c5100b21803154800d403011007200402345078100d4520700004c1d170900c22640c80040d850f4204004100400a01074071040412050307010340703402507000e10140c200d002001d109143c151242404400d1219004211245c002076010740000d038026201e00800701c2840c1142d460340d001d01350324801c251 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 860571654 1250 860570404 860570419
    0x4151b080309150610090e074d0304091e020705011b0207050114030603010e0303010e01051e011d040b0d0818040c05070b1f120b091908090a05 63
    0x8081c00e0020f9440303040020030204007019650501048401c12034170414800003104a0741c104202010250402d40116240c20a010354a000c90710001004480b003003070801e15102c0c515003c030051046d20701e80170005e013804075040070606e5100c1500d81c3d0384580d100301450315a841c28010080ea403105c0100c00310001c0e0440656554460341407140c043c3c5101c05400c1d950080703031500214824000601a02140c0703060f12a41c500c0403840942000b96080141141d1300b554954945100c902001d00c000c0d0301a018840203400654100018040e411546c0e40001601441864038031990307a8120b54814441d0040d88240c0d0b080b41c00c8080850042c0c00d40403541a04681c0b00c5c4140020000300030082c02c03007054215001c10701180500100800e55141c0c21414020440820039140030071142a50789601600050013104103140800c4048404a0f080e03004a01c0904c02d001083d0401041403078058110003000010704c41d4444040301055048141580100f0508000039061000c0e00ca00350b0303040046c1700050418 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 860572904 1250 860571654 860571661
    0x2313020d080906130608090c0405090c040207110405091605011d0405070309080408100e070312050a020c090c121b041203020f0d08010503070608010b0a0c030c020901080d030c030204151b0803 84
    0x10f01400d1b001d0b40d07691014061124900d12505141c41098400e00c0c2101c000d0040080400c10f001c002e511850702641ca483c0302c8808826191034a0140078040e41390100108141d500381c8400002080b00d40e0807031070401c12401c0c400703903845030b500000800d035100440d00050700783c842003001c0d8004d02031101d000700012001300b400a00c808022a460224540c021001e10104020100c2192921070b0341c0801042da0044040040d102c512420203030030a02410300448a03a034000c080041e1107502d007110b12402e1050005820109102c0c040e910580004c2d85040a804001b9460a04541400345000e6001440c5c4804045414980308021104d00394080c901a00e28009131500000c0c2281000d0003074034041d205a0310f000a045104968980c121080301c0d50440c1070110710070080707421002a042c260f080184560101025079604900c06009040a0006004c040600000179050f6400c0ca0404014103105000401c501c0c80d4211182140c05171520b000b0b0104149604039940b090781c804405405018044100b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 860574154 1250 860572904 860572907
    0x518060a0b011115130c171e0a031413171605101d040e1905100e030d051e01080f060a2d06092313020d0809061306 51
    0x1400080000381d90301d28016010f80d2a1075034800010315840d00140b040d100084030085c0303030310880d400f642c03082149000f40b80e03a9200d0840002450840c40100e070700154040e0480c1d4907070b40e40540b80b10044001908000d500c5480c094040244070300380c170700b2003040020040b0700807499500150103054100c1210400258901000f40e60350f4071280b03038030240c1681c101d0200e028079003c2f003100342403a66640c0301c04007500203442c04000c20b6502d02400b5007090f02c40340b1428403101e06000c03000b5505c1c08422004942016030815928110318801102a031500d007802c0326110410100c2119240711031000f001c0f0f400e482d00108405003400600c540c00c00e80030860000310303007400081031010703039410386078100c41d13464907600c0aa0003103881d002400c1d400e04018141800400c000700004000821036a940001c2013551380c0103150175141c0b41d41012018400d4070b030740c0c002a1404108050f0700300d044404d140300245416404503034036140b8280c000d4078985020a0880240c1e0702d03c02280c8140c85030b9296504840c2e40e4220 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 860575404 1250 860574154 860574161
    0x30c030408070503150906151801031505010b03070e09040c0306052a1812010605090a0b091003050d200d05072001200102040f0f0503070605030702100518060a 70
    0xc0720b100e8044d04c0141c1702c4014506100c0c901452800d4041d00e655228a4440d07465000c4440b00c01340c1007092900302c1c854480e106408280214014540d03541d6400503944848211b441c160001c000040e814810b00405079840b101a42c00c44806582e10107054441c1d0030000d2414100364030090400d82084204804025024903c1030341d5030710409000b04800d522400e000580c003e500349507060282031500c006591030140000100c410020000003181d5403100301007048440301f214204085505c88134814110700781291110f0b13000b0540c91502001c0c508503900ca640341c60a411107038082120000301110010810700003083d000c09020f048490801c1e40403006080341c0c100b00c030203982c030090007243c80c401c5810042103a48034030310503900d030012011005c86801c481c0150142920080d9401e101c04184000000b41c45006070442c0708404421600e40410545866407580200f42003050910034405241d80000340f41d080f075400d5401c04a415a2404a04412518001e01e0043d551050030140980700d2501d03032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 860576654 1250 860575404 860575409
    0x30f09011103030f1302060720100c0210032301030515010503010e0a02010f11030c0a0b010f0e0c070201050918040b100b19020f0a05030c06010609080d030c02030c03040807 76
    0x200e03400001c8400803030302900e80c00220352001a0b005018000348400600b102170380d00462004001c2810000301d901e440146140042d98a501c0075410440a442850560790b50025448a45400c4420003c958045081070741c01a00d039000f41500e13640d02082110650050074042050071890518a6a41e410604c5d82e40c1a02c15001510260b103000110f02c0d400c06000700c4c2030f0107034040020903005405600450f41c0e061000d5400003040001600130340004020f000500000c07407120b0060580e07000601b4699600c5e207060780550503801d5032142c1000000040440c055200540e104040c5c0c440d0383c103000586071840361821096000180e100780040d20402c203030029026500030030030b01030184c0c2c07641c0c400000610140100e0b08810002d100d52070482c08102d0083e1039221103841034401380810b03542440d2500a03800c00848003504041007080e00054104405030050119141aa000e9032400d1000c544412124942108060b203074043c402c41140200121400b40442d00100c99072103a80742e0b01962500c9190 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 860577904 1250 860576654 860576657
    0x140903032502040f0e0a12050405040c020601081c080103033e010609020a02250b07050d0e030106061439100221040f050a08121006020d0c0f0203030f0901 68
    0x4c0c2c40705071304100c0c0c0c1c032075960440f403035400134814404e543d1640310840f2490a034150801408120204164803a4015404450f40300d030010034140d410844418101104444804c00481290301d501c0d0b0312550001d81c89045a81605003281c8903c40b0003002c0010010380c0c26141d5071104269020300030051403040401914520400800c00b440e201c00542e0242e00c00d03100160016070090340c3e440c1c0c401c89000070700540b0040c01046029065070326804450315802c0384105485035000764200c0a40d282d00301d2004000000d08070300070030420b424001c0140c1121030640364903180d2100810f4400d09882c03880584030f1010704000b07480e400071826003d04e1349e100c508440c0e0405035001d1180c400034001d080d4020b807401e9075007442c0d460680d07014122105101690003442952402132051110010810501074600d1050040311045c0d5940303a4100114180c010140c001e412203200100d0800009a020035104080c20403858001d040e0740860800403030303d490308140a9814000010003001c0c00e140302c0f00a02d0b41c00002e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 860579154 1250 860577904 860577911
    0x304031701030b011a0936011a0c010e0609010c030b0405040f14190f03030b0f010c08090f130e120c060606030c0706020a0c0c1514090303250204 64
    0x20322519040100030b11004082c258400014000f460602c1c510040000010351441d04104070500082c451001980d02c46800081481800b003110b02000540300000b10039000f806a00d504d404100c0d5001c0d41c3e840d4140481090101c1e540c07110603020b4005100b0401420102e802138100500714a00911070501d6000c046807400304840b0180c00c0900030540315070742100e00d50a4100454507049115054200b0050541c01a08991141d02a507404039076202406000c482c0c1740d10704245000b50446041d5100300e445421515102143d40e0b90002010181e964008a110740300c00e80310002c15041204200340305c3d4820200303280f4001c0300c8204d03800f0701002c03880038080b55250076021681d401c0ba48291001032038030340c021a00051701400d25400031500720b02c18002207880c041c0c02c1c0d00c80d00b08a0300f01c01c680800040c0c144004505000f03410b601007014140c2e8000810001c4611840544010801c410b103403000040410703445551741e014419500b104441003e884494000881da0084542c0c95200c100d10072890b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 860580404 1250 860579154 860579177
    0x90f0602010605010903080703030b0d0b0405010c0507050319110d08090c0114160c0504020309030307090902192102040b0409050106021605010318120f1e020d0f05040306050c030403 80
    0x3050164808850303041c2c541d0030b401811034072401126800043d0a409164440b030001d1240d842e042006155103000d0301442d003c034202481d0160035261504125070411409001810202e800441250030010102c40554409602400117030b80c2d521b08107046074045c0c0601190381d581c00f038001100c40d214940e00300035500f02e90480d00c01035440b011280526010210180100c0034810240840a0f0050303000d405852481039441c00018141d074411645600950008001d2101494000c41c000e030141c1041002907090280c95000324486010300c4d04120300300003010f1100f40b0303822084c1547e41c05c09400c009003559291f48440c0b40b1055644280315003d3f07401c2c5132800015601c1e10110700c0a03160302400a003014002d1900c1e004501400510b0f0b0004020160341d080340000580c1c0c5100419294821b86801c03603940701c0c041703010380b007603071003004042c0001c0d0411000c040966010502c0c54150f9244d00f0134490060306180e040300d982c000c03900b0051603949041300380003d0032150409075209034440c0d501d07a10b0081 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 860581654 1250 860580404 860580407
    0xf050a0c110604030927020f1902070b030a0b13180210210f0f0c08160e0d03051b0609160801090c09020d0e1006031b06020304120f12090f06 62
    0x42e0441c3d0180020740050814014911100d0f0032585141c488129034481a018031038400c201c0e44981820311000c100010038202e003505440c2180e040c9800b40c0041d02c035407890141041064440102031115a40e40c60207012002d640d2280d0360020340c444514100700c103501c400151013804815003002d85c4100a00881c43c410701e440740309991081082800301d8080003c1140708840548001000d581140da20782040c1d1210300d03114400c01d0049403203a03880e103c0c1c13070902200ac4200d1000c1240342c40304025190000c860301da00c1d20b21481d8002e65051500540e5451203d2030780030304203100f400c1e0344518060801440001d500c0011000040790554098006042c2c4e220405822a240820006c02e0685c0c00b010401800480b071b40038142e105590782c1d000c80c00020b8000300c1c0e400d0410002040b00391035074840051050000040c10340d4076544561011501c081c7c02e10b14069624001c41c031401c0d1080b03503200c89204c2040f09101d1009000703984680d07005d00c000010349020348617170000c0c003400780b03402d03c007240014045 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 860582904 1250 860581654 860581663
    0x315060f052706010c080d06140f0a0506160f08071236050604170f01091e020d0204020301031104050a05100b0309030f030906070212040e06130f050a0c11 68
    0x40900b90542d2a19016120b81224080c10050686040c40621843d6101044000c0e00600b001600c80a000400c10308103080d45140c4d4140110013800394210320503844c919101c5506402c2a504115500740d01c80001c030790701c90041050002c0040040300140040410800158050940c4a106080e83e00c400700c000c000856000f8a1480ea0700405943c030000c0300340035000d000c10840c414041e00b110840c2c0c180c8070000b1440c507034803651007d01402c02d4240080ca4200080c000880300304012002802040300d651503045645540c51a2100351f414098110011981d504590035030442d40600150744940c1d403818010f0128000c4041709000720304000010780581030511465100f58481040c5400e030358241050040c40342c100400c40d903250b10040103910300c03141d041c00285121382d0141c4005c19440c907001500906141001d0301928880000703000c18400802d02a900c583d2202d000d480c20412003c140007050090012a00d03400c01076460402404244c1107207803c4000e01d814141c4a42403d0078110380307402d588 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 860584154 1250 860582904 860582929
    0x203040209010b03180f0c010201050112080f0a0e0d0303020903191707022701050a17031b1009121404150f09030b1006080f070e060a02070315060f05 66
    0x7004001407084000c080061508a006406409500c3c10300704c8070a4940b071401e1141100c0c60740704c9041040150ba09025550160120900d8151004100d513110f07101800341403603800801e2130208208542610071070740404000002402929400c2c10360034054020351001a038103010340640d640e914070281070302d441c840050798030226601154840e001d402500e5004620120384c41081e9480502034441b0202c550126007c40340c03418000b55160400300090390303034183c0c002c0340c11401100340507840d00008030560340640e6103019a00c2d01076005078920f03400d140140c0d0310706100078500210320b000d01003a013000003441d111617200e05c05240d2508142c140315004170f00c640d01d10400740461510009204071101d21010302e0a0403d440c0c21500d80d03660b025080411503440e011800c000004100301383d03020b80c1f080d40140c031642000314107052010004058007415000b25020b41c50004402510724401c000c00307401190000b11100e283e040c4180f001015008500c1040700b90401a14049418940440c201c030700e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 860585404 1250 860584154 860584159
    0xa0c110a0c0905130b092b050412081b0c03060901090f021005120f060f06090904020f06042106110406231e0307090801060b090d081e18010302030402 66
    0x480d15004076071001d482c00400d03082455003052003034000910f012403018086c010301000342c20865880000b5949030120703108002e803107400c104d480304c02c13050300042140c00b6615030b080004404065410400741c1c138480c001c080c2c040603c40003c81103104c0d0b40401d001e07460031000c07016500706840c0c98002da800d0b0741c0822005440031441242410042ca41900420040d0485d420700b54148808020f003490580012200da1504003001c10402c07990785080112180c44440c1100e00a040121503030200d000020010402030294010314010300550361503805460040481d84101c207544ea0184000000410a801d0112000341c1030026045800740c6c00c40c1a202aa14607030b0f11080000b940c0740c4030040800a098810070300b030204104200d00520016004c03504003a002100f01e55904240740001c0290800d544144c131603074540502032107104410340807103803030340d204a911401e811864140810144030b5403854010152206640100102c403c074081c100060403111801c0d04400c842c2d00650036440110382c000e5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 860586654 1250 860585404 860585423
    0x904050c0a120e0a080a0908060a021206100e040c02070f0b030f06010f0903020406030c1d22053c06090601050112140a0b04060b180103230a0c110a 65
    0x607103140a030743c009015000043e0482c0c0ca05180354560b404180d0140e1107403400604040ca05100f203580810010b5005200d0140440c82d004030314001740001e05000d003407184104135030700000d084107201d8070002c0d180d0b03d00104204425060050040e569240e244a4001c019030385500c0010080c03c0803080d00c0c13042c00318030030016142d66500300459501020841850520683c4c0780084051384961207180301031442031548019060602c0c0e0f050038540c0c3c0e110060f403240070030407041004100d1808185d1341c805500c040c2140314003c16103849070411081c100d100217052001c070500c0c1c05940c1921074a041001541c80030700310440341c00c01200d40b10f4504541581e02c56100c94010091544103a908891075440c0000015034100300c40340c01404c0e41c800340e42c8040810785880c503100242c0307800d10401006011039480a4a80080881c21000c804101c09029041c1603480d0310110881c2d01c00514002c540c03450040458080c80c140c1c45140080c48030110000c00611201c51040d01c0700b500050803034005810100b900c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 860587904 1250 860586654 860586677
    0x3a0512091c08130f0213061e090903020703030f050408010e1509030414090622051906062a02030f0a1a0103030e0d08040f14120c01140a0e150904050c0a 67
    0x140c09150318202d800002d005021031503101c2c903105150103400c0344100d02230044040030a44840c140130390007641819140c90f5111000940008070002140c0c2d0604003180001d07005a404c0d0b650380260392109400354240282130041103008a8005407200881d03001901a46a034807e00b079581c0668020801c40c0c072800d40c8100e88070714103005015840354004041c4600c5124070704c200b040c00d0301e072224803c89030340d115800c1c000c42000303d010010f0005203240080050300e00e0500c000b400b2410318108100960646461060f225a20007040300640c1e4000c0c1c100c8040d90000185140d8403e42d0410680e6075501c5070500c25200e4140114050499400d5542c517000c0c0b00e541c00421403d2920100204c0e11507408001c0007626420006141d001041e8203190103107060040c0c420312084054014081106800c0f001031603031241e80045420320030901c901600f07900d443d440c10007510f071000d04000281c0c0c0001105079003e4000e038805c0c010a6a6034041e24184280d4a540c40c1003030080c022a1880404500c42d25581e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 860589154 1250 860587904 860587913
    0x20f012310030215030a0f0e06251b171306091401050d1a03160801050906090d1d03060a0603140a0201020325020603010b03093a0512091c0813 63
    0x1946d0854001d490005100c0700141d180303002c0f950708550f1101d0a41040b8200003a0840d107070121070348503944010300c0310021501c00c00180300000c1c1440754a1040342d01c1e540001409080c02c98072014000007c101959100013039148080002688107100c0000c500100c0498161103008a60708140f01c1070315068141440200304c00060902c5030700303c080301c0d554401810070030b9034200000c0780b481800d5140048001d0800c0d50090944000070301c00526030344480c0500c902c21100050b24101038181d40781800d40036000307107030311a4100b40070090030f42c0c580308000500c0341444c080c0e80036408403481030050005c8410305c4009651660f104100181c0541c1081c0900013005a0000441003040303009040e942010303400d940024400d4001780c004084d005c0f0301200300506804100716421420b00d9525010682034203440d10000c0400840708c8811102a10724000c0480e54061000d075600601280c0040e1351500e0040d402503a220b00b40c2c02c084883d8200358010404007030003810014050390b000c200b410419405c0d07499 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 860590404 1250 860589154 860589157
    0x1e090302060d0f021e030a0b0402072a08030a03020d06091506140d0905030c0c09010b0301031217070e091e040b040c0e04060605090f07120507020f012310030215 71
    0x6940f981d5035000c001c4850715500b07a10411800352109403042ea22810600c075543c00325981e900f1090701a900c104503100110b1810089803000c2d0b007043c0842c2054821f941400d0b01380380c1c5554802a81031102003460706003da0550013408480821324010440540d070384050703a003510801071500405031290941408401d00c1181e03c21940020405c0e110b10b00f03205002500c0484d558440f00344c8051b04080b03a00ba0402405000141c64002d00f22800101c0d035040042c2c18800703110601c402400e02d40038a6810056500954190020a0840c1c098031443c1c90304200c050101020140e04a109882070350019280e4990005502071386003480c0c051800d1590b41e55200e01300e0840140050303641e06200000000d22068150706184a144520030204185280c6010b000602c0c401500c0c4408819002040001d895888440d0032000c08043d01c000c00c7c1a11111401d03402c2103000640c02e84903500f040384000140c0c125502150100f20445070701010744d1358041c4580070b04900c50000a50180300303110803400302640c0300c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 860591654 1250 860590404 860590421
    0x6080c010302042301110d050414090103020102250302041a13052806050306100815011505030403201e01020a02120a0909050f090c0f100c0309030804061e090302060d 73
    0x140505c6e502c2c41d44035518540354589180d1400690002014800c83e03007060000c3d072080300c0550380201c055040da40083d4440d01e20b001e0101400c02c180540081103111008840c00854028100f08880c04e92aa0400a02c481c04080c00f07010b529100048105844580b00322072203020714100242c10341c0c0f046582c81030114060043c419415480c4c400200c1d56a60038003103a0f00071441d600907000c0c1a45001100d0f400d000c1c03440403403902800c2c240d0040207061100700300c080d00e490b0107207401d80d80c0350b817586010b0b40e40d031114401403903c01000300d031300c2d181d0344000149609440040d5000b41226402c80d010340e60a03403040000c4040140c0085803500b44242817000500b4841242d4207142c00080e0300c0e100030714121141280c01d429544070007020b0000d4440207100c480907a420a03218409140c0340d940c0442e0351007400718101c20401080c40c1d001018180700755125009164841d00709560f50b0b0307035820010102c02c0300504483e04a0394100d180b180c3c0d13600403181b6004aa47c0079040340c1c103096888100d0801440c941 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 860592904 1250 860591654 860591657
    0x1050912010c210603020d2a0312031815091a070309020f10140c0304080a060b0a060801030b07030c09030614071b021507021f0306080c010302042301 66
    0x5048050105028082c501502d0100c1d914940d680f01914404000c003411085010407503880c0403424030158844c0c2880050355a0001c2c94484551221803090601c185140008862450311b0f403404000c00040d140400340150441d0707014480e4428000e040300f5558814400100b20040e4a000c0c40708103207540e000540f4813030050417511400502100c040b8041d54040328000e00080d40c8080340c1c0c0031072425003229003220b41c0031341b507034840c81010040103010744045032241c088080b0b001c01c0d0b6140f4590108111000340240c00140c5019246602d410360261152a025034400d0080c0c0d0800300c0d500d4840e41096041700d0f040b5200d114681c0b1240b4081e8001d02500412408020300e040020012407c00c0c090800000040381c4074140501c1e2600c4000c1c01c00705c08032568031604186160300005a668400500e03482100c0051142c4c0d24003240c4000307461f1001d28044020386841a811852034640c040d0300030070449030300105448069143d4001141248998010300705418030024120720210b910b40030044501006 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 860594154 1250 860592904 860592919
    0x201020408070605040806070f0206070e0a050310270b04060c0e180906070206070c0204330e0114100e010c020411130b040f0b0708040e0109050402100206060f010509 73
    0x3074072403140c1032501e0350304202d0104a00080030411043d0402440d40d20401d00e103061050201100c10094945102130054001c108400800b0041a5505032141d8014000107085401001845850344042d120701c80444015142e02029042201002da03c25103007181c1c0320020002a0f81d455580d000241000b01c600c20800c400c144010145403101c0586900c0c19988040301070741403400040030f40c42d21600608001c1150024414460841d4000720b1400050380e0441d030100300c0382841104400030b102850048270080d41062a2018072a0070520180e00f03075060129188030581e200c607091128803020100072600090b0b8901c1910072188078010b000c0c100f410501d4120b845200c5034000070701b42d64540d48010442040014651800000c0c007054030000c091000090341000d2400c00c0f100c5494007540701d0a5010780700021020100300c5000e08440282000d140d150a89585400f090b400601003150128080e10642c0c0300c58092600000d8058130a107001015402c00540c070b400110342c1908288005a0010039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 860595404 1250 860594154 860594159
    0x8010b030c0102071e050d20010c15110c0102160b011a0405060c0c0d0b06180f07030b0a170d03050c0702030c060a1407260a090504110d0e071a041d040302010204 71
    0xc1f0081d05c00700c0c50703004102d9900c43c0301c00c100c5150180d040c00c0d509141070004003900c480003d20925082d03814407034290000a407009050390008007510811601c81101d510018400076260920355001100394000d4884200a84c0c136050b00d0400d88403a0600710100350010b1104000601d42070008120401043c4242c82c44400b18034046100c00c02034001c1220401c0c00a0200107581c10a541500701508500440c0710351400c1c5031840702481390740a000c01d000c064481307040d40101d44a03151800e005010b20284800c980040100042d214540005000002401c0c280411807a001420594510f590000c0c043d02c01c0786036000810501d80d101c403100b60f040c09604420ba040381460900036100c40c81c09160202092500840d692407905401c9080511884003400310103c019071040c0604140c0e00151000900c40d01e20070841c400d2070142807003c0a48504000040c00c64000c0429448112903042c00e8400141ca10814914014002c0c0d0040025801c01c1303081030300f030192402c0481500140039000051910380c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 860596654 1250 860595404 860595409
    0xe0303091c0311030a092c2701021606090f02180a150501021c090b070501091106070f0b04030c0606172b080c13120b0a0903090b0c07090f0608010b030c0102071e05 72
    0x808503042c090717040d45106140214230007143d85010b2101000021803621003200010126141106006000c0c0d40d5581010070400c070001a500d507200d41c0052180b003c0b00201c0048210803041199100007881c2001e490100340d1210b41c210350300342c1d80305802034240c860310303009a0031701140040240800c0043c5040000780c15482ca80003419090300880001c0758804139402d1601a100340040401c0c0150410044503010806810b0034908041d80489804000c0e10795060883e0903c096480c084c04d90b80c83e20100040c812110303002c7c65162089030040d100400500000301c0f0050040d04c1d100c581440852510181540c418891250b0200d00195081d007000d11009198000e444541c120740c003400c4103007072014240210030313600369807040304581c09003d0034403141d40041401e58a07105a0210080110b1500141c59003800301c0030103489200f00800004040e0f9502102a260714814000390703510f00002c07041581808034004450340810b07001000032610b04080e034031001ca52410380314910f121022001c200c59 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 860597904 1250 860596654 860596739
    0x804030803190216060b060a0806060d0b04231b030a0b04020d0204080d0914100f05070615140402180d0c091a121b010e0303091c0311030a09 62
    0x481078074040c219051071454170b8405c803444c007205184565030603c06403c80e564491000c591192080e0f40c03094581c040d01440e00041c00c000740b501d43d401401c22555188144008a807e22030f4603170800807845588a640070140070042d01c8038a080c90a00800000300e52509a410001e0740e048040c00c014580455284404101e030441e40160300180c0010800702ea0307031603000c19000b0103055255184032601c02c1040025252144511400041c0070740304400c01d900b83d01a030140c030540c64008c403080c400d20907414081c1400103198000d14102505280d0002481d05262080e40d001d02c070110b243d10442d002000400014400481c2c0072240310490320000f107418002402443e5204040c6200380c4110481881041800da070101c980700c1d0240c5c01102e8103450211103285004a030f001c203080490340100b02c040401d0461103110304280e049041e2040c0740941050300744003001450301a990315000d03201203a02050b01d078411400c40e00c0016a4081007403200d64504041c1c1d09904002e41c0100410700b28103015035442 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 860599154 1250 860597904 860597917
    0x411061e181903030f090f0302010c020a0e13030207140d140f0a0602190e030c04050402150c0601150c02090c0306030106030c09050613180311070506041214010908040308031902 78
    0x88082c0c00041003096009200100c1d03c1d40709040421360760707050051100c14840c29110207410031643e200c4e050309645541c10f41c1d40240c18000c42510349480c0889503950a000b010324110f0061050010010752580e5800322815100f4000b02041f0094040d41c84039201900e4841c18203176a4003856502013103008007000b00c0b01400d8450318000d40ca402107000100c2c0d8040c0c4100f188001d110400d0404100c40d6804110200c4010b400c9600007880d844500204e00c44d0309580b080b414901d1000500103031000710004100f070480e110324040d40c108050030f02e004ca440d140005e00080d040905000814521500c3c6c20280d40d03c948050000218141c0d42d840308008802203a0003c02060742c0e0302c0a02940e400e00f0380c0c0c8202d0000e20b07503009000c481c40c0303050000803c141c1c6200143c00c01c60606100702210a0034060074000b00f40003810f043d01c85884403000c281000c2201400c8503c0c0c00c41c0d010311003c0b4181070203191005904908154209451a102e80e03c0c80d1b4001031031040e400142c4225619580320a10240a9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 860600404 1250 860599154 860599189
    0xb100207090b06040e040b07020703240b040b0a0e0c1c0903180323190812091c0e190303021e0606062a03120411061e18 53
    0xd05403500710309004540c01503000c0350041004000078401c07441900040e54000e036124034030a07015500d505040f400c1c101c254100411803140d114001d2640761001c0c3c03c1d041e0071001d0100400032120190100320403507041d01079980c3c00011503e8101304c0705020001103980400003003001d40c13074500d03881824107040032034001c403441c880e075598041d005040c0e03c0422b0401e03040c0e041000d82000360858030384400c40a00d00304881601d05210711100400581840700c402c4e0b00303c0b00140d502545603030f840c004110ba0442034180740480c0c3c0d00703400070f00c0c800000204020900304042400c01c0d019000401241c030300710007508268001400703d01e4103410728004c03c000c0000b50b000381c1c0501140034aa1005d00e0004850302448044c45c0e005105102c1c013556100221544110032840c1004100c2c15540c80301200280700b41b142c5001d0001041180301c0c1c0103042c90a9200341e2080c00480742080b000000c210090060341030080203100405140d40045100038001c002050002c15100c0d002402c100002d88450000d088508 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 860601654 1250 860600404 860600413
    0x1514070506040303060501050a0210051f03060203340302180303070c03020301050a061421070909030e041b21020c0a11010908060a11160f050d0201022a010b1002 71
    0x305144d070522540e406801e00f46031051515256800c020340d05c02000c0000700d005507480c0c02244130444070320910307000320824198040c582a500e00700f00c0001e400c2250000e00e81000100740b400d00780031418409048507d05000802000712181d0300702e00940005181210b602c0720900340540d155001c0001c0d14019109155807403031241544149802d60b1405400202c48606115080c00203440000c2804820f04082e290091843d01c09106004408100c01c050304607800380400100b803044041e00481c02c443c1c041c1c1c41e4542d40519403414081112141c06009494107000485640d01e244902040000e5030032900d4050822080c1c181001c089900c034140c001d080754803a038402c20402100000c0742641c00d80900f40281c0b1a8074020b030311522108000e0190069542c2d072424111840b110200391228085a400d400c5030880d02e6203020840d10300355400c00e07a00c9100341c8202c040c170306105000700c0740624503100903562101f41c10b003400c0d21900d040e8114448195264000d1550750b4884491154020055074000d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 860602904 1250 860601654 860601661
    0xf1c141c1e02030903040b2109070614030114010503130b0c070201030608010b010801051302160b1816060c030c05060f19060b070b041e030f02070b03101514070506 72
    0x5a030240204500c050075005004200102ca000310541d021a210781c1110740e0344008681e252000c40f44c072403161f00c514650850500c445068001250310075158591603851180324003110f07a02c0c141c0000d10030440c0114a000c90962654840d1002e1504002c2d05111107114100310b03598410320480840340140114070100e1400300303640e03044c046d080c02400e0b54002009101240c8000801c02401400703aa80208102315841541e0200d5a04652056080207001d5208807842c1ca010b06c1d100d40c05407912106100c001d00c2481b45010003248040f040c40b07008001141483c60494140c50003103000c201074060214080c2c5580100b41c043c01402d114101040450443c0d25020710241c0c82c1420110107802d800e450203d040c00510540001c61341c1c44d9802c101243c0c600c3d03450b03142c00054a59120101000c4241c5844600205500000c41010b14541a000d0b1040707161202c0c60140b03036020883e075040c811401076004010a110140c0b808100003001c0c84d01d00845e14248040c0400da910420084074603900003001c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 860604154 1250 860602904 860602931
    0x2303120a02030a150e040303021b0601230909061503031b21030f01060507020d0221010b1002030f0c0f030a26040b0a050a020c0109080c0f1c141c 64
    0x142d001d078522041c1006000d50400c110181c01800060001f02170541c001208462440d103e2a40c0c202d072540001212002c0da10350703009500b401d40a241d00b209072400740d600e444203450490301141c451014031006041d42e6403254a444400d0601591042d018001003186040311082c0784d1100880c82a41c4005000c0c013880710004d00302d181c1c6211070107903070700e103091040c04152803030f948000341107840e10329083d520740d0194000540c100d01d00ca04000e40c02140400301e44501c0700f041c0545d1201d207100c2c1c0000c1041d031700e58005114100c102e202c003a00c0107800400c03030351417500001c2001d0700b847d10f9060219901d010900700f0352032469100c0c04164000c0348110141c00b501c03917186414580480034107442441076003016a5802c4000102400001407603883c0c00c0025480d546036410f803815100500001d0000308514142944203601201d0109824018a000c40a07250400240306a0100c48200c05140100700c400d001c44001c0389060302c8d201542701c100072a1071a100d02400e4843c2114651100040c440c060103136 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 860605404 1250 860604154 860604161
    0xb030408030f06131a1903081605070506030a0b01090b0901171005040507051306021f0c12020f070b0c030403080f040c05191d090304170c060d0204170303042303120a02030a 76
    0x101443e102c1b80080003800019102001c0e1032140fa44140008010141c62802504010b000c1e0001340d0031040100c02c001c045c00d41a049071101100c00c0e200d01190a465150000d418417413490510302186106420003c082c0107010031a038031422458802c41035030f0322840024240e071400c1c1d0300300c40025030108800c00e04214003c1d20760300074007079030008200001000b0340170300300f4819a61401015550318404585c64500a0f49450162075501c44219640c0d841d19807650308039005200162681a44100020010812002100d004a8042d15040c07055990041c883c2ca5180c0010403c440e0301c03000000014240d11107075101015100d4100c1d4032001c0c1828503500e155650b1041181545402449040c843c0090020041b2800d48010f000220091a9003400c0d19141c10104111240c02c1200061713081e509420030350107070064500d28030481e03039056100ea012950760700050703074040d241600c0442c0c0341008120036103625942c0c0050b0000e6038102094001c00a082c184212040000a50000704210004000c3e10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 860606654 1250 860605404 860605429
    0x30203100b0d030c060e0d0504060e030f07050918010606020d080a0c080403081f0308040303020d21021c0f06060206060a03081902030c0d050408070b030408030f06131a 74
    0x8100300404a1400005400c0103009040502840407210340b0501740403194010403413030503281d000c54080b90040c5800401980c0030380300789000640d015410303500501d8080740100e8004c40050081c69800d0a1008101c48403d000d09840ca1060510040a48645081c000d500003440103030003824441d484244060003400c1c2c010300c8110364034545034030340040940081c18a034200b0380603d01070140307540d0345030751541d814043d054028030101c80c1040041000405c400810542e4445c0d82034400181c034416050784e803180d550814a8609202e00180d25000203560302504281100c0103040c0c184220001c00720040368624a072040040341c8481080c808660100141d9420045c20380d0b142c100e852441d11400060b000d11085a8050303080000003814651081082d201c0302140304082d00e03207081c00403001401c1c5070300911485400c0d0090070701c00120140b81e0300644c2c0c841c0d40c02107062032440d940d480006150180c000c0c01140d204403001c41451500c07003203101d03c1c200305000728162200e0a0448080065000c00ca0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 860607904 1250 860606654 860606683
    0xa021c06051e040b0603010204090e0304080d030e031c15090f0c050406021203092407080a0c090302040c03090c091d0a03050901180b0307050405010e0f090105010c030c02130501030203 81
    0x51201c461031094401000d68401e402103c40c41261700d40744000303030281c81140d1141ca200c2d403c0c20120030815001000a00446541100b2910710f14007840068059683d0154841e1440c3c20902c01c00e000806455280780410384070000008092210340e240032030f4140c60750003481d8965900d002841201c4030a104019140d42542006418240b9202d80256920742c118000d600c281004408110310950030008a8903e1032980d1491825850021030700064440445545d40040c4100380410f030008154420301344200090b42d585100d01d4215024000905010b100c4c50003015075440603000480e100860600c0a09801034000c00d001c40f4000d00e400b80954000c8000340560810506000000c0d0011300326401d00400f800c1903500d41501401c0c1e0558590a64020021520700004118815612400801c05d030f60098840200d00088a03050107012807600801c00d420200842c018022036000f400c610880780d110389402d007050141d03540440e90129580306215140b80c1c580c4018400c502e001d0043c0201130414 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 860609154 1250 860607904 860607931
    0x20403110d050d030207050106030606090c09140d0f031806020f0c06040f120c1205010f0e37060207080904051e1603140915010501090b04090b030a021c0605 69
    0x352682c980b01d40c0203a000c8810f01d640011180100002034018a00a64001c002003109560b40e0044c8000f4103c0c00340c0b00000a0b5250b071000c240400310000c50703a001440506001c7c0d117101c1c0b1b070742d4030241102011016001d0003c0d0322400c00c100034000c215003014003815400380000302041c0012525107541d00c1c05480c45484144010b11944e48801c040d041103e1b14240d41d403400c88400d080004104001e50003a0805d6100400b40105000703054111648a204200b010007901450403000b58403403929600303840494904018040301908800781c40751403003c0a8409986131209583c0340c200300e80c010136049510310408a80310fa920f20340741c4a81a40300c000c00d0701c0070760004003500400b03151003001000030303450b040c4d8461442c12040c030070340c0700742d036403499292044a141c242500155520902c2030380603038900b82c81e50008101d6500c10b00125040701c900004041c02c043c00c2003050005015006511601881b400441c00056070f500b98440036074005408020003010030b80c1c141641030302c000410b880e1507040ea = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 860610404 1250 860609154 860609179
    0x7030605160e040209010e060d0b031014151f090e060a0b0f36090a0e030702040b1c0308090f010c0c0b250e010219031b03020109060f02040311 63
    0x1044111060004403c8800680d529a90401600d6043d071001400750840400306000401100a50000d50707154001c03000c54a550701e11461800540e1624940540c280300d414000c183c16110720440c409258000524413808180d035049480d2100c1526101c20f00000c00b0441e0810441d00b10b038852640061040c0c5010124600b40100701413144640d02e468010110009002c6806401c4840141c004080d14500f055401e01c0c1100e03400d015880d11700410344920500e40c0030450a00c141e204102951303513080080c5003441165000c0000400c00d404805400100c24980e5942c141000680d041c6490b200b0384510035076050546025280c800c80c10700d455641e84c9052203449480d81c00c40c4001c0035103507208401510680d00c08103143c4072270795003c800e03901c00890414020395051b0899078005050000b80c2c01c40701c4095651002400c0164840005400700340c500c0030710712486074910b800d156154040c1c0000304200c3c04a503078003003c940c08c0d60b0155070f50341d502190500401040703506403c0400001c644001d03000c0b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 860611510 1106 860610404 860610407
    0x301060c050d080105012003070209090d08090c131e0c02030a180509040b07271410080a0506180a05040303060b0c0307020910170703060516 62
    0x24030003640580ba209a030110704a9a05079140600d049a00b003048500c45000140038441d0b0008000640150315000b0000707018800c41790007800020080d0700020b02e0407101811420054200c0b06500701182e07544200d070030108002905c0003c840030800011036440b109030110300f00844c1011003c541003038000c00500001c505039210b6240883c05804000301c02c0303202e40105544052044041804a40c81c0e0700700e164498a1810112204c143e107001640c0c100c0102580b08100344075a42007032040748117000c0044851003040d201180c01c00c010843c0a40444002005910015507900c0011000e664080b2199007110f0490710440260400d04904d1010b40b078101c2d0150003080c10440c000400c0040c402c12504401a070801035402d00e0b0b40c0b9400c0158650016000c003010b00c1030780001007280e4011605115607603440c08010a286407661410030155078008201e1200c00790901012900b19 = true := by decide +kernel

theorem cover : BRFrame.Cov 860431654 860611510 := by
  have h0 := BRFrame.cov_init 860431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 860431654 ≤ n) (h2 : n < 860611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
