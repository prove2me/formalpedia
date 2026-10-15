-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5132
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:51:18.85792+00:00
-- url     : https://prove2.me/submissions/1cbe4382-b396-40f5-8d7d-156677bf1526

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 922841726 ≤ n < 923021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 922842976 1250 922841726 922841729
    0x6030a02041d0103060b0405070905211c0f1107050108060d060c05031803070221030f04080105010906060201050f0109050919060203090d0207030c23210106140604030809030304 78
    0x10400d000c4800000a40b10928080900c0107031015440e11140820704d09045c010b07144525400c0d43c4144c0c5079400c040030401800741a4a0030000d012400110804200d42000307102c0045555290380d0f500e070301d9840001400001d482c4100fa0410020182c0801c05000c00030b9104195002400d00504aa4440002c00c01c40c0011075000b505d48c0d410b01c0e15041003550094025030041140d590006410364240b402c0300e07503074031035150002c0d0050308215845091089040f0325010601125060700c0c078011110581c00700ca50469004001d2913552800100b150500c0781c442c89000704240c0c0000d200602d4410025038218505100e001c48682c1c980d800a4a08041440195a0f40d44403003c50350388042c05040110003508112442d108601c01c20f40804140c0b0300000b081070499074407400400c0c02c18148040c206001103000c5001842083d0116000303201d540b0070504510000c0d000a904420341d420300300017400d440580d8080f609203404086030003019101c2100b160300360398208620aa54501c181c000c07a1941c8500e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 922844226 1250 922842976 922842989
    0x13241d0a0219080f2202100c05060f07120c021f0b040e0102070c0e010b040612090b070206040b0c03060d0204150504022b0b01050d05070905101205180a0206030a0204 73
    0x41c4900004002c1e08883e9040c000c0d60841d00d490241d0b510703041015044810700d60b036581c8044003182c80c03000524110002c500d5040452401c2d00d0040e54558a1503d4440240c440401050314241000401903102580c05516844d85005001400d10208040e441700c19000c0034405004003ca030210365400c0a4110b441015030140c41000051140601d06000790041042112100c601841c001008550145040d05840107909060f142610701081541c940c4802d081c060291a1915102408203044080b030030302c246803e1f000381c000d03458030303190541c28000000c1900401e606d00f4000e0000549544c41c40f40170700381d8162000280d0520110050f40c12005540c0004d900900002e100d0084c01400c2e0300720340796210601e0440300440f29059004060320364002c0c0a5002a80070710a250703110803541c00c0f143e0051441d0a064074010b8038ac2000c140511418500700c0e010543c0482d200205c5007070391290a87c0036842c0030304002c0e4400040781450705c94041c103501078031501000c40031910040503541200e006201 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 922845476 1250 922844226 922844257
    0x30a090c051005040603050a0213180609150303020c0414060607150e0a1b030809091f030303050603160f060507050f0d0c030e03010510150e13241d0a02 67
    0x2c0620006005030300c540a0140024140404610501024000e5031500c0d00e0fa11800c40a45050003240c54070707501300010340da840c6a1200740c0054428290710941c501403280300c40c1521103a045040291400b82065011805145020030b00c0c545240012600c90308410111780c222b41e02c0e078403130510003100101541c1c0c40c1c600c5450031b004443c0e41c0800181c18480b0034402e01c07104c1c0801e03e41c4054032810036014440075003105020000c1e884a841e0a081300395111101081081c00c010030720710f9010300800030b900100e010030340d14001c0c8889851308001c00304003101544080c541c1c540c100036a0800620241c407542c000d00c031000c030310304003049020720041030002040320403160114403111008040c18910b42c4190080f83c0707980d4061002f42818010188503000c012441980c441c6441c681d0350459501d400d80c03104102d01003910101c15a81c00200e0744040020400204203850284040c400710101d100c210410f21076446420400744103030032503d40440c1040307030610b82596100100e00e000f902c01e1010340d10b02030781c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 922846726 1250 922845476 922845499
    0x9161b050f01151a030609040c090203040b100504020f07150b030d09090515030c13020d0903090801050109050105180601090f08030703090509012d0e040503040602061b030a090c05 79
    0x100552281c1c243c9100c0e0300e04070085558400503071560142c01c0410404002c41003000680030b04028605c40e800034416090340c8011681c0e0035941c0300f02d8100fa501190003204010601568401052280d0064502191700f1442d10115000503500c40c031401c00003c000784401074080500c82841d62040c00101401f506481d55a450f03068020035a0b406401031410052508010a0781c8901150f1611920080a0010122200c00e00c1c2000450942000002201c030b400304400702403141d01e030203081241440b82e102c10060a04004607942969016008070098500e4100104000d9031703400d001150799409141d4a0700d4075122080103da030480e0a8000100390300310b0b6540014180d4002008000c02800395807581c54240d03c0d1420010600028854211000c040804a01d1079603089910011841d482c603102008040e030340c0300e0340302000c00200e83c1a506604042010040181c052124a40c891070601006403607114200c1d00c0d001501000c0c1100080541c1d442290040260141540340601001400500842c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 922847976 1250 922846726 922846753
    0xb1617041212030603020906240a090311060703171e1e070207050102071a120702010c0f020a0c03061a0405101511030304030503130c1e0509161b05 65
    0xc002a200850711008800c82403242c4512920901069980c01812445039440c0c0c2001c004500c0c000d03000104803100864181094176007010000c04c40985242ca80d8003081c3d140d400c1140707906485a546074001d034410400e03840065408104004500b03014025098240c8641c80242558420041203950b69980728007446021790035101410f14082e80220704581c55952510120307124503e601c03c1c103001d42e10100c01802100b829921055410031064105424a4440304215518960030384d103070301c00f50750341c0d51065030174551203058004442c2190008100100300c90390b8110516180c1c0c80040c0181c2c0e80e881c1004403d070005900e21480c3d8400030402c0c000c03810141c4641860391401e1040300401511034003810780160240e041048045107140107541075035201c0d1411307512070780014034100c1c140722000000000943c030702d00d1030320282844440c80c0003c02c400f148510030810094101d5407290300360008200340c2000d8036400341c060b0780003407a000c0700c20b070341750034252000c40d0502c5802005801580143e6601 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 922849226 1250 922847976 922847999
    0x203071b050309040b06070b0a0509030702180a060602030a050a030f02210906100602031b0a0c06020a05070f05030d0f02031c1415010504031b150e190b161704 70
    0x40d803100311810085031174240100161842006402014a05002c0003c3c07032040303180c0e000c036902c4500c01e4140c920782001c981c0007e11794980300100c0c0e401c580440051003c3c0e10350311b204050103000c0e04c1c0011494012500d00180c000e00500103030f0020541c554540d61004441c1e030701681e01c04401c900b034440500000c0500005900001c54201005208400024114104d005004021526550091490b050005c0d1003030314100d0189450304003912a014400002885500c40d810003450700c0e5000e00b040005d0761900c0f900704040c603840100081c0b170700c01003400aaa800b04103407815a070300c0d040c0042803201814059046004045015201001f4110505004074440d04480c25a02448803401d0050351082c81d00c07007070955884441b83c0041c606000c2400026484d04e01483c041242011040520341d03030714003c00d249804501c91000150004400101c0d81c100342c0034503105412500000142c05042c0822030100f4002c0c5015078013a428510003002c140803e1005607100c1d5030708827080c0b40d90750740c980700032580 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 922850476 1250 922849226 922849237
    0x30f0118060e07020c0f19090b0402070f03021513111003110d09020315010605040b0307020309060d23071d190f1d04080703050a03020c0a03032003040b0a0203071b0503 74
    0x10307031800080300c811481e1281844a0031310301d421f4510861411f00501c4002001007511203500301d6400c1041d100851480403c2c42e203058402c1d0b0092082c5101d20b0b0384d03207000c1a00908070700e030800500011103000a041c42c81000460405480403c1e0048014000300c001c0c0000d01ca40d00c00d00240018946520180d40e00900350460080c4c0803940c010442c2c40c07507602c507010248580d5000400a000a220344030301d1000454104040784101c0b0704010324072000600f540c1c0216000e03407032282e82d401c1380a806020695200c407082c1c40000340a017036180084001d000801540c01d1024000b0706038614032915502c89075034122102103c64048c034443c0d03c0d011188616004e50003010101d86d1300d02201c80c03455202001242c4184c0d404402c0310706210541e5026500c81d089038090009054003440300e8840c207041000740b040581e001c4c0d40c01081b80c1c50b9501c06010703000312861150080240403c00c01001c129000d0300383d0707040f02c0e1802c0c0041e40ea0303451500445052445d1421543c504d8501c55200e014810004040c05 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 922851726 1250 922850476 922850479
    0x80a0e0f0d080c01110c1207080705010c031a091e0a06030b090615030d1202070f02120106060801141e0102150a021e180108041502070c030b060402030f0118060e07020c 74
    0xc251a54100c1c420700f540280c540502d4154010700456554408035002303405094440c4c0c071010f00f407003200c0c0d0750282525041c4a00c00c0000c0ea5545221201540310740461607541001c1d80c92030f8107030800c07104a44030b08130214060002c034524030b40890303030034009030344980021900032040c503e4500f03244075081e80320401516461441500e0a59000e001d00d000328140024032110b480304548600424480d40194200c1802580c0e448007042044015840d0003446d0311509022200001e046418040c0142c080a81a0809100842101c040c0300854988040030710003480d001030050700b1805ca40c00103c0c070b03014005150307005203c1c1420a10480030a170350040c1201d01d0391004d00038182d0368000302900c0d090049000a203010201c607580d202c60380d40070b80c4940703800901900c0c0b005105080c1c11501400d80c1d000c0310007141d419031011030402c2441401c607001130704840102c406515605201e120084107a00c1030165403400b020b907402010b00d48580b80d03c92401050045200c007102e20b442000a500c8140d00d06019 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 922852976 1250 922851726 922851731
    0x18190e1602060f04060e1603050109020306091f0b030724080603030901051c0f0e2415060d180c05030607210905010204090e01022203080a0e0f0d080c01 67
    0x6500c0340042042e51040c52103a8a24001d0760321600d5440151038008020840360007004441444624092201d8020310300440021420341c0c0c2c588107042c580280105413048a030007454541700c006c0089240d070204516114001300b211410100040e08281d4a54804c2c4070110044402103100024401540c8441c150340d101e6000c20740d80c10060580303074455100004e0019504105540084600c080600b269040070b41e400549800c0050b48581191400c04071203d4a5010440c40842601c1d01c140341184440003c98400881c2030540c0f00c00c042403240100300e840399801144404862007150b1110700840116036603448100601e09001381d801c0c00c6401518024014500018000e600a82c4000000840c2c4404030a200a80040c1d150042010001c1140c0ad0f540070400010b03042c0072801a50381c444240070005a40720080c00203d03694900c03010035202a2112483c1c1000415100801e039089030250742419846440d90100099000015404142c3e010320800b14010030b0018040160000c00c5050008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 922854226 1250 922852976 922853011
    0x1615031e0e030949060e0c0907050c070501020f07090b01020a0b010e07080a05070206061210050c03060103200a030504170a0c0201030e070f0b09060c030408010b0310060b18190e 78
    0x85060f1424000c070b68190700400c50804c60018030030341d00c511024a00102520201c40d60308000078400c060540e10784000480124150090010074000310009042c01d0004000b44040b4039031440d19618144150b40803d680c030100342343c15900030311800100551040c86088950b0710b0350910101c0b01000e5846c00b0004001500240c81c040c400d1142c14000c40c1c05400a15542d40c3c3c0104000fa80320030425000d05c0350003400103000301000c8900810b8001c9030f55a4100ba01e034982040014102c03050784581c0303940201d01400000c100811441101e00c1181c0504c0c01141903035541c01e182c0d56032884061121303070028000424a04142c0e010f80f543c400039100340d90034001d03483e07141c884d26a1003296010701c0407809000e0740200035545401008202100c000303030030241820148989141036130495400701348203945601510100d071030288007841c0181c0d2550790421001b420001d400c00c0a0041c00855201c808107074104200c1035a404031b071001a20703204141c44e074200d40c4842044d072007003009946204610320a0030740c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 922855476 1250 922854226 922854319
    0x3040815040807230307060b040c080106050403060b040b1507030e060306100302160f0b0106020d05191803150605040f1a211615031e0e0309 62
    0x8038011500014254103003a0f880d282c030155803d51001c0710a10b4500c0c0407000070607060502c0a041a580a1080012401025018081071781c81c50130307035002004090001400314940020943d0166904400d0010f8000100c030007003001024074500c041d0f48010100c5100031801c4043d8002c0809901c00d0f0348401524044601340071445c081034a13000e502c800028801050b00e4400c1d4082c060503100e0614091410b00581c5541000910300d842c2503415002d0400148801c0e41c0400031000b0404662404500c0c1c0521a503000c103840202486060800c02c0c01c1e8408800c50401c9a01c480155070050041c025a03805940d5013401400a48540b41c090f5003010207000e04075001d071280c50000c06803d83c0e42001e00c682c0c202002091007040000546203160300a01c02d0181d801007101000740301008a8501c10642046a50541b500d48501103504050070120800e4a2081e00060782922108c1c000c800310311101840744480c150b00801c1c042a81010040040d2800c031800040c10042403089a00064a500350044 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 922856726 1250 922855476 922855513
    0x91614070f030215070e060c0c04090f0308070f0c030f021c051e0705070504090f1a0601030b1c080a021216030905101b020607140a02040510030308010e0703021b030408 74
    0x50304171012480c5842500d00710b08001000308150503c40b4292801c00740b0100004085500004042d01c8070100071003028200364000002a8104002d420032401c01603003881c0080040129120007001c00c41050645810301d4006c0141c1d2000c81900c0c5035101010480c05402000344d002101c8400352100c046191083d548081011a030106401c0b001510b00503041400703002c0a8611030744201c940d54010104400030a050131205000101a0980110f030303030621380d0006040e00c5010004174403c412412001038801b20901c4c43c1d4203100d500c5441035403112078401086c0d04010701702c0300c000e0300b030ae100141d2080920780d612415441d0318403940b10755100c103480701d041c019022221fa10641c0445d4158142c00f1071241c48500d03001c186480100a2482e069041e43e4201000e003c042e2155000d61080c1201c80441c54640220303540110300d0100f840e007951958a00615151046c4503090b4983c10b000c012441e07540c441e40485802c0000c0740540705106070780e4070030166294080d100726403d5028403503021605400c3c02 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 922857976 1250 922856726 922856731
    0x110429060c0a0b0601110d0809070e0606090d051204060917150a050c1b061911070222150806151522060513080c091614070f030215 58
    0x108010040d456040d81e07243c50300d05000e02400d040c001d000811266061040019920440660361080c1060030b118000900d0300040d44c020500007004042000700607240e2001b0349509800c200d41c140803580c41810514102180c100c11403000340000203004c41d007107800c0340c24a8100c41c1104cc5401d9502409120320b900d0310350781c41e81020340780800f602040c040040d0342c00894001c216801520f11f0420f0504100c9010100300c54464400e8100300208402083d840d015400440840034007408010088030003c501c81c494a44001d104c4c0c41402a801850a802c40c0070f02d0303000c0b20b0400f0070401a000c60360320308200c0009220300d070311a2040000203034103035880600201032000301405000b001e150300c03a10311003d80c006042c2d00c03040300007407810604c0345400c0503a01c800504840d16101d07950520042a8102e00c2216008842c50b94059040c5500c02c0e103c54991960151a10358840d204080c820403c460741c95225481c20004a1b002c41c0d0a018045c030701c41c4241040d846a000c030342254100f480c02413184c1604 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 922859226 1250 922857976 922857997
    0xf0906030303131106040e0106030510060f210903050702130c1b0201030e01110307021b0f010309081b0c1201050603100213050613060e1c060911042906 67
    0x900100e5031405480300c001500030b10070701c200c0132443c10140214a030b03500207501180c003c102c0d10004010450305442003d42010030800401c3d0311300d04240001e0510803150460008006000841c0c00e1242d41d0a850007034140f10301c10087c409441c0604000f44260000c4009910900c00f204402102d403410740b141e85850803281d114184180c00c000000340745005c2c411016418961103240e244c49641c0d0030b220300d480131080780640b682c503810500d030002d141981c1515051011401d408820340c5c0c0780d880041c0003050f50303c00d00e00414680d800c0e240c055401d000d03a20450701480000d100c004140803011400365581c14040d20a0349007900100c420500345d507001d075441600b640009001034241c0c0d0303082c0c000340380054110591446059840300070491070360020340440c07000380741d407001800050361004d80001080e03012100440c058120b1751000311180c1c0010402420165146070f000200048800c02c2010070b80001c2040101c9800c40c050781c1040319204400d289c055110404d089287d180002c10b443c841d154 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 922860476 1250 922859226 922859233
    0x30910090206091305070905060414040e0f0d050a0323180c1509040c02010c201903030207050d02072d03170415020703110f010e061303020f090603 65
    0x10402508000380800d040aa030400002c01c640c50440d10780c82d0100c402d01070030181c00180c2d40b810920080c243e00c11500258032440c4c041004000da9031418008007160b4408031000100000300d003c02a103041d00d10718003e07841d802414270101615800a01900030003000380c5040c07203424240015100c10901086020203510a9240400c00103080381e041600311200f0581150380002c41e0f04000b968026000083c0051090001841d61160402e03003d55102c0e00020700003071040f025044009000c1d0200c0b0100e000c0c0d000c04001e0400310202042041000c01d0082e000c2060500f5190704000b0081d5100170b805491030311070030170125201c82c80040e040e421140c80710011501d0b000e00900e21120301071540c0c42c1c600040f80c40c0d51701201050801d01c4410300705072001c520a9840c0d15004218035a0100f458102c4107641050b4410030200f240700d04803485120f8211150001d1144010043e01c0e07107414001d260707412401c040341003280c3c03a42e1240302c0020369008a502840000c07031001041005101190310640580 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 922861726 1250 922860476 922860493
    0x30a0909020a09090b0103060806010801020705010e06060916030f020a0906031a0a0b0903030c01020c010b120c06030f04081204241a0d020d06110406201f06170106050301110309 78
    0x40c856417100840200500d00419181e0b61520b61902c1c102d802e80001d040c1c2d944c0043d058042003804d100348503110310f480000c0c081c03d203045c00005500d01d100801c40c00e04010801d04980540b40300e40d1024069000c004030840d16580c1c1d0a800a101020b5401400c01003840e000704803a034100c00c0d000722070703610100600c040d001c1c0341041585a903903005620110f80612091107803015150f02070019107141c0d51010b0001034141510005c10803042084140403880da0440204c1030050b46600303080746c1c3e1060445090b0381d8070b80c96920b0f10150300d10480c04514031401c0c00c60244402c20003140703013504108883c1c003001000300355000c0c000000c4804101c0e0509250505020b140140c0c180843c0303101039a0300060052081003002d45440e01510030001d82409100380000d014403000c3d0308810b4400d0800744a8002d07200019100e400ca0769142c4030b0600c0d40c03403c84501c0c00a0070910301160001000303069a084010f0122058440d914040e04050081610030750800c804410b02e115003806407845501c0a20041c500c0d013 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 922862976 1250 922861726 922861739
    0x705040b03010917031b0313060b011b0506010f0f050913020307031e061103090307260c01020d0b04091203093306050609060703080c090405010305030a0909020a09 72
    0x10114044416055500c07825010f000c01c00e150962080c10081c10b81190f52460089902d2040004241c0c901050200602c1031224515441005922403035001b100081c6225540005036401101940b10390b9042d000056400200200410418100c03a4002e03e040c0d5030b19103900340b00382924258003406411005010000342c64022070010049401d0028050721810f607100d4980c0103180c0e200c1c00301d014015001032009401c200103407041001c007001d40c010309811410100c07500ea4480c4a00c1802800680980140c00c0d0784291101324021740e00050800c080d950542c010884d8043e40000300490383c0f2500d00f003080100d1341058005c07511480d501c9401100f031071200b1901540200003400c0103485031400c8010300e1036006481801c607200c88482c0c2d201425200c0c100b54400b41030300c00e07a0300043c1c0240d0040c081c81415486500555500035414103060035550760b00b0301c4c01c14181c01140c245960103410400008284180400107107a80b80700b90740d60b07641c81c5440c1d400a00c00ea01c02c10307612a0001d0f40840c000c000a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 922864226 1250 922862976 922862981
    0x4030f02100f0f200609030414030c0a030b0a0e061e0610211104121e0b060d03111e191a130204060825030203120c0f0607090e18070504 60
    0xc4203804101c0c1c00b03114084844d02464401d08580c0d42200c2c0d0f00025041c0500318407010200c1100104070000d081314144480401c2c0358040c2d03441300404941c0c021000c110441026002401140940003c442c40d82c50180c0c170b60b44540d08240b19011403c10a40041034007400c064014480c0c2e8402c2e82c0b01d0300d4405407940740c0b00260340c810000304a0207035a64103201c03107000340100c000d100910355030849002c0c42506040000c07460020b003407505281c50714110384400103415030550aa100350215130341c40c500002e0b070400756074880c0044e40140c401d00400d520400481e0190030f40717402161003401201c842c140c0d01241c0080c1c24080400c06005000120f030403010310010403900940c00701c1010a44580a045940410113884898110203200d80000603542880e061113040002c0624034094170024441c5550046030704d507001954400c1000d400080c40040c01d0074208034401c1060802c10440f11302d490701c250006e0450080307000300000c111801000c10140c2c01040c81c04404031070b140010b8900030b450708041000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 922865476 1250 922864226 922864247
    0x20c0c060304020a030c12030f0e2805090a060e06010906020606301c02071d06010917011a0402030c030a09110a0303031b031b1b02040204030f02100f0f 67
    0x9122048500105c00911986001c40040c1080083c1100d0b07291503103409041e04020000070b02c10400d101682e41c500da502d541c0c0300500c1c81c81803040019402003a4008404440d02c0350400c2d03802c0400d0400b80031100886a00440482d0404280155183c0340c0400448010001c2e1103007200591003d40450b1051504280d110305402a81028040020140c0596145844071004600c402d4004802d94640740301007414030003d29039984050060780d400c003134230039032454000c000458401c7d41d200300142c0c40e80d00039201c1e6030150403000c11000c00b00303410050705400781c1011800000b140400c2000d06005080600030341e40540c40c00c1c41d0881c02c69544400c60001800792a209444020440c1e90610090300c450301c06001550107650081000340030040c54118800c00200c02c13008140c07920111090250589520701d040800e03610340508031195240c50075100c0035121401071340c028800500041045801c0041d0511b0a100b528480c8051184a0003034901269040700400030585480042e07003010300c01c0d03c4500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 922866726 1250 922865476 922865479
    0x6050a0e250f0909050106020703030c050f010e1b0a03020a050609010212220806010f030b1f060302090310052406070b10050120030901050a051209061504020c0c06030402 75
    0x10744849a1201d80c80c40c075601c9440000110305030761904012994492058005400441e4040c030281d40b400e00b0003540d5030001d110280401115002013002c000040c0800d40100d5000300090012086200300307152501c060300d2001005592981350107000d42044560b2004803034004110301040c5150105100d1f40740d200340c4c405411401110001541510b100e80500901d548216030880000312607840341c0e054900c550066003c0758000c00040144190500300481520f41c00741c0e03403030610b032100b81c6c03682241406d40340000004080504042600e560550181682440031003c0355815036030044040d003251003d954840c0da80c2c80658000c0076041300380001c200c81c040064440c80c0f6142050f100c28101c1001541c0c500910300300c142c400c100e10760b0302c9141d00000020a10707440c10000021050301d6030f00d00c601c11116040c05000701e51401e01c43d02030400d54010440108007001c59240178022151504d500321810712403800c402c3d02c0e42c0034500341807007558031009982c002054400445810840e02e80c10062089 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 922867976 1250 922866726 922866751
    0xf07061e0c030e04110306030d360e010b0304030311070521070c03060510050324070c021807022e0908091306080606010f020c010c0c23031006050a0e 66
    0xb82d006448501c200c0c0a038980001105c1c0d06c0303080c06810142441c41d084daa400401c2660891107441886190000c3d1608800410006c100001c850031642094410343c021142c403d440c00002800074054001188240d10a035000c02420541c404c0c01d408034000e201c800b03445640002d51036000c1c0020507101200c5203d90b10100e0b0300b404d266940d6009403030304903082200e400f07458105100543c200c61302c0000150004030050401428104071540c1144440840d00e00c03e440701c040030850340d84c01100007544c0290003501140042407410040708400d1016910f682c018403500201d9900d1460b0a043c00055a214401903145e02c030ba0170a4401c00340050000a90710300c9400c000300ca090343c3d20040110004041800045080d82c54074071520b0405500901c81c6040c003105c10750f100c524a5001c5084140c03510309081940f009119070505202d80102d6030041c170600800900307540e908146d070801d0300210500860403102e070f5001021990b819202540700d241e801c01c800c1041400130825030307001e01341d118a509521 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 922869226 1250 922867976 922867997
    0x4050303070804030c060306030822090e011406010915030e070503010204150e010504030b0a09061e0e0606030a0b0105090702100f1a04051006050c0102070b01080f07061e0c03 77
    0x2a085a0200c041192003010001d4200201321402d4070060090642d42410880035140d80c6440e0210300c21a41000c0340590111507140d4120f40200c550006403880e588100038018500350700500038550407400d4a81d83d0022030000f00300c0e43c880d0031040c3c00ea40350f1002c0090702c0043c6100a070f010b0700410403a2070b214012805d0200e0706032800d101030300c01403000d010141400da0301d5000c06005092203d5000703040000402007840856001d480f0550010031140c000101c0c0543c90501e2001015107015101443d440c0c06225405908550094a004d0290300251409078840740c0030995602c02c00300c0c3c02000300014100402080c606900c540c0c0c0d0083c024019115002e0f2548100021510409401c0b245250b94405441d1905021200702924150a440030001800d12080d048080c40b504e11600d4104000003070301007500d44080d010b40302c403ea801031b1020300658541c04000d840d030040d80c1c11401e06200704080060b48134400c54260040c214000032607045060040001c5481e5441c2441c00c2d400c0c00340e01d019 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 922870476 1250 922869226 922869229
    0x10e0d0c03120c0b100303170a022116020118170c071827061d06100927020d02011403070309020f0411094c0807051903020405 56
    0x80400300b00807030f0b642d00c1040c0301c2c2514056003084006001c1c0c0d18400e107081d00c1440020f800c034541c0002c0741548000e00c10315603503104501d00030303101b02d11904200c8443c04243d69040201c40d207001d4091804096120b40d21400300508a088440700480b0725980303000c4c10035000226000341003c2070b0184110f4205490182c00e0082d0354a409515800511940d02401881d40010b059215006002c01100c80b54070402040100c43e503081c000560028100315a90340100e030520301604000e0070810309a1007900c1c000d281001061162001c03910500c038a0900b041c250300b22040400c4004800311241c5210b15039020f00b180c0a100030090500402c905011005c0b4412005040c01c10207140310f000d03603070713404211183c8510510003050001d620290180d03080550f0240c00c0c1c1140c038152414080d00b555014441614901401c049100048144110700841e69041c2903d0301814440d0b10840700880394228000442d150440b036000b000c950210010300300384034106a11248140313030744445940340390240c24142c8480 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 922871726 1250 922870476 922870493
    0x33c0f080c06040204050606032a220f0501180b030601051303061b0816080603010b0406060203030114060304021005090307081905010e0d0e0d03020a06110706050f06010e0d0c03 78
    0x2544420958400e400f00801c52400f80143d5078071038810360700c160440c100080e0b079003481029004c100c10604590020945180c0c5c40f0800c0d9080d02400040c0e80f515905d85c08464581400300e40103203c100000c400c07001c1101e501540c00c0d41c2c3d4000c50204480c05681c544020300c0340a410141c1300354104101008061018284e1800601c0611f0044000003030f091501e00b445110b6020380001d20003804480801c1019015041034010b22840103418031000b01da9410002a0040080c40340301c90307005160030741c0070031015400005113058440c4812080114a07002c001c00a01c2d0008686c001d621100841c400ea45042c03007040a010240005000c4400c0562a101c546041c50540e8070001c0f15000d0661110003401024064400f455000303201406040e0f000084c000c10172140c02c800103000e80b11440001c4105031080100e0584036030006030812108100300015900b9a004000641e041420031010403140c0c46402a2039000f018142c40e0601565400801d10541c410104d6054031110340c0d15100002081032030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 922872976 1250 922871726 922871737
    0x30204030b01030605090f060c040510111b0123032d041212021602011419090303030b040e2802031f060816180609020a0306033c0f08 59
    0x20000030541d4034003251410310b00804203082c24010342c0308c04e0500c040001c030b0700e08440a1328000c1c1d40c2224401d040460a640d5035201400d02e05081c81810400400c941929060f421408001d1341c0d50042c1b03c0764040c040b182c0f0041601c403004403200030030102d000e45074403901c0c91901c004491070340c1c0101e4602a42c0d141618104803000c0e40c40150341c1c198008919400162075600134840c02c01181480d03a00b9004d40c1194000442c02414445001c0080b80d082460206071139000c0000c030841401900322480040a12034030748000c0340420b007044680c10062601e801020383d44600c0301c00810714010f1a0900308850103241c42d411314840c0181000d50090f03101886003110644028191143c0c8503594030790441180c0c4c0b194011452608401c4551960200703130002001240c108090010038510350080842c02410035a000c01a41c1d8030000c1c1d00103182d030700b44d0020700c1200e00031900741110101078544009200000e1496201c00102c03202c0041680c00d5580115a20318095034001c41c180516599900007079021 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 922874226 1250 922872976 922872983
    0x705070b250c090506060408100f1b0f020706090e07030507140a0507110306010303020613060204050a1e0e09031c09080a1e020705091512060112060f02130e07030204030b0103 77
    0x2d0b490309020301c0700d0900805402c4031007a0381103850b05250482c0180c44505c142c01042d04075894001981c4030341450380000ca4056403004604100c0b41c0b281201070895104070840e54050b005828000034907500800e2024111340d10058080c604c1e40e20800f080300203110080403117090000a501c2c4480040703000010301041c001c00c0d00c420fa5150058204006040440c403d418800d0344000300500c00130b58085035203074110007803059100c110705151800034040d00a54100a030450040400000c103100001060900d5a00701801c403804540c0f10021186c801c0360444034131a056104201e03030f828442881d2951103855011020001d140c4425641d4041564001c01e5460005445240d81c003c0c09000d201400407245103500007844094a00f07000710341b541000411120780164070240c0340326180c1b603190500725801c013400159050f80d0384945e10b410701c460360080e003520800e25109640110002c0ba20071a4180200320544240041c540402e5446281e4002e2001e01016000d01c40080041c440e00e017198040c510 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 922875476 1250 922874226 922874243
    0x200a090204082d0a03080a02090d03030b04181e020a030602041511030306180405340f050f042f0d0b040515060d02040b0f07060b03030705070b25 64
    0x4490101c011502d40f003914070306007500c5402e8202c0040c0c1c00018a003044070b0741401d04c400280d5480c600c000081c040e2040300e9406c40031548840040550590084488040484041155001006a54040d1004620014920200004034841181c413400904414610003031150b04030980300c7c0c1c2c40c58241d03000782c0e1001d208040038050031000c2580124200c9034080c40c03c0b0003181549084400580318000c5413100100120700d1102140600100780035512500c4440b9403100c60004000c1e507000042250311040d00a402c01e01040458011074010556080ba80c000741001d00301d40f258010000208140b082d4050f265914640311180d4010f142c030b58004483c542005103407580028040c040035507100154940c403a170300d4042000311010840c40ba030300018105440c280d81b15540300840350000c0c401e6400080070945c010038502c00121480004003581351140d681407040124110070f240d81c038018400d000701580c01544c1c0c24018901400d0107440ba0302d0b200100c81944d42103450070840e00c46010b4905813082007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 922876726 1250 922875476 922875493
    0x20408060610050c12090604090203090d1404080616050702090408071a06031c110a0c0906050301020f0307050904060e1602010606080603150402060f03100e13200a09020408 76
    0x50201c030002c0c0007080604090b03240c040746040b2240c075000c09850f110b45042c070101385d03c1d039191144000d590107040364060456680c2000c40d80f05583d0003903031003c080026022980110700d002c100082d18111000e000081c0580c0d120403903011054039184920b982045814083d00340981c1c0c0c2c940525006d140500741465456189083c640300901b072115410519040001c180f00340c0d03840008840d0070844284602211141d607a00088944051205512089104050341441448a9030300320604646440100304180d907070380d50502d0700381e000b03800c001880b070003040c0002401300f8042c40043c400c0711401000080d102e6110355503052a144240c0780e000080c040d01c1c40c080720440d024480d00300540030600b0046901e1620720300095461004030140200e081c80d41c00858115140c1d041a90f007105021401d81c0c0d183d14060001f200302d440a44039240d90245400c0104000da1001b242d4008095005030321382c44180311070003035142149980c1200b20317045007680c0300000d120342d0140301400180c420038020701000d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 922877976 1250 922876726 922876729
    0xf1603050307020f0d090b0304020307090e03090102151b0f0f0301091a010309020a0b0f0c030a0e0a060f090e060d0209091006320a0321080a02160320010204080606 72
    0x34140e180d20105910040c01061744981114a20b130449001442da1a901d03a240e1010134208116a403144444504186011040510101c00741c81354007820303400c850c1c4030075070742c040b061a00b041610a0b040003805814440140303080340b0002e03d0311484040420385002546141780c0400e03071090f482002515502c04c4800104850400705498080d42440c00b4051343d4540d070000f41540e84144030f0036510900000b881c000c0800c480058452070000c1100b542d0315108090300c0034008440030040d01c1e1144610745000320b40b5500400034100010700079542c172051181009250640c129010b4102a0320000c0003000b040107a0b01d4005440c03040e040840075010f0640060018825542035800005604c1110801c4208814000c82010a006005080141c0b40034440020850000700c1b40c101400c4603c0c0040244207545150380e03c91ba03941c8059688580e99900d25050100301c0c040e01c020400800003c0c02403070080fa103e041c130440015144890300c0c8203010300700505800c90780035600c40c2c01c45800141c10881035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 922879226 1250 922877976 922877983
    0x3070302060f18280c08030a0906090b0a18050306040609020a090b090c031008031207080a110d090501020d06080f0c0d051915090317091b060f160305030702 69
    0x510840b4268110f80f0a21540c03d8403215080003201c140101081070040d240d05501c840e83c0c10b2074101c2d44100d0140e0b00c1c2d074000764803a48001264008258409000101c8030700c1400400f01301c5510504a508100c01044110b41346821454031074803e200382c081c0810566000d10446001c3c80c410040050f1403200c4e031043c805004407690000148a29210100040e0f4036000c46080d4080d24a9000a0303584e916140c000f0301c2d14042e40c0040315203200c0071600d008940301c5401403078003400d01d80d110080c082e1b4540000f141607510000e0050100c035402d000880d02c06e505a00040c0a0b01e10500c009401c09001c0c01d495021a25070758000300840d40b282180b4544d0b207034140820140000c05860164891000c0d4840d07503a1484c00fa5051008140014664824000703184441207079444216002e0100748001d080007440600c0040300d00400c0039014020031085840002c5882070042e10f61103801000300c0070b4040052035040300d2400956040c08010113130b01d610035040900446071103130301d07010303100e0911240c020719 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 922880476 1250 922879226 922879231
    0x180c0305090706081e04081206090606092709250b0405060d0e0d08060405130b152404060f080405030318101d0d020102070c05010807020f03070302060f 67
    0x505140006004903070740e000c608882560200d003000c18443d20f0f40001481745014902c0030800c216400380c2030100f0030803070500520000d081d4072103036512a1184410015074041c01d585059200e2404c2000700018108440e61001904080169000ca15940003001103980001c40300e01010f50001c60710240ca10740c50b00c80b4021007070484a184403640b81880f00d50242c5108900829101e01e80200b6250340d511a690400c0051800343e1050700c1415842c1030002d09801c4c8140c4e0507600c030b681410001082d802c151000401925080090b212582d125240070360941c100102e803590b04100c645e80c846012102481904a0140050000540d190314100d0014400403010940f501080340c40b20600c40850800000c3d25003114515118901c903018188209103071084032403030400c0c0542082004043e104000c03028140d200001802d60b03807407160b2040704030300b02e204642005108043c49034051146502c03e46030103900c40e4150040322001582d5000741895904442c5046006074820403c000c04901c04641e25034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 922881726 1250 922880476 922880501
    0x4060f143c03010b03010603020f04090207060f060e0403020a02280803031b030106050f2505060a0609090302100b0a0f03050102191704031409040c03090209060a0608010b030604110418 81
    0x30b0455050056821082c8818410401056004281400c60340d42c4081142e008000c00441195959481c2c906103000d01107054403620b6587c41c129000030882c8019001c24410381c2d0650103003005114903400c229841c1c04581204104405810a000e41d1003084070803180a4000d036001192a8940020040c2e142506440c003003503103c00c14001003111a81207c02c0d64411015106200e440c1d040075401000c401c1d4103e29903c00003081055084140304c008100c250150400c0e1711300f4030440d515502e1110640781a03040050040c0d204000c00c402e200f180394002c114001d00280306500d26035440311640e0301d0340314a41050782c00703035070010f42107282e218801b03214840046c041c24849029410f04c1605290344100070710290030f10298116000d040166a41140e480b8100104100610320f40d40d84c0040052800d03142c01ca0055031544082429483c0202901049400030303034400d2020f0b801c0103c00300307441c3c01c0030301250740090702c5030401c3c51458510f00260001c0c01544c0c0c1d180400841c1c00240c0d1080e10200300727242 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 922882976 1250 922881726 922881847
    0x60815100503011203030b09042a050a0504410610080a0e0a0804120303140405031b0c0d1a25030c111b01110304060f14 53
    0x5111504001624110350000c0c071345003013040c21810158040c199038032185a0088041080008224010120091007051400008512400c0e081704d80070510260190390760200203800104024034040e00080c00c42d0003201d0b82281041000340740340f844840514480b440141d00300c4203122058803420403c9034007032011141030010081b8100017526642000c0c00c5802c00585401d141030f10040200f00b00c41c03049034800c101d25a0f42e03945a0220741042500081200000c0c2030900c1d02ca1100365550b0014000c9411102551400c2d0352610340c4041e441c01140030302039901941803c01d45540d601c01003041402c1c002c04c1030003040041c005030000c2e4160300400011761039914010303085403010001c0e50110004803a080005117005680f2081c0d90400d0740c005603008a00c1442c940050380d21f203008041004071401c0c1c880503004403400b003244c0d03200e004038010400011102c124001d1b0700d03031203a22082d00000100c2819072a10070420300d400325202e5424a98400001c0449010345107a0402c0c440740d541c401039a869 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 922884226 1250 922882976 922882999
    0x5030105091012080d18030306081b0f091e0a0207060b030d02100b0a0f081006060f0f0f0905030a030e0906010f021e120301081f020301060e042004060815 68
    0xc903107030fa489001d8080d10803030010407004040f80f041e50240c09646c0344c9200114425450303180c01006820240912406030140c03801c4d0744180c01004810700c0180500800b070011900350b0f0020f11501090061502d420b00e14211610300074540148031180c02900040005a40c0d1003007070500009407000c890b5800c2c002e921461341000c2c141e501040754a00c1901c50786012442144200000e0010019234002100c80ba0740c3c01000107161000103030501078809040d8040c0082c580d0b8201c00c1d61100c0c01018a180400c24100198508138413845030314001c103c042c1042c40106843e407001c0307803802d032680104602003003584410045070b141c11140b15600078024038100b030749003140060003500d03000c1d589411496820500e80031251004140800070070300780c42b150b003903481c1d603550105035564548854404500e41d04074101000f00030b10318006c1304c3c16590141ca1743d8000345140c10600c0006d000340c08540003000c506103c4280f010540300020030081102da901c089441c240889802c1000c030300310300103a110360004840e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 922885476 1250 922884226 922884239
    0x609060b09091302060d0c0201060f0b0f030f060301020d060905040201020601051509060c0a0209090a0b0603060705090105030405150a02071e2310050c07031d010824060a050301050910 81
    0x4809500c148008803d15442000b03201191043c001c59440d03014079814180100c032801d038154060f03400c42d03000c0390000100035600c4582d82814400d00034801c801c0c94003000051a5460b94a50490b0012006000185003030304501c5d004044801e250483c4504a840c6c10921040d1360b410440303035000d0030040754a403034800392407240852030f4070400d0192030040001280411002c83c050185c03545164015121802e24a40b2403034160b10360003091421039490400801082260a0000d0b41c64440c01e001d480e032030310745001d00e40191401c3e00000d000701d460340705002c0001c4240c064450392034011031441001503180c100314500420b04c580702004c1506040a40f0300c3d9039000c03031541850620b082155220254241c0340307a0010320f003041c4a03a042c42c1c041d5030615061050f1040240018031324103000e5504e03248a410b1402148400b41c03400100a400640c8100205802c80b40000d0f030720707c02c203150502025011074000042002a041004032002080d0040010440341c1040c00b006a800f6410a40d000c000d90b040c42c6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 922886726 1250 922885476 922885489
    0x17030a1b0810180f051819050316050f011b020106091107020d0206041a0d0507020c03070e070306081032040f08041214250b070519060609060b09 64
    0x210310442d400c0e00f440c02d064000c0240d40030f64480324a0781414010b41c60444900c4010307520241c003034000780c401e4100c2e134403880d910526070522496105c00514641007860031108801d00c0142c1e0150b445001b030100c501c070001801d05c02c0d10100142c250f0641c005d5200404003900b10b400d542d0007101a107081005000e03040c0d042c44101c68a240e4120341c0705081100c00e001050712800340e41c00001c21030804035601c100d501c0600e0058015a80700100500203640c0e03d041c22030300c0d28403980a6580650101c0010f20071038117101c410a5101003a031a002400941c1e03445007034a40a40c0708080c109107a5139107203403e20041c5c500031881c01c0030000c9481181880040d549500c200300b00030000b510f103920050358103080040820132a402400d03000011101d008050400c03440700a040e842c2e50489104607040c070045000c50a00c106104080c800040c0505850703d10a1103841d444520b00721a94018150452541403216034403400c0b1a002c0c1400190301410102c0741c030101d869981110412103000d0010503040d60301d40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 922887976 1250 922886726 922886729
    0x1403072c0612090a0507080105010f14101d060d0501170708060712060b0301060e09011403070e0c070c12030311040506040504020d0605040204060c2003150417030a1b0810 75
    0x20045100c5540c0d03940c00340381000744c0048014081d008007000000d00f039405401ca641a610a031902060855803845d402445400801e50f55400840c804444501c2c58000c0c021541d4025140c1c880c60030348003420380058a86e42c00705140c111186e6850006104d0f260008501c00c030710503c00c00c010400582002d80e55561140028184d208010039420032004500707003a0040390041000000041d101d5850b0300b80136103822003189034a1700a00d90078000142504841c80a606107580c0a00a00509410124490107511008001c0d2810401c100250000a10344034040001000340800b40965600f5900c0c0007402e58514166458003600305000500c56603603688120303002c84a08407801039450300104100c3c00a0038803507215a030300910100300042c0f00c582101b0146442071095040da00220048100186003060cc00075158155100d0101020340881c000d030a15000b034001c070559118108442000c0403154000c8950a070243c1d00c0780e0441c07441000c44808480c0007440c504080c1400d107480c0d82000303105c4286 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 922889226 1250 922887976 922887997
    0x14060403051b0f010516110c0108062e0305091002070b060f01180b0405100912032706020109060509060601020d1d0607111512161403072c06 62
    0x51030200d500c0c4003820400070030042403c4009129904d8224100940c1e801480e50302004110440c4005000440201e0f02c490400c205840b0140651606010701c03030b042c010301c042d0008102c880c4800341040c682e00f003062110352856981c046103c0c5420541c142c200b111039260f4241d0a401804110300040320303c0303e00c0f5072200c2c00b5680000480c0f581e000484155100c0403030055821210000071650070441801032096400540e0300c1c041061400400b00c0b00703100c980c42a010021019003401001170b200d0450501090591a882002c6190b8900d91b41da010034654481380c0540e54500c600400c0000e24000d565001e00e4141c007800c128501000041d480d0b000c0d90314090200302d0501d8404850220038540380f980c1140244c042910f41c4207600d0043c004519222a407880b40c07102d4042c01c6002e00310b1208039810090003003440001529220780800705201000f00c24010b20801c3c01c460201340103d9030156208503120382c3c4094000103000044c402d17250b940d400480a5194607441201e460b2116001c40303005104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 922890476 1250 922889226 922889257
    0x50301080d08062707090602030a0203041401020106032f0924030f010903080405060a020f0a11120703051b0120130e04030801030c0602060610030f060f0b04031406040305 75
    0x10340400050000e0220280741212064400c0381d03401814504e0400c40c411a501c0c0c503429620303a12030b402070340d42e4015117141e0001030740b080100384070408a4082d00c40402c2c90600012652540b41d580c0c84041d9407440890030403445081003140c40c1d20741c6200c0110b0180b03a0030345800c480e40c240a000303402c02d051030201ca200c0044084285000d40d4508000b0400a03103000c030020000c0b0080f61900034546032007980c0030360341480f070200402c4008000d03200700c54480001c2e9080714a80180c601c0c0c2504d00d0218040e0440c0b03d80607481008206a034000c0040604030320a07503034541d540007220400c00b500540c1d8900000107a140590600e448903050550a1852881180f07041d118407003003402202074219a04505410303500c000178001016084007140d8182e0380305104581e101a29036070102c2c0d403084101c84580e0701c200b280b4400c03c0124002da1100000c04500c000120b46103072240820b02070307410f49030300c0100d121000240c03c00c144030121800900d808070020181c1428149514018014020008070100503030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 922891726 1250 922890476 922890481
    0xf0b0d021009170d1107080c0d030216061e080c090f03011821020c030c010c15091b0506040b071209090f0c0e01050c06190f1515050301080d08 63
    0x2c1c05192104028003c50790500f5050f02200b08540d11110b858090310302150704140c00703504130310003c204031041d181c000009004800d07001081040303080d10300605034294050074180d07076060300c0030114501c00b900b86600c2d13820700e00c10300390108181110400081c1c410040d48000f40000c00d03900508503000705908484d81d41c8495298800240100000c203054a440c40480c0300c03840400c0312008917001c030a450840f21840318034008006989680040034225815004800114110b602505134004c185001d0801000a00004070898040310004d210503920383c1206c1c80704004280b071402c1c604000c0c140a888103400c0519185440342036000340030b40144845401c11000c12102c0c401c02c0700500a1030303032050510503c0050085a0001c150004100000680d001c800700c0c5254010001c40706125590401404a96507500c0f01250150703242107030040d516142d401d5940c40390b02e94091a071020710005c8100d01e02c28500f010751083c0c0c2c144000c0c0031342480710610042200d0304011962000e0b108990800d040280d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 922892976 1250 922891726 922891759
    0xc0102040503060a0b040501120c0909030519020a1713140303070206040303050403050615060d2406080f061c03030908070c030b0402011713060b13050702060a0f0b0d02 74
    0x901581d0001a018482d800c20040c0c2105581c101d481c052400303440800290340c942c0d1074010b01520085001c0d1001564000070030035031702c8950018080d240280b4000317042c40403040146000044501401005a20030545a001d00403480c4041d0148010000102d2500c014100a42e11003032242c450300f8500c40b8451901c0c03038284c80620450b000035a0080125682d151030303240203026500070b0300050703415104000004030800d080d401c2c0d20b010410014011403c000b40d50300000040c3c5005401c1800301c5000101d41c44807000c065602c20050407550701c5000c40351600960ba410b07a100d000f41450300c5500b008810881d001000c0881c02c203000c1c0c141c03601294030380040c02c01c2056841154001800c1490346c0030b0000910444240c200e000768400d0366200d46170031203070b010502084001d4901104c0180d502e40c1400000d1130b00e520041201c040540070280354540322048a01b210011168403000d600440100480c402d00c42c803034090035550703540d001c1006248031400300b0848403026900901810810084003501c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 922894226 1250 922892976 922892981
    0x140601171b0a0504140301020403030804021909050a0c180302061e13090f0e0601051c11150a09171c030e100204050411090904030f0c0b04121b0b010b0c01 68
    0x9003600c038001503070342d403004440140958403900c81c420003810040c01010756850180225001c40340c04d5990b105003038076681c003040a4001c8000c3c00042030407a80300c001908000034040d107071107020012000600c9500042015003c100da109036101d500d044200140b005030341c0c04050725040807405400040f400d1107400c052420340b184605031090000d80c0c41001861005540105d03820f89032154042c40b00508601c10996160f60a000342a40007044128141313110360b0b032041e40f03100c1c0ca004054401c000c030980004500031101d190304a010a920004020070b0507504460f4610050645800007250155101181c03138070341c404040d051521241555082c01700b6071003504005d203c80b481c013054a03007000594460000a50080c072034140140d0420301400c104904010942d8203011025202c0303c80e0b942c03960b030100c0700007400351100800d106001c48200046600320001c540300d1845802098012110000060300240c0c03080041030104194200c1034001428005045045501014041d522003402c140e21074003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 922895476 1250 922894226 922894261
    0xb18030f07170304031407030c0603020c100c02120409060e0610051606090b0a0e16030f020609150408030a12020313020d110301020720010e090f07050706091514060117 74
    0x1daa07030b04040c0306e0190020603144200c0344119546800c41d6aa04030682c281c5c00b500d40c1408003504285040003012000f41c00600c0074410600c15264242110701080c20035402503006014610f036510818000e005d0700b080b40f20340180080f13410202180c08407200416500c5035000700c41e000301e0000051420008160010300c0c0b900c1d40315403400c8161a01d44401c1c1c001b001e2000718040c1c02c1c407441240c8c005220803031201c07000b41d07500007a00041c8490300c0d409004850780308405e196001011a2a0a42142e101d40f01400180c00074201442e0384205415000303040c050f0061880d8030b280d20401c00e12031112410003455400540c141d48120700000c150401250a0042d04901070b003550000481d8401c200da0f040310b503500303110303902c804489628140300111840017812092907000340855000c520801921801d19900000c1440c03c40e161080720b07a01c450603900282402c89015031580c0d00d0300311208050007661040e0440383c0c0d0100741450050300080507595010f64200080e198500882c41c6a1401d036650b40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 922896726 1250 922895476 922895483
    0xa05040b09220210111507050409151509150224090f0102030901090204050906070f05032509030312110a110f250801050106120c180b18030f0717030403 67
    0x411511021001400c01a40d0384c0364001540200d56500400782d1b10201e0a42c010003081d5038285c1010704025002008007002d042e860b062140500c00004d10611b03a01408080300c5183e0b840d4500381d46003141d1006c0000e43c0301d07000b40554020303d400802a1050902156200240540e4820710b034490484a07802e1107103c3c3d01c1c4034042e500010402c11110030541009460500c00d0350100a03944c0e4200e002506c51200741c0d60100010101c50768184400d2066001d9a040760306516500b05039601000c41c81160000c2c0700680d40460b0003080204145900040c0e0444201307043c503000d120115070341001003d81d11403025090140120904110703407500c0b0410283d070b48030b100d00e0200c600d000380284814020183c900d026008038030a101c0d02045070f40c1c041c050b2a0407941140c5480790240c41414045020b40013071405a020000c0c04009c440e4615008000203009080701d2000c1d69235030300d054105180c0d510048000034041d038009510300100b07a02c0094944119804000180081c644207903200e400d41c41035602c0a1f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 922897976 1250 922896726 922896739
    0x20103020d0515100e031e0712030903061a0d0305180909102910050906032814010513020717030708060a0e0f09071a090a05040b092202 60
    0x12004241d49014a400c3d43c00440303441e0340059072a04100c03031a00b2101e000503050342042c0c80d1016411107001104001d80740100a0f0780400d510340c241002d42102c9050261700141c5c0c4070000700140500e078070034600100300520003065a54100000318132075200d0210000e081002c000781c00b0444000c0c021008900b883c0c01800300040e800c06411083e80c95002d10003c0c100e41d807500a9001a0200c191045074071514180c1e4040d002c460000200002d105003803a60009000c02048800759a0382e960004503c217210003048200c0c800e2141200c0da03610790140c05000c129610b0040c0141e680b0354034483d0b844c11568200c9884254401006001d070103402440001082101c4102101d1418104140a0340c4070704425907913104659603100c10091451340a1081190541d0004040740e0424042001c46074401404400c5400d0740744c0d20514003145d98805140280c001c00041144001c52030400b60400040034215020301c0109403400c000354000724050188101482c00140c2d0b078001c0d022a402c074501c0d654008003034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 922899226 1250 922897976 922897981
    0x6140909070225080c010207032f0429100c1106070501060b041e150503090a02030613020f0d0308070f02010e010c051b070b180d06061403060c0301060813020103020d05 74
    0x10700070303840881c0c0610312041c005d806650000d9403000880e402203035044441200002c0c1901145455854084804400700c1c14082954170703030351110300481d29225240c1c1c4120800204001c3c02c030720000310750b01c00184105402d80c094a0215800717405404259006582c90600307441200004c1c0b40c5101c0c40ca0020495400e002002690702e401601910841d032041d01c207050120751901c58119000b405008040b040b903500d45828400074410006141d10480c82c404980a20401c0c0d000645803030821100e20107402d00300c811880c11800c041d02e107004408400e562490702520f00c2d50780600907503c024000810800421907078400e103072017508a4178400c800701000300b0602c0a40c1000810582c800d004952040c0c48159080c0c4200d1000903000c0101c804d080c048a007840c480b501c40c0e413541c10803070000039400006e004481c00403410070300c607007001001103215a0031900c482100307040c00c000005015405140042c00100150368201c2c09150b88123400e440041080007052005a0081c00341d4184508900e150104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 922900476 1250 922899226 922899283
    0x5070b0403050d030204060f0e0d021207090f020f1e0f0406080f01080c1302130e270a03020a03121b0801090f0c0e090621010f06061409090702 63
    0x6000780c1c0c1c002c8082d01c41800c07291400350182d1290b0f2181c1000200d6207141201c40130710640b00003204d82002020043d0100b41038000401e0344049170051503e98002c2e0b0010440200203105001c80b80e41401815800d008407a00100d0702070080c01c0c4071020621890001801152021080340d0514000b124581e450780c0d00c1d410028042d18048601820241010002203011800000c00004070a0001d1108603070300c55400d4250301a400c2001c121050480c804070218001d0030320105148680510000070641014500d90300303451903c00201c40c0095004490f454010947c0400d505000c05d4050a01141c0b04a003c07040800070b04901d40091107142c0c407144060140b0340d002c550b86040345d11440080c00104114a03484003102ea0407900c00c40400c54100c03485106013000c000b180e80c8030341c2c02480c0d210b5801682c56410750140400c1c0c51400f45940d10304007004411218403900d00586614904000040d03851803a10000c2c1c0714450070316200d41106030014000074400c0200c0b103040c80103c0c94132402031400c0c49 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 922901726 1250 922900476 922900499
    0xa12050604060b12061f0807091a060910031107060204060f080c0a050a0309020307081c12020405090a1e0618050a020f031603091235070e030a0507 65
    0x31000c440303850400c451080f540c6050758015950354003802c0031700095100d85103445610751035030b0038011010000003c0050361003c01d000040040c084210701080b44900300122a180c2c070412122a0312402e0300b032100c11700c103440303d594807250003e81e4103001480342c0c011000300b81035000b0ba0800030102070002070701140f9590702c1203850700c140383c0390703111000c136511403c096414501409540c0d200040302070001450240c4240c0041010318005420354109680700e41d42c0d203046c043d45422140403010020546840203520021126000481c104114102410071000886000b40500041035094454105070026449100302da0700d040e810f0501081181e64070010420051112949084c0e664540b40c0003030902071060003207a480a203804080c501c0c55030f611800401e4080141101c00801d640c030f05100d40000c2e0014048400f0f4040307522040581e00402c81420510144003600c01d41e10b0300200c00c488210509414150b40098140c1400700068200c140031030300c2e2580c0c0c44806070040c45095000110800c031403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 922902976 1250 922901726 922901731
    0x100b0d02070b070f020615061e032401050708181809190f02090709080303090604110102010e120c0102070807080c06070c050a030f1e030c030e0d17060a120506 70
    0x100740c841c80316520403c00792a02c015540d06140507803c040c2c0058134605160148408140b001050790782000014003086522120307690000d04504000028000450b03219800b5201c05c0f405103031034149a81440e00020316900480390000d0a1010100700d002e0034504240a02218000251050880d4480d00400030400c0c1000d4030004902d004141c005426080401981c40351590000e03080c11500740e003542481000c00c00200450304121801e071004c00c400f0070170f000460287c0c1040e802040c4500749400e082c0c0f29260708070481070540e85003e03141c648404000c81c01c041e840c0e0707603a20025110a002d0b0072450291081040043c00c400000030f450040148600142c130080c0954002c03030340c0039598500d00b51000c0510314400740059000c2a451400240b1a14450701c0264403031a01c400e606407501034000702d00b0901d511550209480d184079480081c0d0510031010001c0d251001031020159042014180c20a080c00d420314080f1828001a151b032100c2d10200010001c84140c2c2d1505942c5003061611004113 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 922904226 1250 922902976 922902983
    0x8070b0103031b0f120201020712030e062d0601090b0a020109061b020307060216021011060a110414190b030109062304020a030e0d1205060d1a100b0d0207 68
    0x551070020340034510a4403e2164035400841d60414801c1502c1d2800800400c016103021503408224120001760081030000c0510038585001c511144420601403c220009024180c825440b01e420051a8056031b801e414005141c003418800d5250f5000417a0422155003111401040010b4030030841a8154001c0d403c0782d0040d803080044004040c1c1d6103040800300040000141c0c810b00824010030942d500400d0802e1a281079100360714226030200d41082200f181000205480980325150144280b00300b5902200210041010001c207414140c424099400b40a06580c21407503107000645400080c83d141051910007500c05a50310101c0e6000703036000340500d10305c0508241d000100d0340c107584001b0286405622014003500e050006010081d01b2501080d020035440d21040e0380d408405010308a4507003000da50340e60b41180d180804c60f040d2400039202c85c4c0501c051201d200003252140316100360301300c8003420001c003546901246030b00951072038100d0020082c001510b102c80075034aa00a02001c0d20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 922905476 1250 922904226 922904237
    0x20a0207061101020708090603100806010b0a021b09010b0f0c0708060402240a03111908070905090c030601051e0f070b0f070c080d02041a0403050c03060403050d0506010c08070b010303 81
    0x70b03081c5141c1c00d034000c0b5030001300755060601c4541d000d854a00051580031158600102c079540e0b4546880340307081f0007a40401d40703104000170b4002139640d042c0044591604029143e00304c880740c9a01080d4020014410b14a544c400807a00004401d00c1004940404c00c0500460750703800d8548a1031501d480382070380d00724800e450b1205010320400e10900003d85800c2011001130400d03990340c50503409005c04481c8140b040f201000040034803c8000503170070803024540d507254914504044003600022081c0c003c6446010a0710411200740000350407603500c55000c3c81c2c0f45480d04501d107442d1030380ca0f0741d0790344504800c00042006000500801c000d4004180903914482c01d03519404451494541e0580b60700002a94500001b00465000750040c0b091940d040b80c0103162035610b110361150303860500d842d107440d0b1000003010018098100110038a030720040300580300c00d0900e0781d03010300780d48502241d60090585520000b84036030b0181050104182c0c03c0403086540742c0b00b030f180480c90b030482408220041032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 922906726 1250 922905476 922905497
    0xc0203071505161202071a030705090a030203010e010f1d030915121501081b0912070906060801050a050402090d47010f0b04061d1c060b0d020a060c15020a020706 71
    0x9452054a411f182600c01c600c81c556221403400302c545520100c120b68119410180000c0162424802c250003d007080000107140e54900100b00107a9a405040c043d40381901c2d480b103032032610080308407180380c0001c482160450310169201c000354002c408804100118000800481c4401001640c0480307100b665650f04a0b41c1c0c0d92040c83c8100082c0c3d20038102c4100900c8080c450707080c80c580d446410842c60b012a01c0c3c455445c7e02c58410b4640c541c0142000402c107000410881c10701c01d00400c05406c0891b01175080801d01c0e0301040c50202400005010711040108095118800c480b11114442036416203118556034010303107001e42500d1141c40d010401e249400000c80704003800000b000d45548460091a103443c040c1c0c1120074210342c07100a051344034204a0000c55680e161041c0d8081c50208510514903002401c05100315004d1101190085010390b40314801a6500208541503400500704074503035840300d041c602280c150100f03000c10118070001729100c5194000034410308480180d070340c0485e0715 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 922907976 1250 922906726 922906739
    0x3010602150f15010c02030715030605010e030f0a03320c0c0a0e0115020c030703050c1302090f150c060f090d0c15050619060804060c0c020307150516120207 69
    0x31008451020900c003000780c10310030f15803003252a0a0140e000504540c1095150710b41d40d42014040a2500d001c2941c8103001c2005581164590031056802c40292954603404a65103131502040340d401401c0000c40140c8140d090102d50000c01e25800600e01c864600c01020f0248040754460940400c0a1050502c6044c4e00d2030081d558030280d98018a03030380641d0346441541080d010b4102e0310305c02540600113280003d602c04101000085000d90010070b003494410041c4903801480e0000d00c840c413801000b9070000ca865041f00e40009103015a02102321550083d01654107004203042242e05000c0c940600c523030820207a500b1406501d420f4251902d1902c4640e09a5400d058411700400048290700e41d5444481c240d40803541c46100941504003541500e450201f020110344c01810106000310305000034440d1a00c2900ba1107070f00d5041c0201c2600c05600082d80c1ca2803188500d0000e4804040b50555462103401968501580c100202440c400c1c2483d2034030704140e8200c1c103540148078151000809 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 922909226 1250 922907976 922908001
    0x31e150105031806041101110d080601121e090b070e0d06050414070b03041203020304081c020f1303023f1e03120603030405010203090105070c0b0301060215 69
    0x5144a4058141a040800040d00c6540004000c2100c0080300700b690920f0240910165120340c1c800c8401700640f00c0344200141882c01003d03110009a0f01446804c00c1c404c0e0003c51154104c1001d081100c500d04c50b50550700040e201c0071260000c60900e15124405c0410690401c1c81d07191710811250f04136560752641180e01d0103c12501952107804060040701040389680720a40080c05080d41c8806c40c0d0070010a00c0c508000341e4800c6100050000800c41070044094119000140c1d5103010b500d10b0810352500c503d02d004a8003030040714841860500b070101d005604441e280030742a2581500c0d000722504c0c0788408501448140d0082d220303048500600c81c060004420869107a450180b5640200f54103a1000b20000203c40500d221300200710104041804043d1030420441c0001d56a842101c01829100800641028001d0b4002c3c40280406d80c0c02100740e40610400b803074419120174681c109014802001c0c0d01241c1070300300000010a180340d0100c1d806180d10000b04451180b51980703d0300d01003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 922910476 1250 922909226 922909231
    0x30c1e012a140c0d03050a020c06091b031504061d01060b0c011104030c0b03040302030412080711092a070602040f0503190b04080a031d07050109061707140f0f031e 72
    0xa05800c58401300141d14040d50007282c02c284514001420562a8080e1614201c8180d0300d4882c2680000c04268120344400e040740c43c8001c0640140400140c504001301d140c06c00500300070b11454a6a85518419000d00004130003030020300300a01410350340701c00c90b960347d41c882015216a9401c120410f1603481e00001248c048a51000070b00c0c821a181c0004040c1a0300b01601c21011800200702c00518100400c3c9c8201005010310ac8040d40c07207089140212109400e4440c0c039007d900301e101000001c040100c07141240c1c20b54880380091042c018150384402d4480c0b031000400e020720204020851882129880c016500d0540441e068284002c1c0c05040c60b1483e0a402001ca0500e80002800a021300d00039040a0070181404100003810a51030380e142e107041549200301c1d9102c41020803056070b0000000c6c00529a40c00c20a0089018820000071010300038511010b1200703140001c400c041440c01103030303100740a0340c00140c1c44e00941c000d6107490340d10a5401114444808201041d0f45810080213070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 922911726 1250 922910476 922910497
    0x11090103150b07080a090f0e16080f0601081e0a050f1b0a050f091309020312161e02060301170c0117070c020111010606050c0f030c1e012a14 62
    0x6007461460b07501c1494652200405c80304000c07900c60000b8108885110003405080c01040d424441d290400b2034292000c1d4204c00001000070003800c0c061003c1c901c032403140e0404405c1c0303496034a550315985084946007072100c0d03d180d441c03201800c1212641542e8840d50180c080b030688241241c4035160b10b070002c01c51110343c8021000c2d00b046107104040c0118010490009070003520b42c1060314110000c3c08803c07400440ca6041911400e28104614040c040301d49000440055141040402e01944010581c103c038000c0c8054240960b004801c207400021400083c0d00510303580c2e0b6580c685103540054161030040926a11480004943c07a40c007a940d0382d040d0700f0400805c203985655808040f50007000306441641030284c0c4210f04283e030402800307101c000d032440c1d440c2d482e076640c3c52600700c80c54548200e003100d41540042c031a800d40300750003140744641200007541141c05000701d02d4400d4010b00440c907a800c3d02d0b44000e0290102e03441075480c00a101105601d032420010340b0001041400e100d101400c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 922912976 1250 922911726 922911749
    0x809120c031236010b091311010503070c02130204050d050d080903030c070803060f041803090905090c09190c0801050f09010b0d092603040b1e0f04080903011109010315 74
    0xa4020f00341e80b0b048070382c40418200000c25205e00400c04940d0045083c1c80390b414880c821142e10702485000c02000c0b1403100286001459480e010b040108065503100f0000e20500003080300310b00100c5660182c901800005285031005030103441c0030b580c0c0d8643d901c001d0010400d81c0340004c01c0c116002c0103681c8244824a40c491404015030349080003907100a0610354880005100091103848611803031402c4020010034117948181420302a006503103a1f4040b040361401c2c2410081d8a110104103100c141034280d0360007401d030f1510441d01032481c081102200e051807503d030b40d440446a1100300c86049500c20b0312940710706201c00c41400513880d024003030f00d500c40300b040104040c01c0c0007591044605601030b040b42d0410a03144085030009103080c040c142002403000c400d100c2800400840942c2104550600c03241e070901e10802c00c500104010714a1a107200101c00103824008140216040b08130005c00812a00d86403040da44800e0300020b10300d5000178034103040f02304581118403d403400d80e104062507 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 922914226 1250 922912976 922913041
    0x3031302042403060617160b030417030a02092806230f0309060c0408071e0e0703050f060409020108040f06091403040602011b0f0809120c0312 63
    0x7400090245151880941950004605281c0040c09020405184240c60116101c0d02d0802000801000240150a40d070041c64546440c00d201c0c064140c12660461910b90302c03a9114100050b84032007a6100c061400c000200f00104c201043e402048070303c5045520b03548034420490f5402c88a429140007c000340c07020f8909100d85405113000480010003044e07500342d80080c0c18014051600b005906038241d00c0084140901902c05110540d071001091030000d0602d4030b0480303043d80c0c50120344190780400b4446030a03c03480c14035407514480035004204000c612410021001402040100c5541071004c1ca00000310714145802d010b5481c5003a0169a010b982d9100c0351511306101a52030402c860040d62166000006400282c440b4000070380c40005d90f450340d10b0004085d084d5100c000304019080000d00310300c03881f181c0207000c4208038138091604840a03940c4807a40c3d450a000318682e941c181d0340c0070425411000300000100141020b80d01800056114801001358155a00e00c580d44541d0302240c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 922915476 1250 922914226 922914229
    0x21006031a0406110705070e01080d020a080d1b0f020d110c040b03100e0d0207080303010b0d0504020307030804090c110c0d08070f0b07080106080711030301090207020103060902041409070203031302 87
    0xe03001070150100040401c408134a00103d41c5c024041101d09070040082003143d1000d0700205030040004401904810064050094903407280390401407400c207020625401c113001e1944000c2030802e0b2107000600d00381c0300c440007400b1a40c1b2400514010700c0703031803289a10035101d00280b5400c0ca141c10010554550340004000103001050070a940620941c0f46000410105001d1804005614030190802d00080b584c02414031045810240c056802040100514060f00c000c07201020f030007010004e03c9031154800241000540d80c0007500e035030004100030130b01c8140c0c1d501c003034908200c90304c44244001142c090241c80352034110b4003c1d48030780b0000b034240200354540000e04c8914400c050303140001c40c0d265200003070804180d407183c0000750140c0061000c2d40c0c00c4029a60444c00506294284107101801e844d03031307440140100c907240354000c224035007164001e0b0850000b40030305078001d644880d2640748071401207140201d514820350000d4040388001e030010017100d01490101d1810410f1004980 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 922916726 1250 922915476 922915523
    0x506100e04020c011401090c09060e100c020d060504060e0c04090804030321020a03060504110316050d09140a05010c090807030f0f14010504020a0f0b031f0b031602100603 75
    0x4100f950155240c421a0a0440d2131460040c040c1c00c22540000e03c0246002000701480c100c0c0d04241c00b40003424103816100ea541d0494600101e06034941403209503054400710320082d2581e10002c3c44a820513050108001203900101080e20300704048595070112107041006580000b08091311415040000380003003031107205080705070307000c00b1170180210380340006c3d01040b41c0c403c0802d440040e0303551605200c42c0c5001e0040036a080006a0150705608014082000c0170111040d150180724001600f5625800c59410005443c0c0d0400c16100c000000c0300000c0303440c0c400f8000102d606511302401941020302480c424016240c26000030a1501d0655440c4407108041e844c00395480c094050b8120f00050303030100d001d01d140381d00c4000845d0340d040c01d1040c0580c43c4e5880d00070a00086080d070302030003002e599805980d402104c8414003142200d0045845d00f0b20040394103d952031450006c10030400c0703088c407506540700080c598211108038116111540448080c1d0000a182d401d40341000400121b404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 922917976 1250 922916726 922916737
    0x2708090109050a06030f150b0a030c1215030b01171002210a020901110c010c020603060409290a140115020709050a060e13033c030f0506100e0402 64
    0x103041c6015456141c00005400c801d86a200c030300060780b03502c0f100380d00c5001802102d851010f0100c0001d071184c244141e1013464002c00c251442019035811b9005413180c4910868552841e200700700704a016010000c00004103a02c1c001501d0601c401c2000084c44074035003003915034120a4201801c80c0007842d5600c1800b942c0484d0b00202e81105142028411010048030b09000da8000c020040e43c808005002402c03d00c18000103101d030760022aa05004c0780d802c65a404291a8121007281d40c0ea07580500140003010661009820b0b040340c9001e00e00740c01c0e40030082d4003202c066410555029910020b0b43c1c4143c0340360071884800c2c05d40010040020381d10344a01c40c0e411044030b0058a10054480400204440b070445130000100e4903404100154041900d80680004808c40d40b40d200c6155500e010b441d40411020740714140c07000c40b0021811000002c0f001e80403150003101c40c03d054540d090010302800c020b1581103845807809000c60a40e142c2031820180f4031505840300703440700203e08100402034024 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 922919226 1250 922917976 922917979
    0xc07080604020a23310603030e0f0105120a020703080f0105031e03070615170601050303120613050f040c09140403080705040b03090d090e070c111c050709270809 71
    0x590080703d900380d175002e910304000803c010080281001c1c2c2d4400400002e9180c0c103d00e0391505d841000c0c00401e5011240c80d0002c80145e40c401a15113240c401280c0f1485802041c0c80141c0d02c42c814401e004e6035a4000308140c0d402a0b9400c0071780e85447d01c080740c0202c403c1c800c1540c107501c5081d04800c0c005000341801c60348041070065a040204c180c92390b03420755441d40c1c1e2880403034520304001c1c0940c6071304040030041c80d01004010922581800d001c40e0380c902c1030186001078000355000280581d600c0c2c0414614540801c007007030180d4100a65480545001510201c0710b040c1c10000128031417906115040d051342c0e03030000440301c0f5200c1d52015181c1e0390010302413104019041101207620454603004600640e101002083c001c100014021715070140e640018003444914402d128420740e100222001054002a0044c003169005000603080443d41e4505031100c0f03142800c0c60244080070809508039600c0d05005d200b00d4841000005c04500c440030f05040c1e4140d200c04c618003143c500000b40100480 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 922920476 1250 922919226 922919279
    0xc1011070b130b100803040515070f060507300e010e0f0303011e081015150e100201052403010b0603090f0708210d0906020f0c07080604020a 62
    0x5a50300d4040c04007000b01c030003140c1c9440300c645400030400090580c992280c000038401e2003841c00c001540d03407284142e10800e441668110030030040f001c400000c4a02290340003881d06c1a1199520f4000094030f000c55900b4003044101420b0240300100c2c20003203411030340562001c45540c069a818500400100c2d1070410190358500c0c2c003154105c802c01000312032071803036401036840e5031500103026540081060304064407501200c080200f00e0b000140c1d916404440b00c0d003c540001040b02d0f4030400003203070b4030208010051185c0c0d442880e402c0550481080c8040c0d6508100d0340390281d090b0b00380c0300151a91110744c252416802405c02c0e0007810003010000050012501840900c002b039499001981c01e5000364100c003c04010b020381c2080280000c1c042c142c050841d41022542a184443c4807291003416881e0005503903c040c02940c2c48611002d60090045490781d1013890003d00c240c00070761300e450311441138020102e82c0d24000121240b041e0390040c242c5046a003840b0002c5a20102c0d001900c0e01d908 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 922921726 1250 922920476 922920487
    0xe010f050a170108150c070b0106050c120d020702031c0509040b1903211e080a290109050f060313031e031a010513090506360c0c1011 59
    0x840b8007112402031021400400f002140340540a080010140031004018410022440041e0b04040154111070441c14029298a18010614204503403401c03038404103e40011a080f0a0a003640901440350003030301101c20303001c685810000c13060b503030010940120700c0620940d03110b0302e82030700071980352280a40b002c0c18440c06443c0d1245850f08541044586081011001d8101c0700000301d401c5901c42207252612424802c440c0c0c4d40c00468425018604201806002550b906144d41010002082c41c50321200e841e9032521810318100c5130100703035034000780100c20005080d10704004444a000c800a01140ca1600d4031001ea0020b00e0782400228140040c124500320422141e54040d280c0c0c1001e0b4401181e180008900560595410804541030290034000311300c1d55044040002d09603034525000043c55256000011039011541701011846009619010031011042c40c007002044200c02d180b4032562070303007010308425006004d9500c490b544882c4002c11980d981d5044283c1c1d90700d060f0042450302 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 922922976 1250 922921726 922921757
    0x507060f1220030c09190603230c0711330a0e0d0f020d06060321050a0c060608030c03130807060203160602040504110903120c15100803041806060e010f050a 69
    0x804a0a114444411441d0030400c0408d07098000d6405a00000740110b00920456030102a10600607001711244840800d081d8100320125808480310b42c801032129507141c02d0041d84108826180c00c007600381c114201c5034042822000c40030741e11004981d13201c1c0d00d0307006400b40c14029100581031007034460f1041c042d0290f0158443c00200381d025400b0721000314285d415403c28050324800041980716000c05100302d886080d5004055072a8000580b919414044850800708050311540d0003d051034040003d5180e0441350000040a26040d1140c200d48460365411026032200d50314400c01026810400c0000829841c2e034950003441445041d0060030240c485000c1422174940c1803440e0121040000d012040d441c0c1000031682442e0080c1080f40f40001000000c2d4a41285000301d4209020035030104105641003c0e0f054081c0170008203c0c1d0300c1d04d60724989800c00c0010b1030210001d4524103131010410a20900d042c0b035000340103031601d18002422100448850380101d000070200110900d40a0a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 922924226 1250 922922976 922922989
    0x9110a210f06060b071a040305070602031f120311010b06030f07020f10020405030f0c010e0f0301090210260108030307121b020304080d030204080a0803090a0507060f1220030c09 78
    0x14002d01d021040e2541c172145070480001006802c91200b6a5800041000099015048a09d000c0d44080003580780e44400e040b584180c0b0b0400d05a2020001c2c401c0082100440e030200c00c4110740c0a699000498106100540d0803201e140035882c2d0010000c00005070040b1100440325004403041c81104c0004800211203070506a1b00300750140b40316000a400c000c2440e040100007000c071640d4014090014130300002a20b200800c1920030700400721b80c8400e0900b03990a41c0a0031909070040c0180018983c0d8a1000700105055088160300c6100c01a11224500c1e248c5c42c1a030598031844002c0d4519128048251281c2c240044603075403842c2c40b05c46039040056800200042440d2640003551a20309140200c1d08201c5243e01b44010981306010810907018002000d5007001d40201d61280d80f41c40d02030905060441140d009001c52003100c40010742103a0240300c100308020f00340e07030f00c3e200072550514401c00e030f420003041b001ca150070440340c075541c403210700004641219841c107016162581c00d001103080c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 922925476 1250 922924226 922924229
    0xa050c01050103050a020a2103030c14041403070e070c0318120f060c02120405040c02030909090307030219030e0405072f0c031c0e0a170109110a210f0606 68
    0x10185c101280d60421801d0440c1000090181c0800d104440b00039031050701c04082940390301404041e2079622415036140984001c0f40420f0031094010f5070345490b40b00c101442007540c100d6a000348201c10001400887c44002c0d2030242c111551106004409600c04565542c1002171101020050500004090a420703050011103031150101007040011802c241c42190300000c4e8003020b54000c590584400801c60703003200c2c10741d88201c40001c0c00074100c08049280d80624201030780c1100e090018400305610002c0640302d2248039500316258600030a003281030a0603441002000306d20106002c4000345003a400060380710308540391206001c40c00c264003600b0050441624244d00f00040103603e2801402d01803503140450580040c1001601d03564050026000040d1540800c0100100a1300030b03614007615400070060311007034480300c5e240a0a203e0091001c80b1049665a81e14442900e0505001512504881034584000c03071074082200c01e801e0321240148200d500b082400c4003c00001c091b40b09080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 922926726 1250 922925476 922925483
    0x5162405040c06030b0a030803100503030a0903060f020a140304030c0b100305192111030d0533060d0b091003121812030e0d0b060103110c03070201050a050c01050103 73
    0x1480d41000d080225045807150051420141040304100254660703002da507084940c40035a8070b943c3d960f1f0b182c005d101008990003050b03141c040005c4501c1c80560024003c005e807405000100145034888a0580c100d00c07032030b40540041550034503609007124002c0007540e805806803c0000480b107883e51000c088140031240e24030000d1a924060044c040100f01030002001d900c15800700403803080d220700b1010540010070340348420310305444481c1c1070b208901d0103000070b500d481241d40700c03d41c00e420000038000413140781d401c422100d42403045000018403814007622280c080f0301040b0030141e0520200b83d00200d2400780840d11407070894100e4655080b9644900c0242c81074091190030341c904140501d042600c048100421030744400c00c0c410980181e40211021240c4840b4800b1040c5426a00200702c0c40c07800303500440155558050050700c0b000c45104500c00d13602003044001d0130054491a0240386144103c0e580f062008800650145008003d0555a41046400c1c9003007c2c0c0d0640c20340320240c0040303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 922927976 1250 922926726 922926731
    0xb03070906170304030f140715030204060e0d170c0c21010c1412060d141b04060807050603180d1101110307081b2a071401051624 57
    0x1c0018180b0500c0221100301c40c1d41c00385240034551340f140c1400c0c0040190141c1140310b11241d0481002c0100302c1c007401400c0314441c0c209220a80300c0081c0094220b8480c5602250040140501d09c0c500784a441c403003582e215003d40c00015804401075144c0c0c2100d401c19040f8032840307020b010707255560365104024152882080b20b100800c441a1802d641040b0340f81010710072019003080c0500c50040c103036940310301165001d00d200d03078078840000d81d4a082e180b80a03003028000c107141030716800042941d1400340170b448200150801074206010444115129900302a00b01440c2446075186c143d00540d0010007080402c82081030b0001e00174200f0304a1240300d00818018050030300c4400080c0908800920010003807402c5103041d94000d09045001000981c500d4502e05106802001210603201c40442e00402d0252074001110700c2e0175000040c0c21240c126110380e400001d101205d9000000f0003582c10b94a02e42422203112000e10306400818013113034040303015800c1c1c0001e002ea4142c0c1008580041002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 922929226 1250 922927976 922927979
    0x120f1b1e1a030f0103080c0c15070209070f17060307080706180504090209010e040218100302090105060a02030a140c030d1424120a170403150b0f12010b03070906 71
    0x40510746000c60041c40c90351030050040190000d1140c2d101030450750081071139aa10421009417601b0074150703008c410b600140f42600d40c0d81139900d41e0013621201e4801d07503040500351100704080d61200816010580041c0c9101c91441070050110401034020300050101ca4403035882d8030a03d41803031a1504042c000412040a41100c01c2e103826100d001400256410801c0c0b00717490b000701c4d118040500070109a40c9800b0046000c6440310894003688901000d0803110f2810a0000001c14110030300c001d0f40702c1e440481c0080b42c207117800340031100c1055031a0011031420a0340300301603c6a00e00e460300e4800061084c012404100303010700c01081b8080d09010000b400b40d213003c83d000260140500700b030341d4024000c030240e00441d9540c3d2111102c4103048030300b403102075140048285031140d000300041900825002a03d40788400c200a00241c900c5a80c6038014410155030741c408171801e62520642c8040882009070083c02c2244847c009199070000101e01a80400046131511a0503807116441700e9070b6820 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 922930476 1250 922929226 922929239
    0x20a0e07032003060a0608041a09030a11060f0610051c0204061b03230c16050414163b19030206030c09030c03060106030213120f1b1e 59
    0x800404a000d0a00d42c40e0440c20610b0208501174a14000d5505000d041e601140c03d00540c4940e4440f070503c02c1552203514503007454070f15140c3d007014010101103000344030000116403000c03680c14810049a1701c50781159890b502001501c1c0c2294a503035085c050104410306900b8844d00c640c0c2459210941c0150340d0348d19082c001044450304445064200010313561500c0042d9200f00d400c078900c2003018216000702440040801c0300c0c81203480c80c00562045500150500d008515030a0480d0401c40d0304001d8a5010422070301644000c840c00305c8048514903002c0300041c011084185d4032590044d8132910000485441c40208001d46004120700c112400c3c9008146010456940d0076180c00d40d00f050040d00e1603005c54030500014050404000022070280307244d407000c000c8942071820080032110b007035943d04800341c000e6012280308840a600480d003c09e0640e14122a0313010180e0202c44450400d815883d140400040315001c04000f880410380021351448950844080c90303070750381003500403d19081 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 922931726 1250 922930476 922930511
    0x1b0f1209150c0a0311160b040b06010302031b21040b04121805010806181314010207080f0c211209060c0304080c1603030306091401050913020a0e0703 66
    0xc400c01c100d200340302040000c401003400d650085000d410082110750100203c0d41d0b49008007a450040703c1010041d071014800c1d400501d502850250543c1765064540c0d000440680c4800c0711000f52000b003800050b1802e00c6403100410ac20700f1200c0c1180da410445400e03444d81540d05130b6042d01c3c0340d050881403000784203018111080003001d5003403244001480a02145030f00e2024464141802404000103015460303030500950042003004d40d80006150842c044142c80300104003e80d40c081741c40403060780754079051086031070041c5c11500460405481182c0740640754071401c40e003261400f8480a81c001030b01844840003000092080c4542c440e503006a22013510b10000348282c1e11a485030f024000301811400c00c4030b800ca5001000660395400040036140b4180344000c4451074641941c40000034035a0542c41034080c4d9503c03035014040f1301c0c40049031028003642801001e0f8030100c25008504101c480c0c070706407010903102401040482d03540e902490440041101d00343c0c00301f40c0301c0b69018681e14150 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 922932976 1250 922931726 922931743
    0x71a03010608150913140f1c1d090606070606170c0f280305070f091404020a090b03190f030305010e011a0f09060304061514091b0f1209 60
    0x1d0b0300d068401c0f440040080d901040190030001102441c0c8110070900c1048462181680400300403169250416011680c1d0f6450045a0010300b2a80d1401040c03a503120390600703c80003000301c080c0c1c000c0700070b40000c01050683c054011944400104010b100040080c040c1c4002000d80461804009480014131030800300f1682c0114401c0a000d0320300c070401d5441410500944001d58003a403480c1802500b640d094441c0c2e1303000500035100d80720002942c030141c040040c05460941c103042c05440615640700400490694000f1760140d446103003842003155950011015010041c204c85c16042040410414100d00100589103011142d40031814540c1600a00e801011341d09804401036140c206982c0c640c440007510f0705110076000428000114800c4c00303139005a000240f003c1d87e00e080500e040e400501d40c1c0d040c0e852000000000c0012902c1c125038462012940181003910303140c0c3d4601c4c3e0f0032001c0d170000605404400003400300300502c15101000d081501000b1a00c503484fc20031709442450810300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 922934226 1250 922932976 922932991
    0x5131416060c0b180a020607060b010f110d0f030b041a090609060a0909030504031a10080c0105041a040801060e090111071110030605090c04030c0b0403021c0302071a03010608 77
    0x10451544001040900c09651105440d49441380704290201442e080c00154003010398080c802044117014805aa404054258800d80380c030b182c1c1391101c0c1c206450355a088175520b0015004040c1c1c00c0c80460044087d0340c1c954801c0c1c03400044040909000404030380322031401e08103200440d501c03140581050004c1c103401c85c008a07000c0796989131120000d4089250307402011419600c6080324810103002da4155006554001010903142007a58140c0c0204a01196a00e000441000c00008c070302e500401e49890304035041c2d40303030351510b400e0155148020001c07140380b130a416020040000ca054081c0704010180403680e03a540d00c2401c01061311803e4604015040072100c00422680e4000f0740c80003002140c00d1015950507a42e00c220f131400f503000303180d130758405a0000240c004106441980c0002002500e100e01403900da21910341c0842c0c02140268080290450301c550b00042e1650003980065034440e1181c41194400c40d15012469038091410701d42c181175060210040c400f00e40c0152840381c0c01030380b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 922935476 1250 922934226 922934237
    0x3070207050f120a081e0d0203040510050402011d2b121803110619050d0c110c061c0e0c01030e150424050f09061303120513141606 58
    0x80040f4000d4481d0b2521400800800b80018241580720f801d51907170072140c0c4060f014031b031035009043c01a401b03940100d9080b6081e000700c40501c0c20002c480e10841d170140d901a541d4203881c1c035039000f0112806a03c004c032554054005114182442e003031007421400d0188901e40700d000c08a80d8641021804205101c000074050600400403c020260715031038100c0e81c1010098400c0d03250380340415801c1c0314100c0444012000e0117481c5111030381003402013841240d40c40081040413900f050440e5620310351009400b140e00560504c100600c0c0c01d00160098070003a4007266458030440f0100030454191501c4400103810002000010b0760305489982100e1110750041e02903449600b02844400703400030300080801c10000034880000701304000d04005071001400410079800c10801c51203900030120703503a8103a40b042800246c51101e594240c10000d035810b8a505c07401e005d0000300e80c0050030004011804491a031f69001c004140c4042c55030352202851006044013101c0450040d0781c42e59260005c109000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 922936726 1250 922935476 922935499
    0x506181f091a0c090d020402190c0b062d0604050910060f0519030e1018060617120703021f0c02010f0b0a270542040b03100203070207050f 61
    0x10f002004558900300126048281c4d0310051000400034020300d4181040c8141c5c00781d0035590250452414828280148030603070b4981d64507020030040216204001828050304044051f540f008980e9200c03402d400108021309140d1540c3c00b09443c1d4004aa8220904260341d104100720390300040250141403072031500c14a45281e903044225460884418201010764411414881550900c8841b500018881c1c4c02d01901e00c00c0329141214602c1c60905584040c640900080c110107003910700120340d00740e00c0113402c00c84c40c8c0c21001740903504460404e43c194011142400c0042e8030140790000c0380350340c1c4000001d010440c4140203003101c092400b0000010b10b003a0340400e0641e0f03005415805c503100d50b002c601302018543c4804520800c94000b20000b82c1c18102840103624407402c1310480e441203c0b899910b400f0764000d0000b401e0405c1d4806103884181e8661140581c1450b40000c04501006411114403d0403882840b041f81e00c120341000058100340418802c929162400345100d803021140a03480c407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 922937976 1250 922936726 922936741
    0x1061206030b01060804050f010507030608070e131e0203151e01050108190605030a030e0114090a0e060d14010204091409120a020a0c03081206010302070506181f091a 73
    0xc2d60180034000c280095403001508000007000620b0030320b41224001d020609094201402404c013600070008580200c0e0030100e103070b0141c010224400c0d903548854030701d40c41c900e0701d9100ba041c0c4240101000c0c81c0c1142514400760701c2c20000015410508001c4100510340030b032003200091144040920b500034454010800c5d80c2c0d0050b103990300442c02d00048409101d6215030600109500c1e0301154141c0502c0341c900c01410340104198014660a8891003801c41c12125a41d03850300c22189116840a0584400d1010a18030740b2069030000e40580600d901c0646901c40e40040c43c02c21342809000e070340005090050320202d001f0590252200c488410450910f000d5840e240c1d11410210f9885600200d08021468401c00c418840316801c080f0324400640c80e810840740660041e080d45031348203240000300c0d0165102e8400c070703655280c000c005842e440d00d406000e0003101c145100346046034420400c212400d040b2a02c02c09030703040341100000880d0140d0745400c40c0314034604448201421502c600b0814007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 922939226 1250 922937976 922937993
    0x30702010f0503070504121a10081914011524050d0b0409021804110a06020d08091e06060f09070807180f1401030f1e021b03120106120603 61
    0x40d06051190300e81d904d0300d000712180d01565008014502c020211141400030742606200c26000b03508031003000b60346803004072441d80c1451103410740d250700100c803840000600050802808e482540d41140022185510700d09540010341d1205030595410f004100d14456200401444100400e40808101d08410b000e0807501401c100d0368102a00e415038100c40340d889074071400805034020b094401080c8000041260020100c0307048a00c42e10032078650b03041d0b18242031000300b1548564003c02110440840c1151407030170142c490000c1d44500c000d98801c11084804a83c14202c2c50b4000785081d180080c01c108013109400c050700c3c0103102e010300b409825039020501e654080b0b240d08040120400203501000410b03207076803001c3d540d5880d901c00800d401511180500000900740e8040c041e43c03c8148601040b10007891220418006000055020005503000f40c88a8507800f4503140010310010540c40c1554840204241500e5595006008203500302c1f80c80306800200040c20800d15045a91f91000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 922940476 1250 922939226 922939247
    0x714030c04090f061e0c080c0703121518050f07090302100203090d0818030f100e010e0709020a0f170a02090627120109120503060315040b0609060303070201 69
    0x41c1e44589a007030034420b40f580500c035110340c0000e00b0054045407004009000c0e0980390343d004524100a012980c2c240706400301070207044040c04413490104140d500307445e451419170b44681c0c02602c5000c08220b0403c0541c42d500104448012005203945001d8000111350f80240440310620416003484075003903021381004103883d0305070b941d281c01c00715010080c0d185004042480e41d2181030000e8900810080c0b02c05000721080c100218004440c1c00c90402d500e950320100d94000640c0300c0c01c04c0d6040070b200c5030001c0f512400c01600014480c2c0110f400141042c0381a0840b81000341c0000740c02e000542d001e503c242400390545455039001310b003a4041c000f8010050508000c0640210303018141e5074504007101d404907c5000c685500242488000714004050102c213132181043e01c0919140e610180210031005a002610b0710303403065401d2064501b5000071b801d1030381511070f410551064154190105014074041c00f03040400385400010002960710080c0900e00940043c0031807001030342c0010800d80c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 922941726 1250 922940476 922940479
    0x10f05150c030d1d01020a0c0c08060f0a1a12070f0e16210f0c03050c09010203071202070305070e0907090608101e0603030309060b060301031707030207030c060f020714030c 76
    0x9428101c1c613100b10312148400e0300706050b940f00041904045400034041d0241c2c5115120120710250749803080394490b0000c43d22803901e0001040018043e040381da0095420341c100d40f0b0000c040340081000b040340b58440c60445503880d4003c600501103058083c40680c028110560446001d203020100b0b003076800c5403003802d102400b0100b0401d00303844800250724a0070f503c42017810000050280e1048002c1c003101c80710b0101181c40e002c0810106c0c0d400c1021036003101c1c1c06030000c40c40d01c0c0181d03aa2500070b0008150140440c0504400840020300c24401c000081c02c800090312100c0c01c040e00d641e41011820340c4031141071803070104204466030f00885c0441c0d1001198000107420000710310000034004080c4c1c0e54416141c076109002c02010f070542d00000d2600d0255a04003d039180d0a82801910b11007030002400e0540360054034410080440001c2c0801c3d031183c0f0503228029907980e65104034807481e4100d200801c030003110b40021542e040003030b60001c02458441c4440610100d0110ba1140c904000c0c46 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 922942976 1250 922941726 922941731
    0x90616110c0405040f0b07020706090e2a040609060f09350a0302010f0908030103080c16030c030201080a0c050414030f0a080306011b051023010f05150c030d 69
    0x248103810030300007001001d4018005114901e03092802c1d00407600b85c42c804031020310800d404902c61a02c0007454500352003168480c0b02ca80784c01c1c080c10404100b40204002803e01010400c42d1246101000034041c1c0102c1c0040e0303980711400c01e500030300a416150010b10400003602c03041040c29170302840038002c480540002200034840700c09140040340040141c060780641c2e00c10070701b207907000001c1c0300811140680c0c000c10048007621162419100c44901c00ba020480038001400400c500c1002840e01c400d02e40300702c0f03890544584004017140c01d10b80c425990307030b6403c0382d0030400d558116028562244061004000c000400301c0040c120303000e50b0007003400310403410341410002d403000c002070071001e5500800c0341c006840344c2c58108215801103c800d80040e207010b00e02c6002031100b100c01c2810341d0303000380500107000144403968000c003a000c13121000703030300c10000440301d1041c0240442c1c06001511100850b090074907050056140b01409046104a0708001d40002d4102c0481030711190740050802 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 922944226 1250 922942976 922942997
    0xb0f0403232a151314030c040507170906010303030b0306240d0501060e01080f070311010f0e0409120e011b0b06010c080c07080c3001020c100f05090616 67
    0x80d090301440441c071080c1c2044607000c50b9a8515000b4024290141000c6004a41d83d521203611710f610548030004a0380641c03003589041d42c40d20703103034014560141d128603180b1098120341410f1346181c00c041e50241095003228006106043c0e140c003034460345840035801801c0c64249260b496408000c21002c0034040c1450f041184060740d1030140e0315003550b030054000e001700f82c2c1f240c440342162407080c40754403481e110301051402c01900100c1ca10080325007180c80c42900d0100326005407000c1c000c50100400b0000d500d090022150f886d8030501d10100d01440c0b281c8010346030454040c000810801e64141401980c4420580d289400810701000c0c0f40d00454850241c1c60b0301005862034440182c0c0142202000b00d180c481a21001428504a868050031030f403110320704005000001c0c0d00356241e003027101c0644840e0b80d0741e000d1410244110034281c5000501e04002810030b181000f600c5d203c0301c5000c54584000d0010035040340680f513084002c038005030007241002c00c40490141031481c002010303c43c21508 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 922945476 1250 922944226 922944283
    0x60304020f04020f180a150f052803090c090513150f02071a070918020a210b13060b0a0c0507030210050901021519150b0f040323 57
    0x40c2e4554036000000c86855624101003170440b42c0b84860064042c40b003010000a03084103000c003e61320075070180c075800083c0611310350440f00c2d5071041a01d000f08849e022902c080c54a11591890640c80e0160340002c0c0c400401d1030199510304541d03104111007418031302407004014203c240201d120b40d021112883d2600b44520050203025801c024034112840414400140b200104518500703003c120503001043c0d44901040e100c0858600513035061048556440c40700e008254014255610310741001c10010106030041004101d001d8140b400e071940b00d0980f00c03002d04291400041612600006100c081d00b401d03076103c028091510900204143c40f9069400c4c4442444404081d640160208414229045010306241d0000078068010310401c040d0b9a11030300100026405802a03a040c42040e401c0c1a003050041d0401c90004801110012300020380d8002039001412814140c01410b0344651460070409000c007a00c80749034000d8044041220b0740c900d00481c010121125840e941200c2c3d1070040c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 922946726 1250 922945476 922945481
    0x140a020a0b0f06010f0201140423011b0201060504090807031421011401051201030b0603030f04090f0e031201051309080d09020405070314010b0f120a0905010b060702060304020f04 79
    0x6000d84000a0070060051061144800e10721075a0203885130260b03180400006c03800c8501030000040c1d030100032008580080c500c80c07101c24060401200034694050170040c09030844410a4048117658003602821600e20340a0180b00c0017084100c908100c1c00301e40b42c480070558868558002c041159451400c0072040c454810f0311001c3c1c240e080031403511480200c101034400f0302809441c03192541da13007141c41558410022175403649280d01520806900e5503a8034030400c20041c00d40ea82c10f000a000300100354040401400081c4103220010409500d64100c101c2110400c0c5000741040d08100469081040300042d0241115803e445058000b5541c840260041c211000010000c03100000e044009a03103e400119945008403010031654684800c00d400f101c07010800e0701ca011902000412004182101030080c41340101282c526190000170300c40c01d200d40440d108441e461b40c440c0080b05200c0c003441441010401907906525040f0250000355039800000d00003813081801c1910904651602d4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 922947976 1250 922946726 922946743
    0x30605130c0605030103060612022d030f15010e011a0a0e12010207030908030310140303190504090c020627011415181b1b030f0c0c0a06140a02 63
    0x2031030701c0360481c2c491500628a520a20059840c03030b0401c407000c284820b442500b003940541c0104119682c00d80712518407007039003204040760904c10040b0401035060b10305010084403540c5074409003850580303a4100490403501a0081c607040003841006008001d1a988004901c01c0f260300d4030358445583c140c0442c0c0604021040705c3e00181c58154004044c1015006030444034441d03294100e5903611200c80d42c0d601d0108848072a45c610030304500b01f000406045055107400005402d0300c0ca0500e00d48603240f0300e100130228850006000140420002800748141d04101010f0706c0504114180800407000b41e00c488942c000c61101c808541440c407030750035404034003448510b40c440103071850482c1c08917240500350040705018032090900300001c0045150214032419401d00b02c04402919a204130404d40c03c0500d0907502c1d005c1d0070113400c0601400700f0140c60320021a0000954402e0920382031810046580882802080301d030000380a41071308106501840041155882d481d11072207841280b902216 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 922949226 1250 922947976 922947983
    0x180b0c0a0806090c0c010c170a090b130c05060c0a0213090b06010f020f010f020c07140a03080702030a080304060227090106081012050312010e04200d240507020f0703060513 76
    0x803c1d80c0a2100c079049000c0c0f0b00f9103403045d981d9802d10780c0c444481c89c081e2085150020060342070321001400003602480c542e1003850080c2c003a41040c68448000c02d0b000d034882c1e214403505922030308142c0300b14a81043c00c074a444480342c40c14070040065a403240705011014051606220a036200d25504501c20000d00c070340c00d01044024010985c07814080e40081d40003105502e2580610600412001c02c14804000c0382c1c0d40140001e03000c289191241b00c102d0300316001c102d0745800f0321000c5c4000f05941d0806140103e0090100603554848203c1e62202c0241107080300210f201d642c0c403c0303030703550b074a070103803141124003508050995a958510146500115400c42c1111030000c5032110180840040a0900c04003002d4844000da62208007001c0981003c035070050203800c8c4070700203c1d8030200d52003150001d240c01400302e0310200300c95500d4041d81e0740031080081c07400030345003010600c40510740241034006546002400c2c6090864864a0b01d4480c039000c05401282c40e4400300b107074070040d9565800410380 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 922950476 1250 922949226 922949231
    0x10b0a0e040b1803191404060504091d06070801060e10360b1e032814040303050a06050a0503190221030408010f1109010e13180b0c0a0806090c0c01 65
    0x2d12011211030080c901d4403400240d00c20021030034005a120444041c0c0783c01e5154681005c3ca00403080010b0600301800363310030b003091010348111600402c80c2c3d40c0100c0d0a900c40000035810130300000c0c44501c0510a49102d8090819441c0321181c2100083c0381000902251034220060901d074917072081c807400c855404000c400000014100d00030000303401300c0c0d00c40c14400d907410520440b09107030601082d10740c0040d42c12a40503201c2084800d007000c0c004602c0407070f80883c400581200d1903480d82c404403010380200351100e080054004581c8a080c000c2d140494078142c149003441e0129030341c2e41100000b03100071041044440255500c11030310b0041c001c00c0c080d042c07201200b86480140c5030340103072194221035800c0028000e03054a4900849050300c002070301c95802e1280c0d64004555102c1d81e0b05100b50040031540c142c48040009026203888074a100c844040c1c1c040703040c600750454290003802c41d8030300380003070207690305082d800344046420600455075010a504d03840b0303070368800744a4031011800f03a62 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 922951726 1250 922950476 922950487
    0xa0c0e0a090c060314090c0306060603041506090b040c0906050a0c05031905121018020a12290406050901090b030f010c26090d0822050708010b0a0e040b1803 69
    0x40d4907410080305c0364002203502c96143c49602c1d000f90740344a450a01a4580c019800180040c04c0440142d0b40c03250080d052480c144040d141c840c0e00705e81990f08402800b030349030030741d035440c2d4107050081e90448201803502c541d0840ca0107000070014000c0038074590400808820384424806c040003a544840050880e0b2041030324032802c041c0c800c0c0e10a030324051060300005c2c001410072001484480407214000310403080700300300e468010000c0d40701440d000180021084c1c0186840c20500c03a0110b46d0240d02c1280d1000c8a03d001120190b0748901542e1b4496410010f09100301d44502242ea41140c4581901003103e000c4100040c0c24042e1040206035158030300400243d8269000401500442c2000780220f1140d01503071003c00e034424100d5070360006d90711242d82d400c4ac85108010303160784520280d041d9000201e0350900d01c4040c2044d540c040e40c840d0306c01d007002d100b0321030288181c14000c0e0701221200c0c1c3c2d807498110a2005001d0003800a4012010ba00009108050203540074046031030003030640347d481 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 922952976 1250 922951726 922951739
    0xd2c09070309060e0706032d05071e020c1203090d1518030804021e0f09060301150303110c040924021c02030f0109180b04080405030d0f0f020a0c0e0a090c 68
    0x90b105d504c1508006030a1481c0c40200c0b18120303903000107642d400b00c4980c00641000c4904805064041c040ea0300b0040c0d6a108200500d00b420b405552815044d4003130640311b03101030b04200c03214611894000a0750020440001e082d910702e03599003803090340654a4080200b030600f40b003000386400101c1e4994a84a19840c00030551701807031440c440c40c822101c4c042800c17034051b2164a450b00051282c0d402c0b80090520315918034050307007501e44c400b00c001c002203100c0d0600030481c0f6880c1d0f05036004a005c200c10380665002400103200c4a00248010345003008030003119211a66603518059032561103010041c0a100c2840440d01103808a0040122131080000c4c880142e000952007142c07043d15407030a400000c039030080e26010700c03222641c82040c106006a0542c54092400768080e00480342a43e041100280072340301404070801510040c2c0700c09a41104d1004c01070302401c224080b1100b19000000444009132280d0001000ea80b100941800103a40e041070160040c166840060142019002e0010b0308 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 922954226 1250 922952976 922952983
    0x13020a0804050f060408040311040b041109011e08010b0307090807030f02040b150301090b06040302090a09020a0e04020d060b22020d0b010e0904320d2c09070309060e 73
    0x924840d2085503807400d80010f100b40c50384000d550080403032004110810120f84071142501c02c04c40c1c001d00000d65100703900c00240495410213090306410f034020510004641e0498032901043c080c469a5800c01c00c13811400600c0d15205024001580b040840410b03800781c412070280c4081c299480071100321341d403a4249000032825460b4224407035406d110703905159041c261124148184590042402c0d03909246040d806444407201181e045481804000003503924011554010460158001101c1030a401400701e83d003a90340040c091820b414040c080142c45081c5404d2080e9003082001035000c0b0944005003c2103010000d021402c0303203000c0351280004d2030303074000e0901e080185810400100c01000546a15481c0000c82c1e42c80202400084c010800d00081144040c004060383d807450703807240381e4400380003c000040600d02d40c80303a003482d508940c01c1741101c01500581c034500007440485c3c500c002d2204030606081e0b4041d20740720011440041c007d070400081203034407500134400450718580240c6d0303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 922955476 1250 922954226 922954231
    0x10c0507121a071826030f0d050108030304031202090d0807060f1a0a05090c0412050f0c010507021e0f0a031b09020c0703062309030304030f0f0f0e13020a08 69
    0x200c000082e0125100b18090000001c1c0200c080b8400ca030860700d44080d4460b02c07000510150561140d094070030365400f0090000f0207007032046400182d1241d103105498002c540050300911403540c002c00502002c01d420001440d1005020440943c7d82c0c5840004a05281c0d44841d0041142d40c01084080421581e5009418441003000c0c08120703900261856040c1642d80004090300001c0254003072200781090341480b980810481d6482d45000c1d55100241035082541005440340d1b0040c4000d041c18000500c0104510031091800e103040c49455000502c83d02004520f550125801c40e5052110780c407800065941f5450080602c0c480d540d880c2004d20401200c40182d4911200d42280030400c0781c039600c01d84070305003440d000510380c20307003950748090040c00c0440e4940321032400d66a00d00700c2e180000d01000d114a58041c00b03142c0380e05003031a000c3c09071564540d46d182400f404050b0f2030106540500c156032980040e107020a05124003402007600c081c0440300c410213903400001c41c0d0f0001d030303000040d590 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 922956726 1250 922955476 922955513
    0x2d09010b030d0504030b09160b13060201060b03010e06030a1209060201180c2106090305040306180b0601121d0109120804110d05160f050a090b03060402010c050712 72
    0x400105034004040c0c9911440001c0c0d80812001c1c0018400b044110110f19400682641101e100c840c1c6500f07554610701c2d440e40006030140d800141e40320340d201d07080400c40080a0a00080c058241020300e9034865010500075032400401850001e80c0c1f640d401c201841806070840761203680d0040311075004107407417580d0060350059800c00e02c12010b1507070200e0481390041e0b00080d9030b0401a06004101241440c0905d02080d0188c01e0001c480202d400c84c8140781c180e034880d031140b680c0d81e455171800c01c1c00c1e20106103654040c255400300960118030b583ca05698003c038240b07001244800036000c003074020100a640308a8204c8000d5100491030f80550106851502030310401b2442c2d8041442203070100422900203015040310002072038141002803002071aa440380059030034500b02407500d009410300c15802601404c0700d0300010480f03424480c05800282406090610038981c540002c02d5944201510083c108111588120103100051207010702414408000c4510721040d400c0103404c8880402891 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 922957976 1250 922956726 922956731
    0x1413060e163c05030103020904020d140d080a05070302071a060d060e030403030e030607120c09051801050907030c0203091309050618010c0806100e030f03040806090d02242d0901 78
    0x340142e030260095a0480394010701c00c1200b81e40325404c0c441d545410b0801201c807404050103032103085c070b428000300c032101d002561071021500d080444407082d84c50250400090620410003000800c542e0f081420800111020070718550b20fa21011440130300d440440a4089403402c0e02c60500e8000c040f000f00102c90099982c1101c84030700c4020991103030b50a94491010034480240c15003410501e802c43c0c3d40100050504620346a61200498070000120f00501210602e54005001910b08802d185400131b1407403400f00600071400c1d10282d034a1061841d0f85101d002c0c42061180e140c001c541110800d164800161001340c1015001d2980c1e802c0c1400e945c11195080a88107048180300d2240300b0703c079503801020903201c00000c20341520102003195032950980030708550360f030b00b0490400060005120020080100d49040c5405030b060100c10555002103410140d002c44810b003151010560100040c0d840c00c80913112500b865480b0034401c42500d0502651100380221a0300c050032280c0f18201d118001d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 922959226 1250 922957976 922958087
    0x5090a0509130b07171504052a160203070806150906060301090c121b12020f030601050a0e03060403270302061c060e011413060e16 58
    0x10408101421203048920000340140040400e01c03110980e50400342e9424407032108200c1040b15041703c401100c140611400304420080142018851143c1c4403072000301c14129000484080e1608903a5241d4041c151107012902c01c6090f00c0e0181c01500e0030383c0c020221070405984000d4561111000c4400c208000320301c281290311803c10f21340091003010700402d40c0d0720b540e0800208000425084080d1001c1201203400000c05040c944200711560800e0039920180034035650380200403201542c0c011850b640188051001c0514280603290040d4007403c1554071104c07400c0b021030f0b400019100e002e031705216000611082c50f401810703c010350306c000c18a2072060340c28480c02c051780300b019100094002da42040311021012058030700100b500401d14001c1180b903594401e42044104c03e800141c10404510182c2c141450401c20f0b0f40d02c1030320a03c00038007a070b034602070004181c0307000104504110304070146585496031003074441d10318030a091f215500d05100d80801007107210602d11009202c4400e14100d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 922960476 1250 922959226 922959229
    0xb0a1e08030a200a060906021b16030209061c060501051005070302060103060c0905030708060108062202091e0f070f0219081e0c0a021311071b120305090a05 69
    0x888080340401c0c0c8484031184024800340d0160720070f56100082e035004495901c00051403034001da00c2410f010f08400750702c030b0644054806515003c80351040490307000200c903074102103601030078004503501280e01841554440300481d0148040088000410440c081400200b00b0107910180c1610750540b408000032000320016505486680c030081c01507807000c0010070014000303400184912001e8a132522aa41c1e550011034500100e98100d0262a0014401070014002c100324041d40202d1042c01208940400310f9200c107040c841d800d000e80200000000500d4841003014010b0500f10000d150381c11501d0000215611460300344c40780b000140d8202d22035012107100003030300e40425500e00780411402c4202e50b1146103d42c011600459030780d9101012122941c441c1001c2d0110841d01300241c500907c0754410401441810f606501804e0300e0705030720800d16506042543c10386a0f2002e60750070043c16807110448a01940e5000c2c18802c185141c0220416501201802d00c080d8141c5214003501e442c0c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 922961726 1250 922960476 922960483
    0x19060506070203100c02030d0204060302030f060402040f090b060f0c0c03060c251e0323031017070302031c111c0c1506030f140a080a050d0b0a1e08 65
    0x2c0c0d415405694000d000c3c9140e607101c04102c0501d40102d0345001c00d8030915105a8120ba481000460780c04810000c1c6502c505202c6035002204403411807078203047c2160420750b62800d00841e01c00c2542c0e1b2500c480d25403507140403034903d409003d80845d140c1e0f4002003c0c0341d90b40b85143d0070034001c1c0030300310101e627000001405a62458008004d44941c5040600e20400c04242507102911592120540481d00280d00004602d0343c60280c0c1d00c110740e5201c3c175091811140c5d00e0a41010003035a04008102c0d8041e040e0000030240c0e00310031100b400020171580407900d0004a904048c2d8180a180142c0703200084c42c1c905221144041c0d00c0301600006180f030083e450310203000d0000b07500320702c54130040c020a1098400403401441080c5c5107084040d0318210508035081134004481c2000c400034060b003405100c103070003c01c01035040c0041481c20b10685c2c0e041300b0760040c46421030500c03401003000c182030303104c40d00b02d100700343c07009000d03810b04641c0c904032840c044901c403004221030407030344402090b27269011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 922962976 1250 922961726 922961737
    0x206070504051002120d1506090e01060309060b030d0503190203010807140a080d18050603040302072912070e10080c0f040503012c070608060f0102030705030319060506 74
    0x5403161800d00b49008103100c1d051141c00d004070114000c002c262804980044094441c085400100041e120720703042040921030070750303003080c01401a40407040102c41c15690f4002c0c1034070701074900412004100d03d400c0c00500744c025075650303050080c4101e02880c9940100511300c81c80300117100c80d600d0311300c00d2220b00480c1300a000e9441942c1041d001800504a252080401070001070000300a0507a41c22120b801c003080c030000d41e0300040f080264034130040d050311180c04c06443d08890441c0740d41815174010755502628882e4038248080c1030001403500000d03030244101038100794100b035a00d00782184510342e4048203c403806e012605445410620381042d071403144138402c05485404070390719038580c2805240c01a248540500c2c1c802c00c0003017042d443c20f01548144690080f4852140100c403e042c00d4982c402400385503441d031080d1003c00200f54450380440d000b06064a511900d0422880100e0643c403070780c9000f8105100000500010030494212804001015a01084001c0d01e50003001402c0c860b4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 922964226 1250 922962976 922962991
    0x309060b0418060903021c020a12170f04140f0a15140a2c030304030f0f02031806070c0f0305010c05030708150307030b0a1a04020415140d0203040c060f0206 69
    0xb150364080c0000c03400d40c00010b00d02c2c0079004564000400c0007007200c614589400c071900580242a101007045032a0303011100100321070401141d44140000b07090002d41c0d0003000c1034200c0722881d02003400d0000303081443c540302040c101661070003c500c41d21981d60b001d81b82400c603005101e203640098a110f0313521405000c10242450501140c86611440d00a0b004400c0e02203001d15800c0c5584084211401d50100582006d1000e9600ea191a0601400c5200b0002c110307014400c1c2143c002410703079404021a280950000400702078101c2d41008181107018100c401001c21520350f001040400354040f88408407031040c0001c0c413170b58100c001e084840b4002500c03000301140900300404e14486c0c3c3e00c00700c00341c5c03a032003c0c080710507541e941e403a9200350034030076075403a8803031036480d02460807841d503060940c1d804100981741945454600451038150a162810a02c00c008120100000a140c1d001c01c40e0380c0300550364401c0d901c90038241000c2d28030054501c500400320300754900032040c460000c0fa120303204051 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 922965476 1250 922964226 922964261
    0x2151b09010c06060518010e07030e12070606031a011806030507090b040902130c02010e07080c3c10030b0108240915120316031805100309060b04 64
    0x55001512402a8160115085904d44801203030315103501d0150300f402d40f50508a44003075403503d0080e02298074082c0a4404050900b80c01c52050040011010868540300d60303040e50319200c5040032801803415030801441c51509222110241040309c0d07125060701d92921401c1e80008416510800300c510170300c0000c02d66081250100404031042d4008048400e000e480401c0400041e030000d00e49001d124405c0c2c2c41d403690780140800141d4248198542148118000c00b0644d00300906140d8400c49444018850007580c005100d0440c19000342c21505000d800108064034a92150041100c60034500140540d4401c4400c2031503038824010101a07000684a00b00507403198042100240314807034200d1400040740c0d21032202a141d00c4002840346410f004103c085540150420400405040d48400709501c01d002c8240704c1c849440700c0343c00b442d038141410400306408004030140c01d621903001a5009288203181c1075520340541050365141d110b481c007084641c1ca1380c0700308000ca40c05082200c2440d103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 922966726 1250 922965476 922965487
    0x31051f03050c101e0201091518020f010309051504050d0318020420130503010c09062a0c03080c1020090d08031305010b0d120f0c08040602151b 63
    0x9008000c1c0402c0840d920b00581c29107403e52118031200c44510a100043c0e640e91f00100502c20002001201e0082c4042c090000303007000c484000c040860301314080d05c503120228180c55180c1c003903031002ea06260302c9001ea070314160070074009820b003500c01c4030261018000d107001e04015030f1107846802701039960ba0081d01100316464003488000c00c00800341600002e0342e4055a0110350002c0083c20383c0084040305000e0060406017418296058503c00c9824400c0486d41032280940101c111540c3e04006011071406290541c00f22142880300c1d040a010040c08501c0442402500c800900112070341c04101e5030f259002c585c16008a4048601d02001045031360310540518914074010607460500a082c008520025256002e0f158415140340701244a54201b0004105080c05000b40d0000115016401500309440383d100c80644c480c5448100324020501d80b640e5801400c1e0620001d8100304c045807038649520010b5a900c068103043c100030703c8400001980c1142e82d01c007031072800c44520120750400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 922967976 1250 922966726 922966729
    0xc01080c030703150f08010b1203091528080f151201020904050106020304050a082a0607232506080c0d0e0606090708041131051f03050c 60
    0x41d04040c00c0c1c40105926050f4064046490419000c003405146580701400342c40c00205030300311050301c6100e40c010020440c07200d801000c08020740e92102e9040d5410085110084104007141c8159030307115005e2101204c180e140f140c40400c1d401209000754503074000c00d80b540300c801000c14004480d04445030410a4076006103003800b00c9200b003200b888800140c284281384e8000340607180240c00410040e440410208000c0c54515607040041640c0000350080d054000264152807004c1c2000d00d110a240b900241d072140c8a0b00304031201c407908142d01c0400010614502101005c0d1002c0c40c0c4014032814a240403e8035401861100110305181c1c2000d041d49003030700c01d4586020042c54074001e11400e200b18004202c0034000d14460b4803140001d81483c0c50840708201481c000500850104601001000b000581c5d007041c085803404100c8015560003142400800280d00d10b00840101b420070424035134608465030016030040070707040780561000010a640c80341c000e0b2b003884080e000358410038010809 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 922969226 1250 922967976 922968001
    0xe060f070f090305060c03040204051602031e040e04060906050702070819020a0302030712061b0509090406320a02030c12130b09030c07090e0703060f02130e180c0108 73
    0x4203009030501d4141560f80ba100c0394200f0000701c82c0381250320400410081180351030322840758090310700a4034840e02e600100d0002d54900a22040050341444195250147c2c1d1004061750010010b82e07950701902d1400e45030240243c0441541200e069083c20003181955001280010540300c80000a0000b000388000034039425a51120a0b07800010720040400540c400b4498275000e44142e20601ea11030440d46070002c00c50f00d610001500180ca4003850100403580081200c1d0102400c0340c06c5a450707104e5080c4a0000e06103620b054000b40040f00e6102124120002c01041c0c281d01d4102e80c1e5529074415003d5010781c841110b108040303100c204445514500840181504584005046403d0f0400f0ba80c1d00c24802c01306580100040d8004106e800e2041030411501d4064143c502041c00003510600180d90784940d40e000043c40243c694111242011682e410b48400c23406e081030014480d0b0351100648224801178650790f900d0301c05409a1194001c001503a10240c01041c0c0d6054555a9004e580109 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 922970476 1250 922969226 922969247
    0xc0a0b0f0715050f090d09050d080319020a0e01020c0a0b1e04030210050c06160914060f12010608010b073f1805041401050607170708030103060e060f07 67
    0x101c8100c220039405403210140b040384e1203610080c898000b24280000004d19100441c0c00c1c0b6000c00c9031a0740c0c18043c3ea11a041d0020185034050325080c0c0726100c007242e07030000306059404482e0582c400304604004990081c9c000c550940282c007907400c0c0d0000ca0041c07041d02103c1e401011005d1b002084480d0000d02d4ac00140e80001105020090800b80c980d030002d0f0300b010210f000c2500007403000c640c0c0c0c220070806104254119080c04100c9903100803103400540004600d100d03142c10b2010b6800048101c0d2034050840c1d590200001507140d8a980500781c00a02200a008410000f03100740000704007a130321070b8220380035241c00a080b583c00203240c024010010658128842100c09220700304041d1401401003914012090f8480461910400030351425100d1540d228070f2050303050800b56540d031480140940c0c1560000d654407955030103181028030308038083c54041081e210300001d0307020600005601850580740f01d03070018043c1c41324841701c40b80d64010598800c0f02c607072a08404500c1340e07400307a1001c20 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 922971726 1250 922970476 922970483
    0x91f06051c08121f060e0f04020a091e080f1605060d14040c0819020109030b1e011d0c09090f040201031d031e0a08130507091803020c0a0b0f07 63
    0x5141001e5150050f22201c015070380c16200380455030240e102c1d0030710811210301520080c509801d41e0054100002c914000c2d0000e024080c660009696020a05c1031001c40090100c0c03201c4821854003020060407210454840d84800d030045a5013203440c40d40100e140d443c0d107154100b11050f090b04213000c002440d07002c40380780503855551341200902c5c21410300c0d41034880d5001d00042e0070712615022074141441d040303203200080082c10302c42000041c1e0b0440c0005059980054008580d659907005180402107030070510040e054091000251201e20008070030b05400e02030b00000303070645940050302c0c414000c2e40c0e001e950046d400e10004081545031351050f548a40140341c08902075014006e88504121644002c81c000e402c001801611048e0061441140b10b100da2156450180b5001d001001c1d40006810030a000c8000d22009052041c100440c9000d456110020464660034083c0701c4411841008210094060701c8900001c618041494001302c0d8480c002d560310b400319481034540240d001d140d046 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 922972976 1250 922971726 922971743
    0xa0b090705010c0b072f0f01060501120e0c03060f1005180f09010605040216020a0f05030607053f0906070e01031e051021120804060e06091f06051c 65
    0x4124400e100201001602e50804090072100146c003d818401c0464098000da03041940400503642d0112410710951400000002c030304211a00660600c40c44610040e45881204184507000e000710701d0840c010003c44481241c400d40d1201401410b0015031035504450305450001445068100d10040c6d0108074080001220754440000800300e812800701d80f815001540361000840c10319501d000040d240a000111100d0302c0c03c0002076903554010521802c02401040d103410144c46050082c0001c410501e0b95442c10814480e0038454030b40316520480c400b4994404207c01590201324203000d01081c3d56219080ca02503001035004e010481300482c416003016220000c200002d10841d4060380c102000040900c0c58011007465090307801000c141031501c52004980056a21902444807140c0742c1004200741d5914108134008101d05d5014103501d00a503400c00541074004a0440320903042010b049502d160089442c0c01140e805000c0c46801c1308140009140b00c4180001c058040c40c03040b6400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 922974226 1250 922972976 922972997
    0x51c030204180911210601060f02010e070f09090203030403080c0d030b01110a0201081b030c1305120d14070510050105130b1507020301020f120610050307051602040605120a0b090705010c0b07 84
    0x20341c0c50000d00341d010a001408927400e0031a030550a014107201c1c20000b10007400e0f0700d07003004c848a00c880c400d4032400110b1541c42c6d103103908544080c4292001950002c01e4030361120041000c3d1511a1340311540900020328140040f0319640c05180902c2c950704003e07008003408640c680c0103482080c00903101510010844041010015000c402540304080007204c03a600c605125290071141405a0015482100319018420311104005505095280c081ca0103200040242c0116043c43c4145000074100d806681c102c074100301c1c1d03180c200c40c2c1210421390b00c07120681c88400d07001d42196546580581d220150718003c406081c00100230340480741c0020001032070600262a40303003181c0d21600041040748115002c0000a24180c0c507000070b00e402c60304025103545003800c4010214410000d01500200c6019004025511690b109401410001e41804041140b54a415030785210812040303902200600000f6046440414130b1004ca400c10b8442c005103e030103a85580b05404010049020845860300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 922975476 1250 922974226 922974289
    0x120c0e103f030516140606030304060c171614100b030a0320010516020f0d12020711030d05042c06150d05010b04061d010e0607051c030204180911 64
    0x444da84545003850032a54031846103400c0c0748004107050701c40d800603c401c000264100c000200c020b075009802400e0030740c1d400070711413450040000d1406d030b00f11501c4140b4100303d04400c0c5a200b41c007021046445840014100e01c090b83d400c5419503416400002648000a000ba070410107210103070040b0703004601211080a003110744c103d504407010202818040d4072581c061051207180400d8602900004109020242101d407074058113030003840c2d00040320707018450710301101c072941a001020f445402d00f084e0070040c03064110707015280759155401c0c10a0301c0c92030305e0a0000110381204685c03200b03030f91318082005007102c1c41800004004074100030301d00400341c0c144980c40c0648008035180b41c82e079040c88802401c01d07034600e048422082e071070803000c2460780e0001100e20084000300c2da07059803042c1c1031074440c2c24036842e0107030041c5424000600303500c007541580180c4182c0c0c841201c00c400040004009405a680c0140090441a127003441009203007001c210342e41210340120b1000202c00305045 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 922976726 1250 922975476 922975507
    0x60a121404050c0a090c05091e09010b030105030f150f040c030605011d090102210613020d0c1103040e0703150b030708070207080703050304120c0e103f0305 69
    0x220102d600d074001c0c500a8105207010300c40030f07000d003413030700410031600d400d206000c0c1040c8201d1011038402c1280080381d02d0403c3d84c1020301c601009015055000551790390f428003070603030428001e06101e806140000b062a01d40041d5001c8581c1030303111a062152039401c80c280c200c180c0a8400d48c0d5041d51024048040b4010740162402481e84000490000c1d0031126801d0006102a24403081640104072080400b00c40b40e951502807103c10f070502c12151074150010703031002d0491003401c2006001142c18106d400484d800111031240e0f545130481040c0c5600340164903072040d801011228140540400c0c1d945100e0340c0402d140d4450029540422038881d1440300d060b800071120b9100040144040000296040c03007110024a10000200700c9941540c0e1015124080e90007084007900040060b142407000c00021440200107822242e0040e0800981d400200419030140205548000040102d246c02c000c0d960b004129402d0188110f01c95803605543c101d982000080e801c000092200d0703100343c107004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 922977976 1250 922976726 922976731
    0x1d0f06120d0f2d0305060f0a0f03020f1002030a1b0b09520e010e0906090616120f02040f0509160f08040c0b0d0509010e0c060a1214 58
    0xc0e00d8003100700380c0700c0c2c03401000e240e0802e8031505040c1244800380c40d8140c00510084540e0700600b00411076548000100d2004030304a107076154000725000002034001544103030001075900a0312a1001e40c54014240200b200490040c080164000c22880b621584151070500e000d681c4005da80041100d140c1f01d545c02d0041c162020300d0316401c42813840701c4100701103004449a900802010040c849194000707511241040d03000d40b0400010600f08400f621086003040c09050185c24404140d610386014590122045481c09041d22030300d4040b5000346000545580300f2a10b0a6100316614400700085074801c0c0314444d8111341e151200d01c40c031514980c0340003400152036058421041d1324580710400148104c0a840c0c0c0707031206180d0000700c000540c0242541c40d00005c908080c0c15640b51480c09100d228810b50000c00100b40101d0801550501d83c1c21850040303206038001c0c0000c0c04950000d0742c441c010001810351201d4204030a482850003076803098005400c0110014804c480f520234054910001c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 922979226 1250 922977976 922978003
    0x30060126070e4b0d0614071107060f03021306030c030b0d0b0a0908040306090f0c06030b131d0a0501020405010f0f1205040f06090b010305071d0f0612 66
    0x10340c00d0420b9080100e012522074041c0c01164426441d03c11a00c0d042003000d11000502c152a5540a81c1114030098442d01e203580282c482006001c803401d040d0010440703412000160171600000c00c1c252485480c503018408041ea019080180c03a0600030741d000c1500b0b80203070060580074405221054000e80140d0020b06050318041115010408010204c80e10305003034038450b0388110b0650006c1200610420341c4000c03040800147c2034002d0502061500032584003d000c641003081d942e0422510042030b4201d144199617103607a0a4440b5000c1e015144070110306508600c81110001d2103c12070303080034503115181d82405460804602d41c103414403e0380c910540c0e140c1c0d000581002039583c4040111515082c1c0c0c54003011261031848000c02400e500e0f0050290b65403208049030a00c001e041d04480602d034400f03410840726a26280010408409100c00c1c0d03020b00840d03c002031200846113407080b100302260740c14540383ea15541c6103244018080c00041c2c205c0c0f10324443d1000003400b000310145e801003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 922980476 1250 922979226 922979237
    0xf06060109060c3801060203120c030112060c050c070602031911060a02180603240301020f0a052a070f060f0c0809010e153006012607 59
    0x14424000740c085070349584480708006051610342c004c00c03c0303188021182d124810710000704041048440d800c0e18000300511010318020000098003940010042030f0a1038002c20404841d9141a110103141c0424414820400c001c0840c600000300c80f503100e154441a2400d119052080303082205142c64030b243c020001503480080c0c0e4041028011001820110703280c40d00300c02c580b84050007241c407000060401151941c01242010745400700c01070440454401506068491504180710800302c01c44210124206a42d440103408508042c001c0b03c6506000d0f00768240783c820700850440d80d5500000762441c200c2000145900541001078004000e09808801001c00d0360416581c003404450651004041c0603900c40312102840d0019442030405030410100c58880c159200146c541403075620205900290f903c1070120004c2481c1b015001039503442204c4000300501120a400203403e10310242c4085544000040041d1f100d01121102e10001862807004605241d040b41c00c0b5400c140c400317001044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 922981726 1250 922980476 922980481
    0x90628090b0405040c0e0702030c01020a0504050414070504050f060d0603031707030c0909020319110d1a130507170405010218010f0906120b0d050309030106121203090201030902030f06 81
    0x4480d4050360011036001c580400250038990750300410300a5612030340c004140b1210008085d02c0c02801514070b800c1094009640d9104075200081aa034040d008040c03042e40b90819805400c044580418422003160300e44500d814200700401074540020504150310120401040506803001d00850008511070b0302c0d00c0f581c11000b0320914100141c014a0801058a050100840030303501a05880c2298805013005a49890380e002122002c00045000c001840c24141907290080703d81c00106110340c075004040022103000c020410f00c800c1c0d0388032103990241a562400c01d2244080d03000da604105c441c1170610302c4880c040c2c580d40c040c02c8200c07800c0d203490754003060200a03010030700c00d080b0151600b40784c22041d00d981c90b90302805054040c01001d0805c20241e000c81c00d0000240e01c42c924640f801450049200183c1c42c24666071fa0001501038004e5007400000500b50001800701c1c911a0f512001000c1042401c80d0101c0007420b030b00368117070704040d15003802c0c90140e1000c3c00781210034040b0102621051 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 922982976 1250 922981726 922981739
    0x6030203030d090303240e2502060109060f080601051c0f03031a010504050306040312060819060b0d150f060e04120306060e01120b12070608010e0702030a0806090628 73
    0x1210400c42481c004170030001c02c080603407241c6c40150700fa5080c40e08071070007588600e03403001c071125010344800904003d456280c400c020b8000444030b04982200c182444007548880321091188980e2060145550219006010320325025200d800c06801c002820a94150340341c40e0074510004055054010999402120a0780086849111042c203402e080003840d091400012036038a150090016080001800026004000341d400a074000c158407821150146003801020410555510085801903d003a0700c41c40079007085940030004d250030040e0604010610f40781000600002041c3c03000040e40d5446c042000d14000025030f000300d00900302e40803c50310b00000501141c449401c82420302403e2211080140e80c0000780741c241010006000c41c01c1094070f00418105008200c01c0c1c1c0380b07400741000104400342d012030342c141240c0d81c8407041c00300f0b6180c14200707a0b22841741d801050700195084000a00d10f0501002054004102420b01f480340395880300c4d1406100c0444205510358444402c00700001c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 922984226 1250 922982976 922982981
    0x60706020705061305190b060424060e01030f0501080303040b09011103010902121b18041b02030309150106050d021602040c05090102010b09090d0e03120d150e04030f03020c0106030203030d090303 86
    0x441554041000f01c4094070348687c1c000394001410303240724544811003007402c0c54495269181d00d05e810f200d440c0d000303078942c0c001414a0801d041d4460010f0b1620f561148203801500515040303c0042014515540300e648a494203144c0007020364085640322414500c003201c00ea40158001c0501c401e00580b120b407150800301c0311074000740c26840c2c800d03c45c07818951f05050000488000042040b1440c0b00c808100b0b01040142c40d201690840113112007070b00c0e8074115000f0008620480c40f0341e060f2264a0681c070b680d00354200302801594005181030040c90004161031b0700511000b980840300807560b046560010b4191140f024003000018800300f564071003035809001c0e00c3d0304002e04460904840c507120041c2d60345e0b44101e2500c0340c2007006007103031224642c40c203100030001c000422014580d10f150303a00032040a420850605003042074105d2000842040c0c0702a20341c00385038560350b0310b00b039030702000301c200d01035006100c001084e95a91940040144d070308100400702c6039030f034101c0429255802d0602408 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 922985476 1250 922984226 922984243
    0xc0108090313230303030f0f012903061516060c020a050a08130e0f0402090a0e0c01030e031b010e0c0303040510050a23030609070e0f060706020705061305 68
    0x91a03005010001c03405004861000640e0110001c20910300840011900074081d840c3c0d90740d405000002c103209101c880f1449280c42510588504034050f40d03900545903030320001034a118064204c05d52621183d1046c0402150000001000c403803104880d1260b415040d88005161003124442507110707410402c031402406407202541c0003501f000100c1c0d456440d00c40c41010b02c010300502001410f0301c1c50000ca1490b1401030404046881104e140094000c27504040548040e44502480400114404194050030401c080d00b20081d042d1103401000640240c0101200c443da24082400043c640b80400190726041c040d03120000725010010503a454244006903a111f4000c2e04100f04c107008030344907498940f95500103480e007503a983e0115401248c40001e80c1d070400328460442d0700500640140788002d9401020304582607500c64075000c0042d1083d10115104030b800210500e80c402e00c620f012000ba00c20346002d8013016183c14400e58030141000070803618080705000c0208207a082c07103010424440d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 922986726 1250 922985476 922985491
    0xc020328061a10050f1905070302010623040e01060308191b020a170703062a210b0103020906040608180a0302070b030c1204060b010e0d0f0b04031b050c0108 69
    0x101d22480c041483d210010b004041030100c00115074291808082c102c0710031038460600348441107900d00e4018129400303182c0580042d0300300400403075407140c0c2d80e601e0080b400104d0b42c42c03448400c80070305010140034900f00d0a130716550784000c00004220300d440140250881c11032012000c0c0d0f1203101c05461262603d01e1041003030560303a4104c0058403a0f00c50304090b40c16441200002c60070315020309207041c0e00e58000030721407401e00e40c01005140ca400b01d050300c410180462400c0240401c0c40032101c1c42c041559800e84d801c52615003080b9007850750310004240406141c05450030654201040d0184d2140e4019000200031008000402c081c0d03524a0071a200e80754080c000030106900c00035030320600360007115071110b00000891100c0c14140c003202c84003581c5c14852112498a07040a40c0106510141180030034100001c2c0405841c1140d440d110b12540034070000c900300b81c540c4421000702e100900413400d110408491450345c2014100440240d4461001000d60319175400c00103018040152010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 922987976 1250 922986726 922986761
    0x15100806030d0822031e030905150c130b03010504061a09010e130c020f100e070b070614010f0302030c0a03031e03022502041104060f0c02032806 64
    0x42001c0d50085a400c44500c12450910015212460f4209001140e542c3e881d0307a5078906550701e000c0640044a00315844817034140e03003c142001c0c1e04240c041d00d003094002482c94018180c08185407040e10b0596801c000c0da04040c070f007040388403041f00d0f500050b20b40240c540c2100c0031004115601d02806840041c26240600048008503002c000c86030b070280d080034905000540c4042991070f1120005801480090b05084c4803d02180b10065168284c440c0e4007011030003556007c0c03d0302c0c0c0b03482c050052003402c1c8000408079203140038140031091f00010000c544c419100d507002d00e89850091000b03400b8180d0341d42c4800400e486c5104241c5030894910742c06029543e0b0100c100b02082e0000b24000c02ca6181c40380402107680d50320001c50081c440c0303a0113400d907185c0700c0c80003096140365480140741c031178400c4c0c50030056030551080c3e40b0310900a03442080d0010b582d1700110212144644524074489101508a44044d8941440603d010f02061450680d003120713030842409020890040381029504191403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 922989226 1250 922987976 922987981
    0x100e010b031b0f0d020a0308030403050d05040609020a0e07090e1801090c08160302060906070f0210020a03180e01120c08010c030c08160f0c02130c05090a0f0501051806070605151008 80
    0x400c18459080c1f1003d0907001d400701c000b41c141401503040b50550a1342c803200300043c0c0703010302d0a0401020005400ea0090071060300200e100c05481c1801c500a200d95152600068036003500d80000400041c5462a150b06140328004108001d00a514007544180c01c3d1420b5a130500540350305e050100c900a1502c400a03500800150311340c2c2040301d10022099030425560704883c1440c4c0340c0084900c40080d04064004c002000c0240d001c10000009803107907884402e03034000c8001d03101c2c8a04140c058010035504410040202c2e00107081c117064150301c81c4513a01c0d6403694407400c40f421210181041c0d000310361038140c0b41e4807007980805004d0b80050032146c0d1900c01c0210500040061240030342c0131050120010704a000d5547d40319800403000c8000105100410105074001d2440d0013000905006010410000c20703203d01007004034082e1003040c0c0d501030401d01c00344e01458450014204141e0840b80c20400c1901254881c028540700304110450200c01b440410203020303202ca217012221040100c036109 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 922990476 1250 922989226 922989229
    0x4141b01050f0703020a0b251403070c020a030c06090609081b0f010c05030f040618080a0f020a180b0102070f050303070b04080c0f0f1b03100e010b031b0f0d02 70
    0x9841d45482c803025032946404032413134103a24110700000c1c064851403445042040c10301006004d01028042c82607600224802c0450945142c0c1d04541140e1190005100040c03015120b0001412451700040c904ca00040c1d0baa101c1e044010b546411083c00907807403210074801540c2060004004001c010000c0c000041004402d1186900180d40d143c03007038010140d0f001840e032103441006050354110007a207030307503907013900c0b1441d01c5a000c0d00c11480826040c03001d444403013007400ba6813801c554405021b046001c50039501c110481c20003200c2207034884540c0802181d02d0981c0202c0f4400c01084001c0010a00b051000288c40d0000c02e52000c01c0042600c00180000d85000c001d944501c0d602081516084e01d031480e14841e24044ca0744407051078400c182c000aa071b40c000040004a05101a00ba100910b584035204d000051007030b0107058250740700d00d45c85502c80d92950300c1364003840c0060000095140344000024241a09aa1080c0464402000110051030314040500289204859802c4000d450350b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 922991726 1250 922990476 922990487
    0x30209040308100f0618062c03100c03090506061f050304020d0f08040e2d0603070f14040509160533041d0403020c100c050604141b01 59
    0x40000301081803003030204000382c110f07040b004090081c1e03208680da4a900c90784010080ba5400201c45810400682d0000d03546026641440f03039000d1410072280f1600410b4081c0008a00c02e0080c2c1c0d4151240103003860f02240f031841190010389155802081c00381c0d031800d02d2840e244010b88034074424201c01042c0410796144260b02103680c0d003e42815601c076aaa4000201c100d50b0844020f00a10410f0390b00344100281d0384000c00c250742c450181000140c48000a0b400d101038000c01ca0002150721a1100e14110203981c22140d100c14014129203c0c651100807280b550740d0554403004a81c00148041402880c16005083d03001100d032000b001d800301e2924241c098825a8070030180940c001909045c4601000f1622002549a141030350150f0010000380c10120b6000c3d1280b4200d40714850745411005021460150266405500902d0115001e104000c0758550403565a02440f40c0d50a142c4006002801117510880c00f50789d0000c4082c4c0c981480b00d0a05990003088503082c0c801400d907020366138212 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 922992976 1250 922991726 922991731
    0xf1c090b16091e080303100509090102041d0408090d030806030f03090904170708040b0a0e0d150209060403021203090328200909100e01141902090907050301060216030209 75
    0x49a80d80d14100c01c0f00c4a11503000003034200300940e000020410a841a40d8440c440444506452060055807540788640c01c0b0300490003400da1500d030203d04400134a6003100394541040c0112022850000040c0c00a07600060100046001c9600d0301e0400075103241c00d00c60106000440d50286251001e2030780022003401004100070314004006e0041d150110b0303418107666401c3d80c00440e2651312a00c0700001c43d03030f0360010744c128000204440c002c0c2c3d5440c00d10700a507003030560340a0031081e42100c84240310006500b1034218150005c105000000c017581d01e0050070190901d25502541c2d540a605041c18100304000a80042c00e90741032110403110500c040d40c5014072070704028410110070a0b0902c09003069002c0000c0f552004e007000c18808640d80205200e218401882402c1044c08544003000e0300340e035200e01200380c2040703400780040d58155200d01200781c1c44101c0600145800359200001c1d400714030540d410780003d040400140403ca8040103880045406040c00309441440d6a0010700f825800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 922994226 1250 922992976 922992989
    0x32160b07150c1b03021b0103060308031501050f04090b0f030706120b01091a0307090f0b07260f0c0c040209060f07020312030a0213090b030a03050f1c090b1609 70
    0x1148882c1000610540149040044281d1440400c00c80340c01c0003951303140042c0d4070600c41201e800302c982e00b80d03000c2d214403002c996000d6034860031580d0b10b55038280300c03200003000c440c1808001c04c5940c03c1036603580000e101401460311b001a840801000f4050098804001c640c0242e028100501451790403103501104011030000c040b80018201c00121901c1d240740d40200840b00d250b11408040590080255100d0109940c80700c98940c0d8800c0d0300c042b002c1c00751040242080040080b60003241c13054004c6983c400703040c0300c3d550200740400540d90959002d0341c03024103008000708020040030401d2000380e0030480c0448080d4200b40621001400c01d10131400c003150865070000e5124119201445a00c6d5854400c41403070341c884c038100d10214080e501c41c24148105d0844248080b0741117106200317125401c00003800601c038a189981d03080d550f540c80740000f169844000d1140c03c54240b40e465000c140c0017806031012500942c1464098401b03003020707050880081101a4030900240c0c803241ea007088412 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 922995476 1250 922994226 922994231
    0x60e01141509190f0f05060f04061412031c05090f060103110105180306091b04090f080309251505030f0606130306050f040201110f03030432160b0715 66
    0x560581c0080c080003040944c0d0b14104505620140c05951000b40319110a544540d4840c103040d003000111075442c0215450095031100d00d40b0141814602500caa48800b41200d207403410f12079005008020b024150700e22945c641e410070170007144c1402480b01d03c01d02500100255415a42c444400c2d0501c0c10206040110109440300041c4181e42d07192107402c00902601c015052499a0540318404142600c07034a03001c44d01e50001e6803e003071203240c0605400174048400e0400542d512046c6600280c03440b141445040d0700381d0102d41c12240c001d0a140c0032010300000c0d0601d45090203461101c82c80508003400b10501c1042411200c4c01400d95100400f00d4480c1d5a5111080c148841e0140b682c10242c041e524081c10400d251200a10030760046001340c8070300c0c0c050b6000000040d41c508082048205940040c030120f40051346c55044200b642c40e4500102d030501c1c03100ca03064030340c0d00711a06110549502250740000350811003c5264003500b185c455440c6070820540710350802c04600d6030020141079 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 922996726 1250 922995476 922995511
    0x90e0c0a03091a0f1b0702040908041d09060f0903070311121b01140415050405150702031c060b160507030c15030f090c0303030c0c060e01141509 64
    0x51181c2c0c04a05030340e500c034104070140407800c00d02c1c1840000c100c0d18585841c1c18140416044a521941c2e20004e04252101d070b860052551309010240444207000c0307800071030912011503034000940746690000440c034144507a07071038615040c510344640504401ea5890324031040c4202880007204540007180c150a181100199821040746805181c0034413050040c0046840982400309805149040c04120001e0041600c8110054000d080642e00140000d0340d2443d0159039030003030b41080c4e038072500400580c2c0020b0018510410081001c844100044c7c00004192400f5100050034446403400c8140c1040781c4da040084510a034481d20034a02c00000e100c00c100d40420a0400c98070024581c41a0050710081c2e6802070301c0503020400c4828400b182c00c11042c82d6410f05140326843d940d6800140c0e103900386245803815002401f503180c52504112a490b00c01001c980203000d4903e050348000000500c5100524003903010340b001a204c814071180d466110303081507a40400342500003140002441105 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 922997976 1250 922996726 922996747
    0x1b1915140a1e091e0609090501060206130f050d0503040302010e010506241c020702090c03060a030f080c1e250311011b06090201200703030f05070203032206090e0c 72
    0xc01c0c00d94400c1c0184840301c0419083c10081541300d80480b06a80c65002c5625119030505040e61824050000160b006600041d1003010042e804001c03a400ba00b6228200c5407151510781c28503a1150124011841c004248400c06509110b084e566180e00002003041e401c107100020490482a4108200810100e000b4621402c0c03080484850064100844070f9203900c0342c0c1d400740030390410803050784200b51140003d2020b40303980003128860013006210350995403c666a0050300c00c0c207408283e5002d1418000c010610404100d02e1400900390060003201031103242002c0d203011682014007121440521a5aa0304500d40c3c04c0c400030b40758040039080c0e010464000481d805036001e420301805400c0101c261050041903440110414000e90342c1041c4400c5440e003a034a124200c1490710700e00d0740a081c041000c03900c5a4061003042d5a9890113610b03002042d0000381c916001002c45101ea01c9900280b1490100f4405100000301a14103160405618103030550751030380001001549640c40008408016 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 922999226 1250 922997976 922997987
    0xf08090303161a0c03070509062b060311060703080f0603161e05090601020a020d050c181603050f041b0302120f1204081b1915140a1e 59
    0x90200010b5000b4401414141907015442c4186881a0100800086a000d901200450344180e06503101c0c01d150061351400d1242c0e035800000b84a80c2c0c80d4a4801c00c1c18500608003844085850000d8041402c50075030812030207546124000512881007005283d0000790000780361940900c000b484024160303038082c0840d05007840408282c8098010500c00f0456916102a100003801041031040d1010744980510128542c103844240c007691028014a00502d0b01180114403144688141c03607030350b05403201091604180c5c4940c90f0340e2002c4001000380004826403d0000034003145014000380c1030081014258200140c00079222020101070440f20610070350121004507405051542e85182c00d46c1030340d03110f01900400380f0140c003801c80344aa480710907100f0346003a1507007000a000c00510309440c0d49112138a0303040040c3c001c1c10000b80f9075510406158488010060303107500c1c0d46c1c828a2460002c01c1608440e0f250010044240020031130140d200d1034501032658040715108951806400c10b481d03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 923000476 1250 922999226 922999237
    0x70f0e100b0a0507050606040b06040e0a060b03070e09090303130f1712150f01360909171306031805010606020c01110105010b1207090f0306050105090906040f08090303 74
    0x281d80d50000703200d00c10254401d00070801c0d54010000d0301e4081c1c84990802c003c0c3d0700007818496008030103100900c20340c0f8a4800c0140c00c039a0302100002c14503510030006029420480d400c90101d1040311000d51a03080c002c4000d03a2010b0704e14007540c607503d8240c101c004134a9112401814040d001c081d510104404800c91103461060a168107494026000310458012412106500d002c5240b040d492490305120300150070401c016102e0342402c0c9000c4100054809101924130218401000300c00840c1d10000890409456141400b04003e8594100700046c50500303021a01d03145400c01154080c1d03010b90042c40e0a48405150104010500e214203000c4d5a2414030301800c154a002000110700d0780001c3c0c02c1100d40070030703210149030025030007026080b5402403142800031032040281c0501c03058401c0c4040d0740b10a40d814480d00c1d07591a1002d203511110a90402c486081d9204014483c5141c0071421507803102e07111008000e1490103941d8072000c0c4a4401d0001c2c2588c2c0045564100f41c0c0c0c051040c6c68 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 923001726 1250 923000476 923000489
    0x153b01260312060a050d0302151b031f0509090309010c08121302010906030b0d1205040b03010305010c030f020c0d180b0c030415021507080c07060c020d09050102070f0e10 75
    0x251502e03255440841e0505040d10502e114160340c120005e03850a00c190b191001c9030305500039010f4003642c18040001c4e00001001440c400301d01c44488003070030301070502071070003290f620380700c1008407181081d04200c4c3c40180d007080d0301c1200c10200b0400001d80001c1142c140844c28a000210084d8601e40301034203000384402000108484401c10480304280568050505e000341d9600032850b03641c40d0700783c0440c1c485c0c00034160040b5401c981a00840d64400841d1a00f0500b8642145041da544403064455042a00115040e945603610408842e50502a00442c0700301d900e000c618110f00841c4590343c03100c8084410b82401143c1d00c0782010f91035100070004c0100001010503603030707429044101e5100e40c4140245104040301014a41015100050105403981240d0400c2401d07101e2120a40d01901c00a0400d21940310801410000030401d018003403014845030018100c10100c03010141c20510503811031030465101c0e650400445010092542c01c54940c3e12080c2c015844040e401003d4600a07001070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 923002976 1250 923001726 923001733
    0xd1202070b0705010c02010f061a090a050d030c110901050d03030b0310020a02101104081518010f0501210809040209210a02130212010e060301153b0126 67
    0x44041c004190030060503502140c6c0200318940c1787e041d03580102d440d64007a1050000810a0000641d880c4100410391400001c0c81441d2480da1070300081d40400401c4812400243c803540440304000104408950901045598541d90340c10440483c03504404000064101600c030101c0300c41545003444070403d088010101595a540e0311074029543d40701c640c000701d81991626881031141e216070811350341920861170203080d6059038004424070800300900a07c8800c60a030030007600e40002440b41c2c0c800c8039650100402c2540c0760502e0081ca61110340e241816080e850701c140d1002074401000c0b103160b90000c640060722540c01d0404284403200c0401580c110b00400720703a045c508180007540641140c0300b00d84403100088094014420f80c010703c1c10402880301c4801c01802400214003410781c0c02480940005200703803903606400141e90b2075030322598179600840b5100340301440c4005106038103500101d07001040d0240d02500e9100010503c02c038180900c4000f60845901c01e821424032051004a089 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 923004226 1250 923002976 923002987
    0x23150f0303222709061d0d0f03150306050601120213091128050903060a0e070602030c0601060c080903031207020d09030f0b1b030a050604060617151c03020a0203010b09060d1202070b 80
    0x142c1d9171f0302c4200c2420030203e03080700c1d4032080d0507110380107040b141010100001d00325807035a5502d40181c03101421042c140850b01d40843c07103000c00e078405080001c0c206807600c11440d1518035640d04503020103000e4100b50804000b40c2403003401c0540c1003001c1105401009a14a40318a0100c585004070b0400590500499003808200c0f041c603000010155185400d8840d5140e031060b040e43d41e40719405510b8840d40084004000d107a020310300350200c090041c0e01061504030b0101c000307070942e0b00000a001c0d000c0c0800c014400b4480e410043c02c41d5800450a05182c402c1c00c42d00e90001506180314020324080b25000010807004190b8030350582011013040640d100d0500e41052000f0302411241036025601d8a07000050051040c00220b5600d001d1040e00701460321003810441d00d41f41c01d510604c0d001002d0205107507038450340108c843c2e841070099006c3c1c00e008840d407042500f901c1001c3d6803244070704d1654040c414995a000d41100c0190740c08601404207590b003110590906130303035038400c2e00198000300701c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 923005476 1250 923004226 923004281
    0x516050708010c030b040e0a0c032604090c03050708100b0d020702120604140601030803220b01140906030f1e07030b040f0623150f030322270906 64
    0x4119140b4074229801d01c1210304003587c203543c81c03c1d0402d024002200448080010492852060200c203030044410402100c940e044203c007a031169120800c540c0c5d071951107a147d0307030340740c400c0303e4204105150110050a1054540c3c00c0c0010070300400e4112000003801d601c0d038a10310f50460351410b90290641120352448500c0d03a80ba135004440503160b80390203200080d0146d0012642a050b40d81c00f203c0e0a0031511040082c0c1e1454071740c074000811001000d039480e0301041c004e00489000709003150181040c40019003c0c45050308014021a01035407001c0c144081e91311000c00e0085402c1c40400c0413032040c00b03007004950300d40f500c694400740241c0c02000601c01031100c201000004030380035240520100b4000c9404140c080100181c807900d020038103011526000c0d22400c210f002c4400204402c00ba8059000002d0443c1e00c900780c480c1704051503000d00d0a400141030751070b8000381b000701a01c80f142c0f14030345600090040c4410711141075940d82d10200c4100708284e4040c5014910550038400700758200b40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 923006726 1250 923005476 923005481
    0x1051809040b18120307030b01020a15051f0b0a030207031e0302090405060d110603090a0c241103030c0d09050a03020d2012180303070c03060c0c030516050708010c03 73
    0x2120102c541681002e02c2481c0400052030134952000e114013186195900714003103005026091803103045011303660409001c110ba015070005410310b003041c0052581000c080903645800100342c41013840c6812882086a0707580141516002801410702507071315a0703280740460b502091800044000e039500407041c19081d0341070340a0301c00840146d07010040c0b501c510080040201029200902048500300800594140b0746c0245402103e000700b101c004510955801491111030b802c00b80810803400490410070203041601100c890050800c2c1c030850790b83e440b241d43c44c2d12000705103804200001407110b1a4103e03642c030001c420380e0060151030410055103002500c13100490950b800084030b141585074062030000c24070034013500340402003c201c0038026070308078103400001e5032210740c00ca24804031405440600040582510640040d030780c0303030308628000c3c007183e03140024841041045031002000980040454108004409c90400c100003c0c2c41d06c18903203802c903040106294245620400b000760182c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 923007976 1250 923006726 923006731
    0x1203030a06060309080304021318050f1002070c140105120c0d050a0506130504051903021f14131104020a090906090507051917070c0515060f01051809040b 68
    0x10300180300030307996100200d00340c40319800b0240902404001140040c900640155410f0741d007160040748600841c20b60503000f1207807050940c0c0c40d41000415005401003401203032142d036200300c0118148041a00c0b80ca121281e6401a031040381c4640741c42140d56070280302512040c800d01c3c450005036142540c560300003a00714943d8aa00c1904280106102e940d450140c1d6110343c4c0c014010900406803038101c40050b00010f0030903505806403841482c030310404d600030a083e4070301a8005002041d400c20701741c0240101000c0391914945464003002086000c086510342100c1203200400042206052500c1c56088a1000a60281c80000c10368041c5800000c98012120344020400c0310756900c0d8039803800c1c0c460407680c00000400402005d80b01740d21521201c6101301c0903203466048002941920980003900b0b9074036501040c4108107030002c010702046901d41c1c1c40e0740c01207068810b091060200e20f080c4441c20245041c00404542c01000130142016201c004200600d940c0c6242401c0c18801c0600030709 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 923009226 1250 923007976 923007991
    0x1030309090c0f02120d060503010906050702060705030121020112060e0901450c060507020a080d200f01110c06060901120609080d0f1a01020705010c120e120303 71
    0x50504260501e03024965622a0f0040c0da00500b41e42c4400480c100102d5100352407140e44543d40c1c41c0e010500752424403078181001c0c4518000a034905150801a01e0104020b10010400c402003006101070490039a0310b10f0780c41cac00c1e548a00030704025840143d5205420030301c0c000845141c4840001c1180c0708a071101d00070340740e10008122100c0240200c41da00c1034980400c0b581d5480e255020028541002c90b03141d59016540c20300781e107030050703542c80d105901002d07401100000d0020803001c0c00d602e040052840144080f400030191590381040c043c0c0300070780741000725900c0c05840c000903600210500100080c0301d0311000800c8400c0070104500d01c1608444006909071050030000392950a000c402c0c54142e40c03038007411181d1442a5995000034068810040300c131a50140990606015140140c2004440d03000004c82c1210746810768441c2d8101140c03550b41158014441004642d03004501c241c1c403142c22128020f2514103101d010780308844055101900710b01c0d48420203000b01c5010000e140940c05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 923010476 1250 923009226 923009231
    0x209060d3b070b0d0b0909030d1103010302010e041d01060b030906010603050f0a020a05040315360311070b040609060f0e060f13030c0f05090f0f0711070803030103030909 75
    0x942a4081103250804820309801e40d00c50328090101c2e208072005020000806100825043c0ca41c0000c20035000d002d69140b80540d2000c100c01004c0941402034104185080c2c510342d0541d03140d03030002032285038803024440c0115505c944184102c800701d0301d10840050404024400e00c0c0da03078590362040d54401c840740002c900617807001054062080c02914000d020b05040005280c0790120640002d41c03181da515800d00c4410880000003800c00181000c03ea0107a150006080040511494503401260100780c40e48410070206802d082080b4510171400c1d4251514024140c50a94984d2415a40b900020fa103c403020800184450384003003031505640740c0d980d40c0c01c0c13500209481070b60754140c00c2210b968400d000b80101411446514050300c0c010701010300510340d180d41d80c0c49071a010f840716000141801c440300c2e000d00c454148030701c080d84c1010094810b02e08628222146c1c611544020b0669800c20000d1020040042010803408000d07091b80c000713903039580d65a071038060080502031194029090 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 923011726 1250 923010476 923010551
    0xc0201230a32090307020f01180905240306070503130804121b0602011406011d0406090f0b150f0c070b0c0606040b01020f06010b0f0c01022205060403150209060d 71
    0x30f07004810344180e150301800001441d641c030b10040d60407017502018403410321181200050317400034902505008400710340308080f0101680e11444aa01c0b6400180c500235801542800181c0794400300300c0741d00c03082c90903507958001080d02e000103c503c1240d10542080d00e404054078203001c4950b00d111041c1c108140b050741290f07607071a03044c2e0907540301a00c2e00b494080b40c80e0004146502800a10210a00c0710f26500946894900000c1c200c540507000141d010b0b986040d4000a040f95105a40668204541d01010402200321700c00c0c2e103100d40c012188422a011414a411030020040000070f03003145e036980b07601c0301100c50080ba51617a0841b03415100d14204442148194000306007490b4118654010b40002d82c00d1400c96400c91744500c80c202007814042040e030380c604c40300b84090088001040d55003800e500003500d4207480036403250031441c4100020402080002e000d54506249404c142c00096101d81e510000680b06004e01a81491500c2c24044c18038050110b640380c0041d00c1110b1250500080c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 923012976 1250 923011726 923011741
    0x1005040b041d1014040914160315110421020306040b0f2212020c0d0506040c09050112170f0d33090e10020c0601090c0201230a32 57
    0x382034074411240e851034500d0301c03404c4905058021032440742c0910a0000030b80025044189890408803101c00030140b401c800388204084400804d40150f0b4402d030034000d0128007600058a886148542c042106011300c90505d140c0e58880c2d001d241e20307001001e0b07900e2803409003000c0000c40021122a9030070380c0d5800c0010044407100c0c501c880302d40300c815200e240c1e10340c3c96500c002c0f0030a01d02d203040040d4891913041c14501c0e614100034001051042000e4205c5090a107040f400403101900315040c46070814006010000d01d040380e00e40e12a41048040041c0038118520301c0061044251021940c0800159000c2103145034001c03819001d1a407281e00020605030310007440c5e03650f26141241503200c4200040042014582203460311302d40a8003906c48496044180304102d0307000030b0107208560400b40c01044140120b03c9402d0301240280000c0c0700150034106da04402c03500e4510081c503440e00c40f001080c0c1d041c80c140e1084240d5981c5820303540c445081541310108024500558070029483c005c0003c0a2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 923014226 1250 923012976 923013001
    0x190207050a030f030e0a08120a02010b0d0b240a03030e010e0405190c0201110a03230408040b0f190306090b06040b070201210513020a15020601051005040b041d 70
    0x8403604410603100350040d9540886100001e111161b51160b100000441c03c00381c180300031283d485800c410240e4500760a200642510042c2c031216100e178846154040115444c407110643c0010900d2008040c014401c0c812000d603400c510042e5080031265402004254001e001c012034540241c030b0b01c03c0010040710070481541e0301202c80c03200844502c021101414420380149070254100e00002ca11902c00b8100c1400c10b03000920310400181d1a120300340b4514110100d203d22400401002d0301c818503194940500500c110b21038854000d1000030704014091403082a07543c0c02200e51424000f06240340001805400503016a0060a20b41106608540752500440d03007140e180201c818200f0700c075038005450300d500d02410300d1301c6120b06003001c102565143c4151807144400322000a80300c1c1060040c04603138006504100e00403440411056000303030b000200241125401c0f00c4c02d0142c4040040115918080c65128034848107022070003280100701d00c0b201811491802500404503030b201c0b10034124 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 923015476 1250 923014226 923014229
    0xf0f0a0b010c0201050c1908070605010f060212070606150305010f0b0c10050a0b12010e010c050c0c0d031b03091a130306020d06150c0302010b1215040611190207050a 73
    0x300e84501958801940214042c04a00d60b441b401d90f19580c0c1c0b290a02c8004001c9500111029800080c09104009891091601418a500914443e20700384000695a9110000042141500494860b080002981080e405406d00b507000da030b4034258016000c1c0103010280030380c014404440002207006148281552031441e081002081d48849524a400040c80c0145c40d241e2000e491701d06603201c0c0d444500000a103208001c00001e0340c1d00400c08210708490854403d01c040200c10040400340c69000034900310042d00071180107141a000d80b809440083c9102075100320f540070803a58505040d0489500d10803280c85007041400340342c4203401d00741c041c4a424841034000010b950b0130f0000c2030855006d00301c1c21226800c00510b0a07240c0641900084075003490100144000c9002c0c001c0644c280101a180b84050318034492800780f06085580f00d445000d07014032141c41400029080c001550002844d0488468445944c5c0042d018aa401c500d0340004c0d000141c03090704000280c03400c0c560089030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 923016726 1250 923015476 923015479
    0x1b030b0a061401140c01021204030c1203090c05040e0106080d0903050c060a08042006040f05030d17070e03120403030816080108030d0c0e030610060e180f0702150f0f0a0b 75
    0x180d0701341441c1c00d0011303800902a060310f5640c00c0c0241102410651012405180030740c8480e0701030700072481c20700303921f0412030807540c105030030300c00404001000361100e003050b41c00440b400b090715410100c0090042c010782d8041c4100744145902e14014980020807281520b00403010343d03400d0440181070100320b20807501400b00107003900c1d00080c04900f100c100180f407041001045540c808081000841075001074203d0502201000744c1008940703001c01030070120810505040c1e81d00100c0b0540e801c1402801007280080c014140909030140da4244400464421141819900c59440b418000c01c1840704991030611120500b43c45010503004200e001e0480c0d800000131031424120712046000381400d18210000d21849030520005a0703001c5c020702c1e1007140c0c007600c0e294981d454150014416040543d52602554261004a0703046020103162540000c0c99411081d1580700c02604a107040950044031030000729880030710144601c03555220380241486020b600742c03511900e00500440314003c5005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 923017976 1250 923016726 923016737
    0x10605010e030309040c140a050301210507060e010210020304140706110a03140c0604060515040b010509061e0f0406020c1206070c0c0f0b0403022107030f1b030b0a061401 75
    0x450700717203070035084850025260701d02011581144c41e160368554004c4111003000c10b01c0400144460b28102c508003100d200d9088a0240d440400d84a450312042c15010f03010801c0050b030f542c0480d5900810100d44c00300350800c1e08541e00e00c0c090a00800030440303081482c81c01d0007100000100c1a03c290940d004000c1182e02408044090ba6030950344100c0452600026080501035000110009c0c420030b8807440c010b8502044501c2d00c842850b079500075031102d0901c40c600c2c040600394240d81c080f003580c8140b80c00b5241265242a000000740785100c00140d000302c0c4000002d00e202da90302100c0082d1003141c83d540c00301c0f20007540e4901001001f81c0c2c40c56401c0c0b8903900c88000200c00d94030a1512241490040d45000318103901d4410411000050341c102000040307002800b00118107201480e80c9210180ca0b003040030b8610041001c503128400d910010f13250f070014160750000d000c04d81e4400b9200030706503646040426907030304c1c000c9280e160446104a15038a0a0b00005504013488121180d090050350340 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 923019226 1250 923017976 923017987
    0x10903050418110a024c0204030507150e04050103020f01030f0b060d15050307210303180c03061a03060a0e070e0c04150504050102120c03210108010605010e0303 71
    0xb12100d0006800071500496102d209a2442e0901040104214a503d60213021000300095130120400b507408840310b41220701c0400409400d5034048510f941000034403110110a00840d403030406401f03107420240083c003c61a00144059402c465170340b01c00b08544580500c20039800030041190401d10019400086621414510390b102c0c2e03000c64002c1208078000100c004004010540541000f040b61782d42a95800b4030040e03034501c0d454088000c04084006020b800d04103002d1f83d0700c1444080241c45205a060b000340c08040c0603800071603684002c0d03561640030300b029049c00d4440950610050710f03501d2400721203d812101a06c120b840680d406002001c682d200c0c00d90081c0200309942c0f4542040c00344c0c81c4c010483c01ca9107820a809049a501c030b1540301c0d400e10100d80c11118a06c2284005c1c00800c0204008a98000c62000488900c540f8a41d40300d42690110905611038285050300014403ca210b2245990358601036043e1080500200461611040150f4040202c3c080e46239050340103004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 923020476 1250 923019226 923019239
    0x60f16050f13140a051210050907030b0c090a141e04150b03041b080a290907060207060302040302280810240302061617130f080109030504 61
    0x2800207601c1c02042601d01070707207506034031110b01d956004900d11030700d142d01103001403401c02202c034040d000403a00f48000d402c00c905255a152141c02d89081d0064a43c030018081401c140440c400554200d11181d0b40c9240061045000341d00900302503100d440f80a41c0800c411301100e20a5641d07a030003600c03000c400c603c14a0704400c0b8403640d1070810703032003521003d2403192980640350000052001e45810790b160309240c5010f20412005241c8050521005281000070740c2c07000603040805504080580140b4903054200c0441e5080c145080c03900134420b030103004131a5000030f0100c044425640c240d8415685444040b401c2c1d2107140700195129a180a640301640c0f202d4846a91301c25031507400d9042159100300c80c50034804201014620a07694081c140c440000040c100e0080303480b1403150f0780010307055038005095402240d810440d0003c26600613010894540104506c460045603940e4580d02030010710354610801c0e0280c51450100104006410401406001c03c2c040d455107400c1d0900341047c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 923021582 1106 923020476 923020487
    0x9060703021201060e180123030f10111603080a140f0a09060b0301061403010e0d05040512120f041e0b0306010f0c0b1305060f16 57
    0x2001440072250b0306050706440d042d0600320380036584800803551540c524001c0490b40300b00200049503201134050180080303c1481c0d07001409000b40020b0580ba26000480c500703140d4001602203030700200e075401840000030080582802d00810845413000700740c0070b1400750042080c41042c00004c0c20345000d45110084004071003c1a41003000c0710341d0000e07000400584120b6074503507004040140b0b81c1c1042d0812203005009100c1140c50711608200700701d030440114802d41c0b070080540207050002c1071400640303d05072200e9060601d8003040c045a803443c240c405205005585c0300407141c881c2d80d0050013902c4101d00181c1d40b0345082c42c034841d0b2000364520b002403080300344650800240350078108a030b9010b4028603003800c941d14640020760782100c1c13020008001c2160041000312550301c8144603050355000383d084840503111010310040110064031220108414581c90454090144 = true := by decide +kernel

theorem cover : BRFrame.Cov 922841726 923021582 := by
  have h0 := BRFrame.cov_init 922841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 922841726 ≤ n) (h2 : n < 923021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
