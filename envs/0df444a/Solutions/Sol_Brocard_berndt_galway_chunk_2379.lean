-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2379
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:32:03.825438+00:00
-- url     : https://prove2.me/submissions/8541c884-15b6-4979-b88b-26d4c0943d5e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 427697841 ≤ n < 427877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 427699091 1250 427697841 427697861
    0x606060708130b0409180201051b030904180c0b04150509040209031c0e12060703020f160b071101090506010b0c030d0609060302010e0604061409040e060f04051c0e0d0303 75
    0xb00c5040b4075110030620300c0c075034810712603101480e0403c0c044c031176012080c0c4044580c80340d058441e24946080b203400c404042c1c00b0800c0d020854001408500e5054031103000c0c0c5c00000c40d00e945104a1703800a80381107a06903510750002d1708560020301080c05424602842d10700d1034006401c0040c3c80380420710001e000381c89958141c07901805500c0d0103038070030121034000030b0300e07900140c481c5080c1c001080103114001c03110a017002040c5e4400c0c004540000d009500421116006034601c900e407800000200c218100030410440344041090100400c05902030000c56800400b0700017480140d01030384403155140f9060081c14980200000e0100e4005401c0003160b030708541c1000280a05542c41000038000c10180c80142e000c545140c500000c0d80c58800111826074010361500490300da25140c42e491a030b080b20481c107402035030b03440318240205010840f09105400d1070b0440380701c61805140030b40c10402ca1450301d200180021601e01c40c640d0301302400d4803100c0425103500303142240c10304088000d0081029 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 427700341 1250 427699091 427699117
    0x70c0e090a1a220b010306180807060c0219080408060f06030c0f01090504140603120406050d150902030f07020d0305010807290f0d0b0a060e09130c09021b0a03020606060708 76
    0x4190030881000b00c03183c106ea010b803030b08100c50b0050803e4200005415000280a800c04000240004104d80d01c00e075004142d03032048800c4101c40c510300c0002101c4112054070f82c00340103c0e04102403502001001d500400540c0204545e0508074040b90341c44480c05010740c443c0b83e00e0304a10043da4810020301c2c2c01440000d0080c0540d02048503880c1a03480d081d0340302c0d07000e4020041c41c0b03040e00f1040c01c2240d007241d020307903031781e51519419092030001000548503402d501400036100007420322050000e94062444140702c040f03035003412000a03141401c051542e80500d420800100501000441d202d030407100400704600b0800520000d030241d0101c0071014203845400440e00d4541005c01402500850794087d00800440006900304003c81c0300510880000a51704000c0f240c1d40e05265130f020340c21000d02070030380075904400da88600081e05260020301800740e002c141558404110b02c88030001c5545100074042c40d00c49030710001d44402d03000b00a00c0c00b4070b50008203502040390444c100c8070804a1a1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 427701591 1250 427700341 427700401
    0x60c13180b090703090203070e0907290a1205251119060b01110102070c0b2206020c130902030d0e0a030c1401080c1201180e03070c0e090a1a 62
    0xd5001303002815a950140d000e449400000704032a02c0704244c1074050000d10004001403481c12030120814403008203045400f014584900da0854500006011444e0392134641d00700704d0700501960001c5403401000d130501040510070500c600d40310a03440078440042440c00110010070303d04643d1800c000b01101142007031000d0303545018040d5651290f459800242e0310311119025403443c4500f42d028104015280d11554807007007020706040401401300d041c0c40700c4d0414a0b9a401f00e80c010003242d09610070405a004485074001c10318000c201d80611168250301003107100d0041d004030b1ba55207429200300051020071008844180d507a510010011907020415162103034840c07051440e000d64508020303001c940c0820114440d41400004e071020030a88000080160f8600510410300920240d15800d42c40d540b10103203022842c1c2070008007442d5002c2e600060000340380c08200e091465000300300d1070b01c07034001c0508800002c113a00c50046c03040c4a242c0d909081c1d52a45215602c0003400e2480920a0414079 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 427702841 1250 427701591 427701601
    0x3020310051302040f150f0c020f03010f05010e071110090305070b070e15040e0403080604060f0b071115030c0d0b0a090506090f072102040504110c060c13180b09 71
    0x540007481942c1035000d80340981940c6d8070364510500504045500891f024008800f0054418020231f58814001881c03c41c01c0385038036005c039084845074001903010b142c44200509c10748080c0b044880e0410420b15042041e45440102e25454041c20030085040d662541c080c0d0040c10710500907100b8103034128014904a0801c03c0015003140c3d45a181e40c0d009091040202c1e1490030300d00700341c030100d44c5064038201c06036441d039408a0318a130004110300d81c015641c1e02c0c04a002c0d169000d0200140107010003095a0b104203080100c1703030710090f0902922665609200758a1800000c00b520382080ca19800651102c08850b8807030701030001150080e400c420301000006030402240c0009001e003005440c6160103440342c014410300071f0411600300b008202d149010f0b00ca4018400414520744421000040c101512600020103480d1003203e80809050046101d81c2041e005001c00c0e83c04c40400d4200324541403204401c000109001d201e49481c0c90b040700e00c0e40041e100742e90440400f0000082180902d8642 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 427704091 1250 427702841 427702879
    0x706050907090c0203071a011818080301080a0c0509011a07051002030a060501080f0708010b091306060f02070b09030a080702040207020406030b1501020105270a0516140303190302031005 82
    0x204807402d07201440b1800742c80000080c40135145041c0c40c9602050302002808900c29000741c80e403100181c155982b00d02403000410401c2010b14042c0c00800c010303202c40d410a081040302100d80b600113a100d6417000c0300400c1024044004ac803840f041c101d54143d11503205007401ca050002070080c90000c58000001c02c00200004e910a00c113966091300c0796030319516900075012150724100c2d040f1011900080051061600b03e00c06030045100003010404104d50000d03040e81a21010340c4540045018020515844c0340c0502c0910050284c0c6100a410594904002651b03502c04001c0a40f009100007241e4056450700d0701200c400540103041070010700d54911303160b904401e0072030300c2107248030000c00c00c40c65561060040500840e080242e40f03038400001022240d950852410305a034a00c107a00810000980c103200003642101302c41c1030744a016140150007110708c2851151a84642c004001c0202d01840421084250000c0c3d0b10b0016103030360303c1c0107140103c8110b5400255001a00d0700c200994460 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 427705341 1250 427704091 427704097
    0xb090307030b0c45030c0103050a06081b011106040c0302060f0d0e060601090909171321030306050a0803071202031b0102040305010b010203040302010903060e1c02010b040506060406050706050907090c0203 90
    0x5414804080d18a1824202d1003050041a4200745e241c0c014815904507984240c2045070860044040050311503504c0f14424644048100c1c05010003d024242e0301c00c03582c010310701c02800c00c401340140c0000d00d003554602c1b0f0b080c2210300000744a1303d40815460292548101941c41c00cbc4103030603003001840038043d40c20b5030719402103031050300046900780007142d00d284030301903c81c202e6404200945180d80d03481e440030050b00700385a034a84540200c240080c04e004924420811401c203c00c1030070010409040050503540590040b40c001c1c09908001c02c1110b40000860f4802501701d291404051031005041341948903421040007880e0103203010201c00001076004100f02d03846540200881050070b8016600c900aa2002a02280015408101280994224462040d2410159201d000c0b580d49a0070301514501c1240340142e655149801041c00d051007903d4004070100c0c0c82030304051030130780300400c1803041607402000c8030380b03420124424440070011503002e01034800040c0b0021040003402980c1c0c1e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 427706591 1250 427705341 427705417
    0x1704080604050616050a0309020d0b010b0d05090105070504090b0102100e25081c020f060c030906060102011a24040b120f1003080f13030c06090b090307030b0c 70
    0x1c0107003404030350350400d140070020000d000c039100c060500f00c0924040c7d0040c000d0480c2030340c210380410300110000781c1140029010f4180405485d40303c240484000040318401480040c4c80e03032400060080c1d10741c10a041d40d045403100311001c600d80c1113350040b030802c0e10312200d0a1045003006ca4a80031808041040c4010580c0500f50490300300310b4a1214070180b0051181010942202500c0072400d190803520242c041c10500464010395030300180c051601c1c004035900401c1c042c0102c03c0c480400c0f0103102803030b0402030074802484046401c00e105030b4400c006030001d5110f003481200d94007044805428100654440e404156140c1c0c2e03441c240720780c2d103038030003501e0351802e1011400080201f0280c4090034000d480b8400300c0ca000ca811583d413844607601c11004038440d14810b0066034940060b5000d0900a18424800c00c10000d04e0000098400c10558004000185061101c0f5120351000200d090840350040840d4406490b108201e0b00184175156114030240d88440c01c1c1008028248905a189 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 427707841 1250 427706591 427706593
    0x3009050708010b1801140102070e071d040504050d050904090b0f040b01050907091206020405120d0201060b040e0402190302060f09011b02092707030f02031b0303030c07170408060405 80
    0x4005050810402c000c0d42c60900078181300c100010303c10b6100075203121030744020600444a40645401000002d240d041703842d440000c0c05220820006543d13007442d01d81e01003003501c0520680c01c05603103042d191420300201c1c0d410410040b5811034a81e803940c05c0b0280c5c50750010220076075402c045070801e01e030140490b010f07525100d07203070000103507800c10200305442550716603524030340e232802d12080900d800b001e0802591200d03004d00c0041a95038a882c0c41e0003c2d0180706004050410900202900b03690306503024150503102400208110362888100c1a441070341210303808a400c80d0301e0452218036225400c0a03411860105284074203804403002010510b80988507a0308104100e40600d0312605c05141c003d401c10308510200d60301400000e03200320705520b010380310090030100161080c40e103810f642c0141c881c141f4031500201581400d0162260394284040d14050001591003c1fa41c0c903c0080c110f4404102d001404205000040c1c18981080b83c2c41c0c07141c0f541d80e5035640f01c601d42ea048142e80c241c0315 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 427709091 1250 427707841 427707851
    0x7030801170a0203120901091a0d060806070c0201050f1905070605061c02090402040b0603100e01050f0607030f0225081c09090b0a0e0703020a021b01300905070801 72
    0x1014200050084800307a0040003030076501008003400714186c0080700018103020f4420400b003071080a20301140404103078610b51a880e810542c10304400c1d22080d40c05000103801c032009011020740e000810340c168a40a00300340d035480340305001e84500c41c864040017816003590090001099036008000301603880c0031b80c5c0140019255002042184c18144c40f1030703841188a100c2c440014200b40788c0290f84a400284000381c0c20140c2c030003044481d4400c803181a9659003461040c40f000c2c4400c413846001d014180e449900e691807190108805208041001e814406510b00c0010820310030400c0410701c134207941d1019a4200001004076081005029681d100d0040482000f2200d00e940044062030b251a90b0707801882c0e107854980f84c000c2003200181c6802500300c2c1d8000c83c6440c2401c00c100d000e0348036a41c0059841c00c0002d802414582c03c4148a15250852803414425070f030300c00da403000042d5551500d54000034545074811010311404818a42c91420300048406200740822500115a0f040300240b01c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 427710341 1250 427709091 427709129
    0x8030301080706080c09010c050c09041416050f01030e031b011b08071d030a08030f0718080d08280903030506060c0615030a08070c060905010f270b07030801 69
    0x242c131070085030f040683c00ca00340a02091584606900801d550059041e0b07160031240340b001c5114144200d07003e54404840103a1030003592420044190001c0c01e41c07580c05038480c04c06000540410307003000220304143d10b0b003a4a1030307940300038001c8401c0960160305000252100d02c599502802c00c3c2c0c0311111483c0b03402003a407180c0901481000f485032489550703480740308220610601030f2003070044500c1e4240c0300c2c88803034a0020303030403000550040701c090048220070300d000a001404040180c13501c880c42295007104001c0c40e100080c0804142c507031410302e800700350b858a00b460400300130310b41203008400d620b1026a411031840e900050030240265400c0c480c0355075a105004240c4102c1040c040260702020000307450040a0f160b410441e98018180c44c201d4030766445100d40c81e00449400d1710345035420801009aa60031402800040900f8204250540714002010b0300d4921190703d00c2c1c02031100c103100d580c080c03543d0420303101c041c0c801005802d44a10b41400c00802c4500240151407942c0841c0c44021 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 427711591 1250 427710341 427710347
    0x708032e0e070e06030406150b13080c0303092b0c03060c121a0f040204030b180c04050403120b0d050706050903010f06050a05060714070b031e0709260708030301080706 74
    0x701e043c0001e0001444c0d52901c0c1e540d54001c004000c0003092100301c080011410410701c0008192200101d00110307845400d00c10041d08001031640c66601c01c0e8810800d80d007058541c5d20b0894401d400d48140542d44030710300c01d2201d1005100100080c034400503d030001c010400707158060440710300756030f49208071314003038501c4541141e4084240f00c03030710403009005421034508800030500c00300020b00054101030742d0b0fa035042c100d0142500c03c1417035950040205102c14404201c00315148004407014040d906150318081c0140360f030808020300c1d441d21008400c0581e1911850004482e40c030400312030555540301001480d43d004034564a12030b500f40f844030440100c140c0129026100001d0282d02c02518180c2080119404064121605001892070001c556401d000c2c450040110480c51540e038a004170010500100400c1540003004c029414001c0d450f611402440607142001c4108250860040c0400310003569020060840c0c80303003d901149040011014604841410080b156059103a44040d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 427712841 1250 427711591 427711607
    0x606062007060206160e0904050a17030411061602090a0e07060c08120627040611130902030603030d0f0c0e0a1a16021206070e0a06050708032e0e07 65
    0x14005904c104c000c1007200010f400451024049030501c140c05101036400301e690480112000c0d10b8076008102d00c2d0082c069851907401e041e0398400811441c6103429a10700340c0320081101c8a40c003c030390114040440c2820000c411040a800414110042c038010400720007520907000c105405004103403000501500604804c604030b684044843d00b00402d80ea806041c03124020202e07507100c0f25940802d06002d000001c0d03c0400c107000c0d031449000c1c3c03906042060a980401701e602c00d100d0020460a030702121301651500548103450381c017681e80d0302c0d0b00d00000d2950141d030546480052401000101c001142da000c070220034440c2d01d07259002c200640400c20700d0701440c1705034241c500c020004101800d2024004040071103509030480d000c1c020310b401165401014090020859001000f80b0031040d41010b040031100d04121040a045400d200c4000d105000c3c0d480010804071011022030304013200340742d800c1b16906e0500b04130141c0c100300c16042807c054880c41802c14a0721307100b0115010610034050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 427714091 1250 427712841 427712849
    0x2030a0515030703031403130f030f030b01080103021f02030904110304020a06050f030f040f06050114090a0b0303090f06091914040213060c170a09080c030a0203150a090606062007 79
    0x2c3d070750101b08031038100281940020581400007084031503220001381c40c0242030401d18042d0352005000807103003c0140c00c8a41d80f4404605111140004100582c0c804c4044880340c8880c15100e282c0d458501d070141cbc9180200b000d0645e02038100b0340c0e2440c6481b810000303140300f18000c44060352015070702c26040d0307200c1c801c40200349409141000000d005d4900d007403159070800d00c101c041081d0780d00c5640f10b00c0115442a0001043c0d0b1800b6480c4210314680740c440d1301e40100700d40c0c50410035020b41c100042d40c0c0740706074540d540c0030b0780d101036400380903542c0d08096031030302100500500c108070808012000e850445000d942864178000e901001241418400d440c0300e07000c40e00d0003005c06800e250041e62036110f0200f0480f107613000d840f800301801001002410a09a841d2256800d0500f0190384130f080c100300d020910300907804a0180f02c09a2781c00034140c03843c400c0214441005844400c00c21019104580014009034100000090b1003a0b00c14450544511002c12928003e0000b840d860740b2890f203803103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 427715341 1250 427714091 427714097
    0x1e0c07213516020705040f060501080601020601050a17010f020403030801053f1c0e010e030a1e050f0f07092f0d060321020105010803030108030406051b0102030a051503070303 77
    0x30001d207070140b11090707400691406004440006503a14006016202c07944901c040703c98603900c00b0409540c005044c01d4100d202400a0449036060102199002949129602d0a0340d8409038480c4080d43c00e510007145210024010342d0b84580301e040203009034000384100b40c0070380718040910b80740b034814000140d034156581da80d00d100f1300700091071075420065540701d1502c0741c061009411444410400640161007098403080155480b40d40050045144051114003a8105000e0100003411054090341e4012010092400b22140c03030914526200b16018055024030410300541c10078070740004c10408640700420244107007a1001c20b110a440f1403141c6005021031862814040000707158041c0c0307220320b5440400100a0ba994480140b8007801051260b0901c8540140d09082d030350a0094a01500c1034000441c07555261080242d520b106130710961080000100d41a0118210609038040d0321030014025901c0e410304503a61401004162103038402c101c05400304012508002c10340304216030f0952 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 427716591 1250 427715341 427715447
    0xc170408070506010501140403020105210a090b01080111121e150906060a0e040504060e03040603021b0d0c110415080d110610032004020a05030a051e0c0721 69
    0x12b8019640794001b00402c1803100f003c41c110b0151090401d40c800c1c482ca0343c0c034102240210741d0b81403a040c4a64180c01c03a018603410145541301c25081081292200c201240500050b60340e000c03490060020010080848075100c001407102c80e420f080d140d0100c100c41100d01e200d95880e004200941803090f103515a000c0365070600c0250700b616042d4401d540c80f6006000114034850103045050940c0c0c0075421010210b58003060940d9404030141647c24000c2041d0001c10140904581c0038101213a40346004200003008248542c2644464028194140054018807000c64850307012a884803080210500007507400b0071012030021001680030300920004030310400d01401c6840c1c400504540f54070441c1030490a603810640e50b229403000740b2110710795644e985c0e1a0b04040c041c01c0c0580d2005085441c0200310348132829000480c455900d0f41118100c10003a0781c484a5141c000c1003a10782a58004441e02c450089100d01d0350005455440041644039600f52140700c00d000c1c0458190148128506008072 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 427717841 1250 427716591 427716593
    0x2061f0605030a06033306080303041509120e1017061018080303010e0a0c0509014d06090d0c02031c120c0815040c170408070506010501140403 63
    0x1550045030003842114020401c1030312078582d0300420700c1b800c070026201b00d0910145400181120300550000020810611041c1d01d02610386a482c000580061b02d01072002c0038001860100d41d00003180b082e0b0114845a4060000c02c2c050801801c004407540030b6520402e4074820036204038419074098541d49034160441d11a81d00744803805149d09880d40074451808811000780001d91082c0004007141d900a42d42c0c1c2d030400d114041c001ca4050100700f085402c000207030210a4000c0c040d503500d4582880d010040a800c2201142807848118054620300d0000032262540c912404480c0c0c11042c08006030800c2251100b4a155030302c0d82200c4100b01c1d500301120304118148540c0d072081e250f0340020205d50503900c1e801c90803c41400c02d150134130701066031040b807100103202c0750080712052507a83c10003006901d006c03900e044080c0d085840c210310459603804c219000398021003586100342e85e501a107464130312301032030040020b0b480f5000542e13079072180c1000001c00c1e42c4580c14981c0d0a41d81c50160714101451 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 427719091 1250 427717841 427717847
    0x1052b03080705070501020712021204080304090b060412050a0302010e03040311060705160b031b0c030306130f09050105270706120204091a090a110f09040605040c050a02061f06 78
    0x4003030b1071101044420040d21000c110300b40060110907000348100c1d28100c800c1000a480e1140340701c440014107405200401c48850040b0554040f625461004601d02c4400000506248155006146c03001e90071204401401000983c414209101e50000c1000940806245540340a540b20091905010112004503820840050a02d0750f210b1422207040741100c81c1c5211f4201290740003514103000110401c11295640810304445014a4a0140c0351030340d40c0c60096108d200003054980a9104181d1081c0a03142c2135002c20040c6003488002c00c00c1c2c202d1841c0603400b801003500c500c4a40b261004000010652075000f10007400744560051243c689400e800362101e005900c3d842c5041e660034400007030681c5072409070700c42c101520345071440203401100812001d844003410b044440c074644801c403200d244a5101300d800c1d0300d01d00b400083d100d101000001c0c01504180c1c20160304981400818a00325400c0b00203001074100a0302511180d544094010704007801041c1d2620b40781e603103400c04000082c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 427720341 1250 427719091 427719107
    0xf0d0e03030a140c030703020604150203041203020702010c0209010f090b09070207060c03110d0806010f110d0c02121005160c030c1118010602100c0503010311330301052b03 76
    0x800011104d0a00001c040a1401d40c0c00c078003400d0b405030300b107103081004220340ca4149030729948030342c8811030650405403182d031003030030080c0204014581d002519000750382c011407001089079030041c024001036846540401c40d07000c3d1072140c241c8007400c013134541105140000c52a440794103103600500c0c03e6413030000d0031115290460300c16814031002c90070072131f06410f061000c0032a502d110344901d580d601302000010030a1110414282c10410b0440ca8980c0451021400d60b0071540da62801c00781d0f2280500010790340c0c0d452403070584000d100320b4664180408854006900c00c84000710340c00d0841220791025136201c881010001d000848080e12a00081d401c03804540348a00040c216600c0c50110b6129049845400c0c0c2001d40507074450100c460111095001e540500c2803075140c03290444d455641c80400601c030000b0100d1290264001c0c030b03001d028000401020482200344106000c000162200010740e100380581400f400811009910104503c001c0c44501c152103034903910b031510a0f031030803103600b8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 427721591 1250 427720341 427720367
    0x6070c020a0902040801060e0c030f0403270801051008070b040e0a1b020a0507080a051c17100305061b030f0c0f0c01150f060503070e19080f0d0e03030a 67
    0xa4001c1400708050409102500203405098000070f00182004006e031000c040042c140244041d00704100140358001e180e6554005a142c100040b00c0d00d031070030984209100000e0110712902104000107a100d805401c10303801800d500624030501500c0d96082501c558003400780b030070707604400c12042010030b080340b80d26a440081c801000501d6001d4544960158043e0708400d001640240525003e000061008200901244000307001c1c0d104039540343e44d03c5040107a51041000c060110b003407800b902034140e000520902809000051805400c2d410640800303020580c2c0d81c4c49108001407900c2c680c84540501314582c41c0045045554090800b2010f02004101e05448142800004c001d00341120151102c10002e074004135813142480c0b50003088012a130722401c6c00250b068020060b044e00a0300701d0f40c00040c1494424120710000022804804801000c025210001400051030000220703017001d6050310281502c10000011074111825002c030681e940d8107410801000a20130f01405503901c0d00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 427722841 1250 427721591 427721599
    0x20d0903090e100e010e090c09010303030c0e09060f1504080f070e0c120a0c0e09072001060b16050a02060310080f011505010f030617010506010908010c0c02040e0c030d02010204050f06040806070c02 87
    0x340e01011403d42741080c2d0045002c00d4990404c9401c0d0b40c0c200254154410055a106495141c2200000d81c40d1040d00c0d541401000c200707a81820900b211300c2140c005d040c045040715003a01400417520b6881d4022b1080d10284010b503000720304210049021074681e12202c100451040d107505041000400d400392140c130a0010b00846086280c80703d00319280b03c0c612a0301c84640009814402e0000d502000d0038041c010392610380184480980002078881d850701e01c3c1c029000000051400b40d150000040c0080d61252010041007101401002d1400a0300c0e11482660310610440b14a01c2c280c52040c80404043c0d68036201c01e1005500c40e40d60351071000b81ca0326020910907900c0e05801c450700d014203010344459454a04011007542c00c4680d4000414a40b40200004220480002c140d090075650007481a13882d0b0302d484c2e00d80c0d0000c0052681202000b0291002010503c1e4003038002e51152007035901402c44803152008030f151603429181125030306800703400e455640c0d2200301e55003004528201e0340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 427724091 1250 427722841 427722853
    0x3051006050a1e0807030c0c120806060705030d0203040210032c010605120a020423160302040b1207080612060417130605030105010e0603091e01020d0903090e100e010e09 75
    0x400d00300c40360543e0318154252684c40e01414a010014140c42c06801910280052450740c10005420802c0912a0500d42d250404007506d604001aa881c805ca80c000350407480081486c1c540d0808581c01180168805c50741c100c2840c641c45021707020b5403144488140e00c000c40b440401d00085860f107a081c200010280005111030305d40c400100ca03400032a1440035039034805021003013181007511440d649922240b0a11042c48800b81c96420b403101c0040c402c4a10705006207a5100035030103034054901608605100b9501c4d407014250200113064121441c0300002d043c00c0c081426810005141c20300312107007d000c0c1c0016500c0b0b88070142c000c11002001d462450003002a85141c241c2c00049a02900d416900c281c0e4039490305000410b055100462684200400c10030f02c2100280020140d04082802c0f580d40d46015201c44500e0087c060b10040d14415403d2048020800d0350040f10882a2100410403030340540b50200b0a12154045006403007013803a0a40c01071141c0d44900090f0f13076115194000b00d0304 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 427725341 1250 427724091 427724117
    0x108060402092e09050f09250506031e011a090f030703050d0c03180506090d030905040216030210090c12050a0501140a0c02011a04021303050604120f03051006050a 72
    0x7410912a180340c0071000c00f814040b607109405003580183c14140b480442e81400c00700c240d26100c0d0410a84010010454000e01100c4190113100c01008010301c03031038892814a01c141d07016803401c0c607003250120b800000402d010217013200300d40030403170008100350900726164184003c03140c11140380c1c0d5161055080002c001142080400c0f102030140d039070034454401d940303005010b442c0e1000542503101c05400007807080341c84580503260145d40c207d550010319801070800f074401e040c0a400c01c0e038100e40001280002e074840c2d10b411455551295084440c800c0c44ca10070300003141c4001034010900c4140720810000240c140c00301c2e50302c0c03a0080040c0c49200107a9550139003190341d003d1002072748100d6075042041e8480282306500c0d880315a400217206041410001600c0c6041c8000058403903507010903100c00d140c5c1214058406117501504032085810241004140c581c410110f003000101c4080340040854480e0150710f000c0c0c024204103010407030400070705458503004641d4402c100220114800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 427726591 1250 427725341 427725391
    0x3080d111e12160f0c081308010c090b0702090a021b030c010f06150f050a0504032f0d0b07080604021603081f0b0417150108030901090905010806040209 67
    0x30300910401489156101090300402c400032400a040c0d80220440300000c548040e081400e030600502c1c989040e0111a020b4580201e59004014000301440700740880850025030542c42003120407160b03118000000c1e9030703583c82d20f00380c440c100000303412800010203d0002c0d05c1e1a000f600c900c26030f00f03401c1a503605d6026170907459600b102d0790401c5907079101c0b43d40c240e2080651140360080c050002a0000e80d0741402c0d80609210300207404c040030800005107001d00c0510480544018650104042e40080c048040c0c11214804c000c40c40b200491513070031406100c2c80c014103007031341d210b9101b00420341c4d81d0790b8821b06490f5424001c001581268081092034448c604011581b0200e41c82038480b2840d50400f010724800d4000320007014022800342303c500b40000d4180c5005c1d9012205c0e480c11100c282c5440d403400030305044054425481031008136002061041011000d0005c2540c01eaa60010703c40c4d440c82c40605a0b80c6c2031041880d40d8014034042005403c0103a291903002c1c200c1c6803608402880c514040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 427727841 1250 427726591 427726627
    0x2070602040e10030c0e010b0304020d020120030408010b04050106020d0e0307090504120801060503090304051908241f060315030506071106060f03070605070f150b120703080d11 78
    0xc0c0701500440c0b0f805104001c9040c1c484805030041070715022003581000301d10a410710001c2d00213071140c4280000c0381d0440e0f118803040e500700802c007500350450b201e0018441d07940760481e0203505010350030540444403900b02482031a040700d01c550b00426600b22601810b0300c401d42060f442c603407d402017040100703100066000e060f00503440b40151804240540c07030001c0c0f09680c1a007100b802c0210030024002219400019513044e10800c9803204241c107020f0342d04051024943d44180c2203801150200c02e280003144068030f2101c40b07181c0103900c49a4076106aa000032580711010904940761420a200300c502c20307840050a444100c0404201a071640c0743d441c038182044070000700260b2400503c3c95801014800950801e0301610083d428407030080000e03880c0e0409014003010002d000c148202070001c80244811016009205140449820341c2288007401615043c98015040002600c09040c0c000903000100e80c0c110b582c003420b001c940c0545101904076000d40c13440c400000d0101103200b215110301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 427729091 1250 427727841 427727851
    0x111030c0a0e0103050103020622030210171317090316030b100f0b09010c1505130c15021f0b19061e1403100909260a021002070602040e 60
    0x44035200c14000390020b207540d44150110f0304140c10440100f00507118881519134840011030481070040b04030001201e504c003181d0000c0e601c500c445207180700b02034008010030030a00c0d01c080035000694402d801c4105607043c460001b04000c86600f8001400900c500280c0750b03001004090324845440c0000c5000c120449400c1521598041801e0210066803030041a000344520090030310202d290050240f031714050480541c1c1030000301d40341c034000c2200355000601d8000e11640104450700300003082c15802800034500300c4119025032408543c808032981c00310500c03011a8010301c140719805101e981d507040300c42c1c10202c080e6200c01640da480e95842c1142924054210715200110749490b40050000e203550242000c0d180003881e03c419400da10503042d20b05a400d0fa01e00d981d60307803a00c0c08180400565603000302101d91800481c0c50803c140da0040030b010006c80e0401d0140c000350100d10010307902c42d0f021890b002d6400401e010140c50410b40150180cfe41c040e01e0014102580c4500f802019501164 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 427730341 1250 427729091 427729111
    0x10320307090e07020a080708070305091503010302040b0d150e0f100212010b120109051f170c01090815060307080609210906070f020f0a06052503090314011103 70
    0x1072242400b1201076030740c0800b90384020306000da01c58848980600c92410081c0401c6000070f10001418003039021610800401762a00000e081008806c880c0e035042804120700c03403801d18100b4441442c12035280700700c40d504103003810668061009003000800c01103480c020f4600902c05864800202801b400901d0404000e000d0790b0f60a00c919039503c0b00505803c0240c0140781071003103200101c0304400c1d0505582080300300184545a4810700c684170108800c40c1c0d0a051842403002c1003644c268105091041a20030898001c00042d038015900d0710b00c43c0c081c1d07041d50350203070b9901c820207000240075641081018059400301600c5111181c201030044074500314960109607019241a8642c0d00e1140041e9490102400c0881040020303903130307208184015040039400400c035415550760040c03103040c00100510303900d4100e0303990101074519041300400ca803194800c4500c003044101292985002a075150f684c1c0d10400382150703a401c16800306021404001d40d65442001c01c0110004011030090034012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 427731591 1250 427730341 427730357
    0x60f11040311060c0a03080910090c030b07080c09100c0c270c0806010e1c0309090b0603040203031b0a06241d010b0901171801060510320307 62
    0x820a628199107140e0114050343d400c00c8036940e0300c0f201203103612402d5450720304010aa100c02d01c840f8030340f101d0645010041e518210581d01080002041141201d2090441c1e20490741d5480098a54000440d1515081d600802c82c0c0780151400d51052550741e18a8140751030741d0016500c684d01500c0342c0b83c0080403443c1070240d840c0c50700040800c82490f94046040c092200340c00d6800020580e100103007076076061000009034002c4680d24800801c1c03049244076005402140a0704004215400a04ca10301102e440c00001070f009080440c1244d05c40c41e00900298600404410641c081e00d000d6220b11115001b41c8041000284050260440d24024094042d0b0105000d00d03032140103100c03550000c0c24143c240c07060340800c8600c000d2402d044503400354401d600c601c80b69006a40b0b01d202c0b480004a029071000c1000080c1100302104141660000001c01c90a0784400038007040c0110551140701041400000480142658414582443d83c0c1c85280c01965400070100b0380941081d10740b0001702c1e00007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 427732841 1250 427731591 427731593
    0x3030402370f060e031207060b180f01170d02060c0304020418030806040b0607231006081f050403051209010b060c0604050d08060a0b0d0b0901260304050f060304060f110403 76
    0x10700e0a40d00018228050503920050031861b0010f0311628800074260741d12076508505580d070380c040e981d10700407500c0c0043c01541343c80008001041024001c1805034134075020700340c0c0340880001c0c01000003902d40c2c000309034585410600e9441a00010805c9a00c84c0e120b0301e040d81140c8011210041ca203100791540342035420f25004100a568000041d54020030041c4048004a1039201000d040d03040a1007480c41c8460030105c140e4200027402e1040030b20301e8100040060107a900160780000c10300d4241c007210301405444174590949200742d40150000e0020702050790f500c040710300713840d42180c28200000342448102010403203e412800702c201043c1c01c61410001800418048590415550320300000d00c0e281040004100d80e1032401402c010204c0071548900715a100e5000266542d402804100a0340c0d4a0b02e50801840c040003c0094400d4120744142d2002000001e6a00b654002411082d110340600c080c054035400080040c1d0740d03035845241005031074004d84110a24042803850ba142d0f03650035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 427734091 1250 427732841 427732847
    0x506010612090b0c0a0e03241003080a320304110d120c050f060115090b0f0702130b0a0603021b0601120206161b090b0303030402370f06 60
    0x820208903140d800c108080e00003e44000800b0ba10540400c955500c0b001c400390115841101740b051641c05115424801d807500400c0c4042580c00da581c4c1048030800d41d54003125100c0c11744240b10041c0120760510110078484d004503070008c29010074003045200c0c0700511050166a600194004903904000003e010510040c41c0207004040d2060761183c814240e56540c0c0c2c0300340d04e182840102046100c080490801074240289601851900112801561a440c1032035030144408040408143d0b142c3c000505d40000c041a03490a04078038400f14201041034091090400e03034007007021111941d40303420208650f00c2c0504080582445d0794016192240c40c1c22140d090741c6101c69240c1c20340d10100041042c0d5884901e88003c5e0b9a060744d40944031160410020070452960318003c14040c010313414900c1d24100b0407400802c481d06030a051100c80382d035109140c2c030791209031800781d00940040c41e460b1858041b845007050840c0b40894541142d01c40c4144043c040d81341e5002070382c00c003410201c00c110b1a64 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 427735341 1250 427734091 427734107
    0x9020127090c020a03081b070c080c0f1002120d06030b0a09060c110a080903030903030d14061e2101022b0209132c01140c160b06030708070305060106 66
    0xe503500040c500100c02d510058000800141490321007c1c03440107201e4450035800580d24180e511000758184141c60303072241c503100d100c01809503010b00c80c800305040c424608905803420b80001c58010301400031140741c4081e1164841070103d14102e4607140000000340da4041054400d14020100040c1d1500a1420006076008400f007002006034801c1001111600030070408140c0f0b52000202e130b0f50380102c501003411070065040041d81400301280070445074100381c012807031300003440712640c105e9030307507102006030061001c80001074404184a15003070500307040c40202401141400d40394001c065040343d90742a60700480d9146030900100802094407000751034002550b0446120039420310b00d0420102d038001c14600444a00184c13075001c5d020403044106010b010912617406080c02e012070701600175010744180c20b00d04141d243d809001450340c0000606503100364428030080c18051510351900c202d840d02c00380980f03502d401030300343c00100e846e420040302008501c40d00240c0303084e624089019200c12 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 427736591 1250 427735341 427735361
    0x2150a02030a0c05011410030b0c0f090f01020106091b0206101401120603021c120809030d091e050d1205100605030a090b0a051603110301090902012709 67
    0x40a0044141068021058800c1d50b011403410705003844490500302d01508000c5c4410804008410901000a52207030070407041da8060180a00349440740d1102d4240e0f8400e24086e038904a1040c081c0c1b01d890314081100c24100c00b41440041505600c1c2d44a40301104e2450305001c00030b0079400200e400043d014452503a100760614800440d141c0740002102c506482400c1c000e042143d0110f5031804490307590703c145c2c050340d0003801c54403402d0007641500e544e6290094040e078200b40702c42043c140300c920501c0c80d0340c40b480301880510700b0406c440c60000c01800e18040c0403190b51004c40d00c1c4451404110302181e05082c05040107027020084030001400d07090002207024900e40c180030030801c0480583c60038404540f154503200d03a803070341c403114610020104c02200412040310982803050344402c42e00a40e00442e0101aa541c4d2050711080a904480e00e044189041c807006100400030441c46a110b54292401030400f21030390076a40d81e8080007464111180301000e1034164050100702800c0c03150346450 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 427737841 1250 427736591 427736629
    0xe010c0e0a0e010e0603030421140303040f02060f0412060212010f0f150302091f030b1c1712070201091703010e0a1d0114010509131716150902 63
    0x115050540a0a100030b050054605444091011030b425403005c0003210020908030310f0020341d5202807036401d2000e00c07c048007526640c1040c1c1720302c0b0120300007008980c000c592020703504640d50000c0d420701c4039540100181c02e800a6080c080002c03030000c0301c4440d0030081c0c400c0e0f00043c1d0310590501c4080400d24180c21209001a011006014401c80c0c1c0b8114003d40300c3c1e00c2c1c002c8200141d0060100e01030301c2155500c5802158030340c601e441030920805100b01460b0716032010304c245080c640501888640500200d00100b10030910300011070b843d81d80700d090b0440c000049510f440081400089810416603013040142c0d5a403074500b09201c04520030b040740d501440c0c802403955150000034502044050326211590f980c841240d00c1c50001c1d280398404138040342d4003e000c01c003a4110b2111a000091040ea8020341e0200006001842d4054400c0c5882e40e0240d03600c254444002d06190325a000703420713071107110881160b01e00c01180c40c0065558410300f1420b804182c0510030301c1403007400b508040c950b22407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 427739091 1250 427737841 427737859
    0x2120a03020919060c0b0402190b0c0f06100603090f0c0e0103140712061d07081b0303030907060f090b0409020316020109031d062106011103040305030307080a020c010e010c0e 77
    0x413640c0110b4485002d03821200b080050340ba1400003440a42d80c2c40e81340103c0088564001841805001c050620418039006480308603203041c82483e1242011160b89082080c809001d001450083e4466a02c01d8024140300124480d0343c0c0d0303000121441d44c2c0050703564101c0d48004108000c0c10021125085c104400074090b15860030001c400e00003480e0500812161722480c00040b51281d00105214405450f42160055075544544c1078072445031500f9007004404148130003425080010441e03005103120b000420030245401021500b0f50344130541e180400c49009000900d4040a0001d000503000c0c403030340182c1d01e08012200003800c00300143c0308015641810223010200381c0080c015107200440180c061181da41480010304184503000c80303803641c03003020540e4071290319002c1c4060388105400c3e06d485440c1d01c0144002c6507280182e200003085a481080000d601c06d10502074a238001041d070401604203c08032101c20b0070b4036068590020940c3d541c4501d004203a9101c80c20920809050752a245 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 427740341 1250 427739091 427739099
    0x20102040f0b0423120627010626070b030c0406030612021f0201020403061d150f0103030f0309020303071a070e0a0504180c0602070503060c0a0206130302120a03020919 74
    0x140d0700510400100c0603000c00c1c160b5884944581917108401506002540c1c1645080612440c8120071000c1028400004848035624800d05226a506079a03540c00a1a22074800f05442c014013130031801030100601400400003550084180075502400399426020f484508010009003228006c7d404001800020132800d00540c4444401c0b10101c820009d034a0125a51503100f41c0c0603110310f03400100702e589000c420003c0b42005408003e1011440300c1682c10081640d0615107840740251020301c2d1890302d84004000090103061002e0140502d410301061103040c07900080d003581c02c1001d095840280542c00514800074280c040e9600c03a5190400c8404108240081240c1e6242c901a1740c1c000d96039903406400022240e0040300c08580d0002c43e90100c0703521540000e40350181880b582c5e00910400c1e011030490707074240c01900c071140b10a038020040c0399105010340c2c6556401c000705034258041e440b028001c140d07040e0001d2500d58410b0320050380d43c6402e8400d00010f8800303030b204031204d4401400244 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 427741591 1250 427740341 427740359
    0x120305072924030307060b0301060e01081c0e060a080a06150906110307210824100e0406060f090f06082a03130302010b090709060c050a080a020102040f0b04 69
    0x2941000c003403440da0030030b81040c0704078180c04035003264026454030011500c5020000f15800c000c2c0c0a010940091120a40e074011841c2304480038065100150020104580c2610015012409021146c43c0c000781c44404000441e915501500d00480095000010400b5032070a501444008007161000340c154415189401081994903002c0d8208000740251170300c0d54001c0c10003e8a506a40181c500c007101e9840383e03400703107079400000d00c0c0d507000c11241000a01c7c51107070b480014000c1f40d1100004079070780c004901000144112002484140a00c0320461203a58072540304080140983c0d8803000030006903010042c10b403248590201c403c00d102070b2418040720f9030000b1011b80103a5800c0d00c0d040318050000c040014199075541214580074044100192154818070f0401c80c980a40c00800800c0d401d079090001c01302c0c0444141001c0b50800c5000c000452088024110300c5000b40140c80c5129002e13500c2004a80c0601c02300300050b0f4002c43c061002c00f0451a65900802210a0311881c1502d807503000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 427742841 1250 427741591 427741673
    0x1314101b1a04120314100b1c05010b090102150105060d02070303020d0f020306040b030604081e0409090503070b010e0f040201110c03060a05100605071203020706020408010e060406050105060a0e0d02030712030507 93
    0x40c018182c02085002c08503c231600c8500c0c0450070090140415078483e80c0203a450340220200c0c0e4014842e40465080c030041d00b80a06050f9400275215038540680390f2007000281d0b10554046040603820840d03000c6061103441030844001e214000540d590611000304410b0f40c034000040340c0300790024001d2000080c000c00444d0284003401e50b00d40450100402d11603914042c680c0440c1c2101e0600121008004020000303001c0307544180c00384601ca90b2900460b5040c1c81c03045801e80c0c60401441c2c0400d000d0340c0185141075070800c94104075282e082403131010a0603e40c2c1030b2500011a41c90b0b50511a500c141008400050000c83c50b1031401c2236040d4451100480f0a0f0355810145540040c038a014000c840d0100d03006010300d080280000c5001708980c0f40d65079000c071801ea60540c45c0c00700120b224545a4100d41c50021555030b414a0001304004118200000a20403a414400c1810001e00000703001201c031416402529010380b550303240d082045064540c1c1c0c9041c50350103030000041c40705901040d48 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 427744091 1250 427742841 427742849
    0x80108010e010b06160c15230414010804080d06030507051201050606030a1503020d050c0102250302040216060c17090a0215090103111314101b1a0412031410 69
    0x114001c003200c5c90900511115168001c910a420340d0000303880070fa6048201c1c01840404c101d40369158030000881000300c0d005030700074800c0380030850450031310a40c031624003d900705000e0200e003482e104203a1001e904850480d0b1080f81e00d40c001c00705c01c014503d007408540e5401d5031114000d01140c0790070700001c0d071548002081c0350b4081d0b541d855410f0400d418505100c1c0910f50107010013000d0105230810b9591691404c0d021030051252889090880340c85251000d180240f954a40c07038030320b080d03600b00400b0f90030030241c40016068100d10b07000464120700404491700c0c071584a030035103651181d80914005a00a00c0102d2642c0070b1a00000181c07102c0c5130488902c808031506503180e88040700104c0c060259101c01e00c10400c00842e50401207901c95000c14120394013405001c082140800502ca071914050303110700041003101e0f5000c1642c080700c0d1540441c65100c0c41c4150704000070007107002c00c061000d03541516400054442c04c0b4000b03801d441000c0805208201040700e915000c2d04a40302d214860003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 427745341 1250 427744091 427744117
    0xc08011416172e0f061101020c1006050112020903031803160e01080d03050c1204020d0b0106080103060609090c0303050d0e010603051014090703110f040903080108010e010b06 77
    0x201c00100207100d610000e0360210605040169800c00142d420002e4940e2405480b41032000d80001c592412510040400c0b5400f803880d0900841c60a41d095038014051094210a0b540800940170140c400340190704251035142c070002085d41c10400010080c0b080018100c020314410000162680e03000001d546240740e100700185150000200440e01304a507071000720312400c071041ea003ca41024403001b424144d500c00c0c01210302c20a6644070860079544241c500c0742c1e00d550304001d00b6011401c9005240d030300034006448081100b909690341481c2c0c0c8c1d0b0982c40180041d6698005004001103401010000c0038406814010520f80e6100d9000718001403000030180b14002401e0200c105040e04001d05940542c8001c000300741d030300d007000c948a4440d60641c0602e10f02d0845a501c02c1c22115405034041c10000f0000c000150465450400e0280300f02038069101c0c02d070100104040c1d41e0b03802103ca00900c6981c450304903516061844e03082d0350f07260009000c1039050444070610741e00d030542911032400ca100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 427746591 1250 427745341 427745371
    0xf18070807080a05070509071d1512070f030903080609040309030807060b04050106050418090321090212030a08010b030702030403170703110c0607060203040f060527060112061d010501060c0c080114 87
    0x9d000900b501c1d00d212044c8140710b07408113914500445d4402d07854450001504c44480d12030314640f0840844018042c0240840c41d614046200343c01e00c240042e46c414403e043c80c1030195102d0b00c4008940e00104012500745441e5140300055007014014980185540c0c1032103400c207405d1800c000e002103101208200041c0da00c00b1120207141c0700e0102c22850000c08080c00030200b1920031040064211158164000c01000c00420300124001086a1003100320b03640d50b80f0a42d0800c0383d40102c0343d00c050480400c520040c40080b003c101c2e0300c2a0707041020588051156104200d1034040c2100c1c036103c2d00482c150704980e0021203542c0b0386a045950255001c07200580c0c0c6d0343c80b4a4044010f003403801010b42018503203c02c101c1c550708582d0503ca1901d50b410045214583c040ca0032950b41c6034240110780c03d078900c008c1c4520000707103190019820540041108100021001c1700700c0e084810991081c40041c00016000c414018207400c00380103040d80000921540410340c500300079099000c2c00c4030b00512026 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 427747841 1250 427746591 427746647
    0x150a020901031d010b0f150306011b05031303110420161b0608100b0f0313060c091a09090403050c070b0a05120702060f18070807080a0507050907 64
    0xb0f03511208072241c480580140d02c00016001034000c0209078030180c000e034070317000704842c132481e080c100e0205940c074260400745140e882e02e00450382100000a0764940409140340200090300c24000781899051683d40054401e00d035042c400c0c20350f00c2644180740100d01d060b100c0c0c00803100310303d43c0c1c060034041040d0076035aa0302c0400342ea089100306000041d0403041c0c2e02180c00d240035600051031082b542940d40b41161a00d07000c0d440700c0b144850b40b0801071001ca00704030b405035400c1c80c840a9075200d6510380b0b080d910945a42c03140e1096403000c2e4010300000c0d4014500f40206410700c1072080710038151075421418003240700c0100b00d00b0070000d0400307010300c8808181040001701c10481a80a000c000ca00291904500c1201601d42c1e044074080f09003c112100014550030710003d41d19119040402d4285460f4940c40b01e901e207800351050b0341004a00804001003500642040510002c0200704020b20314000760b818031600300100e580003244105d003a0000d000c151a0710802c0080b150aa90325160242858 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 427749091 1250 427747841 427747847
    0xc0c0603180512040f0b0c030d050604020706050a0c08092404020a0f06030e100e1504290411030d0504090e0c090a0b010f1b150f020723150a020901 65
    0x41c51001003451060090400c4090b1000e0064000c54500740881d1200c0c94031400050b41500491140d0440d5030f0091140c40b81115244d04034a82226000d04010314115264551005a0350121030309100f464a40c00140b4945a010213000d9025189201500740340000050365820101860100c460900456001c2001e65030383e08142001051001981e4841c26564100032780540300c00c101c038201a000d02d0070fa64922840700c1c0a400c009c07100032070181040f40c0600c400041c0840d030150060f20011a60748008415107400585001c01880d0651081e03e60310b050704c1c1c211002054201654000d42188c484588003907048000d44058030780318440403943c0782d64003d06c5481c0c4a1f184050750750026134281404001c0d1201d0384801c000003002c0e078401c10405613100c13040c1c6650070741c0d0103244ea504407080c009002041e510000111580700324080031030f060312480701c800e0036a0425142510154080315813201541101a807102c3c5908401e009080e1209848100c3c4400784001004448007607000104d0764040e0384 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 427750341 1250 427749091 427749131
    0x90a0305071a1807060c0804050103090302010902130f0e0304030b01271812090e01050d060e16051002060f180a0b041b0807030807030f0507082106010c0c0603 70
    0x8030b0481044100c0c074000301042c0d00180030641c400458060384202081c4148985a05c80030940c01c200d10900d02850403004400070211440c00341d045542e203c501c140140d45034081150610151500810704440800416084404d0742c003524a00d0f80c0304101c1000050f60813149a811140e6588128003140c05100c103078001485071a8000c11100c1c030708400a150000c0d0480f41d481c1d5107015401c02600300407880016240b002c0c060040300414141d16004201d00d01c0c08007808042c1038814039012803c04010010316281a11461003140181c100d0341042c07140b1300b4102800f0b20400f00030301c002d14203420407003801c18039800050802e2080e80008150300444c40402c00c0301a140fa54401c844022918003410040c040301441c0c62103407412441e0140000ba5410001000c000341c98101d004545020303281d036015140c41c0403002940083c44010b1003280041070b10a80030744143da6615030340701c4000c00c03030039140c1c1c10100d0000c044505002a00c10010f0215106410f81d1007616500d0034000390450130b14140c0c6d03078502d03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 427751591 1250 427750341 427750373
    0x20318030c0a32030d0b01080f040b07121404022b06050402060903030a0e0a060201091104020a1107030c062a060510050d050f060612060406020a2001140708090a030507 74
    0xd0603c1e05101034001008284084800d40d0420402c070400c0700455180c00140c54408102440e1f00104000c15401288290440b602c3d00340310202c14980d00341d000c203440201e040090040c0302c1608010540c100805075803401c0d40010900d107030964040c5034550001c0c1001101900d1103540301e00003421900c40c1e41c21107040309401011203031150a44e8200500c80c2d1210700320a40594452040000d11074014080e4140303441d030100c040080d41901006120094101451500400c41e002a400700403031010700040780514068511400752a040c40406006856240508452401c10140d4081c409007000310306118168004d201040a44a4070180c03115040c96030070070359000600c0c0c54600100040003074800c0459200200340c0c1e00956942c0f04001090441c84403250081e0001000280000c0d0a070b401011000f8407410325101d50400c6540088005007002c80c10452690b40b9108240300040081c00968801c0440c42e2608851800c1d1131411348614203008001c05225000c64b00608102c0401d07d108006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 427752841 1250 427751591 427751663
    0x51b090109091803030b0f1c050a0c0b0c060c0a0507110411030c0405040e0a0809121507090305010f0b06190c0807120906080f060d11040f020318030c0a 67
    0x860f81103038030000d2071200303000214080f902c1c1c84403c5207a0b003410000c014a9a10080a82e1070903860200703182c0c0c40001c028800c803868002c0048020000326100386035005800303854401c0780c480114004031071500001824940b0603040c00c0c008100096031146c1101c0312641c1c0613144022404440c0040740107006d4216404800e0300003c070410110941c80d10207030040324400c803030a0009900f0300c44515161421a10050700b480010008400345007040342800c521750502a0480d10000d00e00746000c0c1032040e0a6890f01d00040c44000c0c100b050150134098420781c1c1c0c003030b02130030440b05031120005008c82c45107800c0800c80800240d9224000e5010300070343c5210a4000e600c9a0b500d90741c619089112400c41a10140400d4581002040c02c61065407000e2094a030b64612080c01d8070340004100101c0c50400c011600038124811011540c0c5560103075062051060001588a06100e90394920300c00084520802c168801d012061040c180000d1800409030815840107401c85035003801800d01d080403051400c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 427754091 1250 427752841 427752851
    0x318050f1c05060a0b190b04050411040906090b1338040e0c120a030e0f0f220c0f0c060c140a09090c032d15060804050d03051b09010909 60
    0x1224210742154003200313000c1b100d142071180170202c0d114200d0030a026120b140034040c481806030741800e502c02d0402e100f10341002401c0a542d20a0401a2505a000001c085840e000d4200c5d56090000301d8181100030210103101e070710400c0201d000e411150030b2101c10500c02c0000c4804043c070419a504103101005402880542c205030a42541c821240030450b0140a41050b10020424041518801380744d140d5904452021114104403201140b0658180d211070f450011004a40c0d0b05402c580344000004802d02b050014502c242046900d4110740718140b211315040e1400c0c45500c84891500036034072402c005140c4058543c120780c0e0f5503601d03c01100c4450000b4a1170f0072140c01c49044d4048640909044c84180708c1c91400f2000d9a40003048540c2c2c410700342c01030b002000745420282d05503003a14040024040380308011060020140d600510201c1c0301c3d0b03c10b0100340101445055402503007405c0038812030500c000b00c0500180070707c410074400c2c074001c141c0a04aa1281d89d4400041442c0340003800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 427755341 1250 427754091 427754101
    0x10f031b0c0c06050f0409150b1c0b120a082514070b0f040303050c0c040623090705041e08070311040b030a02030318040207020604030305070318050f1c0506 69
    0x9059100701065072500810000054114032940c2160241c00800074103d0504e841d003910031000c1c10303e490006410701c0000c1004550030b440c59000d445040400340500f1030b107500070b000707500888080c6101580a0503041c50351103102d803000926080781340c1d03010403a02e0b074800b5120240c030f0000b00300c180d83c3d48042c20000c03280c10601005074891100001410195102265200200030291023038107420018000107010400129028901a0802c1c1c0b0084064603400082503000038121800758200c0c81e1804258500200c3c45600300444451310b03402501c50900c1802c05a40203829401944243d1000c1801184c0c41103440400b80500340c010032041d812a02d2098503032070054192400740c800c90303015602d0000300c00c0d00307440d00040c00c524894000d000782d49080026150002d000200894441e0800d07002c001c880c00507180c5100400046000f41d45c1c0507151049032600803c8400d001c0c1d0241d07048503604d0014480c070760310406040c0402200b15000c030480004071003000c44020403460040c1860040200f080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 427756591 1250 427755341 427755347
    0x8030c0306030706020601030f03050c0f062e0f0302100210050a05180604031e03061a19090b09010c150903110c01020d020712020d020904051b04090201020309010f031b 74
    0x180540c10850035201e4098403100100d81d41c075000d00c00582a0f070f9109a10709c1c0864068001490b0840c00e403c240d030100c0b0b00c41804035203400402e0380d414200c200e860403444201200c40e8600d003210f402d00102410b510b4900b4260214003007079404007078442d00b10000350307407811b60082041c0c0e50064481c0c1d400707014070310307120b200300c0c0c010001211036502c6285026000540e4a5000c582144210b5054490746400013034032102c0486a410500325030281680c8420204002c80301d80b191091864000303d106640d41011800940516844006030301480326110701480950204000c0d00c1c2418401c1ca0100200172240c02c00105409021030800c807550b151035202d40a040c0d11031003020021091030100e0348803045820049940305072203844000160400d40307003804900c1d48102401401130006290b24128a082e40014492201c140c0303003150b07141c4c40a00c030600302006c1a80c0d025901d19085404109484480d00080e480e48601ca88450400040150308174500f8042d0780300d05040504030000d1300400090060103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 427757841 1250 427756591 427756597
    0xf0f041e0b090114131d030c0106140109060f03090204020403020603010909020405161b020f041b08070302040303080c0307090e090c1804020a030b0414060a05070e040606020d0507060908030c 84
    0x7460007802c03003800100b08000107826103020100003508004010b80c0d401c0da510028100d40c100040d40d075481605c4048944410405030085074102d0b0300008560f032404106c94490300c56031202c0d906200314044c0400c030440d01300c0ea601030328424509000c58100521710005009201e01d0b04002d5001c0404070001c0360b03070719250b401110118070a44041009444040407101003082100345140069040e0b24060550b0314103021401c1064405050004440001000101950280c51503030700c0341c2e03503240001140c0c03c1e40000c4940d000703030550402318500350441d03c0041c181c46005104101d51900080480d148505c81c164030f40051011038003030002424030a0703445440e466034032805c500c40c643c105100450381ca03100280d0707801154002c00d5088420f156950791000020000c10981d00d042c074543c4030302c1804409210303c40c0304600652001a0a02d00000060030982401144c0e5005500d02901401303455000210f0f0205d800840c20f00b2522141c507450008080c0142d104010320326103008c014040e40070550350203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 427759091 1250 427757841 427757861
    0x8010e10050d1a06010201091e050c0306130210050a051b102f1c0b060d06030f02090c0a08060f0402160b071b080d0216061a041a0f0f041e 61
    0x43c8201d90707204d0700012800d8030f0714100301a000c8110546010380392000d007150000001d2041094402c25001440000d06040d001c0300d02c50850210100c8020441c58040c0d124080300d80c0504140e410511007100c003c2c20f034043c4940034a000e030018410b000039044104441100c02c242200c1c284080c40c007000031001d015091a00110007109408840104510345105880c80070b010b40490f04610442c0d000c10f4030240010700c0300580c001400700480c0c240903055000e007601540c0180307010b605400c501d10500080355002086424000b02c10311061400715400b07a0426000102140c2203811180b0075400a0000d20030416142c03601082c0e441d41004005805456901c218180e07244e070140b80b80800302018811002c0040200035510400918130a00c81541c045e02c056241c0e0601482007143d0785d40c80804a030a0111301c0341c00b100490316281d5241ca01030044090b150008000c10000c2c0c2a4000803a880380d000e1100741d0310a000302c20701101d0b42d0311291b1104516005050184200120040510006010b034a80c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 427760341 1250 427759091 427759133
    0x30b060906010c0f03031a01450312020c040203091b12010e0601090b01020c090a0911120307110613141810080c060702060301050d050708060106050a020c0f0108010e10050d 76
    0x1859150303540c00ba2000301e02c00355560300c0341221060380e2030b9801180420303040001b802203800240d8844110127460a1006503100d0640c142c00c039500100060718080303810503034900c00c42c010010042c1c99640810090340d29180060b040c203551100e04000344090000714200b21096180501c89400b01c2c00000c0c5050489280c884204100c0c0030f1803004986071183e00140a03003042d151404254505450b03800824840d018180c40c2c0140c9820100044010261900321021a030000c100d1b4001e010810042e40307204c602c11511103181248180b03501a104402c1d2040c00101717406109061600d4544101910000c8480300c00e1002c03503d801401c1d003c00d1250350083c21006e1045140b8a01141060300071a03482c5a00184950704582c80c20040024481d07040d14221018050407400107420801003100501808040c2c640719107415401100a10702069581203e100300000000c0f007020b640c101401c2410f60703e8000d0891815a50090030104d0142e01c2d61000703400410480d0380400780040d1051814441105131 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 427761591 1250 427760341 427760381
    0x20309090c0a022a1003090605130b07030b060f1207091d06090901020c0a08041d0c03040b0403020304440d0e01090b1b0601050307030b060906010c0f0303 68
    0x158a1400b640c101600542d012250030030001c0e0805503d0701600c052410303110000b140744030205144080845985020907121501c0d03000704505070260550041804136000010b4155890f0031b03030000e03070150451040c9995241c02d00b64a480c1c44003107691051700b0044041d44c849241f10004403c0a013221f510000440080c4085207900c0c10741d0303180d45090399081d9176036460748607032040180301040640410020742d4200a600144081070002c840158001c0c5c1c1d01ca42c075189000f1200c01d00c14039074480d2210702c4240c6001c02801c02c24000643e50002c1e00300714001916904c0d8501640b40d88125045503000700014002e80c1181541d071014202e000c05088030940040c03043d5503844200c100312002a500b00d411403810701900c0c61040d01083c950351014903080d00c0f070b03d64400e04201d030b0f80e02401d05900030700080f134125442c0c0c4c2d40401005004280c16002003900a140da201d908070301c60701a204038861840c560215030f041e889006480b1880c0e03040049000004550315010b0000c6c03140d0604829200d40314 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 427762841 1250 427761591 427761601
    0x30b0d080c010506030d020a1b0503060f0919020105221206020c0c0108040f0f0c09020d060302210607050d0f0501150210061a030405010213030f0c05030102130506130e0702030909 79
    0x10a03111b1944902c1d4001b0144e0301400c4d80c41c5001015110407440c80c507126050002056a401c1001c81d014003221030b01d6441c0341c2010105103003414480b0010014000141140c400180da10070101c8a0740c41408451400c4503080ba0a90500d410301540900f00d001c004211034424007095500403e03070010000201d66048a1080056880340e50850700541002d083c00318100225030005081900d641c800c0040d820b415031070f094080201c0e000503410f03102c01c0c0d507200014421030900b0a8040c001d48001070352042d40103407ea8505903500030040070a81003143c00b00704a20000b031250442801d440203410305118a40c0c50782c60f21782a84200b801030758014440d41f401642c2c1c0c0410307842101c054801910000d2810445481503850aa201038070444c0c13190f47c03c004404980d690b400101004d076118000740314101300710b81401103c851460308050700c80d0744104031141b1007068078141e18040b20070641d0b005460b000c034100c0005084185078418064a80c541082105d1240d000c0010400100221350050030b030744072 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 427764091 1250 427762841 427762843
    0x60f07090f03020603041505090a1109010b1c110403112e05070201020f0105160915050a0f0c06051f06050301080303043302030f060d02030a02060307030b0d080c01050603 75
    0x41445036072441200c081040c00075007030060086501501410b0244254002c2640002c1120011100382003650824004a4104a00302000314101c51003198081015410180e802100c1d1298101a2100c20014045101c0c03201454000c18403911a41c0b060541f1640d49040102d26007903002841407152a054800d800540c0c007140c8202803e95014102c0c400d00300c40d030348040d00c0d1544a00000c0e0f0661084100f000a159400d01481d4070840070019001e500d00408200540a4901074101940044a08420b2031003254810f083c0c1e00002560b2070700c102520300d042c20984442c1550000030b400d550500b4200480074200c4c5541c03e0f0600606074030913030556514882128a400280100b01c0503030030800c040b070081901c042800807440901181610b080078440544104607402079040b2001580100810401c08120b080c285d500c6041a00d00301401065980044e4079021501c800904c101000b0010a46c9544294402440c0100c06000e10700700005a04103442c140d0481c20910752103600b401c0000703245085c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 427765341 1250 427764091 427764107
    0x5010803070b0402150d09050120120f04320706020c21010e060a0b09061e01030507120609203a0f140106020334080c060f07 55
    0x6000b03001e2a2054070759501300301c8805030403011022501c10501c000d46161460744100604d013032084000203080d90894100c2d51428000220202c440b42080c41621000d1110800d81540a52401040440c03076840340340c09640703481c54ac590302c11030240c04080e00c100c086542801e00b0210906c2c20131984075070350b5514101e0b81c4611041182d40c002d26a025104454650000c00f64402001c500011035980d400700c0590346460790448080307100c42d41717030701c01a03110b400c04400042d0040c2d42521100305d0100c5c03000d250405107036403203c4941056665400210414842c19074072110342001e130b105104850783e07010751340060800750030342d2040d1100d80b284040d0500c103950708803000d1500c1d1070480c0301c07407000701c00c0441a002100143d0080341280c602c400b0384416a18481d8103000c030300c1a0000249000045548944144160440f6007954020456800d41c400402129114810480c20380c05850f6031103410150340f01c8512200074011a004200f1040d03180c400300388203110308113003c400082695103140840d1448 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 427766591 1250 427765341 427765343
    0x6150405011a0702150313030305090606060307050d2a031b02120d0902090103080403110d1707020f030a0b180616050c01021b0c010e04050609130c09020415030501080307 75
    0x101d000035202c55244048809801c240d400107100c0c40f01c03210355044030411075000302c03141c6850300004a99081015054802c1d01e4000c1c508400601e101d01c0d210b404185944006401c0505000010802c2100e262558202a289186c681910303500c42da2a50560b610383c07000031080e000070905003002c100c1c0310099010f5060180100b98018111142800d40c4640d103503111161074a000c545a004460141c0c40c1c4c1200c56001318410000e1540c0d8625504085105500c15003043d40714001d4011140c01050b03681c100425884840e000840c1d54055910014500c03051100a243d09030003903c008074244500091024441c1d548550b20310702842c01b10540d95120001250f1441101290740c2e403031904544290041d200004404000510740a110100040c0d500054603541c0500e603c48003e030961564000e68800428000f5101030005040030340c001043c03100d00a02d070780054088030b42e802c000d200205c000ca00003402c06c000c0840d03403103850302c84008078074800c11942d1303021a0901000042207180041290005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 427767841 1250 427766591 427766609
    0x15060203310b031b0307021b040e060c03280c030605010801152303103b0703020412080d0605120d0e0103020d0c0c1106070c0312021e0615040501 64
    0x8a0814201d01c00319003000d4000f02001c070946031054961080c91000318003800042d002018140c121410b00c1d0700d988e0128040e1405242000540c0101c084001395181c2c2100007161070315200d6503900c0180280303d4041c0111911100c3d2000b05079008050f0350301400344480300365018800d080c0c0f01d0b001034400076000c0c4141484200358104400240344600050030241c0386034920303040c003650f8039500c80d2030740c2e002680c5e00000180c000c4800c003c1400c1001da21102e94000c2154400035001a82c00489500e41140c02140c28010fa900091070862180c1d04550141c1600c1d03280c440d05005506029640360404026401180c8ca4100003050383e20f4014943e41c19103101c1c600400c40e0b10110403048440407800da4215042c10b80900c04040151403c1c00f0b0000001c40701c0c0d45083d040141c1d0700340110140491b64926001d044208030000200c2d800308100d80c00e4a030403108910740401c520108a28182601d04050300c40d500740c420285100e00041641800340100c4100542c51891404c00c00c411a40284a18010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 427769091 1250 427767841 427767937
    0x120c0907050d060321120509030d091104050708090105072307240903030b12030f030709030b01140306060102010e1b03070b0c1507030902060403031215060203 70
    0x5a140320348020901081d5151020072003030384d00d0351460000302100d0800404044a07040d00c402e41e542c040e402441100360068140954203200001a489204400d0f0300c0b805580c4031000002800000759a1407074008000d0420061740c5001080100449001e60740c0300c4542d400c06001c280700c1c0d481002078041c641d01444508210725540400072001e540410411039102e103c40c242c0342c40506030101c20107047c81c2e42c8400821740c6421031030014111b83c08005601e02c9200100c01c092120040001a41c40b840300541100b07640c0d8480e41000d40d030b003540b107520060850720454008242d0702000300290360104410303012180d1980b120401a42605c9901500311880d52240052500c0d05100c107c0c10361105502601b5965100c2d1244c504034071960000b01c0b10b120b42d40c003101030100050300411801e50300880324907042140708103640c0042c2d90b0384a00d210240400c421281ca003164811035920000d10000c0d09000440f8040e59082e0107502c0e500824000c03683e4003500d030b103c046008204240c3d8080c0c4082061584c0ca = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 427770341 1250 427769091 427769101
    0x62303060a0b04090f051014150d1403070501020a031b120218120615091003061508100504030e0121020304140615030d05120a050405030c0d090302120c09 68
    0x2c0000c5404150f200307455040c6407021441c14500c18140a0082018200582040103a9401c0c0d401000d04c54202c100c9039401c03c404480e040740040369014040300c01f2210300c03045040c0720018403c28130315070314180070015200d410804150300500e500c2100352014004c5401c00002107100c40d030382746481404070340e484d03944e0020b0702426402000440400401c008034841300e0800316203c5c40705201180e12a82c054814480214002d881d13145080c4c40072103441d6046d01d003941c6100a49030007840014081030300d500100518540300c240743c2c0082c290110858091000802044000e0841503e00350081000d40030b03100c580e54452940c120b007950680d8542e041024108041e84d001707600041080d507608610344110f88258200303000c083d001d400b0303820501415203004c004241c145401c203038080e010722000700034940c814100d14002c0e0742d0107001400c1c00101070340c803818024114440c81d140c041580c0110b62902d403120b900003005d4415240242c1d041211051440b103900e41c0c0d0310740aa21f03650711a200c1d00c0012 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 427771591 1250 427770341 427770361
    0xe0604020d02010318030801180203091c02010912020322060c02060f070611180402072f040203070908070906030f0f0c03050a111305040c1e0b040906230306 69
    0x7004451061400041401141240144801180754201c0005a081004205083c100710341c0d072800c0521070404502e5030510504580c2d41d440071180340341298500b0100411910300070b40c01284104d80140508044003c00d200080d140d44c00f021400d50b0184611710501240342d1a232380c50348243c6032a40c85250480000b5000c000c3d181d040121042800d20b000c020040000d121400b0751601480710280c125101c0782072058500310b0100080005014910501601000c1101c8241c603060544040e40d03982080e100305e4148610b600c1880c8100341c0c00c540000288207213507500001d60400c45600d002030307889a03034440b040c540540c2c0c0306120252540100d01e6807070000c9511140245490b901c1008211442c556039600c00f410111820000e58101030701b000d0b15030560414005180c991a40b0500410062038143c0c0c13020891005800307441800060966000d400c5071000070454007a02c1204000c50300c0302d617985019800b803c01030040340051204410f490058003a455a50f442c0244002c010b02001c0da60bd9000c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 427772841 1250 427771591 427771609
    0x25140a020f0d081e0a02060a180f020303090d03020c150301030c060503180a03030204180917090d02090108070521030405010513031406010e160815011119060606030e060402 76
    0x340c070020010482003840b0300c042411065138a079440d440d00d07141c00b01002d0103414000010f013030410041c1489407840c1c8130421000d00b000d4995124070030038a42501030003c2031a40c05103014040e0011207074203003802071580000d410082002e04444850000790340c030850f149540803c1c400100764028041041c40014003410166910003010480190b20b56540c448040c0351595a103407c1d404030341c1c0002c060184003103450803014107078050365040c44015034030756902c2481520003003030003041c801c081941040380d5506591100301b1500100051000c0d43c59444041d240c0c1d00e01c1c4581807203110f008041d031091120114015122079440e102039030a040c074003001900e40758007414407600142d0308902c02100160b06405069400504880104850342c14602c120181d05009490111001501107607000c00a03440b00c491580800d1021040c1c070080e80700340050b5006c04090550207014010706410400d46688400000c0303000c1c0c0a90404c0c04401d548440540454079032040c00d40c4c04c0e8200a00041c0542000074003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 427774091 1250 427772841 427772843
    0xb01170c060c0a0b0117120a0e0d05010f0906050a05060f060304030806061c020a0e15371106060607020d0f0f0606060c03030608030901051b010225140a020f0d 70
    0x161000344a460381d030081300c4182604070440901e0310314180041003508010ba03122100b0031019907440c100c00038a01503c0000300c1c3c0b030003070710841c20940e0301e4003002400e410078520440110014403007001c86161050241c04103c81d61103815107090002619407a041000251101001e00401c0c6507480382c4d24100c0d1381c217000910440c0c0240c003c0160140620700c08c43e400725100454080180c80c0e00b0300f030704000c1011410548040c82040919401e61004d007030a405c075080348020401403070603195490362107a04168a503160602601c40040744540c216005003800ca1144503400540314180c6e20001000001d01510300084c0d044180c007a60100004d5060f01028442c40c00b6025041a94070942e4440040d0b868036000200058000f90101003090b03058020000039001040286003812120130000b000750007500010b0117114920f4000300040e01080d41212010b80c11020507040024060800c02c400c40550300c021100071200c0d480082c48207001041d0007202c5680240b1001c007207814281080300100344918 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 427775341 1250 427774091 427774093
    0xe09130f03051e210f01140d021908190b040b0403020a060515030f01021e07020105040e071805040903120e030c160e010b1824030f040b01170c060c 65
    0x15441c2140c0d03803812444088450030341c0c10366141003400400340d20204014440500450708424080b10045c26440e190540311202c89001c003024020000802020103804043e4014100200d41c00c1c0d02c10031003440e0010f844c0040c013203031410a8002190742c1a4a48000c001d0044104140030a001682e42c03103003190064000d00c12a4100541c5031142c504884041d42c100704801051840c0d0001b42c20180030f522461100c1328000c500b8440d9010194203003598a048030000300c1000540301045a0081301600c2c05000c035160010b8003031410401c090014042d4a4a013000004452000070b0305190601612845903450380e603039114140c084040c200034103018040c07422603002c24000100242d40800c10103507042004070b0300040785071a03c0b0140060741c0c1d060304400700c2c105040054503404001690360501a4a05454214050411501c50010700c0070304010650115000000d0103a000c055000c010b0040d03001c0d030307000841c50344e03100d814020b00b0000844407112600546d1600b0032500d005070140c400c00c50614 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 427776591 1250 427775341 427775347
    0x21915020f0a110103140906090717060f0405120711030115060e190b0c07050f060c070303050903100f0f0b0303041503020306060912030a030c0f2f1603030e09130f0305 74
    0xc0c5007086c0703c004031540390f01d5a10034010003440907820032845d8000c010981d080f0032200e40c5610390544506008107822005000000490300b00b080800c200b20900c02d500e002e60740c80320403e182840300b140050202c20702ca0742c2892601300522501c0070072001180c080b500d1381080c1490003402c3c805001da04460303004940a40f440d0025400c43c08000a240c00000c46001e031103006e081c4030400c800c2c3c07800d0200d800d0040303c1c00d1102c0b40d00000d0000c1d001d41602d406040094507400950006440c05031415254140c241c2402c0f180c0004007e160800164070074145030a00041030b115062594900803031040030301080f030000d2605c0035180258000d503001040070b42410301c0c114810003c154a2101c0e02468a0107a0001401c080400e41c903124841c048450f034640050848440340b8000c00e4140c41299490015207150703000c038101701c240b442d80040c040703602d0280c0741c009030090b030030b107031050b84500c010750108840d00c1442e1254900034924900c642c3d041d020403040048152542400c403d49504210f003800010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 427777841 1250 427776591 427776611
    0x1170a090c0b120a0501050d0305070809030d1110050403050301090e03041203020c090a0b030604110616050c0a090b030a061508030301030b041104020306090a05070c021915020f0a110103 82
    0xe003a54000350401800559840d9400c0c80440f16a00000b024404441e1900f001070000b0764491303e4a0886542504c1e04030713140c0e6a2402e144080c0d11400017050b0303140c445c11491041489d04454007408041c2001c040d50070002c1e140e42c488054030740c100d42c0100024410401400b0456aa51003403482c1c00e248421603051640b20b07480174060450360f0070240c0c0580c1c0180d01c0a8841c2c6016500ca81d400511030b00e040c0820554040866503c100203000140f13411640040605036450750000e0352910f0040e0881805a101c0b6410080c0d1030340130704101c26004244440020640c0d085e24003903003a41200107002890018a0760b15260020000e03600100114807078081c000400350410005980694081c41030a25141031070b252944002c000c5103402c03800303140140200100703070707480075051680085003040100d807994495000710760340c21012800952203c3c505a2081118903c643c0b018192a1001d0030504003520040c02031b41e1310000c0e1201c1c0d20365503000040030400104400d140d075400705818100451140f5030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 427779091 1250 427777841 427777853
    0x906090e25030f440a0e0607060603050d0c02090c03090a0804080706120b01051c06091a13090203030412080f03070e0310020f2d0c070312020c01170a09 67
    0x3403100c05035100c0900003020b0200d214a201d13950094440350780c1140504828801d844146480d40f10300750104407000c122400a240101c10801001c10020f01f500e0740d40c019071a000005200c94007054503503100c2d003200603e04900500300c0d10986600204070110315603445c1c42c1e000c0140d200801106007030144580c80d0000581400180028098030800303048a40c0c20840001c00c00b103a001601901c41e0300b448211109642c01074101c03501540c031405810503005641500401034086c0d0360050031020f18020280a00005044440c1000882254010744c00b4403200d0183d01900c01082c030103941900100010405046403030011803c407449400c3c0c0c0e83c24280b84200c17080c1c071174200702c40741404035410351600e480c50701c0c2c01e120046028171200411800d251a1250840d00b44c051180b5540d00420314040d00d080f00325480d55006c42d0343c0405120b450791100300c94000344c1c8a9a02d0b01c8110b0b01400a04901d050381400811403140d09103060b510640454003c605d0400503440140c01803040d40d968246071004111 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 427780341 1250 427779091 427779113
    0x8220203010f0c21050c190e03070909020909030a02120c0c09130302160b18040f020409020405030708030c121809040605090c04091509081b070906090e2503 69
    0x11240c660900405035408484a000b00c03d074a813040340c0b460b1100300410007800300c1c1642c03020007405400309002048000b054030b00c1600c1e40c41c200d17070511a109002882036071580080e22010b1003a61030740955101da6072515034900841d01c8010141e0410314804600515107005048403011880403601162501008254071f9107068804a0048000800340d5003030540400c52161160100e207a0740340d40918101d1243d65030f01802020030740d040081005800184d41d6900100346500e1640e00442d0f072196500c0d015002940148500340c040e020f1500002004c06000c01900d00303c0a426001c5e0180c80600c800074035075680015407040318100c200c02c60342c125403500000c40307229a1044000080c83d04240007243d01c0c1a20840f0b03118412410a0591800942010b003407a144540b20a00850640e4081c58071007818040c1468030807a030308400b48008c02140d400642802201c01e900760400840c3d85a41036242076a80c9002418042da118090390048072044500e128000c2100b070342c18291035501c90340d454207148 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 427781591 1250 427780341 427780361
    0x170c03040f1b0303080708040f02011101140a1b02060702060a0b040e010f1a0307051c0302030f070516090203010b0702150405042a02070501021216080706090302070608220203010f 79
    0x242c0103805208044d04070755480d401c20002e0038404135510b880e9450510003800b4032130003030402c48142d07810021700d402504502e6855050140c0741050f0f02d40941c940c0000e00340b5101080750000b80815060355103001242080c003441d0b8a0703010700843da0f030300440c0c80003401100d61044c0d00140c1da44035401c000344c028410f034039450454040205014680343c04036618039500d202e41354400d0308464001c1080c0d554011900200c8041940b046410360020709041e800c50107403c000d0800c0c110700140310410440c0c0410030b00700c40111188034203981c0c0c0d02d5184010490000340141c1c080110304000f008098a446148000c00000140304e0b20b00d0301d9100d502090940d200c1ea070b0100d0015840781402d1445080d103a1703003a015044c1a10007401740da0301d0400002c1d52400e109035203008000c40000c2c180700307203c07401d05070300c0d0401d402c03e642075550840ca19000000300b000000c260010700513204081a11032140c0c060324003407450020700403030354450911000103403500f03014226803565948645a605c0f4480e13001d05d40240b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 427782841 1250 427781591 427781633
    0x9061b0c0e0403080c040f030b100e040c03031d0f010309021906030e010b040902010206040b0403170c25120e030a150504050d0c0c09050601050702030715020c01170c03040f 76
    0x68280ba18003d40300380c1c005011814040014003052010304001200202104c1c2c21a034015416142c8108201a144264212a44c000300d54010041407004200e12241164842c0c1c1e10b8003058080e810107140c0c90789162041950003203016403102041c0d0b12a03040b546615000801011034020702548104420f01103038420000b19866401000c1e882900b803040318031260f0142d03030501400c14907600007510b1b00d5000304028130610700100441c0a16111b4001401244611354601820b414818500f20307a5030040440314030642c0324a546d403a03c801c1e140c50652a2a81d200d61084d8809103111001d03102d0402030000c1070b806100303208004020032801618a0700d0000d00c840000381905160401070b0410f420300e0820320600c10101c140d00d0018210980403000c841c40751100041c2c0303848002c0121080d00c07806001960620851a0204212455202c0f030b01000d2555021150402160801510904a038002d001050740c3c44800140300140000e0055038858440e11102150a003140d440000102e4064840c1f155 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 427784091 1250 427782841 427782869
    0x50c16090605011101150504110f072f030a060515090a0f0b030d0c0b061f090623120601050f07032102040e15030f010e0f06061009061b0c 61
    0x7665130041d07100070f400040c0030000e105080110351240c5885580c0d20a1074003865468140481004d5613600381d6031244038612600750b4078142824a04854000681c004800865a01d4500740140e4540441e450355000a005030890315510b445420041c44024205996a520010f242c82540e8461100c10b00c18901c500c00000c0c4041921800c1c0b084501007520b0600a82c020a42c0541c0542c101c4c9070002002d074001c0074803000b5521170010800030200340c55503500180c001105250000c3d002460701c0142e41c15591028100403070149045840c100507141c0c90074104003041403103103803078901101c15404881070500c00d18003c40c2d0045c820325980000d0043e000200a00e024400811740001020391045010009506007401c010115080180c0a0704642402907100e52918803914144145082d85030840000c2010803d0300203541d440f100b010454803040c0c0501000230f8000c6c40c1ca1120744c80040ca4503680c00103100e0403c982682c81c0076506580030b109201444c410780004401451000107080740d6a240d000d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 427785341 1250 427784091 427784099
    0xd0b040f231f060501022125170315090907050303040b1207021b040905210d060905040302210415090510141c060306090302010e0d030e0706050c160906 67
    0x7480403626480041103d0070042c1c100702c00d80e400501c450356021511042041842c042e010310900c0d126142c1a540e10311050584410440501c0c980c0d400b1070f40c01118114281076100c50012101d00c800c6030808a60520146124018140383c42c1941d80501d00a0403211000d40303503000a03185404c10303401a9070302840000c02c03461100d0000d20480d040206400200b100507036130708100a05e0b84010020364042e80e95101640180141000284c00f017003900c0c6003294031a0404d241c004801d41c010817952520504180300003411102c6413040500c00c98160303000d0448c1800c80c0d5000c5882004681c4407281c160300c20701012a1f101032000f9000d664680c0e640755801180e18007410710500e0201101030a0510048103004a0524071903401c4402c126040320f1000748002c0580105002411103400203413100d1f140c100320004150b0158000c110000d0f2607021105070b19807200049007690303540d00c8620300c0340d0014202002090b001d900038110660150054803e110f29500c1c60500400d205d90210251139101d280400c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 427786591 1250 427785341 427785373
    0x1090c021c050307050c0c040e42070915080601200a140a0f06241404021812011d0d14030402150d05060109050d0b040f23 54
    0x3100c1452001080441c141e11001500502008001134140a40015443c94048052101c10b411020090040140085991410741d642d07445107103186000c800d81c00c100402017080122056104001000d008110400c1d04c210b0704110009400031091100030300002c2000501c3c9001c81880300c1196860780e00b5460140c0c001402000440c41610248900a10350009940e01040c059002d076000920881160b9200e5841c601e0a0300107200a02800d1107200300070104801c036000038080031780560a1120041044074441c044034030900c19814403140d1500c01d080a404c6c00d03009040201c2e105500c6840c115190004075021848400d40b1901c265580c8003640d48540c4c1c2000900e00ea01c0c0301100504440850b01d001604128000d0301144040070084000703801c41d690031102d04070000011200640340c046050917200a00800c3d030b0000c0c00319540c50408034181c01c02030704c00b040640c1c000c040101070f51030300c0c0c8400c2c070100240c0909498400c426846000000f507860040b081c0044440300910380409101960 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 427787841 1250 427786591 427786603
    0x180605010f0f0305150a080717030a050712171603050c03070f030504020a0815070207050d020a0b0703230405130506010c0213091703010302040e06091e0304050901090c02 75
    0x554180070791150703020819540b050080110760894180010380c1d84404034422482c1e9040301c0c06a0f44051481d80120700380d640030410a080710a071482c0744643d0405000040d0300c9000307503005030001550510010001c10f05141c0000c02031112030401940070415111106800700301144c0f00308001c0c04440100344d503030f41d01d8032070503901450f804945810b40c10480402444102090359a504050701c68000c1410b40d614040700c50010088481141c195560400c1056440c01c1c044400d4805802100000074090130100008000158000d000c91045800c0c80c4184c2c2c01a0000c10f82541044510f102c00000808011000e08480188030384541c3c880e403802003003082d200303010301032280014104000d1010507600155090304c0958111a4a225022946161001003400304006441c50b0525140300405081110003141600d00030381c1d06210014001c0d410071ba0320703e4281c80a911030382c09840c150000c1422108052030880c50b080130380c1d14050b030f06c00c00503200324001e0308140c025175600e07000100e03515010012 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 427789091 1250 427787841 427787849
    0xe030307080a0f08281103090109020a0f030803070f12060b04090b0406030203030a030b030a0c090510050d051f091502040e011a070213020c010c08090d090b030a020c070308041806 79
    0x21189500e8000c852410102680072155002c05c81c2c2841d00c1494030240c0c00241002c8901c249250301d80c58400401c0340a0240441d0a07409807282640115400382c0140890003507070b0304038842d0341c0380d500e6800080340d070f5880b014504c1007008440394800c07908082d14040d00307004045010705c0c16100e86c1044002e408840320840c1151003285003000400040e203012003038543c0180320f4140016000ea500c40482c1c240411a94018070b0501d40d60303400715080c442c66210500071928010044000c44c1c440d81882805021076101801d6035101c07500d048a511400c1491103011030705680c02080c2100300e5900c09204000c01040c00c00709540104090180703030120201d0f5030050842c42001400a540300c0100102d42c810b00c50040d0055114543c40d0107180010340407120030564050003080342000072000248000815544c5200c203015940402c21150f200352800c100307483c2140212440e546034403030140002d5100e805110418000d58038000042410b040180c00101580c01e800765010428016007400c6410ba0b0308 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 427790341 1250 427789091 427789097
    0x608030c0a0b01061d1005130806070311091e06090a080709150515030c0714010e06251808010c05033102040f06080105150301050f0906070f0e030307080a0f 69
    0x7903861400301c044681701d51026820303500100005508482280c0921610050003449403903800b0014500074009003107481140c40d0340c0c0c10088000b000e0b141d891140305002c0c1d541d5102480c510301d410070449400f052011608020b00062801c01083d000c078580148551040e04030390444e800401076900c03103002d00060b1040d00180c1c40216801c2400180c0e2514003d4220041d00001100082178589850105c4e119160000d070000304010010401074042c00c8401600500381c00b0b0040420314440d5000020100c1903401c40100c1040e130380500088400d131440140321030340c02801b4071000845100030310a40c0e070905c803543d070340560704d160481140450350501d01303030640343c1c03a81c480007448103c100305a100300082c0d0480b03011a00e21501140b0002400c80c64100d000e465181500f40501490740d1079a2200c4000164001d000a50320700c03103d6402c81c1d02c115008019034001e800000c14243c443c0c000c15180700740d1400c10401150700b59002c40d02d56042080116504000020481c03109508030301550881c055601e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 427791591 1250 427790341 427790357
    0x20f060c0a0e03060c040e18011d0d090e07050c030f0313021f02030f03070e03070e1e060a060825080402041a130e030903031602180403080c0901030608030c0a0b0106 73
    0x20802d17600e58481d910403983d03003800503000b0036109181c034035a410241e61914000e101c090980c0500c20201030035803214503070621074180b441c1090b500403038142c4100c0d41c04405480d0140d88011050307402e644030214612080c041001616041d541101c055802090000c1030744100800368418030100d5910f5540d1301805c043e500142c000d109600204980a2142e40300341c803034aa4641183c1910911240e80e41035030302d4000c0321400300d042000b1884083c81a016403250000c00156000000420941620003c2c0c00072051101031100740c1c01041c2140d00b02c103000542d08a09510a0b911220201e1590314120004480b08240005e6161034003441007100311034440b0b041c280c4180c40004003506640c4481c1108203444501d40c044245091066450b00c420180569565030f01c030004440032a094000c0c203c2c8558003a01280c0d105003a400c0d529031040d94903807905038040c0c552026503c0c941c0c0229030030904068595002040820301800a0f001a500003802040203140500e071045111105810070001c00c8520 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 427792841 1250 427791591 427791601
    0x414070605030f0622020d0b01020d0908061617040f03030c0518010c03030e0d0503010f08010501120b270c040522080f0d0507021b030a030503040210020f060c0a0e0306 74
    0x20400d1640241301100c90442501c911140081036400f60482e60601920208000c109010713a0340050401000c01d03801c2c0c1d054143d050109076002600350003040326a9202a0000380f40320102410340c0c800e0400d605140e034214500b500303840b07034040c401c403401c035400c041103d85201015018000c031000b103100350a26506210321421414180d0003035502d618100403ca40e0361009040c007070f6005010011002069402117511307407001034800d52080c0300780a41f030002c42074006040c14040c0700d00e03410384140c60646001c1006907110804044c0b00500842610406100400310820fa040c081041d00207640000e000c00039003880402040703a00044c6010313049120840111103581e112111420350560104480b6102c030f00b1200c88541c1f5014014003592454581000c0c410860b4000805021251501c5c1c0880b596180c0c0c001499183c80b074110000707011420901c0828014908076443d860a04c071284116801c1d0ba4016040301d1078544103075072503840c038140014004c83c8254003100d403050040c42500200340c14204 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 427794091 1250 427792841 427792861
    0xe070b0d180f0f11040e15010801110f030c0d06030f0317040c060c050705040903020c030d0201020a08071209150204180605060703030b120601031b170a060f090209041407060503 78
    0x21060001e10341c00f421580d031010490121241c0300c4200000d8400c02119856048083d80c6840181800b20705842c03078000003c602e1414004c1520700c40c54010300c1c4e4185204206850306a40004d070106030801020f1002d441d082c07481c0c0c86560020750080310380366400c030030030b080240180800d2800400b030721846004020100d02c1d040700c0481100c02904e07081c2d2404500c4c0c2007090803c0d84d107411a40c0e0143c01d0040b2002450781c00111021444d0b011425111380e944110b006174200c2c070070300c4c420386c000c10032241c001218a401039510070506c070342c000008108103185942d1116510703484500c420ba85075000c00c050000013480d00e620071040d0b03c080020003086040c0310000340e05008541d0000c00709911544011040d407500d0521030210b0312a074003150150f50b101d10b4412050342000003050705012141c0d00014000400320b20303000b0780780700c820013a02c20f2105d1a04ca1001034004041c0b20415075444612030001604c2d0107110502c00c5000d210103100507002140102d0034816039600c00e4080000501c00c0c03205000d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 427795341 1250 427794091 427794113
    0x103020a1e090b1801110304031e0309080313060909140f1b041701140c031303110d0504030b01090b1309030912110307050603070207180e070b0d18 65
    0x702510207400390700150480d001115500a1299000f002c90290b1803404c0c0703005800300e0484241c0300c1d120303042c0021201c01e03540d00680c400031b003075040d049001d46555102c09402c042070034041e2400c0c3d14227035101c00d40585144e108010b40700c1c0107400d0300400c2003402d07030007842c11000c0c0428010500440c1444400c454916001a0400440c5501000860840700d08002e00022030780040305a2501c0755610120002c002060344000210b65003082d0154000d800902281440385c03800c07200780d0f030a64070307484840914102d400c0d03003ca003072142c030610300003210404204030fa01e620310a6a0711076540d811482c0400502c1010ba00c4198924105031507644659180d480c03242c0d0b02400110001f03181d203802c1c01c2c04c0703a80300310316403000da0040c411030b00140070b110021110400c02c48003a4102d55038130703544406014051000300c80c40c60040e000904240030700807050a003c0807209010402040030380406050500307003901ca0380201d10500000403900044003c80c001e41c0d03c50302c9000b0fa520002d000b00e48071405944 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 427796591 1250 427795341 427795367
    0x809030d0209030307020406062105040b0103030f0909061712030114060a0306030c0f1d150d0606050909160f03110906010c140303010501030b04360501050c0a0e0103020a 75
    0x6402080b2800541c80401c26280c170280c0040051144590315100984800c00c984488181c036403890054000301d104a000342da0059900000300d81c5a6881c6803002c550003420000c0c00c00412034220030004444015018401c0a0003d03e851000c4006124103440d00e440c2c0c9020788080607807014001009130074090b40f00807001c840141c580c5d82c0d40d8a15150304070014502900000c1194510f4600407030000c00f1540c2e0107080e0b4551344558108482c035080e0b03009a001080390341c00c456424401c2e00c0d0409003010392450700054494100454219103a4002640c040000c5076401c01e940d204d0104d001111a07c00e682e20000c00c01c40c04158001400d5417120084140704004941c0680e0549000c2131959124100204482c6d0b084440c0150b141045120309480e07034001e00c1154000ba0070020b15070700c1480c0c54400c015512a0740c05582101044003040c101c07031100300d4030031211a64647c4029034045002070154a05c81c00700e0171035060307484d1030174071024010b4510380075110304151040c410440d1041d0441c6000f03941d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 427797841 1250 427796591 427796617
    0x90c0f03060c070201020f060109021c0b151c02070b04030e09090a03180e0420030102040b090409021804060207021e09070305100b0a05070b2d0c0f160210080903 71
    0xd09404d0005034039242841c40d80c4103491048600001c3c000351a907000d0a1080c1c01c0c05161141680c00210200070758003c944c1c0745900507401e9010303844224512004040c0308400c051850141030b0101c48203c101e8011200c00e940341136846041004165000c0e805500700d07141141d000f03c480c18409255030343e401c00188002c003444a050381e0b0365194480c1c24043e1b002030451101180300b500c0e19251441c03954030481d2120070316207224200d14880f4070301802a1001d44a04490071405d081080c000c000180c081400141e80051041b02186001048105140d2082e409200c0159513a02c4600c1407100e600c075056108615082d030342c4400c0c4919034600d1080b0b60441e0151501252544409800900611013507000c00820f09000800b507090300e400c0b4010b0700d000d501074060310b04103a4425094441284c0c5001d00241030528581484d11041100c08000307410032648900b96080500800c0b1000e5103a2200880400410010101c0c0045280c03040c519203184120b0700d842441410250300d180d94038003c452480c40f40c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 427799091 1250 427797841 427797847
    0x218040b03070b181f020d02010c05091309140a140c0301060b030c03090c09070c03032a0c05160e06030f0c0303180f03030414100f02070308090f18090c0f03060c 71
    0x1169595003107080b5901c00b8024402c401805c01d00041c1d516103011088201550a0a560724410340c02a4103071180000054000071001031601403000081c80440f00072640244c9082c86031200c0402005184801071281c03d54895840718490703920314205501c40485d1180e030420605001d501c1643c41903a8000c0c90505c0e141d0740304e8499152250802069000e401d420500e01e0003001500d641c85648100c215000c2c0c2c4040021a03c1401c1064041690340300c3c0110f1078650344011074141d032040f0407000303105003e80203480c58500803141e641544c904540c0101100785119003808018501401020401142e0b0f000500380e20103032401194490280f800414044d0304002c01000540d1240900701c0301c0e0480081c180c07039030380c1d8450111410b010408109140600003003034051501078040c202c2d0b052480655002020f050307181da80c0b25070b6594400450607801c403807042d80d980b400c2d449170110300d0f0000d0f42c0d070341003c0800c0c80d095080350301d084000359031180b107041440d00c031000c80d44010940079006007902c1d0380d80d03507 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 427800341 1250 427799091 427799137
    0x3021f0507020d0f1202031809041a190e012003060d02060a02281a07050414010e03011e0b0a0f210b0708010f0909150e0708010218040b03070b 63
    0xc002010400c0500445005c00356030307150641c00300040140840900328000c3d11445002400707030810044800910003070006009a05518801010517031201701040c8648101c5090040e60045e04d0304004410003603912513111080003100100b0420316103201d46101c50a600c0c010000503080d00e0700c2076004e4041d00c4001540c880c5580309200f940c0501e0b011081c0d2100c98120003004114641c103c04041c0c44407203003d03041c440c5601d40c580109000b5100f940e10181002d081c8114a0321807040b40c203600b81880406030900302d550b1428007400d91000080701408003100810525201079401c600d092510841d0021024050080c00f45d0013182606c1c00744088113842e00500300d114501c03070141c2c2c1e0060030300d074519001c00030070305d0f030000c0f04071b050f03407000a106100d0320f6455651070151140350000400140c0f440000c0c88418480d5800042d4220b1904c0c12100103030303500c1c0300280c00c82e030040c0c00350000ea0701080039800c16070800c0d029184011100740c00038032003189045030428881c0950108007468441c2503403101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 427801591 1250 427800341 427800353
    0x3110d090809040c050c0c0901030f030e03010b0d0f050c060406050a030f2003101e03020d050c150901020118080322060606080106020c011e0f140a0201050103021f0507020d 76
    0xb00b407401c028108004c192003012000d0169080303568280054824440032220506285807824100da81c800124060003006a8080d125200480c1140342c1640daaa0740c02400d0b59101006204654000c0510481100e02c0d4200b550a100152810034080d40c8204010000c01d58840d0490781d200c503081c42c0000f02501e10a450402401850555401c0d242801031141c4105091900550180008140e02103003641d0392400240c110131281810704005001d02010000760520300c0390020820720410955401c1c10020f03001540030440401005c01082010502c4034055809101d00d145020140440700046160396803554064480100b82c0d5080301191880c2c216242c0460500c003c40e194000401d0001d00d494010090059409124100062151850b8090554020200d010944200f03001080c00018030380002d0703030044400c0e01e4020801480303207004e03404902d0707540240c1020441c81d070012845524600402100043c1d42608990052007112840482e5030000100e23481e140d8141c0720345a6096540c02c2c50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 427802841 1250 427801591 427801597
    0x40c081911040311010f03060302130b060c0d020706020c0306060904060c090b0c0c0a050402120c0912030403050a021011070618080610060306080c01021b040603020d12030c03110d0908 81
    0x101840701d80205022041101000d50240356a4003aa100c91402d4030703181c0101c040c1c0d400351201035041141c0c5900030b00c09090940020403c10710141920303107020080e440c03203032528142c9802d00300141c105400600000360b05020520200d00d084009201600b1300d800000d191000140000308002c0c0c1d51010214100d002d006a000103080c01a842034944003401892078940201e1232145220b000a1440032965140901c203584180704c14801c3c4950541d19888480c00c1d0781e10440c83c042d031001c0d14103a4803c144070100010700243d44a000034040d8002c0d144188111030b10b84180801c1441320103160b1804031a400600034040341e4103490042c0c81d101c0c92b1407e640030340c91f00e03412010b81c0740280700400c101d8802100c1620112441c5031707401c009090f030301c660040d241c4c0b1105001c117005030014006544c60707402c030031951806400001e0000880d9039aa500203502c011100300708131a160196100d0394a200d405109011200d49a42410721191071081c0b082c84141c4190041100481c3d903c240c010103020b944000d03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 427804091 1250 427802841 427802861
    0x60903090f13060e010e0f1b1204050c15070c151707051611100e0d02092d040501050a0204120b1003080f04090b04060b040b0c030708040320040c0819 66
    0x1111380036503112415440741c0e043c1102c4150b80121010003084600c904410582040700f0500005418048903071b00100c901310025205a40e0b900c00c0b81e00a050740c2da1030242441c2580742c07543d0301d26925005454098040da01917400300a40902040c0e14410050f00800d103406405914071564030711f42d8916100b982c2c98000c03600400600441c40346d100c01008108903648801f40c00854003001d00c00d803103e004aa05500c04038006812000ca000c0000040c10304641e01031300600201a010340000824a1250400c090640e1149134513250102740310a102d4280315503900900c1e004019880c081c1032101d00d0b40c1e916896040184440c1243d0001540f080701000e12074041c561102059030340390190071aa03442d5030064081d8403101803800e000c0d01d04600e03052060300103c810003c2c0040c1020716245096419810840303002449000c1041603c00040f8070600038405980b280c0c03414020004401d0840c40d9400c480e0340c81078029031400103120074690f003002042e40e21003655805a1440310640302442c0c003038180654 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 427805341 1250 427804091 427804109
    0xf0408010504060c03050615041413090503040302101d2803030905030f031801080601020703080d020403060605030f0c040203130212070e0f22240905060903090f1306 73
    0x82400300700500f03904441e0003d10745582c2840151620410001c9004001c514140148070400c410070000c6004804030008507802400c0421031680e1901c68010348428285c11225900005414411490029486881c2e400c151606660061039611040341d810b681851007031107005c01202410702c40d007400d1100d001942651071040e44003a40d034a07020301000c84900400d4840d000b9400c60000030140041992010a49080b060402140001c0150394110001d001c1d50b046001303101001c400304510000500c82102403400041e96136181d41010001c80b003041c3c004d58881c0d08140c3e0f842c41c09400000300c45980075404c0b200143c0e2920303420440400d450f000350b8020f4200003080d1a01402c0980820b68000312800c420ba207511583c0d90b00103400c0c86a5040b2200c80780c0e0014644c9210100c904006466011489058150000c51500c0042c040204122300910300a40e1501d103107800f086000d12641e0742041c8804001c501709403900c400503000c8003402414a024541c011107054001c003080d00448024a5001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 427806591 1250 427805341 427805351
    0x71503021e1801020106080a1e05030c0601141f020a2010030509100905070303080402061b031803030f0a0309021915090f06080406020d2705100c050304080f040801 72
    0x1c0c2e12501c1d80006000460140d4a0400c0001d0080c0010445e0b0307000d154808a524103110800b40020000ca880980503601880306200001c020a0304004a41c040c0480744c0c0d60300b5020070f600017003001038100158034841d102d0b40784034a408405d4000a204c104158003542044440c0c016102190703141d1a032003a4194050783c20a0520403598165005600400003c42550703140301156041c54180d032080403005101d54000e0b2000c102080c410000d0540103440204050702e8241c040d07030340c1c42a80c0307080c101124843e0000280140c86800c07102c82c0160490040d0040c606042c3c01402e054154043d06500340241038842c0200c2046507548209480c104040c03420300b40c685a216401e0030007544100380b4410114109000120791000d644240400311021075554610350760300c503510b00d0042d401140422507000e443d02d40c181d01ca52080100020b108450b080d146501c0303007150910503d05a182c80d0207801365032904030840410341c5d200382103c0e0711640004030280c1d20891100024054804d1b54050f40030fa502e00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 427807841 1250 427806591 427806607
    0x328020a03061a0405030c090702031207030506100f0203030604091406070c0b0f040b150105072004110301080a120207180b0406050102150a0c11070f0303030e071503021e 75
    0x1640104140c0e1120000407504150203c2210482d20640c01490b62544c000d51002109141002112380d0140340d901c10780c0d0824500e5000d2190349802550004007007910b9030704120140c28541c0d80c0030a002a54038180039540d08041d0060344a100c041c1a90740155220013174031080c00301c01c52408032000b554904441c058a007401e0024444000858111200120007000c41c0c03419481448003401f898101c00c48203a01d4440640c403501044c0d602d0445414040103000650100741a10900f1010403c0c414100340da880055042000726410006075550707100045c001407210b075900103580c0700e85603405030000ea004040d508003a4603000481d400006100808262001d0070302e12500603e002100c1520103100141d00c42005907202d80b20071b0301070074045109000040145007543c10850125010b400e0400d06e01440d2600981091019000b40c1210442004204100f55052185280440b0240007030140203040000040d03500c01410722480400d030f0003082c03500070784000090300d0414031507148006954a0300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 427809091 1250 427807841 427807847
    0xf03230a060504050c070c050108040c0302060732070b03041a1807060c02030606010324031103061f0e0a15030312061e1a070209070804060e120328020a 67
    0x110340102c500950900d00810300000100d0240c2d0461988041c07903c0000d8181401107a080c0001030013910340440e0818004096241d0500030305d401070054001801e44502881d50244804803041c1c100c9404040385d812094402c008903102080d00e0202c0c401b542e8039141c1c1d09228414000b0010525496031000040c000075107038800c06062070b0b103003120980720141c3e6076400594005010042c081c2d0180c02c40703000100650310a03403040c100180c1e1400c03070402d84070b14500425910308041d0422140d2207140c2074a00d059141c20840c00e42c0c021a1f481148986250001c00000701d0300c514400d21000340c4000703000c589548540e4000c40f4681078a51803081400b503803801c0003411040f25450100c2194039014002c19080f8005540c042220714211503029400d103010804e105e8040082c00300e8902960601612005035100c0d503103140107030346560b2441c070103080600f0b00a0455451b60500e02c65503000c4a4903140c0c8800720001d4a0b4003d041e4803810b42d001442d089a42155015400000b042e14800180940ca16030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 427810341 1250 427809091 427809101
    0x6010e13290702061902070c090c030e0102030c09010908030c21160807061a030c060705240f071d01030525030507020c01031e180c032009070f03230a 66
    0xf42c3c0c0e900000095401714910089200d42c64001d801e1a20540781408440600c0e04017400c43c84051900240d030b4000e002e810350882c0c00541d8605580030f00000d48409940e07001c001c200280075180c0103146401280d000c034541e0f400b51034080d0b40540301e80c0c0b01a1780d141c2007250166125880d015480c0a01105e052030706034501d40c48441c0403500d01e0303e8002c00032034000e03a82c03c81000d0071401600030700001c40c101081141c544c20182e022a028407940c9140c41c4420094990f6152274264000340c0301301c9040a51081040d4880102414200501c10015403042c1c944130720103104401e001c0c01d00103565202c40020002e0113440b00c2c010140440440d081d4904142c3c15030005102d440d1907070070380d43d120320140c004405a0b520389181c2010420784c8a58414440826482041086500b2110a00c0c0111998178040c021041368130980e0354800c041c06900c1c13800d1a189215a500c04211010741c002d02e801729003c1c101c0c1c880b030b0740000105644c440d40111a81d01c159050525901c142c06060320500d130031030014020341 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 427811591 1250 427810341 427810351
    0x10501060c0204140f0f060307180f0606110a0816320a0b0103080d022704050c12130302100f0506120c0307030803100b040602030304030206010e1329070206 69
    0x10724207642080c80c90342001e00c1c01d00401c412460300040e902e40106082c2c03131010103081f60344c0c18000c02500207034000703512482c0f03103805001c084080b404440c6442c2c140111201c0740c1c854801c1c0240301250004c1e071880401c07220265a800030481e505c1c1c10049140680200c140c1e000280301040d00100500009000a00300d0100e10700f10300c081142c5481038032803076103030640da500040011100000520010300480c02404041c0410700b001030a004510403500d001d60002103d9100e1000840e2804c41d41c1d06050194507449440310b90300f5403034000310310450813034500000e010a0a1100504a610400d4401c0c800003021401c40c041c00d02130001c110110400901e030030741e1002d00c241125111111440c001080029003010010094012240b4507102c3c8400c03540004c18010400301400008105a040c0300b0140c005010385034000c58072072030245006031815006030484410040480108411900502049a54646e0000c4411080e2440315095550040000c80000781808e5031010400002c0d80000d85030311a03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 427812841 1250 427811591 427811599
    0x2090f040204050a12050c0913031119060c09052106090616110111040f0e06010903120f0e06030a0c02100b01050304060902060c120309010c050c0601120c0305010501060c02 76
    0x41518408010481c8158030801d0740003003912404101c21148901d455070024010000d0312215807440d00001c15650003100d050030091103183e610818541e00c01c40c0c0c00a08444a4002e00c07201440c211a06e4400512000003031515484140350450103204441807001040301030104400280d450703d042903a002c100d200c04030103200322000100d0402000841f02d024070360b42c00140807407214072401204d103058008055141c5640711440c01d116000d014008100400051041081d01d504040e0088040c10003d01094100001500d003070000c129203039005a040b0986081a05140030303992401e48041d0312619156500c03240210811845032995002a92600b071b0680c2a540007400801b44041220350385290340e400118280001000900e9a40c44a282280001c00031030600c2d2000c24018580203200c400d24840a0010041c499203007424010640c580d07c00342413150902244500c4559144030510882210b42c0d0f0b504444814040c800b0091006103810500902440d80c496801920b4054099803c03402 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 427814091 1250 427812841 427812859
    0x25030b1806010b0c010f0203190b0d15050a0c0e03060c0d060e1302150406080a0c03110309010b0f030d121109030f07030507090e0607080405011803031d0105011a030c090d060209 78
    0x380039144226031054400b0080001d049e914050340c18010045580c5454200719164604404600002c0000f40800c0b00c40502252900d1720251190070ba95030301001005016042901600310f07500030401660240583c0314550321851480c0c0c0b000080c00181d03005000d8105882c007440b565084e940072640f0880e0082d07403a84421880c24515038440d10440c40b540000030984000306400c9106500021000c5a040c030300421401c0018010041540c420348400390640e55440c1000118185101842d420607402c501034001c800c0b5085001c0c3c8185d43d0550001c0105980310601d110810980703058555001d0b016080350209400e850781c07541e440005000680d0b0b284103446d00025050641d010710386d804500003006d8032040e2100034090300d103514081c1c0100c40c655201c8440c40b11100d258046489498001d6601044014880640f40d50800f01196000c1035a41000c0040c4410404c810f441403501001c0c110701c40d81c0e03580d903400e1440f0600407520050743c0000d6a80c7c0c5002440a960050b00404401b1a10014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 427815341 1250 427814091 427814111
    0x5070305303a0b01030c0c0b10031403030709080a03090b090a030b0a020702010801080604120f0c0501020a030203011806031106090f04051825030b1806010b0c01 71
    0x1c5201c07003001c080e181d0003a03216019085000324003030152040240d5000d1540450403918100d000141c1d00901880c50300004090042840b40c000d0070034250003030908001c103490f01403004140d402c041c3c2c0050091066070002c00d0401e03a81c412584000c54102412459206070702e9541a202d900a03242080010378502c00814a064040b40c0c0303802c80c030b50589860740d400d490f0800d10041303a0800701015910607246140000482c000322246071007204950030045c1c0d0b44519200140c40d603681a04002482d900600c1048009221441040f010310030030308103010444a200000c40d40903002e1100240b1a50022030821102501074001e1410b850100d201c0040d100014807100c1c1c00c0b00c08d10301c00a04213503903000c5090581e04203403004044080d0701400031715034400ea01001c941034039000e0300c2c40080c038695008402c945002c00e0146071050103005040c4040d489070ba094172103022000d400050404441c0d80e000c2103074a00c8142d601d24180010350700344d80c465a500d2004e050341f50412007111400d0f5003031401c099 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 427816591 1250 427815341 427815373
    0xa0c0506090111030402040c0e090109020d060b1303080903030c030703090e0106051606020307110102040f03050d0809070302150d09030207260616030902130b040b0f010e0904061805070305 83
    0x30030810064409505581d201d401f040098050024400180030540a20011170b80f2054034603030103000c0e1038402503551802c03640900200c5001c0c2e80f00b440b241d081404030080301480018048100c0350403175090394071a000440020306520940001680a1000107859030405401114900c00c50301802801c0101e030783c1e070315030507100c134170600ea00c0c01c0f200f04c159400c41c000107030b8660145400810300e20305148018040e120140c00c90f0300c04d0b0054840b50741c00b0041002040742c10004d03110004214900000a2b041004102e642c07480c85020007440303002202440e020b502c0c085400d81c0c07440e6180040c00d2220001070b00b000f81d1241c445000da04441c000985c0391180d008003004d101902c28900000500c1190746480d050b00714080742d01072103030030940c0316008440035036a00e03081d01403c554403081c0060b130300300307010200812075500c80d10b0325000d459206811400c0b0b86e04038181480c898425100342d04030f0303031780c80c80e1220041150201c0c030348080e0380c60400e032010701c08002194010369205e102285c0320b89000340081 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 427817841 1250 427816591 427816601
    0x1816050703020c100306081009050709020f19030b04090602030907150e0418060c0929090f0d0c150e0f0f01140f03070302070516181e020a0c05060901 66
    0x341c0507a0000d038030b451290138944000410481c1078500000d0181d10b5107a40b80c1441442e000e0070306069226440f402c00d11506000d00f41c000c00680908505d001c1d17660005803a01d001d0032010100c00080750042414260003900f2161107010000d0041141c9503452030590000d400030381d42415107100703060f07001c10740c01e1103400b50340c204403c2500d4401000d407140302080090151034130070040c0004900d002c03500150b4107000d0b03095010000d07103d100003d4206401c4480340300c208400e0a100108041d5608404d0102101f240c1c0702000503221030046c58800e038081685a40500c10040001145400000d859040e07505913a05c46d03119031f95102000c3c1001000c00c89036510300a001c661000070882000d83d11f600400880d2074800c1e01d40071700c80c1000c3c56040440c103a90400c83d03514010030780010714102013007400e105206060000700b5054484900304a10684030b100030200c0350b480f503a607585200484420480c0342030650300741c040040d50340c2c1c2d0072403400a045a4240b04101c0b260312400003c90300c1c800c418025 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 427819091 1250 427817841 427817843
    0x30f031d0f04020901030f0e07060f020304030b01060305060316030606091805030a11120a020a021c0506010b1308060901020901081b0904090624050901140303030c090105040518160507 81
    0x408100301c0c640040000070340c8a032101ca41456500c0500c0240c6042c0c5000301c035981220400504001032412901400c0107190751030040854004003c11320000b444070208038155040e903c1c001441790758000110b481e106800309071088002c2051400010001203420610684648c0c042c140800b08005c166070301321001086000301950003d120405a01e48114018070071704603010219005051081d01100c80d5511002e000c0c001a04810805c1e810341c24050a292104412141d0010f2604000d03211303180c5400c5d040c0900c032a40c54000841d282c132680050900300103885243c080d83c80d54104000114000d40c4840b41050100300c42000044040904040d00e03202e0b10003014045150905083c01c001c0103046041c011904591380340300c0742c0c41c20342c181c40e20051200d41d043c1d10045c0d0f20381010f04103c44104140d01c0300c00749000007a201d00494601000b50b030b802c0f400480f9a203464000590050ba20b50013550810394100c452550394450500d07800d00c0303060146442d0216014160b00081e0201c999108403d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 427820341 1250 427819091 427819099
    0x2011b0c0b04020414100e010b070818010e03010c1d0102010b0607030c020d080c0a0302012702010c06060305011811040b0f0d0203010b040509030a02070f0807030b0703020c07030f031d 81
    0x1011030007080ca004550750344644000c00c00154410403003445030788440d0964a016907818038604c24080a002040f140740035184007402c1d1400c0009a58410000b07110340e40c4401c0244078482c02084050b4003d0042e0f0b10300e010003c4c006d02c080341490100400303550394804a01001607160fa40e41c000c6500622a100803020003034501c525104450310306850410800c20100d8002c9a00d480d102c000c148080003400b20f00300a50040c25580c541410003d0a50307201c0d04810713162300088000c0c6008003100300c05588503254282000c10100c800c0f810600024029940064a9035003450007001c400f02c1d150052803050b6120f03c020741d030040c100109200803180c1d000d0741940c210b078001408500a1402a202d440c18500c0140080b80c1e041d0028040f0f001c1c2ca01c2610002c00c0c56001141c031806298051001c400608081c040c903880b89480e105e040b582e994190310020784510700038404905c034207201e038044440044510301140d04403991380c50700c40d109100305581a0001401680141c4c1c06c9980d0207280e0540184c014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 427821591 1250 427820341 427820357
    0xb090c121510140705070608060907030b0f1c0f03180f0b0d0b0d0c06050421050606060f04080601030f021e0d11040618050117070303020a120c08120702011b 69
    0x81010b0752030030140d0403c500c01031410f1100000160f000c0108001400c099030b500750300f81c1010001c7c810a0b0602414071024981000f250b0415504c4002d1401882a4100c54002144440c00c42e0030b1a5021010b402400c0c4101c2ca84494041c950040d86c022400140c41d09100402036503900600d41c1c0541d507004d000450f480c1000a1032600000303070030864688000070001602d4580035600e4002c1c8031000d0b070000c40418004542000040100c0345020002e1801c401082c00c8201e950307032569100c1d40b0090055116020104440203c44400b000b80d6010380980400c0700e44950f12801d1841801015003000c038400c100b550b03010040704d60005004d03030715110090f0410500301c4c89a6076402d81d92094042e0070350000d41e40d000008041c90025180d01c0103084514001440f5410070748001c08080d2020700c00800d0f41e220b0311040001990002d807010425800ca8011002081e2502c002c80b40b400c80c410020781141b4000c1030700c2d540d12446428960040c281e03034000700182103000d00c030502c003100f0691265000c07582c01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 427822841 1250 427821591 427821619
    0x260402090c09130c030b030a020904060c0507020d06140a14060f0112060f03060c1b080721051207020d0c08030a02040b04080d090927060b090c1215 65
    0xc020302904a10075041035410480c0e004041015050682c071038010310b5441d0344180303102640512514000f904103802805542c1c0868002c9814190080c0c00201309503610404d001360940b15109070340c1007507401000901c83c1e220174140380c1e000e00a00b407250383c01001e00c040484e016010522400801907140300c1c1c20030755607507800c04000c0b403000303034180050610030f0200460415552500c56840a4201e1a2000d104681141490400c0742c5034013603030704240041003800003480e910000c4034800c21544800102d585041c81d15113440658041d00c80c1101c0070891500e0f160540f90402c01420f1845035124010b8075940e100502265035211250601c804102c6da00c42c402c000c075000303c00540d40032514980152400d5078030020f07900c055020b9840240f29410082750301001039031004012006111041051240c0e0418602c00100d80007224500000755070a03250101c00c00590307420603040385200512100e83c928025509104070b034025400d80d00070781c03015000540c100280141c4040030303a05c05031640044a20f0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 427824091 1250 427822841 427822849
    0xc1f06090b1f020f0105160e03011515050c061e1e0a0209041404050c01090f0605180d020306040c08070603091e0201110625020d021f060f090c260402 66
    0x2190040b001c42c01080d110501e141d400340141400341c2000744e01400c010f00c090303a0091012080111031b506ca41d04003c0d0000c400d80c00021468144c0381414426040b0308070b00c82040d00c580c810441142d9907800ba90003008038406074007148032a201d0010b0702c482a9561281081d0708101401c952100e5208111008602804181d901405c000b203005480014814480786550684010464044849034003038007000d0070550b40301085000429500a00d00b201d0360034920081c00c0e43c001c2c03140c1401510300c3d0308490405951100a02900f054010b010380d4070350704090810500d0351038507000345050340c401c240380020180d10030710076042080e40110f243e640c2c042d42440c12482421621106034100300354081c0021252006000c01b074000e01140e0058050341a15020300d9030045098544082136410040d1506400c3d600481c01c200c0a07400303200710503c000c00000a0000400c45600000381850f8880d5000c01c00038426404000382c0c03842c98031400105c2c1034400a0340340c80c841a28000400c0301a507004070b401820 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 427825341 1250 427824091 427824139
    0x8040e0108010b0a031b08030c01020702040b0a080a0210142802031204081803030c150601090803090d0804090e01090515011d090106030210021e0304080a03080603030c1f06090b 78
    0x2a00483d5103032003661207c58500e1504160031061803039600103850011490f00e4410a10821415101441400e01e4030700c01c962142d010640181c020400c40d211042c9152042c0b42300354500c400103c555444a50340128140780900c56002201c4110746041101c9031b842c000810740d6000000240040401c2d651547c4980c10381d0070000b40c402c0e0030711501007011138680c3c050000d000c14080340c10050004800d8200c40070306074030700585050f041c000000802c1c00041c9011049840116050b02c0d07840c1c800c078907450420030038071030342c0d008103440c3d440c1c90808188484107402050215000c3d104460800800c15509941203500b803151020000300d851800305092111070f9001d80c040031003000020981d076030390085105c81e901420b0200050b00107820b020315405040750f040d00a002c0c00b9000b541441d00f40302225640f8031201101400388000440002c00030f580070001c40340d003684404203560020700740300c10751886240852040c4080350f081c41d1000c50104168401c103180c582c001404022101c06002e100010f6031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 427826591 1250 427825341 427825373
    0x30902030f070303081e071d0f0405070903061425050c030a0c020414010e06062a010525022a04091407080313031202100908040e0108010b0a03 63
    0x80030341111841c40c010240031100c0118021744070243c09140601031007145082d98980d0642c65440f00051207d07a030b5209813418460200c10491507188402480002c01b8400c40c411500d40c498100001c102e0081d60000340541100d00c659400c0c482014486d00c5d58441c1c034801c8582608003a0044480400c4400440e411b451408403420127a103000380c452070341030455101c0c04079480868402c010200450030503105101d0710070340050800c1a82d50502c20143d45c100b1020305010707c140d401049100e034804122620740140c141d4086821204400200c41c07a000c1d040403254045000310760301c4001a518100300c407a070000d03945a8080c1901400060485041403501d100403500807540400c0e00050751154403d407440f841c018911441c0000d00050303854503014861304040a240c0050107815149203440c180c2d00300b03503980b2001030354264400b40412854602c01840d01940c4604201042c014050258003e02c180c881081140500d07a07240c2e0038680c04d03500300c50f1000e074104d0506e140c1080403c0400150f92040707 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 427827841 1250 427826591 427826593
    0x7031515141e030402011404240513050105090612010e0403180e01030b0709080a060f0c17010b0c030c0610030c0e061806010207050d0302010f0f090209040609080d050a0b030705041b03090203 84
    0x5980130b5601c11900307230847d41002c202c0f40d4000e50f0056800550075911100c860b05450000e00d0015020400410141d052149074144032021486960560b0307040c054840508408020390415a074a42e80001c161205a4060740880c3d2203001c1c4600b1034929183d00e0302620704c18071100050f6403075035550802d442401064042000b24021000c28100e00900041100300c2c01075201207030b1009504030807401c0f5500f43c400d140c01c0c040d44401c0e8034400036100500030b0449420760241c584945104071030350305500c5480f84e0840f081c05654100403188100c1c0c0c400c0c0c01a24060401614080d031201d40300d00803403105494203548110031080c44240307420f202c50712503404401881510941aa51008255540400d0000300c0141c1d458000b141d00c0c00c4214480c2072426690124107001c0000781d900802c0f060900600058412902c8178058400d00041c041101d222a40e0141c00f08074a01c0c1c000c030348100400c88019410f1090184a50003e464602405070a1100c2201d06580da90600399410603001024036000403601 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 427829091 1250 427827841 427827857
    0x61209060504050c010f0305100b07082511060403020913020a03050304080f010509010b0105091905210d03050702031815040603020c2505060307031515141e03040201 73
    0x315240a0075019502c99001043d900e505580007508178401840514101031034101000a001c585201103c1182c4071400440d6a0324041d003010f080c036120320360000c1c002c1d5030b4100d881040c2c00385c400074500925014003a04180701900008200ca244202d22000c0e50000c0c0410104d1054904e800c55100c9441c0b00038100c0e14a00e580e99546800c42d0440d90041c203180c0c01072000c50072010000e0003010390128200000300b0070308254000203000b60080000c03a40c040c40f405580700c1d00d9010340742c000401920000b000641e25080c8821800e115014400000c42680600145114070f039000340103003170080c01150061400c0424001d0640701541410101303551210389948420200c02000c1e0060024040b50350300569142d408120b540c5c54500003424045640605520211000c0c2c6040525810703100c044401d6592500c5144045024083e0002017140c060b80d000d4002883c81c501c60b80c4003401c90394030745900d41e10702070315440703d80240100510800e0581c1c1007402600c035203504500450b80700c0d105040c9021 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 427830341 1250 427829091 427829093
    0xa09091d070306020903100b060f0f0c0a080406030c0c02011d0f091305160303121814061605040e04060e031c0e100501061b0203072c10030309061209 66
    0x441c0814a50040e01c0c540e0340022000410706092109044882d2460710520154681a000c41e442d8400d0944908046202040904044030444202d0b122038541da4100d803d103144500348810f50b58014854100824500310709203001500420f800031004d501616017074030801d0501810700030200c0a1820755440340d21810244040c0d91600e404900611008003000d52a041c02e2030518900600c1d5807090000c40803210302000000d920200da0f010340708002c2c401082503154a440b554030403140d403c005180b1001507640c00c421100000b41c1e984103208907609a0350441c400601030340d151295000d9209281c00305030003c0c0102d00399800618200102034112440d0031000320541050841c4800b5144000e500c80b42c00d0b0305482d03403c006002811907039640030485545000800380002078030155013040d018020441c00150360301841140010020540c40700101d0b2100340c001c40c614000031002c0c0500c1d00e401c80c0070982e50016400703400140ca5050b211036003043c0c100502540d6088846180506035512084558 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 427831591 1250 427830341 427830343
    0xc05040504090b09012007060c2a03080f2e0914100b09010914240c010e0a0c12170a0306140909061f0803040e09070b0a09091d 56
    0x10b580741c3c002c60301c2164600f0100d150a0035240c0b801032400140c0745109103109030115030400c0340e00065010340002031103242c0303005c260345101c181076018840041c14007455222141d0181c0e400d41061081da200580b551b0740d19044210178509641650794902c01842800e400c02001ea00d440f503413401128800f900da5510304d0418151051030442d2700ca58804e460501c2003100070014100007500340644514103100604c0c00003070010305544201228403010240340e48280c4c5407401014100345001d0741061000e4042212103038140c0c4040c0700300c1e400c2e41c60401480d481240200310014415802204030300f0403807504826600816041d0004d031a01c0000300d4144002c4109000100052022514003050191030208014039042c0a004a07134000c880d10700411105c00d80208050368481e2403403160a8a680d1611655001030700c054000b040e07c1e102c005000b048039015010345612952400045510150b1942041000d0b4041c07060044045030802d0030602c402e02194200d0f07055070030386805a4000384903101c012 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 427832841 1250 427831591 427831601
    0x30a0207170a200c09270607110c011419020738211f0305060f0903040b0f031504090b060f0d0309050f0f090117070f050105030a0c05040504 62
    0x801050340144032950294566159034210340785500030700903074044c010110b103140400622014441c01d0034880301c0491b004e107100350240144a041110440c0c9081c400149c138122440c031184085100c0c100445000358441d00a11104a000154143c1018140d0003884c1c42c203038580103070809500520f000410823160300040d03165007840c940040c070110111106514030180650f00403658192042003403190b43c00406200e03940140080c682170703200340d80d2881c110601320f4040d1280200d8100070360001042c050000b9484ac01000410602e44298966981c13150b41e82c8a507110b460303c2050144182a01c0f20080b00256502800c918a510041d10306a030000701250b800080483d04056804284402414603c0e8580740b024030030b84000f11010044c0e00c024188480c1841000c0c4981011180701f03170b09440f216500003004102422a440e40e58440f10900c1401c1c01101b524a03080c421540c002488180003024902110780c10703142c040c5035480d400c407920003901d010b111801c00d03c581040001442d03182c0e442a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 427834091 1250 427832841 427832857
    0x60e0a030f080106031b1809060e01090c02161401051b030c0f0705010905040203041103030c1e03090906241606060e0103050d0809150c07030809060c030a020717 71
    0x40c00e141c0c000c0c920000b0b040904180c111004051034503050000d464401c084a510701d0b80142010f00c1c803032140e00e40200b000c1070950840c0d01110300300480050400c070241c00441c143c40b0700b02d40501019140e0402240d0b138281d8404400d54508030010100301c0d454402041c0b0190343c5043c90082d03d0300c684905000c0402401d44440f00c010740c4001042f030002d500600807017101c101c00d900030781030540c90100000c0c0301030b502d402034500c21640040841c08206000302803a0452401a0a40340c8a048511505490f510f001030074541700225804003400c601408070850304a07200040102e00e550301c0ea2800d028a04403040501d01c02800e110030286003540200002d0803401d200b480d1890200c4906181017000e42e491607210b4a0402da48c0801840050404a41000340c0b1449203046129680c0d85040e176071504100b1103419202c2081c03403040c4540740304110004d00003240262540c4045440340c0d0192035407403004603010249044140302045a80c4203607002071500038051802d02400d44542005202c080d03000c0c60b4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 427835341 1250 427834091 427834097
    0x10513061e03120e03030a050a05070c030b100b0301240309050a060b15130605090604030b07031406101205062103070c2108090a08010207030908060604020c1009060e0a03 75
    0x10104200010410444060220713407a103c04550060300100342c1d64000c0c400c00c441401808038801c0600c0707124405070703441d03980c020600d140010365905010b00c03164000d0b03e18001d076480500000c01e004102e90210303030499100410307000031003241c080100c5d214040075541408058441003500c1c04030b4020401880c12034092080014101518410040c001d00d07070700c0c174002d80764805011a9210b40d020404000880d03405041240d40c4115a02c0050254822070700b0042801500b44180500d0a40c0740d8800c1649074103c200c914034a484101c20020a580d00180741030010b8401d601d0b075200300d20107400c0260020406007403501c02c2c82160381000c0800b01c042c00902969032000c6090710501200002080042407050010042841c85800000781d01340140c80142c2080c0300064078103013586492405600802204008646582003442d0080c418070766440361040c03500c9403002281d11407625108580142811400815607185450f405001800e074080080c1d484540d141d9020b40c29001c184041c03560039120365 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 427836591 1250 427835341 427835399
    0x306050f0603060a09030e040506031509010c08010f032006131d06120706080c0d0c020f160b0412020a030204061d090a0308060d061b0309020411090901051306 70
    0x500780343c41d21100500d034001144c2010010004640c1100c0940c9845905550100d080e94481d00824a41b4104031140b13100c9807018020828410010342c452518602030744d80e002003690b03986003500b40565040c0809442084449200b80c580d82d0401c010200b841030243c060b9081a900c00050300700c48520750300020f29110281180710b00d00c4054040c2da40d001500302c4010808000701903441c4e0780d0300590b00404c4240082100866600c4410b401034070450420240c041c030501c6c03d80c0d10000e44407250441d0b002a14411540c02e01803e69001d142c040980341d44449541c201441c00c00350b40b000c001c41040c1070760400a030075000305c0982c4840c0181c401404200f4030710704000501050040e980350009051f40825000480c0400010341d20010340d540041088034400c40d551003608002004101c011007500c2c02c086800c2c0c0c9151126010382201417960b000700e4040040e2142c0c1c5602003a684075041916074000c4001d0010300041c42c002030840b141080101c800610162540c015900d82c1d09686145640c046c40381c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 427837841 1250 427836591 427836601
    0xc030f0102070203160b3a090201020607030c141c0507050325020a0b060609100210060618061b05060712110901080f07210e060606030c040504090201090306050f 71
    0xc11140d02a178944a40d80c3c060246007030060b4031180200300c426019508444883c0599504079114581d44010120110078041880c0c00100e00400441004a000d070186d03d000811460185c802d1148040351030303c484034007580c00300600c4540ea000c2481182e0000e0450310401c01c400c0d041c03240500c00d00154543c2d9940382044140a0541c0c43c0359045024200c50710300a10072850390100e1031030090380d0702558103802d40d25040d00280d018040c0c082e400703800100411001b14010360008161680030a851002c00c10a07031601c1c400c450700420440192020300c600c110800c030181c03242e10140810b500d07920b525400101c0954806040c8501070315440c3c0010000d0b10700c445400080e01c200511442c1e407521552520211800191040078000c06041011340c850000a40c400d0090202501c10408030001081c2e01300c0c0243c1460043c041c040c600b40381032140600141c0142045000c40740034503950051941450f01d0001000084e044000301241007016280001001490501a803409582c1d0114150324038900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 427839091 1250 427837841 427837843
    0x14011b080d110705030706020d060b0d0606031104140d0602041505070501110901080a0908040504020c06100e0112080d060510020a12030b0d17071a010303030c080c12090c030f0102070203 82
    0x100701142d10740b200801c07101000840000c2100c1c2401e0740a0405a1505403004c80355000f0140d84c0e0180103110400211082c001e20345a01c890305a402944040080c28120001c85400d4011800f0b200c440000b003e0110505144c40340b8601160391040d0702c00352800d0703100c01c3c0030f000010305007003201e010031004070f9440204542030041001c0140303940b8500d030038072103468002040140c0c003901c15004140d0f1403102d01b05004500e011078014200103002550b50b031500e010026902c04007103804c060f285054a0022492a52300e840d0030307040320030b620840006441c40c0d0301d0300c1d0a2a0701c4030b0505900b4075030702c100c009000c5e216520491074038901d50300945055000741c240340c43c0c0c0e07455081451040510381385501406590301000d00c01c41d1500008452251002880d4020a61003401c002520003030441c1109068107000405c0541031f00d119075006c1c01841031400c01562503000554003949881801d00245400c4a680007110f680480c49004480c8032103031714000f1a0602c229400e00001e02c6c1d4001402c0019410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 427840341 1250 427839091 427839101
    0x1806120405150408091c0c060903110306010b1234080a0b010915050705060109020c07080c03030304030c030201090f03081b190c02030a060e010204091b0914011b080d 73
    0x441c042c04080d01c2c3c656502c82e024441c20b0311041c8160340801c603200c03803440008017168420794011600c4c0055504c0e1880030782054100d10045078611b0f0b020310b00f1000c1303042c0420458121410320b500903040000748843d5841d41003000b03040640e541e900c1c0310104595089112011640320f09021841b000003540400140380300300c014000c480540c04d00340000351690784009007a007100c80c01402c1c00e00c4008107490850720f92042031400781952080d0f0001160758842ca034000c100390f84035201141c40260755021010b4a071381d0b0826165506030800d10000c0c01180c054100071400600ca0300c00054400c40c15070700c3d40c03003500c4000815000208600c04110313480802140e1108440d25000c40542001100e0301c95040c80340d0200320300da04114142c1d81b01c40454070108aa00141d039440001401582c03429040300b4001c0d0807a10451080d070382005c038900318001001c0807618010510759114841e1030f080c4803000484994902e000340c108103540b240035500e000e09200781d001841c46031a11582d44c0c8980c5189134191a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 427841591 1250 427840341 427840363
    0x30519080a0c02010203060a18111305030c090f010b2a010b010f110606040e150a0c03050606070f020d030e130b030601080705030d0f0315090f0609061a1806120405 72
    0x13a10420600c52507540322041c9000f114620214403c400310000ca2100c003420342d088000c680345074045100c2d210302c8101d000e064180ca03000da080740c4080c03445808005804d00140c1d895440d61007200c006000703222802c4010551607a00a542c455042520f4440303c2000702404150040c507552114004503035a1301c54031088000b10580707080150900705032070090701c5400c05081a0320a955a150210500c10140140d02e0009440c1c4107065a5251091900300a0a42054810006403618001030102c0c9060025100d0582c1c02291300302984005601b0311460055002c001d509014016103d0b504550b03400c80c440e81aa908400d010450848140c00e2501d001e006800048050b00013090030b101646000403103203800300007884d200801c80440c0c0010740040060b240706e42005141070a011801c01c140b5080740e42c140a03607201c10450726554003071030021521301c0d028000e00030038090712012001000710042d0000c2c021807000081880d4a842c001045540940c0b90300440c407005008100910109011140c2e0324 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 427842841 1250 427841591 427841593
    0x1b06090c0306050a1d070501050903210a1205010b030c091906050702040f060803030c0a1e080411030a030509190b04080604142b020c150301210c050d030519080a0c02 73
    0x50303040851741c42c0c1780d11850042c00e04100b00400c04001d544d40410400680510a007031041c001c44100402907510703400309000781c0106030803a00818680109201e0079040f5005d80c0851811074881401c0c40700700e94044550b90340d104980700700f4185800800401d45005002a49940307944a04603c18442901c2401203484170f9540b509600300000d420200c1120760101c401c0c140c055840b00710340702c15078840d20401150b445000e001c201481d0240d401c0b40d21280900d0003145d1200a0204210801d90790304001c0c10010005682481040c0345818241c8100501701c00c020301009240e40c8901840c007041d00540c0c4100c0160b44004244402e010b628000c070500800c2c00c0c000ba01292109102e01505011a074100d00c20704c040c405030011201c1d1080c001450304070340007031500c071613050b044801e07903002c0d0800c1c06800a15a8240b405039003006030040d90000701ca900450b5619218908402c203c1981008402a4240441001521401c0f10545600f0b0f00c2200603450704100390405882030b100312103d00210380d0035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 427844091 1250 427842841 427842881
    0x1b060a1104050d0b13050d0e09090105040c0605180d05030a03052211040f05040318080d02121b0f071e0308120403030e0703030206090d0503071b06090c0306050a 71
    0xb058540040c1e10030380d2500001c84103455124061000d04209407140058518001ca0090500b119800408004990790440311014140c45404600382291800e44008180700c185c107000f0401c46014801610030b6011062101c4000308050001c24a1070100d80d00c1114190000541d088250fa05882880c1e00245840c034402c00340042000c0a00700304803030150240107401034100b40c00540e61a600031490664900c80b0074041814030f40381c060152a02c414980b6030010705d01d00d010800502c00181124040394960042c85001d008000e10602580032000c0443d100c2e620b0701b00081d0071a010407402c00920f41550082000c1403a100d20112000402c01d40031829030100308041022503080021784141407440b000544042d1142c4c50306a000b8444000288860b001d0381a0000a054011860910038051501669030145c0c070b800007120705101c1241d1400220b040c000c0d814483c00d400340c410b140c0807403090000050144260301c0b81450380d8500e51086440075203035001c0090440c081e00071001704208508000349 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 427845341 1250 427844091 427844099
    0xc010c02070f06052505100f0b0f0f0d260301060c030e100c06020a0309290c03060904030c0c0308030a020316140a180e0c0301150203070f03050f1b060a1104 69
    0x40d80743c800444170103c01d2168410000e0040c240001e05d208941c420b8204003554505038a5805400c0040c6c004e0f21486800b96600b0250a0003212458600360090405146140c10341d54040c00d28207c07910624807080c881d10105402c01c040009501a00b450313100e840b0800b032540303002001486103195280c0035050214210803190741003c01e4011203540070704013684560040d1812001044886800781c280d0504103240c609402280c10f4141140d030201d414113425540e2400c81880c507100548881c2e801680050010780801e100301e80d0741d00c15a202c0c81c00c52800540d40c0c2c591071b89580007175070707044592680041880b40408600e443c240c1d041a85050100358120040351000d01030160032403002c1400422401c00d0110700e1303c807c4900240603201c01c4010380342040c1c0e40240558109024060000e507400e45c15031b03a050700000607110b02c680e01180b1003440700440d580841d03c6822050307503160911000d01c41c10070f0070100300700184d0b6170b003030400700500d0030386048000c1d6010381d0140010b000c40c2c071f0000c1100380 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 427846591 1250 427845341 427845367
    0x804051902091303020c090411011103030c1b0709050703050708160c11130f060515040f050402070f0203190b160e0d05030903100218061813020c010c02070f0605 71
    0x90303100c43c48201c001040c014905050b418107a428800642c800c803200100b0041042d403802261550b01c0030ba903188051010781c1102a80c900c0107413542d20b91050103008400854103081082444050b284040d00c900130798030f0030200700f43c03030055403000d001c00d44079010000444e9021504eaa80202901e1094100314010032014042030201c0d0009410203150301c021100700e445002104140740303480c0c0401c020703529080564030b00908580c000c00d4801c032103502c43c0c3c80c6054500c4068805540301d1039106030001d840e00d02044001d5001041c21200c012913989e800c0f0141c0c5d4280240400c151031541c4185520849190a59207220020175400c5103610303080340403110f6680175100d1040110280d44415415801d42815451030007480e14070380e030500c9404100044d5246075005043c0100b001910144020007400810070213008da007418611908030b91030540400d01d08900c00d001d60782c6001100500e00010454031509440307510583c10003607170042104004544814a0754070023440c1c0f07450514141413403000b42c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 427847841 1250 427846591 427846609
    0x30201081302030f030c03030912071707030903020d06050a0f020a0f08040507030f1a06040b060906030a06091d060c120402090703022701111b0112021201060804051902 74
    0x2041c079100c454402904540302040020701d00481e1070300301d984400f25078401a07070720783c1704452000041c00f030f0782e00c12040c1004000a84020703d51000a070400d0122201d100d045e903401070342c0244d00f0400225000030240e181e0007128200c00b400b4800c045043e1920090030002e6a00001003803024600c10044060b0942d80b205040c501d418040c81d0803183ca44031400d10701c3c544078880c1c001400800941c0079130004c01030b6a9140e070a90310303900314501001ba42c840c0104011200c10070301c980e0308100104440321042c64440000d541c0500110380002e92661100001c0040b2030030440c2c00112294040c1103001841c4007000b91692100c009404689003200c10100a04d9454000d00000d018191000100e461b00e030080d019912a0442c541242c40c4000d4091180844058904001e0f40405d4580740150341c49800407c1d00d49840006204c50131070201184011103001135120780a40c034140d8203111184240d0302e4240c00600034041c5030b544403018101800e005040440005d6032805110041c521400161104141 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 427849091 1250 427847841 427847851
    0x5030604110702040c02070312091212022506030f0608070303140d05130201080105040507080c09030a0c080705040506030307110603061216080708120706020a020309130f05070903020108 82
    0xc215500c0e101841c010902a280000358050300b40386200f0082a0300280b402d040364041c2c0c4081030580034154094451b0300d5203010380112072402e40380101c046070110050716031130075035803040380c00107881c002c0f0f1000c80410010b07004121409c011f00401c007003030b454002e044001c032240d0010404140360504141d5210014803005084c4009161145035080c241c4042d51280c4080c60414809494200000180710801d204200d02207041e05002113501c5c1494811144503070b8841e2580206a102c0340c140200701e80010b19010b034075104120442c4002954440c41000a20740e0704018502d1034280340801c42522401000305010754800d20a42c0e005c0b405801072490707107480a9030982d55035110385020450a03412120521030038840c8809448455076240820000c5036181c0e0103a4a0041d10b506c3d0990b2129000800301d00045070a12801c4c3c08130380c40340d0050030306003003d0040702d00e0b10103801301040300030312101c04001002c0c1d079071403901061003076034080c49501568510b0316211071815540080c000c0b51010346 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 427850341 1250 427849091 427849099
    0x50411040608030715110708040905070507030f08060a080304030614010605090d030831050d051e0f0c0f030c0f01050f07080a0b03070b0901020c0a0803310b040311030c01050306 78
    0x901070017012081c1d48008000d001092100f6910a05424154807a41c0b042c030601e042e5500d00000a080b03039104205a40c03803540e15594a0340200d66158048810b8540540016400031030b05000080000040004000551040c030000c2131003080b284840301204c00c140d00500600c4020040d0400725580c2c8410040079aa0500f412001900e54003250b4000b204d65001c01180607450101c03a10696850011416800c1c0c8034208982c00704030b512108a80c54054417000449401d6011419040045c20f400580340c4841e8441310f0310f08202c034090f8400e20f0600e0115003e8160f400c0065040e0500c0d00c00e101c1021104a018021300c0745003030440c0e420300149001081f0408108052740856032118164120001d04403008046440d116111030056066900401100c0d0144c45034605401450400c3d4800400316412034026600b8070341800190792020901c00e5412a201c4201c003007181d050031206c00d000c805402c1a241d0940c5a50035460100c0c10b1101200b61507100750700246d0b50b0070440ea80202160b50008044e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 427851591 1250 427850341 427850363
    0x25021c031a0a030309061d040c03091b1401030e10050f0603190b0109020703120c0906270306020a02100c0909051e0117010b0414041e051213180504110406080307 71
    0x8148010101e80910788548c010708000741040096415000580e18a008101448102508500101651288d885454628550080ca10660b0360280c0e00418120f0490b40c02c0c0c0d450640059080400c65204071000480c0b0a407402c180031550a003005980a0200f0318000340a80804940f00d40381181e82c1442600c94803030300000d542c030801d88900721945529030524001d1010402c10f041c040d10401d2103000b500001110300a46604c04120350620b1160443c1008101c8040c50850f00c612000e5403146140034250b11814110000c540943e00c071789013503040d82c0d503107a440c01d9050000308011740780040c0225441c0155070b1201c50700088401e620038112201c0c1d10021301a040781000403405484501c0007194098540076800c1c210140e91411944103600c81e1010101c0f1618076820f00e001090450000380590340030354501d03021a082400100b4090b07406080404040b80e0303c420038601d1451462200401940314818042005140000004d40c0c03030084500b807190030b00740445165280108600500050000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 427852841 1250 427851591 427851617
    0xb07020d0c120c020303120105280308090a1e08060a091a0601090911030603010c080108030f0d0213121b06050d020f12040507060f0825021c031a0a03030906 69
    0x1d41000500f142d0241c1a6a202d000c4030b0340d0201c60b0b100c2445000e0050560401d0b501031a180c0c0d4200c64070103464065201460750450b2607030b090703030340120b00a1a000040000049400112141c500401c100d110402c0741c5903a04280c0d04070f0802c80b01501e91601541410741ca200015020204000c101d402500d48001c80e94820b03004843d10b403251fa020b400d05030300d855494940070864000840c0f240300150000c0c04809040c00003125800c0c02485892444d4106010b601e9000c5481c03c014011038010440c09030074942014080c800788250380c3e1015280340c0003041105d007080410810340c003040201c42c401540e81444d041000e8002d04c645694020095800140f4440415041c0140d4620008001d01c51929240c103281c010307130f40c903001c0c001d40000c119100c3c1c2c20301d0010b1040349100c2c0303c0d0b10503400315001c20003c0c01c01055020203903c584404c0d4002e417965030034080c41031918a009020165004920348c00410854543d00755500c140a029480f04030041c00420f401c0b0124400700c0d4441e1520480c00003070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 427854091 1250 427852841 427852847
    0x1122d0f03090902091e0d152414060a030603020913060b0f011409060412030818061522050c090f0603010b0909180a050307110607030f1b0602030c070b07020d0c12 72
    0x1900c2c1f00074940b8000000350740c00c0c8103031a403040d00305100080d01c3c5c02158882c030b21402249465441070360101c5519010104103818404040c11183c1028200440c0c4182c0380d44c0051048071044928440404c0400c41803014003403203000f172850307110381a40c80358a00490300300020414400f0b220800c003004e00004200360f650301c40900700c40c0180701c2c40840030141c1d0707418a0300610710f4000b03030b4501040038130f4041501c440d89800300c1c40c9401521030f4000c0504107003552003849628207411010011540781044011000b047c0d078028584640c0c180301c0b503640e50b01703050000c100c0c21401031500300d030086100307100600800703007504100c03406400101c503400789a6a170355918210690a1401040300740c024147c01b075040050001c00342010511800d08401401808028001140641c07000500050600344070304155a02411031300b00c040c00c4021320149000314a4a07070b14181e0b44141c3c2c062503805c000040540511400441840c0c10420038030150091110302400244800d0800c84040c150f125030800d8070001c0780c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 427855341 1250 427854091 427854109
    0x1710110a0212031812090405061e13140708270c0d0203010e120c15061807030e010915050105030a15020a02030403170306030f030301122d0f03090902091e 68
    0x410702121202418502c1c442c5003031b0082c440b0700e402107061501190881c60008074002040318003c074100d06040e22001013007042c42d0400300c521452070b03841c21942110b103451000300b403040446880f09001c13400c04520300a44282c1c40c20104200d03143c09160b01e000c100303011540034044d03042180c9100d0310103464000640108200c1401198074400c0090700300e4804080b0b4090310300844284243c41020500c40d064410000c0704440e8a94803c204c81c8500c02c0c1c29483c61078081d0000120f140000707070680404440d500715034204406a80d41d1124031140b480c110094051140544015000382448800305d0750f9074511541c40100c40e4101540100f540d000082c801c105403401583c00540b245282180c1020340402680280e4440e070090013040c4281c0b8040da4000101d03030489400182c0c020b101c5215480316010100c135148030020721250042c0c1140105141c900321801d59008003147c5c40f8003070440c40e02804625185d0b205a88450041c80071126a82e0360205110010710080c040400c2c00040a00188400e1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 427856591 1250 427855341 427855381
    0x105130503010e07030b0610080601030903020106091104050909010c020d0c0323030f090606010e190b0d05070f0801050d02010c0203010212090708010c0e0a060f091710110a021203 79
    0x1620f070942840c8900800a8120200d07401607416032115103810050210350071078802c1042c0810f00c4d40b00031582a52003035100c0480c06000c1c0c40001902600c840c1208159002e202e40a4489000890140400d1a2690345144c00c0a407050080054035003824019442d5000e2201c3c01052024140c2040140350089200f407041401201580388070524294803411648c209940b095a0096548000341d050a00020041d01550058485854001c072410402426190104100884120f41407001881c452440040c00d074600381e02d80e01244a2800e4100203003100d01e04071801080150a000400840e228030301c681c4e202c160286490310141500e400400d02a104082194a040545900f08070040901042110030b5910b07140090083c1d5640c9501101c030504580542c6030b0250356407900b008450b024980c1000c1110450500030703151941c1d00513040c1000c4107202042e2443c1c02031444500130314901c0c491a4103440d40144418248440c01d00c1c001d65851100e08072060259000001c144845807040c034800d010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 427857841 1250 427856591 427856593
    0x90117160806041101050702030c221a0111121204081204030e0a050103090c17011e02040501021e1b01020c03030a02030d0605040908030a02030a090b090a050708010e0c0105130503 79
    0xa0303a5004000c2c1c0e5804100c8040d2622803401c0028409584520101c03040701d0f40080040c40c41300c43c420f0411000041a08180000184140c20780541120500880030f0f10080d880452491040f00d0001510740f1200310594402030300f010b00e11407181e0300ea0000b52201070078105103655981e5128a400c0d4440d2184134015040180c011081000305540507050940d00e00040d9420218943e0303400c010340035501d94071401803283e071840c031060004d80d038442c40066400d0352000000c61491009042c5100391410b4040c80c82c0302540004090085503010040c402c518541c0c06900c002c030100390000a6108c104034a101c018048000900d006903038802c000ca00406407000742074070754884011402035925070000d0100030046c0e0410400190504c0c26105420300140c2040c0d0030791031a85d82c078542a000394401050018003680e104002004140070007429440f0302d40e080d00800c14211a41031062411180354001e5401d603040203268500c48030301150000503c002824030944031050181810b241070301c950401a05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 427859091 1250 427857841 427857883
    0x70b0103120201061413090203070b04030c0e0f01050f04051b1308010e030406021e03130b0901030b030c060a0c0305040803070515130309140117010906050315010302090117 76
    0x50101111040740364000307070340003008929982e54515124040203102168007007420322540000c561160440030b510751004003a1a00c0541b0396040840941040c1c00a403001d07001840c0a00241c015100d226030040780d0440b1100303040d0b15000001e001280c400e000140a161550007240300c1c1001110b04590f02091008142d440d10b0300082800780d042c1c011b101c0d0303606943c2400410090481c01104490584a06e640600320f014403480c400c244076885551b4011252108010940e1820310029206d40a406079201c02580d03500081c000400303403030f0071402540c465001101904255654030048412044460074094800e0815040946072801294440a064040003030359504214022032411f44850300001101c3c1c6a445a1101d0b51219031401c10040c04582118402d0154100c861f03104048003070149011203032404c06140f2548010805c0e0f200740b0300349483d0030051181c0d2600380a4141761354a80141000c0c50b6145400003807040300184142d408003840d00d8022000d00700280100100041440d41c0440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 427860341 1250 427859091 427859093
    0x60c08180409120203030a0f1112040816031205070305131401111305040e0601150e12010c0305010608010605090616032a0c050103020c0c09250e15030c190302070b0103 74
    0x5100e906c120307001e640c5035182c08035050160b05248a03540301c0c0454110001c0c20031030380300031040a00d58040c10a4440800921020205030981900d0791440380c4a96503004185000212004c107649004e0508405d040c01c160800400145041d1820251604403d103200031107205c0812078010040348040c0c00106800050840000f0180c0c140d0f070301111025501003003451052401591148000e0040044081d04203845049143c41381e805590004030007040120550f6805440d5800c40382c010312000d0100e901c1d9030041000c1500489010300600582c00c20510b48400c400c0000d41902c0703400342a41205008503402c40034107114000700c0c4080900c1c3c141990050080c1a40e801d00d540f19500110740750141e480c4086065440381c002e48403860034400c000c001c005204801c104402800500300c0380380c041300e40110300707203803160200b181d151003d140c0320003444100d050240030742c1c0c1407030800c1e280310004d0810600c00700441400031510420020544410f41c001a01d030102d011b8403440101030024104800040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 427861591 1250 427860341 427860343
    0xa060305180d08071d0a090c0f0f0c060e01021b1501271a090109020904051006020307031202090901031101020f0627010f0e16060c081804091202 64
    0x15018412404941c04070144141e201c0e030340d40102044072000226114041207142d405038504942030b44100b0034039007a10f150350010403d0309225900401903252140307480d2403030b160002c6c5803a005207400d2a12540120b0380000152250faa0a80c000f003070344e42d40f65001da50302402035042c4c60b050001c1c00c8207503d20740c1d01d80c1120b6984114031586041c000710b0358000040c5503d402150102071003654860111b06c0c80324181494002c040182d102040341e84240c81025556580c50441400380001030001038941d03031601c0070f120450f40001c0c110100344014540510840c0e17000819108402d9151500203241448290a4000790084034101a0480d48003800030041103103500c4218410300e07081e130031220345506000000b962441300b80e4210349008481e14003035524800e4400c0300100c0301c2591001042d40440907140100312035050b4082d00d0f4079040b03900080010784280441c40d000b041280391281030032100741c9030901700c1c0c80351158520b080704000e51620f45944660b0002d55040781c10030041551203d00e20400303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 427862841 1250 427861591 427861601
    0xc0304080f241e070528030c080c030a0509030408010908091e0f040c050c06040b090d05030403140a0e0d05060f1b0301030605040501200702091e15010e0a0603 70
    0x2c200408240c0850000d1511107411480c403030600205280c0b00310302d0075580f501d49128090115810444200b081c20341c11210021448440306845000041e06050500000c1c1120110150309081020940510520b02416002c1c0c0307401100c94900040d040d140c001c6200d03d5842241e000d42c14650a01070340c5000e0000540107800c28a0041c1c802c12480100d03010010380c1445250100e0342d00650420040c0e0b0f50781040d41c0b111402800071304101d4549900486070501d00300c002c031801c403414030400c003c200d0251014042c421002603030b07007842800c3d4140b5543c00340222603440c1950350010710104008180c0351044004043c0020044d00010f690421030800c2ca0720ba0300103c9034642c01e4058207001c95001d851041d940d184080c100b100756030035a401c5507100800f5141c041c2058646d9074880060400d040c0c601409200704180307100380c8907554455031042c081030f003a00500703070344000c0d80303144810740030641100750b80e43d200c2e124100b071034074010400e40107940980c50069816080400007102150b0340e030f00341d03001c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 427864091 1250 427862841 427862863
    0x1e0f060403080f180a110f06070606090c05030403231201080615060a0f080604140f0a1a0a0302060705120d0603060b0d020a030f0c030807080702010f110309060c0304080f 75
    0x403500f10755454864184a0004100083d1066405882100049608010055411000100703030084d502c2148000611075003041009840741c070341e1030781d00304070b0050f05110740285011a800c020b41186019103015028000d008030801c101851007100c044140c900504031149000810f03000c0e03d40d56110414a982c0c0c103411141e40ba8401080545055240f404000303640e0012031380e41d100c240e140c45070030046500202c0900740c5900030351103d040380103140700d03510b00d180300e140c00e074401d44060b249c0202e082c01941e01e170103000c407107650f24540a0001c6484803103024095230b030151101540c1d04d080d0700c0d00c1032600c51044407210f006040415980048400d50b04544226806007806001c0700404008024144468130f4009610009906081000421240001d40071b035004881000d00d40ea940d480d10742113640404022209100009641021980c022516010700b82c15440c0c1a035036800310f01c50140d905d2003588a070301c0c803620000c40c80454038003003003003218044e000a4017030721120080f800c403050765000c0d1006 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 427865341 1250 427864091 427864111
    0x306060a030c140319030f020d1b02120c10030605010e01020312070f14030709360e03041707030b012102040f14041505070207081e0f06040308 63
    0x224809150109440342a250044440d201007494000403140e5900c1103200746805001d981900c0401c45c0c284c812042e4000c1c0680c46110865144800090030525040940380c1440482151111103014540c201c0c0750542d4103841501d4074031000d0012600c0c018078082c205520a890803866802036900d40c01a40c1111401c0e00c0320700030348079084010b9859010342e207442c91401c10304000090015204400d0380076000d110342000751040089010040665000700d5082d0003080e0500c20400030a010902207840800480d88071443c420780105602c40242c0282d018441e00d00d884021448444405000320740040c08440204d103915881c1411650300d030480780c03005940800c494000010443c05000d245112240d41640818284035641c1c01c002c0200716821003240c01c165108805c0d5201c400380c08089025500441c0050039101d203c4030034a0a40d10010005c10864008100c1040307a8a1300042c0d20640707401484000b03041544c031081d810321b400d24403031950a1510411042c40700341508010184d019507000300f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 427866591 1250 427865341 427865353
    0x606050d1a06040b0315060105070b0703151d040f060204050d031d040c0813060f14090106170d05031504051e01050a0e2d0c0d0f09020604050603100312050903 70
    0x701000f040724098103195805400c0703007501308080200400010b034402d03814100039051955a49420110b200d01b201c801c070210366039410b82031184507080554030040c8041e80c1c0b98001101c1d4035401c11039498003e0001800c0d02030980d402410842d1036010780380600000742001802c840075040003800d5820603000c0d48525030b030380e0b1001c81050a0600400c800e00a007038070350801d01d45400b00494000d000307c201c26100c803a9100c2c0032003086450b500441c1c0880c0712005010001d420f082d113405d03003150a194410f41c00d03c041d4005408842c00003041703910103040a07013080e40c0c60350b4510302c00001814507a010107a0040c60070f0100040540c0707913502c03041301c10040c6011802c0e603070302c079010701041c0c86c6903014440240d0042400903800403440541c00342000795810301c160340c648030a080c0c40d51401c805da910055240000c6080304180e95148142d0a10f007002d42014002c40100f070700407800c10b01c40c0340540d80c000c03080000003500310b50600701410000c43e4030000490120b6400c40f001046500588409807280c0148 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 427867841 1250 427866591 427866601
    0x151006121b0e180c0703050a020a020301020a0305090d21200c031b280302012306100306180b01051e07060b0d03120e161e0b03090c0d0606050d1a 64
    0x3d0f20b4248600003c102c01460030000382c1b0150380c80d80110021104600c00e119590005803002c0c00a4803042d9200d480104c0c484c00e010b0005810402c00c285102c1c00c0041a0b4108111200d40c02800030250740442c0c000114a420ba4a03c4030001400c4400e907205228009141941d1913000001010076805020904410715811501d080d02c4010000d0348074101c4007148400c4890300c1d0900b052030302581c03090000140d040504105484002021400c42c240e01e0182da003085854141131060030b00c200d0080c80d00300800740c1480c412120b03803050384103007004140c1d403040e4040c05c59028008840f40c0032000d05510004031002001049a9442620200d5102d41461490b01103070500002200040e58540c641c2d5007420f18880f1018024407981b01c07800c09912588000804049040c55014050b0540c85480005000400744010f500000ca50000c5400a410420484800404a01c1c07a04521088900b059401242d05160001e4501500004c0d0b02c009054607101c10030040001000703009d481c0b905034042c107a40c1c07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 427869091 1250 427867841 427867879
    0x31203060b04030b0a050a020705010c1205060102070f0e070c05150103110105091e13020a0503061c05061603020409020409150537170609151006121b0e 67
    0x40c0f840b0003010b1344482e0012507100001508819405002c5207001424000591242425259107184c0700e000b043c10b41a80307070910903032801441e51082084c00240300980c54842e281003030404030b101c3c54035a6440c180101d0700941c856000d1524882d0044102c90b4008480140044207490078071080303400c44a40700c0c0016455010703e00740c41c0244c0c2d006008240c0d0068200a0b082507694a5661076441088540f54100300101d03440589000f040b00d82d40e0648915090040c000740300a01c0c1214214540401e290b400010070004032580d115540710402101d2101d42c80c0c1c29000f90050303030040c0c0602400441e001c59030500d513600c4400c4154108413410003007079881041c00244441c0c0040d618184080300400340312903540060198015504141051509070f035100c0d0703904070101c94500601d4680090080c421800020001000e01c00000f0144d54071905091a080c0c1125019104850a001000504d00b01204883d80200001c0290b00d00e449014010320800074503000d03224419501c14445c240c1e1004590700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 427870341 1250 427869091 427869097
    0xc11060f010b0a0c02040e03210105040509031905040e1302041a0307090b030a1b0321120b1807050a0909090809280b120609060f01030513020a031203060b 68
    0x2e02c800c04900d0b00750070000c211030719504420260f82207070711000102e00c00707c0d0030001412a840100c03e51080070b080c20500d00106030040c0d01551245027000b082c000c4544c008812600b40f00700c031900c0440340402c000d0090f01c2c0bc4c05190321444040d0940d4041003501038000001c11200751003160100101c40709000212060301115040d25015405404240068000c59010061002d0010202d400c2f0240300d40c2c0d00c1d84848440d8020614050b40d0103401c02c01c01407050b0742d8009004200138000200b802c4803000400d0318420f44202c15016458101e030507440d40f00d103222a4108513420000ca66a40f50418029020f81d002c403100c40001400f4a41c0024034dc801c520480713154940c401d245034541203a000800000300c8205050454108001000c0e041420321040c00d0310003001e05491168455120410510117000c0c000e0010703000d41e45010800c0141d5a907115464403502c0c0c00d0900040035180c5a10304800640e406500075000080c0c0000881405044004620b07610320320f9500f03001c1c058480303d030861180 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 427871591 1250 427870341 427870349
    0x1b0602191b030807050d150f0f06020c090a06030204090609020102190b0408130b0a0e18042310090804091d0a060c0c1a07030f060f03080c100c11060f01 67
    0x1c8411105000064030800300780e5000340040c9012410b02460001000c200c92080410460020b5441410040e00765140712030001850b00b4105803460b80d1604034040d444002541c0ca56100302d40300780005003008090780c0004e000e1038002d0002c00c111400c5203000002454038450a901600c40e4a4078086441c803420100b0640f0341d84120720728507503160341e600d024560700110101000e4101c0d80501260940182018006d41d04103139660b1003504034203800784807407541540c40080c1c14050341c1c003c00011404140d803812031000340c045244409040c0211403810a400110020400b03418801e200003440b400001910658030303601c1c410080c480950340000044017000c410b00c1d91540056691502145555000344100604c5040c00e006110144d9241039900c40040002203208152105200d00c244d818401c669100c00685810800c550420350b04000c444d1052100411424001480000600040c4440c580748180c0c14401d00c040a02408007410140e141236450f41c013407240c000010041e009141c0c0c900e040b1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 427872841 1250 427871591 427871627
    0xc070603020c011803020a03080108071a09010e060d02070203061045050126071406070215030412021204211a160201090b060609011b060219 62
    0x4614011059019400c480320308202d9540c0d41c1015040d103076901e20500001482070b400b40424050526000e42401310603003100c94594003440081c1700ca0310101224805844003e0500c43c2c5804080300100c0c0d001c008050300c1c6400c1040410300d81441e007100d40240808900c01c0741683c90070390b01c140c0142c109490600c1050070001c0e0122111680600c500006001c00c2642102d040030201e490340304100c00c03e0951041c40e06141c0d160010000038503c103507003003103070700c0f002c0b0010030b1411a0010300c07941c40019000301e021044c0300c2c481145856940c901102c034200c0d4007501e11030600c403200d100740380307036800c02c40b4203513011030207843c0701c11200e4408180f001500070206291401d16007803c10003105030040c1c2c408542000036000c907450100c0d444032058903010400b4646007845103410380780c114004642040900541e03060516000c0040c41c0c0201303a580c00002604c605444003034140c012100c0e480000414002d0003107134080b010034030401e03400400c40c469000c1010305103150300c46411144810304c00011040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 427874091 1250 427872841 427872853
    0x606030304030219080105010b0307030e061611030417010603030206060130092a05061c0507031d06090c1206070305040203010e0d09080706090807060c051c1706060c 73
    0x1032604210100c84018202c2c4d03103509003611401c410342104c0080c0c0003c0030300b21010042240761075160059140600f40000640f45504202c2c0061460792032907100e41d0244416408080010354040055400404408850000410402143d14000c0407540800d030014020f600005a0b40d5000d450703049901d018030004a41260000e4003407503444c0200c0320700c19a00684501c0101e000c561050078000003042050380071400d0743c0c02410140038031071240d484140202c00c14080e52216245180d42c202c200070010710b000c0340315030b1003550490003441002c203034245400840a406035044000a8a00d100e01422800c460322001043c0c2084589064064080480c0c0e00c4000003400c00e500c00e0b0012508a071000d000403c10044004506041460802d11100041d904401c00c10103140c04000c80300041040d418039004190034462100e40300c0d41c0d540200000d0100340500c2c1d80402000700607201c803281c4015030100d00d1005070240140003d0180118198800d2214080750061401c0000c603506600d5000003030103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 427875341 1250 427874091 427874093
    0x5031918030804180606090b0c01090b251e05090a080703140105071818060f090b0a05060304020108060d0816030305060102010b01030b0901091e0e070305060a050411060903100e031902060603030403 87
    0x941d40d1200500389c1c03465403a82d01e4400091581d503a1a406806c0b56a091080229107203408860465415044400c000134100f122070b030b40d802c000104000410520341a1740c1c2d030100b0004900c0c01503031780e03020004a2103141800414000390b4040380368040780d900d009102c3d41d01c03503070780c102d43c403111200c40000001031140007000400c07440003101d5440110040041002d42d6039a8218080403c0e40d4082411aa20750482104910b00a0003020103040112000740c00d40c24980c0009007903105c01400d15015038181c0c04401c6c148007480d8103072480103454102140000c01c1c1460000c01802054403c18003540c20030200440540c068010704803500000742140c18241c0c40c1c410410081c003004980501404500c4d00f0075903a0070503074000c1010841d440c4004280300751840c58441d1420100078405954030b86424144000204020702d408120301080769042d8981c140640003a042001c1c0f01c1031001c0c0d0b1b9280c400b0700d218230003010016000759104070040c0038080350b8801781640c440c441121219456081040140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 427876591 1250 427875341 427875359
    0x90310060815041b080304081501210519050a020a050306250509062d04032006120403080612010207081210050a080604060b0d0503191803080418060609 67
    0xa510134028512811407690315408012500c0064100840d02d070000038007031113803090400c072900014810b03034801005e5600d48458581007100c44140c1a101c05140720400d001d000c1e00f00301241d044403400f010220071132030b2403a0a0ba5a000c40360000c90084840c80400202d514001c5500c5100f10340802078800c0700400c803001c0030042d54a400070740040c0301c0140301c803894984900c4064503400200ca810301c030035450449400d21020103c00024103e5040822043c800a122810002e125420034550082440041000180e0901440115248804500d001c000c00d1690080c2a81e000e04010303148021031071125040b4900307074450341d04013400400c000c10084c8580090a08a140e0020707000400078074030f9880b000002d02c02d91443e07210b0502a40014240805c0c000944219080d10358100e810092940445c0c0d41c0546034007422031640015400c00c4034004086014060711070743e580585c908840165281c1c98941d1107a0894000c1c68402d0760913009512017811241700b00c1007a5805911801c50581ca031000c04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 427877697 1106 427876591 427876633
    0x40e040624090e01060306050a09030f020c0609010e0d120807020c0a030c0902160203061003050c030303010806040b180304060f03180b0105040f110a03020903100608 73
    0x181e908905000300c48400c03038610810205440c651012018018201035002402d0b0301e050404100c080b100660021080a12a4854120319905001c040741d80300c4580000740d41103d010401c451996016240c54807100000519a84e040740d42966003040c1020394031114030104102605200d803081d014080200d01c0f0405541841941d8510b84070084542c0c86403044c19815540001d8262050305440a04d8491035006000c031551400d00c48030f8511101100c5c8015241c034042c5040c22640ca183c0031084034100c0e40281d0060002ea22652500c40c4001e4001d05403400d51060803040048a81c0c2c14805032006000d107031108001d0b42c140c4007001c1c2c1a43c24801f201c28440b01c21401d100c0c002a04d4848003415a1030607a400241c450710401e0010080c140c00c0500b1281507801301c0c107485240e83c035400501000c1401c0e01900c0c810700803102e60002355031060207441070580000300d00c1000c519010100d = true := by decide +kernel

theorem cover : BRFrame.Cov 427697841 427877697 := by
  have h0 := BRFrame.cov_init 427697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 427697841 ≤ n) (h2 : n < 427877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
