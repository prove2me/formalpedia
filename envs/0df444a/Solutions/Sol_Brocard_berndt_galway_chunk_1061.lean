-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1061
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:04:04.794292+00:00
-- url     : https://prove2.me/submissions/1ae6a70b-87c1-4ec8-adea-145673356d4c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 190647482 ≤ n < 190827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 190648732 1250 190647482 190647491
    0x207151d0709020906040303030518070b090a0b092b0b040b04110a0305060c0906121609051008061e09090604020a06080c03070804080f0f070209010b07081b030d0c0201 74
    0x106108007401415280c02c2586001c40b00c80004015118500008090607074490206122024103020f0851502d90f100481d148541c4480c803240003500705205592259040030000302e4114000019950342c030401070024491018411400212144d00156112a000c4c52120a4001c00d44500d1954000c1e4000d40f0b43c00e441c1c1c100350600d141c18615440403030780559001841040010380015049501101e000c012503181d49001000a99910441103540000c41219003805815100065202a400c0e29611000f10b016920380c28400000030b54440003022840381070000740d031400d04140389030020745500e96404444104800080452405440c0c2040341d900000800c421400c3c586c002401408060034200520324154410328254400188500100200d0078085000c01120400380c1c0d0710030860540e141d0301c40c0e0030481d481c1d070642c101c03220030791080310707a44000070726040c00c98102c4a001d5005841c0a182c00240d01c2c11b400150501400c05509e48020015042c24108501c20095a080c82c4d40c000316 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 190649982 1250 190648732 190648781
    0xc031905120310090506010309140c190b040b0714010905240f04060e160602030c01051f03030c051906060e07020705031b01020f1608060906011503020715 68
    0x600d85188070301592985a810014864883c2d01030031400110b84a100d40440c2c6580e8050040b800380c1514031000340603500d60304446d603038540040341d144000c1105960307103056070702103100340c1111469a10498801010400080c00242c0d0540014140c8a004160000142c800b40900c582150027018064034a6040003000300202e0202c01485d06800f030340d042014035181400c05020380c1d810300142c00244070654400c80c0c0200c0300c009200009403002d203e100c0c442030a41c0c442003c0d4581c0c0c01006030110551808002441040125044051000340562102c45447c00d40e9030a4a581c0f00f424000d40740d61064003207524403403218000c050102ca128000c04501c0724a41156403c10b982e0242601c41550032460040c8200d4800203680b02c000741200072810714151040c40180d041030a1455801400d004501c5d9180e00c85200001c02411291900100c032259510110101c0c0c44000a0084039111480b02880c0050240301cad0b000760032031a008140810701c3c512800b41c148222600c485e80c9000c1c105110b100f00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 190651232 1250 190649982 190649993
    0x8091c0f1a0702010e101a0a0b0406020c0d0f03140f0a02070501030b030a050d08060a05120109050f070b12070e130902090c120109050c1903050a0c0f050a0e030c0319 73
    0x342e400070102d0000b400b208040158990300c6041d0310200d442d0031a81ca1080d102d4050b02084040301c051006400d03034441ca62120f810014581c028007070a4058402c0c45156040c0303061162442c5802c5411405400300e0200581c1e08841d03692000b080310940c080103210100c841407100700204240c44030ba0700140080703031070080090142e0304901220351007034202c803c80b400820700120b1b04902008080c50607118507a039545c00195014120740080360804030306028103030340240550040c0b800c180900200c42500e0340818401d60350304180d014030101c80b001480071980b40070710b5030086500b200e030904180d8810322011020031030a2282c24808095036840705100c109504280120a400280404410b8030b003118460340000011018882c0082a130f964000143d084c80c503510940d15040c80b4110b0f40000b48012180060103450240d5503201d195281400720000b0a0083e10f91560403100b9840d06400c2c00160f12060325002581094603406000e401a00c60440d035003403024581d0880d00c030705000f0f101e00306400c04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 190652482 1250 190651232 190651283
    0x4050711060a0915110a20070305060103020913030f0e041d030306040c02030a0e01050c07050301050117070e07080c13030b16020f07030302070524030c09040f0908091c0f 75
    0x9132602c1440c000c6004e95819040c0105c6413158031b43c3c02c0c940080d0030007490045103000f0500700a451030041c0c00c804800c100012803080e040782c2c001c0341d680314151511a400c0072440070424008020070500d1084111141c040d8046182000c0014000540810214594a41e4416850500e02d81d03410000800065141520620711203400d140300650030181035160207800b1079a603001850521101048401d00c10f54200856006084060024081c550791204454170850018050300c2d00e9020310170000c616001200400c40c840d07402c40e070310200310f52a16000300040b607100c080040c01c513075410000400071500709003105015401c03900650341c800c142c00034001c2c240400000d42940540180074100f0100ba40041c1040c150740007103400c101203003810108100c2c0c60014481c5e51400000100c1000118030a60002e07050048013510140300044d10505200229482c034000101728031130501046500d4240b090240240e401c030211441c10440c810b8480c80508070180c0c0d02200e41200c6003503000640986840d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 190653732 1250 190652482 190652513
    0x200303040c0501020d0906020c12010609020c06070f020c0f040203090c041407120501031110021c0c11180c1c140103170a09030303021813090b061203040504050711060a09 75
    0x38401c1b2410304101e0020b48601229081d507114071205a0703100c00d400002c2d131251000304681d02c41103544411030b4980c0343c0c4814046540b1008506c42207825000305002090b01186802e0040045e000e40e100e1108020003500081c00b0b031110391040f03900c3c050b91500c4030300c20000303800410200c0a4a030b00d010000105280d0760944035006550901c0e00400c0001c0c0c10078003018a140d0122801544200c3e580012890000314000c200b0f10720b100e42d500d0105a40e001070030010914007491402613807032651014004545011440e041a9640e694005a480341d07140003d081300c1d4503a50307170540481140c0c2c08524107a0f985200c04403040c560b00c0c40100b0420a00e500c580514258181501d810079000345005042201103100c00350a05400150382c920b101c006400609070b071030b0000d11850b020350443c98a01d008064052040f900c00d243c0c440813990300c1c501761004c051180503241c001c0d03290605003014440030b044050700705028006003840511803884148070807481403680c00c200042075041d03800d040600400c94070f03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 190654982 1250 190653732 190653737
    0x9090706120207021c1505010902040e13020103112701021c0f02120d1a06160303020904020403210305060f01080411010215100503100b06030403200303040c0501020d 73
    0x820400469820207900031601601010058a660541c0041341c1c05e00381c481d00b040642d202c075901000c100070440c2844020304104d840100074580c1c80d001d024003207110300e0240d4185900d10600048240340000340382c0e05a03a1040c0340115003ca82c40241c528650441844000000420541400394100d00c60080d050090b091005050340d030152070035580c0b1000081c114004001d007010729860014002c00200350704516101c0c0303240d507a1403440000070007019a50748140910014a0350b14080345031100584504003003c4a00c05010003003540c05500070360012500f503130840d0702408000041140100c40d030b16408180070500c0001d001c000c0c030040071540004d00d580d21540b5612031010f100d0364000d545982c8141d00c00040c00ac0a80c107100117070b01d85010800c00000b0012214100240001c002911108541080e0f080710401070b400d0605005407402d64134602c0e0802028000280031034442c0306c1c54203403190044c1c07801400245000c80203003140e008075401e640000203084200810359041046610700c1d08a403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 190656232 1250 190654982 190654993
    0x1c110903160f06120204120602030f09010519021305090c1306050301030c0b03090c030a11040e0a0b0411120d0302090a0501051e0a0e03061f0b071505041a070e0909 72
    0x80c00d07002c010400d5000f480200000410384080c0c500d480c1c3d0468020700400c003520341c0070311000d24084010398011a240da2400945078042441c1000501a05019619509208000004000c1044029004484010164086e2010006258640c1d8400c2809030130300c1c402d0659156908501d80790401810350142040050402c0100041041300245d03a00762100301c006517035240c4480b111603141540001d04564180148200744c420024411240448120181c0b410301004a20b80c000c55201d8a0202c000707080d0300c1441000030f00084204070b8000c1c409200500c02080c0d52640c134521440c1580e403904810210358001000b020354501004540e00400092903d1480d04070f91a08041c082c08250004108400002c5542d0208900801c121400a84090110f0f465843d1102e0068840b500c00544450080300c103900210384034041c3c130101c8000b190007500e940505042e26144400800d40200b085d50302d40c03880340e504800d40e05960040d42c040d044650b581d114410030f1004201207500003038512142680310 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 190657482 1250 190656232 190656239
    0x6060f09030602070f050d0909050604020424030e030318070f1206050c0d0e03030402040b04050f280207050d020601050303130306150306181406040b010302061c11090316 75
    0x406008001d4075400718000d070301c2c0c425a14103032800c1c500e0044000c150340241200a4100c95221040000302c510450041c072a41c1c070340c85c0c1404101d2245000d0200e242128144541c1000c040e004001d0741d10305e00d45400100d021107004000d05580065030075101030040844225144002000f00354050158001c081c00c895250854042c0c5607132142c50000c000d00c0c0c850000070b4603215200140c91078042405800c0c40740030705102543d500d90744100c42c00c030311840c0f0700460b02d83c50303040c1446118801e80c8080b809166a4448010341030780141031082802c46c4000104122642c100140094003030300d48640e000700060316402e540a8103000d0140c000c4d81c026402481140844941c041105040344d13041030b000292104900c9240905500c40e800c068607540c02c08118030300c4e0a42d2498140d01c0603000348a0f503030b050b0182251b07490711500c3c250780280c82c030b444150050000d803500d00020000e81d250b0b100d44044119000480b4801c4d41c40d8803154080070b640200c0c401e80d003800c092104201c14080500c40e046050704 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 190658732 1250 190657482 190657487
    0x910090f0c03201017041b060e03010f0b010c02121906090b090d080109150b0a050403030807090b0306090a0e010e1b0603163204050a05060a080406050604061d070306060f 75
    0x211444071910a070000c1020400340011f0004c1c1c41c1072420491428000562905406400c00c03202c1320703c55000750320b0070341e0b03a001807200ca03c12407001f000165160034112003140c0800c06071803a010148031890140d40150980c4003140441c40814601c266404038042200341050524550000c0402c2c40c43d802c005d001d10b00e110f40c80520035055a454201c00580d035004103081e000451102c2d00300038104000007c0b030b0106260040060000c90f40b20b0b59440c41195107080301101c244440d407140254104081c00425105c0c40d2145034a60f0101b80540000380001d8015112400e540326a02c4448190b08001c0000000351143d11032159141001c0d50854558100550084010704940a1420804c0b101088500b03080510507202c0310032241035902111464000110b90301540c2c000d104040c821a0904000500d60900c1016511056429183c0382e401e03030b90340e844203c042c0400900042e841552140b0104003031440d050345030300c00d5800400c03c0031149480000a03089615640200003480140d0381410103156 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 190659982 1250 190658732 190658747
    0xc02010516030510031704030c170a0b1e0a0b030712080405090711030a080a0617030a1805100503011701050402031b130f0207060b01080910090f0c032010 68
    0x760145000a09039803000328540c40d051094000030881240c4c20980140c4010340801380043d64000d241c2d48100c280d80788403255440d411020030280b1900000c6022000c9901d0043c207950100c1d595103d002044024008901c8100046818207481580c5c0d000000840c00c003085401c0241c2904024a202c5060039219181c0a014030300c0303040d129800c1c2c880028241d80c4660394450101140702c0481e0707240d0f180e941010b030500e141210741142e024035100700000e440302200c4550754003590300005940340a60500088452500400601126042603100000c040d02c51a584c00c0b1110482c0c2e41e01c0340c4a505040070382c25024011490180603a041c80c05000c0981e90204070702c40140b00c000348004c0e0705040040031840842408482d1003020b4900038801a00419a17001801d44c03500c200c0c42001507680007801910780d20302c180d4610549900c0900d0703e42020700305a201001190090001d1f924012159540295100035034200700d5220603440c0e9151034000703020511310391043c0121804048250b0505004040340b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 190661232 1250 190659982 190660021
    0x60f0308070602040509040f03020f0606060a05130f0b0703020114041e03030b0a092a0806010c15051f080703021e040222050111011109010c031205040f060c020105 72
    0x91400040070020448a54111002072130050000f0f105031901d82405184041407400c16030240c011500000b01e4154082202489400f004210509010070740500f2101c540140d00740034800d032400b032000301e8805c0022980c2c6005081c0d140d500c940d00ca400349402403c4d11403c0d2034040c0304414140612000420650031038040d81542d007ea4000c1c800b6900b412070150001500098000180d01030109a1a1250700a0681b041075101040082034880d42d010961807004031000c0d00040d250700c0072a4480d8440c14088400c1402084031f803012910202c549030496400707503440030221012021500b81c0102c858090401890090301a102140c915000719420740b6440304c142280140580d662811f665507030b415602c10038900b01681d52754411140000762140018080d56000c5084021a4110810705000c2c03000b00960040c44141060180ca0040d540c0c408906011001e10901a00d400c40c10b291503c43c00d881680100c000c0200b14003d810a002100d10900054045905000c00c1001104401c0d2680340c44 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 190662482 1250 190661232 190661243
    0x1b04020901090b03011203170601120c090503070e0a05160203090103050402010c0b040f1103030c07150311030f150d0f0209040c150507060e1920040608100609060f03 73
    0x56501950040702c030880070b50482902c04901000104100500c4920403543c144a80c40d002401401007840140c1404103e650500040010f02d0000200c5800c2e040b00c110035004e828046503480c3c07aa000642011615002048288030241c2085410b940314061150400011f8400c40070368138520400035100c2c8038503603449051540790300200d0708691045038400710303464000c5054607480c1400e181c000c0d11030b006607000391034420040c0c0c0e56250301d00e000b100301c03941c414000006014062925803446010341003120706c802419641e800d20001040d0402c01148559545c40444e800c61074601460001c03010341480240c0102e17040710b5028001008210072155290701280c500c800d598175403600c1800c01516070401442000411425040315130028081c010062051000348050501508034030360b51411801c020010141d040a0440454414040c0010804000303269207841c050f18400305094646a500a40941d80f01e03101e01c9d51040c40c02c3c441ca00103840703501c00500c0b4003881c003d402c420a03036090001928 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 190663732 1250 190662482 190662487
    0x30403090e060613030f150e07050906030102070f0f030809030f030c160c090c090509040209041203020c070e04060c090602060714090a0906050a060906080c0705150405010f06081b0402 81
    0x20b442d0381d204103855001c01c0310041440b4031074407880d00700518001d0040c2101c2e05800b18249000c0c5600d03e00640c0381c00c0400100a007031003450482086a220800342246800d95401c00c0007001190b910181c00542a0203003040e0303680201e0600e001009804010701c00031440e0024400070790000d1f10502100d0708800b2401c001a01c80c44041f00b0032021201c40b500041214060940000b1000002d81004d0303107081c0daa03103030f101c41c5607911000c0c00a070503402c40340203500032540c0d00000d00007661402d01d00c4007807213113150040c00e195240c80c032507281c00c60513002180c811081108100401445008105060041e0b140c17802c1160b00d04000a561448060031aa00748003401d0340381c101d00315a40081d5100c00d04020500001e00f691092804014860341c09440d01512190340046a518040d020007c11074465a644400079512110740c080c3c00d80200d0004c03945400395507600b031905150132600c0341c0030380d01990000580d02c1a0104090440701c6640c005c581c07907005842c41403105403049803000790f004020f490141c0d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 190664982 1250 190663732 190663741
    0x15030c04030b07020f010603030207060e030c0a061419080609060103150e06010c050304090203041b0f05040203060604050402070b06040b0d11040e03090d03020c0306061c0212030c0d02150c030403090e 88
    0xe0401c05e1502444455601c0c00f0b00010501d54001511400c907a40c0d5240c40c181032110030103050301d9002c3c10a4442e0401744849c41042482d104150381204203132107051150030032500e000712100c000d010401d10301c00548076800744403607490513560701504000242030400c05401d5041c40045054590711802c0004059100020440c0e400780010300b03038095018040d20f60380c640394240c0d400290030aa40a0340c0045004902014407015165240140d40c81500b51090b400c2c6420100400396000502c8150484024800059035444074005400c03a0340c82046082014a40182404120307a01414914481c444082100b80419040e00d41000c214405603070100c0c8408111070010b06d1803141119280c0c000000f4228001416408a1880807a5400f28169082503c940d420005107031940c400d44081140c03400364420042c41c100080c01a45400c14040c1c90174192a00c0c0c0360f90410300e00022090141c1c1002c645001c5103081c1204880d400b0310421403490440c203050714000c0081d225130007448d800d2510400840c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 190666232 1250 190664982 190664987
    0x1006080a11010e0d06091101020a2f040509010911040203010b1b010902270c041a0901020f03180a08010204060e190b0d020c0607030504051c17040602030615030c04030b07 75
    0x100f40820003425500c41e142091500000502455006a608070401c4107500010f41c40800c4520351107821000c106a03406a0280001c4203810050079041c581ca00c001c82d21901d03483e030340103a40c03181d40d41000004000e40642803070110303003d403400d00c0c510940c4100300504c4403040b0b80d016600c0050b070700e042c8003040c001e030228464010130484034040c0d881010b021030700003650010210a031241c2440b00a05985403211750160310a401030b0300908094a994a2044150014400103080a0b05051040751071414855403410b0030342e40b1030046012052075400b24440c2905203104958001e0825000031854180390910003050041c02e22005c82c41400345040d10040c0003503001c82030000d4000b040d0004c0e1744104659022009610488410f0503a000780000a14914082d1007924895500300d00644100142550030700f40c0440c0300799610382800b182e400701d038200b020b4030154588203d1241c4030042c1c1e2410a5800c0100070b080c0c60043c1c02108804004000c21055014251800c0341c1c2e0041012000342c41d0038805 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 190667482 1250 190666232 190666247
    0xa08062d040902040e030901110a0309030b04081209010501091404020d021504030c0e0601030501050d0f080f0d020c071403061e06120102131e050105120c0c03120106021006080a1101 80
    0x113036000303080448000c086080440103186a81003600c811303100151100d401d0b40ca6200c0f42c44040c0204100210400c04240605041d9902500c500b124600d01613040303044d0f1b03034400070690f41e07903d0b5699a04014080b03200f85200e1059a90350b02101c2802c00d14096000039075525840d032000307020b848032400795a00d10310031000361006164440006607484bc1c80e0701100740c1048040300d03480c0c00281071500025003828a040300d503c4541d04102d8103078a03810103440380f0407942d000401a01c4456802c11190014480a1000c0c1032618003c1c000b82100e10b18003100401040c0c0c61112442c070039003040c0240044c80744400c2c807102e0b0340300c0801401140b80d0340d000c00050f044c2c44451a4000154000981510080c0405400d1000d541400f00c068050852103041ca0302d1031681d42c000c9502243c5d04010442000c1200f14125074050000c030806890005019030303c41c01d6800c2134031241ca11a0a402c014007055406004100c440012010100545403800c003180b070f501e507486140a081c00e1403035903074070400e640315120 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 190668732 1250 190667482 190667501
    0xf0102070b0f030f0a0b0907030b06040801060303050c010608010203010b03180a0206120907090b0325031208040b07020d0c0b070315140306090607201609020a08062d04 74
    0x2641501c50280b0405062a58411260b485511403124005034082209100f030103480d0790090480d82c10b550350304000341c000f40f20b103803150359102ea400c0c04005000c1409002d103002452180c1c0c0c4654555091134001403e460b0607401c1a54264014401803002e0b18041d001c3e2680f05a22a55500c01c1803a1081c1050811a103054065041800025004501c109081c0014024900c2030220780140382d44000220403612400d130802c0c0d141d00f242002e003907031041c459002c5050180c0441c01054841c2e40390f4820035408400b07000701c000b00303065404000074451080d00310741c0d0184503800036110402114900401d042511079000b0400051100402c1889229030300c411042c0c2c0076000d1130101241c880d0100c44e92540527410b101c5c030030311a11001541c50240461100d02031101622000d94004601c0024100c4031480200c80101c1d102e11030381246541100300c050700c0140000c001c01a554442d14038014082c8400401d85070181394201c1103891002001040d145400440e5031074101e450b02c8400c0018050180e40c0d9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 190669982 1250 190668732 190668749
    0x26040203210418061e060f050702031002070f020102060109050c07060c030e0f0f010f09110418051b0406060c12051303020d0b010f0e04050d030b060f0a090f081501050f010207 77
    0x402c20f41c0602c0b0198000000d65009480d0f9103681c5002004000304502c0c20300401d400038031802203c0140500800140145510040a031800028444403040403600000e000350b519407182c4008206558040c801540907207040102403166140000c821111840381c44402064240d40c0c43da4404660f1080c1c1c41942c0301aa444141c44841a411581075658440d0b000030981551810810344921100c900ca281101548011500c1c100300e420740030040100f55070350500e07030b5080d40075894800240d4140180f480e441301d40404074426103a00b1003404101e410035041842804240d081083c0455401d55010080d00080e04d419666000084001c10981c0401d51000f508200e00000600400c0300c3d41030928142d0b038034001702c51402070b41d580030705e0760006c015103000e4060b401c22040c0701e08062180c2c0006d0203042c40508024034001c07118010010700d60020050100041d0080c50a1003d02e142c41c0400b002401b0240003400d8625420380442c94480041c89814400d51840d00c1c050910f0b40244507803401800c451 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 190671232 1250 190669982 190670009
    0x1704030206010504051e0c070309030c0f0e060a12020d031e0206010905090a20030114040501090c06030c020312060d060c110606010c1113110406260402032104 70
    0x91501a666100c00e005051169040500180b00000390491100402c0c400132140b000c0ba403140001d04c640d66010120681c20003000d1000800800d411003071050040203c0302259010905d0007022180c20313000601414440c01512904021b4401900400d940c40e03a01116150001043c92600380c6500e081c002c074101144886025031805240c000c034201e812560a05800d00c110707601e52025903114031412200402218401484801c02409002c132819180000b40c0009440f03003c440c0b09880c004070444d02112941c0d1540300c0d00003008501d001250082c40c1506044c4034141c400d84000c6d441c0c1c02151f0881100340304040020b07056554014140c1800b0350006010841608070442c001c20100360f50010007024802d110111b1402d5104e0200c43c0c680390b40141882e05d40182100c10050503090301100c0b00e1040d602c03000c525500740000d0008100800f81601c40900809100407450a14007071041d020f000e900200742040056100440d0500180580c44104104141c00000d0a485070142d600140c0384036000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 190672482 1250 190671232 190671241
    0x12020d0e0118030201050a0b0307060c08091905031603020a0513021207030903021c0903080306040213060e10030e0604080702061201030f0309230906010203090312040501080c0705070b0a17 83
    0x409204030030b45802a80240030030b661f9581c211054481c6c00b6062501640603d40c07c0140074030580201c005248518040303481c0210500000340c2c540c0740c8441c03415844920150030032191030200321700303184802c400c804641168035540004058401d907200307440c0250076001f01030601003455411185040f100c000700a100b130030404030041c002d00010404501503c981e09216981d4441548001c4001e0b140d0740d2600311150070b40d92661b415803c040c0100780c004c1c0e02401b8000d149101c0d0718505026104030356881e121408083c0c1006000c036800e8210f40d06061820388a00b49100c00800c90903423150f00044480d40e40c0c0b04601c0410f48910491a2805101d0b820340b00100400c1820100d083e00c86e4080d0ba2511521902c550349403548200d1043c04d041100b8803066200624108441d41c0c9030b01500c1401507a0a00c82c00c10003103820100c1100c2203040b1000002810301c20f56800441554000c008010100e04011582e0781e1182c0c0d980e81402944d040714004907401800d23a10a590401d01407119040324603250a1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 190673732 1250 190672482 190672511
    0xf1801140f0a060f0b09010309021206251103040e1f0e07091d04020f01120c2c03100510030210050c011a030d050c15160e040c12020d0e01 61
    0x1030758030382070b62428030030002032500ea0884104151001c80c3c001c140740024100064005110501040380c2040c40c060012171a840d00b440400d11800500d407182c09072030001841c0b03c0b0300052049800b410f1001804040c4166000001918240c40c469510311201d500c0b900c0e080d06410244026000c0d11180400d404074022104d4031266006225607100d0043c00c9840c0e0b115410720514810070000c0c00215000000e0140c42c014040b481e11490606081d041030000c072441205958061100b000403680010106c0c5103001e45101c041b04188400d444410b100c0e00384c070b0000c0d8032032045c003034800540c640701c07404504205034070a10100299802000b082140da241e01c0c001d801a08800c1c2c40b400c195291000904c20112050301c1b030b8070410f070000c01412515aa1110a80f00340d001141f03210818450f04502c0c0074007402e82213500f40150690000c0c0c0e00c81104882000707000f4041ca0308094011810241d001029540292880c0c0080c1c00c4409d015031210402d0101c01d0007006c050255408540c01c01030012401075 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 190674982 1250 190673732 190673761
    0x100906060b16030f0c1509020f0909010c02161208030702100c08010e06090103050c0616050703030801031203110906030406090605010303081005060408070608091c020616080f180114 80
    0x18404d03200c050107101051025500d00c45032100151061704540c0c110039501e12590700007000c05100400000a21804501140311100c0486a007411690745030340c1c00c0109901040009202c0046d00505400642840c624003802415103100808143c000710115034214000c0c0803406c0800c440d141d08000340f0b1188100104000c0c42880340c010401c10541c0030400300d042000e081340c140c0390000002c060681440781885603d03031001080c500f22210b0701d8503017400100700713004503001940241e855410741d50440c1013444828002543c1c80b024903103803203004d61107030700c850b01554a402c07821034416850b603880c0d050a8001d0311822078001c00051900e0004010140c101115600401030103040c60f500c80c0e240c0050009512490042000a6100c41c0041145034841c1181e00c0d40b001f0391605036000580313000300325a50003006144810240c0c00602c104010741f0f480040c030003201021490a20003d042003111a00300030b0003d051480b4003040001805c01040d003d40001241d5054501c030b4080501d00421041c4214 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 190676232 1250 190674982 190675027
    0x11030705010c080a020c070b0c030405040e030a0806061602090c090612100b090a09181704080c060405010c03201914010209090a0e16030602091011100906060b 70
    0x10f4005800f00310200500e00c01d480e0801c04107401000c0c664189140000150801d05203466548020800800c45031190b006500c15a503112000755114620036102600100b0300429050040c0d10521061101c80484090404420b030161201661034413140001c212a00c0341088154100c1c81c009030740c202244803200920300c50b4102810112003182c81ea05048818403980141c2580803000100500c20303030310664000580c0d003018000001074060300c3d40c0c9104a00101c0301c10003038180b80c007140030806102c040c0060407111900311403881c036203820074001804a10301a40046c04011504031082c2641105e000c45180541040c0100c51881d6055041c909400d16540c3d0112551410144502c44a04050080c1e9502c0324005201513625580c2c4c041ca00d0040c0f000c11403605180c4510100b440d251784003010010050750194001503035903103400c414010070307818070068001003142d100544440e81c41d01244c40300140d26165400704544406041042c043c0100d034000b00c0d02d08200240100c454001202002c514 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 190677482 1250 190676232 190676237
    0x50712021b0c03061308160c0e0108060601030b090a0905010b0301020415110a031407110d080901080f07050d020d06050901141206060102060105040207060912051c0203011d060111030705010c 84
    0x2514024002e1548600042c0d40c3d610300240c030f1581e400005142c586c040c05854958a040440f40d03141a280c40406100591050081039000401480500c000384800341e4400c4013804d051091003954004507030700300310041c024000155115008010890203403c107100c1c800008009540791601d582415000340e0303004c00302102042042901907000c080110300b00b2050b030703016100e0890b07814141e006a80240d012003411507a050020325210b042da6201195464070300e018a03075064940035a0000944081c0001c4c00d94010343c9074910030010003960180864200c0114200d002d40c0755144800b446000c0c0c00341d50001a40f1581040000c148085004410560b002c001c841c401011030464190b1503c401c5c0513982d00c2d005801c0140140318504154000f0000d682c0700b104000344138146901c4e600f04030305810280100150740041c2f040c001c42002148a039241c00e100320210700e11351500b0000460250200318002d5a049030400080c0380d680600d0071001c2c003086035410340e43d0394186c80c94140d00816107040175601 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 190678732 1250 190677482 190677493
    0x60b040f050c12070203120109060e0702031e1c0f0b1c1a1003150e07080d02060109050c0405151c0b01020606010804061b0c06111c050712021b 63
    0xc008049015080c001e41d0081112031810f403e80240078030b1608014061000e41c031041141d440907030051102c080c02090300002c0000c01c107041c00d515580e4690050108000c40d8014001180480040e00304c4a100da0741c2e04ca41d869599940c0c0055200c2c8410101c0566015881c02c13221409130740072500f03c103000c0d80c011500c0450f100741f00541121a80e00e6001c01814503400180240811074801400d1500402103101c50803406079241d413261301e000c02440110f10722944400b00d1400c0d41e502048407402500510002d01040c48444100075501c00052058801d5584c9420104440e102c81c6400c5034003070b001c003405a075442a50001c031050140c0c45442000440025081901d4098285104540c91600140c1c040c02150b110b2000460b440240a4001d036460b540e03039283d1500805c030710545da0030200714a407110103104000d800c107042180d070f00c0023951801d850204607091160500c50a902100007008000040980300c2c80000c0ba40c001460750300100d01880040c20300d42420320000c03a590b52540610440c0d8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 190679982 1250 190678732 190678751
    0x30114090622030e040906020d0911060307141b0303010f0e011a09010815100c0b0c030c1c0605131a0307080d050a0201090c0906060f030504031d03010f09060b04 71
    0x10b101202c2c1030a030100d100e03410500300c40041c3c41104500c6000d03400920201780580301d5102c04049a01040e4500d003996610403070142004044501301c11001000c48199003507140c000006003840d41103904030f400c0014001426068400c0080c054035842c9940005c0782d03280c0d0b03100d01480000740b416000e14610040108000194080018602c0d210070742c2101034242481054001520300d424007920f88202402d071105203010030b489824840d48080125610042e10a46a060080754024041d0064018500c200300b08424100b44404480d035920b0030311022101341484010340350003070200d9005640c0c4182c00b0b503180c20303081d411a041540e000901c0c603d091090034a01d0101640c2c0d41207072084c01000e130868407210121a0046018044541143c0004030f0307030003001c0d9a110640e80301600310b200800c4d51058180301c4168400700c1d000d0201203a040410280c1800c3d100030f41004a83e03180c8820602e0924900001503c0c01e400184103042d64480511603001145806009859580782e014029454141d902 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 190681232 1250 190679982 190680001
    0x20c042d0204061d0307030b072618070f0608040f0b01080a060f02030907170f070305010203100e1005060d060b0d0b040e0109030504120f02031204050406050a03210e0301140906 78
    0x4c41440d000a00401100e861907440da80e07007580003040b0384280501c0400d4100404844085400c03031400c44000c00c58103203030901c1c82007512004040e07000740f40d91040c0824042c040c0c5c004403110550b0300302c0c100a070b56984d031403501f50040701454800500d510021701c000a4111000241300001d20b201c1d0005008048801110008030302003218180d42c19801040d040040c0c1400c2d40510f001d02c010344080c2d131203910902e540305150065940c0f04460503940001005003a0300059404400752101da60361140505040340e90261412090240038405c0c0300019042030f10071001d42c45400105401050386455101d860b030103000805901014a014509086907143c00c2c2206101c2d4540b01540750319500e04243c100f1038441c1840c06280303802c07202181c00f41560310269400b0402c00d414507001d11031495641d4100710501045d5100f80d40104d016003c07100e010b100144403102000d141008031140c01c0d241c94000507046400c081c03030111941c0c0651130302c1051110703803010031082c5104172603c0080f03900507150340b14070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 190682482 1250 190681232 190681277
    0x4150e01030210030e03270604030b060f0906060a050a020312040b041a01060c03110a0803010b0409060e06010f050a030b150a18120b07050d11070209130201020c042d020406 76
    0x205c903004c0d001003014503006070005402001208455003040b112050f5180800c00c0c81d44250001d8520780c8402003000202d03c0c2c010114280c0f1501994003000d50705103100410700702e004842900c41405008114618200d10030000e80702043e40c404000c0c5490308003420300403122030041d2030583d1030041504815405200c0090346504803051580d4901c0040e419840c1290960400c0500e000c260041c4c5120343c0220f054000514081d0213031082d0f00760380f02c1ca00200c1d5030480d00d19900854900e0340802c204245680c0183c5040c000c810141484c56485408480880c024448810110b90110040d039100c40121802405480000025101c2d08100c0e4003d007003c00b64114680300f000701402c00030071074000255401c2a1507400800310b003000341c103145060f400e0405031040101101038120740401c1c402c0a601d045010540c0202000b03008910240e21900000d4882d10f8495489000d503480798a1040b2024070103901d05401080c000b44001a010b80442d0708010b5441446100001003071424078003c510400b03c030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 190683732 1250 190682482 190682501
    0x1180210020106080712170310170106060c0b0a18050c1201110910050c101b1b110d02030f0303060a060908030706050606042705010b040f120204150e0103021003 71
    0x6241c140d1410020300444503201e00200c45080000e0341f075214a0310150003a60041c0d001e20501902c60b8240304e9016120b02d01060382c0348807a030403c4020410340e50403c94014a403a0480e0f201545079540600c01c501800c0c0041805c0d20f80f481c4010010180300b0041350100d00c02d0b400300d8294802c01c45440c50ba41c240d60b0030811030540004100100a40392502c40b0034040304c585d21f41480c5042181c421640c0c1d04001090904c030340c106ea155040c200c04e15159051400c00382034141460b41800c070002d514644044901c14004080181c4564903410943c0c800e10301489003036008040b1210710401000c036903260b400c00d44406025540100000c554240204401ca0030703036040030300071800c1803503030f41f540c2c00902809400d00390001d000304404950b4981c0c0b1203c03018120a501c0c0441e030500c2d08071038958121074050340301060341c0c0818842444005982111441280d012000d1038981d04928000034000f0703c2200d01e1818006a042800500c0c882d0b04000d41c1c0c104c90007210707190141c90954500340c0c151440c0a4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 190684982 1250 190683732 190683749
    0xe091005190602100e1903111006081b13090c15020d050f071a0711060703110403020603090c0402072301090b070f090807060302120618040b0a0e01180210020106 71
    0x861000144c0c0c5107601914290380304000300d0340c0710300007030f5000e102d014580380341680015144500d0f8500c40302c00700401441900300c2501000300d03516105a25803104007040440030000700c40200b100326555541d404c102e9441d000082044040441d24180705035458a00c00c1141281040d1a40c00c000c40c00030800e0981c0425684520b498030000d0510302c1c045a2010030100c8240b040c40003030b100e031420402c0505101d80d201d601c401d80d100500800003881d025004040404141c101000221400d41d40342c19036084035410384000c1d03100c0d142e44c40a141006006c0c1c020741c0c0c1040c80441c241d018080412841400c511007140c1a000000002a100303003a43c07507039400500b0000440c0007096a00c1d103c0c44c0b4032182c0c00d41600e80406840e40b92004182048455440000083d8010407403480091004812030341100045407250120b41e4484004200e1510042001d0f110600420006091200c1608180b00c17284407540200552444108241240d030031090301070340181c2c807120180019500510030341c0c054030000d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 190686232 1250 190684982 190684993
    0xd140c060c03090f0d0309061b020c060703021219120c0c080c010f0504030e011404030c03030f1b0302030a1706090103080f071a071b0b0a020a0e091005190602 70
    0x1a0411940003502c4542e00b4421840f02d81380e0101d00703010b04d50354210f19540219074903100303003400e000f503501004030a00000c04103010001202e0700018211103421040d26a6a21012a410148d0400506004007440130000103207101c0e044803440b500080784c2502d43c40d0545405d4a480300c000031501d45110820204060019080125401c00d01408021041000200380c45112030804400d85009550450210300c40d104940c000750703040001d01000441c0c420710030341014650384442d0b00f01f5605120250a010b03003180c10404240c4903204c00304c2604084041e811039490203180003941e0342d0040042000044029400343c0c080b001c2d08100c03600409008218072244c0e404c58840701102e601c04104551391000c10082100001e42d40010084a41c42c1203030702604034580000090135404803020031215003840205880c00169070207983c507400c140e51010041c0c132540e200401362400c0503800070440e40564500d041020b40c600250008041da03906455440c0080109801408412000e018080c05a00134 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 190687482 1250 190686232 190686241
    0x1e0e0f060d02040b040c03091104090209180a020a030503030f010603020313030809010b0a140a0801090506070e01021002030906071e0903110d0204151e1203120f05090d140c06 77
    0x20402510350000304005a441c510200150845001c2d40c0e1b14404680c036100c52509010410b807040100d14025141402881c05540c0040e201010052040c021a4501c0c010b03880e0061003009038000c5684c0c0a4004200c2d5622410032598035001240c002800864400002c070342c140c407034003c0e80e024640c44441e410001106540a4901c045d005060303000b15941d900d03650070303141d40d581d001d10003e12443e041d00c3c44036000d000a20000ca40150005491a8182a81b120024900250707140d8045124030300219110f4603480102e00304843d1000708034803070780040b007407102c4010301240c41c0e40241100e8807620314120b1240c10705421000d09110440100e110108100f001c5407086444400d0410000d01c0c400f24083d07164001401c8071101d142e9203601c3c00300a28107000e403030201200c44c01a01c10000c01d2003c0c091070090024a081c0c800c01c0b0043c100408501e001580010a403c48044800800d90900c42c0f0710b0280749580c0d880e44441360381c0b0700280f074003140510a480c000c0c0440d112001c8490181826544 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 190688732 1250 190687482 190687489
    0x6040e07180504381e0c1b060a0f051b041e0e040b0a180309060e030304090608061f0e06042a020c0316030b0a0b03031b0102031b090a030209130203071e0e0f06 70
    0x700300e82089803160000302d035000e0380301800018450b082185000548845102c960b004890bc01000e9042519000e120712003207008890a0340c080b10710382d140780000d201c4100c0200740e1407911640030340b9944a0444c1030001304660841c02c0c0b4450980300108220702507071031807013182c104849000540030996000e07003030101600c03903801084d42c0c20010f821640b40c00d035960b0403502211003940c00544641c02c00c1e41440700c00c00d40c1020940d03503440c8400c0b00103134985c10250701024584001d80f400380720f0365540c1808015007504041910945084008100303150505140c00b9448030a0000c2c0103110b8020001c40c1405070280380c000d1002d5035003180c041c00080e615800940000d200550300a0ba05120501031089041c0c010488290070002040000d038a83c10b10b060b03199103945400000d00c3c00100280030010f2280c4880621104594045404945a403a100b02c0160905130300c0c04081d405025102c0081408107400d43c035100e1044490643c00c41c0d42d690391407941e0000d5030644201d1500b5072000042000c074907 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 190689982 1250 190688732 190688737
    0x4140c151e031009060515040b03070e06130303080c0a020c040b010203070503030103030906090b0405010518010909140603190515040206130e06040e07180504381e0c 73
    0x2400d6203100d00d100c1c0c10590714103410840d094401501001020302c0f0782c5006000c0e0100405017600c00c12000820b2403007a030f01c0c500843c0904c0c0007450001c000959028440c20080200207000b5100740d54440e403014009002a40c2804203078040f52220010848146050741101c002c3d04040d4003802c4001e00460400c40905a01801e1a04621051000c2004a08103000840c0290b00c80d0f11103a00300707483c000c40500356985d668400b0010032410f100420460340c209084900d161103680c000780041007020016a05d0789410b8002c101c1c1e10380f81c840c1d0800e0003c024070741c5071b0040608500702d62500300d03542c403000c49610080c1e40c000c240b608010800340011302c0c032140080c0c10510081a0609000100c41074005140d015808038510709000301c00e01c803079824144030f14244008050040c00c440c03400c1c03400d40c01003080c446a1034081c2d41c0d079030300000e01880f4660b180d0710400d01c000600c00c0c06480c0785011005050808054010001c403030000070401c2c165034600c0c08128200c600503490102d40e01d09100d00f003541c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 190691232 1250 190689982 190689997
    0x6030b0103060f1215061a0a09050a0b1804110c0703110d02060a080a0f1503020f031209240d060f0b030114010f030212090601180b0d020f12010207080304140c15 71
    0xd030301c4400105400d1040c6c0065401030220f40e44c4123807607191044000344146402e40c04140101d05004007403140da0082812189241c5540300804441c042d00c902280040000d801c103070903507000101341101d0608010681d90112401480ba050540d440706041200000c0d4140009611900401500c104140a0003400764400e120340e000082034080310a207442503c11801004801044411081c0110310300f0050100e1584c5040c0d0041022000c41e00c3c020281c3e100c2c0300000707071141e4505695a44003c842400c1101216a4001d86a0301d8203254480f4402414207030180404207401c0d0000403d881c01e0410603a0b048503910343d001c0080c1c00c00d09006450700c05582c1c20b4141019000c100302c4402c100046140d60164500714000c01d02036140a4a00e040404e400b4480712a660803c02100080d42e0b4a281041405030121100e18481e11804009200c0c120081d41902542d400031480805020380c0d94007541c81179015164496800260505260722100250411640040d040e09406c41903019500900b805 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 190692482 1250 190691232 190691273
    0x405040b0109030f080405090903030f04030e0f0a0e0f0702122203021e040b01030218060a0c050f0109050705040b18040606080f0a05010b04050103080706091b06030b0103060f12 78
    0x102d03612911900004491310b5403c0e2082c5000180030825400c01c120400d82c4100f00e200a1811350410000c0d003111160064005030800c03102c050403480a6644040e40900342600400c00c50a0503590240071480c10022603200c403882a019000445035800400c0b4500305180074080180342190361129200c041461800e4011780b00900c0401000584450201c21260010810043c0080080304200010349000b800c0d01030415005000d075020b4030a41d4a052181a0003c5610b59250800c040d070455484e02540001b800503c00d011040705d02d01010340c443c6040342e00403815110003907181e07410b12094884c14489160040440c070548800d0031760010740550080c0c841c0d800880c0403035540d0f840a15000b03c881581c01c064100074007078030400c030003482426240182a9028030640d0f00d1511581c00307a000d880406003446071203100c002d081184041d42d03d1803040054407080900d40e1a850000d0040440c50102c901092500b80080fa9940f503200c50030b03040720403419580400410507601e01c44144034040d00c04c00c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 190693732 1250 190692482 190692497
    0x15030117010b040c08060405010f1539050609071d040507030206040603230411090c070f0b010503060a06081009020604050402030f06031b1f020c1003020c0c060f0405040b01 76
    0xa81c1c0d030355028500c01c81c1005d64580700300d03061080c01c120841d841a800140960380301882007020900d0007140e24014802420110a60580d521011500c07080400266003105440c0705005903500160410b00300d035a018a0445005955a42100b60b42e8103240c000c13503820041110b0140441020000881c0c1c1c824490010343c2c2101e07540c0d0f03000c140d582c1c001d5001140460b40b00d042c20000e000d01f06441002424034010115054103190700c070304075183d00903001180a428250001009a0700302c00490301d205078483d00c80d4083c0381d04c41c184880341c05401e000d420301c04d0190304045541103085002d201c0a842d00503001c3c2410700801c040b1100203008042040340c10410500002a5903907551014501c580783c6a965007402d403811904060925803007000d07000401d4a203e440f1106511284580200030ba0380c0740104581442e0208164945603051499035880690008406142c95268001d40403a412400441d17100c40d04070010400e884c02440241442c2c5003040c0402c000c1460190449110128181005039 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 190694982 1250 190693732 190693751
    0x40b24030f010c180e041b030f03020c010807030e070e060d060e030c01110703020d050d0b03011b0e180a230103200a06050315120f07141503011701 65
    0x7410044000d00303421160b50f40751610b404480e080707070031208400450050544194108032405040620280c00030703042501c2e01d40d90340d83e0400303440d400030003440d000a540c8508800310300d0000d43e901006004a4005010007011400050090107100032aa14410240011608025035070507410300061a240c0d00070003400307455012400c00d21540c001c422041000d1940c8210544a95080d10641c80e02601d001a04000c4800429800700300442c50482c00d140107561182840c0c0c45070041d101c0758101d690f1651801d41020038464075141a94074800c0700f030f25540c0b00c0d07031180380422059580c0f10f0160003480c4d2152000422030500b45d03119099842030481c84807050101034004d4484881d098004560803c0c9100403130440c40400d10200e0f488110031283c0e40300d003a040290041c620f0001030540c2d603402d255062045116541c0e4940452124820070882e01001d800c09145540e65000b4070031241d00e004020b20400c684d040000c41440d8501d2010503542c0b950b468a9901d00c40740c8055a078180980d540e810918 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 190696232 1250 190694982 190694989
    0x90a1e0603050109050708150a020309030409060e070314160c0507031a0f09010b0604030206070f080a03060e060a05060304140a080d050f06100921080301121a040b24 73
    0x2442c0a01e0000503081c400e032401758500400341d00304602591100c0d203d11040e000030650a80e00c40c0e03002c1c4015031607803901d240c09455402071b03400451019003481004600b0756400155a032180720140c0e0103028010910809400004041d17038007004500d461b800716005070f402845155000e41c03144040ba11559503980720042d26804d19407044800c00c440d401403241901007580080c0d04182080e000b00301c000c0860001804134411751000902544c0007090b61000d02c1120078400c0c0034140c020a026940c1d41c0018001401031100b4040c2503c4504a1004154142070900b440b4082d01c0c000f810840c9035440c0c03503d0340c03100c00610b842c0d410490702c02d8003030080000d1507070702c05002da114050308045020706001049030340c2404010308050240502c00301000380c807540200502d0895240002021080703010080c0c0988500314960301034402100000001403034414014000400b50281800c0c00c07800c0102c1d400c2c0b40030f1810540f8003134030100c03036140480d0a20094060400e69004ea1040c0d90210035202c1010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 190697482 1250 190696232 190696241
    0x7050601080a05060a05071b0302010e011104180e061506040801020a03020702120c0109062303130303050606280302090d03080105030705120a060c0509060706020c01060f05090a1e 79
    0x15000d0b040a00c260702008070410599802c9810000c007807105140900004000ca01d0b051303203440a101c000c01c850f1081c14000e41c4070940e040544030091000320302c4040c41074520750282c4144045212102c070314001802040c8206000700707648a001c0d00c44c036200d030012100d019002c1004542d100c0410031000621160074401094290425180036844910500401580050000c2e503e5020342000140078404c0c0c0c2d220310358800750342c00381c101600c2c04450b0150100c40c00b008291005c4001d44000140451513006502c1c0f159214440d9409001070b581d40d0080c0b102c2030040c4143c48403e00d07403441b401c40070f4141c924480386513040d003480d0040c14080c4400014280b03180c0c5860a6020030010801840f25003002d00c40c88024010030350780d103a00e040c0c912005540c0c940981d0000380400340c1d24a9a401b07002d104030f0450300640d03001000e00741c50750b2460808400075030000300740038884c1d80380c500d0006050a5094102080361001002c2951a58030a1491000b07031403011250070030108082c03039001d502d0740c0900c40c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 190698732 1250 190697482 190697489
    0x901050d033903030b090a14040b0703150308030105030f030406020a080903010b1305191a040b0a0b12102301030e010f050c2a0c10020a0501050c120601090f060c0807050601 76
    0x40c04200c1d50121820b2182541d07010307000d1f41c02c2d9804e107031402510708401e40540340c02a80c092590b5504e0703510b07008224000c1180d20182449240008000018010040043e60503a40300702c0c1904e5681c0d40c03919030107560b80300b60301c580400350300b100802030041082c80b80584401d0f20090004580b8410380c0c0d000880600d81850180102551038003800920300740a41d408c2c1408803900c0c41085041582c1e00150724103075440d40c070980702e2a2102c03c81e010940342c09810800820580889640765620800c03050500f00301140e40f8940c14401e28230000b0344a24142a4420301d00303440440305070f1743c18540011009020542c00c121410340d210040c0300180c3e020b600c42c0a102c1c048034035440340c890200c000710b40b00300111700054161015043c0e9400c0d0007540003141005010703100710791010600254140c181c3c2454080a030141030b80d4030f04420050b58000d01c900401c080844d640e11030300180d07501401904d00800714000c1490075020316409201c001d004840d003407050f902613140b850402400781c0d50140740c243e00341c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 190699982 1250 190698732 190698737
    0x20307061404090c050a0f02070e0c09040f051618030807020402070813030602040f050312120601110a051b06070f0b090a140a021518010521090109020901050d033903 73
    0x910106e0007540440d042550501600c068aa40361510034101740d1140c0141180039030600c00509484d00d95180c0c3d02034002060030100500481c0740c14000b610b02c10484120030702c00310b14042d90600300d45800f24909016030341d1202e2810b040c20500c0d001e100007034004490840f8020010000c1030000400200390071300841c4035400160f51942003119005101c103d40d405039009501541209224403540001d540301c001404e20161015038a00004031500e05940403d03c030740740280c0c46000140440030a100715502c14120b07000206076072400c00d1007854807503d40044d041010790608200025000d80d51160440383c004111400c060362511075407404007440713854428940c0300d0b028540840c20590901d4001c89100041d0314145960341d54500890004030080034100403000a201401e1012081c2442d104200382e81d440c07519103441d200950080c400e00318181d12680c0500700005040c58211005404540e243c2d0b6032402c101c0c454080b42c1d04d07407071002d0103000c0314a410f80614904d42c442c0009450111f8002ea = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 190701232 1250 190699982 190699987
    0x91f0c0e030a050601061107080604021e09070810050117150f12010906110f0d0e01020d050109020705010b060a12150e0708070305070509010e0d30031503020307061404090c05 77
    0xc60040c003131521125481f51941c001c0c01080221000104e007141d4020740684020504051b0f012007c8000c40c88241e00703030b1b445241c00003800010f03903014251074031400803007200349141600d48005540c90120684140e411146070f100049110b600384d005840d042001400188140c4030038400514544510b010000e403c1e9910321401050050307500034030002551a1a40a16081c0b0300999092584201c2c2d0104200c551a02d4168101403c02d504030764900c41010410040c0303503164400704010354402e407000c1d10769600385000c800061800038200c6551394041d13214a80208407560152024100c0e102e202c2d0707203204940740b0001e540a00b1180f490303c10304403640e40d01307183c3c50729000140480720b000c1c0803207007080b0f01844402e40070b9030070200d80050b880040311511094a050b1170050400d03044000035141114202c420502d0640038260800c900100944041c01206400c201018103080f080c0300183d416441071b01304000c9180100086007441e141d40e40c01d5407416494142e0501654184140c960010740c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 190702482 1250 190701232 190701239
    0x120c1303060c0302120a050c090603100b04030f060507090608060f030307060e0d1403070512090a0218061003020c121e070b06100807080105090901091e020108091f0c0e030a050601 79
    0x17440010fa8810751600b410001e030300340311510800e60700400d0384aa01030b1078000003140700790035644101002400003829a079900c60300e900d8003004159110314121001414640071504060045c11440c05441e50f80d551400a603440504000f000400d031040943070140030030814140810000c0c0100c03a4400700d80002800d9140c0c140d4001403030032044481d000f031401c000f030040c04482a8004101c6400904007500140302d9110610403a05104440030025808014850f40348803a204030180701344280c0f0229404080711943c0c031010380aa01c00d0260f9001c0a42100d0014680c05050310090001040c0116140ca44e216509560b41501da10286003610002e0800080004c58a4015949000d48880e40390076640380c00d02e100064412903040c042d1902c0340032018006014160258401c618254002039141c00d484071aa010030781c20720101000341e00049a034000035106440004080d82404248204100f5580b031342c81d03040009080702c62024081051540740b00701c190354100800e01a5601071006403003203514 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 190703732 1250 190702482 190702507
    0x908030f012709061b02070305010e0304030302072c0108070f1203170c0c0a030503090d11030a0c0807060615020c0108090a0308060409060608030a020d0302120c1303060c0302 77
    0x10141e00201c124204864940c1c19038480c10303035018070740c00b007a074010840401c149480d10103408408401d4002d00102110543d500fa0b00146c10402c49004030002c10121482d220b04a4a0f841366010140260b070284000308419004079403070301c205985810010700c2950100c004010080d030282d000d2801e80d80031000c2402a0750a44141400500d29003000074400103141d0b030098641e102090034007101c1d0700c0000c0000c14041000c401c660414180c20140ca100203044d241c0036005070000c0d00e95107400c0c400d020305800d030703903000e0381c04441c4580705180114140211740c0e108035015011a403040311000e01c2030000c00005070306406200043e00902d07240320b20b4410028402482c00780d2040703050f410080b04005200ca004401300300061016094030b0140900d6644001080c046c002080000340300701d140410001d14280c0210150001160036401d460345018030120803810b0740202c01d01c0201e044940340104040e0007202c1c0007007030701c40b02d440002c1074110740e2511440119180d41000c00e01280e0001100140d440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 190704982 1250 190703732 190703761
    0x150a20040305240a020a09030212100509030306031f0608030d0509010c08041e0807050a0b0103020a1703040b0a0c200a08070810052203020a0606091406150409090803 73
    0x1140845903440d1283c01c09014441d050140c00840410f83c00182410340d5445a03071000c0207540c014008140110301c0b01002ca0362024241000d00d0b01e0342c5004041408054040103e034081c5000a00411007190302c981d450180ca0040d041c40e2264039079406001070b5100c1c0600c080c041782c907100c1d88001807070f142111083e0300b9224044500400c000c000d80811001a41880c40604110704c109580000100a8603108400340719810b0050810b2040c241031000700100319044506882c07003942c020154a980d50f0150005003041c003d0203007240c0041c00309000d0a20b900000d0419a002c500d4684500f0013181c54a0000e00080e099408140f0140350201c80d8500300182400001c100500082010a10740b00b41e9580b1415225983c0702d50949440120707400d0524403004200b1051f20414004150055280103541d640102c00201c48042c00d0420014480c0c1d400d00c521003000b180148410310554401040025031019107220441c8104188800700b065652440b54183d0130b842045400e0350b03801d01d05801005070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 190706232 1250 190704982 190705003
    0xf030314090a03080a14030a02130618030201030b06090402030a05060a0f441516023c0a020a0e010b0f0f070f1220150a20040305 57
    0x2200d08104a12241d194030102000312a00302c2d24254544c29481c004640751307148501d0400c015a0301005001c0b00011690062070075050900d81c820845595078000da840b0504980307030311a5207460080800265000303810202d2004401450f00745080c034071a00140c120b0f003050f2800d007001586c550800089082140409014140104a244440e0f1902e10041003024000031703100c05100401804103454140d0b808a582c020403400c01504120300c076015650346c1e030101c031440c80f48068442404252200ba080620a601d180182c2c068003880b600c00f0030f0841041d2080e401c00d006400d1126000004502e0024802500500c8030060913001515004110785660290490450a800000104003400084044030f458800c000b507100e4540226560b14050343c000d815020b0000c1c001c000e00e4500b040b070408d038501c910090320f8680c66565000e80b040707054483e02c100c40561480d44004035485003090504a42c80d401100588040351340c9442c40c041300c04074403c0e86025041403401241c21310822000b1b020701c0100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 190707482 1250 190706232 190706267
    0x10b10120b0916120b030d17010e01120609110a09060521070e090a0203010c030606030515061c0219021501060305270f01060f0510020604050d0e0a0e010f0303 70
    0x460a104010303a2800d4040d040b608107002030501051480442ca820040705d400380141583e60140031441c0c09420344940c0043c3d18a0840030100120b030000c440344070103042c0d80312000c090803050701e903030f440400400c4180710035500c2c0040f0404008841d610904900085c180103400410101e00e0300090015104269079a000c007030081d81e0040c8004c19000400ca0111841c5054111207910382090705402c104029002039019424484114200d540541000b0b084440702d6404008595489138031901c24044002060752004003009024028400b407800003540c032090b00710040c5008085d000c0c080c1004100b41400380507030441c001c0c0500d101102901c90f40145004c0c2024045840c01c140b41c04000004003c2005000004500310b8509200070410441c440c04880020404aa11000800f066540c10701ca440e202d100c000300064901440868958000c0354040014414020b0462064400100740141039030031980e00780c000161221100c0c030031802802c810401c02205425410024400104802e00449 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 190708732 1250 190707482 190707499
    0x12010b041109060901030c110a08090f030a050a03051305041b0f020a03020a03200f010504120504030804050405091903030b13090b06091009020a02074103010b10120b 73
    0x2c00e0316100201c0c0c0f06202c003443c0004070086900c0e0305440403c5135084451440c800c0092103820000000b000f854480e1084411024900c2c200d4205980c446403600000e0168000b0200075000034042d90240c1306206c034440113181c18980301c00101e0b0840301c1e0044030300c0312091689001c500c00d9402801c0340055110520103001d0809007918060350b1765000c981c00508112012301c010078500c070109400254000303c802030b1420507441106480c06001e060b07506480346220784c8007000e24503020780c00302d03400c90f58405983c9040610740170800000b484010021181c0e4010b403c4c400b60202070740702100040c070b40b007504d000940d800804103200c80312410400e07060b00c44e0720b05071041c400b00303540702c03662a0300290850300c0307001d6a0342c0c2a180701d41103103159102e064020300114000d82d015401281100c1a81d5002c0388106406d0752040241140240700400808404031410040c0c0746520358000b590f40003a0060008038402c5084000b10f04031426400840700050400962513241101500031348145090803564001c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 190709982 1250 190708732 190708747
    0x303240302060403030507020f0d031112130519080d09030c05040605060d050a0e010606020f010f05010b04150504030512040504140906150f0a0e040c060302030403090e060d0212010b0411 82
    0x2c2c03482c416804050180200030402c40b045544420001981c0040900800c4101c0e2076450081c0c896214245500418011181110000e40e000c0041c3ca82c5900d101c031650304070924000a200c4c08448106070044660403902011800e030301d0803c411200284aa030751a800d1605c0d5051160144056400031486281405001c0210b55108420368581c004010310028450b01c869489a0040210202e241200d508190703000a0702c80e0081101042c2d41d80e010001d0080c48100003191040311401d00070b59629403418081842030442d03a404c0041c10f000f00b03080c400c0c80d0644a440d42460001411300180c0c40750000102880340d400d06010b101e004d040342e0003940006040c2541e010fa16990010702040d0000305c00c0301c2005941c0e66254080d690814041c0491758403989071031000c800c807002110f0554038902c0450300001c205100b482124400ca4141d656081ca6600b06a0000c030008000390000d41e000c1f2001443c1000369440045040f00e0b10311307802c000952075484005000a866029080699041c002d11401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 190711232 1250 190709982 190709989
    0xc09090901020903030a2703060516180e040507080304120312200c0709020c0309040b0117010e04060f0f1e090305040510050408030a020a0b0f070f080c0c0a0303240302 74
    0x50300c1b0301a51b420201003c4944948040071500e0301032003070404a00c0040004180101684418007e010000e0111407001d04400203544403010b282c0c4880d0030602c5500c04020141c0807146054010780320310255001e0303e5503010114075540054002280709548203240340c04060308544c20300414200c4940500111022000c0492201201e0040340840d0b1000582608209000d0110700041c0031038180c11521142010303007107030340ca40004690900440c54103011108542c003480882c3e0a0881000c140c1e41030740c3c206184212404030280088034419140c02d08000c5150380d034014a840008103440c009108a4440b80d800689000124005000d070f15041c464130200358010200d41c150750054881032079849603a070007280d062046038088806800003150b000c01c11075000c550380c0030441c00b035940d44041e82c480700f880720304242e020358450303001c120940003050701f0743e003d1520141e006290080c06420842e0b145e00c100d0400044500440c002a510895a00d0110313054600c1c4450001c0410215059800d55010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 190712482 1250 190711232 190711237
    0x6030504110f0406090c020703020a090905100c02030403021203030a0c030209100e06070b0415051501050a030c03150b120a0606050a120633080c0301090c050903060c0909090102090303 81
    0x4160042d03000d01014402a1219041003005004400c0100315000080000035112501800101c0c071825a4180005604a0318090458096000320140c0918980b46000784010101016500e003540418080040540e0311101d03131444d032034070031006907503a4074008150008841302000c408050602c1801043e1075600ca85d000d845000405080020b50a0002400541603001d140c0d80104091a240308110800c1400c490f800c00314850402d06100648030350035203030b84013088410190700054060002c40140340c03080c0c211040b807111900300040ca80303068842c0041c2040c000d40015011480010704292041c5410300101d9101d2040d070810030001d403c0c0781c8014694072546d518002000001c0035003032200c10341a8000302c018001d9107082c10646440690442d50300c0d907518245620b6040180126807200d000e141d07500e1240200e0540c0c18078603824070140e0303001041c04030004810040148805440750314104080c1d401403044605c5280c03282d8410040044145000345002816401889000d078140c400006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 190713732 1250 190712482 190712513
    0x201060819030c1509030f08041502160f051e160302060307020f1c110d080103020411071704140a0f060807050c030d0501060210021204080c1f050601020706030504 72
    0x1c00c22034681e2504044030041c2d00501c020f00303544034020080b09038000c1a030107500782500c6500c52501e02c0c5184a81521508000c407005084c000003090341e10324102841d4018560244c10003100c5802000710f03140d9585001c03003094111800c0d40020500c0c0c170004861001c6800118440c001000c91848190f5240c144040303510000f40100404004034540900078085003480120050498045008281c88036851954844ca0840400c0d400c3c94802c80c0c0700004220011085180d403500fa50320307441c66007804001c0490000002e20441c050028000241003484034200ac1124003804130744690800c5408100c04030407480b014821040300108118110b94102644212009820f10f4262607a8101066500b44a41e003000900703400000340d005a402e0a40e07100c54182d030403d9084a01a6510045000c220310582140040c803082c4e0030b00284c00103008500803d19040d0321b4043c1c698500b0f0907800c110510400d4242c1e415030f9500e0b1420000c80d96410011000141070501d4103200600b01620782e60704e010110031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 190714982 1250 190713732 190713763
    0x150501140604082a1e041406101101020f040906050f03010507020a080c0106030c0902070c080c0307050909160e01030b0c120703050411090a06061112032710021902010608 75
    0x10311040e004e2001d14200918980240800340f501302d4001100d004008400c030b0a5201d0381c07400c2110f140010302c2e1078809100b80c10180c6440e04107541420141d45040b0410044021590200020789a8110510180006262000f07002c901d5604260800030041929100b15019a2412302003248156000030034204a0317030001d00665171160b0411003940034102581014140d010502c0c8001001000c0d91700911031903000e49000406261508103d64582c0e02024000f98560b0061034140814544962410780143d0f0070802c4444141c2c1c1c84030031026050440e40041018184e078401003060091740c3d1042d41d404188050a0781c40c01028221041c00b13018090200c00406607144001020801c2001e04905603080c0188000282d190821424029101c103002e10713070004185801070b003980000001c40012000c036a50200342141c1d1203001001703840351082d001c44040b242840400580f504103000d800031442d0024405130340d40a0340c0b4400e01b405001e422558086a140c010700308000c41011449008008000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 190716232 1250 190714982 190715023
    0xf0203040507030f110607081206010e0a05040c050d09050c1305040305030109021c0905062a070822080c010905061303030e221b0203030f13080715050114060408 71
    0x608140e041700f10702545081e0400301c00204002407001900141c20304080004150406990b0700c40111023003181c9450305074015411500a015519158002a554170b1a6240203800c258442c40000140d03201a03500703440c26004000140f6807070414409004421140c00ca00f8000c0c2d046c581e038000c080b80f105104610705c00764003068610413082801204132400b4410300b428003070001c1c18145a52602c106907a04824101155104180c000c101007801c052052083c1c0c02904280c401c1c0c41ea08016400342038008075014010401112003031424000078041e040c0800200080c7d4081d03000904418915046580708850500950540b04c81c44203024080e281d1520340b50120389840b02c00f0640c810302c100c0800d65134540c1201009815085580810640505d55171110350b0f0350304660041ea224402501c0140408840d07000080860745000d9551180c603100d04481440c00c0c96644038015007400c080b140307440b015202c0004101c145615007404c0389003907048600a05c0c00c1e02c0c00c405203035501d24128140c40703840e000b03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 190717482 1250 190716232 190716263
    0x9011725061713030e1201020714060703060605030f04050c030a030f0e0121090602090406031104050703020909010311010215070509030610050f01030f0204080304030b0412051e030a0e01110d0f020304050703 91
    0x8403c1b48044015030003009649590746450901d9040049081a1a4520510b40020b003220700c02d0190381d08403003050300d98900c3d54480c010600f0228000402c141c87c64400c84401c412151010030001405600076612031008042da00c000a000030fa841140c2810003c1c00700e9040c40c80310141407401c4402e007844400281300c05c4c0f2850203e000c5d000702181c0c668850300d05030000091080400c5100c412503000c0310704003e00d6541040c16412401500e00082e0000951001480062100418243d544805004554a8203660000303010105802c41e8400001000400c880c3d80b0742c1801c00041307400c0f44400751842c0f50507007020040f5080708554103030310b410103450303540748000c10780d0907070441c2c015180200a5035a12912402c10120001c0243d81c1150b800ba0195000307402c0303501c40c1c0181e40c140c0c0301d0955a404070a01e0340c0f0768031405403c080c0800c160b1a98512400c48116801d104610b4003002e1a20321940f20380d0444601c408803034250b15a488040e0040081000094000c200481643ea1203403070410324104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 190718732 1250 190717482 190717489
    0x1208090409061407050d050603031e03040c0e070e0915060a12150e1605091509011206090c0219081909090504230c09011725061713030e 60
    0x400b900c0c0f505120054418050110303800310007000001034145080c886616100141a0340f07110317040e400700401240341171a110500c0d54100035034026006100c4809516100d0034084008032080c1e0302030001c68240c601012841c2404109964450030105016881480100c041055441040140d504005998018a1001c0016030002040c103030041e0001d007203030351100500c0c04034034419290303811862106007030381031454441c008962200740098078001c800c403a500f41c500c00542000781e1044c10300041070183c00c1d007203505110380b100900940700e011484002240010b8144551440d03002840040d50040314046150002200c003040e08001c0140b207030103840601207403460b20707a822070903080d0300300410301081c050400b01e540c1d5081d40740704007580c1c80303d2014039203039451560301c203025044802d8070f004004820300f0340c0b0740c0e4125800c0c40040d07a001c40401c0c4c01d0a801c4101002d220140d0480401091010651240c25244242801c541200007070130201d100e024070841c541802010083d01302000c1e016901c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 190719982 1250 190718732 190718741
    0x1206050112051506180415050c040609031101090b07060911010311070209040c0b030703021804060510080403110d0507150204060c08072d060f061511030415050c0106120809040906 79
    0x140c2174400744495041030301d450006403030b52084520245007001e000c0303400400140102d81c1201c1c515203d58110b2851551000101d221401c07496050010060f0000b9001c011ba000625440b8810000054080701e1840c1c102d11a0710a207107158101403a1240d80b42d0400d0348402210400b58044440e103034140d441d40340240151034690003904800ca8003000b802103450b0140c02810302c50300c4103404404002e4034002880100d5041d44212a070224100c0c1c030044400b4052581190400c2c000e1501d0701241800707480c0c0a02d4040c0300c4d400c810006100180c0344c000e05c0400040e6407910308288030103516103031804400500d0f40c070b1508409002500002040e004104400403140c0c641011030580c44000051082c40d501402e07401e49068030014204500c88080740c4d42880780c401601c00c030036001503c3c00001c940441c1c81e5488070501d40503d1100700008504070200469000350601b06603500c65032922460800f03400e480c1e00d580b12070301e2556620811030004055105441800c0c005403400070f0650f12071f060460141 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 190721232 1250 190719982 190720009
    0xf1a070501140f09060601080408031302060a090905220b090a0204050115020c030a05250b19090b07030207090b0d300905090703090c0801061206050112051506 70
    0x40d031800e640d00326000007074020349224458060084030305a07108034490341c171580125013141c000350030305000600266019020b0f5810284403c182c90f000303030300365010407074590180c09841c0110b280708000b0440b41c1018000c890f480941c2031210200086171030742c0c06010303200ca510000c0101040000040268404004000c080c0c3d40003001804503503541d00072947c1e0301426240e158018055200c5069003800c0c0010f0b07a2003038603800002000441c184c110881c00e0030102c0006403104400b24040000c41405c801c0141c0256000305540401c00004848040d0202c03559a00c03018600c601486074001103500031500c042140c94004001c00e008010000140e42d08070b03184070007844a4510224242414441c00001c0314801600b00700403203c00243c0d1054441c8981d901c0f411342e0100c030450000344154480e0300100c0100c4e02c1071180320061500c610201e821b49000342c00030b06140d9602498241402803502802e4010f210350312141c0c540b500280c843310b80358080508101c51800c41100400c1e003681341e550303d801d401e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 190722482 1250 190721232 190721243
    0x3051c060e0a060e060a060305150402030405010b031e0705090601090305060a06030b0c04080a0f061e0b0a0b0a12150503010f020c0105070e0105040938010f02070f1a07 74
    0x640c1c6030340030810024016500b103031169207008004680d1001c2a48941d0055000038070400e102440c0c86011000b07450000c01000d90b0381a802e41d40840c42d2241d00103075000398071610020622000d00014545843d2280c01c03060341c00301d4010b506040079030010980c401a580f081c0c3c1c00c3c4480355130312030042c0c1e43c0782507691008001c2d214000070403022000c0c5502a01c1520303c984e804c41a581c58800351921540114062000c3d940c0001c0b90340717800a13040d80c8020348120b01c00c18021411882c0c80901700e0b07010103c68030317184200d52102c4948bc858549005014050810f00343c0b40c0d410b2083da0000144010b150031070310080c0581e20a40c0083c403844102c105801810000d0007444100b401602c100040e400c1514040c4456081074040340300c0c00d000300610042404180c1d0f8079420240381071158000350414022107010031140c00704a0300c41c04848804c08050064164003960303a480000c4c001031400101211450071034212440900869402000800c22102d500191400c02030980b0505041031040d040010079 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 190723732 1250 190722482 190722491
    0x7090b0a0804050d08061507020301091b0602060108060411092a07020108010b0408120304030521040221030a03020a140a0c0507080606010503040609030c02130218010203040305030703051c 83
    0x2049a4008030441c0b0980c07182058036115041d91a090b50602c00c00d44403168011024030310b00c9105074000c0e0262940724002400440c00c015607488071040408403890300d03200e61400c800d05004c0300b60108401401484500d004202500d4130f40c80d9121181070f4080d8452041c1c03c41c5011a00880342c400722070701152805100700c03090700c04403840c0307031003651004004170301050000000003a084407d000351011160060080c0210051384542480700e5800100101c0c240001441000e5503410340c041002c0030000080d007070b00b5890900d4010008000745c60032524180c5a01c48940080f14040401501e210310a581130150b11071518604c140d41c40a800e041e07211031188046680f00403140d001d50650021801030095070b4040d6114030034031341c4658049507120b0100da01003000c0780015406500900034280a132400340082c1031564000b1701d82c0d117100ca40030030b02c180e00072505600e032030403144c040f0251840c240000c51030185541d4482d80c0364002c000c00901800404280d2900c0810070101164076290300c1c200812 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 190724982 1250 190723732 190723747
    0xe0f04050a0f060816270204030302030301031a04230f010e030306010e0d03020a08250302010c020f0a0f060e0705090a0606030506040218151e030906150603010e07090b 74
    0x78001c00d40500301c10305050401c0d0f07001414007400716881c210310071410444840c4a0400c40856907029803070201c1c3c08080320403440301e0701103085403005e000911b1281c2d0103103a8a501d181400349454081070f0326200c440c0036042c18400011500c0c1c102012220741961900007466840044505003000482c0da42607550904418000c45038010005501c02c41090b292014110624000c1c071100b20710b20349000300980c0c4024000000301c0c0e06080640809d00e89050380e2a258503000301560f25103114028202c0150b07450345002e00480307405105c002d5115102d600101482c201540380c2e05921000200c0240071107507600072801040c841070004c03401400b000b50041c00e441c14403840007070041085100d1400000d1800c1d000c90342c546041d00071940100603496160007040220b0013003281e00c2041266907100c3c00c10401c40140241c01080f0303803605030000d800025860745811400e441c00e00c54010f2103540740340d40d5200c0ca9030150b600c072404c0e039055a5041050380079a0740c0b4001c041d18815141e410801c0c003000c003c00c144 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 190726232 1250 190724982 190725001
    0x30603030a0e0135090a0c180204031e03030605061306080405031b030a030f02040510050a0e090c04030c05300106030c0e0a0f0b130902061e03090d0216060e0f0405 72
    0x90340c0b8415020310442145c0da600a03043d00d40d02481300040070b28401c1c4404020b10400321001908030090368200610f019541e039606045804584920124440c07110780030b02c245609441843c3c0141402d490f954503040080748114041a914001c00060180300d01c0403a042c40b00070426500446030741d42d01513110303030700004034036550f604440d40d80d0002074200800410215020b00a890803a6400b81c401800c11442410603201500100030800400c42c0c0707071007801001e60701c84212a0086d01a07440301c4d07a580d421410400d201c50b040307400a90040c0680c044000d401070b0701000072814548602140c3c91225107050740b260140049910180c050600b1501c04a507035031509010300d014510007d020014015103454400566000009940d0310841e544414640c3c041e2070f820807803d2901c001c0140345049000694400c848102c2d828000c1c1540003c010000400800c021041e811010340c00100352103102500600d840d05001c2c040c09080080c06107040807540c0300c0c5101300c0c15545004105009a103031218a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 190727482 1250 190726232 190726307
    0x30f0e0607020f16030b012c010f090b010507080f0309070e0903030a050f09070501110f070801020c0106062c0103061d15011106010e0c070519020f0402030603030a0e01 74
    0x82d905940203909441c00441d451007002c1d002c80b584942c1d004590307232030b204028060903540c02c3c9000c9240000040440d2400c1d035200503034042c0c0340e903c0c25084050b06002c5000115100050703c541881800c002070030106142c02c040e16002414044e00329070701d54450301001d00704140c43c3d11110071440500c0a2141c07020000c0003442c070464100100300465520100708504c1c0072401e0b07502c012982c000900c1030010354400c5090310705410550f001c40ea1140d00e846a41460a1403030380c01810143d60110710035000b40390a000d55001081d49180c01c071100c00c04d5100c00404801c0c002d2000103909c0c1241c00b0702e0a1070340a600201d000380034104800c55121465030058443c03110844900100200d107094088281d802500c00d060403484e06c80051805a00304083c15012410240507069102e50174031017039001880c100204002010051441c48400c0418410702c203c00c48601d0039148114010300401a56440000648417070164901c0c0034003081282c0c2005840b84c50b05005804042c4c1c0250340d071049024124001d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 190728732 1250 190727482 190727503
    0x50312010e0c0f160203011b181e060e011403040f02040e030f0706020313020d0804090c030c050a03090c05120f12070309030b10051f02060901060302060a030f0e060702 74
    0xd040035240e40d0b0800c08030380b030f00ca440c000520821043c0321418420b990340520086280c17014000003030075072903101a0141c04000f01502000070380c400800703200c0e89065840b00e0303000b0320b0240042c00f9100e05400d148102c80711036004200800510340c000b515640c0c42068800c0c0b901c485007500c15941d0400303040c08440d00034070f4102680103070705081104071b000400008843c83e00c615075001a0501341c00b40d0301d460180d0b001502c010b8941112035002005692800c000b01d0049102c1c0107c01c0e80d0b5850003d101d402d4501e1800300d40103140c0f400b03500440484d0080102c1d2107903000c0b40307000178802005190071b403882002c54101d90703007110394442c0c80c4001d0a0001079000100144104582a011120260440c107100e08180140022900202040001c00c07842e00c1e250840b0000c17041502c000d45540c04241c24643c1c0300400c00c0c64280010404184903014000b040d04842520001c0c04014110b030003042880c85015410000c06944850710b9169900c10361080c1c24259030401620b903d41030145000350346590320b10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 190729982 1250 190728732 190728749
    0x181306050f060a3e060f130f0602041214010c0509010c150e0708010f090822090531050703170706020c070518090d0305060d050604030f02070503120f090105040305031201 75
    0x41d65a03d60900091040c0301c6d06070a0001189599042402c2505a5298808440c1400c81c03141c0a0002543c60001e840078003248003010910115a0a15103403208002c0314200f02070f413600b2007600400340c2c00011145862000e0070214140e845a00d000302483d1415800884028600603001400000100d090400c49400c80700900200c01c03414160000c54042c2c08004001200c02c2180c084c81a80d21903014005c0c6902c01c403041405651801101d040d2082120002245086030302d4001e501c4100000803c680004110f41d611508040c1c3e451582d16001d1303000240081e0440c1e0b4202c3c0d06084654102c035102e662200301035440703d1002000aa451080c0d02030280f080f0950008041e0450126903c10310945008005050402221005070014440500440e810005000324500441c40420025004620175501c10001010300000241016800e811031446904040241e0103820441c01c1070343c002401c1b115403159140d403c3e800694035841640e000500900000c11400c8068040d840140e04036071000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 190731232 1250 190729982 190730087
    0xd3c0807090503060105130603080304030507120c050c12120f030109050708040f08130f0e100e070c030e0f090103030216090902011409010306030503181306050f060a 73
    0x20020703140012503005240e0154080301c01040689042d40e211204486051000601180c981e10356902076401194107901160b0f0010310002080199404c0409110740e0303203841440b0400e81c0c0d66203501c1e80c3ca40c1c44058400e1040202030003101d28140043c0742000c40c6288290b644051141c080810f40d002440303482c140c0392070a00003501c0140201112440b496001241c1d0300c1c0351740b2564a030f030026000700c2c0341000c1d0001c0b21000490465108080c02000c1c0005211000061410b42010122504250048031000d9409401d01c001c00f900800107403043c07035040c00e003d4400c83c0070001007040d80701c51070308030341e40640600000000d058000c103e0810440e0756a00000d0b00c00e854120f01e0054800e280c000a0001c0d100e10b902e202c00241a901400241005140110303a680eaa038a40314034507040004100c05040103a424403849240c08801100803c0c0c01080500c4190b14140001c2c4080c0d24581c2628002d0000082814800380308400e007a41030302407600007440306d0080b90001140405480202140700010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 190732482 1250 190731232 190731241
    0x3050604050601020604230303011205010509070b0412031110050106080115140a0c020301090302010b041a0d12021221090f070626010803091903050d3c08 68
    0x18014148142c038181c00400a50701d075139803844500c00c0391075201020003840c840c10b1844051305000450080c01000e0483e16481c0050a0040c2160741c040c1c000090707548640c80402a100c3c0d0481640d080722850600710450000908095643c1801600004001d00900060310a024490f034002d50590b02ca0b03a40726412030780ca0304d1078100c0302030308003980030702043c10325941c00181110140140318800c000e207031060028401398046400d4400700380c41100540d440741c0e080348085c10a4400c2e10142c003a920710380070030107121001041401218880180061302d030fa000ba1181140200640d404000c5108940fa80d100d1803442031005000d9400940c010082a480101d4034480d800195a00420040130241140b20301c0c00c0701c19a400703e05101002e044000c18806046055999035116000780007440185a41c2d0580008100342c140040e05a0140455400d8051010820010b4005410b61081c00c00a0304c44048201c50407075442e28020b41502190032007499402c4049113185e14000e080103883c2c61005881c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 190733732 1250 190732482 190732489
    0xb04091d03030c031003050a0b0108011b0e0402070204110c0d0905010804080328140f010609030b0106120b040c030e010e0304080d0c02150c0307110604060c060902040e0d0c0201030506 81
    0xc1039030942040c0d1081c404540e41c4a1841c0003960000f0006089101840d0340342d0f191410184281000d442d440c11620040007912000e010707541495803000400b41444040000152000340341c141e00314001c581c0402d04004549655020003004250080169120850f00021a43d2000380c43d40d143d002032445400007800d9402a48050b0050740e200158600f980d40720700050a1b11100c60b80c0316002a0121a510307601c0b007000307200f0080440800301c0812064900f24080000201c01a4001020001090f0f0100086003500345e41d00d064030315618004010b0040c0c1c80300c802c09030010002d01c60b4040c1c03a103c0c107101c080c1d416500c940b4243d04008000d009a08128100640f00d019910580c140764000d0683c004180b031142c0c102010701c600c02440307100c415a040128060a0300a8045245e42d5800014241c09010307587c40031403000c400440e81a49481c1c1010b100409800e09000f00600c3d09440300710640440d40c603a000b00320380c0c400081c2200c116042c281401030100311684030683c00302c1e241c01c0c0811030a08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 190734982 1250 190733732 190733771
    0xb0102060c03150a0306020c1e0a12050f070c060302180d0809130e030307170c1903020d18060506040f050402030c10110d20030306130b18010b0409 65
    0x21038404076030459441e1009004194200000c1c1c66020302e01c0c0e40040700152443c03015001c010718010040c003840340318115150700b180721005030f825162301071000700b40000c3c40749007010034141c0145840f0340c0b01d26010701038113014040d840b8018280d0076602030104120764943d01a00300c02c1c0005000003400d06080c4180250200b4410015040c050204107600403801e143d00f608500b500142c1c400030781e00f102e01c2140c0b41590010346800000610002c9540340c0b600901c02519040740400c1400c914080c0883c899040611409110b4400d164001ca07a240d80384429034800c850000f0100c100c6161044603203020001481c0c101c03034281c4118034001003070441410600c280c900c900d5000c0e0090415801900c1004466900460701004004210b1090403d0403414048280a038801c0c1d2101c1c02c040e5562180039580d1807032400b07000780c25842401004002c1c0d49601882d41c2c2c8045e88107000584c823405034003040d85001c16140030f403c00c0703001100000b4030b81390070320040c400c403044c0c0740c4208034010056000501d840c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 190736232 1250 190734982 190734991
    0xc080601120510030f05011d0f030a0c02060d0c0e03060a11040909080f120103021e1c080c030c030904060b0f030a0b060d0603050a03030f0c05040b0c0f0f100b010206 73
    0x5101d4510000c0c40d8016036110341c0e00040e2800040c070115070389aa90300d8550100303080442c2e0f2a5140e40c2e1140c0c4c9a048400414008850000500701780f05a095525a5a00403809401c0c00c110707803c3c88060a5445502c100d40103020624010b12951900c10f070b001c0c25940060005a0191103190300142406003248510360550380720180041c580341c580410070001d4204108280d0340b507841000300c2c001118043d0300070201002020903455542d803450040085012041d401000c3c261542c80c4840155680c04940d10f009003000d041260010b030031820320000c28045d803a00d841242c40005409564600e00001528035280d04442c00c1c8640c50b1a2078014085000f40300288170f00032818008075a00b03114640050781c1100307003d00308c3c5040484500c01c18003a101076500541e140e8000d044400c092660500907080200e03400d0b0024071141840d51401403403071040c1d00c1081c4411202082080c08a2004d2010391108045902104c80714800c00d07003079a171a40e2207620406001031801e0b800840e10350000c0703003180c4074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 190737482 1250 190736232 190736237
    0x31202011b08090a080f040b0c0f0c220c1e020f0f0a230c0a0b03010501120c090b28050c0714091303050d0915060605090f0439030c080601 61
    0x100c0c445980316030300380d000300d1206046c0f02030500000c50040c1c0203c000d41304450000e0020285000c000c120305003010900780080740146940d030440c5d015420360b101e03228502c0240c1100003541c91070b40641100c60101d0506524110000d002402c400075a0010f00d8004110f940700035a40049240759955541c0c84560350000c009403040b0340d104152060031341c0c1480600e007050042d51114113040c0300049031140c45400200012002200500c419680008820071011009200300301c548565080a4021507a0303229000022a00141c1d080200c618980d8406100a2a005e09614440c1032503025040c2d42040c00c0003020781c0b08e2040001180400d1944800d503140002c1c1007a081d989030201d00303203090306809030250306001c01005400c003c880c59101c2d0410181c020304203c00119110351451060351b0441c1c0c8198104001846050b08554030351480406a180490b8001103c054660504010490941e510450350244280d44a040d0045500c0303901111002d90701086070b4007030408103540d40c400a4980600 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 190738732 1250 190737482 190737493
    0x3191d0429011706040b01170106030c120e152802040305010e071a1b061501020c01030c0e090402041b0c06140106020c130b040f0204170d050315010306031202011b0809 74
    0x1007178240b035413120186280615084000c028441d0000b05411820b0f4040350000b84d82d15542e03070781c1c580d2044001d0840c8100e0401031004401c1c100310f803170381c070244100d404cd000194200450180784c146007075a40c08600384022103502d860300920704002504144415100c550820218103c05480895120140c84880c107011000d0502c006040f11a50072001440b010081d40c4c24151072001820001684190b07158060250354007101c0000908003c10720030760078140346c24603482000d00c5801002100458200f560342d248266507500000d005000810004180300304090f00824042d41d10a6490365207034094603040c8442207a10180090b0780100740700340310068001042e65045850405a941c030780b600343c0c5101082200000b40014104c1d452180b1070010716034005010020401007900f2024851034080240c08054400f950251040c80300410b80d81010011084c3c44000d030f8002d500a03400340d500200c00340400064550068020a80d40f41003c00076003c240444a10603c611011481401e051000d0030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 190739982 1250 190738732 190738741
    0x90804060c03050909011e05191208090d0b100b07020105030103030518191706070c12050f07030804140703050c060a030b0603090106061103191d04290117 68
    0xea081e01880c00480c00c00204105240880d40e450040c607001e004006581c216001610b400e680811965034401c900903049802d005521907140003480041b14010b80a450350b00c54289803002c16442002400c0768400306080f41e030018400d0004c0c259115415074500c9005194440038003032214050301100900040c0200b005200081c81000071302084440710b140c402c40036800d50001400d1400c6610042020b00c0c3c00f080c100004a0340311141d00000403814007800e00e9080001c070080c0700700704541015000341018004140c0c998403e00171112010614422241c0381c000e07915000b0603003032040da4281c4038400d10701d11510200d940480c3c0801102c0c0e000004090f100b01100c20301c0403a801c185c1044003816620654209140c84200045210f03c40f501c000160031820144013812002a4040101d03040d0301c1401001d425060f86000542030f0a841d09100315034891900c2e64050345499102426007250620140080401c140c410301c80b02084000d00c400d1506448000441e1040d880f8051103640c95105000305 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 190741232 1250 190739982 190739987
    0x5071401030e0d08060f010e09010e1b04060503011d07080708090a06021801082406070611160c090207030806040902010e100f030c0504060807080a1d011e09080406 72
    0x4048141040c100414016402c0302c2c090305204408a000c008550710804105e09482c00d1050301c9814603090a12200c071034a0100071681e903407414040d01c40d0010282e404243c0ca0038028440001c040700c0740c0e2a0355580e64884d500201030744c20a210307000c15046032005040c200f04103414543c0c03113001c82e9030740d090566032108403c417005000501580010b020310310851000c03601900060410b003194082100c0e0f002c100800040000d40018804200e030342c1c4041140c10020000d0315840d442c2035085a500342c4544040c2001001441381000d40320100d000016200c690404030b000c44170529001c0c4d5801c98903c0e1740c4d01c6441040c1c0c807640c1001000114440006111407030950710034883c881c01854a02e8092010102241e040e0100c11002b0002ca0981c0000240752640b50144040c0200300346802820300d071030100d02500c5a00040c12010920100500080302074107164004290b109400549080440e25000020b0007806002078003240540728800460f51513000d07010304100795600c046140d20701443c05804 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 190742482 1250 190741232 190741259
    0x80306220e03040e0604020c031905090d140d05030702030a0c050a0602040308030411060703050703080601020f03030a06061101060b160314070c14040504030906030914070305070f0b070507 83
    0x1008140d5800c00c5011110340400e2044007110300080d03000b540d489040c020b50040504c00144820712441c010040030340f2808000c0203440c8031b4089500d00c00d0700908844000c1e510360003500c0c00d258020301224002014450034001890310010341406561050621800880d41c52008131090320150388104002e075241c41c4600da1140485008809489900c4880d642d200d06aa001d43e006551300d00021060000b80403103a000d042010904403005890140155000761050145141c081c0600c40c00c2e00000785541d0007071040c1e4001e4080710041e81e90740d01d4220b01042c0140654040d0800159118000da100c1ca00c0501c2164180c9410800140c14405181c1140202c0e040f0584120704211940c51008a2090a9400381003240e10a41c10744081c02e0420004590b42e00e0180d100910950500f414800800d80241d50380303081e0754507840c020560940500309440b030200356070780520f568400d450000040c010080b80d40b000740c41c0100c0000002c00d80c0c400107452640075804002e020381d0070401e0200442d6102614 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 190743732 1250 190742482 190742509
    0x40513060c0c031d01050f0a05090a0906080a06050c07050f01020c010b0108010e13080f0703090e0a0203040b0103082b090506010b03040c090c0e0402131e0e1812040306061809080306 80
    0x1080c900c2c0c041030f4124294160005c9240401040d408145c840180c2f424056100c09050380307030800c200c51450b120196546065440c40078101659400124000a041c0b004840259400034102c0313001042d0000400d0003540610390407005546000c120f400c03650300c200c010310304803542d0303400866441e00c40d000140030004281d21b04840807842000100c01c04400800900041c90280c0c946501d56440c1148030000c0b11001016142c882c1e2040081000051445000c6415250041040c6495003070000c3e00030310280526805142c500b00c003000e12000900303940c201031030051160050710314507680c901c100d22507800203450080094141070014090f080311a840844c0c1c1e0850fa240c1500c420641d030000c035040381e1102c2180034060805207410f00034600c1c0d10465294165290a00000092625a13025003084000d481510309180c1000076906001d0304024003400c030590f2446c80c6a490303070703246040c800078561071046044000d05d905812140d0000303480744240302030b008420903103555210403c11101030356a04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 190744982 1250 190743732 190743737
    0xa05060415060e01031a09041209050604030f0c08060105010507080a0e06030c070c15051204080f03160221071113051005120705060a0c0602040302040513060c0c031d01 74
    0x302001c0310554040d1804018038141d01c030ba60700f0300659000103080d55004041404039004283d50201140ca5650030a81d22070340111210006030b1000500701d070341e40340541c031083c2e00c024040b50210601440031000107206104000500b101d540c0c4100c9180c54410911885000c07540a0241c503010a00c07001c002d0684180a10b068031794980701100203030300c0f50425224450740340c0d4041164030030410051141d40180c544550040000002c40c003004003544607410a41c144800142c01050030001c2d90b200751168a60f1030050a40c43c0d02c4c1a25082208181000312000144a0142450450305a0404000f24560013001e098945187c0e520348145881702084c0c255044200b80940f440c85860740d04c10036018031400305400c20361074581401c0086e140c032000324403d01c50b0807020082000b581e4035002c0754454561801d0686000200c0d0030030344002d009987c0069007007405c03c810441400c500c05a8920b026204030010410000c505000b20f030040340c2070f04018089030300c0741403d41156181403240d41c1101c0301403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 190746232 1250 190744982 190744991
    0x3021b0c3102070308180a02150a020304080d021c0801031707030203121801150b0d05060324040b0c0705060103080c101803080106020a080f18060a120f0b090a050604 73
    0x506100803a440f100060300054029010310800d500c50315040c80d075039a0707404005c2c5078040b0340d034000442d50a8040c1c010380241100207645804a0f0090058800500100c4181d4100d040004006034403a10f081411125400404441008440c00340100e0b43c160780d0400e08045044610b00101019540308034029001d6100501c8001d043c280d11091070740c8203c0c4011400704004110310402401d58a0b0b41084450b03176500e11100f401880716607801d49601a024410201d41a00c07540c01180c240301a4003000c502d480c081c2c180c0b08d0f40840b004030005015074030944403a60203555415541c0904d0080c010002c0c540e40100e00104007284002001d0140d0078221005c0c1c410113616040c0e00400c540618000c2d103a0b01402c054001e080c56042070340c4e035005044034005400c251084d41d481c00c04a209040040300074a00114201000141000e0b003140e910340083d003801c3c1d4614580da005081c40d1410520307642c103941000c40c00342c1201a01e000788640114082c00844094030384a002074042c06004202c2604140d95 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 190747482 1250 190746232 190746319
    0x2b06020f040816080705040204030201120f0905060405030301060810030807060f0209120f0705030f06011e15120b030f0a061a21060901150b0a02010609060603021b0c 73
    0xf07124403044140d152911880003441c000340107041244070b9003c6442948180410000740c0d80040b501c0e040e001c0c58201c001102e51181c4525801403000ca10090002e10451082004000300000298140d92141d00c9241c0d081c3e5440286c500f291320240401403400005112620005103a60801000c64042e4507000d03041241810104046020418140210350310407a45030340b81000510451001c0c2506501404070568992070300e03540c480040c850400c0740d00024885a84400820701c068000c1c000e1484c00c0b88111051900060801403004000d0503060300d0010340c107502d4500090a1202040303a44054035260030b507a10340310000c7c4507007603500040f031030b0700341d4861515641d01e04410813020000d40748415600c6c0980b81d581c60813800404c0c01011307a141c10002d44582c048803540100700c0b6180000e0030351b1483c0300c110032070150086a200104843c1054008605140c00d500545a002c0c101d1416043d001c11401e165075a56400b9043d15030001d01d1005901e0b1803101395010140400461040429600308 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 190748732 1250 190747482 190747499
    0x1315050406081b22050a0f03080f0c060a0212090d2106030501090609031b1e020d02041a0112230c04081f05090d0f0302030a15080604022b06020f04 65
    0x100d00918413150355010144150300007030131440c50140c0703400d464454040e410441032202e8008140000b900e08480804c0020030100c8040840342038100c0442582c1e200d0900030501c401035008200307400496000381001071294003000a05928800544e6901c2a918000140e1180300c0420388194444140d1a410080040f0300240265a58240b041c58005500038290600501d0b11032056201c11601020400e4000070405c03a061420f082203e9020000e4102070034400900c0d5a2a0424025005030900c041c3d141c0a100701c0600c00982c910a80752840d00d40000700c03e210807158015503245000d06003000d0340461080103015a071340b095903003202030300e0b1a45441c030040c50845045002d1010045100c0100707140c0c9540d008694000038550010001e0280b2500f0207007801c586c184c030030410158080700040c1080c0d820740190329032014a5481ca510651a1803c0741e440e141c0407181a405000e540d0340803030301901c4841441c050b07456040e242d4450b00425a4655001e5801681074030139024050202180144 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 190749982 1250 190748732 190748737
    0x30e03121201060206060a03030212030705091c0c09140f270714010c0503090d0224041401080603060411031606020609010b1f081e010b1315050406081b 67
    0x7080c8041c1c181585010360081c5810801440f10307014906c591420000203800085915984000d04001c2c0e450b50380b0000119000c0c02039039901f56100080102c1e04542c03081049501aa80c0e0142026460154450b00c085080c2c40501401201c0c980410000501c2c04181c0292a60031090811201c40444900003036940d545010f102d207220180c120030760800250041800b003100700e030f6083c01d1451040300c490700c43c3da8483c02480e088038011040da0441100b1503a0b00070485c19000040d81c070005c1c86216040000100d6002402500581c0050009080302e5601440229104080c000d0042c0303540d51702c5503501d480780e098410b009600340c403d0306419032000c0c0106605801400166004029916000e480c07982950400c0701483d000e0601d2400c10034401c0303181204a00381901c603007444903840c1c44400700800c5124215402514941c0c3c400004a2a030310300300010411540c0f60034248451584861000300c07280d049000f540b01080b000c020401c038850007044d9003640804030201008a40700d43d0701c005c1d6501e5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 190751232 1250 190749982 190749997
    0x180204021c0507021204090e0a080c0a0c0914060d06020f030a0e060a060806180a060203040303060f0806010b070f1415010510020c030d030b031c03050f09010e0a030e0312 75
    0x340038030761003080d007480d521456601121038401000c82030060901403006100741d005504040380c8420f4150708103801002040c030f038035074030580d800d40e00c07444c401c002c03506d034016490121081e010b15800010300e07940c1d03400340c9100e02d00080001401600c074107081180c030346075041041344d040d0307000d210390700e400452140074501c6645229004102d4881c940c0442e030034020003d0852002a01e4002d0501130301000059203540301001d4800c1104070302001103060302d00090007d0080c41e0900000c1040b04140d4150464412120000308a202087e200e00702640c940409001c0d2118460061003a500424081c5800500b1782e0302526a05100e5111407800b40c0c00c01603a40300821180480c01c004111601b05100205901e00e42ca00c054400f41039401c000940301d0580a20384070805484920080c1190b409000340c1d402e010095989510100b02d4410250181c0070446e5400301d464640d40015400303040c1070140071040d60350740f0301810f919000780e039007528400d440419403030301403060141a080440a400007040755 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 190752482 1250 190751232 190751257
    0x406050105090f0702070302040c0c0606090e06010f120b0c0c0102120f1501091502010e1915052a0d0207060504020a050301060305060721020f070512090f0418020402 73
    0x503605160078442d5140000e844000c001644a0030448201e50108407401525411200071688045540c82183c0381ea000e2800a8030b85c3d45414400a240b0000c1e0380040c25202400d401c1d45c21030783c0c0e55012586442c0c9984110386841c00c88202810000b421811007d5020080ba90500d09000180d01c030a400c90300602c0e1340f918854001014030640c140c41c5400300d80d22030200c1603255004141400001c06000301841180418403059007a036030302d14002e4010003d42d500200c100d03103212001d10704c03080c0540b58281054542203007009180c074003001c0a0141c01d01c181e0180240340c807520704403580d02c9207650043e050442d0103c0305101440c202940e038001800721901908c1c0100307060074240104103a241c0d0a5000a01c26854404200005038000c584942d20010324100240c0740c10240350241d241c80007076440b603280d061002030891a00708449002d040c80501403c216a9500790030340c500902d504c41c0960060b031003001103a4004491801e41c0201651984065642e800040c6030360209050303802c03172a0250310 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 190753732 1250 190752482 190752491
    0x2130b0703020c04020408030708030406110c1c0503100e04030201091202151006210204050409150c020106180209010e151c06030f0b060f10051308070803040510170406 74
    0x103240d03041001120041c0f0842d000c41c98146022500ea5691080c1e41008082400200020b018003903107901c00e072a1010450f28032a80c8082440d5261b03250b5412030041003400303c03501500d4880521038010b0300d201d078100c050880c2c20541800c85980491100130012400c540d250880803001400e065241910303030003036400500d4405003503800d2009604e0020140451701020302e02c10441540c0c880c19072800790404030594000d020007c00c59401a20450300b1130380e002402c1030100800c202107620200b002c0542924200030f1580c4c034000880c203840361031241e800c52040c080340140a4040c00e40c020181200141002d035181c69811700400c06191100c0c0d0074004030340d000b145224948044c03d044600c0314584d0b0504200090941e83d504086030007141d0050042c8488600190490316410024014090018120b203118850030400400c0ea6100307025240320b82c2c1d903000c1c00003000500000c148007030b5001074003d0350405042500344003803640102d6107242040301107611a0380740c00b4a205d8143c0200e00840000c41d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 190754982 1250 190753732 190753747
    0xd20120d0f0902090609100e010803071a090a11010201060f081b03030301031e080d0e0f0d0c21031104090c080c0f0d0b12150109180b180102130b 64
    0x302241c480c0607403000c00c00e0601c40c0c2580180c0d95844500c1d480350701111b056500342ca42c00c00d0712500b640180c10200f050403c1d8000840c015100001030b10840d4455809030032940321801c0300b880741c10401c0c0d504210703981c081d01c803880001e01340c04110b080345c007818400080c0d03c5a41e40d074442110600760b4080007242d0009414000b1b10191b16110000c80d40307054000354035552450b69046549100e00b0305000c0010485e001050400c400c0341e00300e0300421484002400703141d50f000d02c2e0319210306a00980c0c403c03510441c101c0303990090180207252102e90300701014850444a8a94105607018811384450800d40d5034403180365052207050262020344800d120000c5c45240360007010b0100c5901410032104201d082c8107191404000e6811103541e000382c0c0c51b003c51a08644d0011401c03904810060305804d02580d24042031034051181124101e0360741c102c0902c00f0a0862140500740b00e00c2e940c0240640307226600045100619042540340500ca0700c000624001640b020251380d21102d0300021115100000c01d00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 190756232 1250 190754982 190755007
    0x3090d2108160903030f030e0718020a0809010c0906030506060405090c12010b090a060309020a0b030c0c10020f030708040f050a1202010b0907120b0105070204050f190e0d2012 77
    0x101c2d505515400c0500d406801e6481c0a403206040360b81c0340381095201c4192035031904051000500812a003a100b40629041108250194011a4040d400035145000151080c01c0500521070344401c551100301c071003410503104501500c0d006208580008042000041c50780b55004043c0c45409010500c0d030311140e980010850f0558181d000c514000414400294942d90b40c2c0e69040c1180c60b035040020b42d212a52000c18103540007070b880b188040d1710110070014154080760081ca0f0028403d0b066607411400602404128040d000008040c14400d00005407060f000380039141d0428041e00140c0700c0c159460b9901450031890a9048a070282400c0002c0089602401842000c3c0c0b42154147c400b03240a0500505800380d80440d000919140c410240450b406041200e044079000b8005102602d4075011440c01c5507404c1d541110a004801e07a510601d02c507900c90412030740d081101910301c0d00e800c3c030012507070701c2000800d11055081020070b03100344003030401c10720050411211005032141c0201101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 190757482 1250 190756232 190756261
    0x10c150c081302210114070e1201050c04050609031c030c030606020a0201080412030b030109120e0303030708150105040b13030203190b01031b080f15061203090d2108 73
    0x102c0d0b500d40d6491071800041c0d8440d0707402c03501d58560080108a090301203c003103015115000c804440884100c05000c4200c0d4402040094a03405407046145a0401caa00344d007207480440b0680503003642132106000d01e2810400425164400400705c4030449808200c403083c4013842e162141c003183d60746061001c07164060003054000d0181c3d001030b001005143c3c0001e0202c510043c80100b803140b003102c076101e4050184e401009103a01c00303030081051405624080c034804680100c080c001c50002d0310507090615001085074030070007207a996a41191209070384882c46024035041d03241800801e00c40403401c082410003a1030039100501c6d41c0012185140103241c18628500e132030141c484404900c400100d0110b1700442d045950040c03a0454030150103103020b1421003150008901030080c1d044d840d4160000152100c0969600140c05020751070351820441c000945008406a40d00309005120291800d0040500352a024a02c55140c081c3c441e0b48600b441c0d1890070540000c500f00b00203000c003108181c0c41 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 190758732 1250 190757482 190757491
    0x9110c120d14011503090309260f0303010b070332030a06090204060c08090d08032409060f191a040812070203030304140a020301090c050f100504060e010c150c08 71
    0x210031555060501302110500b00d14860130a25031203e0385401003601c1004c07004010302060030103444281030000040451001d0017014900c07845984007040641c0b0300031084034101ca820801191800409a40990b03000401e9842175050503840b500710010040c1042404601255040ca100e45e2485c10103060400c90700d10303401241c0d950344103000900c2055080040c000e0b005803c42040c6031200c0c840ea00140f400410035100400c00c003004014050b0404950700d82c0003c145080030201528118007050008204040380d09c50f60000500030f6440907400c0040d40003a0740d5000c05803402d54035880e80c1000000704150032940d44500c8000408004043c810300604c68018112032002e842c04940c2d80000782d403400080d1002d89560b000191804110008000e8011030b02d80c050300070b00a808086c244007542ca1000d1245a000302600f0485405900c1c0c401042d241c840c50a0711400e04142c2041400c448050084a0340350502c01d416642e000440c1c143c2d2002c03c1454500d100200b0b41d1290b4490052441c0760241 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 190759982 1250 190758732 190758761
    0xf020703150c031d120f1303080702011218020103020f160c06090501030b1e180709090b0108040f140102210105040c081302100e180603061f09110c120d 67
    0x700c0c104e0080901003100c00320852a41c803400d80300c000262148200f4407818100c0d14000000c0c0b48000100002000a030501a0007600c804811040c1c0084460a41d90b070301c550600d007440e80d40c030349000560003a80604001d140000c5580e0420400031089100c2009000080d80d0540307807100700f08a00c07a4812004005030900380380500a418118004c11001021403200101d208803503900000030361200f0000f615801c4c5007444403641070030b00390b40140a0004038054000b15a040508082d41075000d03a81c4075001d16132007203c401d803401c8651500b4500e1104d0700d654650554080201e0700c10941d00060321425541031200c94141940341004110440320010f4035034003400700300420021050714901070120302c590161151411111000c104803032000c440503810f80d10000d444003400c02e001759034174070905c110f40940489003503031200c20080740d400c00c652a108460703041200d8113004043c0e2580008032040c0c4501e10060400000700384940c20b200714003002404103200410605000012030080707200261070b88 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 190761232 1250 190759982 190760021
    0x903090f17060c0705030c07060905130e0c120c03240109060b07080310051c03020f03270303090a0b0c010f02160f030e0307121401050708070f020703150c03 69
    0x21074080342c503041e0050164080820204519040c400700344200c402e4602608151500342d5203030f10303000c1c20301082d502403e4082c4031201280403442c9190304c113402c9140c010310001e141b402d0181c410000a02051041c40d021402084503003012505d04000403000c981e000c80e42905000441c00600880701c805a00c00e040c00b0f402c0045c20809078880c20101c03624640c00180c50340d680e688808604041440343d1740080c1d00030002e001200450b090080c1c0b002500c0740b081e0300b5910420f0700030340c880ea5a800f6203164044070032174885020080c10007a0b00b0040d00030502605032820702c60307240300081100c03680340e0040650340c10001e110281d0601c00e1003a2884900c6109085007407116250135aa0301a4016200410030b0080754105410315010310030b40862401c0c010200e178040c1f0b48a9042110107540702130b003290341e501c0c3c0c2048814070341c5e01801060b20400d0a951500c0c001d5031110310031907601e00801d2080c400d5001d071007008004a01040032084100c0054030b03002c00c12091210f4001c0448080c070003558019441c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 190762482 1250 190761232 190761269
    0xa05010e06070503161407030e0f0103050105010e2103030f01030b0f0108030307030c0c021203190e0904061d01060e01060e0619030f0f05090106260606040c05040305010903090f 78
    0xc40c050325003194192400610240c0c40c05d005840040001c1c4455031000c0c00880c4107010150b1042442281580a486c3d00021104034030043d8281c1700203004050107c1d00b0002d840030103050802c5842e481d80064891040c40070b50a4206500319071040c1c600ca2100d8200100510600504c1d40c00a07410948045041100c3c0d0b2600d1215502d901010f000c580400d61150f21842c04d6601c0b4559082c1c0045c1c00602460400350403079001c0e80d072540142d8038660080c5607079200b41e42440c001d800e80c504500018044031115503c50342c40b072009041c503262040c02d900d00000e00d114101c10034401c640141a101d02c2c0b2081135410550064414480002074071301c6080104075808500b01c6910380b0311104461410701080800076001c090002d4404982d00040b030529000821141c0e20b030541005045516021880700d9100303490041401001034240b000941c0e51003100821140d09142c0c2c002000d50585181c07060406d501d03552200d083d2400e440c0c090300087c41810381440648040c1c803040000301030f20600f03c50140c82 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 190763732 1250 190762482 190762487
    0x1a10050a0503061009031509050c01020a0f06020c011d070305060112020105071101140c03120106020106030515130b0903180a050a0302120a06020f03190b0f062a0a05010e0607 77
    0xb0090240c1e01407161100c00c10b60b010b000e489a8806590300c105500001001e2004400c0201480078040d00e4511441144500c107500200c2c0c100e028a070030524280040c906500c03600044e41c0b02503618101503684604c40649000d044521805640780d00000e00920307455810f01d98500135068010400302140c1156180c0183e03000300450f82915804560b50400c101c191005031840000310326400c00301c10b8002010300f40c0560200c010849561054100d90f00780c0d0300c42900700e00300c52043c003005040b940b010041d0441c2d8949500031680c0410b501ea046000c0340040c0c0d556101c41c01c8d080c0d031445042d0703001161800b1884900d4011507100070003501c01040c00c51604000407402802444041d00445441c00c0988461206000c050a140e40200d0190348d01d00c1c2c010310680280e401100c0a403400c5405d06819860031429002d54189540700600115880b10801c0c01c114460740030b480b0040d9036605142103844641d9004548421341c600d004007501d60341f085410700c1401e454503412000d0079a00207004001a464 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 190764982 1250 190763732 190763737
    0x1407080f0706080702070e1501021507030c020f07050a17070305190506060d0b060f060906070b060a0b19050a1101050a0506041103011a09132f0910030e0a061a10050a05 74
    0x140030900c420123005030010703030812030704464103c0300500150400c5900d982542242a0310581642194091003070700215903100c06050184503840a40d0000c06c0200e0750719001c1c0b1000c00c4401a041d100324603a65035580c1d02d01800035036a208803030854018442482014040583d010205079031044050380035544510003040c00804152144c01204800e0b0700e80d0b240d400c01c0e1051800040c1c80c180d596411400c04a59004003210030b40e2042e5613a45002c201d8007400e03015100c000d00305400813000d040e03003004251000d4201501d02d004020b0402072101e0030080900449000da0410303c80006c280c2040024071003900c3c22012815843c003003c00041241c40c0200100700050003a0b241c0c1207440b60381080000348001d0031240703155001414240100316083e00f4a0083c0080000544130051506091040400501444050030b5029500c0b4600408040c029049007081d60402410364200c1203040d5540000c487c1000911261440d0b16100410a0b061012412000c02c209003010790900f40d40900050031403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 190766232 1250 190764982 190764991
    0x30b010c03050313080309010509010509030705030405040504082b11040e0c0706020403050717011506020a02010807091a1305090c0304082101170d0f05071407080f0706080702070e 79
    0x1280c004000744181ca0a0b0581c400d10f85c0e03202c03600c00e0b601c1c1030440340f060103080c094801c1c40003035280a0215030082ca00008035102940c0c0140a9802d251411003008020f04d00148240c6610404006030803144528600a100c60461402d940c2405420100c0c038504845119618006800b0100028000c0100c1440307120f90014481c2c43c207582c0d45080c0c1c0380c4400039000307070f43c001042c07442905404038003e40400c1c81420040000b1008128010040181b40d0101e070f00f0744165400740c0c2004003c000036501c1008c2081c6e00c882141480a640c1d903a0301d1600790031001d40303007881001c8200480c840003400042c0302444001d0001f02c5030030410303041c1781608810602c4040c100900710940000c40349039a400310040c0d0b20b070441c0280300c1d41e601503039034070702040e6103d00c2440001942e01500b480044514040e60608441524568038182082c00c15134034a050034424110b80b0320369129444000488807403c000c80c141003401380307024120f01498940d0203011158040c0c180c60954005010500c0424100611039030b02 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 190767482 1250 190766232 190766237
    0x7140a210c060e0109081c050601030216020d0201020c19030b0c030c16062301181a01110708160f06030b0906010c030c12091d01140906011107031b06030b010c03 71
    0x3c100c00468080e00503c0003c4005024000c0400e42826800f0110040701c0f0200c40c4000911066565071b00440807842900220707011031030708211400c0541400c1e03c88006561040c011140d4080ba0440001e8590591130303506503084201d0103091013044005841c9036000032008a2083c15410111302560440c040e4961103400c0000454000e01402102d0300048001c60300d51403102d82c10403442802070040d043c00d0140f0a5107845205014403240e20a00c0740302d000d40d80d207034442140d071074000c0e00446044542440d10a040e00c1400760110388070505004003041103074041d421107071661800c004040b85030070740d510030b80602d0300e0304000102d1600c038101110381c032000920342010b081819103810f480300360b0b80500203001a410200c2008100d07802c0304c40d800a40d81401400e650482d5400c0d0300c4c580844090041c20951851099031410703a01741882d003582c100a050412400410b102c1c80c40c14500078442d4011b0300c08216803400c4030880311400f0705c0000601600d1800703100101702800060315452107030000604 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 190768732 1250 190767482 190767491
    0x80102250f06090302011415030c0103020f040803030903040302030d052502011e020a020102010e0a051207290a15080c01110c130b04060b120f040807140a210c06 71
    0x400003080482090030b58031070b10401416005080c02402042c0d0074402d00d43c011401d0b404242e070084000d038034442951000740200740c4d4007000d07001100a174024180740506004203002c0800e0b075680500186208096403002076031640d2550041518250300300c1d1018082c041d04000c4038250144421204490b4944c020032000f00f185c0c80e2004944c10744a1107404600365800751110341265501080c60000d05000f6402440003011001c03c01381c541d815200010a941d02c055000381c119010f401c0039141d803e01820701030942404030400034041c0d050003110302c001d201814081119152162150304110758041c403d5407103590810000550712640c0c1203010f810311905143c24091000c04203e1440c00381d4018005034480d24245500e140030300310444a0f0380c800d504010000c074006a4000640b0316180c0780c40d03001041c58039500303060503078104040c00c00c2d100130504000c81c00204212044104041c04044028800c80080b400d10b03a094407d40702c4044582c44440841c804c010fa841140c9181c074a401800028 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 190769982 1250 190768732 190768807
    0x6040c0e060d0902030a0b091c020304150c0c0512030d0e0303011d1005120304030302071a041502030d020412110f1f092c0f06011e051e0a0306080102 66
    0x6e217080d103a610000c02800311201046030343c042c045030072441c950401c3c0c19001a404050000e0b0380301d0241d1b01030300e481240807059000f503d601c54102441903d019050000b1415160b01c0800c800501040e28681c071030f4030006444440003194420801050b08031000b46044d5410048058151006140a084492490300210780c030080524440b6000740001044100c0342480200d4040d22a00548000e4025024213400024a000e95641c002000f40307442e4121454281041003190075905807140c802d0444c4011b1200c0c1031841e01620080000d03003001f800c40b503c02070240c90305259481e4bc504200d4058800350103010515200c4c01088128107010160307141c45a0700d441307021904140e655114030305021070080c014a207440c1088884010207488410490250b6401106001004040d10042c0c0092698a04294980b801d81403000c9400c81c1403620350f02d42240c004a20350305402400010b5192107001510301c4010b80c0501c600c00041807030030020344c10081c2c0681c82040304418428040e00c0300000050030f6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 190771232 1250 190769982 190769989
    0x403030903120c020c0112050f271603020a080102070528150207030e12030a1218061d121c11030a050603060105010c020607060c0e060703030506040c0e060d0902 71
    0x421282c06035004022403030000300000d6030b90758003c03800c0380815001d04a28100d040d1901400d44204e904002ca804181c036103005100001c2a01441050010050780c4d03030f420594828000c403008200b41c80e0380808400d0030b500401c114a540c560295620387e10401c400340008102050b44080f1640418615240d0350625040c42c804186a01c4000c100c443c8507008564042c010b64050300c0c0840c065500c1000501c0a10b01b07205101e40408154030003540103104101800d8429815041f03225030302800400c0c4684580c61101c43c6010700401107440715140e80420703082d0541e01d00d6030041026560002c0c0240b461503887c8010a21520b598888004d1608141d005c0340713091a0401800ca0f42d50f180703d281c0c0c0b45400044440100000d981a902c24000c83e40002071940c451002582c410345c00038100c030700d091400c0e62104002d001c980341040c180101201c10b44a0365540202602641e4080d88010038103240c071004002c21201841c080707030240b000d101034481580c0c40f2181510b48840c69060001006c01c01030000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 190772482 1250 190771232 190771247
    0x91a0409020a080106060201090c140a090c030902150a0f0203040f120813030813091e0207030207081c0201060b0a05040501050c0109020405250807050a0c08040b040609050306070f080403030903 85
    0x444030f80c0d030912034002202e513815400303d80e0040c02201003902503031b1a80212076410700d401c03111715807000c160311041c812403443c0d9000705400307080c50400050300c0311250301041320f0f003528000034000c942011414a0b02e954009071342c0c114000300303440034501e02424207041340d411070300c0381c0901d6041d0845071600b40208242d03003048403801d03166242c940c1413855032031405900c1948030007400c145800c103042000400900600074605060ba0128121008903100c80504d402908903000c190708511641d8070000c0d40002c240200c0b5560100d40c1c00a00d810020020060b081d24030581c0030340b01f0900c0421000311030030760110035107050318000d1034029a1800c03008041c030302402c82e080001c2d51080c904030602c40c0c1200021402c01a20b41d44000421b5044401101524203130750031503486003c1041003101400040c400c1c224943d520b44030b04642820a92a10fa01880c5038000d504664041034164405009a140400c406640b1620718580481c1901d268100204406400790001741455295100c81040bd40075414 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 190773732 1250 190772482 190772489
    0x106050a021f0605030d140a0309110d080a1805090412021018030f08060d0605061507080408071203091e090207120305220f020607141501091a0409020a 67
    0xc09400b0540280b810500801c0248540d0f40300e0300c685041c02880302d0007038000d40c6d4980c105080d00da06180f146c0c00103070007a1007100300440341511500c0041074560303581b251a074070240c003409855890303040210014008004031100003002a89003c4104101e42c0d9650390540d200740d00810842508242040c02d9260014444020010f5400d11550182b0742d00c180302c031103007114080e82c0c1d504d0005501020075206a0410b4400c15000b11000b5404030100c1e515801041d0042c1000d001d03408074804040301d0240035000300b0001c4440c208006130800204000300319140150500480b00d400507a01c5980107050600c41d4415009840100030024034081484000d181c000c00300900b01399507441c41854000241124074000401092404010844c520b102d0302c1511441c907014034007020441e50b9500d401c4103020b4070640807a0710081c02c104100025040c040d8501c0713000c40e240014502d0000400d005000300d80b058104694403490641c0180c2c81c0004e000b00d0796101581650002180c01e40e90020800e0000240c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 190774982 1250 190773732 190773763
    0xa03020f041d240c03060d240f02030603070510120c030902060412050d0201061a030c0417060a180c031e02101d030109030503041b09152103080106050a02 68
    0x81c1440062050503056111203c2d01d50510103240c0d0318082e11382c00e076000c00d0704e807540c000c0c600c541d10600240e06844401c0c0c0040445110306015040d1403202001c1c2c0ea00e81e800e500e182900071007400340e01c0c1400c21440e0080c00003159040c01c5091074100041c061007101c0502e2032000c4e1500c00002d07900e4041d5100410090300035211945d0b40341c650b40c0044a07045400412529440b8650700288075030710602c598400ea454a90300c401c05940241c4804e00385420150404102440c100000610b040c4101c004031035100c00080034007094640005148112240c00240000181d0021401c0d000540341c003d0788410740c2d5101074149642101100074810700340130810003e40040d1f910222070812034000c188900c1c55141e00c003600c20354089180a1509856412100402240f01030010400040c11040316038078106410b41c009100c00d941e890480292050300740c0d109195045242c0c05e0201801c2c18071052409a12a02000d8513200503a400420384201442601c1c104100030170303100700c07461083c044a0880100034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 190776232 1250 190774982 190774993
    0x4060b0904060c0f020a030504090f0209030f07061202070206091e12010f06080a02060307030c120c090302090703050907090b03030c0601030515011d060f1305040609060b0a03020f041d 81
    0x10b1a02900814032400d6800c08200ba03100c040e52118070010344484101d606954090406142c000084080c2c44001c2000d02001e8090140d4103158404000040b507080b0311800820846251600c05030102e2a00e01000c0c01c40e44c010005a405a26014121400030170259403516180c0800340da0858103000304c1e4031803584010b0506410103a064150004414800300384810020180e861000503a00c22106100a40229042c8005240d0703d010b0352040c26941c00320700303003042c0d01442210200704803031080e284c110100740804001c2c01541021010981d00071000d0030104403509040c3c0c18180e40300014450310034095214155a0b059480600555902414030b0003250819612803034840e44901c071031403c20000c0120000001340c440c0a0a2465000200c1c11045100d25203602c001e00003603130000c40d02260040e18000c5080c00b1a5624810740d8070580c040c4800091035050340c03030088252600001e100744a6514174030b00b40056951300c120004900011580020b40900d03e00f1084000d0f6101188454140200b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 190777482 1250 190776232 190776241
    0x601270504060506030c01030e15090a08040e04150605010c060b060d020c01061d04021807090510080f06010201110f090a05090106120e0a03090b1e0a02030a110d0e0904060b09 77
    0x550000d0f8011034044060301c2c41b0070203000045085804800c0b1035941c0ea406852604000c40c1e51400042c0c0000040c02520381420640d1181d121551141c0d000140144103081000705210514603000e2560001940074050245402c0008107012041400500301303903620125a002a514081180c2c5082d07401c80702552244500b00318a4001c000c03504c80c582c02203000c4030501208803004c908181c0310b268006d24403034601000d0010000d01c0e0340700501140c18011700c07036400700b810795694007180b0180b686542c03900210700d070039520155030300b0000d0a85030640e81130041c002c13240b08141d41a514111074059071151200404030028210600507440750b50031400c040d001040c810340c4280401e400001e1010280030490350b032082d042e5200f66080c40500041c4144805100c0d2450a60040042e42969000c6030010303404034076007080c1c1d540200000720141e4800a100c2001a80052030078156520410160004c600b4000019080b42d03540c47e0078910030035065000504003c502d0f81b169035000805801c0c44040d00c0c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 190778732 1250 190777482 190777493
    0x170c07051c030806090103081204080405090c04030203150f070e0103092913080702060307050d0e0601080f06041e05071206060e161715090f01060f0906020601270504 73
    0x8003070704180c0003e451140010a141092507107503040320741c0007208616000080000c3c11103000c02500450703040e0070400c00003440f81d5407020018018040700c0c11003a9100d00e0743c4101898070b00300c40c540760100d810800c100a030b00d800c2512810b6202c1414103090f2100070403600102c00820003000f000304500c0301c481c1504454001d5000311a0f42409996140d40e16840d005403001c000f00804000400c001010045c402c014149000510380040d8642007081c00c0c200f940941d0300a41745900100c50701c0d64012001085156403c10141101f070b404c003000340900e4201900e540710010201c4c80c1d6440401001d03144a000c1110400140300145050004904034002e5437800c00040c1046100d0390f1520030103c80031843c880780301c2c178240c45052002c0c1c0310001d841c010104082c00c0d2501c002c14401e4107012144504600c6c0d22000d4050f4841d4046a243c08442d40c18000c0240c00100400003240c20012520300520074030b41c0000d4140d0544043c8102100340488000840744034909010340d8010940c2048240000c101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 190779982 1250 190778732 190778779
    0x30203030f0301060f02210d061809120302070c05100917060106021c0e0409060605030316150608060403121508010c0f030b1018050306180d0309170c0705 68
    0x41d031945c0c580d41da03c944a5000c90b500c85c22910b25a0513025284040081041414014092032044600c0030441c0713a03803001590300c10100942c182c01d01a0311903400d54108040f20340d4130038448155080840c10a540d5444030441c0b05843d004141c052404014203245180c0034507002d000034010f1403244641005041421601c4500c203100700c0b0090700c19042114a40b41c0002c2e102c0c070441c0ca00341d44400382d80d5518000c20025040000c408c1d5007181d0b80c3d48010856440c280f00909941030742c0d14482c41d05120500e8881c1d45034080c83c0503507008a140c1642401901340105145403c945c241c80d090f01183c10340404880203201001902585079002c9100240c4142c040d0402d520f0003855840c2c1e420b14203103035030b8207a050398040c0c0c500d00e5004441c903921040f80c0f8020400b04015108440d1001510340c0ca031008a07141c040160740100d00c5c004540010030504900308544420f40381d09107000e000324403542d556800ea9490b1404900641c8d240401c0c0180b000740d0420000c0024540103084030040c00306580e1440290 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 190781232 1250 190779982 190779989
    0x8040e07020f0c010e060f0901110706090609050f0a0b0c1609062402060a110c070b04290403020d03030b220e01050906010308130f0323150c13030203030f0301 70
    0x1805a51010038a9602400b0342c41c2c840309018100c14504020f5007121480c0b0340c8400c10441c12b00c03058906000300c58004210807800f4042d1503d88000b41c6003814800340020115074421446200300083c0f580da00c1e02c80d81402021207510380202a00e400c00c1840f07a60030701c07103250188840702c12041c8002807508401d400c0001181c190a02c2a4912242005440c9400c07103940100c002581c8850302141e1686080c0c0d02981d00d0744c2c0e0f00d01a040c1003035044500141842150750103200304400114007803114600c40b070194070324014800300e0340c001000074002c240d103103024500c8080d00c0f5140380e00d420300604d4026007103c0c1c0c410320001c00000800c0a0b1514006140104518914085160024100140405110326805418000e00034003046c0e10b140d07034659030340c0d001d00c0171105c411078000400101100350303003018400f6610038011075110300119690b0300386035116408941c00e207502c04440018901c1818420607009a84908481e650300440d1f0880284001d1030740c00203415100026842e040220103a016505030b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 190782482 1250 190781232 190781263
    0x71d01050901091b1805031506040e07120b0709092c0c0a0e0c070b01080604260313050102040f08030702030715080708040c1505071101050f07020d08040e0702 70
    0x1c60b40c81d01c10a00443c3c1e01d900d600ca18142031110300e4200180141e4080924016002400072095140c0011030b00b400d8600c2c02d0090a0580802400200d1601d4054032481007d0701c2c0042c4806803805001d00160700f03498002500c08200c0c2ea010a10702441001c0d11005012652800e01880046520340700002e101c182400b10b00d0074a400e0400c07552200800d4807082e00034024141d80f1002c3c00c01181071100403024051580641c07040041c9070003e440c074044203000300001800f501c20b0f1b2030903040204028036176140d8003040c00652068225071056030300640760080104020200e291610380b40c01c900a10071a041084282c02e04c900001c1c2120000000b003000500c00c0d020307101007a42d030b000d0426140803242900070101d66110001854144244283c503030141c011103a41c03002c2c2c2c0d41d800d498135a40101408850002d140000c130311050005184010f03600d05404e103402c5142600300440c0c42490702031004000e2080c3c014801e81c000380a8600203603000b034010459080b10600301950040d40d112a65040c00c0c3d031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 190783732 1250 190782482 190782499
    0xc03030c030a090c0605091e060406080a02071b0e060d03170a060f270902030a02270705070614010501050a0c0302030903060a090b1302060d020a030e07090c021626071d0105 76
    0x1006200501d04007003a40c8040e10271400c19007020750948020400404807011145e0a0044401040382c1c050009200f03041d424041612904241c4038a04c0514014106d0307004051122011002036484000d8078041104009081a9070311007a00304030103410f60750f11000d0540803000004c2189190b55207000c0d41c1101080144030740900412929041d00d003114000703541908038144080140c00c009107028048141e11140510a4500f00c8400e52080c0080e2144800950082010004c0101e144200585c1203060b40305c600007580f400b80001d0241c414582d00d4000c200000300c141d81054000c0003603445000c0000c0a032922032a019481d03400508001000743c0e044109000840c51003040e24240788005d03900503200302e2401080350b074040c0103540240142000c0560b2401d218a11813000c0c40102c001c0e0007400310118100c185032400900c6d000e080f801c4071403402010b100c02c00072a8035041420400051102111200c0d040d41d004180c1011201d502000b00c140f001000c0341030301c50200c5891170507144100c600b102e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 190784982 1250 190783732 190783759
    0x5030106030f06030506041e121d0f300f010506190f091109060c01050907091802040507050909151009030f0209040c0801020f0306040b0102030c03030c030a090c060509 74
    0xb0250344061001400d00d41290000c540440c03800c440e5240303800040140340e05550300c43e9a980844204510a401c0042c1c450610441c41805030042c0c0d204006e03089030031081b0b140a0710005400c04005941540403090b4420f001482e50000d42c00202e0900840310645120100c0c446419001e8081112840e215010440510711840184001001035480b56004801000e0400f05484014840c100064002c05014054001c1c03955070310005280701c3c40035900205031418400641c61500000d50040c0441c00c0c10a100c841c09004402c00c40018070341c040700d020417640c54640003610709120350400d040d00030507a08108001d2840d6100c10b07006942d01030f20441140e5480c0b003011074001b406400010200d84c56000b1900144c030380700107000d421030f0142c001103080135038ad40e40c0309089a0001c965054801000700400129290611407418000000c3c000340d0b03e0550064801a12844000c0041c7e200d800e01101144004400d81d0145445603440403c4140050b110040030b84103800444601788542c0443e00c60a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 190786232 1250 190784982 190785011
    0x3021003020301080d030f180501091103060912030a0b030607080f01080c0609040b1206072309030606060c0f030a080405100603020a05060c12040f06020f030c0309150d09030503010603 81
    0x9030f04a0302d01101a0000e1012410f00328040c3c4074803110a4100c9071900009213808400004500c0010310582c00001d41e00800d00d40b0796008140140030b90b10a820840c10403548040124078241d4502c0c10b00202a44d9a42e4031007880010f0a40410700d83c0c15114a404018000c5d0700310015034050060017042e07400b00e070b13610075043d41c1c0c070621488540d4020f0801d010241c4207080139003202d07100240c005d1504a0b9200300100030b40c40d00c00704030784030340004621500f044011142580315071044518808001c2c1341441c000040b030ba403440d025100501134900020480300c44002442020a0301404500383c96842c000c8400003022001d0a540903186400346c9040c100901d8890b220710030480e540038250801d05840c080411416402148102c00c00c1c1c054110005080d903207000082003d008a040c1c422030080c03c01000a10b08640c0c1540440d076a4020005030351a0311000040e201000d0301100e50b07400300780f940300480c90203004002000304007034106010001010b4100000d07606844040d0740c02c000803e40b20041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 190787482 1250 190786232 190786237
    0xc0507210903150f0e030417030702240f12072c060d020c030c0109031103030f04020402070201110313080c01020a081803030913020d0f051e0a240302100302 69
    0x8000410748200080000403280e9502010242c40302d20001810381e00d608000c02540c41d0216020003036080007900b40703d600192542800214544030085007444d0b0603902059001000c0340308a10030b03850024409100c05c0d19003048a01c5405000202da0315030720016694541c01c0c00940380d42001c51030803407a0607000010280d2032240141201200d0192800f6102480060750010014401150f003c00807401500750070002424010f0005000080340c5e032450030024540032b440900c0485c2a0400c03c10b1088183d40c10118030380103601101c0041c2e0301d01c010f1005036446d02032002d03041928000800e00d2440001c010049004582500f0150382162484a00498a80d0200080200500030034451000451020080b100d14400040c044a1800c01c00c10700241d160030051480c030182d00d030009085200003d642c01180801062542d040c040350418403001040050424280310782c0b80700323500000d0703c043c000f03400074281d2400308000c605080d0140c50301c545142d12107000a9000390106d00b60b0030b003020f209208 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 190788732 1250 190787482 190787543
    0x90e0403050d0b060c010603030905120f03030103060b040605090721020c030f1e04080a0c060804030e190504050903070506010b0c15040311060109022203120e01120c0507 75
    0x1e03042e141400030490b2500518008035a141c124500340907003029507009204200243d4041d445284200b4941000c10110100e0383c0380d0b846080d00001e0880c140c07044008203036410340f0342c4160081098130504002c10002c0c86907900c01580585d00e8418441c0168005205050b00c3c40c4000e90514041e03000c1d0704820980c0f04040a050f6142e00401801c4401442e0101400b5480b9008004080d50b041c1602c1d1302341c03617810a0700722080c0c030f402039000c48042000381c00300480185a2802c0103400c9103000d0310003800034010185441e003c0d1085100040c01d200505041c88040c00c00100200580e0405c6020160303240c101400c122814854607001149181c8403005442ca203030080c000a00020411600b01c8600200182044060104881d0f48001d030718000d00c0380340d019154691006071103891492001094400103540d40e0488103080c0c40510200303201c0349201c0020301107400c000c0c520705c00f05801211104000554140c415140808680c40e143c0d0000007131180314003455080203000050503c02040407840c0f076 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 190789982 1250 190788732 190788737
    0x2010b030111030a0b0a0f17060114100305041e14010c0512041b08060705120c0c1005071206080d020c06031e040204090f0c08070f06090e06040e0d030606090e0403 72
    0x40080e040e40c07031301c0c0c00c40c100c1000040c1050008542e43e84000c180e10b404c07500314092110b2100060000908108105e600404045c00054003003640100461640003003811110700705612100024144544840d00010480c0c1c01080c2108568182c208a0b0b8880703080c8800d15119420500c0c00b1100c6445801030f03070510424030380700c0200740d01d4584d11b60303400001008880407040c1d040100003070801802c0c454244207014030703101d03944d5402a103114400c11400c0100303402c06150f030030300c43e000300b402000444041d032500e82000096261500e0b0f4060361081c1403503803a01041400c04801060845020580d011205490340880704115802d90130444240011210304c3e1901881c0d4111010309079214000355040760002d800041e01010b181c907081a03541e1501c405940d0003150320001c204601e0204503000080c0540c044a0b10348a0034900d000b417804019114005800d04030b071020a900380c0d110f41c84542101442002ca445846020b08003501608181c0316160101d0310b1000009122072103982c1091140b41d065 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 190791232 1250 190789982 190789987
    0xf16060e010519020a080a0302070204050106090b032a04060c0501060603020f12070e090f070e040b06070b0618010e01240807120e010c0302180406060207060f0302072102010b030111 80
    0x101c41d03d40d18002d0320741580d021840f6011040303000c00c000c140140203080540e0780c0569039905a00610050f9681171384180704018104500b044001c0c06681a41d81000d004501c400e0346070700c100f4014034540028503003943e00204c00070b00052020340000795182c21510a600074008155240002d500700d018108219002d00d4040080c1a000d46445441075401502405d0074149180103034046556400121120345a0500040a001405030008007498040c101280c0c01e001d40603000000c03800b1030003212001006040f400e00440c1055030360522800c1c2c15502110038000c15030b500c800c101d032245028845c401c08100380b860b50300300c94083da580c004440c1c4030545030744140d900d40110445000550350940c1041c01c2c4d43d010301000d090000e008101802511307a40241e16585211900000c0c0740220411900c65841d101d4108110b58010810034202c40180c10500e101091174003081d0043d21401c5001005076411446c0382109030075208a441000d401075000700100b0307044200b81800c80303000036902490900d05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 190792482 1250 190791232 190791247
    0x10608010b0a03030c030201020408030406030b040b0411092e0302030103020907050408030f0927340e0111010603030815010f0e12030c07030b0f0c16150e0f16060e0105 74
    0x345c0340060712900c0707171000515040c4c0d12121a800d44d005900320000103030f102c003486203092030b05025101110303c0481c0e080000c1000c011683c00644942601c40d401000342880d510300041812440040104504640b4105000183c50041c001e500c2404104c0c45602c00c41c0208030524850001d403815114030000951070a1840203403e19650045036403203600c019207044100e11040c580b102450000180001d1107090b003000350038558500d0480340308000e00c0103140d50880c01c1209440c4542c100000c1810000250400c12004a5015141c40302d601003960070158000101544444428481d0542141c6248110308403c01141c1c807281d106004000501e03289000d840601c0d2900300950944481030490b45841d141000039403c08001d0380c420b40f2444240010413281460300e214080c1d008403e801c80c54078002184a0b859001c140380d40001d00000f1a01c11080c4010a81da03214a0140031850100c2e580e0320303224159990703906c0402620311801e48142c4000505036016003100e074203081c1c1c1612690305150a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 190793732 1250 190792482 190792487
    0xa110304030c0b1012030f0f02011515091e0f0e06030d0f111b03060901020c07030609022d010e100905060d020d11030103060b030307020a060c170d020903010608010b0a0303 76
    0x100606208446050103000040c1c0c6030f2001a00c17007010f442619036001045140501034503148401e01842c0c10769040c070000f187c044c0014446001945d481c0000e41c1101da007062800c0300c4144e42500001800400c111071603154149400c2e00404844a1285035000d0549412585a41c48030645240ba0035501903040120500c0c041d00000894004515001d4460340c0c3c0c00316102d24200c103907111003040c2d0007030000400a90400707000703491340050701c600254030f082270103503805a480c0410700c0301038003665507007500c10110f60301e40c0c203034071595030036803142c281c1c40c01a00300320100b052010460036003c924030740d401202d2070134040d03204010740c800741c0c440050300c2d480c100510200d90301c8060403420303641c2e082004040704141d81c13040540c5402410750440d1658118500801203841c11403110781302c0c2e8003d0000100503610031000d00242c9181d850030031014000c0d45400f544d080400d5541c40307005200440e45c00395015656000e0491320404400078000c5540d81c2103098201c8044074040c5c2e8000d04003100c1840420f0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 190794982 1250 190793732 190793753
    0x15070f060e030d06060305130b010b03100308042c04020924040c0807110303040b0610020a050706180b090d030f0507060e0d1d0904021c0501060902030a110304030c 72
    0x80c000c1202080c0381c0c145480440c00c1d64055404101c0c01d0380daa0009100050741072003000e42c0241034084d420b9041041d0307125000ca0703030f90511074200d24140000015040c0e100380032105004541c0064001d45454486540a20782c0b500742c1c0ca00c001a84191007000100f84c400c07050039000790340280201c181d80e06d80880300000b4450701240020b00c25183c2d680b03e10151154840c1103145512942e0780031240c20180760003495440c0c4204840e070f440d44140f0034400070520003186603420190485d01500003c1121000343c2c200804402c01421324002c1c0c04002540e142c01c141141d10350304080c00c00d1007420781ca8040c0e80032a0700400d040150810825450000005c0c010000c1e0310b10035001c0c2c141141098003603920402a948103040b581c040c0c1d040102d070715005540006448801010803010f050a1040e035001107103680200600203480380f0352006009445039000c0320010319064100c0000e109180d01c80e0f00750000307035105941c02e00c000c03441d01c0c0c42c4000c0301015070305032800703a1361507650b150341c500490b20342d4400031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 190796232 1250 190794982 190795013
    0x40b1302100305151e042301051c140601080d02030a1e0513030302010902040c0305010e150a0b0a030207020f0a03030c080c1e010b0a0504110d05041a010303050403111507 75
    0x241c00022600c0019030305c26520740b107080c001d41c8402500c00c1d8404c0501055940c001a01c080c8140211300983c020469840f68905540080c0c4100c20051101040c0c001c1105049078041d00350200d8440188030004045013090580385054102d46050b4a4540226079902c41e1051000019011050031404000b80b028404d4070444079260040c1070502803c1000b20300403007644100c0140c0c0d0346003030003011414a800350b884000343e01d0904000540c900450b00c00440c0000b040e01d01d0507900031300000c81e01c2d992540000c5c003500e1035003411171302e0748014070014000303600000050303104480840c4585144e160000444041d6a4035a0b914a2141a19903e205081d081203403004903901500e80c10790180e41005510010780b10b000b0002152010181e03091204141c00c2d600214016410f084441e207070062401e08032071601e004a107000038203540d9410102c1550202002211385000898000018590f020000d041900d0050842518084011003000003441088035003546c030801c140703c00d0380070072407107614004030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 190797482 1250 190796232 190796251
    0xf090b09040e0d080406050105060315091b030718090e190302010609021c0e0d1d010306050a030b0103050f060f04060b0f040501030b100803030c07141203010608040b1302100305 78
    0x4600001c00c2c01428034042407105800282401c0801044c040c042c00364600521083d902c1c01e2550400c56450001c42a0240c9031340d0241c001840840e1519551240c00145c81040800386a241c0c14114402006075842c840800ca1400e600c550103c0c6003501441800425a5520018150300f201e030303464080d840c140300e44140d041d5503035494002101c003100d000070890070301a00303014408201c1c100c1401084070b54121131810554441d502d5465851381042d41819141c401541881201611200407030190549802690b0821418a400020880301268860503203104030f0941d19501e0b46041560b60390b0704111444400b00310101e0104010410f40e0340581e2083c0006020b038104940030a0209082c0d81080e0300407112070140b8030401408000c4414100c0282880e28007542c03031402c1800c0007040c98013b40308082d00d0542d2405900c110309004020620300304001c9824580c8960350343c440036218440c202c609a4130580d038400011502400500301090190303008140100341c0500b0b0100700d004020040c6440075 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 190798732 1250 190797482 190797491
    0xd0f03020703080d021c2d180501021e16031803050d08061002030f0409020f0c100f0c0e10110102040503010e0a0c06020a030c080a050417030304030e010f090b0904 72
    0x860411801800d8000c80040050382e10300c202410121440034561074800380c6c078903000c2e5000300d012098000507010310400c450070303201443c0c0c41d2072031000b01303941401440100d40f2003500c1010040c0c190086c00348005a012021304c0040702c030440c1c3c8960700c29203a1904600800303549280c00a1300805940704109141000714100070780340c1e60b83d0703071034200080311000101d21050104844c0303180204843c041024144051820080810303902000b902031030207000b0041d60041a01c038402c0d41094180c0d018100542c045a4034003907010440c00003001c3c0513050b8078403181045e005031507203401030070071944070300c0068420100c1e40c01010007141c0c440d400e9200512155002c20000070103a509000b510703604c941c0320001d001d0b0407440b072600b00d084481b554403944c15500f0a2811102083d04140310414164006020994031100c04904850600c903580000c164074041c60400b0010340d60010182d44114400d4480c09900a0000c0054841d2540200414002400f5203420301102c1c5095001d4420b6103c043c0000c00c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 190799982 1250 190798732 190798739
    0x22020f0304110906010f020705040209030a020a0303080406050a060308180d120207080f12070f050c04051008150105030c1201090b01030803040318050a0b0f1c050105130b0d0f030207 80
    0x1500d51040d28180c4561004142c00c04071440c10780b511642080c03007402c282041c01c40440029440b00302a00c0f515220301d6000c1040445030f00e0500c00d1011169000f00f50600040d22868042e20455082e0f4090728054a03000009540501c64412902603c1d004100141080389040301d10340040040003001d5004004a2035210004060340205032401d05160041c0c04120704210603c0d1174002c203004540200d50000048444c8102d080c000c6a0207a41c00169000c0b180005007001843c1203e00070740c0c0c6401629000420010700c03800300594054030050004d03214101c3e070108c0d500c0303060a0f003801a1030307040e00210604201032a03e844035007109441c40001081000d40e13512003075400f0785c09a100380d03506e085c0007080000309a4803580310340c00c0c1034101040d18401420003012410030300403030080b4102c0500004903440b51840c1441628a840f410aa40d111880b07032001384000940070071311a99005003060801480b1426460040c041403420181c503071254541d6a46540d41c50324403500c81581523010360710010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 190801232 1250 190799982 190800007
    0x6030903121e0e03180109050f060f072f03060402010906030e010b04092111030f0304210906020106090212040809040204050306070c0507120209041209152303062202 73
    0x1503e00010341005103494491511a1445106803003011504100c0c81d42c005111654440002852880c0c0540e0b015845000c00c40c101a1103109000003c0d100c1d1a0a182c40f44082d0700d030070906100c4c0a440c00404942944e02000d065032080c060b10000d0220300b035054140a901e1103640002d201c0d41c0c0c80f00000c2030000c1d1400115080301c680c4941610300745440580440d00344500a40340c03da94a0130300c4d018048000b0040c9160302c1c4d002d0410102c03003040c07000012038144078006686813944061020300d0f21414803d0310028000e1200c0d4818031026508005001800358510b10a40381d90050a000c112650743d119a01c00001e0b9100b015550340c090703424032010825480c1009024070641c85501c0d112040ca009080143c944200d9612018201542c482c0304c02c01a00c0d03038224160480d90200b0809420010303488291280360301e81d04044111a8442d12030410300f58001e0100b46401311040b4480120495403480050754881110b000d600f0001040784101c070030300300c11718980044110f000c0040c10f00b5a0100034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 190802482 1250 190801232 190801241
    0x31107050312090a0b01060c020f040c0804021008070504090f110a0908060f0106050a110715022803020304030f080d110901030b040e06061e0402070311060106030903121e 75
    0x1980d203036001060031014240140000368111440c02c0c0205500c140035965200900014083c1e141042010708801086460300d4103000860400140144148507011400500d8844229001d900c100e10361541c0301c1009000320003850194420359225480d040c14000c900e4080d050400035180c100d07649400720306001041c0301c06410610302c607640e4042810b20f0103500303501d84600a403808400411060041142940180c212030300e420300c034240703420080740078041c10f402c11255610205480020781c4503000d81c0340d40404c001d05001041c8c60174034a42400511081c503441d24141000740546d000300000c2c4085951041741480c0944a900031501e0006245001c0060380d0441d141c40e00c500c800800c852400d5a094021000d50000c182c80400400005550155480c400601183e0003072014018001000a030000d0010000c14040e000750354480c2149001451500c0d0496801c1d0310340200c40001c82e07224828090344401c540c0603641e04844082c6144081c1c0101001c0e1281c014040100110411300901d5028 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 190803732 1250 190802482 190802497
    0x50f031615021513020103091e030201022a060a02031f06020307020405090c1f02010f090804060806090c0a030c1e020601140402130909060b090906101d060f010311 72
    0x82078160040441d802a2030440b20780b419503200328540f000c00282004a10742e164200c0e40910380031031100083c0c01c0141d04400d986d16215842055960003405140d01500140208600da840c007450300307451200801115441c08042180c1c0f9040301000c911418010317000b441c5c2012600b501000d90000010415070004d440740d0000002d600003145070002d624042c801e2582c040d844001034030320b03140f001001880500b1451040e4a40480c0060340302400f500c02d500035910311903608402c1100039031a00389a02c4030b410500c00c80000844a6000600301d0900c5000c07a8082c003103a0003246d0400c0324020040c0c002e060a1081202006402d44520300ea5000030140302a100c03605402900880d410450600c6140e60f150b041c0078051401009079111011480051030704580003964005880c06c26494468007600c54149001c0d4420b52241c00e0000c00080419224011807a2402e03c04840d56541c0c4682c210040310308005807003080c3c03030002807003508114400b0410100c0500d8002100105005842010b402124 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 190804982 1250 190803732 190803749
    0x405040804260115150c0302030c12030402040606090b0a0f170705030f0a0213060e03031b0f0105010519060309030e03030d0e07080c030a150908030109090b13020a050f0316 76
    0x240b0480a000e420300c034003106495000c01d202001800c00c0d008000700382c500c442c118100000ca08000081c036200703005a442942e6000b0503501e00310ba14043c140c415410a540a900c0b507450594000b49250003869100308a500c681d0f1402c3c01d042181c0390a80e0352201d410030280501012003c070441e0380020301680c0f442030035a03440c0c494407810003072038180c20404020a54040c451040203240505048599030b4011155140750801c415907112010a00f54013800d600e4100c40c03a40e00000d6162002c004c40c008001e8010800200b1032a81e807501040b5544040c21151032101118500610540d40f0a400060089000c0c0c1084504044201d0100c0e01d03661000c6074010b00c1654400b046100c00f03106200120060480100130480082e01e940041d848040c0500d00500040c540c421903040020181c0007503041da900407110507107941e580c42e1108041d001d100401c4a0742c0c42428001290034100c5883c0c034611030340141590002c1c40c01c010034403c02e00c034121280c0347d1521a85d1300c00c035140d40140703030018054130240 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 190806232 1250 190804982 190805039
    0x20406050711040e03190504080102030405071d010518090f0604050303090c180f07090f0602030d11030f070e030c0303160309060f02030d0207081b060402011805010504050405040804 80
    0x7800c0c03180e20403603918403180c492420000c4c1400d210100100703a51900c14844540c1c01c40d1049900306031401d214551000e001940040304000074031001040d4082191055118046d100d040c02562403000380c800d015070f59204100c03002035003269429003001c5500420301c404845001c03100c0e407600b61410304204c4046a45600000800080550501481031480d80649170300b40302151940f00f04918010051005100142a030f00081e9040d200d00145801801d84400d071402198131070500039185c2d070000710050000e90038500085050302c42c4c541240d1254a94200450302c6442d40d0300200da640e0481c40303005505119003044041c40340c2d410f0004285d0030000d400b199000c404545006001031281d41c1c4020b0501074000b180301b8441d60040110f42541d8034860780140d07910388514122050f8003030710803e04c0400071464001b40c202200095210300690003600c6d682044030382c411803406840458042c03540040c10610082050b0705103600040c1d04107200b01d40e100d0074540c544426030300300c40130300d0060005040007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 190807482 1250 190806232 190806247
    0xb071511070c15020a030c06050a0b0d03030c09050906010c0f0201140d050604110304020d1e0b0a0b030106140d0803060d1202100b0103051e060109030605010909051002030103030806060309010f02040605 89
    0x43c041400d00604007800070384064200d0307480182814140300e50282880e512440000e0151032158040c1c500706500502081500c040c40c1002030081202005010100d0030710b030404505881c08000d0b640c031410059403080c6003071142d5920000080c0d450b500490500101000a89061001d80301a2105400414000030945050400c000507031b8501d99103d0341c0b0b000c0400c28000503882e00f649401c05950009111030f9800121411f0b61102c1441c2c1d90081c0480c0126001e00184041d80e4011105883c802c41c001e1065075103030480e03100c3c1e458078004026072100d07600c078511001882200c0075682c8242c004000c8800580c0c0c0340c4071440c50710054002c40700181c000300c3c01900310300c55a1103a038202038401c5c07804000901e05400205d20a034a0b840e00c00141100f90000240e0f903a11808180028690101041c04075581d1070f00003001400c200641102c20f8015000d014030504618420740b4101d0740c1682c1e418129440d4001030208aa0029080c42038039500c4a21104260203940010002404287c0c2d072140d40310107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 190808732 1250 190807482 190807499
    0x50d080714011b02071e170705090c031e0106020616020304090f09031d1020010e0f0f0f03031602030d022b0e0c13060306061d0f010b071511070c 64
    0xe0340c0c001c1e40c0014640e1001802c40d09000d0b02c1a800d44681f5540c1900a0150022140c41e00704160711195019001c03204220010070003070040d600407592500a2080322500344040c5030030038800d00884005074001d800251581d02011409014158140150392500d5103441e41c00050300c0d100c50f00c00c10384039260b43d0740d0020103510100404400c1c00b034050403d40d50300c40e4000901c46000e680024800c01c141c0007d42408054101d00924807201355070000c1216001400d4601d4981d0190b140110407400b0b40c203803003152400701041c00341410300345101035490b5580d013030105100c805108045004501c800d02c1141d020340064401414180c40c1500380741d0505000032034080342101070000b141501410070340412060301e40000c002c0710101c0100e500d0b001c2c2500d001020b200910312940041c010382d04200d0006600e1050402d41c001c030b00444000000c541d40d80d0160100061400c3c40b5044c540791003080391801040e200b07407040c1042500c07850041050704664810700345036008400c054541c3c8030600c400304807024 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 190809982 1250 190808732 190808743
    0x90a051305090c0102030a020d0c021c050604030824190e0a0509100c021c030b1804110103020a020a03081009020307080a0608010b061c0b040207032601050d080714011b02 75
    0xc4244001c500d4031005c980001c0d12400d180700c02740f040c080c0c200e000000719601d041d440d00c0e031000a01e285900051860800c4d44da1814142c1d41580407800401c00304200d441200f01c01c2581d03076040301d410f0144160441c01d009003458100d000c5540e80340d00300800706826502c502014094550300c40e0100f02d0703060015540e0f04040110680494032444e11340660b003a40e401040309401206064200c0101a80c50242038010346035201f141c41d80a078032580c3c2e080704040820f14860069025600c200c14881d82c240054080340300c2c2c4007503080035a000b6410600024860003280b68010b01e2410445019907441340b2480590304241d4102c8040303842c0c8400c12541c0b0610b4850440241042c0c4028040c0750300c00e00105a5911070310001d4004e07411040e0702d03600134414a8014140d03040c03010300b0855446041c4d0400500c0c45142c0013220350f184091040e0007491440400301941a00d400900104041c009603448400550010404480ca07001c10072840d40805c4081c0720f0302c01c0c82d51450304113a0094821020090404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 190811232 1250 190809982 190810003
    0x50319090b0a0f1101240e0a092d05060a0b010e04060b0a030b0105090909150907051302031504050103050d020709021806070206070c030f020a091b05090a05130509 72
    0x30000380207280e5180e0f0b11007440c001c0c07102a42004408619448103082c054403200070585050074052040e4103040741034600c031204071200480c18045540b5401841010788940310005020a940124403071000a000d9140a10308910380b07040c400a6180d5580e1207007810400c0302c00c104442d07560b2a01880558002c1901350200404990400090b07003020105051707801940d0880f010550340700001d90550f405101240c000e030000500002492400a0959580788100c40c00300402007009001301e048104006280d40135150014213036951030381c05035580d10003500000e2820a1441d40300b4000556a1a5072250740d002e180200050304020146410103881c2910ba684100c2481e0710421a103480003035103180040180b03108840140c2c2c5c4002500016016029041000e4000c40d51340400200300316080c1d03c0c8000452085e189450400d9494401c481103d41007100b044d040002002d070802400d00c22001420700709070080010354400e0700e407000300d46480e207001c040d88001592881485000b260400885686 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 190812482 1250 190811232 190811249
    0xf050c0306031c18030c090e1f020307050f0c0606011b110907140d020703090605090f010c080c070603090b132303092e020105010b071104020705031909 67
    0x354180500800d80c0d40342815210a0300466034081c0140941c8500c40380c6007030041a1100b01c0d4241d072030313091548190516200e190149031401c61545507988003c48c3c500ca40c0301ca1701001d00444004400c10b072010b907100a01e041c003000070411408902d413003508040d0081103610b50043c42985001d000241210320340000000829005e4001800041e071030000005500909075406801d58940c5101610702c00000d4020180c180780c042402d210b2401650b000e4030800d070085da9011581917840e60160351901c201040d8a401544e41400c40031154015680000e038144296203403403804070441415030405446030810000a52031b81e40020034420740000c59a0071983c1d55241c1c0d502400b8a654440c0304294005a203500c10385181c0e0000d00c032000900580341802c5e409000c4825092228504030692a0a14055801070f40e02c000c00c0c9495920510404c0e041c1c1d0403020099261030459103844e003a42e07801c0f841c07142e8096000c000780400910140f0183c55400d140041010400d00c594001400e000c20a0f000b9408 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 190813732 1250 190812482 190812487
    0x12070807180603020f07120c1a010b0406031515090608100b04032301111c0c020622020d031e1b080702030c0316080f0105010302030a0b091f0f050c 65
    0x1070001d15001c1010440726541001a56208000e03022100c41c05460000f0740ba003d00004016845600f16901640252007403e2000c6007207980346044000709000e0080b52441c440600091004a001e580100b02c01c50050b8000c505607991103060004500d0100f405200054034008100134881d0010092500400b04a0a0324142c03030038054440f90f5405907110150686210328441191880c1c4440f50303020766a29100284100303000000004121b0b40818504565007408244401803030400c4c4c45181c02240c800d9010f80041c1e150000d82d02551500610f24134202d01e424000740d03006a4400782e204d081701d40b017501c414a562201c1d6100c410701c41e02000401062190702c2c2c24078848100c0205003400385940c0030f48816210f072224000700e40340c201410380307450f098404c449503203600b07140d85680001100c00302800c80d28400078171000319081e600c00f03201c005e4050f841644804004ac08080503203500c210403104640d00c15005000c84c101001c1507500400c007845d542c485420000c0c6a038001c00c0e9010902c080c0662 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 190814982 1250 190813732 190813757
    0x4020f030a240218100c081305010f170403050a03020c0723010f02030304061509090303051503010e0a0b091603060b03120a0e040b0f120c12070b120907030812070807 73
    0xc04d100350320740150b118522040c6085541400f0300e0030300030007036004400d09454403501c0b0280095442c180c010b0b1790102e000c2e98844075425220303400c004851042d08541201c95199540c0650740c45e04000860810b05809220252114004005100040c408a1854400500307402d400f40c0440e021401c0450402490071055010b0b10340000840350131541c02500040c1a48a02602412013007a60300306414480c1010b00c090241a030640150703014180c3d480382d04000f0b030740140c101402c031040c280c5c0121064120350200350101b0700e0a00c2456014801006413403200b401c074014581d50002d40d410032210036a4800511119080400003008448140250146401c681c040d0140c40f21201481c42c510a9464018000081d1664801c020584101401e560161420005810f07210358403840d40074014020351000e0b0340c030000700061200c200d50700c0c1d0654078900328010a030220240c00090880c00144100c480010000312100c1c0148000c02d840001e810103400d104400402201001c0c0680c01004422041c61 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 190816232 1250 190814982 190815007
    0xe0906090714040f02040803030712020c070b13050d0c0303180501120c0306030c1d150904080d0608060a020301030b06010c0201020c120c04020c01021b01020a020a03030504020f030a2402 82
    0xa54001801c1c0141801000c80090003504920131030715807040c0089400194018000081d40c05001e9076240d170303481140d03480021000ca01074200710010b0369201080401540712030304010081110126131566007a0748960109851700400f4404031444010b16008005250b4058460b030b481d24540001c1142040c41e0000081508151640c09281207542d0342061500b09c3c02584010000d561200014004554800c60408101c881e04801c189440426000030421002030350b101d040c8000c0105002034585403034803500b00c960001032262000c60351f0740801140d030050401c00d1070322409901001503629815880c01580040010388058140401c3e00307540c00050f038001c205a9195001030303888141c01441d5020342494441900d00c0241c2092000440d03c12580381034008081800840400d8503c18150002d61400c034403c051280340140c10030711740000001e20a0b0010f9030868001011241e602c0c2c3c254001a081c03003140241156580c12070301c0300c10038840d0015005c0201c04140c10045080282c00d2003030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 190817482 1250 190816232 190816243
    0x106090b0306040f0e0607091a0301090905070801050c0307030c021603080c01020418060501021c0804261306081302151e070602030613050603100b0102010f14010e090609 75
    0x403900304160200015150740c840f03038044240200d006105210710049491540d031903400c00d44d0031000107501d666010541e0185040022156180142054616881c0c002c0c2034005020210048038103001d2018000b55107202402064020a0303001050390b600c0c1040400602181c445100030015900703c010314a0b45c40c00790004a4044a030041400d541d15071003403c0355802481550040070320703862044448142c8590030b522510a403182a0200c1e244211070480c800ea207050400050400140c2a600180004640b030500030003c00e800d0000e020450812500c0c218580c010785240b4400109030b102c20011035902414494210112600e0780b010301400d13030046002e601000c1d03c0b0b502d09600000da61682070100c54a8282c1842801400584501d62482d001c00690300c01d64440d841082c40f144000c41b40d040c1407061501442006004011100f022000740018141e66000941503543c0d81d4180c070307112641d50281498040242c03008074103548c1404104503e47c04040c11307590301e5034040c03010000910000120f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 190818732 1250 190817482 190817489
    0x50402100c060b180103060c1b03050f121302040c031808070507081614040203310206030109090b0901090c050d05030d06061101051510030c0e0907051b06010609 71
    0x40201420203281001c202611402d01c0c5107410400d0008000040c0308061344650690703200301c8040c04401880b0200312240901c100d103401105403003582003030001e40680002d2031078000100d010341c1000564408241d031a441182c005400203150310483d01103240610a001c1e11001600f000c01c0341400700100307a0248181c005005104440018800043c001c013001540c0040c02c2c0c071070840b158114071080320a001c0c00307103214180291340b140a801441f803815009803849200c0c101103800300802460708a0603000d40f000c05416048008100c40c0000d602e032800258042c0070f05010204040016160041440388002e224090030303490010b20400084001c000b00040700c00880301c0400807891810b000e415842650800b4401311300d4290002421074100003440d80714011b81000300b10b6070792080c04003c5841d005c3c1c02280e601c040d214002b104600c1c00ba900180007210300d4500340d01c1d0901001c0200d8442e84041c0e07a154042100031650004101d0700b15040c182821005000e0887c55241c4400034015407002e00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 190819982 1250 190818732 190818737
    0x40f090b06040b12030301080f0609070b16150c0f110c0f040203071b06150e06150d060306021605061e16030b06070b0f0105041e0c020c03030309070f050405040210 72
    0x1800c1143c1d03903030150030240c0d0141e5181030701d82d030f542d4445d405641c8158881030020540201c03c0054a00740c808181d910407a0380c540c0181c4d03c0e1060030001a5200d01c0e05020440d92250005900642c1c3e00140c410100c1540b01604d42185a60066802a004850310240c40c0d40f10381c40840c4802140d02e40040940b0388070010796001d600c1c0d03220303100d0a8800c02003c00400c407121070034090728014002c40e0f4010801009003024150307140c2d42c03200c1c1503074402e00044034039030341106640c020310a0f05644100284180c07044810300003002e1b51a035136044c050703900c0061003450b48600e224074942800800c0c041240c003c1802c02c0e02c60901d102401c1101c603905802081280c85d90040e038496600c96010750401c0c5014a002800e031503498215203422481c108065a05042d403040e40e000204180c14a8401c0c186160aa80e10403224400c0440d40240501030701161101140209030b4200d940780c40400165009007594001780000606001d528012540c0390750010f032181c1e0600c001c3c00050303124a500e52280c0f80c20752 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 190821232 1250 190819982 190819991
    0x9010c02150c03180a050d02011709070503120c070b03070909020304080409050408030a0c030b01020304031b12051e0d0f0e1207080a03480c1202040f090b0604 70
    0x71004a40e406191025441400000b4254800300a0860049072114048494441090f02c45007032092241c12240300a0206049552040c0c50020750040c050740000e207001142c040c1d40d00d03400468280f6405440245c8401c03400700c1c005121941c00e100820242000c61052800d41c80c10b03420042a8480500c80c4000040d800400303d02804403071070441b03014201c0c6d20400c1c413845c00c01c1c0c50a4100e0780c1c02120040780d007602e48070414050300d00c640200711032050140d004508150440d150541c2d140b01083d4548400850120b0000e210a0041515468a13014402804401c9244000842d181c20f40d1900a42560000190100484d8100701c0f00c100000180c60718400c030004800c003080780b030b09c80b00709001c4091180d5400040e800c8800282c840e1418803d646104989280402c0e034650340e03007100441401d036060000917a0300034259111072581d8000c9200201152071441e168220b20500503080f220007401e44640880560400c0e00650400c0041c8040410010702c141c1c07101c185030701001d030885210701e859 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 190822482 1250 190821232 190821259
    0x60614060307051305090711100507081f12030c0b010602030702030703080f070501091101031103010b031815010306090b07020a1104150f1401090f080d0c1406070807080c09010c02 79
    0x5034078130140075150180140c1c1c0d0b203042c0b602000d4810150007051401034800d40201c40da0200c01405105d000d80d0442e1903030295502c07400000300c03601840031103920104421000005510300c08401108060f4020344900e16481c90604105150000c145c108034150f5208010356401608d0010b135400817242c20109958a501042c00f1103101407140036005410f5608160400091102004107403201d140240c0701000703558003120880d0b4490009114060040c8070520014140f02061460144200d8603503040c1e42d98403912241031a40c194081c0c0081c2c0b010f036540c0e070002003080304070724445802c4011800244846103036641d4140d00c070315444034550300598981c1e142c16054101aa9951f0240914840e04100b682c5c4484500d00700c003505008103400070f00846000110150720074901000c2d11200c901404241007041d81c150303150b03120b4002c119032468003806581e100c9030051090074003824031507039007000500300340400500b40100a000418500c500f088880c100381e81100c80c400200d58103070307410030035501c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 190823732 1250 190822482 190822507
    0x306010f1a0306013b010309020d0f060603082b0203150d02030c04060305010e100e030d09020112050f0601030e0c010e0d0f051606090609140f0d020a1206061406030705 74
    0x101114034120011008800180030b030844001e00e604182c00e240b80048101174400440654401500c042d400200100440c0f0110307101507081d8140b90301440011131342581d02e076581030040d0700c503403030003040c02c00100b00140c80b40c00281c6a04000c2043c0740002d40c11800c04031040b051103924468030b0b500c1011301c040b012045490a20600d20000e40050041004a95a0410601070000480b81c81c0c41d0340220b4406216a803440c2c42146203500c0484002c41c00d040e003401043c0001d20841505034107000107014003681d48440c034080c281c4503d040c9107100005042c14070015040d12901101d40c413940d00305a404244507648002041c01c00c5004444100c034001c5181420007039a0540480980507008605601300d2050b00100c80400301c803255507c01d0111541d0754001c6903243c0d90b501808506c0340040b082c109003445c28181d0800c0c901c100030300030350514640d64001020050b00d50302c440910030140501c1018040b9604c86c00d0b00919240404040280074500041c0c040d110040104d0144440070500740c44522 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 190824982 1250 190823732 190823747
    0xd050d060b03280b03030c01023103030f020307060f09030806040506090705070f08071a0c070c06050f120103201203030703022208060a1109030a0212012007020306010f1a030601 78
    0x10000c0c01b074955520034000898003035070045070581c1e1040c8003440c03103501078020358111324600d40c60f41e00f0403a0700506585e421a2180c442040d06011480144500800b040c990312403906140102d410000e4510400d140103041c60b0300080140b4440e034031300420000d0740d4845001140d032002051500d0781d0780303010f2442c2610403040c43c808040d110040100340c00c0d042080c40c445403038028009880503003090b90741d51081c50840c031401200601b42c240203141085207038010000383c04071604107103405007045072101c81c20391042801d900588046c0311800c200803810746580c2103209031040c00e0b501e1198188003042d001341da9200c0940240100340c2d0000e102c46491140f50810786021406103041c0200c240d8840c004c036590401990079840252611903100c80030a0780008030b80c01003001401604072204180c00300a0b81c000d009070462955529001100b035214401640d40d100c100940c0700482e21001ca40c0141890040141c004a00300701744868203016501208090600c0c80354000651035980d0380b00401281d80c40e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 190826232 1250 190824982 190825001
    0x20c100c0602161e05030a0e0a030204150e090d050313030e1903030e060304050c010804020102011d010608010c020c06270915040b04050c07080c0f0d050d060b0328 72
    0xc5102107040c02084002158030302c002402400c003c0d00c030a40c4800d44070008040c1c00001045c99004206840c0030a000349200403c3c83d4000700f0710003509a42c2e802060680701c203006103d00c098440c840c2480041d0800100541007a2088000c04442551f03100c060414440609a02400b16010742c2c0401018410054003254200140003039401d60504038128100020324041200400c140d00300c00ca59505082080e24031580d0490020002000318100540e0300c00d2001c2c10603070441d503c1300c44242c0701c602d0030041c0510041c00c0c0310002501e00d00d003100c050700b1982d520510304219000b40c0f0700920035a1748c50007074624101c0050400542c90f0b6411844031142d5500c0c1105613002600d41042012840c0c18240c07110001c0b006a80030b11086c1d001604000480304200c2d12102d1041f010700014000c1516400901300404c1d00c1c404a845100c08041d0b100d2401321801c400c003000400001d07a5030344880c00c50107540001c08820b440d407411418410700b807800c200c14205042d402079005012030315000d4515044080320 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 190827338 1106 190826232 190826243
    0x150c03010302040b030a0b070221040b030106120e01051009050907050109060f020f060f090f0f07050d031206090e0f060c09060a090b0310150c03020c100c 68
    0x21310044032219014440c2003940b000041d14840e210b4081d038240e4004010915107850380044003030701081c952600c07210600c010070054001000352070640340e084c18081303410300201c000c41d0010700790440d082c1c0643d800c1c2014414a007a800454100780c901c11002441039980c4c6000c0540d13244058401c00340044d082c0e080c100682e5225982da10358201240c4181d17000d084080d6100c034a41202543d560092500d481c00307000c0051800c0107124101070f241d801400d440c5808022103501d580c0c940c0308207400341c1c4101d48400c007010b106403260310b042480c40200708102500c4070700700b0008000c0a07003102024856541c0b182e2040c440024214131405114004616240c200b2042c00007540119100101340701040f040032401e1018000614410303c0102000480d56243c580003034207a003081540da6040c08401000c0902203680451028450041501c844074640b0b50407008581500762040301030325 = true := by decide +kernel

theorem cover : BRFrame.Cov 190647482 190827338 := by
  have h0 := BRFrame.cov_init 190647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 190647482 ≤ n) (h2 : n < 190827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
