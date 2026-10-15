-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5107
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:46:07.333882+00:00
-- url     : https://prove2.me/submissions/3242873b-6008-49d0-b6a8-9e553c6fb9c2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 918345323 ≤ n < 918525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 918346573 1250 918345323 918345341
    0xf0709230a172b0c0f0f0210180b040302010206060d0c080115150e090711070b16050106050402030610030e0f191e391818020901031202010204030b070c06 68
    0x1540d04100c0e0f00c81c0100343c050070320b00c00f803e94400382d042c0c00d00340405c54055050040d000b500c01d6241405030b44014010020300e1100079005510050000b6440004c40280c4096981c16800ba19103a01c600e02001515403100805407400d02203002c000401000034814030002c919008804021549080b4144080c040b04030355803024041c00b0100e40d044e994840350050740c07092803818401c1800c1c2485040c10715100c080d401030a40302e2070000c1d4850003400e14569282d100d80c0700704000e208481c0c0f10000d00c4160300007038801980101c248150710381c20354082d80007449414010f000312581f00c544121003501e00078004152000150201c0c0e80c0d8818003e01840f54060400703810031a0038076480c0d84d5114000740b8110020f844018455040300c1490041188000320100910b4485040c11031720b8426801601000e81d60303481100e0702d40320386906241c1554403002c006030740040515420761b1a54031030441050054507001c1c1195420400030000a1010803024022440d951f40c41e4500c206506d030113000c950280b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 918347823 1250 918346573 918346633
    0x8010b0906090105060405010c0302120a0c0b061206060607032d110106030506010603020c0a0b07120c14190c080304030305061008090d0f02071802030f0709230a17 72
    0x14005001c1501d417041224200d550038a0725018580040c1800c034200710182449080d0304900203a0200c101c0e500088c6c100c2030b903004240c0b80c441501e0710020800c2c501000c40c0c2045c52900004000780795460140060310000d40242050143c9a5066000c4001000340607014890b00300c40510b0042a594005950002c07031840030001c1003014199103440c4c2d500d802c140b00e428101600042c14654004044c030900075031b070741d003c00341c44124240360074007a140406070800c802d000c0340b409503503190705481010f407200310205183e1001c0c039000900d41400c4400020b80716040922918410540c00120201c00071031065009070341c00034140c18180100070244502d1a805400c02042c0004e0000c00036002c03490070021801c0d030402000000050300305a06010345a400703da44882c2d0801c0e42e41c01a0000d400541c410404103031815165178503004251207030407550003003c5503800c05105254840811214100c074041004007451031300c583d18150580852030b9071880c1c1d407054025150003c03451100c08400d018603c884 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 918349073 1250 918347823 918347839
    0xf0108030a080406111b010b030111120c070f0b01090c030c030606020d030b1c050a1e1a100906090b01020114071409040b041401030302070803091020030408010b0906 73
    0x1c0140807100103003001d80b4896403460401e000300c40034022640140c2e46005c50b01000b10203071a0250007000c1911400b8040c0d4240000e00c2d00c0c00c0504030444900306500e0704402d425458a850664007a0004d54044542e140450700031004602c0c81580e007402001c100c24040382c3c1c11035803072008082c1c9916026120a060802100f480b031a600070440080500c43c40c580003a1084e1090005145da040c20605040d169040c1c01c1e00405000c400710715000e206000d407415540d20401400b02d2134400700c45e03000140059010030b04071a507100a8070011074210f02400007030982148c450200c1000c0b6503065204d000150380d44d003140006942c082c041d404512100c0c5095050900d0200760152140d1002000403040d801d000800d240c1640d281d620250256001a0040041800c030f1422081c280a00b80000e501510604c0c00002e1101340010441c0d085100c06086081c4c00d1841c910300351101411204010840d031000c0300c0f101e443ca4070801c0580028070707406002003449102407060100c08080541014010042 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 918350323 1250 918349073 918349087
    0x60405190804050622060f0306080f0703020108092d160605030a0b040e010513021c1a09011b080a0b09060d0209370e0d08280e060f010803 61
    0x200400c0e1000c0b10000e9810a5071261200490035404030303442c41007205c045491001041c0c2550100d1025010262504e042207005d85403551503503660060b0142250643c4882010300c01948503449480d040f14103c03048800c46041a100001140b8600b0094845c05014440c25401600b00b0002c6c0d103e4000300c24042e4000d581464030003411840020300b0400d14503100d000030300303003900c942d0310003404411003100800860500c00b401d00120740c08100d05912803025440d2650340039800b108544a050391110f03020134050b802205a0300020ba000b030030701d09555661420301c2061454456074441c14402503075555154030b0014003000c00c03034140070350050091020350b0400c40f8a48036a0082c5184540450f21001641e840c4000e000b0750340c010f800d400c4880300c90402050300401e04100302001d8504180340900c02803116034401582c822142c048000012107503070200d0b8000448020040300d1100c00f001800918020643d00402d0710451094407099500480401507104100e6004a0141480314040c1d0f1601d40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 918351573 1250 918350323 918350333
    0xf060516080f1e0c070309080303011404050c0904020a2d02060c220306060603180b0609100b18031b060703030c1b0b06010807030e1207080c0f06040519 67
    0x7200500d5040400d034000c01140074205895400000c1c424200b54008082ca42a620000c50342c214000403800704403004004980030304040700fa82e058030321400070300c5d59035030040c0c04000182902421075481a00c2c200b000000c551030750700082910600ca03807501c03050751404403580c40c1c0021601c048000300041c1012050b084540c00714005820424140344c103610780080c10b90041200b56000748910384090400b400004114040e0808422501d40e51070400c1003c0c20f80c41000200495000b00802c07003485400000d42500d40460082e40003100d40b0801510640ca4001041c0c04c0e0f03100d151340c2c46207680210740c020303114581040030840710850848a0410a0000c4001c0350b424011581c00501341500c40102c256118851000003400c0178031081004c40f47c5c1c81c0d43c03c1c45c90100c0c070150745c4180046c50400c00100705038003900603a40010050802406e42e100090341d004e00d141c00c54034003241c014804002200c0494410001c60f002c0102c2e04001e000c0074241803400d2454900c0940900900b450501803800100e9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 918352823 1250 918351573 918351587
    0x10e0907020a0f1505090a03110d050405010c0c1a09091008030f0706091211060a110d020703031404110111011103040f1a331311160f060516 62
    0x140e2140b500764200c3c1c0340c0d2812140301000201d446a18500d84010020001000240c58405500a0301c07000300c0f41413000350180d140c1c05c0c0600c1020109400300800c0160354810a08a00b074180a0071030404143e49544050703140100d07521071070704901c001062100c0c040c035010090580000045592483c2c8916000c1c0d0140c03640103100b5407603c00318000c6100014819943c00002c1c0199004c00c140101080003034000c1e09503108522850690b100c2d42000034440c00303551141141002d42c0014990801c003109244c480030b94040f110440405403161f00d13280682081c0d11000380281c3c49076030304886030f504400004110740640400038000e44e0402d000388101d543e008085035005500300003980d014403003c4c14041035401c080d83e140c0c80d06403000310030041100706e0982c60307450074442d2030079140000303060b105030005030180188801d51005040300b82d0b0003202100d034090800c14140890541c00c10101c14011f615050b00c2680950b640300610414004201c0144526540200b44040c0350140d000032520041c603079 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 918354073 1250 918352823 918352843
    0x50a08010b13020c1507030212070305091509160b0a020d05040308030105240a0206160504030302102f09010306050103231803180f040509060c09040b130209010e090702 74
    0x7681c1c00240da1840840174040748401c214084000100c50803d9440240254402d0014004500440c00440c40c1035219000b0540580c1040c401030001610182c50360415040c060300c6e40c00c141c81120400c4035894003a036441002010035040c0700d525040140c00c00b9042c200c80059890801008010070b00c0041c120509982c191401921080c604000095070440640001c81c401540303001c000c660615000c0c0c0c0080c031180301b01d403200c403514034041300000161000d00076408010003681102d440304229030045d600c220005c4000007040c072041055401d41100348aa0400802c0711034200107101d00a5580500852008000c01c1c030b01081100c0340078145000901e840000200c075600f000d030119104003110040a241c02d50100c0c16aa45c0d000004520341e2940d4441c04414042d0001c4a50440715260520800384a085900d01903c215582c0c88a501c1c0e441d031041484aa0043e91450b403003905480f180303001c407041c0700c1c0d01c0b00060703950242c01c0001d17025008008065104682d81030030800c8096001c514800a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 918355323 1250 918354073 918354109
    0x32109150e03030d050112021905030d0e15040e0907050a030c060e01120222150507030f090801090605151e06070809060a020d0f0203131404090b0c0301050a08010b 72
    0x7001c144980081e045200f0500c19000407401c210000c582c0e4500c2d07202d0700c40351901c04c07038501d00c020100d11104403200225118240e41500007160b1980618000c198680d00b000008141841c0071036109840350b0b46130015000340700e50b00010010030446040412191000d032200b2100d400300c4503c1d45c0d0303a00c1140060fa000c0e010420046000d00140340e405181c861801480b100c10035911840d01c2d000001e026486d050111320480500c200005414103040199480303441155501032526680b600d081c0d0f0124800c625400800c11a0780c0001880d110030300c286000c85104000125042c100705982c401d24860014036140b00b94200c0c0a103441518042c6074a401c0301c43c05032031445e21603c95003402030043c02000c9403181c02400000f08800d010354003141060a04200781c80e100c44190403800101c1c0c1e2802852100d04110024100c240401d044809804200e80d1004001103201c000300e0742e4a8018040c15290354030005030120042c441840d0441020300a000d151008000b80111100000c092044071640703801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 918356573 1250 918355323 918355337
    0xe030a08070302011503050c0f040209060f0a020f010c020a120f1d030a0609050d140705070e0c0d0f09020901080f07120201051b07050901050d0b070305180703210915 73
    0x20405000303401c4180d0358540d81401701384007640c03400c0c0151107506680001e84a01100c0100074281c0c50180300303403040000701824a80c10030029070343d0034a06030300141d5500158840c0701d07502c0c0c904c2da9090080f001201c01c2680940075180c1d140c40c20440b56040f0721815800d12564001c2d400c0030a40c0300079001020100d4031b84803c00e205000c4040ba0a114180001400d0711f400e0413400070a0150000e0300102443c00c581d1303040810b60800d0b0079042c0900401000502541040d00204080f05071800d0b159000906580d00520700500c4250b180b0403901d5010401c140c0e06e45540341c4106600e040c0411034018034604010b000d01d008082c4e502a241e090174002e072424440d0940e420030070341e403251042c0ca894010310103480d40611445c00c44c15588401390701c40c141c816441711002081a0410b40160030f010350f0301c030b0040080e6469000094018150040103061103032400311070845901000c024a1000f54040c0f001040303951410b141d0740154504041d020024882010410025008849800060b00340c403883c14031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 918357823 1250 918356573 918356587
    0x91e0c030e0a0503121821040b0403060f05060f030c01030e03040f17010e01180305070201140f09011d010819061d160c030905010516140303090d0e030a08 68
    0x240c001c101d40e81201c9198891880c51104000f0004020184000d1410071400c80d551501c0f2074010080508410480715000346091807950f0384100740819964920454007820a030b140d070341405d4150090381c000d41d1840d840e090040b101d04544d100e6141c2040d025034124416000140c0841e03940c49131200e000341096561040413000182c280301750b402505080a45003e07842e5034000c007001540161030f00c2000c7e5460004105001241440b4040c80075039506107900603190161025103054028007030503418845140354101e4110780c0400101001d000d414062a21488582c2c0014940f9041034440c455481c442028100c003683c00441d0140d000910f40c441144920054880703102410300342e4895489002d00c80581074a01d0b518a02442c420b4030002140d22903000c02250803100d4182c0c541020380480c071440c07000d10075544260014015458410b241c85902000d9a9905a0002510100c03200507000803040c031103280010300001e441c2c0304886c68111031041c1c6180000307840b518004002405440e0005684e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 918359073 1250 918357823 918357827
    0xa0b0f0d02150a08010303271a191e08090c060f0c1b0111060f070e030a080f04031707030909051306050f0103062003152202040906091e0c 61
    0x104000309000c407002e0303201c0d0550140501008828041103000c03030400c000b40c0d103400d1440c0d400030411038810310305080300074500000c0f0401540340c246000b800a104022380c2d51141c5c0030580b42a100c0103203039181c0e82100c1c8502e0305030780020400414041000a03d80c20300200290024415001e050201d510039502c20354125500710364480c940e0380e003d8600402c461091640c2010049005080083e02c54001c990030100c50745444041c201e4407540c0c640311a4011803240d078070407075150f10002000307000c484042d01180ca07400b40b1a00700048907950350500003020b20420506a038950703280f000c0e8500a0341020226600501184024024400026611f10015418a243d00c84138420a40c208104001302d04040b081010604000d01040e01c4d00360070855101c10444650303840355446424842101d04503260582c807409400309214040303503c00070708003940880c0503141c0b0790606404046500142e03a80d151080e90341c2611541d520904e949403411100e0342c6803d800803401c4041012007007000900324456941 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 918360323 1250 918359073 918359089
    0x1510050901231807110c03010908031506040e24120f0d05040f05010804050a05010203070f0906050310030311070803190806040b0307030b07140319050a0b0f0d02 71
    0x10295120049200000710204140d0561010514005900b81e081070120140000302244090204101010300006110a841401d88201d9503483d20142d0b80030784090b4001a0944030801c90507284500f001050000070010803a280031440003c3e20440e00b490715146140703158120080c96584941541c0000d60b0a040b882060a03260910080c003801500400405143e81c0d00300c1c0d0700c0100d001e132094450401200d800b60081c0d408451040c03507a4100c0c5403c200c01110400c0010f001110a40b29144020340011000c2c000385104000603621000040e0f09c01500821410440d40000280001041403041000c01300d070082058903094200b18484041102c007041c82e00c506603002d41154000450400700041c0b61003880394804c8000d40d01c0c83c00d19205c503000c000c1100c604002d010703419880b1481c100000f6200180072603001d40e56040140f0b20041c079044190f91548100e50b00c50181c8940702050905014500c95903800c202003150401c0300001d442c000c9131103414107604d094451090240140c2c115035030000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 918361573 1250 918360323 918360329
    0x30b18030f040b09030c0f131e1409070905010b030703020a0c0209010305011e06080a170d0626060f01050105090d02063403080a232401030e1510 64
    0x1c0c02552280e07030b416107801e180c0100c840a8806d01a51a090f070003482c1c903000c03003541d0b404001c1144101c084024042c40090022001d980110b044440e0000c203400c290b441903041a0328180e409564a16000040c9418036540340c000d25142d43c6021700501c40403c0344401d8a5000b0341e02d05005a039401280000d0b100e480351088003d40c007015803800803082080640002d00b11b040c004880321030192002103440103940241c05110030030b500c221000c1010494182c1e01608414a4440315031904041640903000d9924030740107146002030020500100030302004606032100641000b400960174503180f6480c00107010301c6000d04010011404404550700e000420030181d90040402d40e03074504040c00b80e0003810003651002d03448800340e0080700d224040038040d03250b81c0d54580e641da0015503c043c5400c1c010682d24a08070b030740e200e0400d507070048004585845800b03115024500d9080710181228a92800a507050349030415003480070550322903000280004c10038a064400c0c041a80e228540c0f0901404641c1c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 918362823 1250 918361573 918361597
    0x18060f050705030c0c1c0201051e0f0d390c03020102130e2e060305130b0a050405010e12040522020f070b0618010b070c15021e07030b1803 61
    0x1d20070a48900025003501044025a40201ca48141d030420518010501b00040e02046007005408581c804510080b010305428005840c1030580302d55075503810381c001480790400341e50707180081c0c21742c040809650f0100718032a21580d400c105810800100440c400000d200510902c80301d01801c041c001c0d01900c0d19040e50582030342a03650344035000316103180140c0b403004c010130240d01c254114420303035950314480200c80d288488600e40340240c11401403400601e02030401d492006040c000520480801d8000d4004c81008112410203083c140e085469a0011103110380c071690090780e00c10a8a03080d01c086800840d040001c13030002d01080914076031082d4042d05850310001d10700d10b4124010000d8040c00f07014031085034056489a0034440007031200300d095516001890010003400070502c0050035600c0c440d1a0100b242661b1381040a00032060080c5a00981c0009443c140700d50901c0400c0c140c80b0300300500400c1003e01d907859604994201900c01c44181c401110340134820381e070400469100000340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 918364073 1250 918362823 918362827
    0x7030b0d1707020141070c0501081503010216020f0a0806070311070b04080319020a08061c050601090f0e190209040c030b0c0d050708151002150408070201090618060f05070503 77
    0x8040ba102c4241700b440d4004801050280c0308903000d44072102517440140c2d20294440c040d6003400010740341c08034003d194103000d10307181000380c0180c1c0340bc0c0003608101406583d80c03441d80000344100485601e0701c0c41340e42e002d2042205c0c1040b443c6800907000340c000300c442c01c0c00128040c00c14250440352058100241a40000806110070000c4806c011072040c40f00c0d0414000b2209000004416445112054800241914081002450091120601c40b4110811941c68504a684c4e450a00b42e09030301c050001980c512082d600c100712030041d608462100744c0509984402e030000d10440507402d0344043c1c01040c00c3c4000504000340d00c80404003454005c901e1503802d203000b41c950300d080e901c0445032500d0b2904200100740e0302ca0080e55110701650900c0c9040d4807081000303083c800711040c0504840f00b140304282004401307001e0300785560700032401010307125075841d0140009440751609034844810000c0c01c0040c00030b00080c0405140c1903460341d1400440108481404031803c0c040c2c40005020741c040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 918365323 1250 918364073 918364127
    0xa0303020901090902162a0e1f0f03110a0905070c11150409110c0f0d021c1704060b1018120206040e0901090212061f05010203041e1502030307030b0d17070201 70
    0x15210103034440d40100688510709d0103008051617045c055440b17000720101c0300901c01e00004498210f0f406140802402e500c1c0c5040ea1000030348261071041d90341d80081240c14690b03605000c495007003078489400503200030904030400308500b5554411881114140795603a04001040410b9200300ca1003446800101c07111000b4240d409038561890282d90000343c072994002d00c041001200701070401042c5a10344012550100c80391501040c80104110342d0599a0fa000c1030550752003040e506a1004e007640c62031000c0520100082c41013a1507004031070030251482e003403401666604221001e0710001030310a900e030b0310380034440c4c2c0c050000900000e41c480c100f65000d105110740091007501c02c040050b512400400651b01d80d03562000240202401a082004180045d01c0b20781c0184c1160b10400407920225070f81d43e61120031118020240c00300507000041400603103680b40c0a50b10460008031400c84900c41c46a8401050181c135903280101d245003c0707808000e41e030186c1000880c1c3e841c8801c1d030290541c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 918366573 1250 918365323 918365339
    0xf1e0b07051510060917010615090e09060c03040212030c030313060c09150e03070b0a020a051630060e07050301140c2a0a0303020901090902162a 64
    0x24888105200000c1d80c800040c04101c0c0441c01907040f641340343c80300c01c0468206611100caa01025038640215922030300b00140c281c0c540100442c0c001080d9980081e4181400f40c1d01070050400707061019150f003e041807000591000003141c0d0460f50484410461081e6620f0301e5055000d94440303034001c0d000200801110060054001001074400c09040160450004e01074650003c507001e00519400425002c200e61806003047e80e8841000804076221259250700400042d48107165540040e0000b082ca1020004200290426600c940b5092050b140c10098216030000441c0103031340f0b0311580c0f03800321509040301038203e030045500b02509000244c4070050f56540c03000c007403040718040c0d8a00030700840c100312081030b840c2c09001c5a03182c403840c02101107071442c0400c2c940fa030880080d00b040320000041c145d00700415288036210751000740e2610700c24400580a40c0807030f0b205602041c010400014041c0c52101b045200b154800c100001002200c407003088444400702c04182204103904020603050307 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 918367823 1250 918366573 918366583
    0x61003093f0c02120a03021515030109051c020a03020c04050406140709050a21020d1a0f0402040516080a240603150504180b07020c060307110d02070f1e0b0705 70
    0x503000b0354081c013004040301d40844d03994060b000302a005170401d41c54407500700d140074003032500070004140402c545c041c0390300081d003161011402181c0c04d03400709030713a108600301142c14081e00c00d4190002e05000c4600780c6002e0344030301d45e90300650b104076624400a020400d003031b170000700d800f8003091410005151142010300000110b000b101e01c00e01548400045c4440340111a032220314510291201e00a03007a4207125094008620403a019145007030300070100c13400185500c1c0304060f10580c0154505003401400f044940162811803000d00e0b40054400941d00710b484a0340000b0034100c00512101c1c101d04185051180c003001c0756040300100d01c006030300d507816000881040c800d100035030240b564400c02c11080340c811484004c02d00034400d40e402e010865a18082d42d1081203401a5000310240c1c800045090b881214010082081c00d440342c480000d00300001c194640c0140010607a180c201660100412500d100300149082c07a08041904c502082c0341e0200106a4058442c0e150385103450515111 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 918369073 1250 918367823 918367847
    0x5060a120f05060f151504120c0e07020a08030f040c05190303030501210308070c0c0e0f0a091515030b0c09030d050a090608040f1208061003093f 64
    0xa22401c004134001e00078021406008484400d00005070301ca1510034042c40482400c2c07814403060083c0400281c10b0f8110f4038401d6894420110200c0e81810003a00c0794883c03c3c0a0406c1d0115440320403007000161054003100e41201141c05021f06c80d5803a0b1600c29a840c01980205da00310507001e035151018511030b0302410542e4403031b0300d040c401a030722440b180341030800340c0d040320340d43c800081140004030f070290158682020151400c4206900b0903150110300d040185e00000d00300700d94808215911450080c40707604a04a98001e0141495a443e50701343c00ca0212007001c0ea03203a9940c9141d40180e4036031104001190b01800c03207076135898801c8280180b074110a80c201d00070302900c04a09140381c429400c035409520661030364411941003540440d580751000b04216021211400310078007140b51509818944462642e44410340e251400a0011402a0210100501d0709203090640000d08824808400784001e402c204250408181c4481c440c3c0706071108105903400710350300c00c000315611141c44292 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 918370323 1250 918369073 918369083
    0x203010303211b02010e190206040303050a2d030b271e040507030201020105070c08040b0318150118020403050a11031e01060819050c0f190906031a071205060a120f 72
    0x51940701f091010284044610029807080041105000003805840540300900a524140702d4040c40d4418042402040b50030020702015804003520a6581c107000d80800c490054400038150000e17100c3e881c00340941c000d10083c000c0e03030709000500f040350340100745074524070903071034007022030802307041103600c3c1c5200d80410390041d420080040d214500440204501035406164185010b02d044188103954002600d00450840ca806034078185106c10001100a80d004c00d000000c0341d4501382282c2b40707002e81c0460201400b03005000c20404207c0c08a540d0200725080800c2b1901110004006400c000d4071040c0c1003000c0b21024025282154154800780503551018100c885201c00620780c040b40303920740d2400034440d90003150504220b0900d800b540c1007031000a08603158811120304c1c91002c2900c0c1d0b0300951182940c0c3c050030802e105058031514007072201c20030354140d541000100201421104840c4042e080e4607180071030f5a549884a0f0400284031018031002d028180d03151a820406118200341c039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 918371573 1250 918370323 918370333
    0xd1106070b0a0c050a02031b150109020a02070503011505090a0212090715030b1f02100c0210051303020a330506040c1d0f030a1a0117010203010303211b02010e 70
    0x1c0e100d00035000c40d0171054203a001907040480e8070140c0c980383c6400184003401c50160720355031032110f180a030585018101d1a00007584032407003004000c2c03a0040ca5440644030343e04042201c641506520b6440d020390381c00303503212a0039a940c041890064841d41a00c0e1a0341842201000700c0000081380c2102500c01240c000b52004010310012010f0b58610005540d10090b002e1004911060f2500742007000d00260065520000e92003090303200b1111803100d142c0250f00700c0030b5038003040d02d11481030560140003818035408070551610000e59414001c01c3c010419001c00b1081d040210b81501210040b41000c4d04681c0d0070505090010050441940c4050280f4149000190500e004452421921241c00d800614030851a41004800483c560140b40c040c000c0350341c850081511004100036160456000c020300c1d501d40300214040180504541c4901d910510050002a070300c00c40444420b10b05402740302580c4407641443c0c0040000e00c00c05601c0f048015914401c0d40e4040d0030030461805c2840640b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 918372823 1250 918371573 918371591
    0xc021216051507080c07140d080a11161b0906120201080c070203210714010e1c050a050901030609050f040b0603010e0307060e0313060c0209100e060d1106070b0a 71
    0x401d00b0805035160b1022441c050001103008200001901119024005001d68260309040603070400c0346001540d40000d010508200e0150180d019500d500c40488003074900d4003c045c04080f50009600d04000d0500820040407840e90003401110707006820043c50410296a460308c00e0248080c280c0030486c0400c2c40000050708803100603054612a036000f8014080300351890444100055a019441e00148001c1c8a45008103074245c01c00907001290b4400041e01280d0005483d14103005203814840310f01c0840c2018203040d03400001d41c5d410244030b0414a0300d840040005030050405600603645581c45c002c00c00040c3c03850340c1c010a008500034808049141c565600b414207892614550105c5503000f0070241c0e0010340303180c1c4024101c00820007542d0911800740c0c000d03d04403d0b28ae21080000d0302d0000d800d800c1d80381402841d600428880c102c1c80a1901d00300c403d95565000610241c82280345d031a56205011092804072010030b80201001d075903840c40d1600200028041e40c0c1c20500e6890403000da = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 918374073 1250 918372823 918372853
    0x6080f0a1b080c19170f010f0510060c0206120c0904050108210d0207020d260702150912010203010603020a18080304030828081509010312030c02121605 67
    0x4181514aa6000390003441c0101e800d1218200004000401561341c040c40005c0100302c85441900540118000e030901e50a0740d040a800e40e8000075207100303001d03d4401400004a802c80303034001250f8013801c04100221150001403e24040c0c0d401811044a45800300301103458444000c0008600480703080015076210440d540c0d4070b0b40760070600110388800f2004283c401c1001c81c090700c881e4200903170142c500a1554041140031110844c00c0714024800300140ea031100e2070608881c403481e0042030f81801d0486640010b68010304e501302d11515440700088404070f944590351460000002c42000b036681e569a00380c0100250b215003013080016008418801d000200e41205000300c1c1ca03118001d5041c2425511548401e91102220890410607035401201041035150301040140042e1202400b41c50496800c4183e07960f61400c4038030400c58400140300003010811566091810387c0340000d803034580d4000a03440c00d0301c0c4c0d1070303080d150040100e5090009100c03180c0d0940860b2148058070b118003000041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 918375323 1250 918374073 918374123
    0x3021804080a0315051806011706100507020f0406080f0f060c0f090a0812040518091507020f07030b070314010e130201260f0114060f0703020106080f0a 67
    0x20007000c5120801840c00428403135008421800450030401c0c05a9595a00140e440c546c0c101c2902500341124040115668208450180303140d600702001259162040014001555a0b00c08030f05114011454a0642d116040200d0b03d92501410401032240c441040994a20100d203a040c4284103e844911441c034001c1aa07a000704059426182030908038000301c03400c0c0d0400c44146c1e4005503500000291074808001c2d03003012506200c0c4035170380c490808e018441500716120480480320542c0e0240301810400003401081d2000b04030400c1e40ca621030030b8013281084e000c44403d04403446000742c044140098144810b002e11601d440801148000414403000704c002445100e4401904ac40041c00000d5440e038007881544c81490001c0c0b60383c648200f8080492100c2d9404031000801b8001c01003140b00020080340948083c408551182c454000000c45a1040c03804200480703401191480c1018000d4004c00d016003140025111000002c010b4551303100d0380710f10180c0b40c444a01c91401048101011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 918376573 1250 918375323 918375331
    0x50402070c0906060c1509050f0a0804051e0619030b0312090301050702011407140706050708040201021b060a0e0303090a151e1707140f040303090e01050924060f04030218 75
    0x11030711284101c0c1c020446d00400562205407070324007601d4079035101c20b5400d011030501540305080098441c1d041c00280705c1202c4a03141c0c6040740c0300d02000310102564842095404982740c2c0d044114801041d40412000303022055449074040c4922091441c10300008409000541b409900030403d565500748200e0036100d0006852128004405c0032902d001e01c103170725034115a907420081c41c1c0344c40c00503900c2c1011111304840703240021b070401303003400300b150b07818001c5035107501591046c00a101120310010741580f0038600c058043c01071524001c0030036141807081c0e41e00140c00070188500ba5a888150851100440702510700144920f41e49510810180c10300e005041442c1c0da40042c5066040d030a80c039101c201800c07103802d1080000000c0740d000d50000041c42d0700d482c0c04044544551552801030314488a581201d009100c501c0c0050205445401c41140e011058042200c500030819140300a000744e14120303150000c60008105640c0805c002c000d0044038401d880d0425900047c202e05401038406071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 918377823 1250 918376573 918376583
    0xd24050d0206210123040c200708030a0306060909050f04020402070302010e0625020705100c0c08150402120a0b060609040b131a030d090506070606050402070c0906060c 74
    0x245040098246940604626190140c052419481caa10b0240302030700f09030f004540081c80e000000151081c910404008590261024080389100e5017000e01108011480230100070f00ca00d028403001281001603600800012041d80e646903070307001d0000d014002e18043c0d040807a107600400650a61540f040910034040c801450f04103884a50800000e503102d48400d404640d01c1c1c440455844806101c024000e040080c90450840d403440f9030a80c4d54a000364480c015908011410045a280c0d84021059203140e4a0003658071001450690b22940981d080200d980c848d88940d00ea954602c61403450160b07008aa108d0340494a07a640c156642d000381c00000c0051201802059003401c080b8003a0a181c0b0b001400445c2c0203100d03101244040e82c84511034070401ea140c03074103214a141c0395151251041000e42c081c220088400002904503500d61180500400000a12205101e2194040f4001d420000c00955a5810030308190050a1050003030b101190315100c0006956405036265209503179103e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 918379073 1250 918377823 918377839
    0x8070501230304020f091302030d090f0b0a050c03040603060810050721110c0a060b01030b06160c0909030c1101020606180411030d0f030c050906190c080d2405 70
    0x403200700c000d65003000c0c0040381c020102501e44c0d445a654007290303611400c0d2030803884890800600415260406078100c80e014000410300c28440075001d400d00c04156080714841da956014060341c00c8a11b8801c0b03495020403130002140c04500706505806c8270007240c80010031035441c8003400300002c081fa601030795000c010440b04840a100d1111031140504041c0c02134600080b10a0750340c401040c19070100c040201581c11005104007046214454403203400b000b071074204031102c1c640022071124803906c19100140c28010100004006136460810060072400c482402489507910b005416010501c000b1280c100003903109001c030354400a01c291007620028603a16005030301c82d403415030914008d0300585d20b20040c1408204651000c100884070800c0035916039080171514034009080390b080309290020041c04012540282d601c442c1074682130001c0b0201e10305151000281035440c1c0304040c900802c601740101d0390700c0300b04c04030303500202c00303d0b4540107546618540030055440402e0b1a02a07203602080d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 918380323 1250 918379073 918379127
    0x13061a040212070e06190309020103150b091503040f03050d0f061202030f0d12020912031803060705030103211b051b03030c0d0305100b030903030a06080f10050c070c0f08070501 78
    0xc680c10230100380b4018140081c0e2860396100a000c0d038026504501049003000034034507468102035950041c0381044001036030070740c1026900c003000b052030044003030104140421030304144109544044407504184208103c2665100000241e0240c4403c2c03c0c2d20a01440420600c020004181d00c04002c0351039440820703002202d10303007100070b41240da50ba9420a030015081c3c008403004000030240d032001c0740004400d802c114001c151a001005020382c080003014001000003641c44072852040c03500d01220701188440c0d0313010403540b490014485c00f4005c2080c508920505c5804140000e1942d460000507040043d00c20916503a4030400700c40c040b4a5210105400b000d510a03840070790000c1201c03402254240d0b48220828203030704280d550140c1e1707810000520402e04102d00c202001000b003000a003007142121080740d91220320b2050348840c640c0e10f800002c1c290203400411991041ea00500d0384203000d44403a4070340e9084402e4002e2902c10300c1074401c00301d02580580080705009542e180d400000c100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 918381573 1250 918380323 918380327
    0x806010e0708270f0f010515011e14090303120702070801060302060415090506030910060905012d05040213050a050910150c300813061a040212070e0619 67
    0x80d038510381d110f50300444107800045901484a4800c0c030882c1400815107090001340140021540701d020f6042c051521090140c1c144043e400072109240d60800c504003809a0f0402c0205108a25039280c0c07601001a11520041400b40070a010385605da0895035015100ea240343d08968179800003951001041c0400c00c540003c2c018100c8031103400d45041c185255a541c045203241d0000c1d141044650081d044d40d1600c13300b40e100744401020b585d48148040e525083c96540200388001d0703258940c20303101030071208404804610b10020301c80604110743c1d4094a203400200d400c0c0314010944070303500ea1080014180303015440700c1d000750761107990214100c1c941440888200420700d0924144a0100c0602010806903165182c081002001c41648081208055092280d500358030030144240d120a200310550094043c0c40e031136921880000d00c60300ca920101d03110690700341081e60310500000b42280d01c0ea40480b030550040c85a522200b0b01e11681c00d0400401d4045c140001c00039084c0c20750b589403d0f034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 918382823 1250 918381573 918381631
    0x20f1204030e272203082e05011b050d090311180601050711030a060507110a0507150905060408161a0711010e040908040807172d070806010e0708 64
    0x114200703039581c49420249803131000e040e2011340075400310b001041004150307543c80048490480c0305011600d21720442e84010000840701c2c0c060749041100c200341c2e030700144c40f040200072005a0420101c0d0188060800010b000c030009010444038881450283c1c1124100f000300340c041c69440043d0b02000d90b031000011120754000e0380041d41e0303d40c014210450715881c18000c0c125220b0198402043d94a40b2180140c0620300300f501d0b10b8610b2380003804900c0072410209403001030b90081c60b03145060791880328084520b00c00700d030001030380035400080c006001000090b0038151841004503200b40300381c0e81e01d001038058500740300064901404202e00c5000030052005170542560504120700242298800b241c102c4080302d1040b244110300144c14000030304100034080080c8030b000d640540700003c0b55042034841d10304141601c0d24054400e400701c450258031205000c00c4500c001154401540c0d0ba004944d110402c0c1b107480010116040804e03c011310407a412440f5a210488a1120042107460000c141c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 918384073 1250 918382823 918382831
    0x1d010e0c030109350a200c03071e050406090209010e100c2402070302010605041104060c060e010204051201020307080c040b0910050d060602062215020c01020f1204030e27 75
    0x510030040d03d41300703000c82601a054010055030342251141e15500360040b2402c100c03018040b140c1c80794039121159503000400009480b6040c07072441e0b010041ca50b1510070044a038121540c86801c109002c034500035181c0c042c1461120981c1d511400b2203003007041c80300c0d80d03880f00c0c10000044c07c4c1e09020004a5220341420421440d10401c1100802c0550b503514103d070411801100140d446036820007903071605020b500044030022085a02c1c151a203840902a140415001010315880707440d6400d10319020f505540040ca00030b010b510b0b0030040180c1c054000e40c0200d5803140425a078801042c859010321065400303076041c481d402407600048030200150218820045020800c040040d00d2a0312080c2c09001e005055540060a050515403241494020300e019481c05401d501071628011580c081d004000840c0f00701d8005a49140c0b410040b40a0f201b156540600124002104440481850f1304d4511850180c0e8072075075142491410000780c1100170049001031100454440c0140c00359045075604 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 918385323 1250 918384073 918384143
    0x3090309030b180105220303051e0c030a0609020405061c06170a0507050909033c030910090503030601030f020702090103060603170a140d1d010e0c030109 68
    0x50035900c0c1d82d40b810011084035240880090110051480301c42409000d4001000e655107500c42c1c94010041302c420420650b014041585440204000c0103507048000c9803800146488211407801d11140c9035142d0040c5d900480c005c0c940000022116200d01c2a5401d48400901641c075003400e40c94200c0d0240503030202c80d6102c5564500c0018620140c201c007480c068040809002090042d05005081403040d9004074064100303401005401c0c0c0e80441100c807401840151944180c03034a0000c0482c4612074031908280755403084e22000c0200440c0b024600ca02c5000c411551130310b402003099420b4072100c00009060b85e00c1400800c04940c0650003008001e4001400142410031a4000542e136070401c2e0b00a0301c4103941c4e48804e00038403a1036079540e62040c02c100c0035079141c10f030303d040c004154103003070382a00007000d80100f25440c0d442a5070f081704958941d041040a11140300400c1c0c98000e1034946030311404c51103000c110002c1070806028144205d034002414074204001101681210000b188003600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 918386573 1250 918385323 918385337
    0xf1e091c2f0a030c080c060412121e020102040e16320f0705010b01090806040f03110a0302070501091a090f0d050a0f061514130b120c03010f05070906030903 69
    0x15224204003034011130281200305010392922501600b07000309141094090307001084148003d61614604100b840e034080c2c050450345951041c00c8641400b50b0700f002904606041420300c03880c0d4150007420580382c8800c00c0c100180c80d00320040a0359100300d0100000300e17642000c81030380130410300c1c0001100141d1400301042846e402c11020074aa12240c000980c00b6070218004043c00424452904c40da102070810748841410000d03c1c980d2218000c0000b849600f010f04c1003000c0510641c100245c14241500b260088000703032601035180c2026004460024203910400038545080c8200c040d001d01c94110721914000e504000c0c0f00c44110381d42911900220100300101c0011001c002401412b401400c1c5003100100515007032040c0e03403465110840190942000f40108590350b60002d40d4154102d070262100e9152454140c06420944030569000041c06483c1e94000c00100d4074a035407081c110000c0020b4071242c11504116003040c0c495500054440b2000d0040340d004c1d600042c13100d802420420 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 918387823 1250 918386573 918386663
    0x20d0305061f0210050105030a0203191703010e040b0c03070f030e0313031b05180601050a030e060a0605030f06041a0c040b0d0207030e0306090607050f1e091c 70
    0x40007201040e071880c01a4000c0000c007132410034912419000d01800c80140180001036000282c1d9002d6503d070725070490000480c0e00c010000020760007102d84401c548100d4503036a617000101072001d021181603c1071000c0100054a4102d4082124800c56060700c5583d03030904d00b2a070071002080302e000340c00007910040200318003e00f42d8a00c900c009500c101840080040301041c1e0544a64036075121502800240b400b42e24030000c07c00f91150302080030b180180d201c101011040380a00642002040c0303030b0103840c080c00368181d0303039401100c16039000358200d424180c0ca1350b40155440c0300445001d0000014480b81122540400f04015006a0021691410141c45465090007980b2071a030f500344141e4009082e1080680021000c2041141100980325a14103102a641c48a400426400030410300091f140390107051401a61060784503003800900150344a03c0d140b02a80c01020064840c20b150814101140f99a038507448505900c0840720b4925014201c0391440030b01640a05002400523100c12 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 918389073 1250 918387823 918387859
    0x813020d0819090f0b0406030e010b10080601140309060a090807050105010807060906020a050705040e01090803100e010b041413020c0a050c1005040b0f0708090907051c05010501020d030506 83
    0x60a180d507540c10581d918442c0050000e402c01286601c4030503904061641048048840b01c03c2c5c8041781d84034103002ca4040440c4040f02c1c0141042030b1140d13030041d4810b681060050380700b01168424403003a01e076540f14005001440f8500d01044904c00315039845440000c00709a11a008060014420f1014505048455640509441003600030401640c04540100f203440c0d444281c10b00100101c1c006003c4042940d01c6181c0c5608142c00381e24020b41d11140b00d00c04a00003544803502650308606955240e0400b90b05026000c441c611500e500310300981c0c00070850482180888045807003842c10b1203035401ca01010300800600c850480c0408170b60901150010030010710401007500d100740c010700384178500c44e802c0014451100c910f00007049020b21040c4145141001201c0000c5162091240c603803050b03180442e0503106002040740c101d540d003424050400e401101618119286641c00c031b01c140140071900c02150390900c1100c2c010b078004900c8c03805150003640942e8004002070032051f0b81060703032145 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 918390323 1250 918389073 918389077
    0x140f0d020a092702130b0616060b2107092a2607140304020409081c0b0f0d0602130b040b120a0c021c021c03020a020d08070813020d08 59
    0x1c01d00440c1d44807810349210486120005801d8a0030506003109284584c0126203100e101c000d2004049659058445041e40c5040649025028820110100e242a880d00e4000f8144081001d806010304955a814903c1c01b1003074448000080e10060107807924241108029000c007004050724080388104180d000c6062810000c00e586c500d0312030042a180c00020074000760035001035150016104070511486540c0854856002403540d80101e40300d840b00e0000400500485000070601341001505680300030000655103000c003144007040000781401d40600c4410350302d50030455131010f010540c100016060360b0182040b101d850400182e2180c81d03c078245c840c1d40c000d401c100700300350010900700701c0c2c41c80c4490115445445014107104145940f54007950b41d001d880d654244111104d519080704c0341c400c0107039545040c1c500783c1d1006901c50014025000758000ca1011006019646c6258145406140710502485444e514100c00b90b48600303a6203141c45086038101d0b4800344094a0001244004c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 918391573 1250 918390323 918390329
    0xa0213060906080f010b04092007060b10020102130e04030509041109040f1a2205150a0b18060f07020a0f090b090112031d06120405010f06140f0d020a 66
    0x140d400c10359082c00b4010340000801840040740015242c0107000500303001301070b281141c161340404500c2c0c09800050303001a983c40c0c4040311030f01201146040602542d9005000c000809031013110164a603008201e01b40e109941d501003240c0541582005806084141664450b001e46000d0b810400a440020b040c1c0303e42c400905240300000c80c0320310b40d91600d44260821046003842c02c0040c07201c00d50710403c0c5a140d03124402c0c0f00b840c090503e030345850034144000100030184802002940381a108852500d64003c4079507020385405000071403491755803400c40f01d0b10044604402d490071100401c11072140d0103004008400d100521014006880c3e0f030384080040c01c07420702140351860400d96510111400024064480d011010040058000d9440c1d40190381d9014130f045032a9004884031404001c880003400703a08140000307030780c446543e00340f051140a948140c0091060300702c10516031007950b040b406101540701d6049400006072030a480200080e01700600141428003c0d9000605620794581c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 918392823 1250 918391573 918391577
    0x70824240c0f010e011e1d1006091802010816050d0e06060f04110307031a0901140901060306420c0c060201020414040504050c150d050f130b0a021306 66
    0x1c1c0461a0b19a8203008103a806034009000704546c0c542091107484059820079500011aa20313140034180a158000701103d02103404101d4407184031740c404000041c2690b21850071007504e0b1903a080d43d4103442c000300c5061560140c1d600c0142c0c0d20740d01a040c01d0041c250320a40140035040018001f10300d0b842c081c80d410f5070280009000a0720345a410300c501e0100e0800414132071032a10714440a01c0600400f42c03a044221482c0c00518030b002519040d015092200ca242c1c0d104100c4030000070300c000c20380340c5003000c400309030740300074960b40d8545064042e07904500455041e0800d10300407003488040e84003036606841e04c03907410310360200e09009403c422105000b801c20010300c0400c0f0000c14000301301c5510740100b18074802145094038000d030a040041c004504988a00e0302d0b00041400e012040280402c0a20000c200952a80610880c813100d03902001c1c099410a06140004986d014008030183c40307820f0741d03115107842c1d10303a42d81c420b00e403e000100441841d90303003401507803050f01500d480900903000715 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 918394073 1250 918392823 918392833
    0x10f0c030603053c0a051906140405030a0507020a030609050303010305160b030a0f02070507140f0f0906010e0307030515010f090c140306030705060c0303070824240c 73
    0x608101c0e0403c200503520858042d0384c44071010310f90742c1c1550a40d000300302010391021941d003c8104141440300303a0102900380e110340c2c104a1034001410440c07032a9148a0031003000700070b125100104000108490107031850304140007801c59240118024a80c01c3d100620000040351680c0e10081120703147c4100f034400ea032001c40180308000080140039010402022594141480c0ca08440e4a0f448000c181d001426180d044580310706840d501500d52940c0e006050b2402181c950310103549403c0d003102c050740701d40d0305064244d5450030807400c0756007a010040d10344185940d4403c015140b98003020310f00c42c1c00d07128107400040841c1043c401c541807136030b10121f02c41465161011250304000e4a8001d0700445140840f00182d483d0451121070001013130300500e5489a80703240010307003018002d603c5241c03c004001040500e228003c001140325a4982d1901151625100d0603080e559186032103090b41c2400c50360020302c44d403810500c1c00c80030310301d01c41903100d950030100c400d201e03150000806c0303250075401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 918395323 1250 918394073 918394079
    0x309060106081e15040608190c051c060b18070309060b180f0a02160606090c020d050403061a061603020c01050c0a03030b030f07060507050c060f070b09010f0c0306 72
    0x12250b9110380040000c224200000e0304102c21540101c03024201001504824080d0380003901c55402401c000c00840b019509940c04a10601740302c6020403000f00d841188114010a161401100d125803001d44084040121603140d524003004104808919500070508018030701c590a80f0b4001600c01c860075603000c16081000c0c03034070206466003103003d5442210f404207118202101007122952106035030040766100d443d0804c0c290b000384100d42540050081c0140d0301801d1200c50b13085002140c510660800c071301c008105003207032070303208189250002501c1000f081000c6542070304100600c0b40851010034000c5800000170300705a200d001403024242c0e008001d1418560180038108000e0002c1c2407803454044e405207602e85480c2e51203401814980d40302a0080541c404000f424141601001259903807a11500b0141694002000468840c8500ca52100e4281411030079501c0c690b01a100d0340d03040040999610314103400c0100f04d95000e65954001403409485e600501c08480501e4070001f0315a41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 918396573 1250 918395323 918395327
    0x305070f0e0a0903080f040606231f091a090a06030b190302090a0c090803130317090f090c120103060b0a0e0f0112170a0914030f0d0807140309060106 66
    0x2070024881800c4500d4000034102080d00565902c3e4001e003c1201c2d008640d40d80e240000040580340c0110000704415000d008140022080b00081010119071540312402c5803040980001050b5845200040342c0e0002004030340c03800c03544052002d072009801401c200e14500452401d03201944070702d0000f034640c10354075401d003000c1c40e0310388541d000c0d41107501400e070454001c01c2a00720302400f121241540d0301000d989592161410380050400c1c102565034926440d5020b27004d05a4134003040d901390350760301e0304940110f0300b0404907084020050085152003088608020346070300014840404003004120340703100b43c444001d126010314881d000001d0503e01041c10310540201d180c000e804003400c00340a1288100b800504541166040100b00200c1d54052600215643d9658a251030322100443c0d50000c03290003054850958238a0343c00b032030801e01e81c00101552610200115800c5400104034034004138480c83c9900d0344030b81d20b0300309203444026101940d00c0c01c0e40116500407003600020011b2014503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 918397823 1250 918396573 918396599
    0x303060a05040207020108011415040b0a020106152c0d030f03180c0b03060619080103061503080712140a080108073002011709061b030c0f070c0305070f 67
    0x10500782d40441c2400c0c00ba0340040c15a01044c05510214400007959a1003951240c88050030450200040760300e403a6508000380143d00803440c190b000d542880030204400d4088032419240d5400e41d91002c2c00c0d192403840c000503440301030301d15813601f020120302d40c00903031203080d8042e81d183e01c2503885002c00c2e414044010200c0d20110b2144c940301c446507506030085410322503020141c40c135103402c003541d035140e0000150f964800d042200303205002c44401000502d40050080c4d0413a0b016060600c540c07010001c420780480c0d4640001880c006080c072040c0080f0b81042035001d08048181082c0c2d034004c3c0031116082c51600103607070240c0010403503001481014424007040c0b0040406002044d101800700701000b140310326410103081600b08a082c410150380c81402e44416024009420080b03c1c248010901d440c0d0204680b441d036040e100354401380c800028102203901c170b24a00403c0a00380030184040124507032000c3d10075559200fa4005c080701049040c003803400182980c840d140d403035500e0000c1c444845 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 918399073 1250 918397823 918397829
    0x30a0c02010506030a24090309031e12120b152107090303081e0a0615080c180a080709020a0813050a0807020414040507300b090f0f0303060a 62
    0x59042c5800d005480d1070002c0e21222099200c0d418501c0300204000c104048102c00e11801d14042c24941d241c4103150300100101c0070749004001c111100b42d1103003c0c9104406081000820091460300304039005481000f44108080200102250082e0300100040c24010301400080c101c4900003186402c5040f5100c860725250380c184051021403401240241c082034a034840a81030200341e0380082c00d14074855a03082c0c9a00282d100b1400c41c4c2c01c11440d0ba4008007850300a079400142e02d401129a064041c0b881c0a110b0411003029034503003464502c180307010840203440e26800c06158040810785843c14841171000c1d00e00c00c0401078542c8c0d0900c10040000034017510004040c004915114041580417039000606030b007001405a1ba6440e51000c40e000340722542040b02c0b075070301d4072003800204500800c4820495140015030320441004e5460041c071003440400d03110102d409000e00c0d100140030b6042c0564030131030140560799105070580500d410141c030300c40c0c1c1c0c800c20341001040002c00e10b440001c40c006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 918400323 1250 918399073 918399077
    0x1a0103081801110607052a03190503040b0415140a05060114030112200d050106050f0406050f0d1e1b1a030a0f0e0709020702120a02060a0e03030405090705030a0c 71
    0x4040c401c03031140c84c0c8070180500602c1c100200024004030304580c042c02c140c0c4c0300f034505c078090401c0c0384601307072a40c0c494220300c1c0c05c8401e401000c1005006207200c1c009407401290050500303110f98440d43e072030600c00740b00c1c2c1122031180341d1141c000e03006520985001900c0f030440790300c001c100391400e900010652168a003080d07201010600040c003003d0201156540c1d150342c41b4405c1402661401d0781c40d1000d40c2c100803065401040482a0010044190420310449200340d800c000d00502480400080c2d5541d4000c1e203801911b1500383d1000ba1900442c4140440d000d2003942c800c080742e0111002022242d40e40035075503c0c2d04809031000c0500c8107c1f100c00200951154070300c0c12002007814074054400030340b1034803040307032a03401002e0034a40076401030003800704180c03c03110320607135032008a4065017028009a126a81100b507200010202140c15400a035008040701d26025808a0980709400b03011006a01403000b4000458517488000820340038a1603912601d441e403034502c030300760705449000c001081 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 918401573 1250 918400323 918400337
    0xf020111120a11270d2103140105010f031104050a03240c050301090b1224090d0516060f050c25050615061c020714010605090705071a0103081801 64
    0x4c420382c00d0010b4603240e0450300d144404490300300028800407007484018203040d9180c000f0380c02c051010f000340307484807407662001c0c001c00c1d0000628042c6054244101030110302d002400c80c0c400ca01c45d40c4660000701d050401141031548aa011030300000841d04102c4180418440384602114907031928002e1104010f028050065030440080441c001885642138603900c441101c42c0555408480c4542c2813140401c403a10222902408000c503e40c1d460010b0b011035052002c100c1401000c11503644c07029080d00c0c2c040c5004d04280f1910401c0e40480d4040da0050780e0790190310748000003402464010b4507090351480e120b15940300c1840c11003500310340c000c200c000b41d842d4131000510040b1302141c0c0003440111440c890350190010a410340300d03002da003408402c181030301185211b605502510700c0c240280d03103c001c0d2805500e0118203c504501030386500103540070004000038072400060100c1c910a03007400203480c01d04808036144031020f80084500701c03c0031660422150310400850000d00342403034110f07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 918402823 1250 918401573 918401587
    0x621020d11120f0112080d0e010e06011d0907260307240e070306020d1103131106120a02070f0219031110120b04090f0b0103020114030c0a0f020111120a11 68
    0x40b040d4482c024000f00301c540c01241e0f080344087c2c00e512000c0e001d00000000e104510454100c0e0f9212182401000904160001c2451103211000006071160000800803d00c00303050000c4201200200c0414108c402d5800b00090341090091010704a214420f8502d01d44101d15141c0ca105c001e0380c4901603a60141c506254421300280c002155001c03a03422500060f61042d84000640180c90501a94405800000140106160a01c420714403a07805108400e8042e01808104001803103002442142d0103141e0000c60003900c00350780144201c41c49203508220394034140d17001c50383e02401407006e422104600c403820003e1210007040c68004080c100c881d01004410080b020707203014179600140802c10f40d1880003202a80305e9902440c58250800441d000b680002d103070011413100240012800686450700e13190116584909580c000c1403a41480e5050034480b460840d15810b41541900456485070303001071401d41c0f594018400c940825280055030729000c8000c03000e0b1107000c0c1da9010981c01c100611 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 918404073 1250 918402823 918402839
    0xf070e040f030f180806060a090203070215130204090302160f230f030105250305070e0907090b030705090f03060402030705130f02040608060103150621020d11120f01 73
    0x154031a0b581810041401100450115044030004d82d000d1512200c2c481d01140350360002448503ca21402c4440344900ca84a8002c00140c0c0005d8030130301c3c0540e0003140303800c001e0059000c0140d40040300c2801c500700010140c00160540b92080011350168101e44a1742405250300da1010014140410100500925000e00d40c803622a01e03140c00500c10b5043c0c0b49007403031961407001050084100800901c100d05003500c82c1d10140140840342803803280180404800e89009008440c400c5c0c40030b448052846600d10700b40b240c050001801c0d20208180014040740f44c880240246000d07a2550381c92a40b594410300601c281c40058903140c603caa40b054040100580d40000d040d410348c1c01c107644000e600c9050340800c001504092295211040c000301d00403134910703440a40184500d80c00d0741d0901a003428040100e200201c2c5010714400213061000c0c090b0301050030820b1070026080144018941015845900d0031075490800110802c0c40020b00e1521419544202640084081c0841d0b8100d514207108 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 918405323 1250 918404073 918404093
    0xd050f090f1e010f09030f021917030601050714010c020f0714060703090f06020c0406050603070906030c11070b04080d0504060203040303120f020d0b122406210f070e04 74
    0x1820b090008014944a012802900302c1114101d4950040c4114607070351a0240c07101086850354030051040c00242031200c80990f030801c103140d802a07001580340d01c40801d00503083d8401001c21b818428100005e60000d400b0300c0c101111080c5d450000142180300680007810034100d407440d114a58421a018441300d0340c01c030310030381c4040d1048801d10f81d00c02c07040c50203551520541c1d0041c3c42030030f201c450020b00030b074010545a43c000e6084404000300354407441000b10350301090b151440081d0308000b05100c107030302179409001d1103c418241000307400d0500207a14a4045250405040f0740d602107003c12582e1020002c0c020050717030908000d801d0a06001000f9601d007d144400340c208401d1400c0c540d084038569200e8a118226040103542d02c00410261401070098030001d42d000d4040201c154071901000f052852404800c80100e40440141c05122201c0c1480585581e40c020720a22006a41c4816250f45442020a203800f5010903014402c0e0142000555400008c0c00d801c0030041000180000715 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 918406573 1250 918405323 918405343
    0x20030c040b0a120b0703150806061e030717011401080a0b0604020d0e16081b01110709020a020a0b100e1906080f07080714060715110d050f090f 63
    0x140004210350386100054180150358409180c0343c0f030319501001484080940e0300c0c0f203003103552000e20400d0316084080540b07842c14070030b420581d00f20fa4042041880c200d00c800d05028082410084c1d9491004002401e1201560203060b12811504212150800a004000138840c400010a1807985041d55180c0c032a030301c0080c001c0210483e800021843c1d90303581e040d50100c4c9440c41c1d0401c18140c51150b1260b07120768034540d4844484841200240070940041c04003281505000d040042241cad000040d10501c0c01280b285c0664001d64001060180741d901c094005100994002e020107048d6043c92082c2d000003034404150010581001e1160440403031b03140c1d4025040103120980260318541440042407260041d03880c40c019078415000d060341c001082d0301660040d0003500c00300741d5100311030700140e044242c407660000c006206c10b070b0101e00041c11041600080400201e00c0000412510070117034820600f010285903240c0074801086002003601c0d61040580008002c1c418140794070f540e0783c062002c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 918407823 1250 918406573 918406579
    0x1807051b010501030606050310060f120302030c240f1314010e0d0e27070509030708010606050316030515062a070801241e2120030c 58
    0x5180800016811140c00511003508000c0209585034600040503000910a840c800e208201080a0505403032003250100d0384038020321a8180d2501c0b02d9200c0f09242c2c4a000c0c1c0550200b4054902e03900c200b0321000e8075040c000f603141c5418a6003804071070100e000141001c00c204a000d4100b00d06201c1d4000d464039003d4001407aa540482041e0526000d401c0c4a090b43c1c41601658000d000942d4121a084e2208801214088401003610b040b21507041010001e20032000468008540003500404c01805140d00160075102225201d48100d0b00750398440c0c1c000c2d40094070002c01c109800f01540c0c2d166241d4000c41c40c4c18052424140c0125103111b6000405030302c0342100041041242442862405801d406880c1102c1003030940c07100d01c2d07240c1c041c1f8403980d042c035420040744d45060442c07400c403c42a40b0607400c00d080a50f08081d4030407245110844241ea401c1560000031070103113103241300044480b046002d0140f07401e0700c4d440c00010070544402c0f4010043c4e113685c1002416a800715a880403100c2c15 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 918409073 1250 918407823 918407827
    0x1303080708071a010611030702210f030a08060102010c1e0e1306030303090b0a06030f080a05130801090312290a03020d0b0f070203030615090301110a0302120105180705 74
    0x54100010a8441c00ca0000d100800850100c000fa4100c1421070741203907220340394410625248417403c0d4513407080c1c590080d070004c41154849483d0003e0b5158105034008101117074044d0528180c241d103154444111100420800020002d03a5030f0b09005580800c501c528002ca0020280d0300c0702124504000d165105021603102c0c031000c07507120130500b0a20b601a000c41405840c1d92414060010040045d060b030b80110b040380080c181d218035009003800c4075449410900c0201c481e44500740329400c459141002c102d010400f48010045140510003e8180b40b1300004a4500c50301d0081d01c100e1481170304c9440b0700d09001c900050b00c0e15020180f83c0c24208411120022001000050f04440450700700a6000c00c2d0510800288081040360a11951205c00160003507110541e060f6a64001100c410342e02c010710380000326201d61241e004e026510030140c000f05d002030076080c001903c3e0300090240310010380d010804a00082c010004140100300c2070b607010000814445010030580401001078081c0040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 918410323 1250 918409073 918409087
    0x70309050d0f0b10090e03030402010f1b170a170f0109090303060302181f03021309020d052505040608030f0307140f04090c0509090f10050d11040c05130308 69
    0x42141c00d03042c1c9a228010070418a03045450603900e4600c1e00585031203d00d41140303036448036000411280a140c058442030f0001c0480c00c1d0441310750301c8105489400d010400c3e031200001c3d0001c0310340961149100c403013684840c101e03000104011240d08503080d0000d0b512041c4929011000c41c4e40d8150381c0c403132070f000c61141d155003025030142115600013500715200c03060040981c1070904a00c2c0c000d65034016202c0302c072150b90211000303141550001951084081d00e0824800c01160b01c0001450b1000c0d1044280038000d4482904083c4852003604001d000d00031a40c110200000e84000505801c0314100410784c01d00e45c030300c0d136280907001030038031507140003c007003002207009240800071750b03a038002025030b0703403524920a03241078105104002e2007509165519000d9130048007583c3d611036018022550310380c4c07044408104040b015055985e2021a07400c0800c0c162513012401615078041c0c0c43c00f1080941000c01e000071039120b1007141c02004400d110203407000481c4034644081765004031489850381c02c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 918411573 1250 918410323 918410333
    0x4020a0315090b10050a17030901230d0b0a080109080f281e2a02011b03050c060c0309070b0a093b01141c060213080c010203070309050d 60
    0x400c280d40030701410781010030805482000e001340741c2030343c10a03140401c24565030743c4526019003812000580e00c0c0c00510100036035502c01c02c000144000c4008924a6003810004030b42455841303451001042522103269480c103043c425031950003031403080005c00900d0f046881e00401c9008400f0083e00c03074440000e0f1004c04158600084940b42e0304802007000e2404000d41c040d140000c00420600919410407503034031802d00030070201c1e513160300740354010006503501c850950400403180012810310810405552500500c00711040e1103901c40e88074527a8500c44001c0e01882c0490041903034810900c02c1040003102d80e400f059480c101da042c46441600c130180e06c24150303148011500072400700900c44041c0702c0b004e0b05001f200541e800c0c01c1c8800080444d0400c03005408102d090181d199500c4440d025000b0b242090100510062500069454010005c1d600c5a090f41c0c0714500c914861132001e00d061145c0c1c41e00b403009035801d0b030703090006510300b416655000d05440740a01c1882c2c4a0300b10030341a0800e00c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 918412823 1250 918411573 918411581
    0x60209061201080706020709050610050a120c09030203060a0204060e01080417030c0d0507020d0f05090402120901020a081302130506030f07030501020a090503010614190e28020304020a0315 83
    0x4402240507034296854841842e6030300070600c10000180b04040b00041d041c1418410140504000380200300c8034404000282d40641c40300c1082070801a0004400310320030041e115242e019283ca640701400f091079401058a46040a4400040103204105c02c011f0346400607000c0071250000e0901c0146a919820f0500300039204003c00320307100c2070002c00c01103421070207402008400c010513010442519903410407607941841c07210301c40200d00d00304182507c0e940a000a4440c44000501c0946800e0203440007940700380041d00c404041d60740210380c4480c45900180480e9211648a202e40071070101c58001428030f550300c03854038612507912804240c1e207440a002421813040440f040b40c1d011541ca00d0700600070f602920014001642a020109643c078060162100311a58200360f4070240001d002000340070843d1000c61803004440e1a0001803100d03264916510800d601c0c07003020000341515018061500090320f000d0556841001004010f82c1c03107125010640b5000883c444840f9000b1081100034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 918414073 1250 918412823 918412837
    0x304181d0106090506120606031005090c03030c030703030b01050703140a0c1b0501030605010e0d081b0f0d03140f0406050402040b030a0c03050d020105040b0c0705070302060711010908061306020906 87
    0xd542050000b050481c0b4a0300130600074041541c8045046080c0409581c503048240c807640d034141c220000e58200701003a40c000076040a840000e48510380d45041c0001d1030355102203070003c11030304042003a60500d60184140001c0100070308146152540c107070b40003031240706134201100200c2004165907804034401c005840d03207079502c42e2a080d0121700f0008002000099803113403a00113810030401080d594412055000309000113400710011080580c0e8241080d04003d2031101104181c6044802003401000900712000590020380340140aa44001341543d0f10f140ca41244e41d10704809001581d6030001009500c00e0f048840082e0988035840010003074446802e24544c1441140c044400340105101c1d5141242d1040045401d1500e0b41c03c02079081e5202180e001e030000240f82c0006604d2080c003401844001c4c402c5068505494032980014000c0c1c202180c29102ca0b0980702c1e0904095800442c40300c00340401070020301c00b41c5440c0340c1e0541941c945d207000a00070380c1c0201c2c0340311007a21840256000e03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 918415323 1250 918414073 918414131
    0x60b28080f21070c0e040b070e180a1b0504150c120516080d02091f0512040807170c060a110a030f1104090e120702030c0628031d030418 60
    0x4c59542c0d20341510407000380c0c0c0550b08140c55101092025005075a54510103001520140d010000325240845486000b007104c0345c0700b80c4a00074041000380c01e0442c0100800035486450300e49050004111140c0303c4c0240c094148060100c0380703004110b04094035111100d56191840c0c0e0380d40c00f81080000c2078070800f0014100d140201c0ea528000110b07030050040410141c034150200164248140181c2039090145400f0960400c0040c0d0000c0d021600c0c1d80c6c1c81800b80910398500403a641e00c02404c1c080d5a2107000d003051002c10765505100060142d00d4000312004402d200c007001035a000b0b4040c1c411800704c8400d140e5240603e081500281e084030300f40d00628080a40c495a86100d4480900140b07120041c06025901316401009100070550b00306980280050a48518071403d12810b41d008192050078201605030511400c0c1ca284401c121003a01b6540101304001420b00720b00f01c18840c906100e2080d04184000e009a580030120142a880300013004241c011201082c03140046c009118845 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 918416573 1250 918415323 918415343
    0x41d01050702030d3b15040c09060b0a1d0a121101030b060f04030605070e06070f020108060321070f020d0317010906030809010c060b28080f2107 64
    0x1041c1c0760080007a1021280c1010140184130044a2030081c4403c00141d109401d480d442d0405070004a0000c3e1205801615044813043e04801a040500c1d56048030122446490b244003032101018030b00940004118803603c075400c04806030000b80618a528807141c07184443c4060000ca540e54015042d030040a106030791200d00241c3d4100389014000809401340400c0c00c2c8000c054107420b00d4000c0b204030409404105090a06540d2050301600c0b018042000b044060b0111550540c0c0d01801014800e10826030081405524400034001c680300400d0b44d4441c0e0021411040042c82c171000381509020700d517910030342d02c0489140c140803000381c149001e500611070307566034000c064000d40c0d49500072020034019201d5070380c1c41c0c4400c000e44401c2d000c0280140307428000f040c0c0c80e50049032002281c0d8480d000215030610924040f914107405080003111a107a0140c051406013100c1e00408040d10030600905910481e401d20b11340d42c2c00301e00003034100d030f190409904400c5882000c25620450342c0501070603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 918417823 1250 918416573 918416581
    0x3030207050607051e0306010c08040e04200609040e1002130f0f27092114032203020a05101a0a03050d0309020402091c050d02010e0c041d0105 63
    0x10000e4200c40c00c12546886900c010444003070156042d600e80c000b80c4030032103104041d40c50200001e904042d0015041c01140600e040001e070416000c4c001626030210181141d10345030520403c200041c00c06803015022840340d0320495140d80d42184c845e0031060f40c0c085101400c04071401d00e0440c5c020341c0008018408030301050f1940c001e44d000c44c1110849844001002c0d06d0740080c05070131096100c0da44450045029024460f51207085d9007128010300480020440202e4070382c00722488003506d0400b0000c0e036081c0754054003500b05150030881c0081240c41419803400c00d841c000f51200321114180846222a1f8281c1058030811032040c8259101060310a00c9100ca168003001e40b940015000418004c40d070302c01814140404000704403030b003140040c00f20103130030641540141100320f003d0380c006808101001c500e4030388100740c6081c48070055005005650a0a0460815003080e501c44110390500c010000384101c0001c5101000e9011580042d40300003a130316540300403600314080426542840100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 918419073 1250 918417823 918417827
    0x1a1902030c0d0813140c0d050f0d080108120c03071b0317130506090406080a1a090f03120a090b0405070e1b1b010b03030301030b0a0614031c03060b0703 67
    0x307019103450820860308612002d24096441840c00c5600c407180c0003c1c6080c1c14081818103090756185c40f100030642c1c207810381c08404510034241841081c3c0b41948a01c145c1c035880306040020011000007403909682c1e0307504101d081d40c1c4032100b80b0030040d0460800300f8032032442c1c84140221064540d005c0140c0e419454004201c159a20f5144019103040c0f01e03803200102522020000c580d4030040740c1050f04101400e10003000440d070800443c1d03980042e50b41802280301c94003001014842d034002c0780e543c022401e01540003800722400404002a5402051210041030400415210010340c01c41031000c4546c5c9520000000b410450000341109100300140b1082c0400401c04a06886449032031040640e40d03641240c0c9150650320140030404401c0048000d0207845003003e6409a03d400004204c0121507000a8919002138005582480c80402400700318161442844000c1101e100308114500007840000d40700c0346150000620508504d0a1809080c0310742d0005002c0d080420440f0740303070941d038240 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 918420323 1250 918419073 918419077
    0x5090910051e211009050318061606051b031501170610050d0905010219030b1f0c060b0307060309060b0f0a051509030a0f050c0405060603011a190203 66
    0x1d054041c41c00e03144080080c44071614140a018005040c00c0e18550791039802e100c0da070b0b010340354651160203001c1380100d4014070341c012407016a0084000f1038aa94000f02500140700d800c480b0396220f0a010070040702030040404445c0a942d400190001d040d9850080c01c0e441d18030300d0304100198400000400a00c00400c86805210020a036221507884130360a002076040e440549509034010760350320308407086d0740c4544d00500b00e135a14080040303517444243d030711282aa0010010301204290030780303241c54051352510450340c000030200d4405900c890344c42104400000b100a00c4010000122490028020550000615a031001d401c0f03070032080d40c4005c024010008000704071007060419281c408540742840b000c0490007001004100003d14281c1000b030800d401c040c42e034040140c03d0209050f59038043c0895182180a82d060304a01c138911b182444c204500e485800b032181c1c2c9490144651601d400042c0d80c15074003100030f00030300c41d1159100030405018a1101c004280c0c9040101c122076070b80800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 918421573 1250 918420323 918420329
    0x9060708090111120123030705100c061a010809070e0f131b060e1203040e13050703081e0a080402060a090503070308190c0803150f13150f03020a0e0705090910 70
    0x4146d590504920001026141c001e946055169000c540180154a060040700304642042d040007a003000d650358880090381c0381c00100d580030f0005c00031203001a580044085521012260213030104506011800c01e040d80050710b0303042542e09400c0041c0700208040e42c8941c0d41600803580c50032003c0055454401744049019800008102504c0c50a00c2d01780060040c600e905000003950909084c000c80c00300030031009020a90220400b03d5501c0450303014040b002c040d5000c4c21280da607810003140000b0052609540b01c0d01c002d1002c000b500070940d40501001d411641c100c4200e95202d84004044524806903004540d0600034408000100702070342c1c0c02840088a40195003590302e2262200380d80800a410010340a00000c000264804000514504407004002c0204c0b5031360081c880440c1c07084c400b961804201642c0c4801d004103c00050a1060040c41ea07100d00c410b50606540c04110001d1031071040c01c062802c01e00104090700d0148060381c88840e800b42401c5074920307080304000740d0746110384 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 918422823 1250 918421573 918421589
    0x12030c0b04110d051006050d031409040207020604060c1a070e09093f03090a15090c03051005160906030f0608010e0a11090708040b0a0608030a03061a03090607080901111201 76
    0x1b4400219414100c8111840a0b050b0315855800e0343c401904042a5101c008a294000e9007013041b0740040e69450003800107000c4c25910540303100018500403022502c000503419400c00b01e8020001e0403640b00300001020141551400700c2a10741c292464034210080448070030140e12040020419030304e003105444581c080500e1403001e01148001d2200e1803200f9103a440142e048031540c02e004c07a0640c815000702116141d400101501d2584902002d0b0320b26030011030300c50300305990140800407207028164000ca8180c00d810707400c00d494000500111070601c0798506042d01e9000202082c0364651203000101500c030002c3c04802448241c0c29242d0140000890303a04c10115221a042d04180c200d461044203292603040b513036151500d54042c581401031000310103d403103100c040791149c414806030890031701584000c5092030030500b007040600c602c8503420f040000280104072100100080c01900040341d0704180350745454224044d405803c01c5180c0c1d00b020000081e0340300030700d440f10107101c1c100c1d102d032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 918424073 1250 918422823 918422831
    0xd020f101406100207091503141c0c1a100302030607020304050901060309060209181014061b21030a06050103021c0203091f060e0112030c0b04110d0510 67
    0x1018000c12611030496010031000300030006015400d01c0100e00d544144640125a81542e88090311030540f648180a40e890341c100000402c01c2103900074080003140c41a0000d8503020002c0b54070844000c40e218401c1d01003020825141040c40104182505000722640a566903442e00104200310388629100c2207000784034100005221900c04000e40c1d080d500002d214080c2c592070034204601404a803242501d071140d003004074961654429051540e00c100740100150589030030079000c0050351055000044c00a459400781f8003030b0b03480008581e8080380201010b90400c2090384054a03204000c1a6600f8001c0007074400f82525001402552182c0202142881400e854000442c1a070280d540c5814900c5401c031390310662291280c015544c020103a900b01c0e6400074804421100c0340e01c0d2481d4030546030380e45800c140220304d100c1d6408c034050521003011182840030780e40c000381300d02941c03003020300000d0303103000407508020320942d03581e81d0000014111030445440d0700f4095125140400349016003454 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 918425323 1250 918424073 918424093
    0x2030f0616091410032c014a030313020405010f03030219080c070b090f0d02060f0f0904021b0105180a11030c150a030605010311090409050f0d020f 65
    0xc01c0c440314050b03c407031800401505044405014440101001c004241512115001082100141030009820f0070360303500b91a2420001215084402000d03e030b050f5050310440b43d0340f00300f145885003115111101e078095801120400740d81d41481c0c407030000a000340000010f010712030214030002a4414000c070760821540c2d9882c03941709141d00c45440010b0244c0c100b5a60400002d0341d0fa240d0206050103100c81a190881d001b80203030400802e900909002c600210f01039295040c41c0d004d444d01c2e4002074815411619071030300013508501803140008245240007a543c252800d101c030a484035654081c0c415074481b41d01d1010628140c60740650039800358030304030000e441c1e00c01c01d8601c0458101d1300da0140c00b02e00e41d00e499071500e040c00c408042e6090312450644000d00c0d203550500450344c260100560380c48003040d090041c00d841481c0d01550406081106014110100104031614103d08803130004401c956032401d107060500390224800640102c1100340b18a50300481c1140d000301c10401034030f0307143c0a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 918426573 1250 918425323 918425327
    0x909050108190204020a02100501120501230103080c19030801170d050d090201020a020d0b01032001050a03050406180b0a06090e060f06010c080a050a0e0111060a1802030f0616 77
    0x1c01d0b600c8000c081000042c081c1d025050030b900030070940c0317050301c1a00c3d0f10f8601c5c1c150b01002d0b14400ea10400b540600c400e00441804402e00c00c030b061006c0c003c403000b8400f4100c2c25044165403010b01010748a4500020003078000701c020001c450040d1100340c0004049145828041c040c030900b40f04200d908001391980082c0e10b00c0105d21010600c109840382c07400c003002d40c000c40340181000d181c102e06500c691811040540e4413650b03003c2049100e80c24070b19a545c10351170060801c03513641c2084e080c62186900104a540e070001d064609500c03040c80e001500d0340e240d048c0b41d409024842807002c90081c1c1d1802c0042400001c801c2c1c07074450b00c43c0d0801804002e07500c9551004440502c15584919003096010500b075480381101c00303030042c0051410040c10b51060f20b42e1102075014403284404140c000610440468000c1090420240d00342071860700b05030079540039034881c94001c1043c800240d84480c46005480031914030600550094100c03010407000900e400d680300703000d40e20341e00603040140c0000c0500e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 918427823 1250 918426573 918426583
    0x306010905031f021303060f020a020106051504060c031e030c1b0f1b1802040801060e0c1911072c06030d030c050702041b140406020d050c1207030909050108 69
    0x20103e0300503c0c014400c00b04550000e401039001d043c62044555400000b01c0d80758002c0504140100e030006946142001c4040e0840b00d071a4021806140740342400340d0440403502c00e85080b2421030620703c1090401e8a400c898001980c40b200e103c0300708002030fa400541c0c1c154002c0101109503154100ca8003010f1a101155034610100100b090000d04254000256011004804448828213000c2105d803a481c5501c4d1140305140d5880102e41e0200381003082d20001d0090700d000300040d04800c0c00038101a0403144151190130003010400c5030b10300045203540c0c821040001114110030607910602e0721042804890000c8400c03d00c4401e04460943e00410300028006008030340080c0102502440d1441c01e90180034419019402c0c42024011500962a80d002c1c000030f6010101143d100b810301350902074440d00889501078032602c428030080c08510b40000e0045448042c5003081503d13000041e0440d803501d4000c0100403050180401c00c3c40030160003054400c04e444031605c0074045c9a0704c0d00f040950711 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 918429073 1250 918427823 918427843
    0x90f1208180307031103040801021b010b1008060d050705060406050c010f15051e0d0f0201030c0201090305030a0b120709020a110a0b010e1906030b090f0a0210080601120e03030601090503 82
    0x942c01c20859a00042c1c001c0c40c040391500107400580342441d81e03451f40300c3e013260001741c0b00030f50362805080031250440c0d00b84680d028404c822240700c00d48181041004001160080607039020752010480c0300113114013000140300424008150540d04c40d200c3c40020a1741d00b281c540b4409640c00c15070900e28402e00c2c1d0107002c5004502030320f001c07a024541010011f25000401190030b090b40d28612080007600c41035140c80385039020300800d45110342cac01c1c40010b0407202c008007200c045914003845000041c3e4008112600031413881c50100704840f6890020b50300840f0703244482c4140c8113034107000510742d0507078000d040c420303c20f83c50704c0c0c6103400810105030312680c06603402440700c0c4190005000401e401100c2581240c4d0740c00c003400c00d55180d41078803003c54246800954030251128100442910108044254022280081c02c2910b86d540d02207075603090040307500c1040c0030300840003490a900c078802036045812892428014081d90710011520303640140d4035140040c4007040c0115407810300080c41e01d84 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 918430323 1250 918429073 918429121
    0x33a09050f010c0305040b040f060f020a110906130f0b311a0301020d05091002070803040602031e15031501061b0c051201050613060f0902090103090f1208 68
    0x403407150240116001e07146040d044082c808103100c04900702c107190014001034042d00d42c0001c031050800e840600b559204940c1c003821944041e46120008919244140c121007003920703d0b0300262541c00029040c500d002114400d1645404030065500b9956003044c1114001980d8160303807000d00c1440c03c58035455021161160560107100d0900c19101540040070900c1003102140e8034081c0000040e003a03a228020302c40c0525102c0081c0321000000340728200d80d032104c800086141c5107083e0780d145080c1c04002c2c0f01905042d03011001030560348144100010900155031610403034a007480005c401d1520b400c22241c000d01ca1942110303040d038200107070385050322400d842d01100c0b1800b40c0d9668410200400c0c040fa04101148000101c9407178048541018600744400440d0b10b180c0481809007842280d144c0007182420400200f0494514005840a4801d03101b03000da41e504905005070082e01501400800110b0200301c42802d1000130140e0003a03c0540c5c1c0d443c0d65a6881d1507e82c0b0807440001104946 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 918431573 1250 918430323 918430339
    0x6050601050c06040b1509011e05040203070f0c060603170301140105030606043507090b0409170a05040f150e040e19021504080f0d080907060e033a0905 67
    0x1c0171400088500f40d010b0141a41e0142c003005074004208416800e0380300341e0f001000000000c90752980410804050300080e217085086240c290340092a05d604600410180300e0041180340510009400400140d030304440080c200c0301c04d00101420030fa000b4466548d0784000381c1c020782c8240d031180c01102d000b1880284203504241c2031200700360130340040401702009601000070305805c00d1110000c64080c0d0701804090a011841e01d8404401d8071400201c19100b6454221040c001074104031024851130720300c0c504541c4581190105441ca80f240c1d070000714400066820008207100c548001c0c000c4140c09035903030740c06c1d1500301c414031040d14410b240d82145a088040560703980070122a110200c41c4c00203003241807441880100145c0c42c0e020340c2050446800c11070000c1d03038040b410822108180396515003820303149070052507240c80d103115015140402851040c020150f9500f0484400c0000c00c0940580d0740d6484020a002450b01c480301c1c0040952800308540c0b425806076030310074215071001e00784807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 918432823 1250 918431573 918431581
    0xd1e090b0f1207020102090a050319030f050d06030803011d0f0a110f040f45141302010806040207030504031e050a030203040f150f1101062106050601050c06 69
    0x4440750080d014016510360188036001400008101e4103004440a070001a0740f0301d100340a2100034402504000c0c0250b0010700c400b401070722403150803040a6010300d81180d0300e0200142c203d841b4481c0102c0c813020182071240200174011501c0c0158101c40721110481c04c1c0190540c901c01111000b00e400c1d0f000c0c0c941000c00038031890308d1360f0084c0031a8400b0071030991500c05036031a21030440c0c01c990007051062a80c1881803021143e141c9504002c07101d940900c0b15408445404111002d882810249030302c07032001e041c22007007186a000425410b40c848200c84041c60200c012800025155505a00142c503810216030907003080d200b150412074255441a14040c03c640f00c050210007240c50003052008500700745800304200380100801c040c400d501541d070340e5140c030031b100e0310b4a0030542102782c803d0510580e42c0180d40d08400003c1e5610300d50304008406615250009005080f16801840d104003881c224011560030134805480c10f0b40304050401030790720b99100445280c0130b4038000c102194041c101003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 918434073 1250 918432823 918432839
    0x120604060606090e090d0e0303040f1e0e09191104050a0b0102070b1809040f1a0403080a0c0903020904051006090b010306090501031a0c072f03120409020c0309060307020d1e09 77
    0x3140301024060b0440c0cac0f0302981d4800900d803c0020381d00812143c1044c0980e243d0303d00c185000300340240200004542c1a051841c862a1240300510307491a0ba24212003010041141070021398442c500c0050042156181c2035080c40090701140c513049005025074000491040b50300303400d89a1260121140000e5659003c09110f8015400750040e00e00030071000c2c003c400542d8400e0926948080102c0712038440c00d01d40b401500307000028100011107820603004660700c0d98048155401c03617070101d03482e42554485041c9a1f0400c034104900c819036074140300001c10031107404c2c2c0011881207003c1e031741084659550016a03040751b000f03005c0108111212046c0a00e0f1400b041500c5400c1140d1840300c9113068000e079540c41107030814013083c80e024200c089190125180c144500d8030000829800340400c410610300a218910550061240003980410501d5282d102081601c9007540003030080c80e40c134180260041d40e245800340c3d0b443c001a4050314000000c010080001c507640000c1e07115500c07007134101100e03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 918435323 1250 918434073 918434087
    0x106080a330518010b12040303020d06091d070e060103090c0b03101419060f050c060408092404031104090b0a1b0207081209120604060606090e090d 65
    0x80400481c0601041140c0d10980400c541034601201404036845240500340300d20140081100c291400c2c10300300401004421008445031001d100400507100e51303413440c0a90013401065440d4004900d0150003080303039281030781710200035900510b81004a0084008041c1e440c4940d0160003400c09040000c2185940603170009580648a4501403080c240c580c0030604540c0c0040b030b002548142e041508021410100c00f070a011945d041e81c138480d07031006264420001c0c40180c0710324000c10802d6030281d87c1031803250080e52a1840040252102428a400c0c0400c181c1c0000f00c11900c640c96050394000c2c92a0000e0140d481c0521404c501801e0a10396200c41000e0080d805000c1e400a4564003500c0c0000c641900311885141a0000001d040108407c180504403d0a801070107540c00070f08103105890300051040180c0f015010300d25580e110710310200e0400f1118501002c51845110b0601003005003540100055800507980c07080c0c0c80d80d0310b54041c00019810b07500200d16801200c0d01c80c5103240303e213038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 918436573 1250 918435323 918435341
    0xc0210050c0702120d0810080c0112020f180f0a031a0703090b0a020c160b070204090c030605041a10060507140c1f030f02042411030d0516080106080a 66
    0x14005003040043d401081454807000000b94442e0010382e01032083d681c0004003190411480306400b440f01e414100507039542c05130011094107000402d420388040d140250121681c401d01d650a4645030720200000c10051803040360f8851003200700302c80c001110b061081e0686c0c01c5179048084018080601c000c15101580040d00c41400c1548492850011426000c645401041c00340401650740d01e00c2c0e51080e040c18101003040481c0d0601316810001129554280c0b10595012540099240c55a01d0100d4030645c0540c40185080c3c00c2c881003206015820440810b80103561511708000d07a101e00d004401d02c0c0307443c011031010a5040c0005000f00c2c4098950045d0103069100b03c070400c0070020b00188000704070f01603407402d80484c405404a01541800342040c0551090425802c1500b0115400802c1410001c2110f01c0785851450b00300351445a034102c00036000700e009a07552031801841c0600a050200d604407884141081c072985100d00c9651040e040325015075503103034251203062181001d00f007042 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 918437823 1250 918436573 918436591
    0xf1503010303120e16051c081813090b06090109020306130504150e1c05120103080906070f06050a0605030303060d06181b030b06060705190c09050f07030b03010c021005 74
    0x203d0700c2408050410210150b0b20306141d002d1704d45840d080420035442c0ca0f0020f1503084a03004c60405c030004804000390f8900340c01408032581480c21303440104401001205100920a040803000010302101100f070038043c402c00d8030204c1d0030b0303a22500880d090f0300c0240d901a40000d01d1030104c00c0390380b800340d0109820034403503e4038070810f42122072110f094590310350010500390070059a4440f0004e000030750003104049030030701e94144031005543d100144814440134101600028007501c40d42e98010840d943c480d482280c4411074015410a24001c0800b211400c003c41e180c45008121480d002050f60311520b00100f03140e4402c00156950000381900010022402041a142d00c001400c40514024003440300700720080e400d859414020400900545a076003d64002c000f4031020840100720b4041a507000c4100320080f154518000b118003c05501c02c1e00e102d40b820b001c1c4451070040d001e0950041240340c0e4207100355200207040500b00d80c0c140304002c0140c0d0000075402d2011185400181c0c1c4440c0c05 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 918439073 1250 918437823 918437831
    0x8030a020a050f0c0f0d0215060d050307140601032306040f080904020d090b0f060102120a0917010e010f020a0504091505030102070b0714040515030a061802090f150301030312 77
    0x302d403e0341c00d203410548103600e15801ca4176150880030b0040202611b108210b00c01010040ca807420180c0680b04083c120302d01a4440e2058602488000c104440895a10a144251340340c0b05032034058071500d080c08102c03a85550512030790b02c140902c0d080001040903003009440740f0384840c3d441c1c0b00c107100d074000c04031501c24061100c00210707500e03880a05000012140082036400341d03844c1400d100b5100510b600d181010000c2404016640024100702c00d00510300000d17130324031200c0800d640260081c1d11010402c091058880001320064101d0101c07482518000c5c82900354400e00c08060340036905128002800c2030208200300c4480e50000c85040b52880751904503141c469000c03d080e41d00c117202c1610006120424080400d41c080750042d1078108140e01e09080604102c000780d032220f64082e40c0d050501c8040045140050307140e00220082004c621120301c1354000b140ba40020b0342050744454441d19900d002c01d07003103013005283c0c40c0940c039001072210710f10782c2990b41c2a9900350baa681d130010302c00d03030b9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 918440323 1250 918439073 918439087
    0x40506072402040302040b04020c07060c05010b0d2a05280902220602060708181507031a0f1c1b03080909070c0b010e0711061801060503070308030a020a05 68
    0x70a2031103280865805016941ea030840c01840251181110f14a01840c41040180900500030411200b90f60305460605040d00303081c01c00c82e0140c41071132000f079480414641480300304043c8150031100d00c0132207440210005c55000c660710f0071156900c280f80d003124440c403410200d41000e681d405400d84020382010f0320309484100c4007040b40c201801401008009a10500e20889414005001400d0318801412203181500000f040d0f8039014041d00380b61010461200201d00043c8400c01d07030502c160b000c805d141d10303041c2c000401901e0344080e49103c2c0c9207580910f0f1000d0404154101908402a0080c2540c1d00e005d160308826000000d0141c1d000c0c203041c28a40c1a600010183e0300040d40550f15440c1c90303800d01c008100c0700072006088101484030b05012640004e01d4a002c080c110307540e10401000c180d603a02c07019500741c6640b82e1042403500a040070000420ba80d00084a40422400020442c064031a800d166503007107a0b0001421810003070001803010f1f85690000c250010381c901e001404c04603 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 918441573 1250 918440323 918440363
    0x50705011413290a0c060b12030a03050a0e160302090a0b030a030c05010506012607020304080f0f0f06010501021002090f0a1502010506040b061e07120f09080d0504050607 75
    0x6001c1c2c001601d25100007201010b02c40d0426050402c1c000d003055204e1030f242c0421405441c201e400c007401007030641c680d1072420f180c2c0ea8840352607403400142c1c0152075442d031031610010000c00084074070102840ca003080c1c11000c003d0001e101494065281c84034290541541c007000303a1640700a1842c0b41a0741c650a1404003520203001c03006c012071181c0c0b035172150503a03103161242c255003000b4601030402090140c40c80686412914a000c581001d282030f41c415206d50324120b0031031040341c1200700288990028940d00f602e00150f0035102054020503600c0c0040c07103198080c2c8521080c40b4072401a44030089142031140c80da4000c18a01400404e003020030303905034020482424456221801c002c0250420b000901d4086c040c440d8003403402c403004c0016070b040c400003d81c503005042003041c0b05414a0025207142c05204100d403c11034200c034500da03214540300c4004125822101c0707940001a506400082c9888000a10405441068030340c0d50a01d8142401c1c0000303074008441c2568118003000c10001d04c10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 918442823 1250 918441573 918441607
    0x626010b10110709020307051801090b04060c02120a02031203070c0b16080702010b0319050109060204080a0c0e0609010302280920160303150801050a02040608130507050114 76
    0x40307075a1181c684035900d0740015800c1002c20303840382609600400c01c1256241d8031000311200114940c08a4610041040c0100c074840c41030380202480c2c4200080102d07c2a40090b8005c0f100351003140d03940840000a071000c1e448030004c402c003d4041d406050421a5000904065580859245417a0550801d661203490040c1010360303442c0060424405901e0030141c1c0034a059501503001e0001744000000c500c04256a200b00910383c1e03103404500e4016008000084d005480d2964004109640301d903214800d0350703144c0000c0381c405c0b070b015061818001501c000000c00248075030001804169283e185800340003900145030a10340003400b40b901c94180c1d1040b14200c44001c0c10051800140c21b00a9141e840c0c0c001480c600600d00c182000d0004c010b42180d0340400e40ca0304d0b540740c50017244491001501c1c2040c5501034000601030350034801000001e50033380d4090412945503640705415a10781240381512041042030140440c2c0044800340070950088200b2078240f8140204170385844400034824040c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 918444073 1250 918442823 918442849
    0x706060303050d0b100804020910470915090402030403021006080a02130b01021608060f15060a2d0914040608060f06010e0a1404050a0626010b 63
    0x1203500400c0144543c0054480c0c901c90f404142c400450a055880c030290034041c000304003d01c20629040043d40040c443d485120003030801590080c1040c8030a04c5083c03044550b01818401504003908084403400c48094904043d120f2681d5540381110318001d100750351208403c401450340e41000190800d440c0c601c01940705074040e82c0500310000c6000542005c1d0341c195404526160b001104600250fa10006400039a62a0010000b60740c904040142d05003400b000001412514003140010709150104541d4411001001010b0315591600f4014503000302d03140e01950041c2041c0911100c89008001300003c0801d08845e0003004482c3c4c450030499240800c98507000100b4150342081070340510240341420080445060040904246469599080090099296102d508082405640180f0148283d43d20140c840b030790042c1c4a4540c100f00b03c0702803203554003071450000064058a90f611529090700c001c400b81091084608000701302449518619104655132013454210303940c1c89101300d000e6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 918445323 1250 918444073 918444077
    0x251e03050d05010e010810020c0703020604120b011e14030703240b040902011b0309051009050907030902010210020f1c0501061106070e090c07150501050312091e060706060303 77
    0x20301c414500c0c40c0000c2d03071010b034070030104041d203680180540f0102041400080786042030058840c1d49510105103041400d9201a4004400003000300d444248005481d80e414000c0d00c80304126643c0d004c0001d0980e40128a00000040c1441d0030700c40185202401029084014100c601d4030380c0b03d445a103c0758201049142c1d5402007003042c12801c00450084c45c8825004540800481e061a0000303010b680c41c050f02c86039268551038180c002c00d80140c414001074403024007042c41c011003000b40940144d056000d1203101d00d018800080b419886405004c7d81c17a58107902400c4c0c2200318804190103034001e0022100801402d10054102c3e02148801d40c160349480040802c2c0c1c0c4d4500360f40541282e42c4680c2110b000e0308107000700851603070040703007503049032a040e00ca14141d640c0d0403088180364011164010a0144203a140c1e071018025078010b80d069070300071020344001901401c00e60391181b08e210a82da4024034504103108a00d0801c280c91400c4117005050749142608507039409084555a40007240 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 918446573 1250 918445323 918445327
    0x6060d0f0617071418130b090d0e0f150d09050a060515180f18010504030c03020727020c010605090a050a1107020105031303051308061803251e0305 65
    0x2600300c50030400d0030f00034450700349501601102003010a22420360569199500f40c854000f01d0404030001e0012900b090304805821100e0410004130358403a8661900c0400254007510b10f8907403483c100d076038511080e100030903000010100d12407405964108a00c80d8003041c0d614048400030542c14003e0039081d40c8220b07000140c0b4906035a012034660804425140542c8020500e240306461132154940c01004505001281d56207210034007040300450501c9240e2942408140404c060304441e410903038610a0b001c0c0c50000761503046425032078600c0e00600e0b00c1098254403d81c0d008140ea40104900a203c0c400070600d591168040781580e0030555410203003e030b40d401040071841007032046d012656003044000d0301e4203942c1d400007400e0780006008116030180b078136042000c1502550403221509c9400c12180c0f401380d50b507442c40f91101d6003240c42c0c151283d018801d091401c10080211340c2d801043e05a215908044024070111181d1840400c40d600b00c41c2c3e0600140f0f010f8280400c401181c801e6441075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 918447823 1250 918446573 918446609
    0x1b02010905070f0302010c0311070b0f0702040e0d0f030504050f1f05100501090506031e10030b06040612030f03060f0b0405011d130f090f08071b0602030306060d0f06 73
    0x20b86005000d5001d54007000b0000340510050384c2c0103005003811601843c00c00d502100f00d000c0f0600302056036014805c0c1180000da1604519845000b03030148900840d8208208800f1200303582d00d4003041300c0000000380011650b03184040c041c0c1c1c0a1900540500203c81030621409003040c81c0611070300d0342203028100c011002e540c8070703514010346511101074600c10740c070709241000181080e5464041c0511402011001031786140740180506060140d40141c110b040c28110462201074880d0300040e1001d200e440002600c508007405400101e0701d00d0380d80280841440d0300c003110030b451600f00700301c10142c6900c0002180318103c54181c026040351701450b035a03585458005001c140700760300341e4440d0003c001d280b4072180e6a9481c607010340ea800701c080414001c444409810040112400040004074040100c1d03081c03003903590181c08030310b104600014494003960302802d401d04040c80340b580180d00400000c0c02c1424442c004d004040c0000c00e01181c51035202a040b01600c2c11a0070141d54070240e60a84 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 918449073 1250 918447823 918447833
    0xe060c030103120f09030b07052206030b041503020f030f010f1b11150705130311150c03031306020d1d060a0b0a050d0503090a030f020a140d06050603011b020109 71
    0x24910280c0034140710020b03050010713010700b400c40076200c05442c40d00307064002104580104107c039260f6114210041d2104085004400040e00600a40000a00d080040d21150a140c814404d09061504143c4805865607017000030b400c001c1074409030903008021003d1061442401006a42000036601043c4980b00e0480612042484a03000041040e0040081e80e0900089611840c4c0050340100001590795894140c0c1c003886000d100c0700b01d00c41d400c5800000d002c040c070703c460031843d000c80b0710000442000c3c0e03038805070b40039000c016401908100042850210955041610244154005810043c1c0c0c0c00310401154850210000c4034a1200d00001824034107004884c0d00040f008410401c0d040100301144801c600b40c010980201c441000d00f0003031100400990b000b51000414022505850786810302d48a08103581c04c07401010301400200320b8049864080a0810015040b590f0158558541784054680581400e070155600d8500b0f0303d00d40d15006060342140000d4002180f03880c440d03d40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 918450323 1250 918449073 918449093
    0x50a15020a0807150f18020d0809060406110105090a1208071b030302030a0e031e21070504060201060b0f09040f060f0b18090405031605101505040c0e0906130e060c030103 75
    0x841c0018a16015000300f4541b480d480c0340780040e8064401180403500e515010a251040d41c54a070361299000c1000100b20794000740c140c41e91414032009000f1a252001c0e519503600ec0d22000400b500c9a0030040384025210340d2455a0040e000c3c41d02e20815554107009d02a40c3c00d140d0416000070343c0000411000740c4c0c0d03a0282c0d004002c1c5d0180114685810403c007403801249904c080b40610b500001d504420030624090034598400f140e0f945955410011005801c9620a1180502550030081d0016440380500d0644507900340d10400e41c1d02e00100c00040000425840c0b0041415503a540008039403004a90040005040c0070b8910396510301034500c20041c0c2c0c0c00c41c0c0000d5841411f04c0800c000c0060008802d5500c052000711004140a5035480d20b18105804400c1c4c04100603c0c00501e0541108080007400890b442510104500c140902c0f0841e8841c5404100c0c541000c4500302140f824109000c09040e04551210300050300e4074041311319070a0807019038041031100800b20052040c0007298070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 918451573 1250 918450323 918450341
    0x7170f04230a1401110c060d05010501080f192703030209040e0a050d030c02030d0509030d05070809210d05181e0a110109031406011806050a15020a080715 68
    0x10042c0301546080240040780e04031860460411510705480019404100540980c01d2802007141d0745a40300007a41400070602485114001140f00011a00207460f46801e039000308608203c2d500c4d6168070f124094082c089144855002511022180070300409511807200d00a200f40d40141e501c180103020041540c0c0200d5042003140c2013180143c0002c0c80004040707020372818180401d0002c04d0403420b07401c6000b6103900c800c005d030501c0100400100c1c044010102c0d03403c2010100b203070f5103440c1030440304454101c40f4401251300c001c00e56010320607462200900f540c110091300346098030210104e41a15800d40705030741c4080f80e005240440d00c0052107052005041e242c480c0080000070300c0c6260b40e901c40c030740d805840320145500744880350740b040c0c1c240b82c041e507000b41c4105402043c1202c40d50340d48200b4824041260309200038480030701030502503082104c078001c040740c4542d424940e417100800540420502580300c0c40082c80009446a130150002d01d00a40740c2d44008100f5075140000d4600000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 918452823 1250 918451573 918451579
    0x2120303151f0909110903150a14070806010c080c030c010b040e0c06270d1b1505121005120a050f0607120c030f050a0b010e0f01020307170f0423 64
    0x2618499070b241e2042d55001141c00c0b15101090200780a2224500780c49004070b8a40c041c000c0180c0710f0f010743c0b510840c0394000c589020702001440005c103090040b551007031310810300241ca01c1c4003142e59036200d120f032034815900070306402d0315019000460501d9507101020489559445000080c094a8030344a40c1c0c40c1c2c0e000f032030050a100044070001a10324400c103558000012082c0580550140c011030a00c682020090020700e0745000764213107940f906108520800700c012000c14007050450040303038401c2200c0329a864080c03c2507004425240c0c1210004c0400000391401c080008042d80c48410f401c1000341d003080a00399101d814107146041101000042d00c66610200070f2007501584807040c400340504078200094804100842140a010400304a8652a05000a0140780d50f815031010031040b0003600c45028801f088004d00058180403e4102d0240e0010f118110114100c080006030040104a2480c505441c0f1620310580c1d03002500080300c0c510340480000b81d00407040c416001c03004021 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 918454073 1250 918452823 918452869
    0x30901141303020309130b03060c270306060d0f1a0108120c0703020d262101030b060925081801090c0501031808160210080f0406090212030315 63
    0x82d46010350741e403007400e800a011300840c440441c2c00d041d99621140c0340441c010f06030741c0300d81040341e040b010f1a0003160b100b090f400e0940f901405200081c402e10755040c08040c2c00307008945e484401b000260317a1580c009131074a88440ca6102c0c0041c10644200c500c44034a0440700690354100403401d072034900c520040c4014103404100351011008000f407110100ca9040744e600c0440c07030b0340d4900740614540c020f68401c08203040100d038807640280c62000e40710701744000d00100d642a140090301800180c0031320000c0d044061800115a10b8107045913031560240e050407a410645017098030f915a035540c00400d00300000c42420034081f00c6a003801a09600350f06080003485000003540780c00c0c04004040c45190706140d914000901ca60341010490643da6800945060300d4055620030715107003034031080040388035000c10601c4000040c00307841400d00400035030b01d0080c519544c3b40d07240c80c0142460b0390700340c0e4400101200d00c10400400c02c021886013a000c1d5109010195210902c2940025440480608296 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 918455323 1250 918454073 918454111
    0x80f0406030e0712080f0c0d020607030c0504181a271b0307230a02010e0706030c05031f0e1e0601020712110d0f0f03080604090c0312030e0303090114 66
    0x120b01d5040f04490b017000140341da480282822040610441520800601070000b40c0c0c0103054011418074421180307610140075a20340084111021703c5540101340e411711207a003550018107000e40c8041a000c4d11b00801800305406080000d041480d0f050000c0c011001850401c3d41605071043c0150700680320000901440404801441e00c90000030004000c02c101d461610680e00d950902900759078800b40880d50303458010040084c080d110703180c00c6400a02c1940d03000907841d07202340b190b100c1e041003550303904d401c43e180c451f05d401047d0000c0c0390211415280e80e078080381c1010941c24242c0614106040c0b40c03114022048a46119003004003043d0545d089a4020495003d03021500e0001276400b0640415884a103c00940c2d03581c510000a030640050007070400070800301d2200f401c40f80e4040d0b2580c03480c5a50f40310070001501e54524000700040003542c03040000400740c00c074412040581d41404149182c0300910179186403c11500c1d16000da4484080920328001c0710481f5410515034001c090001c90 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 918456573 1250 918455323 918455339
    0x908011406040f3209070602030403020d0c0e010b07050d03060305030307030f180602030708100b0403080304112e03050606031503120301090b040e0102092b080f0406030e07 76
    0x14901c50150b9103420b0014040820303a40328080c86011081c0c100440716841040c8140703844e66940c140c02d85040c0b0400704108620009045045a02c107900840c43c1c5030441d8240100c4005414044035000c10010b804280c0300f40046505000e003405000564440790141091841c0c03c000701030700c109142c030300b04d8140041600401160b44c010841e0402081ca071041980c02c0006100700c003003034041c12200c00115002c0000c1d9030000c3d40034034520703902e60819448400840c034070742886120385403244008005c104002500207000d03551050164600329000340960002c500c1402206810400d502c0c583e00b540c07102010407200304d0148540c9446c0800c014542032000c940c1e01c1c400501100c2c0c080c035152601d00156941040340c500d01c40b091740700c000d40f6035030348100f400d02405043c101c01c0d10a40c00d0001c2c6001d4440144207844209000400e080500340c140040140417203c4450301503008203c142c9024040759502c80280410024840d42c0f990302d5280c00c100504031004a102c100c0c56401c0840300700700c0c2607 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 918457823 1250 918456573 918456611
    0x9020406180b0a020a140a060f050402090106090e010303030c031d100f0204030b0c03270f010c0c020306070806010306051e0f011106041205090907110c091b070c090e0706090801 78
    0x2039001001900120103807044c02d00c7c2041141004228a003454865100800c3c01d41106000f144207650710305e07070740c0d0700d0314401c1e91403581d00e014070f0210502d8080100040385c03094001c0c0103010030710701b0002003c8414583d5000205070003c0071a45c0c9a00c07007200f010b1030a0302c44c4181d41e00f0821614003107040038113550b03e41008000151031100e1600002c0085244001514240001507c03040c04c804030080f51094101d4035403510700000c020a500c0c0040442c10039000704481079400794001c02070b00c282c4c0d580072410f40d8189006024141003644d204804078460b152088580c40000701d40188912038001e560070050a910b41504a40c10051403152a40072840009001504650f00c0f0484c0c44c4d40486a002c02c442038010a462103078007201180034400c010f07400c6210031103122020401c0d140c840a02a06010817140c007942e00030b2120441c00240c03a21a00c01c4800341840a101d503220315022641c403840c2cac0302078a228400483d00c68000303050810010f604603540c18001e000c103070000d00078050841d000c1d40d441 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 918459073 1250 918457823 918457843
    0x7143403020402090303090301050712060602010b0d030c050c150d180f03050d0b06030a140a05072003070219080f070803040b03061c2105040305190c09020406180b0a02 74
    0xc2d07074022600c1c1d00282d03801d005650b18040701900800c9a8a080c81000300181c544801043c610b038603100c0045101071041c0500040c000010f09075030f9006445a4048030b014004050983d124010b000c68044195a1088410364416100000716100c4000000c01e2045849401d025154122003c42d4240043d042004400c099a01800c0280e1100c0c0700c84d0443d4058000905010fa01540010401c12008400d40c4040101c001c80640709049580c0c030380740e103811100141d0b003000128009168004181400c3c1004545042c0780e0001e5a06004c2940d0104208100340c40d10001400c11180050090003030801802a00c825441c00602000e403070a40c40075280d1269008001c032200300080000c030f007a21401c940b01d00d1000d4090391208015202c2c2020b4520340002018404084110410308082c0342c401c2c4180ea040d680c1202c00740801c0301b0540d007020003a49014204450810052500044074091403010b000101416100c000c45070f519440d4041c0e03508080d4008051440c0103000e2200d400303031300003403000308 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 918460323 1250 918459073 918459079
    0xf0606070311070803070605091b0907020c0409080a111501141f0810120b01090b0d05030a030c17010e0f0c0c0d1d0a0b0f0f0714340302 60
    0x9100440c1c00c046840d80e01044894949206440000403442c4002004040e618010f40082141d5110f03100c61503140c18844105100348904004080c456160102030702e42c10840741e0049549907070007000881d0503141d8000090360502000b00e18044000e8115651250300c8601e0b4000d0800d1701d0a50446100380d005c11b0080c05140206c0d902c24014544411501e040030784d02c032540041c40106083c00041428030100c5102902c0000001c0014500301302121940a00764810302d072f42000c1c0c0c01c08180c00020305543c6000d41d40207100151450118800348028500d030f5505a801182620000e54040c1545d02000c0c403d884080b00540100000b48455210540041600304008125240c050681405001d47c85c0081814007076890703100c040d15008080ca004101d88003245a01c08030000c401c1108003180361040c1c5240003410003411040401e01002002c02c20103000b4140d0408810303071100c10200c1c03210b100c1c0980b5544486002001020f0203d80d2290100101244001040c0c07220200440c0703030f00c140f1000340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 918461573 1250 918460323 918460327
    0x30c0307031517031c0b030c09091006030507140121051009110c010f02091f09030c0905060306090d02191a07020115090c0503061509031002031e0f0606 67
    0x103814042c28080001c083c0b40d1038001c80400c10030342d2551681d000000d140059245030b400d00034207010714040c414407100d0060241070b0030480070052142c410310051003001c050240c24219140e0303030650710501c0e000d540a030004000c1d090800c64803c000d4500b64803580d0511010320140d001604441400c0c60715004420400700e80358480407000600c0340110340014404a0034034510b03071686001b00c0041c000b5641c007040281b10064500d40c14038124414144255005014a86000900341e4458520081181940344c004442e40d5280c5520b8004d44080d00a1510287c0ba001031200d189030030030000b604039000802030122003c12842c040e6603a8400b003840300c11004041e03198401d02c011903181b0940d02d00512003441da2442c0c405802802000100400c2c803040c0c51103076010450004031b200b4141c0201003921a68a96110341c0304001420718411003240300b02400300b1080805031014040000500300114025841c0c3c00c10414001055405845912a00040d80704125403144100d00207600315800f924010703 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 918462823 1250 918461573 918461591
    0x622060b0402160b06010f05030f07110a151b030203190b061b07030317150f06070f05060403030e0a020112020f040807080309131a041e090b0a0b0105030c030703 71
    0x9400b07400f039070002ea218424021030f4042071103016001148504401da8800d00800340c100803d0729103000c01c1d10000745c0c5054140004508a016803072a602144581e002c5902c09a92603441d1008880c084c0008140d00d522036400c0c4400b85c4907120119000046400d066045285c1154940650040c09182d420285c2e154003015565071a240e0031200c101c4400380c0b48580e61005c42c288188d440d0160b103c11000030710440403245940140e44038541c000c00700d00d07502301c0e0b1f0781d0144020408421400e20400d603121400704071040019052450140742c140c0310f100601b40c240740604016044070080322560060750840060080142c7e032086900e1030b2800c402d0401030f142c600c140220901d50007550014071180c8645070010400d1000000a88030817207088900308038100b0b080110301c050b1004501810408441d00c0c140060600d05034100d03080c1c03400501ca000030305a81e001c280c4010385203418803d5960081c1c10301800016a4180600f030000d81c0c2c00e00341540345003800c0107500080d02c0000c00701801c00d60b0f01c900c81 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 918464073 1250 918462823 918462829
    0x80705010b0604051806220510060c0803070c110a15020606040b030c01051804021612030c0c030e040906060b1305030d0e01120905061611011e09050f0303010f05030622060b 76
    0x78001c0211f100c040c0d01455a20101810041500395200c1e0301f600d03405040020624803d14611049e075078892511404c6450320402902c042058070800c4640440c8000d44000315110300c11590000c20100c0c9000030091001300c0701a040c0500070b403006005508005650742c1507140081c890309150380c281780541c1d940030012200d0200d42003071a2816842400002c10422440f0000e10310075529000740d94090341076055a03400c0e030480300d104510001240da04414400864040c803000803501e4400390011920b0360030769851804850443c0c2108442d5400030401200341070102c0e80319006403100754000c0c0304001c6c40c04000ba141e050070441d4a410081c00c8103140107100c01d16017000c86410703841021100c40703041c065420341e80c1c50386040c10320000404411070f00d406540140a034a0040d80d2201e0798810f10040081c501024044900d010388144c4100c00a108001808100442c000d20114550410540c00c1c1002c1505140018003440859081000305c6000c40e0080c2941000c025440600011044441804 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 918465323 1250 918464073 918464089
    0x6030706201606050307120b0306040b22031d061c050c0c01090c21020904031412040c031a0c040603090f02060304261e090109080a080705010b0604051806 68
    0x900c2c071554030510400030310300390000d020354090311882c1c03109020b54814607200401c6440b40d22050741e143c0d00c4000030502103044420001c4d00701c0d801249284030710060210306590700401890450001d26000d045100c030180b176046085550000300c40c500e2505413883d5110080d8050180c02e00e01e5076680da408100c420b0000411600c0c0001075000a00807002a400d01c0c1500007110712031030284500c11260b01000180b00c1020400c2c2c00d6004040000d50f403170710f45046540c02d1030201d6444400303070100802c0c069020f1404403117200d20b100f0742403001c9160440c90820114146414101e107001e101e4002d00c210741c8411800d031000d5400c0751600044c00d1166040010751240c40010180d0401c0d000403d10040c0141032600c035040e0707404d50040d124142c0c1616100c42841c402e80500c0d06c91140c401c801c0d00c0700c400e105d5004002a06c0149003621910751185103072403e119040748100c88180001174210708114081c01000e8008904440040c1804c0c500f1002c2503080c40203800603c050294070000452507941c0100f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 918466573 1250 918465323 918465343
    0x70e011d19032f0109051806012a060e0a0507030f03032007060e1603030507080d0c0206041a011a0d0f11090a0e070e10091d0f0603070620 61
    0x1032080d100079070482c00070140304030151a18001c0c03d24010803003035500600c601c40c2122400b510004101c0c0d40d44480c0b405c0e00300c0250509041010004446040d41c0c0041505500c004074440c10101ea4109458488211642c5122545040d041030301c00c200410f80108600c411241c01981200201c8030900d4200d0050440a010940d19403500d0a10100400120003400d0102c1c4242d10802a071380e0800d00f159962407035800c003e41c0c04c0d00034280600010340300724007400b0f05501c104942c508003004642083c0503984e50761405001a8002000c00080c4a1103480144601c004001c1c0748419504101501081450b41e4800010403000011801e41000c0260301c100c0c0c601d9800305080244842c2c40c0701c80807040d4405010588600743e501000b04e00e041000a0490003601c1644a020101d0100401c0c822030141100030003080c0005a500042c0d0707900030301c90001d961001d040e88c01d00a4a1b1000c010810341c42c015161a002c0d83c00200d040c41059040000d445408201c2c61140b00d80303c070300c050002d1034005555 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 918467823 1250 918466573 918466583
    0x809010e0303010923040507051c0b0c0901180e06010f022a19051014070c0b1309020903060402060c0703020a080304090605090c090d020d0602070b070e011d1903 71
    0x913507a9000e83c8400c0395904042080308203108120140007402034203550190642d0003810040082d45003101100d450803040d003032640b40b44592612040503d10080350b810300c243d50000f610010940c0e00410452540d001c41c8071a06040d810141940c4410a0040805040c4a0104d51404d640b0b4003c00040d2190740585541e038202c03180355086480c00710810b00d42e0a0003410b0000c050310701c158685007400103407071028040222045040c10103c5d18411000d103071000084081102c0c00225955100b40009403103c10007041d0f940d600b1001c0312207080001d074040728003244180011209660042807094016030101d60043c0c0301c00700f500c0e9840c207296081d40003e43c0400c894400049001010007e402160030b035020401c106540c903010b03c43d4800b4111030290f52000304005262703603480c0900c2ca880403d40060079040c02c088043e0384650072039114001c02e440c3d5400354000c10a1f580d91200c020700c05420286082555817141c0580c4035241803414421611a5100400412160425640c00c200071a000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 918469073 1250 918467823 918467827
    0x30308150d0f031227021215042f01030f0b0a060c02040c02010c0507120306090f0b0a060201060f0902160f0c2409060503090a060c030212250809010e03 67
    0x15140282c500210408124046108196510101d00403441240e00d0303420094803a0720a020011141d110005c08603070101e80c80f5000c0701020790000420008989122416040d00752182018180a84641d4105642c4842800070780041188111403d481040c500400c3c00c01048600e842c4510780061f203100c001d6030b42c000401e0f12000900a6100c0658042603009036402c0291003038408007203080c0d0304010240c0340460010040f0500248010180d0b01d1408103900c1d00280503900c2d01001d00507903681c0301210076940d858058840061400b080d944c00200f4150008010240c0303030003d07409004406110b00c09602d680454407000020340c100d07400c40e00e41da0051080841c081a40740500102e0f00c0ca0003030040100340110403080e00e010351064000001081c0d1180d54800d49059012141640018a03890701801030a080300c00269044c0030303c09680d0500c0d00d0150315046518074a10314600c2c028007007085007203a44200b8011400342007181c0d007070f01568545501245c4d6854100c1d0702504482c1d14440c214800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 918470323 1250 918469073 918469099
    0x1a090a0b070c110901030b1305030c0d0f0206090606031e01020f040f1502010b090a0507020a021f02010b061606090512040828032a02060c0303010f050a03030903030815 74
    0x100220030b20050344070b040c000303500c3c0e0400390a10090181c2400b00400d0b841d00344001c5849090b0744510494000d2040040700d10305000604080d05019001d220240400c0340b46601c0e1008036010b200c01030b07000582800400c86450300c00e00103503507003100c0600c400303084002c60800e0000403003e404503090702802e00c940c15a95079440100920101c3c05209190080c003a0000d541c0c0903900c18064068071036401000c507901515412081401007074007614540941c4581c100107001038a400301000048038210309401b518805004000c0c0c2503400a019251142c3c400304075049141c0300300701c400c040301a040040011000450701e002d500c0c0c4009418240040900810000384201001030a0100d1002081c2c1007025610b10001c44002c011000c0402004100c0c045000b5402d001c1d00400003c101d0450104035084d4510303600842c80c2d80e40440141503168100000612041c481045240020103059030440c0300146180c4004004020600005042001c4c1d0404a80f4070035500302c0340d08034014014039000d24805 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 918471573 1250 918470323 918470327
    0x1202070804140a0b0f042606070f0306120213020d110c0106061206140d2102060906060111030715060902160209061c0807021f110601121a090a0b07 65
    0x921028080c410412180c0124042c1c00c0b081c1179851003100b01400300d082c41c0c104240e40389400142403503107014030603201001c02c41d5402001801e003d2205030b01e40481d01e44070f444000b020b6071840e40100050740d0790402c1c900d005848901030300d24010203004006844d09030f07009590016001c085a110001c0e0340c0423034414007031401075000c04111401d41d01c070140e0131a002280c2d50103803070440c0f09500041140440100d40b5003030400b64458440d1040c5052140c08002c4c1c1840f11016425078400d800581c402010402e07880c108200060b007001003401c0c0740d107410388011440c507502d2080880013842847c0d55225040b03004900d070002400303049200e009545958180241c06071803c5404c0003644030b82d0b014400b0443d58184401540e03600301000e040380c05100c0302c92300c8100392a0f011000480c2c000403004052640103004410005282c07015035601e403440340200078010315003003060300807040f10420b8804460028840b11110700c01095401c0f619103490f41c81c00c41042c1030440000c409440c801e010401c0040d066 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 918472823 1250 918471573 918471599
    0x10602210d060e09012301152c030609030f031326190f050406031113150906020c0a050f030a140d020f0705060403020607020a0f03050714060a0f1202070804 69
    0x4213000000c2103580600c0c844000043c001c035010705041a4114014440c20448154003a100c0b05039060124060424400d851076583c0e1481c130100111108500403100d0b45000c1c403c19402c00c4406004509041a5072070f011a00e10010f00074a442c00b20740f1000008010910020315441141d800100d1190342c0c0018000041d94400102440e101014030300700e61255000b0200321100e041107039203a0b41064100a426801007203042d0500060400c140070b10310219510012410152210003400c281c60071a0000240111155030080301c00c1d900080030080164644860a10444004032110001002048046400c003c0300c41d4026000d01c041d50320f000343e2074400040d0205513404560884180360942e40c001a12400e8600545a001004000c10005807810070302601282d400189001c1107a0380c0d84020007040241640100c41c00c1e04201c604200d01900300d02e0200318034106854541c6054440c0b44001d04a8078038124550900000410791441b03019140e040e1145d40d580041602d681d0364840e0105d1100c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 918474073 1250 918472823 918472831
    0x2d12041e1a12160915050f031003050106061704060b01030906090c0807050a052215180b060f091201020d0207140c01020a05070b1c060605120f010602210d060e 70
    0x2100c64000f1841c05000360310f80380c583c0a800c3d940c062149080029000901c14031008820070450300f0312120600c41060070045014800181c0010b440901d940343c400c1c00d40d05130781d21860038404120b41005030544c000c009258080e520410000310440b05000507001000c0c00803002d0141ca01e000f03001030030817440e14500016540c900c0304032000c0d2907843e030410501e07402a01841d0381100f18812045a50340c0145090030081865050209030f8911000c020000d81a0030351080a2146080060488160052040c1b500b04c401c155202890700c221000c0700030452088800c070602401200e02403109645081d816105003407400e804c00c0d035862910342000224092081c2031000140501c003035554441d030000070007004003a8440040c5c42c580e0724111890710329402038001c1c3c954001d6418142c41d1300148a1290700060b01082c0c44298884c0b12130403500010100041501b034131844140014010316400140f9000b90040f0503d83c000440c81003001082c43c0c0c01032900e0003100c9400d00c0b0303000c03980b020010070207485 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 918475323 1250 918474073 918474097
    0xc070204050a0b031218030d0909050a090206090f03100f0c08160c1b03060203190f201b0d021507020a200d052d12041e1a 54
    0x10310340700c0440364000c407894044402c3d07140e40941a60381c0c1080c0098060100c1802007080022250f5400d1b02080c2864000d0b03030b45100054810000307000d0702c40e942c45016008450410200158a1ba40e40402c07142d21070b180c4442c0c4500076038080460a0398081240b1804151f14603000e207c0f95240104840c007420000e2404ae02060b140c40c00104418805180d2400142c0250f82d0541d021403036840b90150062004400e1190300e04950000c00032507520700095028039581100c0084107000002c68508940100480400c070740c2c01e100603580c040584200c58041481000412903a50380319015a078020100703c081004140182400001d102e9001b00d030030590200c2c0d03007200404907034401070200c0e22526095801805034071000c4c0000d0600203010418001000046c000c401401d141340c840700c0c980110015200c10401400b640102d03200ca6038001001c1900002c40240204440d184000a0703c2c0114001c80400040c40184c0002c4500324000301801810800d400154001000001030300c0b46c3e000c083c590300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 918476573 1250 918475323 918475331
    0x50f070b0406090b1215011116030204060b0a0f050c0a0510050609100b040e0601051c1a0301060b0405150906041d060f061e04090c0e12070501051806070602030c070204 74
    0x513064254400326000c4001102c00f80c04035580c3c040485c0b004a04a480041c1044158452001c040208102c100e68030411102000c0d140351441c8108001c7e105182c2000c468040c060002540140c1c104103032480500700c2d410b00da51502c500f144403501d400c000d000d01410310320610315155400d1200c1c0d401103000d8070b0180e811070426510b50f00c0c021103a40d4688500f800c103680c100000c000d84071000c00084d8100b02c1c1458010318060002c3d03988815016000445416242d441030714860000b9145c040c00740e0b01009400900038503140c4201e04119016522805005c1e415030600c0354003c00208040701d40b5100020503150704e403515202c2c8007401e41000c00c20303045070080c1800420000d20f011016101c40e007030010180b81c0341500498a0554990146010344441c21080c070004c265440a80a80700138040e80765114815100140c08019202103503d00d0100c26030171460090103b130760f10000301d4441d02009003074040c0b054456004118540324480000c0c0140b072000c014000044289402060b1340c1c0d0084900384 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 918477823 1250 918476573 918476579
    0x3031c0b030309060a03090302124005091806070f080603031201090f0e10020c0c040212040f031e08060112050f0714090603151c02010219050f070b040609 68
    0x5542e489000d485a6020b0402c1c003c0f25840344c82504001c0d881d6101e481640d001004843c20f080c2260442040c83d12100103000c201c00b00c040d10a02e8a210b000041d0260421407580e40c0c02d006158991400340318040c0234490006802d1821310007050b0002050b95003220003d1403d03002c01000f880385c0c603460b0000180d202d8041400c0f0b190010030354581e00000c22426400b6440c107030111b001001d0340c251407058a62110b2900c42000000d02c103505801c060400096034410650301200d0500f0090070105102d68414004140c01020350130580d944607030b00082012420429060640300c1d42b13444546200074a0180040d00d80b141e9011120300d00407242a26424148240c42d403050003031300d00c11a24604c224007040000341e00d6621a110005456111914803440d245800020030350540c02103c3c10103105415424007009418071040300e2404121007801120744800f40e40c0000c1d1a94641030a40420040b002e088205011003409200943d02c1c03800100c9108a6480000b8503e541052180b6000300b86001000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 918479073 1250 918477823 918477829
    0x50f0f04021e030c10031a010c08070b1f0906060809030a0f0e0d06060305012a0210020307030b03150405010c020106060813030c0c0f080105061f0f0e03031c0b 70
    0x10502440c0e004054154042d001400c4100404030340790310503494494000100c0d010388481c00d81c1d01080070650b401080f42c15048031904103600540c5405030400112103080804980c400c81038805090b031201615030341d80c40d41d1105c01c51200810218140d00107046c200012880980d43c843c508407030894407180440d030b81d2281043c1c1c481c000c2444a0000c50f00f800d00c01c0d403e1612078034181c2800078000f0300001c0701941a03101c070b404031a1160000c0f10540c1d941c0200c4421481c10003611803003d00c8440c403217001c40002c0c0b540252074850007010721083c03039001710100324000e0081c0c01070b69400c03402a00b1148030100000c44100c030030f4400d580640c0e81e03510b0710424550440c410700910003911070341d448070881c0d40c07038031000d008070320741104c000358204000303021040c0001b05001c1b9480014204660402002805d00b8003540c2100c102a203404e105aa0416502103000c42001c40c901c010f149500b0308149800d80034200395003a820f501c0c0d406030f150200040207502580c2d108503d201c01e030210641004070b15200c0040c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 918480323 1250 918479073 918479101
    0x5130c0b120708090c091803120f060f100f050706090602181e060d060807061d010206041a04110a1d10050603060d1506090c030e07060e120f0f01050f 66
    0x10321343e400030040c0e071440b4180354103440c0d0000301e1508140c401584003c2c445003582c1145000e662400308003070a01424a0307849010307036001b1030122288540d840a9030000340c1140100d110640c00d121103880641040c03402001650541c9800580600021900b49003020007540100750386110210442240442ca003000f90600000d65400101d01c42200752200400046420912459460940342c440c00301c1c1e41103087c030500c001003942d600e40740030600c001e051707032204601c0e004400c0d411903220740304000104895011192807031070320083c0701c4243d0710b85042911035440100700607a00710f403512a00140760015034051115081c003000d43c40707035180c0b00c070319041001c040326100705588100d0520200b0360074034002d1000e85074144036040a4a00c4112001c440096504543c81410076680d42c0c1c4402517529003500945170b1420340718020b0050705042c8840600658105107070b0f2070289007803c80001042400300710b0700f03081031809030403030708002c0300601c5003406813200b111000d11611031080404c0344544c10b064 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 918481573 1250 918480323 918480331
    0xf011e05100f08151509040e010212010303080703050705090618180a0e01050108060a0e07031a060411031303030b01090b070606080f060108030f0a0e1206092a0405130c0b120708 78
    0x1d0115560f176243e00001c06a002003030031943c007541e17812010201000920052420340554813643c3c3c12580355090103000d00c0d200410a0082c980dd00082200c2030b80e0100494000301001c41304075440d07034810b08505890f01c464002d003980100406a24110402e80f0300d04080c0305610b408130a0150104003400d0300c0c00d80348284241d500e182e20020115081080ea41c00c100a40045d400444190030b40d02d46032100841e07001c400203034250240c0da050100c0c50909024408040060000301031941c2802ea0719403c00503000d81010341003558481502c0b100d60306c103d8507000102004052a40c6034602410040003c01d21481182e02e035215281d407800c10500003040041c103c0f060725010b5814804020310113110341d4001500103041118003041608155280141e01840d00c0c0c4a400606480c81d00102c0e841c81e00d510060b012a4503416452584403030b5801c82c1d801704420300300f83c4000c2201e0300c8800c49900c42554104009200c60b00060001c5600031407131000d8003500713034550042a410b8442410035101040252 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 918482823 1250 918481573 918481579
    0xf230a03031a1011010e0c01140d150b0306011206060e150d1401050f150d021606020712030c080c0a21060305030d0c08010506040308030711030c030403050708060f011e05100f0815 79
    0xc08901c00272035130107010048a11003000c2412055425044e0b440b0781e6503000492015008000d22115580c480b103041d64400d10b104040100318202107001e03103031625040396944200c05022001c406a00040d017602c14004654030b00b4012401c1342d006001100c803090298a004003800c90f48100c2c0c500d04441030300584030b964410b0b145002e82d2640020040e41c4039410070200283d81c0c5c08603600140c646c4c03004103021801100c81a480520701c0c1d0005069a240c0041241008081c02c01c1c010b00c0d040403000c94450928074103082c0b01d022500e41245190580710380c0b400d5529490f090740003084c000044020814590009000c1140c003a01c0101920044000c0c0207181d00000180010b20024051500554008440b410460405401a6006451544810640c4d604c42c2c1000c5030410030064100b10b0301e0301614804014090600d009051030b50000d60500c42e550713003842d080030328411080b820082100030b82005000d100b0249013034100540102c0d2820709410008200c0d40028040d0309200c0b60b980c6c2045002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 918484073 1250 918482823 918482837
    0xc1306030201110a0b070c0302070806010303030b0117280e0d1707050406021f0209030105070315050604030809301b04022d160f230a03031a1011010e0c01 68
    0x1e83d0341120f00501c000008c409512600e24007140920080100758000d5120f558045003443c030700000140315609501d003103580241e4030340034458106a04140c0119002801c1d4200c0b2030310340104901c7c00584009031207030b4180c0c0908000e071200a507100a03000c4a911952540340e150b034864140032200b80c40355114940058100706980d0700f0100051034440c0210840070409030600e4202c0c000682100e4084d5000400311b980c036180e5070080501100040020f08080f83d015003000d165449480d02c81c481d01030f80c0c0307105110b081103069100c225180304080c80352011003031224841c0c10aa8095841406e082c1d400b410840026040c1901d282c00d000b266800340c1e08844000303411000400c11000c940c00c024044051000521103807028140148900e503800340210b509500101141c01d21010000c0182c2c1a410b128600c4585100074103400111003a039698140b4000602024466620fa80c0d11039680c480c0340c0c00064440001800390740880d81c40f00c1012b8010003040700b024005101941d640b078610345075021544c9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 918485323 1250 918484073 918484081
    0x30702010e030309430603181106090307030f080a0e041107031110020f130f03020904201503071403090a1b080a0c0f1406030103080307020c1306030201110a0b 70
    0x8100143c2150400000281c102807030304c501000070400c80100e04c017200154400100190741c0e040c025414050b1011000407111080d903141e03520400343c58222070380284000142d08030183c9080240c1001541c0100d0b11000d1594107107004d40550340510013080009030301c0f03100c0660500d031501c140c0707503e910503483c8030340341048986c0c065070300e2074401c00950098002e4000621480700e45000400c07136507403103061507176407000300d107861026010468000d10f1514840b40c07818401078603401d0340380e50425040080a8440d2910945142c40907100c0720300c450708100b078071045c0074101141c1c0303001d0341c0034541d00c0c0c07910707203401c1c0e11052041481d0000320b40100c02079000c1d107080710100b422030901041200404080703d20068903801d46c54549a01c40710119003c106020042246010304c00b01705010784085604d4400144040c000102103002c107000142c0700240000124107241e0080003a50640b140290400590b240b600c2c0000c40180803c2c030050703003c038280c1d0403400d00081010584a14055002d9482e640c1c64172 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 918486573 1250 918485323 918485353
    0x518041104051905220f0608120f22030b06010309050c01030c02070506030403080906011401090b0c010902090a0203090d0806101b0602120a0b0f03061b1b03030702010e030309 77
    0x4034003500303d01040c001407000b00341611142181104c142003d0b903924a000100d0524104946c1e1a02e002246a031400340e013804002004100706d01c0680d1204202a110341c61411441d0840c070841d000d840d002c2c41c0308902420340d0300e038030172440007200c3c06804404002c0e42c40a005409030760410f50028030540003400d010440d5030199024420b1181e852048500032070321280802c0c0182d10548059012903066020019803100802480d805000d40c03a140301e1400e000719001a004240600442081420100d5050003d0720254032103210a0303002810b607a0b041c00c1c0516600000e5005407820011170090030b075201c42e4079005020941c050003003d40350341010900c04e00304480e0071451250070a221001c11198501040e8640090000c9182602c0904090b06000030000c00b00c8911442d80350103194104d8900405a90100d80d0952040102d440b400c801400742d9400d03022803203443c01d1031071a00600c0482d0100400000701440c07190302541c008126040303204881550b280801c441c4051540d0140000d2559a4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 918487823 1250 918486573 918486589
    0x21207030509011107050c0a1706012601020a0f0311040501050714150a0524090a050c0f0f0c06010b04050d0f0f12020105091c12090c0510051804110405 67
    0x190402d000058940480502100f01d43c1c450313031041d200755001140700d080624140704603400804120044078211080d801e6032907101d11051003905201150709001c1041e080000004000d41c1d10440000c5541d20380c2c608001c1c021500c003080030400240340244124181106404460640c1d8050319085c0c2041516039441d000c900780c510b0a5046d60042500840042e08441ea540340a184699008111032510000d0b1140d0000c00040801644035503022140003034440141046d0001650200855155a4900c0010705441aa400021807100005883da6030161102c05018003680f814203840040c0d03030719840d03040380340218080c459000300841c040800180760f4000c60511035110b0421506030411940303d10301c904041440042c0541d44480420540c050144988885201742c00120305c6c5050080e000140558000700c07020103d507584000c1c00040c85503003622400100401021404107040040004010390044c64900001e11a81c2c000400645000d02407858942411640345041918110401c0704503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 918489073 1250 918487823 918487831
    0x206070204020d020327060f0f18070602070f080a021f09090906020403061b0203090f0d020301050106030e160303053c092106130c0e01091b030212070305 68
    0x25402c120b0380f02103601500296100b06c40601c11201e080b10341c0703000341d18010086800401160071250030800c15403000600c0d0b50704401842c02c0c45d103c56640e0310910741c00080c1685542601d20440300002101a40080d14a0a4524190f6200b900e6071303481c1440b80e031394030303001d030000b0340c040034091440740ea03100c5810040079118031900e4000101e90761a013043d000c40d0400001500d1035500000c040c414041c0714051921080fa05548000b2805000c410094503070281c02d001c01d20481c03c2d02e070075000c10742d03884607001c09043d00280200b2241d40c0d21000500204031414145d0141c0c05805001c0b04172240c0040800c04594240d2252481c00d00c0495030b680d00c03d00c20440301c0c00105090a0b09040395600ca4608180840d81c903060141d07190010300030000303042003000205007503640030b00c80c1a04600000c00d90300c3c0c0048600c09008406e00c1039107001d0a82d0b481c1504056201c180742d00001481160a400602e0410540f00000d0343c6001c04020031002d0f40320703150000f0189122b40001c621498440c0d4001d03980 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 918490323 1250 918489073 918489079
    0xc0a08010501181122030b0601050733050f16020a0807080306040905010e0109050709180807020f10080412030905031801140406020313080a020a140102010b0a080610150c02060702 79
    0x181c4402603000d02200d0311100c0f014005c102a80000348100015600207039049003003400c08034103008590741c42001d6014003840d080309141c40180b0500e101d00710300840c000e110400728410311080c41c242c00d411525410844030302d5400355140c0320036014140045410000300b074026592525141007a181c0354416403002d494540c00c01c0c1d0b03440854001c50028032409003440303000c90011680522074185640b030720a0b80d4000041c040c2c5800070444a003104203114012140e444414244c8032100d500018034800c0404448507000048101394251060b8000a1144602e03c10001d2001c2d0514401c011001c542a01038000d003540c2c82044000002d01d070840d20048014014980007030485022010410550096030000001d0380c00403462610381d000407000c45001d01042402014a0707112500081c22a100d90b100c0c00400c1c00700c160313611410341d100b0740010040210284c111a02969544100c69072081c0403241d104c5004c005000c041440c890410188009440d40d50380c0c0c2618050030b80800202d83d0000d102268 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 918491573 1250 918490323 918490327
    0x1c0c0f1d060d080301080a03080106020606010f140f030108061902031608101806140f1c08121611060106080c0a020313080105011e030812060f0307080c0a080105011811 74
    0x10f40503074010340c080c1c8040390180c00221324515010b0303c2c410041c0c100c3c0c0155002030040100740e0340e115811032400303907641c682166000c4441445944a00c601b10109410900000011441c0e141c0000c0b5503001382202180750048000d041c8624040780401e980c403500304074a00c000b89044a03c80d64140707410505480344195070070354404030134503191500b0040c600401e81b0703a03008100403038103418003a2101c2000e44503802c511400e0b0000134020030a03c0c01f06c00040303070310528007828030060800f612030505442407900890300b0940c0500c00c02c580c00284440005410440e441100038020410904848694842032083e8440821001c1c0581180d5050403c600c4240120030820682c08080f20040802800000302941402d07441218180d141e106001c07015216002080001c148804440e0444660803141c03c0680b94000020754017204d49511a074148920040810790102c0480c0c1810039034000c552501c4019070310000c45027601d400b4803c80307203440400079403490442d906820a4050700d5055400038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 918492823 1250 918491573 918491599
    0x4080f1c090501051f0b04090c111203040c120203070603020d0b09040b2203052b020c100506041a04020702010201020c060106080907061704110f1c0c0f1d06 69
    0xc121408a0015030b00d50791100140801110300500c0019070304a480c50b40214141445600503903407103070b48101d42400c2c0c1da81540d100030901c1080021750480408040e00c604034082c00c1c12444a42080e41c0658404a0301100043c4001c202061140c0d2a80d01070301805c1602d14005003a0001d40010144820703d5840d04e07102034081e90f40686071445513102c0c4c8031b0140981402c082e403d20304410080051004c0303d4085451003c41d400005030385880443d11038420500c0400d807250029100d05400c64510280049102d81041340007245c80c1c4510302000208024950300c8208100c140c1e1003861082d1501080084003801604098000b0500e283c0180009450401101c10091500b00260b02581c0024601400d0020030202404843e005180c030b40786c09007454400d030070030280034040540000d00c4c8145480040585403901c0313002c810042401095002411001107554660683e054021600c60507010000700302d00704049409410f4512240c0c507111511503460111180c07001c0509031030750008400c1d0300b40c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 918494073 1250 918492823 918492877
    0x6041802151e0c061609030f1a070e01020f031303020405040f0215072114160816051603110d0507030611181e1905030102040f05150304080f 62
    0x500d41c200d010982c541d52440311440890a26402504122109592190503552140c2c404c0102c02a6a08280e10303034010022440d040e00907000b50400b00a07042c0e1904100301e5140c2d04031200209141003a0250380a0606008600307440340b084240300006d12200701010710140c1415480f0359480f501c1450b03403070316000d42a000500b240d403004180a050b05400256801001905146481201c4440b60060800c44072503c0160034140384044400000c02e0100c1c0b8180d038594401c007500011500078580316030701c02c4800450501c0b14146c850507a441d208000c03d070300070400009100d00071260044105074080188600300301880d8818841510288100f410101c041a40d5105280c1c442c120501c1c0d56a81e0308030070900c0c1e0b80d1b1401090101c0c1c071030120041e80150360180100011300090707044500081c0500708540c018480111741d041a0f80542c40890045512038448107510203031a01140c1c04400120100646207180c40f046400030481001032000320220808100645507078404a40304180c2000c01d030b458 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 918495323 1250 918494073 918494107
    0x92e0b0301110a0906030510150c020a060f0215010f060f050c031206010e0f0102060c16061d01110a021f06090f0b1c02012c09040f0303050604180215 66
    0x8007140020000900e110f10640040382e070802403c85041c01c0c40729141c02d84200b01c88401a2181d081100072010600b2142449402d204d051158014911050aa181d000040c448200c101c00301000d4440c4034070512042e03107044c41080c1201d02640250083c02d08010f400c8550320960b9004c40e003400030a2002c04100c142c240b010f03010355040950309030300702c1c030f460740c0010819984001804c2c003580e1541294905640c1c0410025800081d43c03c0f07550340c40749000c400c0166107884401c041c04c000d08d0a40002e10000104861a815070b081e000280140176601c461401d00b4861142e260780580e208429402c8403503000105420b50b2002c10100055403035403140150255444140107000d015620840c03254107141500b00b0041c00180c0d084100c101c60081d5001800320000c40e850542000d100c0c01543c865608070425524604101505100d01360610789480c0703003a000010400c801203400c040000e0120700701445451009901d49403407948085070f41d020700010420724800c0c0c0038011000c00c8800010801e2000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 918496573 1250 918495323 918495341
    0x904062003040515010914041b080a050309041505010912020a09060806040318050a06030908190215071d040e07051f08150603010b0c01020d1d06092e0b0301 69
    0x34000d02c0400960008074068160040c1c956680340c581e058802c1040c7d2402c0704e034480d03440300020043c0c4030410001c0c41061000c0c1e01c400c48520078100d1000030480c000c005400d15080a0781c0074060812030303014924a01000c1c0c09880c1c0040c00c2d00d04100080b41841009016142c00580100c2099440b1440c00302502c1c1503801003030190340680144400c05034041004003440344025010322483d41010300040c120004c03071050804058540404809018588048078036040702d03180d403810081000440030791210280d40313448400a1041c00040c2d0164003e00050f80c041c9e405951800039101c0400401c4007d0401aa90f00e2451203254408916511000803c011041c1142d4880e07009032000f4a005140d140000d024070741c5841c44000100c03481c1c4428040c0d80c15980104003842c0c80340c1005d0f803500d0081c003803104250482800c0040301010058109654080c25043c203058904960f20900055034415100d00f885055000c0711021301d050201003245143e49c080700c0e00d03011626280d5100001d0940d0300c028 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 918497823 1250 918496573 918496583
    0x17071103070311030c040c0e0d020a080114010e1f060807111608011d0a060902031006090204050f03010902101b08030c04170604031202070c03150902041109090406200304 75
    0x2d114141c2890104884c4c6170501c4200c40c01e11000d864000c00520046001c03078018000e5038002181011907a800c940000030b42540070003003048507030600198514000a22035900700450f40004220000d507554515030000d001ca0446c02d80840c68504202c42803a4001c20113410400131400180f00d200d000d12407607000341c20441c800310310340c2c0c2005200c43c2100c404003120003080c249030319181621400414405242c0e0b40002000408568900210b03040205000070400b000d403501c4000f258141a540c041c0050382c0382903600950940c10715045c14202d075081c0030043c1d84403c9094211507158030419010424489065016668001039642c03801181c0043e5155881160081000c0c0142c51403060461000003e083c002c0405051030345002e00715092a4170b024148079000150a03052140c8c2d004501e0013190b004031038460b549080b201c110000c00c1c9020080384950b0410840064a052180c10fa52000d0801082c2e001079881c1d595661009106842c0c411400305001c064000c040103007040a144540e01032 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 918499073 1250 918497823 918497843
    0x302060d050a1a0f0d05071511160b030a09060b10020a02040f060e072f0a110103050c1b0f0a0f060e0a0c03030324060201061d0103170711030703 64
    0x7842d024296440f20754015580c40c0c040600d06034a50780da03510001c2c6140700391a03146950041b4200103042010541010315041451032407500c07442d0340240038030020740c030384000d40300c0442d01e030540b182544c405031295002da001c0c24404a06980025400042c4035031003408000380c0d0089840c042400042d10310030071000340c1c222303203030120546c1090701840c00395006c0543c082085a0516032181c0c000d44006d01018204142907480908058070522404205101d6408280301d000d0b43c1d00486645071001c0f1800c561800203030300c4000d41f40d40240195405503107400c0d07029041110725480850040c01102d0003402c903109569550b1000c803c1409401416800b078011801c00144505080c81660900748011600b035108ca4080c00115454030b40c00020340340d042c50003298041b40e07440c0c901503800d40e4005480c0d00c440348400000312260158002c1d0211074000001e00240d90404119a900c290240720207000301d12841056518034410030000d24102c0d10400026117070038000c6010900d00610303500f0071107200ca00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 918500323 1250 918499073 918499081
    0xa0605130b03010b0301060f03180c0915050a063914031c0504021909050709060c0210030e15011e050609130c02031b031e0f030103030c0305040302060d05 68
    0x10104030005407020040e0945154941207201d0820301c81442080e04020014102042c40b510940141c88140b40c7c0200102c068038290503d4204480700d440b03010ba140d07241c20b0011f0020540a2520801c65070002c003e010f4007481c040c0c041da401001d90421540c08085540204901186d01150b4401c503c17a02d44011602d0b0a5894440070340c001030090624039901c203112103611107414a6a082540c42e421001180070307265807010034521090074118103941c0070100c101103050032a0754005845030f50f15541d1140d034a80d0307c2400b42c0e4610b264800180d000401d5620002d40107000340c002d40c21907101402100c0300150405240d2081c10700070303040216040303a89254806e0f2003508110080141c001121003d140000b4480014943d000b030710702040840ea1103100d20140c0c14020300c01d60713001e82c109000480513035004103140c54072070b03101c03002100204203c0b04004844910440940380c1c201010f04a49103903900359201078860407041c40003241000000c04c8040016100c5134094400c1c5107078510301240c1030030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 918501573 1250 918500323 918500347
    0xf07060905060301030507060c021f0c020109050a0e011e17030406080a021c0b060c010f0b180f011703071406041115041403010e030406081501020d090b0306010e0a0605 74
    0x400c0760700892181030144014004503001068140403104181003100c510340c0d9501c0400d070f99040f18001c407543d08000014036580b403600040341c0c00405100341e0300c294220340c030760742001520105030040d0522454008014480d542c2e680351500c094640c4030541c24080c41c0d0b10010340c0d005100004c01140d2640000c0340c200215900596547c0c1c02c01440325043d801c1511a003c4445481e02040d080129a07840d07450459031a100c1104840d01d03d049403000340a54101c0700400c4001e01103070901e06000f002d800d90a040841184a0002c0c010324803082c800c0745a918040000d030400080040b07039200c5d800100500300000d02162081c00d004643d81011700120728040c1450008105403403006805241d045558a45a548010454090724500f05141d40040300354404a40100f0391001c100285100009000c5080303038008540b1403142400c121001500e004003c012a01c0360208500c210111340c800d0710500889050380c3c09164813440614008141c51030480c0000d800b003403150301080c00301e10001059030000d5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 918502823 1250 918501573 918501587
    0x20d05190c1a03070e010909061d0c03010b0a0c050f0a0303140604050c0f0c120d090210020c010807140c0d09151706090408041a03060f030c031e0f0f0706 68
    0x321a14101c5030004540c905120050f110080030442000002d0f10204216030080d40c0e0340c006004442d0b0100100780d00c420422901900c0f01055001c1d156120300066848100c2d04202d906071201410f410303003040382507002070f2140f0905103411501c80c0101c405000c1d400d00f04001c4520344030b000740c3d40410801c08001c1c130242c2c1a4400340c11b01c0d00550508041015004944088402444c1c142440325a5289566540d6003000d00c50007401c49408000500321842e9145904003100e19802140c81d01d80d4140b84d000180d94402c0c980b41c90713a0204d01030100080b0b440303000b600d41511071101000c0700303840c0005040e19142000d2035805840d0210381c03035240902140c020700060703004042c3c107828900e8104402107039010030418020306840c81603030402c0c0060700700443e050999004005031420416522411201c0101c4ca0300111003141c000d032209032102c8a14640020505003030320014020300258034003107100088100411003c06020310464601605240080181c480351311190380291a1050600074010016 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 918504073 1250 918502823 918502829
    0x90303070f060c080a0c0215220f020307330c0b0702010e160803030c0d27060b04050402130908091216050301020403051f1104081608011a0607020d05190c 68
    0x2c285400031030340341240c000811b10701c0f1858492241c031460b517480c407118550381151000002d01c2e0703049c148600200b080401c0e48144c114422020b482e03019458040e24440c034800010246e1442301e4212202941c201310a03070800c123020181c070b4600c031402400c0c0c0302c4424608055400000503991110340c41e1a091b014455401c01c10641c030f541d2040030380782c080c69a98a001c040d1043d05600c40003c1c244d401103a19501610790506101c80f1650111982001030720721810405040d02d941d42080440140c0c1c0c6880d114540c0303d141e004050401c1c4d03084000d5107800903e541101210311000401c13041e001030342e602841c81101d0b0422401002900d030120400050030790700d80e11080c06603005100a1000950118500501c0300b42c0c400c950340c0c42c80700d26001b1405031041e800c100c580700c04000f40104000c038010800d49c014014460920405a50b81d5032010700b01c0e420710045074444d507291040321040e07180000c01448481d000903e100c44846d0705485c4c403414030b8034040c08000ba1f021800d42c100100b0805400307807402 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 918505323 1250 918504073 918504091
    0x120c02040515031b0f1807030c020a0c1203170a0c090806070807080405160e010509090a15020f0903060a1e0e0c0904061506050309070b0c0d05090303070f060c08 71
    0x40710b070202d40482d079030300380104980b4802d42c0300c0340500120ba1902c45622543c808000c0c41c4410034003002110303c2c0380840640f1003000103400d0103880d915241c000100f080300c565114034809000d52801c414407115160240b03049040214140e0b0344010044c00b0400640a0307048110009896030181c000507081d0403240e4007a03011504041c040100168200c5009640b01456080082440e51207240c91401e00340180c407040043c500f00c0c1c0780860362818079101d6505990094809013290f486c0c4040e02c581d1480b1039080100001c002904e10341340303400e280c0c001d0459180751482c56820041d0344030010b4141001169403000c8169103044600c401201d001a04420807070a2a0400480007010402c603110403943d20414014107080000c1001c00c00b241d0b004d511248031500803401080e4603020024003960042d141c0d04154400c103031021030410b46d00c5085031a41065440105490703484104285c13800d402041d00540e1501003804050003041e91800301000c4c040c0f0400c030004020a050202428220010b40210342c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 918506573 1250 918505323 918505351
    0x3050702010b0d050c010314042001021509010204051813170c0f0a060c0c150c1101021b2109090c040506070c09062c2508010e070e011202070201020a120c020405 71
    0x2010905101001d40f003400d015000ac00c00039401c0b00184d1500c2e00b4590780100b006400d10030400517640644c041e20030b40740d00300e840300c0da4410007800a0042c400c0c180d4001000300c080031007110005006401c800c0d80041d20507030700da00b4220800720303850030301200c0150f00c0019000143c404040045a1081000756101800c001c1c40c481295158000a01c1c04550308128259890000c8d40720b260240c035070348102544201c02503540c1c0248400c1c0454045c41e51580c0526031040e1410200284441e991b120405502c0c0b0391a141012042c60800403504800f40c1020441c0308100008501600d4060081c4506401a07031034109031441c0075154811140c10743c3c03002c00c01d106540014000c1505042c4507020811408201c14181d840e060602040c0c1d4502c02442c1c010f11440c0c03285403c2c0681c20210300c504803101082d1180352079a45040036140034100b075041e2400200803d0114280100945c064046d1710b0040c8105c68010b1015522252000807806010022840c9600c41504600c0d00340940e560115020603985 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 918507823 1250 918506573 918506581
    0x31a1c050115033c05030c0624091906061701090605010f08180f01061a0313080304030c12030516030603020f0d08070204050a1b0e01050a03050702010b0d050c010314 73
    0xe69145000382d0613582c854800318500c2c0180c00c001c0d0b40070200e1600f802d03103a504504203103000d41d641d902014125019025140c0040c019500700d4024a45c5a000a20280c5a044140f402c001d500f0310028258000400c2805110100d41d1561103082c011b0b1819845429590b180049940081c4078142d00c8444013034105581801283d0b8864500001207409052010301c0e0307104d4980b180c0508a80248c2d03100c191060490700502c0300b00540000c070443d507000000e100d148982e00110512880121aa140500188002040003c0c0500c00640e03220780a490400d4178440e2070390781c1c1c108030940c0108000029480710144952410301c141d841d51410901d05081106a107150701066102a96404c464400c1c06101881014441da8604698150398001c104000b245007080900000b00302d2141c2d0000c5001c2040b469212080c0500ca030705c0d5291505031174490410f1506603085015202c02000442155210040b00704181ca1314480c94600b24403410141c01b030356142c51700042c12180000c1032901c0c08a005410700c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 918509073 1250 918507823 918507833
    0x10803070210030b0607051006090c05030c04120314070b01051203070c290706090b010b070b0103020f130912080717060d031704060902030d030e030a031a1c05011503 73
    0x1070442c605a0a012a02038202c5000880c40d0207038403c040c205001e16000c11042d08015031019068842c1514100304007800942c0449450004407038400741c48408100074000d010008c03480c0110342d40b0910300790729020035028440e04a900701c00421035406940c00e00500c180d2501c0c280c96040d500c2e604004605204103a241c7d03161640c09c61244002440c0c45151201e0480e4000710850151026641f010365542c0ca9840c082d001061032200c1568100300d16000411501000750455800c075070030507031031f0b91240d00b55001c1248411280b140c103036000d422a100200c40c09654061034000701d0003055912803c034040c1d003015008030001070000c070030031004130710301040c07114415107550f002036055a210030ba05800d85800d88290b5108810724030304240c10801c1004000c02d503040100c005200f68142e6110b691391b0381c0140c2c00e407061464411842e81080c020310300780610a900c50702007841c85544010001c2402d1000c90010000c01101001c200ca00c13440e01424800240030b085600c43c8503000800100b07140da110 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 918510323 1250 918509073 918509089
    0x408070e07200c0607030206190b10080a2a14090109140307030618060f060b07031805040c0c0209012102060d0213150314061f021f050f0108030702 65
    0x1010603a48890040c50b82c528010480750315121400341c4065034070007060801035501c00c01200d00034600c540114808005158900500c2e194002c050102000c054035282c003551004e000030b094003101070b540c241c0c65412000400e00010124042d809100e43e007c04010010005107100300140c1c02d00e43c0422400200d6640000c2160847d1040480d483e21058000006814820b580e400038000f170f420081c2610901da00c0059254002d40329450070400b0341103031850320b4180e5420f032041d811190701c28071441e80403c0c001d4840040368512540c0c203002240d01c07200000d08641e62014108002105074100c1c0c011400c0001c1d106000d081c040c0d4040400c00c1c04d2441040b400032007048000d00a0b20702090144203181d40b50165005068004555403440d611014548000800e60110b00002801c01c00c3c0c40d0303031101e080e0714094001c01001c1e0015030790549160450700c1d10714003414610700310712445848920b6a00c5c404081a0f24408840020403981001600c51548003c10317080b100464004000400c01a550405 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 918511573 1250 918510323 918510347
    0xf0103110f0d02120702010e160807060f2304180522050708060705070b070314040602090609280f081b040b181602010e1209041508030408070e07 64
    0x201d080e611042011103401900900c42c06402c021054403d000000307406400009400400400301c40780207032149a910720010f07083c813404940c1d4000d540c7c14880c0610680010078031500d98207050741a2840b80c401c103011040c0b00e0f2100e040b14107010034140800044140708400000e560300e4280b02c40d04003040281e1040ca100360b04043c1c0444000c3c0b0080400034203010300c500a041030700035038179035240265000d0040c1e400640103c400c4112040051030460080c840d85170f4441c482480b0352825600c9030b880e0350081d172000801c01d43c086400e104140660340c604680914421034005940c0f4150051700b40030031444204d030006080c090240740c0500ca44440085c02100040000202c1c15058044001180c000c10a181c036040e0400145080b04241590441c03c040c002c40c681c000400d80d45a02c500c08070308881e21400340700a240c1049035400303c44031404014000c3c818004000013403030101c0c0508025070f01d18540c0590309607000840c08100f140d40512040000f81243c11406a441c0b9062100a1054100c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 918512823 1250 918511573 918511597
    0xc080a05040c030506010e06040506121b03070b04120606050405091203190609020a18050f04090501020904021b01060f0303051b3c0d0f08130f030c020f010311 70
    0x30000702401038803010a00110340107400e4441558480034051803000d002c5810602650030000401d0700b03070402407030614801aa0382c010b4908180c2c2200e05070888649105540c0d49440b606001003009000000184010500200520700c0c883c554a491410348040d640031900c00c514003004c201207605d000c07580d400081c2e40c2094903903803640d030b09014a80c001d024404400e1441c0c541040800c1040c86c0e94014400107006840e900e482008a110b648000c100900a03560400080401142c19080682100b003045100d58000740c24500d6880115040341c01505a01040106e0383c0c0101072101e10a101e2a070290215200720700385d103411a10301610601c1004403500000072507034420320ba2001b05201014500000420045540a02e01406201015043c03038244e2002d5000c01d00807000480060b0ac017858074040c0d141c034605401381d440300707680549004042c110410a50354111000500724914013500a1003030315143c0140d00d60380144200c1d51f1807003007614145403502a0320700083c4404015601903407100703 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 918514073 1250 918512823 918512831
    0x30405031603030e070f03110d0210050c030d05090c010f0801241112040915030b06101403010e0a1113150201110f0a030c020312070c111306060306050102010c080a 72
    0x7441d00720b0052000c4e1907242d04034003039018003041c4107100c0e0088130b0841e805694102440c126820401809000e10710000350321030306c0c6194520480d406000030b000010046000e8070b040a40d10000795060b40e1007152020310580110908070320311b680114030f4072040019072504a1182d81081c1e4825490100c0117403250010b1000c5a4003040c0c548100d4000019450050568114a501c0380c8807091541060182051450600c01c204483c840c0c091610012281c100c0140540d9444000c180405440c1d0f5003c46004c110001901d4540303a42440d000b14001d01d0807519000441c40e00405031005c8403901001c5030106482000484141c0e450940ca003000d0384c03510802803014800c405000e0380102100c00790414007003808140308240103c064041c1060f007100f500c1c280680e0b0400d0b2422a101d21407113403042045036009012404140c841c80507105458424000b003600c40a510001541c03001d10740200c0d0200d9a1200800c2c030043e42c0c14000c0f031000b00781c21300007802855485c040c05410403800a107100980365131 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 918515323 1250 918514073 918514117
    0xa05010903022a150d0e0a02010e010309020603010302060c12070b040203010c0311030609250504030218040b0f060103021b030d06050105041505030604200301150e0a0b21270303040503 81
    0xc0121000502117000400444242612a80d1034100c3e40070260b01084d20a0841d610f10b5000340a0800282e6000701800d15580c2540d00304803880e00a2000306c8080d106408070a0301e02080304000304011405007010f4005c1f854244101803c0d284020303d40401c05042003075480e0141d9904054070f0b00201e00b00c44000040d5203200900d003c20442410420350499440b00d24701d40540c200d401402900c0c000c0c0e6400310182034414140002c08030a8030010407403003844002491059580350900d400076014540945800d00c400301d00b00011840200078060380e00001f07210042460039218207c002c00083c24000c0c2098681060039021407080001c050a1103000000260b40350b5540d4400000340c080201503004c0c10741c241c501c1e140150070900440d0001110058203601060007080d5110496030014090325166080a401d61070b02c0e003142000001042448a02140300c8545a1000f88a40c403042401410007070308001c802e003c0c4854001125154000f0002c2c00b003c11808011106000301a950000c10655 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 918516573 1250 918515323 918515359
    0xa022a101803021b01020a03050f04030203030714100504170a030b03060f0f0a0225020402090901170c060918130f0b01181b1404080a05010903022a 65
    0x18030340044030300e0203005580d00e01c074650603071010380d009a00f115140c0e480182c0c2c03840110002c0301003502607031041d9665000240b1500041c80d0000200162a0a041d66580031a1843d0410041107508000e00000005181002c01002c0710000b009581405075080507190490540304640505503210800101d031200b40c0d00a400843d44450060304850151809902e410542071041c1c807100348400c00310011840c0c1342c00307500a8440100c54644280201c00110007211002591500e080f80c12a800348103c0b00c05a1b1402005402041e40000d11900c3c54143e014507030404069943c0d591086500b4410000a5242d0b60300306220729101080401c1280c695020022584041c164014241660115403200304158004000d0480324540c030300c402041c00b43c7c0d42072400e40c1c0c032005040e030b03d005a15200030350051144a901070f2480d41c0840c07840ca410380301c0900f94200182e491054820707039140d400c400c081503410020000c42c820380320a080c00d4080070404103000e00b030300e00d50341c940705103260440d40014803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 918517823 1250 918516573 918516583
    0x309070810020702040605010f09050405101203020a050c04060e0a05040503071e020102120403150507110a060204230307060c0218070c030e030d12050c07020d0c0e0a022a 75
    0x10042204a40d10910610610070195000d00e00c1207002d9402d20b48000b400e5400740508014015442c1c6402c4115800d03c01400000c0400901202c0c0015440300000f442141c00c0760741182d83c034040e0b400742c032020b203203824928604003422000030700407403500004001001c403000d02c158010156040201d40d68845081071840d502501e00c02400c888594040102601180c06030400114400e030240c80c101c60309105c645c90180194403000c0c0c10081d5000e8004401e4400e03900545e031181076800c1c03005c1541e1122003014940404030800f2030342c507680010240084200240c40b2611441c140307011081c2e01c0c1008011079180d4907075100300001e018900c0050004c40d40d81c0c4a080c102c2c4901e2080c0c000c103038902241c000b02400000442a0b02044110b560304900d400c0100d0b60f850f0102c9940c542d00b9800144d44550f00c0100402014a40450030030710210005980e000e5441301c915000711034600205003407800c43c2407007010242080c0103041c410042e0b00301800c241b460071400c0348030444860012411003003229040c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 918519073 1250 918517823 918517829
    0x20a0f0503030703050108120706200f0d0e0a2111070602010e0f07050d15060923390706060303030212162a0b0a0f3204020d0606060302040614130b030907 68
    0x42d2001150343c00c9014090cc002d4101506400d03000d11818005841d0191510b05651019010ba280cac0007554019403648003031050100d496107031600c6507070183c0c4001c5041100d907400580050f5103031000c004000c401040145805070301c0d0805040041c2c5000001208001c42513001010020101c00c2150001d2482d030100008103010002408044240500c0c2e28a403841203040d40d40400381c20b0042012a01c1c014400b94810701e2562407490303141c40c03800080b0402c1c208841c803201071a400704540000545e9600602c4d006502c00d4a01503201c42c480700c0c804a0001004158461003840141e20812541d0300081c80005420700300340c410340c42144404441d100b0740b031081028145080706001c2c800f066040b07521000a4411a4800300300c0f943c0711070744864807005808482c080d171805a9451401612a40c1002d58001d4401051809444d20513602c16040d92069404540440c1d4045410084d003504840c6600b000b4640e002c58074a01984007103034001084c0c1c00e0183c69200312011000031082d400802960002d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 918520323 1250 918519073 918519131
    0x7050f03090703060e0615060f09120c0103110f0301140627030d030911310507020705090c0a0c1e08070c0b131203020a0f0503030703050108120706 65
    0x92480e00c0c1c42140e644415500c000c46400d4a448240c030b06406000c2102e501803000300c4c9811454000440800c500c94215030907100340c50300c007000325040756500d800445144414080182c50001da900d0b0015049601103404c0800b000c00401c10030120001c500100c0341510000c030300c00b40d410a86140864a68094101625081c02d420510600562010007111242e024214101c0c2c088038400c020450648680801c010000c9101c000b10240e2403078085101d1020f400344e002119481111028055103c141807aa400d405075542d506100d0002d5060000801920003176405000718203124011a4180c03045032004403c0020714050352007080521920f540840303425116608003880281846405544041e10031100c2204000c00010000b6044040e07428a9134452107012500340f030000084010020b00a00b02c0c1140980040080042c0750200a03101c0e2038010001141c4920f400540030702100c0042c2c02005e060344c004030b04508030359200d0080300d50955022201040303604078180c40701c10300346c2c0d43c0741c002c21 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 918521573 1250 918520323 918520327
    0x70c03110a150212160203070b1f03120f02030901050904051801150609080721031103071212090b070e010c05070e04150209010905040e1e01020d06050f090103060507050f 75
    0xd80c96480c1c01074400010f4000c0c1050b00d075210016081205d00c607a1482d040540c00500c9254041402a100558401110b03500c1c21004a51410314811224030fa40040b200c0c514412200039040b41e00070340a20f500d9000740004e40c94010030f480060558000c901ca884d100f1a100c1000400091070300a940c107482016500920408804840c603500014050050a001403250400001c8403030300003420000f01e9009002e50948040300300408521008404025014490f9408108036180070403c000d101c3c030341c007a140f440040d8a00240c0100b65604030050381001c28140740c1540c021030294076400c1d4000110b0306007080c0401503c80160b50440d02101d000c1e0a6002d807000024404040b0301c10248075a00c41d0b40784207151054105c0c0c06080740943d100c007600007100c0750003d10807800c143c2d00510300e50320080c08682180b005980418003ea0300c01d141c01860b80d4000c2041070084100d40125800380c0011290040c015041a010800d45501403002074a201d4407140401c2800e8051421108100c3c04280015 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 918522823 1250 918521573 918521603
    0x904110d060524090c0a05130b13050117091b030c03010609060e0609070f0e150c0c0415030201140306040204030c03140706080c030711010e012a0305070c03110a 71
    0x200100c16060510610781540440810781d528040341c0851140c401c0c1154141462500d502c1120123421081031a00c502c2e1105034046440302000014103041203803d00400c0300716061400050012081d0011080d01c00c900c04103020034610003094004003040c10078520540b0000c0c030000249019640046c01d43c255103001d03808504401242c00c58420b441d500001500107031500014003110003400c59108001030360303000400041c0e40c403448050202c0c1100500010b60300381c2c0f0f0201500154464010310f0926806411070380100d0030a80144d2130f000061020104000d49140c001910015000718000e864900c0000042d40707a580b83d9041e100656080380c80b1800841e103074a8140400741142e807941640340f03e980300000d4024030500e0302c18411039504030042d0071a1034082054500c8803403556039200c155214101c10385070540034490142c0c810640c2140040351003003240f034056280d85c0c10384400105400c2c0f000700012940c1040c0c408403490350626040d81c41d01c0710300004034207003200020000e0014620003501 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 918524073 1250 918522823 918522841
    0x91203030c090915080c0f0303220e0a0b010e0301021606020d0204080102070818040204050d0f0204060e100302012003040509041707030c1406010513090c0b030c0a08150904110d0605 80
    0xd060b22030501c05c1b81d604039901020810001d41c03080145906034410841203c0c43c8044151300c89981040d07024200203a074450010072145901102c10952199407055252441e6030b000f1004400c0d00e00a80085103480020140a4040d50f4840c40c003402d19500008c1d09504400240d04803401880210000c540740e103600c0c41c240701c0c0c907803140c000c10010094080d1006880d1a00c1d1080701d045400003061000c981e031260303032501d100d0100004146d81c01036541c400012038600d11060540b017205040c0312140c5031400d5100243c03841d00359105004403c02c046400c071a44500000c1245c003542d004441d01c0c5400d60f200e1034020895001c143e80c070090307224003107650020580c1055411600c00d11409235090300c0302e040d04405581740d9003403051582c44601d1584420041c0100d40c004003426000f00441801c0b0364903802102c076160701c01d41c1e100090020000b25041440d41c403d11254002501c081180000000c1400048040a0242c00a054445104142402a65504454480d055109400740003e2809a42c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 918525179 1106 918524073 918524111
    0x12090a030f0c080d0306080705040f020c0115150507122a11090a091a100e0c0a1412070530040b0903430819091203030c0909 55
    0x4901c1c0c0b0085c041e40d0350a0800fd1400203100d840e081110004454000400701000410301560300040e002038920400c024140c900741c800005003010140b0380ca68005072402d0300c480300b003d030942080003d2210802c6000e04440d0301e0703001d540c0d00b06600b06071001000014921154950b1501c00d01424043c102d400c12450031031051080e03141d00c00ca01c0e03c804180c611089000c4049000e8510582c8020031000c0022501d0310b081c03c005031110100c5507240c02400e41d00521078041100300456003110f1110380e03c4000b072402601610704d010b2480c50342d42d40a83e402d0300c1154458000138510b82000088840300102002c104200800800e0156141c0841c0c0314a480000c01ca07a031030400108280d00482c14407801200c955075121030007070340500d40c0c405005800c005d125120804010366001040f0a0281c7c6070581070115000f420180e089846001ca6088100c0342031500d050f017800c5c0032031694 = true := by decide +kernel

theorem cover : BRFrame.Cov 918345323 918525179 := by
  have h0 := BRFrame.cov_init 918345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 918345323 ≤ n) (h2 : n < 918525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
