-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4518
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:52:47.407318+00:00
-- url     : https://prove2.me/submissions/e9e1b1e9-f5bc-42ce-b668-af9b4737091e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 812410071 ≤ n < 812589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 812411321 1250 812410071 812410111
    0x30f0f0b1008010b040209011407050a0615080c0d120e040e061609210308041509050330010504150b0a1211070c03120905060d05060a0b21 61
    0xa40c030034007450419a010541e00d060582807800c480b450500b1600c654410420816941d80000c08014003014040103e91902c0040c1001d82c1020f5066500515661071701b114040c2c0d0005210846c4160f0394000300701d6031001610070500030b00307200b490b101070a03101e50409039981c0781c1e1003030003880001c000c0030f400071490341307045c0752080c2c81d00d141568401020024100000e4405601030581c01c01072803c00c05070800f141000a0055592041030b902808000c18140090305120648450001e048400c220400c00c2000d1410a2901c0b40c0008003842549118120000d01d09417841405001c820201032480310141d1030002080010a080d17040f92007240000c85001030601e01e0b90000d0f1081800036280e40020b044a00010402c60b0744064000d841e0b00c00601c10392001c2000c400d00942607940c407281e04909450309601c243c40b5039503150b100550200c07000501110041c0d054101c03e00030141070780c0f40c1d0406a191113405140d4014180c0000b0034040c0c500080419240316002a900003580e1032a184100c440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 812412571 1250 812411321 812411333
    0x150c0f04030b04050a06140f01121a190608010b0a140a05100c0501110a0c024501060806010c03080c07150905150c0417070b0c0d08160504030f0f 64
    0x440f0700b5501a04080200c805100d810b008000f00c92001d5000c2549511341480000308076101802a0000001c10b0482c0004015181014640303880240064590610341070f00805803207c01842080c041900307040c00040d0000c41401703106000c590082540b0902810701c0348500407442510340d950b0744110700346400202903c8407032445a00315950740c0d844d400c3d4001800d1032425181d108210a012080400041c40d072254040001c00c03020b98100d43c0c02414a04241e081d1410300030315001d04490316640058040711310b24000e2010941c20310302c00c0d410180d81e030b00c2070709032034a15048800030301250f07045030804002072040000c2075018105004a07801d0002c40d80340c6101103140750441c02c1c83e00d681d0f052040180001001210305003410b94589020318501000f00a940c0c1c0610322401e1400c035021610356000d10030510004002c1c0c18180b0b40c680e1258080c1c0942a0741e84001c48405020031104400300750307081e00040801c11107124548035546010315641d01d00b800d01100c003009517000d110308481c0d80d0019031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 812413821 1250 812412571 812412593
    0x10e0d051c020d030c0503010612020315040c03020702121209010c06022b0b030a1e03021002030408120709030209160e120d02160e0601080402060f030a1d150c0f0403 73
    0x540c000e000031003503031070f025040301c00c4601d45405005051004000c000c1c0e0014403000e52040d80312001d038590b1a80220b18031404000d107501c0340d100e4106808584419416030261200354000c6841500300607510039581d403100c000303000e50817140c4001c00044030954060300411641e9842480700500c0c0c0202204042030300c0450380030400810502c841440d07032a006034040d2519800e0101c0142c0096191580c0e009220b01c0e080810303030352422040c58000107060090283c040c440081c004155071b40c0c503040c6880600b45c0e0251480d01555804200410002481142d11005490f80907244002e56100e80c65003061200059a810382088880d00b4000d5198954070700c41140c00e0b803840e006202803e641d80d0b01904290100b81c07007008844c0311400c20440e010071206016000340c42800c01204a40303890000c12034074072880b101c644070500f00009021100c0e105500c000f80c501d001050320a00300f010450520b0b02c60950340e40b58404405560301103484042c031400240712003000007080c81d1030180d6903030711064848 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 812415071 1250 812413821 812413873
    0xc250b06040504020a091505130203250908070e040203061803030a201201080613020105071101180e010f150206040308101203050408100c050d0c0c020901080c0103110405010e0d05 79
    0x460007c0401080c00e000c2100d0000c40c1130355200b9402c0d8681640d9940074501c011000740070400442c000103e400340950005809040b43c44140c80f1003648620060501441c1610228041e1042c00002614113533100800510321602e0b070055490f50b2560042000a0300141e150075100e006440300594240e101203001700324144410040e060958900303c9041c1c10103000600009810864183c00710040c0c3c2e01000725542241d10084084480000000403181c0d0010090882101d94401703d020074000c9000131014101c4409a0f0000c0c0543e444507065080702400c060b0090142c2e02440100300001e00a46d01c95911030020300440d4140341d910601d10703400c16072806041d40031440001e400d201d4a0014009644980c05a40d000e0014080081c0003c10034071481e08003080803581d400b000010684035102e94849190000e2400302107503111400151074644c00d00c01c90340464a8404610304440500c0c040d1004c41c0d5050b103841c1e82151000041c010000c807030f00021100c601401c48a020080c0c40441c080030a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 812416321 1250 812415071 812415101
    0x1605030f0d09050f070f060302130f0315110418050603010912030906050c07020109150306050a0303030c03200d0902030c090405010603050d110601060c020103140c250b06040504020a09 81
    0x2841e091660070843e00303410a066035040031005124841b01500302400300c40071803600607910b00b1404900c0a024007260002000c51810820000502010814889400e20500000c0144078110101560a440350b8800e44075184002a58014185507583c0501d9101d840603001160510b0290360f250b10001070300c02c1401c00300340e4a1403a03809106031071188c0c5902030f98040d51103240c001e00d5000a00b24504512424100ca2616450b504406100e80c200800800e0064150b211041e101d01d80a4003420101042d840000c0c5040c030340e01c0c10504080e50341002c481480c200180f80402c8410307504040d04c0c9103c410398042c0701d0900b2149003512004502d51046010718000110203003507241280c00d05803000c40100400a240d19005074003d0042049411101e0608045c040b8031303514801600500040114100d40000740010400c01401c07180003000200f007080801120741866074010307440b01c0301522001d40051142c80004400341025809980c00a000614480030160345217038000694503015465100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 812417571 1250 812416321 812416331
    0x30a050d050c0d08010b070807020d050a030224060d020f0d0b0a020301030309080f030301051e030a120806061e0d06052e09141306090c090f0e0c1605030f0d 69
    0x4600040c403c18a060100e490050019490002c48000c280588000900742d202c0000c0c55104650310400c1c09501d103580142550700700205424080d4840d920b10b06509003a0740710300c403001c20301102803981c148152001426803000103001d80034040000341c0c3d00c201c6500701d00b00e50300900c08562621151031003004800e801503a84e60541c94010601c10450b40001c500343e20210300350b24a90408070a03241524810fa030403c440071147d01e02c540700c0701c1c180d850560b00b60242c05120b00903c0b01d18074549145050545505002c0e480305402d00045100300c8049072108004985041100900a80107004c894074107500851120b4803500002da05c03c4400308640c0ca960191912a030031900d2a032440b205c2101582000071406280110800450f400b04a02a1103403207000400980502107910400c0581134140b0100001812608094156000d41c050341c0c8240124030070010b000c259842c0e07250712944103c80c3c075a0070300f204000c11410a001c0c15000301c805010500c070320542d05a02c00003614140d141d4035002f043c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 812418821 1250 812417571 812417587
    0x30c01060f0f050405010f1403030f070f11192319030b130c06080613020a020c090a06060f1101060308033625050a06050c1018080702030a050d05 64
    0x700c40c2c1c01540b00a000318144001004600c0c03034005194104d410715040f1850390300350800000d0852040000030328043c1004a0103000b44504141d0704411144604986118005a041002403064203844103410380030b8103c80c01e100143c40745d04400a20743c810010700403104600000298a0041254034400d005a03d14040040c0000d401c002c0e40c11881c1c03803c034a180e061950700c9900140404e0b00410301032112040106030a40c48040790389044944000c401c6458000c1440001d48038510340c81001d200320817480210322050340301c2c40381c1011100d05403100a40c01e01c1c490029200d0f07001000300c00645d5540c41d44000003007400c003002940b0904604035450200005124900c4480d1010440c014080c45810f820414038500011074218021001c1d05034492500400464201c0c61250303040142c005a00d070700d002030440e130450064020301c204081506d0a651103050b407034041b01c82085141550310031091803000821250401480500e0002c0d098504011070b688520345001c8074021800c00041002030000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 812420071 1250 812418821 812418839
    0x1060510081e0903070618140115051503011e08010615030c1803030302030a0b0d050a06241208210a0605060a051803010b031f0b180f09030c01060f 65
    0x518404012030b5a41032a04150142c40e949010740e4000034862541c0f018640741c8603903000080c2511684c0301c00940c1c2c1c0c41000408240c040c200044040200400d0768401045620b0148000300c0c240e500e8844003400e5038685003540d0032030f20500708280110fa13140000442d80100031f0083d40068140c50030030034400c60300d030340c0020111459014a8010003810200a00c14504d40f05082c404403501071502503101d8552180f0032005040100a01e64440c1c1c08000000030800d010807a40e40160203590100420340f030003100382c034204000b0342d41c56101da0605941401a07181410070501c038640680405400c010184051480a40e4054054404c1000d038804200d20b503030090103140040c220540c1d0842c02e0400402c400390560007032201c00e000725540c01d001200310751025400784080d02c100408945000c684801d0910032181032484420440d42080e03c00e508a00b07215881e4541002444000500ea0381d031107a1540b9120760207401240140010881105521004d00a02010b071074990707110031031107250401c0d103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 812421321 1250 812420071 812420101
    0x315060f0703090302091302063f1f03021c03031b110f01060b0906030c0c0106151b02060d0905010603120203040f24050f0705060112120309080904020a020106051008 73
    0x205c05080c0710100143d00580340c400c1901d4190940d070751034810300d01c58503001103609802d0000c1901d042994134140c000700e071119510136024203040c06000c1c0341d01640c0c0c003818200bd541808041d41240c0c56400c1409088801010952154064a400210308110741b0301002d5440e003d0804000103000340a0440001d40e0174001c0138020b005050003048064070b00490071103507004142d54a40700b08008000502e000c400101250403000a543c0200000c91300c900495942c0b0381225000c0d000558001603d041d0b5000e0190540c041540080400381001d00480d1200301614810324110f0741c0303540b940030010014080c868001d860049940246444504160402c110300583c2d42c0305040303031203032100c10360300200d01c03150b1000190103607103006540e8540820300d44e8078522a12500420512611000180341000004c15402c024440c011128505401d50021025102601c1016042c140708005c4850f42c0c0c82c159000f030060040900000c200240d86000041c403808284e90340c1d00c00309000700c1c2000501b070325035146 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 812422571 1250 812421321 812421331
    0x60714150403092d0b0a120c080609060105090a03111005040e040308040309080601260a232e0e0a240f0c09080d0f050315060f070309030209 62
    0x558a0034645920010303c108024803580c040c803115020b1048900c0d220440040c010003603040321801c01a41c2e82d000f400300381d00072a420f40002d0415480070125041a006104020115981c0e103049911030b0810480c2d089006013031385050081c00c0002c80b200f503c1d100882c0c0001c41c0284a94504010380c0c0003445454408800c0580410804101c140503841c060191140c1260301850045d400307940300d00d4241d805408503086450107204110000509042000c2d644d4a485900504d00f50b11944100f03486a549622941c001e00000c0c5001e0b4031911b030481070b10300c400303014028401c88000850607028100e10020074807180b840c0312042c0404407070340f0f1035501440c000044180c0080103941010f817164a030307052a407070090903010b000d003144580c4501a9000480c8c0d01910b000104020f0740b00d00c80281100085110f03030b040b00e000c0c043c4090350391030040c56500c0d206540c64032020301d0755a580040300d40452114814640c00f2005000440703462000e0005021010302c01d40743d82c91680e0650042010a10300180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 812423821 1250 812422571 812422603
    0x50304172104063603030207080c0f160e0a0c0201060512010504020f06040b04060e0105070c170607020706124d16060209150a0504060e030a020102070b18060714 71
    0x31381100f04240c1071001e6084000741211100c0e0070300d203022806441440c10281501402040c1d998601d5070124110f56400d1038070040350340b246007160014013225010720034210562200b10005103100d00039041816440618800065203540f5103001403202028040c028400c0c1e9522003c10003107040021101b02080f0003283c000313040900e4244444080e101b1405000300300700d07400951600030303405071058645c11580680354800d4103407154140395210758819001d2000c0e12501001c60b01c2d090000c124002960a681d031528103015182c11080041c1401c884540303520514989034402143c59804d01e0a24040c80b244185008014101c82c1c800ba042000c03051203d0040820a4000000c080c2c1c1c5000c1195030710640141c1c13108451030014481c98003110010746904400a141c540e500d89c008014030580d407a50300c1d007660b0042410180f5540f000e8911000b03001d40d10009040c448031907424098407080c040345541c0e0011030b401c4404101c450b00030700e604460101080c01d0070712140300280a50803010603c0c01c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 812425071 1250 812423821 812423861
    0x6032a0e19080d050a0c02090f06190f06050c1e010507110f0c01121409060901060608090312040c0810091401091104050c040909110118030305030417210406 69
    0x480b0242c651806096000074000c00140080080b4010b02c1c0d0903100304c2d0028098500f52402000c94401034000b16421441802d02d00640200c0408284103001942c0c5988050001581422001e543c168032500c0301c142148106288004042a1000510301111082d000411035050201c0094009000180030345250342054020303e00402d400291a0443c0700d0134070b0502c40e0441d4a00207440108040008000c5408003542000480d6000040c258040c80f0030400801280e65609421102c080041e82c56010a400c00c10011080301a2509e0840e0410b0046d004110300c03550302c070044d500d0400e00d601e0403134996071914064024003400d40c40c4500c80404e030200030711032200199240c01030124900003003489036a650010030016078141c5d0656024208680342004181d55500746900749528400c00d05000400601030f160f65400c1c0c1d00040f000300e039855180e035802c6403190764680200c501841003220381c4507000e0001c02e0040c1200c03079a265185940d800160b103241058103160301580c0382010b24641c2d045440c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 812426321 1250 812425071 812425079
    0x8060f0c0d0207030302120a050106110313030b04021c11130606081801150306020304020f0604180209220507020f0c1c020402070206190807020109020a06032a0e19 72
    0x540480d6040340706140c005a4500031450b00ba0700070700a10059041c0d040c5580208140700e1515407000c1d05a640503200c081c110a0980c12260b981c1c0310b08121403041201c0f1403420400030760722503030302034100d8802010150003d0310120925242e80312210143e070302002c01c1b402000d95080c6600103522080d8003110620003181824405003503504040e11062901c1040001040c232031100303501851501d4a1140403440299407802e01390081d410640d402c1e440385402d10016143c51400c8022107040301c510900180300070240a030800001d4100902d40d640101c0d0300c000e03004540c1009120111141195100000d0f14100440e000380342c80440b2101d4400c40c0c1c000381a03100f00b90746281a8241c90074501c0c0341203442d10703c07500c0850040d0280c0c0c0002900640d0109460780200074040c40845120200d0303032401001e65402e0800c81c2078404065001c3c2d00803c60820900c400352003900007001d8070080019040a403402d4858462044030b1003043c3e10001009000a00450f28040c0040380340c2c011212400c00e92a428 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 812427571 1250 812426321 812426341
    0x11d1302010f0309051204031502090a0612060f1205010f05010503060112150c0201020a12140a0902010203190e030705030708030a0e030f030403050d0822110301021201090608060f 79
    0x5822000303410700950a2004003000c0c03082e0088881c1551110644101044a10084000c3d8105000466a0005104c07a84605213010320a039000840014580001240b03001c006843d9a03030a0310b50462805d44411b404940c2c8600081c0c620000c02c06000d41c0004125182002c500315203503141840d4444d42000700401c03450740d000408c3c5041d80d001040b06440192580380200400310803050816005041075006c0034012303010740c06081d80410031b03281e0266411116a0708401c580140700b00031050719403140496501400369101e10200c034410b0049900c0e00c020f030381d5081d00140304c090b0680d0006031040e0b81606517043c18800c1c10020f02083d40144060b41c10201130584078000e0040c40d104004125a040d5181d643c10003400d81c213815103e051300d941c1c9840b030034443d403500b100c0d10b42c800c0495441c001050350002d4200c4030a80702a80743e000001000d00c02e0392034800d0003e42e0350486506640034031400c400540c050021030300904181a000175240c3c03034680024148203005059204850f100c2c0c04110000c04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 812428821 1250 812427571 812427601
    0xa080103151a10051e030106020f0f10090c050d0f060c0c030c0f1a040b09060705030601020c010f260a050903090109030b0618011509080c010210180209040b011d 71
    0x40100c5000003043d9800c101190207018074408482d480001403405101c90305804000d43c141d402903421390b01c213140c41603605503450422030103041580d8414240e4500200c0b15600886240388108102e1070450b6840c40000c0c4004c1c000d010079038403203924403020001c000581c480c0f03440c1c201c1e00b07049c00c101c0e200694030050010503006201504012101c070180d01000742107500d1241207041202900600c1c20181000408034004030382d082000d04c982401700344028042d03400d69206400c1640100340501d058001110b1803416010054180141d0034aa0f190403410100d903615000c4000c81401500d2810300781600554901800070500d0f90000c11100c0044d076444009041602e40080990480d91542d90110760b000340005100040121080d00100781c066448450210700c820b10f5075031105d203d48440407140c42e801c48407139090242c1d0025015081140303458100c18540d00c0c0d0030054010707030722483d0007150200c3c0c42101e00300c3d9400e441c41c0050004048000c1c1c083c40480b00121032101c41d00d000555000245 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 812430071 1250 812428821 812428871
    0xb0d0f0c02010e0d110f0a0f05071a19090e0106050a08150d141f06031a060604090b03010209030f0307020315040b010303031d2e0509030a031107080a08010315 70
    0x210550705068005401000b821031803186d0f410407181d807202c02e401c050211045050303080b5424000c1c03000005244d07000154242031044049101454904411010340540101212000a10030300c1080022042d041950b11402081c0985515030341d0120703046e008242100c014000e480400380804402e80a4070792070000d001c101d0303200d014010380e60440c04155140802d034262441840e06000d8040c0e0000c122500903070112071140300740358001c94500485210140046482d0ba03044403040c482007200c03002e00e0700241c1c201e10000d4001858818440c0c0442e01b0b205d9503004d403a00305c0d800002d4034011824200200b0040700035899103414542040c0d41c0350300701400103101c05410035480391030340440d84258a400d0708200306a00202c88818200c218845020703008410038150300c911200088044410034050b040c4146045d00203140360680c00f020550080c90b540848840c14041402450001a8000b0041c07801346070545400c20030b5071652038640700754044800340420807410607581d020300300a41120140f44c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 812431321 1250 812430071 812430077
    0x15101e0c0507080303070e040c02030c0c090601030902031515010504060c150204090221090a02061e07080703080603100e060a0f110417100e0d05030703060b0d0f0c02010e0d 76
    0xc0605210745060016004084103000c00402d1150305500441810743c0a44103072024050340e10903180c00d80e00c3c3c3c0204041010741e50422030303800d0354034500740d403403d903104405040002e8518080d8010914080080c0c11403c030008401041c820b0100c00c452075407055810034a000c1d403038141000d40c020005404014024010f09205154050004940e015200900301030141103454050110358030000215000e6079140c000400700201d08000008203001c58096005441d03a40307011000b00e859030750380d80b40c0030108000310028010240007404103401055410b001c2e5031184440e0800d0000c040c240309000031402c40d6145050303a091407400000c104680c0c0040d814100040c00d080c142c2c0c4160150001e805443c480c0c2100050100c1d40070000c071035100c45400301c00b0488a10440c0702c640201150b1101c0715040c041d5001c0d242806c5603d20540085a00035154500810398580c0c3d5541e45005070000950031034659120203101c000124284250204406075200074402c4025000f0b04d40e46844e0808000307010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 812432571 1250 812431321 812431337
    0x705120406020f07111018170a05010e06010f0602070f0918051e060f090309060706021201090e160b0f090a03021c0c0b130e070c050615101e 62
    0x148202039040e110f0034500c546640380d980c0601c0c0303003411942c00c92102c4d0500c00c45481080c50b2145210704013004e48107140c2411180100c0c2010708850b1101c10062118806118054084002800a01456480c100c581000300300d603505002c650319100140340c000070708652000c0c004010320081101c002e0100c0e412404009000700c08861700081d540102d0324003070002e103e0345c041d845030385280b010f84030100382201c03040d1819520b5411100718010400c0d100b0402c50390082c05003c615241442c010840603201d40c400602d0284804080c10480c3c109070300800405a481302202d14800b0140034481000c1041ca07210240746082a0444400c0d02600c603000030690b4001c0350208440d203400000340040d54004281e92070454000342e0b50100701a072580112842da0706d42c1d40015104061800ba07810581880300c034800300506041508045241c014800c004001000c3c00c40c1c0302144007440264041c2e090007904402c1c50340341c03e05000b840c01c0000d0301e80081041c214109880300301e0750085400400402c0c9003040b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 812433821 1250 812432571 812432573
    0x513241409091c0302162406081207170d060f030b01050d030f1404050a09061e0303020a020f06090613170304060806060c0a2f01030e0c0d0c0807080f0f0607051204 72
    0x400103540b407005082411034181d00f07c1d0f0b00b040041c2c82c0e40c661b04c2c41c41e007408080d840c0d92040b81c40d0b409010b04180f00c40003d1004000150410640e2850580c00b1062142000c0e61031006030300395500c40c0c0c0420742c02603c808090080c46004200c5034050541600c0301380303040c0c091380d50082030500720104010410810740c0080d801140c4d0300b0110b80090000803c3e00d07030203688510f150401801640b0130f1142e20100c0d440c3c004940110b0040310405c40360942c01a001d9080180c0900c034401d48100d42c3ca0f03500440c100400c02c8140d8454020381992071201c084100910300b010710880c02d0303080c180d0400030564000c0c4020040130360321480d080c1d8400d2042c1c0c0e120761185000e218003840c001440000034904a200003000210206541862441ca9185005805264032000040d000c64403100001c008030303003090305000d459042401012441c1481180080101a621464a410103600b03030898111908070291a02c8000001c000701004004004081d0280c2c0c1070101000d8450303c00d0420607646c904806000070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 812435071 1250 812433821 812433847
    0x9110405040c05060f04080c09040209010e070309080a050d0b01050c19051603050a0c050901060e1017010f0e0a0b0f01082d0405160513241409091c0302 67
    0x302c010f2001400990711881021545029900030303001d9540c651044464034002407a000c55600d00407900940030030040e9007048100c60b58003100800100505482d0410785000555840052403c0301d40382c0d4034aa101c500500d44030003550144c24509041040622204141486c04580410382114442d403220580c01c852501500303000301c0d120b8040882d008000004140b04e0042040da8950380300700c2044400300c1d02d44041006118083c0221000540342d11000007260820304c0d0103001c0c030545030074030710115894007510071204442600078a00c1046405010443c0e0603c0c0340e0803d8200e401060140640604480440e1842242e0a01d440c1001500700100d8010903d400c0a80301694800c03900d55202016803c2d0211000000e440c2160f00d4400d10341d0700c411500c160388100050b40d400410744000c0c03101e19541c00700501500340340703541b0120070700e1156800085200115001003800b074602980c450f03204010484201401020060690805808042c0c01030001800d40b1030803c05040058031a60360007409 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 812436321 1250 812435071 812435093
    0x30a0e0f0309010e0a1a030f0705070c050427150b01090503030304330c08090606010c12050d050a0609200403030302160212010e010c11030f030702120f09040f0911040504 75
    0x80500340c0070301b801120b1000d4410021803081e4100030070700c050b036100c40308119524414401e002d01159541041440180351a411440c0034100700314110320b0814072905204108150540e04841d03010105629542d09400b6004108080100b42005034100e850b10012075101d01c0014001008031451000024442e6100f400d111041c52091030600f02000b080c403000d40081c80e600362900086400200003604d02c290003d0054032855040e900d9207030440c0b90385c2d510110754003a001c5000500c002800240000c075010700c102ea10a0949141c04124549021002d4040b102c50034103800950019616000211003820110303002c9940c18500117039900306415020300160311100c07009500c482038050000b85020150418018111f0020080100802c0c2100554007803842c401c01e180310303400c00d215101c00316903a07501442e88141070740181ea01c190711282201009500003d240401c0150105010105080500c591200682e8001e8108070300c2c031154481620682d2902c03051881141c42c0c02c00074003009034450701 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 812437571 1250 812436321 812436329
    0xe0c090102160602010c09090605060714030c0d200105160c240507120b010215091504030906182106090203240603010c0c0b040f0206040605030a0e0f0309010e0a 71
    0x544008a8883d180240a0948491604006610a500404c014a891154400710788005000c1842c7c018990385100d150000280b8550300c0780070a2182c1e0380c40312018460010413040d5070361100c203100f1456196815000e4410301c2b91545a00d80000c0111402c881410070040c81450b040c10b000410b028507110980c8520300342119000c040070700700d00b0611000c50308803e00440c07454170b4001000704030324200800c0313495141a140c0160700001f6011411041070117003540003602c0c0c80a9607001c40c0071090710402c082054038220006200040304110700c0d81e0014041180c0320b0b08400c0b0800503494503109500c45200c001022070083c119640d10020080346500c0311340141c0d405410380300b40d5844007d82c0c00c0c1c02c0516a0300040614207110010381a890107126050501185841d80703042c0540645079017480c910000c000b2140541484030303810259881001400040c2003580e2039665900d0329565840c10b460045c4c82061990b4000c0e030340300039615400b10699503da4028a030101103131501800045c540307001644 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 812438821 1250 812437571 812437603
    0x51e040f170d05070c051209120d0819021206010f1701080d0906050c060c030c07050a0609060c080402090402011110050109020408060709140f060c1504060b0a0e0c090102 75
    0x4084841c00c207545028102400d8210700412503607981010640700105c0d500001010740e08468104200e4290a4000e0702507030740040c0841d01303005094070359103150010703010300880495080001c22145824107400c1c82c0303000a00c0a010b5090909030401d0841d40c08010780704070b060110880041c1270482c8501802c0c103001c01140c4140401d0b5a403107504580701c00b074511010001a920a10101d40a40114121002e004c1321000425055441c1440c0c04070035080941190b110320010004840840c50030841c2c2c00d04607000300400144d6040601e849022500b60b403140d14207000343c540400015036a01341707895500c0740c0c0a00300389900040d07800c0781500b4120030403901d40c15a894500081040705059014000341c1307400c40112817281e11142016140c42034036210303410041e000c2007000105030414801d04c80c203046003c5c06c62814240e1400e84c907410058031104c2c00d51025290420482803114600038004401000d8a9034500d1a0900f0f0380c01d12103400080058a411030001080280c90344200030744102d81c44000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 812440071 1250 812438821 812438843
    0x33509061605162103022d0a0303060608150102060a1e09030915090b041707030f0605060316060f051e0c030415030209010c1203111305010909051e040f 67
    0x80d21a480041c0030b00600503545107402100c50300c8614683c0d18503206170550010f040d0880d4400b01c1d01d00c0c6d81e55103580a89000c1110409066200b420480040860b119490208901d410a4401450f140c2e004021041440d03401c2c412440d01d903004121543c00100501d00030506074500030241000182c408010130312689002c010109156014155000b50b40400125105421414000300d500000902800341c500b98208410800c5d105002440000c40d1290030964000360b940e82c851096901203081d0a0345c4858445042001900d418443c50802403070512403410900e06010008040d07107201d440201c140000091009003007074244203a58446840174403640c6d51440c420b0071a9031660414860012030015404d61030145901900175120302c0e04069407056032402540c4c4840c1805d48401d000d0f40c09240d987c5414280004000300201103806210304c3d0100a50701d070800040469071326a1142d00301c0342c500800d2000508007550410345c08107039030700780441d10b03203842c103140c0c06005184000810381000c00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 812441321 1250 812440071 812440093
    0x60b10030b150705060708280b180910150e04050d020f010509030304150b040f021308012007080d230601050703020a1e020a033509061605 61
    0x26800c00c0c070000360191841d40e40b101680d0981d001034061014000d00c2904041c00203000d1034490441c0399840404500a0b11100c041c10700054408900440702c3c2c0720703213922900d00c070840e401c12050a2083d0101c04c2d010300f02500d1700180540d225404100c1a010964541c000f0201800d603501e41a005800d00a20300085030500c1d141180c0d913401c00580c80c20144c0034444140609031411311a0510031310a07000035500e150381d182d40d44a00200990100015182d59030801156a140ca100c1c004848089010041c1e5515041d001d0b9640b590440e40b201440741c1c14041c5c452040d01c03440301c0d00040c00c0c1c14500b4040d201c4410b8a04882c040c020b07507001921046c80c1c1201840c0c41441605c007540402d00d00845000d0396101c0e1401103409224043e000307005a8410481e410014021540b01181040d41954a1400c00700039800a09045091f41c01603601010040702c801c1c550541c1c24039068583c2442c0443d1403c0c41204819603664003e00d09078a21882010540c0900d6900140911f00740c0765002086c1d44401e8030b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 812442571 1250 812441321 812441327
    0x120715020f2512080f070309090c0818010c0e040b12060f011d071b140a0b010e01090b010f080901061205150601020c0d06091505090f2b0c060b10 64
    0x31080c0e00c0c1c14002c82c0510008080729015000d4070010303001841186020b4480000001c2c03980051422030410141d101d0000d5062003501c02d41510349000d9032181000d0410316441108489102900305069142c030341d410030b400e40c021100e20703800300c0182c0b0007142350303550328002a02e640e00c0340d011000580100c0c0204000700c025483c2c00e0b03050720020b401c05848500e8641920102000442d95400030a8900c1c00070100f4445881620f1740d00ca12644140500416003000a03041c01030030f43c8120b56003c0d20200502c01070182258a5024140d55401000b000b180c0c400003c0c189441c00382081d040c4001d603004950310071404c0d080135003d4200c0c0d4400007862541468a269140240b6483e000f80503885030103c1e11030341c40841c8000202c0300041c00d0384142401902e843c0000c02c410981194009002240c206010910303018040c4200060740203080f0940c620580c036410300c002c128000315100c0300c03240035810040070f100d1481094400c524214800c01e090303103440b0004000c0405600c1d88000500f010350390040e4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 812443821 1250 812442571 812442613
    0x301060207081612030305040c0306020d0f0e0607020d0807020f010903050d0f110d0b0d140a03021c090308090303070f060b0a140907030c120c0914120715020f 70
    0xb9180d0202c9261004036444041e20768150301034225440c8501c00700c00c000c01d00c2900b00a401c40c4c010030102d0000303540d940e564000c0b40c2c08641c80100303580e21120801d803081e2081c81504820045600a410f1510700418000e44410303185403500240000503004c500d404e031003000010405a03504000f00900c0926003000f41c1290003102c10a00924141107011140c20618001c9404003080c03150600d080000044408028008001c030880c1c20120a404520124070400078a142002400002d04803076a064100241084d20b070985260303030032040003150b05049a0100328002100c1d001451140c40b001c645001078114400c4520103000031400300c0c80c807000e10406602c10030301220100e03a050b1582c1c2d500c03030f0342c6801d80207100c040d1039002418400080304507029803c002c0c41102a0b10b445618a021162208222402001d1000c00501c04c52000c1c8026948400e41d100c00c8141101c2180010003451205556a03c1600900100001501c41c9a1846000300010502319031120156540100c00400c0740b52611 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 812445071 1250 812443821 812443829
    0x9240f0906010f05211008010b2d03060a060801050705030108030f030604060519080606012c04091a01090b010c08030411121b040f02040305070e3301020606190e060409080301060207 80
    0x101b00c140000814400503c5034000004025244803100190800312942c05013107111804007140c007121003088942e4003030104912410fa1018001855424140310300c5c00c6520080010060020030001440040000003e4500c83c1103540203480e640e944540202c1d01901d225071201d500701030084502c00d8047c00b801e2010058540c02411514203507942c0004440d0300c4500ba600c8030a001e4649018101b00712a40c4030910340030406840030403c0d00b11580c840710084c140101000402c522200140500c224a014040c41503009280c80601080291210829440054002000c1141c4600300c0707092602c0f80b045c1c0d001c40600201c00e4850181d520104001348078006800e51384070714070b403901610800d0401e20030788043d01e030000000d01c001800d0150802c2d021802405181c1d0002c0d0012040c0c0313004807400509a5005a01240102c000e03007070200181c6080c0300507282d5886070f22004040d210495816030f8a604403440001d00e0082c94403090040781c014107507001c5c003500310000000003140c180e800064035021a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 812446321 1250 812445071 812445091
    0x417010f0c0305190f0204170304151d1c020310020d060f0e371e1407031d15040302150106200c09240f0906010f0521 52
    0x5207075500120101d0304204c0b14244a220040e100c0508002d0540c0011003c1d81c00101c0185840c0e192110075000d03050752032409407180d00c001410b010400c156102424072070014100070582c5580c501389070000d5400d003030320180034030700c407900b880d620201d030940d150100c0d40c016083d5101d11614001c0800650710841c61001c0d002d060240000c0c84d400740441b10f42c1250940f0a1583d259210008500544e01e51a90207030401c0c01c011a0700810704c0380c0000003e1f5100100c401c0010303410f007100c0034118210707030681c0309022042c46c101d41251504000c80700103034800014600059001c06c1810b411440c0e00d08981c0b000e02600c545080200c0009000d01c0d01ba0040380a5000c0390f901c1607070003001e18045502401054000303818280d03004407164061102642c0b641d112810f58110742e040c2e201248490300100c0b941c40a0741d00031030181c1c116191907010b0341b02c0201c0c1640c814000c0c030b00f21070200f10141c031701074950b81c100103540c01c025044a100c0c2d0b050ba012075650103951480c01c898560340045003c015200300841d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 812447571 1250 812446321 812446331
    0x60305010f050f0f042c0a170a210f090c0303031113090b010507050d03060504050c0c0a080f040b0d0f051023150f210127020417010f 59
    0x183c6800c200c1c032598402c0c010824640c0400c0340080c800500001141d10725098035000006413500811000c5910010b240704c001d2000e0503107800c0403070003600c0e20307180c015010303c04002905415a0158000e0b01000001c2401806c244000348414010010074200c4622a442d004820702046008210301c02124043d940910108048849001d043c1c419250b0034074840c01681d400700902e0801d1b8000d90141001410141e08140345525510305100503200900d000a55600302032142e440d042c03003465000400810801c2c201195003510950703071403c503000070b480310344041504100b8440301c07001c40d405088124411501c80300c085d50b0781405081806003800c211403e120000c2c00e40c51b044507160007129080306d08645031501c140480464400d060082c1d5401801d01a0b070704020b561080010205c15180741d02ea650350303050340c0e000e00d0441040174a0501c0743d10b09000040121501d1108041181022810510031781c2000c05040b90082c03090707500003400c0049079801601c82007019070160100c000c0c10701d01400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 812448821 1250 812447571 812447579
    0xa060b01020c130b030c060a05120117100b03010f1409010b0402030c07111201061d0c03091203100f060f08250c02030c09160f020606013006060305010f 67
    0xc1c4448141d0025904001215140b0160300d1440c0c00c4510286409026546c0d0280d5030f03000302d1841d0344170302d43c4074000c50030000340c030115806108131450040850324841d902d0b044036008007640324556a100c296200c0c4c0c0b1264003010b103035000c1d0b00c0540462002c0000b0042c19180708070b01d000740881100c002c00e1551820641070158106402203c7c0f10b880c2d4607a01514164450303031030420001e4a64410744c0c00c41c0142e4020401c40d0001d1064201511070f41c2880300401c03030f07001d06420b00f042c0c0007000d03800d00000500502000d6400003484454141c0c5d00b000d0962640e8400007a1800428207900c540109540c50750b0000300250840d0381821114825981c2d100b06070b030754001d41940c943c00e81d0101c0c0240400d09020360f4900344611510880588014140c481503103900000608004050f20801441002c440728003428ac2d8101420704a41d43c0385001801d110315151001030703c0528854100a1442c15213052001100c1c65001d000140f00d51511081100545500008004000034081c00b000c8074070b1034a01003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 812450071 1250 812448821 812448823
    0x60702010b0312070303020909090708010f0e0622050601090b09011509031b050303030405010203250c0809042405010207050411090d23060f10030b0612030c0a050a060b0102 76
    0x2007035500c1c0034004001c807492201d900b4001d9404a88164105503080c00640030a0b91840502c83c000c100d482c0040403120b003804803250845100e0804483e05074a001c015011501c00401c1040e0303c60307401e08030003040031010700e41c0c1c4454a0380754000414a008140001c00d5030302c0160b01103025030000f640d0318016a030300d80d0300a4480340340480c2c002d80404c2c0100f100f0400103022800c4486150102c0d5083e03e44681c1d5140481d10310f42040e10201c3c3d050b500401000118654610103402540c442c403890700c280e0b20304a1000d00200c1403480081c086c02e80004550589403110b0300052269000c550340199907005ca1754036194a0525805502e005005120303002071586414010942c4a00c00b1120861512501100301326030ba19035440c0803178035500c0e5095501d94090340c0711151806009000094a0180703418000028501402403100c04c0c2e18004003014400b0900417015241e003c0343c10346a8140140c081c4006900c0c6008000d203800130f52268191a404100d0046080c4100e548900800d10502e8407101c016 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 812451321 1250 812450071 812450081
    0x30a11040b120a0e010612050c3001090c0306051f060f03021803011e11070308041b050a060903060e0712150b04020325020a0215130807030f0506070201 67
    0x814003000e100103441411046010b036046140c40500040540020800c5400d55441d548100c2c00082c501688034140082403064230406001242c020207111080900500b107003035901860304101c8030052042c4900c40095100703020781ca401030780441200b5900d00c0c04801403d13003115101543c1410700c0c2030010610740c00c011141034580075101c164801d11020401c900a4010182800094202c2c1c614003049440c00e2280701c480b080d04000c0042440c010070880c0007500ca8074002c00d440d0410400c100303400f20360701c110f042d81c001794001413581182521103402c80d551103094010300d60080024400161142c0c0204481c0b003240d103e03200a00c1044441002d0030b031103441d035204070b003040c074020710103103000032101241506000303540c0074001104040c44e00807030100d801c1213401c442c0301207502d00000c0d18030708011101161241980700910700814542d0119540c0300141011b200c045402080002a52a00f041140054a4900304407448690742e400e001c0d401d014030381402d0311180160004204402d00c18012 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 812452571 1250 812451321 812451329
    0x1c050601020d0c03051608030106110712031d090a1d060105031b030307051b041409150a18080a111c080403030608100e070602012304050f060408030a1104 68
    0xb4280705480344805503414a216642181040b00c2080204560303080644880d1540303004000c22503c0e5814844060000c00131228681c103d076100700e408004000300f80000717030141981460200d540701081070140c040352200f01e0013241d00c03d0031501003026031803180c1e105003507019107024080c2940c1c200741a100d489174001c0c080c6a070590051008070f46030380e4000c3d1441c07005d00009011130340b50410356103c4c11b0070030700b50148943d101880c406140540d450030340200080740541d03a001031502d041049810356a9000340c0c403480454184036000800e007051690003400415480820a020325405282c0b003d15907119844103004101c6147c08881d584c107002071403120102d11181c045849d40ca1000d015914003900130310480c20940c913520049204201802400142c0c82d410201040c0f80d400300c005d040c14401e02d42c1003603046a00d02403080d52101d5a011002c80130044890f20305801d03803a40d08250382002c9100644001902c41c44041c0800c010465004512841c0001010041051350043c40d001c24822442 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 812453821 1250 812452571 812452573
    0x130506180f1e09060303070b010806063c03010b060703350703050606041203020c030105010905062b02030303010b070b010501030209010537020a1505060a15231c05060102 75
    0x48007250b604004001c10f8101c1c4005044a0405c00d0990b11124607010036000b12071140c01160601070a130914414110b1143e140d025800c921003e0100841c0d08401c1203000d18a609119461416164400f036100c8800c02c60f0152641d030344e840050402400f1504e1183c0280c04514200098102144450240318801d401ca0543c0356059100d00c5800c90140c8006004940d1041d4100070000e0140280c03039128450724400d030080c0000395007100416085840590014960500340340400480d50350700b1404030b030110ba1254494001c030703c500d4a401030294414100a405101c00800452000070110242104510036201c03083c0d00e81e2101c00440c1070f1f0046228050206000748a941c450708906100065520810710200070b40f00000343c00da0300e844000b00030000c05a04070130806014481c1c5100f005054444c5031b00284885c2c101040440c207a01b01038856030702c0002000241d000c40c80d100d4460700680014460000d00d1078850010b9400c00c551100d802092802d00255200e40c00314014080d00380300f000c050b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 812455071 1250 812453821 812453869
    0x50918030405210a030806010e040b0a05150c060112140304050108040b06030a02041b02010e1f2403150c1716050d1802041409060705130506180f 64
    0x820300c81e000420500fa10085102c1c6480700001d003000b0040c020390b20b0300a0741da2107001c0c00e01e14009028000c8010714180114101509040320b41c0315000040c0484500307a501c0b0a003841842d149070071a0180d00e4101c22103001d101c000146804070b1540a144070307400b801050100e00305403070506a507072040380f18403800300e50484002404640e04084065102e8030140036030f0a03e0100b03500042c121482d03c2c0208204094010740400b0380d03982449050005054540104840050103c00100241141801c43d049580314180061202e407030540c0c4c03800c01d031a500304d00d10906032240ba00034a00001c588110861610f42480c0404440c45407040315a60040410480d0ba15107070000d60102c2580700200443c01d00204100da010441c20a104000c00391850501a10500035248104400e4071060005402150705800034040c0e14103000c0f406541002c0b43d4102281c0d103524046082c0c01d04c605503807103a503004901103221070f280c20088a00e41802c2508558240440c0141e02c2040a0b100905a074884044415 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 812456321 1250 812455071 812455079
    0x60d05120f270a120b0f250c11030309150f071407062a140102041e1401020303090d030902030a020d15060b03010f06050c0a290a020a08040b0403270509180304 70
    0xb01c00c1e0b150810031a074458850341c400d1480350040c0040c4a58847c0c0010800d40601d410709c031a02902c00700442d4102c0c080d500d4124a000050b12421103590800200a40010b40c141c02d1540b0400311000c8a40c4036480c8034440c0d948054860319242c0c1c074803aa13004200258800403603211920003226401c00e0084645c9618040e035102c05034140f42540080388150350802022450607415a103000740d120288181420321824401c900c000d80711790814242c107542c818000c1c07107110b54000c80d0005603205a448c2c0040c1c0c3c0215400082e117010341400703000e508000d0303845581040c4040ba1502d0882c03100268028428a0359407a0040701502c0f00344128903440c0281a01444a2807282e0000c0402d192408110b0b12080300c1500d50401d0205800c0d140007009010b04510031010050044160307002581e082c0441c109205800007a2550100400040c0000d0340900042e0400d40100207202181c2da0700216211000c20005100c5c101041c1e500910703218250a20010700125030b4007a030f11100c01c00749006181480e01e4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 812457571 1250 812456321 812456341
    0x16030b0c03062103090a0504090804030201081308070818101b050f030309011b081909050a0f030809070b03040c0b0c120f03040308060d05120f270a120b 67
    0x4040e004540c021416895142500b03019482c42e02404030343d0010b19074803800c00c0208807041942d5441b490165080440c1c407c0031a02a009071012642c0a09005035a5a05c444003c070903141412401045d0040200c0d1240501c442d05c0d01034201d201d0110b24059030000000c0401a80b0401e4024120001d10500741c070200c041d0342080c2c0340300c61600c00c00488404503090300d9a6401e540007182e490340c01e603544001411202109220041042c04541019022410301703001d00c0500740c0b204c43d8801503082d2075040450410000700003529910350007500028008615240c002c18641e4151001d600500ca040c10100f2000740000850303000f6948000715802203450400784850039003142c1c000e1080c500030404521801065800100f140d003566282e5540d880c68585006030060601911090003006002004000240c2c00552800720171600200d2607200c9a40c0350101c541c9100d032282d001c400d01400000038245115498481001a0007220012803068480c02d80001112620308064200e01341540480d200f05e00d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 812458821 1250 812457571 812457577
    0xe010801050f1b09090f100b030c040b07030e1c11120a020f1206010906030c061b0213020d090804030b010801090b01060c0312290102030f0406030213080109080c16030b0c 75
    0x5070b00307404039050003141000036035040d41c01c580c641b15410168007081604004844075402400e0101401d80c20b50502418a0b03032280a04d00a40d094540001445418103000d1100c1c2009200001c003402515409120b600c0094803140100f1500c00c0314122446020b0324103070742101d01826800c0002c00c1a1100c41c1c081080c01c803889245540c0000040740220f81c2a0001d00c169400b8000da00c20104030300d842e41c64140341c1000b0f03581c48a002c01140c140d54042410340440304107a080c0d01280d41008032051450101c0c002d20410b020044250314110b800740030850814064412640994080d5107903a0740c80d40071500362404008c00818a06010740180500c40c02554003210150192404902c2c402c0034501c21011205011207840d2440b8805503500b02107101107a0304c110962007880a5414195989820071160089000d208181034011070030901201c280c40410000b009900300074003042e1460305140c0ca032035201c190403050030702032062081c0d01c0e03960107000001100c0d840351400b04990b644c03162440c0300d90 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 812460071 1250 812458821 812458861
    0x1a06031b0d05011b0e01210c11010204121434030203060a0911030706020d050c241006080c0306040c03022106120f0c04090507090f060e010801050f 65
    0x300c1801900700c04a40244540ba85200b4282145072000500d00006000d1781c600514850410090011640140c0241002142c0781c0f440c3c40004280c010309840c0a0b555000171034080742066102040005008011602100c0c4850043c0204140c0c0c50544801c01e8840351507418000c01d000b110010700e9000d1683c1c0c540840f80c0c0c1c00d014440c020403616a40000d040680650f80d00d0b42d400d0715000c514051140f008806500c07010304800a0190500d408006500e074054941031b88140314011a8034042c880c03003801511000d1107030f04036500d99058070303100360407403101d0a0700c01d85032000008602080c01400b5000041c01000d80342409810b40c0d441c03404100280105420880400d81c0910801c50754841501800e66440d880843c210032514004003440b1000c01042040c4403280c0c0a6441c00c00c50740e00101c0c41c000591002e03900800c2603502e41c01c1c82032400400d607020b480b0441c9030040c0c1000f0b040150f444102075a1115611008599036440030398240e45083e900400340140396000300300340403c042d0000c0d08803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 812461321 1250 812460071 812460079
    0xf0b03070e0d0f080403060e0c030c3001021e0705030403080f1c0e2503171e030115140d0c121a090c040e0f0403090e0703091a06031b 59
    0xa11481e59550f512003102010841e4034020100f42032040048034003441c0510003001008080340b40a00c0d000941c0c07920b1544200c1d00070f031018000c511507800401110b2040d41c4942d100d01c01c140f890800058001d5100200c80051540310300c688203548140341045a00c0303e600500114200f6096845040303459100e0302c04409071090401180c09009080043c409502940e80c40024284101211072801c10f2410351040c04510b840400003400408250076030002e44e5003062200d1031003050b50380c1510301c0384070344061040320b00e05032005049002112801903058802481c4404020807126409130b41704402c8070000301802e00144003200c14154541d21100d400d480f84d26000041c0d42041c00001c003210b0085c03410308100110b0f10151031542c1040301c0c400f9004174850351010304d4031b45440d03942d00380788201400d280301805062011905240c4204001d01c082c0580c40e01505040c20207000142c010030554504442003070309002007000400e44034131140c5c81001c02a01a0104120400d40201e94001c009940390740 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 812462571 1250 812461321 812461339
    0x60e0c030f220302010f0608031c020c01020909090604050c01022e0f0c050a02280807060e010f05010e18120a02030c151b130509220b100f0b03070e 65
    0x40e403002e086000d1145001c0e400020b580a681441503080e103502d900603d1056004000600b00b42440c0c400414800182400058451a454a44070f0181c86200c42e0b05a21404070414807040d2000491440e001c0d40c82134049850800d48030b40166222f0711003101c00400c54074800b218240c0c0c0c90001008640e001d0725240c0004202408180da08115506004c084000480100c0c0314100f0340d8040000d050071400c1c03003841e4a03c0c108030703070348030465000300841c020300c8010081515402c10095070040b4042a0b2000003d100e00711108192800a140901c40c40640c086418045030314040d000080643c00049000a0148803582c04840725072540016030300d40031840b003042920200c00301803000b00781c10144400740f0907050a02440600c449100d0030380001100004010301143d11144281d0f030400c1b0f41c0155124041d59a9a00f402604914074400020f8510381c02d081c2c0e01d04001c00109000d1160120501401e0500d46407445401c14a09601400310541e80803c0031030506801000283d916040040540038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 812463821 1250 812462571 812462611
    0x907032f0a0b03091612022416330509070503011407020c0a061b020d050613031b030e190b0a0203300a0b0a080d1101060e0c030f 57
    0xa19808541c0301402d800d0020081c0300b800f42052200122140081c11078003081414046012904200784400074421026107803820a09642d6144084500910703450150f164141d121110402e982d02d150212000e1790030300e07000411007444604042c01180c5001940040c0b0500745940801820040c0c44801b040c842c103440024982e409006030003541c009500240c4103410500c4000e4171700070b00081d2151150040d408140800d980c04104440500e0442070141110b100307a00100f5003000c0e500030041c1040c0a034004000300c1048440c501041940f1995507940002a01c407006080034500138001400503c52551142051801c41c0f00032080718a120001d4031626912005100c03958007041e078880250f04089174521860301c07050460b00245070042c204041404080c9035591129100901d002140340d501c42410900ba210018a00041c20a060450f10b101151840203003035402400011015503081140119044400001442c024614154000c1c00c64441d100110b4200300000c0a1091071440380020790 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 812465071 1250 812463821 812463829
    0x20f2a0a030c120c1a1f0b030702060601031b050d1112251709162d08190303090c060512150a060f030209040504030e090907032f 57
    0x300c0480d00c07a8440540500c0ba51901e140d0603080950700c2020b000100100d1404120240080700c5400140e0b40390003d21b035600d2080d072102da007190b403c8070910b0502c0b201c0031030b403c0080c2000758011041e94084890300e0351128011019188a01c0308400c41001c0c1071003805c40240102d002d4020705440c82c070f002c00c1181d50200c28410340d41202e401d10800008010074840004180f080101c07202c085400404000e40000d80301400980f0b031078204507000c1b0b500f5800500d0111041c0251491110440510389170540e84094074440b0001c11444403d480c8049008803881c100c2500c420b00448a204010f491030400d000c400803105c114a280603818180c98101807800104d107600000d01600d29620303029158000307904c0c03150103c0b40007021400550000a070580050380c5d0180b0031411a8460b1500318280c07080c10350220007901800e4011030b045410b000900080640150a00d084110b0a480000315503607210400caa0300c0d001c3c0e12020700038415052032440807480030459580340382c02942400b544011041d001c0303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 812466321 1250 812465071 812465083
    0x9090203161101051e04020f041509150524070b0a0606030e010b011707020708150411031b0603040c0e04050d09080d081812030a0209090604020f2a 65
    0x42071040c20301c1d601220145400990a01226145000800076440e1800074503007494882c900392107000c84020001402c40d505c00383c0c016580c0c8006042488030080c4540c44101103125805403180c8903040c410705505920140036288100d4400421f4510951f607014180c4001c165070003400e03501c80d0020401072003c60a2600c51038001c194091340003071341910b4080002d040b40d2015030b0041c5240d0400c1202c121580c0d00c803040078106500486403924540303403000c0607860040c5950001c21140146940c0a00220004d40002d00c40d40c007a02d0f45175034024074101050340300c054140e6030581e00c14401d501d4002c1400c001c0083c5510621414001450310340b40c80c94510041c50072038084959602080c11004056480460078004101800080c090a8007440c4080e1281d03070f00514128440c03003d0b02c0880c00c0350340100038030000316452014403680c0e81080350902010398000030b0154095014080801c810342490301c21542c0607181318203203d0500c213110f000c5c42c0c1502c0c0ca0002111559803041c0c0c010224150500c54 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 812467571 1250 812466321 812466331
    0x509090c03060429010207090212190f090317010e010b0f03040c0b0f031b0309030409050a15030813230d020103090b010b040e0108030301050607080a020a0c0605040e1605091009090203 81
    0x4050135003d940000918000c595046510114014000481e1240903011015045841041641040e40030084108005c00340401520501824110040213040c0c200c0018400c1e80e110714286101030382c0701c240112503076000b0310a0380700a290400229980c100f600d0302440d001482200b1080f40f0f243d40364440000e5030030150039a0b407006000001c3c00164006440c0d4600341400c1901c0701c0c0d0451a0000c00b003902c0780294800c08122989607000141c00c06665445080c0b45014400030b84071058403810040030301d400c02d0b01892803c1019140229116501c80055100d408002c440c07400e0509844050010b0030051400032418140c0381d1600c00e0000d2020080039021b00040904c2c2601c8074541000d4844008040c1e0100c00942c208000602c002c2e141e9904403411240c0007402030703644201c2414104c0c5000c0d041140a001c5040d03081c40807a1340740e0b1100082040b604c14103404020741d110249040c42403440c0412417400305008008540983c20b0940300708401d540340f818903003200c0d9501c0d26542d00740d03401203403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 812468821 1250 812467571 812467631
    0x302042304030f1809020903160b04140d06020c0d0807030524062106041118060306060d0603033609050907120c1d10030b0a1e0911010509090c030604 66
    0x1f60103d181c00c04200450140441000c1c95090318540008119140b045e4080d40030385280f802034100e5a40c845901d0841d030365501440031943c0721a07120500d600d0301064642600000d9441c004248002d00c40e00900b4010f030300f4100e40c0c40c40c00c1e00040d4601c0401001c8802a40c00c140288602141401400440c6900b020165429030a1b45800820801115090500003440510510510350804240131302586071034070940c2c1040e0381e078407990b0004240307010700020080098280000031040551003400740c03190030002e200d1308285c0d51030210107c046448841c01c503250010301a904000c0b41e080c03600141c0d0401006410b4a40d050340302c42d25805140d8041c402994030700300c0e1000410080d03541c203115560221600e076140100e0701382500e40340130824081c40042d28080c060070224203610f1040c2d0280484003010744144031000540245140601180601074401d01c14070342c0505a154010300850399810b0b0000d203030300595034038907146892981000d0720300e079009076071024a0b05000d1001118cc0c680c0d0301d075200d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 812470071 1250 812468821 812468827
    0x20d0807050f0d090f0b090102090a1409070c03050c0d18080105011809050c130e0c0f030c060d060302030607050408010c020c0105070b071202040b040302042304030f180902 76
    0x1050181200002a054904001041015160405080b410707640040100800465082082e00304581c500c440c03000701501200c4110305202c03030b091055004010130107050310ba0506150791410215002d8101c5503407281c0010300c84002446952143c0c010020861080c1400c0e410101e40405081c070388154840b101c1c012030714508481940c548424041c2005104540c000d00c402c1d03052207151043c8074043c1c0d5403003400700c0e1144080c0080101c10300c013403070b0034810152070b031503003c4a554403007009840f680d00c0d9600c05000c0e0115207105800d00d40d00ca54443e4901400038440e52140206000140d400030264242540c2d0701c080100059900344136140c040d400c25560140c0740d606001c1d21908440641c1d80700d00545d0b0000e0300420300c60342c01c8000d54001541111910000b40c0c1c031000181c1707503540701c0012010814400100840d0541020029000307172402900c082001c40050080c00068000e8040410b03058070f96400080c001030b108909041102545252149401803061064451035519070040f0807215008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 812471321 1250 812470071 812470093
    0x5042109050915011b03032306130501030209060d0606090c080f0a0509060103080703031803030617150a05090703050f0a0b060d030f0509060c0714150c0606011d04020a02 75
    0x62402c943c00900e01d440642d0744912800011303042d440180c0020400f240c0b5035500700c080c07501139880441391944042c8145140d140040940c650500100c038000d1064540081e19003500499102d1103042e81d601038241d080d2900c0300c07400c102c440c030704018084961036103402001c245070000d4040c040c3c00c0812619407543c3c90400b40c44103050010000d081c248081d01c0d180c1001602000051031504480d04810f07601e9441800b0f040440152840203490251b10950805000c00c0643c507a21000c100c40c070300041141041120400306480701c5000310a5003148804002080300981140d000c9074210032101c040300c5000b0717966035450f0b00f807010700c2580c1d1031940c105040e5007081c070005041060f0311403400c6920480344151660058400c036150601101002000700304101c40d074403083d0880c0e8902034102d041700c007800e1f40c0d04c0c0c50001070701c007000d401801119104400c00780c5950a078103a0b0780749900080a0f10660307403200c00440e4912804828504003002403107012800f6101d510003090400c0c1d0b240c3c09002c055040c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 812472571 1250 812471321 812471329
    0xb030a050105090708190914070501080c0406231306080405102c07050a170c0a0614030417030903070b06100207031403130b0301181a040504210905 65
    0x305038032a601841641041000c00c65100b00d07180e40c0900060f440b407030707035105451040b8020541e0043c01003080d40b00c034006407245040000d407101140c1091340c3e9000315a40b040e40f03410710f50041d03204600104a22642c00000181407a6021020600f41e4858509102ca000c001a00846d01e96101b1000304180d1000c1c88240031083c0b01d440b4200b8084c51082c80800394451460305c462a4142021491100c120030500c1d40358001e204910017042e004124902e6240c0703c4101005803440d080102d4000d10443c41214640d045c140300e1401220501e0b150900f06c00003504850300241d1004000b04d80e42069003400f070085107003150295010341300c03039030084d80c44450a24000b900c6a40240002e8420402c081b0311a4295500140c075805032644154600a4254080c9189155020300030326101d42441c49040131a180034284080c1d81203400c445110150082c0c1041241c04036410380300600d55007448940d01602a040682146400c144108044041084101c1225881c0c00c60200380310000368000c14100254a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 812473821 1250 812472571 812472581
    0x5011103161206150302281d09040b010302090406060506070c1d010506161e12080f06030312060d020a08011505010509030a06111303060902010807022d0f070b030a 72
    0x560790b078100005410b0204003420b59540320340300401c06800042c501440340805000569507a808084d180711800d01010282c04128010010081c1c2541381c542d802c05450f10303003540c601450300861054080c0e4295001d00c00c10480003401a02c140d40c07a00000612510b07280000e28145d8051100040d9103814821913005200009254018410610005100941c2c031882101c140e10f50305500c040c0000500e10b040e0704500e4401201409110503204644180244018a00d03165100f956800300c0350741c1d822510b03100400c01a11950b0701980103005003c1000840c81030b46400c202c0091a0b40d001040780d80c0012003908e01a00519440c0c2d441760340d220f800082c0c8801c944054031003400d0140c203000e09100400d50320104440003800c055100c10207000262150400c480200c002d00342000317a416281c0c2011000380c03003190300880c00159118006012148003084040c00d0404280c0e559842e290904d600005001e00f854070b20641d40612414000410000c100321030043c0100211907481c0d150113602d00d41110 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 812475071 1250 812473821 812473847
    0xc080307020a060f0e0f01260108010605060307020613061407030c08010f0b18190b090901050603090a021e0607060b030c031f050a0f021c05071b0305070501110316 72
    0x30a501c13070101c189581041c40740074400c400380e4a1203207140e010401250303200c01004003920250b2405503c03405070b0f132102d4611810388101c0d04c001c2c04200c1e601c42c188400e502c000c54030100103822410128540200b80c01c402d10705940115000b04032819103a402042620007652444003003540c03040d15008254100740000e004014000c07540d00e5481c50483c178103501d0b01c94102642c0e071602c0782d64a208082c0d42c40d1001580c0c4005a007400301c2086403035040d440c01590000302c08502c50362101000044030704c0d0040c1168030035240303040980503a850503404c1c4041c000d00750304000f03d441c01c0000705000319161580900000344c061600401d589200005050138000400c0c1c4281c0a43c1001003806101c5200b91a11200c18a0306180000c0c3c80e59001c0f0800b00a0030440c0e02030451600001d9560410f1b510003d08121840c0000d10800c0b6944075840e09640c103c4102c10703206045c01d008080342010a01401c0034000303940c00341c4004150401440115003256000700c41d88070f03c85982e01c3d15901c1150b071200500c6150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 812476321 1250 812475071 812475077
    0x70201050a0507051605390306070e0f0120010b040e071512020906270a0e070f0c0606080106030302100c1b05010b0d050607180b03040803060a030c080307020a06 71
    0x2400c05000003443c0c0c3c45180c2000c1400c4031007844000030060708121a022408085610306a5035a80c024101c4400307c1030703000e04401c6003180b112400a49408240c29000d518241c903001846d0084d80e040c407003070450460007141031141e0544132080c0345004a22480c00c104c882d0000140441d00c95080104948494031148070703540c4040d01c240150203c664000d03400740b01608081582d5500d02d06031002034400d61071030310f03007010021801d482080303c07041c14810719003070241480c0c0d0340325500750a10189000e24818011200d81980100304054003d030031160b424220303441d04c110280400c4d1244001c3e501581d001881503952a002002070603070501ca8801c2030030f0741078014400c081c80e0000050061072008a241405000d4201d8501040000d40c020301000c100649610004852410410f07141e00d401c480d10760124501030307500322070309000100707400940e141842191700f5600e0b61b80b00c1040701c1d003000380307010b400080b8020088003045065a00a009001300802181d41f10f54603c180008010a82e10240c14 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 812477571 1250 812476321 812476331
    0x60a08010b060a0e0a08030d090b090a150b1302130303090b0a0207091109270a0b0d080d111b0c01080621011b090311010c020d060e1203010b03070201050a 68
    0x1080d41c2d52011200c00e0b0900b03180c107201c10b205000000f84000c6072540a1742c6c5a100010710504010610b8000070451401a64904815640e03041c140340c44264401004010354002c000c80010712036076074012541104040d044058411040b12107008913841901140c100d01040c8604004141d800188800501400500c841c02d203045004040c0d44d0310501d00920310300e65200d5124500e002c0100050f038082c00d4000300758001c040c08602c800741c8001c98034003590600e04040170000310b040620f4086d201240303802401240c8842c80316141c1075010781019040e030345076688901d50050b03010180c10141203801c03080840044440c031511030240c507001d40c047c0ea20741440212400c00c480c41e80c071802d1494420966560094540603100703041401000c0803001002001c0e0300410b034080c3e81d64004240c5003564440c00c070095603500210019208418020320084d030018840707400344006030058110400c2245044101d072504083c0c0d022a4885402c00d801690300d009001c02000f840a609000e40ca0b007040d50300b9000c1003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 812478821 1250 812477571 812477591
    0xc260d0903020d060507020a060212041226060d080703050d1a0d0f110301020d0e15090d050d112b0b011202160209161107060206010932060a0801 64
    0x243d565207026000e811180d4440008418900030700c46101000d502001c215901d070b4061f80140041e0130140c07000d4560700055110504547e0092102501c1080348214903640003400040c06441c1d088005c002d541c001192240f200700044018000c1d00c0c0d95482501c402e40c6a2081010302422120b5280317129031030102c1c074640300c4966182e914540d07148940208250720120180e04140f5105541224100e802d03600c00206d41340981602d078400c1d0504030810b02039a804040003841c18140100030b880c040c2d0725400c00c0e254511118010801001d00403c1c0c8071000c11040b103006000703107203608680e85006207032055084101c100022102003c2d510503c4010030407015903414002400c0c5c0443d0003088041c1907000a15409002c2c0d840701c4850300e90760080c0340c0700c40d514003038141005c60740fa050b00c61004501d010f203011100724000b20340441500c1c0181d0003003003140c4c41e0151003400f030110455600c81d82035032410380c0c0e00c1c00b1640c400005141241803070340c00300609080e01401107641d003e03400b91400d80d14003d101c1c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 812480071 1250 812478821 812478829
    0x3040c030b1e10060f0815010c05120c1e0a030914130f02070201030b09310501021902070b070c090509071d07030c03060e04020d0c260d090302 63
    0x1019690000045911a070310904501c0e070b0700381d40c0501244240c40d001d0411a031107a07201a10016204581e0300c800445481c08003c5c0c2c0c00e00d4003a90812141b640401e81e40035a544506282000d06000714115013110b14031035040140ca5200c4000d40302960002c41440300c001c10320240c90488808008002d11090743ea68030000c0c00510640507110456005190744120390f52551801c0100880c041d200700101a241d500502c0251310a5500700d021a05107a001c4007030f850004441c40c070400030441e0350014505c0c07040d0f1020b502582e0b44040410043e002103070401040c0d003403002d002070303400000c0984449003203100b000c0d1030700a41d07a001c0c43c2055030401441c4c00082101d007154003110864000030810761034100301c0c02c1c246041500b1004080d2012030310151440408907115010b500c2c5502d0411840000307070340403015034480e0b004003000090160b01040040c105031301c2604100b80103803081c0308000d40711001580100b45082012007400c801040140f80d1000030302034031110001ea07040ca070559a20f164041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 812481321 1250 812480071 812480093
    0x414120703020d11030f0c07030203060c250501090c0801200c1e03190c060b04020f0306090a0b10021f2021100305010b03060c16030212030106020f120304 68
    0xc1d0108080d0800c01d4007100070401c00d07600340b421450780151f04c4a103581d054660b00c100b50300c01a8480c3c0b00c0c5101081070030050300c0480308442101a51135154040480e0810144510618100c0c0c0a6580d5965a4049410268030714040e0a144002040010065410b403241c04c442001d0a03401c07034010400b4000001c400280d5110755003900600d12084800740000a095000345006548000d00051002e00c10743c1d40500c0e4580524404c00c400c200002c05903060000328050503149402e88002000419250300c5c0030340440740e004403907441c0801d460000001080048106210050150f0701c01a9050300240345100c4480002d030380048100401c40076203131480a803014020800003401d800203030521804d00352000f030003e8980c100e56542160b0030110f100d0802c801603032006407029480d24100c0c0da80c500d030101d6146c0c010000a14440e0401840c00c030096040368027954101d0030361040310601680c407014040654002c00c00c54010308048014081040c0c1019071042c01003501543c20001c10000401b81814 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 812482571 1250 812481321 812481343
    0x1b0c030510141b070807030e030708070e070e040f060303031e05100302060306120303010806012103020601050f040f0603060b0306090f031c29010e01030b0604050409020f09041412070302 82
    0x400700f050307180d200e908503480b40b480064554800020980c0a0640140321081c82110980423230721a19038030381e51907072942914045d5045083c10803010079910751264856642d20003004000042c150300c41211441158031650045020a07114008a078005c5000c0140f2424032029450a20152500200f01d00a4180074000244a18400710204d0840c2c0c5411050f11614007c007811644e90356140c40b8013598400c1c1c00d1040700e08166009c20b081c2c807288030b0b840e02411010340c1500107041d60b0342000200036450705002c44407900140d40d507600d080704da00b040c00f400303008500602d40040c80500c40000e1508004000b0b080c0c4d40c041c3d00103170b880500600e001044420381c2c0300c20f13484900f04401000000c809084200742040c01d1000b140038580340041251000f07402e0380c0007600c9400000720f1000056058800404103141e00c441c05010802180c14981c02460b42144014030408001034072500058102c2000e40b8280c400d503040e129191902101007088880d040c0b411502507040900310b5038001e40d51054404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 812483821 1250 812482571 812482591
    0x190306290d05040809090f01080607050703020d0c02041b03060f14060d0c0210050f0901050708060312090301110f0c012d151701020a03060b070309030308071b0c03051014 75
    0x30000c0d062050040645c0e41d04880104043c0107401c2c82032500080210078014206107006038000300d083d40340508200ca18855144d0007a20034030101c140283e80c40004048243d03049911364801d0380c4c0895034492100721403000c0d600d00243d09420110101151501030704100e540722115080240c0d40e558000a41e041801c3d44000443c014221050407401e00302031035100300d00c96043c401130100700c62405680d140318040102c0204520750794210200d8005405407000e42d00744e044074050f80d541a0380e090080c259018041d0001c074001076101d44640301c0d5404100c0d00464010041104030461a007801000c145102d60310508000d01c0d0210700304210300c4003040b015010300f540c4222161140c1d10038401071009150700019840f00303095080d0200d0103944007a60701c20001c0c0c81c1010101e100c800b004145d03030b0419050359030315101c981103640c05e4a0074007010300741c1024803a182e0071000303900000c01e00b0080c440e4171410350780c18801c0c40d51404518040c280c1d600c1d0010a82464901c03843d01010b00680c80d41301d02100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 812485071 1250 812483821 812483831
    0xf1104081f0b06120601030b0d03090b0a091d060307080105010b161a16030e01050f060111070b04080307140327061605150105010801031203050c190306290d 69
    0x141007a00034020809101c0d089900070a0400c024986116058455402a03c5c00d02c042800081000121103041e00000e000c1343d400003062001e85a11005800701420700e0500c0200d45458080f517a04d0b9600b81c001c241c10950200b000c1103100e090900009004000700402070065504001b0400390b540241401c400404550352804020b0081000740c05d02d026004040b82e64280c10400c640c001101c80c801d11840200b8140461114105d4051092600c501c02c010100452600c901d001140c0c0a81096000440340c4a821008106460000f00500c001c0c12380780b0047d6a19402481d00030000340c010700d04024260000d1207242500d50103240b40715004841407035641617400303e400c0000e205020740040641031245440e0401e04000d00000e00070344034a40700e0000c0c440b40c1c3e41d610044840c00c0013404010f180500080285205070b0007600803640112918002c141004007401041189003c80008000000c0d21481d0800c244441410800440340e40c1c6021000540038004244541c1d10481c00b215050340d950b9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 812486321 1250 812485071 812485123
    0x304030b2d09010605090c0c030d0b060717072d060c140d090c17031611270a11040605031504060e0907080604020d1b03060f0f110408 59
    0x8454059211081c801c154224100108680d000346843c1c0155805148002e02160750383c40d040040d02d50380e4401c80015442c0555801b5040094248145129003080c03044c07251000244030102c5441c42030006107402ca03210300c80e03818640c0c401c40b400e620f4291040b0340b459481440100b0580c9803070401c0d400c51404281d004450104461000301103000d18070404001c03940b071180381019001105d0170750261419049540d00c072a107103070100910110500269100304000f4881200c1c0308007a0001d00d004e00342d42011010310b40d010800c440b80c031189442c0340500b503d40400080c020b04003e148c01c1010440c04003d81c00501e5645000780c0300c0e50080505010000c00011001074580071a0103281d90007030000d12866680e41c041c101403403810344481e00b40380200c1c4008200c1001c001049481150010504840e212244d21031661900001001811003001c810707010011a09500480c40c1c80b1152020000b0038140c9984802c0446007040e0700d8070744003a0304102c100400300001a81d80040309686801316800090 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 812487571 1250 812486321 812486371
    0x512040e0f04050703150b040b060903030313170706051e04030819021e09120a020f3003090312040305100c02100f0b040506040b0a09180c030c170304030b 68
    0xc0d1700080500003611201c0d080444140c0141303060400940301407100041c690701b000321f580903401c5040d806500600005441d501c0c0290100c0201d80156002070f51103034040d44e0707101c80f5400200140c40054544051101d100d0010000d20518207110b10102290300300780ea002082c021300a03004080410031412140900440c0e907048401041d04c0012100c4013941080c20841680c0003510440e01c034a01d240c003051030000b0040f035148c100d19801003040c020404041c0c02c201d440d000c081e12070002c3e01001001a50520f0900c0e0b620348043c1132400066407580c0c0c400041615064215000452840c0c1c148820400a6000209504a10130080010440d100400c20481c0b5210740e0390301041c0407600b0100a4400b034407255114904030b04041d14148825650a420300042d034904692507600111404801c008000f85603211019900091401d001b1214458540752541d001ea0740061702d881062000802c2a0006d0a56200304801014059800c01d0328640362100740300c10061140d040340c14004a01059051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 812488821 1250 812487571 812487583
    0x20a021c110609101103150d0317150f040c05091215011e0501032304060f0e010213080f070303210c0314060105181e0303070f0512040e0f0405 63
    0x1d55002142c2461509031440e654829003a000c200aa40c40c0c944212501c104041c100d91140c041c0601681243c603082c0b05003c0e030106100810b0f810010f4810341d121281ca0322082c400d0144195101d1079982c0c841d0001000f4840110b4039910384a80c0c548401035040e240c101d41941e034010f8040b01c1c04800c030701d235a031070790f80c1455030f410866200e84140000201e441564002000000b02110903a158025103450040d0f0440e1641101c400040307840c440158100007200d2071095015100e5480400c002201c09000c034150b800e0b0008480480e500820480104400c0b50010802010828020144803100d101d0345900c440d8640406010000c0701c448503081c1412030035901d0740407401403400304480380780040c0007001032006500f407500504181000c1001588038600341d03500c481100c0300707040c245c004170400c10031110081c1c041e814440c103448400d00001e030340502c05040c000f402411440c1240c00039181040c10b2040281041c0000002440705000d440800b44160340d02408603020440145c0312400d081d03140131 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 812490071 1250 812488821 812488847
    0xb040912050a030e1504082a03181008010e0a06051302070605070e060a180b13050907030513111801061d09150409031202030c1309020a021c 62
    0x4203196004403000c0d540701c001002c0b404030950301045104c0d003007119981c8803607000320424410881ea4010802042400004081c0d0340388200c903a4504151501070711404681100c0050002d40010030f0381e03a00000050320326401008111000c0c162110300c0745020f0303c1c42606004090b80c400d6035100141d00020070358000710161100920b02542180c13480e99410280d407040d1400c403202d500f82b1000ca803c5500500100c44c5000004250b6810000340b81d00c22188654015401c587e50b80400314006500c0300304a00411000701801807980149090106001d000c40000e0b218108151509040203003001d02d403115101031552080070180741240c01c20004000c2c21080050340e003019080301c000203009401000305810510101b4800c120843c2c10000c10000d80c0080300c0009c00490020f020500d1481c040d4000c401ca01d02c01c1c20400d6286541d20740c1c503c1260000c8811310314071900054a006c07000207059411000b0043d002c0150310300071080d00025103412a600c012141039030503503c1c0344407050040361084d07140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 812491321 1250 812490071 812490083
    0x110301240909021204110d0f03030e21040906050102032d07020612010806071107030204052d060103061517060a05030d0c0b060a0302030a030c02031203071107050306060a090b0409 79
    0x95103035140d005104c120581c1d04954801ca4120503806608044200305c10700b941003480c5c01c450703034115203050323000e00400c2a4646580c000c1001711903071030007204814601c0e1124030ba00703942c94505214443d002c5a501c1e0b000541954001c0c020912031200700e529008030342e5018075003000e40341e60703030f968420741030140c4c1c00000e620003804a0047d078181100c0310458101d0b00c2d00c60444005440340a41500c04100034440c0d001c2e1504007000910140c18140c01460704400f00818103252540d00d00300c0701212200c1c0c5441c041c0c121100c041407080e15a03140c001e50014007006101d900c5070310240c1724040d1403c00700c100409442d00b4404002402580d40317103c044020f203000780a440d90703070000c04002017141e2044d103000c5614030341c400085a842d0038480c241c40103603036020b40100b11750b02042d28140c418a001ca90700f21390601c10740099802d0080702030302440c003403040c13070311000441d01200c00714a040c80307840d401080c00799000d01e0422446580c4c4003000d00444004150014010800e1004a000307001100d07400340903 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 812492571 1250 812491321 812491327
    0x20f0408031215150c0c150d320a1b02031c050105030c1219030816030c1e14040f03140304050a06050a12150911030124090902 56
    0x310503001c80140031080c40c5540c0c031111a50745141e00640c0301d845800c1036400c06441c0b6840c8502400341001090514002d40813221110789110018550b014a003c20404180000c038030100c16030130b640a8420031144004039901241e2000000c4d101d4410340800401d40e444031000441c03614070072a84091040103c05031905d5500f823109401a503650b0100000b554960342035075041400d0642c0f482250705903100100a4401700203281c0070005c4d81d2070380221144041c046c01070001c00d450780e006503410416100c5e8848425515044400941c0c446055001c14245428484512503455105000fa002115484140345030401150001c681c128069040484403a00000d004150406548528000c4920400b031400710402c03400b02d510346900962043e10b41101880c0340900905c0c0c09540902101909442c0020300b94250310003000680314183d00ea407101e11204a01030002e2003260288403060915407900c11b02d1b55240440d01c64411600000b642022100414040f00081c41000310000501c110030b01951 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 812493821 1250 812492571 812492579
    0x4030f0e03070927170c160326120a05090304030f050c09070504060206040303050402040219090503010e010902010c171b070617041509051609020309072108070303020f04 75
    0x3004043c4c3c180242031201c101c43c05035403100c40503800214001e51114030498440090031000358541c215002000c0b041c00b03208a21146004a10003807001140205a40f18244080c80e52240700d000b010800c3c4030041004000070440300300c1c8036070f856420014522001800e6a545c408080c19406140c100034031640c1c4208003a4107000000989106a0a0807a1081890340b1070b2803066078607124501ca0140940c02000c009000f10f8042d0f80708640c040d0000e403015107000001699010b904000362a40c0d00411000b030010703c0f0b00d080920401a1110703005c2d008226032003043c2c00180070780a10940060003480c22099008006940300c042c1c46204803410400076150a0094665449040c10300810000550580c41a41102900c0c8a0680166000b401c99403880700c0310580c82018100741002540c2d01e1280d212200c0d0a07920a480d03c0c4020f15149900580300d0614240e09414003490b0313405103001c40c0100d015000f112070f682c1000188258030000d07940e62207956190030b50103805221070003100000c0c0858001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 812495071 1250 812493821 812493839
    0x210091a0a120524010521010e0603031315050409021209060708280902040612120f0801060309210e010801120308193c15061202040e01060e180601020604030f0e0307 73
    0x42d05031074501c0c0d600b070610f0f2b4500080c550b590180701940303401d00c07401d81c40400c103542c00348214980450304c80c5022807525485031110000d03a8094040700c50b1181da460204001c000042c414180c103c2d2640c6400c482d5130804940340c50203a0440f50b0f204856030415151207407607070510783c0030b540d845d81e01800a0109540d40d002200c02c1c0c1c5d41080013525109070000c459807113144200c14614607640c1d152a1000d0503400c00104070020901d640c012181c1e0384c1e10f240162640503071004600841070a0383d44d909603014000c1c00050900c00181e00684d1000700801e84e100000780c100100c10390081103004807580c2c168507400180050011a89139141c248001c40b100345c07007904886c40b45203001d801d00d100040f034140e000b2511000c903203000b1404100c2894068050144500c91004203501c1414a10f000d410326468041384500f01c0701c00e0b4001c0b000b0510b90b110f92209410102e114020035200d403040c41c0b0b132a2901030000f0b520381030000d200500b0880400311041c005c1e4052201840c05001c081e04894007562228520 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 812496321 1250 812495071 812495137
    0x30d0e0414040b06090a110703200f03031605070c0e19020309100c0c03090b03060d05010203090a030201180c05130f0e0606040f06080a0210091a0a1205240105 70
    0x8117009402c1c0000050350b48000303019411401c0d2443d00c0061509106850840c2d00c3c42c04450000009110b0a0400011600810400303a4001299011f10b640c0c1c00c00e0400c2001104a0000b9172052117414132449002c1040a10200d0450780e4082c40119142d48e5000000f0305c8503600d0344401d80c50381c40071060100845001680043c0e4803043c15007000280e0b9040026500c4404800009000414070b031018030414094002070350b0401000307442e401d6101d140359112800c3e0b801c11188030020b54084da441c941032550900403500d918404001c0c00075100d15035218080380e0369143c06410300582140ba10040f00b10441c0c0e02a655507800e000b81002140d0540d1580f0b500c0c4c00058825900c0340303051040f4040000c846100342c0088400000080504074000d60034440810149410f9106020300076100046100d111001d00304050048a1540c1c3c0e9129416406004400d04030301d10040c15240c0400c00c030110701e010121070541d880b1441da441c182c41e01d60f00102c61502c504d16480e5030320000c0520082082c04200a9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 812497571 1250 812496321 812496331
    0x1104050a1509050901150309031b140c0d150905030405040204060203070204060512030d0506030a0c12170909060d0609171308030c0c0127060504060e040605030d0e0414040b 76
    0x60380c0502590342c3e0820078040b00a009860310445500102008140264008a4281e100f170804003a1a42035400000103886200c8056480c004005400004502e06014005100b4012a0703010207107419500d510b03524014100409401340d0b512900c0030240481041920002c120003407003590b42c2d5484000c001d40b690421001203010b1820590040350340e19021800c0340030580072100071800c0c810070140e60406090b0103015107425010b001c50500118262062140141400310141c10ba034010524060034584051280120080803d000c0c0d0301c95030392180c41c3c0716007002c4100c03403c01c6048440d040c030b440100350004000f4100e00c10000540401c1021401903c03000c0401c030f04010089548001d102d841c2e05c6105910305840d0050308819203103600440e9074a104d4011034000b40840040301e00c403a0002d103610781044000c00e2010a04200ca07641c401620a9040320a503000d01c050342c54a80403035501c03010005030405100b482c0c4401e0310a507d403503100b0791661500620344003d500b00745c240500c0500301912 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 812498821 1250 812497571 812497577
    0x90b09070306030201080a02090a050603070c03110f06040b06130515010201360c32120a231e0d0215040b0703090b0414010c0207181104050a15 63
    0x60030140c000e10400e81103a80603142c4101c00d542d9160614000e5004606c03103980010102d6021174035864100180d0b2080d180b41d2504074860b2906e080240c00d0040c0e45828074503542c07040c811000019804650590480c2d07008400404503103409001030054014010300f10841440d2400f0032074848101d154074030100c00203030002c000c03e10101412810b410500e00200c1464900d040340c0b40d400d145c20381c125044940c025103001d00d40a40740c008580c0390410305201424124909202e01d0700c08880c010000c09450b000b240d2110b00c2110704e80107180c861071460000b4041c052468140303852828003940494068160030700703862140355080c0160107203200100300c0b049030f03100d02420801110700008103041004080f11080740ca541c1c0b40c1d0f48e12a07210748014450420192100443d4000400c41c1660901841c4a171148a00c202c211190107400c44003800091011540304040410219100c0603000080420394500032819604541ea0f13099503200e00d030f02164000d901600005501c12542c622135000f00381a035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 812500071 1250 812498821 812498839
    0x18030e1002120f0a020102040305030c0604020913032f010c0203030a0516210b100c02131a09060d12020304090b100912052b0e09070e091f090b 63
    0x40c12030391864054003101d21000c0802c100c0110340c0750f407400740842c0080c510000d03191544a590301c9096802c4803403142400d40c06503092100b189018600c590740010502c7c0344400d1340640d510001e045880da01160361188071400f04230b03031010380c03140d204001d880700740340080c00a82800e010007507684c0d104550030fa03034251410011444420312100070035029001c0396504505600c2d030301d040c03001e80f011035491000c010b030382c03081e0125160311f038502000107848040d11103080c00304490042c0800683d0200c94860990729003c006003022313004600c1440c85c50003c0c1c1c1d0501c060307074854010a443c25401500a004c8002d107190750261075900000070010740b8142e03802805641011000d02528402a01c0088007041c00000c0601c184c000b490302c0c50201e517005104072005241ca10030f07078600a02100c600040c00e4104001c1c034002d1980c011a0349400e01c072081e100e580003464000001418101c01802c00c601c900c0d0300700080303201c00c036221010b03d8681d600d8542102d8483e43e070303030846801000d0725840715002d01412 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 812501321 1250 812500071 812500099
    0x160206060a031a09011b030c020f0708061918060225021c03030b0d0503040f0605030411040510030611090f011b11040f0e010c03110403170d18030e 65
    0x503070341e001d045960054203120300c0c6002c854110b1044900070000040c0390760381c02001003103405d0810200b154007155200058200003150f0000d0078405014078000d601c2e030010ac003c0000520014460380e10151f60495858a1000c0700c00450181c00c000c100e4902c0003504940c5102800b406a004140e4030054207041040884000901511150a0715010b0760200c40011508402c2e013038002c540800d01c2c407070b15000461081c400001401c1000d03021042c4d0785031b4000702e001d0180f00310b1090300314041c00c9c440c2002e03410b40c03401e40c0d5041010803113524124001c80d1190041000390034801d201d40041e5500020500825005105642258000350002d03803040404c40070406055014400c40d19900f101008041404651500e40070301e03084141924982060341d82040d44800c81403807146900e1200c000c800403540d00c2a451000701691100403421180b40320400040002461204607606c034114084840ca89aa0b40d0010080084c0300341c018541e40000810201c0b01007661041c1c080341c00040484bc4001c580101c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 812502571 1250 812501321 812501329
    0x39041112100303050a0c0317041b08210703020c060d050f011211040506150c0f07060e03100510051c15110d0b060c0a2d03090302060a0e0916020606 65
    0x4503120190104d0b20411145c054984100000104140641030030703031803000310f6444141c10303150444090301c07415004130700c00454980c0c4501c030400404450340108031001e540d04041a03290000008103110f0a00028004105030007800800d03080c0c90014140c0741c49030400003801002d401c1c100d4504000018040010072610410b085690005802c103014607107180c050f0f02440001d00b400b806217640084881a0400c80d1380b1003e00800ea500c03480d034085c04072100c1144145141000982016080c05109516920a03880c00283d202403055030300d00100d1951507000340e200c03458445030001c83d0020b41c1d040d00301c5001c000040340110214462100110102004d0007a0401c07a00e4589105040f01030402005000c1c1d009034214042c1020014011031030602c1c040361103803400c074540c20b0071a401586825080807a84401c0d07414214001401892030340f1080d680d400901850103400000c0c41101e0100301c010442c1c0c41801c02c00400c0501602c60305660600c1300d4200d211b00401d904007401071152000051403400c2c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 812503821 1250 812502571 812502601
    0x1403040308030c0c100c0c140d0f050703110604140d170622050f011505070804170f1b030c04020c030d0b01050706020a08060109050339041112 63
    0x7812003030050070750b1588403041034141e00c10340c0000124861000c07440c1107203101307200700d5000282a031911403000c0c2003440c0c01800052003482d1485613411108402c1034a680000410943c0c1d0b16500d0f20507a10003441c03609a5103c0002d615a09562140e182044100b0402691030801005080d00f22030202500000c01c031140003900c010300503112040d102050a50502e0480002a02649035180d07285040440408045910480f08868401e1000d0010011410b170139203c0306000d581480c2c9289041d0490b2a80c07800c501c103c0c402e80004c00319113541c04160707202c103110031640303200d1245c00d59018104000132581c030007101041c294468020601541c40510b082c2c42210241802203020714108100c2c00ba107840140903e110090600000700202e00011b00c03648002c210f01441c0c1d85400b03880d07081c0040014080c290300d81029000b0303440401102a1008800044031502d50313190540c2c0403005020306900d1103441c2d0030310036a030028280000d4405200c21500a0302c0d511000d406981c01a42d04c4289055080c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 812505071 1250 812503821 812503823
    0x2205011205060a2709110405060a03240615030905011505130509031b070f0e040305030a0e100f0518120703050708040e01060809010506010905031f061706010314030403 74
    0x20f05100100103d040446610020001d0803000c54424070307103407514400740c880d840011134445016080802a902e0184111501705000b41d0312520540e08642e100e8403030815030082040301d07030412980307031440b010b06d40c00c410080d2464040d100740c2e43d6509040a0040c0010f400f08070b80300e50030f0440d04001090780901e09400c80702c1c020048104488919802c1000301030250082c4200d0004104075290719a0402d2071201d8246980000c042da40d1404203655840842c581022070b42c141d080b01884003190303010f4240e0360409807007000001c1d01c16206039150700d48080c00d10b1301a0410b00b0440251300304141940514030840c0d1001030301c1c0b410700d07101c40c0961b2285121052105030b110b040c85881d0200b44200040c0c090144030b41c0005107855212800c0c0211100b0036488400000c00c00b90402401e07071000c1c0540d035084802828440103190a00700040d44400c0000c1d81c2d501024a0311780140c0f45034540340c10510003440240ca4030540c1c610103101485e00c44109010541e40c040100b503400c0a5120000f04035002ca07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 812506321 1250 812505071 812505079
    0xb04050f0d230f0406050706051509040b060a0302031914060609071b050319030c0e0a090b010203090d030804020a0b070c0e06010201020904050108010209010914060403080f220501120506 82
    0x40030301c8002c2c054010481c00c60100030300c00c20302c04000c1030400540188090306503034607410b450740c989180020544000500a840c01041004003c15a44850540a811640c04840c80190b540c54801040144a00d031740045e51610030401c85811045c000e0549042d0603008000364000c0c4e603060072000b81d4401d020b86801e030b04000c281000030720880c400d400c501544003a43d06d5000d281042074680c1855900540404001e860307202d05903c200c40d80603c00c01c030101e60030341000500c0b100400700040301c002040c03081c0310300203443c0d1442041e070f60300c2032080b01c460210062040301016010b0800404000040f6012070240c1e011010216114000750280c0e141944e001c006800705500300031449120860243c50a415590213221484d46651107004060180000e400016110f404020005000750b40d95031000c3d0801c070108104035004d8541c042113405481d080410166590071002103000703284a0030081461071034000300310007011440481140b00710b880c02d0740c4080c8490880d00c5920103c8105640880e80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 812507571 1250 812506321 812506337
    0xd0b1309212328120c1e0e04180f0c1a071704090504051b0a0518060f0d0b07030c030203010e0610090b0a050702180613110d06030b04050f0d 62
    0x442002000100700c41d035815520355100d0f083e002010703107103201c01c40002004644446400602c0160510540344010414501440440c0c040b251181030030300304200d071808101d5401181400c60702c882d08400c40c864484d00d510f8140c1c0c441030801c1d80700d07030101e510201c603c82030b42c11002801c03420b03d10f18045a0444211010300d4426a84e44200000180d03460b41e0f502c800e014000003070106020704c50144568011000340180d140c180f100c240c0b100ca402c1d143c4a11032141c40e0002d000740e45a0085141c030700318054100803069240d120018000da202c60030610743c0855411862010840180140b90041c64592000c1c0701002c0701c010203034182e00003400703556545061180042c4040c90b0521809032262104c6c100589020380318402903100341d2100344003001240000640f6411030801038015200c0d0b01c0b141007110128200310380014002e482c210729143c200c82e11074100c5403850060604076452003000030b504000c0d2a98900c1c0c01602c04400312800d40c1c4c540203d040781140c403d0080381c10780b20107500d43e41d0600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 812508821 1250 812507571 812507627
    0xc020a0f0b190e0d0605040b0f09030403030e03010e010c09090c09150c06150f1d0f0117030c06040609060f09020f12240402130c02030d0b130921 64
    0x100c0c0100c1d56040b802c00c041040000090b032548444074014500600303020a0614182c203009a101c078001e800010218410310803c0344014002c0260381c03d0341d506141c042c5250b01d0401c0040d01404502034200788a5203080105200180c1049800040b101c1e43d000a000704180c600096407601101c0c411b2074030044c0c08603205d00d00b03207200c0e0500e11050b5106000026445000e501d450078901c0880d04055205e2140d040103020f201c80c0c040354454482c0c0000e022503500d14202d40c0320b142500f0103100f8000702c802c21b102d031007440309018400d4805031805d4608440c2c061130310341040390203001e5142c8180c881d24989081a1100290b90207070f0341049802414201808030030905001070b45110480080043c01610420640314070180c030299041c802c44269a283c90402e40100b0004295030b0343c111380003d02e0016041411500441a078007008000707280040c001c541040854405214101550402490007080c0070401000f801c4055401403800343c00d2942401c41081900c0396102075450303240c841000e5084070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 812510071 1250 812508821 812508847
    0xa0915080102070201052b110406030e06160804030504031a060109080a02151309091208060102030a0806010c0303060305030c0d0210090206030f040f020306190c0903230f0a030c020a0f0b 82
    0x42e1489440701102030b10700c0900043c3c7d82c101c032010300c0d00b50494180003c080002c0b40c0c1c03501601c510044140302901e05810014040c0340c0c280d02c100c1c1d15000740501100010700345405541070764000c54020208440c0100c400d070803120f84031821115180482c10307003c0080340044000a140094540c00b6001d8132150f654600c94000d0754002c00100042c0002c0784201040220b640e01400d150288100c00c07165800000c5034001c0d26640000303101c80e0442d0320510000300c42690106200303402c0802030030092400c0d00507041c220050001c0d90070107445403000207100c925036000014502c2c881040c41e07080d1114403100c1032038002516400200a0740c08203013407000c510702d800c21072100c5070048e11418004600c03c0555002c030b41008002c039080e90050302000301c09028581a800b030ba2911210b2894001c032b08908582d0b40440e400c0303085400480c044444143c007461440c0070880c03110360846030011100858124a4000d250b124180802c90055004d0762001804982103080c1c642038541060826003070240c01340b400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 812511321 1250 812510071 812510107
    0x1201051f120e0f1204080c090603060f06031c0809060105060a120f021b0706080907061707091e0906090b0a150212030a050109182f0a091508010207020105 68
    0xb4980e0390140c250701e5a01c03e48204905240c2e040380402880e01c69140040190a0001e607086060080b42c0d900c040014a03035012848585c01056180703c95616116140468603200c1180040c62007825440d994400080e0032000142c4101200380c03c440641c0c2c2c8903002d201003800707400440400314110701c560080b20386003074010343c150000c4400014200080e840f1401c12008100d0210318894209035001c2c0003075580f10800d150700c40c05020080c00b0092070309400401111002c414a500e1400f00000700e41600e100700340d1000103090400899620304031a03105803500711403600c01d002035036151210000321250a0f00440000c0100140007010040c40d10b031490108041d04c00d0003400718010500c04030089a220405540200261503000a041d81010b81c3c5c1d034115510350320600c3c0d85500b85651540050048080f9203029842c0d02d403c0d81b01c80c04500981103020840008017070b880b1004090219a0802a900220014200402a5000a6556003014200c0c810040081e00144041103d5815015000c0d08 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 812512571 1250 812511321 812511341
    0x10c030c02030717101b0c08120f010501030c081012050f01111c02073516030816020a080a05090d0f0b06100c060b030a02061201051f12 60
    0x181100d42281d4000b03403d058480d00321810581582c42c0741142204108030b103007030440350a0f80402071a8880c620940204400290000030400f100b01613100f085644426a403c1c49041002e04002c0c0c2043d000c1c815118201f400303690300191a0000e040c0d2401d2084082031300403498050700d08142810b0010003000500701020690b405e200341c1d03180e80c01c52242442070024003100710f00003503202c290f551944c000d18004c61903100d015a00521140c000f04a00519a0b000b900c1c1400f6035804100b81126a6400d1441110060000a101041808a505d9200c0c00d0101480c8265101c0c8542c1c1d40340110311500d022642402d500690241e01140006045040180817030800303402c0460a10540c2c0c2c00184d03200b40c1c4048105c0d03034036418002c20340c00c218441502c01d800120072500741c0803940c10790100034100c002051003d82241c0d152501e00d4488e8900303100641d96950007034082075944240e001120b88410080c402c5c1c90144ea056064207a101c205040e5440b16422180e0f6003041e00000350140d00c010b003442c820 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 812513821 1250 812512571 812512577
    0x70302091c050f070305010e070506042102040e011419140c0a0203120103050321090c010302180a030f0b01050306070c03030902010e06160b0906071e140d0e0d031109010c03 76
    0x184000c3e6441004881c00862103034001090610b5840712050800f042980400c1c00b400044c80184020442000780c21810ba50708058441826103a00000c0d02078100c1d50809602c5510700b203c01c42005894240451080b81103029a00905032103440b01c0b0202d549a01150115485100c089003039100c10600a00c03000205104484c10441141000d08802e2001c0c2e000300c48a51000a210300d160510b1009114144200300283c403c52811002460311800410700140c100b40d4005680c0e41c0c2400e007500700a042c02405040c4007500d580b1f07482c201892a41c89c00c6c0580c0c50b205240000106c034640007510b248201d00c150341c0c09009001d1558160054a20058200d050098003d0544c8964640c81c0141c2840521801ca41c0c424808a00b8071802c4880090f2520610f6001601004103007a0081080c041a07000000d03582e410717010880003141c0c0001c100ca0b074204401000901030610802981000c04550240310aa0702c10001401d003e400305c0e00c3c80c50800c2d81454040c0f128a410798007554180c400707940a82 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 812515071 1250 812513821 812513833
    0xd0b070f1805090c031f0b0304060b012d120c02030a270902030402130c0f09050f10080c120109091109040308010b0c01230f0609040312020a1214060306070302091c05 73
    0x300300740305186c10b590008a2902d1000c0104001e000e49801031098110085c28440e040079000d0221414800442021490020340703403108900d0240f184080403100d40c1951003c009075030301d07034000a40340d611030303500c8100107080a0311441d88000c0805800119400314410280e00c00d00d400c0d03090740a500700410a07039102441e0f90220725035680328065620364815035900d50746190441d55010303022900c5600003d0003100f4410f101c08441c0c0320f11003900050308c0d007801e2101c020f0f0f50f01c03110540c4512880200009400d104000025103410700d40003c44031501c1420341c0d072700100c45001440105041104d02600107151080108101c94440004010311806407002040318040300f0400300031124043c8440d03c42c11404400c0221a0342040c49650304100211408022801c1030340740113041400c01c283d05214142c0c00a02c00d20403c0c010000c4038801c00810380148050030133104a41915031044881c2e6000307020b0040001d003014401d10880f50a500020054a1401c401e200e006000904a4004440305d00c618 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 812516321 1250 812515071 812515111
    0x2122a120709091407080c0c0a020d051e0a0c0b03090319021204060806030f0d050304060b04150902070303202b090507060e0f09150d0b070f1805090c03 67
    0x140c0900c3d00d0318000c9408513401170401c1307030000704641d00062130b518601a0a119040d040b41c80450f0801d41c0907011183c0c503604020f1420040c1c2000b00940020744003021400c041c0e6902440410500103483c012903d01c8040d40d56502030030361910081b5240b8080360020015400340c00aa0181921301e4501c034811554050801000070560703a01a42144d40800c2e4110100500351400704136008062803414003600c1c40d070081a102034a54000540020080c0c0c5c0c46125074189915a54004801c0128941010030345503600d100700002940410401d400203800c0009055141000903160380d5114840c40e9180c0c9030045515030780c0181d040c03080414502420043c8600f51070821801500c080d00e010350301808045160030700140c1038410003c080f0f4061700b0041c0040100b036070f4031200c03140e0244008029900a030083e000207220140b240d00010503290b90300e4103000035aa0b0201850601120540750600707103c0300c0400901001000d80b003415030011503000001c1750101d00400dc1c1d0f8120601c032013401904090 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 812517571 1250 812516321 812516339
    0x646031a0907122f0405010e01110a0b0411030d0c0c0909110a26060f010e07030b03010c0207050415030f1b0305070806160302030f0105010f0c0602122a120709 70
    0x141c80f082c4420409900c0030040c9a40e4013110111064002c1c614851400b450500081c0c20000e00e070a04506000703005038001e074100d505210342001c15501c0108800549020b1403d0404500b00000d001e0181c41103020f0b00300907900420542a1040e00008050300c3c251401d8842c0c0301520005000b140c140518000c403c80645a0748200c034003400b4106021004502080c425409600b9070150841035507018400f44080403a0b106851750560b0f281541c0c07000707195101007003030780906005260b69030150320b040e22407804240e000c1032110641da0102d806000c841a1030381c1204e1040c110b400003074400081c2d854a1400100c01410564581d4000c0001d0512907540343c4805041c07136401d50000a464000004100400050070002080620700b82400c42c15402d140c1d00000b094a014001d0364140a03840d20303504821030081e00c40d1b1105690110044d5500c51207c00c0d0402103503001c4e54142c00240401c3c40540b41d010b500c0ca04e5089154a0421407800e0a1040071a6011460040e1040041c81080d500109880711 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 812518821 1250 812517571 812517581
    0x100e160803041a0319020d320c04081005060f1908100204180e0c040906020403020405070e0130050403030b030d0f020c0646031a090712 60
    0x2030004040c545540ca0f20310005054204000e0041c001c440c10002c004483c0344420b9214046041a0300050316032460010100007410901107852100d150082c00e000104040301c0c0d03460007141580c02d04130464480444200b454000c0303005443e460341100e0701409020340c0d03660000342e002070018480940103001802140d8050743e041c140725072104019109005141c0c04008104d00103582c1c0704118a041d140c070700e2160094003040c0c6d00e4840e15071103070f0005290000070407100c2e2011400900410001708d06103000c20081d40a032000324061400c00740004e02080c09911007801420041c3c4034004555545d242180e282086250580c80300c0f4000e00004042004074440c941c8600d2290303d00080008030f14040626210240004004100090765020b2840e540401c0183c4400c50940304152140d441c0b18458440742c1c520180c101c2d00b26207099030001d40da440c1c0321640d007088910010844030039940141c12030030745000c10b80300301c504042c0e40d00702a406e0a11201b4a80d004402d4a081d0310003841d0b0380440d0007910 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 812520071 1250 812518821 812518829
    0x9170709021b06010519060f021e100e060103020d020909030403050a030504081c1215050303130303090b1611040f0c091503051902070804090e0d0e0909100e16 70
    0xe00c0c5210b0041c400e000420589015007030440c1d517460b114030358009002003045a402035000708020310f61603805207402040006050070107940ea0414a000041c200c80e6954107000ea410000380c05d242110300d03940004030701c0505807500030f001c0040305807954081c06202d2002800c400c800e13201c1044008040358080c17003034840181c0300e0380d51160b41c1c0d860281c0301c51610400ca8850300144080000b0b0850041d003299840744914000301d13000c0707040a44141d5600c420800760740601e8060000055501c909006000c0e00000d491194881c50350464403071401514602514400b00229012541c40501045184501a1149200600c0850203504544205054503000c0301c4003400319a0b107640c14400000000c8095107040900e01d0300f0025031406604080300307100c0c00704030060140e5000a0342000c0c807070300c01c00b00c40160440240502c902c401310200569100d02030300d1040300080c5852110401441c1806000b401200e105006201d0a90710042c9840141441e6105e10554422040c14011912061114100030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 812521321 1250 812520071 812520097
    0xa090e0a0506151821060405030a02120c0712020d062f0901090302190e0705040501020c0f030c19080d09170106051021050f10080d0917070902 63
    0x3604000c0d091040b02a20340c580c02188500a0011803201130102204843c10f000855100c00b0b10b4020030308a0281c07011098000300f19005000c1000705010b000030040c074a04c500e645c06c566200c11450203442c1e241c01003200c408841e800c9004100300e011041081525003900062880c80160740340e66542088502c0d250480206540800d10b80c03c0852000c000c1890341100041240d180c50310841c0020075585090000038803540d10300c01c400c041c080d07401c04c1c00000740080080c007103503034144204098541d07001442084e0040c07041215440c161700b006e1241c2c4070700700400b030000c03c210b400c0d41c801c1025034080c0c18210b40342400800c00c0000d00034010064448001102d07112103043c1403c10315600382c00e9044105034006a070614600304115101c5d01148031115025103880c0342d01c0c01c0c504041040d8095280004403c40b410241030103104c000c0c188046004d85500e00c0b01c8050072759594811522040c0c155400000b003407120504105807001414454408482c03030040e201c10503251710803001280c00840104080d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 812522571 1250 812521321 812521331
    0xa1203150509040f0201110303072a0203012306151b010b04020f0a030f180f0f05071d160e0607020607060e010504020a081b01121b05090a09050606030403050a090e0a 73
    0x190350301f00242c5014540440b02940c079500d00120064a96101d403035107040c03640038807460485d050600307030400301034998010028005141c2034030524010801c560700c0007904142560219000d1311741815150b8601d800003401c9410103059545084140c501642c1d400155501c1d0b061080b070696592005184421608080c0e640305c0d101900b00904503100d00c021900401c0c50003c1c02e000301c2c000c0c0102d01e48050780c407804040700160325150000d49080c3c601c6008010384181031001c22482c1d8450000a45440301d1441c01100380d4030034440d580c112401213022400310b000d4140308640d5080c190300521907280090b0482c4d25060b55070340c4000860300180b4151180d07943d1001400218502100120020000000148501c400c4400c441160f10b6004521505014000307080034566015500800c4642e07103010a01d68029110f0800070f489540072440f82403140e401301102041c240000d11449000301000307400315003103a0340c50fa01070f601c40c4d02c5a41d1b40c2083c060100c00000e01d2a07800420075200344400100451 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 812523821 1250 812522571 812522573
    0x2090a0501092f0702030313080d1b02010c0b0615180f12060c03191503060507050c15061f091a120415112107020a1203150509040f 58
    0xb00c88550740082c82c0c010b010070b88002d0b00031900d49031081a030010f44000ea80e40d0044e10000b0f00e144258140c45072040040c0100080560022508491207400350301c6000b4a61512100d289031090b0417080240070a51131a8283d0110314a40080c039401107001e00503880d001d44003034080390765030440059001700e0f5071905100083d5082c8102106854082540c500c1104003402c40d000707440d808001c0604084206c0400000d01e00d041070901ca040701e961440003000300d180d02001e01380031011240030507101e01d401d240108100038400d200301d880950450303014103590580420040303407602d8090034690f4010300c09450180320794140d003a484e1030301b10b0a03262941d18078901174120041000c00104180003003800d00500700180484451217520a40c45400c9da200915641c0c00203005200510404400e02c40204081e00300341210100d09984c02c203a80414100c2c0d56609a00300e83c3d80c4102d180041c481c40002c03034b9a01c0058080c0d00004803d920740180005001c0c3c035440411000380b41110b09694010700c42010b00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 812525071 1250 812523821 812523839
    0x140d0e10090c031208160e24070c0b1303140c120610060212030115030e060915010f080a1709041e0f1401060507260316020703020d030809010902090a0501 68
    0x60095031140c2008150740c40d118040703128845c03403030b1340c10b005210854101646540ea03840684e0235030b2140343d507405500c011103840800321b50000d40084071520f22160002c68204a00c2e0242e800f4060345605542c031017030071551100682c00313400a00f01110b01c59031100c0001641c0707600d2001c1c4030501e0000200b8480c689030b540c81c05e40a4141e444102036400803102c1609160410044034155112000300c1031549410440442c000c20006010302030301e00505040c4a41150040781000c43c060190a4a0000c3c0c3d803101c4060182c0352030743c440c8109940c0000700080c00103425146041e103000480c00710a041061010201d8143c0b1032160525900e00e84441054140b60402d100710840070809600401c40042c2e50600309007210418083d0303109012021a6030f10400100310001511440080c0400c18480d0310b030030090f621034106481414040001c004a0f03c04144009142d00450f42c0041001d01c0600039a1000d40741d000c80500814804e540364102c40c0f026888524006000d00501100040d0941c50002a2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 812526321 1250 812525071 812525093
    0xf010909020a062006070f02010606020309030d0c021503040507031712060105031008070806090c060c0309040203041e03120c0c0803040209150d050109050706140d0e10090c03 77
    0x100964600d84a050400358454a05450a660300390400b20540590503259541d01c02403940340200500c100400c0080d070a40c010110700020140340c000b03000d26070300c4540503070710b03402070034505074150f4841141c414002d441588401d084c40e0029103845050003044144100c150b20403a41940c00b0340c01804100104a4070011020480e00e10784d85142c01c01d1250a40c0c01c21510010b0105810444044013041b000c207520030110004105880841d61100d0342c1d841055100c2d00119192441030043c02648a05418100c0490790310380c40354805103103005030b00000c0000941001c2c000b0394980c40c1d8896485441c0201c031030103442c10703030103500c81c00070040c500c2d4880000d44603140360440c1040003011750780300000c0e0504246c0b5003040d41119044400e50f00c3c02d41502d000342c00001e580e944050300d9007040b000d02c041940882000c5000b0000d55040300e45810041d01c01070b052034600a50540d081050180d0340110760300100c250042c04098460850b48250b0400a0300c0f080d21040d01c0000d0038240400811071074100c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 812527571 1250 812526321 812526329
    0x20d0206060607080711060f22060908070b0c0111030c0310051c020d06090605180f1609020c0c22060503061e100509330319050a0c0e0f01 61
    0x1002e4505046a940c002c46400394042c01801c0d0400005644a1a910b4400791508102406d030104e890f501d00c0201d1000040c8120000d00352014014404180548a52a2501940c134900c0080c0302c0545040510031080d40034405c151440c0d541d8140140b15101a44000d5000e1031f06409032300d03282e0078106902507409403580d000e00d118040044440d9504140c510350924107a070101c401103040e85150500c2d03030240c210b51000512051034102001103040c0785c601c1e42c0400c07800340c030100e81c0b2581282140b5a074545040244003401c1c56604804c0240c00c400390024032a0144800a868403040c04a0101c0c600415011001c80f64254681c508100400c1c079100303440041600300e00401c0d2600300501408072600c150b01041c090718141d90001018110309641c0301e0018880a4403615852405003e40c1d0702c81c254400f00064481c1450444520240c000446081a0f02c0014040c000354860f00715661040d0a40403001c5400740281a2400003003060a110f40c00100b41000c0c050701c491a00c803184c101400b40c1600 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 812528821 1250 812527571 812527579
    0x2040c030c120905060a020a110f0307030f0207030507030f140105010608010503190209060906030307080406050a110609070506180d05010e0f06070e090a0207120e0102010e031c11040305030a020d020606 89
    0xc42801151300010140e4120f10741503c0103a41310580301c0704403011021025042070350b12411244040c4103d00200500405d0b0084d600c91000101141040743c80c0e1446104c00703407143d8011031013440410050000700024903c1503410b18221107000c200a030940740264440340c00b00d65150300402c107900703050000205405245504001500740ca50018102c8000588500c0c000e41203000002d216450810071102c0403030700b06941a854a5803000e0050040c0e00010626001854030520302d21120800245d80e40554640c0303021300708203030904041c0942d503008041d4061220440c040040901c1c0c44460322940f14601400001c00d0312003002001d20728001d03c068100c0440e40c050010807000035031000000103504000c9448014580361142520064010344402a210031002c08507410301c43d8002c01303031116a18003a0024481c80c0700c0766441945a00808044403026220f50600c03c03120761455001e010000038010504d4289a1603895079031440d0007400760302c800350303000e1b0850314a155010480c5a500c080111 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 812530071 1250 812528821 812528831
    0x90e01050102161401051201090b0a09060b1206040221100f061d04090b01060c0b09070b0f030a090c120507050d03090b0702180a0b010e0f03060112080702040c030c12 73
    0x1035000c140b0040c01344907400280e042e41c80310015680c070901c121032001d06840c0b09030355156160384918008146194003a882100c0007400000d40c2d40070f60044008a600c610145030406002d040c03180524000184001e83c056030802900101071822201e140e1241ca00c2e85840320107142400d43d501c000c0401d81c02c031038078160108404101081e03004036a0f92001c086070158801c41c0d05082c2c0458060039100100509920110f000810035942c021100c06a00340148540d00840e101e00300c0d170035100e400901501070b008070b04011214a101302180256004107004200007200480b9480e0b800d6900b4441e001550b4684404a9160600c04104548005408115001c203402c1109030340c060008010b42c4118010246c02040e03030402d6507500340e0a24080500c2901203c80f515091907010010182c041e007550118003940100b02d0181451007125118003000717002070030140d080c010175000c2055914412922120100b0101c001030f112402055642c00050b00e01040c999501c03103000d01012911880fa0010601c0c01e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 812531321 1250 812530071 812530093
    0x2041a030d0f1d36070503160806090a1d0105090a0b070201182003101d0307020a030f080f0d06050a12020307030b0705071b031a0f010b210403090e01050102 69
    0x195101391009164a1000009165000100d404881d9012440c6107210200b040001c83c9801a00079449894860440c44001000980943d48200151240354000c141e0310001003813101c0b01e91100c0f1210710318030950449404840c0d81c0c01c4c20350304201c2e00098540c110108034401c0084602150390003501c00c1c00280201c0131440070002c1103040e130100107060805001c44d10b041c014030316006003086142c041d0a80c0d001641e5101141301804098000812004048002c498011404025165807e40c000e00754640341d483c507121030091820a4034147c40c152070401407108038075440402401003000782d100108000d03280004011a01f22154003450f00c5030300300b00388440103a5003c942203007a2580440010360070303190500206d800e4001c8100007400c6070344900d401785140070100164411030784a0309040e9100c0f060f0f1444a008003000350b4a00d1803000f4801c0051241e0000309001d00030701c0343c0c4080a002c1c0c1c40795041c101403014605a4050740410119102445009441001d04d4050320003800100200e10726 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 812532571 1250 812531321 812531329
    0x30515130f06051302040c0c050601080c06031504060e01090902090a0e340303080f060a03020a03170702180708071115041106040e0901151202041a030d0f1d 69
    0x1d00100186150b6a03040000d000322102031051198980144c02044403d04454000d400000b140318299450300c603940000942040c0005d0a081459029154038110744542c102d81100300f41010095920549848000c120000b9120041c0c0c000c0c0340038880031640c9082401408041c0343d000e044944210706103840d0340c103843c000043c2c40c0c80110705030405e5540a14041414403800b01c0080c2091803100900c400002403540c00004c0c07902881307031942203030302c00c0e02e030314007040a940c005120094010314021030800114401401442c01407041d0030320640b40010550019021581003851101c07024100d806004806901a0f81e15501a50034100301c0d0b001e985034900c2560700d0500c1600c0645048001c0c00180030003080181e8a00f80c980c0c040d158503100c0c2c3e240c5c51000c0c0c0d10070003120000440e601c2d2a055200480828005000700d03400040b0a0304520103d4003400090000c911600013030004176031889010352410000d8180003074599440b44d0b41c000d45c0280040280e000d1600141030003a1407132800c84c5542ea = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 812533821 1250 812532571 812532593
    0x2043602060d022803180f110310090c15080c0a09081009050d080408041701060b071127010e0c13030302251d040f0609050703030e04050412200703051513 68
    0x1800007c070300d400241e0f614000801c500c0188403d030305401804003221048106030003402034075108180d0201902e40742e2810944072141c40000d0340025600c030010410490000707000702021036040c5010080142ca4541d168604a0341030592115076030b980c01040c0c240714040c41404c55442d090314004100e81840d4a80d8800d40c020341c0500e01d407110484c4102058032a0941c0000001c0502e12640c03a21444181407904284000d00840340c0240030002c5184107c07440340070805006821501c1c1c1c406283d01f00b04c2100c3c8a0480101658400c0d41d080161107580c1005454100c0110302c00e90003000c80f4044091580c02c010403000d0950803030031205109200742d00c1d00291040c3d01da4101c1c06416002d0341c440c10408100010400b02500035840d101800c001d102c0c003c200c03282501d000e920b512512000c5101030100300c900403a4050b02c00d0b010b119000c00e041c0e220706050b040e01d19094200500c3c04461600d10b0b414002c090340129860350201c4000ca03802c4071456881ca9005080c2e210f5440c650107151210042c0b14 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 812535071 1250 812533821 812533823
    0x60e15010b0324060d061410050f0d051305030c100605450f060103060e070f0f020c041d160b040303030f1b080402043602060d02280318 60
    0x1070707150071500d284c0caa11040c0d0b15031485c548814820035a455010042009010384200c0c01804c1018801d240320703001d2411940310311240e0040c189805040c9004030010310010b8910030804045840c00d0380800e0041018105a50040000d00341c000303440f11502d0b080707428070350189005008081604a02100fa04a20013008414803c200c2080040003c00c2d105040110030106074101d40205204005001c203080d54404c00080e2010000f0340d481c2c2aa2051070349048645100060746942d4802440f442102980d40303001e0070780100c49020743c0740000281230b9a1030800380e1080007860811341c45050020801e001c01c080724402d076400c1c0181000d10389001072107140000303800e00d0341f01d01404544140f681d20504820b10a412086000d1228890080c406001034078164403c90408190085452160000786845903030490342c10319100460030b9000303162550310b0080ea8003070818050b201c0c2900c114001041c00030907503c204042c5048051117400700400800c40003040629050f1035122804a4800d030003402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 812536321 1250 812535071 812535121
    0xe0307060203090922030c030305091216020f1c050717120c0a05070e0f07090f14130c020a0b180d052206080a0e030906030708070903060e15010b03 65
    0x280d1702e902d050b0075280c450340400045011131005100605900410168515210359814083c1c1e8880181660303941c0d4540e000090244130402a070340440700800d01c08201c5034030190500110555000c000388254400a05507082070000382c981d1010894107000303240241c103140d458403849072b100c820200d555400300701c0071156411000400070100181041502c20659100c0f04503424031707441c0c011700850101c00762041102e407074821020901680c0600100404e5850010b05606a145040c0045c0300441c111220540c001d8101251440311030824002c0200084c00360b002400d0780070302c91608900c8440002d11454610000c8429000b0704480801c100b04540d50b2480d00719182e031401d500d03520361600000b01d40b80721b440f05890005001c03600308502500c1181e8800d41003120001513110aa240c0c4180c0c0b8000794004010000120b16a015001942e0014050300d0080143c3e604c9030354582c01c81380001c02c2c2400300d512201d403004801008006040c050603050b1159411824400c001c1c48c11800384040301025 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 812537571 1250 812536321 812536339
    0x8030904051e0115030b03011815021315140711040917070c05030c1903020409030327060515010c0b040501200309150103020a12020406170c010e030706020309 70
    0x38011440b00c14603a40c03559940d03040003940d40350a40300301d01c141c00c0801e5000c20f0401082004924042c8115918009040721011300f500b05503865500743d47e9260440d8906a6080c070008031400d80391380303406000d000f108842c00360380c0c0900103000d4544060720104481e420803c11000001441c02075406030681020340700031581c03000b6894421210003041070883c45001002c5480400d001c0d0010001084440a0b02074600000040c42032011041c01590100b000842d441070400042c10142d000c220402c1c001e107000101f4011403041c2d070400d41d0406544500c200107591803001840350354400c2c150403e103440b40c11004a956400046c00d5075450b07500141040c80c041000909000013900308240a5000300a8040360100d5020381a5007a081640c44031754034403810909800040c5550b8256050740d80040c4601d12883c6050b00344907220010301c0c81203810170f44403c0002503098141d400182107441c400090003000500c030000520009070102941d119901180c0100300503500801210056102918910a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 812538821 1250 812537571 812537581
    0xc011d04060b0a1206080708150c040302100f02070626070216060908060a1109060a0e0306010e15030604032304240f03020a0e1e090c0409150803090405 67
    0x801041250b00c030300d40c5000009900300725036a0081203040c0c012480b59042000700d840d01c0b182561072589010b40c0035160300c1000e060289031508141c0c1640030781103610340c07483c1c640c4075404181d05007203d4041d00003090320b80450840340c9805000074400b8040510b0103143c0d8480700204a40018960503c21002c2e011503000302d0b0100d403092240124201c1c0304000440c0081d92800024541e104602ca03260080c022079000c145030182500030341085550a078085400c215083c800c1005540c01068040d01f8809201249400390300c0c248001c034000c01288009a80d1480d243c003001a1114405140d1886504901c003000300194211112240d0146030f011391003000d20360340b03510415500c210380260207074080d224100d02e003044c0b402d5000c06000e40030340e132081c100380108601a4241d014101d425804036860003194640e904000400c00c280b81e511904540d01c0040311000310b014030100362890804220000b4050005100d5401851100d55211211020451902e100503880c0d00514404078422600c68010030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 812540071 1250 812538821 812538829
    0x1205310510031d0f0c01021603121b05010507030b01180b0f0405130504032604080d0221090705030f061f05090702010906050a051501110111040f0905090c011d 70
    0x5541d01a0041a5600c44101c180c0f259904018036040741c80b0b1003400a00c0105501c08294030180d44002c0e031741c420480d4299030350303504900c4030040d0841c100b104c505460040311559003054544607018000001c0e007800c1c165402019202d0381001241401018681c4080d00ba001290200480d200c1064081d200c030507481d4138541a1051f0b904c041d9100c03030086200e41c28000c2560ac0706000350310039103a50540244907052034203008010030a5814144860000802141006c0c000b04030091444100503e04464802d1890405600b101307100b19244d24003040260740e11042004002030701b400c40081031400b0030495840c3d907440e0002c0c80407000620b8004044060f0742040e404101405008000008925002d44000e000b040c20400603200381d401c2c6004a84040b58510515005a00c1e840d81929105151001911008a2541c015055658400168054110010241c40a01035190f0940001480d0106070030603184064517041e1240c02c2500c030809142c1c0c0100d02d42403000041e01880f050b40b02200001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 812541321 1250 812540071 812540081
    0x30a0c051605060613091a04020d0c03060b0f030708030a0e0402071e032601090e0a021906080a020c0d110c0a0906081e0c01050c0109120531051003 65
    0x10345407441d04603400c502004004210280309040c16207103c445900303883c0510003540e0b035034400901b41c00003000c1e0704407100141c400b401d0f511900241c07203c080c003d003c0d42c90300f02c4800035074400d44116030b481101c611207180c1111801c980c0d11003240140002805d00c2096502c0e44111344c80d8109200020085402640310340c0c0685410343d803c10141c00040e00340d0311800340d51a09483e022000101010254000b0b80072000c01190012910141c0704134981c2852440d00c020b00e2001c40881c0710f480b81e840b003000180c0c2ea003002240c41064140545480901c0c001c006002d104c4003408040c20b050040c40007130350b2044001109110100305240101e8140b09004005003003e0f030401c40a504403a42480c0833442c1c1003107401090071a0455000c075810030500b019001c00400711030f06603044a80040c1c1d03000100703600c22400790080b801c4a00000441074000c1c1c0d6540054601d09070000c0114030b01140a102c1e81c841840412051510040d624010215580a040800c8500e005442c0f1504000b0070f4810300510952003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 812542571 1250 812541321 812541337
    0xf02030a12080a090515040f0b0408091e0319020a1505040f050d1104110c0f0f01050f040302030316270306060602030901120c02030c120706180305030a0c05 69
    0x903218440e1190030640500300c400c0054070042100d500204001510600c40d43d10804d80040281c07500c0a281da030380085604025005440c46a107500d0b210020407058a02c1d6801180301c1e03103601e07607945400300500100304803040c52001071041140760800300361004580c1c40c801550240240340280a40c1c40007a250441603000003904011410f5500b11958202c8001c2060f5841820303080305595a80c000c1108590179040001c003c200302d48040240c50400d50020b8401e0241c00c00d040c5d0400c1601941186000031185150300c0640c09441000c003510020700c949074108120182040c504d14140d01c000e9542e2201800c0b80f00c01c1441f044108281c0392107081c6041c01034071031003900c0c9540d00c070008280e042702d09140000e0b112103141610000d011400002140e5034618103840e12038205c02130212500050481030301040c258001048051040e0078180402080a00b8980b22030343c486680d030a015040340c400c00b00c3e950307c400342c074101940426041002d8039409189240c0216201c0300703120045070f40f8028200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 812543821 1250 812542571 812542573
    0x705030a021506060319050c0903010906050109050c070506040b1302091510020606030c0d0c1a0310290903011d0706021c0e060f040f0902040e150901050d0f0203 71
    0x680a03000a60115040501c00490b5602550301d44401c3d041046511041c0d80003444921480032100c0c8503030180c0c1205a0110440301070509050800000c00c0c01d580903403d04891641d071700c100601400942c1d10582c1d07007082c4a00c2255042c13a43c40d9440b01d603103203406480640007050742d0000030594809003500551459003e00007900a0a14046030f541d014a9424460700c1400803c5d400005c0c07901c0002d00c144542401402410b490103484184403501c03096000960700c5c82542c80001c100141007040035401a040b222030150b5038509200c2040240300c494020145405180700c0300a0081d252110b044552051001407540d88d520400000b40105100035030560001031800c50b9909404010440b1011242c081c0c0954007880c0c010510441c01040f0310b0415004500410310b10b079117a0030250090310980d6400605249003d407240101c845844241e8440000705400140a01100c0c40d80c0807a203412008200003003070240791010016458610501810f030060240466110030f100066400170030707042c0c0181c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 812545071 1250 812543821 812543827
    0x12071a0d090c150e010201090c15020a0b09160803070503090933010e04050618180f07050a151e030204090f0902090105030304080715050405101701210b0c070503 71
    0x355441240c142c02c020b032020800000e049138807540180651021140d00003034400c131940c1007019201c034041d40e02a010301103108410034035000641c0b071603415001c0c2c0206402030542203200c0c183e180d0b2000c2c01d50000c0300c03d034100b400300d0400680f000058a003482402c03500b068544e66000700c0510403d80f2240d401d418250801160180030044980c10048040c0a9071040c1d900900e0600340801c0d10b83c01d840c03850700300c448014800b4103140d940d01a15001113110984185904202d07104510381080e10000c1a880d4101c40c504010514141d0b00c140c4c001e029140036000258140030b00a17000ba84180001d00c03004007250420543c1610a40c126000303020b204500f0405000850100b4008148d421012400350003054008141c61070b000081e102215048401480348908040044150782c244032000d200340a42480302040070744e1114226210524184d907041c030700411085000b103c0020607480041e034400741040e00c2402401c7e00d24400200c60308014451f4407620341d50851000f5100d4060041c02601001c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 812546321 1250 812545071 812545079
    0x30a030305040209060402040e0112050c030615030714030c0f04150905040209010803040e0c070c0315020c100e0c1c17030901050106050306010509040c0207030b090c12071a0d090c 79
    0x240c0d01c0140500d00070381d00c3d00220380d111004d0004911690140f800748a03014001008022106000a440d041c03060741074a15006120303010a281c100c05640c0c4043c0c40d400481c0c80021820100310174002004004045110f0041110101f92148440c8581c14004c2925400d0020301d502c40e40c01299130340000030740120305a503960b5600801808140d0b0124800c4000200005980034008240d405039104540d806002d6125000b8003206a1f101d0541101d03006103404000001c5000d4442c140000021007501580c0d40040e4281d0324144480d442142075001d1910680710418580051084101042038a042081e07400c0041e80799440041d925000707009900554283c19001c1891001d54050540d001c02801140d0304d9410554450200f00d44440c00607806006550051406030441505004240160f0b030406849031580f161052040300c000000342c1c45440340c004103041c0900c4080380b00703121201809810782843c69903101d0860769071450b100008003042c1c3c4410704e0700c5c41e4000200254000b1703042c02d003150744e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 812547571 1250 812546321 812546327
    0x60e010b0d06050a0e0c0d090f0b061807080a02180d05210403080f1612051b06040c0902031b04030c0f05042a1b0606030b0105030f10050c09030a03 65
    0x407060620030340741d080000020b0282403007101001a0b40c5500019061030355160038015940c0c121003190760200352145000404100c4819a00303c1d090701070710014405141c0f007c180b0040711000c90030350020748002e0040001240e4803803d100d80006481601603510003c2c100c900d19040c0c0000d2450354400c0464164034200900010b85002d6080c8035030790941401c521281c2d12400c2d0117548030190005070100400c6611828a50041041c03400382c21080c10070807499201e42c2101140c48410a010507c00552008002c1d94a5016244086614002c2c032041c07400f0b41d90300380000d480e407081c0d180349074002c4042101c0f504a0f001c3c045104085031081c40d00c8541c0d0381400030383c004051280d41c3e420664000046200d040038001c0c08040c41d00e402c800107941e10394042a038003522680040c0c40801c0403109142e004803c0041888547d103000780c4001c200740b42142805008002d0690280b440ba03404011406180500803d051a0b00e850400001071669a41032803604180301314a80241d042c0a0b04007120100f6030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 812548821 1250 812547571 812547577
    0x2404050108010e0c0f0a210504050c0604140d0204110a0804060b09041e02030c0a080f24072f100c05090a0e19021b060f15010c06060e010b 61
    0x210907680da050382c1e642c40e820580c0d4a2021384030280519030401844018400c104000c1c0030a0307a543ca00071060b445a0f0405854050803050b05064a40d1104244410300030104108124400102c6006260620380f11004030200c2e00180c0941c0140800c036545030555a07507034010121100100043c40d038030342510100904401c0c00f12401c9840c0e500d00300000c08503081806d510341c0310b20b600441d403103481c0030760000303003254000501c004070703810321410003c80403e8450108810050204e82d00030503010590103811401e1059503100d0004001c01c0e0030740c0c114889840c00c10305806c1065800d02c003e01c103000c400c01c11484404950885081c1c10041c142c000f941030005141c0840b5200f0740703000c00c50a039507131004035014807890036031507403042006005110380c1b45042041e0b508440324815034021140c504d80c240d0705a030403c0e0749035072060507071086081c07001c2d5040c440698881d2888081c103010b8074203a00e503200703000f01c071804803810000c0340d03070b000d40070001075a200d117000c0d062000c4016200d680d1240c0c6046140c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 812550071 1250 812548821 812548829
    0x4060906080619050709030209040c0801020c15160806270f1807150f0201091a0910060f0918050105010f060e06030103110603100b03130c0e09060a0b2404 68
    0x514101c143ca00da00035103114050042c0002e546140400345035400f0400800f00c0a00151612402c3c7c01c40015000da003440200360750100324024284501d103202c83e0414845004000b1090140d0035140ca000c03899010030f0503a48840c00302d075907621600d030400c00703080e00d07265554038942000c041c503043c0102e03104a20722192040728501005451109445442912400700e031040000c580201c00d8000f14041c016202d034a05100180f0000500c50b880b5282c480c88010f95426600c0002c40060600001030002d02805034550080c1c40240801c0d4904000d24000340c10a02c45e03003a8055480d0f2219101011003c1282d41d042c0c0c0020003441156101d01d00403c40310301a200340300c042050503088000a080030380a0720b0407280c100d2101c03c880b200003c2440030342d40c402416440d10100300c80020580c205401c0c0030358028040b08003482207a844902d00210a03090540011600c034a4400805c030302e080380090107a6010b9149203000c10824100c102041d8680c5090741201d01c1000003810a480c2e0000300000380c8111 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 812551321 1250 812550071 812550091
    0x90f06050a02030a0c030e0a08031513060305060f070e0423100611010b061b1903020606010e040603051902060d0906200703080403301d011514040609060806 69
    0x18003180b64080e400c40d140500441000d1f00231488807404103036604055030344598889001d00441810700001584201d950070310500e104d99840c802d2080c060100003140c0c0c00300e568007100c0d0081c00c0601002d02154000c1c00c85500c5a9143e44c02c2058140c07000c5110401541100c49800e101e0a2004801508020354060b010000301588891091090f050058512409024255510f0203086c111a05104168801107020034840c4030706171802c40c1c0d01400140a0b00d402607001d4041406c04c0030004201d10441c40b00244242d050201c24400300340007041102034030002d072440e400750041901c086030707150089070400d40c689468117001d00700b03011458002c8070a410302480080c4040b001d200901106000300ba001600164224000030b000a008038034209401c0300540450001c0300c804420900c241402c02ca089200c00d880c1c0150b61701f10014121907035400030f00c80c0b000f48003000d0103284007001d4039402d03ca45030900004079005603064590390f000700050507082d0382c1844a036484084555075280107941280301 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 812552571 1250 812551321 812551331
    0x21b0108010b0909130516030c060207030b07050d060315021c0e070510020f011503050d091a09060f070317280f0e16060f081009090f06050a02030a 65
    0x1250310459249050b07030700c08807a150500002509200000c40000c10f4521044035149203a0b000c520100101c074030300702121551110050851804030019001d0354400740a5600c95002400000c0601184036480700300c1e4a042910784560800060290003650301c00382c0040300380c07403d80c00310000343e40091045c6078804415080780c0741c3c804903190484d0604100a007058000c1641440a0700e0503036445800415940304032006013081e482c0b20707400c4505504002d005245a94400c000f000383c00e004600b10b07150305003400c004081c50901d24440880d004849206c0c80140040c12044554518040d11544400c1804040e01e0301203903e009071101c03840091090200209600080c4480715205c100c296050910464500c5941140000c0f006001c802616501503a12a1600040b1503020094032041420303001c0030780300b050302e0070b4406403400c808882170100300241d48040041350509110500200d5681c8400061031084c0d9041151b20302565030802401d0034104401c2c04690b000f1034020354002d1850b0340e41008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 812553821 1250 812552571 812552623
    0x9091104080a03080c1e13051017283c0506040b0303450607020406080f030715060302030a060908090303040608040c0e01060203041206060e0702 64
    0x2414011849140882c2c1d004401180029100e80e00c00741d0402141d030aa1400d25201d0b140045000b0380da00c0c00c0c143c0c01c03c80441c1d0000c910500860180003850255003100c030300040d00c3c0c002422407280000d00e5070b4805240004c81c000200102c0250b41c4400c02c0c11031070801501e071074010005010719900b90300071840000402c1c5001c482c07404407200c034405000744841c01090400d00300000307068020500c41d0701a60368940c04045413400d0004000c1d480b01c070310b00f0f0342c200d81121804003c0d10194103070b80203081c800c600200c0290329003d08a510300703800440791b00d03071201c04ca4400200a07004940140c1100c3c060b908001d40c60300c200001a100c8140b1400707882102d208600560b404944442c40007942c198403656590000c04c0030759220744041402110712a20300090013000c01d01d1940306900050000c0c40d800100000e000220344c528000d0305901081c041e9651402d480290f5900450048841c2c040504411034100a06a800540104841820840245801e1030003035100d031107824241200984420b00d100d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 812555071 1250 812553821 812553851
    0x20f15102c0a18030806010306090203011a0c0c10020d02070b120c0703030f060b04051903020d0b071e0e041b05040b0a020c040510081207030c0209130b0103030909 72
    0x1141c1c2046400d10300c4a00c040c0c4514290a408050609080c040c1e480202100b419852600700c615a4025240e101d003904080c00018210740d40c0e0781c04443c24a10601c01403154180c000c09400842d9404141691202e004805180c1004404000783350300c0411f581c12031500c03680201d200361040d0503d400307035070480360758001d818051321460400c0a00002800f00140080740d10401038540b10f1b0091800062801000c002041164450341080d2845031000c82c0410045c94184040001210303140ca600380010f01c1c0d540800d0b12840300001c0103000849600c0021401885580241001c003850440c107031a0b00542c0e00c018181b6008044280d0042d41002034203902001d600c00c40e070312010b0041d6a428a0315141c0b5040a13615002502844218010002c4000490b6500e000b000d010310081d0f00f251580740e141120b0307036181203608105076503210824014400425000071585000d5901130b610401c0325a14410400215000c01e030307008020b502c8104c004800c0c10303800084482542e0a241c810040360121141c88 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 812556321 1250 812555071 812555099
    0x2220f0203090c131e1a12031e19050a0c080d050109050a0902010f0e0111030d0501080c0114180d0503070b090f0c091f05060304060207170307080a05040201020f1510 73
    0x140340e06003000000c02041d05c00d240c1c800034000a03034082c41d07064410350400160308030240b100800345c2c9034408181100114403040705502c04100407481d10b440c1c2441c07881101c1008a1000324070301072010201d42c8141c0c00340905d00000b84117600207031841e502c1061440b10002804280103080c849450180000c5100450380702d00c02030141c050f12002c90b1035408981c1210010b11200c1030034100b00440b140c1441c4980200b0240252107180800400d0079030500141e40d182c840400c0c01d1b18100155a000044030190310343c11100e0690941c8041c00700c42140d040070842d412003900f00180b4500c000a8243e041c040715544d00ca010711280d40c203542141502c4642c03103940b440e1a1143d5076000000801007403417803036103441c902c400020303208203020065550750014200340c000321029680190001007400800900c2c208840300303601c024002a0440c2000d05004001da4002403c800440d42d45201160541e03000304401c040341298402111140c01d46a030106070901c10945410707820aa026002082405200b440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 812557571 1250 812556321 812556341
    0x110c0f010618020909150402090d0515161d060f030702060f060f03100e0106030b092b1b0f08040f0513090b060613030b07030c0206070c02220f0203090c13 68
    0x381c10f52945800e10406d424103815888954040e908004074201034903005a80e50120b4051800381001c410001340451020130010040c000007408106a040384e240c008610703007041c210b44407036001c0300440341c4003246203842070405440d003040d00401000a02e0740d002070601d01c2800000700c3c01d910f5489000030701107200c1d00319410990682002c2280d03045094a80d1181c2c095003943d10000ca83d031541ca4858002018054504c3c4c161500310001703e6216107078802075014095000d0f05500c0381d0520711a4010421035220740c01d12000c2c3c00007101e05060100d400075020156400c605005c0d5510395448210200c03030b2151150364050144102c01300c2e4016014458132400c586c0003140e45400d6596481006600d504c10002c010075107044c600040042034218241620076561520b000880311404000039141042c001d003003000700002c04241c400140ca9401c15090441c3e4590807400e64003040d0b900010107882005048491940b011040100885000516062980e006e43d184200c488200e00010140d4500b000c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 812558821 1250 812557571 812557579
    0x102012301210f0302340303050a050c060c040602160b0d0902030f0601030f020a140a0501050d0b0910031a0708060904030504030f060506012010110c0f0106180209 72
    0x401000250000000d44540da212000002d8501e0b0071903075803c4981c145118140c0050b8422003580b0a20700300404121030781c0440c2030344610000114200880e5445560000904005000c50541d4807903000d482078610305180c03202038540303500d40302950280c00e8006101d102c0052080c820103140100c090021401a264540c04403072420100250240280219040032609480f51800742c0350000c02c140300642c0a148502d090841c903040b18010040c4080c0306811122803503414070f004200603560003164400b02c64082c2441c54840c1ca409c800c100082060b40012500452640c080210441c18039507100180c0e031040c400c1c8000c1a1a003031400900e4a001c403955804110402c011480900d04600000e610500c03910340207150a49a0b600e05110822100c8200c41c4e0503150000d00182e982c000c2c1b80903c1d03118500500040d0108010106c983d51101d03202030689480d0b60f60103c40e20a05050b08540c0f01121b81001c0345c11884000c0745080c024601d61103511010101d07203c20b9000c4148900071a254500010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 812560071 1250 812558821 812558891
    0xe06070b010b090f090109060f090b0619090f0608010503011a010807050904090f0b100b09100c050f030c07080c03011107020f0a03021908120c06040b04030504120c05010201 76
    0x91030b400c0e035070300034440b040d84203c440001da0625510b24030518041c00c0e04a4000c144d041c034088080b070b5045c1481e04540300460800700b4680040d1501002d80302c0b6000e40d044082c1242c0c0c541002500c0450564100301d41182035584003242180c0c00028580c12240250000c10842001072105c0b0750803544045032900040e05039020400785840745e4050075000708000d000040c00c490030340e24082001c40d44902100d521444030100540128240c0f484070003040da0081c141e242c6544c42c0c0c0011034490380d01244400340000840c2c19014040c040180300402000c5a003103d44da0b0b104a00f440e50780d058180704405036440352000810443c00c042c090307610180300c00040c803030500c82d682d130801a04125040f134540d0460304416001026035501060984000216008808403078103110b130746400e03c80d1080113484049410031151514417800244141e00c41d400c08004a21503c4a00e4221040d03c1580e008038a14508039003100d00b0b024202000f0350407504240c000300441c000c103041c2c0c1e2091107403034584050038607108 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 812561321 1250 812560071 812560079
    0x7140a1a040507210212070509072303070c0519030e010807231b1b040c1b0302011a220b040920030106061d0d29070e06070b01 56
    0x120200d40c1d0441e10903016640003580325501e030804403e0603005a290710b19800d0601003503040807a02406014800b81c06441194100380200d0388203413000e450602044030a541e400e0303041c031040000000e0810b42c8640c5c550b0b80e0502142c02444082411000e8605010740d01c5688800d1b901c040c14141d1459042c5c46980b84080c5820064a10000040c086020b0000c0c94040e440c070844041003003002c00e048560001d407100800c42c03030307001507500c41203224800d42c3c0f1038000714501044116014440300011200841c5042814504407004e000380265a101c00012642100401d50190409485d4002c213112491038101000100441400c000c2d800c40c03165039000a030400c2c0901e050b000403880c080061b001003035a1880382e03121450114100c603000301711034012000d900c032450280035101c0201040d16080c80301c06249404051042400c040c0c00b4490095032460784100019001c0006404000d0079000250504405c000030002408407072480000c0c2501700e4108003031411100f500c0c43c064000718011056030034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 812562571 1250 812561321 812561363
    0x7050304050109210f0c12030f02100608071202011e0c0209060f0603070e010e060d0501030506070507021302090a0b040902030601030c08070c02040b060d111309020f16060f0c02010207140a 83
    0x4940706036003400f000b400209101c0c1c200c2405600088c070a0f526030b4084501014020304120b00c41c54654401c03420b1400421080b10001566020b4a0507103402d40c176401c4592006070350070516a14040400380c000e10b160842c098000c10442041d50007500d030038141d075558500300800c0001e091280c940c00003080c400300d00c0c054403940c5000682001810400300e88210000020219000480d55102281d11500107004000e0140145a08200d59062440c1002c000d607002640b034400c0150360150083d0301240d1213050707545210043e0000d01100c0340c001d54036501c55440801030f601c1143c03000d011a04002c11411032a00c01c1c081d95120f2202561909018181c075400c001c06030101043c9207500000c140240c00c1c0c00101407050f801c106a1400c5020381e031fa148040242c412a4035984003001d081d10501c10381d6466034048041300e5110f4041500140d1880c1103203003c030010003008040303000003494a4000e1f410190158010890f00e401004c0c03102c1e03403000110810b66940486070f4020704200c4040d0a49411501d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 812563821 1250 812562571 812562593
    0x105061b0106030507090f1a0306040b04080904020d1b0c21020c030f1e06130b0702250603110c120c030c0321060103050403022d030705030405010921 66
    0x45140300101d00c1590b6911910b01e000d4442d000021140e0707841c0013a4000404074803c0801c901d0301c0890210811105c5400280c07228001040500701c104000f00180411004104075404200300a00441d02c44001602d41801003140c084030400c036250780d0030742d07807031035070040f503110b01002c4e404100780300201c12621402156184213400e01007544100700c05203085907070070300480802072030110040c06a8246514905440b00140d03c01004540019003800401030b03182c00f117003003d950072100a11003600e400000b2413030720701c540262400056500503002d0a11031100f0402c03003120855a82803041d4080808550715500c1b4201010791540c3c80441c41121004c220300c05810000500c1090320706005d1203c40c59400d650060042420440c11004001480c0d0400440603801603001c0c45c2c100101d15255034041d550b11030031280311100c80c035008840002ca00d05406131a01c90f00d100340070f60303407102010700d00141e40341c10600a280c007141e50b4943c0800c0302c0003081203420030f104403880100c13812031950b11202ca240ca = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 812565071 1250 812563821 812563867
    0x9080303060a1a040513151a161a040c0e1b160606050d1a0a09020f0120030f18010c05100c050702060315090a0c020a171e0309011103010506 62
    0x1503083c013000480c3d980b500441c1c0e80040b038035400400c003169036400400d003c240503080402918501001c0662007003003001a00c10b54001109180ca104103170b03003400303d00000d45e601c0801555034400100000c0110a28076142251034841c086c040c585c45400200d5048020b007035219031a00020f1104404200803428070107015402540000350306130b100c0c0b010440003101c602040e14203000351401c0404410001600d02c0d40510480800c02c544501030f800501104800c104942c100100a0740b460b6590b05c940c18034480c618440401c490352401d2449122203d070304045207070b510702c02d20300c15401da0550003101d450203e1540074001d060051000c54040b0020b041007111081004818004500140c0303911000714020100d442c0d1b250521260f803020001b4011000b4400b1078064180610780c16160740001d04900044d03030250103ca4060b0328121425010300500b014054110105030901048151580c010360091511500038000b090011100885a10081c8102600b16400704000745c240703e15403412139806 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 812566321 1250 812565071 812565119
    0xa0c140f0d18050306180c0915240c0705010806060901020d080a0b0d060b130905120702120115051302190e0103021306020321061302070212190309080303060a 70
    0x203030f440c1c001007440c5c841d08480308443c55050f02041e0302c8241d801c00542081030b600b00c40600d442d02c2c0543c48100c1080c03142c0d0340140620005100240d6980004041995503800c2d80065622200b115492503901c4090748500e0340490001c0000c1111414590704849c0c4400040e0010310754034000100450308004014030b000340300760703658480303c00503078410107041403850140c4404280803642c0b40030000107001c03141d9402c80c0d0b0743ca4204e16000240c800300307080070307450070801c110b58035154a4000b003004120310940b5440719520345084510003000d20f1003200e0a660069070038020311705090240800300c1c46200410400c410b09a0240349415104101500d0812018035003d42001100038003c1104c105907080f2002503000819402c028640301903d82e0340c020820305412a807030500c1000318030503103040d05d5080301c402d0300020100c0c20364880c00500c04400c0c80303100840d540300d551102c10901c4010018000c0b400102c0c043d2001815217030000540380102001810052140d20f080b00420b0301001108942d42c0f1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 812567571 1250 812566321 812566367
    0x5030a1b0803070602031b0901140306032407030e06221502030405010e0c0604030b160507050a0b01060f0512061014120a0e16210204020a0c140f0d 65
    0x8070102032010b4034a080c4216405038072801c04a40110704d045816114140c00741081c05403900c5a03a10500c00d409664072024144d40e00e4990f000880d042071a41504020b03d045645d01d010410b0f1030310b103152803103150030307507000c001d100c0d404a24107440740010384106200d10710036001c80c01c012400b0000d4000b114450782d00b40c00e00380b4002d114101640c008513026a15a5552031001140c60820701c411908000e003107511518040c03e59503101c815080150a04079814145411480703003900400464180d0303a000700407101100b0141c80c1100184200340a1100000c482c1001d812400340580161140d040035940d88900907556034003440f40004601c414441001031203c040d802c40d071101340060401c03107882c1139014460300d040c2603600147e480030620340c0c040360307c40d0240c10820450311164900785d070300398030f82040140206000c2501103c59494040c2d84903200085802140b60080202c1d50860b118448014400c0c0505c0303046a111860016405142d0f0400440c000c582031184201c407000794504644807513 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 812568821 1250 812567571 812567579
    0x60602032203260d0c05090a150f110304080f030c0706081501050a120635120c01060515040e090703120e0a03200a14010c02011103070501050a1e020405030a1b 70
    0x580b58117402101c0030a1000911a5140c1080b44001014054050400b0004031103d500100380300301c0000820f00b0002030001150306005d040c13049600500a0901310340c1e2200d5125441600da0380148862410307031081c9500001d4440c0541301c07180c820703422004c141c411446281e0040d00c50f5808000403c040164040402d110252a0b01c64000a844807040e060303200d1031142d41c100498100b01c00c41c0c0c4151094032219948012002034942510b10a0030840344c0c440400041c4035015000fa81c0100e81c0c0039194410001d104030540c1c02800c201c484070f41d481c24284d1241000d00b61105031030302020b0461a00d0104d102c2d1660b024ce8014080444042d1803403c44503948c0c1c0302c06406000d4018030b42c01c070a41c110440c40442c542580803501500f02800100d01405401c07001a1030411810b20080c184020700300c00000c01001401a12052034002000740300f1840d00c968400010314890a15281204405400c442180d8842c400c2c0d5041d80c3d0042c1c01002e101e05540c80d400d008070158414a030740080a030b14081 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 812570071 1250 812568821 812568847
    0x9090b01050a050f1c0c1101090c0312052107030c26070c0204020f090108070203280507051009050f0109020d02040b060c0a030c0201081815040c080106060203220326 73
    0x9982c5e1803000d280081d18024141d801000c54441c0300c034164103681000092000300b010308021504584d8408841d8054980403003080d1b03468002c200011542e4034800d0a42a0052080c0648503c106840c0c1d40c104400a90070380142d441c00b040355204818051141171032000c240003c960320307400100c01e05000309843c4c4158005010f9034040c240340800f403140861181c03190350b002080700350484024000346082a501050903401c0c0c5410743c05d400e81416402c6002ca180600074811925401d800c00c0035903148540303d50520000d00307922070003140e40307200e514003929901d03806101341c003d0b05500400c80c0420b035006400300b0018010094030543d21190410805d801500104141e0790064480c1c1c03a00c0d40510369600006d000030710300410b056010382c5050f0020a83c0b000225a00ba0b20002a45a03e0a50303280d5040c102d0154a030340c0c1151a1562034900013242d50380e00040540070742210b80c2c2200103a100318a14540c4d6603001807000078807004118000c45000780a5003007050360f00707402001e943d0800141c1140d203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 812571321 1250 812570071 812570107
    0x30302030703030e120d091b0e0f041e0b07080109061d06031903020a03170606090d152d021e1c020406051b0a020102190309030803040b0709090b01050a050f 69
    0x80c3da16558800c9280f023001140c0c1900c40344900e0f41030a007103100c0e01d44485203940c0d5500505140c1a0203c1c1800a42040650758100360005803962241030010407628102c0c110f040c003540c0c0f090100d200480000303194803141c001c2c0340685444030300c010501c20007441d00300f800c840f0241000d54940101900011440900c40c0c2c00c4024501a43c02418028180d00340500036224070760f04642e80701c141104005264948000f211100c1d007050b030303042c0142300d01410990784001d401141c0049141c10b03c07100c1e00020b500d0300c4200d4071440a003003c00b00c0c5e0700c0640c1d1003107049104501e581110700034107900c1c0c0421106480060718031aa0b8840e010703000342140d030802c007080380d200341c1003800440c01c089a0751145041c500d50310020910b20200800252800d90000707541c81c5034500c48981603a0810082c5010107106042070707401194400c8000d81c80742082c0c500b10048100440307500c4002000400c0004e04480075015201903270f41c4c180c44103807502c3c91b000422a11742c1d005607180302c003c003804c10108009503c61849 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 812572571 1250 812571321 812571337
    0x30c0420120105100207080a03120e06090304170a23250f0e04170c0f010504050102030412020d12050a24032a09021e0f1210030302030703030e12 64
    0x4001e20741c100f108222490004048410440d80140820300100000040802009406091400001010031001e001a1040e0030501c1454000c100034402e012030300001070030036113212546060740718104221041d606d45420720041e20700900000c8905c0b40c13102d0f044880687c2600b00060783e49a00320101d820081c65a03000220244094500301040041400c0221101800d407040800c8420b041c41c0d01c1c0d1680d07041d20300c2a1051034050009d0740d031030043c20030446605030f10701c210001e014910709418401d000790001c035401c0d2a4141c002e2551207015201240c5d4448246076910b0f071541c1034818500801c0200002012b042d481541c581441c510810302c611141e5140010a440c00b001d10b056140100311503108032207616810800524214601ca5404244015078145a80058403032150f82c100340040000c41c0030549a080c0005030460590318520024015a02140904c00064440405400300f00d44203101c040d00580040c80307110006031203500150280e080060481e07540c182004c00d200420b40c4200a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 812573821 1250 812572571 812572597
    0xe0d050606010810230406050301060f0f080718050c1e190801050d0f020f04020304031106010815130f0206190e0303030402030703031b080d050a0506030c030c0420 72
    0x2040000355a030200035035500c003060f221401380309481d00c18058501c4280300080800d00858601410540c1c4030b95210340c0041030010b000344540d95441480440c070090030b001390406419000000b2078000e800143d072904681d02d0803041c0c10b8011107410a100201000b42c40c40341da154041100c5608480b4451850f03d840d0b9050030300300d0369204444201c51550910094401c2404043e40040003aa591051142856500f01445110a00c0c180c0f001038031000301074050941c0184080140000c0c994400720035001055030301d0843d10140d0302d6040141d540c5604c100080c81e1090342da0700040ca045030792003000041031701c103c0d00a511030b481030340003c0c2c0700d80109000c07041d41040440501c2e01c4030341c41580e0766210707002500a1031841c00d203030700030988800d400d000c05001d0005400703403044521550302102800c95042040740d41c8484030145164060a02500c402000354100340100d4131902d030110340784008290060091507034101035020f010140454560000600c48003020a00b69125064020442500650 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 812575071 1250 812573821 812573833
    0x6090105030c16050a030518040510050d21051e1303020409050a061d100b10111c120b010e010914010509090a05070908071a131737060203070e0d05 65
    0x540003805050b000c08c0f01d20039170624060013016410a0302400c107541c81034405192681441c2810003125121042008004a06212410203994000c010f01140c03050100401a000285400d83c501401a0078401403040a616002c100510340f035440440703e21b2180c0709030340d5100d0041d2508000c0320315055113040440002c0301c186040d414103020244090b070340003008103c02d0300c10f480854101801c138402401400040300c01a544408100101c810039000011600360350500c00d14010500c80c03d0410040000c0d045c5029603200303600408043d00040010b94405403041d18200510507140034111007079050103820451000c15407140c03081c83c0d1007285402c00100e56400c007820000c00d4080281c0c862407a0341c00c412010302480700705080d4030094110070524203880700040b0a0340242d4042c5135011501e22403400006010000c0301240c814014100b030306154104045440c04114240000700384822802810814480010380d0380d4045e5401214a10f09031780403565000c08650341d049810416201c5034801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 812576321 1250 812575071 812575087
    0x90d02040c120f090302330711120307020604020d06110d1a15070312060f080114070216030215130b07110114120603150a0b0f06090105030c16050a0305 67
    0x1e07000f104210490510100310110103620000d48801b0090066128000b410000412640205030705403c4404204e00c7c0da001e500b401034000e48484114a5805024000d0368080c0340516900d40a4074821140c58014051a40c1d07290300700301d104080b08030115025a40c40e500a504440240058030311101c0d16080050701c0c03400443d0003104000c0c051400352080260003000701e007140801d4191100781f645030804072030040b00941441c01812168000c10344030350340034a0015144405411200c030703140003003658000c03a80700c140040742c0310703001d4007a14001d074001183d0800c0103082141420f09a620f284060a080002e00c40d2070744800016540300304c10000c40429407030248180d1001c004011802401d100c04401100d5107001014021425825200e400041c001400364400740301c0b02c1c02140c1407181440361840c05109000080100c031641c1030041009000c1503810b4104101212704410050311401c0c2160341d80c003040c02d900e50010040940d40510858000f00182081180a0b142407080d03d42a440e100d070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 812577571 1250 812576321 812576357
    0x10803090102070f05061e0409140a0b0307150c03022d0f0304060c2904030f0f05030f010312020a05010603030201021917070f030b03030c06060307170d0302090d02040c 74
    0x70f035801241c5400542a4100318a45d04c45086901410803c0e41c510380100d0254003240c02c600841c0e0200821038200300782c2d14042150300c2d02891041d9111901000005504000e042d5200380f54022086850000384485107001d001d20354000c840ca100f841200c81270350a9040074841000064044460117440c41e011390414401482440100041c00c001141001d140c00f00003000c4400540e00a025000c130704043d42007052100740004001d002d41c80841c1150f041904d0000c10580b520300380740c2c00217074480d45500386251154003207078010014010440c400c0d90070760311410f10500703154a00406600c44da2a403800001c0080c0540401540250001a01c40d11039455160150300742c00c202c0c004000c0c0198000001203024000680c009c0ca4502d00b0512000220301d003a0001e02c05020030540c18030012511a090100c0042c0d014442c840560030745280c20340c0c440c1c5c44541c0d01400c0b644441150050390030305000911030381c050050040000c0682042c120550041340407101c3c001d00c0480001c1d4178000001c48500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 812578821 1250 812577571 812577583
    0x101508060c0a0c1b030501090318050103090506160e0a09140604020301080a030804031206090b24161506150801060509131508010203090307060e070e07081e010803090102 75
    0xca54511a481c100e5401c000802c081032400d07004244d200c0f40c0d0500b0207184030124010000d50380c040e00030059445542005498000c140c8848410110310b07e8010503654820302800b0301941e442030003058180c8800702c1162a008020345a00c0c2042100700d004c1e615a602c0800030802044ca403040007510807148040010207440007050306000750300400040002107000111803106d039805250500c07150b11503103402c0383c80070030390b070b10760b4240340e060100114900d6519880005620421600002c0600b2410b1102401c1d90103508071400b80389040c0881090106142248248684130b00c030480032201c030651030801180c4040e002040c0c0ca41c061007115881d66000301c07601d4007405181c141941407070b0107000000e8001c1300000d1003280c41c548400010408502c240803c4001d01300d080000d5440345004072070b40d60b0325005a003059031451f090030a01581d031b07000410300c2c1d82580c441d61404095aa603c0c0025a03860340b0281422040c1030844c0c441e000e0400002a10a0190940d20007441c0d48000300800240362136 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 812580071 1250 812578821 812578831
    0x14010f05040f0b0907091a03011a0f190902130608090718020c010b040e010c0206130c052101090308090f150703090c08010e0a031d030a080c10150806 66
    0x10324100030701c0045403014000000386548000045074036a101d5140b18100396982d48940105420b02902c0f421102001b2002200003006030300801c2405406060080e503400442c0809410a10101446a00d424040f0f0034400c1d6503041c4050288040d940e5207401c00300ea100c0e0340c490328010120501400340e1503022001582000c8500c000f17004940c10840468041444c1310411003590780d000401c4100d0394400c2d0419091010018010002a446c480103039018101c4450340300c00500075040011407031901c503818100d0840d04580c11001041c04c240900007801030003440005110410381c2c003010820004d00075080001e1107951403074514102107008510f0a0314100110500d50050768905004002d5442c0f41039000c03003149404940f00c0c0345410300c041200b010750841540c1e5401e142620380111030025403d10001d209030345030703041c281080001156248401c242e265258110400c218040341c1520701038400302d400350045c1c800704605001940101d171200707001c0d6200b020741100c00300184c1c0340600c189507100b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 812581321 1250 812580071 812580101
    0x4030c0c05030318060d180f0b01060c030f080c12040f020a050f030c040b15030127060617070302160f0203010c09050d03050a05040b0c030c070510020a080c0a08071401 74
    0x1010011070f03840c034148441a406134001146c0700010200c29040b14598851070301500002d10380506160803900200f0b4005d81c3d64012710300c00002c0e50380c403450350301d40700b190544c1c4e81c0c05042c003001e0401c4a982e000505111003160090008008140c0040c0e1200d0141d8890000082d1520720780c414004045160b42c8031512034000700e03440c0000c54074042210700704090220b900041c1e560032000090b92051b01102003040440c0044004965031a2110361003140c400411604205200300a80f0a019140c3c80e00602c0000345013042a08143e40c032003200e01c1d07008000c504000d400e001c00e40b0908014400801c105447c0480c83e0301c040c01c01e509080c483c0c03240d050800e181804040d410200410741403c02360350300808201002920041482c851001c0c1c90190804114065680005401e034035981d1300700d041c41030102d003e100c000264600e00481c003441d402038540c015007600c1c41d2644900b20740350081d02c8194100d009070040e12000694040c01090724a03c142500108020314411030750031103640c60140e180ba = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 812582571 1250 812581321 812581327
    0xd0606120b010918020706021204080c06010f0501140901110d05120a410106030506090a0e120a050403050a050607081b1912090b070210060b09151204030c0c050303 72
    0x22003e901c5981034078981c400c070740940d51b140030b46070a030024810452100c41040040d400d0108000e2014020840c0c043c1040031104030341d8a6800c02c2403190090300c01c3d60301142000d00e45814010020026151088050501500540003208160304043d0104501000a400003808408625010382c0c0b554001c4076110040156008450010b00a04d0000101d2188450444070070103440c0300b00500031500210903c0555001e50f994840900330f40030a4840038401c9606000050f41c000d01441004515a07140004012225455005080650048045104010b0100f02c0440880c00401103005c2da94884c40c0188101d01c0c00e958010900d602c0a0005038a200ca9030700b850104a0840042e500c603440381c0c609007156600e403080300356400d8600c010080c0810382044a100c003030001a100180c495140b41d020786900300c1c00100c41e10120340d030501614014040502c03021400d030820421209000121b10b003020315000314504034a000141c100c404070005941c8407450000c101c1c0b4000110000c02c030039001507003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 812583821 1250 812582571 812582579
    0xa110d020d060f0617031803120c01140604020325020a23070f03030c20040507020109061d060c03070314181204050904020904050313060e040b010f080c0c030d0606120b0109 76
    0x6d100c2c403903500801507070101a0403400300d555040c02034200841e522034207940e41e0541410900d010300b43c0c401008040743c0804001445504250003124424000c49201e90240401756030301c0b0b1410080390100c402107110700c040840000b2031681c4850f03075084000e03400220300e44c80440310b24a8562560410030502110510403c0065008005815a00e40c4124181103000740c0254044988070907507482940b260400042c8640560198020a01c07180150424807585009000c24a0b500907200c105000550150002076600500480074642000582c980404c90085004948201d101e05803504500240d10f0600100000070810002405807080d90440c2d003414901000100c09460052000c0e0103020f04000240800409108a814005160521112403525450010200101919810300940c03900310710341a1036016a240c0400301d0b000340d0300d440403a070f194150140e40c1d40124400c1c000e10301c024400708031844030301d014081c003802d1103545d0b204850f9110a01e440c107a80701282c10a050102c010b6048c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 812585071 1250 812583821 812583823
    0x4120e0604030816170903070b0906091c02093c0c0a03060803030a020406111917130b1c060e06040c0c020d0c0f06030203090a110d020d060f0617 64
    0x3012607030041d070400d455101102c540404a41391080007080c103003800032081030028000015200000b000d40407546a5078030784c2106800c3e07108010782d0990002051000c1e207075501d0061550b0008014680820901c040c055011680d00d20068502d0050740114000b4100712010301c030402098401c0881c00c0071100c0d4514249500c00400c0980300d1006000001080010140260466002000c3c08022203a0b2850316146284c000d4016000d00000200fa00c2219900c1d04400500c00004070b4820b1014100f60110703946800001c4c0745002d103060a02024003034203458020116180e070051821052040e80c1e1076000344d20380302444405c400d0100c0a4079040d020310500c541c403210264803a006031000103600d0240b00c402e58921300344104c000e500c03080c80000d4004000d9101e0000c0100c1e5214050b0303030210740d20b41b18144d0a90004640a110b207501c100445d501042401040304440e1001800307149880c42036801061901c1005c4ca020341c0c840b5211284003150030801d110b55401004544903c010301d920710304941e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 812586321 1250 812585071 812585077
    0xf0b090d0906110f0f060601121e02091809060712020c06042310091a010303050d02160204020706090b010603090201020705060c07080718050106030606080f2206020304120e06 77
    0x1500030001c09140c01900f0010401400d140c0c1c0c0454001c98071404c2d54420043d555000403100c0c0d03070001c0c0c121803014090fa081c0e40140d60400d00c182c000d5407802e043e104111402500803e40309036011008090b21360003c9104192113000d43c1407400546154980700601030030402c1001d80303c8400a104000060748610f0104003d90403640c0710612025240c402005183d503404a0a90b4a8060041071b4048482408507807002d5510349c0300d0180e42c100807028a101006040c400d2001402180d41000902c1c2c000c0c0d05a4000c21082e80c00d00007000709100540c010508a070060314003100c415903582490803d02c8400c1c142d1a00404103454280520812540000d440b0a51741c42030501610011811742f1007007400b4402070300685015011180c10960b5020741540810458401c00e5001e4504000460403510034040d00040d14400c1c2c85014003901d0360301c1c0859045000801100c1590034082d07500c041c054050116050701c5000f40b07805070701c900b443d0030201c039040031040001082c840e00b2107101c5540d031941b00035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 812587571 1250 812586321 812586329
    0x4020f01081f09091a01061b081308011a0603240409020316060306091529130816050f063009010b1e100306120f0b090d09 54
    0x1280c1480e482e014901c50004601e030240384600c28400702c010845810b01c1e070103414058016201c2e5071078440710a01c0c0081c04002802403500081d880b030b04905407504070440e42144603101b000468a8026001820b0b030392504c0302e0b00440300c1e0380d44423071842500c401680385162855508541451640c10700f840e440b40e02c100c08068200490b10101f50756040e036582c0d607200005036900503003640e440f140c0c82040741a400b0aa4010b11011a107405000b0400714414400d141c0c1244c0201d5116204604040c4801104c080001d0b07040701104052081c8107201e10311002904c4603040940d15241203500302500075040140300682c0c150351142c1c584041103c2c0d920980c3ca24403504003078848075039842c00110342c240c00355a806044015101510034a042d1049440801c0d4440da011000070401195503404120250501c039486100c41c00108000114501d0105004541504107060004080b952401c003640004040311007074074210b110400b40c1080c0b04400b00c2141e4450008000b515114005a50103426450310b402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 812588821 1250 812587571 812587577
    0x3050709080601060c230307021905011b143007020603010501031d03032403060622020d05010b0d0c0212040312030f052505070201050403060e0705130e010c0804020f01 74
    0x8100c0040c41519141e50002041100c1c0c03080d0700f000c5209546e0760f0380d444010b00303d00480300c0c094a400841a0450b00c003080c2c071016543c04268090307046c0c40d51035270007080c0425200c84401d80d5494070214420005d00c041c01c05028110b80310899044249011b00d00071640c000b01c415400c0207800c00603510103003200e05449003400c001802415012a00d4803544c100c0207a189948000000d00540409241040080c0c2861504001c10019490300381074464405540003030f000f1179101d288518800300751113004040c18041000608241e20001c01c0402c1e0b403002e038016980c04c1400904186a0b0f0120300440800070014001000d01c0c03c501c8401603068071a512000c1c3c0000d50140204008910030f820144009454220034040340c20701d9041c1c09a1103d640ca12002001c036080c038000c0c070385400380c0c1c00e86150f036130140c4815013400c0c69611400050440c901030701110380558000850b881c1c2c0c80104050072480003a50003d0004c0c0103c110300d0031580420000d50a110320301d002c00005940e091138060540c2c8080c6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 812589928 1107 812588821 812588837
    0x80103021f080f19060b030f09010b0303041403190b0610030e10020d061517060103060302060f07020d0602040914060603090c01180902030c09010305070908060106 72
    0x4025000224121000290000fa90500d03107a6000304e5080c0043c940ba040c40300c00c0c2e02104c0c016044552661004401d205000052030112540404060020000000040c000907a240290320400c016112440c1542c1039685043c880c91041054441d00d065020503d49464040004c0440303895020300003880407280c20900c2800b503104000038480240c454140d4079424040690f0191103905242600d07032000041c1d450f168200040c1540c11a503580d45d1881400c60300c07801e680c0001e0140e9041504102c000e00141c0c0d102001c4a084401c003114080d5102058808188a1000f00c00041c00c40707880420005140201904040d02c10900020038215540d9141d0030080c05020550b240561030784040c00030340ea03a501601c0b1800035514400c1000076103c0d510903800042c1d031b00c1110340c00c074005004a1621a42d503018020560401e225042c8001541d040518007591030754144603c00810070b0315 = true := by decide +kernel

theorem cover : BRFrame.Cov 812410071 812589928 := by
  have h0 := BRFrame.cov_init 812410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 812410071 ≤ n) (h2 : n < 812589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
