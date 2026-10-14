-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3613
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:10:43.778564+00:00
-- url     : https://prove2.me/submissions/79ee872a-4db0-40e6-a0f6-b9172000575e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 649640287 ≤ n < 649820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 649641537 1250 649640287 649640291
    0x30c02060f1204230d0e060c031204030c1e1104180c08100f05010f05040c09030c080c0108090f06041b050405180609070803090f0f13050405010e011406060a03140901 73
    0x201d001e040f040a139500701504d10014050650f0b080f00d0103807003400c1611600d4003a6001150709045510304108440403074084006903142881e0610b40148407500708101251260840c000c4c1c48070690310301c030a40d0200c6a1040c1c65502ca2a60780003440002c00304040c0c4d10090128210040c00810341401c9000003622016014007001c0c0c0560034004103940c80c501c60308074490724220040242a058a03a6042541d50454000c202060b090301c080325607403d0341e00003804903a0340010015000c080058001030070042a00c0e00e0605a1301c07244002d44504880f1007030716050b0402c0780000c00003500c40f5440700c000304c503074078000810940b5440480c0803a081203d04038480c1d2a20030038191000410000745038020070003001811090300300680c441c0c032801200c0d46c20340111580c007508405682c941801042400c80506140c60003c00c0c19042c801909050b501035407194a044e09899003150103015840ca23031301b64603000c191a9140c410511040754040d62050b02010b030345100c61240580026400b0f40109044000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 649642787 1250 649641537 649641563
    0x1b050a0906120b101805010e09040b040c0506130e1e060f120d050d05060609100e01090b0703020102070b07030e120d020d0608070303080705040e010905070903211407030c02060f1204 80
    0x40740c03171540c1e59000755050005c0c00490811607500d0b1b503100c40c0d03c194041c0404555884501c0c010b040100340303070010382e0312100200d41080240e8500f030b901001c8652000d0509510389072a030702c0d413084110782180c8400d210b41200010b140740c01c0c103000000002401412200d12a200c1c0da0249040c150782500400000301c0000c3e001d25011064084c0940000d0300b00e41140c0703805000400250700c0310007041d480c000d100190300c005001da0f00585c041c00c002c0084500156440f142464001e00075800b1600480d440701200010594140c828804c4919001c910402041104680c6c80c10a480341c0145441259442e001c210f507c4c88275031a805000c0c0240510340091400500b146005050024014410b20030000c06100401003000312046850445031222400142601c403d0011500d44003160805042307024000080042c1004d880107112060150b90b8031410003c015511500300c61040410250006080002e0705000d031801100504600c00320b001018500031592011520070041100c065543d01c0a801c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 649644037 1250 649642787 649642817
    0x110607091202123c030a271d09060709030302030d0e01094e0f0e090408030106090603060e040b180601030b04110d2d05010f1b050a0906120b10 63
    0x80070f1403a5504c844051400d12020090040051503501e5855943c40815040210384d11028202400540354101500d40c80120f0303401c4888400c201034075010441c0c403030000000d0b02c07113105248000030760340d05601562601c1c032010030320000f81585000c8642d19559a0b041d90b00003e5900e0107102c0e6140103036003851195506040010700e42d6541d84d030300c04085440c4c0307548095403100b9100390010454480c10030700c82c110b40100c800c480d00c40c0b06103101508081510280406e0028010245040340c0c11560f80500300c1d80c48180480680b04035204500c040703034110300070500150b00e410b0040d42c009030803180310040c030b80706c01034581c0307440b8081c2d00a6504000c19403c0c40188603102c00018170b40c02c41664200c140691a81d100300302205074020300b511494160314500c07070020b000303d14112090b801400a04c03030107900041c1c0ca0300a1203818441150010910706002c1035502440a4841e01c140e60b2320350010309032411405883e880c0c000119010120b070b0340c1202110380c0e03903800a1046000c0d4156204256500140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 649645287 1250 649644037 649644133
    0xc03130603060501180509040f02060d05040605060a050312030a021608070507050a1206240602011d0106030308130c0b071a0f0c0a0507020f04060611060709120212 72
    0x1030860f0781041072000c8040301c1c02c100c164521003100c105071900890390b82c070350402c100c0101c20700c0c50080d800350f4002801041c11005801c00e9000d40d000d08030420041d242d4108010801c0c40520405405406c010240f03403030420810701555004404840240c6080001c107012600c401c1a0442140c40d26800310358281444820040c4201812090b9035602e030f00744c00c00340120b4009a40d070200070003564031a042403401c142078543c0c520056900880050b621500e61b20302070b000e40b80c0a414080c182c04c0c524041540200705000e00c07400c480d015161031815843c0d25208a6190a10000a80701e000e0540c0d400603686c1110401030092a01502d4080c0d1103440080700c035910a0005411514a100b1880602090001050459400610b00e04000380e0314041440820501e000300241564440d1270000f0001e100c6811445003403c03104024190b80c89517861000a9841d0310040c000d0b8014140d034040480d00504180701d81980707041102c42100c64104c46180400a5031000042c84050702c6c580e5000c440c80800d0301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 649646537 1250 649645287 649645289
    0x30040b07150908090d111504050103050c0a0c1b12060204061803020f0103090c0b2a012c100c0e0103060503010203010e0a0207080408010203130c0501020c010f12020c0313060306 78
    0x200c414031012903a61500d05090060084c4180b04460308295402040908068001c00100240c03150040d080c1c58040390308250402d21801d8003007810400090a0b10810500301c070003041058964103121100e42e00c0302000c0200c03048040c103818086242c08180e801c8801030b4400668810000540d807181048001400041d00712400020b200112a007400180c0d14180c030240209420310300014455514208510344803800d510443c03241c032001038072409139511200c945502c0384820f0580c421280301d07401c2e2503080724141c001d10040c50041040040e468903a030354000700a20f2422040f1b400407152140c50400b241e60020031480849e480c4003000e2103d51701400b4800c000c1200310700841c01c0d0341c544504032051820003007807140d070b8070f03030019030701c02084800b00580e409040031000854880c07030402480c5680c59590f44080d611502d40301000a51503100080100010b44103a65003c04e0800001c0c0940d80c05a06101d90346c6450f07000e000c0703010424001c2000d44500c41d40a51010900c600c7c010b0050101c40d41 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 649647787 1250 649646537 649646573
    0x102040312080609150d0204020f0a23092218020324010515071709090109090809040b31150e13020411030f060310060830040b07 57
    0x2c0101080071582d104802d4a034040240900034500d03044000006100555181000354410300c04905481b40c1c80407840540f24201c0c072070701c643c0c403558004080c1c101403043d0080100c44c0380701d04200c0780d400350a0190512080300e0f401801164060094100401071300c005040c0c5a1090300e40c041c12809601e000c00001c000a0f070110011200000c1d01c2c0050b1001d86414050f1034040d50502280c100740311600c208039022301c1e42240212888220f13401c600d442035803004160601c1164a0000418852282d00c01d507107513140d00058840c501001d0405100c05845008103240c0d00c60940c80426400d4061100f01440d16018005036071030b041054000d1000315081660a440c0245030b6803800d001e01c0c00b001401a42103a041d2600c1c150104103440010064044100a02000c01c00802405060418819000d005440c00c800340c4460054070144901100c0d01d6110703200e0540c0c0190254080410018816044111601c400c2c824185065014010036842540f003040c40860009002d41407101c608501c43d00141 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 649649037 1250 649647787 649647797
    0xf0301030609120e060409150302030d02060f15090105010e0406030501061413050112020112060f09020c010e0d2a050102040b1b0601030f23070807080c010201050c1e04090e0102040312 81
    0x14044c003203003882c011802840030090b0350f0000707030b030505c5440c810300001190700804442090200101c0291a0207040c1c0b000482140b6907030110320700090030070b0942035241026080041030303868440110b0342e0940ca82c80f01da1b00706942d1440440841c070b0a008c0c1c2009808050390b0907107000d0452050000a005c00e01c82612524a07110052200350519951000c08540911701082c03d00b0040107400001d128a070b00004529202c10400181c2c400c0c1a0080d100c081061002000b812000c0c0c80c0c12074071902c0e0400204e000404242c4001c40807001d40c1d90051030324070707228035541644489648031801c903480b5400600c0d1003000401c05003070540402004075052002900986002d52450750341c1902556155801400944203008060010140b005c204500c2da402d0320403100d04903514100039468180e5402807540b43d000d1035905c045954014021b42d806412080041c500d051003410400032009200784686c02030840811000440c1001070160806249561000594840c510701d0a0310b503c80192071a081480 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 649650287 1250 649649037 649649057
    0x8160302120103080a0516060506120f100e0102120903030a0b2409010c210f0207050a12050f1203010f060c080a23070309030618081803030f030103060912 68
    0x1140800e1010b044030750290003503807607461400c42560580154142e810000d012440030000348a100d03046903008a0702170303d060201041c54104182c40d2861000440714660045d40b1155003c5130f2640441c0004100000050a00035140c8135041001d505440c1360496500220510400c81030b01d200300e64002404841e0f4103402c00c040000c0d011400174180c299240003001180006840e4015080f98128070b5211181c0c1c0c0c8604416010325409000d45c484110004e0b000c2200c0f031500c103000048180c1600c00090040403001c0c504114004031003c0c950007151b0702e0180f10700c83c0c0312000c070810491a0710303c9031400d016140c0d8100200c4401d101d1482e072000c400c0109004050700851034550807943c01c5403c1d80f8004207d00c10100304148900d01d10048405046400240c590901d0391006400302640e1284038248809560410200c0c8280d0801300041c1100004101c2d48900c6000c40900c807040d10006010345e42803000099007100381e40c1090303200340c4813240c031204034030304102004d412403401d4007107410726010813 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 649651537 1250 649650287 649650307
    0x3100b04180203150405040b09060705090a0b0904060b0c07170109020f0918070b0a0e0301060503060624040311100306030305040b090d1b0602190803240d0308160302 73
    0x1e51001a4a5682940c000045403034841c3c20314084541c80c4000d001803000d81080e03d802404841d00710348201d024054140400d1249204008907243c1c0c441c014280445281401d4075054558031040390300b0340c8030340c2d2454005400362150001e0902003800d5405442850314001c0b0003c03c560085c1d04035111640351114101c0160340c4e10708402e0700d01d401a20840c0706a622032405090341000d0403152501813050075400142040713114024000aa22540d980f074030000c100d0f0070f060a030b60f218000c00350b240c1c022400040d4179003402d10702030400740040c0302c0c40ca4040c100c20f19158440e0b481078000703031140c42d040c2c41080441e04207564102840600c900c1c007080304c6465601c008010307002c0c9004061046038000b40f4405c00399144400201101d4000340180e81c428a00c00c6a40300807003161003081e0160041a184e60180110007040c450041d801c6030541c3e01d140d44009201d41c84c180340d04500030510f04d811001250325203035803083c844600e04c0394850300f0941c00c00f140107198500a01c1c840f0700406004200c01720b00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 649652787 1250 649651537 649651559
    0x41a090303012c010b0409060f0b0d0506180103050a0303110a02070b09040603060510030b0906040f06021b0604032003040f12060b06070804090b0f01080f09190803100b04 75
    0x11076070b6100c01490380f400162452214051110701441c0402a41000410880d81c1c0100410889422120411003075a4a0101c6c4039500160310031840d003014284005020000c1c160071860303112000a02d101c85801890305170010111080e04161210741c86800710b00304044e018800c03d8115512a0303140f5081c07600314600250317907598078000c00600c0300f40416071182d0b0b601c55812540156500401c00d01182c40c10003207034021050701d44400d41d807624075040862445c000110340603001d075800c5182c25000d50a1034454034080d40c04418080c1c1c042e5401e03115a002c0060900603180914403a5440c0a14141032203030303811140c010307102c203058140c2042104000c9024015604030403112b2154042c110b02d0480d08010004141214400e40c00810000303014040100c2800180f0a07544c10160801802152001780300a44e62040704c0c881c0402c0204011695580456195581c030064240844610400e030041c100f400300070043c021502480301000f48411101c118a851000e03046603441503082c13501d02451041c7d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 649654037 1250 649652787 649652789
    0x5010206070329030f0102042306040e0f060d0209130203071a16060f060605040e090105010e0408131e03060b030d0527040204060801031b0806011a090d030206041a09030301 76
    0x311400d183c4290b401620f090100c00305074040080215200c035581c50140b54406907200129a680d100c0a410030707071501c2d00c0c00580b01684e040c541c105c40c503559034100304010b94102400641e406100841c510005a68140000d4892041b20103001046402c0d48149884c01619401c02c100c42007400803101d80400303c03002614846440c2c0358009465402034203158005041d10124482254200403001c106a078000c4010001c8403110400344a0302c1ea41c400241d801c0714002e000e040b072503440403000b00d40405e201c03d01624041710145e031040c0c062036643c1500d01428001d0300c82100d00d041055010000d00410388178182c3c10004c180c0140100400140c0000d01c54405d07030000c000c2000440b1222043e800703a800c40516598400b6004560310364690300042c0118800348000c0303401e882800045400b821250041008451041c4010700d00c2e13908101503034040b0310161a007400001c0c1c0c20f000c0520b180d91500180c1622034003940140189080a060410341401c410b20040503500310681401448a00001245c1c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 649655287 1250 649654037 649654091
    0x501081303120e15160203090f062b0b010c15150e07050304110d150b13230906090703030e0a0e0a1a1206060402070201050714010204050102060703 65
    0x408180c92405488025100814400781407800400e003814410014001a08030024003004520365a5001c5040c0181d202191a4006800500c40d440503428880401c04503420000c15141c201119003005101840307913400e0200030015a00000060f8180f41e2141100315032003846c0c4111003c809850b00c0d4084807074500741c01d04056550701c5500c00441070f28005405454540429a25410012001841c42d041680c0541d5000e401c00201003151500d070f246001001e40c445646c1840f01162403049000f4881c01840d950000410004002c5004003441002c441b440f03a50701c1b10304146005410800d00101c01010340c003941e4000b000b131143c1c980c80020224102d0b0342c1844d064448400a00115100c44500c0c0e204110103180c0390207000e080c2c612604440d90034001600f8850069034004200000740824841102407504103102140050500d03030028598076006052070b034600800346d9100c00d490f064603601d81456942c0458244402d6a05014580c0c101c081c6140034001c98254080c0d14a268802000e11 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 649656537 1250 649655287 649655311
    0xc06020d08060d080403020913110405010305061b04090204121101090f030b090705090a0b03010b220b0d02210c010c12260a09030e06120c070609050d050405011701050108 75
    0xf4040010300780c1101c01039a070180031141581021482c0d440d1004110f40d04032040311030581075884c41d003440c0c8101d0781201c3d003090045c100c6845503c0c104003500c8500d04400c80004040101156141c000e000420040c10a50300c401e400204038244500401c00d00361005041104039079081000c04c0320f0301c9484081e41d8228180e403105444400585252a9042d800140c00ca40e0080400c0070348481075000301d600040070740c001e01101324100100004004052540c4240f0140600100c500c0c484681c042c6058840181540000e5201c80d000580c0400703405082c074001807007024403180e800009021a0418000a00f018800800c0c140d4510403a241d02e1801e80c0200001001c503002a6044004001d018038500034819200e030a1180b003080c09440a10780540c0031a1510400000714103241080740c004042d04e45032046180ca03880701c0b41040b80e1021170151500c079110328003140850028440c180c12143d0b2034888560703035481c0c42c00250a00060030358605052500100402159030460045644110301542d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 649657787 1250 649656537 649656559
    0x6062102070213050a0e0a02060315010207081005100f14060d0b1e0312030c0a0f050d11030106120c0f1404030506090c0f030304031e14060f01030c06020d0806 70
    0x2840001e00070400069031000a4407451040e01241d0b038042400f40c4003642c03060180640d0110255990907100500a4008508100052485010030b125443c2240c0c14419202c01540da1490b40f03150030a151425612159141c084c4039440507000802da000b004120003210201d4501781d0820098580c083e21280626000250302c41d001a044e03004401402c4000e00c074031400e041020316901070b0050035907854020300c81d11100f040d080b4507a0080e01c3c0310301c500f601c03010310303012400c101220844181d90b20442440410302424094a109000b103203a09550210016240e41c90400c004081c418850a000c44d41c0349803a1040300b4240e840319809140c040b541c00c0c040c0b5803400d400803605062282c0d80c005003c60040c05c042c0711b11407402040320284610704a50074400070a66030100f42d241e202d140702c020b041040c0e80c43d00206180000800c1140c45004248000c401c0340009001820200c4c01c40f80c6c869415501c00051041200c403110a00142000d480189035440c10800060581080a014280b04080b0804 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 649659037 1250 649657787 649657847
    0x13050c040207141b04360f051905010b060304030503070f020f1b03101b030b041404110a0602030a0f0e0a0b0f0a1106130b19060b1c0606 60
    0x5107200301641e010003281c40c0549200d1142900c0c04444242e10301c0b85041440d155040f2201c070500440c0d07501d148603030310f407081c20018040100c400100c6c0b0440300c0c0418951400c011800c03d000010841070311800d5001e01496070301c1d10390b08440c1c45000711441000b0034020300c0f010a5014055903841070190400802c0740074500303412f0b45010822502d84049100303101444502c003040b88007290a100c015401c44000000d032001d0307441510b803840780343c114140b1043d200390115803107034000243d100406000000d5407040300003020080d4800300c8042d120000106003c130040c0c20521621401840342e840070314100385015100070310081c1d00303814040c200041004205900d9685580b290003c0403600042c6e552900c110f0410340044e00300500c0a00414103036007070b196900b540403031024401d00c5c10003840201c85899076506101d021b0302a0802d07103070003a90307141c00a150705544283c1c03000d050000740c05516003d00d203400d02c0c90a002c08484075440e9091140400c1640c1d04602055000c01110a00482c0914070403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 649660287 1250 649659037 649659053
    0xf0605011a030c0a090f09060e0a0b0d0b100b030406050103020f0301050c04090c0e03010e160605120c03070e030f061819030e280609050d050c0105030603011107150513050c040207 79
    0x18000340e1481b8641200050410219402402110b580c000e070040e0a42c3d03103e070050125055001c0c1c8a4200c0d8111b007400c0c1c0050280c0e10000d6110420f4000307c2040c0d0746860040403540c10445003251561b03503d03801401540b0300081c0321030320703e83c00b04c00034020b0345840810780e039180c06584545000c441d203861080080c42d0040c2c001005402c2e01500070081c0801c0e034010386543c1d00e40076990b040c080080e00d00200e2064400e104480d520700d0201c864040c00d46603081c009490303130304c0180f0003000c006054420301000ea42c184481c03180d484c50b00c4024070340707810104602d0055911080c030344210f5911041280840423071103030364180a03d4060401024201d45180442d17859080051b425444401604284d24000d13506242001a60f0301d941d5200c404580b80e50601c4205042c504000d04184d0107000c0c1c0c09a190b124000640c0e0003040034001113452805246848845e40003070750122100381c0d5018070404111003600c60250310050740003117403640039243c0d01c03643e858011580805003c4da400040102c2441594 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 649661537 1250 649660287 649660289
    0xa0321020c030f0301030b010b2b0e1e100b0d020d0516120c0501030c0206131407030521030402060f07050c090106050a020f071401050c010f02070f0605011a030c0a09 73
    0x80302034950301c42c009990f802a56109020403505114840004501c040100c0203035030740c414207096940303501c2c041c000600d013084040360900780c5003544959010903903040500c5003040c0d1030340c1c1c070401300c640300c4405c0c01180c1070000409006041c6460b146481d1a40d944400e403540e52180c041c3e50444290b03807141003c4c0e040c10f5000240041e44a2141d0f800140b0f01c1e4000c40345080c1c603000b440c0d14a181070300d91004605070b0310200c100d4130040e80648046071451022281d0005d40610807034800060864200c85141000c003168026103580e00504008048400c0003501404640c80c0380021030701c0e514180e80015068014500c12286c40c40001c01d148003009000c10440b2280746005184d26090b40e5100001085540034003c040b00600582c0d0b40c0070040e40d00007031884140c0742441e01d07583c7d001071002d004440c91b4104101c00ba5040d900d403082c03d014803200d48020824036019a07100d51901c215420020306a44040c3d20108a4841c001d80700d41e01e490784a0240d039082208105226030700c2490147c111202205 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 649662787 1250 649661537 649661557
    0xe0c0f12070518090105130308280617010e070308030c07080f040f03060b0414011229070f0c03140706021201080303060a1202060a080c1303081305030a032102 70
    0x1c440b800350f9100d1078000662103000c07850003d201541e1003c0e0500e0003507200c0c5000a0228803468046129803c807416414850a01c2d810081201c1400015035802d9804540c0556442143e010211075800001c1c05080302045580c002001c2045c5556117643c0a40702c01400421074841c00701d01042084400000c44600058403c070382d54071162200121000c4100900c012644603242801040c1d290805010f808281c405a00303001545a00c1c0c1801183ca40c0f40d401811600026050220807454042c10070241c0c40382000c00e03480700706150062000d80b07400852049502808070410740d920009611809002c4d40c0e40d20181255283c04291420324041d00545a00082540300d030030000c038070f042c6c00102441c4642800c80c0d052181d555602869048244500000f940140301003007034180e01ca02a0b01c40d40c0c1c208121a203130300d10705080301d03070310070300c0c1d0681a08121421200011900034540866034058080c00003100070740601c241c2d41c0d030042d0929220700e203c41c030300321010200f40d42c1d40340c403079030650f40da120b2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 649664037 1250 649662787 649662799
    0x1e0e06060607140307060f060e0711120903030d0509070f080a120c1401020a0c1104020903030f13051512100b031303180311090a02030712050424020a02010e0c0f120705 74
    0xc403d0078847d014040a00234101d90000c2c1e40c0028560911448581d4003101208026200c032002d03828031004039074050114190584410052000c041e00a4811644203010341400340220b60709140301103007a41001da001c0b180315401078503000041a030070001000c1b50622414190048a1617143c014520081080b8a283c1c0c0e500c0880e000c1034880e00301c00540705081c450004e6401030f10f036090401049004034007000e42c1592090020544140d1540f00428602e05615007280130340c1e69600000342c0aa0f100b1103154079003140412407000c095045004280c0010520602a00c442e0400840341030600004105021014200400600303044c0034404c000301452103400d000d0030850704d80c2490300c02e0705000f6080c6402000d0000010303c040049100b583e014484650b20000056410b01d40b04000d080041c0081d100d801c81c99601e128540e43d01c49082c8607120454070003503250090302a000c0d0071180c0f0091051110707000004d54101640d907181c4549904c0038103c4000e00807024025105107008881d41100360084 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 649665287 1250 649664037 649664051
    0xe280314010c08010f06020c0d02060c0d02071401090e040f0c150221030609070c1704121509151e050c1c0c0806130b03011e0e0606060714030706 64
    0x103541900090840840c40e10303a81610799840042e0b40700c1011a10074040180c0081c0c1c8a001945801707064510518001890182400c1103880c9090421610b01e81c24009a07002c0c0c4000c1003040c0507102d2500181000342400340075a46040049291404000c0005010300781e800c88082c100207411000c28041d00035001e18810620341c050001e551003054900941c3d080c006280410340c8400c03084100c078410b110142c118841501c03036510550386400034132000c54003040c50500c1224000c1e4464080c1008103600d2a48648440c2c0d1803c2c400421a49600800b5009082110f41008981c01001c400b035520440417000a24841400074410344010300d503034200c50981003000744400da410100c003610703e8080e11031300081e05601c115401c070203c0c0c40100d0550041031500d400140e161511108400821030840390201c3d030b4480b003800203400c4408450f2801241c0610758602c50100f0403910030160020341d03500080c4030701d0410790009201802044c0e070003400c802e04001d0480e61460140103685206030b0242c0700388024 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 649666537 1250 649665287 649665323
    0x81b120c060133030c021603112b050705040e0a0f0210030e06100602070f23040902040f0609050a2304020a050a06020f0105150d060e070f0b07020f010e2803 69
    0x241a40c00e01e454014480c1d0f507c242103901081307501000300c0303030b00030382d140803200391b52050040380210b4a81200007012040f0710610503072200f42c54080c0091161014000391070401c1d00f0001111440701d2050784560141480c000081e015031001c068564041700d000d1040145070380704070040e00e0202c90514031402400144296496141c5141003504c0380c1f9001c0c0c0e46090b441d0703414124440e03a00e109841e9038a0058090ba41c107002426005d441c060809000485e800240e500070505a8003031402c01039096640d00c1080000c3c019a21501381c02c010350440611102921203c0055000f0101031041c034031030318920103e401c46d55420401801024041d01207085166a40740103919060b1043c1c50751850350800380000c0c070f100001003000b2910000100b000314886003d031a01c80c014002d19003103100c40e11800328081014000d00c0f0f4060018400c011103160b4515151050100002e100c440703440c1030061000340200c903a034038080740f4144d440043c0300d01c80d0307421240440c000d150a080da00203420a120560f90f002d003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 649667787 1250 649666537 649666541
    0x50a0e030c0a0b0903030f070507170c0a1b0807090f2304050c010314040f0309080f0a0215090d1202010603020409030906080f0105090c0d020403081b120c06013303 72
    0x1041c0c0580e10b108011394070109041d44030301c0f0480304d003101e5010000c00101c18900500c090004280259007003041c02219201d00100e07a0711540c02e014855225130b025400700000030340794000301004010800340030361506007083c2e9503003d070780184000c26480d090074503818881c42e40401502d4054010080401003c41030500c00c0340720546050b1078902403015403803c00d500a0240000d410001114541d4959407500c5264843c070f1100b078100e04100c0341a800054041d400c00c080281609400d01401603840d0320300c100241c69180000c0d440454006100d940030030f994080600c00c642d60042c000c000c1d490701d52031049005004a0300000d500602c0c0c000c0c1c160525030302c0745001050303d5058451160680790303090301c0c088a440234458142d00038103e030006001d040d408005050590b2680c140941440c2d240d43d5401c8041d004108064400e0401400300300074801c040207030010b10009003100d01d01e03058000700225102d4805008501c600c1c1107010b00d1000000f81c3d000c90312400d80f1034150107000c410b0100c0300100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 649669037 1250 649667787 649667803
    0x1060e0310020315090c0f0a11031b030301180b03060a090203031c06050f0d17131214280318090f0516050f090907090e330112050a0e030c 61
    0x40100c900100042a881b4140300722246100c0303440d0040e04089010b0710880b6000e1514240e01002c1c0400d0015a60003400080c1210000c9440d0028548a6051404900c00d440000ca070001b2000d0900340c0c00200742d180402c4498100249420115102d0020f0012030300d503101d4440c030800d55030780c8409010481d014640c071603000d680f0704840d401c001a5441081000300e5030031100c068200c1060b20010780040301d10f000104010031007041c130803100c9591003026080c102c5800d182030b554001c0562050740410700c144041c9200100d4100d42c8116483c071840400b0101884060040900500750221070540411008850045c80c2c192000c0c002d10001c4010f039800740c0010303114402200d1000c810744c401c45d4052010f40e5484101c903009642480000e40400c06802d2020f400300051044181000c900342001074075007403041070100d0203403840144103a9140c480000080d145410700c44040003050560783d1003101c601d6000d000060210301e07515020415802811800404000c9110000390310703500c824003041c022 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 649670287 1250 649669037 649669039
    0x110406150201051e09060a15180b030f06010b0d02070501021c0f0606050a0e06070602071a1f0302010507030503060102120a170f040b0105010503090c040c0c210801060e0310020315 79
    0x303c4140d6498401e01901d800f40d602d071280d908440700144c807c2c8030301d502001449017420800165103a4408400707121007c20b0001182c441d8032a00c0407901802c007040750703950030409507005210940c501341c40c1001500403264500492900042c0d580b041c410250190381d4208034000b034040400c10a00890710040c0441004c00144900303000001540b103004200760f03544107110340c031407100c9604040e00300300440e803150000f111020307800d0000c0c1f40030500740702802d01c81ca08590b0b4000c0d41170801099a0100c061494400084001140001c0c40183d0703111040d1030032070340d15081550308c1e07445900043c0c0c2081e42a4501095001001c520703040056071040d4041921002c580d1008140c0e1a40d414032010040d00b1503001c0d2121130f20034010001540b050004540c0404950240d40900c00c0d9a4001415143e100301040001a00b220134481817100710b031140c0700da074400c2002c6a00780d1100c507030004d40342200500c50785042c4804000c400015407002c2c001c035100507102c800c0455030791424180b0030031600c1a81c1402 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 649671537 1250 649670287 649670311
    0x4080d0e131103070c150c0e03060c0403030e0d030c0f2004060807210602040b030f01090506030c0918060a0c020706090f030605130227090d080411040615020105 71
    0xc020300744040d101c0c808542a112840c645582c0e200b01040d03542c82d0380d241007105c41c2c2d501c00c0800f102d95182845100056601035036501010f0032184201860110b0180620741e510b4020441000000e401224005040b0000c0d55200700d0810503040c10350706894002c4c4007134045070394241c1c01010000b110402d10348082401042d81d1081c0380c0030307080c001152a24080c5030199400341c042808806030042d80700a41016051200559181e07981d03404080e43c2281e0301510074070358041300380200401004101405070042074001c100502d007005c0003954030081040650301a0381c1e81c1c0c0105485220400000c815048010211a121f0074500381840003010380d070100b0001030007550700c0400c5035441601d0503411600b040303980441150850711660002e14014001d0b1203074155902004005858501540105416003c1e030190703807650b49400c0382081e0300700501d00680380d000060080c0741580c000068540190300030b80c0050701d01c107242010a0081c400c80c0c0000428501b001c2d1150039036a41500003a01c203154180f04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 649672787 1250 649671537 649671559
    0x10030504060507020a080301090203090304150504090b010c2402160c030515010f1401020705040e06040209070e0a180905010912020f012901030605091611030702010e090c04080d0e 79
    0x100d88030750003007170014998413003000100b05001054011f1904990407609492501e40d55080030901c1001c0b462004012410100c0c0402410100d0320500880310380c00c2c2400d61000c140c0313a9981c0b982d10030045e001c984011020103280100003150341640d040d50070403420241c1d510440d040c183c9222a02d13120495480c031980210545d0076075013048441c12a10300c49101d95149003403003404c44207120150b110354110311801c0b0001030300d6074840c052420610302402c00f8003201c5c10b00b8010f02c422080300901800601886d21903510203506c50b1011141200c5d0485403100242e000c1c583c42d840a046080800350603903080440c0c140034008402c0d2000003144a0750200d0702120080c410360b5003139036a10b000003403440310700e00d41e8040d961070b0380644c000010a0502d4006140d58070342d800590050029070b05540342c1c80b1030071003040701c0c95000b2018034a072060141c0258245000c0d680004c0052000c26045c0f8014914000443d900503001f00903078004d000034400307980808281d0703a0000d00301d11aa0060510540341c1c021 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 649674037 1250 649672787 649672801
    0x280905030601090b0102060c071119061e1d030a06050c0a021c090509040201020f0a030306080c061905090d0c08030703171003240e06010519061209080702100305040605 74
    0x4c9034072200c0c0010b8025084503507035841400c4194001d03000990f940d5035629000941641c40d026104044151780001d46800c600f080d500a29550000c00040c608101c1c00903405001500f104410300c034420007000041340c40c556030022a04081c10200c00901e403506041c18800c14402e0f080c00791141c846244e0860f003074881e0b523099812541c2008034524010540c411024821410140600c5502034018011281161301081110740b800c05031a10030360000e0340d5414184104001802140182039084071103904080f21241c45904820102c00d410050050004030110140c40d0f43c00030b410041d4120398920312482c0e41741030380780d160703400752004400140b025403200508403210300e032090041140d00c0d02d54000c542180d0b5081c0c0032202180341c0c5110303018525119035180045014550340b0003400006803200b9450402489480c04800e00303412101410600180015030703014420b8400180b884002103100207007802c0600c0faa200754075019420480c1d042d400c402d01501030704844d00940c4034040c10499582c07844 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 649675287 1250 649674037 649674041
    0xd080f01030c18061203110106050a0303090e150307030507080d1704060902060c0318090a020a12020a12060b070b151c08040509070c030f02030313020628090503060109 74
    0x40001090000d001005004030940c160729000c00c0d12403d40001070042e1915402840d0b0040e00900b200010916250b0384003040d0207010301c2c80140020f84821f042641135903000b4081e420280034540e4079119a1000420b00700b034044004096820103000e40350020307281e0400b6600c61680780210041403040b440740c00c810300c0c1300d580901d00012030103c000d02c01d9111980c0c0d13200a01030869040e03030b01100500c68004813003018401010f80c0b60180c69004e0060110300280002084002e00250b5035902c1400340b41b0180e0741142907009c000014100060b80d0b404022000d5880303c12007910341e4182450a90003140a08414000740111401058110140d42e9008400000648030124850300b1004c0c41d507038004400071685000c5141407140100c50304154440020441058084500300006481c85200d076080c1600521500640390180c1b010303501d90320300309514040403410018000c1c0607420020fa10b0110445080590303004504000505406000c805c000610200d01c074001d03e8824042c200c00010041c10398 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 649676537 1250 649675287 649675289
    0x120312060a0b18010c020a0906060813030221070c030b0105091303020718090503070b0415060303020705060912060106080108121806032a0307091e0b030907170d080f01 74
    0x25021180b5041c0e0009102032505000310383c01c1d050144c0703c5461310040e40c07070300c90803005801c202c280002c01c01d207041401450070002174110704110624649040200f07a010424021b000d507a11030310802c03607600084000f4507108070a00a0030b4200340d8400401000f28032038040c0d04980b8122240321a5485401441400c103540e070000401680c40090204810413400708e40c00c0440f00407030000039248070780b900e500c1d00b940d2000c5012103e5402c000100001c0000d80c0c01c0311429010342e150100504d070308540e0084d545811a0040e0743c072521020a28440030707955080500f10046d0485e040ea50f82e5696500040c18598080c0505c65450040074001c0f681005a1004c0c0c5102580700354141d084694804148050307548044d200d4000c4107080e01142c2580d00e0800302c022103032092014200e0b524648401d0041010b840c68004001414003180044000f8141d60b07c2c1c0e209462458441546c4c1ea1942c007211480c05c5641c1d0f000440a40c140708241d4400000803480058118664a03074040710364640996544001003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 649677787 1250 649676537 649676549
    0x13020c211201060f051308010c030c1e0c020d02120c09011502030f03060a0f06050d061205150613140105040c02030903100c030b0901030629060901051305120312060a 73
    0x4035004103c1144200440107050800342003007450301c030010074214082503540d003100030583c2d1100c140c800c080da1325110b16086031040349004000c81801010309c15203a64104000020841850703074500030756070343c00300700400942d006141001d81404420603617155122003190714030600c00d1100001d030145050050400b68400d0790701035460408c01c0c18840c5840c1d00007802c290b4228602c454082140d5004040403405803c441d02c449894802e000802000d554040e004802c4202d035082e0b10200042c1c0c002100303540c1d078620b5101c02c44a60340d40303000b003100c070300880000c0c0c42d13910704058400e00c1d498403080320179050720001e95082c44a01c1f401c0509aa5910590080c507405034403840050f01440196449070030601d000385004a10b00b003100c000180e588102ba0420382d005a640d040010140c0144003ca0f00c4600700d00c54080c20b001d103584001450f030b00807018042e06010000402c50300580030040882c0107020020082c1c0400c12421110039600d0b0405110400d03980b0a42001c00d41c00e281c81c480c0801140d00c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 649679037 1250 649677787 649677817
    0x18080c0103060b2a0f030f1801030209090c18030d030e01112a030705031803010b0f03030a0e0301061706040b07170c0d021b0f010f1103011413020c21 66
    0x141641c0360701101e078044132044501615481105842041c001481441e01000e4916128518541c0401c000700e62001c03030b94181403040005036802c2d00e4100a80c0e62142980141d0b0f600c0e0080500c03908000c1c00444001c0764540038464a0b46c001c80d0701540000111584e9400801c94014100b54601c0e06200700c81e07200d44c001a0101c2d61345d0b02520740300c0c10301420999003819607007003801d00d540c1c0510f0364004448154100d2038000903408682801d01c950502c60804442c000c4a50220b0301c0401e8480c400d41d43d840d000c010b501c54100a181d14250800c00090140c03054144110322038800d40d64842e0b209890480d40d00703801c24040f1307160a1083c14004699900c402130b0110300d490b800071008080e80000314540000390280081501c80d00401215142c00c50000d000c0e2600882c0801c4803800c46404007103114a05d4900b103032f54001101d05a0a1b207041d6004200880410203000d40007500000040711140091030000030001001d2501080b0b5400340182000200c007082e44420f4000d00c00d020781c22100003030300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 649680287 1250 649679037 649679077
    0x130e07030f1a0913050703112805090601090f0e0106080f07050405040f240f0f0602031b07030c031110030c08070c02120a06090c050109180b0118080c0103060b 70
    0x301d469103040350041011340c3d603500384200030341c0c40b58213010083e48143c0320140e2116043c0740718240b01e291814102d101e0003c04e00b54007110580d00c0f2800080713000e014061080d440001d41564010038040006e80034150065500983e102e074040d100395070074015840000d140700045043c01d8203c80c100c501441080d100c8a00302030810301800010418101182d08498440c44840d851503400703100c115683d40b100c1c4c103040c03805040c183e840c800541598414a611000710500700800e5902105489016019004000400300b40d00c40d1949020443d80010300120038a41d0300000300000021344140521081d00c41d03401080140390150704030350030904000080780342000001e044920486040801c3c0f07200800c0303070001003c1c02038000d20704000400115046c42d134070000541800f00641c0388400900c024130b00782040301e041442854121442c00b1000b000540c40c1c0801c040668011180c00300c84401e03100c281c1c80e1899a44ca0b0803a580c10f492101640824078040c0c0128050740d06c2c204840c100c40e0b0100c0780460302 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 649681537 1250 649680287 649680289
    0xc07060512010306090f020405040b0412020313060e03030403060c050a0e10050403030c022d040b041b0507140a06091101020105010b0f0f041e0509010e01120305030c130e07030f1a 79
    0x107800490b400b03c83e14006c64601e40c0050343e45108860045015003606240c9140900e800c41c1c1c2c000e9508071041c1954018446c0011003511f1568050507180180703400b03050a840c040c0401d20354011038000403c1c40d4105a00001c0b0182e100b0041c14000081c0d98950044401500034002481407200340303034000880400080c00400d00407210390b98580d20152508040000b001c0b45e003d4202c1d0015407113480030404240d8028180b51600078000d485100b2101000814410042e03581000d1804d080e05007071100114181052010360029030440b000714005895003005189400b1008103e028022038095004d130001514551051180505842c0400411031a0002d00c240700b00c1c0030b4014940d00c0c00b440004002c08103440c00c203c030103146c1c1c0c09810200041000e041108108903040c05030421450b00c517000c03004002d1402c164050110803605400c2003940c98403201d5501c209403003054a1500c0907440711340000781440481c010148500001c0c5c4c1c08105080003c5d28070b800f03807981c0035994041801c40c05010321407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 649682787 1250 649681537 649681541
    0x90f0e040302031606050a060801020f0301030f33060b03092505130218030d02060708040c0e09070603060f081b0f220501060e09070e060418020c07060512010306 71
    0x4035019004032030812420040381d010100c980c0d8011540e00d501c64085c041c061646000740c034050301100000754205840754414000340e0105200141480503541100810f00c0400310700101c80c034a44052840c0e0a14070815202031f40700300b0a48019115262020001e03440c05543d00380e0340074403451805005041480040301d043c1c090444003101895560800029860381d030303403200400031071041d9000358860000c480e2032103e080101d542d490003a00b094806001032030b40031804c258440d038181060707456a183c40c03c202070014100c2d044403410b07110381c40c00c5c06010b00b1700080074808c0342d82c550340500046498224440d4803108074891510280c1c08440800712402155003070a51501000d0518080c0306801000100d00f0b1419010580213803c10304c0d031103690204a405014003400c82410710a400f0441600402c0000700000c03c650b01f0080740b00c00d04400c641d00d4204440040c42032141d042c0800c121004540004e5001c058095110700c0390080020341640a4001e070350b22252002d00d86c0b54a80c1ca03644400c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 649684037 1250 649682787 649682791
    0x6090610080d0e22061a040308030408030c042112140409091b260705090117010b040507020705040b0a03120f11070b22051c0501020f180907090f0e 65
    0x142c090140e5102c0300e1380c1c40c240c05404401402c00540400e4151408441e030345900780a070001d40200380304120a1001c00c06510480c0e400139481103549580e9526441c1d00b50340341c0115000080321442500034070070150501c2c140040340600032828101c56061048003034a01c1d640380141e48100200134032081201c4c2c8110b40c410b01659010b2040000c0807520896004030543c07007034000c040c140040010f404020898807040521601e04140100f082500b0a000200503080c1441a50344066902e403502880030401c0d000414840d00280050100381010369019486096a01581b8095880d080c2c8240042c90915210300440340c0040f11890360b22168141110314840717a50b5000c0030302000c2c2407402c0606504200300401171007502c072000c5d112000700746000f14515000e00c660340d017104050302c140400d80c2e91041c640865064901c101d41d40c207280c0d16001e0f01a01072001c0b45900c1d220042441c4414200000c0080c070301d420704070385551a5944600094440c03a80350b004003a03c90162810900c01d074031044a84503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 649685287 1250 649684037 649684039
    0x60e070806040b0f12010603020a0815010905100504090f1b090c050f0f0a14041511030c10020c0718090c1a03160507080310060e040c051c0b090906090610080d0e 71
    0x10400a45940214201c0319846e40304504903800133a09848242c00e40069502510390460f05002d24200030480c143c6c01c1200d030280500c682d0740d034602102001b00c1c001780c1c07811560380405002500d041180d40d00050b20254400c94a0b49800c040580f6507103840b850071541a80d078081315140c2421440c65a100d5a6007011124800b4081066080748108038041c014100a125035206e58005100c410300041008c11140003030301d00c580c414005c0140c1098007191144000046090058482c8042c507582840d00415a008a907411036104091149000f180c20001d070960042902e009015034030035580240160030240104800e800380003150203080c40c4111040a030342c2c40e1514030b09000c180d858003551680141c50030708940349545c00402040e034209070301041c0410211010000c401580c240500188190035040321003074000c0c6c082c001f000c030702944134502162000d4070700d00051400d41d002079501d40065443c0340c0e4600c690b800003035110b68408924415244450050400046904030590790201490701035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 649686537 1250 649685287 649685291
    0x501120e030f0c250b0a030e01060506040b12011e0b1815211306021b010e0303041b050f130b100c0c0801020a081b0706060e070806040b0f1201 63
    0x4002c56074100b014102e40ca845501410030a444180f00c844e40080450030015043d071103010810407100d202080e40c803040c0e20703401c0c00700f40942500041401402150042ca91000c0c0220700400c071a81040040d040300c0b01c0c00030800c0001d0742c91701000702c0074070342e0800300300c3c4003034542d640074850813026101400b4880d090900d03102ca42044200054084030382120655014a0701241001c0401c845c08450100008082c0703001c03000c1d040840c89000b00600d5014080c1002c2c0e00014213920342c00a00b103620300c50742e550038002c001c041c8d01581000d8690b4015502a02d0b014400c001641c0c00301020a10081101d200a01040701400b00c1c0f000d2100700c3c03d039030314009455507841c101401c0c136444070801c040c010385496665000550b0140740c811914042e5801604140e8810703c84814040e40040050750001c41c2c19198800c44500a8107410880c07241020044c400c0d410584000f03807010328500118040c06003078a44140650b500b100b400103d6141c0600d140d40440c00e1001441a030401d164214082c100c001c3c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 649687787 1250 649686537 649686547
    0x71112030c1b070902030f04050d0e1c03020a020603131b06050706050604201306050708070215070501060b0301060e010e010806061602041118010f1d011215030c06090501120e03 78
    0x111384200e80003221342d890282040740c104010040d09108034440070145040111050b042240420354042c84507100003103650f0881d502400b814000c0021400c0590b008187c01c1c2da07403806c00981d842c03140c3d40300307821030752400d120050b200941d6201c081c4005669042d5502c6040151036191a409004054419038005940c0d0706c4a080c498038515500142200082c5181d5844408281241f0140490b5001e40304000c07042c4110340014a201d402c940c503c42c0c044500d4004e00b041100c080d4554031507441c00804540c40c2810008441b21088007440c100d61040d100c1e40b81c0241d100380103540d602e1020002500043d04e03007001409518184000c2c08110b10540310b00280d03950b0a5001c142128048086414580008908240c615050f2101507030400d80070700e400030461401100140130141c60f21140d41840c90883d840a0541e48141c481d640b9003c000c40b0706000c203080310ac0180c503484020b0300044e121500c034424082400b500030b0845508840040c0c2d100e0b05101515080314000f402c28155100d03260004001c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 649689037 1250 649687787 649687799
    0x1b02150705301501090b07210c05060c0c06160e12060a05011403190215030115090b0301080d0e040b031f18020105070204020a0215071112030c1b07 65
    0x6100c04009604140400742d08480148114200c2d100509615840c035029400b0306003a68040040801c031001001082e4031030a003880c01130103412025030301040c4000c2414050346d8166010301d030801403038000d03010340300d040d255080124407a1181d5002e00c0b44030b6100b0004140c038400d505088582c005410b14003201082d030950f00083c0c4c903012078192545980e02c00001d00c15038a201d4818240144902c1c2000c0d0294208840400d0b290300e84160303d1518803202752007001c10b640382d00c2100e240b01600610302540d40c0da1510b208070941e180740c0c0300c140c0008000d4400865884058003c0703a058880300c100518040c1c0c1410411990300c110089080d400a440d007000800d00e44041013541d6840c064071000c02941c84840700c8401c01c0f200032120035044400000040000350f40c12000310b0302c0c0180c06031000750307544132400c0060349045188041a0a4245601e0400c503071141d0003801c1800c65030200082e01c0c04050800382d040140d00090b00c00001d100310070400c03c2c402000004001360301c000c8802c01e5602c01c6039102c0e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 649690287 1250 649689037 649689067
    0x102011d0a030215070207051e04090b011d1005041503080706050609070c030806011d0a0b0c0f06060901150c0501060806190905060c0309101e1b02150705 68
    0x510031540315401007031154201a014440302d80c103015408800545403920310740095480345107100d014010603d5102c80500c0f8000d4540001d020880500140094a56032520b494050400d21510151071b948000c4083c0240c0031813030440c086c800b01d400d41415103003010204030007032174000c0c40181d2007481143c1c0000003800c080e0103004418040d610008851901c841401142200144600c0c02c00800e9804140041e0308032020079084407003840c0061071038040c4030311401800109043e0a0740a200c00b10002514200800100b01c44040d074000c1c0e8142201e944803039641d03540d041e2251544668280018000d0210b0442818040c2d1118500101d00114a444043c00c4460680251295401c124200300520b00c0d00e200101c0c9800a05504019181e115101c00362505005840c0350f80c02c40d8000046101c814040018a00b1440e115008202e801880780e0104050801c1880f041302807410600003c0301740c03a00a202d40340d040055006020154098070305281542c40050094081c450140440d10311a000c4c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 649691537 1250 649690287 649690331
    0xf0303090915040c050a02121c1a0f0f0a0b030912030f040512030415050c13180b0406180c0207090c0f0305100501200307020d0f140307120e010201 65
    0x451107202c0401c8044007408140e40706980040144001040f007085143d50003c0c0a40e1b160410174802a00c8400031303801e5414070784506807c002d4040c10000140d1407420000d13100b1500388003c80e01201a1803a80c81800418848400c080354802c00c100c5080104545040c01103900035446c0302a0743e0009910071840410350000c0d80e0803c400060710040004101e030800c08490f46201151031103055160640d50948055000d150031030081d43c4940105400c20f20f0300090726554207000c00d244074400d440355612450300c002d104583c603040d0f041c15440c01007802c01d80306070420384001140320410410b902c03428102509007040e401c1c0851055441c0003c01900500c207462542041d5500e00c100e0203860740e001000d40d60301601c079500201000c3d4040241d40e070400780050b0000c080c4003a8510700905020780c18114080d00f11f0280d00042d02c0d0785900b00704010900d00301c008030700ca200100d00035610441400d80d40e000d84580144250792482030f080307066024060b2001c802c801440017150013a86807c00f1803401e0f0034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 649692787 1250 649691537 649691551
    0xa080f0301060207060203030f13050a08041d0a11070807171306110105090615040204080f01060f09020f090f0f0301060311031b150309070b0705100e0613020f03030909 74
    0x8001400b003036505201800040c5010310041d415401c0c800500c000d050006000035908002400c0d00c0c004102e010f1003880c0456800900c03590311641d4580c440384a0810148040300d0160f0040b001030725401ca5445000142c6014036921410203640b0f0356091300719880000c040c0d440060048480354000039032001442100300340d0001c040708500e013071405010011014030807501641400708004141000148565210681c0102141c00c1011310300450020710480e04280410b0180d880c1e00000f0540541000013101c0c188070110500755900d1002c0c0c4101d020b90000c0000101d0204a00d01c0203280c5210312411030764008000300318014014000a08403100ea40c0101c9107411080395000c6a440e00b07000c0c008451a401100c54000520140010f4200c940c0440c001d40450300030000c1003220074100100701c05055600720b850ba5032421810b0403562040030324000100d0b0780c1000201442d01e5008100140a0341fa010044400101a542001a6040d80807a02c540510007840044651b179550856203000d424 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 649694037 1250 649692787 649692817
    0xc12190c030912031b0e041d0a020307080a080405010309030917010b0415030b011802040305060903090a1a071511041403010c110312060d020904031d09090c0d050a08 73
    0x20291802d80c054803c49030b5220706141c90990100c0c00107401d010380700380100c01072400c1c1004008180000b00140b521030901e00c947c00b800581e00c0c0d81d00348001014a8600d000700d00b1903c1c00d942d143c142542d80d050011700101542d02c02d00082207075501075003183c0d1038648039040c640041c0e51070307642d203c1500e40c1000e401092030f91905140002401c0030711500303441007552442d68100904507214001c0c0b00c4010b1142c03401d8540701d91404e221a880d145e05550180da48101618064148418095a20b42000c4041403042d002c3c2f0031700148040e0702c02d0300d4100305118940e03c1420b0684545602400204e95a801003e09407615400681c0504000040c000340c040c11811590004101e4141821181c01c0500e05044c006484100034112380000151060701c03031042c814020540d44d0380041100a085100000d40044500082c04105a0800350262100080c0d03960300c00400070704000c0011645007510500703015040703c540c940203400d1108044041d140500215406030740b4a41d80e0345400d5001410702d5101003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 649695287 1250 649694037 649694051
    0xc020907030c030c03110403080904020c060c0a02010b06032e090f020c0c03060103022202090406060c051b0a0b07080903120a09090606121d12210c12190c03 69
    0x160035204500c44c03c030b2140f40c100714103041202604240d101d10302020740800e80205502e107041d55140c045032103000a0b081540c01c3c90506148a214580014520354055403c10380780c10882c0c1064001c2d00e01c03c000b010741c515480c0d42c07440c1150319407110918000c903029283c61004508181135010700b4030b0000c40c2941c0166a403802d6500c2504000500d031203a446030300030000404c050b0343c030744006011030b49400e1100b0400700c03415820302000344262426560003500b840b000040311a0841b401c00c40f15030007030080d00c01003849141c950001002410002c1c2d8001c3d00c422050004000100180101d240700d8084540b90406e0b0600007490706a0241d2a41e280c10307000511040c0c000d9200c0d80c56001886414000d000050034203902422034a107081c4441082d550f0380640d401c020f8958848203204010050a40c0c0f0b40d14502c070059007455008a0814100a13500940d1144941902030410310a05030920350b103040c03025031120980910406807044014141803001c00e0070889161180210a6060f510001100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 649696537 1250 649695287 649695311
    0xd111008070f02010908090108101e03020a08030c2d07030c030620090402130306020a0818030c0c040e07050603090604061104050d0b06010318080409061e150c02090703 74
    0x30b2059100e0290031641401e801000140080b01a1044000242020f41903551010710b46501040541e01c03210b59000e22005030300d0101c0542400d40d00790b0b07000352a686034081c0c44021482d0389115401c110300080d40f0404060341c1700c6006820100c048000701c81c01c00c2d00d100100b40030920f00202034009942e255000b41040080003880d200e240165510164103110a81c01c01c1406c841d2800385850240c0515000544d140d01004081040e41c00b842d4001300442d290340714100000c1600744100c0d81c030840300c408110750701c1440c00c0000c15680041c40c0080104122a414002d00010b018400c16150041c8220302020441d5600c042c007440c484c4501d039000341000d18150901105542880c035000084010400040c0321580f9074001d000700c42500001111303415106d110040b00108a90681d841108502070004003c000601c8010001c80724401070500896866464014940b80300d4044031a615000703031010001d0315400100d8a5100095041480d0340c0002a000300313848401c110340f100f00180d43c2d4002d414030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 649697787 1250 649696537 649696547
    0x1020913090506070c1506081c0e1021020304030203120105040507050d1a0301050c072a0515070605070e04050f07080c0d090203070311010207140604050d11100807 72
    0x203944640d800d0100740d0458480e141c44100140c8104208520701310000c0501c551001e1035200700440100803c4502d566003c480d07112146c410382416410380001d04000803610828003820344480090585e80c80289142c41030301d41a0602c4400d500c0045092980c108088482c409948154003d0700030f565541c160182340c0504440c160081c41c8105e18000600041c258000141c5850b03a040c80c0c2c0000308051240c03c014041c400000480e0703815800c003070801108411500113044102d1241c5901400e03140740791900701201c254142001c4603064051801c1109152186c003000750107400f04034240c5003400719100d000a44000b202c040000c80c002c0c101c0c5083c00e00309440740139030210081d021561a4204074400401c016070107030058078940004650760318128802e034080850260f0060403110702c9980c82c42c0034000e200080c8000c6015004030345c00003460122074682000c45e0311004000601d071a040108101c401c0c10700b0181a90344580d0079002b41180e4503070f0721881c203c910f0141c507024424036001c900201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 649699037 1250 649697787 649697809
    0x6051b0102040608011205010e16050a090e0a0201140d06090203190513060203091603050a06141626091506030a0c050d0f051b01030501060309030f030c20010209 71
    0x2000340c0c4104410404258448003540c151240d502c40d0860700000d5040c0799014151304003464102e4020840c0c3c44d400761081d01c980f401103500036900c500c0c40603502c1080c40100c0b204210940161741041d50b2480066100f00d0140c2e0719101039224107802d018215028004807501a000502d4143d40001032000b00b032030101c0d00700c080b810400d9060007540f500003180030031210082801084a40c004c404903045040a0050412004902c00e02044042d92420240e50304c80d00c040d020b076200c501d4042503044441c1134900d12440b501c5134240369540c00143e0b00c1c040740d100c0e001c01203100c0725210401000703007001c182c520b40901605000c4d0040043c01540310b000e003500080a0003d41c420340c4183c0412002852004040003214011101c50031078168a0400d403000b42c51015005087d40203004002c0210000d0104040d6192070a0303808120980c0c85007010360840e001528064042080c1003100d0403014440d0300301a00d880aa8500713003801c803001031481d9040c204c1c81108030601c1e0350089651070040c2420a8011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 649700287 1250 649699037 649699087
    0x2010b0405130b040c08010c031b111e0c04020a021b06030105150c07051503041103070605190c020406061d0f090f041a0a0605010e01090803160f0605010605 69
    0xc4107040c101e100b108428000c290003840400c00320700207414054031401c0f0314010842c2d40001c0c0304850811000600400782c03065100880c9a86151428000b03100c2c0200e440c0d021401c0008068280701071201c40c107a982110400d8083d48540d01106000e40ca0f030b40040c6c560001075030000c0000d03951303100b0018070f030340200d1407500c1c05894140010480daa0b030f1b107054803025000c400c00499645001d150700600700580c580095410007a18242c09500301114001544224040e5149010f105c002504240c1c440b00c292288000040c02070100900c401c0302459008a2414241048c044803003199003c6015101264000301c007083d241003a40a40c6511043c0c4107814510486491040041c52000a052504042c000c1400e41241c10009020450507442d0710030509800700520010b80b820184d6200940400d0284c0c03400580c0701442c02c2000d5001d084000251603401c4003450809140180302c1c82e0700e2440e95806d0b90341c0c020f848030250100d00d051095902030302260f500c00380d454200340b00035481c00c610036241c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 649701537 1250 649700287 649700291
    0xb0a30090803040530071505010608040b0f04080a030522230a02031e15040c0302010f0c020a2d030506060405011d0c070320010c03051006080c030709180207020102010b04 75
    0x584070305d054030307910002d04510380c0001c80c3c5404140c2800c5074100140d03040300d14007503d4880040b44090f00300010718070482c412554406d0503901c9489071411008140c50051001401380000f0522038003039005543e01130104070f2088030080318209207024014003c4401c6e0340002900112950aa030780074220351a4290310001449072000c194046551341c881d0303102c000241400740c210410017200510034400850003100a501c1c850516040080044a580c801240414450b00c6071004490003107032000b40c4290014034140403603280221039091241413000f00300d01c848440c1020b00d214525551118040e601500003000c0c10314040302448115181a00140c040341000b660f00c0c0c025020b4049030541c0045901807142c2c036102c0d946019a807841d00002c0a004907008144c40703110207803055028150207011a5004d0109458481034400544102d0103400001281b50f40003c0d94062000001c0d07801c0602c0b807516903481650740c010140101490782e0390189031a00090703014150b41e424010403103030940031501 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 649702787 1250 649701537 649701583
    0xf0e06090a0203100510180b13050609040b180307060e12090d120302130e0412210b19170f07141e060309160b0a300908030405 56
    0x19035600c0760710810b40621503d03500006d0200b5802030061005000c0ca2a4070501c0c005203c1e050400b50420420450040d040c80803803e189040501802c1c0c003881024140114030b0300c0d982c5900c00d03002c00c01400c828082d010a40c444088000402c010445140148000202004030040071418001d0351023040314a000180301000311940c03103603111440580c2c059010f8181d00781c011400d40180c0241c6111581c50740c00c110780003441030803805e911486a0312400f80a0007101585600744e03400f00900c0345d1803803500c0c9100074507003040b281940301c400c8500c00140322000d00404043c000c8181a000c0c0c001122943c4030340000700080d20100128180c0502c0800902159403c0040c218141340641c807080780f040f5100010b0541e20030243e00f0000c0900e501030a04d55407481c0c07803940c0640e66241c9c003011040c0311a0030000014880401000d8071200000c1d903549800c40c00c40d082c5c1b034403c000100600c0140d6855070403400050391009208020340f40e44914000c03a03c03854207052050510025201202d032660920b10707 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 649704037 1250 649702787 649702789
    0x100e2e0f050405010b0c0d3504031724041508030a0912120c0311011a0102070b04080606091803070c030314072307080303090714030d05070b0c0d0f0e06090a02 70
    0x20044480c1d0b00b0b9103015032000c000180c5c8d1041ca0003403405032400c40e40d8443d41c03030a10240c400312200d1041c4e000b81c0f81e8103c08082d9406140700900101c0d00300210765540740e0400901d898010810140b82d0b00108080340c0030410801d6034100c0c22080e40214405e41c00091400c1c90103402442d000020034030b01400c80c482440ea13856040c800c260b62a0200100002c04904108050003521075503078007403620000300140c818401306000c1c4034852120041c09446180345c0040c88010712000c0382c0c00c2e10090800340000d51103100c14826a94030250a4000701c2601c890303a00007107801040581030b2540251801d40209146050207042039011440c140c80c0c84008100050206070012509080d03005101c07005d0a4a0a01e0900e090034001303103402a801c1ca000000520540030301c0012041e081d610014100602180c901c01056541e10895040030003080060220201298156030150307442022400301d14546032030601302800703e0f001c00705003c15a030b985000300f140000c002c02c42e060380304400500504581c8140d030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 649705287 1250 649704037 649704043
    0x12040608130317061c03030c022112060d1b030314160b04110d05010912020102190807020313090c09050f0d0b0907032405100e2e0f050405010b0c 64
    0x54102c030120110b03031004c5401c680742c1503c1c80a00d040301510300410030b001032800038040d0080ca40280e0043c4103c401121500c50110a200090903840c000e071881d00480c3c0041208212006200a40c41184803105030045041e0300784034986036081044407585a404d5103000781c4440041b018104540e10103010715050004242820030390750380c0003013000700d40340c0d00e510740304290614104030141c00002d550000c108000054200822140c072601000a0f0b0403040d842c22070807406022401c190404640c00a40e008034024140310b43c000d40c007441540d15000461744c80d402c070b10001e030b40310042070f039901c1c5040041036902c007440320045c02040318401003407400003000400840040301c01030310682501012554403c41084130a00850b80901c4040e40140d60318414101c0400c2c1400140c1c0050400e000951b080e440d048040342500e80c040d00e0600242c4880b0018401310880c094403d40c0518054541c500014031a01c01c14014003180100052190800080c8401d841d81a48445522001070248550006006c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 649706537 1250 649705287 649705307
    0xc150a0f0801030c120215180103140423070b0304030f0f0e01050a050906070b0a0507081305071205210307020d020109172506020702010807020a020112021b120406081303 75
    0x184104120211546c00000c0d9206841c03079048a955800003116204840218640340740820240c8040040844110801e003000b002103a000708030540001409000c0c00306040a80ca0b0300f45802e0485203180d8a8046458403039106035410340c082003580800c650705a5012400020460712031070042da00000d02d4001034114002c00c1c0e140c40a010f00071600c4005500d070102580c40c1c05402008202c40760400010720002000b090b9149000074901034005500b00842982d0089900c0d0700200400180745011144500094034500466090003583c6c1406107200d401a500004001c0d80300c0c075103999091101e03000c2d14000c06d519090066906048908021440a241c040b1180c3c10031581207655003041d41100a00310250500545911000b5095106000c066400340c85014402e0300c81c1036103503d42080c01e070307520409143c2c001e000a08045698101c40015006042c01d41c0d5440003010001d078810312454140440044115588540440c0c104035065014002a42007070581d1407003180340a142c4c0b030091100010f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 649707787 1250 649706537 649706549
    0xd0c0b061906030e19080d05010f0f030807030309140f1011030114010c080f09040605040212061005040f060e150c062206020d0203191b0e030c150a0f0801030c 70
    0xd00c0d40c56604c000b0003030204000b1440e41100d0a0072158041c54502044c4e085000a41c80162420002003154628204510f081c2d90061503420442440d650302c83d0007070b51000c44110200354072004103d0015540c0840f02603544454000740c0442144208034074500024160406885070134030480407914004002180d066845404501750b45d2014107005070b0324655202c40c020020b440000b94810071082001c040c0180300002c90701884416522410841640a2250000b00111a07a80450030910b401c00c440151822a030074601d04245e5280b0400c100004940d01140c082280c42141800c070703107040360501d41c0c1a1900100d03281084e14800b01203648481c010894081e854070440c40407402d0ba0407410002c80d80360300400c20b41d44d032003440101c403010303400940e42da400030140c001d5028600c4482d4025121821403140480c441c456a162080790564074016226407d0700420180c22a5511506040000c0c8001e4a24850351800c10000084c00300d0b2202c1a40c0040040c4c220061002400c2a0b00001c1203401c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 649709037 1250 649707787 649707791
    0xb040b0306061003320f0603030403080d0c090f12030e04050f061005070c17010e01050402030c060915030109050624070828210515041d0d0c0b06190603 67
    0x301242800c2c2c0100400100c030b104440646440da07256000a00006106d940c000550218503160841859905d01560000030306842040c049c8025400312584290030600b038a249c00c070845540d903500040076501ea900030207092223000c0c40e114180764102d8061080e0440c00d840402c081d19002c0d00d0040384100243c002e0344200200c0c000d808600c0c2c0302e202170301c26954002d2403c034141e41d500c4160008100020b0001001f650910b4081104d50341c0611039a840303541c018024120102c1c010040003010b40c0642c0e41617502007804052864000c01744000380d8083c0092001c00110b5003005402c03c92040005501c0c14118020782c0302100441e00340400765400d1aa000c0d01040c3c844500300c00550f002c00040c41c00e6084d40c08500d00002c4503a9003c401c1c00100c004085103101200500141d807001d50344202d0326104d1301003502c00c20381450709190b4007a402e00000d04408882c04200703c0759140c00e003041c0d8061000000d41e80e020960500050304401a00050219411203520003c0e038a8810305902d00d02c101810700d5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 649710287 1250 649709037 649709051
    0x120d021522050c040b0603012312030307020d0806010309050d0e150304082a10020a030b0d15050a02131a090a0e0411011d040507030e07060801030c08010b01020709111308010b040b0306061003 84
    0x348400c03c0800f052b081d02c0e0103481d00c3e46000e000c001c0d1b41c4c440b078099080c0001c108201140341540240300d1b0b958107540040141200000001007a58110340304516644c11100110a0010031410750303001e90700540c0300300d420540c0e401070007035800b2121000041c01c008002d54812252811500084d03603000100085c2c0740540c4400ca290070613001440c0c900304454018004460200402440400701b40582c00784103020001512254541c000300c0c02000c480720350310f542040c0c0600840c1c0c0c01070150404c0302c440303005261030002c22901180c4030a020ba030204603a00b000405000803ca0a40041010343c0020719004402c040d4a084c48011041600081ca01070303990307140490540c03840398000b03000c0780c50a02c08071005a5911140204100000d11003664000c003401e10218401c2d4060188050500059004109242c10051004018240200c1d559141a4200206c11403542ca0b0310202004001480002a100c41810b052000769461a4801c910907000b946c100145640c8415040400e4101071400150310 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 649711537 1250 649710287 649710289
    0x105160b1f0e2a031504110a1d1f1e030203040201210905030301060203090a08150c1308100c020d020d0915030e01021305120d021522050c040b06030123 67
    0x2d11550a0224845400001044440102d40c602c941790038405942c200700a4809620800c0c0781d0040c1001407000611784507400c146041030300d40d001701c0a40e00415040359014000030700042114880140c10200307204203c40c41880550141d110380e4204a424254650725043d4002071007a000304d1200c07044041c00f9400d640420b079260744040045c90707001041342d580313584403680a9641d400c807040c0d01d41700300210f0b0004134003401c010a40e0b400300b524864440300c0588620a120f040c07a00803070300c030f1072210003500c03000140d04108000800e004003140d24001052850030000904000c18101224255070040b00c203079501c20741c440d030080c1c1180c01440e11700f69001c040440c2103010b41b0742000c0004880d03002103181030061844d81605022104104d802140e0810f4200d1010b403550b240b01c0407000940c0007a07444080b806244010300364040b040d081c120035a41c0e00148080310101a50b07109a506030b1004070640743e58100b510400e1040074080340c2440c1550700d051080c01066020015407451500050801849 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 649712787 1250 649711537 649711591
    0x15090302010212040b150f030703030806060706151d0f060103020a020304050604090605030f06090303071d0d0506190902030307060e01110304210e090f060105160b1f0e 74
    0xa00244982010307060900b4181141c00050306c0b015030b0a20350203001d99607440c2c0b0a4040c2c584450160140065034615101550004001003201d90024020026400098a0343c4030b00400d00f241e40110f00703412410001b0328400f000c091550302440702107031401d01c140b101004181641c4403509203000740c4d640a80b10422070540c0103e920964000c0343c042404903000c905038000c41c0581d03c040c0d007200c0c0100c5511051030360300c503016120004990420804200c10a04c54510a01c8841c461340b608003038110030202060810f01c0c00502500d45400c00b005021150480c502c1800d00596141c60501071040303241c0000742c491080e040004c01c407568504c40e80481410079001420402132a218154407483c060620140d42581da0710807901c2108034400140415004821036651801c02030100c49883c1e440e1540300000203000380056052010522580f0f50009004040d98201c1d88030b8130104505041c071074407071403030074641c1e0004543d01003044005010b00207851805550026a1100420b8031040113400841 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 649714037 1250 649712787 649712797
    0x307080307020d052503440105010503010603090f0b010e0a0f060f0603090c050909150c040f030f0f06020d02070c08071208031003020d0c0e31060e1005010f0f03150903020102 77
    0xa4a40e05664a034000c7d030341e6140403543c0000c10b240c0030318a80320344200e0120210009000d9180450740500041c02080d00c02c2d0300000c0d40a1249921400072101503d0380c9030018000d82c8114101c2d84a42d0420070035054a010306040310200700c2c000d0100500385107031440620105c2c040c18040550750740c0315505201821700003200070700d009007441d4003d06004007200e46441c4440c1c445c003200c003900b5010454021846045508403400c6d0244209518216500c20051621540094030300341404454000403c0c200c1c40103007031507403000c000140e0356042490940c0d55000c40b0350103c0c54a802c4040f04000158803080c00c0c00d07040da4081038aa80c0d030350311840e41d054200e01542019411440c85104d08042103528070b0300c4010b803181c0361104590350391a106400c41485900c410442e1109142e641071030700c2035040c000c001d4507034468880498041c030411801441c0c841d40c0e00c60200b00315110700040041000910602c8081d02c2490804103045082d0340302c107035035102e080c002104440c0da60600c84083c10b1003981139031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 649715287 1250 649714037 649714067
    0x1a0906060a0201391106060616200307051c020d1e0303051009022809091b08011517060a0909031d0301150b13080307080307020d052503 60
    0x4040c0c0704d4240d4440c016105008203610100d402c1960041228010b610200602c00c19200918087e918401806030a421450346680d401541e040c10000040311071304240c5480b0440300c00090400000c800300743c030b40314441c0d00c240d001d1070300035100e10f40c1c8240e082801d810380c68042c1d4003034440001e14681140d0740300340d45107001d0900c000661180c0401d54143c004500604544402254150b1140700c080124480c1001440d4020481400041d083c0a08c0280003000003290801c10840c903a41d90580042d903845014400d50000900405600c0d5600320710124003600e07510040c1c440303003550620054403c594044940c0c000301c0c0351800240c01580c41c425108058080143c050000f03415918024140c040709480140c0030040c04000c03059207080510484ca009a0031840221385c1da450011100565800380141e01c92400c15000c1c0403420f8207042000300b6001d403080400b030344c1e43d1030610402824a600103862900b004030800a0401c000d902403d400a012428280d2401d05011854192a40201410301c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 649716537 1250 649715287 649715321
    0x803060d08181011210904060602011508030403031d04020f0705030d0608030306010c06020f0708070309090507030536070f0e1b030106180f0306020307031a0906060a0201 75
    0x290408240d805001240040140c60748071005083d07000c20b664156401c80320861651101d03000f485407018416aa02400c0d6002485514022038440468151000c6801800143c0e46a0005408840161480200502c0035070b001d1800c0c07030304640c0d000300182081c0c81c031b00c2d9602041c1080907000303550b2681121340c1400340246680c0e940003149005622500003200181c0c1181c58103030f00260b10900807040f240300f40c0c0140c0d2401910305241da9008000e41200c0c0c11f90b400744205220500000303410200800300d05000c1e84a454000349802204030544070700500302c00400d414101800091070b0051801d5542e4420000884004003030b52488407113441d41e00030b0001c8540700c1d4180c00180c00b120011420140d50f10998102e800382c0c0c42803200e0580ca9040140c01e00100e204000401400307100354030404032600c1303403500e006d00a950348004640503105c0ba041685c1a46d800814007041903003620a43c244000c04090100048140350001a5685001400c060143d800014807010a5100317601655540242d201d00f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 649717787 1250 649716537 649716547
    0x20309180c1b07050303070f1203090b0c0a480c03020d03020c1f0e01020c09060910030b0907050a1d0406051819230703030c0f0b0f0925030803060d08 66
    0xa2084404050182c880440740300389c075041944a03014003c00e003a040716680340780ba16181d02c81002d540c4282d49803400c1001884031003c030907090f1528011900c400908513504000140149200036042d06c94200003d034560481400043c10341d0101c03030841e60119040c9034100100d04059080c444d038212101d900c180a1856200c00110b0008124800c40c0c160784c80b00081c1e485000107a03601c1c0c400c0603a060740303ca40880000c01c1032405030026176211707200321011502c40781e80795940044020300b60380440c400c6e0030190082c401c07402c103540408000c3c01400b0002c2402124074080c001c40000103000a0000340d03c500014124807100c40c1c5084003003540000701da00c1441c2900c2848000311058804a403038800c00c1044903000112000340079400c40c0382c00d0107058110b2a582c5c01f0345003600002d404592012a452103000401c512201c0140b0422110450403450300c2d0544445007001150b40002c844801c0030000c2800c80c00e0100307010010340b5480300d0000e5507620b0340300c000750b0981d095081c02855402b000038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 649719037 1250 649717787 649717793
    0x1a16030f060902031602190c032d050c0306130b0a15080a060605030c090402030d030c0e042c01110901051305090103080d060905040b0f15030607020309180c1b0705030307 75
    0x71150004c5c4641d6401e4601400008062188041d0640c0c80600344200c105000c0c808a00d11400684a00c442e80030021040ca030030308a8040241d4170a0001d030f0381900f100c0c0e0002d129050a015050348000d411000341040320380340d80c504480d0070b00580f485c00b141d59280040110f88007104546409015284210b440c584250301d0110060442401500e009024404d8880c0003402c002a1241c01036600034051310312001c0d041000c8009222026a840c05c1103c008000d81e203a844511a541d0006001d4440f070030a8002010305000c40189180a105140c0c900700c0180840d0258130181d409508091826554a044080103103410f180c0f5508601c0c0e004080034000820000c161000340300c0746451140c280700361a40c400b0720008442040710007910098042c800076849041c0e81100581c02005136144403c0e860b00c41e80807925002086034600096440042d1070221847d0421890310700382091840c10a0b2803501f01800c0701c681c011a41f00c41111821080020408541400300e9009014040d040300d0f00c0b20400c1c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 649720287 1250 649719037 649719061
    0x27030816060e01020703090605180a0902071a07051821150c070312050c1b07140a1202010804022b060b030303090604080310080a0b041a16030f06090203 67
    0x180c04403111440e10703580031101041802540c0d222600758460280c7c0501d001c00694190380705209191459255800d1031440d65900b95200340a0940130748010b88a040524202034243e1000b51020319000b0490100080c00e540281142c02540080c484124403031020070205220b040948516002c030080f01d800c41070784900014044511145501c00c4010035122103440914030300c2014400703400110a580d4015110040ba044641c0002d02a01182c0c9004402c0c4801c201000707944c141c4540c5030f08a10810412183d98081c0a140084221101300307155183c042c66540c6007200000003414000c17004005000d540e02c404000c07016035030183c030076000c0f048031100d4410403e0301d801040381c0b528a4040c1030f01d076504000003601d109400d60300c008c0480e42c845440b1051a0740000302551082e18000c0c0340492600c10511400003180c0c42818401028207103464140711440324401071004a400c15000c10860b65907504007200310782028140007407400e804142c4107000d00b04541010190341c0c000014025054604 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 649721537 1250 649720287 649720327
    0x501052b140c0d0c09030b0c0a050d0207050703050d141803030c060108010605090a0911010c1401020408010603140a021815090f1006020304050a06120b0301060f030b0f07270308 78
    0x110100301300080d40d07000182c82c00c0032503020240c1080e00b0540001d080944a00007840000c281e820458240f144a0702100d081c2d038010b2008860a4104c03d8041040100030049814096418103002102c80c1c0c06200311003d901541564503039151528030000c2c143d450610403650a018080c0030f40310030351707190080c80d406042c01d880340728001c1124000007240150144500d0002503400785014040d0124030004466800e410403041d6180320030000c040300ca2050901c02440108460000031408900e9414614040346040718804001d80185c09040c00581d2941070b040301d2007150000c032424076110070294000e18424141c04c603800540325411700900c1c00131011840d2040c007080002200070b41e02c80d58120b0700e80c05a0300ca50f0350840254042400000d0080d517010b91325140075400002c603048102c0009080d150703030b43e000f0301c50348800308020310034060742e40c0c225507010103003c030316806034144000000c0c280d240000440302c0101c0b810f5103401c400d0000a001100868001002c20740320624820b12840d902c0030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 649722787 1250 649721537 649721557
    0x90d0f0506090f0c0a050d0c0e0703150506070f03140708120916140112150f051005071e110a0b03190603021503101703130501052b140c 60
    0x80340f103002d01081c000203160303165a202405441c3c00038900004d001c51841003031412a034060210801248051107103a40300c1c80b03400507907030100340c00d0f40c0d8041440b0016001e8001c24000e10041001c54049a4094034200980e540340c54103800071459858005d0b9140030b40c400050598800141c00710940b01c1c64044c4901074003024003900c25003461140182030360b0203184100304030303589079410b4120990f0044510b1680c24120000c00304520404851384100301015400c035003d243c0c8004002d102038208a4440760381c02c08107080c0b05292550a8075003c0504105c2c418454a5002600e003c0d4208100205032408099002e031460340b1f959111192210190411130f040d14015410403541d130300c1c12245016050480c0c0d0054019112042a000c40014651004224003014a1640c0c40059650f017424100e440200401c4003a646441c0604101070807203902d9805203040001c20300085804609100d0501c00c03a12001349140c0100c1a4910240003910070001000410180141085103484003480200f0200c54 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 649724037 1250 649722787 649722793
    0x6030204050601210b0409020d0f03080603030c0c0603070507053f040b090f0a031101141c0c11030a0819051306090203190f030f0206010b0f090d0f050609 68
    0xc0c6000c011109008200d55410160724082051030300b509840d805144174800261010440503203940101700030a1921100300d4038040c001c003062044c160320860042c1c00040c00c40c061031400905c40031442e5107215032802c82d84181400804112024081c0c000c590b1003551003c03c3c0c400d44280710200b110100c0c2140e001c10071a62200300700e11503c00d500f0191f480c0001046448604090500d1800e6010381c000c81070031a041402c81006501c03d17503031080b44c0c00c000c41c420150141e40c903401e08001450b81c2c0180d11003001c100d0044c0880f00641da4403140c4130740c0c1811180e00c000f23054200030104032141c0754001c180c91035600000441c0d025155021011511408441a981075203203600314496003100c40445916186100d03040d0010005403a5030421820140010211804204240b00c118201d0012600c1214410841e924403070070035400070341c051070031035580c00a008203601d805c005080910500e4030100e0184400210b03807445039902d0b030111100e20303008250072030305444501d0907503a600030681790400c00384 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 649725287 1250 649724037 649724041
    0x115080a020901050409050406060801020f0403061a1f03090831030302060402010c06020405060f0a1b0b0c0f1c0e07090501051c2f01030b06040b04060807050c0d030603020405 77
    0x390007402200c21a42c0180e55503890103162500c02e070000c01c4090b10844003030392281c40015035603a00f40040e00310060403070300c0c080c0c0e518a1440c0c0101160b4048001141c42090800801e13099a1920480048009000325684140401e000214000c0c2080e900c02070008002060060030070038083c030b03000c1d9803410408403600b010b20780607102006115280f01c01001030b03104400040040d440b0740c0c1d4801d24984601005800c040c4c58800044031600300c0b40000c205041d01080d008200c0d079014980301038011411100348011040354441c2e128030380e0010103004401d43e00090300c0c5074042c40a07040f03035062052040074002c00c5401440c18400380c14500d010808a208c0c1b0f180101c1c100b00d09210b0641211402071075602940c00118984058400354502030b602200141805040b6003820102a840d428403100c01d079031201383c2c1c40005005c9601d2122140d021b1482880140881510b06007200d09a40080c06c281d6003e94503c0001c45403031091781c000c11401e00130b404240c0350454054200000380c91080710280410b03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 649726537 1250 649725287 649725301
    0x8010518090d0302130f1203080a05070e060c070911040503010507110615060705031303020a08150406020d090c080106140f0105090f03012d0f02190806030c0405011508 74
    0x1034031090300c40c40c481e80c00840218010718001d43c0280842d0910800011881d44e44a0718440f0b2440755074009170010101d11046010168000c0070560b110344564400c005500b010b040003000740554425650050b48002002070320b01c071003003050384010b0001b40c80c03d1000700b820781802c1303405401a20480b400396003000b0209007101c1c060b119100c00c540c1ca2078010801030b9520030041a424500c2e154854120340100001d8000c00c0040c002007543c10080f42e00c0f601e4040c558814007240880c0d90317000c851f07160080b40d0303510722a950200700c0d44c1d00107400c0140035890304070b41c20114008024400000b0b001c65000b03240090549010f40004040b203030b10000e200102d4030705105101e028103e04090600203a0200941640743c03500c048041041d4030058000075a039400401d070030308072411200710310001065812459404071a98040c100742d2001d03180302035043c20300c18030503403003410f114030318003001d104e9441d000803065202084114102c0740000c20030b0010756520741112450003403074442d1f5000200810005412 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 649727787 1250 649726537 649726579
    0xe01150617060f040e0f010525140403080d1b020708031e04050a0806182107030e03060c070203070b0f19051e041403060127090c150215040c05121c080105 68
    0x444121003850b09d500345900808541c0300300d9a01855052140510000c00480d80d1203000d003030610040500050390405424071500c60781e0540c040001103601001007840205d0001c026100828065148464582104411640030b40070b141c01c0325030096030120b00040d00300800a00c01c1d01514102584103022081080e441e5101d0404d2011001d20110b001c1c54000500040d100402d9687e00034a40746501107000e40000342420700c12744a55007850408135440c0158541440420004c0548101152401500c1d1042054031f006066041121002c4101084d4025003d0401c81d40303d0b0461001000e060f074241c1d10b0301c0ca520341080c001d0350700554105605079402d0800040b0b942c140c840107030804641007022064040001020745001c000b81d80c80301024000940c0f0706800c0703130140040440c20b825031442401d00a14101004031640d821056030814440411a08064001610000d4800d223810507825640340d841d01d02d4191284140350701010b0704201042c0c1c4001c8480c142c401c00c450042241003900840d400f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 649729037 1250 649727787 649727821
    0x150b072f011d0103150e06010f030e07090903050715091106310806010b0a0206071e030507051b0d1209030203090f0120010e01150617060f040e0f0105 66
    0x1c0400c4200038440210540c903002020800300515012034445c9030002002ca0310311240e400201c503100407406000140da000207450b2090151840c1c1000508001c041c1140d403800c941c450000c5d5540d0f500f0b030b0301040c988a00d044507201c5400400925003910350582d020000d01d0051003d407200ca44c0340350091044c0c03420070301b1581340d549560a540d0b1400000058503003450544100c4e10310705803032003030300260302c100501c07043c4e00030a00e0003a01511810440b60107800e0090041844082202d00300001500d2080c0c0c8500e18400c00c01d034600095950b0399084107880a10880081c20441210140704145080c000074504d03034084901d42e14000209000b101030002e0310004200100035800520101c170b5542811036020503c2d59052400c074026180b041c04013100d02c01905899641039440341e50001000b08240940d81c42015480c48003403800307103003010040c180f4207481c2a80080e85a8100412030a030340388820a0f03580d44004108100b22220008810f542c1c15444503a040d0650820000964803200381c21400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 649730287 1250 649729037 649729039
    0xe0d0b04230303090c150901031d0a031706041b081e0930040e04050102040302061b07061809050601210207020102100911090a09080403060e210d150b072f 68
    0x1407d10200c10010b401410002e42d101242c41100103001a402c0b0040025100590207500c418000c49075030104002e6248000b0103241c00340c2e04019050b003484040c424985c0f100011440d09802544a01030003440d004170326400c0c11482c2c00001305000d1079400110b240164a0643c2001062007840309455050b038060028900e6000081844100704070150341d1800c0794014401c100052400707480b13a0001e591500701d2074821810b074210348032a44101c80200649005409141844c040d9090031113070b40480c0c00711b80c2c014500c8550722500400d007240d000c0c06071204814000c04c01445e01c05207000102000b500302c11000da006100343c443c400c20440040c465140340b03a800c44400c82c5103030526030500083c1a8042c01444500c2c1d078403c28400440e440d00003520140d4803d04000c5507111110744520300e0074101003600e050002402e241c189064420300e0844902101000340400d03511899560f0001d8544035502030740e02c80c1d03000104102080030b45055403280c40c0303030480038441e661443c80b1085034002903804a9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 649731537 1250 649730287 649730329
    0xd090b07110f070f09090602042303070803090f0f040b031c0905090c040b09030a080705100606170f0907031505060424060c060b060d0902100e0d0b04230303090c 71
    0x240305c540100c0d044007211a0064a01615040d41e980c0c42035107141d00303c01802d42c505480c080c801420300d410302880b8000c10100b00103500b42550700d0700003507144c0100d410780ca20414500c00d00030200c2e1601d400151400c440141a1192403000c0d04c07500103600c142d6940c01001801c480e8001c6007910740328499501900003401900e0401d8100191a42aa4170032407903070f6890320807148250b00003a40140100102c62040e4040c020384000002500166411500304500f8484801720841d120003150b80d65030b41c0124075110030421616401849428114150409000401c2c02d030718240c000030082d00140d0186006507020402c250803030011402d60a05400000d1450300300000030420584686607905840e4050b0600003029103100c0001455640150245180952124541025031801e103150b00029400c80c20048040c000741e00004a1035641c1040080209015101007400d0041c0b414071207a0000b0360214600200f0806030b8a80d90383d4101b00c0e4504000d100d040440c01c0c40c1d00307101040c0f10b00b0360021095 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 649732787 1250 649731537 649731539
    0x507090303080f150303070804050103060609120210110d051b070303050706050712020c010f29010c0516030c0f090603080901030f0f0501090c0e0a0b0901050d090b07110f070f 77
    0x103d801040281088810083c0703158008074035501840103205140c480d0113550b96441c900b4001400340c40c0d003580b00d5404d01102420130000f81010261400035654103c4002c0481000c000302640c0c40e011024044844d40714401c10040d5850300140203248920324020203010b4164010710b180d5841445000c024009403081c444000042c0160300255042105410502d102040401c01d8008a0304152400071190b03446503903d50414441c0e2007000b0441081e80011250507108030f2202095001540c101c03410044008551030503c501442502181c54100c00302c052595a681402c03501d041650003041e0480c64102c200140249880c8030f0041105d03845812981420300e4080150000e102c018191044203440e0241c11841584501c1441d010300f40040c0002581c0004203001001e90700403142e403600516915900b480403416800603111003144c24030344103950700e011548034005090421401003c803407840c070034811010342114800c801b0400d0380c001c03580c2c4070750702c00031281c1d0b154500e1103a580c1d140e0403400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 649734037 1250 649732787 649732801
    0x30a0f0b030c1518030307080406080a05061c05030d1532040b0607050607020102180a03020f090415050a020901080702010b100e030a0b090703031b08040e040f08030f0a050709030308 80
    0x2000d130068512084c1e078210800e0091020034215401072004403030170b1000207800c2c0603c98002400a40103818040108424500391020910b5841d2000d02c04042800015032800bc00508008440c2c1e070300d0300c4400074000c0d84480401101d00e144907024030120100e40c000d03100d10300a8002100b202e8405500b102014200c40384081c400140f04502c0c030150480c804126501c0850001c02c95280242e019600040e40e842401c54841c8001500c520340c0342c41500e0b40101000583e4460003203d0004a0448400d00c594849203051890300c0c4084510b48821805c10041261b40c56480d03000d05440d400070380f540c84c0c02da51803000803800c0361304900c081a0b010040081c05035000c0e204481c5040c40c0e01010b8100c6000c00e0080d01c03904a105021500c180082e4002141401050f5022100d07891807400d54051003a02019a681d03580a80114040e14800c0e80380c010000e0188242d0181c0c0151003500042d91070b0340c0e41850062101700100494000b08014249400b04060511a060f0031048a03010b588098413621102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 649735287 1250 649734037 649734079
    0x2031305040911120a05011523040e0d05030f06090f040b090c0613050f18070305040503071a04030908030901090b2101061701090b0a03020f030111030a0f0b030c 71
    0x402507401d070480c082800402d44504e11605400f64030300004120783c0e170141c81c040742034624110340310410081c0010300700046595a04860301482450942800d0b00c180807011800818001d142d9103028820054000c800300e40000045014024100c040d45241d81c81c141070000041c4241c0340d014600300070f00b000601140e1103101080d0000c04d00d2003920720a10f102c000241451300200740c001c140e841c907900b08010b40d1801018103c500324003500d4652480140d10300003010784800900c01c42c18141c40c2c20000c0c8c00c1102c244115943c00364000101c0b020205814210968054100c4007103000c5039003c200461052000030503a0b5401c40142d4450303036450304164042d075a03500302c151f6226a070441d0340580c1016061010455020f04803a9903240a08506600700d1200b03950182d0183c92035a03e811018000390725a030050300e0039250103494021040c1d00c0200801d00404668000c1040c2e510084288800e00f140d0b90404142c072206614103002d0441201c0c100340e01d901241c15603650000358280312100b41c81140c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 649736537 1250 649735287 649735301
    0x12040b010f03020f0118091d071d04031d220e2b0e06040611060a020c15130606060801050112060f1a040b071a010e09062a04150e010203130504 63
    0x440c00300d0b0b0045507510611000c1d1940b10703900c2350f154001c070001c0d40340140c400c01443c4000c1401121021058940c40089070715042e002d0405020804607500040e01e078004445400010440541002e80410048501909880c50044001c1c1c0c1310381000e8400c04202e00c0000d0754941e00300a0f4143d83e90028000d5030501200e440e1002c50b0b011300201703400080d1290384810160001301115202c2e40c0c0c202d100d03200402c1c180030b0010700080fa43c0340705020100849100081d4403c02c440010003070801912450b40c012688607107403000038441ea06185001c01ca00d94003220b02c40c1201c0c400c3e20380245400180c0d210000b5075005000d15280001c41070010000040052041860500d0fa0b8602d00d2415441e80c5c641603280e80440c405403440b0001e0141c04003440014420303d401488124803001903410040d00f002c0d21000040d00c0d1640c2d40003a10005d41005401d00d103101114020200c89035550381c0d46e01c03a000f804510302100500480c041141c8041039500200440f944803e5000c0c25a60036410301c41003000a2200d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 649737787 1250 649736537 649736567
    0x1090902090f03010e0102090a0531020c0f0109210e0d02061b0c09100e040609050f0f07050306251407060c050d0b0604050607080c011112040b010f03020f01 69
    0x100600100c003e4400384180034030201c0c40d400169a88503514240451059654400d85c003403604807650000300c0d03260350075103d40c000c031141c0c186410440000001020703000d1800f40700414000c403220007280101c15404804058441e841072500c000120b400300c140da42000307001501062203002040300c4c6203401c808111103244020111424000d00c80c04895000007c0c4404601a030f000d071815403040d18101c854203504c0520781000400301810208020004200a84014480b988429242d07040020901c50300c4621071100c0b048030b003000307078041989548280340d10556000380101004508410348006a1100308401c0768420800345000c3c4900b21100700d580c00c000003000c9030a01c40340b80003e1441c0034007060784020b82d880a486030085a440320442d4a000c0f42d561103620200002c01c2962500c1d02030b240040e8110300710544a44a2550340e50151000c107008c00909140011155001074202c1e070794234000c501501040300280c0c0c0750751b1075141d0501c032404082e50015007403114140310747c41403007403502050b5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 649739037 1250 649737787 649737799
    0x2b0c0203030d02130906080a15020703120e070e0a0507020a031206031506090e0703050d030207020a09090f03020601080607020715030b09040c05040f1a0d020d1505040c080307020109090209 83
    0x2e081000007080b60825040800d080c00600000c01107500c5c2d0740280d001812144000c8c040d00a07035561058880e2149a440640840d004500712003854040d4004480d400703038082c410b008a46680f5000c607210f0410340511802503911390082039a07000244105842460030380c00a151035081350702c0a844100d2001c2200750901c7e00c402c000b00c005070000404100c1960070440206a56081401f00c0041d00d00d89032040b1203551144108002041001404bc0d000c8016414010794406060011600741620354000c04109400c2c40d041500b0005041d0598500f03078060383c2594166607c0e50b01071034031214151a80d00040c3c3c8481000e01400c0c03032046400d5441803103402c000500c1c40b200d10108445400071201500d109003103a8040005052600800311a1070050104019070241c41c15148054007001100c580203030503c20801c411501c9014040d01510340005000040d000a19490000303010110b504641c51019000005444100001602c00d110343c142c4803503254504002d506170083d0045030030254085 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 649740287 1250 649739037 649739047
    0x140d170d060603090308090d090e060a03050f16050d0c0501031107060903080f07030e0304031e170315060301030201021b04110d0614010918050417030c0304052b0c020303 75
    0x110501c50000100394545000c00d480603503040141c40706000518240385a006030321540c903174640c004413410955400c03907542c000d41e0325004042404d54000f0303040203210b442a480c004c4a0408002440d044144060820a03041038a41c414400300000219006100e41559881801503600030781005424000c054a824100b40d103585401069414000064021401e0b00c0140f01583c50910981039110000c0d0500b80300103940ca0400540d030307100302e00c80030341160181400c07144c4c011030100c090208aa0402151044541c5000082180c3d074000d807101d0028080502d02054079040c0402501c0c120ba4050b0040c0a5404103034240120b61148203003569170041e542c1c80c1440718081c014010345604c10990000098560501c1e030030ba509000c1c1001c0040c180a00d94408004044841c614004609680c01002c00d03c3d449900d01220460028182d200380c140c404000c12091891100c095803049026178200c68030070200b0829100e40300040080900d10000b0040808061801050001c1e4401c0c07019080b00d00d44 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 649741537 1250 649740287 649740307
    0x1e0601090b180412020c0103051521070b031509060d0f051f020a12050f01060f03020c0307060c080703090803340e010807020601051809010f110307020106140d17 71
    0x2c0c0012a4104c604407984032641c082168100f01d03410510741700703003820070170341c00e0040d88004001c2e035810b5014400e0380c030800240b0700c5030704403480c915259800328100c0c2c02d86611102d2148950704115501c9605c00389400940c4d01900d03013507a0403030103424040c00001c200d81c003e4a4540041800c144140c80c1d6114400040300704002c444c001d21036508a1310070041c0c41d245112001850500d44402c0d0f140c40508100074054585444803141d41118000e003002654250761200c141c2c0a0f00500940c810240004940403060040c03d4000054015003690350540310355400500360100e84ea0302c180900341003c02c1c000500381001240d5000701054600c0c0c1690b0b031012a12143c0d200403442c82c0200000542100b0842000356008000140c10141c640040e042c55818140070a01c5d400118803450300503990b60000c503044e04801c0d400310100c0180d01d24180428182590301e4000341c1c1c001c0c0c50141c019807030403000280c00c02c07090551075014003004003030020704503d90322400415040c4282106052404016061078 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 649742787 1250 649741537 649741579
    0x310150513140a0f03051209270103231c0908031606060e040807120908030705010504030801140a09150b030a0c0807030b030a1407080307060e1e0601090b 68
    0x1032001c0030310000c040e44510180074080070b0560028803180750783d0138240006000420f00c0441d011b40d49441e6500c5130722000000300e40666070340d00c40280303036420500f6142c01c6070081116816071380109140003501403d043e440113410340411031f128140c1c000d040810300200e21320310305140c0e40ca035500d805101306032242c0d2698150390086810314a84201c0340b000c0340400074a170045a000b0031b00452130b251940303481d840e185414802c80c0c1e00284001d84c4018544c80c00f900904c201e0015200041c02c40ba03c0e001946002d90090009807400d502240b1050000a80745200340c20004c0030b1000130300000d4082d45080f1303402e0068207043c41107130680340240b0000700303000c441c000185101d2a60001c002c2079004600c4805091910007901403404c15060403107460300344d24001484620140d212100d061520900ca05250909440390031004250000003100000d03c01142c000440d29450070b410b4400e035001d485c1d0044180d000d84900394610713030000c0c001000300c90450303400180400b030080d2038031150740809151441 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 649744037 1250 649742787 649742789
    0x403020604031815180911040e091c0e09101401030504150c0507170304030c1e08131d090a1410020706320604090303091e1202030310150513 62
    0x8440c100b10404c40c2044103101c5c0c0080c0044603040041c440015115400c2c0e00c00c44c05000c15002c00880802c01402c1d04100c00c01181403400c54501042280d420003c0c0300340d6006540e14030424111000ca0024164004003508807110140c2c42c40401c40c0c0c9074015009004020b01c107488005442071800410441801400c10075605a030715203543b183d02e850902804c134000194201540030a00800000980207035003054016001211040c1c1014000714040203d0100c03a0000c22030040411101841e40b10f01035100e040e1140010603100042c1804502242e0040455003003a503070f841401e00c4c1c2c0206441700c00c02d2440ca000c1c00280c0707003d010601100020381c0d2005030202c42c595130f10030300242d032540848020680c0c1a0344001544001e03000d200c40900716100507100303d00c159a1503421404041c069800403500b240d0040c05185440031100e1400314800c400c440c1074495001d091110f40b00c492010048031301c00d040546142a4890801c0c290800d8548000340c0c59040c01010048103940000c6082444 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 649745287 1250 649744037 649744079
    0x3010c080a0c090e0f04030f02010b010c080c2d190f0605041e0f1a100510020c1f02010b1801060c0312020c060901232e0f15050304030206040318 64
    0x86d00f401c1ca0020007a11610b02141c0071645000071494180c1e078451034000c400303034004007619290301074104200c0c208020b50b00361890b00780990304000c1911020080e90030120611a040d940280c0d0342c0c3c0140c8013041031202d0014159022030315200c000404c55408560407a0180700c40c699910800d0750380d041e504800c0401079540c0d0010071102c40400c849031070800b034a40040458940541020550050600c256009103403080030447c3c800281c80f4404c12036a060780310020514603103160a02ca19655401c01e00e80d6140c01542001e940c0000f50400c0c50801e22040e642062520480e840c0c580d04540c042e55040341102000703040b80e88a041c55106001500e42c0f0a0b942c0003500c80d41c14014040d50840307200300308110303101c080f01d0801d061008003501c18580c005c00051407002d4440000300040480801d1041003e0000100900425109107140400c401c1c0c4108117000360281340201c00c1920315010868005006a0000b0b00180000f886031180065031480709000303036021925603a00d1101040300641d0b80f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 649746537 1250 649745287 649745311
    0x130b090112061b050d1d120c0601090204030201080c070c230a05120a15022a12191b0203100b01231e0403020907120b03010c080a0c090e 60
    0x420900003140f041841c40b241d42d00400003089141d65000e8810302401d4600900d00751755001c102c01501809122a18180c1d000e400c0e206c441c041403c199606400c10032070018582720351000400c20044c90710880e406d0b290142c50300352080d40c0c0c0d420360842070351018400b03d8001d504010001a41020049003090b002d10b00c0d180305818170361150034440008070b6644000c3c40740c540d00c03103890203003100410280c0074141c01c01c0c0035144c1e4002e11040702c0068440d03900d0b64100102021103240c0c80414010381d03400f03121400b0061fa401c10481c80f41d01702081c061400801d20400ca0703011800700c001d0049803606403401044022041d0405241c0010f4108400c5400346a25251913282c19095503070303c00f03000c0445240c8801095912072280030b5405040c0100c13500780d003040c2e010a070202e640d01605c2c015a0000d50b40100f0b03200607441c2c0201d0080105031400c50000c00582000914503492174103000e40140480d0554640c14140d0350050028060300d03040e10b6000078003134800340110b01c030040501e90901c42c02c607412003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 649747787 1250 649746537 649746569
    0x509040c0e0702010902211609020c0d0906020d05160c090b0f01021603030804030909020a02101b020c2b0c060807020610030b0a0f020a0e010306080309030606130b0901 74
    0x1c2001c11020081460086903d4003802400503903d420359158000810000c071131400c110302501625100451518038482d8002040c00140b440d20f170f40092401d4840b03181680c03a0008804401c1e61b10310241c2c010030b405030300044129890a4801e0020f84141e2140041d1950b03500c181c2d88614190460640000f1040f0f1b841d04010310081c1040910392012070400c3c4028038602c4018040441c8280c8940030040420201c103000c642031501c03c0d04094082e0551110842d9242206880a9034400d54079124402e40d90800c41c0803482156100c12186600011b50003812440103524200144040411160b0501302d440e0f1005800e10038214203403000092084444520060800e80090403040c0001e1005046500000c2008141c10800042504403548409105210b488080916010303152100b0311580051000c540c440700c4030741c03002440792890002c1e201080b0f950340302e401c003030740340d10070101d0503a0107074412004107195090003104e07100f50b010501000640c5a21510000b1280202039010481d00410b1100e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 649749037 1250 649747787 649747799
    0x2304050f010e0309060d0b0103022704061406310608060a0b03010503032706030a090b070f170c09120a0314160b06010c050f0f06010807121b0509040c 66
    0x4076107032081925100850078000850001000d03441248910920740c7d440700c405c01c2d0780e03034020b80540b1103d030810148080a041c01e0992100d01e00404000039110b5401c04200146100210b000044981e1010b0541460151005c0c140007410508100c1074078020b1240c4040c06c4080da4041c1803101a1584e55140c0165040040400110414580003d08030305410001085203640002c211100480c9809400078106030901e0035080c1c101c42c1c42501078124800204100c0c90a41980c4020702d414070512300c0b21070645400717600315082d04100020101003500c564119030483c0c0d10920701030b8001b0356010784170300d440c4054011801d0b6002c0ca00ea07452103903001d1000b441c105a04001d00030a1101c908080307030f0501c0f076100360b000040d06002102070002515240031a02a901c55114420490340290455441300a203607251992a111300030f03080c4403400340e50b001207a8500045a404121200070340f0341030405403251251000040b00946038a43c281501c600001c0a442e0100039502c01e034042c0c0c408030450f501d011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 649750287 1250 649749037 649749041
    0x9081236160605180a0803160c0b040f1d09190f05031308100207031202030c0c011406040b0d021e010c060c02030d06090b10030b060d09060510060206040c0302042304050f01 76
    0x88013003481500c0582d0140070443d00041903e441160004410700315500c242086580d007001d80e00200030312800024082060007600d00c1d51022100180300c08688201044246013988505649840458000c0f038900501c20a2402450840074050b014050516109030b41e09440d640c0003290403240030708a404100040c0d64180201c1c086400c01074420b5150817510ba600506100b0708084161856a010004c00c21140c2d203001602c00c2200b43d84000c0040181042c440800000125009886542001450142c0d42094070b5108000d0b81c1c046c1810484a080d8007000702028010010281000010a00840411518083c0e06030504a44d0081c43d034542034100400f013500c40315040006128140300d660145610b031408820300c03280851400290060f42200022520f100318109070400310b00700683c00061043c60380c0950b0140c420551452401c0340d0f00c0d20142d854a20440703004d04034948401003080541030a40010f0b8001d4a2141c0e055801c603070800d0503081e040000e07102510a40d02a13100c500c9198024 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 649751537 1250 649750287 649750327
    0xb010e01080303013002100c2f061602061306080a1b120e12030f060f1503040501020405100e0a060518010507020301090609081236160605 61
    0x4002d18919810141400140c0700c0341040741000d441c0c44038000400803207480c02c0307504465000b4107941300c520000c1c40003400080c003450305031108850b081e01c0400075507030b0100aa941010f544107800200c0342103820042103421856040070584400034060b001656884006c1070021052014008050b0402c00000c01904009050401a5291600100041d4081e070054200455285040514454000400303805040001c80001043c03081d041aa40b90044060285100d401c2941112081d03645107010482c5242e60f540003250030544001001201d002c94800960740f082c000d4002520307180e52440031440c090044200c1030006080b141d58480359281800d4414020401171030b0007130910321881d1240070344142032511641401000140d5004545007908050403240d00850204049101e0f13043c4032105902c0b0f2074440d50f01408400009030340d03000300c2400c2c8491402003034001e000e91400c142640020004500b19181c0d034480c08003c41c19441000000002408003a41c645455450116110040d640a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 649752787 1250 649751537 649751549
    0x60c0303220c0e1302130b01030506060910050a0306031e061811060a0c060203010b040f0608010b070f061517010b031c030c1215050114030f060f030f0a0b010e01 71
    0x2400011010404420450741901c0c0d281c1c3e904180c07511415000414000da61a0094001441d803691001050143d48a121001030a88083c4260f0f540c000c100200361041038001a4000140c0500640300e6200b2009000e1545950600040f09074590301e640e5242c0003051500c4401e400b1428804081100307a0161072a09900d11801c4e10b03034214640e40340c80c0801d09600ea118050a8041682046a40304007210b081d031a0700000d00310750325611044160025807003401910a00003070b80b103000807100e108101d418100c8451840f00b5051030f800d80e450f1040da00510300d040d50819251000d0500c1040140c0d004002004c414904042c1701e0b03c6609910b081d5501c01042500c40c0d0010402000c010300e02e8150303a10800318511700040d0407805008241d80c01601401c020542a2070302e0446003200109040c18400d42ea426202c00b84900b4a0b03402408181c401115413980301460400440e4075030800d0400d504617500028161032401d10030600e13851404c04002000d603501d001c1c2100400c0344c84150301300030340035241c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 649754037 1250 649752787 649752841
    0xf010b011403160f0c060515010f0f0203090f0d05150103261b03070b0403020d030f02090f010309021c062c0619090b0a0c030b010509010f0815060c0303 67
    0x9003041400c4090f40e00f4045420600070f07808041c500f454401c610510180e0b0b4003000070070150806101e0418600d41c5601064041495a2804480240510031291106006130300a5203440180000c2c0040e01c80603c4a141e04004000046000690103214407596418a1180d400d610f41c550f0a0281c280c00f010901c0d286c1d43c41d00035003c15114042201290701600c402c051b209040b2800c40c00541c550720480202510008410b4144401c2540c08a8003014804990780d0a211240884005a0480c0311b410403240d40401c0084038244254080d40103030074541e00042c0740ca12071207000d8030000c40115244d48111289581e5030081c1081c0d1100c0c80d03035141c0072050f4031500c4140c1c000888010345d8914014140e212900240400d40003505c0c41e5401460400307900440c5000103040070f000a4010300300000010010900704141041a94800c0c02550390080059455048214450105803400400a0406000394000e5041c070b06c0d19456400040064140500040d035807460b0072900038000d00319030f00c40004808 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 649755287 1250 649754037 649754041
    0x17031204062f0f090d05012f04060806090717090c1203030405030301030f0c0504020a030c020c030a05061b04081e0d0318061e0e030c0c15030103230f010b011403 71
    0x803040c0103450803425190610f036078551442c400600040030100300201550f003000c001c0c00760ba5825070600401d4005140c200c0800c00042c0580280c540107501403500000c150b140010180d26101000c2504102c1c2400d1107021400d249206221100e000c0f070304400307954011429042242014844030420019203005981903060a580f02510791006200141c424408988210288010080b1000003460b000340119620085140c5c060083c02c90812500094091080000490708021907041c3c1c0c034070ba010b0041c111685c1e81c02c1da4600301c503141c5100c100c1c0c0400e041c072001c140002c007080400c000040810b64003001c0d815030724049182011102448040504001200d44600c0000c44040070240c1d0241c4045500810a1078000301c038121803800c07050300303400c14180c0c0010400c003000811001d0b0091058032220410700050100008021464584542007000100042902c0d0002d0408021400d003608442c1c1940641242c038000c010061412140d40d9882d814000b036070000c82d882c401c0b40c10062414218 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 649756537 1250 649755287 649755371
    0x10f1e110c032a0102030d0218090108010509210d05010810150b070f060902060307180801020f07021e09160e0f010509130209040603060603060506191703120406 71
    0x405070350800149903d603070048098541c3c024015110491035016085454528101010031001c01c3c010800d070007080c07800004a80c981d01070141c2846070317a58034000d00300001041d00340c80c19800000b4a85240003001e101c00783c1808180e004a40c002d1078500e008120518010304d107603040780c800022484036254035140811401a0b0360043e07600494220307006d002420500d081030030103844011030003548413500001f04809540c1000745400e0391910301c0403070401030391030b028554202d118040400c48418802c1c40305500610707009521500c0c0540100c005501e01c1407038404540340c0c8509986401e4840c0c440003400c01c0c0c1c80d0780300318107621203081212410140c5000030006001803146089150050f4001c100300603010303a80c5c0e0121180d0703210141c000c100e4a5038a00b050401012140400ca6000d0700f03081c0490007902d0a08004030000e1600b1141100d50b070300c0c2c200940d490000003035240c515400148038840382540401126842035010746ca000c2120401413001d00e050918510390300724108030440c4001d0315 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 649757787 1250 649756537 649756573
    0xf022809061d0103091a09010e0309060414030a02031e0c030607121d120a12020301031703090708060712050f0424021303060204030b150609010f1e110c03 68
    0x1424000c00c0c80703000d40b002c8190049010f4214400c002e00079007070800a01d0384081007002c0141c03281851000030045400c0000c01907889101c0d10000300d42c02074052005004015442d05070892081c2c00900700d507030844041d40801d0420f03892415a1090b510510821400c511042c092014041c07030407406010036161551014251242e003440c9111039543d144112010402007041c140204007003402221012000040090000d91152000303000248400c01c2c4d0401c1a1807500a5034141e95008d400201c84045810b4645c48580005144c44464450f02c040054103000030300c00c860007150f035035582411000d640d00455007912400791072103046901000030040490b6038000071109884600701200104105902220040c0c020b10300380c0c9500c2e8500c0d0310f00204000d400c0d4010700469100c0e5072010916582c003410024000d16000c0556001101003108014940c821400c050f070b42201418803072000720348094100a9000e0075560b66020034080c04940701513075020816400160030072801002041111251400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 649759037 1250 649757787 649757807
    0x31505010f09180501260a1502220f080303010b1b1603060203181c05090316090c0e060a020d0309150e06040303050c0903102a02010c120b010e090a0f02280906 70
    0x407410410084181e0342841030780440b800f40343d2090341100e0400c0c90811032000c08615205440c2f8620009000080701322011080e241258602d13010642040d281a1007581c040c015102070361880c0c020420041c04c400e96624280c4041c5028480050301ca1034492848071001e05e818050595039444030760724804014201280100d0000c541c0f901503140d000010200385001560290f10020311202c0b88046881e00003a0721020300044d859032100c1c45c1400700700070312000d4468090100016000f0503c03440d03000e030007500510960781c440c40d480b18100d02083c40442c03c03111480e4500340290440018003050561500a40b50041d580b0502945407066020000703564a814804114a091322003801e25409034045801212101c7c8004401c030030525400e6001740200204540c0d0030100303643d040c0348541c544180c441c0304041c03041030310b92032170021200c4104010311400400f0304000f0780d141c4080002c0c034401c60025084d014201c1000043c19050307000d02c00380d61143c90300b0b80c4040115500003040728550000c4801c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 649760287 1250 649759037 649759043
    0x20d15080303072d0507150903021905030d05040602071b0f0512101b030c02030a0903060e0703020a171e070302010f03020c15040210031505010f09180501260a 70
    0x4c0c00721016204800880d0318043c071164691200c2c4480c211001d41c0100080c1030141c4140c1400c0341c900083c0c104030080f55464503007d001a84074485041c0d040a0300c0f255150400d01a908883c100342e00c420000094440440d011a22180c0214502c82000307030707801402001c4424206008007660070520340c1ea454445ca481070510980d03040350141d203111000d002000c504400311f2001d1100207081c4043e40d4040609605000c00a850b005080701054804016034034451180c0d034510345484e245460b400044d001580e170040e018011403d0010050b50380d0099580207254028010100681c0c0701040c03401d004220500e8000003050241e401c10701207000c200c203025240d09003455500f4074900c0004074024004c1624408940c8103c0c13561404a0300b00a901510840c0f085030150b540a5410100b20291920010001c10051410303406000940c01562052940c484619003609110f40c0c4e5110b012040b1080314400c1d000c03580d01c50060140030300604520b2002c44440000c2d200040c2071962060340c4072a040710103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 649761537 1250 649760287 649760297
    0xb07291303050c1005060901230f040b0d0b070f030e07050622031a09010e0c24070b01060f05070b060d080c0604150e010b090f040c031401020d1508030307 68
    0x1040500030b2054640c1c10035980110b8050760500750700c0c1001004107071800352003105d00c4000010f40a070303098810311184a0149610100340e4207d07040c0601100581221503009885d8403410203580c942080300d140441c01f80c8a051003505042001907c0001c0e9040c0c0001050705060b00070540181c0080c2039070840e04184c5106554400c009102c080c8040714203040040010741039400003c0c03081e11b55500d003c0744e903000403010203612400f105508951a0702820161500079200c0044240340940a080c501d041c40892882e04406c01d060140b440c0c0d102060858890980d14018400f0551025500c18180740500340300e4a0452a500ca0807002c4400a103524459090300300c6c40d408204a0303000762622601c80108036400380c101480c10321050661115801141458003441d030b460300405003e001d001650140c14122103440300c0303400c1070b28484004c10507611304125901c0040041d119210428041c0e52400c0016154007a5140070003c0d611244c00054811100040038089001c01004581c5c21032254213103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 649762787 1250 649761537 649761571
    0x3009080c060403080d0e030a0332150103180305070512030c04030b19060b07060b0910060509181003030e15040513090204061d010b0a141c060b0729 65
    0xd170140c2030b003000080107800049001c885850b05a0088414443c00001803013105103120088070b115011aa12070032400e48180209503140c801007840000900185004540611012030170b50030404408802c0300010340014805042c044284020004411a00c00f031900c0c604002d92142142d014500000e090b040040000c901e018030741608441180034114000d1140230f0b5140b5000d40c0d2070304580829100c00f400e10200f90f00514081021511545070103c07000080e82c1080030840780b82c0c1201a003550401641800d6411031540644000d1040306200c07000c19210781507141c01040002c140811901508028480041000381030303040d102500e000382c921402ca03c00c3d0b81141070141c00300a038081e400502c1c0c89000320300800041c26000c1240c08903055490311b641e0b074101c0101c4512510410000081e00c040070300038103250b100000d00d0715400c8003681c905010b8491801c20111111a400310402500c0050724001f0000055403034102040d98901c0e44030390801031200c5040001006090344210f0002c056 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 649764037 1250 649762787 649762807
    0x7030807122414090702121809160219030e04050606190201022205240c010e031b0c0102121b1006140d050c0d3009080c06040308 57
    0x100031000111000c01031959010070441480c001141800346050703040305800e07402c03507038101825400d0017000785900030700b40c2d180c4d4041e000741c00b42c0000a21074840791f405020f0345040c0d41e68203103c602921102d407641c600d80d0341c0c942c0045d103400b80c521035242490b05040c0d200404244c000d001c880d085c540940c0c011400341e503101c001840d5881029054408045d15a50020741701c1e905502074284c10703842600d01021907079103c503103612140e07441c0700b4564401c0d1607507807108800901900c4000d00307004020031fa500300303000c50702403e02f51a54100c000481da400030a540780801c980d00b0002240328041d001030a007074540325000039181c2c650b402a940e822203000410801d0808029009000407629406956a0403c9000042d002d01284e12801c0072040c00c503035201c500380c50010212200580e0040c001c00300c6902c44000d00207050001101aa0144615852a00e40c80c0c0f6180e80c000c018140300807002a1a0100c25001d448035400380c2040c15960b000407900304003501d44000715800d50b60407811142d2070f01c62040d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 649765287 1250 649764037 649764041
    0x2030717130b090a0b0a0b030c060a021b091603050c09030706030b0a08030a1e0201110708090a080303130206030c190206071d0105032409100f05060703080712 70
    0x44420030115910020040e8004034001c00c40511032281c00a5280c985501040c6a5110701c0f0b200003602803e4140301041403144242d110340c4554074068189d440c0007803400300158468005080ca407004da0802e400c00340807100c4403c20070300541401c688180940c2000081201520210002d940500d965000401c0b42140a02c0a488000300020200d8583c00c0d00c0382c07002000740075611005401a5103e880c040340041021081e038012a643da55a0540003402410150012103448121f50a5550340c17600181c8a012000040c070079103002c2d101a90780c404004060042440c050ba0054116400c1032040c0b01c4080c00c140c48040c10150104c0340c164582c2c68460308481103100b44186150011a64181f00c00000d0300422075600c101780300e407148680c040c10251001c0303030011031050761800120100b002481c151144030100f01c0544006003000840e20350340002c9850b01c001540d9952046948800030408009482e050001411042d20a50f0600500d5036000c0c044c2940506076070107000880101000c400226 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 649766537 1250 649765287 649765307
    0x1f0e010309240609020f070308220606050108060a15031a09040308091212061003150602010213090e0a0809030f06010b0d0e0c0112020d0b091f0f0303090306020307 72
    0x1002050b02c000550a00c03041c40d00618840e000700d068203040001a009605209548200d101410350500d044155903007110311500051504c000400502401e800056603103201e081602e104080000c4e0b002d040000240a0f101d00500462040c3c2d1081d9040c0440c915041040c6102d02d420b0401141104000c80f454a00710100400d060704540ca40d4104014541d10414080c058190f41060314520b0b42e001a42825521900200402408084001c5051410254062803140215240001d007445401200781110a0390360b0044d070060f900414962240d800002902c401402040340401c4009001048280c603107042803000381801c040822501040c1e03c043c40200d00344542d16050721502c2d0b0710b602030000e180d00800c5074221f24518060922213100c03c000780e20700c00c0c03010503100c00b0070156001801001a504c081280c0380c0e0291500816112038692543c2d003400340c0303110014084030120649140b042c0c20f000ea0701040750182103080410200b500407641c14256604a06c0142e40c07680c58101c02d48900b060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 649767787 1250 649766537 649766543
    0x9071e0c08070507030b0606031b1b01230702070f090e2509110f03060f01020f0a03020a05060a0522020a0f0b070204050a021c020313051c0e1f0e010309 67
    0x10004070501005008504d18013941d224030340001c0180c890b1014005640402c640381d04503076100384030011a2500090140030460b1044031082c00c18031751441c00c6829a00c41444162203410100051480340c0320901540364000c0b15880200f060038900200c410f5207011038444c803400ca40d46e6039074880740c03903005014038404035400030b80108142041d0703800bc5c8a1310501d0703c90b0101003840c00d0344d200c0490359640201c0316845498140f160840e2201402c000d1040c140500300c3d4150720510610714803840e424445c024100b070281d00600840b0303029062050901400400c0c604030740d1314000800c5400000c00c200043d00350100ea514121334080761010a24961882c0c0025045a0380d0000004041d030303485e0002c0c04014402d803011f01054882100070b13016030185207580b05800805848003400d160302c0341e001e164005c802c0c0d805855203a0003900c0e06800c1400c0d0200d0146035015030f0000144064004100f20000c000c240d0f007c0e03200403502000c074800340b540004200104030240b1102c0781750307038032a8000c1145160 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 649769037 1250 649767787 649767803
    0x20607120908010e010b0607020405130b0a060617070212030417030c091915030209150301090212010602120f181221070803011509090f090c0509071e0c 67
    0x40310580280145101e846429a00d41c202101d2191103041130060b903e600c2c4010744940d04186056003040b0140000920b194201c0400380060404542c0541d00d0074014861035500240d001e08103030005100c24101301d0881c221588080900400b41e0b070004d20200c841320b8524055480f40c56900c0c000b00c0b00032a401580390005004401e21800d449900000e241c064000c440761283c2c171034010540c007290b81e1148900030240301c5440d10b900949000b500146200b80c0c0c020001500240c624000340300306c0e00280c10040369281d001c110070a8819103002250302500c2180010070701c0804400c1440c03154441c2d4040581224070220303240540072207261900c04050001010340709281d55002056548000300c0b0004241003e0000e030829101540b4401c4902c9a0f412050061440e800d102c9003120030310707032001d0f0070782002024000002d080c1c07507a10404903181241030010450f514039090413404458142c000e603116014400a00c40c8007a044a5800300c1150302c07a540245090a400054030420141107014000c20 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 649770287 1250 649769037 649769063
    0x70905091c17010e27010f090609031b0f15020c0f0a03032702040c141308060c0f161113020c01150f03030804020a0f030b040b06090c04050904020607 66
    0x20b0308072501080c0c1c0084510510303081e81c1d03100c104040210080c1d44400e20b052800324240203040701c50a00050900740383d400400c10403252848082141d030720b000240c49c0660703520308003801c040e48203052400f1650400c2050f00e0580c0551682841a00221402000420007090a44001701641c0544100f411030400b0380c1c0041c600103c140d5103070f00d00e40c1c90850010349070581240700200319000d0f580c02008041c640c04140c140590a0100070800104110180900a1111410007046078010000e2058801079000b40ca4580341096281040203464042810b10600140108646000c00da540403488035403844039003202800c04406440c0784440c081d8105400b07140c0401c0c503c541c1d0f001460416101c0000708141c03007035443d01e485061258007a41c3c801e40781c90103040000c24401d8200b10741041c0028a1240c807155141001d8101e80555881107516540010400c401e200700410387d154000801c0d039404405180400c03007000c0310320079802610302c20002031001c1015074459100740c800c42640f14800d00410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 649771537 1250 649770287 649770343
    0x6030f121813110705010c0f0221120720030a0c0303050a11030901021809010501080c0f0d150608090d1b05010605030a050319050c060a0b03010e0115090b0105030907090509 76
    0x164003240c8162415800e00d00141007d81c4103104004038403180f0f41c00f40c030600c0040d0500c0003104042000d0600c0004c414031074a680d280f50008007a0103280d143e1140308144045a810140306880c1c0c1c1200b092942003448100489a08140d02944103035040c5800100350742e90b9000d0304000c0c0076810300b2410304217000c400c103d003030403055004160b01c4011440300354020348030104000c00e032103090050a00103a44100411802c0301180e001d06400032a0300181401c010044103208211107450728003100c4801c40e90b41c10480c0642100c0d0791034104982e00d02511540300e24020141c500d00310342c040070f141185050300740024800c0c01c1d07003c28040c04008058485c0c10b031450a115030780360088030a9070000981c0034480480d443c0610216482c41c07550390094421981c5050340000105010060f140d0075540b214042280700c0028440c2243c910782224542c8000d508007041d00b011149245810b41c10b228082080c00a0740344009070244c100c455114000c180c51340c172072080c4c90510915000d410040d40900c1030890300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 649772787 1250 649771537 649771571
    0x6060121050412030e4b0d0f02011b140717030603070e0103050a12091d09060109020c0712020103020f03101838061206030f121813 58
    0x2c0c403120b41d42800740210381ca45c0c00c0d40b204980c1c0c4558880e01154421074941070b00d02c0d0000c1d98107811b1150744d0b00f80d204450462044c6110b01c204040000d030000c0100105458010b030041c2c05884861000300504c0204200c2c0b41c0311100340200c854180104c410303103a11418101c500300c40456038048401046a400450501100c0d00261200c5200f801042808180d0034140046c0c41d048a070444020500340d042c54903803007d0011401884820012903403000704040b1f280c0c0c4042c0c0302d441e100c125009031038a013039080356040c00d0068202c2c1e03c080e4010010084030340030010b144025250041c0e4110540f1b81c1c1440182c000303107c1c1003400c50102e48040300300300500c01003420b16030032600d20780d048802007026001c83e10102c0f4504001c5403907460162214900d140b03201144c81500700c4100c010b50b111550b841c030000720581c100440070400251108100902030406004518003440a0070061500341c0c211103403241c0d18040d040070009401c0704514403020b107a445c06151310b09c0b40c290103001c0010307240103460050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 649774037 1250 649772787 649772813
    0x19090b030106140d03030203040602040f17010e010c14030c0c071e0b0a140a030e06090a021c03091703130e040b0f010e19020d0c02071d0405060601210504 68
    0x1109518102c800110641454400d08141c40300404d04400c2d04401d41e4190025040680300341d402079070a000100d1000032100b100c00141c491a61019411481f010742d45007074403050420549207904000d5102003447d046490b01039001300840d0190f440759100e88030038120f80102c2d481c002c4284907100d0006496620404144825a5803001c0c0162003a01d600d00440136102c0c02203490001020705040c5103c2c5c020b00005070401260a00c0e0104002c2c24108e10039207088025200b440c45c40e0045c105160461074280c00e02d0b2034204002103901d400f00296200507044443c18880c0c0b0744c00113951038503990a800240100c403c8800030f0380c11760348244d843d17800d0702452030790441c2c0c00c0300e0111120740070400c5580c98071803d0341200c0405a56150907503e95544c030203080b03400016202401c1d000e000746c10f800402c41c0031754615203800380c3c0201102860b01d0015554a21840042c01d000a1504d00344030110f40c01242076a441a420f081100a10203148003426200d690721242c0706c80d0707901d0f22041c40308003e007442242d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 649775287 1250 649774037 649774039
    0x10120e060c03041208010506090d0f2406050108010302030d0305130c0303080403110c0d062004090b04050f04030c06111c05010f0b0913110f0a091809050604030e19090b 74
    0x80da00988030318090751741090a00859500c00c0c0b042c803207800c152602d880c8003113084d0310495102c0d041c010940e071400346803452402e44e816408030b074a603002e11b406654071801c0024242445c094215500d90f03004203480d5075582515104050b100d10001f010610302c5100c60311003541c03081344115901d541c2e090060001605481c01c49c0050b45400c08090030320400a0740900001c0c0013804518050703290750700d100003044e0503000108a6068070450800c060050b102400060030408400b03d1803055034400c100480d04000e18090401d51000b040c040420b81c890145a600c80d40715400042040b0803168051391070040c950041580d22050640d000b40e048540c110f98105c604120804a030f090720b441644503c0d018688155421507107504406008081703c1c0c2081800040244605241c44044030010ba400d5020703807a07d002160f500781040009a41113800829402641c18003000300c00384554507075442d0702e409040074040185441d4000711a03680e2581c0a00c14021449540d500c0f103030b4a9408001034101340d6180303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 649776537 1250 649775287 649775303
    0x304060206040b070903050606010c1419120906081803090d081201061121210121082b05070e1504030804050105160206210907030210120e060c0304 65
    0x800c4c6440d00034882001580d40c0680502201d42d6090011100420b104a05070b420004d0714504558010090086c0100560514411262144a800d0801100d48502d80c0c10082103c01081006003507072240c0c056030442c140031210000941144a258907601034a2a207660080240344100304101003040108038400307204a03007000681e0385250603620b02043c84080103842c1c1250b6074518007400d0070381c4084140d03241e03801003d00300340c030403415101c00ca01d601c01101c070610340ca5401404a000c500040e00c260412002c19505500d0720307070390f8090140c080d8551840d0018000303140e410744400c41e40c285009a003011102000540360580c00245048001000f0701d00800e80100486402c01040003190290f0360064440c0e40f5292404004490661003140d64105024991601d80700590300e400c02854600820800c44039004045140c80f0180701c000b03400740c0e030164021141000140c41d504100c40c1100803d0402190224260a40d03002412542030301250a0003050200421411010302450042e0300903071035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 649777787 1250 649776537 649776541
    0x602071707060c021216061503061508070503120d0930050f090d0512120114041505011809020d0903081303081306020c30040e0402040e0c030304060206040b 69
    0x100b640c45d0000909120400c400802c001076107040340c0030314820594031417140001c03640801343c02e440c00d403030403a04104d5480d922a01d5004a4800c1e00c1544000381007118054208285000002640c41c074080d140e190f4421000f00b00c07100240003650145030301c603070050030b0310b10709000e071142c00c140c000313886141040d042144601d00c0d4171452041090701c0ca1855810840e9262260280410842e003070b0001c0d044415100da94408002c00504a01401000307a81942c007142175410405094814007021b980136010b1864880c2d6001000c19240d50041200c400b82004c0f0495202d44007841d030404219000303403180c54000102594820205e81c018444030b8000e5031a20199290010a54550805074401400084002e00031600d1641c50100c901c0355140b2950f00145485031030350310282020a84200075240340801c0c80302c054130200060724a2010000450390b64030740750510134040440b01c0701400180c0140d0f036644c3d10140703408041201019401e801021070341c40d55a1100001d50b983d0781100c1c102c51036951400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 649779037 1250 649777787 649777811
    0x3020c0103180c051201060b07030c0c060e091f0b040806060a1238041202070603020418020c0f0304030c0f1a041403210d20070f060207170706 63
    0x5119a0300c0340d0f101001c0c140561410040002444c6201e041c41401e55840c01c000a42c401c4100007001c1c1c82d4070a840304800300a40c0d040c5844060f215a000605000019044040710764403510a80d6200e280c0140000310f0b00c4085888003c0c1d0b854541050b210300c20f0015000ca142d8a000079031611500d411100501e0070754844800801201440d00d0003088041c0200d0140b00405040c008841e140c514000d40244609081c41000240c41c002d490a560b80200b044941d0207480c1d041c403080c0040c2030681400e41c5090314082030b24000003800110528840e50210349114100030521440c0b500003803400403291900c0d22400d200011100c0341c801c0d60001040610006400c2d035a01c6036134907942144440c1542040e160080c2d2203015490f8802069150254880b403c8240709800c444880c000904600c054a83c2154050a011038010314039000c40c030030f0741d80303802e00020580c6001c48040d01e600080078412400203107401d030080d01035201c004101c1480f0320802000308000030003426095005600078888403060708 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 649780287 1250 649779037 649779071
    0x80705040c0c0308090a0f110103050601020a0309060f05070c030809031c092304060303080601030b0102010212070f12053c01030212030c0106140301150617041e03020c0103 76
    0x800c0d1101145540b5800e4010138002c21460381d008084e0800c0e05d4480da8259144040209000d10450300c0c514071000507030103035a052040d6548580f082c0001d003241050341c0c401a080820ba23200d0b050401100c040741034440e912800542e918941e1014a44826a40b40c1c5014107680d0000e5603120300910800c5000034910b03440144000075008a502c82e81c0c02d081c00c00d90900d4400404424100c442040c9941c0c960581c0ca0714454a8000d5019540311600e9080c14000101a01c1040106a046a0042c07006001c0480c0d007000d8250043e2080c11b01711498a03213081e0a44010040c41820700d80146410b0410140310301c0b01c5403150621400740a1264070000342e0900a20302c0004000003d00441c40c01c0040c0300605003080d5160491101404807424181d0f54000982502d040390040e0081c608219010300c400e09090003202508140102c400c0300c41810401e00402d0716280e495001481b85d4540c006c0f506105200b03884642c0d100e1010700c2c00d410300341d032414046e5441c0b003001d0003280000e243c50413600168203a5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 649781537 1250 649780287 649780301
    0x309030c0d1e080c09100e13020405090c1803032b060b120a06051c06060e040206030703050a0207020a0b070b07090f06050d24091a09060108041b080708070504 70
    0x14010a035021180300b034048411080042c14502042010002a1499a0340c41d100442d500510359403501007039101000e0024244000303c88002560052000740300035a10034030800e0b4008242e040564441080a9010031480b0540300c0268240c040001c01c5604690a00f400e50040482030021400146142e06410102c0745240f140e004c40341010300c4440072102c0c3d00e00c80c0700d812039001d070008030f4225107032030008040b58480224041c8280040701003030200803050148100525151962101900d410f8001c20100d00c00107244a08141d81c0d18002407680300c1035415120042d401502d03100059480760f00401890740720340e105544402e10007002a00661164071020700340d401420b200c2181d03d1030b210082e200303078004807202d12303045490b10f08449158003c070914505c1c3c107201c68401d1940c03d207800004400c8a03941d41d81c600d400284180d82114a407245803d240c2c000c00c1c02c1c600500b165569042070900c80580b01385150044c1c01c2c58000040301e410018949050b1207410050b14030f8555031b00100700c115004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 649782787 1250 649781537 649781567
    0x40c0906050108040f0b06130c0504050109150819110f03040308060d0309150c120806190b0f07060b0907051b06060f0411160606031a190b150309030c0d 67
    0x91719a9141c0054010010b850700044050801c000c80d9900405035000d990308801c0d041c00240000c83d040281d5a84a00007000500035056101c03028152030f24000c0846000600c511800160440184150021984050901c05145540c40d8a4007402c0703104002c07136401520181e00003000c2001049081c90110141100650f0584403046c01c549000e1b07000422140700d070382683c28000e84c400060b0101c0c207000314000580702c09076030744041c5d4a0400704010f006140f01e40f0700302d4181d212401c14001c290425046403203082c01003040315240d0039103207095806040b4148500e500610f1200910100d503070401d014101034122a1341000c80380c01c3c0100c0c03082d66401c040760080d41c4051011842c49460500381d010204100040410a140031305e9401d0400b130307100c195001100c120740e6a8404006000460850a038400700f0f45040306014140b00110348040a4420408501d80e540c03251000f045948080008201400b600862074580c68842065a01c3e608101d02c0a003003406424100025284958584801d041c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 649784037 1250 649782787 649782803
    0x6121d0a021003020904021305120604080406030f0e0d021506190b07030504050316030b0c030601050703030b1309060501030c05100206180a0b09010e0c040b03121e03040c090605010804 81
    0x41d0200320480145a071520306140c1d08010445140d02c4600051045492610144100714945018006a2000d04420780d000e900240140030000d960a811182150914540071400550450b0407900034000011409182e01c0f81d03800760310540ea000f18003002c0c04460b14800c1071003aa500070904c00c1c080e8174000300c0202e078050100e050008950513000b070040d6034001d10740103081c80e80352000300e0300c0c048a0b10b24050030360000c030100f001000300440d4600e03400140070074020f08508200780083c001d8064100000c0a00d501c400743d8401c2c42e00d0300c94000200941c9400203120302503050030500c00030002070206072155040d01c41c001c601405c20700c000b50b155150070350041006a0b00c000c000c0c0d20203008500f07141064003400c8010300c045141030300914000c4100500029580c00390045a034a05030802e04c003680250306220f4034070f40c0ca50b400300700c48094440000b1950b40d0703003000d0000c84418100d50420784407060340c040244020701c580755245505607552041c00b00320450321040191440001101e0050a0031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 649785287 1250 649784037 649784053
    0x1009122c0118030c0605030f0603070f0608041406070909060906030b1314010501090c0305060a08030301121103030c0a1511090f030a0b0a0b03010b01210e1606121d 72
    0x75200e4503a0360102446884907414164903507560840d03807401035000200081002c8240302583c00e1100c141c9801043c228024680d1a141200a200d040f509100e00b100340010600080c00b4404114000280c803d0f07280203958883c902110082d04101c41c500038494414640840071410350401c0c031482e0f040d03030340041d07102d03115540d01e0050801910100d141101c4c03d15809040410301502401004e010301102c00d030106070403070710650013412104001d10b49880745040d60b9003002000004001c0320b041d50a2060b072014402020700f40468180034040038290588000038240003510030100302c16a00358401c0c0707110845001c503521140d054403429400b080c454801005000010f149c08001c24003224005003d40c4c9052400303444030f100031102241c815001c40c2d200c51401445107404c1c0704e43c41c28280300b42001003c890510300707000c104180d804a0703c2508c0350b58100364004074804000c030f034010350030204060843c103895031402071420b00f000601d04011400c05032080c401082da20078401016441c40d000700707003039 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 649786537 1250 649785287 649785289
    0x807080106031106030c070b04061a1801030308090c09010806071e0203161509031112210406090203071502070b0702010509040c1b0f050f031213051009122c 69
    0x180c3c406400c4000c1e1b04004c00c00b01c00003e60001d145840381d805000000f41003090f2807028a95414980401c0e480749055404d001a85a03801559505480d014a800882076030781d0403045140840304510342e980310300a58000100c02c1341c00600280f14248a65a5081041101c00c44401c2c0d81813055517080981c109001c00108224203c200754480ca0042e60703864000841c98103503c0403540792440a40c0080c00080040b840c20308100080c88100e440380214903d0141010041468298906103c0080b0301d4070002040601549804c00e03091203030011301303a0b2540303940c0384044410f0030203501a03040540940c40340050040780d14003e0ba007240d41c044e150580780188440800c8020302c109140c00c1c0030310403541a52540038141810030000c040c412818082919a281026482e04062001c2c0c084568410010700401c4043c980000b41c10041c0010066299902480c2081c1025074102c2030411242c60488000c0c188404803c0c20420840962144900514849071003110130124617001d01100c0585100106d10b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 649787787 1250 649786537 649786549
    0x9111002032701050d1404061d0a03050309100608100506030a020108070f030618020c10060b0702090907081b010e090103410303040c0b0414040e1606030608070801060311 75
    0x192500500d046840c5ca558072000b0b0007102e03071104000840600307200801042003080d22450a810041242501559440c02c250340c1d6a520003200080c100314020011401e05003003000f0700910000e0b401c40c06d1041e25142d5072040da54003034443b85070590760b040c040441e046060200e01c0d1100d150301a034031090300f6590000700340d8511510040a004040c0c0d1a4000030740110307081e46240581203c10809030381c1e1003510201d036182c200b500214020305481d0000c200303e0003d100c0111200998141d82c1607010741e4440e408075040c8906a4400c400d5030007201c82c802003441c200400402510400d0303e8072150784101d00c052101c0c01909000007031100c0a8040e140603040540242004946102c552740014040a010600c0c000380d1250742d402901d074408028001003006240550004d0281894803504091510424041106420b195107024a80d02c0c0c0b0b0060552a0a0111046800085040d0101c642e50b413040100200014440c50416000c0c0040100703c2041c180141da0480e500054042d85070004441000a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 649789037 1250 649787787 649787857
    0xc050706090807061a10020601080c0d0201230415030902130513020d120818030d0c031d07061101232214070617040b07050d0911100203 60
    0xaa03042e800e20290000482900034012100b980d038124002c16800740050203100c84258000c1019500300c02c006001c25100024001c5180d0002c03120181000074900042c0d810440103040401d0308034404192185590544001300102c0f02403024903040d45101181c201d0032034a0308040254001c1003c8490740000029410064000e42950207090340b5401540c000303214481141d0045aa01d10042c010024040d08002400d610203c1c828407014000c1aa000349500e81c0301317040c0511621513403012004800c520036480740e1098103c5007082e15268000c0b4002540c2d415191068500169400141c06d840c50418000c0280700c0a161010201d981070030407000f40c00c03541c001e000310002c81030035a00d403031407180300443c1c2d0100c4c0380a0303040e000200502d20441e900b402c03a160000c00c107021a05000c80d09200c000d055242e44203402c048000001d496003803040311544a19144412541d05201d1004c0602640605034002c0440840700c070820800000400d0381c0744e0141012213030303500342031034403241412108003030700c0c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 649790287 1250 649789037 649789043
    0x212070807110a150206150a0509010b0d0209060d0f05160c061d0319022b0810050a092c2e0504030f18030c090903090308030403020a150c05070609 65
    0x2031202a11900c142d200811600413940041c0d000b0020f000d00c0b4610000c81203607400701a25038541e04c50138480490054881803162406090b00000c0c1c0c4400703400c166050300c1600030001c00c3e4079615900034200c50050304030380710100300403450700c4041074901c030070480100d00980e01600e0301d43c03150b50300351943c600a01901a2854819648401c0a51030b0780c3c0a00c000c05d8100242407080041c3c4994140084ca400700348008008040020307225169205800c1030300080d2000c2624124040b80d40b90b80c054490a04150b0000d508040d9a0601140c6107000d5040312140108202504000c407180c0c103001e00484101644a000da6000701d6041c99600e02e003907455881d900d401030920b02007000ca020b0780d6011990f04403819400510034040c010700c00c690109074002c0350340301d02c00c468200d58110b81315413004403031520545110325a20f1909508240c0a0032880b0025a04901c0c1c1c1602d13442c05044c040d4480400001c00c50b0142c902c5680c603141018144504440401107a40f03032410702d4000d0380c42400500c0380903025 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 649791537 1250 649790287 649790299
    0x708071206080709090b090303070518030c1f02010b090105100c050a08030c0d06090b0f011803061410050a0e0f06010e031b041505150f040b03010b0406021207080711 73
    0x225090504000200003085602e0000500f201740d0b080000d000c42001d00704da80c02d90000c10a000078541d0000580300c04038006825003180008640009141c1b808012250723412410090780c5490443c444641c00114591607002448100b040808101041d5800d00409511030030240240040c58070848000000f607100710704aa004030a03e480d1050250812940c0c288000f00002f1815200c6d0914041d00f0300a014681061281442260001c2d10601c00c4820790741c100f084961030104a040580440070056130810400c01c41240507000c12400c9450407544031a101099500c0000d44d8140b104003d42100ca0605082c10591940110149908000b17803002c2d04225100600207050b981c14440e500c2c5144050203024042003d11003400241c4040041640c0141c00f5814200116102c218100340590180c110140da5170004080c240072602894028540b2950b01000100c0da1000c8000113000b960b4a82d0212161b0a071580034818640c4035000e0001c150000602110000504d82040380d4002c25000300f403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 649792787 1250 649791537 649791539
    0x20a120c181401080d1706061b1e01021207090305030304060b0103060306140f07141222030c030206010e040c06050705150a0f050609060a0e10150804030210050708071206 75
    0xb0300c40070750390a030051880c42e00400d14903c1d440341c2245101030601caa070601d000c0c49190100001e04a4020404903002989560400a02840c4240000e80010055041c103030402c07140800024000e411051001e040044460302241684d401a40d40340708481d4068011840c5503201e950740009014603040040c107040e01c984000c00015142e00922032040200c03030780a4014030b00122030410b0b00101610344c1c824071070345d21440c54805405e50300329002c40b00f1580c3d884840b502c8420120148503032a450000b00008141e81c00020036038440d0a820019020707500310b90490342c9441c2d45000407102690024204401c400003002030a008001405001d401001500e48265807d026039928803006c5851100b0203640c3c0203002301c554464840c4641118007a203041125243c00800700710314803400d0184004202401000441c0e00c5000c400e220003030158a0072406103101d4407840907040e80b80a9030110058041d40e505040d4818440c802c1c0c43c46000c140d901e844650320780c07100c113641c10408511480c54a41e200c00c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 649794037 1250 649792787 649792811
    0x3060e060a0b270a12051c09060e010c062307180303030c02030c0610081e03040b070f0c08010c031a09041118090d0e060309060103020f120613020a120c18 68
    0x114510041000408150a17181145481410300c0d081c3c0400c40554032002441c03d03000c681c007109070000d0790401d0038985019040440142c40540010800030138190404108400b801400024014240344495042d43c0c25200c02c0300a9800e035404841080d40305543c0841000864400e4000c204890840d0050b24503044805c142c490074160100d4840078211507401e400c103c203010410010540d12104ae02034041025183d800d143c41b0311840c801c4400c03542e408512103003480801c40c80000429440b506502240d591000c0d601e002e03144c3d02d10001d010034502500e1a038208404140384252160003170004001c0d5403540d840010f00c00c841c0300c041d604103400d07484d40c80701940ca200c4814050600c110081101d000c80d050020070031000045540e000720002d1042c008407000001d981070540358116900d0451084410229000003080c845c2c0d00310350300c140c000b88100e00e0300009180d083c5034001d550400340c2d1600e41c10414551410880c000b061381890700020402c000300000c00f030400048046001c03c1d6090094 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 649795287 1250 649794037 649794049
    0x2041407090311010e0604092a0806040b0103090f030c14070e0103051606021002090105070c0303030c18060909110d140906070906050714160603060e060a0b27 70
    0x98022020030000e031014000d020380d02c3c5408007199424078011508603480c40c00300c0e80a0245100301c0101c20344070481d80240488951082ca0101c070250500d500c01818130b4002001c0b00802e039400ca00aa1038003060340d0541d4482d01a4145880c1c00244004c0503100c950381c210349003203821409607401c1c0c044020440c015a000c0c0002d80c0102000c40c000525941142000381c106040d00515030814200311000b00429600800d031415668101c060045e190300441c0c0c0162628401c0001c010301d070714581c80303010040642592089110704450340d0344a48109000361408180036260043d030001c10709407201040003520725041040c42c6a40500446d0400050043c48400d0726a41c0444a86090350340d0100030202904109599004415191203c0e005152120282403842100405055074007600703a10000800c080226550601003508900c10f095540c0030002c0052160b0702900a8441c110401308180d460015440b200f82c0e880040410b01d0030390840040c0090000c5441c0c8842280140121100303036690321 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 649796537 1250 649795287 649795291
    0x501020d05090d030e211b0f0d05071d16030c120b041104030602190807141b0f0102030901060909080901200303150f010c1104020f0f070501020406080c0f030a0207020414 75
    0x1216108540300c10203043c242850441f980b9210102c40a40400070a9600c3e04019203001c04181c070748095500c4c09040c61400c040140e0000c081d905c444010301190010050641c5205004100300300010030070040044064462902c018030026001c103203501802006030f80000e804203c01000020302011014290b19590442d5006541196001c90303030200d1510014000d00b180c050928045810345000d61010b441c404803480b40e014080d102090004040c464400d200c4000458070045441c52400ca040040c082e5004480c208169420700b400080c070012940520b548444e4003190a608044d294001107688507912000c140000303c40410303100e060301007440114004c030301c5000400380c030815003000d011111040520f135504100d21802e4000110700031500300c091100c2c0440380965500041030426406000380b19010400c4000000c0342010020154018005c8075201e0300d448223140d80385001440c8030700034a0910100158200001a0f0298041d8018109584010310005d041041594402d8140c041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 649797787 1250 649796537 649796569
    0x216050114070201140c070f0602160c0311180f0c070f0302010b0a1d06090702010213120512030c07110612041109090d020a0f050f030a0f090501020d05090d030e 71
    0x40d0034103214100d6428010501240c016170101d0401d404c080d054070f201c501c10901e0140510f220001400c2c2040100d03012114104000000c00d0300e282c4403410607103680c003031a11040b1131f04004104080580c0c28890b000e400e015010010038030059944a01130b4482404c0100074606540303040004000080081c101d00d1142c40c000d90001400010702c805009905081d80c2000302d12a01c403880e40120012103042c9680d0007402901c4510300e580700c00c10f044e406801040c1401c8243e48203107001040d004d403400b210340d8501d405a0120744444040880d070103581c2c030098448110b9a001048000041005000c10140b81c00c1c000d0002490180706003551a1002c0b03064a040b102c440c442c00050b0018038100d54481d03007010328640a0031024480807000380d9500e84030100100080c0c0811034000030b00c07006004c6040d039281d90030306581d07030ba0a0b51080100368904504c1d008012420104000c0390381d510001d8004120f94039600c0e12454020700c0d108101d0314480c0150106c0030890342e52410142612002200350007020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 649799037 1250 649797787 649797821
    0xd050304360213030803240906090408160c1503150f051e0d030503060a0602150403031d07080706170c0d0c12020703020607080708070801060302160501 67
    0x41411088410740819580d00d0465000d512001405034034510002418615a6140103a030381d210a80000700700601c50f0300c0038221150100411000282401a102100c3c903008a05181521070300c2c10030481400c02d0701c1c42c5410100d00800a030004ac08000208540306000154000455003941d5421102110b5041405a2250100a005056050b0007003100800d0300d2200c55402c1410720850014020302845810301c1415000030484039003080c1450201d160201402c000001c00e007900700542280c2c0181c82960140b4400034002454a2011031240c2c24081c85059600990325140c404801500308030011307000c0c803050221704071090102003108030014a21034014000c2540380c01c40180c0740c030103440220150000401d0400c2259400d1b001190f8651764803000004600400010803034100101c02910307501c2c2417002900400f070540020f1420300c5076042e65124001c41d640d81008a03141c0d10b068500a000c6000d9000500010307000342c0107000c01c2d50342c5400110301e52010742c4405081d00c107101036501e14a1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 649800287 1250 649799037 649799039
    0x11011107091a010c030206150402090d06050601180605034006050c0406020307060c0e130f0f090f060e121605010606050a0c0b070903080c03030709170c01080907050d050304 76
    0x180316180b64280c0d02009003041c690b03002c202c0e1806900d82c000101885128501030b001481603a5869050325454003020700050f420540034585000184020b40d15180400c26800090446544c00c0d401a006e0324181e0765454195207506103280349801c80014090b186030b40d19111543c1040700d03140c100840c00c903442e130b04104c94411410503e040f030f03001030800c0340d0300349080005101d0301d034000049034601039010000166481d6550401c8664100840340250721040010000d044510382d40c1090600140e10242004105034408041040b1280b03000008c1011207148810030201344181c0c4a00c1c03a00c040001540c4080300740ba80c0c191441c0c4d10046600040d0000c550013201803003024841c1030040c00a0b0300340346240c01c10f03000010f420b2040718078004044c01103a20000749000e00c100d804000940d0300c241966100c0250000b140d86a420880344c0c44d0000701921400140d03008a0a030b0318022090540140c0954245600110741c41c840040000c602c1e0711070f00000203207688407007140264050041010315203507 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 649801537 1250 649800287 649800311
    0x50303070806060c15040c0e0c1b160504021c05180f1b06030c04091515030b0109150201020c060f041a0405030d0f0b190503010c080f041101110709 65
    0x1508000d000680100c00c14800e036020303080e0000e81c210500c05c0490380125180d03290324110300004c10a410240d1219a40000d219185680074042c1408807250744000100088054949541d036400e1034000702012000c0908200c1418580c2c006c01d4490300c0f8101100c041e080151505003603810a6503c0f8041c0458164041c0640e5000e000d4001070313160190280000303269808010b0303c07120708042d100348500c40000102d00100d1102040310300810f5060350910900c48810040e2045c0e8481d4411070082c2036045204081c800d00c80c0c031460119000584820800d141820100e12032103000210380300541d90308000c2c0e1205440c04029851081500c00020201071400303142111b0030555030100c00341499208000e000000c0d4001c000d54081c20080d210000e100308078001070f03c01410300c102d48203405c11800ca20140715242071850720419030b4010344c02400100a08802250f80352000c83e9042d012404000118002850940408100405c149800c0140c0c4100700340d050b0905c001c5074800008160356111007408 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 649802787 1250 649801537 649801547
    0x2101b1107080604020609060c011e0507050901020a110103090c030f12021908030714030a0906050603030a050409021e0409090201090e040f03081f0b222111060705030307 75
    0x24100e9580a0403415150045040d41c940e00900028440c04000c28440007a48a10050b22080034184009201c2500300c80030121002c100030b2080c81c819400d00c00000c120341e005e03504803012120103038003c01e140403007a2504180c62600d07006441c100342d03e441507400800c049002d0100954001d080140d01500c0c07514001082082d44a079090541d00215902c0080480d00074981078103540003541d0f140e0f03e0341d41f0001120311016005e19444910800320901040c000c00354041180d0034482c080400064480b94205a92402540070303180018404100c140304c2e20b400742d0042c00d45500f075a490030104d6008984280b9140d00190031030729503a80c0e00d840e001d0079980e00000d1000203080030380c3c040c0c1042c102500c441e080d2500c6040d0140c24405003d001c6851140c00303010800a0001a2503991071050300d90341d8a980710b92208003503640c0c010440300302140140a212030581201c403660344820800182c824a0071460a00300c1040d07440903209058145262070f20401440304078403a402459484c034181e000601 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 649804037 1250 649802787 649802807
    0x60305061008010308030411030a021e04060801060f030222021c0f02030c030105100e090c070302060114061209120706050412140d0902040906020c0607021207050c04050702101b 78
    0x10820400b004101040d254006c59800c1508044900401c1c58880c001c00d1400d0140c41000b5045044807201c1e100001d45928030030f06601045030b0038001c4648e84c0920343c0c01d843d6940252480d0000e891010001442c040c1d94120941800c191088c55452200314a54100e0f0040c01200c3d0380d064042000b6a180c021520400c03900b038002140860a600f04581c642c0c03240d0005000b11800b80444198075070302c00d40035202000e044039004080060b40d10304030a03d1001c54100313960881c0903224580000c50301d4581c034598448107403000f9001905000e0211560356041c00042c08600c030034026200710b282400003800003400340d1030040c007021401d130078149003103800000844090000c201005004238040c0380860100d42580032030440210701080b0f180001001004e40641c010b0480344002070a01c0101d1010030300c10710502c800e809070703521402c2911440c00e80d4400d1850090443d0040e100f41c070503d181c1a03101c0d5800c04024412030b040621022030f80c01c1140c42d40f411005002c0e050208400c0380700d6000304025 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 649805287 1250 649804037 649804069
    0x1a0702061e04030c0203011e0b030c010206091002093f0307030c0b06150c0114072105181005180c06070807020d020901061218050a0f0c0f06030506 65
    0x105074038580c1d1418100002000d0802010804420000c9096540c02d400c290010304054000754082e056424682009280c442c02190090107031204041c45503001041803441349418001401868072840e0601c2c00075071001700e24a5008200203140c01020b420100c4d00005c0f00a407022046c0200c680c0c030011210711100600d007244a61041080038000f0354040d0078942e040e40d100c170003580703141c941c1c2d000500c0d41c03401e1600602c0030b103a0100c1c500c01d4002c01500309007460400e5840f80204d6440d0740b0000c0f00d09520a03201e169801185101288500c84150b000c1a4011406514061428903014805052150040b0421b521545400a0110180c04900300247c2d40d00741c5001001c8110a28000c83d0301409800340182c0308800100700740d01951918074550060a17401004907846684a0340060b041546110701390f0142441c0000c102080d201d000303444100d940e00f100081442134916650001c06242d8007100f150012110880044c40f6407800c20320a010b00a1074a01041c5450001c0a0100d0301606c04105 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 649806537 1250 649805287 649805311
    0xd021804060819050705150409150308070f020f120115150f1805120a052a040b13020d09051005071403090f070b0a081e060103181a070206 61
    0x10405440002240740724262084841d1003c6003140c1410350034004654082c0e5040001603900c41294140e003002081900e41806003084214580f00c41010700c9003c40c0030080c500c52040103001d0100701000002040c040c401000070240c41d401c8004200c65450f0a0040d007002d0391510a55001c0820080c0790750042c00940004050083e011900104680c1d105040c1505002004c2002d0f44000c000d510f541c4003601c000b401101a85100031790f141d60b00d50030702e5015925030103944626890f0509040009442207190517204008d440307140c08001c020001c0e8080740c2d900608403100030400a4107800604030411801d0310000300702d01c090820300c0c1064645181028050310b07182c2086200358201c0414040c08184402c0d40b6181e42d00c00e500e0510381030111190f1401c51190710300028004c200240107100203a01940d032400700b07440d000e015884c005500480704071000600e1001503031551003079003e6000d01940160040780c90340144c85090300120b0850b000001c40d0f2101040001068040101640128103850a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 649807787 1250 649806537 649806539
    0xe070c0203031c0b03030a020f0f0703050d050313060509030a030c020309030703060902120708010b0a08010b0a061826010b0604060e0907050403061401060e0a06020307140f030d02180406 82
    0x42c0d240e1250384441e190820b40704030140614501ca5210030486031014003240c3d40d80ca64440f01940d10244020030b0b0b60701e8440c4000081c100e49010030243c00700c0e58030000501c1c007a80071171803e648a4200070104504007101c9451440480d00a0040c00e000d0442e041c0519582e590141d0001e05842031451014155842000801e07200d45000942c03600712900800c00080118007480003600404100c095851540718490010840c0071040d80f1045034540115040b40099641d8603100e802e803685520400d42c041c0303254000700010b60064240c2000038550350f20440303d8a03181c1c2c0e00481521a07041444080c490b030607484a403101000d128258036030808a4046080c1407410340020311090030501840d014410180101d03114038000c405481c061a80f08905010840480c500000228003d01c10340d4001000420111490b0909401c0942591501d6000c0d600d4060951102000307801da07002e6604c40d0740f2401c070704200300c0042400509051455250f001d40d4800095003a6444500c0c001100c610440c0f40c01c070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 649809037 1250 649807787 649807789
    0x30c052505060c0a0b0a0b0915091b0d0c17060405041e081605010b0f04061802030405030d020a05070b150d02010f090f06020a0515070207031403090a030605010e070c02 74
    0x8869400c072001229419625140206554205200420010304045055080c0f10403140e0381e4100c0d4401c03043c1903410001e07964aa10b022006003180001c007540004d820008174074180e00c0e00d08001d8040300c003040150310341601071400408031000c1340904000180c2c3c400c444002a0b101d42165504407504840505c001c0c10301c0d44030454190382c2200b07030704030191038190520700b00860b10b0141c0310724000d00c0824810135006810003902070b200c0740504901c1203003095034030a41c0d441c00c1d00c02c1e8425500d0840891001c01c200d000014001e510240055803d88828000c113011001140010f010b07440541d910180c484115182c0301c0740103d0058114030340600d11030352108150701c1d42c200c6840015024030340303124843c2c2c404105403900304460b0841d44541001040c003142c099000140024403030702ca40f003190700b1020075450711056190151542001604041001c001207458610b00100b690ec0c48000e581c0f801100e840098070304451580300300c8003180c403500100450f1017000003c0341d1012075400c0201c182a07642d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 649810287 1250 649809037 649809103
    0xf09050c03010f060c1106030c0d050a05040309050f060d0903051b031207081905040302011d01060e070c0804170d110a05070501030e0304050406030b060405090d0c02151204030c05 79
    0x405141d08002009805206104604500c81d038115005403e443e0340c0d090640e27014a169118400e54080d1504100100340107000703030b120710762042c1d0309540c41c1094107041404000807481c0580d48581d00000920214021071301320700c035a04040380300c2e460300c41c2d6a60485520580e803510040100b0801e0b0001d00026000803011680710354450405d00e130022040c2e442100c801c000143c500403000815183c041004201030301540402d940d400b41001100c00c40240000e95400d072aa5401100301541914020440705405184540d14480c410024581070a03242e65a0b82c00c8961125503051507076010419192a19402100860440000c400681070000141d00c48554030025445800d04050340c0c0c41c01000003030320510665000d000010014420190740b401d003d043c4d0300c001d603900f82c41f50b0700e8000401d9101800185013901c012964403100070100c1181c00f040a0300440380110600428200480021904005407103072049100380c44516907d01e032402c08500c1c0c45d01c4a85103112140d0740340540078031030b0105 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 649811537 1250 649810287 649810289
    0xf230103080406030b0a180504111507020909011e060f09290a05060a0203091c020114031e07050c0106080106050109090f0b04060f08100204030b07030c03090c0f09050c03010f 77
    0x240c20302007410890172011074420300103548407018012001031218401e007510380040c0d0140340510944281c5203a0b220400c914508200805024080308011440041c2008040d050740001070000002d0880e0b0903a5000c02038003980741d00c115030140da80c3c0c81803282c3d074100c60208010b080d48030000c0220700101390100300c120b4942c680c9501182103200c0c2ea000d40ba600e00c0342034005040003a00058450078007103006981c90308030707a612038403030700743c3c0403c6d40600d5100c00256842c040d0165a01c4020485124140300141d102400101c040f000408207414005840100c50380030708031564410b5a0740343c0403500f003400c542c115000916543d04115003045960b0340810144d0a17102c400c6c0300000c0381c01300144894002c1c00c0c3d0110f02c680060401c10f0005805c464501e01301e0403031b0b903807c1c261030340141980c01d82c0d02203200e2800300814034020000855880303803280d0f01009400059040005102016403100d02d0101c040b64032180c171a992594081c005680c0c9800f07040e4110030a03040c89402d550600c0400c1100c0c0e030309 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 649812787 1250 649811537 649811549
    0x60108030901050d1d07140a1d04020112090209070c420e0708010c0f030504080d05060612280e1504080f0a0e040501080d090902090d05010f2301030804 67
    0x119003070b0b12407170481124620b0707800d0401002c40d070117203585408401111882000711403240510810010710a11012464842002d103000d04c0e8810340e44540c01034603540350185403041d017941c0e038034040001600d03007808650041d04107031a40903424145140000e00041c0c030f41c0010401604c2e0f00382140e01b10040c25010048840c46844000c2c0b0b052003010030000504010411011a00c110000080c8040e41035020100400703260340c48204a4010200c00d80540f83d0999000342201c80402619409030803541c4042d8001e82c00070320b00d920f80b803c5446140304c4004260703220540003111040c03150405048480040f02c0d4441180c040c089008416032a41c3c986020112103881d60b6032110014041092080440e80d4242c0050040d0781c80394030343c0600500104000c0746040c002d9140130b0000c56124400a0742558040459407011821800e201c0100041c1d08000000c80d0000440035514001440a001da03a54054203410002080c0c080d0140300744568248001050f10201003800600c00304103404221001c0d550 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 649814037 1250 649812787 649812791
    0x1140d02030a26030f071e020705060d09060c02010606120903080f0a090f0c0504050703021206103b040204150c030c14060f0601030b06070201110c061902060108030901050d 76
    0x1100282281160b001080001d400240041000401000c0c51810b0b07000d145559034401d24500c3c200a400035051031007210b8005270740004410030092074620020026810360140100b00b42c00995a29170a03103200c1407502c400340c0d448580c00e101c81680154807003205180700806000002c40c50b2006020400c02800f62000c0c0f00040000030443c1020380c0104640d5580048210340c40320040c00d140d0700c0c000c0702e40211441141040003044003a07100e03009640900145290304c1510f51144400c2282900003849080280448507041c00c441181040e42d040c1ca5801e6600c02d0841001d20702803c1c032200100e9005103129510522060100481ca5540c2c03a19100417030502d603140c186241000d0303459482d86d0034000c0030708141d007200f1000c400011031901c6c01405544000341e0183c59850055069802c41600c860700002c05214000c055032040364114942584841031710104440c00000c60400d9000c038084441700403480240d43c100560400c4030f580100381100265045c0023040c40028154401d402d0030f48605a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 649815287 1250 649814037 649814063
    0x1a160507170c030403031125170709020c03040503070b0408072904171027060e0d0509010228110105280e0f060f1e0403080301140d02030a 61
    0x140c00300d01220100c0c111030b02220b8071103a80380b80003400d05160310300d84441d0b40120140c10824142012400c080080d815418032446400c00d05500030303561100768046524451200000303002c1c1c80034401040b9034400c1902941d9070718140800c4c1740c5822000e43c814103400400304001c00c0122000708282c4103841881d50001018005840c04000329521110441042136000400181c106402003140d8038044410090b20020410340769241d00b101d4003101c001c00d1840d0502c160789140300c0e4a58140455910902e0f0011795101800030507850000341382c4010000c181d001403020680d603010450380c1800300c0031403e49034400c00f807044600806030110394002c042044404003052181c3c040c000f5500181104c0880304d5003142070981a440f020704c400211004a424050504800d05144040e101c000801030440c9180ca500000080000d83c0142d81c8502000804c046c2290090800c000a10007140102c0c4201d0f120350400c0ca05143c21500c100301184100d520381c88404c01600e01107222400790b500111140c000c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 649816537 1250 649815287 649815323
    0xc060c03140d1d03091008181501091b0f12020d020d0b0f0a03030c020907090506070b0a06090606020c1207050a091e02131a070209041a160507 63
    0x4640500308462814102180441c2d61056030390012024000303d010303403003042211a402a48a100302440c80b40c201183c81040120680100d8403d508a00d4283c03442d054802108009414001904060010400d081c001004042658090101d00c21101000945080c008203005001d02d0103131012031044c806411050401000b00390b041e00c2c400c0035000001c1d551038100103450001001400d03603241c440c14296000110500300059542c0c02e46e68541c81d850300780c800d0b0307400300491450010312006c1007040010020843d500e5007000b4000046c441c80c40c51038103003000512141038132200c0d0040307002e252030141d04000090f4006030f1a582c54209680c4c01da8180780e006800c1c0d0a000c42a040f00b40c000080d11000a840003140d8480c028a0308041d444001039400713075940d00141e109401303100140841e10309007031100c01072500c0c104410252810b03880780b511000e90b001c54480c404c1100c06642481c0c004052072015140c5080450b4011910362101c009a111240c0c00f5080c0d0140800c054401c41c0c8440f004428 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 649817787 1250 649816537 649816547
    0x11a030606100f05070804080309030115081203130c0305060a0506030c0105030a1505030105180c090c19030f0f1b0c020303030a180206043206030a0506030a1202011a09040c060c03 79
    0x400c64010607610b47d07858548174030035a41e6100c4c0032b146000703620300003640e1050340300c45c0c06100c1034619070000b90003100d0300039003031701d481d40c00c0030b4510700b250400c0d000041c0c0000e949002450080d0b1040c40a02103d00d0720184403401c03504c000b08880d0007031f0000c802e0340507180c0e80001100c1e44803014103400158840a90104c500640d100e030003181e050741c606404d00c0f400d40700786040048000d000c0c101302c5003d21690014406807460503107010303d800ca81444407642964100e03c405004681520b40022403052000940040c3d86500d610700c1d0003076648141e40080344000a00c04524143c0b1400c22442514240d80400d6803031100a014025030341d0f40340c40c0b03240f80280f45549c01b540141c0042c00c598444d519604402040304040a03408500b4124010b0460388002c2080062481d51000302186e0841e5100045080504802003840d54103000e40c2c0c81e8540020908600710030409942e40c000110300c886074020701000e100316400f0754400d005010402001980921207081a01e00900c1c20001d25055881c1c00c0d14 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 649819037 1250 649817787 649817797
    0x90a0504091e03090906060302130302010e01020a05010603111008071e110f01020d1422020f0915010206070e063103080a0810050105070f15060305011a030606100f05 73
    0x1100d42c03a101141d42459072000c40c41c0140e50007039208000c096a2114103070100d11501c50f000070307851003031101000950b001e4264511001e5040c016545000c25658a841c2111860382084070201054141c030348040c101205081d188052506003851681030018010340004800c0610400d0080038454820708944529072000c003600144007111660340b81800001c0c043e41000802c513044a1424a80c01c3c00d8190100b8407501810b10010001700c10020450240b502480084047c2d81280c0c108049103816101c0c181c036203220380082660390040c07080700701c0024209100940b4050422910035503521890380c4072022220031000c0000e0f40103c0d940c1350321018098140c1202f1081500c40f45032000428410032600504988845a858112a40e01d0350812501d00246005680c002801800010b002030041c0503c1e940e0b1a000d12443c0ac4084c0110003480c4c00e4490a820840303d50351a238164000440113120307041c081c035100b180581628039000021816440e02c03040c80074204030303040708024900c50055088074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 649820143 1106 649819037 649819073
    0x1e16080a2907111507030903030c0f14030a06120c03050111030115050d0e0334210c02060d050103300e06120106020c15090a050409 58
    0xf2010b14140d0307803000103445006100783e100c10040d10480d00c64406a82c01050603001c5240060580702152215000d0040381e00d0f2102e00241c0000c2000c070100031240d40300343c0326501c0b4827a62019001e190b201c10030002020076800144140d82c4c142a060f24041d03c001d1144c411032101c0c20607248030900c00c840b0282d4001300e80204452040005240010f1441d40106800c005c0160307650030740d417084a10301e07100c0389201d1081c1100051000ca500302d103684c1000d021500c5401d40c40381e03100113401800900d0388400c0261418020340c01007045084007a000380c0050b032070b540001c820078024102804140d441c8107060348c001d2800ca0032210502000540165951500040d000c0141e400c61403040030300c0d83c0264280700c69810450041d039014020a4554003d06034480f1842c1072100341902d011111255010400005c00c5c01c4e147c96035843c044900039280060301100905100b01207101a840034 = true := by decide +kernel

theorem cover : BRFrame.Cov 649640287 649820143 := by
  have h0 := BRFrame.cov_init 649640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 649640287 ≤ n) (h2 : n < 649820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
