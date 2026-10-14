-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2048
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:32:01.115691+00:00
-- url     : https://prove2.me/submissions/01642082-ccb6-44ee-8e62-4db98914263e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 368165467 ≤ n < 368345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 368166717 1250 368165467 368165509
    0x60a0c020615030c010e0103202a070b0f041802071b05030d050f040f08300706050403141809010b03010605031b071b080d0e03030d0b0111030c0a02 65
    0x42e003500400d0300e4140b41d0501604100b035400104609901980241441081a210f0380c0740c038083d204100340c101d42049600c00e140303003522100b03850200a202c1c080d004c101025005032002c58038142d0300c0701440e0f001c00c100380f181a00c14403000510000c106181180e0031007465000d0313544d00703140c90320f8250031000522030303083d41240e51030600840d1400204200d10f0351890400c942e83d498042c810047d64007466000440b80c168400c00801e0038007011590304901c0b03d00c000403074803400c0c0a14800780b0a003210b04154214140501042c008a40d4603040140c01500900b8140c0c690300000000c06000c6d031000410301480d021000718020036041c20b0400c0d500614514485906550400c40d00800512025204844110b0b014560f006036188907421541469030104c404c0d0303444092030a1040d2040c6251040c140140100c1511521440c0208405501c4040c020b0284d840e1070310501805c0010103800c171078203040044036580380303203c0c1d40108000c040c40e5030140000c001075012881042001310008804281030a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 368167967 1250 368166717 368166751
    0x1208091501050d17040b0405211915090308010512031801030b03100911090601020d14032d0906060d030507060b1c14100e030403020904020f03060a0c0206 68
    0x4455490034a0540308200c1e400816008681404202d921911105400e01c0c0750004002030395404100051044132029100c0041c140310010515518a800290b24003042c2c0002440382d4034680304000746507085205951051066984001c41002c41e440a2422800724000c00014001441c0c00c00c10040c94100d0080214a0144c4103100e02c80640300520106041c5901c96024180641d002d02440100300c5410004011012540c01d000500144003030581b401241c0003404035a083d40302045031a81a01c40d51507d203142c0d84200095812a407004082c400c0c0d88040140d140912002d00541c03194806800c607c20b6110b09005001d035040482c007a11040c401c0b00d1042100002940000030b5070309641c1c10000010340500044046400b003d80d400824001000400c2e0034000c005102000c02806a00c80c000c45911000da050154122a0f031021322480303950080c442040186400401d603035015102506035207011841c100481c0c81c0890941d100d55415407a104007080103030381000040c2e84001400202c101c04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 368169217 1250 368167967 368167993
    0x30a030e10050f0a050405010e0603091b0f040903020c18100b071b080a030e040b01050702150c0d091d01060c030810081c03050c0309070e15060304120809 68
    0x20240440d518000e1a004107a00034072801002a201c4071540120f4a50b030750450f2002c0280315500c0360007118045411141d100c50b850800c2810b4910800c9060000c18642600707243c442554007103002c41c1d030707840081d2080e0304009844600400684034800d400a02c090b254800800c90050220001001118920000c0000032a030345c88520086403440c0c11655920307083c0d4100a981e0711102c001c01172041034a075100003900b03c0001001d4541f14020780d0386041c031101000800040e15103d40d0010300040341840442c001d40340c250600c0840107481507402d0b103815489030300a4105020403880700c01250000b0030401803c0d0700e242035445241e08400900000358102580600800384240700501002000e500080b1081d406003581c2001c1d1400783d00300c400d400955428000c0040c0310031103040c0040d01300300201e4030700700b21881901c0c01040e551025100d62400d0442100003204010035040d880c5004034080b4031281c84080c02940102d001e00b03070301c448407540c0c150060b0000c1c60151001940d45d0046001e0000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 368170467 1250 368169217 368169227
    0xb04092a080703080406180b040611010b0a0b07140a0314030403030b091006110a110603040305041a070b06060304050c09130605010f061806020601060e0a0b03190b030a03 75
    0xca00e03294550429001440d005605905059000300180d48600350000c8144490480039000b02c0304c0580d610280b000d0201c00a6120007403a2180c4101e0303013070500c01444154000c60768081255018000060104840c45c00100090800d41c06a0a20355000424500344215a1141110f0391070450080100e000b00361350040008514052030058a08040701041c1014881d0300019508500104001c1060600c80504559002148a20004907180c44eaa01002c4100450078a10030754010011b40903a07100d46041c0503080c2d100034400c40820000700408615848601030302915460b64071246a00d4007410325254010100140113140300389410f008200010304001400e849405080d6582b4681e503c0d0101d1544601c1070f40700c001400242454008507040314850700d0002140c4180d91140c08180c207400d20f0030381c01201401050014bc012600520259008030781040f145400541000161942c0d00100e21007500143c6030100389a0241d07a0f4030036403214901070340c140b0f401c08501400c6142c40660300030380 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 368171717 1250 368170467 368170493
    0x30c011107051c020a110f03060a050712230c04170a0c0506250c150c06230106030b0f0a0308030f070509030a031b06061706070201050103120c0f1704090b0409 70
    0x2c06c010442c1503411072915588089550a6400350459032181464034544000d80b004681e4072000551296600107070304524020440341d6601d101c102c0070301d0280aa240000014002c28422060004020001e07228035148440c03400c005808002d04054821483c00c010f01d554030307a0040348a01d000340650b0280c0002c0251a0283c844d40c00550003154849107807010030543c40c0e9010b00203806080241000392500007040d0062107105100401045c1c803100c18500c0c00c19a0030b80840c84000201c4014001a8083d40c0205d8800000a0207039020728080000107100043e1604102c0701080e0220502c4000b40800c202281c00c4061410300606049200b004a9a510342c404005000c110308610481664a005480c000308580c00240c00c0c0120703511480320b24003021340300781c8c000098403d240c00600180c0c41032195a050782d5000a05c60384606e14800c08480780e912811051b55003a400900e070500058640c116401e40b0020900300c2c03900c4610740307a13242003260000c0000380d00540c03c10f10086c00055a040b001d403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 368172967 1250 368171717 368171723
    0x140f06040207031e05070623190e06040309090515060f0a23090306160f0f11070e06010306090216030c0317071d030c010e01050a02030c011107051c020a 67
    0x1070b01d824290400b01c8031054589601c91200c6901c00c0d02201241d813040c01810780030300032102400442c0c2e881c0441e1040d0381c3c04003d440300d4000e66501240d0791640c254052240000b2040000c61907c0c0a001d001c2c2c14190103440c00c5000c1703411800304000c4580180a1598460403003004807a2a402c2d400c0414014032031042070150485000a050b51494064400c01c4026072b46504001d001003000801e03481194400203281c0e100707125400000d03110400110b01540141816910700711250f10410044d83c6e01410700800c80305101501142074500328040003040c0c010584051204500d05201002404540c0c007504200c0e4828010000032190000036800f40b030443ea4149403290000d030642c1130442d120b06003616a1140402c0040900115607130007141c2c1c088582c90710800303101c1c1c0380001042650350b000b460022404218100c141e80305544c014805000148041c0c01036030300c2d2040714400c4a003154900d40810301c0749000030a0f043c0a000c800c01001015108120880c0000c2408110207580c0b4402d80e0001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 368174217 1250 368172967 368172971
    0x101d040e010e0304090603021807120209010e0405040b01050111030403051f0b120a02040c080118050604020d0216050c04020c4903050603071508130203060c040306140f0604 76
    0x100e011048258072000040307080205581d280e03620341c64100040e00882c8810ba02c1040e9265401700b044018083c841d0180c415610f0307502d08252085030910182d00803c007042e05005000450307a03c143c9440c042e080c86581b01d100810803540c10540054150724255218200079030090005000103080050340140f42011f800f0708580d1074180c01c0884001d40f490b0070201390810032550740602c1d01da0000552030241482182c041c841403401c1d0f03400f10358041d824401c00340c0d941c0440c1c1404400d1703001680016000746000d0310151500740c07020004000d071f9004940e45000c40c03860710b40c88024003505100c001ca40c01400c85056140c1038002009665940b00c107984410003000301c031040400303d800f800c2d101302c0c41030241007008038140c04900c00d081020301500e4240c000ca41440c000444c217203000705114003960010b03220031015840155045485a074003c1c12416001410695000541d40401020780302e13010012030b8983c1c4078110710303100040d102e000ea0800c0701c1006d40000e02c882c00310700c9400141c3c011015100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 368175467 1250 368174217 368174231
    0x2100506031e030301030605131e051005010b090111160519120b15040e030f1309050108010e12040602060103021c0c06201f02031314010209101d04 65
    0x80d003810006010699107000380000b4100c42e01000c03000d181205d028010801c05a5182100c2d0843c0e8040c6000090596800700b074403e0301d41486503404003c0c40d00840c100c64030611541c20741d030f08a0300203800400c041a0046400d080943e80b01120b00d50194054019060050741c0e03002d03031011858103000c0c851242800d90360080000f48204030300e42c002d00000300828014101400c2c01380034a201500c44444a00000c1c0354020f003400c041c0a411981c0c41c0c2803005500d010b030452401c0c209a000241d513085003006406d00014a65041c0c02694068144240001403a0004100c82482d11030f1210600a45c0d900901042081c160007090990460fa016103582c4c2121101c900001781ea60700340c00009010200d01c41c1d002c500380740d02601c2440300c08842c3c46010007034859141980c1e074614800050000b41c8208051141c060040f03900075540002c00c201c00d41d05d401c42039903202e5808201e002d21307440c0305a41c0450600c1d40d0749058040500000500d0400c03110b03440d5100c054103000d221008040703001d03e4039960 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 368176717 1250 368175467 368175469
    0x90e060607030c061103060a060c05120901020313080304090c18060305040f05010c031409031c0b0a030f030302091f020d031113060c120203030601020604030e150a080f07020d02100506 81
    0x12480c40b05580c080c80030000d00303040c1703210b0b0341050300240d5000d409881c0b41c080c0807072264054412419003680100080110b40d4001110107a1507002e414010b0440c0428840600000c000e41e82d800043d00d450809140c6442c1806178480840d0207c0451004004640211250117460b00c11014203840543c540481c80355034034100303030b0704004000e40010244d6103080a03180c0041d5140d4020701d4140c92400414150742c5880131090b69a008100c20030b80d803a02c0504880c249050680e000121844000d8141010700f83d07240c648010800c62000d00742c010940001c2c101001d80350140c540e111400d47c2c50650000c00d100c05000075a42e1050710b01c00c41c1032541c4c032070041c051503107280181c2c0d12820b80511425409070b03d03002d0003031106c40380c40300448415000700c01000f15640084290380c03188406a00420250741c0f181c2301160b61002502045070005180d02c060b1407031100c1d400c004c054012241e1101243c0b41406402e00c1c0c034004000b0034550071504030200c0f00031102e50100b03060001814009020580b43c039850 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 368177967 1250 368176717 368176727
    0x3030e0712060c0f021c0c15141909030e060904090c0f05130b0904080706060305011b11060c1804140103050f0d030c080106120b03010e1606090e06060703 68
    0x1400220740c40d00100301c1d00082008a8100746150381d0396a0350b900e01a810342109a1766900d221502c002c1a50b5025004194903100d1816005540d0040c240c40103a41113260b004005c0761502810403515180040802c50400c010b80d840d4554009000810000c070b002c2628014010055800c0c000d220781400260307051540d4841c4c00102c01c0d12f4110034449065907031804100004e501e1403040c50300400c0240c2203036071040041e00c60b84540e15000307440c003032866403503a0724149254441501100c940780e03500c2010001c10400d109001080b8041c2a084845a0620740040d00351203040e001c82420351f20030810000000768041c00c0c2c80301c40141400c1c00c030343c1d040c0c01c200140144c0200202c004202070300500020601c03c0000c0c5051542d08800107507221000c040c00104d081d101c2c000c2c0c160010509020040100512902103c1502400d221000030081c829a00090954911459612040d80074164820420554008000003044103081c22003d0314075103025165140340003030007079100ba42c020803d4402c0c18080c2c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 368179217 1250 368177967 368177969
    0x1404020c0d1214010f030303092108100b03070215060609120c040b0901061b0303020c0a0c05090705040f031b08190501050a020403050316051e100b01140703030e07 72
    0x890a6032688009000c1c010864070903240b121515a043c00f003400c900194054a550583c1c00084030400024215102540581107161007110000454504a443e00100310701c0c2c1c007000c01e840c7c0e545a440d4148080d400301005216000042c5c603001c02c2050006040d000200410b1707040192990044076a00d0030009480390254001540e0855010a8445126040032400340140340003264100201e582c0c410521075066000d00070b440101d600c4a507002030b044000c00880e80441e03c07a00d0f01510303102c16030501c9410310701404011240007001c45024041860100d03821075001c000c51425030704051415a200701041d000303100282c44090b82c090a07a070440382500381c0c3c2001d07294000c202e50121105e88a611400c00361800243c03025442c14000c2070482c0514000c440c112030704080118204022203400d46884c5103110402c0341c080c40303884900d81034903d00c0440c50b004103115501401040103e000718000f03136109524070710b0410042400188464a4600607501c81d103400d0710300018030900b80b01d01c4616001c55 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 368180467 1250 368179217 368179237
    0x610050915090a0602010e0d0e0f06070b070e01022d07030614011d06010504063902040e0118030503070504050303070f12140316021f0509070605090604140402 70
    0xc01c460401a1588024446010103031120900c2540d1401d04900300d0341d040c1c200c002a600540404d500281c8120706602c0038101c020544001f02580d00c0018200e035002c10011100c0d00e89800800c001e4030380101d141e154050080c000740288800f80c3e0b4510f0320420b0030001140d640c86580d403041c0ba48010400c945009190722a00c1000403c82c403198411224009101e6144004078080740d03182050203d115850041c501a101d00d800c00d0f0030403005480c00044010000011b0807104c80d9241ea084003040c0440484044690b036100c442500d00501c401d40e00700203d1202103038100903410fa111100c200c100d0000ba60140340454890321108070480e107c0c0705d40da2109a044c40f0110303500e0180300c0c43d06a0868664400d1200c0340c000c030150a002e0b50b00d424450f4003840301181c1800068111010002003240c507121510640e80c0b42002d0314041c9403509004448070020302d42c2d0300e00304a8850410042d0070041c1c02e090421500301200803001440d203101350b0280900d504041d112100d450740780c0e50190b61032401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 368181717 1250 368180467 368180479
    0xf01270906060503071208091210050703050106110f0a02060c10150f0e190b010c0b041b29090a030b040b091204030503040b030601090e0c0309010c050f0306100509 72
    0x1541c1008400703052107000703862081c040c2020008150319641d101180d0a54040c002d03a0904020104021408006400c0300d81c89024480100840c1070180c80303250301c00c0c11903840c005060f50411000910001d001d246c030303480035800141d000c003c40c04001249504c1782c0e4116199561400d05001046c246011091030b0301c425402c04008444208030400701c04141d400400b010709a40c1e0f0b580f88020400d040544100004400c81d609609014403580c004004850043c100071903080710307030b55034841c000108031010396490070301071000980340000f14001e1000b005410031900410146003510585a0070000c800b405007c400110034030703180c8509000034025504801220001c2c5020300341001401c6040300c100c80107000c2c0700034036003140c400b4105807019640c2110083d0309050901002203031590001d040e85051080c4000c001941c0c0c81000da07501d1241540402064503410412659404d440201e0300100c1442401d01c1080d0700c505010068a5000400b01c90141e2248221072040d60184100b0a203650821 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 368182967 1250 368181717 368181731
    0xb04060302121b0103180b0c041511070e060a180f0f0f0e0d0210050405010209090408070b1b1204031e030207020102061602061618030b0a140f0127 65
    0xa000c00c06a004400f402c1d07000f0440d50341107004608542002c065181c20842010680001c10b024500582d40094060030440c40d20f91220280800741d0450081903000400c444242884d01c1000e0040030010f10359001c100390039080c920005500705805014500710b14042c0c13443c0c400c00d600b072600300104c5500d09480030040d80d21402450000382000c101c00c0010031303040540043c0b44080025400719000c50a074080c0c1030500e4018140c501600d006081602d403503400740296103031941e8402446d4003982c8a040c0c419a00c1c150340c039244440082c010000c3c0007150702c500c0b20701084019081100c2d00203100101e4500155114a4103480c0601042e0810004801401c2c0f82824242c041c0e00406034103001f6000c840d500e50741c0001803001d88082c407419074016000303c004500743c40c0c6107001c2c200844502d42041e240718944902c00002d100500c0c3c1c03042d20144a6441406000d070700701e11420500400c42c08585145281000c2c10110b60307041841003e40c87c40e200000045003000c441e028221011030848140140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 368184217 1250 368182967 368182999
    0x902060f180d03080703021b1203010501170114040c1829070512072d0605090105060f090a02041206020a0f02030705210c0d021b0402040501120b04060302 68
    0x40e80008021290544100e6030201e4586411620b880300150715075a000d903a681c0c0c009040f8040d4025404484041d141c81c17001c2c14815509018031910351901641068403585444001400b810800c401c00701c0c01d00c2440018018001910080803d452043d507001c0f822800020045510f041302c81c01c502c0004040c08408030300c0e003050b20320603540312280144000c4210025a48101c9902c01d1600003403080e800000700500380c50010001d440000d0280c01c0d1107961f21004051160142c1c0e07080444812403102d0840e280c00c0000c0d0380b05064200302004000c0000d03180060204007150150741451384201c90880004e101d103002078044034081c206c0b901ea90a9104400d1820901a402460800003c900040006080b144c03000080e28021500076005010803104621603614800041407184020300c4104840300050008010441c400c41d01c1e03a004104035400080ba150110b507161008a204c0c9004000070002a07074171025841c8000d2201d078001440008400004005082c1e030303070000750884a0504c8178120 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 368185467 1250 368184217 368184247
    0xe0f0d2015090112050a02120414070609140405190f02130e070c0b0a0f09030c051506130e100c02030d050a020405090c090d05010204080d090f06081306090206 70
    0x11548040c0c0d525011580200550311850107000340c00350000b180711040c11401001604415040784644200600c0d10048d59480c800711803023201c095070006459007106900301c01c00c00041d8014000352030110281424403130010554691040191301c500c4e100ca0104240b060440146409c0d94a05e41c0e040104c104c1401100001e900240d03171512049081900024050307000140092146409d942d403811584044d5951280d90b403009007404980d19590b0000c8000e00c3c0483c0b180c112103a01035210352440650510b0207514001006480785202104c65050061a40303c2898480d584c00c040c500110304000382103590340c130f000030f03071074448120f03906140d90038a0b055001f00c01051407601d0381c841070203d0b0b0707101103011041e0b02c6288103641c0c10980e04400109a80c1c1c00c00082c05410710000e224150088881d200c3c10309a03000b581000082d6000800e0084102d074120700c0501c002c103051a03000b40300b18a00840070b020200d008020038a8400c03072020b03140800641d0350040314420b0340105070a885820440c60550 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 368186717 1250 368185467 368185523
    0x209041d0c01090e09032502030316060b010f1e0201090803070305040b011215020d0f1a01110604050c010c032003040923010513060801060b03061504060e0f0d 70
    0x8049920150f0218840e402d1a103018401d100c040c00540c5043c01039aa01075003040c4400e80f08000c2111203600800581d000e100500c0300c84108a235001d82c3c04c4060400c0000c44030800c0d0b8260500c01c10007059580d040d0400c001d28210300207049041100180d600f400e0b8007400001200600b103a50010070000030742d805a010900503400f548000f4200d0380c8400280c2c022094000005e800700c0c0740c0c49520b4031100aa030f001031400150404020134804450a00786050301d5000344251403007040f4030a20030465910500e0050045140350042c0030702d0030305443c1c0603101e4462600d0300d810406800e00c01c00c02e06000d0381040c6448888841c25003034405412707560f241c8a40150080000b554108070120603014001d185d421070b600443d094180ca240d02c0c0000300196941400e20f01e040160301c0d2540050301160a03c1558002e10103480000d40c1d81c03070500c0400c03c091409510005440100b4441480081d6220f07000e001c20120030380700e1101c40c207206030000e031640d100701900611070302c0004003100c4209903d1031010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 368187967 1250 368186717 368186719
    0x309030a030b0306040b060415090e0703060c02030f1c0902060304080901080c03061f020c04020f0327071202031606110625030b06040503120403030e0d02090601030209041d0c 77
    0xc442c80103000c040d02c503001a60050800c10090700492801d10300b580c01b950744090000c0000d041e1913a200010030a0f6a4011090350080d002440200309000c007601900c1c0101380b4034806149443c401244900e10740c020541f94003030311465490041a45000380e80045d40c0300707800501080d101e00e85844e00d20741c01d80c402c100c0140040d40780f20210f011281c500301035070b002c0c0c40020480454080d04034001a9195061801c1702d00310f11400000d1080340d19688014051050a070660710b80e00e16011030784103900d59806042c02034409840b002c07140707140808940070081c0c1d135400b60742c40d12240c0310b400000d02d024165108801c50300c240b04030014456420000014180421500351810b0380c2da0341030f00640f2030b2020036238038506102045001410f54400c0e40300c0e0290308001046c40d170a282c0c90303c0110b8035000240500540003800080c0c140240354003c900203080d071100320396851840d089540480c05204002e07154505154021510366615910b40c0c1200418038070806210040c51000240c255544213928911 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 368189217 1250 368187967 368187971
    0x26030f0f090a210c05150d09020d210e060a050405060313021302030411010e0f0f150c0d09080708030706021b01090b1b1305010807021f05060a0806040c03030503060307030203030309030a03 83
    0x251800c000c490f02d007038074009011150602c0816010300e40a40324075170040303030301001008ae07050000300c002c401e568081c030716800c1c031400502a01c0d8019115031b030001022445074100303000001d44168000c048070180c8505803036040e161740340d41003204245046468000d40c8010b000a07041c019040d6076010b10b1085001e1441c1c084e103441070500540d031144040c115140c016810b003034486c0d11400c3c1106014070000f0302600c0c1d81c10001e103e0740300b1080750f004070741c40700c0d000d411148003a5a100e911000c404040c125503400741800398a08004182d50788900034000300000c6d000300c1e201e100c0707400700922040b12202140080c4101051031070801e40005d0f00f1101e84c20412001040c0d00c09c2d40d504842660192050072501c207000604060056404220040c914021442600d40c48040144000300e0820014250b00c8007140b1810a01c0420034030381440e802074000d0340d20290421021070000000441180e4050410540c0c83e01c81101107420000745410184d010f200c004180806100f0010040040320a1b50303801b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 368190467 1250 368189217 368189219
    0x60c030605040212040b10030b09073003140c15060307120b0c030615130303080c0a0203120705040504060f031a010315111326030f0f090a210c 63
    0x401080f03002d800f0400300e451315508000340004c0c07030b6000710f90f81101c00100381e0450903a4031f80e681c1081e41412a0b840c00c01c1c0c0c200090402054180e80204268200b0701d4015002c043c030340581c07150141410483c060200054213540b95600d440c202c1c104c4031411145400d9030014010303103152004150094616500a12482500040f014180544400740b25440301c3c090040c0c1d00e501d41015002c0d0409060701e03a000000b000580003c10f03200d4020600714011002a11400e403450801400c4010000c0c02890183d804000729049203602008680203442911604582610740400840b41401a80c01007030f00940380810124003445055147c100b16445904050100054036401400d025004c1c40002d00d01c4144422050030042c45800001d05078440780106414040d06ca102c1c020241aa07078421644030382000000b1103100340e0ba0701c400445040d00300045141181d08158031540703116945240f481404080390b2040c0907035a904ca00380041020a480300e601d10f403880407604100c404600100c1d110210307140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 368191717 1250 368190467 368190469
    0x120b060403080c06310204110c100501080303061305150306090f10020a0503162a020f090403081317030a0b0a0e0603120912010f020a020c01090b03161b060c030605 72
    0x900c18001248810f03804600d0402417601100e0a0203000007264042c1e150340c1c040003e03455030b101400480782480028580341c1b0506d8941403c44a042e08140402c1e0000c008011036519820645415040c5070800050286d503100400c80c0400040244650300d030086000b0302490030400a80c80103403c4442d001d8501c0780b00b84c50320303500480c8140c40410b80418014000a0a01c0d1030801d0081824241410a044803450b14100411301c84411441d60140340d1b1040700d03040a506000180045080080d11074403801c3c10076803009030200c0c0000f02006103074101c1a040408100043e0a40b610071120800d03555202d0400041e18805004e02901950003440c00380341c00900380ca034201d003481c084d050290141a808134081040d082030b500c030040c0d56800c4668084610f400c884248a1055000760106006885c3c2910709402424408072013880d504001c002c100c10310084084004498004e4501a809004100c0b1a40e054038a509040c17400d1401002070000c0c0001c0c458181c025a4818202359410444951904 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 368192967 1250 368191717 368191741
    0x40507080c060415110a151b0c050c150d1503030f02121c0902060c0c09090d14031e0c0702030d0305070c111203040303050d0605060f030403120b060403080c06 70
    0x22143e5540c1c01060314030381d20103030f0150314070014a1704a20300340c42c9954002d80b110448050081444003a40e0b030703140482101d0301418151909466018503001001600300e854041d6250003248002c0d00c240c0d101d1401f4070341c0602700303000c8400000c0d20b10030520200120004000c11102da43c0f00c10b402283c020107a0068451001c20380e445d407000141491800c1040001c010405a180400301c0d0b501255108800700260742c40001a0500031041c2c0010071402c460602030081d203200242c02c8442c0c1d60300035000d400b50745400c0b4006140d42c2c0440507840343c690780e5051952050034080e95001040c41e41e54801d001c0301400c103c000701810740c02a42116035110400400301d0898404848040c0020400808280058003030248040989001801001c600c0c085441e030500f5903016a10403404118002107080080c5044d00621008020443e40c81e03081100d40d805c00c030240d1000900c010100005145035601c40e494680c0960075410014180c29107440d01da282024a5034805d04201503d403040c1b00008034109912 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 368194217 1250 368192967 368192969
    0x60602010b06030f09120c0606040b03011803050906070b07020a0302060619211407080c0301090503091507080d050609090a11131803350408031905040507080c0604 72
    0x241c9554a99a1001c2d4903c060110117403042c1040d00a550741c05690f0303021a00540303107210076000a0100d9051000c100f02c2118220490f090081e4141a00e1011102c100c40740c00448907058200325648404940c00600588602c3e140100314119000912100e20703070001d10240d0152280d0225a042c0d280d400c02c00c00700d803c00400d6040720130024041400006554205c608900301101605010f00115070340c2c0c1080481c00e1072448138a54000c01003003110341c1c2c04101c81201e821040d4020007504849403540ca4480c42550911070091080001c41b03211003211108a80c4240c2e0860a61070b180c854040c51000580020307513444e0701c180940340c0404c807051804105120b049620584043e2011801002d02201c03203024801d07604101eaa031002840521100d5080300d070007500c00e5448078690203070000ca0070a41902c0015202c0b0f0200300c050b030140c26803440d0140640160304818095120b95810312003110b01a04280590311180c100400d2004004c0005400b2046e1032505013039032501654681403240034003030303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 368195467 1250 368194217 368194219
    0x60109110313060e0604141207050304120203150703090209010e070804060510031a010501020d181a04151121090f031203131203020301030206071502130801020d060602010b 76
    0x204101060050480002c0c90507440d10030a004558428036841d41810042c0444041d6102e00203010b10b020b0783c040a000a4030460156003040b41400c0d003a485039680c80c02280600303404201c842d60703180150f640410800082d0451800381d000d442c981a54014041e03e600388040b8010210345002042548866541c6d5100d0106550740090aaa858441201170240504441c294500f200c40100210788030310040020700c0c1880245400f55490013000a1a01070008813400400054030048115507880d048003d00f02d500440d0051510b80b19019800201c3c071450740064041e850440d603801e615030700044400482c040c0403040d518070065146c240f01c1c0320900039203040054513040144a0342487e10b01c4183c0130300140036040f902c81d0802e01c1094106030380203580c2d40c0740040d40c0c407a2a108100c0c0da5250078203661030610302503046504d9613012500d02e0240c0400101004141e9016070b004007515415100ea000422000c1c040386aa51000a8000d50004030f048000301d06190001c256503005025401c03030000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 368196717 1250 368195467 368195501
    0x513020a0305072d1e05040311030303071e02011b11010c0f021e0a0b0705030901150b030703200409090501051005240415030209180624090a06080108060109 69
    0x445586007010f0307040c0d40d80100500017081007681e2a02d043c0350700e2500e403100507120750765561b08500300f86c00f0601501913401e00c030380d000304104668254400e640c01c0081c40070b2254603181000d0805d05a01620300c42648881c05030310825000300b40c1c0d90102c516480f0113400e034000c1100b101010b070125030300710400c0d24486c0540d000264010f0717a1607680c0c906101c8030160f50f003566403c5204d82d90b039882134001503c001002410200501005450078030034054040e010861869108e8a44040400240030003841c800c18181d541400156503200310b082c00021041c074510140c0d03200d0f100e1040701d00400280c0740640d842d61070310f0001034040da81c9040c0c070b00955000500040a00304000581c000060000c10204001079040c0b10000d604100c5840601203c084c5480158580300c500040c440341c581041a000d6003186400d00380052030700c0d8a0300b2020b45c907002c00b842d142c88800c4101041040d104002c0140c2c1c00070512a070000d02c0300d0784450030034107880d5000c0c00d0721500c1c3d980f01d2034081990b46400440522007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 368197967 1250 368196717 368196767
    0x140306040302210405180709121e0201030b090c0301150516020616060213050f0907080a15081504210e0409020f0607060f0e03130905040c0513020a030507 68
    0x154511180d00c0b550040c140c3d00c80c6000d403030340c0114600c014820440d92000c06000d080c0f200035500310000c04090240c0415072a0001071584070200c004081c00400003103a0f501106440969100360400f01d20400060041c2c0c0e400d040040d29a0001c3e0b0091242249110560f45510002846003003100c58141d081030007001800c00c4da8082081c568440c0070b1606009290b1280303000041c0840c00070701044041c046010040c1440c044c14410a16801100148101214000c020380f040d0421916038100e00a82800605002100310090389100b8580040d00c06100b0080d08071780041504880911492045041e05031a000350b03849417030325000385100c100c08a840013481c0c0c4a076090507406107103c1c0c0d00080102c66581d101d000031800d264804401511816118103180203042000c3c05000014115200110719025243d030450303c1001280c00f954280a403920089000e0061a461107000f4050081500b1020b24546c420b0074002d41c0410842030102c2d003000300080d10280206195200341c0090b04070880d440f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 368199217 1250 368197967 368197993
    0xa0902011d01030e0d2604020132040e06120a030f050d060905180105090313030204110705061609060e0603010618031b060210060b09090912030f01140306040302 71
    0x8600311695141010303504d8070a4041c0803010000345500304810b840f41c6840d104101c4e05211903507400945500040c100005020060342e21501040c8000040200d1105100b51200042c0004002c8030107000c0ba900c0c04127021414500d08001c0300d000c0c0d0f4048421480b140c0601460546130842e0404c082c01059030142c000f01c8031b5005500500c86460350b8000000c0f0203480e01410303c2156016600070740b24440d201d825101061003442901e030001180c40045050101400042c070900244d13010003402a031b154260064407005070001c0d17802c4c0035031002c20381c0d90a16181c4200082d80980c60240c0000410484002075800d0060944d14401a8007070019841e5130b0a10380709444642c615401500400409070000000c101310510005403807207400c5000c03018526084000b403600100b12807800c0020320301002003040c00c050500f1143c3c11030042d503d1558a43d80e6003a02814503280c0210001401c00020400900750391800106060b070700c00d0b02e0901c001540c038006050740e60f40215002405030b4001d001d4003c4d8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 368200467 1250 368199217 368199257
    0x708070c09150e09060f0c0c0c0607030e090c03010e0c07051c02100b09090d14130e190905060105010e0d0804030503030f011d01060f03060803210a090201 68
    0x450340260004041a41e40e40c194404a65000009410655100c00b052000605881d40d064011810030300400c11800c00090f203001c8482e0281001da0f2540002035401c0010034240300d136144a604c01800319486480c60708000d089108450076561003501d0b820009810042200b041d2030507900d0300782904101d0340d0341021031a25030340b2503003080e1101c1c413941c5001705030038059000c0c0c5040d0000362340c0a80003100178070b0501e00c1074031400c4000c0c1c1e120364051420882c0070b500002c0c00d045040224038049145090081d1030b54450f01c03a602c03007030040303038442000442c065070541c510601070784100c6c0c115020030400303000040c00c40d00802002021500b1240c0100321940c810080e04400700c01c001c1c5508070000c203607500e4010399440340d4003c50700f6030004420441c420a42c9c0c0306142c01040000b02e5191682e180e414210a6650705000760800d0000e80a2221000c07031107030340a50098207281044950755141c400000c031b1842c0000c6500c84000c0208000034103030400d6409034000003603040e15540010308a40480d210 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 368201717 1250 368200467 368200477
    0x4080304060f02031512010606050d0c050c1c080c04060e2215080d02070b04092d0b150f2d130317031e090708010c170603120708 57
    0x7070076511004003030300c144880d100460040d030b26614007100d0b00714030000f4000d40705039600e49503200364074000003000b0303003074000c011a030016000c014009250b40b032811041c0d5190140b0004d102403481403400500000c0e09541106483c9242034560303080543d500422440c1c0c901c200c0c061600050198000341c44d0504100c42c110502a102c62000b0740c8044e400c3c95400101d0b03895134202501d00300a10400c010908041c00b0710100030300c0c280b024184050400b02c400e90701c0d10841c030a0003819696000340d446d07808081c440078a800c1017207964400d130301918109014003420074111001e11602860340c0300565a801c800449000003182018581041c011180000c00d1000b030160300130001a000c3d400d003980c0d064241c0280302200005144844450440c10498402d81c5003a46090140780100309100e4a03800030414501c1800d03181e2008400781e035509a10030b003041c80e0340c1e120201d55030070203014180280d00544402060590751900140c659103400405540d00d48a84044883da0420003004012030105c1000300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 368202967 1250 368201717 368201723
    0xf050c01090b0c2203021008040c0308040b120a05010305100e030f0d0203071209020901170f0a0b07110c0a050904080c0609010f0b0d030f080a06030b010e060316080604080304 77
    0x108034225444000c210002115101c043e10000107881c03900c2c1c43c82e0f4030b0f0b0360010740c1310400d0b80302258210350200307120903901c0c4040001e0018080001e400c200b141c43c0c0a00c05103522091180e1129514a52041240c000e1800d160b0481030070030015103029280c0c42201c0c100c9400c00000e10411035418a40b000030410408002074a0008102c0c402c480c9400700d0003440c00d06140c1c100140d881c501210000c20389007030101813540443c2000d9603200036a1301c040300681540e0030020b0326150140411501460242074158000e00c0b8000c2c40110014081140019442000c03a903c9800d0324070380000310030752900b22103041d00c0e0344200855800d0083d41801c581195100b481084c000c1e1a000c40702c1e41d10ba00d086421542c070030700d0b42e44403501420321321f03034234010a50b02072002e403080c0c3d46c03200d41a40e0280154001d245010b017007200c181c0c00208844100d402c050011604101903400303550b1221200480442c007250324034000e00c5052600c1c0000003a0900b01d00454261802805050312a96103810301c82d0310103032043d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 368204217 1250 368202967 368202971
    0xf060904080a020708120703181a03070905030a05010e071e140411070b09010b0d021003050c0d02040602010b101815050904050910200904020705031306050d0e0705010f050c01 77
    0x3c00c48031410400c8030501d00400044d41d0301d903e030900d40142000180340c1d06509c0e0002140c0c0c00c001103c56200c00748454840c402d401a126984c01500311010183d070380c81150b0602c11580c4200501c02c0640c08801030040d00002d6818050300d502682e242850110502c10003201c1107101000003881010799452542001000860300100e0411808108c0e00300007402e0b2a880e14020500104a00034403624030a5039040d81c4030b9045060980003d0305105448240006240e150300019030201402803c40c0c4400b0b0040c17030219240c07501c90718004c2c003c02c540101c7c80d00a000d249009201d0f076000360b01191150034102c560440c0d0a0500d00c02000e1581140d2650b001e00c00140694890391751640030300340c851403a101c018005a0100305500066a001e0741c1540c14130440e011038840c4041c84201214000001520301594034402c51500b44c5c17440c070071002003910710503428101080d901d5105005010403810980140812081104030350b48600c030900c45c55010aa510700d88a01d01030050f80a49800e503018000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 368205467 1250 368204217 368204219
    0x30c01180b0a0207080d091214100f0213080c0f210303190c0e0112090f0212010912032c03070c0b04050a060503010b03040b0c0c0a060506090f060904080a0207 70
    0x394007080d0424a100b601580140b0002e001c1200c0800081c10303002030910305011081d1038079101209101241201600e1101100d0040750840d200304085070110103c610104031012015090200a41114500030f41030145103100140000000680301c803540c40c0200780011400b100001c00030700c122800150b407580c0c0700c1c00c00508010081030020714812003450100c500c04070a801601c5046512a100210034055203400700c40e070302e99010556904802504100140500040c04e14024281012400950000490302c0c02c0c1c6a40e0010f4100f00c84440c07060f0b03480c2d80c04218054040d001d40b080501c1942d070784440f03d402d503c408205000a500c01130910300c1035a251400a0702d548000d44001c5c0c00803001e1a100160422450804404410003007178540f8090b802c550420050100700d20000d00050414885100800d0000c0c440e042103a80007003030f02c4110b41801c08146071590144c40304581840c41030f4074000004201240e8007188030b21a84000f44494040c0c1d03190b6840001c1030300710308034800841c89074140c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 368206717 1250 368205467 368205479
    0x6050f0306010e31030906030507020f0a0618060e03120601170402102705091f2c09010b18090309121608030306030d0f0203030411060f07080711030c030c0118 70
    0x584c000c003580a9a1401e10031800d0602c0031381958000f41007201190710003a503000181780046080d814081c1d0000700030917114155403815007240c44c101c40282003a40741450286010030004000c2c881e81c14042a0b42d14660b6800d00195200d105a00007003842c86071b500c0004e03005182a6404c0c84401600b4206208090030003c04410f1070141c507141d0b00f00300e1011410611051821a40b4503030711075a0410014011010743d240c41d100700d06240303c1c40020360240c202d1a0340b440e1603031450502044000d10b200721130789007490a10f80a019126a114092404001e0640312202e940c1d540510481c9003100440c0761000d907500303020840e10385500040040c000c1c40e00d00740030311080104000040c81940d0095481e414100109802c140b44012208280034548400759079154011064940c8190407200c04924401d4079004100c0d00e10942c0c003081c0e510310340050b20707404004100c0098402680100c2d605100e0010010605954003e10b1100a51590005401e0043c83d0720800e40701e402d0b200c6040007822450707a240 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 368207967 1250 368206717 368206801
    0x503100b04080a02010e0402032e090507050d0b0103090201140a03060f06030209030118331409010b0301061404150f120510140615190306050f0306010e 67
    0xd0444000b0350000c0e414042035680c4407070a2901800c00712070461960501a42c00c2031000705444c07005000e400000c00310441ea0100c03001c400010003082e8028000d038500300c1401005075100e6581600e00915004028000f03510038401c110341550b040e1122650f04002081c2c0d030000307421031102c0c24201621004081481c1840501500003042691000f507240d104103020142990980710710301064500303d100b610082080621140c400d0040f003804131b000e0112090f00c0c404107420003038803980c01c2400c01c000c2c410700710b01400001d84501a00c0000308415180c0e407040609840d0300d482410643c01d5500c0210407146060361050400307035002140e4070440c596940186002c910f072a8031980340c040b17041c802d9100f800804c0c0484010b904034044104a61104032083d80949180508182d01840c09615405030352240d00d01202e681c07840d0340a10007a010140306004000d0103150195138090110031202c1e010500300040e40c0d80c103803003a09451b40c51590b10100c140902006001120b40c204c84082e00c04c600075650a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 368209217 1250 368207967 368207969
    0x1f0b030a06020c010b0915040203090f150711030c060601030b04060e2a0a050409090303060e180f070b0405151903020d061706040209060121060806060405160503100b04 74
    0x148030168403075140c401c0f414215188007001d18028000c82041100f10003101c8038880d1219811540180c1b0ac0c0c4840824a19002d460058400c480c8500380c0821140307010b2250b6548510303a65555213806003161400d071500d80c0a80044040710741e21040c04960250300036000081d01d44005000001c81c0d0343e0310010894250000d890390380403400720007090740b510495018103e0aa100d2104d09038501120650002c003144264400c8400041d5a03684ca10201482508010010041050a19082e0421101c0c80c4800030800000d41154814074011599407080402d0060442d4941d0800da41410300d40302c2801700018584a0707180b5050001c2210300d000c140100140c1c0034559140d0350050300c1d66040c10740f0004803585604a250b181140f00d01000e0010800181f443d88143d06894649903900c0e06c82c0183c0c1c425045040119111400e00d00c140c05203101640100221041d076021118161500000d201c2100c0d015581004031110100c80d14800c03500a50042da0081081c0700c80b9050a5565041c9403415001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 368210467 1250 368209217 368209223
    0xa0c030c0311100609050c120f2d16020118020108060402130608010f0f14040f0b06030a020c070e09030703140405090106030231050f131406100507051f0b030a 70
    0x4d074001c1032000f00f55a00c280f0394010070441501b803608900740c0802d003485000030070380d89400011100203120328410003000c020802600e0b0600b400c4500b145840e490750710f01213890311040208000700c03448507803050080000600c1c41c40280c8501400075001190641002422143c1054080240c841258101c0311b03410011314640d503d410065041c1303c4840300345141c80d800180c0c052a501000e018040e42800e0540861008a40011ba10411290a1800f80000c160110791000002c4100880c003907464008000b103011040030345808503291101d1301d81c80e9070190b850000580c02031101c10002070181e0b084050000958940a0400f6502c10014411180c00d8001000082d004140500d40c14020030030400c450b07240320301d0301d10402400702c20f015158112b0b10450b0311402c4600780c01e0015445d5000d5404500b00110418480130064070890b142c260760560b405409800022010058244a002541c201c142d101c6c2c054603030340b00701d01c01c404203007043c00810703140841da160641c090995040000c80c00700c1e48 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 368211717 1250 368210467 368210471
    0x360302120a02011409010c1d01170103030228080307030b030312250e0f040c12050a090b01210b07110604061409030703050d090501180c0e0109020a0c030c031110 71
    0x508100c0a001c103801707404201640c1c1401c9a0340b0007513410045112112001c5c4600c541c4000313404004950328403080c81c0401d2491000c00001c0145640401c04842c080c206240c80200c440c107841c3d140b1030b0241e450310003a20700300090010561a038482c1c6c0144407004801400c43e0700301581c0c0f040140e00800706480d1031062240165090560000701e84181e00400000d0514400b140050000f007142c900300d49919078070450742ca5902480e034602405a0421540e4a00303401c121a00c1c001c40c0c10802800c02003000d8500c203030840000158004201141c0c21814181008441ea684055980c010b01d200003500410621901c3d5820140d804020042d03070741300314007d007000f0411160000045010038070141102c581e030340080103600007003074120040302c171103c2d07100800103850200c03414114014251009100320040c0d41c0124074060050001138041a2a4003403115101a40e8940000080f4810440702c100410121400d00d004a401003040022080c0a82070200b810310701607900034100314121001d000f00365 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 368212967 1250 368211717 368211731
    0x50d0e03010b0405010509041b0918170403050d1101060308070f030f0806060f0315030a050318030d091701060801050a1406090708160c060f0c0201360302120a0201 72
    0x11809000b1076641003416601080654140300205910880c000c2018040600c00d81500c1a401a8180610020002c101081181140e03550a03072400002c04e4900355020480030800b42551041c030012035045a522200a00741044945010b0310041409020518107569807400000826000c170b0086c83c07054428007503c80094003600e40a09030140d01410002044150380420620707481d00002c0328a10f406905019451f6601c1c40c0201d10320002c0c041165030540120100d20040007030001c0602046582c948902c0500f05900003896581c52004220600250306003400308071030a421401540e10541c4000045156602c3d003d50a080d6101520703613007525a0340302064200c0d062000282d039080032086a50407480c2c10401ca008150050141c002c003442c0c60a00a407400d07042c0100280d884541c1e00840c1070008001c1d502c4014020041e801e40c4001650800004100c1c1e0840005c40003009054103244100001c0401a2240d42c545200b800301c0944c030520206000601800000d400950f0081e0b002103210 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 368214217 1250 368212967 368212969
    0xe0118080d170a1401120206070c15020d032c03090901061110060e0f1f0602060f090a021305060102010603080d060815070203030105010c030c0204050f0f0907060c080702010c050d0e 80
    0x4810b0082a5810091800000351030004010320903e04685850089245010080c0000b41043c85515002446400f0180340003d0300880181c240c11289029000d0700c1540700b10200070740541d4071600c05c85d0460040103803840c0561410030b06200401e03610354122030601049402003550010207820080215145004055070145c08220800d84521400800d000803031a052288130b540201502d586005c100308400500c04495214408801380000e644e00b092850303403214044d454401c140c80c4045c200e2009000600c00c4440085c0040c545079010b011020740c0c00d140124000100405440c050446d52555400004175000c2030207442c424a40c6c240000e4001d103071a411519002624940c030140f103005d60704100c032150700481941e04403034080c2045040c06150340b03400c484204a02e04001c1d809403402061184010a401d01d1074440c22030294000700c10b0b00c4004010303980b003840740704071000589503c48250000d040100913100f0640306051a1142c100c01307a44003030910b486d01074000300080c0680052101303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 368215467 1250 368214217 368214257
    0x1050a06060e030a08070204020c070b09010f0906022d07090b1825030b04140405060121061a0a0803130605030f01090e0a053004060e0118080d 63
    0x1c0566092140014540d880400d4072002c11120181043c90003003404000d540303440d0100e500c0207030210252904640c0b2024000700e107030041200c560025810100c008480341c040e107200001e80b03034503030000c05d41d80180e8100c101450000ba2001310110701e110304820000c40e4100b1440d006010440e1003c0380c02c28500c8103110b10000c08040b40d0051801520500058003410107160b43c0e4114030505801c43d81440103020380141002248250308940380000030090f50034084401800f0b40c0c40f550035203650740d13a5640368441a03a8082c5903c0c29181441200d0700c00031300103034032020350140c00c200485018101d0078001040000103a000010304c1d0070004164101446100321840a041c0e00e045c4542141071107240c80940c14030502079680f249a40e1280790343e094104100d640c1949600004940c14100a003442c1c800040d91100c0f0b604100c1310313542c4030300b001c0303c070fa4000e40301520303815a9603a82c8200000b004481c0c034900400291071080303900001203420030040c4114501070005131206103030800410300c803041c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 368216717 1250 368215467 368215469
    0x1e1203070c120c0f1a070305060105031303032a110102070c0608070302072102070509060d03032c0c090c0901080105060a030204081f0506010206040b0105010c06020c030c01050a06 79
    0x110500042040042581d084980210425040591108010540b407802d031100101c0d8080640710201d640388200404c0045c510b0524104808214551107482c0d17045e0030760a0743d8081e01c5040c0414414400500d00012007e50748901500a190206e078050813081101e01030b010005402c4c0d402d50241411f80b0015421101c002883c01120740214604245034450780d03807482450140e04e042110003070100740303030b28403030740595411179003000c540d64002c001d011460300c03a480084a00310140c00380784000a00c81c6001da02807071140f03a0285c8440410401560102e00802d00c85101d40d041e000f89110400701c3c101404d5480b10324458200081c40400995400c00c940c1241c014001c4107410010440d401150b41d001070428116602541e0880c0c0701c030b01c5000181c01a0040e5000002c0610618500d10a161111400c407288100800380801c03003501c0300401282c03034040845001d00381217407101c010011548102020006540160401801c24415000280c1182d1250b02c19040b81c0e03444009000340c61116215000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 368217967 1250 368216717 368216743
    0x1513091e02040803120f0705030a0c140a110115060c08070305250501140c0a1103040b0705010609110906030c0901050d0501091a0108070e0f1305010305060103110f061204020d051e 79
    0x106e58908190700501c1480001c03d2144040d4880704005001d0780549100c101e90345000e1050f5032100b01e1a00e0003012104084400310b0998240350380110308032003031088142510001e0fa100c158040c0d542e150202c20380c0c0001c0d0120100241000042041070b92001d1003141c818414980c1e006400b03480c2025400c0d1841504128824032604050002c10000c1d8030440f6072001450900008000314411400c0c11409143e20112680c01c000031441d003008010b500c51002e4803410030041003071031911180c240e454000d2003000340d0046000c00c0407452080c02034002c1c0084c402c05141c241e01e4800c03a40516016a4820380c00b00d11000d448800820900101b05061038541c1030a103090b0045140a140c010000d0b604003074654020051111954030b07039210000e43d9071300d070415400d0034400340d40d4a142c60360303681d17600340300079a01c2c04640c0c450444503281648102c4808040145070500344002c41d41080c0b25040c025108130b82c4080554108800a0802c2c403c003118050b01c541d11016020341e400ca40c0d42001000f00141c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 368219217 1250 368217967 368217991
    0xc0309010e0714301005010e060d0308040804031704030210210b15130510020c010f36150306050d0b091203010b091513091e0204080312 60
    0x140074408a1900e00e120081d01200c189206004480358444045003000084c10001021142c20a1412001490010004065008011503070380d50003d07001094080da150b682c0802000000804248070307450044e04540100b0019140c10b9883e55448641281440080c02207040460708105500e026282c03140c1d1080542446000c0301c6c1c8083d4003190034804400a22001c5580c2c14200417140ca610400410307034540d1400c0242ea031004070440301c4e04a100c03407007414401c201d031500b0350303031651320210706000c62003070603124016100c41d600016507085000e41018040b6060a139146034280f5a0842408581c182c00440f1004860500209075040c0c0104003c1c6d07024181802c4007004151100d0031034641d015080045000c4036101c21240030709001a040c0c80d00500880880041280c120b84c80041001b480102e420f5041980d989024207120300075000c0c400300343d00182000b082007040e260090301d18501ca18520207407a55001034190100c0e002030300711400e95407020500b850320107404031050307030080050060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 368220467 1250 368219217 368219219
    0x10092d0b16020106080a0606050a080f0d080a11070609060609020f0301030b1f03030e01120e030306040c201018020d080906090904081903060f0308090a05090c0309010e07 75
    0x111040040c019004480a00e4280c01c010480781c0700394040005050441d0a654a0388a0382c10004040d2046000346c52140c24241c0d00056050400100d0000c0c85c0d20100250030040e445980030355030018018204808903481d40004081c1d5411b0790000c02945100e030030000b4034916942007110031101160007200000e481003010388244800007007900c1c1126400903200185a45803400c00c0503001d881041c8218444010001104045e000a13440d60112420390703038041c03109000081c440075a03004c070301060110340042010038114141600b024680981904004504229920a19003e0a441d005402c1503402a056240c804011402084144013601d08204840b440039000103416801c6220700034030035000041c440c044e6841e110140c46240700001c041410510307150400e240302e648100310700c111307074080400e00c00d00d00390092140409a905030b008242ca072034291340d181017603070303014101d81a840740c00150001155561108600c1c85581d0001620b5203e00b05001e4841c00d4030104040c14003560070043e4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 368221717 1250 368220467 368220473
    0xf0e181e090c15070204050f090f0c0d0209060f030d0f080907030812040312060909050c01090303081b0d110c0f1527120a09050d08030c07030210092d 66
    0xa0400140b44085400c0006194202c0000182d07200300074000350011309110411031640b40a00c403d602c2030041d2300c16106075010000850ba03c8641d50b0100c01e5001c80000b000101604002c03240ea035020344050403500c0180b02550019260040c0600d92200044003240b80c0c10780f00f6070080d40c480d00001d40704010b00040741941d861607820b0007024030104c5c00051500000f01894490300000150300f014140c10800c4503100e1550001400c0c10f0802517420384980d01041910754070551028080700c0d01980c0da440c49484000d00e4404555903c3c44921400f07405008140b0300c007500344a1409115021089241d90b80b0160f402d80d0b040c009406c19003031194001c1000c101004a40c0b004c141e40c0218040b40710440d0080013151161081d2501c14800c803503200344100151010b1303950004010aa601c1c3e2a042c20350ba6585003004201890400028120a818000f0401c030001754406010082d1090054405040740c030460b52086401c40d80e420b0b61040c4129802e491414900e0345156040030002e008440b102c10703151 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 368222967 1250 368221717 368221723
    0x91101231b12040e0417160215070203030c0f0f030c060109050408190201090c09150918050f0c0112020c19020307090c030504120e030d0f0e181e09 65
    0x9880021800c4041d40022000942441625081444460065101e9441e4400342c404000c04443c11101c0f051a421030460100d44402552000340070303007507000c07503050280e03080c4071543c20000b542c01c6200c03005102d08030050f9401e00280140345040e500803e1110140920540b41c11041405d00d66680c208006101d14504040b400034150b90700b024000c9040e469a1814090034032a2404481b03d402101b2880c0704241d9040d0844000d482c05001c5010030f0548660040301207980d8070116424504402104008120741ca40019800b032004103d0700c0180780300c40c1c856a050030362000724150726070884039402106613082000ea03640303010a00750441c00d00c48403c14407a5545d01041a4880f040d200080c003c046540070030401001e05400041404041711600300500902010349080304d600c0c00031034650b900c4510801b040d8142520081c0140318800054200b03688030b80024403090300300314400010310a640c82c0d07c1e100c6450004541c00c0d03c4003610341203004040103c51140c0450b142c0c0b1040080c000d51801c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 368224217 1250 368222967 368222977
    0x60106081e09030702150d050c16110a0302060a0f080903130512100608030a031805060f0c04031a1e06030606060c07090924020403150b010201090609110123 69
    0x550000061601c410b884189140070720907000750312032442c06080600e0000390f0b01402c40065104024051603e503410300341d0480c050300b00550b00344140320b6940b002160f2038100c0c0036804603010703007400341060301c07900800e80c658001c014940c04241550f103030541c000e43c440e400c0c50340804124040c40c01c0040b107225206021505101d110311400c0341c6020441c0012003400204d0b055103400c00c04015450340d4070074a6880750010881140400d10780340304d03142020440720010207081c2c4d001c0d001d80815526954000f1071a040079007a40600305050101000044901100c10184109810080e10901e4608030b43c034941c611032825051021416000e00103140c9000411682184045030110f8442140c0c1000700d291001541c0404404c500301000c00081c441e10030f692031007480f0340000c6224402000c031400d00c180d01c01ca2000910329078448080d00c081c02031a920540341c540301480046007010301602e07410705480300d0100aa80d1080745a021100c1d07503030005c104a0742c12800d20801c000052080300300c02018091 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 368225467 1250 368224217 368224261
    0x1a03010f0509071b12020c010206090c060a110105010303360603020d0e07150f020d0f0e0d20040b0f030307020405040c030f050d0e0a08030706110f0409020c06010608 73
    0xe060100b0b802a014000c1004e00030798100d620b4001003060706101c400b640e111001000980240103d0410700d51000c10030078403510b00d0a00600c8070b91003d03000d00130390b64001d0540004124030011041440c49081c010f29000b90b003e991982d40c1c00c1340c51000d88058901d076041c0c8658030a6800716161804954000c00030807900541401a224509a100300c0c0192a000801a00704c0c09a064003054500040010003e1828540d40c1c40404002c941c106070791b189154140500400c81c0d040407032805521944130b00340f00c00e0b0702405061030351100396180001c075216038020650903555011407540070b0400303125507400d0310402c513104d07800c4041c0e5001194aa10424001034000c070780b5031000409110051031410025540400400400d04150500303e8480481204980002d010012503074803504c0c010103201c09440038903014500d0903986945550051150ba03079102203260f8207000d00e003006494500a48001d01c502c0e0005030b40d8291514209090060582005050140c04410b10840a400500b01420303035503 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 368226717 1250 368225467 368225479
    0x90c020c190506070c140a06090329131703011202090a1d06040c0503011e0c121803020609070b030f090129040b01020d02210f070c1a03010f05 63
    0x220421031a5040c000b504100e41010000414a04000c9265a420100d41c0e6810b6603401310a480020042c0c01085803092600047d4009000d0020503e4190152654000861680c1c0c2c05100c04040da000c0000884c0e980755500360b0010420b040c40340f0340710700e0030300c0741c81c034070400c2e85036605041100c006000d082c1c1d00a4000e04103000092082c10781c0d980041c090402c400785400c0d112042d01c5a9507520001114211201c000403100040c0c94101406048258840502100b9040c030200c03a10000034a071081004040002c2130081d000c4030700491141010741c000e0a00070921904503400c000e850400c0140000c04507601a03c1e040054042c1501969040705420702c2096050312411380041c05080100f255000400e03140703188903000d0781c0c25040a040e030a02a50248000000703e17005903140c1240d44070f10380c0941c00401034000110681c030340c801c44403056001c2203400c022044107907080b103402c0202d0486000e00b2407030003400080d02c80d0380a03000d200c1c42091642d145604019007071a00784d18a204482c01f4503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 368227967 1250 368226717 368226739
    0x70807150c05070e04020a080706020d0e130c020705100509030d03020a210b0a060e0904140f070902070327120204020904290301111b030702100f09090c020c 69
    0x3038031400c0c1d01010a504801203500e1030340c4031864101c01560550301240710310030000000400b481c010a25070101c420a030050300d101c441c0e0070b1041d81c4ac618410540e0b50b01c25411b030f140320030345280e40c841c48514a405900030710380c4500b000140700b4450803100c0640140007040c03280400c69a0002030f001d0382c400e03a901c1d016071144000308050381c0307100c00d44000e0710000c50aa40e22103c00c010951050352650011a9088041c2e0f0b0303203400584402c86081c00d00740d000140b40303000402080c1d520200701040503500c005c40314580301c0520311505169080d00403c0c1403607000550b070401e0503840311442e23200700c54001040c40400c104404461780d00c89244660310840c214864a0f03800d5648581c140c1d0252400504280088422090001c2c0c1180044007003082d03903500c0300700d003154505052251510042d0601207540c6410020380580f6100340743c031100081c180c03108000710f00050300c0b510020840c1d8440c948481510104844015000880c141c0298900903d001c0444103101d5001a40d01110581070311404a41 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 368229217 1250 368227967 368228009
    0x1213020103150e1b0c0c090612010204030602270a17120c0a0b0c041d040501110c06010e010815010306020c0a020312092b02060c010b1003051503070807 67
    0x341c284512650340081c001d1400150030b100e6081c0c0c6034070031011308407465059002043c60004900424500400560000c01054410b00b450080603030800c10060203075030096075441006080e030780076800c100ca10903004100b0252000560500c005a140380c101c808954102c9c00b0046005080d141c80b99900307402981e070342400c500506012a0f0011001c003c032607681d0b280c4040038a0303599881d825049408110384c400007a0503084100c1660141d518100080c0c50089007607142c081b07244d0002d407055855550302d01e12020860f082000034000c25290101130440c0758900340c2155a500d1050703100c40c241c4d4200000d0813254000340c125441c1565446600107032107046520300c2624240070008000e40520900551110b2540e440b0040d0014420440c2c949020203200c509010f204084105c5040705420f80070032290041c5022009010802c1c010000090080e04000010700001c0c800502040842d550b03209203d09a0804454040004029001007040c58074182186580382c500388200e03450702140c860a9508 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 368230467 1250 368229217 368229221
    0x12030f0913090c030c0510020601140d4103030402060307030207110a08010501090b0319020405040510090804060f05030f01060f090803030a0e0c030f0d030c0c08070506040b0703021213020103 84
    0x9203400440124119490b485d1501e90340059000d594840c011312001c02d40000e100040150507114200c054200c014912014844c1070761a59104a0b440c903a00340038540340e20080c00d0300070380c4101d144c600d0b10843c030070f44a150078041c01c0c04900910b258104108000150300d900e02143d4001c2c1441c6801a170b50001414040700a05031034600f03a52016560800007041081500f00c18107030744040a0401002c1c81c0d0390704055840002d030074680140610030110102500e0294022a8450301072070990350003606405c2c0c2841110300a03041106d280c207001c1424000b05601160142c5400704030b082c4685035041840a92500c60b0051180604001000480c80136036072080c084000241135403407c880c0c403420f040403d60003070294280818201d2040000c15295803500140d5800a60780d800054145682c049004801414443c4914420302100c0601180050400001004032501680c00303401359041915101d4200f04015201c0020076005004180941d0900360030319401c83c0209000c1030004540b8801680 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 368231717 1250 368230467 368230481
    0xa050915070501090302060703090507030b28020a02060f07053408091f0807180329070302030105101d0319050c0a0b0405090a0e0f010b12030f0913 65
    0x40d400380400c206081003015084000214401c0e002e4400c980e40c1e1503400ca044501c5044081c04079441804100f01044120b0103442c3c008600d00300040903070084002c00410007090300a0107502503400900c0070000742c2e06000040c0c10000d5106c2c0c40c507550420000c0101580202e90505803401010700c0035000705048030075811200780840c0840e420141a5040c021010f810000c4914010080b1030048402850041081c4042c84d400d80c8440e00071341c0301c04c42c04443c08041c1e85034a08203064000fa001c030202d6009088003151001c8948080002c1c5160340e188180008040e0412040c1401400140091398803020640c7c0c12921900d0102000c40d0200f84d007049401503c81034036018014680c10640d1001e080c100d000034180510102d98000c4804030500004200328402c0340002c103402c1c0800d22083c42e010016a4001084900200d03200595500e09030511180c0b15690a050307541d0068181c80342000100107200303070040c2000c1c1d030804410045098180c890041490312401c45d00060080304012030703001c03507 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 368232967 1250 368231717 368231749
    0xd0c02011506091406090108040f0f050a080307030b0d02010e0103090309170f07170a02090601180b0903190c0623040312080a0203070207030308090708060a0b011b080a0509 76
    0x8048240da8410203040d000e143e0013030000c042e41006001c4070a00b0302000300c03201364206940d40c1c5007035a51911543c1080c07551761801ca65a6040c8030000003c11810008140118003410000362340e820205000b604851028404070b0203801110030000160703030488c0060002860030f00b00466071150750324003103030000003607004501c08580840d80c03002401000111445030030480011604a161140206111645250a225519445440c02e20018102540d0741904080181017200003599500c0c031407202007400c2d070804500007401140040161404110690300185100301e500060351a0343c0328484810264050a000d10800c2040c2c110050120a40c14408842c1030460a0300c40b6100d04d080d41900c00001e104100003480c1001207010411203200701c1340038040700e8009089082c0341d950169105d100040041c01e03a805403103000240420b060101610a210400001480c051a900013601104040c50707205000c032070124145000400801c01c0f104000c00c1170804544440140300011045071503070310b0b01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 368234217 1250 368232967 368233001
    0x14010306020a0e0a0b040f05010c080d090807050123010f0627030206040f03030e1f111002041e060203040305100b0406030f0302060f061e0108180601060c03081b0d0c0201 75
    0x100521007a0180044e03994171100744c100c080d607500c01113030740000c403040c041c000d030a0030060140200041d81c0482c14a3b40700d40041428020203031a45402c413402910210b04034500e02500c0f008592601312041d003d480c440644404070390800d000181840c0015440c00700c050881a0500307251000418040f004690080095039143d45a18500085104520045000c00d28514030484545444001303240c4d6242011208028010700b02c4044501046400914086024114a43c043ca44560000f400038164901440c8982d1101e42c2c1254030341c552551200045420600040c000540301058100301e2051400021510310300110001e00240501c0d48000c105800d010040010960040b465500c10080d035002200f07039070785074004d01440c0340200c4000301405032a464640459030203429526000640141204205040400350902d44070081e0480d102040da07000c00c2c1010540c0c0040203e6002491406e09032080b03200c1d8450121500402442c00304c0d40f625204510301d118400d40c4030306802171040480d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 368235467 1250 368234217 368234219
    0xa110d0209010f03060f091203020306040906020c010b0f04110306091008072d0b030703021b0115031209080c0112021201090c201e1603030e010f0314010306020a0e0a 73
    0x19008403d10140f0085910303038202112020700c0f00240c85400f441c1500f040d90207111151b040c404500030f50004100355442030b40c4500b2000030554501c06484103000060000850a2a05003044018150490300300d21443c2080800780c1024001000d40748c0000c01511011103031340303c5c60510000e41d80711350001c0e000d501c40e010001800c0c42c0f0404041c05c11080811f5001c1c0c511180f80d01da1500301040c0e0054400742c5408101290710a0701c658018104e011541038142e01315200c00724043c1c20b445080c0e00040310100c0064052090040c00d5031064903507580d6050810045144c40c0711252610048190281808084a00450b01c045650116103072100a0000d4851a40c0c44180e800300504134920324500080d44500a2120b1040208103103010305120782c000c01c0988101034049429402d2050fa030701603402603030440070120f85008042c40285100ba200c0141c41074030a0001002a02d01c00d4500f020141401204185040d800d8030b0b140c1500d800c03800c05a0348603080c0d542900d501201d04407040e006140900 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 368236717 1250 368235467 368235479
    0x3050d0914060313110316170111030f0c030a02090301090309060e04020a020c040c11150a0b0d020916050c160503010609050f013003050705010b120a110d020901 71
    0x340c000280e40c1c0841038020150700110070300c0118082142d0b42041d102c0740b2150103001c03a06418000b401248010211410007244040111400d0103950190f4035013040003221014060f428003415208829a025260451030103041da400f50781000b4110100c0e8140000110700b003071881c1d4040702c00d4814003400a0082845920340207025481c00c0c411200000d00c2a2001c800f980b800740201d07001d0000030350040214070501d604100084c1a20503421003881034941400740380074424404090781e48c09080740b085482c6020340240c002d544890030702ca841004907103001c000503902c4000082d04400e50494110319550a00001e07155071003030018078400c600c110f07000e070070b0f018000d180c0d404161031742030f0000d0049a944202c2e002c01e4900aa0300301c1034401d0b40d007006008a020201d50043c020080f0302070302c6070381c500b0354858a101543c010b030705800040000078031005001090043c01800701094480074a0b801c01c0c031880d16180d45466030014006c42150b28160003a5444035403650341325400900b14481543e40f03030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 368237967 1250 368236717 368236727
    0x1006050a0e090c0c061b07022b03081009060b03070c0f0204180203120306031c0c06050f150a15140903030a0302031e1302040f1b050405120105060f04020703020703050d 74
    0x88840c459034841c80d400540440382c403c20024546d08502c101604003040c950820460404800f55296442d105120921603c2e6a003070f0705a00703050094450140307034203003060341715400401e64204405140c140a0200000710401e41101e91180e118030b0300000c4101645404144c0d01d4072044080c0d402800d054010b0500c0c44030380c800d13030005031080f402c40712181d4a5800e8a5441d00040702c0b42641900000f6052682041044c143d1484074090304e4401821a925030300c990440c3c0054402032030000c0c0c00300401105018000702c41da01d1300d408940c100c680c2031074000003600080c1c15405840800924031a100f408100103c02d07649100e500806490700c070405814028000d41048542d1140d03083d40b80841c80c0300c80103001c1014051005d6a0021504e070f40b054003070002522403807414075100342e504c1d40c0c09503159004403080d44825207550740e0039a4403442c10003004410340d4060008411a40741806001079699000ca0301c01c1c1c010015100540c403044181026428100369500c003400c280a03080004e00790075800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 368239217 1250 368237967 368237977
    0x4141306030501151a0301090903021005090607080c18240d090c05060f030609130f0507030b181e01020702060301030303050609071409040515060d020d0c0201051006050a0e090c 78
    0x140d2804c08099450340742001c4031410561009803c2020001070180386041c3e0003002d103d0740a0300480383d0108000c81160b08444040301c04500039003010702803003d596031007410b4641200f810032249051441d01c1440c00b6403110f042808a11945400301041000081540340e041088810b400716510383c0e406500760009000d046a08441c0a8202c1d4008502e0b8038000d81030716070152000c6c11113030035503458805210064001038000c003030700111070007202c00058500150f900310751710070006030230741c6451450050b05801010b44000a880b007401e00c02201480002040d115070074003191080480c400048040c0e0082c402c001e03021750080310010010040c190540c01580c014041501d060065a40d00442200d00c0480304101403000c3c4002c211140c5145082e8103c1d9801ca40c05000b6645404161800922203034004841001c9032034001c03400010324031192040d0b030101029070000340080e14045481c501c03014414020380301801408a418441c01f03100e60304e0320614180c00b804982841c1010b68182c1c41035048 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 368240467 1250 368239217 368239241
    0x3030718150203040e09070b0301090209011b03030b0102330612060f1602063306031518061507050c04020301030c08010506032b170403050a080f01030804141306030501 74
    0x160081440c122002a07e83c08032155540e60714256403d044106000e0340c40700580314104004d9010305d0001c82c1c41840d146003480d01c203850010b03005540310f0004e070400f0f800950130300c44040b105448107030744203000b00f9151201c43c44200841036540c400f00020b494106d240e50440c05881128100820701d0101040e05014241a245901484880c20380890756400708856070840e100c5c910001c06031850414020144841c038030040b60064031044008501700e03800403136004d00e6008007006545014100726100240015004000c00700c98501180810920f802da01c100d2070700184000303450300600605002e080702d41038000703000359641d50303403400c4c4260070f4040760080c0e106c113501e00000b08005140005101c45141150210170002c4c16860310420001800030714038100740642e0b207004400310300e050030440b84114480c0e200d460301c5d140490780040640b0310013000310282814010050001c94814000e49048810006000790703e100c0400110380c00ca445c01400c442481c2c1450380101c204803040d04082c2e01142 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 368241717 1250 368240467 368240489
    0x2e05070201051806160f03090210051e07021e01120614041b0e04110904090f05070807120b04110913060c1b060b030c0603180715020303071815020304 66
    0x501550004c0e02c403041035a10844038070b540051140001c0c068900d4402c14880b070f08000568024a4020414100c0c072045c003040069400540800c11040311010031744007040c1000030500349156030b404a020703065410103c07001080100102c140aa2042c03461003101a200a8180809655407200080401c038013a106440361341061403c01521488180b0064a5455503850001060b020400e0000500c2d00d040f01540c1076800300145881e5885034000d01150621540030188a544241131040c1000c1c256086080c141c1c12104042251000c06608107840c1ca030880e90303080c0755840e546441605921041280c07900300484008109044414401071181540515005d011210060b60100c417155501040342c66045070301103404004c40c410b90300c0000401400b41c22245941441000500ca81d00111030007440031242200c801850741007400300c0801020b042d0030080c820449440701941f2400010034034010080d440741400c82152103400500c00429585841201d0705011000080d00c0c2c0c0c1c000d01960003001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 368242967 1250 368241717 368241751
    0xd03030903171e09070b181906090b03090c04060902090108060a0f0611010b0607080a0e030a030c061503140c091e0f07030f1a040b0a082e0507020105 66
    0x30520200d581e03c145165500d03600c024401d0034200910503405070100000d80b203010408902c12500300001e1180c2d6101800500860f042c180030840c03c44c820f4141c0000c01008108100210380d00f0000e0034090310040e542e49603e0356a154049860201e10405c025071140c10075000049c00300c3c0c164018007a42c202aa101c440c5599414140810311282c0d1150028002181001b041031030f1265503c3c0001d00c50040000c25a06104c0340040d5003078012030030503240000d000590000c403075001207140070700c49000d03005004010b03030545014081c4880545c0240c10580c07503203400b001c003079503c46070304000c0c0d40d000c40e210700445100d281069a03141485040360107507514502040e107680342c00706c6c06002155400c030000426902c40500c441c07150030251800c0d0506842c1c124100070100c00b030051808882994204900b410010001c001c04d1354403c0d1a02c1d80140c584041c00d00c40c9139408601c5440072070180540f00c403070070141c115001c0540344d1181c540c0c6200b45004140020390381c1c1900214024007440010fa0580 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 368244217 1250 368242967 368242997
    0xa020102070834110409141b13060807030f0302030c0618010e01020c371203050f150405070507080409060305060121111518010f0905030c130b0d03030903 68
    0x114840c1c601c06807031300c91a241120700310b1030940c0040340010301c81e850040c0710b480810051490003e040055800c4440c4c07d200d640f42d80d007420201064400a0050240043c3c1d140040c00b94076402940805001407480b05081c00c103060080085070703600a01d1804540c8a442d010035050300350601ea030070082e8154205403030508104814001e079090074404501400d001680200010913084143d14100c0e08a4250550075402c1c900e01742460303185134001c42ca01808090100f000078100d600042c0b402c80c203d10301c0070031700c10824011000c00c0042c203803c0d02d0005194035100d1041d281d40c01641e100500502d000580864071114941204003141d10034801c0700c1c21641c9420404802000000722410f0b4203501071042e0020800a80840d00100b03406083c0807603060000234885102c0e800380c040243d01c0b1a142c0480040365030f10210301c011480161412010182c14200000d45660f480c0080d0340c49000c054603091002010383d03000c0742649a0050060880050310f00c1c1c090042c1c02610000e8005c140758060710080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 368245467 1250 368244217 368244307
    0x6220317181603051b0a0b0a2a030507030c05010b030304030521030105061e04052e090506040e0a0f091208060402120415090605010f1802040e06060a0201020708 71
    0x10f483c4c1c0075014110780061415028022043c2c00c0c141c5921021864000800c40385c00c80c002c000000c02903440116883d1115401403034090300440d0440b64000003400305010917480020b466a45602d46003452040f00c0134180b5074050a2000340f03441d4103000005001042020004100c0140400b03000103818407850032000307135000c0c0424410b098010310f00308041c0100507110070100440c90403924801d17052613104c5000c10111040304448c03030030700ca11600b1001d0a814808a000c180d100c0146094240c8504100224503180120f120300340b154140e1801090070f80030749810a00900074519010002c045560901880f0103d0210a5901140b10840481c2c0d290815008a840710509400320030f0b02911240c1d13401c0100010140b000110340d5650402000241d40307801407d0007400c01013203d50182741000362034020484207541d44102940b04210400c14940040d0b40d150384100b00300c50050b1180d036040c005a0192041d0031004001110014071801c031f040d40c0546c103e4400d00840304c154005900c01c4440c1c80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 368246717 1250 368245467 368245469
    0x601080402012106030c031a0103030e0f0301181a0709260a1b08010b030313030209061305010608160c0b0a0b01231803062203171816 59
    0x1001480200005000d54040c40d100e000c451140920001c0c004070301c5580c2000c13100305400444407109406030800c241301d00c41042003070030303043c1841ca40c0039940b41d03980c007802d4031208044c594041c5c00c01180540b40741d9000e51050601700d0550110904007901c5261000e610f03400015240369501007000400c0c0d13400c0c8902900f2040d240c070340140680841c4140301c08030101e0b00180c503030302312031080200443c00900542d007150800f54901c8100c2560600b054006800e5480117241203001f61720074400c42886054460754041203d405035006415074a910f008901a000144140c82e146400c04000061069010304406d01c20710118000d40c04500940a04032003040c80010094001d6040a000c0f802040362a070003400680750504107201503c18078005249110041e915140455202046200646103884010110320708224007411003460302006035102d1002c00107081d2459084441710504060044031480c2c5640403007020701c1c00915000707008064501c841030800e0520b010b02101c031090390071401e80c118 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 368247967 1250 368246717 368246719
    0x509090718210605132a0b0a0c0b1609090e011407050702010206061203030a0b0a090f0e070b04050d0f021519020c0316060309060207020913030813080901110c1c0c0e06 74
    0x1001001c80205401c805a86c180c0400d034107070f40e14007800680302a00c20018506200710340c87d0003c0310140c90a060910300e1000b0030401c0281034801d00f058107180d114481d070040d1020a40d000401d0340080000e2401040840400c1810485110078011140e8202c8040c2104500c04da00b2201547d86034020701024400ba007912122640c414008a15180d00c0c5810039414480050440741519544041036400d0b650040c1768105140d598001c40254000144421009404058481843e084c034190105120009415014000074100c4076408210b6807400c10701072110761100c58458851903d0301001c220200e00142c1800548202c00741c40c845802c000c1202005503614079000289035280543c00d50180245160440e0f189508104aa005a4440e88401c0c003035920020889445d95591034003400b050005009a80c04891040e42003000940010490340c1d4101300781b0b8942d00000c03010032800e24101c00d00d542907621404205000d00140303440520640c01ca40981c072440447d40d5103032030f202c7c903111040d00d810b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 368249217 1250 368247967 368247983
    0xf060d030f03180c06050c061005060a050a0201061a030610020114150d0b0405010c08070302070209010510050c0a032f0c120a0812070f050909071821060513 69
    0x12480540030b5400343e0103010490034011428441075840000c6a089030700014042040841e400040c04400c000140d800014140480c0307150341400d00050b100c0c01116041000c22100181c0c600001c0d10039040040105017954281c42440748644400030180c004944042c000c4000090780e200c4107105001d40e49038400303444031081641c0c541f000e00395011110004aa5000010780c003ca0002820018113584503d001da80002029200314100030645040030705803204160044c844400960f4681003504d0440310111600107070303202d80300c1c3c080d1854020302545403c50b02070b101c448814141c02450101403010401c01d40007031543d82401043d140c41030441100c0031a408501c0080c0c0609241001c210980740701c0301101c620701d0103951150000e03030010102442040d1070000303002c2156044454160000a5410400c0c1081d08800200d403072490020841c0c420003075428412030002e1060381c100e102a0040c0c0e8102900c070141c5035264094099110381c1101d0139440d107400260f41d40c89244c100c005665010102d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 368250467 1250 368249217 368249237
    0x10e040c090219300e0f06090303060906010c0c23061801030612080f090105070c170d090326090406030c0315020f120606040e09100f020a091e030c0e0f060d03 70
    0x1004c80108150b41407801e0038800c8100700e4800150400140b48942103180066550b45012010300000e5040540101d060002e240b01c01c800050080d0305030001d40e0b0803070021802c0303c41c801080f5001c070035032461140d422500015030b4000620071010000d240103030a0301e003800110ba83d08128112440c0180b806041c555041c046211003c260400030400610140b402605000c06521103103443e1a8a9005405401c51805038101100c4140f20400c08001c15040c0702d10400e2039500c8900b4508200c0c0d0704284002018018050282d640e9015034103c940c0140c001c0080a480b4034101d490382d95640001c0e14018a14400c00404160600031290414801c9500504050483c00da0307181808002d010700340d01c82000c0c000807494000620103140305000140050a9102c6101d400c031044a0180c80d000b20118010450000c040d50042e48150031648049100c00e8100007070940007001d14030a8100400e41d124014000610307449a0303454601a07840803440104546680c801c014207500c485100134045002108 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 368251717 1250 368250467 368250557
    0x2e03050a14060c1c0b0a08100c050703080103030e1201020a0306060909020c0a0f060207020301020304060c482015040e070302030c0c070321020a0209010e040c090219 73
    0x807413800d00ba040c080001c501031020000155040000d504042802c0c0d00c0507000c500120190b000d58510540c06050070344c43c3c1192501c00401d82101408050184a0340c0704d4294000d0b00d5884c070142516105200131925215102d00003005840d0303a10a00300011080700d0045488100c41c03007161482d1415034010824249a40d85010800100303036010f5030001e030309000c0302000d1785007030008600c600e12070280080e060400c171784050010400344500c42ca0b001a0090801c0c602c90108440098542c4860140c0060100c012214141c0401c4500000c0980b60302e80c2c0b40d05074032070601030100c0840104464040044a00d054205c0d082d0140c0e2090303a442000c0740001c01c500310300981c01950071101415059240c1002018a1440c0600544c012540049010031900b440302140e4528104102035101601c4484602d8000580b805010b008070100c0f007420302c1c00704003040101c82a010080141c0c81d015034540082c0e010b07140b500c1c403402040c0ca001c5104070001e604600300030320681203100c0504118044200d0410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 368252967 1250 368251717 368251747
    0xb0a110423192c15190f1d090a02090a1d06040b0c0a0203031306110703090e010824060316030302160609060c12120f020309010b010302040602062e03050a14060c 71
    0x20340c0c02500b0508003014185d0b4469444240405441c0b000c600448151501881c500c500c0145e140105083c003c12040c0700d80401d0200d0340b100d00d80d070100c403003140545440d500c02d00148606810b50003624041c000300782074080c021401e14480d030300031002640c5e80c1e030b210b00441e45984600c061480058008200060303543c41070171000d411a0f4080e140004650402c91003031640c4c1e9204407000d40c042039030f601e410002c8101c004c0c40701e809420060080c0000c005687d24510403941501005641d00540074000744080d10200a840f20804803034412440c20b039580e00300030b511500300350000491240176940c04541540108406003c5030056603a0071215150394948e5200f803999254442c0c01c11070040c2c801000d48045000d09020360212540060380d0b0705001c80784d5801c4030882d000e040c2c145030041c0010022541c01141a03540022503603017520254000c2d1002e801c00340e6050342e1492062082d01004000c0c000c1c0040d400c03440f944919110981415030420381952000100c8403c08440e0301001080d0b6882904d07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 368254217 1250 368252967 368253001
    0x703020a0314040e070e0a0f0b0a030b120102030f162d180825060807050c01060510030f050604050c0a1404080f0a0b0a110423192c 58
    0x1c0002c140c00d0544400d040100d202095410b0000158400b1040c0d0710352402c0300c0c030040208000808400914075041c0e2803000350003491544418903540b6503942c169038071800d01403a00c0382d00700c500866482c600b0301d1a4885a090980e80c4214110226200d40c410030702464680c2603000c0d090510701790150480485411381264006050300704804924150190f1104041810190151901401d0030307200c0243c44042c04c0d0900c0c00f02c3c2546040d1404100300554103d0512030300071130545031a90f40d0b24026183e06014110036070150741c003d5810600340c00c04942c1948140342d900500d4409208a80b5118204019190300f584d00103e00740c1c041000f07001080c003c40410041600708401e0500741035445100504001c000300b520300868101b90010320030000c6010b100b6501c5050280304000e0795a80601d880d126000f140551070704020040b01901c0452051070941902c010024418417526880c0690700e040071800b84603a0303000520344c1c0052406142d0603004001084502172016241c1e81e12000c508440e1116 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 368255467 1250 368254217 368254247
    0x309060313060629071505041407090c08060d020a06030b010306050a08150108030f041202060d02030a0608070605090f06090406180221063304090603060605060703020a03 75
    0x140c5040741c0040c050303008000003400c0814100394043c80b8502141001140c03402c20307903081c034010443c100008440314641407140c90f205200098640d5145001d8500d0304048400e0401403150300c03000241044141c000049102940e516603606403503079818450040c416600c001d51200e401c8105002081c0310341d021140308003051501043d00d40e56132010811a095942000f08a508241106010144e0303000400e03005000c9080214a0515a002030b20224045c47c01a44204400c00800b10305540da48410f4582c0301402a108665038107104070114001c00517480b8444560051001c0001e105010b0815510203000c00f4001154220600c020440c003940420302842c0e104d0350b125804100600718843c10024143c0301d120050f61a01d400301113003820304080c0d01080340080b61004101c4d803074a43c014941d10510442000155106000e40341d4007092100c1c2c07815101248001c03030002951034564008404880c09828100407a42d00d80003444628824030001401585c080d9803840c00003840b904e40c241d20152 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 368256717 1250 368255467 368255491
    0x80c0406050609011d180402030c0109030f03180f080d1d03070306090c030c0b1c0b15070302151009050a110f1305100f080f010503120915070605012603090603 70
    0x1d03500001424003086c2c04c00c2e1040c25081c207000c010440c1000c01a072071100c84242070a598440c5183d0b0b95480c030080c0354000504110002d00c01c40e40da441a80c40380800740200040c8040c500da1030740d03a40c0d41e50f9044210542c0004141045030480c40d03e44a0f4400000d00b0302802030070895085440d540060140441c040311103460040b00000801d0050490b080904808141c80e40d4078580c401d0007000314621000f12000c02482c0800101c01d43e503a2596802c0b0002c5000301598036210981030aa082c5150800c40d00110221042008104918400c40800307488804c0c0c4100040d844010f4100200c8000008440070040100594079a031000000039011207000704800c890704540382e0000c1000e03071005800030400b00d49600c990b4454103400a100366440b1030594020542580b4010000c0d503940702c0045200c64003c0c0014403018280c0328002c3c00c0c0300260b01c2d61582c940d507a0b80f5141a20003000c0074402c440c005509407164602c4d1f16000345540c0c0018100b40011402c00c0004810000e8030b60000c0c1c070f1648004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 368257967 1250 368256717 368256767
    0x30a050c120c011508060c09091909080a020f03190e22050105120a053403150b03070b070b130212060405120a02030d09020d0c080106080c040605060901 67
    0x86448018074030041c0c10000859850a0a410035040c0825600401c07641c1c0c01440421030342001220541e45408001c513801041ea440381002c0c030b2b410b0007881c0b41c14081c0e80d0400d5030400038814110010300000c103043d402c4515440e03408060395140e01526640c5001c000c203030a80300d10698452008030900400041c2a4241c8050164150340a4400c05860b803002d507441344010409840c1015000792460194000340c4a036100a94900c3e80340c1c102d103050080d0b41c0c8224003440441c865014007020001d40155001070410340c40f0f05040140c1001128441c0c011400d0508003103141c107010420781d088036000822581031440036542c1c405044001444e03242c080121220718805659400380703841806c950348014060904040c10928146401182d02d1800340d4010484005166400400c44581150a050000f0510f10a100241c10310a404102030311180b00003001140b100411b601c0340c01181c0d031a8007256041154142444141e500a02ca500d601040c180010040ca50044001d6103081c0c500c2d1107119140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 368259217 1250 368257967 368257993
    0xc0d02060702210d02160b0d1a18160c030c080c010b04110909060f010c02040e010f020a02030a030b030c09010e09011b0903171303080c010b03030a2609030a050c 71
    0x11103c040055651007101502d03a0f60341c06100d003408042c00221851032036810001d10100c50300c584145080015690b44c0c21400c1058078801491410000521115541101c071814489400701a1407403070f042c1142881c20182c9034018410400c078207502d62240c0600700081c0e21080d440b034100241444086d500d4144c6080140c0d180c0c458070000719155080280c41b090450700780b0540d04002090103001b003000b555400456a0444a01d5420a41c101c0380412102014143d05025003031401c2c0c4039200500124040c3d14094020000d0119020240d50800003d0240020951340d500190902604822140700501865001081150344060039100101c0c40c6058940130348024560300112100140b0381d101d00b401080565070000240f03065001419080c00b8400102000d032032014400148800c0000880580411003034100384140741d002001e503a00d03a014410042d101451040c450420310801d5041580c1c0500d8208650380103580c00e000450501c10165801d480c142e1020204c082c0a00c01d10b4004044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 368260467 1250 368259217 368259259
    0x14040f080f04091b0807080708010b070203010b061809070c030c060b030f07151211040e130b09060604051e070e03070b0f0a02280b060a09050a09050d020c0d02060702 73
    0x1c1030b2607138100c01c809803440e0200070000301015041c40c041041c0c2405002c43c1550002c40a4191200c0340c0038540d030740c8243e20000e4014280c00c030038590011404240321014041070783c401e10f4803007000d03143d80d003031941e892070b0844c0c150200300700050109018402260114006a00203820147c000d021070f0315008181601d43d10341403d541c032000700c0c00d05031403036000302c5035020711030980f0780e803002c00248141c0c400640501000d00450003003079403000b04040081c0228074a0354000c2d2440390042801c2140b0b04000c0344241d11070303004844450040341014003081920b0151180c2c0790804041c05150042d94541341c404030344e42904a20400e525105503000440c012040400409558000b802004ea0350048903401a040ca5044413a215111507042c0212008050780c410151030181d008070b5081441e51240b000941c0d890700364000705038081c500303400c018408429900c0710340118042d0003120b612401c0444d0403a901d4112100c40d90700009800340303c0c001410108064004a807000301002c0c040b280031f20601ca0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 368261717 1250 368260467 368260481
    0x5040804180903020f151b1204030c050606011d13060503010212180a0302031207031e05040b0105120703030806040e1504140d0503060d030c02031002040914040f080f0409 75
    0x1c40d03652010310034101501040b044480d0800280a49100c0f104040d1140d0a40401011480412518200f10406d81226000c54141840c3c5000000726803d050800403e61a00d6010480d041d21607140410a150f02610071000e009001a9821a081c0510701c18403600d41d81040c515140d054442c1c07404151660280050800e80c2d40903001c00e551072070031003403079000c4002d0000000f10035044856507001180d8080102c56150040c0c007005a02d070344592400b2001440900c01040b0f4005100b1000011000c240d008140258060280040c00d40d80f20010421070908206010503560301032541040080d0050100315807003000208000b4038602e00307240940c1040d411a0800c0c0590200a0410041101200107418500b41d04801005402d00d258005441c030300c00a403001c5e200d015031241b07120406106041d40c41e8075030350140540300054010f0385100041d40003402611901070502c1111680c44c038610f61594401d90300081c100d032049110742c0324160a540045800e9905030000c100209054055018000b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 368262967 1250 368261717 368261759
    0x6050c0715031523092208030717010b0a03091a0405150a09031706030a021f030e0a020d120507050f0d030b04020705070608070903061107020a080f03030a05040804 72
    0x2041c2000c0d242c1260304122615000044403010580d60544884040704464850701c5003501c0064031611417083c4441900b030306c0e8080d4a5500c000380e00001c10003030364030701541c0160041d4650140110b540d52a00c8040d040c24090f0a001c1c020505c4000480342c400d40082c0b04c0f407402030f4441000444100170b002c504542c11203007518a540180005104141705040c020713804020802c1c20410404a0b940050000f40743c0c840d8055054254004101e09903810302020001e075600a1941c07408900c00307029038100c041300c0c03112107001c00e00c0c0040c48401420086007072440035074010113202c4140c03030664681c40c421444250300c03402c03c01c0c180b00301d0b400502c00f0003060781034140080040c05100340c03191005040e03a88040d0401e010f00d0040c070a600002d500080c1c803000340e4003107007060bc07200c1c2c0e21804102c1e01e003150f42d800034001d02d08080e00003141145034402002c006009940307403540307213888900040d91a08082040c082da9841080040c035104c80d250b00954101d8440c02000d8034190b5140319035509956211320030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 368264217 1250 368262967 368262971
    0x10090906170c0d0b040b180109200607020a030602220308030114040209060306010f03020c011a03060609090601060e010e06030901020306041b20010b040504080406030f0b060406050c071503 83
    0x16003407002003040340601c0540300700c90502d0054800d130b41d48101040d020308020b0a01d05240c022030585045000080030002d50100200400c00c480d06107483c50030056100e10789101c2d402601c0000c2e0741030a1003280c85158000d0100060740d803440d41d40c40c00a60100b02100745001030f003500b4443c0c40300380040d810011409105016120750409180440c0c0c41c40344640240706910400812120f600c5480541c3d512680900f01080b40030b2210b13505401a120b182000c500e47e51038100b030b9444a2441c8600030081407802c0c3c0c21118030707542c1c000920600312429170319546154465001040414403515041520340c4040c9401100c0b03982d058040380700c42d0001d036058a8540d40200812540e8209031140d981c213242d071a001c886051010b080c002d40f1113100c4020003a500d00e014082503079840400d4000c07612000001d84100a18070341070800000e9600603000314000a03060000c407841441c19406507260b00d140003007941e40b5280c5801d1080d141a40215859849070049880008404a401c0701c1040782480365180 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 368265467 1250 368264217 368264249
    0x80a15080c12190b04050601060903020a03020108090c04020d060e0906060303071205090303070b070e1503070509040227030d0203031521120c1204030c0302062101060c0c0503190210090906 83
    0x11b1030411030f05030032003420000b0104040025965440344481247e40a080480c1d8949910b1106421302d49030035240c64105000103000e0410650b664050012244a501070500680340c174180e15450b404281d0b04140d169001f444060080748140300d1450130f9960031305145152124010120b821504a40425941d02901d20b00b0410229040b08142c4c50601080366581c09507480030701000498000900148100701020840300c42c00d031190342c11900700418060001040c40d40a48403001411040e80805000c3c1c00fa05961100751800001600d000f0425030007c1050b1035404010700006e070b4001200004061000c000c08205000d050181d1803821f140b1954581c6e554103001412072600c1004240900d4500b010803081022441c41002141902da0448031581d4684603410f52110400c0940c92001c00071310944000500310350000118441c843c412104901040e90791400c15440b81400f01c0140c814461362001d9000601c0c100c00045003e071284d040143e040c0b07031903054140803510f141d00021001405040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 368266717 1250 368265467 368265473
    0x1202010506010908060402090c1606060306150605030f04020904031e0e3a080c0708160e04080a110f010e06010f0f23040615080a15080c12190b04 64
    0x3c002d00c09088510000c0c601d0f81403541c0400d611000090030708560410100300c0c00300008001c0c01c0d0008054105805202c40c40e2603051200003010a1121120001c40602000a40c58000c0c01541e00c9402c0c0010440700070b54880e02070104008008008400f044130101f146515001e110341d120100340780c680c0c0c909070410600c0043c4000a280c010301c0c000c402c007200502440c02c2c103401d034002d040c40c081980c00c5440181c3c80d2801c403c00c1e0245524507516070098000c041500400080c003503e48004400000f6007259851342580c043d60070130307207024119090170050194211701481d0302e0312119200c0300c116500c110440a00c00d084802000301d400f865003059004101e0710061640100150481c0501107844515180c2140b492051a00044021801d5a14070352100d83e1282e00c480d00908660040d040300307080300342005102c1a001c441840c0400d160442001c003035000380c4001d4065880c40401804240d1429082120400d82001402c01500c22080291407078511200e414000c030348555210754a600f000c0ca = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 368267967 1250 368266717 368266727
    0x120601030506192603040303020d021c0e100905150408010e010e0d181e03021c02011d19080102090a060f0f260108100609050f0a0506010c120201050601 67
    0x15080c070b40b040982c1a250f050050b0502a20000c4550020740e04a0a03070014489081c0c0e8114041401d003a40404203000052540102c0c29080714803003075080d0b80b10342140c0001c120102c0159110302d00054007030705000040342070103000403000c0303580c50610b600915a55000140c6c0440400000014254082010001000709001d81c880c4800010002e008a04079070030603950f12101600080100700e4207041d0000d0103804409034030702034074040d01101202000c01c10a021609982e20040b070003901c0d82d0034403208240c0c0c140b8900c100181d0580d50010740c25901c040540301c0c0c078030042440742d002902004080d40c00f600a44108002d10b851800580c0740c9a2131820804480c000f584600c090013241107006c0982c5501c803800b090305600c0e5080070131814012005038000740c4805803041098004410001c9240c3c0c1002403000d149400c4180f00703101c020f854010a605469054594000302c140801c041200c0700150303080180e00141c10714100d504c800a039211280c4a03511442c0c1080580d6654044c00b4007941e0103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 368269217 1250 368267967 368267971
    0x1e0c0a020316061206050904060c050f1303030e0306040c05010503062806030b03030309100c090503300c060c07050111040e0910090503070b040309050307061725030207020d081206010305 82
    0x4d080c0820400e03141c031000c2103c04038003e00081071255160554208a4060301c281d40c02c11040d1f104031358560140000807016044903003c10b402003183c09800c00c466140000f0254413666111200e500454500b80c010340b0b66800140040782c5c8400304446600d4502e500c100030015502d03140e4004d070b4005240200c007a00311101850303264041d80080003007182015001032802c4011341941d00004900f8003d4000303c9076001c207034100a900d030040c0410b641c07103030380310701002d0201d40c0085030341c40728561051507540d000e44200c020005e002e030058070002d05240d03441000b0b040c10780d000e0000490304058004442106a0181d04004100e480348410310040c07d404010840c0ea14100c51810041c0c80159210241c1d00d0245800c01807402c0036620000e410507109001c80300090402400b21810f03641c650703502400144252040c00c0d420303104540001c00c00300302c2e4040c882821040f43e0b036480002060a070110007945c030410301643c10507400c600340c0000581d03a20003450344410040d201c0859040c030701e00049c207490300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 368270467 1250 368269217 368269247
    0x9030706200a03020d0c0512070f030f110d0e011505010c2d050d0810030209040f020a0b0702030c040c0f05070305090a03030909053303010e0123010b1e0c0a02031606 73
    0x424410232000d40301c00da96030386e0800c0381800d07c00d0190b407070100c0440c0605803100fa00d011003403c01418a8610411002500d08070158080900200364401d0040b401c80d00010107042c40e50325a114100219402040800142c9002d010010020a051801c00141030031018051510709113203210101804020b00120045201a10b0f1107481801c20074901c15070720209002c0030380300c1c3c20144085030422000e50540c000d2940c0c0504079006869903840c1a10040d080003070141e0080c081d0404c0501c031868580305030049203c458032414000c1e030341d411080b03030340740c01c400421810f01c6400c10241581e0754030010054004c6110382c0d14920300354200b80380d6200350b8801800600c91508101901a5544a00044040c050301e2079030801c0b202c0300c0c0e0000082c0c0581a02c46102400d1b501c2c0110788071080703c1210311803130202c60303c600898059a8854440729a44039008404107140211000d400a62034407100808005201d4000ca401a00300303900000d003410800d0f40060541041e248003084030310742049481240201c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 368271717 1250 368270467 368270477
    0x170106090302120307050601090e10050c1c05040816030917070312030c0807141608030a05060a0b18041b0305090f010c052203080d09020a050909030706200a03020d0c 73
    0x71a6640c01c7d070355040c18010b505519848a004801d0600300700720080d21000890410310003402c0c45841f03804140d01003410703402c5071040045021030b00b00d558011030b4061503224900c94940500140800123141d0070034021801c11011100c00141101040ca60ba4003078000b1707102501501d80348d4a8000851070060714060f050605050240b49040e030404240781e44a0780d6400e02c0318003c2c880000d07005151180381251402000103120380010302c00606c019520501c0002c00401580c1c984800700304110b2954464039202c0301c0d040001c1400b40c00f4025207e03010b2240544046402c1c0f160b0030380320504100103181d66001a560310200041c60b50100b00c40c003405031003080200402c941d280b0000b096403241c0c02070b004101503440056800c1a851580500065400001940c1c83c3c45080c4219006403c2085040e0305c5600e42c0d010215403480c00c05001801030144000542c5010075640d03901029056030b00c42410b40c40b0f0440389111020400038010603002a4940d00140c0e1078a000010030304460b10301e03400f101048 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 368272967 1250 368271717 368271727
    0x806150a0521031e0301080c040510030f052107020103140105033a050403030207050108070503041b150908121306140d02070b04030e01030b1c031701060903021203 72
    0x1850711503069498842e412620010380d01070030304151035481285000401d00558030369180202d2101070241d4166116101900c030b9045a60b002c1100383c51060318142d0382542107003000c10005070f291101001c180e00c20030544280000146a181001418a0b4850a100000a03440c011980c1c10300c1146079002d000700804145504060219030307030304092040614a4002d1200c204d03080090400e05040052a403a240c01c041440c494005255070003a110403000740c480c0d207401140c15030140203124840c4405a075528210759580d180c070000840310786d002e9221036941681c04a20b02024205005500446481d1840c1d0240f5010555240030520340c4119115a0180044402a869085c0d40300071a807070303854201145902103500500520620340f4070a0001c0c40040c0c10b10070482310144052049000e038492403402c034120001941916035100088e40c1c80a11055030700f0020400070300701c265643c064588055494200007041c40c849000380c100c42d01181041000f0800c42ca04800003410384c0305194043c500344 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 368274217 1250 368272967 368272969
    0x30602040618060f030905070e04080c10020421020d1506080d020705030606190f08060717070e0603100b0301030807050d0f120c0c051b1c080d02030606070c0806150a05 74
    0xd0142d8134071610070141c44100710024000e041140c0c0000e0b20340d041e1801e9241c00c007407808400380c6d80804816445030007040310f103941c02c841d10f00c240c8080750407031001030200d40404100c05100001c0c011040303034041c003030b0315000001c1342605020142d0b1407000c001c001451824044600d01c2e0181c0260020210b501c1064203001a840114030381c1c0d003103441500c00d41c051050480100b002e10b101908003d5014000c100001020500020054019029030703d0700108038019880030454444102c0300f880200d00c410041b039801e030900900075644030152003038031002c0c152145160103c0364000c0c1d0095410a1000c00d13010b00b403003414003540307440d1045405d19400d400c00651025040303c0c800b01002850a80d1030840c0d82401d40107054440e180d551080651f11500071021912183d0404811214001d098035500c000d0369560b00881c84840c241c08c03025047c03e00143c1401400a1750006105980060b0180316a41c00503101c4a240b1700a0004040a40b03075a00d84805c4007003850300c00f10743c0c1d94410440341d13200b0449 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 368275467 1250 368274217 368274227
    0xe04020d1b0908012706110c06040320150a0e0a1103010e03130e040501091403180303031b0f0c0d020604120306050f01050328090201020610030812071803060204061806 74
    0xa0803170b564000d031141d0099401d010005142c622940707070900500017082c105290010809034800d902c25141c0c903440d0340d01c0303115401c6840c00181288410354072410420020340889505203030f004203002400300ba4405140312044c2451940c0d903044580d9500f1000910041c81d00780108042d05281200a5041c084212440281c4c01d04611071040e00043c804c01050500c402034104982640d00111805050a083c60000d03036294084402d103203012031440142e403994074001c000c41e03008243d03540326a641103010100d4451150311003642988520340421107005115014405183d141c40700740c0140c4120301c1d281c204041c800401c00303a0350040500c0e1440c103000700e40c0c03446082c00c21a8030a181c86900d036900c081c1e00c940a010115070b4404020307440e0794000040212074022142d024800c2e03013982d0003902c035020044d01c00407a40c00001c2c1306860600462aa240b90341c0b01c82c1e9800700d003503d0940000009074600d451b0641958100350741c9960000340c04e1010903004681091a401142002d082040c0b505000070303d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 368276717 1250 368275467 368275511
    0x70c0b0f03041e080310051c0803060f0117100e0108010506010c060b0105070f0c05030c0102010b0901060311070c031b080c030601030816080409061706070f0e04020d1b090801 77
    0x210f0001e034502014500c0c41903802c0d0048442d0700c444002d58a080841000088902910410b80714260744103608602c17010200350049a2580042520705540f00c1ca0200041e510802421031704010b41c50861000c2c50507a4a42d142c001c500c580030f880c0b8800d0600c4800b6503c004140c020740d000c0d0381880240f01d0981d9005c0000080240c2045000420805880040302c45128004e000341174121422404800d1012800c9441d040769011011203540c2c010361401079017070f901082c0510340d01001e0b007001040352600941104494562880340d40b031078408545d40d44c1103d803200380c0054410381c0f00303443d103135107038001c4a42c2d036001a20340d400091100030855800683d0300c4405000051243c000444e58003511880c264060754005c0d48111800e0302e40340c98104400007002148940d505075030f402c0d000529042c801042c001e010382000d5840030126000c407607094807204600c1350308a40042d8200b0140d801040140710b11110070000c03510040200c0d01c0f2540041081d146900a0442d03030f4500100828004141c5450f40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 368277967 1250 368276717 368276723
    0x8090a05221d0d03060608330f0d03080402090601090b18030313080c040501060e06070b1b030403020d0e19090510030812011a0913050406150605070c0b0f0304 70
    0x310b903030400d4040707101514000c0c82d80344201d031040c5500d403005150103070007000c00d603001c503501d03804180e642500d0b04500b00642c0c03082c003264984041c0e80b210300c0c1c2d041c580402a0480e02400d0080030301c42c5c900100f46449140c8506800080d150001c2c082185084500d0f641c21901c24030700503da040c00d001c4030098038030030a40b8601014040d2503185c40d868038240155110380340c40007007000301541e8404003107855404c2c04c0b0450f84624607000001c200c031401003002050001c00030b005541000c009944100b84c0600c05010000c0741551840e58545142021000710b00c07480c800e602801031420800d2024045080c5003003000e100b0419110f14560305015810795008864640e840401c1c0b94540c56076203050514113820280c181800081c2c00e140d4102c0d902010f90494040b03100c0c410303003201021880b84603030049031491139000303183d4508040d000c009900030540145c058a00000c0302050140420a140c40b00d92101c1e0200782d020414100b4840c8a03000000240821280b45151a00080e04400c0c1484010801 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 368279217 1250 368277967 368277971
    0xb07020d0516051510030c170c060f1201141e01080a180b0a05070909021c0b130e0f1e0c0d030c141b0118051302090d08090a0522 57
    0x43c42001c000101a07010702d07800810940c1001070f041268956280005c0e11a00700c52280007440001007001d110500c824a0090007220902c0005c21440f94001c540c034101400b0280811544c82c00310106040c02880201d0421010b108284180148074403510b00b40c0181c2403c541c0d01c0e000c40c0e600b0043d40d07a4007001c910f0000504240c94600e121003140c588074050100259001008001e6803164880340c003502440e2903e03070b110781d6920040005c4e0300c1f90302c1c44014450255942601007607015000100030010042c0500001c07007100c040c49045613901c0710020210340c0101160110203400740541d440340100d0155141d045038443c05041c1d915400b10342c11034010b44004240c10700749440361920359a40c0ea407204140c8000d003020500566543e00c1d054544860512180f07001c50a58000e9180e510400b842403d1640c5403031608013045402c0303503082c00d096001e0b40c08000e110042d5690020005007940b00b40300541cac0360390303583d000d2211884c1e1303540006020b0700d6041c4201244e00440d002c00031a50b01307481c0340 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 368280467 1250 368279217 368279257
    0x7020a150b090f1308030c04060207050a0305101d150720071403010e031207080106111504020a0902210907080307060e0c0405041a0f0613020708071b030b07020d05 72
    0x152021300110300308040d00300d4002000b8040705650050051048545641c21224641d4454042004c901001d210040455000305e011505080980d002005420014900451941c0402604d0740c00c5c0f0f591141c400d02d0300c071800307000c11414a400100100402105c1944600100725142000d59111224020482c6d0090b007200d500d0060b6400f504101440c18200701941d403034504c00e80210500e68007c0c0e07202008140407400226800e4070540d18800600e6003400242403c6d03040510351034810300064030590b00420081380c046040c4030580020b20703110110742604110200d200794214022440680f07454103e4000740700c01c10883c0e1000040e07444a0360400800034203c0011455a03180c0340640000b41e400a05050030042030100203c01038284100c0288099032039591442c103140e5244088540f20740c0069818081c40c0140b03040d6001d018440e201e45103031032130158a91211304804800403410880c41c501000c0c28070070020b2007441e545d0024054001461420b1500c50007501c00c0c098150900100d104240d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 368281717 1250 368280467 368280481
    0x360f010e0307110a050d0503040e070216150c0503130f05040c05071b0e04031214010620120c030408071409062e0509030705090c0409022107020a150b090f 68
    0x4c0b640006010091220340400301e5403800603200e070410310032042a542d03035000003006240003050032103250f824409410401030801312035100d4581940100800c01803244a880000b030404c2000703142c10691211101d81c02c0345803502c0b1042c05082d940016004034100b0305980c02d07194006054948647d407050500360480c2c1c60b02c282607003c00080e07000441200300403047c00203250708003c140c0c0f8060041401805800e45012f00d41000300000c2c41110001224207030740d1011140c031860341c8010303030b0700650940d07035040180300420000342c2195801212680000070108595601004400000c2c804802c6060000840d1000a1100240103000c20700500046032140641c28030a200c0c2603022140407401c00f181022100020010303000840186d0180c0700d42e840104103460241c0d075852041ca04800218902800e00030030034041c1d08520728454007803528080243c40d10403009411441850690300400300354005042c58000b105481040e8141c251503d0172a01d5541c4690780d0195000720305480348085511000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 368282967 1250 368281717 368281729
    0xd02070506030f250c0b01120c0b0307020c09040614070804030f080c1c060303110f0a020f03010e121c050105060306041104080d030b040e061e360f010e030711 70
    0x103c00114550030580c3c1c0b80010715000200340008900480d40c8135500c4c2c1e01c9850482c50522364650203010244207035002c0010700c0081c8019540450284155105481d4040104041910a80c2e080f1081500c07010080c209004c169441c6510403141d1070032030384505154401608061850300c1e0241000341800c001145412600c046602d42d060b00406090742e480164900320042015000840c0041e01448685034000c0001074100c070f4007961480501540c540960802000000c0444850307055500c4d0380342e0700b029030b100307211010341007600700000d60703490201d1462080c9800307040c5c140040043c54040140f040d0789334002600d600a50550700024001202003c2c0100b0b809107034031610b01d6101d031440340c60415034150002c040702e038800d40e400d0000004464105031180001c840355003402000740f600146500c034204c080e581001c1c8550250700243c06251107814032020032040c1c6040e044801d204040c25407400c1100c120b140031484d0080001c221508031942d120702c10404050250007141c40c22000c41d94480c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 368284217 1250 368282967 368283001
    0x120b0604030210020309010216150c0f0203010216030e01020307120c0507170309010e030c010804020d0c08060109020a12090203101116051501090b0f06070f06090c080d02070506030f 80
    0x100344800c80024180002d507170340d20030710580d070040c0103071103640c80c0f4480080c2e80c81061321003848001c0d840d04082c05044075426104581039440d15004e2401e800984c4085c4000d0074100c1b00f0740c01100061101d8103010b82800484842c15045600401030b00001c907258407150a500509480d01031645005820203900c0c00c0c240350082059001480034600e011800000105a21042030301c40740c43e0981300c0c0c01090b440342c00c1c804c05540411144400240103181007016a01d540c2d1003080e8910405407203d9055241c280260001655030f5400030b07016143c1900103045501e030310482c1600b40030107041c590100b521000b10700c08000d40c0310707144c4400000e100c55004c02d0720310700b030540b80032407001070783c00d0070850f5541d035803894004900010040040780f40021800365460980c0041d1000c02d441144a043c0201644031b00c0d0305035854000d940b80d01c400101c05018142c00d0902500c02c500d1200d041c9000c441c03d1840f042c2400f4190f501103e0204504c4d143e1030152644600582101d401c41d81d5117000001d410210 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 368285467 1250 368284217 368284219
    0x30402010f0c1208191104090216060e01050a0506030c130b040612080301031a0f06060904060302040504060501050a09020a0804020609030c1002071a070f0b040302161d16120b06040302 81
    0x1d140e10034041541d000c40814032a1980340e0035003140b02d58104103c5d01701c6124242d103041100e402c10041c40b01c1c030310680090031801d0100c5002c01d0002101c3e1114021120040400315407a5100e005000308203007240181034100300110040e00000304000001210f203e2074a445580e802e450344824038a42e91aa40300788010401c51225000d8848207151481d0564400d000032a10306d0f00003c5220300c0e038001020258426000f48011001c00c1d11200b0822555402521007694016150200400140c07070720300996020b1480381e5404506075060204000403412030390440140c840c414407540c60699400000329402c281c060b00d119640d05208008030f400c0c9505c0310902900700c10b203e0f03132040b10150b0024102046444c68002420680000c1c054420301d80300b8450094203101c1d0b04072450f00496051010660080d1003801151700071002d16005031036408080d030064100302da00c0710400254100c2c6002c3c1c164032110300c022115440d41e150360083c100900140e405403086644038951101920343c1e0381100c0240d90 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 368286717 1250 368285467 368285483
    0x91203080601030230150307121b060f120209100309022b0606060201060f0905070207150207091a092403010f061d07120e030405040207060504021c0503030402010f0c 73
    0x64044251320b011076007000d0000205000400030b1206031b513440010900746c10041c06001d445192070210700003418150026152198020000d950742c500a20f034007401026291102c040800740464080c004038480005102940d00401041f05c043d611304d800e00c07007503000d40e0a0000b0b0801141c00031503064544440d00403154044402010200c0f1172465002c682103119071002c0c0718254458004900740c0310310b40718680b003c043d00c2105100b02c6000381c1080d80d1048041c41101c00850341e900718490b080e10584c2c41103000d80c1000c07105110041940c069407106000e20098581d542c16020f000c201034204c000c1c03800701c0644c00c5807a48154128080c54135284c0362001402403201e2200141000024800c4d8400e5051450712031980c08081514181024450310440e281c0001c0e010350f54080d04054050f912100103240000c00000c82d0036034075072004e00350b403500980d8005028941481071102c820700080c0b001c0388081300c8401820004000008403507005a081c6411091000784800039201904e2075040100100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 368287967 1250 368286717 368286757
    0x50112090b0c1b03040303090b07290105120f0706140c0a031e0c030c2607050601150206150d06060306020c010c0801091416020309030a0b0f06010912030806010302 72
    0x100c02c04001d010b061040e40901040d665040c00da007662807003140f0000300411800c0b1403c00030340c4e03111000b0344046801050070440c40c441011036030202c0e0790b001c0ca01215000d03c000c014080360034030980440b204a20080200424420441e489550710303414442c44041244404108200108000a80d07410030410012035442c03140d24a40a45004113040f00040040e0784100c1041e601ca100c0c01c03098100c150140c807040e01001054903010b8201025145144440c6c204202c614028184c940051581a0240c0040c1101e0f5041482201d19088181c229a0855000d1000d203c0081c1040d41c004001000c1100c1e16103203541680307040300180030982d1020702407502c00310b102c0da0310340c00c1904035802902d40d070740d44e11000340c0c0c0b01d000c501d00700e5081c0790404c3ea01c510302000151070100d0141c03030880c804110740112400c00203407034000384c90441c0da00700c1168104504400d1207241c003118a0540d03080352090074182e0706181841303000e0820502c200005010009903502041c1d482e4040e81c101c40342000d090b49514000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 368289217 1250 368287967 368287981
    0x12a0c0c090902190e270f0303250824090916060f0c020909010e01020a1d0f1e12010614031203012103050c010c0801170109050601050112090b 63
    0x41450034820f0303000c0d200300d800c103050a01c91802c9140980c3c4001c44807800c181c43c1e10428169054940c1103c0103e00d245001d00c00b41203004002c160305018190004558030b290030303102030320401c0c6039107607030b1012807107605001241a4102c111594444610752025038800700302c4003811076aa091510720740d00705540009100c04c12902007038510121007050900b004107907403460212540d0600004400c00580080c2d5040c0040c60070307800590300000300900200d07a008000e00c005003246c1c0910340200104034440b032144000030341e900444d4000170080342e40204808003600410f0b01c3d42961080b89660010354817624403a0b40c1d0303513004036040c0f0032498020010300e900c40c441e80c8200307164100d04522031f10641d4000012740203018101d2303040e102c100c00c0d506160700030750500a07400c0c2d140c01d80440c1407150511a50702c80c0d92092285013040907482d55404029403414160780300810781032a45124590500992902140002801a04507072080c64110045404808060b00529110000030140d8600000f84109 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 368290467 1250 368289217 368289221
    0x1504030f03050c0105090601180e03090a24050306090c1605070f080c06070c060c020303040306180b0603060402010f081b03010312030e030a0804021e03060403020109050f012a0c0c09 80
    0x103d03440200200519241c0340c2c05181c1e42c01007485004241280d4410002022400d504402189803103002105e081440c1d03200004d47c4106903422107045024000b004c00c081c1303c10075801c0f8a0313145280c203145181d800c0002c041005031000a040c05141040040c0165503410307030004012086400000755110340ea154034241104070b0191242c400c140c4603d0140821500d400c030102c5102d540c2c4050503000c021701d4020240c603000344d60350051780e060205010000108200e402a00550f00155050441c1021249040d046070780b809003a0034005d5020508100060341c001c0e140325005005401c004036655140300c0c21050004010a0300d200440b80400008108100f08040c07580701d0b15036071001d00803986840426581c0703000712008840000e031018041809070525a59071000a41d4402040c0000000780303011a1409400343c0c0c084006039510414007091013000d0050032a01c2c1400c20090040f0000c00c0c01c1c00d01c0c100b020107000c0343e40c180c0813288030a1090007691245502980100441e924035500d00c40310700 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 368291717 1250 368290467 368290477
    0x3010203090606132a0212040305030a0f03020a0507020405150d05010209031207120f0903020d0f02030d051c1a2d04140c1c111e0901020601051504030f0305 69
    0xc0140c000504181075046903000d01500d810000000800300d80345140a908507480b59817004c4c095014400b01d64000c1c850b007900600156000340b00841e61841c182d140203004c101041c009004261050200c1c1400561002c100c840160701110045156100e8041c4404000f400b180f4141e480700304445040200041900074041d000780c114161441b0b00c201c002e00414030f1285c440002d102e86c40c0c3c0713842c2c03146550080d5205224845185407810101d40c41c0e501048050a20f4001626000410f46880046140800400783c508d2810f107442410442c400051002d142c0d03524006184e465140d01c03c1d0b21405420640101f0010303002451440324814502006002070302141a90001e00300c80c0d01d6040041c102401240d01c45100c010000495a89030001c510890300401d1030303041e20103041084c1d8020b848503030152074025422500d55a5071405201b118054040001c034280c00003d4090002d0100e03603801080c03c0d03044413000d0741c80c44d01ea1a21803c02c25940e11550304010b054140f11602241490f6000d40500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 368292967 1250 368291717 368291719
    0xf051306060803183303041202070f06052b050105030d080f011719110102010c03090807060203100f030302010506010f0e1e010c150506040c08130f02060903010203090606 75
    0xa95a1602c009070744034440c025195846030b5065250914900300712101222120704100c1e1264550003104403010015603403500c000c410080401031109001c1446920038941a084c002030102926086848280c01020300c01d48003404008a8201d58070030b414481303284e1048240211521000c840821000204401c0c0a0300d802403141b22540902e150003980f946000c1d2580010b402070980c070301485210300c8856044240c01314003c6081e800c01e1100248a090b44561240c00c0040b5400041c000082c01c403081d02406604142c108444000400d42400c1282c0040f03800c0403001da6a0365480b403001c466003c2561008080d80c050750b100100b81035065000e20301070f038000d03a0399461415030f62070120313000780201a41941c051140c00d815100c085c400100c0006e00801030503e044901e0f41c81c1c450008154450030398440703490301c0d00700300f1215240902c41c0a80d0240c41c2d092102d070078103088041002030100c5580043c1510124403406065690b26002c0d40c80382040200255941d2600f032121944602050f2542 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 368294217 1250 368292967 368292971
    0xc0e0307180c051204060903110307050a021c08070b060d21030501050f090f0a110a020106080705091e06010504030b0a0f050c0c0c060d14012d050a05010309060f051306 74
    0x782c64141c1c46082120070314404808540c01c00e440c0e6484600003446000070440602032041442071178007400380007520b0030310300070005030900c602240180540190410608450250124003070400034131000291031009408ca801c2207c20754800000c02c805480a0a01800c0004404020014468928030003074030071109a400340800e0b665941030100206c0000d0346d035070380210780100003a000d4903480803480c3e2040142030701007009000f03084450030350782c8400b40e640011b075101c403400d000540c0200568001004141c41030b411601e4802e0007215152804424040c004044c4400304136681e100c0c02c241c03005140c101c440780740d090401d0b80800c07008014010350210060300301030004400310f0026007079650100f24600507000ea50b003410100815079010030301c0000f105585551259100e141005514041d11b08084070307100b01d240300c0101800100c40b01031240b9440740c6c915001e01080d2102c1899038100c8000382400324041c83c543c42c25501400c0f03250717203071b842d4180707404104500315440b004400407040c054681 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 368295467 1250 368294217 368294231
    0x12220821101a03070905040b010909060b090909060603030702012001020301140f0d0809130612030309140a0309060507080d0c0905010e030c030c121009050d0e09060d0201030c0e030718 81
    0x981450f40401c403245804500706980400c003d04142c2c000d01800c901c1494504001c0d0b450306140b02c122802030708450301c02080071aa02400d07040c41d0030880c2e0440300c401e000342014581280025540d12031000003d040191009203400b0744555410700300303840f40d1810000d540b29a1142c4103000c010880070100c80c450140c2090940c1c0509010790511407040c0c00840b2107203042c0c988002d00c400810030850310321110369035810000e814031300006c42078000c034829039000c04d4405c05c2d410048801040c00031304403200c1d0044045140025000b003110780407914142440c0340c940b9454101441d041c0160b661580b500e50400ca4000d200e16804803d00090750300c2620b400e00b2002c2c416040c0356413200ca89c00b181e40c155000d003c1c59507181c60300302c0402803a421408100c03000080e69214010507a0380000007101c007640000c1907060055004560ba80d8007110640d0051101d1510a00160441c5913005003e0f05240e5a6078502210610072140c011010001404503848945c2c0c0d0f1108034090104a1140c4003000d01d4060 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 368296717 1250 368295467 368295509
    0x30210111611010e060c0a0b060916030c0309050a031707030218062805091c2319030503060307090b06040303030c231222082110 57
    0x780e0388070038008034035488a44026500d41c850b031001c140c10b840c10b01040014800c003d550301d01c010003182c100c80000d400022014039200090500207071041d8410421802001f400c00c484000310b00000b201490045005c4035082000c2c0d0040c007000402400310700801c88200c05241d0404141011201910341c038840c541d51b455011822405500362451030002d601c4084401840d203c8058121260f030144240222048044089055031642c90788201040e00860f81e00c00602c3c200d45e10522214411100320f080c82c00d1551030320361110366050140721001c200c2401740380c0c0000401003401070024548180c00e1543c0313036040c00b03401500300301c1c1ca5034801e01c50420041035041e4203000d074451102028117113031700b807500f10f03981580582520f2200300c0030000b80f1292100b040c2d052020301c000203607108030300c3c5503a1030044000310000318009048921820b05a45600344805e942c500d011011030308402120340707502040503844401402c919400c01c0c121062030078440381d26010b0b100181114151078416a1440c8055 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 368297967 1250 368296717 368296751
    0x40e09060612120702011107170d031b050319061a070605090304030f0305030c0d02030c0904240b090f0303030a0b091503072c1f080601050d060c1209030210 69
    0x815800064002840000015400303007005407c107080710780c240c0f840192244940400c601c00d5405c140d06582c045080c0c220025018440c910201180340241e0300e1b940005a800390a40c4409482440b200309012080b41400c4001c3e80420060048000740c2c0c6400e0420401c0c5c09100d401003082510801c0c91300010810a080c000200c43c2229880300c2c1280c5441c04a4405440c1600700400f247c095a004018402410155100840c0320b400250301403611985504103005c21503481c2d080e4000d111608220510351404440130200c12101072146207541c0b001c443d0041211220b1447c0003513014880170040c44102506904a001e1408081d202030b40f45a54413841401c100507482e09240d0560040082403042c0740015184403c0c0409444050507070100c241c59045070204119203003d8820b840401d038102100b0500e040c20000c20301c0c54010700c0a541050300013105c440010740700030321880e40c403081519201e0050b02c07624507581011404002480160401030b403200d00d0304d48204080c6140c140701c03c01c608452 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 368299217 1250 368297967 368297983
    0x612050105030703120210150f0501030903080c0f09040608031210120305030604060e3606060f0d05030a051c0c080a09031808100b2e0302040e09060612 67
    0xd004000c503d1031360320707485024443d1034810f44c21402403517001d21030b00c041c900511000700403180f9141090340ca0280080e03104501c3d600314504041c14203401e05e0100b50300c1501c2c2500401035a0400c5e075102c0d040d1071101d2080c861080c0d2107402c2414500700055412000c809407094054284100e05a50345086d4081e05500c0d05e8003458616204440300301c00401d1140018580c0490041c100107003007900d031141c409011800303c40c01040e02c00509480381d4900741c0b01d0b001c2c12508848100e1b1030240c1046070103042d01d50400401d4103008003241c8a10008956421141140e40354102c0e041d01d550721340e1904014400c3d400112a440c903540c100320b40e820007003030600c1071501081c800e1382da000c4640c40700280b040c00341400c01003c0e0100041c3d0b1603060b290b4520326986034014141c030030042c5210820f44030110291511030984510601920017000301c50102c1004005941d5000c06d15142c102580000c103400074000c9401c0552072280300c00c1042032100c070000700e207800341c042240c1142c0f0035007003840403940d00c0c404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 368300467 1250 368299217 368299219
    0xa05060a0504060302131a090103150501021f15170f07030c03110d0215090306130b0103080c07080610060e030604030e0d06110c0d080c0c0a080f13090203010612050105 74
    0x3000200491442540038004100800502103607440c0d440c81a02c47c014031110442e20300d00c00001d4860700f150781500c500c1840241c910000c03648075117481c0c0082d45030541c2c3c280c01d0300031010214007442502144d40c40080d0240d07c2c44c0d41c404441d500c0d4074210f9245d00b4096034000c0644603240c0e061100000014100003100d51049029500390b06681d00c0183c0d0444a048558100e006840964010ba550f00014248003d0400d2959201c0e00303230104042c98203002400d400b1a0054465330540030402c03804a49044d243c000c004a6541d004a1104500d00407040e4007850300c5000301003d0000b100000341d80d0804541d07982d56440b11503c49042055141c42e07050301c0050204203140000001c44c2080f0400c00da01601a001c000740c0700c007000c4207032103041d4080d40d01020b1a4021321010200d82c5e401190454112030131082c110300303002404420694802c030b1400094028000400c88075110308540049440c5941d550329260040340c1d69101c0e440c040d4000f8080d00c07010403e03031220306540004520441e41207401c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 368301717 1250 368300467 368300477
    0x13020111010e12070809090f0a060504060807030305070807060e07170d0f110a020607060f20030c070c030206070507080618030d02301611060a0b030c030d05090a05060a 74
    0x1400c01c801c0e8086902010044900c084140007aa00c80d5589412451248c3d0023440c0c40d041c68901400d0b00011691307142c20180c4103600c3c0c00c000f0b02800d00700141030000d0300c0e40360138143d96a003441d0908510b80d0160300b4004040505103641940502000f01c1d100301110456a41c418034103590001450f00d5651045018001038441103040400f2031190003a125070703041c0c910580d90088460307000b044c03040d84000c0c01640c00c5a101e82c95407031105050700c11880f1403c1d5482003840c51078404800380034644409005032100300808902b40061000c070103034120013107900503d52580d0301c45034902079844940c60f100f000c10074050000002c04885d601825400780e2030108014514101c1e0786248100250847c101d00950848221034031900a404108000d440e01c999035844125407400e004800002c1006150100420040068000c012840001d07151380016080300c3c081080900d0b800801e1a083c00e4584c2561305114299841030003503042001401107180c00d036040a01030340c40b2800c2c40f6980c0702c0d0008101c00170b8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 368302967 1250 368301717 368301733
    0x609060d0b130c0f390c0f0303080703021c02040e040c0f08100f32070201060b0702091e0c180d1a0a0209100503010602101e020a0e040513020111010e 66
    0x161140031080c401c0e0781541550801401000100441811706640301c0c5003c40049860030140304101c2a50790040c00b4244602401505643d4000c3c05100007400709414107030040f1302c0a00d2050540c007c0c3c0301400c0400c0c030841d103e41d928103026020403419281a200c400c42c1c5200850b105001040610945040100520004c211480580014002400480c02441d42e905080c14180742c81d0036100904904101030000744507440c144032100c0d42c405003070701056a250060404c812619481565001601160280700c250340e00f03018100100c2c4514249100c01a900d02040300b542c0307610015040344110506501c4020001c64107101600c6100c140140441c55151907240034410501d070343c0c503800302c8811300250810035a08081450300324803a1420010071004401400400c0e8108203072101248510b0040c031101d102810996200f1045199900e0354136000110326526900a035041c880d500c0000d0410441440c0c00710301081119007000e0300b04d000070b20742510400e04802c14060b24090500a5018007442 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 368304217 1250 368302967 368302997
    0xc12131b06030b042f09030a0c18021905091909021909030b0f180d05041809110f03012a0809030304080919091d1c02030313020609060d0b130c 63
    0x2040170101149a00d900030031555502c1d4a0610011107090b10a206445011b4141030441c0060644124031101651040c13100781505900c120051401100f2410a55a11803114000c10413485031301015402c030315501040051134445582c0100f03241e401e02d021064200c4e08040040301e04c02030911014140c44500b0010900111103200e6203a04040086085400c10800f2881d045c2000c16140900020a10100b800c010418080100c00d40480301d0400c1041881c27140e5641c81610085403224134010140c410301c0d0825502c00b54410491008c5005102520911114056030380b0340780c90100c000094644800314801c01000401d490250798003080302804c0008000a12051106001104080030381c0108001421591480b644144c0382e44035106201d044030307039a4914a07101c1c1070340c40c03034102c00d5035001400b080503800300c03c0d250449054503001c03003060841d00020320b0380e00501c000c047c1d12500c00502464034816540c03043d010010195051096000e800c0c03010740c03c07200071401310b001080800e0b40040c0c00e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 368305467 1250 368304217 368304281
    0x70b07080f16290a060803070b090c030118021003050c0d020702030307080307030203160504120b131a010f050411030105010f12050a060501080c030c12131b06030b04 73
    0x41540000d400407001c61142d1070700d040c00d1405403e6000d0a0150041c0c00e81040005081c140d4481101201400702605d0700f60016601d100d5444041c020301030303440c04200413100038080ba20b0b21440c02402440b601400303044100014400356400c038440c90064482118041c00b9000b6188950504101541006087d030160340c060740c0080310887c1d00d03010400800740083c5812006d035005101c1c540e00181c0381d05e4441a006800d403203812060301880030034002000f028060101070b041080d489100750850b40c503100c001942d40035000d04000d00000060840303150740c0c0320b0720407058101c502c00b503d0801065540c006110842d40c052a03c03c0300b0500c204018081075000301a09011141d4900d410041030304d40156100c01c031a001e03101c0100d00d54070741c40100019070b07101d00c0107504409040300c3c1e00d00e5424410842e14292080364001c003076403c1890001504500300035074204100d600a4100c0814070503024140d480d03901d66010308030200345000d071001401d00b018131540509003004100324840741911701c2440c0c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 368306717 1250 368305467 368305477
    0x90601050a06111f020403110103060302090c090301270302060708060d02090c1b071406190f020312070201050612011503020913080c01050717130f020402070812060102070b07080f 79
    0x70354821400088203240b0a031400d44880040d413100142c031103041d4a0464401d090310039445042508082052000d40c2c0c2d500002e54118104203041607850642d403000c00e000d4144d241440c0d44040f102000e00d58800d800b000c640105074460390940c1c5881ea2001c00561309088280c81d601e41140941c0010401400c0001c0c03031642118404038a9402c20310400d0118402d160708107201d1600e60002c000410100c003809032070480305181110a1810102d5096503242c481c2c00c1c00d00c5400421401300071680d0350b01e0007407040f2005144c004520800e01c1c940302101038060300081d144c0900407050072150445118044c8101c51210324900c0c8010f002c1491a020004200400f4041f111400f00f0341884400051006008120010103d000850640ba102d540a0010300d4007805408000c01c0300d000b0444505108102201c489500601610184596001060007401940c00003406410b000954001e543c04205d040361140d4400d070f080307413402d50b200c03d0030030500e0255880c0100401800c0c400f60003d540060007500c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 368307967 1250 368306717 368306747
    0x50708040b1801030e03070308130c150302041d010825050613030605010509100308071a13051c17040609050726030a1d03070e010617090601050a06 65
    0x90506403156042074240d80a072200140455400008485550f09401180981003426010b141040700c9503c010708400401040c0700b0141113a004904d04110f0903806400c0074142c0b4080d1074024801566000d40254018005c2c4a004540d4441520340d030b500d00c0c803110341600c03030000280c01941890b0042c480c01c400703d0704d201214841075940c085030350b0b154800070f0003920049003c3c1c12141c2d840c505060007100d0f410b030805400340e8104410408041070500060003126800701c00c4503a03076883d50a0005030125885802c0a4010101d03043c480400c42c0150a04d0609000c2c4060f14100e11403984000e003580c42c65100c6c98041064140040700090301c003292164081d0191a003c11950110395030305090114581050f00c82c0c0241c01c8581034082541c2109926104030300009524090310660302030700080c00007000d074000303016030244e40c00036841c01d0100a00804200d00380f400c0f15611010301620070110041c9803020245082c0004040d080c0010300b40d41203da029181c201304034109101107446600c0c118280b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 368309217 1250 368307967 368307983
    0x1050a02091e0d050d0c1401021305011b170a0206070804031e020a08030901022a03030408090d06050901020a0f051215060f0a091401020a050c0f0d05010204150806010801060c030507 80
    0x3030020a41c244142d00d1801c0450b500d04d20686c81c81e240c00005560743d600e040c41160b02c10301600c4052040038084c181070342d4090800d14015200b055840303d1020002400401030041414400c580d10400c01c0500702c4201c4540903200c003075503500d204444500301203c020300007514010041034844000300001e80b12441c248190744080f000c60302c0300a4150f106440340314032a9800101e000008200c425120303d18030a441c00c8003030b8000701c5040e0941d01e010182016102400c0014001041e95451003800041d0b40d0140c0f01784460300d0503c0650f8000e400c00a420b101084850301074240c158842e00803182d440b200d00d003850049449540588070715020302e40310580c00c40d40030481660024804809803101c85011780d103c5e0100ca051003084060b040c40418101d05641c490801d000000d8008100c1e4030b03107114266241060424000001003040540c0000a401544005000304404451076059000c004041c2c65124890301e441c4011900b0850903c104000603501d0424035000901c079000508040e4010149 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 368310467 1250 368309217 368309239
    0x71709030708010e0307060b0303030106021b0d1a01090b04060302030a081b0708070f050901080c04053d1205060a0f020403020405010b1306110d050d0e0a0803040501050a02091e 78
    0x542c5086524100c40400c0b00d034008074907007003000018002c04c07054000c10b0700039604552400401954403850100390300000101c108190034951907041039491050740011542900c4200d11240340729181c800c1c06203a41c4541030030464021070070130340250400c41e50b000d0000c28554070240c4885c08030380c10400b44040c2050b42d1000d1700d0700017a4100406000b50480340c000c3c1c00c0041c03070300819a078105076a0b84814010300c604401004600804600949411026036022449688080d0600d0707401031000701008200021907010800803d1034100c0c0c1128220001c84a0616030300d0f00d2551500c02810031005110ba0b000a000680e20b8000d0380004101c2040c0060160800b42c40f54000b0301179407030907000030301d20002c0400c445820026045044c03005201c0ca05100c0403070500c40c10080d40340d02c00d01d0034080601030000303a600802c9019038072192040f0000380c1514500003c52504c640c0c1c03540192015a800d6080501048a940c540d00c2164403160008040c00c40d210b41203112084050b9210380f420781c0c40104495 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 368311717 1250 368310467 368310479
    0x6131704050919060e0f180c0916030617030403030c03120f020703171b07150203010b130f0608010608130203070603050709080a0b060d0507090903031a04020717090307 74
    0xa4030b075005074010079400d00c0c68203440c86581d04031035007640003c0a00301c0d41c0c0107000e440f003aa880d4003500f1104520381180c1d40c0790100c02e901e01e0a41ca40703035070030b4000c0080320810034040ca010f8844a500000b503a001d116190340d845a14440c441566420200780c0c00402c030401c002401009040d0000d442801d1400c8118402c3e400c030000c0b92416003641000c83d0300011100d08040d0701051405503040441c45110b503c0c1050660008144110407280710000310004e4440e060011000046c0008003e03242c1c195940d41e101c406c40d41c0c1b1500301c88120b401040b1b0725a000b20b504401e6020b21019506e2076510035049030b103000801c0b0395100c0003030168092a819841d4440c0980c505114800162000d41c41c04107032410400350080100441e5807002150340c002141c0341d0001409603c1b12030f00100222244815012641080c0d03080014951284004030b241400120405030036420580141801d460071b0104020590140816440740c150010403000345070803603a8055241e10081c180c2a20080c08880f1300742e032544 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 368312967 1250 368311717 368311729
    0x90a030c060503150d0b0105130b0d0c051206010b0901051810021501050d050303060402031e090601030b0a0605030613050309130204140402190e011b03030903020d020613170405 78
    0x24200758002032000040001841c2d040e01c12a4540307000780c0300c000100185485130500300030180103041c07007412600316520a140c180e401c4410741d010001d048030108034403440e2403c0400075034404e8502468000307d6503c0030110100b0315604035044801d80a1a25000d8401110075070700c420003491030908080380400e501c0d02c400718030707900126180e00141a040d8854180540008050340218030070781c803c40000000900220680f60041c3d01a82c0142c2c80e42c490003e900e40001c1d00c1034131403040507030780020894003043c0041d90a04a81c0100b07142da4460700d99414840584080740521501640070601046c481c0d0f0b5100e050b1711545009000b44e0341031680d200e0005081b50120400540883e030003081c180100304c40306c00c0c1c01c66501c800701c1e011881d000c01e06144c1c056802d401e00c1c1542c00d000c2041040d0078184d02428580720300000e09102a2100840f5150290007004601410780061103550421080b8900000e440b50040d0010707060032803a50801d039200801c00451800c401f0780010140400601c0d0f403508 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 368314217 1250 368312967 368312969
    0x150412080d020c03091318020d11120a1709090106080901060e070504060e1819090807030f0e030106060806060a0207091d19081801033e030405030f090a030c 69
    0x240040e40c0d0321071000080000d214000c8001200043c6032401072200fa80004010381c2020340e059271900b0754041c03541400c044d80020322100c0d581100c1d00300341c85060400302162040119102e584450780b081c0e440f03410013155000705100240c00c20031840c01400041d005451147d44014204004546c1507240e082440d490041074505802044d40814240810380d0042e04000440c50259404000e4564061041d211008007810084034800c0004599414410f150026003a854201952170303656041e92030003c10000100102400217001c018419109143c18024003049840750381c1d4000d4a92100300812405900c203c4d520b0302036100300c90700080c054095010307030004000305003042c0881501c1d000c0414142410b040c00d242900304d00d00c5907080043e108405a40a000d01c141e158411200790b41e005a0080414003080d0b2035243c0c80300325601c03108801d441c148108410001d4403041040030f022140e49a40400d6800901c260002d0100142c01000140030b40810503008100e40200d0fa600d0700c0320310b900d400c1c07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 368315467 1250 368314217 368314237
    0x1b0f0103110930062a0d11070b0906090703080906120405100c171b0c1f0c02030720010212130f0e2710020d0b0f150412080d02 56
    0x452840320500d080c9182c452164409001411351071500e0044103607080300044058003182010040d420020380381900f078484001c44640c0c20000410491500c2c0603035004070008890848255002414003400803901d540a85000c8005121140c10b5aa800507160410000e0381d4120009108182c0d11001400703807180981e008001030a009144000da540a50304040116410301c081183c2855811100c04180c50703110300c4c001c1d407a01444800c007140a52502c121a0380a849106070000b25641101646102050840d00720381000301c100030107010f03a01da0194610207041d4541d560400040070309a04171680c1e52110520507200820b800340c8003025250420740da03855031000410020710441d545812800d001e001c0c1248000014a0071081d02215602d149003001c40c07841c030440c402d40c2c5810080014941c410039014042d900c0e82c801d034031401c00520305440401c2c8507440450f003091041c203158a1303469000314055456443c0a040000010310642c0f00c103000c58002c0400c000b0900c19030b0492010b0841c41c02 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 368316717 1250 368315467 368315509
    0x151b040303050d110903061810051501031505060403110a080a051b010239042301050405040b0c030702150a0504110906030d031a030118051b0f01031109 67
    0xb1000f21640c08581411070307250104801044031196a0750001a86903006015010b03c0156114415500741048018400303140c0c0d10f414041032107020324405540900390385082e60704000902c1c1143d0202500740d182e108a0b6000303c400c2100344041002d0402140e80c90401800c0740843c81d98503c0014900070030310f842a50580c03c0200e00411000b501843c0c40790706942440280048041c10301c141002c1c0580d40020001f0156541180c429865403001640404000400400050003520101a45150303400c440750454072401d40042002d1038648603041c01603810020310b0846a89901c0a5081588081c00c98025441102100072101d4039080d491340c1b0542c10080003040c3c2d414245000101c13000f40400c0103100780b10600c2007111036140003070048516096803802080c0401c2c002d200c5071103900b2203201c2d240c05508204540c561880081200710f06948540708039a0040320b00c0407140c411500c0300c6190b540c8640007d00345003c0d503110340c0019400c9507034422030740d1074191144002010542e42d580e50081c500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 368317967 1250 368316717 368316727
    0x10b0306040b061e0f010e0d0218012c28090305071208090a02240c03070c170a03030f11030f1503010c120507140a0201051b0408151b04030305 63
    0x42060f0203413810708008241c00015101c01e54002406030345c00040c51504004401300300000360364440e50312408040c4c01805442c403030f20714502e5866a1303202c2400740d17942d40d01001541c0b0644c40004803880c2080c61850311540c000e030301c07079011581558402140001c40d08408012400300c071485440307403440d0b0301d00c0381c0c031030903900c0400b840e182c00f40c100004030b41e03010f020f02c0030100134013503401045591142e541120a10550303100c17210301c02c4054080d450b880e069140c001c6030440310001c0c0000105149401025070206c0540d40303c1e100c00c0700300501c1025524a400c55070140300003e019801c031401c2400310141c04900d1840840300740c416070b0001c03144011070800d040700740100d69191416018254100340c0083c40703240c072040c4000d0560318081050b1021384c1d60b201c0010710200c0c819049107500f40d041a50042d40c500b011180240a003400342c1d6441d00384d84890814101081c1c0352800c4508a84402000d4141c03084100c0c260031800800402c2c10a40b07107507000340030310406840c00040014602c240c907020348070307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 368319217 1250 368317967 368317969
    0x60f0b07061404050d03051801020c0c030106050312040923160320271f17130618020402040f08010609050603072706030b150d030806060a02010b0306040b06 69
    0xd6080164001c00e548544000e12000c0398010801c60780d00401e86c1400700b59501d621a481c200c2010340c11200615501c0801c40008915010605124821044000388070250306ca500709031b02d44115030403404440324100300c101700c40c1041e03400002981149003400200c143c00b000e69030051080403922820303048809010401c0150701803080c0009902b0040b160406441242104c400a110742c460110f5440000007280c1c5030308402c82600100000060450113a085a0110035814403140420000108100c00e1820007180701d440785241c403d00044d03040c110149a99100c0740c006003005010038101c4181c1082d20fa01507140c03800140010b00c1041900c5c00d05d20320300380380da81c219045030700070048460401c402d20800b07640025440054420503000a40e0f2201c11101198511202c8502c110410342002c00c00014056880e88c0366101b003112181e8824070b021020200b1000c4c1050003802000306d008200030466500b46000900381581d80740c0000030343c030500103000078078000b01100c046800e030281c48100096 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 368320467 1250 368319217 368319221
    0x406270209070807021b03010e0d090512060708060603070c02150c0d03060f1505120a020405010906021609050912120a15080a08070606050603041101141608070303060f0b0706 77
    0x302200300e00c3c01e0742c11400d1030400203442e8103c4400000c4c4900b4a01940452070390203602030071061000d4821103454540015026002c0c170300314810305210740d25085141024440200e41144030304071079500ca200664030380d400c1045542010340070340104000703c0500030058950042c10700e075503075003d000541c880f00000c084a10348940d4074450ac003014201402040b540c1400a100c0043d5214558a000c0480c10b0807001c4855000e6101b404508403900d2090001c41d43c0c059000303100340c500c01e9a660800e10344a110136a038409420709840c002e2910101d0400031100580d20141d08a5078160907030f02c42e40c50319812104ca940203800e81071200620710050282175001c61003000805a119034407a2081898204090740300e01d2624401f5040100018410040001c01d500000241100420341c9449041c18141180003a07107a007206404242c1e00040302101c04016001e91740d094010182c0c10018040c295030302005a001010304800741600c0d0301d004169005045450006410040d034043d44410345401c0c1041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 368321717 1250 368320467 368320471
    0x160506010f03021f170c0406090b0f07020d0201110a060516210c0509040e0a110109050a05010c060902060c060f07090605091207090203011e0504060605120406270209 73
    0x480740012030001c00040c0c44802201ca40c0c405400f140c0a2210740036103040c1c0e40c210b40401e8a13001103411108000b64a8600000b61086e03e4a0f5510a44095114244040180f150102b03d00c049030003440700e0801481c105903804505403041c5025140c0300192050a4500303000740c0402c403803142d04d413003c024050040103100f0003110501c1c03400300300304d1003c04866503000e00e49040241959031a40d00310350a8501800803030361040c00141c81085513502201403240c44e901c0204040318900399180269a803503204005038410761300010201c404040c80d000054621118002c8215a855103526002c4003507945c0d400a0b100107827000780600094600307060701c0c0849200081c07003032081c003882ea8018010507070303c0000d8800c0c0c1c0c0d00a81d81c20340307010078200c8000c0c645480340e80000007850000002150000b9407007003c0302c01c4071081c1c0b4511040398545003044103851503400f0b43c1c0c000403014081509511601c0490b02c0e0002c2c0503100000d030711540c004031000d8a9003001507814070380c92058458421400c29100c0d0607 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 368322967 1250 368321717 368321729
    0x204050c04031b0620070f15030e0a03121e0203040809210c010305190507050c1209060711060c0a0309030312050403020606011101060e160315080a02012316050601 72
    0x3c01d2a41400da02a101d45003030001102d4440c2c04041c45500d080040004d2800390149024059805550f5031019291403064030302000086c0c28240381440c1014006008a0400c0c0e15880c1c003142100040d00c5140106080490303102c3c801c1400b210038210b10110b200441c001e5006410700e0b9903d03048082404850804903040381000900009042003450002c00d500a4048007403802003040d450354540e40400030040d9010740f002500c3c0c401030110990700b2500a000c0c1108000c19148210612040340d0303001d028406080d81c014804201e0180005d02e15201c024144900601c1d26081c0501045c59619240e40140100c0120300c2c0007405000703142d003024001402103140d040501892400303640080d12841c001d4411030500010017a40c1000708429003255002e400600c01c1c00783d507454401c4031400010616580030010030300d0508040264180c500010041e035440e04002c28030428150b0044411451500440e11000e20380140b40100c120144001e02146501c0030030581110f04500740a8140f80c03060b4000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 368324217 1250 368322967 368323013
    0xb041401090509071b080712110c0f030a08250b010614030121150e0a0b01050d0c12060f090b070306081f02070804030b0c1e04060c0f0f0204050c0403 66
    0x10924507400605c4603d0710001601c0c031243d01402c0d142403903003030244d400000c1c8020495402051496404401045620070030001c680c06049100c00303100003034000b6081c190705504a0840340020074060001020710602ca814007031a0520142c00010202c085507108a42d00c0c1d840d80c004102680c0c1c4901000a900d440e94206861545401610f2510201d803e030b001c034040c1c00c00c008020500c8441c3c2081800400b07501c00c1132284140c0707078074029210300750702c0e104503540c1c2d101c2000403071182040c1140c28085644031724001c498906101c60700301428a2403000301c61254841c411004125054000d2a507887d00c24420380c202c0381400b0101078203441c61034208050383e07403006040c007404059419950340410200034005a45150b682000c1c408c5106940019184c02c0d800c2007881440c1001200034100203529840100c2c2c51001c18019144600c62480381c840041d18001c0900c0204d011086403080d50780c800d035081c4828000540c0410b003a10f07000c5811f80703011300300424200b040c40309805083c1e41030b000b90415 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 368325467 1250 368324217 368324221
    0x3030c05150c07031110021b01060b130608090a080415020c190902070f02030a030c1b06080414100c031a04020915090d0f0b0411040b10180b041401090509 68
    0x308030041c0140b0701c1c05400c1101c11003600004140510040c480210381b001c041d0742c1e861926281c0c0e1400305c0f00c1340500d01998a000400115500c00c0000e03924075402812450000900d4084211001e1202074040c059500030340316840d00043c1080700800082a005100f2540a07080d9040a42000d0700303007103000c1c0910b81030b4002100e0117a10720038038001e0301d02c0c44000585a00013400e00d02d000c83c460b0b500081d0140300b0380e92b0103002d05420a50b8070941d14400c070180c03601c80000000302000307403085119000c04030f0340d460003003000240c14605030700000500c0800c480d006140383e0406420b81e800b8014900200c0e03070390b0000c0c0a41541030041da40303007044c0c152010b51a118005001c1100501100340c1e400401001146240c59aa00c100b80d50740010342000c151807425420341000c19030210242e0b411500311001c03a02aa400707050500900c61200310050421021510366041603511035a0441041e81130718112101096944a06d00030f0030203003060140c0400500796500014140c4461608824841d42e40181 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 368326717 1250 368325467 368325481
    0x306060904030f02070f120209060d080412020609060a20030a120f1d160e0c03042a180509030909070c0c05100305061806011202090d0c03030c0515 65
    0x20098101da4503181001e048143c400c0c08908000c07190b00a03d810008070940000c1e61034103080030f80401030003100d00900ea619000104820580c2041d00108050400d01c4104000c02655151120890001d04820701e8140200001400340c0c4c0f05500c0000411442d05c49070b861012803c062150540132040158a0920b4144010300035600040422003041d4480092214810454025001d424205451010f000c100c05440c0b6445800385c2c4070070f04024081003000951700407041c0c44a4083e1440b00c804030729640b03e6440301032204c0c20b0503581c04c224214090b8032041e9034071075000c2c0200816807000c04c444240c0ca9101d008055810180062105610070304c01040c455480c0b000040d04211a0700703100300b40c19800c1c5003001620340d42c0d600c0294051550809192a0f94154102ca4030860048034004a001c0070042c01e110518802d40b06103001030210760b546040d0510950040103640c1c001003d40d00d200c6c80598503281d0041c0030303400440000e80303036264400410104100c1c00020b40c01d070510203803013407030411 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 368327967 1250 368326717 368326729
    0xc0607030c0e030a170c0a0c0611010b0109090c11070f031707230f0111091305160507060b060a020309130603080d0f0e070306060f09091a250806040b030606 69
    0x264025180799020a85902c003551700304100c40c0b40c01303107007410780e54045078500340040005014880c0e4004654440c0d0b51216000041c17080100001058545400d51030030003030020700a0038614036010038001219030300046150b04115080c018200c9440c030102d424251702e8071049569040d0921f00d00c0c41c105000000000d1003119251541030029001c50400e05280499185000003080b080740f8154603010392040b008004000404425000340c8036241c006003030038101c6044400803141249500e0706880100180d52042005184035409410013046410a50700000e049074444461140540d000181d0150749080803e194803841c030840b5803c0100ca843d503140c2064900c91808000806076a4154803410000141d20a00703440b0f6003207044445054036864500c009280d107002c1c25840b505075101c0010901054083d01c2800303503100441038985a6090411491140c01400d582400010742854004148914020509003010b0340e44100c0c860030410140404c4a038030000181c001e80059040052940700d034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 368329217 1250 368327967 368327983
    0xe0c0d0c05040203061302040f03030e01110c010509060c060a150506070c030f020607140a020a0b180f010e03151b0a0215091603030203030a0f1e0b060f0c0607030c0e03 74
    0xb91000f580d00d030360309400a04100d0224a40d030380b40b0703032000c1b40100d090170031103504809480c800e44441c48441206401903c80c090711014641346a400340c900e41c0081d5101e03801601c1ca00b13401404d0a800c0c142c0c0c04205178104202160110f04040d0f4036411407421100a1549400070103090340c2a0385000c419440f101d10320704542c0809054224484202d10842d00c0d0380044070b1030780d81c020305d1020f14214500c800301e0301c03024140c070140d00c200b1141501040902007a81102c07200c0465640555901440000b406291680c03000a82d060003903920084216817018080b00e10300d00e20003108038540740f40950302194400c0f2340c81071f001910102405544c0c0c55070340028500340103818080307544601d07681344c410300b5182c0400741d03074190701e1252591000420140c002010794004d424054091004407454156042146d80e00300640d0280b1421900950510f020b43d44400d10025010b0a91480d20403107110031809644190008496075000030100002e017641807044642c8081185045a9001041000179a4030035a03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 368330467 1250 368329217 368329219
    0x6030b1f050109060c150c051206030309011d030a081201061202130605130503030a020a0c08060408041206060509070504030302010513080f0a031d01021b12030103030e0105070f060e0c0d0c05 84
    0x110031901c4084c030040c40405030f2003002c0320009010087e007414005080350018000c8007058801080891380616020066a0b540c90b0103075039407082012a40c05120309042c0c041c1c2c0f03643d01805801080404140785100608a04646141d8a40154900280240540010329011a1091041c00041c07692200384000c0802c6032954506503490b16a1a444640301c2003007640000e034548000200c03e5642900403030458080350040b401226810b59498206499200450740200b40000410040c4000702400029010550003140c00050b09925403005c1546000240c44a10105201180c20410164240a070340c1e401848602c151101c00002d41c2c0d0526036020701d116400c40c84001085001809200354402c0f00300581111626220391410110301d0b0003540880050340c180440500c48480e10040098507440ca4444080c4071844c40e0304c0e50b00c0480c0c1d00c400460700c190400c0001c01403030b40446c40f503c1032680c0c1e0b54000c08d0001ba00c500014011458414465441c81c0143c19404083c408117024005031022210 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 368331717 1250 368330467 368330477
    0x50f0f070510050405100e07030b1609080601030317091903031d01020409050a1506020a0b13020d0606080601090b0a30050105100905040807020f0f0406030b1f05010906 74
    0x149207015418080c030560008038442c5030104000c01d201c80050f072040103100443c000c11034500f0301000540c4a5080b4000600412000400300d801000c51422007400d44002d0301d05022030680300c09860303040460a80c0264009005450940d500d151744409458000f40806d0041c0105001c200e04901401e606c044090b00b0301d69650b04001b60741007500214040154200c00842d40d442d120341101c002010191204600c25240003680d00803503002c00034040a50380c80e90001c0043d0000c0707580e41100b07560010074a441030b03040701d0300c200c005848848096602034812140400e6840c208145140342c980141c4c8214281070500c05010601d445903400502a9a2040c80c440040d0244480c25140440c00c0720b80702d0f14448000302c9070790503c003040d800240500c090000d144c22203541c40e49a50140c0d6829500070301855020071540c80181b80c0342158814800020301188620340607030001800311070440c0d0080d2002002079040281140700514180d14280001d08000c2500d801c00000900d1100c0318060304080c85 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 368332967 1250 368331717 368331727
    0x40e1c020313090f0b01230304060b0d12110c0604260604030923090117010e0609030403031b03140c030c1b090708090c04320610050f0f 60
    0x1034030900c00c4902103200b4544425109584500840040140320003001100d0724005616030300b580314000741c4d6051040c0c0100c001c0c0b8103c00e180d085456500281c4215003542e518140c004140d21030000d07105006010b121006050009507601070400d0007103804465194020060145140c0c2c2c0c0d00040d20262a219002e8850f0390000b0f89480325410600008003400e0b00c1035030104002c00d0ba001c11064156800c0c0c42003008075080c03110081000c80388100b101540016000c0060000c1010101895800b84448001003240c0358004401414038600785d44403051504002028000d1540050940340980f424030080c680d03010184c2c500402801c60040c04060230b01c00000c400c6100380c41003040d103102076003600582c2d41c60000382e24405046040900c0d0b45004600718070008910a00451300140308496070805047c000407580208002070528045828009504403110b0304501d00c035400011aa071044070b07250300d65003031030750030000189110344039038080007410408a400c40300c802040c1c82c800068a08100d884d5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 368334217 1250 368332967 368333023
    0x9040e0c1c0f0c0e070f05030609220f081911060c0901090b031e0106020a02030a060e0106090608030a020f03070507030f031e0207091a0f1e0604030c08010506040e 72
    0x1801d200034024280b01040b0a001c80d4103800114042d00500135a107448607106070f4450159014023040711400d03840016503001450b55a0140c0c0d0b1014a00d2600740760f120360000c0742e55001c4416a2002c02901c82c413901089614080856485101c0719039170b20700700100c0f4036103000c40b03480d0703182c10040090354080340c00b050765405a4001c096002c00340c450007585644918040d040100b504d82041e80b84090a152080002607880c00031404072059500030300a0310311088280c5070000078214030880d803c450344d604d000000764803035140f207020060f000ca0380145903116040e000007882c1c412042107140054004011107000030b4000120302c000c5030781c0100c422400c401039003400ea4501c41400751099601c1d4821900018095001c100300d07085d198131290800c6140b003103076140300002900c0f907089900140b11a040000e245841101c080003d0b4100d9446802d04501c000481d8007600039510480c0c1110300e000051000420a014856010609880030465620a407181580d5803002080560000c04091a20301d45 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 368335467 1250 368334217 368334233
    0x1181e0c0e090604050c04090201082a0f040f0b131703160f03081006050f0c030c0a05031201060302030f06010e040e030a020c090a0903020304051c0f0809040e0c1c 72
    0x514216180c0c400d5840c2800e92a41c40d60f40c211030484d4140208195000d480c0b0f080d214607110030780c043e0755211495607160f040504070300303080725032401b020940d000d510155050400103200600e4001e00d85502d6500e42000403029a40c1600001202c040c1440007465600c0e400c840241164a0014074030045212040f10b01d08500c030340d514145840e40c144d03902c01c09100e803100d620440140710f541c905940d079407594115560000b2034060640062000c00c440750b4110340e00c002615a4451010549140040c03001da8103240128084089410703810110368201e0002b404224140101150f00302546586041c1070913100303551000b0903c40c140034080c45e04102c0341c1c944e6480b4040580d1a80e044954030b0f101460080e58417024022418130990b86000010600d03000e50244440e05030307154008604140c01c003400c10030204040384c61400ac0f00d604085403c0402e07001c11344000070364050134900e90b690440364180010b072844140d90a425070f00c0b8140d110000d40724120440040d942106058811102500c1e15580e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 368336717 1250 368335467 368335469
    0x6091003091205091306050310090507080607180b030408070b0c070605101a07260d0c12060b0909040201050d2d0513120807120e070302010201181e0c 66
    0x3240d48458030b01c882c0260070800400065108840d190300d90510220168240c1c1d607075008480c1c03d9000b0240c1e60061507071540180c2c040c1481003080e0b540042c4c4400c98075140000c101c90190000300e10b050703000001d5210b4000c500c0600700842d0f05078918035260b15403d4091099000c01040000c3c0000008c032214556819144a203620a809001030b0910081e600d9407840e250003100301d1010807100c0c949118038800e04840031b440d0310540c0c6071129818084400111680c0300c00c4810701d85400c0000b03080c3e0035007902c945184619540c41d81400803440400e024100c0b0b1054001c17510010003081000da0a60720718940c16409a4246441e66071006504008005084190f50110100745404008012181a10103021042c1c0c0040000c000740c1e81d400c0f858400c0364501c00d00181084200000303c05686108406461344007006040003005c1410290304502225405202071030035070001d074414021580d086c061103403500406503810321440c0c4103488446601401404078038110992500c40020410f20400c0c100c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 368337967 1250 368336717 368336723
    0x19080f04080a0f210e010501090605090105091e090d09060804051e100608030705010c080c0a0c081c0506090a02130b0c0109140a0b0a0522020406090c11060c03060609100309 76
    0x2050b520900c20b0040701030000c00c00751708020b50a1000200e02103040b84501001c070b500080071f01031264600028032582d010007620745001144011340030445204070602050080c2682c200400759092108402090790140d03400000c01c000b6440288804910002040750011030501d000d1040c013031508a2041c0b40c179952a503400c50980c00e1010009074080c000c130181102d00c4c00340e0f00a01c40308591006c01c440c00101120b582003240d100307000c09605903200390110030a40d4070900f600ca00c0c22408540f5166407040c0c4a000d65001a207400421200f42800901641c0110f440d80003582455010014031013031300010700030040c0b114000705140c80a80001d4110201c4640c02ca080d000d29110300c0130b0026119a5410402d54070752030140003040400b0b2162188610901c50310108190300c424515120142c11540002a03038803030344640b004520009140f10f0300400000c1074a403484101e0100e103442d81001c80050400111b40014400c00c8803544a0b98100e42000f5030031507038403031012010304003a00200313818000071b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 368339217 1250 368337967 368338007
    0x80a020922020a171e1e01090b101403060d081c050702120f030402040b06070b0a02090f09040c060e03031318110a0f140c0319080f04080a0f 62
    0x303080000c10320b9009266424440c2d83e604001030914454003450a0180ca24401d1004c03000c100303d012404e004411604211458001010081c00140d0720100400a8010401e10b81d6240c00c208200d207450070300d00202c11514104243e02141910103101d0f280801005180a41666000b007020011008125210a000c6d01030041c0403d425103a00c400402080b140e80b0054481e88039842e080512038020b031015025034140715499507580781d0901c8050400840d21603081001400001d00280d0b030481d0f4107200700c00b104801a01c80506c501004103e0758411490f038054017540c014000407854040d81c140680c3d0b0281802500d9450903800b19145100e160070a104810703035100003264220090120792210b845c0700c0420b11581003009240111803103511056004a840c0200e9410010f0061864035446494801c5550508a10030380e1a8115031014503400d050500c0550405202c03a000079042d030f005442c112a0b083e4500c0c180d600c0c1c4070b003403103494140b44c140304440b0840001c0921603402003222021082113 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 368340467 1250 368339217 368339269
    0xa05120c03031306031d0a060f060b071506050f091b0903100b010206010e091c110307030504050a0b0c0703061e1107020102070803090a0302150c010203010609030c05040507080a0209 80
    0x20440441c3c07514000c1000090030402a42040014040a0001141d850703010b4070811540e9502e92000780055403019401f0764032000005180b051001c050b00741c0c41d006007481822592011a040219180342d048280710300105000706140e80c54540d0340c15131186580c01214001c10140300f0220150240d011440d500d486001d14200d01a1850340040ca4000f600f078080318202c0c0d807110140140c04000b211105010ba001d030450030080241c80000d002c2080207400c1c100c0c50385002054060442d0300c014070a40c00705100103010040c60420501d40c00082c580300ea511030401c15000380ca2034441c00284030141001d51240300c100004c01e10290b582c1c1e5074041601c0308103c64840c80300800e825070400d0b00140e000d405002c0001817035481c0441280c0044c2e00092507510380c1401d650030041c801142c001181c85d503042c2071202440c18982440194060804c2c0e484202c0341620f14a0001e04540b840d400c0b00f405542410140840c1540040302c030394206902e00009625004000081190440d0000c401d174007895000d84 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 368341717 1250 368340467 368340487
    0xb090d150e07150e090f0403140a02011d030705120315030106030b01090b240a0507060203070c02030d09031a090a240e0606090115021606021c0e0a05120c0303 70
    0x3550030200d5118016510045103101d00c15a082c112104d052600800b20f40e00182500e0b8403500070741d50182c80303400e1048402c02c007444139041c3c80d04520603450140c0e6558003246096001c011034a0f01c60354030703074000754902041940c5294860040314007a61040c44040013003401300d06030990124210401400800540385ea9003008950010f0038071403034110a242020044440c108148440068150000c42c2110034460361000c0032298442485401001814480800000c00c24001180902210b903107034504040b20b0b004160810240303806032000e1002d51241000001c0c00c610300c0d030340c2c0d4807a050b5600a041c0c4d5602c00c143d0802040c1c020041144254020452100c03188510341c181e800d0b6005010040e107424003400c0c07a40c0310400c0c0d4249502c030140ba00100700482071810039503035846551050303a14042402c400c41102c002c140e0048070168200a04400340300b0700300b1030b404d40c4844007071401e1003200c0c03034540202c0c98100c024054207006203a4050f080c150003004100c074441c011406800c9a030703a0300000d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 368342967 1250 368341717 368341723
    0x30304030801090911010806120106120201080c03010e010e13050604060501170f0304050f0a15020a0302120a21020f07210801030b0c210106050309010b0a0b090d150e 73
    0x680840114036580c0011601c1c2c80c0910401c030381c580d4006151652a00c070f0780015608288020b08081c0d0201213000340b110f80640a0042000404900381d0410b00f54055100140021a000382202c003040300900040000a80803180d641c1105c0505945441c0340d19140102c40002d82d48000c0034103203101700800d0104005266004604032403010b502680410400c014072030300c0d035440c0e100f180c140d0341c01400103100f00c1c40d1954612555640003808111526078405040c4454a600c03072103000076800095003c018541c040c48500802c0442c024258640307a41c0c104060701c0c1c05010408050071108242c02081a18415411540d0410660344215154681031800f004a0b0a82e0300c10102040e148910f81030302d0300d0095000c00d040e654401c01c00703d0b0540e50308070161305d903422030a8401390002c1d4648040a064050000d2513020381300f140d0b0b4072556071a0907046507081d00c1144444600400c8002d40410400c0c0301182a100300c107200316418085144030f0304101c1200020341d006002c500c1d01d0400010404c0b0400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 368344217 1250 368342967 368342971
    0x903050d0608160504110702090c0d0c09080f01021e07020102011e0e070b0406020d050705070513050f28021803030406050a080901090309091d060703060501031413140f010e0303 78
    0xe490380060240c13240d013440250340314101e10b00c001c02801d1040c2001442c2a0241c1c603070015100f81c0345030419440d50300d040c0564041200c83c001289a030b40d400d1040c900c0c140928511074808030000d40c50942040348260700e80341e4075100c59a6961000c114141107a01c00e4221641c2820003103003140074013a08190240042c03000850550a51040c6034001800d010301505660460f1110b801528200c1411807080e5030741d030710020089030940a00c1c080400c01c5c0c2d69040114000f2074400700d000a151038510041803441f40060880b5002c2c900e80e149101d40c1c43d003543d8800495080c000d80142c0c54000303e0101c1a1000040f03900181d01d4000410080351440e8000701401140c40301c0d42d9032200d2921551100307802c0760440103010300000c4c0c050500340f1100316150800c1d0040451151110f85400b040324003141404c800351381500c002511101c041000f0343c1d141c041c4002449801c0541c4150341400c6062020300004400020800e03002040710009510081c1f00c2086140c401c040240400c0400c03100841e2a507100b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 368345323 1106 368344217 368344243
    0x1080c0a030b01352a0d140118110103053909090a0f060602070e13030903021008071202250203120c030d0f05070c03030903050d0608 59
    0x1a541c030b03400c204e81a440504a440c40c1d8121108145808243c0740c26181444189416070399120341200a00035442603054244542c3d040d04103002d80b0140000c01d02c000050f004001c20710211140d500d0402109036030411095542c00e0b865299218507481340d88e0315508000302030b5140707110000c03e0060500d181e00a14200011000003a0300580c3c100c9050308080d480710b040030340f0a0381c2809250041c00c140c3c006400a903082c00100c1105040007804150181243c0240405140c000e0030043c0242d50050640c00c0795862258015103001e0054401030000f603041640402d0103100b0f131007035880918078120303103560112640c0c0c2d1a0941808185046c1c3e8107001c2c07001c280d0844d550040003000141030030740c05540c5804251803044115401040e100541ca428001081042d40e0301244a480603989420001101c030914101110a0702801c602e414100e403501e0f00118150200103040300941d61 = true := by decide +kernel

theorem cover : BRFrame.Cov 368165467 368345323 := by
  have h0 := BRFrame.cov_init 368165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 368165467 ≤ n) (h2 : n < 368345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
