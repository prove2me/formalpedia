-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0407
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:39:23.090526+00:00
-- url     : https://prove2.me/submissions/96be6886-422e-4bb3-976d-b537cdd55075

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 73021584 ≤ n < 73201440 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 73022834 1250 73021584 73021589
    0x1080307080d02160203030a090302010807050306060304030e04060b0c15060402030c0d05041a0703090c050603010b0901050d021605060703060803070b190e0d020703031205060105190203070c120b0907 88
    0x2000030410102c050091a600070f0708415011091988114030a0b43c00a400e50700003000c4c0a00144040e0001c1081d50f901514158000006081242c59802c1000118080c0d00c8010809420300c102040c1d6006a81c5560703000301c00403c0c12036482030b01d038401244000d031680a215144c20001500d18042a05c81c9400c2c400c8a00588844103100c0c40d2198107040b01014240080099400e10364081001a04410300c0703c0d85480385401d9580005d60001a1820b607011145942000d80036420510040c0f100742981012608259070034242907444680c4000c2c4240070380716075070300002c4414031103006000700140081c0d03a40c00742c100e64074240007003500d03051015a03d004400d40035101403241d0010401c05058500805920b080744a8040344c64945880350600c2c0c0020790180c18010792140300104140341d03010b40e20720f0580803081d000340700904002000a0082c0181081c4004050041c001d86c80464000c04c21070790119480a14020125910310030011403000184041d41d0000708240013501090300424101c0c04d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 73024084 1250 73022834 73022843
    0xc061503070302120c09010e0610020606030709090c082508010209130c031803020c0f01050c06070e0111070909020a1205071701021315020c01111510050d12030501080307 75
    0x900d882d503000c0050403112100900014000e00040c80b103552103003a174207800b038860710075044610700300541401690309030201080c003150041014450940d0b000300f42d07182164480d01c0042002070050811400303c06c03550f44a000305115220a90799001c1001882e20242c1c001c122803039640310340d5001e4040c00c1c2d2140c4448164801b010381b140007481a91030307004042000551034005100041ca91091b410048000c8060300176030b2013290302456610b40441036891850080c80e02e141000b0001c1c0c41c241e038980c00038182100380310b510007000c825030b48103040c40c6c05980713106003c03148026620460b800050810301b5003a801241180d101107144066902003459a0303505c200100845486e2100c01c0d0b0f66201e011140c0d506a5400300000c240d030003030000d10381000d0103d403541c4c0f20014000020186c0745c120015070007414440381480c42c850506010810810301034404408800b00d40d40c0d0360b03001324085079907040150b022540f01d00810921260340d440507019582030b28104140d03604c80c0c0c4440c2d980d00510f40e0090 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 73025334 1250 73024084 73024093
    0x30106051f05131503091205120109020304020607051005070f08150d0c0f0b090f03070e010e060319050c10030612060906091e0b0a06120206030414120c061503 70
    0x7800e00b4410301c000e10000000c00b00361a4280d40350301c542004184000000700009855511402c00d01030720104014600c03440307003810743c6400c00703154442840c502c05220b00c11007503078080006415516a5400c460340181e106060354444991400081d00804007555150002007100448150903400380300454016107008009080041c0382d041008401448940c0440d01e0800d21040001c0c1211000d4040c1301802d0aa80c0c0c0700d844103ea007040c800c0c84814009070a209601c00b4004200c05070b9840d91490540700050000100c030740d1201c01092619aa841214424142d415034007010b100c0c000c656002c00e210b08454058610200401c118165070880c003540c4400114182380c200001e200f60f009203181c611440c2c01280030281a19070300c10300d909442c9a0100035a0300ca07146410000c074000c98950100001000304501410110202003000f0f190031300a004000c0000031600703104110710781d100d4480b401e804492640c0c80c2441910190742140020290320711035540810801d40d1101c002c00c00c46c450140040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 73026584 1250 73025334 73025389
    0x70206130b040f0203120c0124060815060406030b040b0f0a2108030a0603120503100303050c031c0b010201141e1e01140922080c030c01090605040203010605 69
    0x1020740060140003190300e5500d0510340001a01c0901400080c03091510741251100282d414145c25607402e00c416001c1e03c001248603038580c44002c5044001e0395050301d401241d80e6200300041c49124200440c050744a040801c1c0040e030b03130341d254000070301e003c0090320103211144040003808900c604078010140e0182e00c041c014000c028602d110921154054000d80700d02c00c4450300d55020f5544203850995410fa00c400040c0244103500c1f104511030304003403410a1440c17403c0300d181c05040200d4040181000400210107052400400507548030181c0c00014030845148911500020130070358400c54050750814220001302122110014403038211001c401c0001d0540d011107a02240c0c2c0105840c46084e156a81071a00e040003004c0b540c00707400828108000c441c2c8910800903401c500030706102440b150041c0c0591048a42c400d0880301a0740220b94a48607080c180e1502e086000d52030101e00c3340d62805c25014144502c44e08420300480c000c0d8001c21001d600c1d50709000c1a41080d105d40f4801d2201144803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 73027834 1250 73026584 73026593
    0x8151608061311130e0105011407080a0e0a090e060a0e0d0203030606031f270515221118010e150304031b0807060605100e0d05031e07030807020613 65
    0x21480740360403c03405454444141c049180c01c46241d0844640354807030a00505c00703541c00130000d040da0110784080034103107486a83c418240340324444c0240d00700150901c0404054a8810040e0080c2421041c00d10808042942003540d44508503580900786061144003007000401150048018071035501445c91965100103222495001078954640003ca4030321340c074103650240142c2d03000703486036084941ca28150310b0401c40051010490319803030300d447d043c00d10050b1441c580f1400c01e0035a0549810981c4003c40340f40310840d00c0c10f08880440c182c00c0c1005000a01c9800000704617680c020200384100c4002140111560040322000c0e5030000f10400c02d1002e84142c0901441d8450300c6494840c180e440c0840c844241940140000c5601c3c91011980c2c00421500b40901d40c060715040d2250a4010390496000300070b41c08913505140100d000241c44001c5c0601482100d40d40c801d000448901c44140c40b055816950200740c081c0d000070524408192064400f08241e800f40805441690f06800d07980c03038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 73029084 1250 73027834 73027841
    0x1090b0a1706010f0207062006090d02060906010f03020906121207021207060c0308130609030503040203011802010f030905030d0e0304030201080a06052209060e0303010f0e0f04060c09081516080613 87
    0x711403000006560300e80422342e80400281b44a0300815014150148003850040d24090700541042c880b50440707401840301540348106031040b00d03012900c1c5503840d100c0b0f402180c00048908044141d60040302c0000380011181c2c402000204d10945560280c4400380382c44c0d03038442041e80510030010318049580004684035070106500680701c5100f12421009a98619084840c0380d038003200800c40100400040d0302c1c00788650858101501c0c0300888068a80d03000030480540c0c2c0e0000300505075255080420700c00104144c502d0407000b01810008112525241503880c1c11600c0100e00150401700001c0002c44940a85421154094450b0054010b80b40640c07100d04026070621840981c0c030707220b007404580e0a011301802140c0d41d01c0516507a504201c0b80105140c5140c101000304944002408001e0401040c0141c0c400d4000c0800a102d50403184c0c1220034004a030f1124074603100c4c07040d4402e502d4040e07002080c00307182210620080402c0c140c3c42a9002a021100e25500c44e1f000589042c030044180c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 73030334 1250 73029084 73029107
    0xf06040312030c02240709140a05010f030216050616051305060714030d090605010f18090c0302060301030303060801060909050c0d060b04060b0702031912030b01090b0a1706010f020706 81
    0x1074420a0f01740b40c0030940c1c400d130a004444c07a4410b9035400e01142c1600004644041c01c140300365107124641c08400316140d0411486598100302e803007031050303540900c60360650b0b04280c410480c00c44800d101c1e06151359074010039034030846da000103000c00e151131600410440b0415801d0706444e000607407070b03d0100305085d04245001c3d40e003916491031004e801841840184240312111900080c402d8407801c0c0031044030b82c1604141d068810001c1e0606c4180014034030b091019510b0040400d03000d500f40750403002d442c429480250004000703c008410143c03d500907078260703030558008006d0381c3d40d02c4065009070303541c60b01c01500c0e039000212003031030b41e00300302c50742001c402c0c042c21011030101c0010380070400b240d4107030b40100410308020480f5011481c00744440d0001d5040d01100458000242d150300d040410041c03040030901d50f4800482c803517640036480d07200041080d4a0b07416110030b0480700151100210009425081440c04000380540d8028420f0707408454a50b401400514101007041e0344400600d07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 73031584 1250 73030334 73030337
    0x30209010312170c0705070509070512060d020612090d141603020f0303090c0310020702011b0f0b07080711060c0d0e01290306010b090d0602090f0405090c0f06040312030c 75
    0x501e0120b08605100440ca4007901c82e28048941c0d426460411030304000903600149e1154050906004100f80d01906884407001001c90284040d100c180009041000002e802500200d000c910451800404c5010602c00c030400e078195041410f000c1d10443d40c0c00076034140102860303414800e0b80d00c0e030680303010001450361280c01110460004101d0b80c61541c0c0044a044001c0c0c0d000707440c00d8801c0c0c03c083c8111070b00c66030f0b03451044d42803100550000c0d28070322100e84030b225198440e02441052084440203102d000b90803400700e04c040d0078061402090302c0011604000030400c4520130981000c400140c1c584074100203902a400c08422600c03001c040c040ea45642c6c1900d6407510416a15039155411442003002c0c0d0480300c100710f4008806142c1040e80582c010300c2d0025081c0851100764031405141340c81694481d00060f0307100001d400245c100090190301e10b402c03d2400c0100011070500080c0d58140c207004889102d03082c1100d40400102d8800c0780001485843e140303c44509541c0207422194050603503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 73032834 1250 73031584 73031597
    0x2a071202030c03010603050c1503010810020702010c0f06090b0f040f080a14040f08010501060504031106090d1a01090b0d050a0f0206040e070e0109060306050105220b0c010218030601030209010312 86
    0x21000013400d40704031350420780e00754200f440e00682c14a0168510b501030308000b28810305662408005a4440d480c444011002c1d980000e070791401c41e8840d0404184080e4000c558141160365410100700600503c00e040b185c500e0248085590b40d5503224040d880366a104107a486250324a03500c0f070846800030101038060101200798440d00c194000058000782104200d01c1c03c00d1450500c405e4203440069000c4024440100402e01c0030070026000f20b6a90310043d683c80d541e8003160030104035801b0004602410039031104134001e458061590b0114100e4141c0032052048460010030840301070500040241194007001030700002801031403074201000d0001348414101030f500c400900c8000d800301c0e110f000248103072440d8003480da00201008094901890100180c82c144400a003107441181640784005500880ba061181c0c4106101e070064040940c250b40c55010901085001c1c0d00500d0f4845111115480c00c42d0b2942400030b03465048a400811140181c0d1858403941110030f07803540f0031800c000b031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 73034084 1250 73032834 73032853
    0x90c010c110a090b041401030503040b1c0c051902010b0105070b04021302070b0106020105070206010b1209010b030304090b1809120c010209060a0e1f02070b0a03020c0105010b2a07120203 82
    0x140c1188020042c02e03080400304e03a40e0031040400c002c440880c104490101040740040c004500000300b9074041c0c80076101c0030f07a662041e650340304402508044c1a40b4040c4d0400c0001c6200c20350010240c0700154030503500080d81b0841c20016800da403200e600381c6000480c140402c2c008507590406c004d4000307001400c0340c070f0004201006030382aa0300c000c2c42030380c0030980740d00108052582449180c3d80034280348094000b5504100041244d40b01e4102c0a209520700b0102044500100b0740c0100b510010080880b540c80c1d50314041200030b40300980610384030301d800c0022480140c002c003440e14441e188540c080c021900c00107800c84802d82005034414110740d800e0101c5001500e9507002041d072300303003280c540b01d541a030098100303c0e0050044600c41300d200c154025050300180c00059002c1901d544211594070742a8500040340240039504004e81c02d503013410300010b100f00c1070350014100120b8801c442001e0480080441c1c1c0c031004103800e0101d4640c00038108120f9440c5441c0a10403243c03004064904010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 73035334 1250 73034084 73034089
    0x1c050901170c090306070806030307110414010f1401090305070e0709032012011811010c02040609020a140c07030618020303071110090f0e1806010b04150503090c010c11 74
    0x5038101c072001ca91250003d61240145001c0002c950300c40c00a281402451400303401094803800b820100821aa5404c414000d075030780e503074015045d10440c40f460707a5411740c0d64843700e4140365041d100c2c8031481030380e0940448855115030702c05016a60888028180c080c545409501c10f214020600d8040000c08140480001d41c4104168010f04403603415030b2264a03440200035000c8207840a410725689010416444a8014410325440a8000c51002001d001120040e1998400481d00075400b610303004002c02c0320a1207034041d10500701c103951644800d0030066140785440c800c100004041d0b03882485c042001410b96008025040d0240d00b90b0100d45141d603011920b9600104822a0b0300c2c1010441c442d40390a11001507821322040f0314121080341d140c211010201c032408d01030240005410710005400034080c400e52500e0424420459503190b82d12100c035606500b1030f0042543e024031044101c203c3c140b0800c1601d001e010aa130103003a5101a44005480c8840142e2003143d0070000c44100341e550341d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 73036584 1250 73035334 73035377
    0x120c051306060305060103020328020c030a0207080105010f08070306021e04030501020a031a0d080702030102070c0e1e01030803010e070207091806050604020703080402010c081603050c0f1c050901 86
    0x514804401207025424010080c00703503200141441c2c10540b0500404c842d00070710314500e00d03800341c2d5282a4201c0c5040c030290207003e8401c01c3c2591205100014401025940c009102e42c100c501e00d8008012036603d620014a500081e40309030401c0340e00850082c400702e04035074020802d0324a2902c075004070041540d052407941d080383c1d00c01e848a03503001c143c01201642500608101b2104030070440d004064132000551f2400c0c3d40394010700f490ba8040b0351402103407405d60440359402d40044a9108045e55000c00000310041100e1314088030078404a10701103002c5c00c284040c1a03d92140c09941960b080c41c81112042c68024500c1c400c5215555001954200a01c110030008a000100501090300381c1048011381c1d20240400b0b004074810804c42002ca079000380c00642080e030900e40801c41c80b186040c40060b6020b042c9001188800c4584a04101604400100218000c07482a10160042c0b080c2a58546550b0209221002c103c0d640c2c07101c106108000800f41c54805051001d11807a5144008405 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 73037834 1250 73036584 73036609
    0x503090a120f020d0e031011040902030a0b0a090c0c03270803030907080f100b0604030615091103060904080a0203070c170f06090304141503042003010b010504120c05 73
    0x10682c1045000c0009030f0500400c140e01045040c0400d013100040c000c00c0d92030024081a6100c1c46e0f4a007c4030284d40c0d00501181e00a100d4000c1c02e40d01e03802e090b00c0e02e40c000d00e02d81c003a040c861000c01d04c0008140c10a4003444100045a03140c00c484499a914140e0b05d807140807a5075104411a840000301c091174401800d0040c0665030029626454542c10a03403409000d80c100c1a902d903c00b282c041081280011100f81060307204c030b13012070b03c40b5460020690318019034000501103401c0c6012200d00305499000c40c0101d492258050000543c503907103412092206468403500700d8441c07000078000c1100c100003000050f1191040386d140000503215414010030075040891004491420840c09800801c11306074030700c0c076441c050718940c2032030b0180c0f503901e211324441c01044010000013481e203961020f000031a0541600030b601e0780c9290a1400d11a26050401000604a66500221182d00b0144299608201c040c0c59240ca014140141c0c40c0c240001c0d00c42c1210303000c4580101150a40301c0d43c051400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 73039084 1250 73037834 73037837
    0xa18050d030c050903030d0e030c0d080609071b030305070e0406030c030b0f01060801060318020a0b0901031a01090302091918061a0604120c03080417010e0102040509070503090a12 79
    0x114410045001000e80b0320310140c0c6410400c0c14007041d0890765001c422950000340f0f0040c0020b40c50032540301507045010b18860f030140c074068501c40c901ca045d00580d00c90700c5507604541d209140e90b5691026941800c1c800004002600b54488400000b40642d01680e040402404c0140003601c04100007002e8032500d41040350380d04a010f6040081103a041030302a0002a20744030700c00c030341d030402c0c03801000d60350140b14031010941c031602110700160405107000798141c0c02a20f62951a078441e524604a03500514503540000d1910041c051034004038141489100c605030340b50440d41e41385408029007288081d040c405038002000010f0400707102846003600b05c1600d0005c14200707200608012040f205090b5a600400c40d9024400d540c0d40c0e1031104075003e0b2100300c0503c03500d0425900345500c20146681005001e2400060049060703114401c012500801702802440340c0545041d106d4281d014920906801549441c04114580d0050001d5075002802c401203c040003a541c496080d60102c0207031160 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 73040334 1250 73039084 73039093
    0x40b07020109171e010506010c0209040c050604030c140d0309051504050303070b06030607020607090e07020a120201020d180c0303030209150f031012050a02010807090f0801020c160b0405090a1805 86
    0x4c0964100d200c0208981000c4020001803074080006483d010198400034400c0071248001001c1111901514000e05409480b1300c1d1115140e01d403104040300e4502680c198610300080d005010310b069105030680c143d2681d9040ea20703e15020900542405100c0f80c4c800424040c4004140b1b900e0410141c0219401181c44a4550404c0c1e428036050840140c581407c6422513000c005030307a504402c55008030b0b00901d00e86000f5a655000490904112400c0240484101b40180c0b4125505401900941001500420849031165001c14050128800082c2520b0700c11404002203402507005c1e041c00d01c0302900308020030005001009603684000400c0c51283e00200600c07800c2c0038100c030390802030b001c1983c0d41d024400c5036450719561030084000c002e04002c11000011401482080100000e12090900074084c0f40c40d405030a0103900080c280810340d1040d4008106c1a056118100d004c80d54079450751482d00303040c141485000719001b401d5850355500e5030501d02c01014414210390250380100044d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 73041584 1250 73040334 73040353
    0x611030103114c0207080c0406080c0907170a052203020a15150b03010e07090501050304060b030106030206072001140d0504020d02060a020d020c01090b040b0702010917 74
    0x140490008600858000d0f04000c1d505240309420703005550124040030041c0e01d00084224410307000e501d2540e03a40001e4801c0b02e0701ca5405680019146081da24904151a0214145402d1008580031441000d84550041101c1c03203450030300c5000660480845d20740003403020032040d4800c0a84809a492108656903001040021801800419001c2c0301c080704c81421002e068400a5551765006006170030744d40103280210030103000d50f0010b03010f103801c00f0660350155503400d9031203442c0e0024425061810444030004103014406c8a00c0c500b80c4205071611401c40d2966103400740100800d43c43d8030f41640d681c80b004400b69840070007600045108044041002040304080c600d1410786c80140c5040c4a40175865202e0b1807100340c280c07a18400c000e540020150303110700010f072510103840c401942040c1c4c0050540101a800308030091076800540803900d1410480380111000c0040380301d1900c6882c01070009020014040d1b0081981034014905587c0981d05c0f2000008a052144a207100c0c1d43c2c1f288884 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 73042834 1250 73041584 73041593
    0x1c02031206040227040f06091a040c0f050f0d0609020405190803030105040b041b021c0c080708030a0212010609150c0c2106020313020f0906150d02070611030103 71
    0x900341d200301e082e5019420408034543c00b0104c10105005603404408070103910030720b511142d00405400a124405028080e940c3d07601500403e00074000c46000c05140c144020329042c03500401e4880d5246a0340e0300492080900d003203616420820120316410810404180e4102013402550080d01e2070160060345e840c542020010403a8a04001c003651050040b0108036030743e000b0041d00e046070780c01d44003ca240e03074001d00001c0007426007883e4224002c94080740d441d4000c1d400240b81c8641b011440d100038080400500559002112620040c480401003190500041401002e5074001049480c0982400c4038001c2c2c9140d10b0009030820400940440f40400c5014031520f10b5101c400c0301402d040c0b090740e00d0340d00c600041401c18000c1c20740300e402049181150032290454000b1203504000210b441e03040401d004500074081000503842030f101d500300a1406e1810003103081c062800200001d40c0002c4840345900030350441c18150800d25800d000c4540400c10b1406040640c03440d1100c3c083c1d996045140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 73044084 1250 73042834 73042867
    0x7081608010c021b0f0d0c05040e1c0507080403050105070c02090a020408030412031701060302030405060106050a0c02011d03030a0804140a030c03140405060f0903010f0e0304050904051c0203 84
    0x4260441d80c18054000d04840d004280030160042003401d11410f400704a0101e0050103240c03000c26000300103040f03040b090142c0c0712600d0090b01ea0032941804044483c3e10803560b41c2079541c0c029040900306070540750300c80303000348010110240300d06042403c10b541c0343c03209400c5800c100c03a20000300b03000301c415801718034000c240c866002082c50811403d00e07043c001d030565603010f40d00a00080f1007e0044203001d060003440020102211440340003007030340c1c446400070042d42080e01c0441d03161007000c001041490080b0262100401070baa51203a425000e0340045810950360a010031034011188082d0020307440a1004002d00c2005444038010b5080628020102c0d451101c0090707142c0e0480801c100000384e00102c2101800d0701450415401e03888201d1510b007505c1640e018561110000611454888241c805000c0a41007140200910790303101061704d05803111158a125113420801c800e0040e071406021303180d00719000d20200d940300e6200040f40c41c0c003485a8006080507a00106801c1c011001042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 73045334 1250 73044084 73044089
    0xb0a0902030411060a0c1509051603051902090a02030406060e0c07030207080705010c02010815030319170601080c160501050702010e070f030209071407050a12020c181503030c070816 80
    0x1d44107172810008441c01080240e54550040482425842d0255415481c3d0042d01e0101d40040945403d03070707543c0709040f208000c50f110843d024054021950040e0240207800c94030709e1b4002e001220340d5a0b41c0e4005000a51004104440e034681e030358404a07205d4400c005182c801e00c4d45100c0503130f4410250030080d290100300d41c410b051562006c64140300e0759a014410f100410360a007009a01c588600c160b5203c415100d495094040c400810059083c2468100c1901e074290349032500c40301c40c0b140303000d0700d040120101e883c0c60106885134080794410354082c00403c5a03001030054a82101c2050380c5450954005071270362001030303440303400c5d02486d1081408008018640007618002151035580440c0c4a0340c00100000240300111101d02000e032040401c8540ca103501c501915a400348a29040c11a0219410050018400d05c80c0040484c1030400340d40d24245000d89801c203050380e07120910071102c800c82a105805000c00d001c54005040108083c42c09010030340c0252910145030200c1500340c18503503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 73046584 1250 73045334 73045339
    0xb060a08030304120810090e0c040c02010b010e010e190b0d0b0a12031808030a0c03080a0e071503060e0108010b041a0f010c030e0d05030301090c0207080316060b0a0902030411 77
    0x10070600001603c2c808070581c0c035001c14201158103030380d1b20881c0f44612200754032200095050040c403651486002c1030012420100300c8080120800c540412401c03030710000302c2c0303501103001000403000e19800755500b0404800014448040510b5422424403510f0056100c19018040825507400900090040460080054407944442407620b06a002107801c8100302034140185121104000982c89007424054040c0320101c07030303441c411840010214001e84034143c0000310603202088510800d40260540c0c0340b003200041014a051240001d14060260b0b02d103000d00d580c960002401c8044003645038000c00011000081025040052005848840001d80704810150003003000c140c2e508881603082c40428640401c20401b81d160079602c0501403524581d01c0504140b007a0100305001000754165906c100c2c0c02d120790704040350140e03900c0180b4050b03800305810910440342c0381c0f103001c064204414040c0350041986d100120216800c54801e030810b03a0032540020400c402d0240f500e1444c804458203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 73047834 1250 73046584 73046587
    0xf0c080c1e0705011407060e0a02100e04060801050601020a0821040f0302070905100306150e0c0403031103030903040b0f040b04030b04020306060d1101120902040f050712050705030a0f180b060a0803 87
    0xc1c0290a4041e100b00794001f42041d40ea1078921003000317003c0140c068030795409400d4440481c3e101c200648122a0401554400ca0420a01003400881800341300c0c010b03401a0000e2107603c0095640142c03c0d00b0180710304814808130248100c05152003030166016600035200c05d6500398135810000e040107007680011a015003420b05000c0e030303000d9201041003100c1d0400c1e0300092400020408400820060780041d40d0b0b00d81c0d1f8014810341100002c010011a48251105d6840b50052000c5a441c1d0004482c59501c0e41c10500c41000081c020800500030583d84048051405855043c0ca0041e600b281d002a1140c8140b40204011401c0c01c001030741d0041822245480081c03165030350082101e1405180c2c0e4108103030f138081212440b580b6046454002e80c02841844031504003001d000041c0700494141c0002216110800342030a0f05200300381c06500c46070f130b03601c0c0307550351300300c068006042007a68543ca1240e8940d442619105404c4000e1403007407140b0f4503117145060020411290811a0300008100d400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 73049084 1250 73047834 73047857
    0x409290105030712021818010c080f040209040c0807091a011e0315090e0c010f0c0807032a11040c02030f1c02040302030d0f0f0507030f0c080c1e070501 67
    0x700043c120003141c54144294a8001d5584082180307040f492107400f05241034003060001c0701e043c45200d40c40c0104190000c03c0740540006007281d031440c044c3c68004488010340d012801504000c10b1569015000d81c107505006d565503904180307402c0740c2d41d1002e00c1f9140e030350260315400070f4608845040103009280600980c0e41100200c2050200203804606155588a514807a981c140d0703c114000c1007500001c00c5044401c048040d191180d0b01001c5000a0f0302200100d200d40c05590710500c0b143e0003582c2141000038507031342a03c3d80c0188130910107070080052421701501610750004291039101e9203081c81d416420400340001c0d609041d602c4d0301503400901c468200314001c1c1c42940d01c20300032040040000b07404510b030f20000744201e400194160240248990072031360007024031841d050642d502c100c16000307800c03000c0761140684c1d070004002800300003010307509504c00c445a405c0d0500aa000c3d40c5840c0d90700ba243c501e0101000510364408031039655a412150090124000804081c2042110b841 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 73050334 1250 73049084 73049089
    0x2011a010f0309060b03010e0a06060b04030308010b0c0c120102090f0a15050d0902041401060e0f09041202010f0e0a0c081b010f03020906070602040e06040c0f030b0f0409290105 78
    0x1400c25070100e041698804890003440215084480b0b1500c01800070400a2150040340d6102c6120300c0742a60a03c2c18901300003404c3c2e941d403080f50101c1e901644c2d43c100b00e90030b1621980c80307603000d0700c80500340e1300c20082940f2044c0d4411802d0300344168030900061b43d502c400300c2801500c1c40a800420300c6000301e070303508200c241507003c1e99a00b00180d92801d9961b40e00380c084d06070020304007040041c0d00300789002704020580b103c0e40007840c103039511a11400c9543c130b00030040280201d0040c6100b5007014609001c507000a0494040c1030141500340008910b02c44441c0d000b004454400e4807168082e406203054000344985140c195004e4040b9001a19031300d2850074001007508011a0402d0400941d2407102c1e140303510990540e45c4045004110030340d100d080e4141100a50042c2c010348400d00d003007101140080c0740c01d00c1100716031003c9803580034414400940075030080000c094995000100e04582c1c1249071f03180e20644d0306c00341c820200305074035198024035031030121805000000407a400900500156 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 73051584 1250 73050334 73050347
    0x1030803070e1f0f0801080309061206010c1b05040e0105090304030f0203030705160e070e10030b0d05060c0304050c190e04170a08090f0c180a090512070302011a01 72
    0x2115090009015a40001085900d45079000c0c2d54060380c15100f1040d20300340c0c0445000c090900aa841801d10390301c07220500d40b05d1052004c000c2d800802008660010102424026806981414251849020390301c0e4108030f160341200b07080b01c2c02581030f01801541303843d128511880401d20001c12040c80c003401055a0380c0b003a40400f4040b00c0d40301070a0340c01c540d82081192420355000303051781c400c03401c484072264440da014000d40d001c410020300016100e0b4428046a06035660092039011251415170090b4014080c0b100c9250304502c14107460302c0403420801110303014032080d18410b956403a190030000d0404070241c2c12144526404030620210b13003100710012043d14012180a05a6280c0380f910314807a6000d0341c00342c00c2075080402c1e141d0845801400861181031844180e0f4841d202e07881c0c56585815070070f06003075445005199204207003846180d00541c000403070031000034562a42d45481d4503200e100305400d9121301c800038010040607420301400c003602051084194040b1131141c002b0b80b00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 73052834 1250 73051584 73051591
    0x5040f0302040b030a081818061012270209010603110f0307120e0c03070905010807210206040b030a0b0603010311010305090c09010f0501091403070b0c030403060c080f0f01030803 79
    0x41c54803a0807041c400d607424017100d05032035488401d144ea900070710444c04066414800c5254410a0702082100c01c622201410a200d0000103158441e1801480f0044e40d486018000d510f442c80c0d592602241c00000d0024001c0e16100c0a59030031005640b04c1c0704010319418140c00c06010542055007a000c3e44000c5402c0da41003407041e40b00c071074490340c82081c00ca813401d0380040b02c8104241481040300303180c000419401202842a01500c9410391184140001d880e4284600304555112120811103420b8420007a02030f9040c50080d00683d08403500042c103950400d4005d08221400002884400b072418441d0102c19841a6071040c2558950b03121114403a5840c0900383c189070320340c0001511302d0380500c4600d102c00c20091821080c0d5131210507406102006000b12408181080d102048140d822443c410800000030002c2c41500d0620300010200e420500d12002e051005000100001d0f185004000c40e400d500d58035440d007450f02601d0104100307400b07441000130541000050021444020442e0f60 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 73054084 1250 73052834 73052839
    0x207061202070c0308090301050a051005040903110d02010c0809011406060f090d050c030d030e0604030e0a180519020702030a0b100b041409060901060f030903050c060414070605040f0302 82
    0x200180c034014004080d00c103218009041c0c46010802008022a01018260b0b0310001d6000304499540c0c440000200c4209607513080c651481792100304440d1909800c03041490380302e45040081801c00b0007041c0c0c070b80a007808816002d42d44a2100303c1c12141d1000d66141d21074940c2c4001d00203121413008011300c00c040038101c980120030002d051480c0a80301400c8441081c009040c00711940f10f24100180c0b2080114078440c800d0040520f00da01d20b510901a500410604d0301c0506400d440350f0f90b01b950080c00104940b42c0090070810005420300000302c8440a02e90300441c007243c40c1c900b102651a008401c2d00014806510610130f01d030140c1c03130002d9030101c06540a4440103032600c074502c510240d00c500707034400c0c1c42240d00060b010402c580800c010b105114025074a1030400c1e206c607010009800c1c0240200070000700d105c65030b401030300e21981000d1112402030900c00e01d816046900b142c200242141d05903180001001c0c0100c003c40208442c1d8020040c13032518074109418148455000c144c81e200192 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 73055334 1250 73054084 73054097
    0x7021504081305102f061603090f06090b010b2d1c0b0906030102030705162907020f060907060e0609030303010303180e0103080720060a0909050606040303020706 71
    0x403030440180074504050a0020040c42d011441418001c012803801415901417141030340030001a04a0520f0355400940003402600043c0d80e40d44580540b451006240820142c40307081d040c000c15030b10756050900c580100004607000035039040c981c0040c241070f84608800c88042045241d81c11826124180790150280c1010000c8680b60803841180144122181c681c08107001400480c801640444a0b003841511102050b55402e41003508074001240c0c60004642c0400552602283c0c0005020426200e1000c4a03204074102d40c43e0000030700c841c904003140002d00401c0c0121242c04002a0341e540501c90b00400c03c902c0c0c90864942c0ba000300f84240c0082c000c0859a0345403607520300d010344614040180460392a076940703003801402040300d1408010b007100c4d80c0c02e01080f110003c003c0300e07060340d401c030581c1881e1066a543d0541102140c3d145a800c407034401401c08415a141c4000300103003845070f628550880c0c284040441151405421544600800c0204000294003c030340321084505909014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 73056584 1250 73055334 73055347
    0xf060f030c0617250c02090a060f0f0302060703050d060f03030f08090703030e060d09060e1e060405070b030a0e0109080307020709060e01090203180307050d1b030e10020c060706020d050702150408 86
    0x1a85c6903408144002e61111440c410800d003141c55501070404c44040f10205c0b0205560b56418035040e00e400c3c00080d41051040001402080c0110001c14450080c50000902a6030ba0030807044503100b2070b0422000601c01d018008541c982c8041103a0b042502d600c0a1b0141c20310b1550080c0c080760b4500310240c059240484c400c1950f503007a0b4482d005968010b0700c2880442601000a82c44916500441103082d9910640b482c4581c00040e110707201e11b0b4840010210a420150b8000f001d41006020610558842000f40c8071042d080c09000c40740c0d44202c002a89034107004501030704040c19600300355204c0389031002c200300c42410704a21b141100e118131030050b1340c0c1c0c48403001020846e44c900300f5420b4510001540904010001880340c2801000d56204841c031220042868800c2c40491800740024140b032030350201c10b24141000c80c0a961150044a0202c5640c40104040740c00001e03099503405c0c2e01040443c60500701c0c0c06056071100701840540014003980d80e100c18112009800500550f10110b2003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 73057834 1250 73056584 73056587
    0x5010605160b090c0303040e040c1d0a0f020d0f050417070c050609280503070e01140103110910030e12030c030c03060d021206180d020d030f060f030c061725 69
    0x811504513020b400e03696960740315841072100a40a8808441c444100b4000080305003602090300c003038440c0718101c0803868513035244603005010310700721104400750f0030820071400c14811302c144e02d44806116000b0504c0c2c42c050501201b80d00000b090b420040800300544c00008501e4152642911002c48845841d0420700000c5418410010b4104c4180c0304140c001c3c030100c1d0040d00904007124000c80490705035a488482c1503406040c203100e10202045601034150881d8001d8201614019440c0289418501c0305070008101e141c50f0082c070070101c0d5480c8000c502c014400c0c0300c0110700040c080201c40c80c4d4145803403040c1c01403000425031103140758044045030640e038170404607106a540080920b04140045048661604019104c82a418150b0710745d45c2101d01c0086010f2030080d229801900b0b001d60307000d4096024141c40b0486000d025561840411006480150300c0e01450050350303813180f220708000b006403c841038039030300c00030380395452040240c1041c1c04075500352074072003000c945000e081e0351250 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 73059084 1250 73057834 73057843
    0xc060906110301120b06010203091c0201020a1e03020c03010204050105040e101a030f090111030109110d02040605090306010f0506030a2706051e0405060403082a09010305010605160b09 81
    0x401074040ea0010000824500090001501030300a01842000d0780712600160398a02c2140030858000a801c401e0315070010b11103089400c8a401801a505170380103da5540458080907181c0b10b403604644500101419810040d07103001e408164000c6103050300301030018081e40107e02c0784c410f000c400d8500164810f46031000d058000d10683c03d9a801c204c244a030001c3c065041100d5a080303140c03400c80001c904410501401d054004081595481c6900300303007112001d80000341345070030000801c00030301103003006901c000c0006080c0e55131800e03144c49403d000c140c10f01c041030344043c11440d001c500502440d594001101d0b004114001d001038000f6422020040c5940c1c611518080103841890180512200d0380040e40725088034003104680304504000c0300c1c1504019100908264403030000200082e0050100399000b0490f440b4016500d0010b13142540c4101484c1025441c2c90310124084140d960507004545c0500000e0504a0400300350700c8000a920b02e00c01405403202c0141c402046841d40c0521 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 73060334 1250 73059084 73059101
    0x60b0409020f0d1103010302010809010902090f06040e150a05011e05040914150108010e01020a1b0201021c020d090b0c030d1e020c070f08010c050d05070e06030411010306090c0c060906 81
    0x284284107006140c44c201009420074070090b4080703600000090740b0141c041c81198240c40e40102141c106494404660717a030100024005030300641d9502c40791221a170100180c80581441c0403c0f03500c035150002100e4242c44042e84101451541202140720007090070480c10300b035503000d48000600c1622410407030494075001c00220701350300800c0c10510101c0700301c4e84854143c0e025140217000101031590454200c1c4149411000014030040d40c107a2800680850620340c1ca00500c1180c03000c000d40041aa1000c0e030145440000da880070038040403a58000413810010200207070f030241011451310400703481c0e200303503102e1100140e941e4043d01c14001e03400a180d02c0b425030f03247c030440d218480d440b0b109560b040a070040e1800031074030307217800255030605010f060f007100c656581d058103105281c5402e03000303000043e2003c4107024081c2c00d405100e45131038003e18410350003103251594481c00400050111507141c1c21043c640303401c114980001c4c5030001d0313260215a0340122b000600e1a95414910010401d10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 73061584 1250 73060334 73060357
    0x70e0415060309030915020d140d0518011a1324080a0203161d090304050301090b0708060306160509030c0a030308010503150f0c03090c19060f03060b0409020f 70
    0x100030101d125940359010f001400d2080e20352041694458503483c65090844850300c00681c01050134840c2188155404400000b01500d414249000c40b900d0381b081e0741b07040300c485800b000f0f803400702c0034080d90900540341340040307100c0700030941c0200f070001c500824111850340b01159150a000040d80240c1013542d0400340c80000e102d0000d607107503070003542c1710091094103034800c0c0b2850041c0000c0072a00b104150445450341c1092100780b0105d52203082c450002803050000303020504c00050a0307102801a140160300c2120340302540c0c607200f00085c2c1903c030007a190f18002c0d40304908001210030740401c0c101c0e03840028200191207018120000c1c1c5030801143c502038004c2c6191340000209900f001c0e8041c141e03202181900d501e81e60040c0c04034096801110250b000415200102c0d001c1c4134404000d41c3c02207600c0054a9880c840b40d40442d200400d1905110f403100e800e41410880b00f27500c481e002c00d20300032502d0b040c4041d601d85a03a0121502440c05056841540040c0e030380098500da404480303224518 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 73062834 1250 73061584 73061621
    0x705100501030503090102010c080609130f1b0510032903070807080106091b05070b040f140606010905040207020a150c02120f010506010e09040b0601090f0909021c0b070e04 76
    0x120300d0010b850385c10550049003d5170805099007581400713007803401d1041e0000f4141c21703015652000c01c16902d40080300113940b0700c0d030703c40d01e41c0c4041020001007030750742c10345041404c2105262609120304285400c090604040c64508040d1108042c942140c20884425800c0c100d0090b000300080e04011072540103004d144110200000c804c2c20640040e000c4400122041001e4840d80010242803205925a1000180200321040000710005441074000d4010142c03007410150360303907584100b02c4c500340c451260b681c042070400c9080d41e44101030300d016010683d0f0030350400c4810b42c04111483c03030074042c0c1c1080100f83d65400d03130810310503000c44001e560014000e062002c4c0b03c4822a413120980c0c11100c00a5003030070000b40c01540143d000003004071b03010b03007818250380e6242c50304202c4090142445040008544000030340b00c1d800f005034006410880303000103503c881441000300d519400400140000c04074180d00c4007149103030f0750540d4090708508041d4800d0040324000b60040071980c1c1c1e1035a15246 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 73064084 1250 73062834 73062839
    0x40b0409060b0f190603020c07120f0203060105151b03091005040915060c14011508070807090e030f1b06010e0402180129040302040905060415140a020705100501 71
    0x2840d040b01010503416901080c16901480601818440c50360400407a14000b1404000c124840d0f4014951141c00409651070552140c2018414075840d550a50342945216554401c3d850f003840120700405e0301700c0e081c0302c4511011096201d14003c3c0000056295500c01008440740014021101002002810a40da41c6047d200c064800c2d00030f4001c1a10217840c03c0c245544036103042c0e8110041d150305403614441c5055994a07916202900b4981400075522400591030329140c084202c800b0708100c10240600310f003440d10a51625032a40d0100c00551708008001c03604400c08800c07100019448581340342d0b2903144207401c000c51011207205408034800c00000180c035003011000640908d10885804203c0b03242c90140c0344031040c0138043c500181d00d03400d0000aa6640b001c081400b07500408910906040d540d80008088070041c101c181d55641091003000200102d80902068441120b4810020103005003000031948900134070004040c0c0c0d0004105007030000030428540780f02c10600703062010f587c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 73065334 1250 73064084 73064093
    0x1b060405060409060806130302030912010b0d120201150308121e010b1b1528060306050105041b0e040902040e0d0c05010f020a08040f0309080d050405130902011d040b0409 75
    0x2d0340c0300d000098042c110100ea47e80c0c15a158103008560160f00440c1050404000c00040311107000703401e0700035942c030010302e912515402420700c0898081c030035051041180580190079a1060000040e495840e481c0070700008501605803407080840c410000b8040e62026809a104165000c2c0a0586201c3d040009080f40070703403004200303804e274a010601090030000c3c1d2555580c805c1005c280c0030000c0c0b0b0310001300c440250500001c40c0401004101c1c074078034800f0380a80200c03801c0740c20559115440344010b102e0307820103010381600702840c88000c20940c100e0140081c500703580018014880c40d254582c8070207564448d0846c0700c03140110010385079022810000030700701143c4c00400316029401c0c0102d00700a0407243c4260f84444110341c69246c01c0e507483d0341c0c4070001130580c2e85007107050044800d070228142804000103c400c00c13207a121030741ea6a0030704013046282c060030b0b038180f0000c90500101d840185d80c008010440d81080d0203003000c00031070520004001d8025a124150054a00100300c414007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 73066584 1250 73065334 73065341
    0x3141603090504090305030a0f02040909050a020f01050c102c030d0f020306030c01050705030c070e040510150e0402040e1c0e04200705010f06030c030516081b060405060409 76
    0x100d1080d00e54048107582c1d00c00703100036035003141c0015002c03074024400604400500d4210111114034800b0061401d501c0d0310013a0102c2e204540140da055000030b4041e021402e02e456100618a800d090050401c010407501e59916104581c01e403a1041d15102c000005000c0c0a040c800700c0c918640d1000c2e03d0303d0550240c1680c03900260000c044003400c1022040c043d00f060b01c200c0340510006005452406040401502d80740c0c090002102c0e644410041c00802c1841480b4600280c2514402c03107559040904003540352a1140d04890781c0f1514026000b40d2210300d04a103101141c980401025081c1d2305c90000a008000f01c0d04480c0303050054130400803d203030074230030280a00c8566455407011990300030300748401c03107050303520170200c460f003d0380d000c05d0070300600c0040d00102c0e110350000b080203011040e0740d8064810369481107a0020600f40b0034010804140300d21905101400d0555200500d8084070554490101c0754102c0800002e5529107001d032100300031240035002c00b9001c00c1da138540d9524080001d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 73067834 1250 73066584 73066627
    0x305060f0a050619060c0f020a0b03070801080d050306010e03101b11010b03100222030b0402040c03020c070317070803180d1d130b030615010f0201140c070314 70
    0x15074902400200e0603e0840e2420b030029004c82001071502e41048006d55404030240003c1c0c5842150300182401681c80003992409071965032812602c9041803030000d0600101a042484550131581c8240c10395540700c800d0b203074400400d207000d109401617480400c2c00d103a200c541013842d26080c08005100c4004012070b9002c0c02c0070a9881d034911113840d406007401ca66100040640c15004182e6107c95086960068440c1e1510502001003c14962004003d03c0045610071110402c40384100410340ca003074401c40076640403d04065241130952216140c54503014013006004402c801e40702c0c403000d00303020141c90030540d00c480030380e40d01e00b4202c03140d000c40710b4146c80307000340c40c4140d483c950b103400e100c1e000440200d0142c034075503006001008200134025a000c50349041c004e41d1000400d510b40c6e0304100a5000781c1d41d094a00020400c090001007114011820500540e07044c025801c42e1010489640c5603ca142c0390748181d102d010a18003200c0c1c09c8035070640350315840d0010820010094413054102031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 73069084 1250 73067834 73067851
    0xa0605011d090a15050315070201050f0906070c06020d0903031a01030623031005190b0603010f0b0309010f0606050c0105010e0f0a020d091b0509090f1e070305060f 72
    0x21890003020302120401c2507020040d0b0008440350115464104903004411502e2890080d440590380ba000400e1030065105003101c01d8017404028031402503028440c641d00070307503290351881c5a81b03000c0c06242e5503040042d00b94820066140c4110007807010076070640340c126150a008ac804c40b0041c1c100180507200c2100c0892580b040c252180e802c56000348280390849120240711441190b1260a014440e10800d907140e8140c041c1d00104081c041d10340c03007180c0c40b0701c5100b00f001118515a808038021100421103880c0298401c200505c8214403000b9000125091481c0e1503507266180b44407240507040d00488201810b09040c8041102504600680700c0000c0c400c0c020882685e032082c0303c03540c1031000d031059880c0f020ba40002c90051403c1d600100403050991170f01245980380c0b5610f400d074401c41280c03150080420150240003d1414900030f94000e51410014040403140e940b00a0f03c50311010b106200d40801c0d080954403650003808401d000b9030b0042d0603641c0780c0c641132181080501048980c0d10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 73070334 1250 73069084 73069097
    0x2130f050a050405060402100e090a051501020708190602160c0509091902010c08071718040603050309010c0213060603090b06030f060612071208040e01050d0807060b06070b0a060501 80
    0x80d2620300c07610420740304a8210b002080765494a409000d2001032041100d41046140600f807084d54403407a0030140144546840050035141c0380541240c0d1502070300b54181107400141d010880000c0002d6441c1c2c0544045844907541451481e080c4003c5c841c0e000441701d5007128080440c1401108018201201c1080c0c50701d11003070313580041c01601d074041d541c001d08071801c00641c1d460255200b0031104280512800d805460a1a00d842d044440c1c0d0600940001030b400c00900c0d19403025607a0229524904251014826a82199545601c03070103040b10f42d904001c504044a801e650f41d0002d00580c4190300740b01048403030b44824005001d4041110103481009084020030078a0800241c84200000c4180240c0503584580c0c040040a81c0f2049188107944038034040465903086141c140d2480d40e100e6211b0350b03921450420050303080141603200500c10701d0401141c50102d45c5079801c41d030606d603001d04002210541100020400d008010000c1c06503000c2d00d00b0049110541d51002c0c056032000d0b210300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 73071584 1250 73070334 73070341
    0x10603050615030c09060d150510050a02060f04021f020604030305010b090306040209072309030d03140c0a1211030f2503020c07121a07030203070c08070c0302130f05 73
    0x8014030000c00421034011030704100195045044c1d5000e45907141008040c24036100e416480d02055507604600710250400c0c00808000c2490080c1c04000070503514100942844506400a034440e22b00400e400304400361040050304543d00c260744041c90204c100f064203065851024025a161001ca1303084011030f19100c004a0a554001c00780c0325461002801030060b50380b66806c2c031240080c06440c0809100613407841101109411407080d801124012a841d120101c0c4d504162510380d41e01c040600745403500c1c2001c2c0c1c2e000b00c40c4810310b90141c1c0e4490300907600c0001440403200d040642d0040707585d40307103807510142080250000642c01071041e0f50582e0101d480b8824180410182550010014124641e4034000035003c0e4010305070510b0240d0070b444600d55100b020b80e86c0c11150840444941c08503100e070046003004140e07072036045103440c9000c608516140c1d201400c54140b1070400307040c0c107001042d100c00700480102180051a4003500740b110003620080000c001d0420421344040341c7d41400e000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 73072834 1250 73071584 73071589
    0x2030f03190207050618040e100f0f020a02120c1218010f030c05030106030b0d0c030b070206010e1512160306021e070f290c030f0c0a080703050907080106030602030106030506 77
    0x15042076840003001e05d40392101ea02020414003100565154010381c8079586404c1c803c0090100c0301c1904c00011005c2918420f20709104100c03017070700e542e4140061050020a40c2e89600107800e4010071507801c3c003151b0b240d400c035039014a4503143ca82d409541e01d100007202500b040d04505074802c0e00400303032030300e0160084200c02030341607800711140700700003e0084c0010850385102c1e03080034403007100c06405480081059201d001c440080c41c1c00030b44650503a01c05001450354100700f4a030040c426606080a542044000b1145202041c80110700c210800c1e0460031200314103016112184600002c1402c03860340e0b0303280850180d0000303d0703641c050006540c0f4070300110941d442100c2c980d41e803180442c540071a2958400e5459a00b0310000b5080c40c81e840301c582d0708596080710150040150240c015164941000c001c2010000108040b02c03e0360700707000b81c4020136002456540c0001450401083c5980c403045802d2902030b141e4081c2c12298201400042031046580c0194103907040b40d03800307001075a81d40c020b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 73074084 1250 73072834 73072843
    0x3020c1302120708070903140a17212509090617030d0e03070c0b0415110309090406150b0d050603060603100b010201060504021207020607021204060c0503040302030f031902 76
    0x15010324280302d20001030500c0c0d1044c1d801507440400790409141c3d0a41360744519141c0c1c04600c0c50032000350711540001c814090f0084200d4510040601c08618200880078500d5188a444c511482d0300c80403075001c41d119802046002812005000050a11030030030500240300c0d803139074031802c007c0034a400c82c085500100c1c00e180c0008035040348002c600e0040300d5020380004203010388411031540018055140044e0692001000808241415075101c60400041400c1e400100c5503010603c4280600c202e20b0a1000c800d4800a1208640c12a6959250f090400c0504540a4039181c0000381103004200a28160058003a240f20301c503041100d9523071032062694511003501c920398558484020352890b2401504407016000041c400410f050341e50303802090070303a00201001c5886052031410031000c5541001550350040c60342c4003c200c20b240c900c51080251145010740f070108007070b02c00e1031030910004201719001558050121080000c00c0c12090b0345a4005500c01c03504225001000042c0500c0005d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 73075334 1250 73074084 73074097
    0xa02040e190b06061308030703020709020a0f080414010f0c1b030203040b030a020409050a02090f0409150b0a0e0906010302010f0f09060503131209050f01030204080a031b06050403020c1302 83
    0x8595200702181ca0301d030800d08030401032280c0c0d40000100a241801d000c03044400d002050030710011902d441040c58044d00304111500724031111031041c044000c0c1d813648206040c01d561504e050840081e00c480c10140d0407100803d540d94065800c05080001c15402c540c440c0e4920202c50f964080c024160301030700c1509224030540500180d20501c400d1207070710920001142c000c40c628200500d0f0030390b540744180503190225a0001666030208040c2054180091040c400550403030b0308020414199443d40907403401c0c001c00303100141c2d540010002076207803103507003030003414414a0103a070fa41740181a6076a00d01090000b240041d103842a04007000f03024400c4440c2103515500c5400980b07090510885254200030010500799251607548004078805c140c000c652040f40d6600c0c140e201e800c00c4140b09a0703004050030141094810842081a01c801107044021980d044c50001e07a00040152000c07507080480d00007130051480c01040c802003640025003102034143c15284081450451a82d003c124084c03035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 73076584 1250 73075334 73075363
    0x120509031b0303090a02040510031205030601030c110a03030b010309050303040807052107060b0a05060d05010e130309031101030b060f040503070501030b0618010516050c04050606040f0306020a050d0c020a02040e 93
    0x1741e0807000141f42030741165520580c08c0691402071541da4030303201d244540380700d82c0e080864800814800c20356403500400c01c645480d400d01281c101c000c091090f07606c10170048040c0401d655001800d01c642c1c800c0e0491030159030001e0880b906d80c10141000166984039400c200d43c1481640310829100c01007000b4404240b0218004608101c800d4481c0009441d40c101410b501070031180d004a920340d1010050084441d10320341c0010a9814a000c0d404145c5025003e0f01d07020103030900385000640d01030350342410741e0307881007030010b1008403c80141c000d40204070036a0391121000c83c03001c1e88401100098801c03200700318212521680d4402c0198220341940d000e2035045041003142602420600713110041e4844180347c09440d0090f50303801c6206a41300d428007141e43c3d400c0b800315111240340034050150000c1302211614070785458141400190041803000420541c0c01085a55005000701c09403500070b469850103005201100d00c00a40350411100100d11491a01d0703914a4070180000c0da40c2c01d001d009 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 73077834 1250 73076584 73076593
    0x3111b07140d0609020d0605070315090501120311120f120a0c050708090d201e01051b0a02040216030215061e22090308011a09060a120509031b030309 66
    0x25103e003030103002058410b83c1c100300400c0050300080c1b014850a403003031040d9a000200b61403012504000d9061540c41078032100e080400500c14081000c4e90080400d81c50700b1b002c601804030b4000030707003230060b60b01e0803414501d404241040010001801084400007202c2d0300c040303a584824107030088034001046000011030902560002643da980103060700c10006040320b849540aa85000c80403500b1103464024051000c000c4500b800c10030300c11900d0b055616403c410900b10100001c0c0039004071080705580e083c80f46015260b00700248000c5080c650064000d56075440c641da01800340750790002d801c600510481d90381c904110000b568181c0260801004e0140c034541390140c2c413041e500d40c04142c0383d010461f0841c5040d000c03d9203202c1d00d1a024845c5000c542d82400d42400f9202d1034050b44100d00e161441c00c51301c924600f0020031030700b213000219040c0c0c0d101c1c51501c0c2c04488510ba0f141c07003000c001d440c00041c0805076a0000103400c180a032400c10300407607031000d002240c503400241c0c0e2001d140e500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 73079084 1250 73077834 73077859
    0x7020303010819050f0604060e07050a05060f0a1107080303040c050108151512040f12111009170309070801050603030c06011503090b01030c030318030515040303111b0714 75
    0x3030610314411140620119040c250080a0381810006e065070200d408642c0c0e444890204001484188000c0904484041400c0c0c6444003191461245044204030f5040000b000800f0f075000c0c40c081c2c071004414208891030543c0356500301c0d0f80c03030380240d9054504890a074800180c540c030841140e40309110020402d581e000081c401d00140f82d0102101c4103050300248252910240c828403081d10940c002c0640815040c0541003500c401d14559000d81d0401c40400c202685200b00042c18002042d0400b500051101142c1400c0340245038515105110a1000041c040c1c00a00000c44d0002d90322114020000f0307071191130800d03543c2e00c41c0d4015102c03507412110041016810140030007072040c90b6801d010034505481c0d99012031510090f08220f40b8582e450500344141030b440801c880801c07000b184072418403404d680322213076214030820003800600a11000141058429040082c0c08058006156281d55400f000d5086400c0000302140e0303544203036000021002c0c500c4640340e81d0240d01401c1030007441e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 73080334 1250 73079084 73079113
    0xc03060f210501020d020f070b0105010e180a110c0c09070207080a0b09030904020403030f030b0108130f030c020306130201080604020a320d05010303030506030609070b070c05030a030512070203030108 88
    0x1d00e520800e90702d9550034410800c0f8451240014084540d00d2048103030746901034508a000d162041c0c0002e0304201030610300300820780f905161641030801c50420480241d555940c084080d14042d07084500b1080c010a56401000f00010800c1c40c82c0750884043c2c1c410b42c0c0d88041280e035661644a20005503000824107004113010391070898000e81d68005403481d1850510104080c0d0b400b41d070003100060416203001c400e0513410720590011000900e0030074042d081030f01c401c084007031245801811012030840c3c168200360040454080083d80502940c02c58641801c00c4070050309100011fa001c140044001102460a8401c0310502d50540d103c0070380d400c199282d03101a003449900c01c0c039100f40078200703a44050540131002d0003481e038003c0320220304c560641c070380282901c2010700081d000e07034429024801101000314000d02650350711501162100158202078220030115404950507024081c42901459400300040240a840c128020110b4541c00c078201d9036840240b0403107400b0b4010320b04808024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 73081584 1250 73080334 73080389
    0x101103030c0d060e090601030c0b040f03030509011803050f1b0a0e0720010b010e0303070203060a02031003080f03160c051f09060203070e012006060d05120705010c03060f 75
    0x45000360782c00688151103101c408820401074074001c6896006071300400130401503c4001020b011407900395801d0500d00f4250740402d00741800000c040c008040380c0340481e64803036800461108402d84910b1807507503403410320303070384581c0900010307001c9008407141d02464074160072104807030040c05030248070030364540102d4603410003000d00813a041100c200b103040d4100e102d81d00352410a0006078000a14111001c00141902078400e542d03a000750014003034200940da004c661958462002d80001d40d4955901641d00c02444840e04004e11952011031f60a14804c2c500028600c00c8181c403c1250500503413a00035206d060070f1100003015513001807a0345490303038000307440c3c21040d4020b14004611001c0300d03030b60303001680c10440b00b000016403108181585903900c840c8000101e0070450030300c1c0580410900860300c803070000341510301408503e16681d00b040010000e05850104510351940c407103a2601e0f0a9010700895410100024140300d008155a11455803c3c0203c5035071000d840707075221840195090a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 73082834 1250 73081584 73081597
    0x50f01060501140901110d1d090403210b0d0303090c0b092b060606020c18010605041a1210030b06060f03040209041a01060e01020111130303050d110f040302101103030c 74
    0x101b1001d022420003c002c2084150b04200140d1a040ca00c514103d003044513118249501c0741c440c1198105000c0441d81001080000c2450040d404044006107032092029141803a54660030034818600c940500d0b070f00d544491005440380c0344007001d46a69400c0110a801240d1006070b02100b0740c0308099807003082000d4041e00500c11410b1410004180d1038420848a00c0e510020150300440100c070014648807044000b40d030b07101c0f4441c0f6120350406000411601940c025001c21828600f40961506921707000e541d6100a60000c42c0d034a8644204000551880c42c481141c503841e82c4000700e803144ca0000c0580c0d0003a0200031001e400c6903969020042907440162040e9001000c02000c000c1c20900d20705043e01030002a116000248a18400282100c00c845074084600c0000e000354243c010900c0060000c5036050b24003d9141c01e04c1a1603100203219804441c83e18074400103407000c1c519103400180040b64000c454400e2440c220340c000342d5408180e1001d65009410810000b6000b40039000078050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 73084084 1250 73082834 73082837
    0x4021503100b0f0306010f0f09090903120c05040806090106030203032b05040b060111210901020f01020d09060b0f01092d030609050f0a1104020a05090607060603050f01060501140901 80
    0x200e1503851680e0078103030b0b002c44002c00d01900f0000410019580051030502c3d61402071601c0c910020700200300500d44000b50180703002c0e44d51104056801d1612540c0001505100140100000004c8010281980d8041c0c0704808d140c0c040d020000b40f4182040c0b0500d0100c0750040d001e140b910406980c3c1d026016020f004403045610281c92100c8048514441d442c4910311440d070052040c00c20300005407100e40c10701441541948000c2203000c40e5242001410464406242d00c0354035803820100507414001100301d20b00712984003140c04410a401a04299281401a60708101040c2d400d0140080616080c2420307000c1282581c0170444c802d00740300000d0460290b0f00d01440c404d40c110004e054510019881a940c140e01e90080506009060040701b250002c0300300100780481c3d07544d96a00d5041144411544290340c045800d80d60140108100d41041c84024605587e0780d40e0f52034840028203850200381d800d0711070122504d840410521602050b01d070141c44e440a208000c1400c801c050748031145450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 73085334 1250 73084084 73084111
    0x30f0703082803050103020f12070306020306030c030307031d040908120c09130213240804020a0e0f0712020c030f07020a0306141b0a050f0d060806010605040306060503030304021503 80
    0x10780c0c100b28001a00c400e00c0e0395070106440d451401001560390010b60160b02c60780d01503289002070b20000172000220f03640060096229951000001d0410054003d8560940030020344402016842501025003d42c000c004418a0b4a520244422210030010041c00200c007040414040184800c110b60700a1031486030525006104000c20014908949000c00311600401c400c2c0210318203440d0381001d006100d0405c960202c054161000c2581800102c10900c450000403074155214981c403480506030f03208003008603062210b61ba4410071400c1f54410002142c103819030b00d04858038000c94801d01540e40081d4203000c0c3c01450140300d644000000c0340d021400c50b000100082103401340990788440c015a0a40c18548120b2010948000811965901500300243d002007600300c025583e50102c0da0b0012a00c941d40780c040c85000f4100d6404c00320a42c400c1c040005000ca42c400000c0c0150391240c1e2003406081d0b900c41c1810364901060320000d50107088a00c01009a40d80034024582c082035001c01d04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 73086584 1250 73085334 73085377
    0x607020913080f040e0a09020d0b040c08030f070b0f06010e01210f0510090605090a0203090f2b020105040812100906090b120a0f06020309010609110901080105030f070308 75
    0x40c0030342c2d001d45140c0c05008030100b81008440c011070640751b4130007032111003880720303c005034001540c80c0c0088070024065040d50010506000845180b4000390154408995072a2420019000035400c916811140c1c00040700c0006c2458011012203802858181c60720801039424400542d10001c071001080000400c0e000c144948132254011030343e080b0a00d1100050505001014201c1c007042500628503490604404000e143c50f000201e59001a4014006849442c3c00392554104804020844075502c64101408a0f0406660302c90810103c4500c0c0c1d140c0d03843c80c155090f2300703880007141d02420540083c40b0046651007220803466002068460810a494403006400103c99294100d05141940c803009000d2500f4158141842100000300600c3c100d546036480b01e641390307a1001c000b01903a0b00480030445880d0250007501c0a400c03075050521054000040000c11900400450380c002800d0340c000044604011070440000700701080074200003030039500c403140d1030340c00710103036920040114020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 73087834 1250 73086584 73086593
    0x105011b060912020706020d020d18030b190f06030209041205041a0d05150d03030b0609030a14060a0e19020a0b030405100b031c030f02160b0f0106030504020607020913 74
    0x2c142241e4842d0080300788014602200914000003604a541903620000c20081441d800041d00b4054420900d441140c5001070f5100d002c1b08010707644010020320610302800768413074810703010105906440a0401c0103100704604003043e0b0318640b001a400245540c04503011039065500d0441500860503e940b61035602d03000158113203800d0416080820010500c074690307907800d004a0360070088408083c2c81110741c0c800082c031150031a0318020700b8150790300c4035079000351a81020384101c01c8004041c1c800d00b60031810120b03000c06200000340080d00408001902010580c07140c07150030282d1400800001c0b0613594400c00341200000c05036403102c0100d0b400550540100001d5101e544035001a00380708180c800c0d001c081d24049000ca0b440f03a0401e0f4103c0d0a81e028840c0b5503018482c0361314000c1054620550f0f100024071810131040c2000c0d03e280c0c1e141007880b5010000c940140c410270700e5851982c0e40e80c102101295001c0d03500a41c428010481c080c050b10300190119001200c0031226250141c15070344 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 73089084 1250 73087834 73087841
    0x906120f01060f030218060901210905070509010b0f0f0f0a030e100b0f041a0907020c0907050301140f041b021006050109030812070903080c010b040614090105011b06 73
    0x181010a500094010b1103001da00c41240c0d081c08010313050950074802c1d0300240090704022200e056005104c042181039103680301c1c0c038009106850305845c5403401074009520030054156000199840e05c00c801000640c1c0c14140240c0b41200c040c0c1d0302c040e050401d1034003c5000f0b44c4c8451428140583c0601c900428800c59100503d00601c15403000100f03c015074070201c0c241309803050440781ea90301d040195151500c1d01815646800811100010380316885054004c50285400010b80c100d6280c1c810070001c140c0000700c640c110001218450f1103903a48101c21241444240500c000c002501c00310480c41e070074180030700049641d00620210321812505c004450240d40c41c0d004500603880039401c400110032911944d400343c00e003843c100309000d055441e840c409220715850105500484000205038510402150019503805a15550360700f02d908002030182118511051040d8a0045c0000b02c40d124241c84002d40c45c000703005100181c1c43d1038010f440082650200c200c80c100f141d00c840000a10910 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 73090334 1250 73089084 73089091
    0x102033906100e06061303060c020102071a010905160f030c110a03080414190228060c061a21030f0c0304030501050a0212040f050312070206090c0402090114090612 72
    0x34042c01c4a5103062074080c24150007a1201d030050740200580540c030074804400d82c050300d8000001181003400c0c000b0880c02031040c0c00e00509000080744c4002c4552082442140c100c0314413803001c0c4426102c08032401c1c0d64400220004021900c10242c0c142414040d8229801034909070400b1520071002c0400c4604081222108900207a40902044100301e21404541d04100c003e200405060902c000c0003104071220381c0000c0c0c03003110040c042010800d140300140800782e000c0c140c4034400c1036540d00e0151650041007002c58003641402e1400ca01081545984e82104400030b208110422030354140c030b040c48000000c0c0140d1400b08200b9a107048055800500c0360701d115038010b50303070f030342c6141070880c211500500425400ca004004540b00c00c1d50700f001258105401485800c050000d619010b8650310840c42c03180031038442103042000041d00810054410344144050300c0640040100308003c901c60401400c0c0840c030004181c2e10500400b03006001460800341c5543d290203a0311007050039011046 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 73091584 1250 73090334 73090351
    0xf08040312030209150906040b0d02040b0a080f07030504021003020d0f02041805010801090b06060a020304030b0a020a08130c0611010b12030901090f030c050d0302150103061a0102033906 82
    0x41300d84140c1400e1441d07004c00d1201c00e0605060038031036030010702c080c071941c410302c1584140840c4110202c111503048800800300500b10340d5603041400700c00391841c0001c5036403210300700310301000481c0700b8002d000300b07449154002e000d03a08642c08114160001d4108072104084c45607103c580300c040f012244014005407002410b00200c07c00100108815140305030404481039040200381c000150602e02015080202203403002d4460315030001c201e00d14080ca500203401d5000500c1484807801c2c030396004040d500d5203581c44810950740c410420038903886040004001d0100307940d04001581c40b034020030b400040c040300041100281c000000c1c0308000c450200b40c207103810016100d2174541e04500000c0062900d040328030344107451611019005607051003034038094900302a020701014401c1c042a00d00103a13110381190a5616030a115005202c0150307000e4201a0b500c4124500398000025905468040140050014103811888503112203a00080000c0c0c1000e4141050780c580500c03846104034200c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 73092834 1250 73091584 73091587
    0x1104090302071a090904031b08120621060c0c071205012301060203040b07020105041d0f0105041103040f030e06040b03060112020c060708060a050a0308070203010b010207120f080403120302 83
    0x20403280103a411803442501064540820013010786844004683e42d10603010706144500d600f056040b201900200180240800000521303c055224050041401510182c4640f203040804190404441e04031070f80110780c40e400b54000550078182c0308010051380b0700d40340c152808a90b48140d620040140b584048030140d440c4c040503403422000c1c0d12000c683c0311290040403100d500d00a4045e45900c601c0c040c4010940300001d00109590107a01224014180c0c55005a280303103040e4a4156440d1060b0345010100300c111000203001e20b068083e10040c021030130f0140703240d0340b01da40d940014880b4a8804509104140f484109203540d2080944014036020306440d81e0307840c2c84000181842000250b40703007114418044101c602200254440c4c2c488c1c0300307081032103050f15100b00180e80a445036012903480145008044200301004015201450ac00d60003440184c0514006a03103901d1240201c0400c45038171160100403c40c0d4015409109000d114100c2c80c00f0740725103d41500303490009281000c01e40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 73094084 1250 73092834 73092839
    0x40b061c0f0b06030703091b0305011508010b060d0230040506061518280905060a1215020702040c110c030a120f0207120506180a03020303040f110409030207 69
    0x15000c1c00c4101d51207501d0402c856490745001904502002c0e0580080503625014002000094084489044016000d40402d591380f0700c0c209003c0d080034010344079070740b28040700003031100014022550b2070740c8010070f01c9080800c84001c00000f0741000c1d0501c03506010000800f606001d00304051144982d004c0d1280040f0b28145c03d00274030b0040b024280303034003075000c907118184a2500704040d502165a00c0152415401a80e000034010b00311005c40c6d00e401100d003100f20f50b600d06001310020b040f51020102030000f599001d0070000510450311030070200a4100e014940080c0bc015201401d0f107140110041c14000c081c0c000c03804542c3c0e041e110b0303000700d400c09481c407005110400c184942080300700d00030000049290744895100b50125010401d0003854460108494000e11001000c1c7c00c580b40d000ea84a41075007080c0396034000550f07580402c105000d8000c1015000071508100281c1c160f0019807440c1c5645d690302036006640030741a202c00b81c01907030011459855020700704015020b580101680c90 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 73095334 1250 73094084 73094137
    0x4030807020a060815060714060a020415051801180905100501080a1a0108060d05010906150f0f0302060901120c1d010525050102040b0307020f01060b1602090402040b06 74
    0x204aa04004203000001003040340760485e00ca85949282e0040e11125201c11240c41e15140d400e6182d9200700c680d01800d01081030303190041d030180c400c0320041c030383c500000812840c05803180e1190b801c0c105407032aa00c3c0110307505540200100c55078801201e0740307803d106544240090850341c0c103940113915140c4940c81040340d9a4442403982c0c008400b102c04210f15481004080901c0b201c1d861014140a03840002902640d254030b000104035402400034001d111851074440024080d0003d4549008410040403560b00c161408440680340c100344841c0c9154190340821029400c00722005d410008940c511220004180c0a440080079458952100c3c10022552440d00048041c107894104141845548525002144814034030700417801940e402000ea411315a000e0701c01c4d90080340c45140d00005019456500180c0400d44007040402000307001d0b00c654800700d4a210b0f51110a001c50841c003036034005403030402c0240d81c002d4401480011641904000701e60150031003000034100340c0001162140c0328 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 73096584 1250 73095334 73095349
    0xa11030a0309120f0516020a0914041e0f0b060d0f110102010b040e210f0406020d080601030507080105010503130c0621050105101115010f080f0c0619090504020403080702 75
    0x8000500380141140c1000e0b100030404d00854406c500e41c0d030141c1c0074803070a40d01c8201c2c228002d00000d4209000e0725045600c0a494a0019038003100c030b402650301038811507a01000039031100c9601c404808840c0002d0b442d1000c0010001d03100943c80355900c0e001c840003481c0511030307024045c40303141c14a490003030400c006800c50780d540c44000e010f01c3c10550f00341080000419030a80c54103018140b030701c807000344143c80d150500400d0b80031206120b000401140064000441403c03002c482e90f120744c019618180114180c1d00c0c103841c0d1b03201250000005105a60080c0040c550020104000c00c0d06202240c5801c0b6581c881c0380c3c031400104500d184954501400f041e15104800d998031070604c0103503d41030103d400000380000000820100c84d40e0002c40c2d0606000d290181a025000c0e11030558540c91221100c030302600c100c680b00c0c8074500080020311030200f41901c4009008151a007000308a44000c003400d07880d00e0214041000303a2001094940e1030f8805440070358050344100e40ca0705141d1040c003900 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 73097834 1250 73096584 73096613
    0xf030d06061107080304121b080a120e03030703030c0e100e010f1814060c0601030c09050601020c010c020907020102040b0c1b0a0f09020912100905061302060409020a11030a0309 78
    0xc60708840b20a10003104d0002c121000c403040d01e045400004100d080035030b5a541021410703051a0407030040040c0040002614070451030003080700c034807000c840d2070041d12449111280c058054105100740c1c4003180c0654001c00b4503005c3c0f8145040d403010b0940001e45032003002c00c100c00c0454000d4a2490140d64400c610100210740fa090059601000080420032481a840f40d80043c02e035130f08000d441a00c90100352045105860100d5101e940c40b851b202a2541d401c2c01521300c49481c02c1c0004840758800118440e00600c10384524040382d4141e000e00c00d202200500fa0b030b0540d902000000741d0b5405c010014406101e02c48003806144814100b0702c4204080d05042e1441501004002d1040d0b01d5081c4510044419001d0016038a0b08004003041c1d020706103400250203401840c0308034441540c581c010800d0b45200310309441c0c8641c0c801902181504051202940225083c031081c08140c00682c01032440c10780038200040c5208011449914550202c5031980c00651941292801c1080b004c001024 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 73099084 1250 73097834 73097867
    0x5010915050102070b0c0106050618040b04091a04031b0b060310090b0f04030c020414060906040c050708070c03170a0801090204150f03150609030b130b04030c050f030d0606 76
    0x110207180000003540e4100034001c5115040c000510504085025444030006000c09025a40c0b28880c80a500d00c400203c0e00381c03503000d241043e1801c1443d142603c20704044680c840010658420054114100080020f000701c09010103010a240598010100050302c0d61040c0f000360b1651a0040a040c140b2400e10115407035a800c25000f40c00051440554540c003240702816541156034070b040890f401100d804000e50402d14042c03018040c1121024014841c00050b40c00420b5529920180001c842d415540e07100010418402100041d0540008146550140714030f2101940c6036118800e60b00d03c2c070201100c0380600040c10000c0b0303681090b4054018403a260045040910342031007403285144801500c0c080040022000c07005074000c0d80041c1005c0900020440e89580703402e0080d1001c01180000d881c4210100e000551001c030030b08800c48602c1c1c0c070509044440d2034036542900c101d5002001100c843c082d0350191b040303100080000d00000210520041940b40c81c04c0e101505d0080d074600e5034032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 73100334 1250 73099084 73099121
    0xc010204050418030f140415080621030d11070215090310050912090612010f06030e070b0d02090a09050702011d210c030c011e0c08040b010b0702010c060c03050109 72
    0x60101e17400072020301030036626082c40b02c001103108400c44400e00c91500054840c50392910440200381d440003249108102c10f461010001d80c800d5154480768404200328400ca030b1041101c40078090030703074204065010088011506080c010790000d02c15018081c0416814000804c1d030200314601000007000807000d8010801c49804c14510150f111040390181c0240d60100044041c0c141d22403904564001900401020362541c44500e074090300b00151003800b000034140020700c2500e200c0414070004407142030308020310306441c0440c05400b941240d01c4855101c03208040000e100010340c06414031504070303030b07000003044855861142c5180c021412100204c0c1d10003440200d608254107660550340c0203205550f6141d0186000c0245144100d803d50405075081c030350f0382001e020110101120101c4440c0007800441340c407020443d030000d070468000d04008800d00040180c0d60700080105a031034018582002c941003540c844d64240c580c0c6800000c0041d0b03444004028403c40c51150b045001c50303000d02c0c078 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 73101584 1250 73100334 73100381
    0x140a0b0a030809100509060304030305040209060a0b1b01060302060c0c090f01060203180406051c0b16050f0a0302092106070e010507060e0c0307030b01030606080c0a03080d0906020c0102040504 85
    0x42c0d81034028210501e016204103079102c0344660280c0c051343c24200004210303654901d0303d40340080c00f03803400f81c9089001c0c50130000030581601d007800010088c0c410340782001d81418041401080c0c06400307040291041d558803200440980c4801008104445011006218411188041c072242e5240101550f003d000013070018032103294003200f12003c00341c0120380c00c0a20a589800580101440e0b406564401540114001100078010030208400d01a14040d405076446d00c4000d1004641e209078100020410407140074a16610000342600300414900182004c882c0780100f0740204440d180c100030201600b140001441d4100645a07000441b442e0800c1c0b0342c4802000600a0300548500403e00b58845e6154000500d0810841c449404010100c81a45070b9038105040c0ca18000c0c001a40e90b80d041441c049000d500c002480c5010040291000c20032901c3e6455400280e0010300c00342d0041c2e5255292000440c1e50340c0043e1421942010005039203901c3d0104103c00c60700c074401c04000040038071044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 73102834 1250 73101584 73101593
    0x3040f09061d0a06050307080c030f0604031e110d08090d0207050a090902150301030305070c0f0302090601030903030209090420011403040b090a05060c03040201110a051b04090204140a0b0a03 84
    0x190500c0c0814a40c100615142d0f00c1d800005484107801042d090306c00e113a000030300c0380c00018200b100400150203440d00e001181c0142512084100d80280103c0c003102e04180c0117440440303002008089038a8001171020600c01c50b581030a40c0c20030758070000b9000c1018400780c00b40a12070043c4400c2c650000b84400c91034800490b02c441154854103884983e0b80984000303644a07108400405240d61610719520742e100e2401800c0380d040180161608a086000030400e58007450303501040c0c0c2d80080c1110380c0d0f940c41e50011009491780e20400c40405400340800c400540701d401016008910480e1510b0b642001007200307141d074108000c08036040103410040190413100450489030440e4010b41002070b25943d45184924005c2100b0b40100396104100800c64451404006140281c0c0300340e81d0440707171120081203241c2e98111110081d005801c1030f910702d82b00b80131542c00b00005000c007400c00300d1b2410443d00040c049075092280c0442c1d01d00c0410401690080381e210b00e000403901140c804003001c2c11500c0317 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 73104084 1250 73102834 73102859
    0x80709080a1505060d150c030b0603040f0803060a150f081e04060b0303040e0705030f0a06270b1c0606120302030406080604021303051501210605100306090503040f0906 74
    0x686080d5a514070200e04e80b43c5410001800031070f0012030404503a18602110350062174113601d00c00c002403509032603150902d030000c2103e000719004440f1104d51171103904c0d1014a5480900403030361007142c2c40c00001c1c009000038500010810f080e19900e002201302c070400780501000803d18510202d0302480303e915520605652074000303401810000740e0b014141d010074a10f2255070812100703240d4100030040300d5907000e03005601c20744c002d602581803501e82c8103401d0103031080d0740115041003100700d440103039511031721280f8604000c0c83d010125004000d00081132085c92245035900894105141840911156018040003410340840030951030000380c6009449005502400b020001210040395282e501c41d01a00c500003004001c0702c00039070b0380c0c0c035026a0703841a00d8030015003003005200020300074000c85040c404a171600040340f10720b074510f0b694000003000000c06426040340c1c90b0b1404804915144900868903100e000195592800c00610040c0300741c565100c0d1500324180841803000144284 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 73105334 1250 73104084 73104113
    0x803180319080706020706051f0f0f0314100203090a05010b09061005070c0e100303020105060109050901091112090c030708030a0906050d1e020d0b060c03181305010303080709080a 79
    0x252554543da06468020086e20403d0006000c43c1d00f00710601c25070308102019034013040402a06d41c80c2d8569200100d0004031340c10300c50b0b918601000300c8100f0102d404141460440e6442c00133440100c1800a84001260000d13245d0500702d60101c08030310208102480780020100782160001e03200d1404000151002080c8050001000b501040e80020441c41400003401780161402440140c41c08800c0050020084e100c03e4005600340342c042031083d402418444180c0340041e1090000340e00313001503000901282404840f42d11420000500d07000722000c0c00301e001e0300100000d000140b030100f0806280407130301c1e080485140c100b045601c1c0029001080c1000302c60f42400e0040d00e40c2d500c41000700c005c21040324843c2c10b48a18040b90804000a940108007940361802d081018880c03002c144035440c0103203c0c228640e544200582d14005194a407040c240000040204021201c28401c0034180ca0080e401100440d00240074040c0341d6800c400800301900351900281140a005d8403075940181114 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 73106584 1250 73105334 73105343
    0xe0a0b0306011107030c0b030f0a1b03020f070203070b09030d020303090a0b0717041203060801020f0f070c2310030e060a051906060801050906041404061503020a0803180319 76
    0x10790b01003c400034840c420007150401140505540c0e00c0411783d013660300440300d01001407003800004441e440c00b44038011600b06605e030442e0041809000690082d8880c442d0300320100014004940182c5d810071228002d4521034030740355114091501403610340501c4007070b002c0941d007051040110b0f0030000250500c0090b00318410700c4c4d150722080c1040e030b0090741070904e08151801000400c0140b020003402110300b40500d079010041e095a0b00201401c07400341c0c5000540c142e408120b035202880e003500141c1545809002c00e10a80c540c0c54580703c00f400411451840820000c0c2c07508006442c1850605c860054941001d018403a0142c9055490369001000305070100e0b03941c03000c90340301c00183c1005900c0c0903494500f04502515a00084c01d5040300f48a414413400c2203000181d8036090034025041509916100c1d524151138555580c4040c1030300d0400c107403d400039035900002683d24a0181001042c4540c050b50b0303a000d88401d0f006c550314030700c0c20081c0039501c040030b82300000041c10340001241c2d401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 73107834 1250 73106584 73106597
    0x301060c06110904050a09030e19060c1401020301120c0b030c16030201060503031303140307050a2a09020304062a0302090d0602070c0f06030e060c16050d0e010e0a0b030601 76
    0xb94040d04100e80940c0ba8200c1d04070349020100f01000c01c40c1c2e03100440f4240252030b440100d80c40d0b04100581e0310406074203c038070340c2d5020b40700f003017018003e40c0d44400141c0b10f1032003941914070f4075071400d089810990110403641c2d9400050070a00540e1500c1102801100c20071618500e401800e0f10700c0c51040d010401002c060002550003898400c1d448000908002825695a40c1010880000e81215404241d0b031071800481c01c0340c0230060000440ea28143e00c5405001c90000640b15140c0301c1a182800460107903120f51505403007032078001e030302001d026410001a100d003003904019088030b040711007000c4401e00e002150015480301e4844210410158600544e40d0004880443d04c200540c0d1f40041c0b1a81c008036044c0b0070014601e8604050341c0c400340001d05034550b01c034000c80a07031340c00c001444403540051011404030300e0b81000800c401c000014054031808801c0e56200c0c82e100300c078a00e940c0040d4490740782d01c0300c0d5a4000046401d054007201c121184c181030100d092000d100160286051088 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 73109084 1250 73107834 73107851
    0x50c0307080d0e010501030b0105040c0504080c10170901060f0b13090b0a170f12270f1207060201050606040605190306030b07020d03050604020309060610020f0102040f0f09020301060c06 82
    0xb0aa0008024103040707000a000d1941d4030700d40691106000e010b61441541403c200c460614401d109035000c40c0c20050041104000c1401403004404c070548000041007113908416440c44c404100c00307402a001c80c400041c03410b18000003500b4981032608000207524082182001251241b0000c01c00d580c00c0a0000421440020018450010b6580701c45841c48600616025070003020a001c0d42c88901801914260340c50920802d500c0e20500c010210803d070a6980a04d0440303145122404203903000d8010701c4154402000104a22480300303801466a002c140706204141d828043c458100800b82da8890400d270521001801d2401004480041007042c1c800310002c01e403013a0880c03030095030050701e990020f0914aa0003501d4810540d00000485e041c01d004c102c0d076080c14400c591003404d5400140c115901c48804222240c8603200742d40f011403040303241c035000002d402e02c0184000c0040300c1200354120720300b0200083e00341d0790340d206944803841400104843c039003000b00c1a844a0748030000080090 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 73110334 1250 73109084 73109107
    0x91603080706050c270325030b041e0b160509150309031e040602010c09050d0b0405010902090703090b091b15070804030b01090f09030e0d1103061312050c030708 71
    0x240d00c00c5081051140740426400384840c05c5518100c00c09406503000c0c080d45070348003c205981441e2520103582000410800708007200c0702180c0041c401e5813800c0f140e0300444a040c80700120b0340710079525400e041090058210500c40e50701064401814080c0c104088400083d004480070134108000d101c0000020b03001030000c0c0308950410b54201d100c111440c590301040000e540040c090340c03016620b020044a0014014000002120402410b0300c900c01d039203940d80d0182580240044a656407a00c416038010790703070303c5041e52140600e55400180c3c41c0c214117080c80c002801030420342054120356100c0c0c185114481451304051003c9c1c68a04504003600140103042c450030102500113040401c02200304240810028101c91007060207200a040100c00c000c02c88000c8075006011030600724080304203041a19545844030301030601c05095030024000b207814103008a94a51841d02645013000c1040003180300b075007245c842480d0440c10660001c61140d070f42e100303482004d4854a40807480203080c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 73111584 1250 73110334 73110337
    0x30f120a0c051006230f0d0203031605061501050c07090b010c05030307030605040615080103120504030c0306020403050d0507050627010f09031101020f2205060a08091603080706050c 80
    0x99001c01103d0b07059030300c0f0300d4a000900c26805014000303803034922040c88103000300a80d001d03000001030a0354100c202d0001041605000480d040360540414003850020441100c154034103140518054102450b00d00811210702041c001c0700d9060042c2800a00b85c1100b00241c00c40665522400006481086800503902420002001409448000700700011107516410010445406079028040a61122082d1700f080d40c18940a200080303c5900410100311010851003620805040442c5016100c0c4c540e0501012560015102c40350000b9040041040c2044243d40b146010314110b410503056688150b1610300103044200030701500100c4a14a60403590001045034414008100504580801102034468100181c003c20340e0484030484c0c008040c0221061581d12407984c510b0403418604520b51508040c05494141c800400d01144646a001c0148502c440c56115015a450001c1c225460034207200716040760190806400c1000804402c2511421b0b54007040c041243d980750200e56006 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 73112834 1250 73111584 73111607
    0x7060905030304080c060c07020d03030c03020f04030b010315060e0c0a020c1201150e010b0a110312070210060803091503060102010f0c05090909010506010804031805061b010b030f120a 81
    0xa804000103200130032155800601c004801801035032100c3c3d480d08a00d2060740a1601d02a400c00307000031002001a100c0d41c462040e1210ba13083c01800e107440704458403401d8202e40c10484650003d0b000510502032107070350000d2240d940745414450242401c0d40102241c1c405001e0040003100420564030300b900034480740d10640c0001e0480402400c612000718082d0039420007a1044401c200c0b8042507844c00081107606a43c8490982031030120030001c100c1f815400403401d103150340424064903000c182d80c03050050003164640c0c02451030079406d600100446060380c1c00302e0040da2081000307004a0f00c845014254405401c555039440ba9a10700c01171b0701500100b00d484170322500c0d01d90000011345d007100c054401c00c4d00075600d0f82c000c4d0750b030724000f9401c0310001d075809030105030460001400284034240b401743c0310040d86000013000e41d6490200d140340d0440c0ca041e2015400b0000b0040a0220921034400120821401816288810080309468038101490410031500c006004036078503000304000940c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 73114084 1250 73112834 73112843
    0xa020d020f07060b01020f0309100c0c0f06021e060406050720030408150105180601170c0405100309030f051b071404060e0702070e15041a0102190c050402070609 71
    0x16951a51a40c6855503031220381c1c203c414501d0312150042d04d5100252031820740c00301c0001540350101c40010400c1d00c41c1400342ea07604000c0030450901c006200d40554200424155091a07801410142c2c06070071b098121100702d00c2800900b200f24000d450016503260400c0c1c0040000945440d10001103501400740c1c26410944403111000c008419000001031041707400c0320042c0d48030352844030441c0c140c003902841002c0e4461034214031038002c9100d05000e150080d00c1414050441c0714191409582500c0844481c40304080c041000c02c024108182c4004c04010a171a00700002c0c011960003400945138100e4100c10084046078050072002c1c0341004a4810b845601200c10407942c0d894054004084603182c54061400c0c1500010400d900c0300e00f040c054821900505015410a0100034500100524420441d2444101010140c40e035204a40004140c001c40100b403080500001e4a85080803800b0081140d40d82d1890012030b125070789200c10759100701e03030260303590030581032034005070070810000351 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 73115334 1250 73114084 73114087
    0x15070e01030216030801050f0d08093c1305240102010e0f01020702040e0c0a150c0f0305030402090907231212120f04030507020d050a0b090102120f100e0a020d02 71
    0x10f05140d00314800904861013100e1208424000c01c0500080d50354000c2c004200c0c1c030042c80100e01e41d10708012a11202d803151640c4001e820030300352040c0000d01b119410402c2d241111031000406003000105c1d400e5030040c0050902c11030a20303009594010306459400d0011541000110380e803a8800e401100c505c0c90070004590a60860340403042c000d5000e1402248200d10300107401958a0340445c1306000990002c0001ea2141d00d804800320110300b0492006080000400140001841c1d24108a00c040d0190b0b580304d03180c4c54180306001c001d000203000710801b0f9011550800c080c2c0403400309040c040388003100407524070301c600c00400e17000b0040481107617642c0180070002d03031041c2040300a46840c00100320400029192845070350402d001c1514083c2c0015404c01003040581402c2194410451080c002c03074030402d03034940344c4940b01c55041e0b6040c21240d4000401815803a4601201130700b00010311800100390606513100c805904452041d05203d050540004052241e5a410382e26681115281507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 73116584 1250 73115334 73115377
    0xd0b0d080a0f0917070605030a060518070305060a030b070c031103040b03191817072a05041a0d0510020a0309030f03051905060a0b0d06060e0315070e010302 69
    0x50720502204035000001100e98100207136040c0d025106820804140024100722805c1850440b040d506c000c281d000341e607464041c0000c0e030f42c030740c14805460035201000420351800c00d0030b4000d040e03841c0941402c0c81554485410320200381d80e0003400b0b070451054100715001c031595243c182c4100ca03032160001140d00000c100002c0d9071440000030341c4078400000c2c50740c029135101141c101c00c4809554170074070740c60134072032481c400140b00c0480364034040c40c0d034219035003004441d60b47c018649114440070041c0d14181215810b488401104440c05071400711800e0203000060b402042d0314500c8030340840d200700f1800003d4401d11506000480c00310f4002c0b00300f0340d5260321000020f03004c1e04c3d244400301d0000c1c000c021010240c5110b40b04035402890100b4122485024550840000c0c203000f070241540282100400a1000c05403401024074850300c1d44003140c52807a04402600210712605011301a80190401c403c0300308000311060390013030650a08015821014004078002d02a0b110a100610241c00c0c80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 73117834 1250 73116584 73116587
    0x1081b0a200105010302030f070320040b060309010b0909070503060a020d061a0406020706030606021b0a05040f050405070902040302060703050307090506030f0f1014060c01140408030a0507080c0d0b0d080a 90
    0x190617a40250f04480400d20140e600a90f11001480054801c40d2100c1212000d00d0529410000340368004101140d0200305000003030155000b6286000e042e075442c03c41e01c0417420060001a030054103040a400d1042c030f0306010a44560303005004420340e0360f00186c540500382d03843d484480605241e8094100c1508614050b0807164018000c0801500c00c4140c00140a41719004442c25240c0e96400382c00081c51103000c20f54800d840c6902258024100321002c90980c0700d40c4142c800b080d2030254040b840342400d040c65400c02900e60005c89440b40100014070150300e640046404140c2d161401650700c0c0d441c05401c4407480800c0c0c200e1030380040000203106ca07039001004024014488911066100e8030340c0d031502018680c440c410358501c50901c941c0390350305181000180c0f021041d07610012542480c00f42852510b0142101c5c201c460b590040280030341c4048034405c2c0381c2e0000541c10000c01d6800c25a000c40341600a00744086060307a150b1140c400580c1b104040000c02d01e610110305902e4000c1c08a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 73119084 1250 73117834 73117841
    0x40803040b04030312020901090e0711061314160e0c07050a0f060c0807120c050405040c050403140a0f06020f0d090804080c0306040b01030b1320040b01081b0a2001 72
    0x8203900050440c905032102410500c212104000140c45003651242b800050201c007480060690090101141c210085080280801c84c03040c940144103614100b11841c0640e2442c1c00b418505056500904100c60a28014500f05041e520144424035059640050513212442400c000601500800304400108000100b480d83c01b18030808092090780344d04102101e188030101c079000b00140720741e4181d030283d10b00355014000038401e070b00d0312600d0b103a1070700003040944c1c000c40400000100d00140400601c40c06400c0b071100e00e546900502440905074641941490300754801138590b641c0040d200003041e5104040f1912002c1e64602400050030509008500740c21a01c503103c018040e10080504901c1c0100c0c805101e254003d080c144140d0a40d205c000c0c101800800c214078803010900c2c0761000c01c120045640014416080308443c448400007404259410145241e05201442003404250754482e100c0b440c04440e22801c0e01d4490103c1d4a0490302e03031024200501e450b494104d8141d2004c2810740 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 73120334 1250 73119084 73119089
    0xa050d0210050109091502090d050111030a110414060d09201002191203060b03010b191407060b0102071e0905130203030a140f0a0816030e12030c040803040b04 70
    0x1c20400e40e07981d1201c01d02520940c160081ca2500b125052200740c0310340c0c0e4040e113852000a403641603c21443c0d52507d0071100c4c0b65084100c0340707801104000b607240090181c948238140c0120034504051504000e00300345442e000308203118001c04110702000300c1c5a6846012100d03005200342d0010007040540001030401c2d0a14940038000d00c25115540c035000040180c0d40e088003031030031207002200303450364030801502d0001c090406480f12070010310204280003450203449068581035803404000048510520090f2228083c042c80300110f004100e4924166280c080e00004081629500900100e00700056a00311851518120784600c0e21540c94680110030f450140004211540300c03c0c4200300c49405400000354154000c20060302254465100c460000c0d405c1284207050124903900c1c5101a0404080040065680c008201d07410020078458109400c0750305080140c20f0350980e8140e01e03100c0e4811a100c071401d00101081d0f03507903048401c444c010720114003038980381c0d07440e000911181d81c09031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 73121584 1250 73120334 73120363
    0x17070507080106060507030c0f0b0c030a0b0103051017010b100201020403050105010906030c1a0d0219080612030a03110c030409051617011214062e0b0306090402030a050d02 76
    0x400c8085900841441050183c42458458a0070800c1d2030f0b0b0101c90001190004440d55041e142da41c00020780c4021100740555003060540f600c91800c00040ca040320001411281003608107018081d1818021800800341d400640c0c0050400942c00c04250240900090461b00003054505003201c0583c1940a402a2440381d0000d00032642d9840c41001a5038103400007511400302c0d02c1c402c20060506206003280040d00303500c030a0030b10050088410490b0015170f0407a08105603103c0944803a81e05c1030100d82e201d07030126005402d500281049503034038000c4902c10014103503100c60024800040b0001d6594129201d000c507603981d900d0380858800703010b007941c0d03000207010b0f40c1250741c00183c01504030017015101451003c5240e864000244240c10795003009552501014481d13002e0840c060080030f02c19106d888a05010310a101d64400c4c24042007915125100b03100b10062140340488400c0700c2c0c03c01c80450b003100b565191800001e060103062000140113104003034403d0341c40b54020588240740100f8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 73122834 1250 73121584 73121593
    0x31602030721090602010204050a14130501091509140a0e07030203030c010615080702030904020306060708160507140d110619020601150f0804021318060b0906040605210a170705 78
    0x584c882a4245e0086000b0181e008060000901ca10b01d608180300e8181c00c03000707090b911101160011802258401e030402000b05440d0200015008076036a26a40100000c0100f0014180240c40f000343e00c1d9000391605241c642c81d00740e2401c4c290300400485001e9600203042d61f03580e86404000c076000301128403601d0301d40e000320308801542e54056111035104080c190081d40ca04a114130810009500082500c0e51041c2e0500c01000441c0340e010140203048071700a01412041d1240c100a45030994030742c00038848000f55000c40c185600d5000e07a01e07840d15071001c00a0034500401c000104503018014481d080d804030384600003410b41e800103280341250b08010343d01c4018580180215100314010980300c000c035440501180040c18020802c0103c002d20750b000080022079000400c02c1c0282c101e40a8444644440490b013181c40c2420750950011021503082140741e10b800c02248019204000001410100e48683c852900c4180101100e103603021000e040c2d50000c042086009401029003601d0b28402e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 73124084 1250 73122834 73122839
    0x2010c150e060a18051207060f020a03020c0f01050106090e1305010c09140312041e0519062a080c160f061704030509190302150304151103160203072109 67
    0x1070b0803035010b80c60b034100c5d010308020400b54002c6400c65000b4901112520b03500c0c10442c01c606a144094462801071f6a405079903150b505012a2420b04070303403400794141c2d16080c0100850b94000302075800700d82035407401c242280d0b43e030b10303030251040003810006d80366508280c45034402540c44402031058034100c445502c810500c1a0525036150108000388403c01c4080005010100640340c00c0e00302843e0740020000b007561100d010401c12264403580031611501440d0a010b000d421904580c0044007098070441100400820018400e02c440000f80c008800005e42e079507100001d00091190b032030001030b60240c00d55107406040101140c2e2144400103200c0350014841400306446007401780e50141d544508021045040201c200c03c44801d94414035003404c800001270f2103042d203003000446020740ba40c0c0c0328a03003410421104a00204041503641c40c090b03000c0b0034031800c881905c0d00300355132f805019207540a05006034a58415800c02030044654110b11030110312500408000480c12079a8601c101ca0707 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 73125334 1250 73124084 73124111
    0x301140a05010e010f0e0609090a1b090608030705030403061503061404060b060c0a020411041a030f010501020703030507060513150b100306080c2e020a020a06050c060402010c150e060a 81
    0x4041b030040a1302c5145803408907d182c60305034040c41d084201c1c1d005584900d0015658144114000c0501000171141c0706800c020070b10680c812a030003014810040c5107040a04d950741c546038412400003c20b059640c1004050f544280070401004d1540701c0703000c014001100c0045a039802d8201c4003141ca95040c0302c5d00c14410f05002043c3d0740780044080040c210b042c607a5003080050400c1c051304802456040c0300c00246901248258100340c404001c18959078101003604030713281601600228107540c002441000020b80c05000ca0300900e070230040020300b984400b1041c02001410303030300282401c40ca411490000c42110f511421803510100d41e032660090318418150f0a0b200785100e1440180c01a640048950816800c00d54010300421084a4065142c2e40045141c00002c2007040041c5d2007244c002e0f0071800c010f92591b028000c03905009041c030038442c41c21641ea00780184004d04000c0244d02c2682044584581c1500c0301044050a0210b0201c055401e0396481086469010703031810014202c1c10301 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 73126584 1250 73125334 73125359
    0x1e010510060503042d0803010f0501051e030a0207140f011505030a110d080a0206040c05030105160309030c05030315090a1505060f040e0c04080114010e150301140a05010e01 76
    0x210060340703039a810f6a80c1c2e0b80381c110b0450b1104001400d411900e48110420b40a5100c480c64068401d403180c948950504c107200c0039030405a00300c2da052100400110080c9607910b10344103103406200a04036940d64444203038801a014000c401002002240801c2d4823602c0f01146001c05014840c1c001c10880301e1955400708042c06611610781c141e040720b0884408980380280c00c0c2c1c1169806030280c0d0b40c240d06070780d030980207900070183d81006801c21010310040001c002c5104000f048c00320000d20440c2040030b203580400344c21442c04c2040c995242440f00416000340d001d070140070b80000c180e984a140804030300301a41c0b801c00c855849280044006070740010340c0d12801b0121519980780001050414040c044240e0189261600f0824180300c00507046d03010740040d074401c0304a4510316444a15008203242554000c810122601141c031005004200905c40c85c2584011a461100520a1039801203801003c142c04411801c42c201820031008003010341105040728441d800c501d000b42c0c0c0e00d0740d150021 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 73127834 1250 73126584 73126589
    0x10e1002181e010c06021c0608071203170402011107030602090a080316020d02150406020c01030c0e09070f14030f070f110d121107050c040b0409030905060c010204081e010510 77
    0x2541c405104802c0340c3d4421005111200c1c49203c00601d41400c070610301111905c034039240307080540c45400c24003150009100c903500924014140341c8204130319039000b41c42080070f9009100210513580003c1d055a03c92500f0b0240301c040c4c5029115010f48038100940690b03c241d1a107070140000140c0029460400011285510040c1c035403074142d900503500304185034424510503a07000307010030400128503100b04010f00c000c02064001382210460700001600303031807100403540148040c0b00c0d00c440580d2180d0480b954080943c0c03030300201c401210b0754182c80d0111080c0d104405c2d04004020002072100304040742d030060009031201350400342c82090456504c00d900e1741100350364000c240180d00f11360094407140164010381c1030104226440281d554059001144142c074564000b40e00c1c0c000c642014896560b141074203580611414030691405000200c03030744901ca0081c02d0000b031528403540c0a50546002e0068081994a000341102c1c050030301c1035083c60566415480c1c500072407051751645c0b804508 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 73129084 1250 73127834 73127869
    0x30906040507060903021f0509060c0d02010b040b0f09041b080f0c10020d0c020105091507031101020a020a030e0a030f03080f01090b0108010306020a03060f060c05070806070c020909010e100218 85
    0x6140d9420751410b00300d007007091f01810b12105101210f915922500a0a4118442001484100801c034402402d4030750450029000f0317490510040c20039242d0001e455143d0200b41e5810780c0355203607450041c0c008001e5030007000c1c0190f07001c580426208400300303404481e01c15400440b14080d04110401822488259003000941d12014006e40101c0c001ca554503035103401410114280000840030612044100340c0008610034001100020144c0025204144040c52802103007852040d0002a594035151748000d4140b107800100c0d400151b480c100000081c5034450f041402e8001245800380c240541500c0a040c0741c04810008500c0404034424207081c203030140e6442409074a15101ca000a5128091820405031560408a00c5602ca941d420000f0000740c3d54034002222075080660410076150031404550b004030061081140d40007a080ca9115011100b05c015625200401c50052166281c105041d0040019031021112180d010344800c5003190001d8000c3d041c20300030010118088001c40c0c070f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 73130334 1250 73129084 73129099
    0x90901170a020907030204060813020907030f020903010c0905090903070b180a050619060905010509010311220b12060402030d031112240a0303052d03090604050706090302 75
    0x80034003401450405000c04106450301000d8580102d1003840040b204030020070f40000e01001f0705a80211090340c410136481e07801501c04055070006600d25005403140b810152a04032881664403d58112207032890000c0c0200482d40c0b42031400b400c130602030303c2268840c505d04d000243c426280403007141e602592100c0881d54035610101310f031030702c3d03001c1c42000e02151203105091400144100213050203540311b40c0c0c05010745c03584092810309446d0f841d040088a0f60415004000c540c440d00c1075030341900d5000300f8114804000f400419101030f194040407042c035000441c0d80241000542c45056001016a03d07000184101c1140310341d10203086d5002501540300d2a003c0000c64401da0100100002c4080f90f03a1909020002840001d442619103e0400456401000e416030341441410303603402081da41c2c9080745186031405005401610341c1e01d07008170360107071091740c2e006104051b41e40080300344880030303840742000403110f0755406013210115264801c3d0b01012440c5170040d620101207030f80c024040c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 73131584 1250 73130334 73130339
    0x317040804060309030e0301020c060603060604020a0219050102090d0b010905150105122703030a0c1106040f0c03020d06051f21050708060f04050c061e1602040203010b09011103090901 81
    0x1c40050214250940422404020222040d1f40a00042c914000040f00402d600d042400816060140240c0401d12840c410031002102c150042882d184d0f56070040c02e03080d414040307400c1c19800381c45036420301c9602024220f0500c0c100700380e480059058403184030b4100916924400d03800301d958180301001d40860020302ca50b5604a040d10700483d48660405d1210000880020f13054005810440421429400100800645146c64403601e05141c526280c00000450b80311204c1d074440c02d01900182c4100d82c1d8007940c03014001c402c801d050041d0b6000e80b400c40a4611410107030000d02d000d4407525a00040c1490842300e11405040e91019a404028000f902001d054400700200066201c119110300030300100051688050045501c40c00520211340c9107803174103291040c2001003040d1f010340305541c04e200070390062509482484070181810302065465620003c5080c0c034507064000207501500000000c02c000607518064480c007002a02c8030b0341c0d854001c5503010386034001d0400c090380103030501004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 73132834 1250 73131584 73131587
    0x30316020402180306162606150f0a0306031103070f060e0d060c0807080109050702030316021c09051008010308030a091712010e0c090108040303020c070b0d09031704080406 76
    0x10300015001c1c00f00c045400c00410003007810070500300c50b04001540c01c0c4c1d0309114100d41008440404d0340c01e98081c00700800826512440b2800c010780214000e020380e40c8005e6130a03411900300d5075110f1194501d2901c54101510044c041c0c1000e0104450118400704608540d0400240b01e0041c0c2e125403983c2072482d0f0603c0c4040398541d0040c2a80350384000d1103038000010030428818440100515030780d502040c0b81100c005014240c040e84a54940d501c2c0204000d501580032058a800c0014100c0907500d018402c54103e00d041007201d402003600000c07e100a0f40a5013090003507041305c4003a221441946116101554808401d2001411600003000058030400540d4030044203244a0580c00c01894100002c41420342c0040c5030042103c980c480050100c81074550503030394051400401c0300e16103002074000034038135080a800181030540101c0c4c0301001120502c07409000c2c00030b40b846951590b6070107142e0b00107403185500550100f61044e070700450110b6030320049440396400060340c038506850f2140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 73134084 1250 73132834 73132837
    0xc1903140315010e0301140c03060108090307050705130212090f0106060306260102040806070804061d0a0605091c02070906171510030804032402090a030212190c090b030316020402 79
    0xd0f1300398075544e0340c0c42c00030388100e064145a004210340500e00307440c0c1c03804500241c45600e0103060045158018009240040ca0000300c1200350b903c19034842e80c4007a42e03084c0c0c90b400b03405001d642c1c480c2801030808009200100056021040324280001e00490782d80d0301d410350480300759009035040d4218100000c80c0c0c1d8030380c44411007140906c6030001454241d4600085013002405d4411000044011091005010701d0b8000c203a4661099034500c511a80c4603141150b41c1c18500c50000c28407a290000102e00c040b09002c80c40c05003003401480088000940d6000792550681c0c000d0691240c80c0c4034002c41c3c0840003c100d2105992130000804c140d030f4146101e410154030082408a6400c82d0100c044001204d2401400082d440b8441554280b800c00c004080c050020059000000f84180400d012540c0d6500551084a8050782c03000c200700c20607041c0c0b0f4200410b64106990f41c0e80c0d2558880100301102c8008400c54010110030000b00400d501050f44910880301c0e04030b4404078968070b490161402c0e90 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 73135334 1250 73134084 73134107
    0x150a03020f03070e1006260402091906080102091305090a030804080904020712021b011409010c060e0f160302011205070e030d0305070905010503010302030316080c190314031501 78
    0x6007110a40c5690f40c03458000013408844843e00b2040e42c807800c00c52290450240a40940c1c11212a480314500c880c3c41000d101c4010006071140400d00b02190b003030784610208040300c0c3e0b0800002c1c444681c9410306a8080d40c4202401c0d40988480800034041403001d20440340189090742c090201d540e41914122240d00d0094010341d00d000042102c6030050f035891008080191080e040501b840d0368041010f418400d031005050288200c0038107000480e03911416001015541035042030b2204600030040300e80051003140280340e14504802c500101000245c0780c05180120030449070f21114030842c241824255200081c0442c4e0b0741c03055035045000c66001240d00c11000e20341103001d0080000000e207048040711843c0042030ba01d400344000b040e409107020000d4036003804c09518551440d0302003680c03072141c911701c0c00320707030501c2c0083c0c40400480341c01700c901c240280411921044040400c0810b402d03107412003100440c51031030803070b40b00c81d00b181c0680c2d1181c880e101d10241700d00380c150b0041d12800482e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 73136584 1250 73135334 73135339
    0x6050306120a0f12050c0c060d061d0912071101030506040e0a030c0605010504062306042301020607080f1602070815090c01031e020702060409060e0906150a03020f 72
    0x21051005034640030050361540c00e00403428015100020705000a100131400100f40400c041003181c80d8140c0310000c1c60261166003a50b070541c1d1030403042131901c000d1a50760000e00e1025200d8407a080c01205c10040540260741d40025182c1400540a043c55030b8428410010418100079400c074183e507000f03078401c90340b00c0d07405400410007025044501d42405c804034401ca0208207a0700241e03040c40901d1255602501d0207403410042c00303080600c00688400c641d65908a062442044107600b519032000b540c0c01040d041c804000b410300000503244000341c40000c040d0042c03042e030b00020b140602c9081d500f40580308920a1003519102d00559810740c040d00822001540b24515002842c3c14042008800d00c80c8a03076583d1005040503070806040542111745c00d4109410000e074000764800c21030760054144400c410040e603901c1303076201003281402540c0c00345980074540ba000040c040c4c0c5034142e281c0706d81d0040c010b889182d42c071401c0300c40b40e40650502464109400460500060816249429001d80300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 73137834 1250 73136584 73136599
    0x80c0c0102070212030a020f010e0309091803040b0406030e0604030e0607111002100b100f1101091a1f030c06030b0102030c010c0207080d0207080d1202070203101a0d02060406050306 80
    0x1c81e008210b000c01c04c2c007074a6501c0d6100007200b540c101e606224040c100710300200240519040308605594900804951520500756032010a00490042c11050302623110b507802e4903141c55840f91054599046803003002c01103402d26442550058021544901c12645500c604410b20444c00921070782c0e402480041316048034401c1d03041c030705954082d00c03010b644400740d0051a68000c0c2d0510b84080d11414030050740505000c0e401100030540100e207610501c000c40c50222159404254298098100c2c3c180103040e8164104140030300c10031403040c02d8443c2c41c014440c044261820207095120311800d10015103580c514000170f00402c0d110b5041800004414410bc9040a00d8040e5881c01c492490401c5401b590100200700003014051020068a900300d00181c4145803a00b40b00c1519405008141d10410061540c002031050440e8140c90020380c02504803250340305100d030410024503c1c880c545d480c0c06943c65215140b80b0384021566a0164090b0072079007480d280000035602d603013002c1c003456403003600d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 73139084 1250 73137834 73137847
    0x70204050a0f0c050405030a06020a02120c0610060c030905010e0117012903040807020f01050408060a1d07080c2119030810030302150703020f0c03071101020c01080c0c0102 76
    0x5690189500031800032000007000b29042c81110211103002d401c1e002400001d00c8208080d680202d15028190b4000d0780142c0d941983e03980480c01c10101258080120602140e0491922000601103216041070540c0d5104991185015191a220814020009403a80106200a511030b0210150b806818180ba011010488400c010f030008245c10200c2c12140c4c056041040202001d8a48a850b4005a00500d10705150f221015079200c0c030380020380107040c1c403184000140d1040c011940240391840030381d484c07810b1820b5154081c00300440c1c031091079541441d4100c0d81e11004905001100d22520041c020440140144540b20080c000d02e18032181c00c500c0305240d20740d41449034150071148500003507010b051900c0c02400d1940e01a0190040f061200c409000098001840812943d4140c0143e642541c9440c0f00724042e100d10032489016000208411101103030010203851850b00c10440c6060160014004a90310312050103420b0000b04a00081120360078903900608614032950005407a202 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 73140334 1250 73139084 73139089
    0xa060209010e2b14031b12090603130c03080a080f06090105031506030106080115151b0b0406091b03031421090703060c050301091803080c130f03030903150b010f0c0204020702 77
    0x1004085180b844400d019031611b070068052140c09415007112020324200340864002c078a25010003403559111a440e0741c1d40728240400c080d078200c000c61344914859502c4102d4007004000a00540702500001c8202c004140103180003121a41a1b400190040650600044201005e8032018084603015560f85402140803542030090350a281107101038031a10034074240b441001c07020300002d15400c010280b1103802403101c203082c00d25000d50f08405114910b88907814a580148000320000b03102100c0181450006070070340440b4000c59005e03271070b00c0b1035090400054580d80e1040c1000380c040e0403020031031000b480c440c0c02c10440d0400803440807101d20315265502d41381180c0c00000a8800f081c00031004001503002da0280103202c410314161074400c851995400f03003052034040c0c0071003040070020600c1c000e0401181070787d100070b0410206500250380d07030b4203000d016154a07010a0f0b41c08280e00306250b544984034052100c1400060303691200783c681200342281c040b5105207049910640030070850001d603 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 73141584 1250 73140334 73140337
    0x61c060503150405070602010e15070e040504050d0207050301140f0403050409150e0a020c0a031b0b180c0a0e150d12030e0d1103070f0c080a060209010e2b1403 70
    0x104998156900b03905042c10325911340880d45c0d104c2401c40e810807040740390007600883d400082d0140c561601e841c686582100fa5011201c1c000d1301174029103000300300400c1c0500011201c941c10308a40a45076050744490625080c0c40000e140a40b0000142d00421620035590b01104c1e4400d0080c076000742040c3e20b81b00702d407043d43d4070300c0b011500d6240100d40a0226501d0900916000200803a04616041d0751031143c40d00c610104101a00f07110541d10500300c84031225030071403500c9a10500009041c64038800d096154100071380141154032440c52000c846040958007801900c48503804485c007540d0342d0070851003000c2c0a2400301d8101d45c41d081c8031030004649100174030031080b458a0114803100601c03cbd5a16144001103c01c0800c90040c40305862183c0c0030017112140c5030440c0d94001e00303101034103006440c0402c030b51103100c180c0b20f00700c1d00c4004d00c585540901440d110998980c80345010300010040c01e44103900001c8d1518004c2d4551030080405264035030000ea100d84c0c40c3d4038246000d143d44c907045 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 73142834 1250 73141584 73141603
    0xd020a170a031409090a0e1006030501020c06010b07020918150702010b030f060c04060c1106040303020304140609011d030c04060f05090109051015020c0607080702120a02061c060503 80
    0x2903500240c0071030105030700318045070b550650410101d400c00501c01c00144980c40c015101c4030540765189141d02d03103200140004081800c00074010700c13a079a540c3c68a54001e60007041c0c00611409640d0001c10510291002c44240503002044080d4588a101c1031818100c03400350031054030311030701240a03150341c090305100b48504426000007401003001000d250804480c1c0e1903842450b00000100405a5607807001d0701c081c0d41300b920b41040e20310303da45060442e1415103012650300140100d80002015400401041500c00d451f265440c00c1400308140500d40c080c1031542d90100d80c12580c61400004404055400944020300301d5002c0314403000810111046a084801d07000c050f46c90a200b241402d1400c81d0041c81c44800030400d82c80e10300b05000c44540e4500440c41040300401650069500c00c112000503c00d00503c040d41c0c581035490000c0c907580c00420202e02a03c1015410959504089030300410300740c001e811a8608032840c8500c03524181e840b1a540d0001d5500c1d103010070319480411001c000f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 73144084 1250 73142834 73142879
    0x60306110a0807020d1b020607080414120109050d030504080d14070f0207080d05030403020717010501060e06030402010905010509030115080303070206131505150d0f0b01060c110d020a 81
    0x55480709040010560400104200d055500070303285840c64503840481d941c500c0a1418550303403121117a10004460348950880602515130110700400c545052810210003d0000c85072404070340100d15943d42038580481c0c0182c126006203803005c11a50003908000c1d8054840d02403540340c0344200610200300c45500766001001c1003110100841070307401c103261403001c40d50741c002400744520b040c01032503503054900c141800300480030000c5070405000300322040140040b0715095402800601c8050700a040074450710001501000c2c62100d5810100101d900407501a13482003009401c01005545c20340c01402c11507015943c800144d060301903480c40c40e5015101e0b41c0040d641d41e0030b00d180300919009000d004a411166000f2181c1c002946043d110214440d418101103120390310001c081040b01c1c0341a2440750420002840d59042050610240001c02d1042d0100324059880300360458460b051070400074a0440b80580105103480c0819410b00124401400c0c20b1602da21507800c1c84400340941031b07484 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 73145334 1250 73144084 73144087
    0x602070b090c060f03150d0c0e10060f02150903091002060402090c0c0d03150e090a06060608011401120f020a0c06110a050d0c021e030408060f060303040e070306030611 74
    0x40d01c0e0303109104800c540003040361220304120305200314102510024010b14a22811051000082c6c0c6400001901071900120400c0c1129640d0b510301290100454035444046404100440c3d52805403040d04540308055001b0501c0c5508101e11448100024061a00500c400d0001d02c03440c1d0b440c194140c08024055000e8440350070315105101900070007130a2850021340500000c403441800003407040744610103150109101c10041e03034030140c000d0160400e1900e843d4a1040206c40c10000480c007031160300c1040104142641c40004990301c00081c05000340101c00a54003503000d40c8601001c0c115070141c0714002450780d0100002d0b00c12644010000c802180c00400101305202e500e00c18544080d020500b914070b031040e00e2a0003020b62040c400101c03462980c4404000340c01c3d200700290706840030030180842c3c0181666143c07641c0da400500c00c07415070780300f80c3c400942600d1b44912283d00903c0c015000f10704050503e00c0a00b90040010700b0207081594841d000808180c05e4000c1c102e41251104446 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 73146584 1250 73145334 73145341
    0x20a081b040e01020a050f13031e140c01080712020409020d1d010903090302120114070305191104030b070513030809090105010804240e0303090319020d050a1b0602070b 74
    0xc81a0b890104034550907034418418050000e03041400c0702c54481050030095619601034410142c02101c0e904041d2511405503c802c04d12100405818a070320700541d50803400b841c013070030b260359205035040f4560f00091041d40445d000d01d0207688a0500b02c0e4005202508198a40b00f070740c0102d0300720a110004260b1500180c580c841c070680314948030711600c04002c2c00f00249a4134064030134007003444021b005106801c40720002640c00c1d8484069a8176900d480703d41410a024010064402070b1398801c0001038400005001c0d050a22410301d15400103405141028950384a51181e400010184010f0290070000b841d50b951464280130040c0d44240c81042e00c0b00350a1041c80000c0405800060500c00403009000c00301c5d1a02d0a10b03180d264038000070b1850192180b602c0b0010f003110344061b8965200c00f2051200c03c3c0c4010010701044408441c0c1c0c50249419001c3c100d03642d81c41e942c58000801e00400030300c500240300700c0300302e5030920368101510882c071002d070741d41401c9a20400d402d80f504000181030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 73147834 1250 73146584 73146589
    0x501090b07170412081003020405040f02010801051207030f02010c0209010602070806180c0d11060f070203010b0d0f06020904140a0e01060602160501050304061409070f090213060c020a081b 83
    0x690081402c0203002e41500e00e404e40c0d41c060764681010f0840c00b44080300000400940d000401100a540c2c050020b0006060a00e044010601d107602c0807404034070306200203d0f0b42c0c142102682e5002414070000c120041c6541c40d840310b1100880000e03810051065034400c05625026981c038002d00841c0d000340302041c0341c2074a5a0030240c0150400304034903004140340d0f0801c0c100180c540c103084012511075426007c20b00e000c41d03696061245c00c80d0400c9001c6003600f4089805009040c0381d9000390003c0c080031031104100314080f072000800800600340030401d900450043c2c1d000d891042c2001d4400564001c2165401340603290407120701256a03144c40c500c04d4124001c0c003d400007403401e4001000742008400004408000c507010b081d0420401000190a00000360401c0008091281030440d103810030000d041d4880c03800e40a00e1002c44815400081c2d0340d40948202d0342c1070b4040246240501c1e050410446400b603030041c081c0da0181d4240000303c0d120000740001001c3d240324094540d002d12440d0107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 73149084 1250 73147834 73147847
    0x60803071406090d0905060a02010e01050106022b0921020a030f060b100e011103090904030207050a06090e04060b0126010f120b16020715050a0806060313060f090501090b07 76
    0xd440d6213504002903543c5100d400c508540180e4604884454507200f5485040380149200b8910605940c04c04000003070181d00032032200022210302c00300c060340300420880782c11068414410f00c0001000d000d001c1004291a608048000004c00d07891140808650005501c0d4038541c0c0054501c444032102c410308100b03803481207400980c1d007541d01180c001d0048402501288483c03003168140490000e0a172a170708400e1040300c0260100900215541c202814029610300541c0551380c0120008040465498080d80300f0008603881200c5598240e0360340e640b00000703045a000b52605114840c1f20088002c1e803090940b0302c401a00701d41405040d071505982c00151007541e0b10a00140c0040203440c00801c1d06801c0840d4024491080c80900020800080b440c0c080e8903403000c80700400000350242c1851b0310100a154000340b542d10303000c10b82c56000801107944400c0c0c0352448c4400f401c1c1c80300c1c0c0001c0c186811243c80c0003070140c0001740c0c907203150312040e00351480c400b02290b030350440740f04021144c0c0d04140c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 73150334 1250 73149084 73149091
    0x302030414040504021305060301090516082407030902012a1b05060306120c0607060204090b0105040510030b0406090609020301050306150319020f0a09020309060106050f04030213060803071406 85
    0x96061040782000d80100f00d0200d8886c80c554405526075000071503c1d18250000d15401d54040126901c0c1022450345540c40e0384203025100842c000c03000044084041440b03245400e001060f034aa642d41c4403000250010003001c00224180504401c0700c02950348001d209001a1102c128034414042152410f030420340b0079400e03020344640c5191800d0000f5119101940d500001c1550104084c07030f600e4050781c0c03400c170002881c00d500402c00110304040110301e401400846001f008184038100480006480900407402000c1d0031040c14407d0702c840900c42e800079406400c010740001a130b142c8610b110000d41c0e00c02e403c0018560b800000400c110304003040320301d91141010082c1c90841ca01c000010313441c5c0030194415903a003500c00c0e22079010365a500d1400f15507008000d05428200d659001c1c00d5011f5001114050050301594000240403030203001118080305100c7e41043c0340070304590030400003048800304003001603030302c82c4049144c0004200511140c3d0144000001d449619a079041c640381006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 73151584 1250 73150334 73150339
    0x30914161e0806130c3c05030f01060e090c150315100c02031902030d050c0705040f060e01060c0809041d1c020c03031e0f07050304030302030414 64
    0x1a03040058003500340808005075020701a4510010007960040366101460340c0206106009071030501c4840381c1020514185144555040c60749540d84009a0300540c4814500c03044105010f00e04c00242a51081002d412aa10b44c000c90302050f00e03100880c4c0f43c0824035240407034980d0340d0f4805200310740e03135041040c0c0e100031480e004012020414001c1a032022a50a6521520b1004008240c200d0084400d542c1709117000b82c800c10032803425400c011f04010712854168040d00a1400e950451181d988594800c00d4001e401040c11142c00c5400315600d40c407100d0b0304c4115020310b2201080968a07806501c02c84555400049042418000030081c1048180e02c100d060001400080d400242034106079010f0b00e600f19000101441000700e041c4500d050100d4000341405124990b00f0002b14920041181280c680d088484080c102803d00d80d4a206211000e8905c4080c04918000710349050014442071607202101c0d420501c036503503818034681164004078003507000403c007444003e078241d0000724811001c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 73152834 1250 73151584 73151593
    0x611100b030307111305040606091d120d1104090911030601140405270703110402070305160c030c031104151220030708011a01080907060509041407030914 68
    0x5000040e981c2e1240143c0240a0803c00d001c051596888050b0800c01d1244044c0902c12440c262501400500300b80c042c0e10b4525250840001804180c0c128100b408022440103080c03441802601c0c100c517810512114580b9a2a80c04002d0075140c0000640020404034402244c1003805261042c3c0d1820f0400880d40664400b8004000b001070007500d5002c0010240c41c0020141c071400304000540310006c02108400310ba1003081849460700103200d0702240d020341d4000728666609000c1200340d12400c90003400041c82409000c502d103002c032421010b460b00c910707100b2005070790303907912046901003139881900d040d01450581c0405043c2030007081e6a110b1403a283c022258241002c400340c0926a6070043c04a151400721000c24418212104400c581e0040458101c0c503511070005001c0c001e40d0300000101d86041055107855409440707030500440584001e80242418401d080b26940c11a641c0035a1081d12881640f411104107040c0a01800702958045058102810000d0030060000d00e01d140d964130 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 73154084 1250 73152834 73152851
    0xb0f1801080402010c0311010f020703120e0303010f03061121010306050708040804060e1306080a03020118050a03050f0f03010e041e0503030615040305030a0201050612070302010507230106061110 86
    0x5d101c40c4850751141e040c10000d81100c1448100e500400b0b030742031083c034441c1c0b0009040c4141504101e0f010100c01320214141f05080780b10003c280c50340401c0c07241017201040c001c810b000113a00d581007617002c850540170190608420079001e8541e00c00c43c0c2e049505401f0403100500600c000d41c042d41d1362100362401c04000906095644035184e01c07803845800300300005402a030182e0795807282c0c1603842d40c41000d0103000700c545600304181c990310b5800048000d5841c256039601107804c1c24400c0381205400801411362032519407010341e103e07400000e40c0c9040200c10005000401014806107020f0060120f045440d0300d420700c0c00c0c00da0b01d0303c0b209076111085190011200001c2d40081101e901000544402d64140c0c0e251708040483d000e2600020100d01020031200c140f5030703056020f94030552045800505401400440507290702840c000a40090400c200d008041250345c604160002d250b074020340c00c00001041e10a00b10b880d182c00980000e15a40c0707504410000800429013200c040007800c111404 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 73155334 1250 73154084 73154087
    0x504200d060902041506120e0a08040e1017010504020405010e060a0302040e030724060f06021504020a0e09150618010312030204031a0601091401020a03080405070b0f180108040201 79
    0x4442030001416507880d04201030444d1a25008003101c181061141050652034a8014000d0000b4900c042403152501040300000d13603000808200003504100d40c035103460300f00351442c03d08a034000c1c040c6c19075488000001600004e140003c8040031414400082c00f42010b104120942d0710607070048407501440807c0c000556650b404100480b54100c50005640c01c400000900354040e92001804075041620175810842290a20010b06030b0102420044507445846030701050030725020f01c400503070251304182c510a000000c043d030000e0004098500059560180044040080f1102030942d08550181c0c03041280498500360030200850340c01c03601408044018484a03414400a0302e2101540d540c01c60a40c000d6040700c0185400100d01042500d48454080441c1420b440b032030300140b49080c0005044100000c048040e800503405030144480343c0e2400c82d2414805042a2854042c00b503000074214107650041071100800000161204903000121000490300b81050703050000700020080182e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 73156584 1250 73155334 73155349
    0x30206030a0504030207180207050d0f05040608060a092301061d010e04150e180703080301090f0b131514030d050309010e3c19050f060109050420 64
    0x280340c07448000342c0c903a07490500703e00c0d0842c1c51780000c0415010703000590780308907190000c01045003c0c1d0200c401c1c2066a6004560001000c6014000031f041032105200082c807a030038803a0800e900a03c12081503444140441c102c2d030345046101d20401e02c06c85562100e2000c01d1449004003000e0030445110160340307a000b85462a0100700074100030648120110b80c0d6038561180d45030000800e02e01050549030301201404210955112111811b005500b1041090006840301a282d10014042c11a481c2120701000b9020074420610502d40384d5007030300350740e8651040d8640140c0c40250049071a41d1561400c10714040c5a821003440000803c20303d000343d0710005008090301025241a0b130f5240e440d142c24500420306000045032070b01a10b10015090f042070188002e01c104402042c01229085a100c5404500200c8800d42c0b25023120216201002806801004d064000d0090b44c60310300c0e07000e401d2030410200340c1011103600c1c1c2d51814042808026541d00d007440100c074144d401c1e103840381000140503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 73157834 1250 73156584 73156591
    0x170606150706060b04080607080906150f0609040e28020d020f01090b040602030301050f0103140105060c0f06010e04110105041202190506030406050a15060c02060c190501020c06060a03020603 84
    0x3200103498402c1050036031000d00200780001c0b602c0d0f1075607180c1d0141c0d922408161103a000051344400803c040042c003059140c0200404c1d07141c94420840801444841185010801c1d4800c0e802d01c003003110382e00c41c0d0186800c0035511902401c84200443c2140d102d12828005203c0e510107201740d44001030301d60a8084408030307012034021200046c00001210380340c4440e0003080c0c2011011400151a03074000010b07605851080740c51450014902004600700c400c401c1011081c3c080000c0100b08505215005104460161041e101240ea181d901b141c58410b0a82c0701480060700d110811080c040c4141200a1000092800a28147c13800c40215001c20050601a2040008000b070b00484111424104002e14015011544904d000d05012004220031903100b5507050801c43c8522040704803041c4103040c1c4001c0d884240d20a44150203203c5990402400a501c600ca46810700044c207000d40d0780e141c0880c1c0320b5070016944003d0f403840c0720304020020700070390f0050000c81c0e003e00050341c604c0113480d030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 73159084 1250 73157834 73157869
    0xf030406020d0e070f030b0c1617090301021314060f0301090c032007020103110906040b0d0b030a0507031202120708090d0b0a0905191a040302010e1204170606 70
    0x2107450381d500d030600042000c0c5024000b1481000c83c0000e403900200c1e481406c07607018400758030341c0740c1c0c8481c0e0030103440c071411072600c800120f00d10148000030226101c100110404280c403500b040c0c4d00b1300c0424226801000c2d5424808192030040018a00d047c410500182080c0c81950400c074908003004110300040c0180010b40c1d49801c212400769110760322000c0c3e111210f000400c41d00040350700091240c1d1280c001640041c0c244003c020b07049903d001107402c01107014161914061900d00b8907a0aa08041d030240109a2240c1c00b03000299001c02410b1a0580114050705000f450340c0341074810200c0c0d40903071b0380035900524001245042ca0a051f20b242d45d410140c5070390340701052400204a810100c00041c118800c080a1040746070496111076003e6100300d0441c5c1c0f068441c03803010400b2100b80000100801b10744503c1c65400f0130300d206c00343d4000f4802d00010466204030b400e0b45050032040103517960300020214081020715500300340da01c44240740300050a02030907d0700100d002c280588070104c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 73160334 1250 73159084 73159087
    0x50f010503070f020f01051608070309120c0c170705131a090604091a07090e0f010506160c1d06010e030601030b070e090901020403020301060b0a08060d0305040902070b060306010b0f03040602 84
    0xf0080e009000040068402a000704024501100d030803003120080c0c42140001001e40d40021442030080c400c4181040c0c02450b42c0b0440943c1d1801200c082c0c010301802c9900c510a0752000600400392140000f50f480f100002d450881c0c102020300161a00805c4020f80060600c01c030340e6003045403c440c401051006560740c170115074504010402402e5480001815032b51842008441c1d441c1c1746100354003448180d5900410709a48285c1c200d1140c000f80c509a0500540030010405403130000001c00311011450180580316400751a401004c61955000c0302e60400c4ca0349a0201c161603045090380d001009003864445e030402c01000c40e54411050100500c0c0c04041404104c5040c05204a0544d626008000000344d107400d01890b8081e4005100480c040c0d800c0403400f03d44411548182c1d8545c0c0001d40e50303544282c0c0c40700100104005000c0041c0c051107400c00c400705560301240000d129045c002d03680d005e0f59090200a0511b440c0c01680301114603075080c08000c8013500200102c036003140c0c0256015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 73161584 1250 73160334 73160357
    0x102011107080409051b031303081006050f030405010b090c04050f1008040210020c040c0e0301051012170d0207111503070c020409111207060206060a0609050d0c0b160507050f01050307 81
    0x10b246d482080c40c10018204000c020030152401060100e460340c0d120b03641c1e980c541e845804690081911364003035400412821700107600e264900c00080e55100d40070310008100403c0707640200381d9100d1b0036642248040c600280074881c0b410301e00340d198452041990226560b240d011001040f1120261009110310b106554114030188200300801072050010810041040144c1016000715030312444d8074003c1d401c100c0010700c030240c003d9640c1c0840e8450000383e0450400ca41e00e0700c180784150b10084200d140d045c8055282881c19102070701c1d40790f1241303108424040070b50040040040c031841488400300000c208018036981c0c401c03003808941380e0640b0041900713106884d040f401c030100c809100750003404081414003810000240c0c0800c4844a030259030054039900244040d0410a00034000440c0e0786000400c5a814400040c88520340211450340c035803511070500321100da010300000341440212111030f0051020034801e10004007001c403a281c0c0d88200c0c000018149010051030802445141641c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 73162834 1250 73161584 73161601
    0x3050a120608030408031b010e0d051308120a0e030703081e090405070c03170121060f051906060e0906040903140c100515010c0b0c0c0a11010201110708040905 70
    0x104000d00002e07401d8030b4a0b50f4541c11855502d4101c01407000100c030100110f00c0c0e00500610411070344144100152000191041c42550b085d4000000f191940511641c0081e900506200b02920b5a44000d04250b5610700540c0080c502c031a008040c5220303401055042000034011011580d010892609948000003046215a40c6010300c1241a40144c10002000302e0702e907104005060642c841d80b80d6070400440c4c424407a0070000240078401440340c101001c9220003c40c01000003060b4403512000c20080307414032090007a030314180c03040d000703a0040c0c0f00079203210f0910740100c80141441d403410040075180ca000203401e5101c00341205002d5591a244201414482c07000c0f244440c112070300499541083d518595a60940107001e01d4613240b50a0114019140e810306e8100031400594684d02100c800740c03a041c204003809004c108403210100000c50072001c051022841450203140503020701c001440000e13080d1043c40342c511581e00000c20141c800564020281d6058405280d40045d0b280e854144 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 73164084 1250 73162834 73162841
    0xf0f0806030a0f05070314030a090504180f0b06010f1701150c081309060501170403030c02070519180905070b0d06090501030f05070b0a17060d0b0403050a0f020a03050a12 75
    0x4010741000c921600c0d40f400d00c00001401030803640701e440d0704035002a0710001240c6901070001c20100148039a00304101303515145d0001c03000144055480b0866481e683d8402d189000a0710045800d0800402000600d607009220141212440e00340f01211441504200e04002014003c0000c5061038441e4100d100d0710400c12600c030700b03a0100740e03150f61701d1002e21201c002d81d03014450460300e6824080702042551094407102e00d1185d044021600c50b440b6540e050f0302401108000200318032403a00001707640d59405034001c0c2d1004039540354050081c1043c0451305034070000c4072072844d45410304007000c0008500144c3ca030101d0b450704c0c0340f01c0d4944a05080c118003a107a1540f101588900780400407051080c02e80524800520078011100c070265540c150409d140101c6803860040385446c2c028401d0714180030901036000c00001d01051014071213a950400c80078007500c6c01c1d0002072002c28a8086950030881407200a20300b40005c0c40200c0320355500600c3d6104640d4064108900840d446550606582 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 73165334 1250 73164084 73164103
    0x1b0c0308040602160b0a0503060d020f060a0315051905120c040603110f0a14060d11070602040806090303060a1401050903012909010810050717040c0608070f0f080603 73
    0x200d50941e100e641d52030083d80c84070f500002c24541d000802001855220403001c552a03c102500c13600c1c2541e41d100100b01d01e660030401c0590300300b40a200486010307138462005013545280381e00c1c00200001041461982d070f084a40000340621800800072510803150303140030b0100c40080b03a9840c24032500130000760030700a1500d159034119082c40b80104c00c01c2042c20600055400a80d2092210080348081218148492040119000e10300d00f9101050600e90f004140320400910f01040c0040b03141c1c80c440e0a544024000d40e01135a0104091100005c18040310740c214000200a45c00c0d0708080f13001540b40c0c00030744074400c0000c507101d030107280990140082e100c405d10000e000b000007020300c1c2040707102044556a08603503110713010030b00d901070720f080c181c00d5050700d80ca58024803903405801615401820068580300a01507011903090b51802001d0003544a18450002030000c149802005491820081c01680501088154150186a0141c01003502c4000391400c00c1070b5444540200e2300b09013820 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 73166584 1250 73165334 73165343
    0x3071106040b040204230118060803040b040e0112120e04060e09100b04090c0530010c08010911030403081005150c0607090803030f0403140318010b030d1b0c03 70
    0x1420070003888001c0c8040c0b8410b0340244d43c1400403007079615840304003141d00916030645c0b100310030040c0070314200381403940703200d480854000410b03940311100285550400d5210302e94041000809010040c01c0c0c5100500500d0035030713500e6512800ba1390341c8140e25904842c01c503013001640d108a603401d5a4a41000c40144401c150f1403155051a0050340c1d2102e20a80305281c980f42030404c4d0390503d0403e441029a45038001c101800e15506200400904000d14081160800e03202d400e88000540350200780310b030f0350004070000221881c03040e00182610005902903925240f621420041c80d141c08022254015814070b0407c140d0360355582e90298041d0725400054102c007030710001041a01c13401d03004050340c601e124102c4800d507544400c21036a01c09503028415480c0c01c14808034010f84c621a0382150000e209082800850b5646405107071540c2040321030108a103038407d07407460064001c0c402c22801ca1020340c003804090b0400712014103031100564500e001d0910041400381401f501c0f40c1d0480145078030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 73167834 1250 73166584 73166593
    0x6021005040f0204321302060d0605040510090606090612051806070507050613030f1d060f1207031401050d02010c080a030c0206090601140607051509161a040902030711 74
    0x2a880b0007640c2c005903050b0108000b4041117054040814041468443c03501d50300350320406252170f828445a0740202d0f0022107030b9900c85001051071b95071401a00c0c0300d01242c8040608140c5010600d0341a00c5a41d03001a00384201500240300566028218440c05809170001040d0b984400b0070034994011002c10301d034070750300440003403240169103c0014100b0314001d4085038a2034440b40c11a001c2d41c0b840450080219401c1e1003035810042c000c045400d21a48001070400980b04400007184180e40010200101c0d0720b00040c00c20b8200748451035044c0c001c5003914080090001d2801c41d02c0c0c543c5010701807548540d220030720000071603101e1030b00314450035441001541c4494036001c0c0034000d824030100c030b580507000700c4001907008080050341030304a602e00071030020030644281c04d0042a5100c9070080e201d41c0a80b8104c110305511440344207000c0c58a890050506000d5210005144031082c2c02041540d47c0503402c41d40c2e02072081041e1005d45400752001a0b5a442d100400d5951094105e03a41c1c41c039004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 73169084 1250 73167834 73167851
    0x23010f0f121103010f020c28060b0307030c030b01090f0b030a0b060604090f0207060c26180f07060e0307121104090506090d12050103200a080f03091906021005040f0204 74
    0xc1c3e00030300380c7c6488400846607600b5000080982c1d030384115a6a42540300c21000348070119440c2e40101060140180c103481556803a074a88400300d0521350829074040f10840c0040200002c0b034440c02c00b010050010800c02c500c0c00c2d1002035110591000003516114214000c1509980d403070003124000c001116040020030050f01d84070300070350030224040d00d00500e010390b070020b1140104a9292803110f41ea8044200c1090105480003070310300a03100c0c10408000d1114030031150010400181043c9118008017501031034520010f00000f0110710690080c0c10002c420040c11650041c1281d6641d40311081042c41008071000c20010040044003512910406052000d641e00210303000450030310f1580c40c042c1a011160013101070701da081c03000030310b41c154030108020900d07400d00100001c0d1500510b41042079503100c03091460519541000226a08002101046841e10507401140c110340040700d032150614105003e034403100c3c440e100003030301074070b9030001400c021f101210294070300e50040c004c100024 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 73170334 1250 73169084 73169111
    0xe0d02010e0706140403080d0b1e040b0a08150a02090a0e0114061206010302030901141608011217070809030d0807030e01090b13030201020403020423010f0f12110301 73
    0x320321001410207001d800320110b080c0e0b10031030301342c144101042001c0c0d2801c1e2a50b45d9114a0f80d100320601e00c200350303880d039400b442035955075200c007050540f031141c01c0c1c4110341460400080f22000340a9603c1180b41810402103c14003250030444035850001e9114250345501d201c1010780315a500480d44507601c9107000c120100d0f03104480c1d040c0e90800261081c0548000c0c1030221074424001c1154a03021110300094603507100ba0025a1700014100001c0b070103001c054000c0f00c400030103403510b100380c0c60706c030441c0100c0c0741d8071042050040c0a0440800c09540050300d42c09100280042805184200001d5500074459560200c50030084043c00b102d1480c6003840c0d0051000f1070036a00c07000080d0500800c0f0921040502a031030180790041035003d016242c4900440391200e6401044040d950280300001c0940ea551007a520302e16641502c41d01c50729503030b003080480030038140c1181968541646041c805030320840a80c000781c44821085100d240340c0c90815080c1c802405444903030540c213210005d0a0351 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 73171584 1250 73170334 73170341
    0x20f0a0c0305070603020f04031403120f0919020607022404060f08010902070203100513290702240c0f1303060c03020a05030c0304020a030212031c05061f02010e0d0201 74
    0xc1c0e01440a0703900f01921403a040b0241d1181e0ba102030000c000c107100901c0858040380220906005a0044900d00106004040c02490041344c5200785110a801007044100e8280210303500c20740c0b12070441d60150b00a41c00078880d4012104040e00403144824541e44003d0810850301050a0080940d40c9031541c4501c000c00b00d80c41c07050a44000707401c120000a02e61203e00a030b40c4901d034018050400c00134041e600e100241001018080d031811440c14003000309100d03070310000c0f45001001020004100b29401a800070074050700010455101d00340c0d01c40405a24010141200c2000b0500702c0c2c0d03a125140c00c15403901451040ca01608000201c0c50070548a4410300d0040302c0c071405040c4404800d201095089008600032070b404514100001040e10309414001d5601c41d100070b261002c241c0e01c03078000c5400c0000841405446500001d6001484001e00500781a00311100c003080c040f501c1d080f008240034021603145c07201520301d424900b4028a000390007900403024072401315101e82641c080f00034041d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 73172834 1250 73171584 73171589
    0x2070c261c0e0a0509040b0604022208011104080304090203040501021209010c0905090709121a040803100e04080a0e010917070504060b03010f152303060f040b130c020f0a0c 76
    0xc5102202d682d80b040c00c11039540021103200800441c825600c42c2c96074481610b0040c8040e512617400c001d00302c1d80c03104400c1200c04400851a25200c060300b0001414212400e00020417000300051008020301c00e0300200312004d03101c101402580701c0d161403034000e02a00a03030b4680b80c1e04050040c00c0207850b030015400999280f2035a624203124594038800e0201145003550044005441d110050004607021a032003142c01c2c0c840c0700c544091201500c00201d80c102c06940c1141d181800006102c40440003040e001c3c00b03003890503c2c100260a142e520f2040600c24505880240640c0d000e00942d5a802026840020000e05005016001190b83d030b841d103918040c06440d12980c0f40460200d80c030100c6005a030705840504451521090401c56910707004480d2840e820b040041200c13040700d554070491490b85003461003a1140d03407207040c2a010015204141d01c02e6a00036450b11414440907529001e0b60158072a80b4500021860512034040f402c040e41c42040024510440e1400707000c1201c2a8102d408 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 73174084 1250 73172834 73172837
    0x504060b0907080c04052b0602120108010e03040302040c0e09010b0324090f1003080c0a0c170c1e0405090c041811010f030b090702070f0902070c261c 66
    0x115540c145064410f2141529942e005140a110901c4035040011103685403920703140401d01200c4c0011030086018082c89012181d454011030300c0000b038140210190f0140c0100700092100501110b0040c0d9280124030002e03204545441c0b06003001805018000c0d01c0c0d1901409000d629a11690050480d50090360030b0744080c10801610804ea2032142c40702c002c0c548008011003460345501d0341e40c50801e00050618403001d41001ea00100155100004120a10155014142e4042030b4108145464090b81c492028040b03082030140c015800480c00c070000b500100c480144210000110ba040b1580f803915590304545007a090004c0c400b0700151420f01004120f170709204840240306918007221a25170b0041c00302d800704ca00350110398002c00c200b5040a840b80340004240c2182030004810040079101d08015130098030b0280301e20101c101c0307080701070440040c0540c41d10040d91f440c540305408512030807511841ca82c89401420341034500e404146402c00f000c4811601000e00b4644100091760380420 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 73175334 1250 73174084 73174099
    0x108010b0414040902010311120405060a0c050a14190206061201090807030302070204090b01150809070f05040e15040803090d02060105060a0513081009170c031e04090504060b 77
    0x3859003030000c11601654880c0503a11040564041840042c2002e1007080741410340702e0b404107800748080000740c00c2c101a000c0071802281840e0810500308075000d480058198100141020081e400c841101e01019a5142200800200f042140f406001d84040440c0c410180701d2911450b07503000032801e0143c2c1e4220340f182c000d1010b24054508841c203600000707110700d8080c031507030000ca8069030240050a00107000422080d02664690642a800340c0211903540641c10128813055401803840b0f50164003880200101414a030000711031007910300c90f070b621460300e41414024035482407209480101003500401005c2c2054a0b2080301500300715110b141714803a1394100c0c00b0207480066050304984020701014582120860200c40d540e128500c105181c0c54640c8000030929010441001054908500014034002502d058201c400b000b01e400400750100340410742e60300d80003100711882d252440d94600c1c8036003510b14803a503480c0034581c040020702c0d140800300001d00406400400c0d410740304840c2c42 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 73176584 1250 73175334 73175339
    0x30a0f150501020d0c1406040f03020c0102011a060c011d0d120b0a0306090515040308090f0a0206030a021309021306030e011a040f020409020f040306060e0106120b12010c020c010801 80
    0x11518030400d00c18240168801d12880341403a015624140c07817107004000d001c0075211900501450440241c80031148000c443c0c420905241c0d0500007450040e600b407000b4451882c0c03031202c0903400001c810980c1c1c0b14800001324544440400d601c40314024440b0300c240200c08618103440c54803213421554a40100d00410b90304802800c0c94825100792000003090003180c039045850f840010030000104a41d0b0f84250030000c0a070b90130b800c584500c181d1280d0341e0f0342c0c4a4901202c00c641042042120350340158040c50120005946040a0301c1d40814102030040e1150b0715003a01801c004055489861820700c00139441090342c00107821601660440d40f4288002c01921005c0c44c00c885030090190040c0c408a00302c00c2031403509800c003c001d0012100b01500301b035199000300d0126808400010440140054204104159401030800400343d01c07264092940c07410320003130300c520142038a5100480c2e0b503010400d000d0ba92a0300140d8480c81c020020040c144482101a40c0c3d121645c840d203000c80c10f0380000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 73177834 1250 73176584 73176611
    0x4020906090108031e0702030303040b010f08030408030f07020117070f1e0c06090215041403010c0f0215040c030c180f020307020a02060d0603241b0903020123030a0f 73
    0x1014100ea950b480114a800290f2444010004404485c142800010864040541c0d000c2014500480c082c2d0b011801c15490100e40a1301407010f507004003800d42090104002008020042d00c00c00f050b0b06803001c0c2d8030080307840101c45803801c41c0040c00749510010b007806806a4403502502030000262035031502d0462055101000311401c20407440001c0401a016001a100f500421030807440640360000401c05000c3c042d465805c590005040d000b2040d03159807007840d0900502e0711032111401c25071004101400d000b0740329441c1c01e801e2030181009101040c10010a0460f180c001c54001140d50715140c2c449182c02c40300c4200c00780c80132007141001c8160762580c0652003140e01401c4150010610041c0d0307075082c0310042d0880080d18050300d54629001000c10b05180070117070038003c1021a40025003640d41c55200b166084002c0003090002e010b60060501e40224902060f25024200b4a18690b854000000c2c00180da800a0313080c50b4000c0180414118144c128034020114a40c4c00e118650304102d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 73179084 1250 73177834 73177849
    0xe060607021507020d05060c0d060b070803062101020409050702100c0207120305040e0106020c1c0b010b0f07020d03080114060921030408010603030c0c05012607030209120604020906 80
    0xc020754007940c10221003600d512254000d040b4184007030402c50a41c901c645a04c3d08021007190002140b00c1c0016400c03010102c1807040383c1c00303003402c0c401c090300b019025100c441c518003000740b0007030080c24079400e20740c503020390005a40103602c2d0220095540301e07210b403440000b4200950784900503200382407640c0034041d00340c000c0e8100720103568010b01c80a0301d0040c0d0300031001000304054083c40820000890004040c0d5281390113407100c1e400400710b64030300c0020b001c030b1511600b04104405142d400c007500040c1a12000c541121000d05409480ea0303e06007000e022849480d600a50081841a83c2000c142e0800c01d014100cad60040468414000d0500034002c00e80325220b541c50307014008084e090034000a88000400c1f030b04441d011a818513484840130741c01c45072903030025004100500144010492100c0e8142d019000a00e40b070001c500b10300140c110030b8030710100069040c44c0b00d80c00055102d4400d03410346502d000f00912401c0c030b0005ca60b10381354590000307690a034014402c5ca0002a50350600c6d65 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 73180334 1250 73179084 73179097
    0x2040f0b180f010306090e070e0708010e060d0c15181208090402070c05031006140609010210050a0b180108010501090903121e020415030b04060605040521060c040e0606 74
    0x41c1c0c0400708001c40c82040902c03107054072042d040c1952a040440c604000d8801c0d040a0007134500103007142410864400140c803001049801044400b00041c0302500014560581004007502c18007012600ba241100620001d50048005003090411041c8c85944c8800c120344080038100054010946070072216804401b03004025050300d00070402c0c06402d0405500500a2500411281050315140d030006401d02c101c1d00d0b6a22442525000c00340a0844041c0710040c40348400c07603c0900c2c060380360340041d4482c0c40320181d40c6901078ad604005044d8614503081030309660300080000041440d00c1c19140e195600078083d030015136181200126444803a0b00c40d240d80240c068683c2c0c0f0600c8260340c200805800301b284903201c3c0205003003804042d0000e600107000980b00440031844558002c6500400b2a2850031540d440755040910820802d50400200d03025134200355120301a41610310410f0441c442d403440459124842c0404124000301404c1c0604150b400001d1180e405d03898110410805000d6003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 73181584 1250 73180334 73180357
    0xc03180f0a030201050706020706020f0c06060f22140108030d0e0304061719050f040b06090408181f0c1a06030c1003150f06090626090703060203040602040f0b 70
    0x110402d00156015401a045d00341c8210800351400401d42d030b0b48420303030304056540c82c40660040388000901c0424412660710a0042e90f000c0211035100000071881004c8c901e141003906c4022412009000180d04000810380383c601c403107005965140e000996aa00c1040741c2800c5ea0301c1d01031102c1145002108036022664142d549026000116840c4801004080c00303406a030b0b2285134030316200d0001401117501c0754071707014401d9a240c0b40909041400c4900101010f200d108200e0401000401c12810385200003410301c51000c41c1460307000481c0c000b0036810380140c940b50400c000840555400144d441000e442205003014030b07080080b040307c13214400d0310219455000000c5090441c108224109642c43d842e15001c584100d03820074500604426402110b05c03005504003e000d425001046c600c020700030380c54410f950b82d0100030180d4103200407452100d01485000046042d507d0100442d001454101d0b004555030704251030241e00951003441070700d4599a0004002800d01a420181e40010484 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 73182834 1250 73181584 73181599
    0x7060801080c040b060c0a06050a110918071110091a040c05010804020a050d06090c1d180a02150c010b012a060f0c0305011404020712051e0c03180f 65
    0x30b010401015006100c0110b402440034800031040b04400c000000d0101c0c0145400180c0b030134035020f04410750b0080d8142d0b4008040400030040c0e0741c1c0b642940861400541101c14413607403551281107030a4180c401f00c0b40300d42e10452111580c08103565000400451258a8190705065401c0701980000c60858014042c140360480401c90b65005040a55115100512080d0460b448400140b8108403c81c41600c50344d0b503c0030040204088508401d0240641282403c00d5100b240c004480c050030080981409840109041048110401c261075155600400050980c0c00c14055010300c5d0b00110b003107201a6081c07803ca0000c5501030390008036105141c0274102e80c020ad89904030100802040c03000c031291030356000c07a82240d656602c107500e1100026a4041035a515003481c10904000d6410744a109502c10005540021103290300d041c0460020305200c0e80300c405c5903508420041080050304400400010f104c80c291a001c0018001d0388030300100000d8080400040c021070441420030990803220 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 73184084 1250 73182834 73182853
    0x160603060605070b09010f0603050a020a080714060c1c08070207150906030507020c15070308060a290705010203010f050120030a180b070b01050108090d0c020d0816140706080108 78
    0x303140c4d00d110b61181c14000086030f000c0022000204440b810383c021380d01600111800c3c0114a030400c000b6004021f5000102010b9007012004e409070641c150425200784000600303806142d40a200c03030b040540d00c08203044401c001648002e4100e100c100e03102c0c0c0060040301c0740801c40c140000c8081307003604900c2d55804c040ca42071440546c0100806010041540304c0c12803064040e40d1030011840d904403e45041c292101803625011b002e061000d08900e1080101c1d40060100c0007804070b505549900070107000c18603c00560031074030303140305296000d000340d400000003242102c41d80d9039050844e1003c0e66143e5800070b0241505002d0f2880051801280e00100400050030f44101c038500d0802140740811800141d5801c60030207140c0c00344100b214016502001008a507801040c0240d0180304180038000c1094184001080090f401800034411103041e00b011041c05141c805603000b00824144100c8285035504107580354440d4452213800910903030901051003403292150178101c0f04842c005020508 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 73185334 1250 73184084 73184093
    0x120c1d040605060117071d01030501030f030503040f0b09030316030207151104080106030506070201050c0f270301020304030201270201090302060307110d0801090c03020a0e120f0d0216060306060507 87
    0x500641424100902c0c100c1d11304c1580401d0680342e000f4041034547c4018601001007000e003800114100ca07062604d01401000410684000d03011155458949690b5a03500d40c170702a031103030390702c04409004d1101d450100b0048850000017540a031005c1c440d40a000c00011008400340c0c030411300020400080c8070000182c6031101e4020180b480d12200c0d9450405031100009802c583c15640103440c55417120040c00001c94080c402c854108c40c64480c91440c0c209201c241c03038154807562564100d0440c10343c01c010500c0c42d03181c003619410000200217545d242800c0c2002400b8003000c51112014030510000b402c0265003030001d403480541d060f122482c2c0c01c0e00c0d503001c200182d0001485c060034000782c2540c006020318288030002c601c450b952248241c550501c0700c4070007100e034120348902c00d1501c1000410003a540212546190100c00c50300780302c0c58241102c43c40d007010140744400c06c3d50311600c1e900c0b0114540108101b415128040040c4a0075030383c419045080d903c3c6c0d4421034000c25010011031001c103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 73186584 1250 73185334 73185341
    0xa120504060f09080702120610180204091a01020c09011d0604240602070b0a080a05061302040f0905060a120206030702030702030a14060a11030105010e030a0804120c1d0406 76
    0x341c02841c0009500300303004035402c10354101080440d42c8060001d000000c42c03800105c035215400700e5000801c441c0c03921802140050240d406403d049040c4079a000310280425011076000c3c0c03170507071004d010444500001484600c00798900f41d02602501d20031a450b4201505410304840e00c0281c00654891010500105c6100107807240c2e03001501c0d4000058002d90303110030464400c038850314006000e49008002401e001c080d0700549846d91042204800695201c44800c3e081248010000707515240c03500041c44000b040d0f0714900c074890010a00103100f441c1411750700101c0740c9100080c000c5d5900c0900f003001e05a01c900600f01942d04203103608000d170411070091075102c50b8600480c1d15010081e000a49013040c00481140c0d003035215101c1400e520001c6c0100741c0c00034030707110050041445007018080680014001c0c00c1c100710049110b03001d0399a08010859516400c040d4807540c0c3da031174042000d0341081d0346000380d03034001c5607403000100640c80c4100043c86040900700b203469a00c440d41c130040903 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 73187834 1250 73186584 73186591
    0xf0c140c03040911040510030207200f03070308090a05180c070804031b180c020a020f04020f0c010902040b030f03030601120603020442120303060f0305070f0b0a1205 73
    0x40c1c1c40184004100618076200e20490243c01c00c100c0c0c1d445503d01410032019019880500c410035005101101c009940805c3c501e2404646031a800380e00c070f03840d80c0420350710007000000701c1d85441180f40010030310170b40f42c0081031280000c1e00c081410945505c2848211414000e0aa00c0c2c1c984201c0050481d001d01409052206c0c869002c0da89400d0780c0341c50300c04540048104030420590340c84400c01c03481210711024181c2c80030b400000e00101c03d50010203915036281c2d1038064090803c68140202980d02d5a048071091544442265102c0c0d2402060600800c0c403450200c0c09603240c282c0e1b00140b882c0000f020421a040d840003580340d44e650300d0044079400f8951366003100c02d036101e16003c40181e550740200d40c51891011032141c440d0540d0541101101c8841808021045403501d549100080d2944031006481c018000030000301d8aa2504a006014640c00700c00404090f91020042107000300d02ca808944007403032301d403030083d03164251804648100844003003c0750700d1101d0f1001180360768203c15070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 73189084 1250 73187834 73187857
    0x812030a09080a020303060a27050c0c0a0308010311010305040c0b0702011223011e05040b03031207080a0615080402011b060507030e010510030b0c0d060305070e0403030f0c14 77
    0x1888980c981e10400b043d00145010800368001000704142400d0244010001b428000c070120750400d0060010407461460304060158192039000181000031114110b540c50031180003110709000c0203040c02880307000207010489409104025107090703580700340201d9016941000508000e6840d000380f0700c4240e80001400c07410b11034070400740d1030f43e811203204006104a224150035086070f44000301c4056a50140c2001411210340c2c2000400c03510691645015950141d500240c00e804c1000040d241d0b00075901500c0300c0000c241c1c00c014465030710404050045990760010301115031154400c0d0b070001039030781380f5600040010300020090341c850f0407040c50703207120b094110344541500d0311410151802201d1800100740ca400c50078500030b00900c42c903a405502090158032050460f40c0f102c50900b8042c084022003140450880c00e01500c6a1051000390352000840d410141d45954268210408440036404a85098061003008900b4055010401d070540d0f100c2c201d44103180c0b810392250700030768589003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 73190334 1250 73189084 73189091
    0x402190c050a050a0614071e1b060606030204080607050c0c0d060213090204060906091401050705030c0601030f0605060301090b07050a020705120106030209061e04020f071b08060601090812030a 85
    0x801040d420320007041300a0048101040040c6e8400700c0c40d45d078034070161160b420007607080780301c20000e203c012501c420340c4018a030040260309800101460b0011031507020300a245001c1001480940641c000c0003150103900175149140c0e9040001d4810340518a44410f281d0020180449103191072590003030041d00c00c0b0401410108060b801c4590040c050b00304100d03551340007078240300c1d041e0018650402450503203001c0c000c003410305111940d0304002142e0310f414000c002c60900d0400105005540d404440301d03084600c0b5603920300301302025064110f41a190b60b450000850140d0406015907200079401c004074100c00e071111007044030076600041812045000e690000f05099885044071040c0610042c0080b40312810341c01000003260018064910900c0b1042d181440301c0c02c15518660304e81c800301d034010b0302c2c1e4813201418409032090840003400400442c0103c030b003403140142e00900795002c3e502241e406640700310056444010502030212613912045800c40056104001580d00c4036000c000170 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 73191584 1250 73190334 73190353
    0xd0813080a03110d05010302030f030703050409020304030e1c060f0b09150f03011509060602010506030703061e0203070c0b101d0a06030f050f010e0705150702010309021c0606050402190c05 83
    0x6464014111139074016880704010815407400700444940914a200510b01d800c806a802800034803403449003481c460380202c0002c0c103150103420390000310003019200002c148015021050302c5d001d22141110f0482c90b00c901e03060031000a110314000c0c0b04c00644448916115000c4074210380300a0060b10358840c41e01d000381119501c00b03004007011070481d5284082c003a810070745680e05079000c81c0c01c0320045a1500301004001d40e400213014003100d8100340001410101c0000f00050084030b40c060b207008a0000040c40607a642c04044825100d01a800450894032a403c2c41031003c00e151241c881c0c8043c415042e054100c50900d116a0021003029000815581c0c6c0d5840552074040c2d0070043e505030300103a4414500c15028002c01161809000c05049080c3c02c4c030001805c050380f41e1350700c0c44160201090305011039006e030380710742841da40013011455407440c01c9840803000c6200311004c07141c1c2403c200d40003c0904040c02076a455141c800811011850417090440e0f20420762401903c4c0c1e40b280c05c2d050b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 73192834 1250 73191584 73191611
    0x41401031d1e0c0d020901030b2a03010603150b040603020c070e07020a020a0f050105070311010e0f01060503010b0d1505060d08031501110c0d11010309060f0209030d0813080a03 78
    0x200108004503080502909000e402c481d00384200c0100c0340f80900524204400180d44e440070f0b190560b40d009103552083d4403041c45c0541c2c0a01f54241c0c01101d49003030704c481c00d940c00700e610285049030b09960742441a0310703907000d0107800c03203002c1d1180c0680100284000d00c820b5010350040c1064220810031507095541c9d844040051000694155025030004115881503050500c139010103003c0c040403140c1e9151030300000030098450020098100090a000c0c0e03c9060704c00c1d00250046900c5200b1a111144500300b03944c020a240d1140301e100350300e00f10005025007000760103e500c0c0c50304040c804151039041019100641070081441e644440c1c401c88142c000b82d140c802440c060500c1ca420754410f0402100007401d048940e10394880c141d40700144450f00b035954901001c0c051640141c2d050100c80e000360050300505004000102014207010020506e40a130341c0c050039400100b10200e89a001d0013482c1038500000903241003200104440c50b5001150327094005040440d0329280010703105081103007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 73194084 1250 73192834 73192843
    0x1002030a0209121c030c050c0a050d120b0d1707080703080603010b040e1b0103060f06120501290306010c0209010b030403020705060f0a0c020a03141c05041401031d 72
    0x303409150340da011484842a082402c0800d4031668604004d001158000318440545041d44001600300740d05c4e414400c10451041c002c1d504910010000c45180700460301d0400d40b902c092500e04000500418503403800a030150160b00d0764284003418110300300b5541d8a405400120071040401000010440c05002584035130007001114040d03503803d25603040c100205825a086400b1013442181420300c44d00041034007042548040384845103030b4070b00c2405a070042e4094405644060f11040401400003200e90300702d00342100c02c40e611042080a0380c0c0310041c11a600d0350311546e000c02c50300a010f21000c145004002140c0189050408000704d070201e40c000385040009802801032241c3c04418002015010440c003030280c00c0c00c83e109030621382c5255a10700140210110031042021004070242035445a0380074070051600035941a48400012400c1542c1d0b08149a54207810000d402c0800c901d613208100307031010395501c482c03c8030951402c0070046018200744a0340b0404074251104820300f0100030130 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 73195334 1250 73194084 73194091
    0x70b0301060819060308090d2d03030e1c050d0b030111040503060708073002030a02090a06140a1d101d01050301030b040311031207020c0a0603150605030603100203 72
    0xb614441c00d8900400d0754541920000e00c103600c8941818814400142c00f402a9400c03040c2c143c031804a040054200100c05403045403d0840c1145d04040d0603180e001e44a9000d00c1e154000c0d02c7c1423110000e08010705541c2c5246061182401101c108000c4006204000030250f850f80003101064181d11240040d003103d607480769078210070000080811080c20280841035111005091070b0280703141035a4050300301c0000d071741902ca0b6060707140181c480d24020101c103640c9160031203508540321f181c0065424029480405018860050184c00103103962295016060044181e0f4a07541009040c5906440340d80000310681c030100808030007032046445000500154601a81d9503542d0880c9a58540c02c601211055450421501308014401b15407200025600940e00d0700d041d20011940360101421802100884880b09040c0005d004031b156002400c800488411241c4801c1c50390344800c246c0c1182d0080c85503030403040c8419410840c040c050400746602c114007505071041c0d0203a01001070100ea1084 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 73196584 1250 73195334 73195337
    0x30402030a050d09260a0201051b01090b0a141302060d090212010501060917032d040305060402010f0f0c0204090c0b07060203150604030506010306020a0315140108090303070917070b030106 83
    0x740d410051000e900b00d1013201c0d8055204501781e41c4010000072612074a030a280030b0305014000170f14200c2090013542d41003080d44c256000300125001071402c0d4806803000d071000617610f420700c0b00000100310a00c0c0114025055610105411103141d4240b014982002c803c0b9507007980e40d441901c01684032440c010a509040341d000107450b42c1005000703081054a80c1010048035100044250b03a4080002144ca0342000c4400044003038600c1a00360070300301c4032940e0441c100301000c100003042100c00518280958400d0301e0b82c2060b00380c482d4003201c210402e100500001f500c04070940026003401c2d4404070040d0f0248802039942d42c0c82d0046150786e0b40c400c80742151003e030300004106451001c03072079070400924101c07039051a0515540720150ba804041c000507018550020301000d4060003a404100c480403140d075005000d95071840c166210010740480319012400200000310421400300031240302d05455140d0f13100d8107040030079041c83d01000c503001c03c52034403600304089440f10b1148040d5000300003a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 73197834 1250 73196584 73196597
    0x219021c050c04060f180515030d17010506030606270303160c12020d03080703090615030302060f0c16031103040f0f0b07030207090c20010501051206040c060302030402030a050d 78
    0x2814002207601d0741d84550b0035403085090070321080034103118012404040b1305001c6541d440f4814200c23410038400010b41e0345445a142e00700c0300d40350000303e80002010101070514550780c0c0d820030b00401e803004940c840d5220804001c03401e400d000100c0b4581d00e0485c0c005c0c02100350802c1c100820724580c4455059604031483c2c0050100b0442c031008004007800b07241e10341101c514001d80c080382441540007801001e01445400150740548a980040c01480d003114040c00701d000d000c00d40700070680c5c460000790014001c2c4030001d55848135000100c1e000303074141c050803440c01d41324020044a403110702100724100540c0c8103040005c1041007000d4000341c51200149038005280128a525000d02d83e40150642c64042c0f2103640405d402144010440300081c8001c0381c60820120200c03000c20300086112030594000c40710107864101548010b05a400644641a01c540034511a40da120b600f128020300f580e040d44000c2c8502c41c426006143c03c6031010b01101e9404c522075070b03400e00f020013a00101000514 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 73199084 1250 73197834 73197853
    0x1050c040510020a08070f021203030f070f050304210302070b010e06010f11060610050409051806010515030a09030e03030c060402130e0d0c15020a022505010219021c05 74
    0x10a040c0c1000061a94001413820034016564480700c1d001e0f1144c041c1c4600c1ea0360a2241c10740d143d18040702d0907001c0c2002941c7c1d27a03140010954108080c1a111003000031200352504d401140508101c0307005642100c903501840300d400c856200d0300585c908090f400c0603000d001030000513001c00c0c0824003a14a801305408607242c000300040100500040210820420204455101c1004100290800302c01d85039812240603c3c5000d44461180342e101c3d0000754640020012544a0103039030328032240b0b8100c1948c0e09660390b40101324034031000714006d40e00944204080780040070140d101300c0758640b02c2e0501c651884a01e030006402c582109400c140c060300b088003000110301c2e0441481a0700e040d8444100428500305111558580d0200c030082c0600075095049018001100c8405410301121741f400d56440c80c0b00d2400940b1001c04070340154903449002a214403541d20a8108000e490f4103038018030302505a203084a040002c00303901aa0007804154050072042203001e00c4284480c014001000c00a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 73200334 1250 73199084 73199089
    0x106060c14072303010b0d05010b010818030f160609050d1202070c030602090d0206130e011d19150303030c081b0a03020a020c0d05150109062103020c0301050c0405 72
    0x401031101c080680e004240144810405054000c000e007081c0300074070341c40d0246000403900401903100060b84c420a0a00c4000c2041015003095a800301d007030761000410b40342c0000d0440142e031160200c0202d07400500881c681140d00e0400b6003d0f04802d44c0701c0903a0b02d0101d481d00b501b10b0300ca4550503141e82e009840011030070764020490000110590404620f000c03221b44851006149600006000b6900002c2170749007907030b81c0184107207100c0c3c00400483da150300003440e09400d5100d0380f240412400f15040001340780480d0014020403407080c60301001c02a40c8100f82c00d203107207070407420424103e5030360302e1320711050f0301000321140c0514841c8e18001584912440003609840c0002d00c14000c05855105c0460744c41e80e40c1c82070b81d088040c60b060143c0c81d108141c50503402c1c050308074a4150080221658a0b050020014440071228425112907210341d072541d9104c8181d42d0b6030301030b901050628a4000d006162503410806082c0d0080c0b06560304186440002400d541e0282c410502c4444081014002403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 73201440 1106 73200334 73200353
    0x90403120f0509010c0201180b040203031306030b010801151707050c030d0603021804050a11010c210e0f010c0f080405090403032c061305010b030106060c 68
    0x650000e074000009100440380e18800b0760070045110406070040c4200d000b801c41645000c00940015101d00785d083d54041c2089030036201c100704002d1a851a841d41c07001a04003903030041403881c0b541000415100f4181c112545003015411015000f54020124141d50303540555450070640e11044142c400d4091400c0d4034803107000000f841d408c4041c4650041c0c00352482141c1001c054240d04040d14004202110028031340c0e0301403840e4901007000503090700510201403424140c808840d40d180000d4a900080070705441c2e0601e0300d02c1e16800c1d080301091a0500e02a502e01050400c00800280000740d00c020241c074440c1d82c030400e42c2c06d1040f180121030203050090b110b00740314201440d000b001008608074601110550032022030180840200105001c000440102459143c100c00480308803880c0310119040d40d603404081c11039403400e004100052455440d0003189407510304000d03611 = true := by decide +kernel

theorem cover : BRFrame.Cov 73021584 73201440 := by
  have h0 := BRFrame.cov_init 73021584
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73021584 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 73021584 ≤ n) (h2 : n < 73201440) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
