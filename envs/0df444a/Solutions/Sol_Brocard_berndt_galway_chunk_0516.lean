-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0516
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:12:28.807274+00:00
-- url     : https://prove2.me/submissions/17229daa-548d-4be1-b690-3cda698da05e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 92625899 ≤ n < 92805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 92627149 1250 92625899 92625901
    0x4060c020d0b0403050327030702121c051909140f010309021507031404080303040b130c03080301140f060d021b0303040c0608180303061c0204050a0b0112020f090d02060d06080307120e0108 83
    0xb00840152f050300c0c0501948107810620808440c140c1c000e071200200c988459890f41c1c90050451402003d65000108002001e00c1c01c01004440340341c00003051200740c9104c01c11070340c0c6000480c00740c01211030283d040380e40404c188501303062060041a1740c9000e983c0c0c00d00c10b000300c980315800c184a10311451450340d00074000718001c11100743c0d040c7d80101160400b03030840341042d40c03207500c016140d510960b2250004401002105c0724400c6038508901c04131030510303900013124001005402042a1400c1132036000c9200c01114a03000b0382d4007a910022001c40c0c0d00c9140c946800b201041c0180030360700015038000301090311a0408406000403100360400780d41507998404c1071104042e00c1620101a19003001504000341c0c03100c1c4103160248182c0710b804100d80036080c0001d45a02240e4842c0c0200a1041041a4001030002e082d5128550204c2d02c401d0840400d0001a8050040c030041668087c40c10702d000454174400002003032018401e11111811551400003130721110f09049009011486100c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 92628399 1250 92627149 92627153
    0x6050105070b0f090f0a0605040b0906060d08030901110d360201080c041707090515090a02161703011802090d3c051e0304060c020d0b04030503270307 66
    0x400f41d620803c01421510341c10414060f00d03140500c43c1d18107842090342c0b4000e00c0140001e000019500c50310b100c0c001d09031410203030003003007007400386c80350103008408040040781000c002900000d540d10304002400c1d40b10982e12a811005103082615154104440700c10456211450700c114410020904001d60384e10340240c005482200d00281040b1107494100008529001140030f0615540340c510000c00e00c85040800c080300b20f460107802c0c00d58000605001443c0360b038443c205568403603601407001d1b03141c41000080380b000d0071080000500d00c0144010a480140340c000196048a402c00e071804100391a82c0030704001c0307100d0300342c21035084100505600c0100b0290072608120303085601500644200c081c0d0b40031a6403000211032489400315480c0c00003401010801c00320881100d900c200b00310100d8500c410390b00e10440c450142408203e4000409551711801704401e110340084c84072026140c1881d00805681c4220365070400d0780b1000009064608032807000e07500f0400f068004500e49803481d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 92629649 1250 92628399 92628421
    0x50c3604060320220504031427060403061b12020909010302010c0f12091d0f0708070207150806120c2103040503160501080106020d050a03020c16031506050105070b 72
    0x20382c8440d1340000812180b82881080030040003114108038000252078241450001d207002030141c01d44000c5141840482108150341001d10500341091001341903a01c09540814424051a40082d11181c6070405041d03110b1880d070206c0342c440580f0780c0c90031042603888107060304070f010302070809802c42c0103a80107000650003081e4240308039004c1e01400389002c030540c1d940396042c080a8010000a0928030042068045208003031020740300b800e0606810f40342c215204000808001c25250404c080000400c01c80c03402400340c0000781007002017900d44c2141840c40944807070800d68604d801104601d9640c03990030004500c20304030140081c0301181c6110b0602c2641c135010f112034101c0e40e41d404100400103c1d5a010020004100d40c00b407032900c484ca00d004005000c41d00305901020540d004054104016503107d400c4a110401604005071240740701c0e9951450140610304a24034523602c001d000c01401071000b0700102940400c0c90520001d51114011500380c01070b103900601840c1c02c4008607a0358101c1d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 92630899 1250 92629649 92629703
    0x9090c09050a1e0f0c080c0304030c0206070501050103030513080c011d0a18050411030a0b0103080a03060305030a0c17120a0f09050a150b04091203050c36040603 71
    0x252140102c0d5402c14480801c00380c002001883c210680d44e0038065111944078028440b0501090a20704910b140020f00502d9520000380b0050402c500c1c1d642041c07c40d40d071803044d07941054201c8000c00043da180d2501410fa80c0c45280c4006c071950f4240000a010351000403003500150f0107950f0141d07907900c44c88214261507490420554469000c1c0340120700d8492100304040505051380001c1000d0810307041603240110781c03a01e43c078000d0f00040409004258142e0f0b81504480e03010b846641d46660010045000b0011500024258000010284202c503800400c82c0803660007428100700710003801e20310751503902c26502c50340d40d030340034801c00280c040d803503544030103c200da4420f40070414035080d41d640d80c100314501104a030710350340d0b011042c90010124407606c81c0400080d14100b01c020400d8236151039240e1008010340c10540c40340000749108800c22b00707442e4084c1420344240f0304906807800700e5050264080007002c02021411311540c007445c1c14051602100c4e08080e809242c2e10320011403200080b4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 92632149 1250 92630899 92630911
    0x20102031b010b1002061b070215090301090204020403060c090e0115120e030a020304030c0506030c070f0507090e0312100609030201050d1514040507170606090a0b0d021309090c0905 80
    0x541e030000342a0b151201088004201d1844c5e01401d49841c1c604085454500510319111902c50113000c02c20058641259000380c813850036589a4903140d50100080c0581000c0310b00a400034008540001048600d4019201c8401c2d141c8a8100c40e40d103400541960724002d203c0c00c0c140080000940300b005014208130342e80c26003c1c600200c2c1d40d4509862081c42c40d4450750010005900020341002030198583d006400f906080703072158030314105160710780f0b01030040c0640a020400f0515882d07007040010402240102034080062290482c1001096202c0d003000a200c03003c0354614000034281c00d984140c5400b40c80c0c941c0c841006160450300110344982081c0903200c0481e0b07480e1040038503003400344d2440004010464a0f100c0c169440401c2c80299a0302915500500008030119034841300c00510b51a8040c1d415075003951500c074000005281200706a100d0fa90488002806241403141a00140b640000c40840072009903510f029040892b15400390140c2811085581400700140c2500041d030802c07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 92633399 1250 92632149 92632151
    0x40b070311031f030b10061b020603160e0a090c0f0512040b0705040b120601090608060f090910110703180602120a050405091603050105100519110a0305030105040b0d020102031b01 79
    0x3c0d88030380d01c07910011030035500481c1c050b00340101081280d0b8869000e20884050200c128110255035000c42c000d4003014249031690141d420004114503c21002c0e0050028001d0054800c00d949440b9007004000d928034840018040c1802100c083d8003400442d4a140d803405c8220100ba43c2e82d0704c030303038140104c00b81060701045810800050640b08000c050080558191100240c604020001408036069540030700d00b405080740c104609583c0e030654944d2026000c0d18000f4007647c4280250f400c1c20864215050341070725058a02130203015000c064815075101e52158481d003145216080040102d0f07108000c0113901c0105002070150150000d00742082c4941402420180ca0f070380024a800303004c0712840c42d10a203900600a01c3c41e454003409005000981c1c0c3c268502107041c00c0189035104000340e14825100426030481c10714031410a048064000c1800c4c0e44517041c80d494001c00302d074001c0c80b50520590809001e004030f803400d1030000e401c06505800441c98000c841c022000508a0614040125 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 92634649 1250 92633399 92633461
    0x204050d11011404090506090604110306040c090801060b0702090c0c12090f0a080d02060a0605100c0c0503011e05091203060f0103090b0c13090603030504120501060902070b040b07031103 82
    0x40003e000940302600d1849000700d002d2800b24140943c05500030001e6108034100704410003162840d034101c1c0d0300000181c5002c0780300800300001395006106035116041540c40e00c0c0c0005812420007019041043c42214410869141d541001d60030340655903c800184e0409961001c072480c9140051460b200003904642c08a1300903c00115160140d43c0318508540000810b00e500341c0c0d049c0f03c0140e0084640b501003240c5070130305020400707103519400000c060210000c154003e002e1410f80b480c000f4800100240040d40340200e8103400c0b100e90440c0c1d00700c020b0030000429520000407410340702ca29054140c550556551004000241c00000c140754140360b5205c07a0710003c1107055000c2c2e48600a4195296a12401210342c003900f4803003940030000300b901c0c0400910000b54007804980032a10402034441c2c0c0d42c0801d04019004104076071008003610310005200b400c0018142c4407074803403802421807190590750040140c042c0c981048070303c0f07017620080001860280845204454143e20181c6621b00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 92635899 1250 92634649 92634677
    0x30c020303070b0103030e09070f051308010c02010603050f061b180d08090f09010e0a02070305040803040f090605010203120a05090f0f0c03010c0203070b07030f180605070f030204050d1101 83
    0x641c0d125a0303090350003409040040c006c0c59004030745002422000d8642840c1c0346031220340180481103010041042000002c1d01030000e1202644120181c0010b01c02006103405d1042d01900a183d244002c454a004044180d40d0310000450510b1052280c061907003000c10001e0328007d155804481007040c5501515070500c441d4030340ca029030b111184900c24003079a034080350040200e03030310f10711172801e00c540034034001031000305c03d170115068221800c0300015840321b0380ba24040e261360040c0d0304082c019100219000845a20310703071203103040321350b0044200302e566180c0c001245c0700d220705240310600622800200305081d0040c1e010980c80202c61080e64201d09584420030f05060300b0304040c0d180c9038400c0201c400e41d480c003813003440141d0b00b2038002180b4125440e6500c0c40102c100901003002d159807003020440600454005401910a180540344d01304c0480c43c040b401094182c6014001801603814050070a000c0e01c226802d9442c0106250f22129460303032044030400e000050755040214242511507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 92637149 1250 92635899 92635903
    0xc090405060a09031704050604020f1e0904030302040314070504060614090d020103021306090f05100c03030504021c05010c030c03151215050117151003030e120d0e090c0c030405060304030c0203 85
    0x401207221f90060141810503004000c41c42900e00101c51086440c0501101d0b55030084500c03103070321481540d41646598507824103030001e000340c2c0c0c0302400000d0a4191030b03610080115941741078400c203d50420160fa1286011212041c0307003020500c4403141084400c40c20b07d41b140c400404c03d0701c1450058908500c865a180201260384d1001001c40c40d210824080d804450901b0805001c0070380c2d03422020b8906420080000c1000f100141c14142d0312404142951511000780b5095888a241d8494003a90381c0740c801e00a085880d00c0c007000030710707118407a0041482409640c000700003100c81c1c42800c1d4280b0710312090a13100308030101e80302240c1c90580c501c14062405001d00030101520400c00e00d40558400d030b810502c90b88801580e01945600f0401440000025502a2501031402c03040342d0280e400454034405002002905502c600300300303110340940c01480744a1a4030140c0d490010f0352035080441165001c1c03860080034541040c8001e02c042c0c1812000b40d5841406450100d0310709a440d004070b4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 92638399 1250 92637149 92637151
    0x307150c03030b0d0b010623070305090108090c060a030e0c040609060e01092309010e10020c010606140406050c16030803071409090604021605010203090d020c090405060a090317 78
    0x5020038801181101819058440c1c0d00c0445410380b03044c2d511020603500c45c024113805004440a005042c4442c0740640e43c01031900c000140390301c3c0e196594410f981400303400c64009880090000b44148005002c858000c644050170030b01c058105400c020783e0460503000b404050445543c0c2d846900c1140304983c0e01c40c01500700030091914001441400c0054811600505030410000d40b41403c6968518902690746003110118011000406441e034961180c0501908c03603c0f0301d211b21464000c0c01400b2030b5603005081d58040d010080014903902c2c44140d03800884d80c00100600d03082408100585405070000b48007400c45841541e5940242545004450710300d070f0025200000c02104000d50349402070031059a241c6210101800c054400d40014400039006010343c0c09183c011403200f8003820b90300c5a0301c40141d4000020b40d200c3c50048580b50381c1c3c6030001909001881040005625070a1600d0058011a0044041d0046030342e4842c1d214050a0300e200304800700041d103c402e50380c9441c111090b0f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 92639649 1250 92638399 92638439
    0x31c0f0b0a0e040204060e0f220204050a0f18051e01200307020c0901051e01140708090307091506030b060d020a0302030f1b0d0506060d0507050a02120304030804030c020307 76
    0x1e0b12141000d00521088a06541124242004400921030b20407540e0403003075031104410041c44000000314100352038009044600940050602003032050440258100001d800800c1e8020444400c001304204c9202d1103c40c405045900803810443c600c981484481d000a10884004101240b100c010b160903040c91041d240d49903803002c4140040c50740e051010900d20b0304c040b14500180d504200c00142c1c0c2490241d410720384160340c0092940030741d00404002480b4040207090685519190078480d41c01c1d030181140c82e1081c06800c40c085003440780da12580700d10329a4180d50140c0c50b410148140c009001101405600c03820502c035605030305405e4001000e050a443e50003680300d003005080b400101602a002110118030b0000e041c2c041d80204007502d2600e04003007030114683e2154008141b00303208a802401c0000d040070104140380e034209e4010841540142e00b141c141c413590741c0a508580c0019500240010507020110b80803078494549611114001402c1c1c565882e641d0350788400380309480e410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 92640899 1250 92639649 92639669
    0x10c1b0c0e011212080105060f03090708010203010b07050106050913170d0504060614010801230a030203010c02070e0705070f120203091f1709030405010804050f030301180b03031c0f0b0a 82
    0x3c00c0810954225428403100c082c02c0009035941064006100c80c000d00c41c1c840700c1c24501000180c807aa004210142c000c1013003400031566540c6400d4040890f900c0400240c601c1c1d82002400a0070f4140f55150b1846440801c21182448566940c4c4168185c682e02a0b4100c000080c8694036084055200b564040d80c81804001101da140c070b905217182000500180c1d040c0000400100000000808070b140c034240c48061031030f00c0c82c0c9003000280e1071003403c0c0c00107034040d071030408880f0840745c001488005488208a61034002c0e0740c0d181d000c503203500c00c4582c001d1689401c031502c003000600800d005e0f80e01074000e005403400c040031203021400d08010355140d58102c845288010f04850b0b00010426072980f07806034102907910b003c1407503d59900c01ca01c2160304122805000400340102400b0389800c4900c080300341c9a40c6e5a4500740054000d032052113000805d40303850000b103454030b000401c40b4040213040348071601c1c444210805a00a14030714104074681342e00c40d4003003501591580c01c007801400c42994 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 92642149 1250 92640899 92640929
    0x9130f0609050903070f060e071701050106030e0a080930010c0905010f051b03040308070b061302040302130f06120501140c03070c0b1315021803010c1b0c0e01 70
    0x802002901c0380035128408980040186a0106d003859001e140101d4100c90007007172450414544500d8102281e0000c100c0c610b61400d081d0115006400c128122a020764051160340509494952500d40c5104002c1800300104409802e5007891580f03500a104090034420b07008950302d00403680c0443d0400c181c16113940d202d400d944113035081101c2002800d02032a00703290900f4403020140042c0304030103064008039030160f00b000d00d0510030403c8401551f4802001030300c400e017518020520500558019200301c1c061016140e60060610075101100d0b00246082000c9000d1844d6038000c0c165240c034001c903d9140c9002150034811000d086004622842c00014040c21401e144521010041c00011410408206010b0314641c019036450800d82c01070442044c42c1c540c180e030f0001242d04250020020701c140d10801050304040e81c050420300b440d0814040100c8407030020142201c0461100a0114240d40c00e159111f52040300d04106040c424a41903156580b280c29202d28058240e004500c2100018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 92643399 1250 92642149 92642159
    0x20c04050c04050a0b0702120a050703050123010e1302100e010206060402090f0907030e0a060b0102060906040b010b0f1e04031505040308010b0f160305041a0f03010b09130f06 77
    0x11094903030041d80c0031030141c241402c140000348407201c584102041c000d40070a00000359510494001600a880b0040b200590324034600651154001c0c0310a88640d4a8002640b0800302d1042c8410040300e10701500d040750b44e00b03010100b000094007078280300804240b40f4160005031540000c0c0d42002e50705031118080204007600092070541d000f090300703010300d00501180c2c0c6141c030b44070850250020100c4070004e07030f0f564242e07044000f008880101c1c039052240c800c42105000456110100102c420390a540007580c1744403285540c0c407415100208800400001084103a40c0d06000c1e182140e055051305140c822403a103810b00420f0910f10840c01124005010000c10080300c0b100e90103005004024080ca2920303441c05003442c48144503800f18a1000500c0e00845c00000302112440783e64035030140d904550f00d080090658201b030080803100e00c0d018001c204003110260a0320500018200010b10710380c02c01001c0c1020390400c0300070b40e42110003029450141943c5002e0201206840349001030081d00d01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 92644649 1250 92643399 92643401
    0x180907050c0d0c080d0903050d050109050402010f110c0118030209010b09030d0c030f0e0109050d06092901030809040e030a110c0f01020307021e0d0b0402042003070c05011803020c04 80
    0x184100b4180100348504900044000050301c3c503911007024002000381441c142540c80e8410824003e079080e03d0100041076114a81d40200d02660007a62414890721030460260307031041c0300c0072600007aa072056407101050340c031a41028001a20304859048010398a90105640800a8101800c940d03c0401d01101c641001c02c100450b1050504d0291100342c1d80d5100070b0581e400c181c140c0c7e02000845904400740764000c0d0304580050a010340385191240b29400c2c80c400600d9503e030300300d5071014100a0280741902e01040e1240e00c854801840000340d10715500d0038450f600c610a1641c019440700b41c0c1a51203082840a000c02030410303180c0a81e40764910f0342d854240b4042e040b5203889280e003440d00030304a9034004240e8014a074159407440911030203030968581c0c0c122400e0b40c15400301c1c541c0040750410404542880c0220310035541800741038040910001c03803004558120200507420310020750040e202c5d00d1442030043c0290b00014603215094040107003400c1c03905059000da40052200c800c0d505003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 92645899 1250 92644649 92644663
    0x1908040509070207030b010902031f120302011109060a030b030c0405011706070216090e1501081605040506010819200910170105010c0303060e040308010f0b030603030708180907050c 80
    0x350f202421050b4103641e25003080e00010f004038102c456001c030000c2d011250600ea4040480c444000c54a0301d1940c4229042d009698854103d0042d400e0140911841c20860103481c2c16010044c8924101011001d08038020501c600e00c0c40c0e450b2192000030302c9c007500c4520906018ac2080c0e0354655404403128519464090701078400821940041c1d2380c511754440e08600c3c41c080d503800d80c001040c001016413009180165801d400018184000c1c0001540107001a0078071a210b070400320386800740e80d540c0400c4101d4a04603801d80c04940483c2c00a6107a1455001c1c51038800203409000a0b04900c400e550b90340141d103800720300796103000000c0143e2585401900c105c46002a89030800140d40c0509840b000c0440601c1410305100351316140d102054003075080900982084000e103951480c2c0360030010042e00d401e2082d2012085c00c0751011813540c058000722031046c0400b5008500d002d45c113541e6405594041c0d2140b021040d0680101d0f5004d82e1503018503400b80704181d640719201d5001e10702e001c0c14045 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 92647149 1250 92645899 92645911
    0x6060b0c0604051b03030714160f08010b01051905030705160b0f090303071e0203070501020f181002030702060702040f02120f090a02150703170106050406021902010e040507021908040509 82
    0x50702c81300b00c030365941c000f084039446030b80a0211940d0444641c0315514101301043c203031010070500c24000c158080009000d10494602c03000071b003c80d0244500540f4240300b200c61244074107107074180011001b0300900c0150f801641c1c610b000303860078940010002c00c1e030300b14844c202d50075103184003484400200440d881e0b8020000e030002d585141003100c03002d40610104043c010341ca0103601540008036000740f0a0342e43c890f80110095540e1200c4241c0a54260f1182104041c09130207680315000a0408811099580816400942c039010346502042040d4100f03040c126801622858110400181e0340040c0c81034103075421620406040000120310b01c0c0400402c0060781c0d40c48402c1c08800f40c1d130b60480500d4004d02040102e5501c1c445428203c5144191400c4810211840000094a40e50220042c4105c5081c1d5007515442680380024441c0c1c8070908178040d0000c1c3e8040280c4800d031805070301c5075400030940e004503489000601c0c042170107202c0c030032003c0d00d03204804a020801820320102c140c0d8000303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 92648399 1250 92647149 92647183
    0x507120e03011d0a1401150914100b0d02130b0c0604020f0405060604050108090a12080702010e031e0a0c0605100302040f0209101b080d0507030b04050403020d0c06060b0c060405 78
    0xfa004280103603541c0c5902e480030340600381035580e006110800b980881d442242185404120940700e0003c00090b0100d0010312603e183c50a0000704420f0078425003074195081d0020052030810320f1042e08000e500241100c1c100ba82e008140003510f0300900c4000c11101110030701030322061900c0c1c010421980c0114031554016400d10042003034540d00d21040b5400d0701c009082415061b19501499890508660001001d001d4008421521250007010592040c0110f90081c0b008010b1009400d40b01d015000070848441d156031103141c4401c128401401e4030341c08078684035411080903100d901c00c1d100251011840407407500c0d002c1c025410706005c1d0b14070441602c0010b51905541001007024540407a042d18100720540c0a400b507104440c1c0c600103a055000188551a110655503020040c02c06407107460100b031030295901c8241c113180c01141d00c42d54064018241d01c006105040d5042038030b20804031103460380c4030f20200340c90280c0400751034501c02e5000204600d103010302c0c000d490030403140040301800c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 92649649 1250 92648399 92648441
    0xb09031c1214400c15030501031b06090b0c030c01110c010e06040b0708190509150109091112010e030c030a0f09140402090d0209070c120e150a0507120e0301 69
    0x840c0f15030441c0305490400d8078008040351035030502d00d20403043c9030054088016280c0b01c4941c070707a030700d41c00150507240200649030b03214240d444200317400c0045220b1a0042410300a0401004080501500f51f0039281e40583e0302d811a03681e202da0846044052084280c0c40101d01201851802d1149045145c0e8041c01007030309052603216590982c0f0020001e07000c0028a0002904210b4811401c0074032016480c41031081b820103400c4561110022005002c44c201d0102c0000b645031042c3c0210042203800c00303080107460507800c0911901d43c01d00c01c4101360a40d2103105214801c40101300410a6484042c059a102c90070500f004000241000800e010405160340501c4030407141c0c2084480f1141c11140142d440c1d40000114006007505840a03503c185443c0c108104181c10450341c0c41c04030701c98910200c240760003810035945144090f4007507070010755041c25103c01c4802c843c0101410700040c10914100f24455540d218181051411030b4002003012070b54460604007401039121400c4084961018 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 92650899 1250 92649649 92649721
    0x10801020a0206011814100501080a02030c0711010e030d020c031204211b03030c02030f03030c0a030f11070c0314030304021309170d02070506010b09031c1214 70
    0x14695040c0070b510480340020324034056050169200740b0b400104d00c014402d09247c032903c000300c0c2000ca81705103400303e52000e001402d4650780c2d1003204c1c440c14122001904184481d201d6101480e2000085410b1000e00d4100050940c0c082104442c422011341c002e04010100c03d040c503040c42800d10451011b0b080a2106101c1882c082d80a94903008032402d4003440e0f528141010915140c10100624090410700c0d408014554890f1000c0c0d11a8025403c176200e80c041c2442a45c1d8900c02181c42040d400024402d03071020034400d4109c1c00c0c03507481410010928070415040601c0a62103003070200c0701a04400010000c0095010f02101081004000303142185084d802241c00c9200c50090742c0c13500c1d07503581512820000c82482c0d1034004c182c01c0003215200c0d03154405180080d48484003d60702485103030000581020340d00308484402c01e029018080201c540301c200b00011103490a0041440030001031f0340117040d10b911601c216a040f01d8000f84941c10b000e8901c260885944035001c5c0b44c02c01020070a00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 92652149 1250 92650899 92650903
    0xc08010204180b0a260a211107140d05010b06030703020c070e0f2d0429061c3e09040f110604030519030810030f061a031c08010801020a02 61
    0x2000c412000c0340703026020140c181440c00d24251040047c00c055000f01901240541c405e45031120f41358545846080b8902e40d040d06030703140803a100c0c0d034250b418190608103090501c0003000c8643c51152000bc01c80c804c00c00b002440c0e0ba0400c17600040001c1e400f14540b00b41810821440c801080d886001700d28a09084c4840362030b81200400110394113128000d18100b0074540c400551b100031b02010121100d003054035121016111058040000c0303134501500c1402c0790f5010680a02902008000d40700e0b104c9801c0c480310030104400c00c152402d0322201d400c80d51001010001581b002d989032046009146920024130704640100300450069070804d04010005060415483d50a600300c03d0344411001c801c40080e0300c42c861500002c209000300388154507103a10395034440d00308612940319100c9a80e00c074120355a000c8140d00c405444401c132090303540e0124007141d01801440c49201d881a8040041e007010a00d010f000d5180c0d086d001c4a004143c0d80c905610a503450f02502402c0000e600e803203d0020000c1d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 92653399 1250 92652149 92652179
    0x40b010b03070f0c150c0225050603041101030b0a120614040803061e030d080405100e070b090301060b19020105010602010b0f090603070e0c0a020d09060504030b040c08010204180b0a 80
    0x641801300c400340f0710080c0306038000000c40506041c80f061160078105070000b034641180d03000800c5d060241541e40070708028841401d6050390f5000d0081421940c494441f50402c4a40c0e0b04582d0500d5661840a0b41c0d035100e40c25000081c100f44040902c860100b0b103084400c0321740c0c2c4d00090300042e0701d40d014000059203000840340c101201f00ca0401e0700c3c41c1901c100d1409001a441c01590510070345c0000141a6041141b0b644200d0145060368100d69050140c0c130142d40c00b00c0c86c4925180c00181c824841c042c010800707042e4950010300002800d80e119201000d04e43e01408a50345044c5030b5482c01c0c084554240a181e02402451000b4030010158030f0104030040781d0030303003000e01c1190340000090103618104062402414060000c90240c100490302d442c1e10f83c07120080e04010302130f48840300c91190082660404403001030f50b0780c514140c03843c2c903810100100580101c8480711101000182d004007400a000035003221010711880340d010040750030072a8000384141c0e016400f000c0b400c000515940748a2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 92654649 1250 92653399 92653427
    0x103080706021c0203090a05061503030301030f03020705060f360402070206070803041416060801060f03020c0f010c0e040905030405011b0b041a010501053c03040803040b010b0307 79
    0x143e00c40240f040c0c0c11080404030b40e80b00b0416031000c070420981e5840001ca0400013401041070b58503a85489a450300040c0b80c9604032078166104000410004084615041c550b41c040d1040c3d882e0140c4a1001817000e52010050408543c0007140c1084810309065030605040c003012140d5002c0038140360400000d1941e0b241c098071480e400304090b01591904400c0340c0801e84d00c0325049603030b41fa052a001c102d45450600d0140f00b440381003141046007420440301c2d0306848490312040016071030505c0032240b8881d01d0b4810000c06409202070400100100705201100a6040c000314415004810080402c94440782c01c1d0b00c80e5050080c4040412000320481e819500c00380313450781d04010200101c20b203a404100c0e00904109287c000c12050200c0180c20b03950071818540e0f00612660783e07400442d40b5004042d0104070400c9014505110413040480c0314202c0a41c00e400743c81c20324100240300b4103030f80044505842d5401d0000401040000000e9024003501140d20302e1400c505052000030301000c080044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 92655899 1250 92654649 92654651
    0x7080f07020d1407062f0a080604020306010c0503030403030c030e1603140a0b09030d0605010503070206161101020a0801050a050406030506010e04060b0a06120c0302030115080c1e031602060103080706 88
    0x32042c03140b40d454211500c40d45c00c04024800060600000c800c85000c5007003400341030410b034090422201c11442214003130001a070301c61040c1e0b144d210421009500291160341880304005000000440c00e1000d5480307180039480024140e01024009401d50f503041070301c180076401440700d500413100404c40701415281c105680c204049441c04426252940e582800b504d1164504104404603000200809811010b540c4c01e110b01d65503800151140d010980e503e20242e0481400210342c06401c944a01100405181c0062000501c246d2582280d2140b48c20038002503004005000a05084000c0f42c0204415078081040741d1450315440c0e1182e00601078012900503007c081404e100954001c90343c8024020700400d40299502c20140c502c0c0c3c0d80d0101c02030290b05150403807848c94043e100341c0381211302003003d00c0407007044000b01300c610385002804217030380030802c1c00701515080ca020100640c3c5800344407070580d80d0500e144041341050240003a5401c5500032001400025401016038000640c8000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 92657149 1250 92655899 92655917
    0x307030f050f0a150606050301050a050402030702010b13060504050c161502040504020d1b0311180102150f0105180114090c071a180a050312100806070807080f07020d 73
    0x64540d0038801c82d158080340d1841141c3c40d1905105111503180622010740c48100800c0381c6e60042558240000d10881d1391100d0150020046400c1903001550700080b20b10000880d1401c0a0001e80c4520903086c01c1c003519507490b1028003450801303218454010200c0501e9074101010441a0391450360080002040505a1070400321a90400e40586000d48030041c401d42d01c440c0701031054801084510510340b032680d480c044400d5540e0180c0704040540804001d002e03d068080040d40645580342c00c140c5046100e0545a08001c0740c161442030300400036011400c1e000d51520b07080050100c3c039002c003d00780001d0f12004102000c900509400d00c4882a41d203100c3c00d548441c0300100030b02569402503c01c05100c00124108003401c0009440b60302d4949241c42145091800c1d550343c1c40b00181e0040050b8020040104501d0f0300908690b480b44062004407035075516070b6001410510162100b00109203982d040c440030342d0308521010344c09100801202402e1605050095071000310480841c14482048 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 92658399 1250 92657149 92657153
    0x12030a1112210609130303020906040b0d140c0a02060403081005060c010e010e071815050312070515130f03181707120f030e0d0b01060c020306150307030f 68
    0x809a038104450352500c007500c1d00c02c00c114208003814420248401044280b002541510f4091001c5015402c000b002c3c02c4101c8980d43d0a074000d5220501840c1e1100c0140000501c202e4507000420032001e42107000324040f241171565150b481d9018203980b06600301402034002103030f40006c500e540241c061900e28034580326881030038041c0c62150001c541200300000d4900907400b05400c2040c10700c0b000c5000f0060034450076102500d1700c0707090041551250000d80d09001a6034160001044407040881112210b41c0d9000000e103064400454042803c1c0007169500c01e00505021035040c6c0303070b4500c0b8005028a0300c4000c030085030004220081081ea2000c4114040c136104c0c00883d0460482d06241d030803102e403100808900c90842c0a940c408a1041d40004181c01c139180f60308451640c0d01942807150302460f564107582c03400740c0e8a0342580021000042002060420784c1c00c50013442280c450042e07000a40c010b060038218000d04c1c030400758096411013001a100082e6200c116601f003401c90003881124 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 92659649 1250 92658399 92658403
    0x60909080409110f2d0304050102091e010906120b040e0f06150604030602030403021510170d080105120c03030d02030a0e0706020c060d0609090c0f060809120f090a2312030a11 77
    0x24550405c0b00030001c004c200400c101540188000d000403a00d20700441c0a1440301242e01d1005074071980002e030341c042c04000480c01115502d03044268000d0100c0d00d803241501107821944030303c04811641e44402080c0c42448024001a40c02c5040070110344400d0f09a000810910312903488000e1140d98000000f5062520238094110805c200c6040390703201c4e040203443c00f800d50801d17000381c44026120140d45042c030030300040c0d1280b84603503d49807404c00d60320b080100a046d080fa40f400b41750600036011035803140c3d81c05100402c01024042c0d001612800c06039210000c03183c800c0000c040560100c1800d006542c2c0000e103025220600b00c84070359860030001c843c0c80240009604ca501c40d03506080050f4204540388841c1810b0391145c4100ba00306035035511040b1020082944c2006d51a0480c180210740c41d00e0100041c0020640b41d0b04283ca01009200410090815584014000000740c1c01170010000e0035420080c140c2c0c02201c003203100c18071103d000f585a105134082c07070052214400b1400080a01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 92660899 1250 92659649 92659717
    0x40b030703090b0103150605031b10050408010203010f0608062707030209090a020306040b0d0b0f07090b0a02010509012f0c0703050a0f051c050a12060909080409110f 73
    0x2c0641201d80550f502d1606d1070341c03440d04507520b034030140c10310720042060305002030b880d1800f1240c94200c001921410f020700c1100c907080200103040040c1000007042c020802d0000354020f0107562138040c641440d05400411100c400b5184611664081ca040c80701c40d0204034107180310788207a0340c1c0e29089844170b038401c0d002481421085601300c1c2c90310f820000d1210650307018500c1840e090b101400301784034041c208803101260782801407060841101048a0503a68502079500417118204607000740c3e110300d040401c41c1c124900560060b91580c08000c4041004c2c040c0b0315441c03800010b800d002007114413008102e1078803910001c90003800071407442c2450340c0400503c0015900807023520101ea04d035090440b4010703041170303080c2c60b41e203c0c3ea546404055180d51444140044640d2254280400d9003400c4507050b0a142109081c1929aa00842d00400920500c0c080500c104038071559549010110400e4502c41000c102c0c41c5982480f000d03218143e82c10885510108240704800c2401069202c11440741e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 92662149 1250 92660899 92660903
    0x70206030a05180f1c09030803040809040f0609050612030c030919050909060f010e070c020d0501090203010c110f06090a150e1002040e06040b01050d1d0604050a0b0a0b0303040b03070309 82
    0x1003003100502c02403c0129685017003003041d40001c9140b5846490540311b2802034030004182c1c5000b0400a408250758a01601c8820001000843d13840d1071400e0400944107660000101959500c0a010f40b501c0d10414404075000600c024601f861889840b1a4803070265010310740c060403110290713031200302c85203241e4000380c04000d002403154103113100b40540d503040c212510300110329004d00120b090050302e60514410007040d5900703c40b120b00d40d03080c032090841e04401104c2564030f598941006030740070f00503583c8120b02d0742d0f01da4010348000b2284510b84000340d011603e00d40c104101380322041c2004104061210b40003400c0c680000442c00c101402400c424241c0d01641c050410aa0b03028422500184210781201e90180d9140e29030394204811540c03c2d0701c4060104008212080d94001260440000700131044200040c44a0824032035051450444040f2400d410640e0007204220b840c0c29560780003241c0c01002c01542c0c10b1180441d0f80d0340329600131101416030110014464038407170381284242903 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 92663399 1250 92662149 92662153
    0xb091008161b021009150c0c0504020d0906050405030c0d030b150f04180605041a03060f060d051c020d08040305030f1008010c0f020f0c060d020f09030303150102010c05070206030a0518 81
    0x2c0c200c44d1006140140b2070160801020704100c0d4034039020301c6000034400b5141c2116485504a240c007003000000d501c00103a5108403030300c5403404000b0602c0c52041d40c1c450b0740507002840d550005102d203282480801e140c0346081c10318040585005490f100040e24100107103020306546d0342c400050700040c5000710b60000450312151581e112407020b00343c000c002200d0003a54140700c0d0107000180c0e205200c10301107115800d94080000070300e4510380002010f81140014003051040806600e599040030540c1080c02c001ea0529030f44200300940c100b241900d043c400d45426842414140e034014542e100c0a440c041e2242201c10220700760302c131000300b50710081c51900020001c4280305080a0a400156481c00015020781040c0c0b015103031001c1040030815000916662030855902043c2c0002c0d0003811901e030480e02c06101c40d00c11a1803c00095008440881045e15982d100800090950303200b050032108000090044000686482003942d403c100001c202060f00c0d501c0d05480c8031901d015404c4280340e8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 92664649 1250 92663399 92663419
    0xb0f1b0c1002010b09070311090d06060b040e01050a0503010504030207031101030212040f020a0b1602151210030b0a0c050315041113030c0506070507031202030909010b091008161b02 80
    0x81d40e01580710031602003003500c3d4005903940c0e00d00242d08a07601c0d40d0001c07804003403c01c4640c07514034100550811061007000c3c00140e2549595006006406c0740d0407018880031b95100600292824441c510000c200031002402540741c1598000d444500310320004001c040c418007050040d070300a8040c2da4042040080c242c0c05440d047c01c01031541c44c446903050f405241079403404540c40d03c0380030488040404280d4000040c1d4819402c2c4007030710301940400105408240480d030301c0000c0b0410418018482090114281030039400e01380805d9070041c0c08261140d10740310843e0203030340e000010751340d00c115101240101e444c003103008a4003030080d0746441d907245000010617002032803845903c1810769000c0d1500003450380c0c0b510203000380b6204000c4013500c1941b11550410008214413401e48403288644140e0703041003a80b1002c00c2c400402a000580c00c00c07800b00c0d900f0300ba410030100b410020a01482d000c5070a0800032100d210000440c1c0c491400c002031140e840309440d52654600c0001c07607000e08480e402c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 92665899 1250 92664649 92664679
    0xf060b0405061c0632010216061103040f080d0f030209010c110d06111c0902090c07081207021c03090209040b0c0c0a06050f060603010b1c090f0510060b0f1b0c 70
    0x41820142060840a03100171180016510004001d80c000122001a032aa00e04008050749c41c031640c1580040103110401000c1100301c0c1d1003030501c001f40100d5009040c10054403102411001d280307540f800802d4414046003e6582c2d1041c050090140c2004a40100c240702401044c2d0798030400300085e00e07080c1000b06001d2105602c4000348510903011741c02c0341da00e03d00c071300c904815100c4501b8080d511040d02c50100303800079440e100070910a0303c205002440c202c14403049101d180d200b140c100c800360300b002d11681030590303503072181c919064854582004060b03030b03d41c001101803a0182000e4682444000010049408001212040513064080710340309886444d1040c043c1200301c5241c0f08094078000404c03da41881e0701500d040e1910b0000460070001c030040700ea09212127410503404d500d51103c4508000ca860800380f001c03070b54015005840300001500ea8081070700c0702e07540040840c090800441c034401400c001502d4030480340c000d038191524030b190611854440c00094a560181c50021910b40e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 92667149 1250 92665899 92665949
    0x20a051207020c0f03010c0210020f09101107090204061d040618060f0e06030d180b0304060f050609090a1709090c030109110703050313020d05100f060b0405061c06 72
    0x95000e01141e80305144400c190030f16003070ba0300e0244821f015901201c1004210071154024081d8480d101803400d041c884803800140c000708650150a020580231744804d40d09102c10300190f40a4004840c065140ca403070130f88010801c610318030b9500d12889813584181141c4e642d0360480401070208003c01c00300982c0c0200e01d040103052503c04d003444043c081d080003d6143c9440040d521910b0001c01520342924013150549441c003804101c0c900610011101140d040e01d0b91015501071401407000040004d9018484002c90341d028244510400140c001c01002030030001780c040f5019405044014140e1080c3d081d10054040c0003e11507101c0c15007810420101e0050006c5e504a504c104420301c803080607901c03150400d100c1c414001d00050020000962480044403484201600c0904491b8100d44c0703d0301e0f045d042000402015481c1512401194415441c80c040d000190001030b400070310b001d1402c0d00140040c4203a110840d003030303440c0b030040c42c24140540d4402001080220b440354079a05505407610 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 92668399 1250 92667149 92667163
    0x40609060b2107080c0c070e04150c0809030a1107050a06030b0108070f1b051f051506193002092d01030b0301091b030c05060a080a020a05120702 64
    0x21a8031448500c200040d581c0100e5000340c020307071a00c045035161078600c0c4542c6d0303100d58868035892241a80016107802d103012181e11403409842218080e603400c0d42c5402c195034604c00f884003005844800e01a1205c0040101c4614540c281044401008a4100103007062181d0f031115501003184400040e41542507084010188001d0381c0d00b40c0c5070b039140c00055483e40c1d000d504620006841070881e80b20074051003100c125842c020001c03100c40e11b58290311420758540103c0701e11107071a04c600510072000424111850800030403039200341007119481181061950039207104080186108640e40000d81c1d524100a040c00782d040500321101d68100b440340030354000600c00c0e01400c1c0030300705231200726141003003d006444180c4402c1c030440d13190401140500007181d95158155a1401c10100250201c00390200e00c1010701c000c80c00452450034441c000ba039030303a84914040c52040240c44400c690125255521043c120001610754a12240c00c03902805800e20320202200340e070007400700342a00001c0700 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 92669649 1250 92668399 92668417
    0x108210c0f0105090a0605010602030310050607020111011815060308030604020304060b060703180b03040203030a030509011e0f06090b01051914030910060602010615080a020f0a05030708090a0b15040609060b 91
    0x1d004c00e0740d031511708074be8034030003100e031400b820440030420b101070710b855001803160f20700500d80040140708001ca0344c2e0031103c4200003210315081158060007045032482c080d000400707851800f0012a482c0d62580c51240c80000c1c540c0e441240c1c00000141046807075802140f01010151480751600618036024060000e680c0ca600e10682c5c81d007000040c0f61742524212445160702401541c01c0403602901540a400d003d0700c100c1995494a000c0c078030b91080d89180b0b4640c88400749011a94204031484034007100d0094001c04500f41c108490b882d4203903046822103840d48000001414841102141141c400306612244c2e000d45c0000000e02c01c00b1580001e221a004144d00010000345603129816802c8070303030602c42c90a102d550030f132183c20240e000e500302642c8a080f540d000340c40d14090381d090000b80d510100304640881c9012003070003803a681c01240c590388244c592000381035a182589800d288417400411600341003106100142c43c135142e0303810a5008084202d400d00ca003e4440103c1c0c030140d0031600c68 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 92670899 1250 92669649 92669651
    0xe0703080334030213080129040507050412050c040c0f02011803020726070b0415030515090c0702040606031b14030106050a09030c03050309090108210c0f0105090a06 73
    0xca001d924610314901ca4100501600c0201c103000b001e070058029411521651513090500c1c10005282c1c10280a9140c00d04901c2d12a0981900361410100b84603801c4c961241c0554076150410034400d400c10200d038103452206800301e034082020310300715103468072103070b501a0028249024203050a401280307003c1c900c1000d030024800b2100c140f0407200c0100c04a1405001a8410802006504900ca00700f112803164000c550b40c149510020040c40e100d0198800301c1c0340070700050100020a0b900049c01448546480c081c045170034283e403003542c11811b000f05a4440d022031000300e4003100c0c04c40e04aaa215602600034000d0302d81c6c4000103402420300000d000841d5100f45000344200e4031440c802000368542030f400904590a0200440d92500048914000e21031016000700100b4841442040207600c6000116605e04444051224040060b44100c1403640640ca883c8403039007059013044030040703001c1c13401519801d03c0385040e0314010902007204032552a0106000f0282800308022407400e0041070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 92672149 1250 92670899 92670931
    0x7060b0411070f02060307091e080d020f0a03050307030915050702070501020a0305030414070b030109020a201911061209011503020d030804031418011404050a0306020903010e07030803 81
    0xd902c0c410440001c010406035035296005180000c0074641001da14074100001e00d03280c104501e0304102014400d19007560484042100100400400f113090b80580702a00164006041f896a182d44501c0001c090000110004612030f10a034420054590007005600c000c440905040000703010035140540140264200801c0c29400002c00600d07990340b550300c1516582d1341d0b840304180004040440c81d21805a5440001c0b041c8402020714040c0000400040e03498602940282218000f4a2a06801ca030040c103000509140030860108088101020003031450661420082850090121543c02640843d030036605400c00a400f40c4181c1c0184000c003e0681100da4403640440c82d403100952001a4020000c0028459044150020301c60b00b020745007260361040e000c040d03811503210b5041c0c030342d220411201190b07409100e9040e0010400355a43c0f40509281c02705908034214007020300030b590005100740c81910250b1001802d0741c1d489041d02c00c8546c980c90650320550080d54940030f4954a04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 92673399 1250 92672149 92672171
    0x7030203120114012c120109020619090e0c04090f0f060b09011709030405100512010611060f09120901020c03030c010b091008030712030f240603060e1803070807060b04 74
    0x90441070070001091003c81040d00520104001c6d604440048039082d500d40014200503100c2d00046c01e008141c000f242318400d0a40700004220410f20303071102501110110a004258061404590540d8001b0202140512401c660311004d8207100e5015040b2038603002c6d00103600a000005400800c0c0242d95070152403d00445006504009130b5060656030010001004280703810714190b0085881420f20900f0903019051410140c42c090340048041112003160000050f428402c0c943d00068000d0b440546040a401d20b1381c0e2280807240075511840d0018845004c2da008204182c110b65008080b2035079540403407111406021845081c03800342250f64042025031b01d038414082e05880003400151300b40181078503051190803120080c5000d0654422601c8040922800781c82118440030340000301c0e03500d0041a51140d031085038040d2080500d000010310050210306041ca0300250030110741da840201e9100441e045102e500002480c0301000030705507041000580000611b000200c0e800c000c484080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 92674649 1250 92673399 92673437
    0xa1a0907050402040f0605071e0b18060906011a040e010b0909130b0a0522050715020706020a0803060a1707050f011d0d110a0605090913030507080703020312011401 72
    0x5000340350032400004421b00c5000d2284000d0b04105004950790103642d49401c10f101e040400e8140141c906c00185000c1210b90000c0f49c8400840c116000028011171030f11070a507544807c4103000300504002111003462508011100751800740022161030666540d444400b001c46903c001c2c002400741800308001503080048841d00406507810204006941d515410504000c04004040a1490320907012441c0800603400d4a0050a403140004008140c20600d010204d803220b02552811035004041c1071215641c04185078640f1640101407903200d80b601c00000b020316a903504203c2081c400c00204030105000040e6040403914155040c101000c40b51004440c401c0ca0003811208103404002205030070300b0107424040c80d240c014800a000d00c200031b400a0718208655009000103140030809801500d09004103a0f001a1a0b801400096142c1d1360080c00d5405910405080c13080d020411009060081c812260603038030b040e100001d02e60716800f408280d001d80c51006400540c035810044072403150 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 92675899 1250 92674649 92674657
    0x204150801170606030a1104090f0b040605010f050a14030a020301090c03030e04020a0906050903011e06060306050d050a020118030507170d0305071d060903030403060209100c02090a0b030a1a0907050402 89
    0x8094040d14035079035140c80d0305007c510413000550700240d88000490100d04402d1080d81414404d4081c450b41d81400c1c2001c0c4150340c0c043e04002d84081540301d00300300c240d40b400485009c4aa0000d80c46d10350051100010703040c040e0000b0041e4165080c0f81031841044115200c640075280f09844004200c86a141480101d000c1e889413200440c011a2040c01411300840c05040751400040010822140300c0111910241108001480303041d1150030901c0010341501031540030300003d69120803d0103198a43d1540c494101702d0103814010000c50603009110545000009035820030700710366000f9500d141051000700010030200c5580074510b14070040700e2080c082e4501a083da603940c140f4001a01c2a041c40b9199848569a0312040c10000322501d5142480030f400294000e410051712001c1309400d0128081041c00d8050800071004103002c01aa500102650090301050300000c00c11840c0c000f11345014034145019003e2240084044007204030080728501c503207510b005607a0382075030390002d010503401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 92677149 1250 92675899 92675911
    0xf0601020a060902131b0f050f0a0503100b03040f02090703020c0705060d0e01050c07020301140c03070c0809060c1f140415110d02040302040b0901050105190302041508011706 77
    0x60344001c070120351035800419200e0300007003402c80f2490540046000300d07201a03000c074507081c08641c0c00d808100d811900e1340050007241e042c114980001c00307a0341c12079885007140c55000d100000c0042004918035240710742c06002213440380da50300d0509040525a0280c01e034000c0b40700d0310a0b04d0004012500ca4003d94560080e500004d115140c28a8100100c603004000480000c50352044601d00a0031709005450107920640ea02725515606070040c1400d4544041345040101c50b00030602c044462a074044a0b44000305242840140c2401d20700200390780f26000c0c01d25072103803012420944a020100b440500d680394419101d854400c0340c0314020030b641c1c02c008001c07003801181000401258001080460005001900003103400150944010982182c90f003034000f2940401e0600c01c5003850300c22405001021182c00c540c1c0e6142c40300007046031040d00c007140d0414201c504006d1406009406980140030b02c1102182440c84209005110358424840d40c10702014400c0680c0d0240008510240214 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 92678399 1250 92677149 92677153
    0x15030b0712020903070f030507080d1707050910080f010806010803041e05090f04060e1b040f0605040515031b100503130803010306060e1803090409020d15060e0f060102 74
    0x59641402541e0000d648500341c90025000c1111042a50f014080d003c0030700401c0d136038401e1050440c28030500c4c0440b5904000b0307440d484422100c40c4c0980000786203150501242c01a9265541c1e100d0445150142e002c6c02a00810760f885900942134000c0130f05803144548202a0286a0382c4020b81c1d556401e084c03081c6030042d001044240030180c221464844451600258602c0c0c00c0e0340c500c04100d00d4002103405004101184080c001000214020001e01406410041081a2490049500f2192a00c0c000d0784503e036590101915610190031000c010000108200035a24204c45280109400d0703900580c400d002d08a25180d250300e031001286a03015000d84446058400441b080e51b4540c070141003550000d1501300c4100c0042c4502000394081e5100e424085840da1414050484405004d0901c2c07600414940c810065400c0020554a0041c1c04940100d514070460022030741c01449000d0140003044842031422802d00345410030000c4818600f1a1809a9180481c1809003003041d07500900503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 92679649 1250 92678399 92678401
    0xc02070b090d030c0203061314070602060105301606030504080409020702060c010507121a01080a050c1309060501020f06041a0711010510090501050a0501050706020c0f030a09030615030b 82
    0x242482c659030141d01d4400d040140d08242c0503000a4a010011035122001200c04c880380b40800039644021203416400c80c00501d4018100301300a0b49561050049130700944ca500503400410281d0303c108040384c0c42c1c44813074010b80019140310305c2d02d48002059541c260303043c0e004000384a922a2203000e00c42d6812801071030a240c280003804000e176001082c242c0e4800018418034608100c00c0c071805000c0c1c18251101c1101c110030a2458055400409a4040c41103409810903100e0340c09c8501a64015102880010180d540f0340350040d081c02910b00c8001444205800410305c20001d6110303c041c0c94090f0201c03022040146842c07030707035130074219002044d864401070034500c800d00140c65190481280d0038030746014000400011700b1500c0844a1090180008804105481640c440c050140c01c050781e0711a0a2824500003070464814050010705940d8009034074170b5100d50030f200070b0340820500d90650380e4910060034024070740803542c0419201c141c034060090414000c0000b4140841c0e40c4000341e0031075 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 92680899 1250 92679649 92679667
    0x1d0a1103070b03011509031a100902030408070201030906021b070503010501080f0d0c03030612080918090a0b041112100606260717010f0603180201080609190f0f0c02070b 75
    0xc243c0c50404071020300a030000702000040e017030542010206120308c45001580303400d003101e032408821680114001803041007403001007030700242203074021502804d02242400c128034000300248a051481000200c140080201c02d14000c500b000484a08a0091040b43d8842411589400c41d4041c61700055100042c2d00d13000c280a0030881e1100c0707000741800544641c0e02d061b40c0c5081646030b4402c442c2c2d40e070300080b99001450440b0000014038500740180c403107841c1141e40e0681d0b501031300780094107918048000504021414221a6200b0300241503140c038854180322641d5900d040c41c40b6003840790704058001c03c24902c141510a28558502070120140000002082000d840a0180e0042151a91084010302d46400881f4000c01c584642d0480c0e0038a00400141260710501c080c0c60100ca0920f2a100541c0e03000c040590000002c40304003044d51110002c100f24600000c0740c41e5640b9061090500d01d044555003c0b08440c48c1c244000e00804409201c02c076200d83c235500625002400521444003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 92682149 1250 92680899 92680919
    0x50f0910120312051006270501110a0c03050309030601080a0c06080702010f060b0901030c05040b1209071206020304030822032a0c0303030b011b02040b041d0a1103070b0301 76
    0x1c105400b07030500002400f030035010b210075607100301d59a000840d4082010010396034000d03c03680040d03541c401d0404000300d035800811101d0b90140300301410042c5e02e015003c80604184280724002e544685492081562031501a440750054000307039100e4025140001107844000c9645481030f0b0340714400022882c00d006003584c00c200094000c50443d9030701e206107481000540b0a0030003903c2c3d41017882e9296611180010b0642c5c0e480d0490b0b000708201404200722521012054030700c6006001e41d003144c0c039031301d500805107001c000d45c0c80403116081040240080c0180c960003103009602a43c1c51100c580d0360001c00c281d18030b0303451170f407400c410440307a14850110b88aa0901c0029080c003681c60621000c8a50b032101000d1642242078031003800300303507003002015014400c40820003000e003072202101c89020403d18603580003e0000c0e00640d101c6420320890380d02c542c031141c41c1204a4014600c1164840d81c0541e0b1000005811510100210300352842842c000910031b00715610f0304903092035030303091010501e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 92683399 1250 92682149 92682179
    0x4110a0b120402011b050a0b060a0906050303030c0c0f0607050301081e060f0a1e0204090b030604050a0303050402060f16030e01020f0721080c1b1503010605070213020a09050f0910 79
    0x18008000d00e031703054000070014030a0703d80345406448140b00d07504007541000070440007a804180e60034500081044a40c60101c10f5a62041e080c04000d51508800c482c40c50520802e40703040c1440c3e010352800c00010035040b0f405103050320191022a0048a0354515212f44100380322041c40c0150301080000c3c2d00652014001e80d0302040a82d80480c1c03400f2901051512040ca5425000f4603503004102840003401903c600940f0103003c5000b804682080c1c0c5446480e00076192000d030130542c1b00c800080954135218104c4842c10404040c1c1e99641112006850406040c54000c03000900005514107080d880010440260007000001e0968a0316029140c000604806040d0884a6000384424049803800d07018010119012b8083c0070008016000b036030000034072102040c07244240d07080c2a002d041c20601940d0550303001e42002cad503580c2500e0001496013520345080c0710321a400080c00003842c940c400109000c42e0f40a4a03101201d6081d20300b04402141704584144440d6842903040140b9418560b0342c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 92684649 1250 92683399 92683427
    0x13170c15090a08100207140c011403040501060f060306050301050a060e060f010c020d03020102031e0c070b07020a02030a14010f05040209060d15020304030201050417071101050c010e0604110a0b12040201 89
    0x2042c0143d4458190b03080c900b8004185001c0c1740d002c5000820300c1901d0a560450284810103001100407500019010400311003160140700c4022000408000c800d42c020005413905030746036011959541c000130040d00403030140324000c1d428200440c0d501010742c0244070680348130a0300030b04140e42e40c0d003e0205000d03aa01201c0d04022181c80745101503102d80750581c81060207039001603902e16204483c0c2003859070350301000440760800c00c02c0000010700c0c3c07825581001da0080c400000f603266614120300c0d08a1862000c2d6042c09240c0b1a5010414054040c1107079a006034000e001c5a46042000c0003214011540039401015000c0042c0444c5070040c1b08034103403482110390901c4502500c50950480e00100c1c1c00b100942e5549050006105107006405940e280d9000c256181c594190785084120b03080d5038501e41440004105404041c000b900304500c1103210104a0b541880d190908041000c0c441012034010750486401283c0e003190002100c3ea40240f140c60f000c400d07152640110b41003402c101d11 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 92685899 1250 92684649 92684659
    0x14030102041a03010503070501020d0f0509040b03060a09060e030a0c0210020102070b0a02040503060c030613111903020d060801020a050301030f021306062001060617040c030813170c1509 82
    0x1012460a12100c051088003803803682d0720380c0720742c1400141880c1c92826001203041d5400011040140c41c1d20000b8022501da940c0740180d182e0030720102040203400c000418075410b02030801040818801c1f54072040d2280d024040038003039840001e03030864591061143c1304001480b01250140941050401040c4500c064070006181560b40d8a80005500d0241c0d10581040d0300000c040100f817408000791604403000c000103916500702400000d114600020102802c1c5498000c2500c03145840f4003642e080c040c551844441102407440e006000750701c241d441944051420401240e49441403080d28000e031141e40381c06245900b17684031220080c640050499000d9188600049040142d0103800e00601a540350348210042000c00c2c543c554060310f85244031603240c01c80802100b544800041c800c8110410104115107540c100048020b900d0380010300309a400090a035400b10f00340c004041200d040c20000f001e68240c2106164603050440d040560226881175124000d0901d000148101100104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 92687149 1250 92685899 92685907
    0x30c1f081e0408040306060f06051902070b0c01021b211c060b070b070c1e031707170c030124030b0d0501150506090603040b18190c06020c01020714030102 68
    0x101490708010448040302d08030710120f0200100400703400380001038180d14540d0b9a81c503003080c1005050340207d0003015403690596620f00ba9090003484410090102419072a80c0d6280d055015400307540f0109101d460b10100035840b103540c6801050344444040c00d5245071500e6105681e00d0110382c0c101c0100714500c1000015114480003036841010700800c00b00c81f4041d259141401c0c01e800c6600010181c90901c19108222000207148841c0b68804030151000f040b2040e40a0400319590240c98100b1005003152030280301910344c00464107001c1240d45140145a9696854019030a000c00e1041c4d00c62121007046440c4c017140307000070002c400c9083c1c0c98006004441c02c00000c0c002c1c0220841070705c1995441d00749420f40480c03143c01101400d0140c424505e040c40d00c0005c9041848000c00180c115442c280209100c1c039444e09000c0c02402d0004101c40c030710051910641c1590030b840804550210300d14900040e002c1c000300e0442c0c034140e0140c0240c09000e1900c100ca21040714502d00184d41950300308 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 92688399 1250 92687149 92687191
    0x1d0103050a082a0a030909020a170702030d02030a0b0907020a030203090f010c06020703030527190206040503030415030c0c020319260c10020f071104090b04060b030c1f08 75
    0x2510390b0080080f102c000b404198071a08014003140c410341c000c1412640100025400ca40d0001501c08015440d0074905e0660740d10201c01300c0c00c50090781102d4407500d000000344a820b400c0c58110401080c002c843c51150741d122200160f0340c1c0c142e00c610040141c2c03c18410401035281c205c01c0d006000038103040060001150707681d40e900700c1e80403442c210046070f95070082c00f800041d411415803840900044c1600d001e100e0a105a070350302c04502240140c0b0b030341d00b4a0b03a002c64a941c02560014031001e4212a00d8540b03c46400c40c9140e4418001c0d07000174031302011000b06611400d601a03000d42c001d000b80c1800c01400038940c20303400c212101614604166401034408290210f00e0030440140040401c0d01d960100d071080d0308200703110b084032885070b0047c003110000d01c400704222610958040307070040610041101040150400d188090f14211164042100380019030300320200d000c074100c080e92880c10072142045106c0042101081b030303406c50396081211040c0103901d440e0b001207051032410b9880b100c070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 92689649 1250 92688399 92688457
    0x150304061b0305040b090c060403060518010921030902060706020d1104080a05070506030709060807020a0b0106080a0b030a0309050409061b0203090102070801060e0411011106010e011d0103050a08 86
    0x500c8400010341d0f16810070042c009031100c3d00d80c2080c42200940f41034074407000010380d03038052030101402072503030380c0701090f000d13294440b1422031000784000038070200e801414030b20b00104004d50881c522048041c6040c02e034610901c80c02c00c0c1e455006204504040083d02c0700402908a07600c0c11503007603611180f40040c0443d00b00580000c1c1901c20060640d0310441c038000307007000e00d19481140540d04c144140400341d5004115a0250341c00f030702d0040000eaa40803400c03860014580009441070689100100e40b140d40300055900c55605200144554070001c003d056035424255409000602101c809001302c0c602604444c0300c030b0780030381d00102c0d16003081c00d43c000301402e05000c0e00d0056440001d42d0a81560103005100003070030540020820546030212281d1030280c0100f005103245c050284203100c0b80e0103800c10b08040540e83d0221203007036842c0c245000b07000d5428095028008000503410640d8044412002d050ba170f440307006490101040d0b1b031074032200d4001c903075070843ca00c0400780507000901c14 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 92690899 1250 92689649 92689691
    0xd0b0405160f080703060209040917040501021e0d0311040317130b0702010c03050912030c010504020108100305120d0615020a05010b0d0c050d080c0312070f080c1c0e010f02090901050a0515030406 86
    0x704405a633941d450320001a29000f00c44d4203c46411b10310408113100c554000c100c0d010a4800303800d0100300e2003035244080c0194482c0c0c1c1c00c000c103925040c44002d12002c0219000d400311039844089901c10544843c0c440c510b45c01503460003400550740c10344540003e4810740241034100e0000d80f43d0043d81c00c809008030b0070340c0c1001c240d2482d10ba5441c4100700a42d030740303c0b0041c0d40141410a628903044d045441d540d4684028603201d40800000044a421981b62a4016001004000004506180880c0000b915048000000e8480d07600b82500301d94540351032a1181a0541d12040b1451070514040c00d0004100100e2001c0c0c8800c03400f48904504507500f40010500540d0001d1040c07124a40501c01800044004030103004009003201080301102c0d101c411101e44803e581d10009100c546803043c00c002d80070003e802c541d25424a070503803440b0106a0042d0030700400448406440740e03210418060301c02858030855900c6402d0010000d4241840310003560414000d10700401c0f5a88003294100384a50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 92692149 1250 92690899 92690933
    0x5060603090a121b030302120601080c041a0f0a0804050c030718050a02040801150e09070302060f030405250503010f0b030d0c03030b030d0509100804031d0d0b0405160f0807030602090409 82
    0x180010303072012361668400310316500c800c0909041d240e07410301501c0045070b802075014044040703001050540d04014120240d030f030323028841840c1c0395032400c0d000b00003440107006540403a014422260800b0f860300e400702e81c050560b9440c0c10002442c021310801c54010b483c0282918030f90359801c00c004038180c8420b008806000b410807052500c00c3d0b160101c0c0c04080d000092800c410781d00296401c8c0010383d9100c0442e103420100b4098241c40362101e00b0001c4c2450343c4c0d5440b01c81c05100040720740350300c40f0400600008540b4214001c020340d000081200064642c44044a54144c100c002c1600301c0718040d043c903a20041c060714000481881440210345401e090b4010140840c0d40402c02c03980c145403480d02060b00c02203e00d000c1416041c1968050114804800c511211061409a0f000c2c20340303031484180d162540200541c02541840d09141d85c03a000c0d00b80155000341e2540d10b0200700070304c01014220031107503600d009012076495030b224440203401204001d42e20030346aa40b200c011804003c1c4a0150003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 92693399 1250 92692149 92692151
    0xb060f0a0e030615010206040602030a021603030e010e010b030606100c06060b070213090c050618090109020304050601121101030515060a030b010816080f040201030b0d0b06030105060603090a121b0303 88
    0x240c81682018940710f4000c01c000b80c85500c0000b0705200366404030b000c603003081d40030320090307160380b034006850010b801900d0380c85210b0b0149424034014158142c000c1c80d041c440031002044240b4880218a0030380750400d4249070980d2140e401b080c61400c14104044070008145040000340c05e160f5030310420703580c9980c425140c00001260b03001c158036003000018950610a0010450b04200da0b40e5000410340c540f207118420340c0007080248013481011105141d5541c01041190701e1344c3c43e0b041000007900203460507960b5101e00720010a0f0010f00816280516400500c11503224003100c00450140800410518290707400c0002c1da0f8650320f490014003210500f6480104005010000040846800400903060b6152560030000d0860700910b8564210b01d074010b6a00065446000580140c0031100c0b00b9034100010010709018000f40c101841e004040450007804152035500400149000c191406000c941200304900001900035004020720203d03420913110400780d41c0f1580c101c4c403180d00030035070100e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 92694649 1250 92693399 92693417
    0x30b090c06220608071d2b06150602100906020910020c0103050f06010f030213050d08190305010302130f0b030708030d0f060308160302150412020105090616030b060f0a 74
    0x20000500c44090201481c16411342c0c03400d050010007048800900103003001040030400c00340d0721809405240b40058000d04240c0d0307084540c202c017155402c040e055071500e14116240803190b501b060610100c0718030b1b90040500f01e02901900340100350b0320720b040313521a80c00c2001560301e480e07441c940c00c0d001515402400110f2141030000d42600c0008141c907018101100801186a800480700280b00505190050b1180e01005440c0914440c03031b00b00c50740c400c882071402010040c50400904d0311540840c0e60f02050b9151400039410ba0b0030a010095203ca5500040102c280c41503104111410f240b21020890001c00c1021a00700703d4250050741c2960030004200032040e0840c0541410512030380c100300f180c00d2440d2210441030081c0c070943d01490a03207003d0b0b5814540300304810070080c20011a5020f10742068640820030058802d10200075500308000101410008030f1075502c41d14002c40c1c540b51504001e50102c2c010f00e110000140d218000f40007500d00120050050032401d074040d140e070303022 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 92695899 1250 92694649 92694697
    0xb100302041a040b010201090302070618090608011d030c06040305030606070c0902090316050306010b0a12180b01060f1707110102030f0a140106050403120302090301150504180507030b090c06 84
    0x541300d140c0c0a1074156810000000002940054948215442840c0104502c00f4100800b400407142e81d01100b0110b003071603000f103040c4106500c550300c078107512840d00d411580005815038a0b80280d250740682500b18400040200c3e005100070b6074043c0000380810314000543ea50350160b40d0942d000a0b44490380411181b94504041240c007449030781c3c1501078030401d490070000075503c20050154100203640070a1481040f401941e85503644250000f041c042c010040740030924020780f0f8441600d035084084000684107006001c0c1c41031840003550b0b0440300c1d003020b20240280340d03c003800790001c101d20b10001400d208820b1006e54003071800940804000d09240200d502912104c00d040610300050800422943d0303000400c50b021250321007150304803840c0401046e0300902503800f1464055085c00391000702800000d40042c140c40e0304941c00c000112440054500c2c800340c0c41401411503100c4a41170011400c4002c142d40e1000f000c10864101c40c0500004c02c0ca50b400103107505000207003a4159501c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 92697149 1250 92695899 92695901
    0xd030902040b0603090c120c0915190b13060e030a140325020f030f060406150506040e090f06070f0809031b0708010c1d090415060609050910050d0b100302041a04 71
    0x291005820002304a002510800156510409003a005412110044158a076100c4112000700c90790103980c104003031a07072180c214546030300c445050a0301e0f20202001089142c0180b5a42c44841c0010f0014821040c13107035184661400c100e0041041e500c810300181c1010815202035010460210032242e215210f44d02c140401d200c8c610301424400e0300f03c000307090f10030940024002d60140d001040800c500e14041411580266203800c85900060001408031312186900582da00800c20042214101c21040540070786694054400d900002c0358241d242c5a0144074040302a000501c14050340d2400480303400b164100100c1d107801c244107070400c1504012408007803007880c0401200d03080c00121240303042007032241c030031200e1002d622400d04000410240140000d00c5034860340500b800308500c544400d8090240010392054034810200c107400903a2000541d00da03002162400b4041481c02220340d60350f505d4108008048038076185203910008056540d50250410f08200b050900c5144402e902c103003c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 92698399 1250 92697149 92697169
    0x503040906060306090c1b1a010b0c190b0105190807090605030d021506040207290603070b09090a0216051f0c1701030818040f050106080105090103050d030902040b0603090c 76
    0xc5c9000e491b02a400201a812001d041d4200c440c034110a0007400031440d1590a42210145901c3c0c0c4061000010440da085040104040076069080f41c0c041c442e650000140a1000240105014001c200403c01410090780d40c405151200d10000800b50f01d4901040c6040c8081d03000381030003074961a0800040c1002d104401c0d80a41502c054030b0400d1011204505100d17028154900496002402005119000110400c441c0071110207035100b150081510708088403d9900c03d2090155840025402c01c1e02c2085541841028100b14080d5540540600c0250010540045107444000915000407000e0019540600e407004219100c00c40c018102421030304507407105001d0201d0344074001d6403030052136450340c116507219040990b40c2810a040d550104012891180c000d8146056a401035059070401c40c103032511951070040d941e036500c0c10400118403e100141c15074110080c0d610a29100707811001e001400540049541c070201e001007a510307442164041029000740c1c2c504642031408040316 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 92699649 1250 92698399 92698409
    0x120e0d24061a0304020613080307030905040c0f020c0d0c0314010203041a0402030a1103280203060705070b1f030f05010b030715020d200102030705031e0709140d0503040906060306 79
    0x28038a02c15140280360103900c40900041d1040c031001c02c900003603010041d144005440c1c8030081d0380d1911200d1070080c003603010394050a07211701c0c213252b004402544124140d00b40c4d00c825038010004410000c3c103000e6043c600000980700e1124444020000c03039400c07582c00203140d40304000141d80740b0345030501190240310303100c3c03002003440788030207120259500052021540b50010f14515840303203d600001e29105c440036852501e01e83c0081102c03d400c0c4038619044019000340c00ba20741c01c0d5190345007290326104003500145104013110101c1c0984a0b070040d0f000515607160091120307a6120384038428900207000040f6003682d10341c00c0103000c0e07044c00c2c0080002040c400d424941d05500058002e91900046190101008070340740f4945140d0340101c105144250702a002107659041c95480205154000c60b554001254804010420b0760391407a607072482041070703940b03040c000c034148190480c4100e00c0b4648154040b40060030742012400900080c002400341e00c0e00003558516118016065401c144c0c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 92700899 1250 92699649 92699669
    0x1002121005010c23070e0a060501090902040302220b04110c011a06030c0a05071208060102060112050309120307020a0f050a0605180103020a091e050405060904120e0d2406 75
    0x28030006081844c0c849136089490084810118801e40283d103042c501d64021904064646c00b4441441030583c815810b46900382e0364000c005403280e6030389060b8816803000079008034840c2c10391404080d141802d541d403d9400f11001c580704103030000080580d001441d0264840f5030024030811030110034400c47e403031346011031080801141c082001440c9400010100c0341d858200007500300409100305c0031a01e0303296101c100301d5106e0144071701c001c082d06011a1402d0251040500206041d4021442d601ca0b04c0c0e40700000710300c0d1501003c01c5c001e9005070a07414404a20062106500594822502a010301b00d074011281c1a2413400b0100505c0301c00300da011005004007044103140760000c01050707806001e828240969a03c102400859000c4040d07480703c000400e10030801ba1400c03010000400032181c04079000c0c4032580300c960030070444210a41e401003002d1036a400c0030181d940103400ea005505001043c5450380034203500c40707001c109401e0b8007031842045810280558010940300364000350140841c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 92702149 1250 92700899 92700917
    0x303060509060405070f031508030d050f0106020f03040311040908030f0a0506060703020601150903050d030203070306050109050f10050f040b03010e07020303010501020a1b03061b0f0503130212100212100501 91
    0x241c09408401e844e2000c0584071400d8011488003e23000d140104801000c482d40c441c0c1140030200206015182817000311881000010344502c002032904252b41c0c03400155241a01c0e60765034642d0020000b40031900079440315090400b0a1642c0041c502c40c500404529406241c1000340f4070131a02c00801c110320035101030060002103640055107a0655541d802040200b1812200948840d0072543c0f0041062040c004468800c66054020314044d4504d51400c1c00b125441d1001925a00d51502a00307400403110181c8007040d26015070301034a4a903441c02c1c4180380c204c041003034158950050f00300c0d0300000000001084a0758000c690654000c0389032015600315418840002c0d00e802e40954003a000d41a0289115681003a01c00750000856010700c08000b9044e2524243c0c0074481c80801220200e01c8482130321401a01a0f02100e2003101d192059940651259080140c0b42e041c11170060220300c2010700316000d20b4200d03c01401e01d006050032004d030918040007941243e80061b0442410482d0405c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 92703399 1250 92702149 92702161
    0x90c05060a0c06090204090f030c0303110a120507090f06090812030112140c04151d01290403150915060303090e1e1602210702010507150203040303060509060405 71
    0x5240065030241012a41301c00c00c0c000a00540080072000c5d0030a0703030100440042503001300407030003003600c00c0d00d0502c000c01000c04e40c00c5050060380d2805010512250120850341d0551380302e642d011601d800c2000f250f6480e01d41032a40c1140740d4000d0b001088041c0800c0c010461300b00f0549440b0603485040600d9581864121000c1940030303000100840e52038044035025410a2102c1820032501400030000c0c40c802035040d001075a80d40c81508641980100e0903113907903414104041c1a40ca86200d80503420701c0ca20500d2404007619200302e481040180404400201000349141d008030b5100000f00b11401a410100f8003000d00d20f40c0c00400314540070742080000d03002000f01c07040355400c0c21290403665071880c005c01f6842403560081014003c0004000d064100d8410f042c1d00c200302a802c4a0114001089105588019140d40107040c0d034240007034001507100318000c01c1e0b4a031141038400d19813103113902d20100341d030000c0d5022400b1940354803050000d810142c8590354000300480d400e0099003000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 92704649 1250 92703399 92703407
    0x20304080706110d0e06010306050609040203060f070e040207060c1412070e0f040203040302010603050d050c120a03060b030106080712020a0e040b040b060a030e0d0206013b0a090c05060a 82
    0x140303000382007548491681c0341c14110202512007849412000341700e600a05000151184824001118920703d402e001c80e02905100b91510700c10350b405401461036446080c940c007805034005001b08108040400d010086490307074005448010f105c0c8401141d07a000b40c150240c0980540b40305c80700050000c0c4003005a1420891000d900000c0d5800d049038103035280b50214200b00d4024200d540c00500000600040642c1580000e007102c2c012000d4801043d4200c100701e58a00c500e42c0786031200d0f07110715207100b40e4000b100010883c0030458180041c0f010354800c00b000b45500241e00550220700343d0b03810050000e8015140784403c00c841e00c42140b1302552880040e0982412820706401955180240c0c507141d122640001c0119000900c0c1c070391030b041030303890040240c803c041d81181e050158840052050740001030751410395205032081d20b0a000ca0800ca50aa05031810743e900c0c004040703e5541c80721106003610107014455000300428243e610342012500180540c1c07106020303107000c100c1c2c01012588 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 92705899 1250 92704649 92704657
    0x50601150f0f141215040605060d020d0b04090b160503040b0c070203070f0909020f0603042402090918160e0a0f150e0609090c1503222402030408 64
    0xe2030038680c441c80c052080840300d00c03e626040c0c0c0c841000014200b240d940b04204054460790780c10b424a4038120003401408152910f43c49034a80204082c801f1003103129a0750050300000c3c0b0000000600c0c0318148000600395910070304c040e1a410005402e0060111007481c2c0c4101c9040305c0d090081c07a504081c1c0c0c6090440c48010140c841c5d680e00810004119582400350b00020031880001c483c5964458048200038418260106c1c42542900703080300140c1049000e403031156400208090401c026880b00e0203105c5410b488900b0300b60360801c00300c4107079640e032003120b80581c0311860b15440c040092000b12346015016050a07000f5542003404110117417001c5212076000740c0802011903010040100c44020740700b20000032500004000d0046007000f11098590320643d002c50748080251290840a512002c8010740c0c0f1341c120300003403800c80080c10044001d64011001c011003210114a1600080c44010b20000c2103407a180c1000c0e003950360111002c5002e4a182441c41d04601c2c2d4142030b9552001442 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 92707149 1250 92705899 92705927
    0x513050d140111030106031a0306010b030601110d08060112021204080f0c0712111807030203100e09010c1e020709091106070f03081e0402130609090b010305060115 72
    0xc140d90800041011108408012106400007884510f400b00c18100643e0400d010300750019180101d4518181110071426003455030160240c040340c0d00b800c07445282940018507481c18490314601c1c101c1c4025041001c0d060b00b0619984110050030039800045c440e06160100000c160300501414502220361200c4c150415880702c2800d641c1c0c0038005513000207015035189915a80a05035001401184401c4103c1440e8400c0303041c1340c0408442c1c0c08100c028501c03e200003d00420a00c002051103010f6802540c00c180680303050000f541c1c0d50350b18115008070849066900740d4444019441c0c3c80d801a244942c0450341c1324000900c1041a2002580e070b60b801d20501d03d20503150300300142800241e00345803110f00d4020b440342c0d54803641d6043c440b40701c40f0071a00031400510b9120004202483c201701c600f440f1501000001c031240c503203800f04485480d0350500c8950040e230303843c0d0010707200d0000d01c030703690030140724140d00070b0698910b04105040c804161702800b00d0690741c03504540c925501c0142c80380c00c0c80c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 92708399 1250 92707149 92707159
    0x906030606010819150f060c0c060f030b1203120603030a020d0e0414040309082107020103020a0e03010501090e120412140a0507060804060b03010b010906030902010e09040f02030d051305 82
    0x607581da948000fa1595800e04c07040c1d042d14211700d0b1104045048113000c140c901821414544690381c0500301c4290000c440043c10210080c582480b4241c400c1c8440d40f07484d8107628010420100b0800040d800d0f404064100750194000224408800c4c00120050b03030002003180994103056a51001030345a0350140c0f651010081c2100c40c8111580c0c5660095043c242c4a40d4007080b940391916000d0402d05641c0030342c841d24402c40131a401c2d0200741ca2440c80c4841c2d1400c944074280702c1c1d42d50043d4040e410041204080c46095100041d01340c609119070380c000c008a1354040341000c1011210782c02d11811340c0324116280d008220920006852140f03100045d80d02079103080e0400d00b100106030401c03421440041c11802008000910175500000581c0a43c0c0108001c002200c51801050708076592001d00602040041004100080c0039501400e00c0d24010f040818145031090005240c0d0399003101c1c2111221002000001542401c0001056098150034003e14154082242e9103010007c0d01c43d1520407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 92709649 1250 92708399 92708401
    0x504090c030608060702030702031606090509040f120503011d13320c040509160522020705010c03060b07030e060304061404060912020304030b010e0a020f0a0503040b010509060306060108 82
    0x300c0c0300750b222000a1610700151010350401e80d500a440ba40403a005034401d1158010380050314000000e4070045803032a4035058040d074600028045844002442a071300b00100c1804c240101c0d841c140d0310396441800d51754450707496040500c001c00c0104800c01e18000048018100b003003281c030740c0c41c0041030365070050010310203003010945004218036440341402e064115044000805440010400b0648a08403414806592086002a91644d0390000f060a820707807040100510708110030300d51303100300396000c2001d401e00300300e0220400e0b68807240c82241c07560b544054552802d0b6140c818030000d00750016013285000241e8800034203a42e90f2900d000d104440002c04038040020aa10040a0604c4035044c040b5034549420804000d00d0700d07100030742d1402d03c0c888009441074804030440702a694441e06601041e42041000b59502000414501c0201c1d401c1154010700607610003d001a80c01c1075030794a07603d01c3c1614203000303100b6042c1d00030350260340b041d001c0c00810fa03001f02d08a94895405c0ca419000c17 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 92710899 1250 92709649 92709671
    0x1112060301021603030c031d15040309080a141b15090d0b04150e030301060c0f0c05061210080307080711010e0406080a140303070e150f030a062103050409 68
    0x903c9200708040b240038800c601c840405800d074200400700903081e01c04002c01016608070700c12207848202c000a09420100d41d03501032403c0e1075480c40c4c20078042c2c0383c850089501c0f14522482e0025441058488025415a40040c0707841085032802c1c0c0742032080c06070445091000421928079904051074440c0701c000c41c1030f130802c2c1c40d01102c4101154001118581904050804100c403c0ca03022000c2185400c10b400031007045800002c50341203401d01d0340c40d480c4080e540d44601c44100b1424100311501c1c2c0c022500026983e07a000041e00c1104c0700f2a58404082c10080034658040ca00f0f82e0000415407c184441408103065905032048542c0103500310502e1503a07800101e441d09070408032254403502d05600410070810000b2803e99451280c1c1145000202d24045d403a501d0104440300d000245844011100508001d0441e041c00308018081301c0c144889000070b1801604101e83c12050595036030130400422404a201c8110000302c1c0551a0007103100d610010944c0c17150340034009005da04c45014003d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 92712149 1250 92710899 92710901
    0x4030c0503041206140402061b0a020d061b0305010e010504020f131712032a040803030c030402040c050c0601090b030708030705010b090c0f0d110f030f010501121112060301 76
    0x101035405400d40740c0d62074841d00800c0e009810040d0a4401d5441c0c800545000022120b00500aa400900090800702e00700240401e1591080340b281280c000d40389c80c7e500680324980640344040c131851011443ca03c078201d0700400340c90b20802600070142031200400880000100072815030f101510090703075481e0154100e8100f48a0b21044641c50b41100c03500041d440c0e403060600c460806c0c404150703040340c5000d021a01c454002070301d5080c5150200c0303940e41c558981803503103542d94643c1e9802d064203143e51400103d007507070011104038001c04400420841180f402c2e10030780c1903134807160800c0c900300f407421343c0d4080e501e581c14040c0002c402e82d0b40940b0a0b50380e404200301c0300241403800880e6600c000d0303454000d01170f0504d84c4c7c485029110342c0000c1400641150141c0f00c1c000c9031001101d04012412004c1e50240c0701c4454541403440d0100010385c20b98000d4002903101c3c6d6060b00e10300040d540341c000010881031101315148084c0380703440c0c60500d40c60354000c01c55502502100d40b48140b43ca40c080024 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 92713399 1250 92712149 92712167
    0x9010503100302210f030c030f0d06080618070501030e0d080a0e03041d07050a020a0602071a010b0310060e0a061d040606080f0a0915090303090c0803071e05150403 72
    0x654010100c3ca24250b80c160490420b1008100110580d0940821001e070280e40b400f4203403040e0980e410071304c10180c01c51014030180c090030f88007490101c0c404cd9a080d0071401d010081d13480d01200c070200003105180070000c00440d4000e0030207180c100f00018400f41d00c251204116180c0c04100140e031004502c80341180d411000f00c2d040b818042c0ca5030b032540d680600030800d5005604c884280240d0001941041c001d0b0242d0b500303040b290300a132100c6407242d07a0300c000960020708102c81c2142649541c601c00c0c156521903e0180040c6401c05a4070b00b40305001c41c4621095512100801c54148412070b200d4885e800d0240469900d800c028120780f624003100e4400e907510405903600300385041000540c0d10b500409190140c4e000c43d61407001e94448404c0c5205407425200c020305038084c94014a07114002903440140301c503001e0310300064617212940e17901100030f4690b0f1240490790302c041448028800e03070304a0300300c0100700c840b48000303520307816910551039055000700e02c01442005000034081c036006a110b2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 92714649 1250 92713399 92713403
    0x5010f1101090b0712050f060607030503041505041505060f1509040b0301020c030703090b0c120f1c0501050a0902031501051b0709090b280b0109031707170a05090105031003 76
    0x40f40c05252030303d0000c0c50050601c40480f201070418001c6440000d040008a01400021b090186030a0050700c0944865002400171104485104401185d0010b44c3c41054007c03441540d942442c182000320a0060341c0024024510407456140d60301c1080e9246500c076550b1003a50380d2135a450b0320340700000034010420b8842d11901075000082071507080300040000c00b03040e807098403100d1220f42c441e0308803c2c2c240100b04200440d98000c50710301c121803440601800c2c100601040191501e030290b800c1149035001400c02c000b0782900c440050000f880c1004408024050441003103043d8030384240946011021040003a0610600013400d071a40c030203003880e5600c80044c3c03400303c0c1e0040c1c4c0c1e02d0202d10028140e0b42d9055039000001004161815888441c282c0b0a1044415031445605211814801807446243d0941400340c0d08400000007055100c1c06018038210080107512840207081c20b400e0419441c442035440b8008000c0840c01980100964465080a103801901d030381e64403103c906030f40055000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 92715899 1250 92714649 92714663
    0x2c041503060e1203010e0c03132109060f02100b0103020906040b0a030605060906031501110f0601080607030b0102060f0402180414010b0a0f0b070f14071403030405010f110109 77
    0x8040140540d07504103407a0054140111049103034042d056080e94002805a180103a01c01400f00d203083c8003010155811080401250f0200c140f155511102c00c03a00d4029545103014000ca2a5200780e0001d080d00010015420200ca8003102c03140d00035100c1d6030104000400a03500c4803000b401764401c4e416950354010240c40b1941c0d6503195101c040080d00b100c1207400000c0d040c82404038076800c0810aa0b00c7e0213401900c07050554a5040d000000e56480030070071810400d00d01d01c2071142c0340d42006242d142c042c4e104041c008a50400d080c0500301030005104000707040c1400051001640d0025000360710602501e00340034940c07101d200140948221039407078058064204140028041d880e101c4c001d22a40c0782c0d0081200c3c40c5540d00380551030240d403065410071600748008200c2424000000c0016502c181c1c2c24031520040c65544014002d164030b110941c035480b41500b4054032015201007411a50110010350410b860180001d0040c9c459802140400c14418000700c1c0c440000d403c10a119648003039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 92717149 1250 92715899 92715941
    0x303440c1e0403140d0903060b1305070903020f0a06050301030803071407080c060703050118021c0c02010504020315090607030c05070b040602030a2a0e0a08010501060e0901062c04 79
    0x260500c182c2c1040c0001d4034410050742515440b090001907030384450f9840c4c0c54103c1c1071481d6895543c010103c841010340c110a00034402c03040b0250b20b1107020701c47c03c40341e150308000c0f5055006009203202e413214003d00503840e03d0360521589800005030790449600004030313035480e61450011206880c0e00c03404100b00350008503c107402c00421401030320b400c081040850358076584042080701620001c0c410b0300010300c840070184065066940007800901a0b03440c1100b0410701e0541c02d43c00711125800c42c1030050755500103120451a090002e0035041e81c1d9082c14509505000011a84031040500400c00345642c0b1131142c40468024002e4907809500565802030314a081c0c00c1c4080a540f08807600001c1510340408009402d900700b17a40c0d2100000c00d001c842c40032244620a95603003801e90309490740400880400103240209005607800f802d0f40e581d8445504501d0014400c0c0e010045c0c10070010f1048030244116190502c890459030400454030625440b8000c00c0403400810094040840b1003204030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 92718399 1250 92717149 92717197
    0x27020c190f060506040b010903110103060b0301080a03030c08070806100903060212090105010f060c060c050c0f01060e060618220e1b0901050603041104060504060303440c 75
    0x2480c207801e100e014110912080d96814100030403541c0711100f0700c0c081410704200b07002048400420035004071060400041940e281d440700c10310380d04240e00c00c0903164845140141059854000c4500401c02800c0620781030512030b1000c5e122900091400303000e01a900016000d036480303004400000c0d500076000710f42c0d55400c042e1a9146050485418003e0f60030000001102004150900c1c01c9442d076075a404a0030040f90f4815001d00814a4080100079003844400252401440103800c500c80160002070420303d4021100030500e00140040d00c02c680c1445602c1605000030311550200d0401c0300c0e0b000c1c05240104c014401c0341041600101241d1801141080300c1000082010000e555528104035607040b410030810f802000340103241d0072450910104001480007504444070410061000c560b03151280c1c00302d01243c007503601c00d9000401401e40c81c203540c1c004401000c68501240301e11940b0311032407111045010303460b00002c84400403403030001e40b080a1070019650420881d8a0941030603100e8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 92719649 1250 92718399 92718413
    0x60f0207050706081009050a02090303040f0602121801030e1e150109060602120705010e120d0e0d140c0106030203010e06071202030105090604090206070b0403050c010627020c19 78
    0xc034208684500c5004408580540a40b19880c030a040c09003485481a08005e00440680000340101c500c02d030b020b01102d00c2c01da5040c0003400203400d450722841c01880c608000280b5080d01706814002d080c0c82000800020280c620401003491005e007808103600e03c010034914609080302c0308e00c42180c206a504081940e0700030074203880011407098228110391700c4044080844241c0d1003000056480743d440c10f000d082240c4060100305000300000031300328039400d0041d411300c420203000c403c07450000610562600401d1007050032151407000103000200703000d40040c0c141c103c6050101078a200204602c3d182c60b109400c41c1015503800f4000b40001e9019003034807981c400042c1ca031a404590808031070140440b0034800c0c0c90480e50014000f400c903031103840502c03005110300501170f42c121408010103800f0900000c0074a020f14480d540d9a95900c98035041c00e42110010b81000c900d0304400030058440d800842d0034604001034051005954250100420f440c003404401508404901d0790808008e03c046 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 92720899 1250 92719649 92719657
    0x30513090b01030b030105090a0209092416110709022a070e0603151b07082a07140f040204050a0b0306030606040b030a1205090618040e0604020a030b04050109060f02 73
    0x20070f803810702c804100c14040600703948044940080990001404802602e4150f120359000030402099030b58241304222110b85c007259000c03400c08000306010901c12400983c64860704260303214548140042002040c150b25803495110342541c0f80d4021600403c0442c040200850402c0c40088060f170740b03844e1031002503c1d40c01c40c4c8541445000c02074005115414089065006115410346120043c3d0304e001d0690480c0e910442d81c40350740581030100701700054655004082c00d0b031304400d40303ea09620a03030600b60400c40c1d060a00c030558001c00b2042000300b124a90310049481c04450064411005001040007801140e0002d60f014560368000101c00b2101401580907200581c00e907016070f40c41a0902050b200800c4903a50940d104070340520204107580c110303181210300c510304a49000c0f0800c000034080e41002e055034156660070300102d880e07450184207952011401030080d008600d8990001404d03001d99100c00f408019a80b0000303010400c00703500204209600c10f07030803c0060100f20401e002500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 92722149 1250 92720899 92720921
    0x80316050106090905070b07150903020c03100c02030f07020303090d1b05060703080a1e060b09120606060a140909040311060907030209070c06090b04030c1718010c03051309 76
    0x4030300500421070f403540d0b0182c50300c0540c0040051030a1450a50100f443d40e105c980d055803000300c011104442e81015010700032007907000358010400c00b0f02d24000c26041c03d8100b0f010300900c51070a1039049901c0d401100380d032640700803454443c0d141e00060010078107610070411143e074071002c042e20402c2005100a401c09024204802403854141c0fa4401d0000b035114050010f804203002c0d000280600d01f0079003052051a040205901a070701e0420401e41c1543c4135504252006030300480e2084490510001410044254800500da44c1c02c01001040007807140715048c20410560741d0614480100da1012a1185000904400707542c0c07406007401040f0700c51039200c01e00540078002c0490f036136040000d940400e880e0010400500c944414800b42c0b41491809000c40d030b040e8441c070070000442c0402103c584681c0c029140d60350b8002d45850000b40c800e0303025100b0440d11714280041200714164034415583d020081c20b003014056200e003003d42d224016024060701141185a000c20416600c0c0c01440d5244 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 92723399 1250 92722149 92722151
    0x102040e010807210f02010c0204110903100603020d26030709090c0302070201140c070803070506100501020a03020613060e010f06172109060c0f010e0c090c180a0803160501 76
    0x546861448140d12020f044c10b26a0800002ea0310020075a034040b140400c51050400105400d010760115080d990340840c4070780030000c00706011100382401c0c82151140b000840f010807009003140d000800030358120700301070a0042a69400902c030081909140319a01c0500038182d101d02d0055401007200040d40507014a550412800901050290003564040d0f80e05840310692030811486c451440d030411201421688140c010000d004442400103180305805080a001c480c03900c802c1500c582445948a11b0455110081010110380d020400304d812480c40001414956960b0030980082c0003c0b02e2811640c0d403030200e0715031140d08903900c190b088854500340718424801144940c0e8440c108100c49104980c141351022041080340b4000f0300192100a155a0800c00c4000500385400041e090800c211b03907441c01c034001440010001201071340070483d0117454034944110003543ca80520341d40e10b40c081c80c41c000d0950282d83d8080c09103000d48a2401142d0302e80560305420480540426019034141d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 92724649 1250 92723399 92723413
    0xf0a02071406071b08090103090213020f0304060b090403020d0309020d060507050316050f0417280c080a020d030f020f060901230103050a03050304060b06300702060109110403050102040e0108 84
    0x801c1d12480c092502e405c0a10903090003c0c10006401800320901c0403070303010940983c80c51250310a4400703001018040c121180c3c0364946807600004686007070b03484a100703413018802c00c40004c0d030010b102c00481a0610380841d540903984041121020b5491004103c1404c010070090500d5200015602c03401005102005222001c0b1041e500b612a07d408034070300300c0342000240451440303903a0090038100b109c801c840000300110117204078a4000498501c07074500c0e0f405100300380030b45542000701504412000c1d0100040b160300103031001e1100c1c0c4008003800225a0f2580c0c00c14001c0c81241c1c1030342a01d1040d900e403858903501c298000d001248902d10206084041807401c00e41d4120003c1c160b9030302c0030060502140540b0180c40d45c1c0c00040c01140c400c2d80b603c004110075100c140151400240c0244c1c080c4030b00801e0118210038080c80b625580520410204104405a0002d02c0354115025811f00107070103904281004224499900040c0541d0700008000030075400340c2c0079580c100c86a4500343c44803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 92725899 1250 92724649 92724677
    0x12040b1810030509060f0907120201020a1407050a080c1e0303090904050d02010c020105010506040e1803041d070315090e0703021905010311190e06090310090c060c0b0f0a0207140607 80
    0x38403050b210180f080d8824038050142c1d89c2c01900d40c400c014014012100e0150840daa580c2a040b015003045503583c00140c4204118180581e0b1803010f0164000509800280e40010419543c04515401642000150f2035012600c0500480b442200c0c050322013180c903c0c203410007503940c0b102003030644015860b050024006610603c102c0c0e043e1400200f06510340351800c40858a04070001c0c080a22400c0c00c0080902601d48c100000c1004200d45008002c0501d44800c400103107000c0208950280742c1000210350000d0800c4016030300b95201010009800100481c1c5249000c040e078000075081f0118054100030300c5640b501460803150240d13018842d40302d1103030040440d4050281e64100070f01d50306005085081c00380900e800340c4280a490f075400c015208000a1900d031581c20000c0045a1324607a0074140010040c000d00644001d0500c10000825990707160720b1003070011300c110700603e03200e804030b0401d403c03640440350301c2c5402440b070741282c0070a01d84581d11072609840300710209801d0119150 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 92727149 1250 92725899 92725921
    0xc090605030303040b0702031605061006080105010e100909091b050102010605031f11070609111014070f080f0c010f09080304020d030909020f0a030e12040b181003050906 75
    0x829200007802950a5840d41d0b45c1d04428601d02614400c2503000c1401038038904404190440c480300d00440040c01a81411106911041e0380d0b0381100c002c01000c00014403840c2d030840c00c1c032800c22600350b40344405c95281480031100310b441508068a11380c200100c800c1401100d160503c4519010260544051340e41e100690882e400ba11846070590880c0351a502c10450f90884400e40300408400441c02e289617841303005a43d0300a000456000d5900c03500a01880302c81d0500300701106056400301560b0640d44000b500c0c1c01c864004020b0780b8039000401c4010041540e0082c00310305da1201c0065102c04440c0748140030b0ba082140b28084640c680b0516500b03038219400f80050140d04510030901d5038841e50244806200648800d409101d804503000410407420b2008103521101070044a40f41c40c01c0d000014180c604220322040c0b05c2c0d2104000d01e14007400354007100d049803668214640c3c1c07426035030860041c0c4445450a1070b48246003c20861403903405410443c801d0004800f80c680b16524142844 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 92728399 1250 92727149 92727161
    0x90c041b020c010815060d051906030308010b0a12060306061503060b07020925270f091e02040602070e010506070f06050c070b040c06020705090106050315180709030c09 74
    0xc00160b0081500b005079502901a080e08074003003e2511081480510120b0703100c2d030040e070b4000c84e82c55031001001881024103810800c0d000c1500e8092090520755180141640010b01607581203200010b880d02181d400b60750710484412014005210707031075803400c112008203214810800c541c2000d8403180500f074803a01c554002d0301da60340c010b0390401c0890313020b200384400010301c00121a126180044038685090140c100108c1c0c0750382d90126441c0f050f100300c00000c1200404a40400c0da2040306001c2c0310040c00080d01511800d400001d402c01c2200343c06004255000ca03122005d920004000c03404075400700d41035060300d0704d034500489940d984405001191152a1025024001e165070503c00100c0b1508220b401c1545440d4850901714a52140900d810066608484200460b0810030072241c0603c803c0c00288001ca4000d2859850300101501c02c0c40020100d644809007180303050859641d640d1200d200c0503480719100c103a480c06100240c045000e074002510158008130b00000c120030710340101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 92729649 1250 92728399 92728451
    0x30a0f050c1b01032304050d020d1d150c0312240123041d010506030c0a030b060f07060c09090e250506070b0708060d020f0603091203090c04 62
    0x240304880d001d00181d041441c00303441060405407035600d404003445a24001c1d001150034105c009000d400d0030301d0140c0c5000c02401c185e8083d174100303a605840c0c003500a8418900c580d00744940701220702143e0005540080601616000d024020566011169000020741401c00c1503040c2000b4503210070181c0c0702004014202500c52410420f00c1c182c1d103500c9243e04082c44c4a405a40181114a21a03260031582180e007100c44032800204450619282c006411401054103403000c920790304104141c43c50390b100e40085a024962102c4122007251200d60860b41410302c0380e541c0c1134540d100c0c0d1a0000c003800d070752112000002d000c2000424102d1140c8506039104080c0001401c1c9100089000241426070020300c0c03218404080000450751a01c1008007403151045256000c07600d060400a0b10346007021b8a0903000c6d80c140399410700180c580d21308038592031204880498032540c480b0007035480c1070f2101c40c0c60910107030003105000c0660350014401522240440d802c1c0b19403501010804422140800c81d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 92730899 1250 92729649 92729653
    0x906091a0a020c0301020408030c07090209010e100e0607061d0d08071107090c0c0c0b03060609150d0c0201150509151011030c100509010902030a0303020c0304090e030a0f050c 77
    0x599840c0898190003024045802c0c0190780240411500007401c82e009980121050342000030080c84040d000e0000303802a2124010840c1407014800c002413a07140c50000450244c07100429004500307002e0310190b0b04441001b0300a80e600c000a140000c05804800f1407105076101c1000034030300340c241c003180c030030b990b050345644042c02d0b541d07001800c4842455003107040d40d10b07002d20036000c18400d076140030700f101204041d140c0c03074100f6880b071030300c210040c0303041e8414151201c040c0180080f956442d401c440540307800315031809401001580010aa2249100d880c0c841450200e4a01055030103401c24803520309080d005200c501da0742e07800d01404407402c681c0500818410b0a0960107490403240e0030003a18100d20b0010140548015400d1440d800108a81078a9100c000f2a03540341c2c2c12030240d00c0e0700407075540080c0102d20385c40c1d010940d9680326000c01414540c0103e500b0510003001c00c00d032001090300060500c0902e1948100356100e40c800422040095030303440c9a01c03001e0340520300f03d801c100c0700000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 92732149 1250 92730899 92730929
    0x605071e170307090503070915080f1005070311070b01080609010b090609100302031006081908161b060801140108090703080c01110d0515041104030b0a06030b01060c03090609 77
    0x1200d0700c002d9100518941c184103443e540428580c404101b107101a28404030001507125a0340d00c0c03005240c3c51548011200d074065082c078800508041044084c8034000300c008540d503140d4003030580c0900003442c03250003012000700e906402d1124000c5280e04039000002a12040c0e1a20f554040c2a10007055070039810041c0c1601066a5042050b221540242d600e5140e00000d40c5a41c00203040180e010320083c1c3c0c56480d4141030011000a100644102c8807003120300140740004d90300c0c607041c0c5c081d5015a0800a04c40300c64103090000d500c030400200009101c070050855140d10b00134003019400c1c0034000030f80382184195060b035400750402601035143c0740e000300041480c6594100c459489842d845125548070083c9621255801c805272001d9804034001080500d410001040d030300340e1034060948541d0425508550300720955040700d00360b81d00a50f4600490340c4902860018101d507070310060046c030b0b02c240001120b540c0a00c0c1c49148a10980c4d40414482e6105000c4582141d503000d00c3c02d41680402c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 92733399 1250 92732149 92732183
    0x70e090402030102070f0c170304030f11030a080a090e0a020309030318010207060203041101080a050c0405010c050102070c2706080d0f02010b1002161d060105130b03010605071e 78
    0x881140d40540700800161405046aa0340410f29142c450101e5a00d2071200c41801021216030091203440c000da401503007894915211300c003082c44107041c06088860700c0056420551418056100c7e05a040341d04030380e4070885804020001c0e035003440b84c01d0102d6000e030003280c4075203400d000f22801003514000550441d201c1c0c00c02000303911190214180199801c0141300001401c0c1d0001d948140c1c004c0821142900e8001c00150000500501c041032440c500760410208400080580f41034074000c0c40c0c0002100c9851802c1c03402032145c2d502c00341013251400800510b80526046140c050900251326440a4001c01442070a6a03a14010980285c200d68614092070340f1500320b203104100325100105829030030f5804a1501803a26120b0b00040e0000b0100122a0f00d40e00c01240c01003104920360084418585185816a00082c01d560f0411800096092006100001c0c110190100706890355983d6543c3c0c4c4060171035032002c03504468201d00144012400204a80720b501c5a5800c02c154154a026030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 92734649 1250 92733399 92733409
    0x160201080c071703040210020604031205060a030506010807050a0b07030e0d0201030b04020310060318020a0e0402120f030901031a030a0b06060c0a05010905010617030d020a0e0405071d0108070e 85
    0x20305007401110240540ea01040b00303480e018500300c050604641d03030390505005005e414118010a4420355011070b09001c00240c0c410800c001c010511000003076203490340000034043d018941d0000c1c15a11031040089039804020a944d03046840440c2c1c4450819075800c0010202e02030500041c000c50100111149107082041c1280030041c41490005910148040014200e8006031514070b04100030082c00d10802d0b80511034407000800c1d108032402c21070010740c00030b040720845003c2c03142d10400040c040b504644131003c8002040003c1401e81d4014030441c000d841c3e80350801441240040c0c1090854908000d9036105011440c81c0070380540000b41843c0c54203101410080d055982000c3c0400599103c2c1c2c6003400028070b464400c20011401ca096800d1103829900140c1021b41e031001c61090400c0003090003c120360b0001038103c0003584880a40e0b8040e0b4600a04c80c00107a00b003070421040140d540c0d402255080d602042012412032032000380f004451380d440890382000800d6400e0f0b2034039158949 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 92735899 1250 92734649 92734651
    0x41205090105040306020d0c0e0402030606040512013e040f090911040608100f0527010b100806040c08070906050c10060f030209070503060d0f021f1107050616020108 73
    0x1040c140b162420340d4031703a0340038126800444044011a80c1e0066007003015444950320301c461604507019819810140b00140e07040c800e5119841c840e10441020a003a84000c0d0800c01d4010491050020708a0709110560507070003800a01380000d40150407003004e14050038007a101070380c0b900c80c041441203003880c1c00000102030700341050701c00d600001074004580e6198054500a080c58502901c107050030700e084481601c403c00c0d101000c80c1e08110400400c100c07203c49120f0003000d080383c440314144a10500e0390040a0b285413241c0c10804840d43c420b54503400c660303024010003041c0d8080100203440e51003201c9180060b102c3d480081c8200703004100403132155001c0d0a007030f1808001d4a4000c40ca5642c0401285d9596201400400c0380f540c081040d03103400340f4000d80c0100710741032032459460072a0004110004050300241152030b00031074203040d5101d0a1030194203640d00001074400340032500c00946075840c80051722034144100c100c0492903080030010b5800b0034118041070030344c04c12207a0041d02c048078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 92737149 1250 92735899 92735917
    0x207030813110307061206080c130b1203030a0515060313141e060114060c0726190c1d06090915070507030e04290406080a060b0f09041205 61
    0x2d03041d0640d8110f0f0f070b0140030100007880161940520b186644940314165401903000035001c1e004100b080002c1c0e10395803900c1c0111800c1901c00250300c803020300020070f0010028078452191001000b081441c0040d980b025025414041c80c841900046070108141d0340f10445184031040c0c0c9140525002401d54120341005c0c1c441d00702900c1442d0421f00600c0501a020315501e541030380300c240100201c0c2c0d1510007034403038a803041c0d460501e0645441581139840385540303e031140d90f290194410038000004200080e2071040c11040d14000303980041c0706180c0c3c249900d070584400540c1d03280010030000c0c02214080d803014100002c0801c2d03444504100b1400001400c40e0221300445824045d11041308080c07610580340c640b0b89503110502420000e000f1040011024000d914080030b804400c0400e925401c0551103030b00860488030740d08401f03c4c0c042e2801c2d501048441c45811500401c1013900c0d0401c0c110100e068940c1d5250b070340a01c003001911072040c0c402503e92484290445900c911801c02065400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 92738399 1250 92737149 92737163
    0xa0305090c04020a09140a081209030312040b0f150312030a060e0705030f07051305040b0109050a140301050903180915030d0f0206090607050d020d0603200a06030207030813 76
    0x30407120214040c3e0340b10b003014400180c020300040c0040d2450b07042c243c6d02100c09459400308a400d00f0203c554030401c06400410841006c9049460755604200301c0c2c1e50980c4c1c0481c241800e007814036121524982c103903071404c55802d030540000d4101035001c5000900a00080040c049010000c181c2c50103035001804280705580c44400104104a11740301e840c0c0a00013507650319943c2e180a01c540f1550281c098004401c104040065038620104070164500f82d0300112000241e401060b80180d8440c1c80a03406150000703613000b00001c2d1030102200c1c2040c6603409800901c0560345080d445610780c80b46c0298101c2600300c400101c0660300384030302650750140100c140010140c46100000c0c0c41c003075400801e0350010300d5520005a50940c1032202a400c825120b0050505040060b4007402c0740c020080404000355000c584540000c006800130002503822402110350f17041c0c020031002103825044800c90240e400f050001448a1113840ac4030300c03040e01944c0d00c01c02074940d0b504400080c4240141a42c00c6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 92739649 1250 92738399 92738413
    0xd1104030807030906020d020a02090106050c10110901110105010b04060c1e050109030306050907020c010503091519060e040b0a15170705010201050718031b080715020111040b0a030509 81
    0xe01d1407030050040500035100c16820720310f050310003031078120010f000c03004541204506100503100c2c0d00b50241507400504102e0f41328000700341300500d800d06d000100100e00303060802c01d0400c2905940104050300c001c1c0e80b1207041d85e0742d101c1d07c282038450a1045200c0004200010004c50748290624a0f07014031501348031080e8021101c261f4046a00240c0545940e5554080d40007095054450240144400e0b24241424501164084d4a6004186440d8140200080012400c0c101401081c0345c01d81c2c3e080308a602800e040b212016005050601000000c0c501540411040480010b0342e00c40c51b444506c48690303554002c070443c05803566041e003003948480301c0f20100b46401c1c40c0a04166050550000303007455480c0c04002420744501030a55010301c50445800801181c1c2c442c02041501e402c1100350240c01d20944408100402c2170f40061f903e4010030001080b4120700c2c0b4185010200694001e0054115452140d01340f4480c030300c15441e051780200002d41c07086010741c0040c1e9022030a902542e01d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 92740899 1250 92739649 92739653
    0x4110a03050c0f0d0206030a1a18060909010204150e0f04020301120204061502030a030e0c1002070305060702121603030f0f0f060e1302280f080f0c01050d110403 71
    0x1680040303400864441d04036008101403801d2030300708903840d00c1040b140c8920503030302900810480d1001030700340d49060751035800c039011100441e0884c458124024041003044c3d403007904150b18039042030741c10b00d11800f1780401262442c9414000d0318265000798182c001210340040e0306540710103003841066003016548040ca245035540f807003c1d600808904001c2c042c0141d0710320400c02181c046400800c02011000d9014083e0307a400801c1d5091074070341d410001500c1440100c039514045001280c59030003407448840044450b0b0108d0a9011a03124200705d030415115101d069845015034010034007115000e02c40c883d001c2003a5026054400e0081c14009400400c080d200001d503281e40421400064464440d900da00003d8400e03440100340800600c03200d414105c00180b20705141c0301c0d003c1e00c03910503c030382c0342005c1800e8401c190700c0c1e074144035218000b107a48118401303880249208000590143d5900c42565003004140340400300c205946142ca0543c4140c000d1004180c0c1c5000300200003014000400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 92742149 1250 92740899 92740909
    0xe0a03030e060a12140601030f0509030904180c0308070506070905090601120e06042004060506030a0e03160f0c06050304030c14031314030613080426010903180f060203120411 77
    0xb40c5c03200241c2986030314503100001600340c0e100080c948032a9490401000340024000c419140590310444005c034102c10708914003401c04044c4c1202074402c0d50008000810042c1500061041c076220702d041d115035a440c942d096134030707076000c0c46819005001600081c480b980708070130b0303c1e10b20361f2044c0d03000622a0b14007030001c1c680f2038101c400729400d0480169214000540c0303400c0c86203401044034144421400d190105640c0d02001d030141540e076031560f20b991403110050040d504500800c0d10304000341c036007030f05115424a154600582d03140108183c0800d2091044040382d103d260562500d04001001e5030380d52a803070014407000c04550100f440354140083c0c0442079880107089841901d00f02000c0c2e0f008060400801816603c189007110411800007080d000c02d8030300300c6881d00d5495104000b8229136014030b821000551000c0d52030030441000b00740e0008014010b941010100355401500c49881c03101c41e4655001d40800f581c000c1c040e49800000b00004981d21900c07031001102000c1d00000410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 92743399 1250 92742149 92742161
    0x12120e0a120f031206230a03020d03030501050906060901081302040e12070c14010c060905010b12060906010e060f040b030c03030f0c1009020112090c03170a0e0a03030e060a12 77
    0x94604032a41c42d42414564010581e9420800054003000280e19107019480000801246001d03a0313049090080c4c030701e503207500f529001150040c090618091f51458000e000740002d0180c0c40c442c0c50207902142d180c0c01c129094032644001a11200583d407141c00301c0d0000d01c9030708002240d105480e030b510104c41400610800081009008855884020514264207403100903001403180c40d40300c1c051280160383c800e17806a03506030452000038004a544c100f05e03000d0040204d5042d005050901c070825603400000c2d15510621140094850607603d40d00f62154a400590b401ca603c40780000c005e400c01c0c42e00e07501900101400074111070003c802c590100e41907420001c18080304c80008610b020311490144800c0e800c0e002070745000c00c210304259001070041203a08100305040c135a00c0c80e2910400c42e03070f501040003841d00428034402502101c00b80445a0340700071080760004060020394500c60400d5450441a05d42c035403200d0140d207900005200c065003080e44c03200204511986048800c220070302c210 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 92744649 1250 92743399 92743403
    0x40507050a090c02010513080304020918011104031e0201050d020a020703021e090708090a0b0a0e0106081605010306080a080a1206080d080906070e01031505120105010f12120e0a12 79
    0x108503e506248003a08440d07006140c000c0d045041d004a00024058008482d80306034111522030040e121410031b41e00d080d140ca03500108940c030748000d0107012400354000c3c008480c803840389042c030302e0408803211f020340031400340c02404144207005410030000a41c0140036101514411605e00e40e65a0b0001000b075029200000c80e4081c2d58010010641003507269180c0c4a2800d040036081401c1c4010165a51003822502030904c0c1464804100c1d0000b9980000301c000240100901506440d041442c3c0c485c176800403400044030400800048039402030140c1c2e422120800040e2460010940720a946a400034176460100b10850700d040386096002d12900002d018410000c0403801381d00d51000d030040f600030b8034540c280c0d0f0000d010864003e90001501c0b2040e4001c0c07901081906900d24425296130003500f02e954061002850080c41c0321056018034102d13040c14a580304a9683c414080d80c0c49518030b400a809611651341c03100b4000e0041c4070041d40720001604603070340d2990b14000781040b442c0c0c01c101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 92745899 1250 92744649 92744651
    0x2090a05010302160c092304051213051305010806070e03071703090d050d030b04020909060121021219090b072d020c040b010809070e0405030d06060f0f02010204051503040507050a09 80
    0x184040032000c21f0722040852101c20074418031802c1544820383e451140600c5840c0340c0724001100b0001c210300c0d92a90000340341c0600f0400c0203800740d40d070ba08040d080902600c1c07101d00c40d0100103001c05109000c0145800d10180c0135015560408141811504145041e881907100030000304155480c0d82c03100758541402880a01400310008900030162400b5030358582c0300707a0050140c101c4c50f07078400130000c3d040348003400d084a005a100d48000070104d604c07800035403420300c0850180300c6030420061061107aa04070701000c0b02d1b040740d449103074102c4010f4076014004500110014107414014550b00398007140e40d806d0616829544041c281c41c4070a0036411000503040588040007500346400751404142c42420101e40919000f000d06540d4107580c824950182d0408002c5010b00c8030a0085920344541101b0501105844079000f0380b1250640b01942e001849a15051040740d00c180700765825681d004000300a0690201c0225a86400262003a2024080d401c00043c0542d5003070302c068018180010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 92747149 1250 92745899 92745911
    0xd060b0d03090602070b1c02030604090605070f09080d08040b070207260d0c1509020402120a060e0703020310090e0f010509010606030b0603040209070302071401090305030a05090102090a05010302160c09 89
    0x43c0081c24032140e82c0c80380041c51004d01102249005011000f0b241c40300c0b887c00181c07640d40b00000500078014101780584001d20704014445002d5102080c900241c8090b02c1d50010076a5401640c0d40e6a009400c0c0800001c400e1400708d40000c0c5500003c6800190703600c11541e03030030748900368140c41d448207072907010100760903207821303640c3c503405221900b50003403241819246180780b9190440d10242e0264016411580c86401600315655036064844040e0505440002071400880d668000c1565000d0000360906c4100021b194600c139008603841500c4405c94000c1c000d103080011000391444104203140c0340601e40b49405001360910400c2d01c11302160001049981c0f1b0301030090210340f0b14120040c01200d0410400c005a202d092171980c10030554900141e941c4d40ca803c2403022103003044d00d08041035003400810028194848003850050546800c100190384a01d03184a080f4420010126000040028200a5580650b01800c039a1a500c038541d68810401c0e66001c0312480550807241405035504 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 92748399 1250 92747149 92747159
    0x9030726030a050106080112030f0f0201060b0f030906060607030c0f0f02030604030e040c030b010203041a070b010806071b0321060801060e011706070210020d0f02030702030a0e010e06090d060b0d0309 88
    0x8411b442c010000030448000340c0c0c94907140204000b60007a004400e100300903070f810080354400d5000c2c00041c6502141c0707c3c4c032010713984008021030740151001032451240d079010a0342880d0050071a51035681c19100c0c0d410101c02a030b15a2184030020030183e540e92a0501c1070310158409011540c8075901c60b6607440d0581f1080410001158002c1c440ca1041601d050040421660004111005d0360900c0818182c1944800c034403440500c2015001008032644000020b6000000200503014100940302c2c600312148001d9480ba413181e2601010300002c0080c1010403401c2040840d80d9211002404080703980fa4807a4003090941c1c080e40d010800c450303100300040000e9003503044609080340704000034000d40c0c1401080250303540180c02c0c01c01c54031540098001c920710352135407005850020441c1d055451385001030019459030400000900803641090800026620402040644071802000182045150018844104d40e9a0030480f24180e540e40c803154180d0b10111011040ba200381d4529541a0401d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 92749649 1250 92748399 92748407
    0x70218090105160f052206020d03180b010501110c0a06021509010212060909070f06050405040b0d0305041404140f0103020a1e1208190908011409030726030a050106 72
    0x28180c14011074594000c089090380b044c0c0500e45003d00d840c24070f40b90100d0342800c41e0f081003a0b205040c0d01c16403d000018659401203029001c006954504204a01505d4a60030215000200c02030007540004014400c2d5070003600311410345095142202c01c144610303804100400110740026015920004803442c141d0043c008050b48464200300075810b110902d100311001d020050b02c56440740440c000083d2601c0f20811401c0000c1000019600581e5500d0a01900e50390083c043d803801035040c068031a00e50306004038142450740c1e143e0780d0b082c9804d01e0081c404444040000e580c503482600e613807202201707621761076a1074001d00e2034021815495141d4410040903003465440196040d03022604204110b0703003034030724104640d0035404001c2015a10b03c0e100d20b5500c24145040d0224601071080d1007a603502a03030100a1300c0908c002041918451000c1c220058001c440b09103c0781d10400800300003401e0b0032403204840c0103800b00707580b104030061000c43e55a00119403480c040303680d0b0401009080e0b84 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 92750899 1250 92749649 92749651
    0x303150e010f080a02030703060e100f1407030b090402040c1403190b030706090b03070507080a0c0204060803090f04020918040305030a05180a020103050c041802040302032e090305070218090105 85
    0x4200080c0903218256022a1f1101c0746403001520950b607071520682072000600c04405024104101000310100030851030b0010580d03009038904400c1c500c000511514040c3c46000c1c00e0202c0108243d12a1760f1f180d003044043c05120910000308000720025540510081003d0f40c0145404400c0d1b40224a1810000702201d0381038614512039030004030b00b080740c240c210380b0100955900705042c039070b641d9408805031128424200010641080010003004066009502d150a2842200d003804030540d03030700080303540303010300700b9416880003400044840c02c1c034003035000781a03112024010311040304002c100450719140443c1d055010074400002c004204c880752040d02d0b4840c041c000e440c01e80184180806a68440001e0700a05040e070f554013044485105074156001080c68030064102504040381880180d00329200807030092051300c03003440320321f0190550354441c01420403441c03551030507070640c1d040500309001043c0c05021301084454050f0b01e920484c02184000000000506d0401c03404d02c50031208 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 92752149 1250 92750899 92750909
    0xf2012031809010b0a0c020d080c01150803031e0a060e0403171f0b0318011104090e070b19050910210b0f060703020705061908070809070308070303150e010f 69
    0x7800042c0013060f40da8051341c9001460346040c0284030000d1011621422070058054609131004c20420140c01e41500041075900c00100001400b61744c0b6800540d907400f0503a61b5804071a0312190080000301030031810740d88250240d501140541d6100114241088180d034142d00041031007107225460801212041e07000f842c000340071890150910410301850101e07000340c154088000000c141d80090381d211405410398020000c1003060000704941002d6070180c405d11049030709101c507507400e204000c1414011210f101c46018500b01c0420003c0300301301d2140503c0001d0000602c041100c6031204480c0204e48403090700c60007018503180314085800c5100c0090508503904159078039110b0b8564000800d40020143c481c0c680710b14140c64141e003007043c245c11003a085000071600c044480c0e40c0007924101506d10340c846507400e880d0407008035100581100c203044c442d80316980400003e001c0c8801040c0307240c002e05c0d001071185409221401c5804203540a11080000c0c00c0051126100b181c2c0d000000300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 92753399 1250 92752149 92752159
    0x8190509010e040b040209030d0201020912010207020a030b06030a0c0f06090b0313031b0605040b04020405101202060f040b0a110c010513030b0c0705100614010c0f20120318 76
    0x503020000810b21070002c2a8540561345681400440352200c0d015100c2030b84005055550450202d0340090003900507029030783c07241150341e441e50b10744601031013122041c54029156544039411a160207604a03806400c280d014801e0303c0411001c6a2031522440281c01c0350340f0341c0300d0300c6464030703100801c9249a90083c4506100400c01c0c800403041d00c40400400f01d42c1030070901c89100c9030a41d0002003015181014051303030304007030801040003551000e440c40b403403089608008031b4030b400c5001c0300c0541050260985c80c11411006001500c2c100e0060915060301640701881d0948031088814103810013039252001ca10020340407280f11500340000803c8110a29004c0e00300308010120403c04c0702d06120140450003404080380210a80808450a454222044a44da5244004014001c0c48248103600c0b5500d51080d032400d0542c032400048041304c0d08000090801109525030410011a00e003040021002074208516a9200c7c00306c10b03083c00b01b440f130195443e03c03072126280d1909080400305030700c50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 92754649 1250 92753399 92753407
    0x106080717131b090603060e0a02090411030c3105090c0d0204060e01030804030606050102030307080a1503140d020f010b061902010605043801020309012109081905 72
    0x104148555203540950210040303440c8082c54185803401416100c01c01c0400c0e42401004504100b06400000803a40318520030400b5010400d407107a00d0341c407095002175102d10348402003408a020140e154540c0100141a5441c00c540c090010307005506d03004080d40b4040c40306e200c028520503818042441c44800c004240082d01d0820f001c0c60300c54081d43c0d05140704071540400d542c10740d02d071ba0340000b01a02d100c110286603961242410a0640c100c1e00c000c8440b40e041200c0402c9551011003070341d00407030f00c0b07440d51111f9455804101025181c1c4030a0b400d440d14181d403000022480c9034403110b1038100c84401518030940c40610003410414031000c017030389903814841c61540945800c012207841c508240ca001303203407412140b003c82c0074019a90100e9401400c224a40c1c4480100e1110320700d42c00f903c1e9400301088d0001285a510068002c1156400b6810074010081a035004181074400c046442180040c2141d9006c040e200700c522a40050b500540040780484c410031600070b80c0802c82c0a68100a414 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 92755899 1250 92754649 92754677
    0x30f01050412050c01060e18100b030d1b050604030f110601080a0305070512030702011a0f010e0609011b0f030201060605030c040603021c0c08060907050c1e0f0a0b01060807 76
    0x140c0e050b6240644208000000c5600c0d20080a40c0071801034010345045020310300b00450310480490100d148040d240c003518401c00002e5013148100e03114464080d003c0c043c10103492405860b100741c8021511001407002040c50006070b400e210691003540f003600c03441e81c64100003030010003d000094009010303600c2a401808105d03c000780d0300d0380c3c00c0d515113030059498030303079261190030424031113158110850040140243c0c41e8041d00140c1060b5105141001c4400510b82000f1603068070200300303400f00e041d080442002d0b013060760080420583c1030400216010302c0b6071801c3c04c0d485e5172503c151101020036400804166080c044d4100038020b034a4454110b0074a40c040344035030b110b0f0f40301c1d400600da4000307000300c01883c0030122030108048403413081054200c1220043c000d200211400c51080546100040c065802603041c0e901d0070f0b540310011f0007198010510550010200c00c0290280e110355440070b40d404900b04042d0100030b01ca1800c10120f5490000c01500030030000c2c0202061020079820811 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 92757149 1250 92755899 92755913
    0xd1803120e03070602030901020405120705100912140316060914010204061407030e0a08150604051509060d020a0f0602010b0102010b010c0b060d061109010908010e03041a0c0106060e030f010504 85
    0x14815044040141d80e47c841c0050507009100c1e50340440e800c101141c5003180c054101080050132030b0006e5030b0b4440007000d20a4111028403203805103508040b00303c5039502c081408420031000601300f10742142d291580e08070b81032030260240d000407a5541d4644000c0307020022030b80107160035001003a000b5030515040050103007040c0e40b07014503584183c601080100916100344850643c000c0094001d100c05500d0300365494580314002c0402d94586619004500c3c0b03802c041c8110782c0f0900301c4034010669a0900400c00840400c0175144170f9100001c000c0c0b03080966030b003110100082004014050341c5c80e00e080c0011782952003050300c46055916200703407004d00380d82141200400c07552126041503181d03514400540001c000d804094000c5192410101c080001c2c20002d200b070303050036210514a642d4445080b800d03600c90208044840c1c0051104201d00c443e50943c80000c61030b07200120b411f245412441c142101c50503400107001a0390070450f9801800c0500160707140d007016800a024602c1c0540b60b0907 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 92758399 1250 92757149 92757157
    0x61003030e041b0c11040f050402190e06100504050301050a0e0708030a0816050c0a03050a090b09030a0813032a0b091f03021308060907080a0b0114060d1803120e03 72
    0x20b0144444c415500003008503070030340300c054140e0041042020342c2c40038001c0340052408903401c81c00b440d4400c6012040e80d0310308488104a8000808849440e51484240149042c04120000030700005100105940d41c0a0103658414034000400042c80c508000d9100e01d0b24a055111041580040060103402039001c3d91003680020044002c5d4001c102014084405120f29500342c11580541803c1004060344440100598880756642002d603503142c2a44025511900c0340095141d1311800da0000018501d8000e03012480c20f0302c005001b420340e240c86041100c40341c80d01d01581d040c0a07140842c42009118407820180801070012410080d00c2030201c2d07003e00e00988481203a102c2040910b955a220703030126180c0f24803070350455044658170050241d44a0040d60004124000d091000c0361080001541c5a84250032683c548500d0340703441c00400da03011800b01c203990080010842c0907401c01c0c85026001001101c41010303d82175000e07003002084103005820b000001070030700401000718800081a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 92759649 1250 92758399 92758451
    0x1a0c0a02030f1c0906150f050d110109120302101512020405060307180b150f0406080405100c050309010b06161509060e030301170607210905061003030e04 68
    0x4541d03210340c020f116200d00d0055a83d1144058145100c0b103040080641000d280f846a000d0405119a1240c1e412480720302240a0190451180c12881003c82d54212032a41e000406041c0494a0340e1210500c1d40c40d01c205c084164096402050b180120608030311540c800004009004403c00c0e0801d0306d0300301c13850202d060284c403a81e01d072408034000b95407e110150003800e8004000b101415240011405400c41941d903c0c401c01c0000ba01216006c0a0000c8803070b48600c01301a603103018100f96003540d5450010740b05448a2003040f081e80c9805aa912407907440d40b029446075030726450b000070b915003514800072410b8080c10007030200082d40d9007485082940030382d11001c44840000301510104c02000012030151802e400c004c4040c0604030080000d46c1601c10055000741c5c03401500c24190f5950105481d9100000d028646180e00044844a041200c1118503400b02d083c80b05900c070246040401e50b10705440d68071030f1408004149e001501140504000d40e0140100c3c400003002c4200c1c0c2d2541100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 92760899 1250 92759649 92759677
    0x190801060f1209110901060f090b070f02090a0e030307030e01050601020a0b0721020a0c020307121a06030319030b0a050102160e0903070b040c0e060d020a0302040f02040509041a0c0a0203 82
    0x3880070058400d010124424010b01704805540c1d542c013009001e0702080d10818003040742003102090464105040f5943c0741d8000d4442804040650309120700040000e0a035003800c1d40d00c0c401111500402d100840c040c0d282613401141001241c50b0442c21504050815410355024071540d40004070054101a807001940c20031503060642400001c0d108244e0144604829100107030011503181c120744105c1f40c0e20b0081d000c440e203c03511104403d0030000340c05400703002c41001d000488070b0800704039803095001601400344c034108030f8074042c03807140d9030300c09649103021946401680c6001e0901e404640010310003407000380110030842e40c03111950b80480c050b51310700c1c4a81c0310001e1009481042250b000c51740c0075074500420300e0306040c12214503810703000300068880305a000c20b4061400144400d100d036001414000010700d541d00304002003440109010960303800f4000010075560300006035204034082ca511a442d440c00300d24882d180400201405130780c0c2800c0c05550696540001a2549900180d40c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 92762149 1250 92760899 92760911
    0x8010219030c09080703080a080f04051b010905060d0603150c0503011424042408060d11040905030d05250509010c060e030a0207060819020d090503190801060f12 71
    0x42c125074004142d005410076228150002082000711002401d06010913a034200090b01d40d0400540307140410303180600700341c4c0500208040460007500e010200201414640805a6a81d0215880d41c0240c5420f060072070b03039488100284400e0303000c90301e00d4200074030080080510415000e0314602040c02020300c0a0124180200c158484040003410500039198000ca15041e04d2010034480d4270502942e08804040d80b162181c0c1c2d09103800300c2c40c644280d40c0368003416030345281c217001072034281c080150b54000c00600c460003240c031148683d07016103000e440a9651040c01005c0901512070281c2000d04107903444080d80382c2490f803000100c110381910719200da580e40c903280040b41c1911140e1000381c042864041c640d80398150000c01400b54021540917225a06d0307952406544c4020100c50011404840f0141c0c81c4600303501d54010b14660701c1c440c02c001050412a219a0724581000d162104058a140e00301c0191503001880d090040c0380d80e1415054100746580d009092000690311500c00d192645 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 92763399 1250 92762149 92762171
    0x100e0f062d040602040b1b01060b09060406110a150b0a0e040206031b070507141003090b0a020a030906060305060105090a1a21011a011403010b180d0f1b0801021903 72
    0x44c048600500c8910303000ca40b9024150b04607201c0154000c803801081d8689000050503031b00c90b1050301c002120040000e410b282c50030109950402c07a4855182103030240c00720300030010b5404903181000c5410400001001d48000c000d201035150150800040300001d40308000050b43c030141240d42c401c1418959501e0107070a01441e003100c2c000c0d580e00809034050008081114031001c0c0d075803440040c04507a10341ca0100e85d540c3c00d50131101c9064010b480c81c80d031000055100030b50b03a001044c00800e1407400268170381641d11a070084403100e401c2102c0c41c0e00000010080e500c0d10070f0030180c01404401040107030780e0b030f400c1d00e2141c0c42100e0700c1450301550610500c42e8031003040e00b81210300020b040d4024005105403c80020103094030080d11408900c0e022100c122098a000a890503241f26100c51403038203401d40c41001c61001a03240ca26803041003030f01203138001070180449907d035611640c0c4884069002d88031084c3c5000d10b03074200c0007082c2c0c414019450340b002865525800011030782000a282d100d10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 92764649 1250 92763399 92763401
    0x1a0102210a021204091b0e0901050108150406150306060908030901080a02091804021504060813210503100506090d140705031b030c031906020c100e0f062d0406 70
    0xc0c030032180c80f8000103d00080c1991140e00220510882525189111b1400c2101a80c030032400018868015410000501c091b5000300e0040c2d400034096801c001a4010742c100080a03101a500460201c1e000d150540c01d072150140142c0b000b801d07440c240002000c0c200103100d0b943c1d000c3c13500c06c1c904211550f4042091400c0d107a04880e024480034140080040e040003030704001c1381080d07400324001c0026207540c40410100200b42c400b0707901c0542d2108500c1e124858407070400b8001c1601911151001c070198580f41d071150740500410344690300c4844c0c591800500c1d01106a05690103030740242c0b420040d0701d80659405642600c00f80e48410300c44604c55003100705a1078900e480c0c2103650140302d0340413003030810b6840e0001000d0001c0c00314200d8200307501440034503407595201c1c43c00181d1001810005000a0301d10f8019004029944040700c0c00c289800510a050725082c92030010a60802c0c5940206030000f44505a40000b11035008507604076210b000c409000b82112000c1200b04010000c20100708807 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 92765899 1250 92764649 92764663
    0x601170a110d0603060c090b030c0a05030a1104120312060b030601081f0902130b090a15020a0c0b0a081803030105010e04060b0a031e090f02040507020f0706031a0102210a02 76
    0xb003601007000383d449160040c024106001610f02040301e040001810405400850780f0400409648500700a1080d1065035682c00c05007001d5411f94071201c00320b04070f00e102d2020740018517440300302e010311503403a040140204010105155803a0b040803000e01c811659541100d0708017000f072038041035a81e106e41c40000c0d40c0b496100c80140e4078410800001e07a000710354019000441d1040361340c1c080c05c0d65031622071116100e40d50500d80c10a090200030020501c3d061080d44110f0014010758200190690340c8809400898220b029a180c1c089000c02c4616071003400a5803020045500401c00c81d0512200740d82da010521130309042003014200d0b10841d40741da0304158000c0400000d0503484441404000e40603000741158110000b4036030320072034000d019a0149031080740d000290701015156940910019010003412130042d44074400680910400400c1040000e0105640004403800d1044201c80790404543d8540d045602c50001204401660140d5044004010607101da503a000e1203426030038419 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 92767149 1250 92765899 92765917
    0x4030c050a14100c0c0b060904020a090207051c0309020109030212030409020d0203011d0412050f160605040c09060503100c141804060905070507020d02031c0c02090601170a11 77
    0x12040c0c1d146040100000f0345025080c00035641800300349100641140e000c448607601600320400100490220309208007070316003050010703040740140c54a40900105036480544116501e034410010601d80084c1c0b0409050017090174034092200d80c6041d0002030441e462070001074406d40303400100c03414900b41081154001c2c80301c03110664850f1811566107009400c244500001540086149214403010390349480c46160300000c4d0b4a44400f142c082142c00e50071960601850b03940400c02d203110034208210306d440151040f080810103281c60324010600f1012548208800ea0411105004a81c7d010582034036501e40300c0d41c000340707074400e9850031580d0f254903100c611869080050001c04025030030807400c1c18060180c409102c441d6494401034101e400480f40c2c2c00c00204280048001458811441b4210354001021170b803d02240500700c01e1b1900d08590100041101185180f0850804103241c0b03602803003d0826001c820910070786e914614000506108c3c846541e6014152480c1c121000c0e6144a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 92768399 1250 92767149 92767163
    0x10c1110030f0f1d01050712020904021308210307050702010c0503120103080304060501230613180603060b120604021201140a0c02010e06070906050711040e060601140307020604030c050a 82
    0x11031441180f8010303d030340c0010071007540081c10b40014150341406440c5c091111039984a0061245804c40702c001e4018080145c0c0c001d4007004040d0074548034484110150140e0700103801141d031008119032030380c01211410002a442030003000833081d000410348041d0354081c20a42c00000c01884c04d00d0a61040351104911394007204008424413011030041c501c40c0c0c0c8a0802041944d80321003070b207242c49086020040c0c610007001162442c1e4203040000e08540c2c0440510707840c00c45c2d140c4001400441b038011075034440964440c1d04209000d5a0300801c108203d080d10034032aa01d407003418290f02c1d51030050011340038243c03040540142002c00d5102c2890028030007440121403c0c0711130841d0250940115010040d800d0114401c0c02e250003054440c0286540d03160f1140c001d150080c00e65090b08004000d43c2d03810350182ea03065072030b22507001d1411002d150001415180c600702e0009403c1d1401044e081005110900410240c15000202c5a401503058217000c1a8119603180044c40c141440c0b40007020a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 92769649 1250 92768399 92768411
    0xd0c03050106080d02061e060609060d0c0203030907050103061508090a05061f05043b0303010803070c0b0708040311061908010e06010c0503041707080d08010305010506010c1110030f 80
    0x42203000c59920124501030303080c0e031b0241d00c882450645c1c040d070742180346030080c0501b40880e0306403900300c0003131928003000341c0b545050030a26031440c000c176200c0c84556805031b08004100901c80c2000e1140e82c1c090003013400d04100850402c01201164141c0c4651141444020408540001c81c10080c8241c000d070b2001c2140c0b0b1a02e00280400c8840080c956064a05048208080303150300d00b6000e40710805c1c46a28182d4a19000c01c0045182d4000321102c10300300c030303550b80310f500103038442400210701a001000003565a82010724046400c4445580031404144040c0821030025821900f00c0d4100d81e00000c41810320704002c000a0250b21451b240d120070001100c04d11a42d440d006103050341201c0c0440e0704920959141801540c40e01003018008009400410040c02140e0301c170242213201c1075100e0201c840103610f4141c0e003441d07c13040d08844004654490010020001c0034098594044020710300090359042c90307900c0c40c55111000300c0041c03291410109080c1d10324481d40c0301c0c3c7d40c1c4040c03a0405000c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 92770899 1250 92769649 92769659
    0x506120d090f2102090403180b09120c09010308091c0614010801060605070b13050609061807050109030350030601020312071106070f0201290d0c03050106 68
    0x8120000d02c01c2085852032200000b8000c0c0300c8041407550044030900c148150740c11a42000104d210040c8120f003448540f180300c0801c08280110035006d40f002c07a804c0c5039034540d0303101003003004000074003003031203c1d0311121481c5600c0d00d440351410304407036002424684904060000860003010001d40054500c8013035078810500005800a508100640b12401c880780d80329480d46003a55582d004080101c0c104020701c0c0006480502980d0748071384000502e464110702c560780ca40c02e006d0103a0351604035500c4002444045418a19081200342e605c0000b8841c1503c0d1100113003a031443c500c005014400308106400e0040e4007103010347e04a4890145800712103501d0100343d0507120100303440c000e5407c0003031545040402d01004503800740c20142c00450905110b90040040550010f18007130400c00c50404040164908100303841c0154801e0700c94100d03840240c50001d00b1140c20541c000b5840c103110782e0026001e02c94006209803d4015140e808442072a4107062410602a0b40020b040750301c0c103000055 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 92772149 1250 92770899 92770907
    0x111100f0902100801141c020a03052d0d050309010b0a090e190f02040b1f05030a0c020d1202030a0e0a0f0201020c0105040f0e1506030702010e060a060e06040506120d 73
    0x2480742c421201c803501c85041d4042140c00d480d0900424010020903420029280380040340e484002c0c8800303100584042c4c0e15804244800304030b81c41150150300c510381030302650b81901744102d46c00c1e449055900000c6002e0281ea55a00411790b841410701c28000007041c11204290020b003a004405441c0366500782e13850342c943d0000e00c41d00030011070b1801100300060100c8941c07440e1525607908003100c0c1d40384083c04d808000013404820768050744010403202405030442075204654042e001900c81e00d840b03240c4007101c203081d251000f10143c2190412500f1039101c50f040780c1c03810301a144211005032282e407020842002410501890b990a225000003041080301e603038042c0c0180c0d0710030b13425640c40140307c0d0010b40e1a4000c2d4050540c01c90110803090200d0840803900343e600004508803101d1140c0424042030141d070081da001ba0040c0d440e0981c10020721805c010142c3c21010400c010420301c2d1900c074030b100e5070540140c8031a02c11601c410208106513158050101d020340c900041d1401e5180348e04c4050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 92773399 1250 92772149 92772161
    0x8070e10020d0801060f0c021003150b0c0d03180b150307080307120c0c09050a090c03051005180c042003010b04060e010203090f1c0804270504020f0111100f 69
    0x20b07000032001c0001040251245040f151840f10a444200f0301f5113480d4208145100a43c3c07000082607999a000d50f140c400101079100100486280603039980054024981403d0880c98040141810504a0705129400300c600500c145c0d0020504d00c01034440a004190a00c40d00040c02da2500c503140303000c40c81c50800720040075540d2181c013407900094591001540c00d48100344003c3c042c00b1801074200301c2031205402c4031707034404410f034000205034000e6924600d00c2d505680080c0ca0b01c0e84070200329500309100d8031030341d50006022504081060024500282d45a2261010754050390320380c082042c00e001824031900703444840320091600d035030711031003960703090740051081000117101104c03644461750012080f144540c1014005101d00d034041024480040702c0f030160a41141c511540c8500070804000242010b040f908140000c00300d160079081c40b4022030200840d01d03a03444d1400303100042c1e803107910a400e0404282025152502232a0482d420f2007003051b510079560742451f40c05003080099074450703 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 92774649 1250 92773399 92773423
    0xf0b0102070815040f080f04030f02030c0114030c0705030d0f05070219020a090b03100f020a200a030311070506010f0f0e07120506150408010506090c070506060108070e1002 76
    0xe0325050303038610320303243c0e14070400001294074a5018080b80108102c0503854105501980d0303200d03e0000d62480c04803030766000f54030549000c0c040c40112300441c41d00b0f200c000003070030003460b00c013265081c83c055400c80c911003d080007c7c01c00002075500200a270500c140c134401501c554040281d0300851299102030311003118800c0c018010000109002c054030a0b04c030b4803840e00030b070010790380301e023042014002002c80044c16075040c4261942000141c840e8010000104141c2801607183c071880d0743c000c0c080b464000071080d503006207514416014400010081c41c071039010328020035800c00340220b01420b403264083c0a00980078070000440c041a1702c01241c0201c0c0c800c1e0090545240d603803201c2c000c0240060320f078240003c03050300c0011000c500d2070700f0041d00840000d00d1030322040c001e40144c61666101c0d5102ca115651a802084050720303145c0200b40d13020701540b0219140105541e68161204001000241803040c02008103610a20400c0c1036034015030080d11243c1500f03030110010350307101014024 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 92775899 1250 92774649 92774653
    0x1150f0503070b070201030b150d0e0f030c0a1b030206030c132403091707110a061403071206030204050c0903010b011e320409060e01050108010306021b010f0b0102 72
    0x10000385418000b407200111000b005070a400d080c00e603401100a031080d55440c03a0b12200540442c1044111040101a4203015a0300082c0303c0e00c01ca00502d0918400c2c2c40030200741c5e001400b02080c4100082a8000d4583c1d02c000d000d0031032046200d4220b1021029000a90000e8004c010001c2c004200e50007030030031954000b0850081560740007000800d4003079058107142d02c1640c10307003041d85034002e4014652003842012162100c20a41d10100c110f5001820180d40301d480300000745290f800c2c83e420340800b400e82d520303003180e090001343c004000e030f4400501750320204a4440c0002070001c40a910000c01396900400900c41410900c02800303540d00440f6031180b280d40fa1020354603045d03000c2c0041210a807000e0410b40b10504070550141c1e9403208030200b61000303490070b8800c03040c4030000d85501c00c0102c0d005104151603505209450303048411641140300042c81d0440144043d030f030070000507811a90703c04805a0ba8104032000c2d042d0159100c00c840e0030540c2448402d01d5868040d421085000000307900b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 92777149 1250 92775899 92775929
    0xc0c09010609050402070203010f0c020102130806160818030d090204050a09020a091109030706031b0302070803270105070f0e0406030f0308060319080301060f02010e1b120115 77
    0x4100500a00280324000c040381a8900811260402c0d4001d480440c0c0001c0000500c40c114070700d003500b80e908002c103100050f5800078004090158000c0054003074036060000b003e0703031f00c0d25214049503c41110711030424849158000b07000861803001c00441001c4400507241c603800d00c1d841c00c10140280a0080348a50b0801001031404c3c40d65105030302c0d032690014080d034030301880c003100e131070040c100701c113401103041e07406c010400080d1802c0080b4030003052280e400041200a01010700d0300100e5180c054002c26004010420100c2d030b90794141c9800c520002c1d145017110380181c02d0000b02000a580f001d425508040400c18255008001013801d17812649644004101c2c0000308400c45555000c01800d209418070a180482d1041c0e448a0f8444805001c031004130041e803520b0307104041102c10840340c2040c0000148502a44904400e56040c01070000703201841c0d206040603150103200c1907000a008208150b10f04030f54856210f11b050580c0c2c1c6000b000b4184501c000510310f0000c9000310281011500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 92778399 1250 92777149 92777173
    0x70812010602030c07060305150d05060108060108031c0c050c160608070203120a0504030908071403011802030604030e031e010e010b0102030c070b09030114010602010903081f09050901110a050c 85
    0x12044031071507036108001d0302415080110a50040130027803c1e041108440e048141400d03140c03d5482c8100700d0040340104081c0d071500d6200f0f031500754160001400c980003401080800940420003410145403218046a4420074110450307403800b50740d00d06200da202c0c1c0070780c032050840104004010f8500a03540c070249a030700c1200503a502e00c102d0050840d240c94460001d130030300c21640c0c080c6400c02e110345000c3e9901a40d410700c0c00d02e0710b00d651300080300034100c00c01202c8191500f40300f0f40480c1c052070030211807040a5600001e8540c10f004002509100c4d0750542102156024401d90241d4407840780420325110030509124000d0440740c61903c2190728bc003401812540c000010385580c07400030303030040c0f005605152823010f041d000608401d400d036484000140d1302d54000c8002c20b0181503980c0c000508800c032070600800000029014107891030080035140d0f5000c24a0a03900c0588500700e1012403503440d01c1386030794014080701c840440340f0100071484802c0207030f10070020700d20009500121040d0384c0703482d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 92779649 1250 92778399 92778403
    0xb060d0f0b130b0f0906030d110a0203030a171e0610030b04020d090203100212010b07030306050303070f0b060a0501050f0702060c070e040b07050a0206180309030a0602030a0c050c0d030917070812010602 89
    0x58446c40d61650182d100f4484e003a118100308403068030507406a541d142620b9010034a141c02540390880491060700d030408030079440d2a1455031284e071080e241c191958111010034202d00014088901030f844c0d1a039491540c50103908025a21200034108561b22414500610000d1448900481c071900948100c0c0c6580201c40c0261500c2c2c0e9240003e241e4141d00e8541c1590807540705003021800d041e155000016160b805002609105000e503c6007180f102e0b4a00d0180e401e06402081c8503c50412900700740101d1b40d2100540729182140a90660345a0150001550340d0150348400301e0603124000003c104914a82802401103214001a88803501c40c0601a10b0314091440044010ba10500c0010702900b01040c001003181e0f003001c00d03245803040940209003040340c03e690555180c0d40000a00c0108196882401c4249101746051420000d09441594a41e001039000200705038544a90000740011b003c10a00801d50064050356202c1c031510300400b80d130700141c0720700e00d400209400024500b400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 92780899 1250 92779649 92779651
    0x1509030a0f14090d0f0606030303050115051206090a060803040f06030c300f0203090a051b06070209040c0e07021c08010e070c061506210b060d0f0b130b0f09 69
    0x4604035150030042040240700032800b00a00030343d40d01c4d181704480300104031140304910166000390303000320f915030424100c401d00c2011143d002e030800c43e08008101882240d400b00e0364010604480600390703500d45000d200040c000d1904088118080080c00013a0404036410020850301d06440601000f90181020390300308840303203108003903520122000d450844600142c50b0480c4243c03080010031070401810003049800413608000d02d80c1c8550000b0042c00002c01040c1c109000c40d150301d108031105040812080d000d80c071002400303410b4180100c0c04000e040113004007d00984910f405040c544410001d540340510b100d50700000c1c48204450711502e100300d4003030b4140c2e02800b0300840d407038699440032203403242404410f5500542d5070801c21070b840414511040141003a45d00d05c0803040100040c0c00004102036050b0420900d050300c11551a200c1c07401355603a0b524241400542e00c0794002e0a40c002d0b00c8a1440198440084000102e040a450f80a410b130000280d03404000c1391000f03010b010f00590 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 92782149 1250 92780899 92780927
    0x1a0c060a0615030b060d0e06071403090c041802040e0d14030705030c03070c021e0406090204081e0c0306040f0b0601030501060e04020903150106050304141f0b031509030a0f 76
    0x1407640d00c4019034065000300d004080060100c078606080300c80024225052030407e4244c6400041c2071100d1507910440c0a40111301d80048070340707035003007a550142d540c1048072030701c90086803036280d00c2c540500681200c0c056242c01500502213540d001c814a42c5904042060202180c03c08600b0403500102000341c3e03101e692592a01850342e01c03005200f00f40c6130002840303030041003100c105100058588041e0404030400d81644940016281c2e410402a20030680111002c241f050008100607080090381e401040e500e500d0031741960800b0f5030414101039081d220039405114210500042007100540d400340540606039011ba00d850348001103040e03c00a02c01c80001800d00854122140b91070350062032020070040440e6075001c02041c510a40c0c1c1000d07400400403030004801c1105214a00c880d140c10807202c140503080c2048114800c40341090f90584100000395102e5028080382c4080000d07100010504100341c0e4145031070584e11359a40c1c0040280c0340051445445240b4007070281c0325806480c2c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 92783399 1250 92782149 92782169
    0x507020310050a0902031005061002030c0c0f0102070e0f1e040201020d0809010f09080702030706020a0f120e031006060f0201140f0406060b0a0801061403040201080f0601091a0c060a06 81
    0x101902076200c040d1202812603600b60341d940503c1801684c04000503100582200000329140c07402e0010880110030200c0302c0010364104002440704200d01194480c94000d04031540e1000e8904080100d140c454660011203100480310148090000d80c000500c0c03040c1d1540700550f00c401804000e21b0400324050301d0080c0542d200040000103540610b407071075800082350340002103d080e8036100728180c5180d2501a146000e00017078450550405000100c0a0159070004124485041d0ba460381c40c0005401c1c06003480190002e0302002611507103251a51500c001c0417500411080201000142124454907001c100c0c0b903041c0485250041c01448071b40803444c400c01312503644071084008810b000174400c03100156a944089010801b0724082c2a41588903a100c1c60303198100f26014207a160070204690014800780100f1006030f030312141c40c50340151084500190f41d00c0b0040180e50081c10f81d04456003040c448900d07121000c4170040a0940c03000700904480c2d0300c0c1c441844160484103207000d180004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 92784649 1250 92783399 92783413
    0xf020a0b0f090123040e060910050d030807090306051503100605060a11190b0a0509010908090d030e060c01020705060c04360609060321050a0309050c090103080307080705070203 78
    0x2907001d4010104c00c4c480c11241c1c040403100070760b200031481d8841d0b00204410540b9506000160503c0c0080b660f004100c0000a503006081900040b58070030700e40300c020200020040000c105500c96540c0400541d4451010b2016041411281501110a0010500a100e140030040300c076003031401440219200501102e18001c070220701220030500b004006d8096101d104034003c240d6001036500d00d19180281d4a55042e82001c8030301e4420f0341c8025000304281c1c1c0c14110290045000f0804039070300c01204450b84141096076140c141c9840a0300c0180b2540400045285038501006400810f0841d229400b0f80d41039603039408900035035029038001c008800c081b419403004524082a0380103020807101041170f0100c20303130030b0a143c2a01c015410071001e00d500c1d00b400b0800c00110120000040001141040c1d5100b211000200540500342c006010181c41b803d1007030a106092102181400000e89922800d42c1c60782400580c5504c144d51060004650f280010700700f80c4100300355410142d00801401c10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 92785899 1250 92784649 92784667
    0x91804020112140c0906120f0612070b04090504140703060f060512070b2515060e04020d02060319020c0307050c0d0c060e1c051015030b1b090a030f020a0b0f 69
    0x11130f410640d0480c0d000041001032106045420300000d02c602410108c4002c6850b04ca814460006a55a450a001d60001c4424000001d04009a500340c0380884400611690345003410319820012092a0078540204d8102000f841840c0d000700e812010484c2c000c3c0000c03590342081c44440607400074494450740101c042442038403500001412440f8421449a40640541807145002d00c2c50000c01c90b07000000810000d0340100038000c2c00010440e11240040b1841c064010905032883c40780004e206500000015440d0b0600d400c41410211410508548030381c9400c000c980d50b50301110080d034081c81120081c000c1031510383c05407005154881d6402c6109403a12505580940c04140741643c0700b0300f0400c400e001c1c1020110400001c50050008200e0380a070084240c003196042004601101142c48040c030105030082c1601d6005081c003140a0400075070340301600c00034000c51041680c0050f18440000c207105200100d000c030a8004c40d071034404565907241d10000c600c80c00c210b00c80380c1d800034040409 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 92787149 1250 92785899 92785921
    0xf06030f042303090907030c0804020433050418050307060b04060308121602160303080a02070204020313120318120c050304060906030506040606022109180402011214 73
    0x1c0c2103803090b00881015104a107005812990390074510400e58030118000c20b203460514000b80c0c012902c0d0504000450501000074440080100f010780110b440704800806103e1080b049032980e00900401244003000c01684905190075128241c440c50800d5080103c004046c041600242d600000030761810255544070f10142401f420003d6006584420000200d2420401401541c5c0c4102c1c05124078504901e4000c015490380c18007408540c001103200110300364000040c000e032605400d101c2c11075503844220ba4041e01c501c08000390041d00110500418494402e0810302251180031443c013200612081141164050642e00e1040f40c0700d040c482e40032603444542c00708148020b241c0440d01680742d84919142d0750055112100081e0f42841c1044526414814503030070450484c0c00703100c0c091a20f003000755600806000742d00d001610340100005124984112040040b02405102e030302c9003026000d8118040c1110168003183c0c5030b0700d0040030143e0341d2054060038180000c03811410340711035940407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 92788399 1250 92787149 92787151
    0x712030c05010b0901060f08070c020906130f0c020102131a1905071b051c020618010513030b01090f23150607060e0c010507050303010b030606040302040c030504030306050f06030f 79
    0x59010b5586081c40c0c0b226480d03094046028242a48a242e000410141c0c0100303980d400400c10010440030844500040e07a40c02d02c02038000b5011681d0f0361010100e82003e20041c41ca156801404918002801c1301458064000d050640c40010254400607075982c8080b26005001d1003415010070300700120701c60540307508940a1241c005191076400d0106607070b1350940f41204603007178401c01d41020400300303c83c0c41c240701c189501c810070300c000f03815046081c1c0c04236002d8000d1702c081e0000100c01d0721294005901c50401d942040c9a96401200fa007a903c4c14401003050f001e01480040608000d8848503070320a0b40100058494410768400300b1003c0724268125004c0042e004540d40d10700b481c854006075440c100a04402801800b000560464180c0362070300c1c0403a14030304a81448028002d400114101109481c1110750085445640b40c1ea010300083d1503200d1030b04001e51040c5010303007900b802503041d84001c0c8110f100f034504112184c0c85004101400b0710171040207601100070000108901d84d2180c0e16 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 92789649 1250 92788399 92788403
    0x1c020301150608010306150305032a0a020310020703020a0203190c050a0605180a1d090d0e09071112070302100b0f0d031209020319060f0501060e1c0b0702010b0102010e0712030c 78
    0x40c7c6030030b41c1741e82d281401c507031040f00741a80c1210a40035541c03811814043c009201ea41c2c0e4002030142c0041d40d80825103c401a12420400701e9011034070109150003071003156405a4010144e8640c030800c651269002d400c01c0c40e0594078543e2413075010566091020703e010580b082a203a103405c0c69108420a100134003c40c0030107410004456000800300d40020203800310350f4201c04a5801407034081c03101464519040c00503c10001900142c10a980b25660340c2a0070842c03c3c503181340f2511104d2016480c0410124180c50880c5000400c40107043d4007003100405290141c50a026201c08102003008030300c0d480b01041d90124081d40c0c01c4000074000d00c081c070304c208800d0201140c0001c80760000390400405460220345241a0008001003000c684550503036000030b00c00070031041d41031010042c00305014041365400755008400a041c01030069942c40712140d07121a41a680e03280104009020300311074010f1a001d90b0034251450200503010a80e134050341c080c0c800303030070300d040164408a1b1121948001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 92790899 1250 92789649 92789681
    0xc0a15060e0103150f060f0612020702010e0607030c05120a020c01021c0f0c080415090b04030c091d01150f0e0103080d150905070518060c060403120204051c020301150608010306 78
    0x6417a15070406018540043c52601c4061291914100018005d08000c00902c502c3c20710411a840040c0e030809690340c1c01e81001d9a403a9254004e610702560106e010740703000342442c0b0944c0400400f40300079400a180304c05540d0700b0b0f5203104003050016070303449a422141e055103614040c085000745e481100040c091000901c1e004100c00b0b040d484c1c22903103034001d40081d80c1036600201030041d0b564200301400020440e010400e40390034a5501c1d407104da83c00c80d00480c0d81158507913040c440c00041041a00840d642010020801843c1d0384d00b406820802c2481205401180081c0010741e14103105e19081c12a504165840d18080700c1c140403800410400700201c120801c0c102c2e000c17400124a20a06101c6e1169444682c0d903064140301c995611440380d205a88030b0b050800c64440c44043c0030500e0b541041c4e05042c00c403501461b03107071040d02a00898002980141160200c840340e000b0484400b10018007c4e002000312411044441010319164040c507804140c40e038004000099242d0301208031201d102e80 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 92792149 1250 92790899 92790911
    0xa020a020901030602220f0501080a0603080c0106050307061d120f07030c050f0d050c041104080a0602040e0c03041e0602040b220608060a0308030a0e030c0a15060e010315 75
    0x800034000e8002038000341c1e110350340440e02c601c9407020741059202c1410344245214906d03141828201c0380c0e403058098241000300382008244102042e8208078050340d0301004441d01c40500000e0280281010302c5414403a00c281d035800074050340500c101d01010302400c01d06080b04c000d01e40c2880788074080b1044582d454400d1841c0b6180d4420140644005148210305034030b0326902d010104012201d9040456205000504002c0000fa20016800029010545000ca4040c0016019558a0003144d0020001e402007294a0703003040307441d50062050b1800d1401c540c1103a2904180c40005000c22100104414190f655081da103259151005180e14030900000d0b00d07042e00c2e240f10785003030781001c6903140e5a00c0c0ea44202c3c0d118100c1c00780002014002902d040c4029180142c0024007441d0b0038880a400ca00300000843d200420a13040510640040ba00b04c90340c5000005900c0c3d59000c08030001d0f038940866038100784403074016009035030032136006a4040510742d09640350b4803043c0c28030b0340180b400755a03144 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 92793399 1250 92792149 92792153
    0xf0409080909070c0501061a0304030806120709060305060117070308181f0807020a03091206020f03090307020a14030c040509010b09070905040e06270a150b0a060318080a020a 77
    0x1c2e034558842c0d181035446a404080618140e42500e0f0260410f2400e081e003030403000c4194048034150380d031064152401390025121400824081660b4403c445c4541c001c1450102c1c0d54074450300040b08681c1b281c402c9401c142c0e45d5038030000d280041070000d109541c2014008101044451029202ca440020110f1691484400005003205101480b0b07400b112540c003030511030203030820000355000b01d8a002416400110395070040041e1180d02481c0300001c0255102020f000050307050f9019035009800039a41da09151a0311030b074903008403004030f118a0a2400218200c0304400715100c07181c0c0c0c090010300f1a40b094400308005010011700c002001e6585d04180d8010b690788849041c050035a54841031a114140b809110981e0700c07100c4002d206034044418000c00010b8900b03103000c43d1182d40c1d602c01403041c1d4040b03100d007491036071003001c1c144a04c1d4840da00ca29070001d511603000c0c0081245c803c80d21980c0c40609030141c42c03040700000a4981450b000e4000f03c1c1a0314010031141c0580c7c8140c0d19121095 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 92794649 1250 92793399 92793409
    0x1180204140603060120100b04050601020a060c0903080d0219020a05031219150503100204140f0301060f0905070905040b060702010c0819020f010e0a0203030304030c03020709050a090606140f04090809 88
    0x50149003490741f004007004c01400307031842383d088100c0e4281d42c01c1c415072800c0c0d00040d41d909a03508004040030744e9441c070784114902c107100b5600074503840b000c1d441d070b201d119130030300e402030340100d20b10615004440b6420450b59000051200209900c40042d5041c18050440d00c114148002c0400040402c60400d50800d01503d10500c2c014044c650b52070950a82090f0500d0300c1c1600410803041010b10421003407108040380c8001c11010441200d061f649289498003180c00740c00c05070b000d00c8001c444c605000c45e01c80c072203412880c881c4c05241d540004855580c801c010980c1c090350b2115800200811151025501c1924505003441c0114038561800340c0a0f0307601407801030045a10401038021040d0886040f0080c02070f80c11011800c0c00400c0010126000a0384030722018000805008a4400001c1010300900c0002e000781202c0c10100311034580640110b02500901000300c444038601800400c81004c641742140c04460040c050b122040c0e509801d110040c14810800d46003402c091050006907518 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 92795899 1250 92794649 92794697
    0x314061b0c0307020d0602070512030114040b0d060e06043804020d12091a07050c01050c0a1205030402010f022b020c190e0a02030c07030807200303011802041406030601 74
    0x841d080048e513a85050814a003000a411908825040200b004001d0b6110403d0f560000303880031a00050016001800190031480d071440c014012401d107050115101c80c04580c01d0b00c01d074000c0b680b013427141d40c0f40100f13019040d103808200c441000c1c0c10070b4501c840c0c02d45140d80680c801d00c00762030300c2c4000005403600351085070740d40000c00001380400ca00380100514402650508240031012509004c0c00d51740e12600c504a42008504010f00403484000907002044000300c1e95400c201014007030600500020074680c402c80707050780810828180c2403021840000c80d4440083c501e050b25260717030750098000d005060b41000800462159610342d405580d1804c80010403403581c1411244018034018039a4030700c2d0300050440409606c14410410741f004440111001c2c81da00d03140005455682000540c0c919002034003100039940365602030f04081c0700c00002103060707c0c00503240244402648042c44d00703034403c60003003c00b2005100c141d1800d50400f840a142c100c0c205042c02c41900184886400c81508 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 92797149 1250 92795899 92795903
    0x52b0504050d09050102071401080c041a0a08090303090d1b0507090c0908030f031906030f0615120c0b0c01020f0c03070204051005011e140d02040314061b0c0307020d 73
    0x24500d8100e0483d00b201c0c080d8000c0c0420300107440500e1800c3d26001c55202500d03d400d060002d684006103541000c207044a028020000d01c8045c41e501c000e030207134000d400620a1401040341d04011801c41c00d00041524459043c2c0e000505a07403030029001c0311094525070444045c070244cc098440098804c0c0080310150240b400c000600c0144140c2c002c180d60100d61000085800c00c10444807490f1280c01140d5000400ca0981d96207800c803154004002c22080d0b0000e00382c0c0c6a0803808404001443d040310700030842e00b01d03c51110719224810035074040d0700e6500080100882510030000240e20390302800300400311700001424006104c2c1900d02941c08201300c2c4446800002d1600110300d001d1007404d8200316442c00500646042c1400a0515040c541480060b150707a07180307050507544108466100002140b180302e0700d400189007150065041030004848000e110380768070680040001e042441090410404c41264600c02081d4240768401c0481001030300040103007402603280d820003a00614 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 92798399 1250 92797149 92797153
    0x110c011409070e0903040b07030e060706050f0c09010e0d060b0301060b130602010507090b0706060f0b0702040e060403140705011107230115060f180b0705070605070201052b050405 79
    0xc60714084081c10329081c0c1e0030290005010905001c1800360004c2683d00340c9001400b043c2e500c1040b070900b03407501060090a1540803c0004400c4c4c02c10580d5008680035018052014089484500c0e010710580510404c541c0012030391501001145403114000891714000c1000144e2050450086420340340c0a03044520503003400a15481c44500e10030044009000503c002c000e5814143c5004101c0e4219105121950101064071018012280e0003034004060b07501059410725030b1044000d10302e4018403000c0e8401c52821900c01006400824811f102c1c55060f40c4007000036000c5500130300c1a41001c40140d6a42d969510400c081c0b246042c0200004d5002e03481d980d4600b951003401290f50020b04184103140e9050100c031840702240603a105040d5086420406d112030508c9004903542d0b6502503249141c944182c81c0010728000400091451500560584002d2074594005854a10032000002d00003070040042e0001510003070f5110700c00390080000b140020b8240c1900e4810b44030191015a10b40d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 92799649 1250 92798399 92798401
    0x3a0506040507170a03090501141912060b07050c010810080703080714010b0f061815070b01050a0e01030b0a02040b071103160501020717030403021509092206110c0114 73
    0x9408500c10201d525201c3c8005084d0740c202a81c0003044101d051003482d040c0800b80c41202845071802c025944e00b83c400399003180c0b0074004850024120307a5480c082d00c8000b440e1504c01b2412401da04212041d60350031600400380d65420800465500300c000b030020240c50059038000c25854810b002c07150082d80a42001c58070b40310a810074208545c400d46094034983e1400340740716026101c588882c03140f400212401501d42000c00e81860841a40b00c031401d41c09845511542d4900c0340c1b081c0a0904540140b8954042e40e81340c5052003000c5145001d54030040412000420000c4c01c1c13980d030a6400010f094000d420b21b56607518008098000340301c00c61f0880140020006076040070000300d04a0303000c0142c030b120b042d072800300080c0d264901801014545004a09030180481003001150000c5a01034540c00840481101d40b14090300061f91b281e200300302ca01c01082040c0c1c202035500d5615140c0c0024160540c0103591140d004210380752100060310000d11802007603103020301c282a01800c3d102d1180e542 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 92800899 1250 92799649 92799659
    0x20703080609010305060a050705160305030f0916120c03020618090f011d0604110a020d0e01020d0f0503040c03020603011503060e10030b040302030f040603020909063a0506040507 79
    0x80d5020003010345000d80c0744000100082000080e4041e080888140700080caa00c8051044509100303030841030035081034903001101010f80c070400540c420b030bd03c0d4186038600d85524458580360000f090190710070f8100c181007404894003c2020307a1102c1d00c22030484100c0c03a941d07030108440c5d420000a24034900e04200c41a2040d0802003030b0b007641705401c9500c2c0f41e415170404070b48032618260000c409445854010000d443c688940d40030308114910603140e20f40383c4800c100000c0d60b4145582c8e250b40045c0003210b460003a54000581c0095100c8592100149411040e4080307a003608010410740b0140b0801d04000b001d602c8010045003e401006100b041d05441030a003e402e0b6602a0300070b04202c0540420001030381101c80880c03060301e600c0f1440e20402e4841d03007003c920b1402030701c1075041460340020300003d00c6501503005003c1250107896146596548104010303001074401c1181030030702d00181419825100111a40740382c480302103170500484003641c0310b003813400b001120b0484040d4051081400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 92802149 1250 92800899 92800907
    0xc04081005041a07050a030e070b0409050910050405060408030a1401090f0c0203090a0504180b43030e0a171305150702010e5a0607061b03020703 64
    0x18001000d03080b0f8001c1c50916540050540c8100000c06040681d54103c503a94100240480001003e810030080e80b11a180c131600c500511081d500070015115043e94885854150b000740d900c165046005414295116201c6080ca5407000b01102c01c19540c4042c9a0018040c136001103010b0201c440340001d048411100312400c5461245405056510501c0094503640d2103030390f860107540040c1d4000c02c03880b021a038404c2031641d92580041c402c01d1000c08000c1041034a41c40c00300070304002001074100d000741c030001034280040301d034280d0703030303180d03c42e104880c5207400794215091200760401110028511034031111120402554001c46c0141e00080958950004400b0140601000c503500d116a00c0880c14100140c030032218000d06104028103940050380c0c42140051803101002082c04080805038034000030204006502c01a07403480000485d00d503a1a1060301c4002c401800030384126280003c104038107500140d50441d0705545503a00e90b00d0040e604021512406910744000d47c4424591402078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 92803399 1250 92802149 92802173
    0x403050c010e070807140a030f0302010209090103030c0c0f06050a030b03190303020c010b01111011040909050c0102010509030c1b030c10051b01020909070e040e0303010b0417010c170c0408100504 86
    0x46071b11580e0840d00c15544d86008030075080341d0340048401025803440c0f9090740039000b0741401541c846c40c1c0e0700000080c17540188608a07c5880b90451000c055295040c0c0501e4428501a0800040b0f0a100307800741640298020f520307400c0300400300c404440000f02080311603504160308400281d0089440543d0030424020309403035141c2420444142e509005410341d60716080f21500c00750a464844154154039140129409090350b9202030000f28514205190785001c0032416500561030b2030f001905560001c010345007021204800380c0f00386010f1020110700400300b0a2965418000c049803440745940d0524901b2041209031640c5072034018120080340c0201d02c8480d401c8241e401080321400b103a0341c1040142d0301c1440c504010309040314010110b00284401c020f0900355100020020910710011006003040701c1c614140c0c1c182001942a85500b030310194440b01011070304110408803140009036480f54044000c14000e810503039610092803038200c6040f0603011003980e171000e00003809850f841c02 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 92804649 1250 92803399 92803409
    0x16030e040509120d1b051c0603024506013e0313080304090c09080d0c0f0c0e150301090c0501050a0203070203010f0501050906120c06030403050c010e070807 69
    0x4200d00e20707250040b03680725a403071007142103c4507000038400745420142d07000f4411810840c04189583da0ba07084007400e00c0c0d1101035140ba06641d16050f014090206008a81c1601c0d03005d480c0e82000b14511686c40848030211756208003002c10307200c103000b500c2d4845c86c841c44841ca5148040745a41440b000244c111a4480141e550741000c040c8601100f80c6d002c0140c2d04e460240c160094203d07d480c0000d9411401107001d5020910380c1c1c2100047a000c600007014005841002008205a10b20a20283c0d144e0314540b2520005801913602c0300d5449014450484c04540118814102c102e80c65607415076110a580113403200c140e01c0d400344109021311071400302c0416003d4000b004080303050307142d0030212210b91041504000c80080c3d4007200303e2091069940b010341c090300903c84d41c40d4140008008e4a0709020742030103211051700040b4180b40c04c842a141c11a24035020780341c4c3c0301c2d4030801c0c840c8030340c00180244d09000e8208642c0c803045c8401d1050301f20151040021308801c07814200d01c1801c1000544c05 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 92805755 1106 92804649 92804651
    0x110d030206010317090a05040b010212030906090118020108150316030303020903010e011806090305090a03060515010e01090b0d0608010501170f0102180103050402031216030e04 78
    0x1d074140d07442000000d02d400c100d030101c0080390282d0461a50b02a8036107004001600f0b05e940034112000040c81951100038000b0082c21240d4000d840300619903100d041004006c21003849030301c411440c01404400d03402c59035000208107013409003000054200b4445086c4c5250707030802012200244a08500c1300959407803c0140c000e400240c020f81c080d5090603070b5400442818420444c54130076101c2c04964850441c0c03070b140024210800100c061101c200043c800c1d40e41d13515030100c001d520036000400c182c9840385405241d01c070580e03034440c184140d5104081290f0381080c02c00c820b544090048a844810140692000d42115800080c01c0e51804c000030510469a059030350f40c103520801190340c400a1010010308034402c2e049540d580d40803000c012781e0158425002560003a000404480b40d00180c00e440d514150f0041c46a40b0f01c2e000908481420903403c40100c400d88402224 = true := by decide +kernel

theorem cover : BRFrame.Cov 92625899 92805755 := by
  have h0 := BRFrame.cov_init 92625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 92625899 ≤ n) (h2 : n < 92805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
