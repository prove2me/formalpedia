-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5410
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:46:56.687144+00:00
-- url     : https://prove2.me/submissions/da678406-4dd5-4b1d-b7dd-9a38bb5f77ae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 972841726 ≤ n < 973021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 972842976 1250 972841726 972841739
    0x8060720030405090112060b040506060409181205091e0d0b04031b050303070f090e1521031b160e0a0f14070206090f0d050f1c1a0f0a 59
    0x440c0150354802510050001091a8407090001c07400782c980b046c1e0702c050052003880c02a055905040e00c1c82d0150341018140700b041d07142c881c191020354135000d00c0803c0360300c481103023440c0c130340c1022074041c0028600f4022031410a8005005200c40c0c0b4058a0340040803060ba081e40b0514503171201c00c3c541007520100301601188514211940081c46071134442909a01e070503041000761050002130b6600e0f00000300740810960801100310001c511800c01d0550319180004040b170640c030007007030039840c00e00d0508100159a9008081d02100c13107220502080e4902c0c80e0f441913581d4008010b0300221000002c080240588001081c018000c010010b844c407050500c83c2520b40320b08058908010103455042c401c40c4514540108081900c01080c070945619200200070f03d000c1003e010420300350002c0c0c030100c00c03c04000c959440d021300142400c942e03880b400c2d44190f40c00d214904d8840034086440c084080051001c1e00000c4a8034841040c0d0b81d40440c501003080190580b01c068950b00c43c249034020003c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 972844226 1250 972842976 972843017
    0x30f070303110c0a0b0708130b0f0612240109020421060209030111120a14010605030601020304051f1e05040501030902030a120c060e070617250513080607 68
    0x60040b001000350402d800c502c02c1610348100c0c844100c4510440c41d0804c81d80e2540481d042d540f200c440c1034a00308100e4141c941071909840034042600c5440c5400000b0501c4d100c8920b1480c0103408142140c5a40e4200c0c80d441c001120b89804c20380724018680c00010301594140240c0f01a5075400310322480d50701184501c604182085e8508444280d000d10892100d0f55080c411508501c866091607640e070a90421003e41c0840e00030301034007946140604584880e8020762440c0c0c1507c0c031905200d0398a45038400140c0c90360017107500441c0d01540301c81355107801c5201460301c080c006007c0d0f1140170880254100f00c101e1803406440440010343c05020402c500c0d0b1107a04000012400541607070324101c80c0c0e840f0202048248003004010a96000c0310f00100140c42c484d00281ca01003202500c010b5080a0005200f09080391000101c001480c000c18100c0d2440080c000d400c0300e811544100103441007201416640000c003030204540489040041c901c13001181c0c0d41e108403007550381d01990303221108200e004c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 972845476 1250 972844226 972844241
    0x1020c0913050a02030f070504050a0903091806080316050607020a0519140d020303060109060305011512020c060a0f0e06011206020a09080a06090215272202091002030f070303 77
    0x2c2910812440b1009038405220782c0150700321110181c4119400d1405020541d4806031000e6186440c00d40c1a0001c01c0e401510b0000340c5400d040801d26241000700d06201400b035a80084003903000002d01c00c40b541c4c1003400c00c00e0703d803441502036445a5603120000da840c3c407e01d04010382240c008044a04d2040f030900318020095100da8482170f80c0602d584006490013501e0514600560700000500a0b00d60b000300441c002032403285028000f940c1003c1c0000407002a580c00c0130240841c41d4503080d044443c030b1301940c4401174604225a164948403000f1400b030860442c549002611705489620f408002062013816518208105d0007885480c1e030f84e08000f0b511010a000400122440110b41080b05002e24200c03e0302804001c10f86140c94010000500c11200380301804402c01c00124082c0b807814807124403510003039103000c48c0c81d03081070300818484041c00892503d20b0004401c022003041c00c59020384030500041d5014042d602d021003082c4d0b03917440750401138650804240090000030307100e0b400142c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 972846726 1250 972845476 972845483
    0x402090901090506030f01180b0f152719110a0519020a0507060e03120a1d0a0b040e150102010507020a0b070314162705060c16081b01020c0913 63
    0x85007400a031b042c0c0c1e42140c0d807a0303c2d18224a204980030a017801000030190b0381020510441c6900c1d424410010203891194443c080e000700e0b01c2c0a03611b44141c101083c01040d05102c080700120358270b006090042c010103a000c03208040c40c600070001800700710305420390f001c19009450f0389250090200500c0813a032207046801007148900292000050414400701d0000d002945038050425641c204141c2803120644405070001e10520540c0849a8007078a692038000200d501c9400c400058004038498240c26080400a40e0001400140c54186a9015440345111540420104c664007004900f6640151414401031f0700c4048960041448148042d0b0804040d0900003910039114842400e1510112090b000002001c1c02076040c10390450b1106030421030b13082c01c004a064046014038000c0800e8044c00e07025410100d28210010000c1000c0d51842c0c11504000440369640c007140c0d41d440c0b82038080001880c40e40d8040752401c1d400010007122140d40200b000001d2b544a1000c1c40d0042040f11064 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 972847976 1250 972846726 972846733
    0x2060729071416080d1b3c11061801060b0304020a21061d060a0605090c0f09150c0708070608011a1903020d0e03073f0e040506040209090109050603 65
    0x11080c1201900c03460780c1c40108558a4100c400880c24003074840c6c4900c1d403404a041c074440803412180885a1031102d00401d01f0600782d000402c9101d000c813080c2809001310074161042c031090000c1e41550902440500004034000e0000079224040c61529010903513000b9001030b075042d400d10118160640245803200c1124a0310710100481c5c8a00b801d45c0d41040b0850115460b051061102c5501405001da106a069406001c041c0c0713020b02040d0081002051030015440109016000701403c40440b0300d90400206196091120b4111a032070952025002403800e01c100080080d041202050b51000c407841d03030f2203201c0da0341c0c60303c0300024900081500310f44450b80100001102001900c0010703601040c581d60058841221250b6002200c0c0390030101d40c04c1c0e50091000b10001226811403096034080915449404213400c00c00e400c2c100400080204910408805442381d140d002d9081203081c10110f40520564076031308140002c9224111104d5003080307840c00180107a0f403541c1c00c210340200c000f078204e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 972849226 1250 972847976 972847987
    0xd0b0c0c030f041d01090207170c0c120607091e140f280605070206031314150406110301080d0e0a3204050c04030f0206072907141608 59
    0xd4011a8020f0b0401c90504901004c07102d9000d11030030049001d4200d200342103107000d5040d110380c043c40f07910b01e146008400700001c4800344e0010034003000c2c030440405081020b010180000944d1030341401c079486d80001d000c0140c005081d0a0288800210506059000349094100b188845180c5c3c400c02507507402882e0010302030001c0e281c40745807800c60300c440c0447c480151200b484c4410080d103254415002c003e002e03c0710201680d01c1c031040ba2781115000400030109500c1d8901142146e00f0034104420350700500c1c0002420241c5120f01764403540c461041000034800b0f01211007805e0000b806030001a42c00841400c0d5441c1c0920050b13540404010304680c40e107649c840c1203044000181000103c0e80f03801c80308420310f008200740d0311124808100d0381486945800040c01c080e5005078030016121503000722982043d03403a6103007119a165042403103084407050442d00c4a5041846101c122070700000c2d600040c1d2170700e201c0d0800c10741c400640c0c5001071a026151409441483c0d8040c1c080d60034140c00c00c030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 972850476 1250 972849226 972849247
    0x81b0f1017270105060102010b0a0803043008031906060e040c0215191b0e3601060f090602061513020c0f1005010e0f0a0b120c0a050d0b0c0c03 63
    0x22501e414520350000f0400f0305d0840002429500010803041c01a8245d2100b80310100f008025241a03812155140e0742d0001c041100c812480030b02800094010021081c05050181520003903100b5454034050345550070140740544101c41042c450f1000161a40030302101c24517280e0825065a48244121401030340e003200d40380e200c3d000640300c40c40082c00745002c21811003107d028041111040d040040f10b01c0c107148101500b00c0d42565050780c404d4003100310020311480344502d111000124401349002c07090302120950306002c801e000b1040860055030303401c40303860720490143d01a100a80c1c00b801e00e81d15103122211040301c50301030840d84480c40448084400d100c601c0508501030740305000b000c60b200145407103070070301d000310a020015034104001030090310011410180c01220200b005c08160b951075540c000240314000800d90300103844800c0700f600d68800100c41003500c4080b0344050489956200f000340503a440d540c000c2800c4100c40c001840c0e0307940000940074501c02c40080c1d0380b03010200c0e078 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 972851726 1250 972850476 972850531
    0x1f1d0705211e161d011403160905010320010e010e03010b0d0503071202030403050a020d03050f190905180a0c090305070b0a0201050a020c06040615081b0f1017 70
    0xc0c44030116800503552480d00900790f66107a0051040c40020020b401c5840d805980d103000502400c0206219103940034069201009000d1041c0140703c1480303401d60302e0300c0384400a03050030f21040e03426154251080d034041c1c60303941502074450016100d00e1403d0f907000f0015200030401081c01d6905569500515542c0e1711021540482c3d548518080c5981d511949420f0302e07168412050842154000d0105000003074000801e15007040d0100c5078a5294234040c0380480d8940b01d840742d18505101e0214041c00c6100f51514100702507401519403070400c60700c8030f0a000702011455149000d80070528040f410045c4142c1c06032968510b03030703c2c0003040aa200d803100d6107080e40e0351f440034520300130002d4980c074540c0d42031040c40d81001c0010010b6280010700009565034400c0034002800c1c040e41e90750340d407000710005020b200082a68600303a604540c05441ca44036080c1c960b9040600480c1c40c16282e0469107080c0c150900c5401c0300c0e44540b80440b0002204a2521364000c010343d12094030001c0020601c031822 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 972852976 1250 972851726 972851773
    0x130608030c010213090b1003051b070f05010f0b130b1c05210a0c11130c0207081002030c160f050102031302030d03050408030601111f1d070521 63
    0x30001698504e480300440d010110b0a5002c042c0c0d0602c1d1483d9255507a80c1c081c20310150145600e0042160344a00c5008240050396000e1111006000030302c403070402c2520040941e00e00d00841c000c01288091050078010385102d02c80c055404a514070346459002c1b03156002a0308008040d00c0103002c40083c140c5100d4400007200c003a140303075008102450616103006500c2100c0c00803105114100161080c003e08000c03248200100b045404d074440c441710791070300c41140f0500e580001c0d06024100030309401079110302042c06040d90790300512401c5074501416001f180d02851509600f00c4c0f800441012442140c80941d44c2140e9082860500030701181c402d0010b0360041c14220700c08441d1044510400d8a844442d084030b2003410f00348003c010100e0034010590358000b80a0070f01c1c6001120003204035003804543da0082d800d4842c2e4560712030320001c181e40b01d482007a0380b44840011030160f07070b503c5940d101c90900c26031364003000c84000c900072103802c1c03041d41c4440c201c090100ca8800010398100440d40100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 972854226 1250 972852976 972852997
    0x40e010f0816030f03111f0515010c0210030b010c0606150e0d02010906270305030315011b0303020706090206030a0c080a090f0809030a0b070807020d0f0503040213060803 75
    0x3185018054003209100000c02400c9400702e03607501c00d02d55528104100d0300b581010701801200f0f01000752103c414441c03c81300c100e801a40e0000540f144d1408401000103541032441886280503510300395028449410003507400605450041d05c03001400c401520b8411021750420081520140c001100c83c0181805000180482e91969040e010002d12a42c2c1080141c0d1080806038000000341c0d801103680720640b1107518000044500a281300c0901004484400381c001f090b118002003440300c00b2010b140a0300c100c0082c3c02454070f0300c400468403d40454074852400c050135210400284c020350040200710b11901e8041100c01082e000a081500102d0300d030044180c46010101c16240d1107004154840081001000040700546030351910b0703161a4401000d0840c00100903206540800c550140c55900a926030000d00d4541c1004001400070b8507008058410300c1e01d00e2645174050403a440c4015444c2d501c840c210b0703595400f00882120526103003003210b81c0e00c4002007040d120500041802680 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 972855476 1250 972854226 972854249
    0xc070b0c030c12090d0609060e0d0909050105090403080a05090c04060e07080106050414043909050d0b15040b0a0b0a1b020d0f03351e1308040e01 64
    0x2c0403980c15041c010341c5a10800c200c10100103030725440d0356102c02e0345416500f080001800e2242031070108003d00358104054680c1c4104000350304280e5000e0004c0c4260b0380b6100f810700069980d44240f0600a00a03a0001c3c0800e556400141170715046030f00244d0b00040d503804943c000d000d0360001c18111907003a001403040b81418000c000300c0c46d03000001107004003000e01e40146002e161014800c0307216280c401c0d80d03201d151501c1c01c152042c41415007000288002c03000100b42040400c207080d58a020b45c1c05c440005c60400d4800180901c1c240b1050304041da000501c44040e0b6444096038071559000ca6143c0360700c6136031100040080c0c0c880444000142072180b10099450b9545540900012921405882004071703050141006840340460000f40503808410350b06050301e9440c06407406600f540241039501c1d60744c80c8100c0051540900380c000d01c00146944030719504ea09281054140d080300a52004001d0303100420b00c01d4039240d4201074402d009002990405494070072208490800707a105445560 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 972856726 1250 972855476 972855487
    0x3060c030e0705060d020a0905040f051e040507121509141207021804020d06110301030201080a05060306011401090e010b03010609080d0f031e0f1b180302060c070b0c03 74
    0xd400d0710800e800c90403040300601045191400103940c40c4600090118000d0300440e0b1b900740d441c01012848064040248203110f00024001c2d410300420085520f030a8410144100703810382a20001c465010b182c0000242810300d007003c096120580f4916002c4407005002c2c0e40c0340380d0404891042005c450300c640202c5030503080014405261002c0c0310f000c5091540d0402c9840d0059481c0c0c212a510200d1100b13000100f03580e5800010040c00106002411003410100448401403d01c0e00440c107980c0300b600d40703949540340d5141035400c60b101107901c1601903100368014882c2c04e20f014844004140145071405500da10b800040001d86000c0c2d04c025a403420105c010b01090350018103110141c010180142800d60070500d0007002c84420720965018141d44500d0b000c2c0e41071070099103560f5800318a00c2409103a111190300401002025100d008604040c0240118a4816004284107024880d0610784071420354082280c1684003403000315480c480d5070710004802c8511030203071007070f03400c2800030311b840b00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 972857976 1250 972856726 972856751
    0x408030d050f0603030408100b0316030c031703090c0f0f060a080412020f0d0f03141321020a02040b13060602030706060b031308070c03150e2b1b020603010306 70
    0x8040181c14580b20742c10611080c0481f840006110114400300000400d00c468510082801c161000341840c0c3d081c02c1c003410100070710030f4554250044a124a4400e0002500c80d400410140400d444c0c50000d03030416200040349241180c5418103001c4001d200d400906503000c0011001d500c403040d09008940100100401d01440c1104075480e508680040c00003440c5e007088403a01c5540c0c8040390010700000360303050410340340329502c000500404000041c01504050765500d410a4600310111008280d01081d06026040c50710703400400039041d0000e2600310078950800011707018400030282c05c200c081d41c1c42c42c01c544490181e040103004c01e4014583c2c80601741070010030340340d0342d8100030031020042041c03001449464411500158121402a40b20851407401340e022402aa00161604c002040c250400f1034840d480440300b0040001281c2070030781d94140d040e00f62843c00000050100c128020462000c1c081c2840c920402d40070003510300b406050360300051a6030000c1e0010b0b01c485546540b20580b9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 972859226 1250 972857976 972858001
    0x30c060315130b0d020909100c1e020c01120c0c02060430020a03080715141008011b0c08040f140906190b0d020d020304050a060b2e050408030d05 64
    0xd942c1002c002c1c049504400c0c0030803242900010000d004090000010740440030a01600410100d054010300640071401c200800b081042000b0110315200d15151450281c0001580c1c4081103060f128000b10740f0907559550300070035501d00070700f003400032000019005a50b2134005201030030f5464043d0000d00162640110951109005441d050141c1094240940c4d41c0428200407aa80008144c1e40d0b840d803403800c030800700700c8107660741d07044c1341012802e221409500d0b072118480c05107880e0702c070f4200b5581c0281600740c1b2004095409543c00d09462080c865208040c0024014040c8405601d0190b681c9a000502520b1707900c05424020780b4182d40c40545072003581c540d080802152003020042c0c0300b40341e43c04042c006115202c50300c480010344440b0030445805641e200c5031840c40c11901c84c40c0c5070078066181c625190307044910915081c2c401746240b515041c404400813005191503803500d41e582200003105480e00c846010301009200000b85450100010310403000c070030001007403c0c02c100d03244e84071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 972860476 1250 972859226 972859249
    0x60a060b07210e1e100c080d1a1201020306010311030121062d06060207080319021504080d14010b0d1a1f080604020702060a0c02030c060315 62
    0x5003840800c91075011844100d900700c40d00300381d034402d0589003a1a89040e508200d80760b4105810000e0220715400c0c11000444c2c40200340310940311550142c05003041260991250352001307001c5803045c4426450b05c1724560281c4032408250a05806044104002075829040c04070484400c3c3e400108002041d6490b00565030076a45820415096505200c8885250310071100183c03035000383d00101900f4043c00c0c3d000401d8040307150320100c00c2e200c21542ca03001d181d40000240c2204a0804100060780b0344002082c008442105000c1c50905a44001100c2062450b5543c04214480c180b14209004c9104c140d080c022440f5000007940d4002c41070001d01503070903808800200310511b00c0100300e0300541800b02d5410700c160001c0000d46071003481400c004101c1c070040c1180c0107404001010300d03030003540400801001282d02d60079455a58003007000180e1203401c0c6c0094010f030083c01300b0990035004400d46001941b005040d100c094004901180064000b290025820340c03101480c0c07007030380c185820401c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 972861726 1250 972860476 972860489
    0xe0607020106150543020301110a0906050c0721020414010b09060705031e0c0f011107171605030a09051e0d02060d050408040312210b12030c060a06 65
    0x710140303d04079002e4400e0203000407a010444d4903140700400c1d0b22091088000c205500f80800c80b400000040b03500f0340d00364800c030890080d0704c0d00704d8801040d484402920300e00041955110308139030401c041202e441e0031102d45012684034100d400301d06520540d02d141a4103c1c0c2482d03802c6200403500401041e5000c084440c80000c88103170050046c0c0c119041103070203040d4161011943c4101c140340c80d501e5445900e07c2c001d1140e8000c503006040100c24001001008100800c85141102c103a5219088070619101c01030800c1d820058030000078012281d00e000690a0070036039082024074458000d540307181d018111001c1d0000102885a1608001c1c0700018010540d00030b05201d505650800140078240055441040d2441c0310200710340c4ca510441d2543c070320140d0140150305051400c68100d80050000707d4000c401041c590748580e1145510f1610a03c8084022010054404107a0024000b040341c581d013000080d82d400c5100c0000300005c212810408005000619090107800d04913200d50b040700 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 972862976 1250 972861726 972861749
    0xc0304121119090c090e1501180b1218061303031d0a0f050106030c0303081938060f120c130306050703060f08010504120806010f1b0203010e0607020106 67
    0x1424040b0348100c80c0c10503600c0041c0d002900040c003140c02e40b02003600f43c1c804400c0303002080421031181140800c0100322075083e00c0309034524940340d0780781181c00031a001e0741850000510510302d5005503000300c0c9400000e403d064003044000e8035103d0b414030408440707a9034480c0000410804060b45841042e0000e11201c134284402c0412016140d103440c042c04005d480c580560312140c05000c000e602c03001c011a48045074828156a0386000307801508102c501e0302103e0800d07051f81e12110441d00a40650480300d40ca200a150a42c400070000e90303141408050518014900341103103a1520300040c45182c00030501c55444140715070007281d0b11a401421b190950109004011451790152109003e5903400b03480800d00340c0e500030088004140f02d901c4980710715210000025403500650050780600d0141d2689040d400444500b5151244150358441c0001d4141d4155020684505100e184400e0301e82d181e001c20301130300d400180c2517a11a04111190782c010030284555282c0911910000b030506d0190b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 972864226 1250 972862976 972862999
    0x50d0309032303091b3d0f0f090b0a08090a0b0108010f0b0f221517210f0f0c030c060f0f160e040207200414060a0603110c03041211 58
    0x846d442254484070a0700b20400040e00071501c548201100302c40c03d25644800d00308a901030802000380100c940d608011906159003415000d109015040c00c0e28101c3c0d048a00c3e090710300038202d41804c801030400c2858080c2120030800035150074100340c002d201c9480007013824440121003404942102c03142621460000b140100f9540340d5400030164002c00c20409d10b05090a86004406040150705031014000c51035404198280d124040e64001c50300b020480e44503098039900e140c508030090700c215500f42c40601280702081a01802031188100d6400e85d141020300c1c084072941b0b160004800c9442c0b03a0007080400c14240c1610001c661321540042d100301c6141011811085a030700c0c200e00b81c4042004072916005962107640441d0242d41d401051291201d44213500600d02910349408036120364100241da41c1c80c03e40409270079016010040c01c614090340344c0f5000794024481c45240090321441032146481c2c0903028409031004200100c80918031500700c0c03510840d2101c030b806402c1c0c440d1051415 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 972865476 1250 972864226 972864229
    0x7030b0a0e010e0702190b0f1501120e010608030708090301050919020f0a12030807030b04020405150c07030c12030906030c0816020f030a0306050913050d0309032303091b 75
    0x1e10504441c0d1080c04080b49844040080342000074210100c40301058900660f4200b100207480c25200300c50a444c1441c242d03c440c50003059001a009086001610152001d0003c071510341c031201480e030b11003000241c420b0fa64510310f811038121007003d0b520340074003280380e10090a0038020250f1028122014011038095023011003c4074000d048040d000c0e0f64040210580c5490701c8140703078050401582d9558512060b0318000307143c4401101d403140024100302051040d82040e0003030780c040c1c58004000040c030084050500119402c84110f20f1620720a48800001060500c620100074012100b01104034541c1070134054105c0600d030744114100751401c00c1e8041d482e98000d555640200d2004550102e01302051000c9141c407800001144840c040043e85084031505a88440d04680c0150354900142e17450701e2841500009449010342a5080020115103081c402c0e84049a00d5100341000450302105000750943c80d111148894910703100041444a03d0b40104a00309460640308180c0e03440100e02c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 972866726 1250 972865476 972865499
    0xc08010e1504060306060b0a09080c01020a030c06110a020f060c0f090f120303100306060b1e0a020a080a0c0b060906210307020d030305100b2b02091807030b0a 70
    0x2000c00800e803070307038a04941c510340e0b49800c8140119000f02e000e100c580d80f1428280706940c440c0c0c0010021504500001504510218580e458a0340580180c04403081984040d601e00301031000c00c581d03165941c034a440002c1e064030064442030850394000c007042d0f991071903040c0c41c11001806901403a1740030b11104500c01d08880840d0012001540e050244144100114200b020a0590a02c2c00e010100800c05c91610b40d0034140201c80c055401845003540d03034090131515201d001c1d07440140410140008540901c014020b1500b1a21481182c4018044c0e1311007a1a0307401140b90b150000340c03201900c4060162800246070030030740072101481203040030000140382c54410f5016003c040130850707000100010520036070b20866005024466101800e2400500402c011904084494420740005c1190740040080da4000c50a285501c44551152242c00104241c150000c0081039020000c181d2251603805d00c4070501c117811149000c1508003440b002c4c0a507407981c295a4000c502e048010006130354001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 972867976 1250 972866726 972866731
    0x10608011d0c180d020301110d0c110c0607020d050718141519121a0708070507020915040f0c0306120203030405090c07140a021c050a03120623040c08010e 68
    0x9440c1c03c2c40f0411400700740301910110000e50b155180003004010201c180c4d00400071a046c03407508010f50070422000744c40000001c0801d0105034007600401086061000c02050910f0008024105c548056903c481c80c21030300760445d1084541d480300b09101107249028a40c1d0f8021070556840d520720700008110007140103401c3e124424003114216905411500e0040d201078040d14140e221401e01505003401c00c0e907160030450505010210001c2d0140740f040394640c1c0030f01c0c15551190301d000e62580800c094548082d100341c075604202040000d0503608c0b42300c2d58901540391000490750100d090000f80403220305501510812040700349030030059801104071000d5800840c1c40000d992900da148001a0042c030f1801401c003840291611005280003030420309480c0700720341003280d88035001c148000142040d607004009510101040000034095204000000240000000c3c581c0c4d0b550340140308000d0b142d07004ca40700c4c1a1180464000d041502601c0c140143c2400c100445501d440711481100100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 972869226 1250 972867976 972867997
    0x2031011070b041502040f0e010f1a0c030d2328020c010f060303081f0b0301090b01020a0213060e090106062001020f1801110a03140a0512010608011d0c 67
    0x2d000014200061140380c040b401464401c02c640340c0b51280c0000c01c0403941da001d01003901a0707803c0005160424070861000b034034544a10f0680d0100900300303800b02c6400045080031940810700130120309165a2040f201c01ca0403401911490381c0383c4051603200703600041d0020159550300c900310002c48004200c1c000e4540c641c801e0050fa00e07031419407170500503d210301c051821141407003000002d0547c01070815000f050032030141840c12000190010034001680305000900d542071004001c0c81411b5803000600084c1030048e62440240c42e400603884499010844c10361950f030700000c1c08020341e070003029644524290020010300c0c4c10441c020307181c80005215001c00c00c4900480740c0c05c00d1030a4054403e21628801c405448a004e2404042020804a0400e000580b29104001c0d04c045c00038a860340c058140e06d5644910031403020700b031806e6000c4001c140c20b0242c100b010002a4000701e0ba00c074000c1090703554100b015411702111202a0f5100c003071700500a00d050041c0309007200c0000440d00608007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 972870476 1250 972869226 972869243
    0x807021b0d14030406080f04030906050a0302070209012403110921030c100b01260717010305100b010503071409010c050d03060807090e0705040906110f070203101107 73
    0x26020001401d25041c40300041454800b0004196808400000b4100755031061711008044c0c1c0c0c88041004e13a604044034040c00040089030300f0007855001e41c00404040d03405290140c6003006540114450020a0b0b002c030300c40d00700501c5000302c1d00700b0401020703071400c01510341801200441d1021881e24041c91a01c24800c8500a0101c903001381001c15501c0584142d030240d17515403049000c09902c610704000c6580ca030500388000a5107561103050507a01c50941000b01100140003a500c00e03640d4030b0700400c40014402040c0103801c4456912100038000d6200307a000340140301c1c030101c009080d200d4407c6041d0522800f40180301d22550001c1070000340a04540045403150160001295031300710800008d865402101140601290300d9080b0405480e50070f411035901c190f40b00010300484500b4014030794160803a5406020b0b81c60143c00083e10140111700100f440c08000d80c20340025400300742981843c1100003904c00450405102d09070801651502c100105124110582100c0c45110001049500f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 972871726 1250 972870476 972870523
    0x1060903020a051201140f041b03030507110f1503061c050703030302090f06070534141206131a0103080313140607020f070b0301050f100509040515040b01080702 71
    0x75003580031404002014014003824100049880c3c40040140e502355181000c0080101503d0b00302c0c9c0c28003044941c559160791a101e01c030f44031113024481e82d013400356100400c0440c00d40d003a950000000721520b8813000290f901d0502508000442030b429500c07518402d58040c5400c003080011440400b12901424050f964a42060000781c100030480110741d80014041401001c3c4000082c1c0c03074941400000ea00100051100100d61480741c00c0e03070075504030a140030024010174003a62108010301002420440b2441030302414242482c4084800921700a118085281413110440720111520307269000d0900650641c1c40704000c9201c0203002c0c8091102003182e05081046825014103405110340907186c071401c0011000b91151030001c03a14600f8410715101061610b090380884e4100c5600508802d03a07402030405218200c010b226000d42030107401e0000150b81d403540d00809100c1c01112401044004041c810401141d046002e040d041040076070401998a800086a6031041d030008591806070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 972872976 1250 972871726 972871759
    0x311130f0806130213021c05180a050715091d0708010f120b04030507020405010303081905130f031e0e0a15020c01140c0715020f0f031c0617100501060903020a05 71
    0xf403003850402d1a140c9400747c0c2894180c2d2140d4010350040d841d400850b402e282400d1940760340d404d0001d8020b040c9802c041000c000c16803c8031150010003001e0304100c102c03a596402d0aa0940d505580764000c00714a45040042060740914254051318000f0304515840341003a504803000c2d5a4440002c1c015410785d00403c050500032820348056aa009200384a1981c4030728005041040c191400070080c502c0b101103512869580c05070398820310301076035034014101290700e410b0000c1c1060b240a6061041220341d41103084c000d03803c1c6a80c0302001d5220780d614000c0d08e8040c060314030311540c0030341e80b640101038480103419030200f004e98429009290070000f101c1804943c10f4a442031170240340441c030030b5100c0001d940c100102400c5050400f0303001c0d2600300210500c00c0d030b128102c550111081d44c00800c802c00e251000f0307907100c0c42c011280500020703410352256602c040130a0f0100c0d05049641c050001003020f004140100b038050452860409190742c07940d4041005024103003e6144108981200850708 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 972874226 1250 972872976 972872981
    0x40b0307111609050a06050303120c1605150609190c0915020601140909070603090606030f050616032028050c0c040204050d120311130f0806130213 65
    0xc070301a4100399108a410104124a101828451150507905000020351080f2140c1b0880e4204d0b04050041c51803e200d07401e4040300c1c0140180115441c04080c1f01c4c0307118091462414001c030511030001410441681486403640a030001c04c668030070303a040810003010418484900310301c40300742040403840300d001c04819205401e89400031080c112292216aa401d51300003078860484010781c4651206038403042c10310008000c112110509035002c503a042001c944a1790101c4e26070b5004a00000d40e10340c40365511255801d404005581c164010000c0c0a003503140703032541052007640c0b0700341008510780c01414442000c2c3c0f0103404d0601d549022030200c400003c40e6040c001c0c1d03804054540d07007804d0744507070010700300760000c03019a0040d2250032030b18421070800e4030843d4165940104041903242d1266503042104400041c0007007010b450b0300c1480382d203924200181128410300c0800c03a14040c244280c24160b01741070760280000343d1251060159080360b100d5904a09031701500c00f95005000002103001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 972875476 1250 972874226 972874247
    0xe01110a06051f05040204050a0612180818030d021b03011b020106290304081809040308191130090c0f180f060a0b070b010303170903040b0307 63
    0x1c00d04281c01c100e07404a00d00070302c5401050480f07001c4440d07902d400900c4200d00444c00b8407500402e4200e82403240c45d008a411442c001c002c00b00120700f405017403c07600e03200344189100322860200130071150390103800e44419480e400300503401060500a4620700a5446c0040d0302d207000020040c294010250300c0030b4004445851000c0e1084210101d0114000c0c001d100038401ca030000c0c403030144207030703c24141003503040d4016a01d5240c690031500c075505d503252681d0006c130407031031201425042d010103a255a0300c0c0300d1089000343c41d030746868506403c482d001108030351a08888107140c04011046c620995080da582c03ca40121401c54080c0c3c1c4115814122175660448495100031780d0810138001070004031190754507025509102103001c888140010124001d0711000c1c130528407000503916115a10700e142e408680209901c0f0119582d8007101c0159209140a4071680b408000600a05410103e402eaa29581c00e4500505140c0340c030340b0644901450190131030f84000040401e101500c01c2d040c424 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 972876726 1250 972875476 972875483
    0x1b0f210312111605061b0d0b0f18040201031b0c080c0f07140114090904020d02061c06051807081305070506040801020706060602032502031912080c0306010e01110a 72
    0xa98074003140c0098005003041003000c031240d210b404006440c60300790a10070301a450b440c03101e0f903087c010031030291405013403200d02c03550300601071488101c05a52021805051800846040f40c1c013414070340001400e50302803007014407000243c0300440050542c00103030001001d40100e000e0b52502e082d0440141001c01420080e001803083c40c101240503c0d000d04200e103800b5098984100e5004050002e501074061202c5d4541d0040d108400140941802405068041d100500071440c8c00d040d100c08084c00c0310391810020f805130b681c1c0c1080c041c0e400e00e03240784506041c643c2c414100920780300f980205442802000035026011101d00d12042140812105002e820024035140d1101d4545011078001d4200d500103484560404100090160011003142c0d40c10308810070041c4003114520313070804100d40c038000803a00b501c5101300340e02910490a18100f00356100342c880021050b070b00c95000300000c01c082e189021042040050081030f0781c0249851407000001e0801041003076048000d58101000c008028 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 972877976 1250 972876726 972876761
    0x180604150312030b040510051009030b181207020306060d0503040b04030f110a050913142509020f090909032a070b04030f11030a1b0f210312 62
    0x200400c0442c64050700c0e00503a40d82d041240c489008104003d4581c00ea85da060141c110340c00c180014100f28003418586500350a000d0300c400c0d96591407880394103048499036803040300001c5044100000b8032240c00080b00d6032002c9824a55039800007500c4000c040c0155108500401c4032808020302401524020040c0d00159030300d0707559074202902120341c07241d01180c0306402d081404900c0d142c896404000d2340c10107480c0c001a80d40350303076401442c0c2c1d08409040e2908100c10883c00650310381040228140f40e0021550310800d00b2514512007500165003105001b00c0c014003007005046004026a03120142c21580340c0c0641e221449414210320407581c01510801c00c882e01411652000303844c040d1034510140c01c80707400d190340b500c9410003806240001400f14041d8480300c40811080c0c400071061400c000c0690b0b9941002c0d41c4c8410140081c1d40c007411034100c51200030007000701091754803001490188a0341c0340c10324145060b8040500e203048002d05010354011881044113456110840301a180c1e141c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 972879226 1250 972877976 972877979
    0xe06270c2101060f030f0c0c06110714030703200606040c03020c34030506190608030c0714011d04110d141006020d0903030804050c0607060b1002070518060415 70
    0x402d00014070144c030000c40c1c20300030190540c3c00a44524031401c2d580c2c1c1d60311418011aa036800024203044501840c0308402440481d0203e451241248212140b401c001c60f40e6000503d0041e0034244c8a1100e800b81d146034002c149071f00c58010a0459204404940020b00010200e200368003d00402020705007510610841c0500c1c22041c1581840c40d1031550006045078603000b0012001860901004040350400000703c0d2200010060220300348a078181c0121750340d0b40b5946420b2842e04424031441c9103a0200408220a600c10941c640e2700280030300e420301102c100244001840e00f0102c20781c0e40141ea4178425401d040d42d0b000203440380034070352490030b111015800094007200013059500b85c2e80d09c0c400700d400242039400026203655030b100c2501c4141c2d145c0d1868074181c410110080040e50540292014009180d0f50301c801001040c0c8998000038403c1c0c101c409000f0500b41558446040d0340c00701000340019558503071610040c2890f40d03c8111140e85204c0841c0142089032407504031100c0c0d0303040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 972880476 1250 972879226 972879239
    0xf04122304151e0c0303020717120403090e0708040305031906060302040f15141b120414030f0618031303051f02190305150a0e06270c2101 61
    0x444100310001d5640e20001c865544a0243e8040310342103145000c221300390380c0600002d02a07001740c80c000c0c2c0915242404100e513004411001ea01500d6413a81c1009a44104401c0640007150701015201204070002130381b80440024100741d0300940003400340301c000b00015162464036045984203c00c0a60180a050780da054040c0c040d402c00c0c016001d240781e02440c0802c00911504c5005888030061b0b69120662054450250b55580b0506a808000314120300542004208000383c1e10300c0042c00403400d903140e107400d9202d903600908200740b81c401d4000c5503400f49104070024000b504464903140b403050324240001c803d450351040d040110301e1045142400000d1002c040f4025280c0b2016004502c3c0c904000300fa10400ca2181d0b01d60b20740615406400214282d1180d8002c0d41d2003a07801e22103030b4519108800064050038180c0c4070b2000345080c10104071070b50402080c0c0c882220150441c194621104065494003900028450303800c0032404204140007980c4600c0201f01110010061405540c4030702 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 972881726 1250 972880476 972880499
    0x2090108130f0f1b060203120402061c050709090c0806030c01031a280b0a02030703030b0103020d1401050a080a080304060e0a080a02151311190815010e0f04122304 72
    0x613825400c1c000703081000070081d001004403203171402d019454511660301c907802c0201540241c0e6042c07082c4c40301d2036800d801007085c078451076004e44030b6034032003034040c916001044003a90109800c100170000340006008031618001040d086444007400c0100703114000c11441541d1541c0c02052685c010012008490450803c032140503542050004400c0500d03218485e00425206800c1c4540050384100a0b00000c28840c0e84074016490301450058a018801013100301550f82031407602909c1141c0f100100910700e8540b40300c90003485000003078800d248840c0ca07068400d010082000d0203403502c03401d0480c110318041c401c405005a1243c8020380f10080f00700d00035650045440038860301c030901c0340030840400c3c0c4244000c10182d4040c41980484002c00c091108105c40c050041210003110903010509542c00d001c1c00751300a07244141000daa626044d00c01d011f070180941a00b0384140000184404a42c40d8400c61020007454207195070b202440107000c00b4858907000411954900100c0d0100e038041d200c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 972882976 1250 972881726 972881753
    0x503190806040e060c0d020a020c09190b0307230303071a070207060903121101150b180405010e0c030c0d0c170f2403010e07090b090a02090108130f0f 66
    0x140c804100c044030f8404815980c82040d90350829140701032200440501032600100245892441691140070641d0045601101c3c01c2c2e03142c020020000c900519001e00e180301360109404110018550945020b1005000c2504840e4100c800e008020b410340443e1000c10407681003642c4011f607510f45051101c1c14103540b0344241d402034014002c001d00003880350b118000c4078040d80d42003e55403031581a144020748481803054500c1c6001e5498a0450308081d640301c00410090864205003a91a20341c040c00d000104bc2a520b054800d030714041c0103101841802d000d483d888580d0362101035403600d40b1020900c0e070780150311394203202d103003040c0c0c4a404855115214075602c0440e00f09004070b40e1202a403d08402c2030032107500680c40d09041650b074800302c1000c03c14000d501c000e00005041e02d42140f0301420541c143d005054a140c4981c2c00c2016420004d010035800700000c0c00c01c6052908100000b40f0039000a01004054080020b0748002e00451001000d42c0a51101103c81c07440340034601140000c801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 972884226 1250 972882976 972882979
    0x1406090306071106180c010c020103090c030302030d0c1809090c0b030406201c0b0604030209010905070e0a0b0a0e0a0801050f0403080601051222050304121716020d0503190806 77
    0x111408a007142c1410f01c18000345c403c0140c040c05030850941d00465848403410000c0e4105610b8a05810100303c2c40315040010318066800785548030000700525054500a500140c1001009020a2480c14201e4480e03400d5070616a0041391076905400e00810003170403500b0015141400101b40820481c10b5848410003840314040b9030803000090008032018042c1c04800d02100c40d180850501c00b00711627221440039540245124245501c82d004034002c074000f40c101c0340300700e035591050240a5030081c003180000301d4125008100181401401596070040b038140e84144031070305205000564801f54883d02404540b0002c2040780740c4080440c19040041d50180d002c2180803001c030f4029482001213503111455400800165203070761005c00c02403100042151009202c08103c000000d60620081c8020301a038005824446981c0c1071001c075803032101500007096001041442c11039450441c100e908150100c801d14403064607810200e0441c800c08c4100c1c0d03100305000740104400c079040328103240215070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 972885476 1250 972884226 972884233
    0x90603010f060311211b07061a0d021825590307030c0f050922060e060c0a080114060304080f39150114060903060711 52
    0xe01140b2132151203000e40d000b100420303201550203a2000d01c0d10298004a03c41c00040c0000d50162440107150000b2004850341c6455441c0320804808020440004000440d0548002c020690000e42e00c0424841d810152200c2c500020725000584185070607501403050079110708003903a8a0040c28a4034180414521022405c6600000300d501603144049900c070806001401d001513441ba02c2022241c1001840d403074180700c1003140da1310b0070b0001d800290310400c41050128100001e14507454250380140d40101d1900c0d0810031b001580041d545d0a0800d01080507404c4074807400c0c6000501902c42900740644244028800b004041e500106613548460303494160a0762070f00207045c410744400f184160b0140c400d00210703010512201c002c10507018408a203e2400300d40303150411003203040312030581c44080b0324901c1c0d202d603c030b501d186901c400c1c00c00b2010304a06003440c52010090704040c0219600a1800b4101e010144c460a048807003511008088513240e1500403070041c286060560110090700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 972886726 1250 972885476 972885491
    0xb070c0804060c0519110409080403150504050601080a0b0a0c17010b03060301150e070e061902011b1e081807150f0804030906080a0b2224150302090603010f0603 71
    0x14103040004251071b4800c62180805043c50200005020028401d442d0b0607030401000001408048580c5107141008001040074509420f200e818400305901003803094201d80c9960000500c1c00d10b1466115a91b1703000000c1e01511008211810741c4401d0580d900c0c204858004250050742c0f6002d0b520400c1d00302c000f40885c0b040c0312070007850840d5510a8401000c16a00800c8007176000341e080c110208005405142803903800c0790703411050104000b00d10050b0755112003441040c104d55000c50f07604a0a410035071410a401c10702ca04040e0b5142d2092010040c844011989880303840c1d03a00000101180c0456030ba05446041c040307141c41c140c02c5c0010100700084105481240241d80c00c0d80b040c0c0e01a110500858a003290644600b64000d0208800d5030b5100070103151561045803040d80e001c8082c00b44200c01d4001d21490048800c0403028641040b0350205003038191000035241c405441055040c0b54103d02440002c3d4080e006180f0000c1c0c2c0b046010001042000c0901a9003088038003558090090f007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 972887976 1250 972886726 972886753
    0x2060f01080d1e05090d0b0a0b010e0315070519022b0504060503061804060903080c1602011413060f030c0305070c030e032503020a051206040b070c0804060c05 70
    0x40798036482c1c00011490904048180b282090000d001c1d90900741401490200220001100340100100450301c015034602848a031030441d12a4051511080c2004805640b0360700000b40c0e00c4950505803181041c1ca0030009038803601c10000c0e103540b0b03454099000d240c2c941c01e400294451410700700c6400d80540782da0b004044828602c0c803880b0218925100d252805081c000c044415a1006002a821014440440b201c1c500d2450000b80306600529001032500410701d030090210381d028040d548816170501091055000040112800650900700110300c12a0a00b445840e801071414508007001002400950160000361285c003c150640d407c004d08a0701000541c00c03030700181c1d110000038082140c0c800000c1c0c0198000300a49a00804441040700700314510140000462080c082d0015001d2007003046040ca01c1e40040984011121942d203000114403041d80c0702c00040c00036207108040004030780802e0040031031020460b040140140e4994580102500c990240102190310348941400401d10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 972889226 1250 972887976 972887983
    0x6090b0d020a050d03140f0405100e060316030b03030705010e100e0a020907030e070605042c2706090c0901150e12120301121a07080a090c03060c02060f0108 69
    0x160380d402002d1040e058103002c240046058140720840600403c1440001c40100701d0700900840100c00c0d00c0e8640d61420038042c0f0400076540450b0f001880702c01000a40c080d0340f404182c0390300030030401c0811000c00d0898011400b40200080c07058050000041c0603042c041c0642014803086454421542c05410354050030003124032001c04541a900540700c00801407078200c0840780c000c52107107004100a8595010103080420744d41c0440c0106d8000641002601d2a004615119041907003800c40450140f0307446030f850300c038000c00c2c14030030324150300c941c0b0b004015510764651002c60f04400c50700640740c41e0241603580c42000000c5442684041d000160429001d440d80c1c45844550341c070840c071100c06000b408a000e0034014143c0407400380380f058100900707015014500070082300580110080480c1461100c0b10140c5813940301c512500020810300980000c0d000e604040c003070900180c10981410864051403240c0c02c000c0c010b5041000d55100c031540003803540c4c042c4030700140b102c58a90b80d400d000d555 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 972890476 1250 972889226 972889249
    0xf140108190510050a02210103051207081c021c20040b0901031505030f0a061104060203030c090a090501030b04120e100305060d050316050d0e18090a1506090b 70
    0x402e83c4890b03042840b0150942000d0b40017252500d025050100e000d1804208214200f00048107024000041007400000c000c190743c04584104401e282555075110703603c00b44070302071080c014a6098040d402050803d80e04444021144800c0c0c00124405520020060400c050ba025414441c078004034200d4080c2004440c00c035046010064a8402108015000340c0241d83c0b00300c2083c900b000c000151502c081c0180040d8945003000741840c07807424a4214110b035151010381400010900c0140000c5400004581c0c00c01f1000401545580108001515450031a08421100c5050038000010005442c2205009612503c03040e00c2144915500322201440400b02c554007041241d6082c400c507000f43d00440c0c0006001d0200940c106054850f5441e5611283c048001c14488003460030503c2018801c1280d01910340c03810b400125000340000740309409002400301e0402884000caa1440c204120800419510030340504055810000220080080303224001d1040d003010000304072494100103102 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 972891726 1250 972890476 972890483
    0x1507020d0f031a030d170a0507090302011101091719080609130c2d06030606020304090c180906050111010504020a0b0307021f050610020a0213050603010f14010819 72
    0x41c588000705044025040814108814401c600d02040c0c1c2600e0a110404280c0035a41390f0a0841c000180302e5445070f1401042c02c1c0c5180e18200038800d02c5540040b034101100d80906e001c0b00c00d62411780d1241c1c01403810003401840d1003c0c412003035035041981c0014214000d00014418000314551000340e50070390301111559030083e00c5200054a1000f103a5204624130702504481251175101c280c2403060f20911143c54400c00b071180e10480e2845450a40c84c0043d003140d2070280811480d00301d01940c0c034092405410010350301d0303280c2c84028900c9007041140c000c04a114092140740c0d503001450092506014a80c0042d400e00380e002d09101050241d5802258064a903406091529259020640000d000d54045029040b01040c0c810a02880e900d40c013488032000050f20b08100003000010445151a0400e41d00006240c102503a11130030f42427006030300e5035800f2619170f490b080080d0041c032041c500401e0191400c00e9042c111800000d50f18141c7d1104000ca40741a44140c00e011020314a5041c000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 972892976 1250 972891726 972891737
    0x509150105030105041a0c130b1e070c0e191406030706020127111018050f030604060f06050307060507150e030409021c0e03030403030522030806030c040e1507020d 72
    0x342403000c5d06034446c95000da60b00c80361905010404030481c0d041000b84d0f004019454001c00ca450100025052003ca00b8016242440c60400c055446c510700d844107101c2e0054480900001904075262800d048181d014420400c000380801c0c030001c1000b410341a00d00d03900a105040740030a99600522031010035914200c010385004090b00140c1c1417420102208980d40d9061040c11665074403900a0038120080c42c1d15441c500001019428141c8092035114900c5040c2000924105807001324806c1d0304181c01c903002044804140c0080b002804642c0d200300c0c1c0500c5051000502a43c0c1304026211507032040e0000b528150840000da4140d61980b069a042600108001c112140c1690b0040c96000d001c0d0041e900c0e207082d020201012148000041c440e280c00000c20001056414030449900901841008a02d088000c07440c4c3d9104801d00401030502401802140c0656010020715601c100028028050503050404040d1074032202c5104040314440c000c082500180080340c19560350707020365541d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 972894226 1250 972892976 972893003
    0x601060e0f04020d020408030309011812110c1f03050f15010c050f01060605120f19020901091a04030314030601170a0f0c02030c0c15090105090112050915010503010504 74
    0x70002080900300390203074000d500b0040c4034031004c020300103400280403410113075459103807004583e07082d02c200c42500308a0f41b2075000c8132800108140d00c50180c440b4180782000900c00007070708031490030200001040d40300140400800045403100b41080c0d40b0001d551701481681c44010002c82074200c03d60354001407240c80314068041d540704000080241d0b006108030303140000c0807202c040c00c642558000c580001c50000d91740b50810b154039043e84c1c02a20441d1950118940441c080103c503140c0002c11402c1600020410900d0388104403a5024010480358003645c00741481034281698001c0c4422404600d5400348050030090010550f441814181c44804bc0f010101c00c5445e44d62400820f1040381c1e80d542c8045108500e11441114040301c0d440c1c004650f036a403000101844e041507604014410180940d125001b40040303800d69281081c03c0c2402070f201d00d018001a40c82000364003240400e82d01d424104031544100150000b242410908030820350703620f600c240340c00d8550480707005e005031844080c0e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 972895476 1250 972894226 972894229
    0x11010c08071d0a08060a0b041a09070c1b2c150301060f29030702192a06110705030c040c0e06070c031203051311120d1e02010e06040305090f0907200601060e 69
    0x1e0554440cbc407a24100b80034800569070140d443d40d01c4107000031032504408044c804680c000c25055040842c00c050001003d0141248050810b8002c050f5100c0e20100e084565054030b094014201424242a2000b0400c0d200c0110040100e06d10700c0718080c09805445031443c40800e4800c0b80d016a00503806007241c440304110944e6a003988070b00c104d6000d00002144c201d9124101c0000491440c454032819420380341403402081010000b180120f0350700003280800035a81c00041821403008255408a00072000710825180c4800c0241860b40002000502c1810440c0d400c0480e01641d2158110004082019504504607082156014420f24501d4450404a034030350310f08580d5068020140307002030200071001c81c10408040d4001c0003041c030100604540141c000614020480340303100820490a045401c00d550315000b41000d418400d0015050311070b522008641802c4100190018509041c0050018094000b10102a00d507240881780c280603288041000e030304907242a660300c041c00c0c42820 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 972896726 1250 972895476 972895489
    0x51804140307060c0305070906090819110a08070305060c12060d050c100302120f0f070f0c02041a03011518020a0e030f0c0111010c08071d0a08060a0b041a 68
    0x3120000644800d0044000103855400344059180c42070350040760f207040a04001d0680e0030190071a50a00540031410710814800003540351030748a502001a0380d0030030b80e0a00b00c94941c0d5001d001c540184054031f0110700328100050071000c69100b0400c80300f5543e68028030b404070f805030b0b00560280300c84e130001245241c40c00500c0c44d09081d010385c1c00d07260640348882c006030302840d190f6950004250042a000076803074122000590046000b00b0b4403120349440d00542e22b807281c1c014820001d110a4078021030049215010a80a4550141041001c20040c100b203800708200004460f200350b003040d51007880f116809900d0000c6641406a42658240c003000100107908001c00e8801007144001210107a96401c00c8900c2c04a85c2d07401c05800c0c103040102c001460a4003140c01e9200076814840003010f800d0b0303c03a00b600c1c4c0c0a0007514001c0c1c2c02c160582c0c6504248140c40740380941c411500000400d1000c0c011031450f0180b00910317410459002014140300c1070b9203444c500c2807080821003202925500745803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 972897976 1250 972896726 972896753
    0x3091a040b071b12021507030501080d02030c0c010c0321060f050303091318020d0609030e090f010905060a090c020c0a05040608030712051b0a0312091e05160816051804 74
    0x5d0054504005080414064001c012568032000a4440004000300c100a100c900d110204501c040c6280c003908080c01030f901e2a903d43d0407030400040c500000d00b8584107001801001d0109454103a20342506103c0390081e01060080c207a0100a1540c002424078002080768000310028202c0040d1120416586008100148000d03d009048a880c240103948901c0c41006c0c41c2c1c0f003134200143d91a407909000340f5a250340c10001d80920010301c2480810840d064401c1c0c1140d1090002081d6941e40c0d0b008149c489600d43d00c82c000c480d0900d842d1244041c2c000c10400b12400381512406000c568890402c020384015214010700361f04108030510200b2814400c00500060170b052540c9412034441141d500c01d44140c40f0b240c000d405c0848072038100b65000354039909100304d04005100303945c03c40e11869160a0882e403030414031040c0040510800400380b000c208140c0707002500c540116034404140c1d880755030b00380d5001040548850b0102e8145070560240c85c00c1c2083c541944a5a5560395451610b5143c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 972899226 1250 972897976 972898013
    0x5100f060b0a020304030506010e0408070b060d060203160e0105191409060c07062c040e12030a0605011101060803030f042a05090a14070f03091a040b071b 68
    0x36194082904000700d4014042d080c540e40c0150355aa1a504000d401e207a41a00285046201101400082002c110903140142d03040002c07075245490300e400041c0103284d05040100030301d002004110b40e07e08070f1160305181c03400b40d444a42d0016140001101d0394840c220090008144004051004038411303404010041c2c0d81c00a110f1404444000041990700142b41d1030a29a1224a092084a902964052100b540032402c480c0b4007442c21003c6610f5149456142e009070380d92603442000603020810850f484c056803004c55a00d06002103070700301405803809000d0103d07403658601440740c50305125410807911b201000d1400c41d15484411400d0080140090380c0b481c400704e07410300000c200c25401b0010051070705d108544062420060051440e401041240d0061074810709402d502c40154180d5070040c01460700e204110414002500184410000074180c0240c4800f00700020010310a4140214001c103454030080d0780f0194125242818200b0300300d04071421840c03050014801c80800c04507a0328 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 972900476 1250 972899226 972899231
    0x6040e0303240d0803091605031c210507201b12030a030605280b0310031b0614190509041413060b100801050f19030b150d05100f 57
    0x2403640000c04180c040d10003503c00242c0003050010248041049147d80c8007603030707004c4183e1450308000989a500c020b8081d5a503082ea08860004907104941d1300044c0000c105510090b142c01584a500402086800e0400328500d11000900b08440a075644041d4040a0013001403400030b1107039800858948070b040790810090a0074900010703090001d440301c21103d95000610501d0a001c0081900500b5640e2802448548501e0405a4042c00704400d0f14001034856a494650b4000042c00300e9040e4030240500d5800d09a403402c22000304000c404848403035031000c40051800740c0d0700700d00c1d202e50300240c00c45510319000420200e004201034544070380000c000248154110b4140510712400300d40851100c02c920105004021051180300040c013002d403803201c00c3c0c0d400600c1c003400212041c06040c0c030429800020200e00d07030704c403255105403240071003040d003c07150340b1300e0000414102600e6604408a140c01420f0617420070790114107100e43c00100400d81ea00c1108802c03401001c00070040c04007030b0b8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 972901726 1250 972900476 972900541
    0xb070f0305091f021e060a0c02070b07060203010306110c1020030a0e2b030207050109080a1d090c0702060a03240f0807080a14070f03030305010e06040e0303 69
    0x643c1c191001d98402c0c80412181408862088001d042103c080341c507007003000c4020340e034608000b000203609610252103040001c0403861a18142d19015030307540601084000020048108105900910304036840f94006100504082240050034090900c500744550300c818507106403094141c00000c144401003140c50b14100b600c85101489034000c0350b0801d01719440d000c80245815041180c8040c00301c103014800c0681130844c007140c8404140981341802c264020454400340f0500b903205640b8541e11062483c0d99003c070307020180640c00c14009050b00104290107825981c00c240e102240300b650f2111312a890641182e007000300d150801140c0804040d41c90040e195186940d078102a0441d00c40c81c502c1e030010b071900100c414a02d0190700320600c01d401201c0d08000000c0700251044095611145e404401c00c01d0080c2903181484035800424891b294070000001e0682503404681a242c400c0a00f846c0c581d00c03102404180e44101d0100b0900758000c000091203001c83d01d810306110b241c042850707420030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 972902976 1250 972901726 972901729
    0x6011703070b07170f0105120a050601090c26061201060e040b0705070b0108070512011b210606031a0102190b0c04121b050108010b04091d01051602160b070f030509 72
    0x2c00d012070740100342118007001400646810340048230440c0c0741400078440c100c2103030b03615602e400d0103125000296441c0c20309601d0140c0982180820007203010341350309424211360082521514151003290103108078804c40f01071540306002e900160b5494041401d91a1503d03510464410402440c04081040a01411002408030251103000708007820041015030305100800020802e03002d901d40150385440450540e035515210404103103620390502d4081505040c50403a80001031005422255142401c080b9540e50150321040084050b44005049403030510010399840e4031075842c0005075142d000e40a0001040102220b82c004110703000603092943e0b401414200d0304e1010001c0300c40100305250b114034a000c00e049600104401d10300010306515003950600544074a00426014944030120b40c1d80d0941025003001c07034004420002c1045183c0003141010b252810952000103018880c040020f4034071800342c0d80c040c0d8501c601528644100c036501d41e40700203400c200407001e00c423040c4030303c0406 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 972904226 1250 972902976 972903017
    0xb0f0708180d050d1b0f0f1b0f0e012c06150d0203040b060f01080c0a0219080c01050c3a2a02010504120503060d021c0506011703070b07 60
    0x5552081c001010141900301016003802003a040b0514840da05d80c3d4040d000c5805000c00740411600002d847c07240c014241040400c1a00341c000b042c0200030950000111601c0c0112143d00315405180594030603600ca070124071003900c1366003040d95824180001c1c651002c030184c4200d03130045001030004001002c00441c9501641204400900c00b50b0b01100304024090b0700a40c4540c0010125041e10b4542c509100281c8103001c003074500c007881d540c00701d10350403858002c00994940040890000503c0e0a0b00d2a110903141e00c14040048a035092602142400000100f55244034200b00d2419040303460722400ca02c407000f45c2440489000021251701d40d42a1a6482603550484208200030810310744840400b412548000c0c810307046a152004000104240c4c2d50112022441840c01c9a0ba9484010000f82c0009014401030b602c1241d1019003048809409041c80e00c103481081524481e03a41c1c2d40c1c0142210000310507010054100300107100000d07811560582d482a01c2d0b0400550385c81071040c1d0102e1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 972905476 1250 972904226 972904249
    0xf0c091f0c0c06051803070614180d0b010305102f0f031f08060601050d022a0c01020115030c03080f0c01061202040b03010203061f090305100b0a0b0f070818 69
    0xc030f98001072440b1715141a0f0203151407014145e0080c03042501d4060020804101c1d46009845c40102082c1d1718512003c0c5010806140c400400d401d10303490842c2000c2c145403c0070302c400c0315184900c0b031058034440d070f180c002d140e414031010f013950010b00c1c0d42c0080f2075410100007a8062205d80200700352b181c4c40503e04081c50180322a100c00050800c44030200ca00c101ca9550403551855010208000d880d83c0c0c0304049850200c101103025171241480030802c10408200001c500b443c881e2014610860f07030001502e0100303444240d000f405200d01c0d0095489402d0f00360700001c6c00c2406108401d01c0403d60305001005241c0840e907401e45030449458001c0d00f180d4181d00440d10015403132a41d0019440c01c0e0040340c0500500702c000f1451414150b00240d2080002c0103030b80780e03020038005075400d101c1c00794607900300442e00032050307598000c54400300038000c0a680e14100d108031501c05000c50b0307a0101409944840311000103007890480c1644a40b45581c0250009100b150f59a0200c1a000c0d124181800c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 972906726 1250 972905476 972905489
    0x5010920360a081f11040308180406050d2307030b0c0307030c110d180801060e0f0a020301080a06240e090c100e0f0402040b030f0f0c091f0c0c 63
    0xc0e00c0048040400202c00e24550040742c9580c000440030054098283c104540c0c0140340c08002101412a140d1250a0140340e00103018100701250800c041c007031000d0340400e0900102c41c00c224150b03c40b030030024568102c0c0380113040d000340152180644110315080780e51088201c411146200e03074036035a184856000301d5081680120200a0088943c0c25018048850140707040510424401d0301119640c0c850b000c405900704110b110704602410036004103e03000e030a0300c40c024807150b034545075002c2441d201620010720003070524001405010503442941e060391012001742c0381d240788548982c0d0140001c603040340c4003004000c8060749140c0a10a0040c01440d4001d9060300e5468840066800d01e805034110342c0c01904d0011080c564a94010440c05c140c1da41160300000f070744489004140240115080b00c40341642c00000c0c003043d2101003840703c0c4118000c205592070741d9181103141045001d020002c0e80c000200d10700c0000004007622444142d00101e10341401007080984945250440b1607000d074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 972907976 1250 972906726 972906817
    0xb0406060215160c2a080a050c040603050c0d1b170606010309111302160c050901140a12060b1003020405032104211a0a05010920 57
    0x70001d14030200b910381d2000ca0394203603a0482202002c0038046580c2c4840042580d00f140008007404610614191070380711000400d1000e19441e511601d40d00d1940c280241d0b9684100f007034042c0c051801b405050140d80d4040d0240c004000c40805100b11801e0400c41151400200b40d030180c0501880c289400046c800380c44d024aa0741c0305205124100100904070300e0406040c0703500d110120380c06244403240c545040e120b00d8014076141580c280203000d43c000192003555070759011400d00110b424542d0a480080762012103599807040141c40500b82001c00035001620042c0801c41c64000c040b0301c0f182c1e94000d10700410b60116020020712a020000300d46d201007580403405100d642001c00c8150300c0d8408805480d1610103845915948174001c40c442c0c80b10030141c3d0b0003210b40710034084500005081d031001d410b8210501191070240700201c210340d4046d5181c40c2c00700000d05500b0a006401c0242600c2d0034041c1c401c0f02083e880350b89684480030415190302440c290850743d012020140044d8800140345 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 972909226 1250 972907976 972907993
    0x9020a08100b04270b06121219021501090902010309080a1e0c02130207051213150c1e021c1103010b1f1115070509090108011109060304060b04060602 66
    0xf004203c501d481c00444e00c04a1042d2034082d480d4907030702d0b82070a0135086030400c8042d40e1440c0000358055810f2003005490f0141c0d0183c9030103c141f540c09030010401c07182a5100459520034100d03076500300388204002079191403004001d004c8082d40040303117450040c500400e90020549580b446a4881c0200600140900340070942e118802c041c1c50f500040180780c04090481c4036000a03096a0951400d00b0685034002442c00400c0303c10002105099440b4510719101c50400000c9075000742544186036880040ca500c81e0485482a08500381d865030044039a04800307000306000980024910040303070000c0d82102010005409182964001841003807030760b00100d07980b8240350a507403580788240e01421401c12080c035a10031008189920321402d1400c40c004c0c02560714254908040b10900b80001101302c42488a071035032010040c80560300a64503110a82d81c2c0307180c0d460896500344502c280a072000e2007039407602e20300000196001030281070003044205582000404554a076070001c1702607400b0401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 972910476 1250 972909226 972909229
    0x14060601090609060f111005190c020a0816030306090e0c040f090c051203190c0b070c1205090d0510020406090f12021011011506020f01020c030d09020a08100b 70
    0x1071032000c1d282c07a00d00390861500d00321000e4510b280780415282400301c0054010310008003085041400a42c28000303001034182030855151001c0c1113010b00030b0072810182c005102134000100907203410340c4075039020b15015030000b920b2240c01c50504110209030300c41e0000902140140210500d100745031010303005200200c0204401c9403d4a42000001410002c090b40030401c0182c042e421200c054175101640b81c0240480c9003035100751035000d41004128543c142c5000e030700c20042000e9500c140c0c0d02900780c2e02d8008084e500516488ad004000da20203c0d08142403902c12405400b0840003d803400c5c004002c40d40e60310f800d003090703051041359440d80030604004d21684201004000d15030760007444045030420810b44421084618003038001ea5045404509951054007842d4003649000300810581120035403126560040303210f00070052148910300c42190390706200f29601c00c8200c000a500c0c02c54600030140144c8003030744c001da170300c580910000682c03403000f071003405c2045801c003a0015410f10b6000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 972911726 1250 972910476 972910487
    0x60412090812040515070c090207021201020313060c1106040f0b0606030c1e07060f140a0c090e130507080303010e0a06050913060b0a09090203011d0a0b040501020714060601 76
    0x740141e04692000100ca4100306001c1d00301c8040e240196550f400c001d0825210628a109400300244000083c000c00180d1048960107040c0042c800c9031030118082240225501381d00003909c10703003051100c004900d000540c40d940701e40c0d1402c07414200f4000c40c4606944030760601c01e00b110309540303003200e03a0365540c100010b040741d595020710116030041c190b05188080c02210300511800c15500c02000000b5074150101c202603501c01f5501031018810780301101c1000001d030241c6040648107020020102c0c000c42e156000f40740d404889a0b0301e00c1d8416240c418640f150b2040030746020020004800418042403081c8090809816218011039603035162090b81c200c81e04c0000d100f100441c0c42d040c8240255619114150340100070300075107403140211400c03c040180000d50385194400d01100d00010001c52981102ca0300034000c80003008410900c04285603955040885c4001a420000001d4000354140310f0517904140141c000506040341c40d030398420059802402c07144660700460030000550381c000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 972912976 1250 972911726 972911729
    0x406021006051002060a0906060510021c08011d101e1505030f0a1d0d020706030609050412210603030306080d211e06030c051807080604020f0c06041209 67
    0x1668554100300c240e41c0005d49500c2e026052591658603844010213005454004101401004120001e86592084c007c0d55451484240c144000c0460154204050164104504a03481d8007007016828060885c60301c1d40000041c5640400d01a0304401b06440c50761410510001c132000d8041200b482c1044d42052020070014100f00800008204204030052400003940c1c03c03507a01440402c690300488017031141b0000310719100d2824807882d25100806680000c0d40800c60300071303480401003e5264407600080d960219000707061074029000b420ba40b10b1003041c072030f5902c5000700558003580742c51880c09800d4032810f900a80010361100c40c2888a0107040c070541000003c6420003907180c060810b0540c0580000b00301004c40542c1e0b070344d040c840c403200034003c45c8804241e11104021080c0c0f2854814009034941c020b09000c0d281900c901100800c2c5070502c507003d00d1440d203e40080396100420000654801000c03d481c80310b090005014130202080518042d602c203002c0840d083c82515001001030f0701c0da = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 972914226 1250 972912976 972912979
    0x7090504050a02092a1308070b0a0f0912050607080c03060d02040b0112090c1401020f100906090f0b01150e01080f07021e0c2d190b040602100605 64
    0x405061000150740040d590500c075a06852098040d5540b801e146100131000c00c8030441010b001040500044070340c00280442e0460f0f0014408007512019496515100c600071100521820006601c140703000d80d00c0f44150030f910b4078100c0e038aa0344681c41e48003011605141110aa80581c0a01080076003141001d90301c03441441d0a141145800400607460b503500110182c00350f6901c030583c00132a4882c420000500882080038040107134035182503800c5440758800e401c03852964140c40d1189610120303200e078034072458000034220110794000b21002024008000c961495a9920103000240d02c1ca00c4504510b0040f0b1032001158074000c0c8280f02400c182c00d04d2004c20100c0e80c4100c02a070703000801d90b9084061403004018661701c02506915000342983c01d81d40b80c00f54100c40c40348000c40028502d4500c0c2e4140ca41200f107983c2c0410281c10410101c0784e802c4480400032802280b0b08003c048003408030003000044649580e600f4400c0c002e40d001d41c0081c80180c210a03c0240042094000d03140240310 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 972915476 1250 972914226 972914231
    0x30405130e19020117220f14030f0409020c0a12030b030106051207060e03030d14041202030304030807050c1510060809150106121b050903101109120709021201080709 73
    0x30b01c0c2d00013441c01c5041c0045c004129541804100040c074613424146412081103545600000c0354144590420150b00c2c0c12920101c4070480384200000c044103454050080c5d1000d00e003843e0410b40644080d4011a007c0201031050550030700c003040040c8a400703d82c00d0240ca0006a40304900189400e48040c0d0b00614081c408103105555080780004040044501d03520305010420b403414002411485000c251000c080d0520302400b190301ca16011a900840c421500d031040b003042000182d03280c1c00121405004907269500013000640500c00400708030070250141c803070000010301c02c00e501082c242ca070001011a100710520015400202d19500400114010000c0b08e0a20b2540076800d1030500487c1d04109284031145001c10a60300010382600205841400d03082c0403160003045034010050592081c4030700020a40703d0141d0788500e840c40b01109070300713901d001c8d140428044510940001c000707191055010000304021144041c25081c0707003230b82d96101030703500d041d100a1400005400c03450f04140b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 972916726 1250 972915476 972915523
    0x181501230f060705010902041506080108010e030d05060102100c09141203030a0b121b10050a0815010c051005060102070b0f0403030e0402070519020118050102100e030405130e 77
    0xa81d68410706841010407241c0326600c802520b419400b42c200004003d4000303081000d4410342c0008900c126094403150794400301c0581c1ea8180090903500d500111690580040000340c080b01c003940c00a650100043c0110b848103c0710400c1c090032140043c00190028114980a0004002e130b840040b04a0b0012a040c00e20140742096a98a80c400a0001c04845580700340c100007a4442c0f02c5e80000440201c41135492810a100b0b030302869522000545c0e1013040366920400645000d40c0c242c03465000143d42d0403846035074098404001080c0604071606020036030304480300041c400c210158400f28400404510390a100d0006071a003100c1350400c0316407103000d11003050301521080940d4200e0b505843c0105816054130b012030000e00c1201700150160081c00035014905405c1101190b01e503200382e03150f4103c02e180c0b00240180b100c10b4050180140c008043c1b4020030240d50304a01d480504010560349082e9031030780080d480c120f20307110a03014652614007a400d944014030010081c0201c4c8006d031400103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 972917976 1250 972916726 972916729
    0x5010c05070b031807180b0a0e070f0201020904060609080d02030408250306020301031211010e03090d0c0914071d011b0302152e03110918150123 64
    0x701514042e44544841c040001241030100002c050181030350302d010b403200680ca807a04d80d924401d15052612500d41058144040ca003031141c40310301180c0c5d0f45051503050380c90754003040f60310b840e10507800f008640d0284076540140d5210f2081800907e1142c84802c1c0070303443d00740070504245058880005540041c4020850240e0200381d512500c0700441d00103048a031540c1042c41d807804140c00c043c185520100000c01041b514000c0d040c0e1301e41c0f054550341341e00284500030034241d50340850f0303852041c0c10030b002c42d00c0c1c0c2d07082014110340c8141c40303a81e1902d4140d03190303401c074000c440703000d004020610340c018248840c090300f000c2d540800560b035500241c2e00c2c00da980d001a04c9000400c201c6200c1d100800165001c4c944240008903c40600b0500d401c030600f04450314510380040e507a520749002002043c40140108020b0301d020840381e001c0840ca810341558800c008032404010f15502c80b441103050b2440c40c1a1007440680310401d07000071500201c2d418042c0c6d80e0299000e0f04a03100020103201103081c500d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 972919226 1250 972917976 972917983
    0xb0a02090111011526031c05130c1401050c0a0503040611010513030c081b03031603150b0705031c020d05090c21030d0204180c0207030308041101030207140a0b0105010c05 75
    0x699288007001c0c50131891031036501020780803174807180a640c00007240d202404c3c0200c4014020121101100740001e0311034042c65000c01c00b00c550000c154100b0790000b04030605005048d1814004141031032030504071148405814485000000c480c15000024280030554004103604510034091008000d01d01d00043c3c00c04600c00c681c0e10280502c10101d40e600c0c01c22480340112078041101040c005828440b031503000f0b9481e00155055416a100040500ba0991007846500c010307850710358410100e0762520028a840c0d510105d410f070341d21b0008000f03007040410241356142040d2408000180c1e91404000100202d40300074000c684243c100d22200030b000e988140003181102c80340e564580101000300c0712549540300e41c20807095564000310300002d0704d0071040d18078070500c605540117010343d150404040781c840b00c540c00010040348a290100e004241842e10444c0b580c0e01c10f0400504d030402c240c54403140f00c02c28001d24005e503840b102400041120112009004040a0904d10300a4206a940740c0e20f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 972920476 1250 972919226 972919229
    0x11040f1d010b250206071b05100e040b01030b0604060804150c02060718050d1b0b040e13020105040e151e18040606030c15080f0712020c07030b0a020901110115 70
    0x206180320503e032509915200d070040381c043d8014070455443c0300350b02e4010b00d80c4540d01c1c2160202c0094801c0041e031400c2800b8081c80c002580e45e615419042e481040000509012800e203040580c1c4110034950740c0c83c0c00b001400030f0071098440c800d46103000d14100c0c01c07141d15000341904050a051083c01c2c1c1c0c680002e4261303007011460404000f04560000d81d6081f10810f07500c029406510502040f09008a0464943c03941d0342d0b0401540456889442d02980c40c0b08600c03415140001440001c0c40480350100f010515520500d01989400d1303541d1004a1311802c10f03078441136950544c1855610510384507103004521001440007885001c980f80c001040f140f10035403039141140d014000a02007001c0355200310042c6600080e200310301c83c0c40d4141c841d02a0010b400550100c0d10703032400b0404041851040314480e40c440d5071218813800900003801e000e0340054054540314482c048022000640089a10b8070902821600503181c070700210004060f03410403400f020883e41f410340d00c4201032402140307440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 972921726 1250 972920476 972920497
    0x40f090b13060f06021e06070807030e1203091c02061306090212031c11030115030e0d1d042715020a0f0f02060709150311040f1d010b 59
    0x203440008840420303100c4444400144501e031411001080001c0300c900c245042d14820b83c04c40e07030710031080038400c801a80c0d025103603252070380144c0009a4061142c0600d6902c040c0074540485c042000d054140c0c45c15154081440004d48040204043e004003004100b4840c440882c601000c0c00443c64060f440700c1c0090103d100c18894440628144030585d000703100d0056000d40410b80000401050700c3c2c8917040444546050400a4081015201c0600a14050504056000d49903918040030050380141e050060410700d6143c2c2c10b00c1c006070760706200d10b00a48503243c03201070800f68400e0041a8411140203038602c1b682c640040800b2110301c00c0d0796058171080d241041150b8120509140e280b0038038001942000074000640d81e00c14903800008000700742c6071900c5098407136080c1e02d81a07807184805c541900014480ba041040140f05003107400c1c00070641c1e401d00080f91980140106038581c0203401c4103411240714541000000c003043c48000b079030b01c0a6908800254144121440144500000e07003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 972922976 1250 972921726 972921731
    0x2010f0201021317030903070e0f060603010311010503180a0c030302070602070f12030c152301030201320a02030c07090204060c0305130906142b03140f04061d06040f09 74
    0x10400584c00300101d030502d4030010200c90060340d4038002c00500300070440c0c49010031400c96002c111385050100c01d480c141e80c0e210a03171101c1044c03e00c004560302c3e00003c22481500040e00e0702c48801e602e060020708182030041c100708000b2401e5040103840c22180368402c81c11940f00c02e104100d45406a09801c00340d403548200000c42020700c0c141141e400007400c4018100901c2c840810300900010780c48101041464044403030091110310001a8201e424030020f800b280403a10a810309140000e60701065003002580100d2204503000314402c039030000726007400581e02c00908016419401c201c90030060824101c20343c689810300c0302c02801c0801921008040c01000719403102c0c05100c007205100500400c1e0b0301040003594804459200300006903849000e541d424110012400b05040e0b40f0302c0403c80c0d00d400c201c2d03060203954221084c40313103076019400d05041480340b803000060751030007400140388943e60131500d900442121781202c854401d809100d140100004c1000c600700c08490300450715040c000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 972924226 1250 972922976 972923009
    0x40b04060e041d1f0e030f190c0308130c0905011509080c0a05100210020d090312090305160f0f0605060a0f0f14030328020c060f04030809060c0303090a02010f02010213 74
    0x1c4c01a18200900049602010401e0820550368030f01034140e1404070714042c1240c6603440c40c2918042620711002d4005101e0b0380010b50215140c42d261019644100d00c210300c0c0c10780d202a1074088075400e8100130407060041d1000c440d610340c0000752102410316000a00402c0703e1074400591081301a20600b401002c154541c040c18a00a21580700710b0f881d03103401555a04280043c003001429821b40c1140841c0003180801c0e0030800c41d11546103640d51549035140760000306044c02070034140801041792083c1c110b080c948006800c81c004000c40c10311450700403407141040d40c208a4008655000350403a02c44a1104000c40007032100b040d030444108040c040c02884a04021030f055100301c107103405c10140b0a65441302603060551020740e2820b940d0f421307500094500030800441d4170403036a108010030130038070061000c164024001d1090320f030000c1800c0c1c90450050142d9041da00112079110362500100441410f5580000030305950100398030007103145c501000c0c6e103000300048601441d600c0013170012300c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 972925476 1250 972924226 972924283
    0x60b0604030609150f0b0d060e01060b0f04050328030c02010309050d02060103060f020f040902090f130606090e06031504021201061e05011701090b0105040b04060e041d 74
    0x88401464109509024a44007030801c80100480b03003248000d074619140f17060380035041c0c43c4242500110010b000c0c49041ca0561225009091034100d200c0e002e5680e00c10004003510307a00020001190b14400710342e202c6140800b003500b01440d82043c090718808007151098101c000402030042c45070316041081c642605400100d00a05056030020654400e102d80c0c505501c1e00007482034100c80c8110301c2445411182c9110300c06078015800c9115686105000a0101c0b0103103402600c0604005022030701e4003889100001c0e040c80b200c1d104501c84c03e0b03031b600782403041940c0500981d02810780501403d00a003054004a40e54518102c581040c091070b00340840c046654111644000c01c9180d002440021345541c7d030301100310702d03001403560b402001c90800692035000740c0d080a04420030f901c10842c3e580c40c0c4401e40c0301810b0342c40c141a040150030080400d10180b82000382004c1c0c081507448064048101050004a952031081c03407c08455418401401c00d03000185007091010380c08040b400b01c1100344 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 972926726 1250 972925476 972925489
    0x102030129090603180706032c01020d1b02010606141c060905070203090405100608190b040f09060b09240d05030a0807020d0305010f05041d150a0b0306090a060b 71
    0x80c0d40f04a000084c050f00c4060b084202150074880760075a440320307941c1c00c020707030848520300741803040c0e007662180c7d03102c80d07450780c441d61710080a1310350025280055103203020040b03914050040082101c0ca40741202c00e55424481d010141c023250424007404100d01d030140440740610b0040c05e200c0000020034003640c10701500300f08010208103205202c5410700003c040d489030007030b01065000300c0c0340500240d04000b801d009039040340c1d000e4580750038070740352442e00d0b10391800303c014032910703107502c0e406d02036030301c0d1503034421001e040e46920300001b032440203031509400391040510500e00c220307094802c0c000702c2c120304000c005482c4080c0007c001c501847d40040303145182c2d0303600003070f00c3c41c0408035115024540000c001841032405500341c1c0d81c05081c42d03406408440007030045840744808a60180801e0416500140c401181d09003407412891124040b240b5095198138600d071240120814000c40b1078030303805411207121046001e4500392411011455541001d000c0141519440d8002150aa240c54 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 972927976 1250 972926726 972926737
    0x20c13020f07153c05100f12060b03031c051302040906140112080a1d04020c01060f06030603050307062309010218060301030f12140c010b120102030129 67
    0x800f420039200012000e000003802c0040d03040c1d04a0148000c000d1000800742c0d11100366000403640c000e070034041d450501000341001480000481c092003c04034200d400d44544100900030f0740b82c6000301c40520314001c000c1d1049071040c280a98000e01070707840c000d03c01140c07c0b508a20800b50025092b40c030000c4101200c050810060b40091a000b810300c1403060319041703d01a0740c8c02d1952001580d0341c8090300b19989640d2100984490f90034800804403c0c07190454588043c15440d0b203231040c1c114880024201da00c095038201040e03543d2402000100500c0103e207000380001e0500300301a0303145849054a030700c10788400600d281d41d1003030004180c0b0404c2684000c1840090802100341c40c0c10b5034034038000c4d801460051b80b408444003051005103068001c0b41e060ba680850014150b0129695041304c404003040c02105100b010b6000d1030608070300070068652040408008501490000705220004800f00013544159004200501003400d040c40c1d4054903034070030103845410300200c554107040c40c05030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 972929226 1250 972927976 972927983
    0x90504050114222a090b182b03110718020906071415100510080402040e2a0907050301060f1101051e0916140a0504050c03070906020c13020f07 63
    0x814a10718200d00000c030340080d41800c03009a412513151002e0341900d00d025144901c14200710100300070b00d40301c81c0c83c90382a002c1d0708000e064000300c0b0f20882488901c40540c00684100b58440459030b405140d4000ca80384c21280070720002c0c02000d418646080c1c49000981e070041e008a4000410034140c1e1560b4044420345504005007603101034141c184103072124441001022a1a101400308100003000c5520300122800180301a80c4010403400540d003816008005990165031091041c10140b011300100103207113104181075001b007100900c4114045480140c840c0111000000c00400a8001d012203064881505107030b90280600701d41110200c19403001200a9403d11041c0040400846104d80d070000e507028042c03440350b40c3c0742061603461040d0b40303664200c90300030407007040610646002c0b600c8000000e0100d000302d546800200c2d09980d000d072140d0748000d00000400440683c0000c40e40e001c1e00141c8082d09441c014400003a01c500d0340384203d80012503000810f5181d5904440807905e80592 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 972930476 1250 972929226 972929231
    0x3170c0c2d0f190602060708012103020102070c0e070f03020c030a111c08150111120d0609021204060b01170601081e0f04030201110913090f02120d09050405011422 72
    0x401091240d48000034841c02c0094821071007c504075600407000681a10301d0a411174a069a1031000c41ea0320840820f415030a65500b00a40300118469503007180c05800300804406c00c0741002c3e08020489210000504101807042c05220740140d4044100c41200780203141c14038404c1c12002c1c0180c20400d007a20142030007140d4002d072011b0281c104007428403401c1c0d00803814017180ca00303800649241000074607041c0c03103030042c06600510a031010054004107000c140e002803115140c0c0c0b40c44080382d001040c1403100c5001c1004004c10003082c1d005078842c4001c20710700108400718003960321940c8500a00004e05101402e40006c3d441d482c1e20f04890913186140e61a00140d09250180b41a249010f0745c0a90055080050044907620b08004541c1c1201010f0003104980c00c041601c2c400404241d8000c139100f070146900803016a407551070100305201c0860281447e10000303d00500201d0300344e40501c0c083d504160042102c8003014620794000703201aa00c5240302155081d1416007020301030390103041c107803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 972931726 1250 972930476 972930499
    0x8070f02010207240201110406050d050a020d09050606030d0509102102220905071b02030a020d05100e0703030c021309050d17180c0d0c03170c0c2d0f 66
    0x5021010305803944c1c1d134000704802c0c203540e503a0030711a1040b8003d40010070010401088007104a9102c070360300c02c05485006043c203e0a0440800391102c2e40c905403a15408082409000d180030310220021001e941080703882d01c5013080103e01c60708041d4420109021020140c01001d00a03140c840b200d06200c0041190748400c560740d2112250004040c410500b180c0d400045207454640c45103d020310f8050300c405002e02c000d40900c0d444c41c018600126014003030a140100142c44d040d07104c1c1e0625124070040d00d2151488200305088541c540000d06030781d4401502000480e030840d41e004055a0191190007811208856440107440c203844010454414280d1042c41c1e66404810615400c580075242c103819110000c40c1d0500c40c25004901c480b84d0041d0129020512302400b607440428482d620400c440c0786d90303885821400948034030002500b1000120804000c40034000720f9500203085030010203420520001c400001104242800b518121010180107583e400400310150000248007081c2c80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 972932976 1250 972931726 972931769
    0xf0318030c0e0f1605091c0c0806090607051801081f03060606020d11060705031f0603020703090504090b060103020c01151715090a030f050c0105070f1b08070f02010207 74
    0x200400c9921401464018011130706020b100e5980c01c00380071083da00d40341031094071400c0050004000900b0902c06441201850000d01440d030500000c043c03031005400c4906e06080c4403418004001c24610401c0001c002e0200b0440c902500340000c202c0030700c0e05800a030b90b05403003d00c03061130308100d104030600910030000802c07826400c46001d03a11140c1c2030302e4076042080000d9407100940485401c5a03004007000600c140d1042e80a103902480304110381411300c403560303000c02c2807128542024002a800103840300a058000104100512055500300a122996210340c1d42c280c4014000134100764002034507641c4031009401040742000c0100303050221542d904121441001d150840021034000e0454a55130031522000c941e22400781900602907100302d558046482c1a5a1404c880600a051002c000039010900c1980c0c882c01d095240c46002820444019000c805145555520700b55081003075800600b010054400850340801860300c14204c510050703080030442c0d046078090104c21104050304 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 972934226 1250 972932976 972932999
    0xb010e04020c0f120f270d1406010e09100e1c03050612030906031302130c080a15050109060c060e0105040308180705180601170a1a0901030f0318030c 66
    0x2014080d400301d0312102904031004130320340100002c010b52014140500c40f00890001070240c5d446000300f1461109011680c0090074a0200c00d030280d460054008001d022400100240c501404c9220804c048a180101044e50303198000500c0e640034540318104418541820402050703160340d41d000c2114060559107009009110071134219101d012010840b40c00c0041c04012542ca11101410242c81d5994101211400d1499580200d070040d100c41e89422046603e0702c2044004a5690b6908000f400c000c00f0b014250f40c05000f4208954a0070305042005d80e81048003881120103074208111103448a041020040003e00a1134109500340300070442019400240303d03205040b41d000c02d02512903107541c49660b502c014040e640c2c12180228079040d00d2150f038242a40c2c420014506214004580c0c11440c141e000165800a602c0f0748808060158001429485449040036541c81c01158919120b03002c0401017002c000d014010310000340c0721400c1d140204000619009502071145d070b551410450344 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 972935476 1250 972934226 972934243
    0x309050f011a130b06091909060308090339040e0f24010302060a14070c06080703060e040b060105220b0703090e062d04050903030a0c020703050d030b010e04020c 71
    0x40b030014a009030441070140c0c82004e160f0039000d0999030800c030b5030400340000845420b100c50b1101c000b1610005d00c101d014065540030310f110304c05186d26103104400381458047d5800010403074181480c0030a09030404c41a5060120b0110081c590203004110080f800821110144080a01510402d81c0b48018002810011a1080b90000e03451114240003004841005c1c04000e500c54810400c840c1064402d0124114a4070100c54036441e10100b035803180340110700c0380c0c08100484c000d141009103080d0113101d900018065480f10101c0d5180031b982e850700b0948014081030501c0000b240850980d00d200300b81c000101042000ca02d206a110a80c00710507400c60482100001c40080011820003000b0560074007441019000c090740d41c4a01404102c1340781164400c0540c07468042e01541e0076035950040d9402441010050341d40c90030108890002d4034000318061040d9808998100006107001800a001451764600051225040c1c40103c402180f06240260f0290022400320441013020600d2070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 972936726 1250 972935476 972935479
    0x509180a0b06122e0501050a0e060706150f0f1e15090305160b0a0c051015090608030a051213080a0215070914041a040203040812070518010309050f011a 67
    0x1407021aa60b1400e03413000001545511103145890350801c03003940580041c00543d0102d080c80c2c101d80417003101103615600301c0c60f015110741d6103501032200240010329010300a00000d003002c20300d060400c640c03294030101d588a280b0b0780c26403a50904107071076003d0600001070000200c01c49170310389003141c0080c0402400e0005036114080c0311100081110500b181c0e6044401c001007081c180000150240c1d400c61b030100040c3c030103000da9141309903a402d442c41619000380a10b8418100d450414001d00219030150b0000c03d015402085409400380d004025189540080302c0c20841c2581e60a540210001302244c0041404501082d48040b154002c542d138202042000250716199541d800215001e081a218503146a02d202101042500b420341105403110881c07403010746040c1007040071404a80c0104c8040c2c0320307071102180c0c1036229030918442c1c079089881841c0a0b030418040a103102c02c15403104521605260380c903428841042001e03c02c4002141c45400200101d966500440f40303031444400d01c05 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 972937976 1250 972936726 972936751
    0x11107290c031801020306330d060602100e0303060d0809040f09140706090902070507050d030f0f020c09010b0721091a0403080406180b0a090608070509180a0b0612 72
    0x1c681003c052003a648111001002e00c010842e082c4d0f42a20001c4101d007680d1354400182010b90001c03101c3c0c034018811100c1a802c00110240340c41030081c2000421903100300302c5400d00d8500c1400c1040001030f02e411020440321508120f140c3e2038811540e00c15071080d241c0050904003914501d90540c0d000d624881d0244070345c049101c1c2500c80540d21480c05003e8803010415010301030107051200d90142244512407000c03550741d07607114000613201c0b40300b0000840010fa6000d60486465900600528003104940014508842d808000a088040c14052506204804522042031001d042c001000d028100b030405086a1100031009101c0c41c8a400740c0b1101301007c084451070924a0070880f401c490300040340302e041a0604800b1208505000a001c1000c801c0000110744411940020130520070745464920207070b454400080c00c2c0c00380091502040c03140078084c0000a841700d00c80f58031055540c0c0c003a11116034802c00c140c4010300441c00501d401450100d0389808003500c07003040170f0060103d854074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 972939226 1250 972937976 972938011
    0x90914060a0504052e08011a010906050a0203180f0603040f0b070509060904200a090305070509282912010b100807141908010602011107290c03 63
    0x2440301392001a2401c544081030780340d0286001403d1a40000300d0503c0851955503155035002441c2034400d441c2c07401071841c5444500310420f42e0000711100041c00917040c403504200103008041d45030300072000c109040040c0e035001c01139a85e0b100040030603003090060203a51a801c03e42061641044072440840b40b4290820114203400e00a50540e001d41070000e1001d4900541441404007030100076452401e40080812200c4001c0c800202422040a00f941c80701c401c24034504020307107000925480140500003c00c2072080000300014254a60903942c0340340c07a00c0312111490100144403031120708100c042c04c2002d1704515290701d0700040301c040040314546131192824101ca0308032028039801c10350051130f21482503401e0f0b0007a19610f50250203810b00d035005401140215400d9845400c1400c54419021800110660081034090143c881031000b0840c03081541c0e401d9540c6d00c2441c0000e08820703041b0010495454070700250500740195003100d48154180480395003000d42060342d0075194940440750 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 972940476 1250 972939226 972939229
    0x20d14060a0f15030209150c03031f0501050702010f1119030e040c091208070501090303020702030618030a030b0a0b040801060305060a02070804091e050906060f01080c0a0f090914060a05 82
    0x1000c25a146070350350500550319007106134000e41c41121020f030094502c002c0c0c40030300c001a80c040c3c102a101034025513540d107011003060490392402d0761441002d5040010900031a680f280c107856196a081c28203621010a01360292a9400e0368529031455124410241c0103009514140061203031003074690101600d02881040251203000c001c410003d101132030200416548015114165802020701a10700742c05515402e0035169912000e9021a400040210860030200b240552040240e005901c05001c03040002e5124418400d0220806850b103401d52b90656848000f0070052281c2034800c4d036125540c00040b030181c4954402628240103040000303a44c1d01041c0201d1351200d034010139441ca8503091010350380081144000e81030b5000c03800c4903002420ba5044c032515000d1030643c8001d10480c5030440401104803001c64055042014040038400d940403e90b060b501c0050306400c00c680749007940c0000311200051507000e40007450400070f410740d1640c0203003007030fa010b04000c0d81d000103500d032100d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 972941726 1250 972940476 972940499
    0xa0f23011413020105070b010e040b011203081504240305070b040f030303051905090f0d142505150604110702010e0f011e1205070801150509010201020d14060a 70
    0x6841c20900740041e000950b030904400310207122540305051481c00c0142e41d84928414140981103124454680400d12050040601c0b92a0042c42030f10202c0c0c24a281d0799030024403900010340b5050003207071107881801241d40c03103400080740e0000e0360303040e204001e0440000ca041119540f0040d24203010b11407001c188200031800301c40035154541c00400000e455550300300c00070140200407600e07640c81d1140e0f40c01612954000d0754002c109150042c40d443d0392107041c0710f0030084181d04c03000034400903000e0341c120f200050040c0c82c082e0540b0840142d9901c683d0401c010340da000024001c18500030f1a08400c02c04443c0c412150089809590411507501c81000c1e40caa80e105a200c040e0110f10340d41d100504500d084c2c0b85490245006241018841103c2d0504980c1035400545840204d80c1040c2d8100c0e44c0c1403c5d02c20701d58041e01da13240c8030304154900382e0890452003440300803004000d070004800160364001d404a5502002c242c5041009501d9442d0780702c00010306503000307481405102c500084a00d00751 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 972942976 1250 972941726 972941741
    0xf0a0b07061b0201150621060603021c0c0c080c01110a0203030708100e150a030602040b0a2606100302070b04030f0e03120f0a0201090512040f0e01121101020a0f2301 73
    0x1070140c0080a00b03004003950340565109181c490347c1025044602d41c0300c0b0b00d0081178018140c41d01c000d03890320f54201110601d43c054070804522107241c1003101909550208c0b03003140d031a400900c000c0d0b5840201e80c2103409418a0044525204000102d50414a034000021807207401265a0450300f601c80b5128606d0007500b5101e6040d46480003070100341d0301c80283c420803000c00700c020b0152900c03079580d07075504060380c20a5214555400c00428100501500004107450b0b45180d400200c40c02c0b614007000c0454288050314842c0150199141040640c0c001e0b03044425568100d2005a031900e05403400400035440d40010b83d00080e015011054181000184030721481c0c0540e00060818606101c3c250040d084036480008541d21480d16502050080c49a000c04501c411030841c2d80d0f604101c02c19440c0143c6900012442d4501c400401102c82400d85100006030710030503600324031820b000100d2822402d0400581100481c03100d4404000400354041181c15034500d50300050070b130034002c290803608070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 972944226 1250 972942976 972943001
    0xa210203060f01123003020406030b01020c030a0807031b060603020a1e0e060a05041a01080709030507050d0206191706040b0121060f08060114120a020f0a0b07061b0201 74
    0x41c80541390001c1c0c50701d1590103401c5111440c04255140041d250551740681c11901e501090307000030107010140c0c0c180201ea4034010700b1f00041034070501c0400402e60303a1511503009059405c000c80d00c1c0040600c02c0b1441038400100e0b0f041d4050100807824030030005c003c0f0780b10803845108a00f00c00240c0c040d1460a07a20011800c0e10800ba403a031400d051140c40d903100500c01580058203c50224207030b5103c1c403a11002d541d103502d0440b820b41114002401c9000c003d4020b03810300228030310400006000090b132009841003650741944041040c40400c4060040c8580c0ba101c420b20303041d40800884d841a1820000241a03580030a55110720003030100703c03a04000140d0000300984503403070748a10650020070f803402c0700790b50020b032007a600c403d010300603e4207070054225500448010459081404414880304208596501010081c4007645030b0300d0304410f900901410f003010072004150740341c00084e80100400c80c9004d6540e0441d1810000803e42c0041c455107040100141b590007600c14803c40303100404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 972945476 1250 972944226 972944249
    0x105060d02060d0f0f14041208010e0a021e0d09060b0f06070b1306090308010e010506120a050403140a030c090801150e0a0b0a1203020d0f020304060e0a210203060f01 73
    0x2540c040540107421440224503000ea15004000c0c011175191084a0020303010050303a0000e820075180043c0218000612542080346400c01880044054650305411072540480140d803511000148401c0e0691202c4401034424007080046403034100b40c110600062065208000702c41410041050248006424680140003070040c0300000701d0888045070010164031b059640c0994558416080ea64000c2003240060ac0210040010344180c0303040602610045500f203040c440003540b0b8132850030004005100701521b038004101411300440c00d609212080d407070701c29600c00300944003034094021101c01d07500103007a0150000300001e042c13040d00c001c040c80005004050307180162141403003c0c081d018864581d640e124221107955807504404c000c00c607003981d4019514090a020741401400132144040c080c0e00004403c1490303020003101c05542c10390a0002001d00300201150211882e07400c05000380b01c40d880703e1402400c4150500c010603100b00c1c01c43d826503403640b0303254a4200f020b2060584407107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 972946726 1250 972945476 972945487
    0x6150405060c01060e0c09031009050c1e1305100f0b0313081308071701020c0a0b0921090a12032a050d0e030c150f130803030907080105060d0206 64
    0x240c0741c0000e00300945048008980145c551151032031041050f640c0111071000015468144e040511500c92918054001044040041d4a545480307200a080b054843c48002142240c8089007540d050800c0c82c01038001a11108843d441d900104015a4602080d0214950000c0e001502184100989143c030f40707042d0660b00c0c0d200341c001c40e05517442303030849481006100f104040219108014000c1050200901856241161554801012112001e0b8690040113180d800c1d85000650204985c2d205402d0f69203a512121403e081c109070341c803000140b0f9042000b078994540803001030701405034103d03084017801c1d5440c1264860848611001400b05211050300018030082403050b04c45030441e28048541d8400d5983c0c0d1a00388444403000c1e20204062542c606100e09040051900c3c4050a94001320984500916070a07540581a9690001c1e000020515800075180300003030014450b9a044039100e0424030748846c0c0750512800ba2a045601e0315000171107500d4105071028038150050281850103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 972947976 1250 972946726 972946729
    0x9071202030a060c050405030a0b010e010b031e19020403200a150503070201021b01090c090c0c1b05040905070e07031a010c0507030c06030b18010302010813050c18040b06150405 78
    0x402141c0e82c5102817003c24000025191030902001415500c20b181d101d10039030502c10203520034401a000b46460f42c40520401500002e0003034040d2440210500041c016074901014001111031843e000d0407050000c10000308029107607099100340003803442c1131919512800140400000c0c1c51058188906565081c080c646010b00000e5421a140388000f51411485129160000c0c20392176984c112603640d0b50581c02401030712034001010346110300e014040310343d01080003441342c8000c1201802ca180702107211402c10203144401c50041c080640144071b4040e00e03040c200c1d1590494401c011007442110000f40d0018071030701c00c041d2030401862910b1a00342071a801110b2401e14180200c3e0f061050510200124502e0050680144626540410810f0080003031001d0100b2600c0c050310141c807403400520040c1e8112001580c0283d80411000c0c0651003420207a06d000c1d5486412500b1a900100d51980c0100c07104c01d0500ca18001c2c82c0d0085161a44800d001c0503d10f4040c004550740014803050025 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 972949226 1250 972947976 972947981
    0x204110910180b030f0601021606050d021b060108280c0b0906070c0b030a0b0904020a0509090304031a040209060f03061f05030f1e060106080c0a05040b0c0609071202030a06 76
    0x140c01d420391080b800a40c81d8410150340d035209640140040d0108010410f8640c1e0410160000054102201c585240781c1100038106000e41e41014080716000700c0e080d00642d00604030240046401d40460383c2c1075940d142403940794180c0c850800c0907004005110114141e41c04607400b150b0358048692503c4524122000956400040039182d000d6810481440401d00209291028090440741c881c1da0f4280968403a0444d1103009007980100304030300810015035a4a41d080048641c19541c0250a0b61841003050443c42241c000030401080310250010050100004038400c074400e0b07490f80c0312601c40408001c42541c5250401da0b060344501c000808500040c01e08040c40603100460f00000340c0c0304d00c0020f0070200c04030302509040d07001032002122a040c80b81c2c40325104030a00c025000d15410900010240b5200a00440e00f200380040c44001e25032140c0c0c12a002407030a0f0b144140c985080300c0195445a0050310005c416100300ca6001c2040c00c2c0c02d90941980741d5006006100040c22603590002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 972950476 1250 972949226 972949247
    0x60f0d0c0303030b060d020c0601140a08120901180902030f0a0603080714102d110403060e0c040207111002030307020316050f0a0b0403080f01060e0f0a0302060c0102070204110910 79
    0x104aa800e0000380c0048500740050f11391248c100018100640c103000f002c42040c0140c50146200d2684090f00b04103020011540005000c441d02201c1d5913600b1a80c0140c0d14024805d4070800003090703030000082c100c64581e000e140034154510401003142c80c1c60b15034805546039804040c1c60141c0400c0103200042c0c0038a05042103404c80030a9442c0c004844041408444001c18410211908405c4004048000803009402e506105104205040307540d0811640b0740150700000b41050741c1e89486506c503280420100000e00d400030030565840c0750f61325000c0c0d6240504c1042c14000da40030400c10f00840d0000c400c1c0e9110b03510300e900850900000c00c08460380b00d8070800007551140590307542400310f04001e11030310301881c0c0106010109410540703001441d2240003010007440c000c440b401400060752028000310700c400c0441d0f00b54008400b05000402059441c0e000945c0680000380600c4080302c103402510205000311001c125003640030b00c604805110714489241d110281d10480010a0b001d03145550 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 972951726 1250 972950476 972950479
    0xf0923040c0816090f0c0f050703031b1218080a030b0f100309021801050321120907080c0a030b06040c2a1202031e161505060f0d0c0303030b 62
    0x40036079495520741d08141c0b010f841c030110081000c5060103082c0e0207002c0c00340411222407042100d410b4041004040c41008040c4404200f0000b400d00709061194100580d10004407103c4001c940c0a00c0c0c01030203603c40010150b4a4a081245006001e000d00300001903060708660072516000340180220300a219804405504c000c4007045c41e02ca50316540140c0d4024840354030002403000721341c0100480008881e9458948418400050006807000700e4980307021034120162641e800c4041c0545c80da10302849108107180804141085131443c0700152040c111614003046d517220000d8042403001c62034140c0406804101044041405410268803c80c000e66241c036055804807513800d803814060228003000da00c01d4030b03910f1004081c00845c2440341d500707594500066182c101d030340007102d2103c0030000c50035107510800304a0446941d0703c0c0706001441c9a0203010b03000812043c0907a100281030550b140d90003890030520800c081d00717001143c504500d40101500208500d0b5a4084015180f80d80202c0d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 972952976 1250 972951726 972951743
    0xd1101020a051911044d0337021305040911040c0f020c060c011e02090a050603090613110a170f031312020105041a070209091207030810030f05070f092304 68
    0x1b000d2110060740181c1a40707001c4c0041d2a6241042104154501c11044000410b50008104d120856403441440390b43c030008040096100c80b20501c61100c942040d500c415005070900e42c02e00308100480b907000030400c104803820080310200b00381c00c803400400c0e02d14800c05070b40310b44811030b8a440c003172000c0d01200c84c2c0e0303600200301c50f11503000c042c04100c192044e8401765078020500710001e1801060300030142005684580c02d515221500c0c0713a5969001e03241d0400740d4008006541800f0072604014031051000d07091105459441622a051404030004011070b070044607400100d40401104580780684440915842d0300c2c1842400c88680e40d00f680124148003040100041c0003074000020026840c20700051611800540140011400000e10341c10351a000012981e00c00300b442001d0f50541078151610100c82c0d5104c0400e076502060a40000d0600302c4003020ba1020080005071620655590070300d5405074a684a01c82e0069800c0c1400c0c6110650304c040600b26200ba00e08030702ea038014040c5851 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 972954226 1250 972952976 972953081
    0x1d0913060c021b040504030c020d02030a0c060509030705040c020d081801090609200105160c0305160f0b09060403170d0f0509120301050d1101020a05191104 69
    0x909048554401600c1d0150b0044039043c44000715040d80c0700c1440e0300c00c0d9000d001030f00e025a0020a00014500000d02c10204046903e080d504e042000103031080e070010b40901921f0312480c0242c819040341d01c50303e200b8400c120340814942442d01414450114940003046990344181c800e990302e51008114603500b082180b0300003800d038030902403041241d018550015060750715003030070b807120f009400c01c041840c1c0540707900010305d0340c3c000c0c202c5035440822000c6206404c42440c01002c402c1041e4400f81c0f841c86500ca01d2011003c444040310b040354080d90707118081698907094041303039000351407226a001c0e005020030404154428481c0c50302c2400001950f107407118600a150485401d5940c40c200641c0e0343c404c101c0c8101041009504160120002034119898500050020440048002c01c6400c01000440d0603034000c00034070240c2a84901504c401c0003190034200082c104c8013200b5079107000e007803000c0300081c1050300c62036400582d00d0358094141c0c103041203442c0c0d09103540344400c032a46500103032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 972955476 1250 972954226 972954233
    0xc04210c0b030916060507060f150306020d0905070f080c10050a2a0c031e0c050f031e060601091202010e0114090a0803090a09060506030a151503020c0d1d0913 70
    0x1c102c002d05210b48032117803551042d06080d030849195000302702d503072440c0800240082c15000701280880768014400f5a8072044080c3d02e201514a60f04001d10500c91074501080a1984203c00029242c0403400c5440507000c560809c503642e500c101041000c40ca080151901541c450f0700540482d0f422040560640b1550134089001e004500d0010342d00b01e09400c0c41030040020301e00b000036200a4400302018001140d440781d6800c0021031040611426903241e2041e2035031000d01c070b000407405000007100d5003503602000003034a481088170203a0010380040c2d40030815401041d01d0002558040e95810500c416140056920b2000c54410003010401400400d0b819516000c1c00c2000e4481c3c1d5010790740320904d11003805206c0d00380e900700c03600f040d041038820f002a03101c1405407030340940d10000108400201c0c15072680000c86e141c1121340f1914940c5240c200c095050717001054501041c40440b0303410740048200b21243e114012200e0742402c1582c8411109252112138182c2225460014040b1880d9942d07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 972956726 1250 972955476 972955513
    0x40803040c0b0703020105460b090c040801392d0207080a0f12111207031d031207060f0e150c07050d03050901090b0c04210c0b0309 58
    0x4013200107039141c17410411703004a020900265076002c08503c103100c400c1030030024891900000d02000d004192600183c001a80d41c201c8004c0480203400d420440c204101c42c006140d0250044c0ba48071b41c2031080c440c4241d8801113000e0319842180c040d05054085242090700d038005240800350030424503000b00028800ba40045030302d081e000c2c0c20440000001c1c010041e0404d006a0711604180e0040301544000c40c01c2a0504042c00d0f0344040c4805506d01969001d4032400c0e01c800c3c60170020710414540b901c5040052000b00280b0b4029102c0d04004c84c04402a612342902c0c0003407858041e00000d00d254039180300b030340203010414410500400d26000c1100c04200b121800316404401358000b03061505690b1407119001d400c20752040340c4600e0516640c580341d580b10350080810040503629000505e29036420b600a0343c07115800540c05201d4142101142c90540242c05084501c40650003240403d64125600c42e02d4194002c1d20802c0741d625100c80c0c40c103107402c014100780355809a082e0400c10030136000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 972957976 1250 972956726 972956737
    0x120d1d0d0204060e063f0a0b041a0f070e040515040207060906060506131a0705010504050601181413241b090e19020c030c0601090f0c08040803040c0b 66
    0x1e903001841d240800411200c1040724141078813100051890038a021220340f001182e130b00b40c400410106e009191150b903c1c02601c110090802e0601405000811100160482c82c0c3c0c1140004000d098075642e100c030711710b044183c5070071002c14108000e081030390070302d83c22007940070507258501881c2c841c170080400c0c180e0b0b11100c0202c450359620034400c2c00308082c0d80701d0300010300400c1d9691403d2240c0e40101c02e0b0440254001c002008101c0342c00e407121308003404222910580d12500a00107820b10345416a6030381070a01509100406a032044003c0018034031401958081d2078111200175110070021110503581407200765004184812001c031108499034005605506001001596428070051300100c5070010103090100904a40e080000302410085250402e51009521119680c1d420001e0f009101c2c4103544566400042a00c8228901c0402c100d070484a84040c240848043d80848004680c42030351114080341c022804100420194400745034400e10038001110080d80380d54500c00c803500075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 972959226 1250 972957976 972957989
    0x11120712150510030203040812091f020d05180a11040e2b03090b0c0c010e0d180b03090d12020c03030c0a1b110621090606120d1d0d020406 61
    0x1160108150f0900d8071414031150414501107045090941d1010094030400c59040c030000400740224029010030700c110762118101151580c6000078102104002c1e401c48101302d00e102e89070500094005901c800a41d4900e090a00034000b4151955901080406140b9404e6003007940c8440220422204001813444d00381801010b01000682102c031490400c00c0900724020141011403040008800060382d45d0000c180200305a103031541150020b00402100716000080e01c180000046d215402c5041c8004000d505101040407070307140d11b413640c000c2c4001d48030034030075a121050130022607100f44c1080419800301d1074007525025407090002d01c0c0d50001e03641c41c0c50f0400000b41d4141e659420a10700049850100844218030000e1344912200030040800c0c0d5009070320014090380801c005814040341c220603851902d81034240440d071966115000c4540e41d0045400400700c10346031500080b603900c0840c0580c0c4040c45401130540c1c141c0e81c00007101314a500808116083c40c01a515402500301800c0b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 972960476 1250 972959226 972959261
    0xa2007061d07080a0b061309060506030c0301050f1b22060318020a0501080c0d0204030b182b170f06010f0527030f100504060f11120712 60
    0x810780100207014080700861641548034403810031882902140c00180650071100b00c2041d170b80c0d600c010840ca524420300007903605151018600400c031055010500803030040e02207036540b0445c4002d043c01c85e00c0c181c03a8030380c0010300306000605421082e045030146603c8041d655040107000024014103d90b00500441000e51115080c0120b60b410700c1b400c8214030b003030784410100c06d0706500880c01450440c0600340c100610f01d00001d100921050448090410842c1c04650700d0b9501d0500d00e5450350241e07002100d201c080c60364001c851a0000e0800440040f11402c1040a61a8084c3c201007402e0541c41d03030140082080c42294102d0440e08051042145102074405ca00d024400104171144c62220031003070110030b00150400c403507049070f90028195180da1120326403000340006441d05803403000e40c00491003540c0101e84c408100c7e4216500a81c030130709041c0840c036428072102045d54030380300c000e245240c414040c0041401c050409250800c00e2810403c04440d140183d04054490000c4903030442c46 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 972961726 1250 972960476 972960491
    0x40605060117010303120509030405030a0614060a1505160c090b03120a120905100c051215060319141003020a080c150a050c07030309140a06080a200706 67
    0x1600002403149402c0721040510266040d50360140a0300314001c2030180c0345580c0c0f0000342c183c030010401c850250800500f00d03030703442416140c00c001900e208200e50200d00c1d04440421050700b0050005000c2c1c80784010400740300101b01e08101e0391a00f104a94080e408880c1d9040c801062403030f0f04040107046407a8000c00c407510170800389803600d4000004007105000c208030540c00b840d804a6100b2201d00805001b142da1540c13420b10a141c141e0310b424a0028038035002040c1d4400d07404c0320041c584e46140c04848146a80c604820044101034421a590800c1c000c000107111095502c4140f0450200400d00080c0c408118400305c8a8103000c4030200c0031705068a400340f080d403030690441c000920746040180b001d07a0210700420080c0c0b801c070b8107482c014000851000f02c42c0e0f0250050314540c015070740c22116420352780e08000303000800503c1440011078800c559081c07141082107030301040d610a81c40c0c9143ca600c1e540b000c84001e082038108541d50800075420414005400002085094000c403400326109 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 972962976 1250 972961726 972961729
    0x3260d020d0b030606060301090c0c0b27070305031e0c1608010b030f070b0304030908031206040f0b030c12104d130e0702010905010c0c0f021e0904060506 68
    0xb2004079041c180310703500c0780c0308204003640d903002200e040d6001841c010580981424064440c4004103000400c410503071303410070000000121000018084003107001c00d5480c0c98800b01511a4803500000d0042d4201b04041d4002c606c220381c0b1951013807056456181b6000c2818000c9007020640182c2c800b0300b07403100c08100b0503aa8240541c0d0004d800441c042e008410003660942da450905216411342510040700080906008211070001804000d041c1d0381e035082c05005030000c4010407034031644503620740300b00e50075180800c0c0f081c8088404040e000b007014828401c200103131103001005c600c1d19442444c41500c1c41424600940888400904c000119000c0780c08600707403404144204140182103040c03004c500c030f1980c82c40c05d14075008503603a091394881580b1b56a0a2055140d002005240400c2081c082c4883d03056000c02d0682c0d0061000700319611340c02c1d80071105010607090147c483c0303041050403805071402c1c22403903a484041960000741d00f0b40d00300104010030b1302114141c03469a030312000c00c8003a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 972964226 1250 972962976 972962981
    0x15040506010506040f29030403020d02120a02340303030506120105060112090c0302300708030901110a0c06081501030225030306030c12170304020a03260d020d 70
    0x5020103e8080f0705041c1003810308445100140f292240031100c0c608012080803a46030b202112100ca04107540d6249824200030313555800042500b401480360310340358021224172005a1b0380b540f0a80d0f0103807802d24100d007a850450b5426094a8580400d0407684a201e003008410300790085110b40c0b804a007924001041088000710001040340307a0341000208500c90f07a2024003c01007000c2440b00041c0301215080c43c00b40700341e054100135049060070480039100707404440002081000040f11505081c40c070122a0385422451240c00d039684c2c402d025502c03540d80621824103041d101941181c1c4047e40e43c2c0c81300c0c0d2000c01c0a5010754040b41b030315401e01600d0300c241120b080b1641400e003000d518160002000d64100303442041e04c4210074504041c5001014429001840115040010f00384002d40b10f1200c002055410841190031810000d1401d150b40500340580e072055030000c015025040c5181c4440c1c1c030700642c201c0b030a07070b200c04e040e07003440801241134024180c0480304180060302c50f1001c8010004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 972965476 1250 972964226 972964229
    0x10050a0e0c0a03121b02041109030f010b150c1c050a090608040506010303081306111b01150306110d061409012106020d0f09140d1106040b070504081504050601 70
    0x940070600b018000b00b00540149115516149490000012240240c2c0020002040000c0d40b241c207203030b0480400b0800348080c00810104500351030845100b050080d08a42da600189500040d017044986003080c543c50241c40070003030200c143e40c002410034034180c0c0f491222041e00c0000caa400b161400d601707039000e805e1a01404c0c0a08041010f4145500e8403956610140310003010801c0540000e0070400183d00038034100c07580b085040c031600347d03499034ae240d99810903011a24180aa84080f54a0450500522021166100248659030300310388642015154a0208036600c010401584074040603c0c0701d0302c1d000341800700000c42d880c4111020031007080c0c07040e03000c0416540101020f03840303004082509040e40d50b10041c0180d441502e181d90f0700c05071041c4184407003c40d241200071410700540c83c0c00340451a1241041d41c0d09001da10105035029500c00076031100e83e0b400080002c0005408c00e0200740c01180a091060a0650b00c8644074907220b0020312605203180351a00780030410404200090 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 972966726 1250 972965476 972965479
    0x905061e0708061009051206012111090924040308011d06041a060708040306271203090f051501060509010e040b0f09100305150709060e0310050a0e0c 66
    0x922428152401002e00380040d008130b20900106140d00100d0f400313403c1c0600201000380203d041c51000203d600d840758824400c511011310000507400485809911071901e00f9844403410704034105680078040c044100501c041881d1181c0300c01c0da11048980030703c2c010701c2081d540189126241030314006000d10f00c11303400342d800711205040b419000c0700508109503010105480002d0304002d044002d20000420320b258640262001420a0900000c80700500a0707a010320002d000b4015035100b581035180c0340900c0140d10b100180790840010741c520400100500300343c60042076100d0141c42d200100300e80c80b64104e83c1c030f0740090035900c0903481c1c21502c603005000e642841420101c150380060800c81e450440584034590728100b0009503a1000713410b5406810161440d03000317290104400001e007295000c00d56480c4520f06078510401040c2081c2d910410250740d640c1c1c4407529000302030baa440312095015515004411600094540d940300743d521603003200d0408241c0313508480019041c60320004405 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 972967976 1250 972966726 972966781
    0x1211030c0f01052212061406030703020d0f080426010c0926010606031508010603020a0b03041104050906011412060106051b0d120b06030f16020c0301090506 69
    0x440d401e0380c455280d152018000c1c20071a03a544144040350720100980c032202c850404442030042003842c4000070000f600340c4520070410500b0001c0800640450007120400d90660140005200606000701510603940c842c400303141e90100665118450b60700150803002280500aa1007104042441d44011048003104c008000c451303105c52006040c9480c9000c0c2c64040c51441c1c0303869000c01c182458031004c1401c290002c02c00b141c1c0703070345000b4068030700c0300e41290410900c0c40001c18a094188030380c0d811a58000c101205480c0751600c5040383e07400c0200161004500e004d5440f42507103a50081a1040038480094842503040103d801e002d180000310490060042058150b051000010701c0c0d4107681443c140943c807414107007034440100c0140b1102c409036000301c0e400300c01440c5d088008418000c000b1071083c4400c5141e0740c2032100c03d000c00c44d00c00704025044130200d00c0207003001c103540041510520543e1061030000e80441d0940d240b808007140c80c1d81c01001003000f03044022081c00c80310035410a40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 972969226 1250 972967976 972967993
    0x6150909020c0a03030c110a05060f103008070b092a060c010b1201060f0605190c03050904060f031509023a0828020d03020f04080601121103 62
    0x31580d0f034104094000d050641c0c6003880c00c20309002d013400600c42800c0c00200d81410001d031400c00d80300c030400c0e66896241010301020134100d000014040050324510421000d00c00e10350480b04004503000b07900100c40c03031240d800881c08607100000a2101501581310004107003000201c461130060001c0143d000c2c40c802d1115160a02e8180c100c080740f45100b110b40a881340b04450b4210700501803025159071000d6103404000400c01c064201d40215120903621880090740ca41c426103481c03040e04032220078030443ca40240c0d030f0303680103600da8101103000749041ca0401481e4404134084132015040720399100000038040040091446158241c00114a001c1c4680300701075011034441c501c003521000c1c555584c4c501c00310340f030441c0c5041140041c0b00b18980e0040eaa03642d041940b410f5201d801e555080c6020070601d01146c075900815a415250598006c2003100d500c50030481c000d400518600369403400400002541c510708100041c060309070074510300c01101e00361070032014081c0c4c42c1c142e035402500300c0c898 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 972970476 1250 972969226 972969247
    0xa051209030d080a06241e05071203110a0c0c051915050d020706050109150b04090b0d1506051311030a091a0106030606020d020f120f04090615090902 66
    0x18456121515803c0140181e00c45400c1c48002d031205411441520036403070b0012144070445410381668a000391120840c02e504582c00076000c078544854207020440c00c00c50000012204402262003a910785000074502902400342d89017503110500c08c50020b08003400c04c2e411700c9158446d0800415048400503201070300300c00d64800c103140c01e01ca50442e0340e10900a0085a90003102181c40c40c07040b0050840d40c1c1e45541c0390200040c00300f805220341007490301021151030417082101c1c4c0181d41c0c10b02444c50426240c5059a406040d41ca0301745070b0000c40c03c0c440740c00014001e8908c0140359031180700200d00707a030030a01030041441901c0012100e45041100c00b407034410b5448101e90b0020014035001c1181e10203400d00c05054a040f00c1041c007007900d48400001c142d58107a00c00402d613180c43d400c0d03a0a592642404980c4c50792640424012508040e210040c581c0304100208100820f00c2042d50505a03030350b40503001c96099510006c2e15596500c4043c1d8803e901c50764000280020090860a0481915 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 972971726 1250 972970476 972970483
    0x31f031203150503060a0c09120c03150b150307092c0601090f0e0709030b0a0b09180303011418090f280204051b0406030204031203060503120a0c0b07020a05120903 72
    0x801c6c84032240d40d00c03100c200509110305462000707031240518122134014071b440d03c0c00d845502071000741c5080861000c0d442c0c1c25000c43c02039604136030009003690501e030020484000d0710341c009450700b070620040c8800041c240e81c0c9502c042039008200030300d07038905941009241203c4031300103040c40d04202484000748240c8074242030309020350700c0030b40d080d9203541c0d00e0b540d06845e1340503260800fa00741803103c820800c100c081e540040c0d116141c150f4417440940c4441c15508110160940f8030300041e00144018000d40c3e00007003e00003488002454104090003107080b61003140000e55500c1103036000328264411030041007203807042c0b03402d04002c2d102402001d9440c071788500e4044000248215103071070214113402c4032001c500b91707010b42d51516569110f40d1030101400951007440101c0303100b0302ca28540c1d0304990191007480c01f00c2d0400340180600b84c1d490150784210303500448405c0309120040800c440400c800340d4403a442400b250300102410034107404e05c1d074038102900030720f44200741c02085401043e44011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 972972976 1250 972971726 972971731
    0x506061c05070303050d11030408070c0515040e040510020a050307020111120c0c0a0210090302010e0a24050f160224091504080109050304031a0c090105031f03120315050306 76
    0x1403174501d444545c820429009005400f081c460404d42c0801444240b19041c0001c05500d4030070503050700d405075a1400d0264080c0d06070443e4410103c05d000400c0700794149100c0540c4a4407990689000900ea82902012a04402114000130700080200a4440e0702403060a41404d40d00c21803500f000c2c0600c00702c902c03182000385080b85080c000325200c09209810041081002d9000b851782c2007500180400410b450414801a40007540403d401c008605000700c1c001c003070310a18006015202a810b000c00d9804508000e00c01c1000300c00c011804200110601a103c03445200900c0c0c180c840b41c6004101c0a212003103c034240201d41e0300d10640c07001c0d032400c3c21121084002e483c5154180168005925540a150b000807019401c0200070340800c00088018016a84503040740550110744a509040041084900204c0c8400420002c2401d41c0200055036003c01e00080c00d0801003003480e03044014075090350085031070800d0301908030078581d054050000b00501201600100d2480c107000a542c81001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 972974226 1250 972972976 972972983
    0x80a0c0510060b0f2a1f0504080f090a0e0f04060605030c2d190905090a03050403060b0d120f0f1706150708030115031d03340506061c050703 62
    0xc018010030818900b00c4004041294a1141c1ca0454801c2603106d050521503002843c40002c51505c040c4214480d0381c0c01240c000c05210304048c81d00041c2d14640d401074500c1307a802142d003400003800d00310b400b1032984a001610400d00f40342c1411701e000003d50f030171608082e1180c2c0155201d52959210359020f0700701310f0760745800400d403081d0040800c0040000540c034107422800d042c46950480180e18030b08012954519010800c5a584044940c0c441081200c0140011810007041001c034050780c1090aa0b804005c12001e02d40d103d55440b08403501000c4001c4000c144042d1042480d40d4000d40c0303140302090a0709010031002044848001510f200a01c072610405c00102288015207852041da001164041c55460392540c552041c844038241d94061a80060b00305500010403110703030b130b8100c211210894000c60a0200344090300803101010341c0b28a070040d080341004200c480314040755001003405480600020704280c41804044501101c0c640c0c80d40b4500081280026000509001120342 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 972975476 1250 972974226 972974257
    0xf050c0a2304051e0a08030f040e0702190605070914061e07050106060c0c062a02180c040515071a090f0a0b0609090f0c100507080a0c0510060b 63
    0x1e2801c0c04491030300a07a00701c903811151041c203900d9400640c002c04020344000f02e0f85404607540d26040590b40303104114034019014800c1c4000c00c0701148005000c1d401440500513103400c1a015006442c40031a141002c0d80e80030340301d8050041680d040303d0074a0150110206100b00404000c010507480e1140042c51103842d001000c02198450000c0d09a800710740d0b1210003404031320381d101801080750401140130f03142c1511115000600c513019019103114030300324856070744486086920424240c00c4201c8140d0f006100341c0100c40c8103640d4024803078860f660003072070117454904040510042c420351001d0401c1070b800401c0008041110300141606100d014508200e955407007003503060903c640020b4400d61031180c400300d181041a407061040c81107200b45ca00481c40d43e2865509940c03107200710020526500f005d001c00316541003949030b010b03051109003010391824100c0d0b5200400c0c0c2e031003503800c180000c40501091040107410310190002800243c02446040e081c8a21640c182c40f500d00b20540c130b03c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 972976726 1250 972975476 972975527
    0x50105031c02031b010606120b0a03172107020d0504050310020304080c010e07050f09040b1518090705030708033105060d0e0706020a0803010506070c180f050c0a 71
    0x20b10070400c6501211083d414070400004000c0064042e01c1203000f4203000c00c60a46042648000c0b610030014000b600038800040945943c0315030b40721030921104044942810004d11120800782c54a01e030b4800d40303810358100286048400241000b010103100c4040100c1040204996900021302c5006510520300050340c0e0344491070110014400e8101d41102035003414100280c100c00410768000301c032401d030b4507807c9a03e2000204428400101c03002040e840766000416894441c45080f00076861002d40340303851586802c00c03401020340c0120381c08541c6910000c0240402e0806010510082c26030000031070900e080f4140348900d80c600001200000c180300700305055041034400e0b20030001c003800303004940e4070740c0b110000c0d45c007401151851001324811200c0018a0520010f00340c025550013130303912415a401c10040200c1a805108296065111250041901a5048002c4d1515414020000b9900030120888400c0d180000c00b4446a404140030490305039070400160508a400390315240f00d00d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 972977976 1250 972976726 972976783
    0x3080103120309020a030b160e130f110c060621060f0a020f1c200d1805070f1a131814070e04110f0703050307020114101805010503 58
    0x20b00e42d503c0003a40c0300c0e26484001052040008109000d055240d403c2d8440c941080e41c103a030440c4884070351036040311002c4d00c03021417400340381d000b104a02010300c004a20070000700540c01c13264000707800383c45040c0c016105210321860982d03d003503410211a41327040083c546040c81c1648589008100d240e11204040006040700b800d54110388218821440150b15010640b6041c614608040061007030356191414450b48040011442d10303440c1008041e0900c5d02608421450181ca400040e4003c1c80448002c80c0c000038209011040c060320308040b1004241d80381c80003c13500c50242020604440d2030400c24140d01c05980802482034503071204200b60707400c0b0000c1a0b2002890828186400112064240205039903c040c4c4403100c100b040320305000304000552007041501c00c040015500e880c0801446000038007172409154807a220380000034641d074101d402d040d0802801c80e00d1483c69070b441c00060280320040d4481e10503140040d2010881340d8180404a90f88001c0d103060101103070800304284809 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 972979226 1250 972977976 972977981
    0x901050f2d040b090c030705091b04030204021912151401111c0e0916032003040813060305040506061201200c0d081e070c020907110c01020a030801031203 68
    0x340351034a0002501e03440d20341460283c0d0081603441c041c3c0f9005803141c900c5c840c980010310b041511001495100c20741c03034801d8600d90102400c081c00f42260402c0c0b000102603541c0c0c0c4050203041d01000c01d95044444041c80041440c500c180340a80c0162400200f940029030000340003060358802e1034000c400783c0354400161803069440d44040e0213440b0326800140208d0766203180d01020f81c1c81e9261083c3c55070182e402c22028500455200403460f0b00381e0a8500d000b03201c0e4000c03d40d042549100328401c1e60044452001c9940226401c2c0e0318004001800c0c0d003d518000ca010004051a240801c084d04150752425100c81002e4103445c400d641c1980c02d1441c51a0039803040411034000302100c2c0c209102d0a00d00001034201903510b8406009917821006540d00401d542d505c01e10341812140c040305102d40c0110b001c0c03000581b5030010080c000402d58010303110104100d0084880f41c843e000c5084903890080d260080f002e01490440d088941400b0000b40c0142c40345040d01e42c48808245c0d0612030301400c400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 972980476 1250 972979226 972979291
    0xc1902060c06070c170f160201051312020108060f060a030c03021306110d030b030a150b18040606150e0405040f05060c0c1204050a05040f062c0901050f 67
    0xe80b4091a800d00c049182c04c060301002c410b1141010b680c500f51011101c001a00900342103000c1d1110400543c00a00c2c4d07088030b0480f0081c41410018203064801c00301188039492a0040ca054503800c0c0d03482429503030003a0811384e000000300e41c001003240300100800e040d4000c2c0749401080c50b0319406008180d034003c3d0180c81d000c0c8020204000c41ea695080010a03102030f8900404850045001034204c9034428003030759000799005002003a0785a20b540c1c1c3d2744407100150004810965480401182c2c6560303a074a5030366001d008070035a0f151420b06080c1001103c009030700c01e1120220a13100320a0345138101341021a2002c00f01c0d4000350541d92030400440324860702c04024480c3c040c203410030000720504005002c202031101c041f03c580000910b08488144141c1c01035130b6002c068040100300702d10b480d400c8100e226414010208081d42d5558401d03903c1d0342c2c1412440d040841c15490012020840c0307800c140c1c400d581e0b900030301090074280d140c03012500c40a004140d1070a40000725005010000d514582c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 972981726 1250 972980476 972980497
    0x4080f120f0d06051e0108090714061c0f0203090c0306010e070c050703020a0b03071d0918010e0604060f24050f030a17030a0e0303042d02280501050c190206 69
    0x6404e40303103541c0031008052405c0c14503011074101404141c0c0300c40b000034040160383d10007104201d4038000c003003008500d810032140c041083c5e0216080800c03600c098003c12010091400b000340e1039003010603916080c80203d112090090b8080001080300d0050185413981100c1750381081e0054240c541801c904180d06a0800f03900004003040020b06030703142e4070045200f0305507541c55070201c0103800c0d801c500c005e405810643d0310074010004900903c040d00303000340390000e2400c000502c1c454580d0103d818540c084805441003950342126100c1800f842c02600140b064804206e080480410310a006a050034000d044c040c0c0c0e200f03034504255840c2005811403c50b0422840382031000c03042500c403125801250140c0c1854107100b050140940c000083d2401598429070740c0764000d2480f030710ba040f440344e00010b961215820f03840d01005a1140b901c030702c03140f441070091929544200c11007200b15004503809241080300130005400136040105164400c80603000f1074846180403400001c07000c2c040ca05119 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 972982976 1250 972981726 972981739
    0x140906040308130e0c0408070e06010e04150303120e071208130905060f0409050c040c090f0b12090604051b06090901090b13230c12070504080f120f0d0605 68
    0x5800c00100c3e08060300807180c00300c09540c0180d840301c00790442030040e403113008841d901101007840701420354450554800303010326250b6540c020303c4000806403070785040210a09006103c0900c180b40c0e011120f410b00860a2201b8402a103e500c7c44540d0348501c1d00c10220070a0345a5071120402907060b0894070035641c40c44501c0e61031929143d0107401808242c0d08148100380c2180340c0b20b5a41045e004c0d0b440b0041e00304003d409011400c809000240004802c10740070230111650104000d2038000311175001d00011041a502ea24521200c1010400b0103402c10a007680f115040100107400091103402e1a400110f810140102000110b10680600c112495101411400108040c02c45a0100744210b400321541c08555400d5030400044138180042c401a036a0486000e040c0040321101341c1c1d801460b04e40b1401e00e4041011051801c0410544810000500008080040441c200b03c4c4002c801155400760034a41c100503030380c050300d1003000d680002d071480201d1440790220440d40407100510025011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 972984226 1250 972982976 972982987
    0x20313110a2d050f090402041a03191505091f0b0619031a011e02030f1b0706020c060d0e010f0c02060a140402090f090307050a050105040c0801020a140906040308 71
    0x7400002c510000a0207450b104807040000d8620b8001400c0c404034001912006440e1140c6c1c087c040641118400e080b111410940a4001601c0c10402c0582c0c0003402e2040003280b803400e25000c1c0411240181d81000c55040c84203007d641301011581c40308034040203c660b070318410003070318407401703009404120390348000045190079044985103801c4a001d04150340811522420401e10200f65192061090008180c1207820000e062010740ca8245c404160048078200003803c0c0204065502c41700303984038078510604c0c2c201040e800400207540604014000740401001600c080f6440c0d01817007200801c0740703840c2d145202c4003000c00e60001c01e004209500600500c100804082c1d0344000c141c40701e503a21880c021001d8075480f0007240143c0106e0340100159402c0e180d0741034240c4074907400341510486000420080000030010070a5400c0c06120710004190342c0360900340105441e645130300401c0182d0040050007405907200664004008418106648803020900810b80ba80107681000340702a40004a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 972985476 1250 972984226 972984269
    0x5030a1124160f020706230d020c0f060f06040b1807110c010507210302130e0403030b040c1e0905031204170102190c0206120705070b0901020313110a 66
    0x1e038a129a0784900c0001002440c048111070341c0e501c0c88003840068014080c148010351003200ca030180b101403d411145156508a0040c40070351140c00510720440d070000742d652500201340701c42d5203001c5804014220610300080045210940200140e10a550700c0319404501d42d1031504500d912040d211909601e464600c00c0030b000d443ea4610781c00c415100d40d1a045101e588118219080164404200682c0c100c8127a084442c0c050a02080c400b815001d0218400854840c0500c1d001081160000b0440b4181800c01508840c108980d050041c4e003400200e41515410a0354040d14180208195800601d440070444074100d9503041078be0b241c010606600341146091000e802941c51140c190318540111410703944c202d202e000504002500d989403071428241c040da00014020b40050081c4d03140c942400b55085201d03508440110119002003814403d102070b50b8005540a00098000c41c5141003c01da50500b1014005004102040c0d082e080da209444e05500d990080500807850501d601e000314 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 972986726 1250 972985476 972985543
    0x22170715050105030c0114070602041e090c030513020f0a0810020414030607020a0308150d06020a02061e0c1e0a080105131a090a090212010b1c05030a11 67
    0x105180c549034107100010074a450046407a60708994140c595402c80c200c80c441880280d005810251000c650038000006c13180c1784031764400c0511494118401c402801c007510303001120048d942200415107440100031b40c0d0303001d08520301c20003038045828400120070703500000c200c0d0340c150b085010f05018030100020b00b4441034020f44262040501090803903110042410355580085442c1c40050384a49104170100307005210082c1c020300c1c0400a05850301c10140842c40305241e0a000700c68080c0e000801907980799040c0700c056001400103401e203c0a01030080c810f0403ca01c05841a0920103002a440071021403002d2414404642c041c1919112100c80038007401020092207040e0042481d42c1158144d90f00b10321174152030024400a00040701c90ba002405208440103000d055026030f5980144e0240c2e480010322a001c084a1002040748851503060004c03082452101050001440c070b100c1c00058004015680802000c1c54800d43c403031424400c2c1460880c80940d5071480540d2507450362007004951 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 972987976 1250 972986726 972986753
    0x7090f0e150a0b010305150d020a080307030c06180c050f01020a0609050708060612060f041a04120e010c031b030c0b0106030203150a060f0c020301020c0708160b03221707 75
    0x159010403001003e0401901541e004941c0000000c07602000390940f0b1902c03a092180341400a00b40103403603034031100941c2c550742c0030800036404036103c6444001003040781e004891140c40800714102d400402961040340e001d48a0040e40e1003003800284002e1164800c1040c40711407900000248100319850400c980c03110114055506180180130000d8240c3c188280820081407200c0e000f09150782c0d520318000300b15840544100c981c00154259030b800c03118051002d038042d034041e007034482160a031b115000e04003005d05050103060006042074100426001003510203c05081c15030180380a82a15048a04d101d40c40401400010442c001290140e4141e000d0b5209225948030b0005181480b010004040e055200d10750029960711641940d207441940d5104091f407029001500b880e01d00d066070b80c01c101c0c0680040f1003a41c080c00508000c4440041640c0040181006081c80e50401c607080c4cc410441036540f10309400c030701c0d1281c0c400700130700082030190b0b05d541c1003125901ca81803860004e0845081 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 972989226 1250 972987976 972987991
    0x60307080a0e03160204110f030a09050c09090d080f070c0b1b040815010f03080405060a0e100f140a02062701060f0501080a0b01081303020c090108031201080f07090f0e15 75
    0xc00c440510011f00d81000c403440504040e00403402e50380c44008000c05808050012903240c001c04000540390346803550301d1806a10759102520141c120400010311f4100d00030000103261703a100041c4580545c2000440751081d41108510049907640d0070681119980c002d1086851000000c0000d0351020104014104030400d2038902503e981e94001d000690065000c040c018600400081006150403001080307541c41505080d0700c0950410005907031441e2041c21140031400d200f040301000e5500142a10a6004040703409040c405040002552107400810301d6910307540741d09003014005e094007113011500440900a0180c1c946400f503803c1600414801c4030701091210020400c03842c824021054420f2041c1d40310605681c40a6007012104840e41c0300340c082d805450313041d0b0455203954a07120b028065580003103686001104000d03070407000592201e90903410190749129004c40100300c440c11a5400350000c1281a400101c4400a0201084a450707a101e001e00181203a2500d09507544111030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 972990476 1250 972989226 972989231
    0x70303020604031d031509010f1419050c16020102030f0403060605040524010806190905160810030b06150c060403030e1203181212040c1202060307080a0e03160204 72
    0x1c3d0f104107040140c07614103075855080352502000303a01c01c120150b41e216080b1fa001043d83d01d0901d00000c02c0303d00d2000c01500d0b982c801d0b002c209180c605134001000111408400b00070914190f180e011042c0a0074207802c1541c0100007464040d60300c200261000d40c01c030b8034185541c0e40d07075a00e030110042005105085c0194103020018201d1184e80d84e501e103202c0c0c000380c08520b8181130900110b070404c00003801158003045565028540b01c07180c9010030064101c100d800511410404009412110300001a4040241003003c1000c0403001c43c45c20003c6a078008a2405141c0f914070008690425142d80c5000045000c540c516289000060880c0214040d440401003000c1403000d0701c1e2100d9072240c071015200010000304424204014240480c1c0c201c007026a50300d4a55645074140070b40c000340c0e04520b441045c80c00e2000f80510700c081c51009080040c00010440410360110300745000c000c100300f0500043c0c0380062151009a00003403103610403c030507039a80300c140c880022140c50340500203a004a1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 972991726 1250 972990476 972990497
    0x30d0b0108070908032b061e0902250201030207060903020d09050307140112060306060f1404020a0c0818031c08090606010e1309050105070509090601140d09030e0307030302060403 79
    0x14010b003501801d4408a1000c2d52411b0500190b100e490100072009044100c0500e80e4086c656007584140300290006050600794580c24000a00902080b0742244120501c104000140541c2d00c000c02101d121944495110070489400160700034003030000b003e8000c40c14200c11400b010390200308650300c48542d4485080f0380d610390341856a1480180512504c0c030707034103501000440d0302400d100c4100c144030050201301c0584030390b5034a040d9041c0380d114549201e4031041c10302000c5100701011002c60744c252030850410100400007070050400c0440030b0001d500000707407916038118068656010020240858983c03020040c409089a04201000b0001072440c801060320720710003003032140c0241b40c1652180b0028104400308421400c4550010041a59079400d03031000441c2030251601c250380d26110b05481e91004014403084010051400b03040041054004503c0c0a801040e40c000d030501e8803001858000034034040d60051000307001c4590510510000200305940014183e2003184240d5a801020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 972992976 1250 972991726 972991741
    0xb040803040218151c0c030c2d030b07032030041407030b070507120c030c1e060212071b030f0c08270a1d0a0207060e030d0b0108 57
    0x450240c0d080c000e15001c0320340181d0140381c1094030843c5e000001c11000013100c0b0300d90341d4105030240ca90003206c2d02c000c801020010110716207650041b9840d0541030f82d14090312619043e042c05042c0c040102071011080100701514441e82c080c0501035006040f500c00c4221054500d4100d411090258881a0320184000b201c0d03440c003000f5070342c0101d402c1001c00c0705889a0303980c04052060780146e41c000348500301c8000080340242c000c050040c040c60b102c141d42c0e1140c9040954a028102c08001f09110b014905000040d90015050408503045007600001c0040d03040b42c51400da6400001810443c0003240c000454589250041c4c0a00f916480d241c403150140e003583e080c7c1c940b8298024000c2075a101d501002c141c001d14108044a110b2040a850244280e4450b0104041c1c0050900d41184440e01e6000d04d05040454001601c50400340c2282c001032241020780e6800d000708030001300d41d004680001004503d4125284281840d42500c2d1514044184040205802a07034180050440300204516 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 972994226 1250 972992976 972993019
    0x62301050d050c09041109070801032f0906030f0d031a0409120509041506080402011206080a08070510110d0c08040b040b1005060a0f091707061b0b0408030402 70
    0x42d5100001e0000008004104910310000520030b44206005060040c0184d40d585045889824140c550106c55410b50501030b048000030240c5903040c0440040045011201c143c5060030360400f1203400400d03a581c80040380c1405156644a065131103065468125070b9090b80084503c00300384a02c0d001c8640388041000142d480c0000044c0030750303030403001800205118800900c442d42002c0c1000c43c0f4030159000c09200b00016522080000c0c080206010456038040784000c1c2044181c04140109801c0440494503200d241000400ca00c100180c14010000188000701c44a070701d5020400100501c0c8100b00d00ea9030020500d41040e52420342050a40c1c0d0103000100c0c0070301c0c0c10400c1840270359510b56598900d1035019200c1d1400507001e11b00015540e071410020505480c045c6d0b01d85a00488054002c0e114041e203070004040d0701d504611502181c1000140d0b0800c0b11164070389060310a0482c416203180204504001e1700035000e4608020904c103101000f10f0080b8400c0d207272030012200b5104003426 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 972995476 1250 972994226 972994249
    0x61c050318040e07240903020a0b03060f010206070f0e0a0b04090501060f021605040f0b0d051e0106120204050c0d110901090e070801090c050c060f010801111617040306230105 77
    0xc5c41c400c030300000c444201103500320f1080a80d40d803c11038000ea480f500011103000d06036009800030358000003000b4075410034520038400b000e42800200f40714241400050400d40005081008004050400b10305581d101d60800c0000c154100c00e8507030300da40300e5828401508017402080301140c000003a41e00414800240160450150800d4084003824881040058650030380d2035540203071201080461a40e4401020000c940705000404040581d005810000c0482d2018514030b64541001005031800b00044904866412140040c441d42c882d120a2079600900c242c00a0403071510030340343d09048051000301040c44007602d808014940d01c182c281c3c0507aa08540705c0303000070300820041009030801d0f000003403140c5860800300d05280c2506405843c0040c02c540d1f039603980046800420655400780f2031030031000181800a803a00200c00f90300c107210150404000c10505440001846030580441541c014640c840001e000c0107002080c501d070100d001420f2089545039100c000a22841d00694045 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 972996726 1250 972995476 972995489
    0x6021207080d02031305030d0b010e0a0f170703050a030c0b0114061b0f0a110405100501080403180509090d120509190f02040608030301170a0308061c050318040e07 72
    0xd02e807050504425000c0e40019014000760100f6651220001d441403024144061030900300042500861000600340e0718038040041c041c54204c2e80520184480781103002c10741d0001816101d1403020101c00790f151068a0380003030a14020b984d406020594820074026216006000915041c0d0700c1d4010302c0d001c1031300596a958000410403007510311003080340800310744603041707803e48003000005c001417400c1c000c001d48111010070b4295600200c502e0320340b141c00e0700090181040e6031300710300345030029050ba080680090203103c00a0380b030000f40031600d0070a07009420064095112420031107c502c3d81e07003000442200201c1c6100b04d0446040d0307a644a030511880703000380201403510300c400540c805000001da0640d00b6203614804900940c84a0003100001d28802d80156941c1d85424034010f21300340c01402140c1c0a4110802141c0400c0c6d20600e1960000c00448802003003008041ca040c420a4213041d0051003408040340305d0060b0030007038220558120701582c0601c0240d40e121406a180c02d01e41c00b030300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 972997976 1250 972996726 972996743
    0xc0807060f081623040609051c030f112d0d020c010e04091103060108030c071e031202011b050d0c1403071809090f1106120708060316030b0106021207 66
    0x141d000601c07607806281c204041c0240c08110045840d01013402d40d0140d040a000321320b0401040006040002d04580940c400c1541d40d98070301490380d40186601d080c1c5401c0d03000c0040c011281ca036180018051101400112404040700c0003405208058442e00951550b81034010000d1854400e400411540c1d070441c0140e407a449a4014001040028000082d098614184005031003075103803410080c00e030207402e02d24000c585800c406840070389041d803180c0001607161001c04107210300000842c82c1c0c0d0700740ca500411184000352580000c81c0108000351101c2569042418444089a00030005041c00e50f201703c030503c841410358105465400705d032074100d152444108000b030b650307611a01c8000410300366402d040c400680c2d101e12000070740d03059010940d4844c2c01c802d00082040f44425075101c0c4510107803025814042510007808194078000d0805c0213100101c00016110358080c020104c140c0c85000600c14401d0300e86c1440c0c0c001000074010000544280c03191100c004c1d5040d0182d61000740c1c030003c0c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 972999226 1250 972997976 972998011
    0x6140a0b2115030f030304020a0b0f0702010507020f09130b090d0206180a12050a1206050f010f21060302030f120a030b0102070b0d0c02100e1b0d0c0807060f08 70
    0x201d290580000d00e42c0301d1902d01c00e00401c05543d07090168540707007101c0c035000710380b00e0505004000ca80e4030181d100030042c5400300820040742010005450030260242440d0f41c46441500201d440c00ea070341c030786c03640c1d21289080800008006e0070503074440003802030f1070300c0402d950b403580c020341d41e4035800030780f03002583c407070710001e001e00d0014440362280c0c80c0e9607400e50312071003142d58500302130305825100080841e0012505a001503440070310f0389204080303d80240100361501c404905040e2035032403c03d04004d0081c0820035054001c008090940b8078198100440d8245202c403100201254001244240038070b80440205840002c2c80c00111400f1840300743c5014000b0b07400350000c200880c2e1180c1540502c0c00004ac0d680e4800018001c501003203000800d158079040002070504031520615800c151400b0801e544d05400060500b1030140100c2d0f042c0c4d00428403000062b03002d040014000c3c4006081003000c900020b01145170021101301d07403100d1600c5031403060709459207141141e902074a004035008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 973000476 1250 972999226 972999277
    0x92806050619032001090e010603381e150c190b09060f0c030c1303020a03050f0d030612030f26090d0c050309040b0a080106140a0b 58
    0x30540e0020002001d0205074481108080074219040c1d00a8821428a4005500720000100c40d501a4002482d200d41800c0c20500b40d190b03140418001d106c1015a0780410392051412065060611142c2c18400180d070781c00621088070f2030070203000d400c2c06421900303020f481e01f102144590061040040c83e6019000740310360384000e00c0d084503030011030911582185403140b110400081c900359004410500c918034100d48103520f0504081d140d8031200040004214403c20014140c07604042c642d590325035980340d0031000d50b101040030b401c0a90b0104040c8c0c40001004070008a010314803035913009035003140c2c00341142a0b00710760851090f00004a040c0c0d4502e40064401d01c1c0700d01c030446203030900c200c0450882401a610501400018040300c0e5548140480d01c0002c0101142d48c00311440d05014080c00e6036250781d01d80c02039040041c0681c0e241d000200d49a621103011401500820f0000c2000e103603651001c84bc403101815003a40070710b601e020041500c010070000ca5400c140412000503001c1030461 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 973001726 1250 973000476 973000481
    0xc0106080319030c090f060804061d120d0b060d020409060501020a030c030f050f19021e0715170c0d1109091513060f03020f01080108060408070201050d0c0305092806 73
    0x2204d8000300400c0c54000701d6401758401d0080003412503503075401c0b284d142500d4050704030380381c2e2042c014081c15000b0001c11548030000c3c801c2c80407142d0080050300c1e40c1d145440c0d00e011f00a650000341d40f051000c2915012011258007500c12221540000e004003944d40006a072079903203041c40500000c2d1500c0c0344801090080b560300004030aa0714269142007005034030703144070740c00c00c4a5045485c0c0c103011086601541c10000b4a00c498036801e66a00159881d80301e16594000c28800c451b030814a0340c0221151a01611802480314144410040c481c5815175605c0c03c80e52200203060002450088003a401c9a03500b004e44588000140c00c0021a48442201c4500c510040c90303c0c0c2d501500d45c0e00181807151042c001c030801800c2d40c0d42d4101820f4150310402c61141d1240340044d0410910800410002200192054002d9000030889071b8844160004030f403036114010208401a00307061071816803607450f5000500c210040c4e026240e00140c8420b184006204050055914111841060740842c509a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 973002976 1250 973001726 973001741
    0x30302031207080c04030623040312060801020a1709011d0d03050c04032307030c0906290304030c1433041203110d05040303020a091a03010605070303020d110c010608031903 76
    0x960103c0040b440603480d010231014111005c40003d104041c00349451ba0703260081a0203003025000030350520480800c01400ca4081e221203012401c84480800c940c0c00d0290f0003140300c65003002e050854076081000040d903030540112042c0c0060b1402c0c0c005080b0010300d5080e50256903001000c28501540215100b50b0028010306042c0940541c20002002460315003c0030000c05001001090180c500010900d2400d01d403452a030340c0c940403031000044401c0c1142100c1c0d200c1d031b042c00c0c0041c0401103400c0400030782000410340c035424401c44031680b400c0101160145050610a06502c812100158424003140c80075100180380c012110303001c1d50180c0c004d4112904051010500e20304120101100000707584041d2016804030340d00007a901540d65028907800e02900302d0750800410791640355003d40702403005110b84c200300075012500c102014440d80403035645000b1720a09001c2c001030f011004d1083d41c00b820754030889600c0d004001480810110036035400741007081d0f580300041c1200500340e002e041103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 973004226 1250 973002976 973003001
    0x120507150c20090403120b090c0a3b0f01180608060d081b0f0f0c010e010302070807050615040902031906020c06190c1b0f150204030302031207080c040306 68
    0x1c0d904001030b0700e9900c0014800c80c06031b0b03607100c642c0f12245200300454664003da2401440c190080004031059182255804034141c5840396020b1a500d400c0c09900c1c07400e203000c100355030030844501a0003d20042c1420300d070008840c41c1c0302070400b050065410710b06080c140b0010b4000395500300318803030143d8a020352081016118ae44410b10316038903142c1130740c0500016010702180f10100c1c040c40700d040106051a00055004001c0c10811322441a51080c0b200c1402e41000700d0090502607907440384d01503c1c466a8441c003c4c5841d480c42c0d140c0305480e80c100322400600140d2030103a00c1d19a2405000f4410101d8015001e001131070904454404d580c64000b0f01a601c0c20f07000c110141c00e86404002840c402c0c0a0008803203002806290340c00c0907038041d40103d0007007003c10b0010102991440c2540c107030071503004000407109a9185000c88442d0703c00c0003000e80892020034008241074002c8000c142141080240320020fa41740001a80c000009941039000341e00d0078002400090352551050307124211 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 973005476 1250 973004226 973004273
    0x303020405040e03270603010e0a060348050609121e07152f0d05040929060c030c0a12021b011b03110106120507150c 52
    0xc8900101e02078425200410101d540000358408000c0717a48501d5810300f5507200c030341e0b0300032003500400903516000c103003d132610002908001c9051101ca5a02072001190f0011040d041c0020794900d8040300c0381d010021140c04d803100c96802407219160103581c0c110201d13080c0c0300f85070300303043c0700501c50146c00405049030004d40c004d8144514a41c2006911852154505503800114060019074100b4607164030451610030080300710300310070307400014942000d096040c0780c0310164505402c0001e0340311540c00c0312032280210551200102d6000008009a8184c2c00301031210340c40414020840f603641c60031401607104810070450030391400c14010302d0315404400c00c070380c10118103040f498244034810300b040f100030060101c09031039203806009030a21908042041d010740a40000040e2416085601c50012102d150b070f034541c00c05014410038540c1d101d21314001c01000781c03500e81d0f507200c006003a0001e8400e4455940e00044000035407400c80132240a0b5076030460344c8402c0c2da03a0030a1410300c074600070401d0b01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 973006726 1250 973005476 973005479
    0x8130c091b181809080c010915020702060d09110a0303020105150d0206030705030705070b090a060f05090c010503131a0a0b060f07031b0210031406030705180717040c2c0f0403030204 80
    0x44009024015406c124400066000c01c0c40c030b880341400b02000d4904208500620510300565100d0007510b0095402040201c0c5050f82480c000c0c284c0c443d2612241d601c07001c8020080245541580150300c030304941c0c0c4c1040700f20700304c1000b00400f645071000002e50201c0c081000031541e1340300f4406990400b0540c10518200120f270ba468a50603081120030400e5984500e1261040c008580034265041c407100c642002581000341e960380c0c90303407600707000a41032180000202c0c078690b4985d0300c4d14601c86c0e0007254450401410010104a040c000c1e0f8000c002e190400102912510741201150540a1040c84051400300680d0741a16603001c080300c80901c0c8801d4900042c0981c0b02c1d00080d45403c0d410380d80016030300545c0c0c000e0404500010b040715020740d02c1900c080c844d0f40c035801486d00d400c8846d41807921240d039441030200d58010300c82206180140400d41131104000305806034a007540d008034141c0c000305068181c01d42c07006441804061301024000041184000c40c040441d420a0203440d0241c9003d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 973007976 1250 973006726 973006733
    0x40e0115021e1b04021204060b011b050f0f070b18030a08030f040b1015120e0d05190e0f0d030309050105010b0c0c0402030f0708130c091b181809 64
    0x1003600b40c0c180040f80c11040794a42c40003c07000700c100c43c900d0102c404500302826600a100d0a95004000600c80e955462044416030302492071b07079119080c00d03510000000c43d949800ca4440c1445290540b841c400d805558074000b40205150081e242c4104946003090410000c100d864000004041d425000d0304160340f01164012000310b22402e8002c046c45224202842c15220705100102015060510700805002519113954104070501c6c2d58604181d0914210141d0070007810546106c0304a4840c02c42400250354001000e040301c03510015406a45400c85101901d12541141595070b200c038000780403580703034500744150170706081c02440c000400c11156640d00e82160740a030001d102e8018080b4103046141410006040d0090080d101541141081c1c1c002c0108440d000c0d0002042c0f1421000044400100d4030800480380d401c80c036403640260352221060300412018940d11400e00d40d0203031030758116009075180c00c05040b0f0250622841d030725010b41d0b00282015840425880c071b17100c68018001c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 973009226 1250 973007976 973008013
    0x1b1b1804030909090819030b0306150114030a06081203010e040b07110d0806031e10091401020d0c0e041a01031a041b081e0c0f120f0604050606040e011502 68
    0x41c1407042c181e5a5a40c0695211b082c00c488002c503004080608000100203162800718600b41c000480f050040d43c1c0310707078050040ea600d900343c07200d8200190000c0200006105160405400c4401c0b840c00e84a15111040d0030303031200c4c4002d014030b11441c41040080b80000390303402c1d4a1903222200b490700b0341003c04000006420110b140415100103010581481018a0184108116510540f620540740000341c0c0d40c20303884901203008805100d5407040e503002401172810640701103a02c00b000840d524000c002c180402881400c51900002d0700c1c200520a290900c0e1088080c11000380c054801406050801180a00040240d490082206a00c034070055129070107840c1c1040002030440b121030001e510003d2240c00018009468a0503026408100c1a085400507422107000b80b0030300e80d80c0162100c0031845114076040d06100c00e452234108400b210b840d22040d40903403022941440360b91a01e808010305401140510702040071300380f00421210000041d400d400764140c0c01500c2250b201c48110910 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 973010476 1250 973009226 973009241
    0x250c021306060206070c1e140708100510050102061f0519050301140f01150302070c0b0720031f090f0f060b0303041a1305061b1b1804030909 62
    0xd69803551000d01c0000d8041c4507240d03000d89645460500c83c6016103403402c1c200070071100841c20b0301650034040d041c4a140114400820710340803c03208a291b407403078138940d100003200d80c3c00155841c11001c1500518408000307000c0b120140e0040000751900340e48454060310034551510480e01107540080c3e035440d488101c45e18520440c2080c24003070710705400d042c255260034201c110b08141d54002c002c6062500000e076810750746902142200e00075114001c0d0300034450050040c0c0308121888001502000020003800d11034403079002e1002612030303a1075201c00f110030280511380c15040705d0004c20b0b420064a40d00c1800e014000b10106680200c1c0d102d1300521070004a055a07507110481910081c442c050240c038500240540040d403806240042071842420541001350901c000050f0104d200d142100091018180042070650b440748082a40201e40580240d102824000da40e00f00050312443c0c180c050201c18050409080c1451886907259100b900800c114184513803107201242e10240c0d0f01c02e504 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 973011726 1250 973010476 973010509
    0x8070c14030a1704020a18060306110c0c03010905070b07050304120302060f070915031e050114010e041a150d050a060f050f0a150302070f0510050f250c02 68
    0x155030b455681e900400d0706600700f000d0310544030500c05100050b242d01c500c2d5002c80d80c0f8081d000050400006c041805061950301c041d00c0d1905104910754040340302c50041012003000412507030305541d20000d00d4242c5201e460007401c1d43c0c2206000308940f1368490002d1038174603c50f0007524905502c607510910f00d43c0c010401600161b009104201c44800303001800d1341c00080700d042104400e880d0038800c22503006000440c1080540366000031310041500c140714481010140e100748003560b12590010104424449903c0c0002c0e014500c540aa081902c1010711070318440703440304507520030f000038424200c0e000c0719400d48560b001c002c98907040311588959070041095035008500a0b140c40840c00c2c1300030303440d003141d80700b2240030180318040c3e0356003200c1d00119250700c0100c02d03142010074000c0d4000d0003403250140a128044809200300000880c001001000194040121391280303150341d450041c04503140c0381c8001d440a0b1400380c15000d8184440c0318403c51802c4c0c80207800340d0b4046041e41e40300b00c8640 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 973012976 1250 973011726 973011733
    0xa0e04050a090327121a15130b0604091104050d080d0b010302161b080a061d0c060d3c0f050709050d05100213060e0f090708070c14 58
    0x100308050748030b04181c180c40c3e981c05249050104010189041d060a8400c2c030200c0040d0b0a1090b042021210703446c0004800d1502d0750040d40707032a41c80050000c00c2c55034010303c1581c8180c0d40c14280b03850b61180612103000500784a040504020a01000340110709504084007014080051aa078540103080889131155011680350711010500344180c420a400360350501d8018071410070030a0350380d05000c9606800c240c4c0c149203442452241841d502d41500484640d000d9141e200f018820550040032202c40d0445064501e0f06040310126110103c3c000c00c0c0d90f015004004003507110b0510b1300f040f01c0490312102e01c601440216021101e40d01940b16500d4441070f540302078925000700381d01c68403004600b414001d1001c0e141c03194004042d4025401500d20660310b8440c00014042c01b000102803040c5605021555404021081a4100d05034841c01c4001142110025500d007014072508104081c0640002d00c1512080300079541c1b200024203640801c100030604a02040360b024a00c5890644c90026 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 973014226 1250 973012976 973012991
    0x11103130b04080c0a060806010c02190602030c0f150c28120c14040504020f090301090308041202030a05040e070c06060b0a090609030f08090310050108011a10140a0e04050a 76
    0x1c0c20701c0380a081041c1700d01c200f0700040014030340048056a1200c824a040c5041010310310002d034240f804500c054405242e001004640150000024000341250008640e04414a0402d0303030b0f544c803086c0701c0709402421000040b030094000c0c40c0103485002d0103440083c15070059400c203010303668800450240001c80240000078900032900c81c58111411358a0700303101c3d031b80c5401080c403101d1003144112401580d0002d40704801d590500113440500743c000b80240041c00090030018654841550180d8454036402510b2864900003c210b0360000b0050302e54609080c50801c0c04420100028121001e0100114280d000211981700b0840500b41240722191a0344640320020501ca110760845e6090003030104d0705101241d0071282511800b80c1c0594502e03558011600428100b900e4481c0903d40c2d541800d0020a065606410803032614040e85421240011100108a42c0c1c0804500b00301c0880c0400102c01d100c08004001091804c2841c24035129003103984010400301c0b6000c4460461441c1da4854 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 973015476 1250 973014226 973014239
    0x6040b04120f090b0c03071514090d0e0105162307050409080f070f0b1005091b03040303050603120a051308010c210617010e2802011103130b04 63
    0x805840410a14001084640c0300b18040c112905038003aa8052040200e1340c001e101c1ca0400840b02001c0d4010703c4503411769010300201d0040c0140c20860500640501d00080d40000c0010f50710400754010342e80c0d00d9a880300080151080d500c01c040016482c2d4020103550003241450541240c01460880040c034160603004c0c510b0300b02400c2d50001433080d401c00b140c1d1400306050400341c030343c9074150840b407543d140c0e800d1400d156000744480b0020804441d02c0200000d040b04810b4175022900309951807803450ba0b403901960610b000321134802041040c240041800310b882680019441940641103404945038003444180c40c0d0001c0329050300013880000c0841640b2090814040100500c078024412640b0744070025110f410a040002d01d0580401421135950503650005801411100c5040051440d81c66140e400b91072052407089192017960076480002d55040c100c907a074801594807854050000e9401102c0e5020031004070383c214801800a00b40c042030043c2001e00818230401859070750b900c1c06c00c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 973016726 1250 973015476 973015493
    0x5060402100908030706020f040f08100f140112050c130b01030b0604030f031d0604060905030c120706120b1c17070b0a0f0e0d0302040906080102030615031806040b04 73
    0x40d641e104018924200704841140042038a601c00d81c1306501503160b00302c406045000b8042ca902490129003001c000050b803020200c0c2e1841c4010b56843c060201c0d001c0000003905407016003490314620400c00004100d40000e0078a136600c1d1500c100190707814070142c1000540c9040083e0441c172000c90f520f8000084030741e054410316403145c00945605040c40c1c5161960b40100005040280c00e00107603040810080318050540105060010301c402c1c1c890751070340c00080c003500e83c5000311802807160119611062800610903900c42031000003c0a031341d8104482140c18444a0141240140c0c8507002c07003505684500d8250b00d00c001c0c8182c0c0f4502d118042c200b610004042100000284008014000106124031034a0364010310f81803000c43c1c0c18142c0d40e000c800130240c4901521540c0140c030001c01c07625515800034400c444900500340011922514014201e2000780e40c2c42c2e51213501e410106410a80c80c1018541c054400301d5581001c0c0c00c0210940d00f08102100c0480d141c117800800c0004010019 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 973017976 1250 973016726 973016749
    0x150a03092a0f080c01230403080315040e070302010e030717010b0103180f0b04030903060f1b050f0d05070504080610051003050919140102130503010b04050603030a1101021605060402 80
    0x1280b02d5003034a07100f003080d00c6004030610241000340307000e50100c41c10140c4a042114008222105a540d5076a0804603442e0300151403008400a030781c82c0140042c90540203d022640064001c1d110407031031a0300640d11200c05015141e01402403c10001e22100e0040e041908242840300202c0c1d500703102000101294003a6403002401c038044402d2f54081000524240d8800d0303440300a4408a031241d04064480b081143d03c02050103040c9040e103406000c80340c1014540005028881c0c00100020006481a005414000b0808002400781b940341040d02d41000e43c005126040403072401d500e415171141001d0f411203004005c42c0c04040c081041c0c0c10105160b4200c0704242c07408000c2c904101e4041619010b0078069003c4103951003100f1410b000644809940400502000315668001d001c0051104001e034442c07144607518000c1c1e40c40890038103000706849550028041c51419042c403d09840d410950310355031004e5942408400c1000014080194080b40a2802841149001c1c4104460340216 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 973019226 1250 973017976 973017989
    0x15060309080714011d0c0f03030c0d1b05010e1f051306050a0f022706070b010e0903070f0303020403021c080901030207060902190e0a0b150a03092a 65
    0x30411648007050041007aa6001d99210144118240303108150a0160440d403a010003200d0610172000c02403440081d40c555101c07021b403038445145000350200345d1603000700d119507029508000143d1002602ca01c80305900b0140c440d1001d00d401c407041e240c1c903007141c003c000f050301694460907000481d040d081c9450003c808100c08103202519000500b01c0c0c61802c01d40c00107051b81d0300d440104159041070b8009400c0f168003501c00315100c0c2007202451115200000030181c1011a6042d140d00300d041071011198065002040d100059283c2a405840e0800c0100f0070f0081d03001c28404200014821034a094450b4000d99015854a0540c0100030700401401c01d4035503154416501840007590403c142c0d03071011800d081c016120f41890400f90094116400001d43c808049002c130100b1b007a00800c0340c0c1c142e42800c4a800c90503600c0f40c0c0100704907820311032001d070301c00d00e003030708900348100008010030540201e40780c04600211035549121192851000d117100e07155400b601169068801c00540c0010140f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 973020476 1250 973019226 973019231
    0x61205030c0f0a1106030606090d060501051e100c02010c060608010606110307030e01230304061d0307051c11010203070903151e0911030709140105010309020f040e1f150603 76
    0xf540d030340c83c40c151500042a4064440400001c0da165928001e0f2030800301e0141000303168480320701c1c20b40014002401402d110385010441c1240c010f02d440725043c419034000c0c0055401c107000060030760b0340f008002000c0781000120100800050200d00030b00c4010314400f000482d6460800d80040d05080030005000c441d94014402c070004a03901100c0307041250028240305180e4200c260444407016034519a01a00c8800002031004100c0c80d07a011404101c002c95001d81010038221070181caa11070720001801d5030340400c12803181c4000310303d400801e0303e42c50304044000328030001e000c82c26608116011030114017481800c1003404252099009020b18100c1c0c1004032403216090040140305030303621032100703c0e1b40705040b008004034504402e0807410010101c0710095580e032441800341261180d00e8100c68121000000c4c10f50082c0544070720503900600c0301601d20b150b0000e000040410a002240902c192000c219491b8040701020b100564001400309440a04068404044c1c200b03074403500800d0b1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 973021582 1106 973020476 973020493
    0x111010603210e060f1c05011d0f01080d123308070e0f040302070302120c0a1403210c011121040b0c0d061205030c0f 52
    0x1804210240500410b4400407222a050b48802c03a4020b41d0500c5032966443c4003c02501010211004040002c4101d0a0311800d44900781d100942e403500700d0035416000707040070034040d9108120b076416803580c0d49071200c5c00f40d0b12400c5910403003c0012081001c41250b1440d00116031105a56851050b04a00810140300300600d404061100c16001400000d078140e0100e854400c6a000c200250301c16916003404c4600d00388010700860460040003404070040e0303200c2d44001254403030000140090f140c2e00051069000c2d058021401d03212006550400342e52300000c0032040b0850081e011000e41c0c8515607268041d005503a402c5102d9400c0098264603420b820001e000f140c04050400e2844100d8190744a404101c180c6010303021401c684009003206101c0001441d031b0610b010400038500d40c1e1004124000384002c00300301c2e80b80e000050000c0142008002c030128502d03c5a000e8401507 = true := by decide +kernel

theorem cover : BRFrame.Cov 972841726 973021582 := by
  have h0 := BRFrame.cov_init 972841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 972841726 ≤ n) (h2 : n < 973021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
