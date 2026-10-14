-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1134
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:23:16.033402+00:00
-- url     : https://prove2.me/submissions/89831e84-fa77-4a84-8ae0-2d2cb4910502

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 203776978 ≤ n < 203956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 203778228 1250 203776978 203777003
    0x50a031509080c150105091003050a11010201140f04061d0a030c06020904020d0605030c01020705060d0b0301060308031603050c040b04030303110f03040b0906010e040812040510020f0a09050a080307 87
    0x40c12007080c000c00c0030ba02e1050041c4844c6028240205501d541611801c960100c66600c0b058104803000300c4038440140f40d83c011508010100d115404030b2000c074070040c00089120411040701d00c40800c42180c1c480b0203202c0d0030f01800140000ca21400c20007102842c10500c1c50b0301100c080d80d5990411410080800420041c020704102068040d0748203504064070175034941d650080000040c1003036019040c000d00c0b44c00354020440d0700c00160a021200080c2100b458944090310000181641c03201070741d09592204000000140a00007c41c420803401407071140c0f11300031001c01001c1d924060499859103000f40420321020000401b25000c803585130500041e02203a40101c8039460048001c903135608d0101008201c244441104094800c81481050340d0303140ea291520020300031300946010b400283d0a0021900f240f14401910360802e000d5000c03148401c000d03503240380590b80301040f040001d14000c1400459030307401000e000003408080714100c00b8207040400e41542d031701a0a101070724250b081c92 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 203779478 1250 203778228 203778233
    0xa06051e1f030c0f06180302090f09160b090306100501080c0705070f03050f10060b040e15031209010912260708180a0902071203050a02160506060109050a031509 71
    0x4803400040d0743c001012098580e40e1980003203204480d108800100e1101d0401d0fa06200c40c83e00d210f816294018080300054481304850840d541004000e049140f062460842441031016507100003410001c20310381d5651081028542444000b40450300742494400043c070a0383e820185642c0c0c0305544102e00d1ba2918080c2c109240b03420b0040d4000030280410000c040103210000c151711f000300300a503007154842c15030300d6001c808442c070521401180c0c41e411320040c44020401d200080d00420340d4045005001012000282807107150311200000c0a03001030300400030b58200944100902c0d40b001401c031001e4854072004080d200303041d59140702c070311808606400280c1000030b59802d59080038080380c458000c44000e14001051300d071440e01c1010216000640d1241900071260010b42c403526492118480800950180c940a131042b840c8580030310051005d03004000204a1440c00b50008000d10b0038600005004008a03070001030080740d00c1d81091010403010720346540b0f000c00802d80041c1d188110b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 203780728 1250 203779478 203779531
    0xe07061107030c0b03070f05041a090a050301140a050106050a0e24040308030106021219030b060405130204030614101e051002030d0c020334060204080a06051e 70
    0x2c0e0030003400749180c414013081c404441006181300b900591524480c1889411007560b441c00b8600c5058010800007004460860891000e4019807901400303581c800d5469030b001030b0950b035001c0d10102241405800300002840c5e54010301c1c0c01003065061041c9890300c4820b0040840e0b0085001c1c44c0900e020b0a90240d001d103a10710281c00c512003480800b80c070b554403881c4c486c105500038030a2000612480038071501c60f01d03004080f10f00c0c00704070300445424410b00b800d003a405007030381010503607010340d0134000020346441d0480d40000001c642800180e503507081d4500101202c0d561099a981040d407402000688400c50080c0c400ba681c0f03c42008890000401c60f50004043d00d4000310303006070119085101c000d80001c0580101c0024440c20b00030f03a0440d040c100d9036030041441682c0e90803030500c1e041d82c54080800301003500350b1242c2c94042da01d20168540070140c0c2d120b540640741c158000e022500600000d4810150464211110402040c820314084080359002500f80550241d070400b900d00b009005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 203781978 1250 203780728 203780743
    0xf0f07060203010303050c10050c03130c05090108031e0412021c06021201031a0c0a0e0109031703010303021504020303040b0307030b0a24050309030307030902031f09020f040e070611 80
    0x20406640e41d60b105d160003403040d001085216410b00c540c00c54100b0900060203500c1c81072100d03140103800c540d00c1c1145004403c560680c169000c8600c0c0202042130340718033303400c0d41c0a0102d00c0000c590b0b540380003075420260411502034100d0301c3e805010501210881c5c011940301190100c40f001d450416541c00d85044150700c400040040e807000032010541030000c003205040b603018000f07480d00e50b40074402e0300340745520440c0d42600b015810800904100d015281c800300c602d44c1031410348101501c81d5107001d010b60304044201e02d1800c0200040040650400079400921100c0380e011840c0c2c01c4c184c1c0425900d005a0191043d10303c4003100040e1961b103c4c0c0d205a8905400402d02240c096550b8000f0141008000400b421090110b41c000c00045c01803085070f008034000c800540c51a950102d04800404c4590000c980c180101070755424943c08481c1008001401d1120004041801d44100b1030880300c0080e80b41c0c056070400300141480000801c92004490729400d0404050301c401e240207091660 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 203783228 1250 203781978 203781983
    0x702031501030b0a0f02071a09190b090607110d05030406020d02031005100e010507061d06040501290108240303181318080d1d160501090501050f0f07 66
    0x102840000b0900c903841d2010381c059039590f5003c0000380b81c592084400d0380304041d005480c01c400f203080742c62840400207040383c0c0035242d001568000c4d9804003075040c240e1494130b01035a00d024001c0a1100c01401400700e19040300709800c0002081116001c529201c0d4040d034011414004003000060502c68607404951801c018400300715583c0c58000202d078500441da00941e070140017030350708a10291340204d00c500c1800b60161242c0303003428465900c8a028109000800105132039020945c2c580c3c100800c11a401070703200c0e0b00003180e48030f180c4d1544e02640303801d820f0302003800602981508a0b42d800c07140d05a04142404180c3e02210b0f250b042c8109045424110a601480300103059215407035090985225400d0454654042c40092468070058800380c0759442100c03032066031307980001641003001749101c010a1101242104c5003a00021a000d408120300c0c481c5c0d0404440c2040300c10960908801a200900300198000e040c8000281140503411040ba003510380020740c0c0f000e01c0b0038581940d089a5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 203784478 1250 203783228 203783263
    0x406090c051f03111c02030c0f210606040506070b15100309020108100e131e06091103011b0c030c0602070302030a180608040807030509041419110a0302070203 70
    0x40b06450100b01c00c07030b02400100019140021007515880c0c0c840c100c81030f441070300840c82d4100413982d80082c002d600251030010710441c1040300e9500c2d0302d021409452001c07804500c2a080030110b0030702c9180004024440e500c110030410060001307a65403010788102c07c1e0408811610342e69400d046003544110300c0c400369449050303e04400d038443c1d0705810800403e4405e90b18480700d5125104028801c420b1400b5070b040000069000507128800c20030301c1281a03014496803080440a21460030040007030381c02c140c1c0e115443d8002c18081c840901240d2807880002d90003045020040141d00e0415140c00c0e030b10900300b01024080f0000e1520400422000c0b5400090031903032101c0344c3c40c010390f4070f030301050000022420f81c1c41e1070340e0f4900c0426081400c803115600c81880c143d99665803d400e03603000c1c0d01c0880c24001c05000515250301c2d50711400d003201040001401242c28800340c2c03031030b1250303001111681c00c0d403e00d4949038199a0f00815994003484908000da220201880002e0800314002200000301 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 203785728 1250 203784478 203784499
    0xb01030605011a040b04090c02100e0c040e06060306150f0303030a021801021204050d08070b0708070212040617060406080d080604140606070b0402060d060b12060a0e0406090c05 78
    0x3152941c4628101c43c54088400801d201c18105161680158411140c100c0010b0108001c500c3c9950441410114944152148091000070103000c84d039841001c07072001c1d03020000e8003015040a21403440d00300313003070070007054146094800a90f449500505514204d031900010201c41d8170b850140007200c120050981e0f07201d02d01280090001d40180481440324624018240c1965002040380344010519115041c07030281800d0038801300d1200302400322078400e010446000030401c50404180103d2103a0794400c014104107100034540000709002c0302e80050300304030030480d85400034942c0c0301406902d0f40200059440c1000540148540c0c0e01081140c005d56882448032940700760a20f11440b41280c0400c02030b410345501c010082c90403514660840d50030041c1c00080742c2592700480d842407004000500e09105142c4000a80301c15504c038090303030f603404245152503003446844964018019a080100c90b80b4080743d0b072042450240002c5c0005940c1e180120a019020401c4800b80c078000c0c03c14000b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 203786978 1250 203785728 203785733
    0x60c0d0201021e0703020721020a1e0504060f060305130c0e100f0303090501050d1b021018051c02010902150301180507022a13050f0108061b0a0c0b0103 67
    0x1075482600404400e522220f01c0d000d07407405410035202040d13051703401003403540c0c181294805080540c1c400c9450703d81c200803101d00140c0c1c81c0100d1002420108881d15150014030240012041464000c1071080b42088420b01a40c690004504100d80192901091588a66161145c00005040040d10041d1a288003103120000030b44100e020f1b4450405200c1c4256580600e000b000485000080024400103820052988500040c3c1503480c10080b0004109698500130108100100766180158000c122a80030803042485000d070140711420104802010740c3d40c0b03007070b107800d10100351620b66940c625201d50024801d5125802031035000d013080b0710210414603142c3d4540c00900c61900d5044d0710510b00201e1000c075020741030082c1d441d90028004141c42280070300c151001007076454040013160b2200c090641e606640c0e441400c10640c1c0000710b80c1001c01450135409030507000621150b000c602808007071181907420311050701c00540641e4890740c684000702d032084031001000e404590107030000b005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 203788228 1250 203786978 203786981
    0x1023004050411040509010e06061902030c07090b041802150f1204031713020102150730110403050601060509040b030f10181104050c0915090f0a180902060c0d0201 72
    0x30307141e04039620f1041f60390380e5010320800103085803c1c2d50842002d015500e03410047c8244030b204e0040f11f00540c2d0401c0900a0140e01c1d0415a5100350740094580c40c154500e81490f03c106c0c800c0000c41c6c20300d85154507407500819090800c00e800f0360ba001d100001d00b5001e4204140035a003c0d12180482010303d42050304004121115030b2844d03c101610b03200204070303207440740d021800300c0300e80c1a0042c2000768a4104841c0c00680c0c0108032409100f200004404418078481d145c0509688110034620030007074000800040b107507189034400042c542000140045400003444904641983c03070f05590314411400403070060004001e04503054407400c0048003407103001141403603203800c000608001449419021141c4940988806450840304080c5038206040c203801c12076014520310880b034500064540420401040c03154111400240490201003a140c0740c10b040c1010041101c0c4500f29606090106582c800d2440d011503c0907902c0a0440840d10f0310741c10f443c12640304d502620100c0d060748001a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 203789478 1250 203788228 203788237
    0xf09030a02180f070e030616050c03042309040c090f0603170d1103061003090c0302031917040b04170114071709062203030e161401023004050411 64
    0x8042088000281500d485468002c170303200d000030000c00107511540c000d4a0380105030115941006000c02921900c524108020310050846905103400406080c5061501c1582d200041e0f101e0840c1e04144404154100c0a98042d182e46400c0010030040d0200120002c120651000309101040881000c0c03101043c00501441000040c0c00d021152b1f00600181da140b2007240c943d58080310202200c0300e01d07846544044402841058a201003507200c1c0c000a1600c0701040101c0452004071200000b0012600d44c3c0781c3c10502c075440b605081c9402c10120a1407402035004503038505241e07400c60383d03031200309400820003c01001c58000c00303820b003c100204860103000000305008100e9022a9448000042c1c0c24842c11011102d40b0300d01244950519680c10b950106034105603d5040c5186070070411706c104a50102c01d2546085030754900400c0301e9283c10480c00007070554110011844030303141c109880d40034000501741420915941034503040600d01484d04595089071030310403040122000f180050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 203790728 1250 203789478 203789491
    0x605030d090807140607020405040c0519050906130213060e030c0307050d03110703080a0e0901050916050d24080606090421051c05160c0302030f09030a0218 69
    0x2105140d24081058501c1d403001d100b07400440c1d00501d010080da520314480b038025030314010050741c60a03202d900003400f03844040d10183c072401c480300c90070031144c544215207426241050202007203c0c1e2920380021181d0000801150203107034081c04410440d040c07a411070f501c030741190341c035231001980307500d07004020102c10f031060307402881609441c005038a00080c03500c049a00090815424103595901110326444070301101c0018410444e002c8009202c58010b000356520390341e160071840140c107003001480d01069200f0360103603050364248402c0d6410380900300c2c0c044446007012a0341e40700b42c6011000a0581d03800751081d11030310926001040020b003401000311b50bc440200c8a560f00c4d0b900c204002e0843c00c2e90b0062205240e203403040c0d103801098000c54696019410a182810340c00a2200c20700400042c081942903030b62030400910705044c244a0745000f41c9840d01c0343c81d02c8019038000e903aa01c034400760300c80c20038808920080c0e5582c081064903501540585241125117045441d0500d030801070340d40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 203791978 1250 203790728 203790733
    0x1120c080402240d020c0102090907050d0b1017042f04050903030705031302060f030a02070b010603292403070807020606180604140c0a090e040803040b0c0c010f060503 74
    0x4000c0344002c007418506405070f40e14a454a4841c03440f040095202e42008803440d50280f00c84a140d50f034001906120701102d46440b5540c401c5411801d01300c2c1d0200c010580b143c04820792400d0b07420b60080707007495041041c034500c2ca142d44550030300f040d480001074607200e5910b40c010000f035580c00c00c1c11040080d03404141d1301032145841f404103141e100c0c0000c5543d140055400e000142900b0303601400041d100d4000f8148a2078120608601c8130942e008480d00b000c2150001812020812441c0c1254010580b46ca400c00110094444817100031000c00311035494002015000f00040c0c0d24402d120300e80c0c440c4034039101030300322051b20f01004681081b5070200104081000080c251800402c115104100062840d4000c2d4003000980311b4800000d003c0e02c0d005580c0b074115009040c442c0c0402c60090943c0030006031101180040201042b1241c0c000c82d03012050507003800000349054086e65041941f082c8101c0040d510070000c401d4038000c07004140d0071503084ca503030004a07410301d900c50400d4070f03820707401d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 203793228 1250 203791978 203791999
    0x418111c0e0d020a0206131a1c0e070504150e0a1b0c0206040e0403030e0a0809120a0803060d0539010206160e0303040317030108060f04050d080601120c080402 70
    0x107030a032100c284035907030400743c2c101000450061401c50014810511041a8a1001c07130303c0d0f0b40140380b0007295461038140e443c0d0006003581034001044080546500000c0c0034064203984070310a40c1c4400f407030320545001d55200d80352042c0c5011030b000c038400030b02818500e2200a140c03024805000d00b840101088190b4840c10a41d07105c00c5c4503c680c801100e03006803081345401c1c601080807d03000001003058041680e18542c1940400d81845885401030013000300c9038503010780e50100a09000c0744519200503a00c0701d00f82c8400100c407003043c3e0340d1021048401142c1120b95080c44d60074611030840307010680c800c0c0d220031382600300f032940640152284201d448802040f24001603a942c4410b90300c190740c8136104c0c554441900d01c920f00741e804000b0090250381c2003075969034030801380110064060002060110051251800401c42c0c1a44000845181e100a0030151983c80e12400200943d41c100282280019005d90080102d054070359000a0200f001140780680188005000e0b03904a00c41d00e500341c1e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 203794478 1250 203793228 203793251
    0x2d09180a0807060b0d030806060d0603050a030e010305010602010614121c0305041e1e05070b0c0604050c01021c050901033809190e070503070f090507090b0418111c 72
    0x10f54031703100c04d58036448008042e20391404101840e0040400200c1c080c4d07c560001c00014810300022005520035260010304400c2040050195481601b004046a2400d14100241c0680120015603840180c0300b2084d0b561206010724149003128607000c1495010905081e0007a9140c1e100c90720035800340481d021201c0c600c00070f11031801d65000c00a0001c119000d890015540710013090b18a003031048084500c20307603076611803001cae0360089403c000f01500b16404110900c4002c1c012030310802401d10251041007400300005034862401e8600d1380c10040e001c50700303100ca070f4029031140b10f1300b4a0f00100725000c1c0c1800c0b401c6055803030fa20756941c4034644104c441d05489090400b000d40c054900301904070340d0701c900081034800400340b40c030345441607100d1848000b03210b46041c0710290142c00340e61078400c84c0d541891900400d84401800b020208541c824080085192010584040d503180580c241c1007451900455005418049959020b1060000d040407040301c0f000b000c140340c0c3c068442c05000010040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 203795728 1250 203794478 203794489
    0xc0a030b0607020f01030f06050310020a0318021c05070504020301030f050c0f060d0e0106032909030307050a0e0d020406060e0114130608040203030c0a05010b2d09180a0807060b 78
    0x42c0d0001e400c0164040c6406644d802a00861082c03401d44d400040c03003541d10030001c0e1030600350780841c00941e80c0c009084568158580240c000303030400d070600007079030610039404100b51003066984100c2003540512100e0400c0014051900103101c0140203540fa9610390602c2500c03050719007000c68113403082c2400b8000b141070a055040760403c0c010081800c0c00441403154001c1c200001001459550300d070400300c0014010b020044820011440c029905013035038101c61004400034102e000ea650081c03040080c803903480003c49a4110f81850000010040c6001003020f08a0284c03000351b1180c103120002c15019407001800d00c010800b60303a500884010302041308114031420304940a00281c0782c50034007405010350070241c1c11910240489141c11000002c2500b02440307083d00f1140d69440300c00d814110300d840030b00140f1800c101104600c0700300c1c1c65200702441d020394144890080c858800004c3d20300055010070175400d48900103640a09060385405501a4404481140c680b490030b0001102c0c0d0400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 203796978 1250 203795728 203795737
    0xd0c0312020c1e0a18090204020304111927090803091f0213030f11120709360c09060e09070605040e04080f0d09080901140910050702040f050c0a030b06 67
    0x82c204c61540c9042800c1c00000c0100c0602c001105c80c2c46100c640c0040e10340344000d40c45140a540e5090f040410b04040150070113150f0600c04090f000c54074140082c05810341c4c00d280c03880300316402ca101003202c1810f400c090301030a1030241c59800007008011043c900414950181e120410340250703440320203002801240900c442d190341c00d80a241007440052400e00c910ba105500a124100c4401160000106058100b030b00c0704030203030451340c0100010500d0303000f02c90a008072008001a00e01600381c0c81c2c034109802c1d19011869480b00c9040ca414032000c81c10503809007400c47c1d801e00440d502c0f1544125821f40c16034840e04103104010000546c648940c007500c064a4500488086c203841c0c0b6201c1c481036401690b98a070300f0190401007000350808030720818074814440c03140070384c40d005800000340040740d00c45080407202c002005500000c0e42d074481700a402141e5400d0079030300c0d5134950000c100100070f50b21030442914581420300049502000103003500b500203070b4091241d49012001c0c0311a9002c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 203798228 1250 203796978 203797039
    0x60809070503240a0b0307120b0108070b121302042306060307090303051b0d0804060f05060a0501030e0c060c07030215070302100203070c0c0b031509060607020d0c0312020c 76
    0x20310780c03810301e143d203800c5809507004103202c40c000c9055100880001c1c01c00c0441d0703115041c045401407001042000810340701d401017100001030860a881c0ca01940700d07500c10000c01281c03506506000514102300006441082500940200803460000f0240c00b0000306074040d20800400c0400003520364a8840112449109281c0c0d811802e84c3c5150350176a05a0015a01c0300c01c101c020000b1030960030810480520361700080c1c0e40c2c50a240c1454107014044540042d940903800d4104010442244c880102c00400c0342c01c02c1c600050210b241080c0c0c0c03410b1242106c03800e5403020000600d61201d41c80019180300760b0b0300071100d51401c1241590f40c248248500440280036070442000c030740942c4581e07405036522a6140c20851440c5555980d030801c4404a5040b80c0d001040100c02d001125141052040e8003440a5440442c07508080380040c0e12801070401c02885800070705803500c00c110a850303441d40110b0384100b041d80181c150340800782d15880c0118285000b10320480c44240000c0c050700030301c0d40301032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 203799478 1250 203798228 203798263
    0xb0a02030a0e0a12050c0a0b0f07091422020418090209010e160311090603091e0c060d0203040c0b03040c03050111070b04110619030f0e060103050d08091204060809070503 75
    0x2801032000c5c2c071141c208a000000f2802204240d202160b42d00d0030f424401d07803040d803420710700d860b0440024002c030005801c0003480e4035107048a0701c1d89854a100c409441d0400301d0b9481040001000180040d10a03900035030b041e03030811000410706101642110b030120b03100300c41c000c900703a0f01c84800580543c42107401011080c00c0c0c0440500160080e03101e4172a04541540241c41c1103902408920f26510035100703005583d00000c2024540c0c08031902885e0500345a0014181c80251100011080d0062800110001c2c0d40080881c0c1000080d0116100030500c9002c0e0717035260300d0542000b45052120f848280c40ca5400d020407040640c840f80b007160705103584182280c5054599844060071520100d003a650081010004048443c0d0300c1009070240522540e00460145515843d0006550551a800720f0b144e00840052000510100e070b9003001315403502d000441960303003404039460251003070900c01912100103400310b0301c0c5911500342c5104031030660458040594940a040e5164400b251029001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 203800728 1250 203799478 203799503
    0x50402180403050f07050a0b0705040b070605090f0a0b0703060b091c020f1c03021c050316050d050f01060e09010e010603020a03021b0a05060a020a0c0f06090b0a02030a0e0a 76
    0x200040052500700d8020700d05541421441a003403e40742d80546015075080d80002d802030100464140e0895115030949082d038106490070b05c6d0090b46001d91a40106400d031030380300003945000200300001c13070404010112221450f0505000508560036202440028100040804e006121a0484a00c07140c042d00e03844501c46004600301942d40a400120303400401a418480c460b41d0340f494540301102061411042e41403d841c000e4504040545034506031040a0040d075007083d00f00d02582d90021856511516100351100d085600d0302c10b5407518805140b80405001d450a0103020b018140c13500364582c02208400c40d8100300a0608c04d11840c3e80d9814990018407505110b6000380c5040101c604001d420315540c0d1448080d0403c10005ca241c175030b801089050180b010411403141c112420b2601103103011030b4444020141c0e4002403011300f200391041c0c40d080401a0541c0321030034044d0040140981400c2c1480c1311000303540140e80c0111030600340101c40035116004a4000126507100403980000b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 203801978 1250 203800728 203800759
    0x810091212140c0a112422050606030c030a0506010302010f12060b0405040506061c0209151206040b060307080103020f06190801030303110903030715020f0a03050a0c03060501210f15050a09050402 86
    0x40c0f00800c24047d0b41c2e10444407200d5213151010600789148a2009080f03603140031000d161401c00400c030402c1c40f95222040c1030740890004155541580c0d02032a0a21040148034810307150740900598030940d491078901c0011f103500c1060060310507030724100c0b001e00054a03000200b251900503400c580d00656015107400101d55020350040040c102c010305241015808400e15402582050885410b017118002c100701591a092095280c0d00c141118a10f0850070000d1005052180501000f4000c200c0400d401441c1d82d50a0207840001140344c4c1d4200840307a00d40781c02012400280300031000319042004c214404c600100503610360790405801542070003a0360b1071302c21003a1211001480c00c01d50070000300c8001ca000d1801403060000c5a00c01080c9411710b044114100c5400f40350038400c061030140306103e103030b9002c1d82030009261009281c1c10300120100c20030000f03041c00b042c0405190310700036180814901d5a610301c411270340110b8001c9042a0384101c401d043d11021500254040c2041840700503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 203803228 1250 203801978 203802043
    0xc03020f22050604060503010f091119090b0d060c0201150602010e0309010315090908130503030301030b0106082509030c0b030105060307050a03020f0a090810091212140c0a11 77
    0x1c1c8a80f00400204455607618080390845201d8800040515219200e40c2c06115074240c10a105850617107040302c92001e48000124848501e004103001c841d1282d6588081c2e65507002d00141c0b19402210401c003100c12980d000c0e00a000e0651194181070212500040090061103451003240000380903500c1c0c01401c01c0110b00810010220001100b800e03100400e4450341445a0400703c2d100d0301403141d40c1d842da04008c10b11034000d680164860780c0200010700c00038101080e018111481d9050508a540b0761843d0034264448403200c1003c20f00c01d540800b01d01c19800b640e002d04990241c40400641c5071140c1c401d0789079220902510350025410000710301420310890040c40c034a00145001800e2400158800720154824007080b8000b4140b000c09001400c424481c3c616000c81e142c004008400d120358490380c0100d03a0500030028000c01c080302100741c20850300070702200081e0303000e040454602181140980d030440046200041c0d16103058004134000000e164000d6041d500904080c00075400c031084 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 203804478 1250 203803228 203803231
    0x11030906060d0305030a0b0d0f03020d1d010c020603040218040b061903021c03110105070203030105120a112101060b0307020706020613081c020307020708120a080604090804120c03020f2205 83
    0x80e008603141d00c048c0040baa00e680301100f40b901c20b50250002d101c20301d8000b440c0152000b010007076001104a03108481c0c0c0c20403441c0011603410303a0a151283c0c1c4500000d60f010030b00c2c0f103001c40b0554a2604000c1084101e02d01c0c0341c49000d00302d4491650400031040309400384000c0c0002074211000d05008850024005030914030540b10b49040d0b0b820f250109400c0c0c0c01d4600a860000140e400480180b0040c44c0c80032090280041c07a0004207000f410940343c09100c00448511280141240c807400c0e1480011170441300c40402e1100002e101d03007952420f104145074022582c460050140031800f16040b44007007021406281c00d0090350020340c0f510380750301032150300c1443c1089040f1140305c1e8188203699140007a5120740300d0354018140b001d145c443d40f1424030843d1046036007402c4c0b0410440101c00c0d04021800d030020000d03900000e1000d42490004d0305889580c1101c03801e01e6000022504000c0c2441031401580d109940381e1044010300d406010f210107182c0b40740c1a201101c190410b003600207590196 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 203805728 1250 203804478 203804501
    0x80304020909030c070306061404020319050702010b030304060801170601080a061109090c030a05100501050403150f06170f0706050316020c150a02011506020d050706020d11030906060d0305030a 85
    0x228075002003881402d103400040e5008030381054a6200c20030000340c43c621520010480ad880c154954580540b5500d114060f1400c0d03420003c0e44ea1000c203030940d100354082c0e404514090f04503035480e62903e80140060400b44a501c6c69040002c840780d20400c400b0070218101e907000d100038208840c290340c910000c0c109824078003002003000d20945406540359103080303020300d5031110825074a05240402d4815144003d001c107603802c0b10b0030001c001f9a68020200c4017100e070849811b41c04140300c81c0400001e040000d540001107030070b0001c0800c0084070070203c0c3d4000303c0340070121066441403c680700d80b1880144600d9010840c01c0c800140c290340e904a5540391010103106803194000d001c030001d2491401025482c14514001c1841300f02d80f6024400c50340c2030500000b01045003032910703a009507101200300d0100b0030810b02144250800a03250145c0e641103003801c03814000f0328441f005c0b0103c1e5400072640c10140d48201c00104106080503070003038175801d80541e211880d645d1240e6492024044000c0304 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 203806978 1250 203805728 203805733
    0x10614040b03031e07031403010e06030606030f19060603151b03090209071b140d03060905040b0619121101080106080f0c0a0c05031303030f02150a052e030618080304020909 76
    0x503007c0000c580e400a5001c0c051440812049080403418180340102c000d00581c000da100745000c0d4500100007a801b1100c1003101d070700e5082c56029181900140a030b0b540024241d444000d03400702c032042c50350008440f11111071f008108098600d03404400b51140540041d402c2010000421b1410f845881460380c00f011110a6402c01200b40d564078207864003410207510300360011801098040d41c5402203100502c42440c0900250800381c40d440402500039103068407541e2a06006090101e1030340c07007200100032641c0085003020050909a84901458080c2c034005003100c0c0004c01d109000e80d0f00c044c0220048031225031144d58240821070130b944160851307001c0c819001d1a160000d0b0301003009118111400d551564014914070300545640f102e450090255000060b40071030b00c009100e0710aa10010320003001c40d041d2078950102038146580016148401c0700c1d042c0003003603a000c511113003003124842c000c20803044e46d06030715550084840c18801001d90307004001040140c0344c40d9502c0d43d00098a03009 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 203808228 1250 203806978 203806997
    0xb01050402130b0315090105030c01021506010903120509012c040c1418040f020703050f0711060a0305070206010b030601020322171609110405190503010614040b03031e0703 76
    0x80181c01c64200319000e59004028071172a0025040601c401d50040800341d0042c04c5031034110300041e4a400e20308146007480440440040d140341c0c070417446039005603080410024000c001200080450b4444031299004c04c07041e40d03100c0d0107170f0402c40030071201c049452481751414803880c0801021b400341c040384071b0410042e05c282042d29459140280000703110b0400802c1c0c2d000303105007803000f60b81c1d0b6404070520703952051000b00c0100381c12030110380d800841c203000290b4808540c641500b00010640b0080c0e00400040340400310b143d00755110700d0207020036808840e02680c1e102c0e5402c0c0544404c50b107140c0180c00034010061241c4805500000307004459808082c0b443c1c4a117601d68420411303014100881c3d01083c880409401c030303204010058201d4150034003080d07400c00842d46191087e0300c20700707000d580d01105249946008030580380c06070000900030f00140d030760b44010741c00104110500d20720a501c1c01c0c1011402d490004111010000004445c2558010781c01c2c80302d01075081010290248802c0e81e1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 203809478 1250 203808228 203808239
    0x804030515070503130809011707030f0f0905070509190c0309030e030f030f07050118080a091e121104140603150613020a02030705070807060e010c050616020a1a061206040b0105040213 81
    0x140e270070b0310840340d50341c0000b00c42c600d82c01d022043d03407060381c80f0811a0745800202008182c1c04610a42074800580e01800c05031100c140c09645190a04007040000b490004080c22056043c8c20210302d40380a80d0700d008040b0301c40002c041c0c07544039003161070300306520400a5aa041140030702902d000b900800002134040e9000300c103000c0301601840c0803120114001a00c207030203504604241c0103040740c0c9001c901c010341840c0343c1051518a40c010042d1405d1100c040200b002040843c113840203002400900008503101c81158803490190744880c8a03000f1000c820380320210781849507200c0c80000700040c2035012050303c0800203500c045803080460000f0890f5801181003000142e008241c2c41001340704452410710300508070425158120704000c4500d001c500030134000038105d9000200f4242421490720010313002d80c58486561740081020b0a07801603072401000141c40340e4410042590b00703001c140000445640c45560454000b458442d4010062046080c1580540b4603500000c80d48000780d504c84 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 203810728 1250 203809478 203809517
    0x2406060d060315150f09091104021216020a0302030d050405070e01080a0b070504080318060405040f050f0f07120902030304050909010c021e0703030516080403051507050313080901 79
    0x2d420943c2c00d001040c1c08900700c00701034481d103040119010303260200c9a0a181c001c1108501c01c1c41003962268981d03000500303000c41f540281d401201d000704215942e454078900c0345140c0d0340c116482e1000c0f1240790880c045c0180045444420560315602661414100c61464001400060700a0f03c030380c4554080031445224910a8502a1000c1c2c0010329815513249840d0300e00c06002001102080002e010421409100000361400c91100603002c0c210f014800300465064001c0307a2080303500508044c05840f0007009540014020601010032640d540d6842c818502503080035502ca000086081d1031038040c1086943c840c0004901c0101900c0c5800c2d56100081c1c4c042600399140175860359620007514040390100852a0b1107803043c1c01075040e15880300b203441d441c2c21303a92001074113110000807240700020100c0e494945140c3d2090501e42c440d0b8032800c0c0035940b903115070004426807102c240490840ca0042042d80d10a01d09012610f60783e011a54803010144c2105403903a0601804603650b41003900c0d807 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 203811978 1250 203810728 203810741
    0x2a04050103080706051302130207240c02010b1e150c060a0501080607080105100f110106080c092401030902040b0406090e071a0a08071103041509082406060d 69
    0x5030348410f4032540c040c00c11100b1110050006200c0c26001a007001c0140c5807006550307104100960010707290506420503801101c03000e804925000c2c401826950341c0f03a80e039809140c96444d0f980c02003050798100320a204192030724400000781400204486102460034860302c7d503a01400041140c10245000d460503c1c0c4403090311210a6580c4500040c420003004011030390f440f004501d000c10b02d41d450800810a2070454000110410042d0302d421b07607020307000d480e15030138584816008000d41c903501c617002078941da42d00030700724442d004003808520045000000445030f17601d0203541c2d18502151500640045c410800120b03009515400b1403c020341c1c49208840c010842c81c0804104105000c0c1c1c20380c100b142507040004074098500307220307003019651001c5d50801203041c202500b040e110040c0980342c01d0006854002244400503020620030030440c440380304c06440f44c07245400d40f41c4440005440b032903c09001000c0050f403c240d01010b601c1308080e1a00020080c0145242c4501c0007a6007066400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 203813228 1250 203811978 203811983
    0x30a1208070f0801121205160303020d050606160605060111070306051608160507061113030b01090e03040504090c0e070e0f011d0d2a081207030c1203020d0c03050601020106060f022a04050103 84
    0x14045500d80d58280035001d4dc030790200341100d280b450110721500c03507101d4942581c4090f04195031000002c0e0b00e640145031603c0c0c106695812296503a0b17591402d0b0300503000898000d40040d54445140740d82c02d004030075650181514600d103012800e440d100031181900030346002e868150301c50485804841003600105810a401034044a0781401c5003064510031740103030b000300c0d40d40d40b8041c08103014200100a0790144c420494002c03c0e103441d036080c040300103040b40c0c0241c0c15a94440d01403040d00c0350000b0400d01420425228514950806801500d0035501c002180e040614400000b215074a48003000c8003200b0b10594211004050070385100040c0c03183d000d92079100303a10901050000c038008104403141d0f015200700340ba1510b0034070b41d0000c2c0008041c000080100301c04030900003034680242c05071040e02d0310500e010402c2385100c42d4002c02030941510001d015520f40303000490420b00c1817071442010034050300100081c041c1045070f080f0301030003c4070458506140c4000c000a45d83c0b1405554021070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 203814478 1250 203813228 203813231
    0x10181a1e0103081b060606070f06020408030f03090115260109060e0c040f1802100c020405040c05120f25050a09091b05031b030a1208070f0801121205160303 69
    0x42e408003201c81042d4201541c4c0c0c40c00c1c0d002d40c04201d119500c4100b02c4a0a45c3d001c000d55685501616010000c0e0069800c80c0071345020200d00c20f00d5000084002d58803c00b4500300900800510441c9200740d81481d000301c2481c60811141c03030303026881d51090345000c0841d4400000d0b02c08256284d0780d08a8500350380840e400c0d00607e100d60a6880c09029804000d041c00030108200407013a20401110500050024003444103188129051805034021200c2d058025000303216920b4a03241c80040680075008031440b4900c01d8104894003040081c01901b80c0c0c40400c010005862000c82c4942c0002d5104110500003003000300100d52921a80c1d0711400a02e9030400110703100c0241d25100d40d83c1070200a040c070341d1135000e8108011641d000110a0301c000d82002d284a01e05283e500400d00300341c3d0b017074406019107003914202c0c038083e42d00003141c0b803117102c550743e0f10508490101012240c4400078841c2005a008600c808004245005401940c054807030604500d41244c40d400207080005010007500806d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 203815728 1250 203814478 203814487
    0x10608043915020f0d080c071704060f05030402181009020409060e01120309090209010912050c0909151f0e0a230708040b06061b10181a1e010308 64
    0x14042c05148044989070341c0080e0400b42c4c0b000c190075541e0b40f041556441045072020206120b80b8814040303a40c081d410010408107881800da00000e154800d204580c0011030062814014600c184203072401103500415410301c9000f83d00302c07002030110140818400c001d11003000654929603100400041050382d4010800c5403400041d10322008050f4011000c0d0850583c030140000d42c492080350988400f1a00161a400346200403903d1110540008081d0341084900030280540018112151350007100c4140550780d03030240540e100c08000075002c41c0703404001c003c40c03080403c80f0040c6100343e090041c1104850340c0c41c00000102c81054800c00116941c40100310b070084000b0f00100c08003000ca04c00d100203800d00308401084403400400203440d588500300070030340d42e55400f41110a081c0d540c01406004581381e80000740c071081170720501010700f894181000c40c0e128613041e44040c0c054104041341a01d0441604142140078020040740044407014090442d80c18445440c501030741c000e643c01c9844 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 203816978 1250 203815728 203815739
    0x1081306150b120105041d0a12091203030207110406050d110409050d0f080105060307080c09010201090c140f120705090405010f110729011214011d060109050106080439 74
    0x2154074240c0c00607c250004054091006e03000691014400d5104420b64450309404a049440300c41ca604034511104045075040240350341034000c0d0504ca4042c521013105860a88100000c41c0e4991203601d030040940c907007141c04101c1d4204d2038011110302500c081131080c0745503503260420f0020a81c15011400030218070050341e0f405032a4034054841a900c0300c0c91420241405000e041c0020314400d039818000440050700c0c0d20030f400411226a011800c04400c0d6200c2045030a078078008106030b4062481d00d08070180c989040c000445440c64000e0203404918105800e1003100c40d0001e00a0b1469900c0d408680c102005078070880d080c03002c210b00078076180e143d036141a001034001092801c09004500c1100640020002d0701d060441d4540302c500c1050f080a403801c5aa1101c400c10700c84e545502e480320141c020b980079000d00f031442c89140c0139903c2c180c5c2c0301c9680c10201d540a025500c0054540340000340040c2d24130212079013140400174100c860340c003074010318141c5070000d14122a0764070300d400c410001d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 203818228 1250 203816978 203816981
    0xb010b03010614090f1c06050c090f0409080306091b0a0305040611120c0c0f01020c060103020a050105071713050405040f060f110d1a1002010c080601081306150b12010504 75
    0x55800350150f9072071070700c110180001c0081c0d5000469500c0b980f00c80c4a4a0192030004201042d070030740c02007051140e8a000341204e02d241d0800c450250280070071100464040c58030744a80796900ea440440c050841d00c0e41d5003808120321000305522032041ca0045070110211081c0080d00000400baa8007003444c0c580b81c030b04402590800510402403403070500c4120b13440c00701c8907801940901860129070309c1c0c640185480e80f42004400c981d2020754400a0700441c107504c0802c505041e01c1c020364024450f04d0752180115018420144050a1030080ea240365081c43d003008028100780d401d00070351040c20381d12500090200c0c0c02c1500d0444800529005590402019000740c60741600603003c10070aa83d5001d4440380e0318415200303190469079460185001d8294400503140306d411000c0d04416103066030b550040c1c000c009003000000840c0039540010110340c46101341500c120400f0401c0103904034580d071a000607004948000b482c4180c0e050f0085049695000940000340003890181001d501d040705000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 203819478 1250 203818228 203818247
    0x7050a0506100918020d060213030609021002030406020304170a020a080d030e06060d14031210030b011505040302040b13020a030207021804050c090403020f0d0804060c0c1e0602070b010b030106 85
    0x2d00e81010300c09042003c074110413040300c2da01602d41107581440361811400038440c44000c5100c5074074402021051001c964000501c0303600c260341e050a80580e0100599490045120fa40010f1b4000c210520201009035040c0c207e0840c1c020807102c040c50298006000700541c0e030409920356002d480d0b030300d02c0d00b45d241c011005082c2443c400780c0f4040c102400443da110209801c06001900090188054154100103c03200e1700c24264801509042000c80302600301160b220544000c0c80c440000304a0004410300301c0140310058640c02d24040ca1a42400013a004034004a40d0000c1c0d81d01030304080e0001c41c0000c15807403465582c0169695100d10420806040b04003200a0b0081400100700010b0400035184000035403c840aa0301e603070b980d10b0124903254911400c01e03081d024282c04105095041810503014920404040c800a40400011101010f80348030140081d10f29901d560343c0d189038800317801440380c01124054582170241e00c070165406070030384c0404450440080100200c80d44041e014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 203820728 1250 203819478 203819489
    0x3120815010c02011b03051204030203041d1e07020f1606020d031806090804080a030f03061203020a0305030c0c0102180306011a0717041203120c17010e06010507050a050610 76
    0x211030102c1c107030002030074900030b8103c94110114120244042c51300a8055400e5009400c620613050310302890020340b6904240b040c1c03085900d0040c0c3d04454400d94a000701d10401e00c05040d80800c5d030b030072080003400001c06041101580070f15051050038281c00c1c0613101602c00300c2c181c000500e62609070700a2030000600d005904040c5050182a000d82c422261010925080000820205403600f000d140305c0c0b1441d8000320051259007540020180c00030303481e5036080010307102001a1a80c805040c17503c124010801401070304044080000240075202440e048070a00d0039207810001030940d0300382203130700650021007000548025030082d45070400140f800341110003840c0d0300c80c22051104202134000c0210040038050381050b6109403008840030781c1c000301641c03031a00f4056511824080c00d68540142c80c01c40081c01d040c02c600100740605807448502c484041440d415030300e4204448065030010304200c1c10480200b10100110700300300280c0c44060f000b40060189030074030400048a9040c0d80e44070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 203821978 1250 203820728 203820737
    0x30f09070f0b030f06010203090909010b0406090e061602010f0c020c0406080c0a140612040f060f06181503121215050d02010302030a09020915011202090a030201180312081501 77
    0x82c00740124000950f07412182c2441109095196800140e046004803125284c02c44400000c01181c0d220540115400c81401d8500b013000e540c50707074164000e4600190750b000c00c9503c00d0380801e8a07802d000401d1031240d0710910000620a100e0104d540036a0342d6000748500503800100c604c0c842e031500307116000c004c15414009082c400b1051000c41d8400c1c40c980328200c0c40700081d0741456116221403003169070040300e48513100b088d49071030301d00b00c40b5030560b90a0645d2494640091800100c580307204150a886d04014200b407025002d000d50340181200c02e41c84000307445d0a240c0000040ea4114003105032607456100c901101d40c0540000303040b42c4074070201c00d6001c0c1c81c01c0340c100170545034120b804810980a00e00981e603036880503180b00c09031550740750082d0803460034010460030740440c00f40094248000d0780c038103280e0004807400c84143c0c06101c0040340e00c00401c031300400056000b00e0341d013208450b034108a40700e03c80c1d41c0d4803130301c407100d00403c1c1d00c0707000c52075290401849440e03017003448160710001d090 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 203823228 1250 203821978 203822009
    0x711240c3304080d060b22050f060d020415020f10050114040e0f07060e01020c0103110d180605040506010e010506070302070b1312110a0e15010e1203030f0907 70
    0xd00aa680340703603005001c8030081c400301007028000454125113000391000700c103200107540c41141004a40c4011001d2a1001102a0340424044a0507000e000c41350020004140d4000c2c00081000d95480362210583e556402c10000506d140743e880c41303599024558024103141403850354240d050114141c0c0b04000b4038903040052001600c448401400000282d0300001c121503849aa68502a0080c0c100c0c0340c3c0d84610f070400501e156104603292a405001c3e8281e400518a1000550569102c0300010384003a42c04e00280d83d012800e5841136103c3e181c044044d14860045440d814101c0f0070a681c02e68587e04840700502408000e0326520b40103000640e01586080540d0b10000d4035282d00d4041c218a8280000e0f1026808070300782c1c0241d020f818560918940c0e40c00615150a000c40f2041405006c3c0c06008000602500c912041c00e2181115a2544540030200c1c00111b42d4030340150846981700a0f8030081a441d1001000514440c0d070044540c0c030341c0e42c18240d808529145459000580800403800c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 203824478 1250 203823228 203823283
    0x80d020a0f06020702180702070602032802030405060f030103020301050f131b0b0a02101a130b221409010b01021009080702032b090b0711240c 63
    0x5180d50800d5040010040c203980c0c0703032408002030320444102a50040910000103c0003000c020000d0040c04507800322182290748030742c260307207a0081035407e00c00f07460f403a1100442c40c6d002a1080007880000d1040d030746020b07240c00010305181c124041e03080d0004030100040c0218202407003210b4210380d01c0c6c11a940c691410707401414500c0010b12004040010b6101c001100802080f0010301816402c0d20300750b00c4010810000395149001d00c4922406c03400e141c51410280005084c4450800300a440c0340c1d9148004404040640506040e864000e400844103c0c0c4410f02c0394000c103070b403140802011403614403241009080450241c004000e1780d240450041a0360703000100c00d03503501c200020201d030b008000c2c20601e45a001e0030601a4040c06075251010080482d03080c0d503402c080e01e1080404074a82086011100d01401c0e015410702030300104104000b01cae08a006401e0207280041440c90710b4100d0401c00c5014071624014010f1403900452a03604480042c40047c00844e0562140071240403641d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 203825728 1250 203824478 203824483
    0x1918050c092206060f060c0209010f120b0c0d06090608011a011d040608010c0302031006080c0d050604020c10021903021804020319090c060912050d0503060103060f0b0304020109080d02 81
    0x100b00521059428158060400403160480c1c0024011030507140c003020f41e1604060310060014104074490500300e4000304051a00c812903800740c5000a03414164000c42c1c0d512007a0f0850007615900e401601800b5440086e05180103150207800c61281c082469450029017909440480c078400008074040e511114260742c0c440301411100c01d0710581216070701092004600201441d812500042d4203010b01d052003550075800035401001d000c00c5821b2010340d2100c2c120341c0c1c1303401a00c41443c099002c1105515210f4281c0105030042c06c01000180b4000071202140d180c0405410344448154000c100e207080305241641902d1000118142503190424591350a9649640c80e60b034140b16982c0440810131440319960302c1d103800740c3c04600420540c4154280710010b08040d00c10003000800140c0c01148505c44958050710440d4098004c2000c000a410140d9090b040100f54604055440c4000a0700d00c0003400d2400052902d546200c1e964101800018200c106503040b640301a801515100703681d031b600 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 203826978 1250 203825728 203825761
    0x2061504020a090503030304060605031e0615180a0603030908031606050703021c0609060504021c05180d120f11030415110409020a02011a030d081918050c09 69
    0x1280c0040e81c8400b00307181500c98a005401490300344c84044100402c10042c2e41c03003442550812421a01040301402e140b00d104400c9000f80f10365034100101081c1640100c401d0b940011100425401440c03916040845a43d10704132518a10300352910800c00925030020300c3d21002e409004095482c15092007000c00c00301051107030041010381e443d4000360496110750706480600c1038401e20790355904010204800580b10038062010b9503403600c04c0014580c5040d1003152310490302ca900b00b401c15900c0b09441402000300034900b40300301c60010744220700302d03005000000d460005074540207100000f446210040751b0010103080c403111f00d0306c52040085804503003a6948036034402415294064a440c09501404164103201c0400e20041030114910300309070050300c83e9228650003001070001d150309019104200700700c00c0d50190403c010104c00305100782d041c030381e0001204589142c80207c600401d01101c02440e03101d1400c0d00d41001c02800c01030700740004e420704c40d811140301c4502c1c01c140c40c5410141d0315 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 203828228 1250 203826978 203827021
    0x70305031f142101051003060e0c210a120c03110304060221190507020414060a0b0a050c03370203030106111501030606090605121903051213020109060206 68
    0x2440c072241d0a54081c3d81c202c803a04907a8440081c8514180b54086a4080003a40402c4800a052081e20440c05070006818281c04800030440561220002a0140c0801e00004112180c0c029001d241c4045400045c01d041030000d10b81d02c6540242d0942402406603c10101c001810b8000300401c12155600041004c00c50880140e03000e07a01910445d00049441001c0c15080c82c440803010106401d038022004d03151030f5000391014800341c2050071030f00d07090f4407040721700590015001105203d50071002d006000040c059003445031414000d524981c0c41c0d0740100c6004d84141410741d1048490005444048414042c8010f00310103801d0280006900d901050240c8810007601041c505a0203074100710440110b07040412003c000d503101c1c1003030005072549000b202d41850404030000344906096103901e9000d6010310140423915210200d82c00081c202900a5007000002d016000b0b00540c6504c1850123100d2054101c1c08030301103480051b0a5044940c02441503411110410800e0200e01c00304c1c000044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 203829478 1250 203828228 203828239
    0x10f1a090f1207031e120c03120c020a0204020c01060918120c020109180b12070f050d030e03030d0c03050a093512150906220908070305031f14 63
    0xc0c0e04071064604010f95001411040700840e0100a0b1482c12002446090003100d148001040e00c00c000c1d9030f15807800100600040b2807041803550714849600405005000784152071443d4040c0c0c000030180c6c1c101400d04001a50344074004c0000b17001d14801c11f40c803204d6136500c02a050400d80c85500c02d101d100c074050001e010060460701c04680c418007440010b00401c20398045044000380400d00203180014109001c2c1503d29141c0848070b50002d0b84cc421258502c00001d032403801c290a01030046140c1404070709200a28842d10f410341e03014006012500b8505000040c6540c83d07940060941d64003400450350945096203240200da820500d58120058104824603084403104d600c6404100c00007001c2e00d44030000c280303481c43d9480301c04d159000c0c48000404180d0311a0b0041085100201552503980c801110841d84480c0070410340032510402094100198100c03c40d12039155507407240304124006440001000300c044001d102003401070680a514031031150504100c0041d41901c11031151084 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 203830728 1250 203829478 203829499
    0xb0304050a06020a030c0306050303090d03111c17010605040e0604180c06020a0506010509010f17031e0307030e070605030a1104050406062f06130f0605010f1a090f 72
    0x2003420001c07494015409070045540302d031080c000030020401c82e420b110019040c0100000c0ba85400000d0b58240b1000914045000640d541d0070751304c03915501d03d031940600880ca01c1c80c840b1440b040e4222881c00c00c0c1d8490147d0300e00e5100085114041c160061000c0c864180014000700b03243c4451107034802c0e401c0e20002026502c52051a901d6009081c2c0202281010617001c60016170216100c2c8501e0320804c1159080d0741c03039404111400c0000d02680c10000d41000e0108503e11845502c01441c0d410102901e00e44400200007098034482280d01c0c00c01c00c0390000034000d1581d0b1510902e00b02ea0200e03030240c1495800e14800070701c42c0c0f001502d083d144a46030034500b94007103010b1084070000c00004000300003940e520200507200e144400308940460400d0001100c0300504c51526100794100704016000a0380d40200711214481110302c00c2c2d50074290101401b000603500c0c85014041c01146202e81502850450f6950842d02d02000742c01040505010300d075401e444021919003c0791084075540d90f00c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 203831978 1250 203830728 203830733
    0x30a14070809150d0608010209030a0f080408030706020306090105010513090b0f03070e0a0c0804050a030c080c1006080705031218041401091b0e01051b01020408030406030e0609060708010b0304 85
    0x14050582d6003544040c0502c1256a00e005640007002080c1115105201e82136407a5800b900301d00403070324078a4050b00008829800500350081540c041442280c02506041d281e001151031500581c6080740c001c2d900206100c0103203450f11107940102424613101d458240d8811640f624600d0920843d420207885414440300f603503d544c010b00540b807000d011901044da80340510b6100702d40a403540c610403481c12079031981903482000700c1440b641d0814000d00040d40c0987c0d040700c007122140001d840e0345100b0302860030140014000e14003001c0441c0404152035003065051818044e566100e0343c030070761000390105102901e0310156070940b146040c2000202d4288070126018044030300f0300c00b850758225400426200c0480d8845140100e40c60300100b2001c2800c807040d61008803000c8018007080060115244070703540114264035050202c03001504090b0343d401c041c1d05d960042d0300500701191b182c100d06a49a401000050740c0014071100416160400d242d02500c0740c03006002d24104005c6c000001403d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 203833228 1250 203831978 203831993
    0x11403010620010219020703120903080301060509060706020301080a110307081b0a150203070b06040504020f0603190615020f0c0a150c0c24020703020f0423040303090c0602030a1407 80
    0x5503181c51706902c111000d41601c0094441c0d8040c0000c482084d41d048490340c41c503110b01c5a940c02d4039400402c16147d40d0230010180c3c1d2a0f0802c489840d840070041020030002503590010754001c0c40307050000d01c0c2c07102d010f103020600d160442040900940c04100204003003200050401940d14035640d1002a140c0000701145c010600394000100d0b02c0300e07445415502030750000c02441080e005039641c2000761900070801007035900c00d50b0080d40c03241e080e5403801c9417031810700c0c001c50304100e1100e8406120340400d4065001d450707856000981d040200c807209000690140130380100c6800600150608045020001e032140403503001d010080c80074005007042c1c0d9030084040c000b905802a82150409650708461040750002c00107080c203034800803a1501d046800001c44a00b56503000303080b81140d030a078000340001498403440001101c111380c44101000c4440900c13250256001e640e010542c82d01d42e04120754540041d80c4030380c085500c10400f2003c182c5c1d1000700c880c0030300c1042040701c0e030b600c00d642003a01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 203834478 1250 203833228 203833237
    0x50f0616030c14070b0609010603090302060415090c0b09040b030105060a14060c0303010803070303061403060403120f050a0f0501081606080a0e0d09030203060606070f08210708060114030106200102 87
    0x543c0e04000591a0188460740400c41d124180445d101c40d4242e81701c0c44110240c45003140014007581c010b0000c10000392405600b82164448614005071400f9943c03640454408c10b03500c10841341e840002c1e08040d1317060a02070304802c0842034000340218202074011500f0001213200301980100710181c4140d155642604490400b40c24004607912542c40b40641c50700c943c0b0410702180420b1810a0018802900180002801c070004014020981c1c46480170703514a00c119581c40809a55281350644000107440b0b0940500f07654140003c0015482281004483d0181c10484040d4440c3e881c4a11030070319868100182c8806181c41840d584031090680007501924a1540881c01661061ba07445a485030a4004480c02103007201c6090302c40d841400039900c40c0d550302074000321a2113256400304a41400500b402114014030303110909090751030750701140d0305482c1080052040c0050008960b800804140c0c4d40c42505c12551a5526201018002e590f50a003844c1015a088200c11810002981600c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 203835728 1250 203834478 203834507
    0x210612100c0e0307060906093809060a0509240a0311040515070b10060e01030902130c080a0f0b010c020108040c180213120f03270b07050f0616030c 65
    0x1a0304040c0c64105c080c010481a020f0000003441440001038400241d83c48515144000500400d01584400441808441c001d01c81c121005040000e0b00c10358480000410036941030380c1e2525114544401002120b42604c00b20503a429100756031518821549021a44005982e080005400d48030555034085405282e001a40c006c503204602c12421001100511045106850300f6080345c1d2010f0a80344072003d01c2c06048002039136401018440e50180d40072801a41c0004e092216000c215451041694511050000018584814020300c070314070707004003250108039980600512421400080400a103094003038100b181d00c9010400b4060000441c00141c80c5c0c06280322882440c20020300c000e0750000e4000c0608034403403a40007902c20020142d550382c0e141c0c00085a030b0400e5954134100c03003804010b5042c81c410400c0d9581c442822017621240c0c0003c1c08241d501e6500c8400a08140341466010481c24002744c008804002401c0c001c80400004012036060000d051114414208c880100f8038814 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 203836978 1250 203835728 203835733
    0x9210319090c030201020c01020105010f0b071a0903072d03030b0409051507090905190207080c0f1c030b180a09080d06081e06010311011202210612100c0e03 69
    0x1007090203503080486080e28000e03002c840d20304072000012422920f00344a00105c1d0381030400140b00002a200041c02803c1c0500e524124403107450401c5503041900399403042865000003000300800c4011100d0344110300845c001e07601d05155100301c0e0064088a00f8008040550754484840d18ac0e031540e01061315143c2000481e1914509074881c503503051826151800499946040040c08403240c0c0990707849456952500b69011448040c140069048141c1c01ca401d040240141d44108a04020000451549400502039000e002d8580e195503545040800201030130400501816158080b030442c9645030b000c5c483c4081c1e0b1382d56240c44000c2c4481c142c0180031540028400d240020039070002e009803400b10302911615a4102074440e40c80788000e40840c95500010010800f0071040950030004a0041c1005166000242c1c01b6030704a0b8040d82c1034000141c0040d07aa6884d098101c400f0717542c003500030349a0300c0e1800920550a40e562805405411025071120591441c007032044644a40360300002c0d04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 203838228 1250 203836978 203836991
    0x8030915040e0a090204050105030c1c0c0815040606090e03031f0f030c0e0601050c0a0b060a0e090105041b0f0515090603040b09100b0607020f030a0203071d09210319 73
    0x401e07001502138000264400c2e8201400802e803450007181c600d4601100030700d0112940c0c100b95048861480d10300c82554891807405000466103014440c070b0380210035007402c0c3c000c01e00d03041c9400d100300c0b03901d45c00c009459880c04443ca103001d03100004680d040103801c1c411282c0c4100d50068100503001d1030708441c21144510000004206148084d002030328100a43c100140d900ca00c011141c5009502ca070b811164072490203d80440c8030b0b03002c807a400040160840d24516100c0d10926076002003a250304110340c0d501c00c20070090100305150484030442003402d19401500e01058a0904c00c00d5014103803003003030b844440406108680c0129440d808014280c60f407245407600301510348075070869444042e0f0207886424010710f00303184280305139880d00070203003400c0507600d0b02440084403444081980501c1034212070405a901000410010080c1c5446200c03901160442540c2c0040c000d041000b0799406034480070550403031652203200c92880e0029035a241d698440e10512200c640400c80711500e45003d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 203839478 1250 203838228 203838241
    0x11d0601090b0310091d10050403080c070c0302030a080309160303020d0323010611071a12071b050319020c030703062c07210b0114060702060d05061908030915040e 72
    0x14030508902c003181b0036a24100c00700344201c401c0e95011100140020780190001d07e41c03e02e0840a0001c56000c2c05684814a40b01e60202c0c0ca07142d03006400362030b41c100220803c00312407000c10502215040c40c3d006201510303e569400b075981d0540c1e00005007419290b01c01012a680c4402c0c0c416103e901e0401071100760759403814050a001a24041070039280500c60780400d031011705075907020300004001001d034603001c2815500c480c211000f41103441000b800001c0284405190301040d10300f1405903010710b90310350340310b40ea1001c1e43c0c0f101d8101c1400d54100d8100c42d4116940030541408481c0c008002003820b60004c1820109400c0000c1c40c03010000c81080454861980000c41500751120340d107480018082c0f1441004a0f200da24000600c1076400b20014406401c036194044040034000d024213003403019540c009803190f040009202007507075a8008000726031804001240c1c00702d45400750f000751103051096450b21f034486c0c051402e01440c200b0703002101d01c0308810121001859800c485810908208 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 203840728 1250 203839478 203839511
    0x307030203180402120601120e2b050406020d03090c080a0b0a0c0207080a02090603120a110115051f180902070b160807110a060504030305091b0f0d1407030506011d0601090b031009 79
    0x4801120820903a5500080b841cbc003031000c0350300362003130390300101110781c2540002c401030706013200111a120310049000503078410030840404c03000e2103800b4040c5c2030718048500d10101d0f1a4514501c045501508040000003404a2074055854050f00c640c5d01c0c90707440e1000b2a29282c50501d83c0c0502150000d48001c0c601ea1280911400f060311400a000c110403d40740003914244500070981c1c005485190080d1031000c0c4441d0b1984485207052000861248601501208495601a07407a203900042e50780d0412250756801d45c0d00c40d1a014101c007041c24000c01c000d005603c010700c420280300c40034481441c4040c1c200301090003203501c075605000d41e1400c2c0c0b40c01400752109462000d40c03403203041a0360090580c1243c0259211001070090300300d070381d443e0382040010b40301c050003510210b0200484880e090018000c26000e03500401c001c00d46940342c003018506081e000000e20111414070000c0c80138036a4012048021202800c0a0305e07207a803a86180c07250f8140850f4010f112481c40c000145920b08440c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 203841978 1250 203840728 203840773
    0x30307021f0f14120702010b040e1501080303010b03040f110603071715060a18030f0c080d0305041101051b06010603061a1e0705030c0307030203180402120601120e 72
    0x140e544060300c1003036000090b101e80003950340f440007444007448034400705818900d80c10750160140c4004604032806201150494503d11048140f940103950a4541d546440080e14014103000004500d1585011030400c0303103010161000703040c088502e61002c1030040c03070100c842c151040140103550307908041a001d40702ca50090840821038030500c00152114001c00c3c20803200d0340000e00810700d8030503220002ca40c0059440220700054201d8080400840e40c00c68551b84020320501d80d11180e10b05086400346810340065011003058248000c0000280b416001400d80c14001e0804549544403191410328207044105819202d10a1000004d84544e040c0c0040e022102968920b08220804030040310f1940b04000087c42d203d400001100102c84c0f12034000c0c00442e024a082d80e041442e40006a41954000c00d000c1d0300682c07020030740300d0300380040450b140104141150304600d0462101545036040c01d000708190705101c210030600e440400305402405100058405440b684105254200c0c1100c00d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 203843228 1250 203841978 203842039
    0x180618060c020a0810021209150f060307030b0a0203100503030f16020d0f05070512030909131a160206010909020d02040f0f0905061501080402030703121404090e0c150a030b03030702 80
    0x714000886d072382070000300d1301004d400f5000355680000e035242440c41040e800c0141041d0b80600c07642e400000421400e600c8a4026645110056500c2c00d181040c6d81403618141c005c80d109820402c503800e0342c500d840d0100c1d81040d07483c01590a40c04024000100895407101000c1e083d1a00a074140c0204100401d004060342c074203c422140007080e24540503540e00440f1410b50f0020300800215043d280120f29030a840e6110700b124024041250a113081c0d00b407400c3d43e00e000f140000304007203004d90360184409405052010030400c640502c03900010f943c51444d40c00640035550720000e017520042c1940100509031018031052000100a00d089544c078141155900e403644a48c81d03e1031030540c82115070070301480d0000c0003002000d0664461010310008080d110080c0003180e01881e8001c12110040c0c0014806018002800010315180c50702344020081640c2c031404d114411000000e170014142d400040c414a8002803120b0a030700030a18501c903021020b540180c0c1d10b8250450a2541d1110140204 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 203844478 1250 203843228 203843257
    0xf131e09081c020f040905040f1208010602010b1f20070b09030c0f0603010e19090f02010e0301060806011a0c01050907051206040503070303020901170403180618060c020a081002 78
    0x2034180c0c074000c80c020a0084c2ca0059801c100400104030030b0340110741c00c00d0007201c003d080d2412603a03030700e448491100030f6500811a61001006203d4081c410440d5515055035054880004c804200160032107010741c1905024428000c51810900060b0144c000c1010404440b2050f882d0740030a45103400c41c1606510a03c41c003c0c10b00c5a40c205000c070b00881c004064019070941e400c100c1c5002c0090002004000341c0704203008071034091492802044801401204580042c070428000140710a5189400030300030b0381804400c100c1282d001440504407034081c03104800024145484a205100e010408a42c070360804003800000c3c100401d458084586c115056028611804403190710b03260211800b0b003858000b4041d150210b070180d00101510501490080c81c80307091003000601861080d101940012400124a0890411505020090a01800d242504107030016000d542c0d11058000c1400b04943c4186010454407041c2d100070292910000340c1c0d64601980d0301c11402900700410030702000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 203845728 1250 203844478 203844517
    0xc060201061e030c0e09192303030402030c01140c0109060b0f032802040204031b0e0702030721051e090f0a080a14101404060b0f131e0908 61
    0x4919840d420340c03c5960000d0107041042c5803ea00001201c0010700c0200640a1134185e4076942c55042c414a80780ca214140c090b5030491031018851f0241c051400d0302c5c1c010b5100304244405030750300041c20410324000346460009180c10001071140d900510424429540c2066442c408026440d00010000701e0241c8076040811401800c00d5503030503100c0e00d42d102440d00286120304003e02c032031034114681e0003d00301511f066660f0303440c0703900500d081a80c0c2007422009401480003000c000c0703800c0c0c6c01540c244015400e01e80551140d8a45218610b149108002ea400344040074900a030151201c641040c030310344020b4640e080d0800d00c0c5500c80c03d1014456684603411841c540b82c0440100c0c1521420f1004040d20139940d0359180f030440140701c907003000f4800c004c500300f070003d0180120706411102240c102d03c90f05062038200142c80760851400c0c800d8400700340d002e0054944004640e41c42c88206000315001041c0c2d09400b540700e10600c4e44d000040d0600501c4820702200000030070300540c1c4840c0ba040d01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 203846978 1250 203845728 203845769
    0x623090c030103120e1507030314070e0a0506030415091a060301050403080f1b0a020a020a0902041d0a181208090705060904020703020102091905090702010c020c010c06090c06020106 80
    0x40d8030003408000d12142c60300b6030301640740e84506102d101c04403014010382900100002c442c246600b10b072504174000303030725500420000c0070064107040d000b102d5801c10802500e0308800241060f07059001c1d40e4040d40000c0000b80c10721914004c02c0301040c0c21003404102c1d90655003401c1201001400240c580d624416002c90343c0307800c0c1441054032603505656078071131a407282c1c03c840c8459a00a850065014000c9400321003000c4540010410640b464000300b00c10b04461060018400c15503101d0404184140700412010941507008020801e070f05207001103540e500100ca000422861000211410b0801102d208001400040311004400c5483d003c9a954506440b42c2e036076007440c0140c9421610030b1040b10000d060907009401003500c42e0001605002040b40840c01c54000d159411b900200381090402c11802d04040c42d42d0003c40303070b01c02800744108001d40a0760703482070040c5450400090008a005020700c1c1c0e40503c0d04c0960005080f1a5180ea40c20024043e2019005404000e090394145600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 203848228 1250 203846978 203847001
    0x9020a0816020615060d1a0102010b06040e040b1008070f03060506060c1c050c0f031e0a0504050105070204060306050f0402010f03060608010504021e040b040e01122004062309 77
    0x2481c0320342c1d401040540d86020002641d41da8600e9480d4004405001407540314050f4007402502c00216155003807121101000207084d02c03000014540154401c00042c04003410480913164460380004402c2825169004480d203007000365808040c65015111011604003405000402203c0c0130b43ea050000c0c2c0c480d0700c200000c84c407034240d082c289035200684c0c8c800790000014002002c0522030400a04014883c180507041c0450600b502170302d07410014045400896451600032991241d42110307080405c05d4a0281c1030b40b245006140c1480b10104100d0215695500302e507020759401101800203060000a0f55402d070010303103049003c592002c1101013910321a228075030450b42603075601c05059180009100003075002c8010b00244204400280030416158001403004201100b400c0c0d65803450118010088a01a041414440d8410074480c0c089100781000f2041e010004032601c00c28130344000098010315090380040e809003620f040d403256120300705a2109500d1416141c0122541c0d44a14861 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 203849478 1250 203848228 203848261
    0x90c0a0f090605090610140903030a02070e25080a0b060a0305040308091c1404031211101401090b180703060302040b04020c1e070e0f0103030e0a061209170409020a08 73
    0x260010683c85041141c00d120b20324601400d00c00b1f418291410302c000000ca400c5a100951a00151b40801c10030880020090421580860040407854010380352000c0c480b0203004400c5d02508000043d00480d9400300e160780104210f0740010f00f51a80d4610b120b40c040c015200454090b40486d100000140032220b0201d0090b8160312030811214015800c428103840340182400d40b100c180009000100000703442c200c22501c1d0b44126202c481268101c280020b15080100c02c0c41603003a030030814010300101809442a0548040203008500c0f205d1010200311131070304010b6144031142040092040b902c0e0507a00000c141c0b030007564144842c0d100359007030100b079100b0042c0c1d00901c2e9100f00040f080404007015038807005074484043d42e10381c954901494401b84000d5402c08401c0d030074280108101a00802504411030058075131000140c500364001e0041e401010134000056265030540042000011500100507170f64020141c540d5110392804000750003040c5490041074803180440c1c1140c1e000d030080c6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 203850728 1250 203849478 203849491
    0x40303090e1303020709021b0d020f1e0c010804020103020c01060b090112051326040e061825050d050a020406020c010206151c060507020a02010f26090c0a0f09060509 73
    0x20308030b461400020030000e600c032040740001c5031492181aa072304003081c40046001c090a038003c110500c1243c088030b0500744418818012841c01c082495001c030301c007184040c4680800d0030400740b1640d6030700058000e84161000010107501e00344011034410b0b40540a05103070f4900f80c0c5c40c0c9081158816841e0100c0d48159100200e04c007a400c0420b0014034001c7c8103042185c40380310385410b408400314101403d60056040481e0800c1034000300b10307a50604106c540d1300d94900c1010300e10542004008004d106240c40c05217025603104600100c40c07540603508a44a03c184040300704802d00c2c00742c40041c000d40003402040014092408210f01070740c40042e4090250511900807041c4c401034100b04043d0001c48010030341000c611110030004661140b00b0030384661125006080840b00900c0014010360413a450b09041c44040b00e038029009000c10395101c4a098680c56680c15521609915494201001e022951000840c080412224940c2500d00c0480ea40000144145a11385040014012040721003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 203851978 1250 203850728 203850733
    0x80712030210050c13080a030311030601080a090809030f06010f1d01150309080a0e12120a030510030f050d030506041b0c0f0618031d0a050909030f040303090e130302 73
    0x1501e0002c801544402d81000380007082d6440c100e071070510024000f4099100b103000d500280861418035800d405118a411070b0441068070b58038010001801020004e0f0080c000c0070381d504070107020403903050212020f04000401f1541000342900c0740036541e01c42406044241e0b21071000006080c0000d02d024132034400c06a8000c00941e0a00000e04050060010340c03508040e00c401c1030102040520000b071241b100c0f940e84003944040c9800510040b880310b601400c1c1607a03c00000c4007154082c082c142c1e50001c060340f8001c210782d19150000090b41400341c0001c0d203102d104404200030008005910b101c0100140c506002982e6010204000c0b15802d04181446802a20313041009504c01c0c0c2c0b540203481e1041e40100c3c01440700da01c0c0e07081184e510001c1034004a450342090414980c00074071410f040030314014000e40c083c642d98007095081400384900f500503000c040100c0e45d13800c07042c820340d01c0c40c1001c1c1e0380064903540d072070400a108000504c44d60b02111002404a126840b11801c412800e6805800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 203853228 1250 203851978 203851993
    0x1205071107121b03120c030203071704170c0306010b0913020c031b06070504090c120c050918040f02040b0604030b070f0f020c0108041101020c060415030c08040f03080c090904030305010807120302 86
    0x101514005606c0e001182140000c1006900180c21000c840a0f041100540c041d00d4a040c08100d09518021000c8461385500050403203560b81e500142c81c41c19181e25100072038440f1341c0305009c0bc1022990392400b440190020803000b44122002001d400c0801d0a9107140c01da5040110340382c0e0311400180d9200001510802003404403c1940d00800d005051a140c4141c0c0740381c0568101c02101d800b510030000240c8009103904552420041e0021608030f8001c00c80b40a0505a40780c1c050034074034080090007140c07100b20740c090390342c1c0340803d80d00116040f040000e407916260b04001c0c044d0315407014a00c0465010a6030140d0710344006111903c0e000181c40d601500c0e00e890301c44901c044003071700f8414114404c0728041c80b4107440741e80151004000d0380202801041a900000d425030394606101c00408c00c503c0100300c00714080c40100c40265405081074840345d01d602d040203a85115034001c2940180e440d005010070540d2592225048401d9031043c0c442c40344d2504c00d00d4148402c4481d024006a20064 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 203854478 1250 203853228 203853263
    0x90313150f0e0d0609052a030303061207030516090609020304050604020108040212070b0301080105010806090a15090804030f0b0c03151507020a0b03010f08030a1205071107121b03 79
    0x16403002d40007000610003048242c561340d0b030605803003040c40c08403001d03000410b160303c203c600f40441075861504120130004011100d0007090740d80c000200f1903071140407550b011403004541408808051b5400106807520302002c1445812806001e1264944407071902d940040c0001140c400c0d00d01440d0300102602c0b00340c607079400440d185840500241d03404000400030540300c1908018450041460064040d01e96141003c0f090071076a05074000082070300300e00c04101c44001c0c08160b0585003644500411030b21100602030b1002410b000100402100001070044284610881c0f07103482640308031000344465407001d04000980c0800d40e140e00050705020808001844c0902003908145025500282051100e400085040300079500001e1f801c03800000600c01101410328100180c079085006519241d1060802002d07010f00342d1360711010540d030708040303070b101c0344511001c450010140702200e0500c2d860354240c050140c865441111805025101c02c081014903c1060080342d41048040c0030706841c82 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 203855728 1250 203854478 203854487
    0x615010c061104120c0e0603030406050703032919051e030109050a0c050306010f030201050a030c02010b0d0605060f0d0f060209011b0309050907023403020603090313150f 75
    0x141021078800352141d003020b070218001c0000d403000300340302440c1e5600c003461814904001280f64114081101114080003140c0c0c80c000201c9040b11291710f00b0b20350f03690b901e040c101c00411000585400740f034182c940340103680d07800101d4a22964411140011507649107526200c0c2d1400511031560450104001d078107201c01801e010107402c100240001c90000d240d9681c550400809910460746501000000d005600b4100b01d200d002d0102080c1ca00c06a41c1548c001038a03500400190340c00b0103403a500c0509056200390018100c282d0054104103001d9410714001e00a480c08a070028007504182055803140e2405104140b4140d420040d440580c9100761a00b0300170358000d0710b0300d50600c0701206080c080c40940442c0ba40000e03019540d0503003002e041074200000700b01e000c0c02a4046510403040301c02001c80219411380c1c66251014031100d02052030004880801d20b591000c1c0d0711507008010040b03441c00110040000303d80c00221480e800303803100130400600069000f200001440b000b03160f400d20740074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 203856978 1250 203855728 203855747
    0x4170903070515090315160512040f03090314100b010504050a090b031533060904090c08010f050604060512100209040f05010909030f030606021203060a080303070c030e03061501 78
    0x6490f61031802c010318021070302d80f0b0750000442c9420340c080c0c1e040014000c3e10b491000c0403114180f81141ca0644440c45140c14030902900c0034142e014214819420940903190400096510030349181035041080e4075143c4800028010b0121a420400031181c2507100e401100c1c00d48400500b50440340c0c2c10028090000c2c100720b03031204d0301031040c0c51491040c2203a40b0800c0d40314800c60b0491175052008401c0c1c900d10310510008015807480300814074071669541710143c50f2210780c15500040c5411050030300f8800f0100030b030b200d01900d519101c1c01c203100400d02d8014a1142a05036420702059607120240062081120a000f14607000440d6400303c2075015001040603140042000c80d5040c00d548050003110801c0e070092001d29a42e079585001c054000e8548200748265003010040c1d14984440070b902d1304100101418201c600000290250395030342c1c100700c00381251000f103944130f14103008040d0140c0340d0009c040e00420740c0d00c0e07100c1130306180000d100b0344600074100c0800e05100e61a801074559192 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 203858228 1250 203856978 203857009
    0x1602120304053c03040e1906170304050a1a120901021e04150305100501050901021f060f090207080909092b0e0d020f1c06060e041709030705 62
    0x250280c4a060712803107203801007240c45401c00b040240910024011400040b0745a50443c0e8101340b108014510502c0201d41e40207002c5406407605001140c4084020003142d0001b05400c0d4401c000f85081c028000054001d0b00c1088d103410040f01d0b03d03045910603240c403907130480f140b45c4810010460000751174400f00350018003c0c00098204110031b4031540700741081ca202030380d814001080030441c2100b516510030310030305682420441c3c0d040081026841003e00d010300c0c0c3c1403180c00114102c160744200300302e0300d61061407080904428529413031800a0103d61040700500e1141d5103001c2101511842207c1545912005080c81c1c808140c0500c80c40c80d0001b0070412044c01805907000000e00c8000381c031504454400030046100f40d96200203403c041c1c58160850158403149128001a1039244214060110032214484180c5079a9284c012000c00e040c1c005042c58249072000800704254000e65000d00d01c100304e4103100b00358500c482540740c007270350f01c0041c2d156014032010401c0d400c1c03154416580c000f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 203859478 1250 203858228 203858233
    0xe1207060c110a030c0303050c07020a090e0304091806060501050a0e190e15121902041107050304060206040203060a05072007080708030c070e07020303040b1315090308160212030405 80
    0x40c0402c190401241d82c1064002c100030900d100700f0140d1520400c1c0e8413000c0051198240701f000e8011070207100190141404450fa2548000c40c0c9a0003001518000c2c140c8040520010803510490110f0740c040d04406c4914905003000815550702401c1613900c3d49801c1d54851658004440c104811038080030b4a00d01b04410000010803022102c00807035200b80032203420981c080d1340080511403000c54810800702ca0707400c0400140030215101f07c003080c0d056011074000c51709100c40c0d036007005a446001c170024290300c80002e0008409402250701d910550080303040d031321103a407450403507002d0321411540b1600191900820600054164214140c41d0a0075000c03251043e4079400d0b01480c0841e41d40080e0354581c804a29400c00c40c904000e400b014148511408501c0d003491030000c0e550380000342c0028046204000083ca581000f01c08003015550044095012103060300610001450102804c0c2d0024806000046080801e14041006100c59900600402d00849a40c441c29000901b0840b07050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 203860728 1250 203859478 203859497
    0x30c0603010e1f0b03070507170a0f03020c0708010608070801050105011b06020a0201330f06080721050106090612050c16080c01051501172a1303060605040e1207060c 73
    0x60604e44c0914401c10042d242c150380c03440c20742410101e10506019541b10709030304110390712100d60702500b0800d16000b13904016880301080d00c8528101b420b0f43e003041440390300e4100b00142039407002601070304540162008000690b242c000450f100e4000b4840005420584581c3e000040c0180d40205450307030301480001450b03c919404c40741c85a0180341c01d548d0034482605801e403000714843c0302400505c6a44800071089150000207050b0304801801d480510040c030505061130f0800741410040c600b0300440170081903842d404090180006405428001a00c1c0010b4100388a2203100740783c09800648407043c07c00070804010070a28000400440e0600c0060001c142c44070800d000d00b0b40120030054141c00044001c0000402c40398160342c13104c54981c4600d0500c4403010b0503003072030840140c510705209042c4080d41c0c4407a50358030506c030b0001c070f00000014000060000550000b02580d504032400c0c0440c40c10010065540e10702c0504051180314104606000200075510500340c0d52183d00304140e00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 203861978 1250 203860728 203860739
    0x307030c02031e030c0c0d0f110a0308030a050a0c030c02060114040e0f060609220b1b0a030b030c04020408070e0405010b0a03050d030516050324030a03030b030c0603010e1f 76
    0x4044a90f2007032483c2e600108122840c004207000d01c0000407000c1d19015005e0019445520620079420009005c40c4028042ea00442c1c170351540107c05075400c00545a503e0a18500200081104030341c102140d62a08900c0760704107200707018031b90b4603400c0e035030007485540d09007050308c035510028005566005682da50612400c500901c94a0401141d54024004500d0040180424103030014601c10652040103266078883c040012080341c1039030081000c1449540d400b043d61400010100c0c1007800202c080b0f1104412503064200c0d05d582007083d425604600d1031001403106038001d0780200100354201d41e030700b800b44c40103405605501500540010030884843e20110300ba84900350410b0752140c001206202d00503405015403034021104082c1109541031717101000345240401b4104840d07000c1e240000c02d80c1d90202030030000603003a0040c2943e9800c5942d1030080c00800741804030704d00900902c26654210700c0d000c000e880c1214150280740c0000e54454401c0300780b0440c80d001002c18403d01840105a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 203863228 1250 203861978 203862013
    0x903070b0a0f110408060703060807171501080604050c100f031512080325050702060903070e0c0d1b020a02012303070e0f030105010b09040c020a080d0203040b090f0307030c0203 78
    0x3140d50383c90107981d0750030690b00c0c5003810801400d031000d0604042c02001740e0070700003a21508942c4103000840c841481a20418100103040c41011400300c290390001c5401c2401007452400380b0310410480c1d41c402186018480503110a2500328045012100c0c10b011a50007078011004c241c0c202c1c050121801c0c1c0b280224541d440f0754035400d031a00130000c1b08201c03130f017454031005049005081f43d1251501e10b00c030000074403c1c840c01c1e1000b4000c0070040744031000e44d1010400f6001604516002c1030030303440d05019180090300f001c2400d010b0642003003440101c24a0103401416901010740c05030251200503001540c0003001070b680204c0c5540c280d03000b2940c00c0190301c0034500070201541e8000b400c00698080000407551030f5802071107645080010040101448e080f504c9082040d0703008218020781150580c10b089043c8005054010000b44007500c80740994010740c4100c0c410b2210314104d0b110000c5c802d0b91441e03c0c0c180c166041e84200000f402190103002980411f600c0101200c501005d04840c3c400c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 203864478 1250 203863228 203863241
    0x6110f0a080909010b0708040b09010309020a090507030b0a05031504170f1309020313170c0106090b090112172b09030e010e01050913060509070f080f0903070b0a0f 72
    0x7105000042034401d05840d254544034010942d080b610f81c28101540c982940d00c0c4228495400d5107240090401d115900076045100f000390000d00300c804865450402c2e20140400315000c0c0002481d10000350014170301080c0200035581c001e8000c204440e0921050710440201400079100c0d0b0074440d014280880220000780f400400a0120b9034580c011403800e28801da60542041d143c6500500401008559502114400710342260b641400c2111220042045104000d0354030515401c010020504e0000303900104e00c1c44106a6450040d40e90b121540501103001c42001002d914800c540f214405e0702d0207000e400c2013005d07440e02d000443ca10341b000050f01c0170300c0c2d07000c1c0400eaa00d8043c00410301d5080f250740d080c02042801e01000071160704000030b0451060310441c1d841154200c4501c001010b050381300c00054440540410303828242003401034607018101c14003000042041000031000056441440d004504041c001d41c14503556a487d240d0802005091194069441020b009410b81d0b600691 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 203865728 1250 203864478 203864483
    0x9100e06280504152a0b040b060d03020a0b060f040c1e0509030a1407030f08040f080c0105190c05030310090f1a0d03020726190b0106110f0a 62
    0x203107002010300e045001c045500e01c0c0440c1840800c0c0020800580c41000480f80c04c04180390250409039050319401078503505045d010000c1046074000000c005403041d400e40a40d019589410107941c52408100a28003413480050058201c080103000240f900c452242d0170590050071404c12143d004041411554920f48143c005410800b40c0514400001815140c481691610514000c41c00020030382d1005a0900103250000074030068400c400240700f50300107140e00003480a01440a400e0222a0740c01c41e001d0a003078002c0081000880120008109000384010786071142022b40101c18404401c207071140e41c1090040900041c400280188004d600c1441ea404070115003a0411318102e007243e10b8071650b01c2120f441c0082008001c3c001c00c914280c4a0307011913307020b1607035444c68204e0405010b90300005100d40145421250f041c0208050841c40c400c034021207200180c0f59000892961091501500e001352280040c8940d511541c0a00d210802131012501c4501d80040c09500d170080c8580d06 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 203866978 1250 203865728 203865757
    0x60812031504050105090c0f0c070609050a24030504020607020d1b0504090f060c02150705091e0d08030a18110901060c0c140111010f0605012309100e06 67
    0x81050807810000400e006031401e440410980d8141008070f120307060040c0c568208104086941d13140480520708980010145905a03400555a200042c040794840c1c02014400d40b0441700202d942a01901421041c41124540359010104050207030003c02e0050016038100000b042120b015171540801403a003280b180020000410400780a101d05288503000948124140400140402c42600352540203a412a100041d4030181c040300717038a4444060011440707410000c04001c803181c0c004004c3c120799074042d2040658120038031081424a01c0444259500031304d021034500104491801955026140700c00006451060002c0ea040004800000b2200d4070204c4000c8a0642401903070b603801420103003003e84d20602c00d03541d01e9800344520701074000341000795100140c80c2ea02c6079240954842d01c40707008125140f0010b500801a251030b00401f408a07164200c1c0c60f0310510381e203080c0b504100d1b111034814180782400d0200100d640b0f0720162001045108142c040035562404014202005c66111 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 203868228 1250 203866978 203866981
    0x140601061e020703111807050a1706011d121204050a120b130501110304300507030503100e090303040c0902070816150501091406060703051c06081203 66
    0x3002816400c0d40e001c0d0240748032511541c4101c0310340000d42c82059075841050390050b001c450002c110103805003401c107030141c0d81d4070041c045066048001010910041e54910904005114415041d02000c0d10140d0000380038400717140c801120900d0360011020300810704101416442c0c0c10310328001100c1c0b140e190321000010104a545803405191005002141851344180c0d000e448144c4030701d030002d180d483c480b40059043c00c101301c030039402440e102a10040107904c03401d050825110780850120074440c04000200d050550f0507c0c4c800313074840c119031380c1e446c946040c400f550100c0c0e4980005e000d80080300060a00820161140c0300c000c0c1c415020b00d00155202c0c41c00f030500e2000e035a660b6002c041d0781d07841000480e0200d01002e04603640d08201c065070258144092a10369024503c1c4040c0041c4c50b80780c070b4004214010150081102003205211000311500c420081140c00e201d41900100454020000c401a010548113140c0409800301d000103801030b41c2d100580d040c50610402104001030020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 203869478 1250 203868228 203868239
    0xa09080a020f0106080a0f0825030309060c08010e1609050a0b0a18050603040b060d060c0f091d04030f11150720060a11130e010509010b0a0203030f0403030603140601 73
    0x100304002060f142009056080b032588070f114400035402400fa1202c1c03000260860b802504804904102710132440c001040140c0d070038004d00424035500110b4a80707042286082c6068447da6649040e030301100c006507000d07202c062510052400c010b42c60350500800d002c00141030b0340e9940d400780041000030003840e9940701d90b0030003c2182c1121900c03a140c0e1100c050052101e511440140d0368403e0340f00003103010365114440001c0c064445ca26004100608014441d0442c903441000d5602c0c01c0025202d0750f03001910340f132030300b510101140d503046a440036100004000c00d124802c1d070181c55800381400901c0070a140002c0f400c0c50301440e21945d011289400f4442602d50003036100100c907034031048003000d001504403103a0b1686c4002d081d122509071103181d2200300140007421965052a200403604132650346814010b4022000d108081c0318045c81400000e040041d1403c84613480c0c1c255010303624681c0e645508541011024109a040581c2c80748080005030154801c0795002e08014000c021a41c0b425 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 203870728 1250 203869478 203869481
    0x303080705040e0a09140322060201020f030604090f020a091b0503090307060f150f05090c030903070311030904050a0b030d021c05092403150d030f080a09080a020f01 73
    0x3900500c20401e040104000300040001c00940020321340c1004a809a120b06005c1c4c0442046101018140000580010358441180240b4844d081040714842510303a2000103a080707002d0504d0b4415041e0042002980074a0316070b00c48081c0c10b00ca4000210010f0340340c0c000c5186103904d6001401030341c1e901c100c09450314600e0f10039402c449025140041c03861400d91010b03034407406043c200070081e03034555140c00c602001581000d040d20051002411009584070700000c07001110313210b81c90141c0303203c5000c00c1407200f0300b4007140d01c5102210000d5103400300740d40d0708550800f14070b082e054203400b040c409480c03036549a004850091240c132802240e4090044101810107003030803403060941d0b112400500882107868004503840025040458441c202d20001c101580c140c540780e00d03c0c00c20021842c15154456001070340c01041c0e404a4000918242802d000080b40804400b402003105542d400280500c1a5020396201e0090b02000c0b81c1c0c1c080680d13840045e50800c1c0a5040540c110b4510058449400d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 203871978 1250 203870728 203870731
    0x50123090c0a030f200411040603111602060c070b07080c011b081603020d02070803010f0611030d090f050a051e071503020304030203040e13020a0504090308010b0d090203070b04030308 81
    0x1101c84868643c556070f00d6003000c46140340b0040c200e2400740f01304150222011072035110060003802c00d010590003440d04401603846800b540c8046890464000070851040c0c0607250040e90180b0b19126541c0903408119880e009048903502c1031140b100e02241c03a001002c050071115204072522074885183c40e61280c2500e08100d8200c0c40c0075080d14902e02d200d940b0245140e000241030310f844207820f800031303812406440380c00d281c0c81b0380e1800081c2140402501c1d100950407270700c207490740c0b54907261a9082120158140c0c0c1001d1025481444008542d280e240e0000200d42c4c0b00320300b10914230703e840d5601814034040304401da4403a00071a025280d40d404505d42c04004012000240401030304100b224035211006002c0502019070100000d82058000c1048070042c01c0d0f100070f204070a142c0030301c580600d407075541000c0b4003e0b8041500000e60f401c05004519009926440b4071800b6030820148055a0f00300d2480003980d503850303188502c0540c400340000000782c6070b100341a642e21815420f000e0301c072850 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 203873228 1250 203871978 203872003
    0x90515030a030e100c020d080403061103160e040b0d05060114120307060b03210406021e0d2106030b090f0a03021f020f0a020607121803030905012309 66
    0x80500010343e02642c0c0c0007003a4001c4401402010480e41e00320f504e203144210003908011100c0685042c01002e00103001103e21820040c0b140c00e83d0700d2100315a900041e100340c40841c0204000e1070241d80036020703d09400201400c001004e18200e4001446001e6804050b83c658111070018849004a001082030001c4250392030f00500c8030800301d4942e64460741300701410716943e4007030750070a6170340c10b01c0703030111803411252004403001c1c980103041859845442484054814040c0c0010300040040306460240346c05170250603055916502914100d140381c85403556452084046805001e0383d1103941d0286001c0c0c81811490301d00256041d18019007030b00003042c02d900a6441c80b000982c001a003a90b020350004651a6400c040740880c00640100030080303208440105040d080075a002139801e200348403650311820b00000c6061070204660085120102c102010104100031030b00030741210143d144a0710000a400c003115005c00700c05025020f101604124400500c401900c040045800600 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 203874478 1250 203873228 203873233
    0x2304080913060501050715020d05163e0a15021e07170c0109052e061a13050a0801060303110f06060d06020d061418061003110c0709051503 61
    0x43c01e12002030030034081c600006003041b10700d0141545414041d0107981400c10916824480e50074560038200c49660001407260000d0800d6048461440c03034886440c040e128444580d91780702042506060703200d9960040d5800e54406c0041100000d1341d4200f204414483c0400016100c20a030900c8000031410001c1345031900b001400a4400b24410356100f034034024000b40c0d4a59200c050148175405446084001380c66030080403881c00c200120494595001c00c1c407450820010803200300c41104403045c074001d480c988155403419401504148006240d45480c03080e24480650f030301e000183c0070700c1843c1c2011000b651a85400c02c00c164101d1031915001d0508030281104101c00b0448a503501401800ba600c034851840045051100d81d81c115440e0030043d90081c001240c890811291810368074428034000c90010388280045c0b400404031070b02605008001c81d8512429070400c030040c00c40118550344c1e081d01000401070110301000604000d104042010480786880680d0440584989a00500a4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 203875728 1250 203874478 203874491
    0x4121e09080f010908040902090310020414100305072a06020408030c0105180d08040606231306050108151f0c020102190206090904060e070b071e02060d2304080913 72
    0xf4581000b86c90a8902e150001a00e40c154240041d180050210318214414400200419041d44540b90340041c10000d80b46140d200303100c00b104800300c03002240c1c030320001600c14581c48442c411155265642c410584107442c0700c000306880b240d049a0180e07100c52690752002403600700744a405e01500e5800070507000858910f2000c3c924454a0301070b03800c400f604208a4034002020001c25601c034101070714800001f581c03000c0d031107271416004400103000c480c49a08041c14030111035945024481c141c400603900c1e500a40c8a40c1c801e0308041c12030f1004160b00000100081d9401034500100113076609096840407103000e00c42c0006410301c840303034801c0049281d180040c00050703100c000c100c501510090315518244e43e6241017801c010303e1011010001c0c1e0042500020f91801c1c010f014100e10b0f4029600d8680603c480e20f1150b490303403000356009400103824481c040c420180742c2d0000c0c170203801214984800d00c02c86815103c003284116400c80d880032020411034014100800c1c401501c1000380e0f4100f012 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 203876978 1250 203875728 203875733
    0x30f1103131401062105070b0310050f1807170109020304030e01050702030723010e04090b010308031302030d051b0706121e05070519020c0904121e09080f0109 70
    0x1210040d00003404400000c0d1007940b40400c01d5001c3c0c0c1c001c0c942d0a111105034002000f8880780344103c0441910b0702d00c42d00b98003180d11004c40c42141e004006002d0f00c2640f09280c0800c0c0000c3d081140a5103904c02c14074141c0c42c002c03880201c070031446030490784d542d11405000043c210b0f0420406800100c1564030500401001030341242444102c0da1003420300c1620303140785100103460803200d50414080e4000070003000907000c000c0c60700c50104800903210720a5080c6030005010855860321409080084104010008281b64030000d642108540982e18061034403500031924010400e8008400290006000d03099245d00020113144110103c0140480710f207850001015149030401146c44296505081161885007660b207a5007200f01201c00e0096282040d0080c0440d00324501036410010460788030f403489440444c664012560041820503107840f0368403880042042c40b10080288251101c80c1034500d45140642031500a05a44504a05041600c10f0382811400c0381511b0341d503814030400400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 203878228 1250 203876978 203877001
    0x10b03060f04050a2a1a0301050607080d05010e01170d211d0a02040c1121070203030714100606021002030717090705041808090d060605030d030f1103 66
    0xc0000d0582412003007034031a81802c0b424020548030082404040c0c03090121881018078806110348483c1d900803208907620400101c0d44804200d0b03140706c0c00010001486140b5102d4080c265160240040505044100050030212003003a0003542c00e100d20840100a06060080e00480252007000a0001501800d0002d00705159025044541d0205820410092001c69004482d141290351030713030100c2c0c10701010160b216200c030a000d030700903801c0c00307a001001801801d00500d030f803281d60010001e0006400c06e510420300900c0d00500521020420800960340820161401c40e0142c00c50401c03142068042c64a06140c0713031011485a801e1100410410303030003080401d0400466940582e8a58440404507a14200701c41810440f1036140c0c2402000d010000750841502c00c15a004c110784507402c0c1c4001c040f803510950040021b5001c0040c07134410306040d5034020307659210318004180e07540c0b80e900090500315001212400a40d0303990f002000071f0000e02400038200701e06580300c1e1650408045541 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 203879478 1250 203878228 203878231
    0x50306070c0812060111030d09020901060c150207020f12032701020c060306030109050703030216060825020f1002070c050603010503250302060d0e01150b16030c020a030c0e09010b0306 81
    0x25041c3d0090b0300141d407690207109210741c02805902076981d54410380400030020610800143d0140e000f40d4000304200303000c1d040702c0e10003d401c58652921521144414000703580010022608448841d0700440d240c0c64200e000c008801807480078684070b105040c00002d5686142c2c1c210030b80d401c0c80800c601c816903000318041144520076504183e80c2c1d503441022030301604440700001c006d4401d4110000505a01145801c0740400d091a0740aa196a8020480790701c0740581d540c010340e4409010180c44103003011100b45c9244200d00541c0d580d0ac8122405505000b000740d0b4401c041a0001034032420004a0001c01c00588021540303142194180800b00756903484100404003058031003404a00100704101410f0000c40d402094541d440d004880120050700e4072a5102c01c0369800c00e01c000200501e190006400c1d100c98000701804d00c5484805411081100f64043d000c0c000b10a03040c80168940540080140d4020624514a50304d0180048455800203040369903507498038445801954003c20700c00d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 203880728 1250 203879478 203879497
    0x1060306171b0d0f080f0325020c0d0201030f05070206010801060503030c1009020310090809040509060412080c0d020d06030506060d0305040308130e0f0414030903030409020d020f040609050306070c08 88
    0x20303001c15815113007001004d200140e01078440741001c18844840c618a00083d0311940c0624820215501015500040132019403603610268102d82040307011800c0001d440c001c800e005150100c0c5095140a8080c02c880c030503a01080160004801800030580c00d02441d4028402500210700c1d080421000303e4440010b9000e04144603181c101e4541556002c1100d40d4211001000403c401704280c544860240d0045103001d015509050015025060100b4103e01c60740c2c000c01e00880300315500c1400c03180203200810750b02e810725044c406a0b684081a101400061002641c005141c0b820360030306c580380ca507004110511800d440554040001d078001e0a8400302c0f54440700392912601c40000825210413550400010b010300c0c002080aa969200680c600032401945041d099a520b03840c015103038440d00b01c58541540c405c0008000048241c0d0042004030040c070703030041c141025400e44400c0ca501950102000603251107061009103410b21045170010141d01f88845000702c16500d00c40940200c2404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 203881978 1250 203880728 203880739
    0x120705032715090a05270c130f03062007110d0204240803040b07140c030d0207060216030f0f15020d020a020c030c0108011a04080601060306171b 64
    0xc1c00c61510710304600c001e0700301d0050085160401015001c0c00c5074010102191150f1400040000c041c107117003010701507240c0e412a91540b14400805e212032000c0001d031661300e00c480b04009102160400d044100c0c0a8601d08101c4008a0f295061074400d42d44c010900805110402065440b104d42190481c0d441503401246103420500402c002600d003ca0403001940060030a41d41101720f0840381c4080c041c0103580d222802146885400341503482c000e50140514001d000c00c00140411542e800000c0b41c03001702400c5551800e06400800d0500e03100d0440000580e0020383c041c0400b940600004141380b40c0c1c00003201b41036286841c0c001c1c07044611203010706102c99411500052000c5040101500e40540c0401d55070765440c64490f0000b9413207051180014040c0b1084403042d0302c0c0c081003504071044165101304940c0d081215030700c0c50403c06070f40d8440e19202044001840842400b007280200b5242d20000b40840c0f80400c140b40892490081d50000e400a824200f10b138601e00c1005540c541c000e588 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 203883228 1250 203881978 203882017
    0x10f090e0714090901150902030118060f18020403060c02010b010f0206130611120702070f06210b0a0905070203091002060402010815010e0301060b03070e15040b070f0b0f070212070503 81
    0x13000c6004100c0c0204d2020700811301c41d0b0215038081701341c009604a03544050f000144e00c0c0340340d1a0408aa42a0240d502c00f00c81c04481000880c031001905529008003e40c01850315599036901e40460700107080d91001b503511401d00201c25a04220f189003030481c0f5001402851400424070a0b404180003c003c0240c1c0d516100e10030490b01510646008201001c4040000d052450004c1d56501a0f48100c00c0c402d4010030b004103a651050405441c2c0b48501050008040001c1400c10051701d614005140c0001100100041e04202c5018003401914207402650341c0303082140c2400318041074905508150340c0108103100043c1d84c4140026401910a04400c4801401800482d0f220b01401d003100d6041d07003002c902107004c40301039004600030200364031024090b1080409106003c054841c05078074088081c003080080c042e03214001c05046200310880c1c04503600f25030341c14020160070703180e2040c5419605c04000d851501000309d0300e040650000214207000081c0e860955911a100c680414040c4420 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 203884478 1250 203883228 203883241
    0x6170c0f03070504080f0705210606040b030c0a03060b0a0501050306010e0909010e0a08030901050907030f0305030402130e10061e061d0a0305060703050c07151503050105010f090e071409 82
    0x3c0c00c0d80c000d4404e8100b9255440880c0f5580365460301c0c540a914072418810f065080b00c6160003004200500101021b08900c1c1e6802007004000c04e0a42000790f0107000d55443c540c00c9079660700c01900030314418640024049004070a0203140180740d00014113000c420000d01c083d0781c0c0c009501409140c4111a045440c0c2d807003884282c050701207000400c00c1440b5060506040102e080301561064030b144008101d141c1d0b500040799941c10240c40090038000b0304140c02408070b8843c0008607031090010300f43c000c2080340900c240c0115404040c0b07000994001d9280c0310090002409070714020302d20b502c922900a48202030495805506114010a00c000749681c1c0b0303401f0308041003034140c16000400800d11540d8030b05003262a6801101c00c0700010345070000040151102c1c4007903624080e0014600c105500302a550b420040c003280ca0706000f81e0041e100004005030702405080e0180511940201c0503a2419550200340c82010004100e1500800707800d0080032884007440d44104411141c0031031585448 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 203885728 1250 203884478 203884487
    0xf0816060507020102070312060605030c0310051e040507080c09040c02010603020319031701060804060216240b060f0a030506060d1401031203051504050601032406170c0f0307 77
    0x80090a003418981042182601075015180a034000c4d00c0d4001e504407924981401c031070180c060080858024404560348030303012400341d944403941c0e2486600303c0392958009840d0700c10380f40180b11550110207050340340d803c1034040c0319001821030420b02000e09151079500c0d068055810414000c560f10407004000302e1003504107000031500070741a203840301c0d18101c0d400e880c2c4143d40015000b241600304400f01041820544504031030f0b0780da07281c034240c1d16565260740103940099005420060032000910108134085903424143c4100c0400b1341e5403880b8044a5015035480080507482810306000040ca8812848100d030032070000b0307150000e0181c0d540000601240203100c100744101d440c0c13504d2400a21448902181030380d0258003050766505501d1005c40603a0000c482011041031040c000c0c445509064200301e07013207401410081501c00c07104901144184184898501070a46440308100340c42c1c02c044128011000e03495030400c1d514180b140000144200410748110030400000074142078401c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 203886978 1250 203885728 203885767
    0x1203390c1009150c051204060203042a080d030c0c1b0e040f0201020705120c0d0203100f020306130207050a080a03020909010303020f0609010501050a0608040c030c15090504090f08 79
    0x203800c0c04102d001c14900b89058401803080c940850a0720300421306490500442c295000d0740340c00d01c0700455540c1c9980d180300c080d41001d0000c8900300d485401c600811000484003c0c0b00c1d14000350000c6801340750248035464114400000d2060503c0c207602903a403a40e02243d0425201d41065a006003000070b500c00700001040383d405030700700d8034941d800d0004000c004901d0001e03e50007682201c24803a280c0c070802520b4683c106058025512410307802841c0e060428244003000e0009040e82e4098151540386000d4274404851014170b50b900200300401440c200030303100300d9201c5e886030450408085a80346a40c0d600c12480c00f402191010408460a91284d0102d661100e40905000100c8d607403480c0203551110b00200e1501c05000720b00005011840500c20141259402002e4204581c640301090b209040040d101303031200000480040042546100003070011b00e90040003610f804130b003d000802c082c140341c00c00d61045090686078008601103070358080005400c102841d590b15130101d04807030401034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 203888228 1250 203886978 203887003
    0x40b0c03042705010b030f01091a13090309080a0203060c13050a0e01030b061e0d0305160b0906090312010509280c090e04081b030c1203390c 62
    0x442c614454860040c0c2600c241c03480c84403941800f2613601c6481803845400200d401d800e42e40e120b54010030200a80f0b4012000d608841500381c0482c0700000040b43d1f4500c0450094103c803a2a60069410954483c507400000e040d201e0140856440e01e500180d107401d4050b2070720324003100108056103200c0c0000709000091000401040c46070f0b54401c00c00c1103030324003440203079451a9440d0000d102070502c00c040c410340d10008a04c1007404542901080120070541e5425001c101c0e00303220a581c1940404060400700e4014580d07082d0701c0c541800600d1400f240189940542e4106008525132917180e4484681914000c41c1d941035141d880c0035900c00108106046415140e0a400c0400c0841f1415440795070044c8182c0d4400d02419103d40c54040b001c0700644005040e50000c10850311140c03e10856000001d2150041c1d910384410030a003203140165944000101881c00030a00c04c264100c5141c1e0300c1d6007400013188040300f210341c0c1e103814012175514150711000040028100301501060014032031401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 203889478 1250 203888228 203888249
    0x3050703140304030c170307020c0411121003140a05030a0c150c0908060105030a0201051213020604271404151b020106140103020301030210030b0a0306050408030f0f060303040b0c0304 81
    0x74060800500c440c160131300c161018440c0002c5403170081000c0003180d101d5252500145008ac03030640520005241d445000c0f4401034081c8503c1311411040581c03203000e159a141424170840c1181450039290a00b0f808000c055400400d440700011030100a03584c0b406258200f44080324440c0c100002003803848c0c41c0c0740c91410703e00007144502c07a4103c1d034844241e48a480484407140e80302d1089c036589008224019000c035900340100016140c8441105a0000702d0791000d03218600c065001c141355401c1600315200e840e0310000f1035041901422900c82c0320001e01c450511160000220f10459a0f40c0980040e0407452140360302507802c03045800c0250000c144030301c0c1c51201100c0d844024000c0405004100c640742c85811240e25940c4203000b500e050b079400900c08403600800c1c04090300100580640c2940000c44042c00002042051044a02c1240a240083e0380c924003080804240b4a004040d103884800c0740c024041e99803030000a44040d2140004010381e1244246001451401554401113144 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 203890728 1250 203889478 203889481
    0x1a0a0207030f0305070b0f0910050903091002100b0a050a0608060312030901090b06060f0307050a03060f0b0a08090708030405010309060204210210110c0d0204150905010512010203040f030507031403 87
    0x56441300041c038401d4010082d0407001c0c1c07541800c0021511080d120100b0680c001118192034400640c000c580007503c5004884c40c280c400c602250341020722031382c40005a0441a5400c8190003c5d028100e45e2620454052020314100000a194400c060040c08108901080080c500f5102004140c00039150b100a0a44914094041c0307406005105000c6071401c6089001c03030702e281804c000741c40c40844a410714074103681e10454110340c0d9820505042d010103490362400184907141c1d1649402030f24280703c0c00c641d203500d03401010340000f02c00707440e1100b594441075041140fa0700100990301a9031007440d000c960103c003818424081d0203150040160382d91810314143c00a0401285034a403988240e4485c02c05285409040e036140707500040704000354002c6140f821083c90302d0f1000d4140d02e440113200003001c8401110341e4451203415082641015a598014000c1e4030f07100c1d03801401c1d0440c00d0005c0d455031030207565112066441d07c0006051010110701d4100701400785103a041010600e9148030740741d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 203891978 1250 203890728 203890733
    0xb0c09090a1d03120a09051002040f0e18061f0b040f090c1b030f031b0309150b0a050d0c0e090606040b010903031b0305090a08030c060f011a0a0207030f 67
    0x14250381003607000c02100b0002408406101200340c0345007130a401407107a07441e6644807241d0060400044202c800d80900c6191404a207418400f42001d017210444404040e814040da0340c41000e000341011841c1e4840e8020308080b41c40c002169684202e50001c010580e40d0035482140710070312550405003650501140c04150000e010642d1411510790360300a101100f01c44405980302003420501d0b0034035054694109001c2801001d0a003e46085403400103103c0009580320041404c00b810842c00180d00d5504c1d101c01d00842405c55410f150300d11000300005e48039803002404c5240c580c4030f8123015000f468848400c0c80b004110100081c8565410f255061800c8441c040d1110400c030703403540c455450201c01c4500355214003074010540b50f040d190701010b8481c0804042c500900c0d250300701e04122041041201c4e07501c405071520700030003501c0000c0d500c03610b5024525081400003801411405030880c0100181a00c43c42003011000d4048038840c0d64010150080f0b08015540e0006071030300500482d031f00e04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 203893228 1250 203891978 203891981
    0x7060e030d0603060e0607030209061623010c0816022e060e0103060608160504020d0609150302040f1a190803030103080301050405070e0619020c0a0b0417010e0a0b0c09090a 76
    0xc100710b0f0745c1a1146c540e01d01109074102d001d00751040d600080103101c00305032900380ba020440c106000e418401c50400001c000c811201c00219500351250351910300f00041242c01040090304240e01c4c102100405034841002540c0d42c0319400c04001841500c1c0e0110460b9810300a540700142c950282840856103d01c00e6111400c1d01703202c2200d195240100000d140f020124801d51504020100316500364a01010000650464400d41207001d90740e10b80041d00c040300d44644030020030503078250b4400c0c6141d4010071040b01d030401c003c09001b80c1070002c4409864510003415105000499200765880341300c4002f4858080c0c82e811074100c6103c000001700c288070165011390b04945003203409100c00c1c0c3da0f200040761003050108940340c1028041c031400c0d064003845c0d00320a01d85081b500c1201c00612120001499141095000c1c05818000140c1485503140d00548001ca41c80c0d650300034481d0501000080e65560030f00c81024001d160648041030b83c1a110b1011100300b0340b0b00403c1c40c0054101103203841c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 203894478 1250 203893228 203893241
    0x2060309070816060503070c02120d020601140105120711030705060a09060c0e03060403110c0a150e010906020c06030a110304030f020706090f0e04030203090303070b040b06090c07060e030d060306 86
    0x1805442584800030350f0040442e00b075803c1e10059074415045486516007580d15810180c012a400b07054100e42c2603141c08100682c0342405403960041207507524000e02000f407201e2001c0e0b55410040200242d606260140c0e134407d8100e0018580124503068401c41c4908600480c14002d00f68011041880240c4009403c0311454034000c3c0010003040008490503a0707030756070076103c080d003581000c0b00040c04240a0008080060440000e54200035606000214070001e160854000c0f0a40c105040d039480703500c10600706a140b000c1c240801c0160404002030743c0d0f220402c1c0070724480c2800000080c20703a0a5500f02c00310110301c1c522900d889041924019069136039171845200144203403900060054401e080020071074004020704045c1c681031201048008500500690551100304140241e0791000c10040c6803181c042c41081000d400d003480d0036040400c02611140c400c13070104052003440c100540c106c880b0310740e100c0400103075014040d050f2415806000501603005150a40020030303c0342c03a80040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 203895728 1250 203894478 203894489
    0xf0406080f01050409030f0e010210110706050c031902030402060409050117060a0c050f0702030c030610090b011d01031d19030810060f1d0904080702120a12030b0d0206030907 77
    0x14072190f81c0701c6003070104503200c0950103400601403a41e98040315000d6000c1c00c0d007502c41803054802c1546403244c410b007a200d0000400d114960001104828050300f40b244a030032102e040110791543c10080385901c0100c03094540200b650740d000002c14110b54807207086030000d210282003407100350780d280c80c500e08103d442c1151403407078068000040c2c0f003e034030740c4100c40031a05292140c82c01c1208942165002d0b400c100d000300c1e050310903181040b03055030301009094401c45044152502e80340c06e01c1209402e9030707540390169040c0601800890070540c801c80342c003030703020300d080c640062610a56084006a02520f000804d05401201e0071400a01d005440d881c10050007603e40070341603120b03954030480400321ba10880000a102040d400002481002d030410241c00d03100404000036140d00014518000a41d03003112500e000045110031402c052451500742c45481001c4c106144c080d485030500e02c0d041d96040010181c0c6c1c1c0c11041456560095482002a0054101500d92503c454010b6443c3e100d4010b1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 203896978 1250 203895728 203895751
    0x30a05070e090117120f03060109080606010503060111011b080a06050108040b0103020907050c03180109050105070b0606030c0c0a1b0b03010305100b04020c0a0b060915150a050f040608 81
    0x11030341030054891001240000d03003042626883c0c0900d8400d03a04070040e00f010359006050800100c03080d010f01610041003101103c9a980c00c0c020005802c07411030740c1c402d02641c2c02140800015a801605032503101c41c0030308040c511440520790176401840240a009810101e40c080c080945500032041c0384601248a000c100741a211130040d94041c4c01210020407540307030b040041c40182458107810f60000700d941000d90a00202d0b030410350840d00800052340100c515110000c0b0150380c010070f43c000030a400e0800030b29082c595190b03000031810090049000c0c00f0004040781c3c0ca48000300072203103150062015100400240d14001c1d188146151001503080030703200d80415003d2140045a04a9902500610020010342106070107000404411a4001c0e401d0098a200e943c7c1401500b1100d449025840258502042040703005c00000d0005d402030400d0406e091150b84030640c040c200c10501000d070940f43c15016400701c82922614107200000407020400080da0b5800c80c82190064450405 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 203898228 1250 203896978 203896981
    0x703030306080a0506180a050601060c031d281a21091009020a0f030605180d050a0507050304030c030804030c080a0c090507090b1b0c0a0503070302090c0409050705030a05 75
    0x10b10607901c9501410250241c0c02060215605443e0b4486042c04980e00c0fa043d180710709840c4c2c440030b082c0380090f80118045450400b10200705944140085084542d090142e034000b140035012400070751010800c0b5002c505004c1a0081a5204038201c500500c0d000840160140d03040f41180c0c59900449105000f601c0c8240700c0781800710750038603072921400d420001030207512140207000000c0c4c1800002681c02490380e103070200300821404150340195018810104ac02d045c120410019008595a000ca0f650001301290f10100d030b0000481d051460035151003610f4034000d0400500310b1180d80d00003800d80004000010420041c080900201c03170082d400d9222030796580001c183c480303140082c001c01110368408180400d004a070f000a03004070381860500c00d000c0e1910000301d01940000520460320882c03620f0345403602c800300140c0d00c080006441c909030017440c110201e07a0b250b149000087c8900b50f0200004c5091714000300f80c400411162505010300d092425014040b68000d6850004950a080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 203899478 1250 203898228 203898239
    0x5131509050613080c0d05070519030206011a090d111002010605091602030d050c190504050a14060f0d05070e04020c0703030809011515020f0703081c0e030307020703030306 76
    0x31541011940200241003150b4401500c2030340d0154440c070450b0000c00911943c03030b02e10020031040c103a421468940301d40e5115581010362a0521020791103058a40d05403000b00000d5003c00d103541101d25081c01010700c0207004400404500684140360b8205804100f00390a00003054110056018241d40500081d064644120300380d5906000351904200c800c404140488010000481200c54502c1503900344000a00c80c2c1e02501c005a56100c486000840c07219515103403000d4441c00c604140c10b265180620f84404212590b15074030551408054800380150710f6281c150807514100f8030002515502e040c440c0340c090050105648481c0001c62036040c80ea518107040c800c54008500c440020a00740b8550768040343d20500c011f1010b0a555201c012204084008802140c0640502c06880c3c0c0d079140d5240c0024034082c400304d0b03901c100d0340c400d440810100d00408111a031123004005103a821400c003d8240001e8801381011000e1744c4070000400c4421030380450001e051b240300e82d0f0140701076503841 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 203900728 1250 203899478 203899481
    0x6010302012d050a110105070903061109151b0a051507080c1803010b040207050102030a1a0a1e0b070318050103060812070f0c0303020304091103041e0510051315 71
    0x7048100e00c42c2c804410300d280114050005080b90390840e103011008111446881403d5410940380760000c40c0e0406004d03c01c100c1c182c00303a92043d15006100a003070100c100c00284d18290341c0154480d03010b0380019000b10860300c0c4440c481c1d000180303404a400350300e400e10f842552156002c1040c8100409800825145840b600c0c0150164442c03410f5030342440010514000c0e001020700c840e69140d969404059000d4603a400036050580c051400180c407403900310190001e40701d050301a0501e1a00c00001148103503503044030b42d0700352465114508415a210401000340c4082c0381c01044036100041620410503520207600c00040720f1000d03220b450740e40e84400640c01c1d10058094525a5080750a1840c4071802e030ba005010784a000340d12080281190340c48a10b01482c1c650010340040c5c0000800b4002e105c0c081c0600c510054910b00598994502900c6408207890078034500c1e8442c0c0c24001c111001d004040200054144080c2001c00440c105061000450042c003c0b084030300130392203000400b407031285 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 203901978 1250 203900728 203900777
    0x1612030509190201030c11071806120201080c03070e040f0c260c0a090b130509010b181c02041407170c1204080d06091d0307030207150306030f050601030201 69
    0x540c810507080050b2a40190301038000d52100b0300412500760001c10003031804206401c010845844240104408c0c080c40b44140c40c07668002c40c5102c0c15410880d00180d9000c1101c550000d16200c0d4161a521512001c0315004400c55605030301c1800c2031201445082c10303034006005030f5480d46402c0d292000e02060042048086680207844d02e908000140c0038000d010024411401e540c0b91281c0060f45072030821007150481c2c4068a41e40396004002d008074100301c01c0c01405040300003030141c2041a2540011200e008141d400c81c0038410614007000030450f2400340070f1546500420610150607100400e514290007101c0240000e00c114a4001c0d441003c4034106010b406100c010034901070076408219440301c80500206d030755100801c0004a2040c80d0b00c120030140600074004103a812411604400c00442c000741010150410010000040e4002510f20220b441b0b5411a8281c1c2460b0314041e00244200d50000d00443c800080010030800040b4682e4142d034800d032a104050701d490a095403800d841c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 203903228 1250 203901978 203902003
    0x506010807030b0d0c03150b1e06090402091c120c0f020906010c02031b100e0d03030b0a080d02010e06070e0907080c07210f0305060d0b09031612030509 67
    0x21603400714808038401d80240781c0080018146070f60310b4400d56900c000c241d402c0c1c1c0c400e80b680c0c0e00300c4105000c0d04880d80984a83c140b42120314008882601c902c0f100800f180d0b8a0b514416100040c0740ba04036240c40d01610008600149081110805100c25032001c100f4411308469a40c0d0544140260b01e0054681030400394110007080c543c2c030026800e0059540c03001d4030040c1440084141000107a81c208951510342108007000d0b50241c0401c8140325190f4400301c07540040c0003000c83c101415440300d4078901d0360b143d010324020a00c81d003884046414011250031001b0325014803941c80302956015004609580720000456501d41d40d511004c82d445440d440055521001460228901030700c10513071290000c18900e600c0c0e10f020484d2b0345005828440c0000d80519050620f440304080c0e0300917401c401c281015080030b118910f060780015840c0300e0020001407500c504100810b1000c03804006591040380c40c040f0101d900902410580d080002d041c410314002414800005c00340c12011501803070025 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 203904478 1250 203903228 203903237
    0x6010906090b0c010204210302060702060606030c16021005040509060d020f06030903122503050c0a18050603040305070c0b0a0207090218031606030e03131214070b0405090a050601 79
    0x500b400c24071180c0d6446511030000d29034080c04041855641d800d44007465185008110180885e0b80c1350180c02c0c010020145020b42d00500e04000da103442e0901201d500a41501401b55100341019030340202c241402806900100390040300b40085801c10001d105545c0d04130380c0d00303000b503507854100030161070000d200035044098440f0121040c2040400b964014815030107403418100d0040b20700140700411202e45140b10260040c004400c0904007110b4441d0f80070b45402d11107131030712805094007032040101010820110000d518840500c0e02219405448010032007656401c06003401006500502d500b51680030b10b1030000200b080300d10f801c84041000c6600a82401c5141c0b0f881070009400000301000d5541111000b2403ca68046c400c040c2c103030f1043c820f195062030628100500b210300c44504040c00350301c10803811029800c0c061502007141d0f5420030301b94104e0035078038080074900710fa1083c03175032203215900b004030315001d805004c3d005480081e1a8041550b5507110b140040d50340a41e000340c080b4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 203905728 1250 203904478 203904497
    0x409020f0d0305070609080904050601020a1a070e130e0601060c030c0b18030a020a17040e04020906010207030804121e20120d0305060f040501050105120a060909031706010906 77
    0xd0801c003080711400c9000f41402804d01c80b10352103800c10f81c0d403a086d00303c0307901e40c0001e070b0204c035442c0900c2001d8201200b0320040a001e150760f600c104c3c42c140c0d00d000002c5601c0c0c85500145405100343c2c044020008042d018000342c1c449548008007401c07130300588088038000c200007c65864482e02940c01c45503015aa61400b950040d02d81c10807914001e01000e01c109031001401c2c1207210308000800c0540c60b543d000307011103506428113119040c415054003603d12010081009502c654a824030703085601112101110380f200c000507450101c841d44020580c240c085070000b46821050030503440e9034000e0310001800024040000d101c0402c0ca000140800c2c100d11082d070f604401003411080241014100f0b8640100a20a062622060050810000c0c1e164020001e150400403031080c006070b02074406100c3c9504050010b01103018440182d82c082150500082e04160f49812080080c0000c1008004911403410000d10100000c1f403030000f01080c140110742254850382d0001e04492181e510021170 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 203906978 1250 203905728 203905759
    0x10b031203010b03100f1205060709180203060d0b0412080604091e110306190f0501080a0b070309022e02120406050706060503030a0c02090c04120b040f150f0605040902 74
    0x69000600036803a40085c02c200400c0015240d400c1e070000c2d106601072810488942d280551600000030f207403904100224108009011282c2070003003c0d13081140d005a225642c140114585c2d04c82c0c1c04026010240c15000e0206000d000d00710112780c007040b50754281803591003805000542d42c007407000902054002c1da14490807400e10030007048140c417550040200c003180c0d100007131034a001500ca0b088041480102200a05d401340f0540c010580d51a4060000c1d6140207a469242d00c5100e2020340100302500020b80031501c41d0380720049882c0c0c0200790b134a20750200e403166000c1c020703800c014204044d01a0b521001e12800010003159400c10740b00c0580c03600d41800d8040b103660300001011159552101b0000c5450b690a0025000310812a60f078030030324000074010010342001c0640300b00a0210200401c2c0500c03848890300d10f50300e50300114070392400d840e1031030450760a903980740c00905000340c5007240c10403808140d0480c050b40c0441910900c80d0310740307030400c0100300d503040c1b0700c025840030810f240f8081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 203908228 1250 203906978 203906999
    0x2030616051b03190824030c15070c09060e150a0b0c070e0109050a1b020a02010c1707061d0f0303040f060e030d0e15130f15090f05010b03120301 64
    0x11100400c2c140c0e0b0a140140411150001c001800d550214400500300401c02441c0202c80d560400440e80340e69000b59102c01081e1541c80407918103000d20045c0200996440d031800440e15001da100d44542d54803560355003080014844d40c09070003044c510040c0410403580a00700710030309202000340b1401e1052319200d00028990700c901c0603c52640103070200000e06800319078809000304081e140104080c940100c0e0704c0d0494155002c82c4100c00c1070740509a0410303034005401c0b00050ba080c01d1840c8118800e0804040e8410400c4200414140c00a010f070102301d0543c000c0c84441030ba114146207035a4801041a46501ea03070701c1c0b038115580c070a00c00100402c445401d00b002036401000c0c005041c0c101224aa403c5038005080b8641003a20f80c024182030b40410400d500c80d0248a40800b0490b003441800194040034015010780030321520961130080c00740150150038600032120f42005101528170700340c100c9080e00a0141d8035546803e0b5045258280441c814110340303100c040b41855a03003011180345 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 203909478 1250 203908228 203908267
    0x2060c03091c030b060a08010e0711031819031a091c03110c01050f0f0f0f0a0903020c1e040b0907050a1206080d031a04060609120203030d11070203061605 68
    0xa082513103503c0700e0100b40c0c49020051800c01c5035941c0b004007540c10821200020a0003411802c10448108080402c2d402c0c003009503080741c4d0302e0310000040800c11000203241c00c500041030411200703104070700004200c0d50340d44d900c0c5c0d001c06510710503107156034511190f41c80e4503001e40b002188804000d0018082c910951103454490300712610141001c81103000c283c2128800c0340e801c0c1d40744c034001e801d2246060030000f555030312020502d6100c20529200081e02025200601003001007620303514400101402842501540fa9015110010742d10414010050316420801800c1c091032409140c0111030404410103841003003036841d0035141614400d82100d510701d0b142c04803c80725a9440c408500c139801840020b40904181c1e80101e089400e01e114252880d99410740c06101e01d14107401080317003982001b00c1c6021240c0166500c0c40841c924000700c3d04500c6140c40300c0c02c4451034030581303003d188010340241220b103000340d007110040d0b96a1b00444c001c0e5200031a40d10003003035051049007125590a0010b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 203910728 1250 203909478 203909533
    0x6140d020c010501060225030c050d081b031c05041a0619080312010602060f04060e010b060309030403110105070c0509060402040504020a030c080601020c09150301020f0d0c02060c0309 81
    0x1450107201c0a03080b401c641e42a001800140c000894114290005800e407001c81802c000c4101802c514598503100740c08054407800e40100086600c540a1010f454295504801c8111220404040380d10b61281c59074400145203500d1a507001d04c41c0c040685908c10326110b00e074081c0c40c0081c0c01d00110420501c441c00140020b5000b60000d20f02d03007444075500140340081035918000c40e21080d42c1d1049800d441030503000f000843d8800c1c420419a59803215083d60443e41007280015150007902259016100010059070000400001c4c00b0b5000b0000000f1300c216805002c03061007250000004542500c500c201c003a2400400440a100c603150030901070303801c0003000304018603141d580c5002c80d00b81d0304500241c1d801319950740c6105601c0ba40041e001c2d03502100034806032001c0c1840304000ba5100c00b01a101c02190921034200800035202541100c4503814815541603c403449222240c0141088001d40c20040c060000421682d0f01c01e07900ba07a000305c8018001e40040c00402c1e405003151a40707015003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 203911978 1250 203910728 203910731
    0x91e0e060604050a0f061205040f03030e160e0a0e0c100e01050409060e180c1507020d02090103080d0f051501050901170a0605011b0209131506230a06140d 68
    0x2815035200c1c044c2c0d03001820072281ca0903100b0301c1c00d00040d00307000710300c5100310015092a0410000421007031a90846a515040004142030300400c140d1901100009058107144400000301d410317102c00415a20450751102d0034050040101c0c55507886006003800c8a800110361050050150301440034160500e80601d45940bc00e0354602d00315040e180030342e00c6101c0c810404000d100e00d07403019154006040081c0c0340109421917405010642c02c0310031081c503404c40d241c0031130315504641c3d500d548140240d400829800d03036541c61741000380301303980041000c154003403038420074030350712549402502d21818003129856103101c8a0001590160300600c4040c1c100825000428a50280780d6031450040c00e0400c0300240c51401c110000d05080140c144a00448011181010040c2e070b40002d82c5a008011032081c18100c0040d103400184000c40c0210645094100341001c40c003040c040a44400d001641c000c400002582d003006d00000030554080d040008000c2c110043c440c0c10b0b600c00401e001200600c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 203913228 1250 203911978 203911987
    0x23151e031906090b2403010b1602090703141302030c13021c0b13020310031112100b040501060c02010c0b0601110111030603071d06090c0f130501091e0e0606 69
    0x811002c5a4041e0040c000c55a550740102c010780c1800b40400c1452483c00102000300d580304104480300c0d001c14441c00445241c0002d80400511000400d040541d0b405042e160745800c00000260140031400c841c1c100304007140001440c90700c040c2422000141d0060051320b50400d1541c14402c0034051003001c80041902080050420b80b040c000b07001450064010010742002e03404100305841440d21122025107005009002c891001042c4180440350312540c40e111014130315002c9000011102e04180c002e000d500142d19a80625030440881c1601c103e40c1040b9607a00d4030030a56000020187c00783c002030650002d0400500303642810398100307005040108c445041b1001503425207100b0124a0480d0390080103014140c1800c02040010f008412042c02070280a0b2007145d0f50b00350010101c43c81850710502103260850107604595030000b401c1500c0340c1d01c8031140c03410301500030640b042d00c2c00109503020000390000b1501600352105036645150150925205016401c014003805056001c20f0401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 203914478 1250 203913228 203913271
    0x20607020d0f1103010e0102040501080112031809050406060b03010311100201201905030108030715270b0106080603030901111213080111040605030f1023151e03 71
    0xd030002c515101c0d00e8460b00b807807041d50504d401d44200c90342c0c0648030380c01400107000c940c2e00043c409040d102c2c210700a0441b6559424219018402681e1000c0b04041807500412490151340005102d14000c80c01400850b80c1d0700e82e03000301403009200281020b01803105601d0b161a140d8120014038940c0e10000ca800c1c03188000001c081c000040000754030000005034080f8000d104080704041010f28107041e421985001d46040c2c803481801c0e402400601e0b5040500c144060b254171058a51800b0b404015650552584116002c3c00350001952a0003410000143c1e0034803402003c0e100e81400b40c00b031424140a0001580d5515640741000b40c42e00826241a09000f5190050311202142c8945598400c0c6000743c0e10303007140c2c0c813410840d00c0c0e5102008144a542e40150440b03402210002e08003d080d030b940e01e074407044090290821401c0010200419001710883c80040b1102e00c1b0031a500c040210005a0300c0d8414450703a20b41c1c4085406100040d180d98101402030360344014000d043c20109040d50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 203915728 1250 203914478 203914493
    0x5012403030315050a06020d020606030109030e010c0c0e011206050604090213021303021002070618030825051605100327020d0b0106020610060f0e042003090c12030412020607020d 79
    0x6d030001030060344040324010040e641080900e800140a42c000c0284100f1034034000c0c8041c80812003a4140204440700b0341c100a0303000c008030000c1c04945d1a020036540c45442c140d102001004041c2c0301d4508040101c5c102d4540f80c4203601b03071281d0040541013218240107190f0040d40100144250704100486d000003d0f840304c04005500c24040d50103001440c0c24100003400c843c03c031000038181a200c0640600000d000c807421107582c1052408113400050303060011004030304218600502900401d805080207411126208058440403580449084407035581141107651036a03801140702400500e845600740e1169644107400d0020b410008101d00030b07112031803444d03001c2c1d00c03200c0141d00403001c000c2d1038022502c9100103000d0f980352010711400e001074010902c0303e20340c000c244556952190f0600f50001d142401d00d41501000c01903459291414030141c4814605503e1405490344120129807103201200710b500340d80004030071480d0420700c2d40902c5815003101c3c6003243c0003200001a0404034038007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 203916978 1250 203915728 203915749
    0x1f090308070813080f0a02010302090a17010903020c060918091509060115030e0c040e031e09120f070e041704080f010c0203031b09130203070c0501240303031505 71
    0x1d03520140d40b03440c1118004100f1a060b4880a06074000907000710b142d030008140c500d00d1075024a0050780b03d0010000168588000d03910282140031600d411a40c01881034100d0203009029409641170410040144640d034864400c4040d0f00002081c00c890401800c154040d8105c80010b003240d0b0943d11800081211800954512500c0e40c0442c004100f20102d101110070440e100d4a401c0c000b100710014205ea440094194840c821034480f0320a00920200300103a544c0a54078030390101d841400e09007101c0c0d40c0d902843e00c00f40102038a4200d000c2c0507000045005200710b001c402808e0311860301c1103014035444050320483d401450040c2c0410605404009000a007e40501070044c1121103400a421200c80b03440311340c250341041c000c0000424000b10400d031580c102030115951040002c00003103400701c0542800c1a0070388003000b03121005d54040c203190042481003000300f1a54100c0c43e00403001c0d003020900915060601407040c0f001078441d8104030300581c10140940030660707c44000a004189 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 203918228 1250 203916978 203916983
    0x3020915030a0521090a0302131b0302130f030c0b0a050702130515090402060901140708030702060402010206100e150d20040b040509070504021309060e1902091f09030807 75
    0xb681c1142c800384018403034109041248010503160600e043c020a480700e189105c040d10910762889c840c0880402c94111000c41d0043c41c840d11885038450302c001c0d00079004413000921540368080041108220f005a14044d290031907040c0110920344001c5145541c05400d040d020000103103d020b0040e124141544030100580070041203034079021842d0344009890701303401441203407548140005a00c4900403030b01c200c0000e01e80200414138420580c0110703c542c0c4401081e1003c0002000015580801c1060249100368290361968441882d0b00f403880a13640580c3c40003101140c0860682905050044103040c0007502000302607609449075122481d401e4107506c1300c0903c2d518091810300c2c00d80728408140b1002c407810803c900380304041d00c0d901c1071341b400b0380350203240c1c002041da100040c0c1200440041002c0c40c028000f5a80b81d032007550110100380d0302d4062628200c95410b110000a000340da01042001d400b0410010000001c8018514422a1002400103900700803012a01030390042c0b0002c0d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 203919478 1250 203918228 203918233
    0x130318060807141305010f050f0408030909010e090606010e120a05010606020c03070f0e100e04060f0f0c0804030f121d0d020f060106030b030304090f1e051003020915030a05 76
    0x2d070503034024099031404210906410010400950800041c03108041074941c02c1c81c00c40500d081109080c1d86078880d20401c1f03100b80345c0100d00060044000030042c02c1c5100152280003060341c1e2a04550f019100c2500d00f024035800050004446510852000134404c00c01064402c079650030035520f0341854410714055505035110b14042c4032141e01088190000d82040d4010038049152071107640d2003030744a004451612010101081c0036079003002c00540981000d0008034014289864140d008040c1d0301d842e02c41c203a040ca9440c0d001d1001034070988070010007030348440d815030765590307401c80d03080d540244460144058860b4a010401c01c901c10241890000030400401c00110f451079890108485580404c40d44100324941c41920b000c140070341154500d0a000c05d0410341c00d1f0000342580210f03001602c02c00e01d01140c2c01c90100c5c0702c0d00100403504c85070492401e80d51003224150b09540003225030000d802040b09080005040030b84106500c00c0d01c01042411880c18040081d0800c504404c0070b5038180d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 203920728 1250 203919478 203919481
    0x602030a02130510050403060e0120040e1e0403030c02010e07080f1204081c0e031b040b0d03020607050a1218050d020f0706030e030d0906020414181303180608 70
    0x20a2074040b2010308001c80e0071610002414800415502c600c0c0030080c4483e4840645080c8a40250030681d2001245990303080c0211401035500803070b400902c5646000c048100108594410b001c82d00705a1400780d05800607140c1d00d03500c00341c0190820402d820b0840d0750b556041031188130b00f400b1010141613624042c0c58a44250381e01daa1401ca9544501c1028180403c8104604a40061041070349655000d00f200c2d6042840c00543d40791020b8a41079416001b0000c9040c4242d031000b10030706148070308840030020f2860410502074903070144400100980d1080011483d803074003850107010078100c5860700d4116400128040000e40d1802ca5081c0341140211002c00c0c10081e00b0300401d0401f80071803008056901c3c5d0b0140c04c2d96100c055110745c805140c4e03074240d02001c01c5001c1c411641001c41801050144100c5072038040c0c000d40c000d218217400184071030b201a4041c940181d008902c20b041c0d210002d00c64507014000341c8543d5041d441281401070081c4501c010306682c1c80450000c1c032240c4c490250a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 203921978 1250 203920728 203920747
    0xb0103051b0405191104030b0106080a05090f150a110708070201030b06070f1b09020a0c120908071e03020a03050a02040f05090d1206090f0911010503010605070f0f0602030a02 77
    0x1520314400c60804040043c5804d400c1540400e10071030307510204420100f400150040d10840d0409800a03040c0000403565541140b1040c2c050f640c24001040107a0312400307002c3c1c41d030081c441143d8a942000d41024000200010141d400c0f41c00c141d400101c0441c070b0300c4a10310a610460701180d4162000c0361400940d07815105000002d1806e540e80c6241c101d0641d40ca201c0b0651005004001c2070202c0a9807080200c020030110162049140031950f030500744002510034413014400300d403203c0032040243c5038544260303011030894030620000e000b4036040c80b88482c11600e0003407054004030141200000035944d80600d642c01503001d1005421620000e0061009039505086218015810002070020460300000c030350024140901c0c259280c56200d9080c1c03405040da81d4018407805007408510a042e40040d441a00c607540b164494140d400307088801501e40c0e0001b48114800f20340c040c031181c000719000048545140c0e02c5404d0707510050010b541d4803012601709407050a9801e41c0403420a54 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 203923228 1250 203921978 203922013
    0xb0c160b060a0e1306090501090804080a051027020303250311030307091e08060106051b0606060702060c2a040b030703053301080115061d0405090a0b010305 69
    0x14000d502000c1c403030f41ca01100b00d4203c070580010020880d5964040b01c1703040c45001c0d800350708900d502c4116a5600c5540d05411303650f030b04080030207540314000c00780030f4500200140304021550701c8080f4040c0c0380111a8000781c003103020011041e41c15000c10080c00489581c051a00c0d10380c005803518011050700103050003000c00185000b102c50f540c0c010801d1240c855005168841112005070880d8442020b03d88c44469140c0c00340c1c00300c0800c0c1714810002c41c4840e00b04004e08290702002000b5807204240c2542c603640d40b070f0203a0b12150000d8003049040d015040c1030380103185a03602c04e011104005100002c41d28004c0da610001c0c00030940d11241500ca03454030b4001d5030314040b4218000c0400c5411074a90b15102c14250300101c0b000e01e000000c013501440c01410010b100348010816125540c0e6408041d4003905030700b0040e880c180c000310408110703540281403010410301034070170748141c1001d014107100041c43c0142103201c3c5071040015030400542c85080d0705001e1480380c1c000c0d24111801c04007109 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 203924478 1250 203923228 203923249
    0x20307090603060308030a020f0d05010807090c03020405090103020f010c1a01061202030f071b0215090103230705130503030d0b030105011a0702040c11100c0e0d0503070b0c160b06 79
    0x7010142010750070008904030100703583d0030117441c0a00680c0d5400b0300300001418850440964106030510b00002110f64012a40200701c1d80044810312051000701c0c8103e08074400c50165543c00f216810040c000340c00c101514a02030345040c101418004000e03140c1c1c1c5000f50b007420a640920031844014004c060f4440c0224030307281c4107080c0a60550810001090351400c00400001c10000e840844805041c07420102c0c0742c02540190204100384011284031440354405521203000c2410040c0c06007100c0020f42180c00c10b05100350107041e8940341c1d40f204a496030b02c0b2200c0c403500c038201003402094943e0244018000c1c400340c1e0800041c010f4200060600355481607200c400900d00c0740d0100441078040c141120f0303d10b41c0c1102d0000300001220342c142d9501c0400b121042d203500c10f46800281544450780050071009550302d0705802c2001050070003407003038044600200150010302800e0000303229081e5194100c2008000b00e4240301001c500030f58a03001000054030300c2d28400d0284040c3e410064140d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 203925728 1250 203924478 203924489
    0x1d010603020a1a030609090309060406021506060307020607050304031707050c070905062809180b0c031306050703060b0a020a03090803040f060c030c081b0c100f0f11030d02030709 79
    0x1400440c43c1d82844150100400031405201c2d9040056040c030418021210803a10007426642c4894440364000e6544540710380c11402c4018030300110321545410401d0301c1c4585155402428159201407003218039070000340046083c0040201400594512250b0040c030418655039860f0b01c503800d89840c00c0c540f0b1025440180058a0881440803039220784074410b445080355a002d1180704154082401140325550000184600d4070400c5040f00d01c0000b4000b0109000d034031070042075100c106035001c0078801644d0341c1e03100c1d000310301c01d56000403111303040140e01c841d1908000486039601c03246801d403503003d0441c42005801200d45c003410541c0001d00d49001d001142c004508040c01d164980c40a458640034039028440c0c001021010548250441c40166512802d101d4035000e212840b0514410050a016610301410381000103500306035002c1d4000595503039511444d00c2c0b540e503007034810303c4032010103200300005240b03da4007180d0100001c00503041d8000c80103036039203004000107180c0c59031070b0041c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 203926978 1250 203925728 203925749
    0x140606010c03021b03070e0a0207020109060e011b1a0a0c02070f0506033105010b09090d091719050304030204180305271f030c17191d010603020a 64
    0x4071404640d001803041c407240e194404c82c150100188000038905102c540c40040400781400070070100d410160081c1c0760703540c400e8a41c10b18940d1500c0d01640d000d14030218950000308030402400c030102140c0031050303a940c01159202000d210003614007031000400c5a440480c00d813210100010254100902c900508054084910b002d0030b0600260703180c40050071440c2c03070745410340c0400c440010301040c3c3d008124004080d10750380c600c9441c20602030008100d03481d100300c603000e001032400c11010608508041c0d20340d84890416081c0300a00003285041032109005109803100c03000c03106034031450740d403503940550025a1200c0c5184100810f43c1c2040024a614400007481d0380c1c00070340c001c8151481100340b203400d101c0749440782c80003e1000b00b40b002c2456110b0608520380c120040c1c080d5000d1090000c0340c0e02400480c0c0c4403a0706440714428100d400780c51248600000da14207182008405580c202c5420106005080f140b130b40c140602036140e01541a551004100308515180760340b0001071017106070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 203928228 1250 203926978 203926997
    0x20310060818061302040b03070f0e0a020306091303020708150108010501171513120c03090e06130b030111040312030b01021c0f0c05060901060801051b0a050f1614060601 75
    0x1459100c60000c2d18603d01075071100441390455845070400d02100c030014040b140354540c3e4000c0d40121524910135a1f81e000c0c20130303001c5078402d03010b8005c072449040d0280040085d0b40322038140003440030b488203095085009551000c14908030078000c8108510b0700401d00402541450300060840d0780683c0b0819061805640c540d5000750701040e6100d20cd4048120036515544440313060b640c0384000f9800801c10b03401d404422181c203800031040e401d0b0038001c2d0707a4043c0080c0c031f6120009140505850165100e1a60f80e085444484d02ea0003a8251100190020400d03640c20340003921590042e03001160300d200000103c0c0740c1c050b0305200310701180300c0034402030200c0c8400001401c04d07030031600e0780d510800001d5445ca086490050000d00c0009a107c4116146494180f091a009003414042c440d2a54202000304a007503402c50903104080e030400010514001000c002030300d099104244900e0340c0b0703500744400708091228500415a00b4002c0f02040c8108031404811402c1c50b80061615050182c1c800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 203929478 1250 203928228 203928271
    0xa05040905070b1e07080c0609010e0c04110c010e0a0516050901170307120504150206012d08010606030b0a05011b1e140c0f09040302120313060203100608 68
    0x40d0520440f040540450f640d100700321044030201c901455154a6100d00040400c1001800c4000b4440c9038000380594660f41c546512480c280d400b00e50781f10602c0d80c03105518210502d0254040c107500552500781500c0c1c184a80d88190a4441124641403203403c100e4440b070034032105004000140f03000114403015030b410640000c24900060280d0040280a40c820044040c020000c85083c9a04400029106013881d07070020b14560142c0909000c4180e50807024819600011f10107051300c2c10429103ca44a100141d03020051900b05181c14200009840026200100384120405800e959502243c0344c0300038010711003000040d0340002d0400451420303000e0035204081c0030301540760b403110b084546040c04600c058804020030801602c441030f40044002030b041c0005170300d02d808130305071103d000400b06035003002550300049401034056000101c0c070500347c071080d50042d540080035548510440400b42c40b00303005c91304222910084c880f42c20206000c546d4010711441e600c01c27144c0045101460384030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 203930728 1250 203929478 203929483
    0xb01140103061a0d02070602040504050a0b03070902040521070b040f0806070c02010c0b070315080102090a0e0c030a09050a08121801060b12180d170702010902010c0206030402031f06050a05040905 86
    0x20504e0254142d40032507024100001501107500401c0700900c140290300f0032802e03000040c0007038860140310b880340d07941c0000c0406047c000e45084a00052030340c0d40345a4040148101c08103421444503c42c041c441e404241c007118200a0700140017610200f01c8114107202c085464210702800354400e02c4000080000140e9022074000d080c540c0c4a900b0341d1058035910010f401030141c0e410b00c020f6100c00320718003041601c015405050540c104881c0760803076039034404041e80c1c0b00d001170b1760309440c0403000c20004881c035400d1313048110070705d200c1c0b0201c4240444c1038448155642060400c0701022481206015030440424801c0403a076444c40c0082200034078161680c0d480e0320030b644c3c420884c2e020000000d801005902c1032401080706c403809450500d0445000100310308c0c03042c0d11101070b4050100200e00c1e20b500c140b00704030340a035044e103582158821580070807160b6000100120303854800c0c15606581c200c00c2c08080b0615211210010a030755042c0010456a00300c143c00440c0654501a413441c00304200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 203931978 1250 203930728 203930737
    0xb10260c091006032f1827150414010302120c0102030307030c02011d01090b0c09030a060506130f06051305090304090209181006030f0209210a0b01140103061a 70
    0x100c2c20b001600030aa5501309070094500469100c1d5850170000982180080800511001c0703444280f4801c61301071b100800090b43c048454030080d41d024001c00c01d40940c0381011564001150a040000c0050700b20002415522507525541c0100310203001042141071030080890813000d01c00103402d0030344480d070000b507607400020540e60405468000350071416000b075110f20030b50034140e00c42c440d0070300001c1e803504d010b080740000c21034554044400144014458509031901982c0060103400c5158090301c80c100a490302414a660101d80310f60407940364105032180c100b90400902001c01e07410b280c0340401c0b001030082d159400495060008000d0b081e14040111820b44050781d40068071200310b1004a045409012401d4200708000410701c134290754007125510807101141c0d401d00c04100d5400c03604041e401004509070b000810b100c0d03d00c6800d1903007400b0301252400039080f40c240764034646074808a180280d22074010141100646403095a1601819025010304100d080b401c20782ea00314003603281704 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 203933228 1250 203931978 203931989
    0x201020c040b0f0d0507080609030c0d0f0302040b0c060702190f140a0203160807150e13110d020909070305010501020a080901020106090c05090f030115030b10260c0910 74
    0x2652000d07090746583e200d05101c020200508844200c00151a06550310074a501580200344900000100802400011a1000320020b8050714429070540c40903940c1c4115a1003001c2416000c2c0000b24000d1100c00242444282800040506081c002e002a08001418810b005000c01e0009228041038201030300441140e881451074003040e0707020710359600f0101e0b4000002d40c5400303681041c0c0400280980310700151400d81c82510001c13980d54070220035415509020201142c0d08803003a080500e4010b841c00943d114225010a10070b00420310803000360f11000300e000046501043c40d540c80e013440d094181d44a91942401c00440d410400081c0d0b540c502c000c0c004110800010781103045074801c1d0400001401c98074420711411103124400340c4241c200c07900382c5000e0130007411030005a02e414002e0071140c0040c1c0310f410071030301d0442e251120168001400c80d491105811400112918124490b144116845007035490700701c1c01c0b2640f6800c1400e111f5502c0c1c8146120028801c4000309409507008030346 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 203934478 1250 203933228 203933231
    0x150405150603120f03090c0910080613030915020c0604060906031109030a0807050f0303011d0601090f09090303140108070e1302010f0f020c04110a17150f0d0f0c090c030203040201020c04 82
    0x1a00c03141c0680c501f100280071560001050310a101c0c000c2e4400007244150340d290003d660155407604480c0440d1080d01c08040d001078000d031000c001d407050813022816182864419030b0440714a94000c5801d6900580c000b00010b488050208080390f41489a0b025078982d0b044914a41f0f503602d030000f6a20517001c417015103942d00000781d080400100300029502a4101c8040d25200d60351040b9482a130000002c01108040c40400010119880703400c560090f10360340740280c0300c5241030122510041c09039180440074590341e1420f440c0f0121601c0c1c5c0440c024401040201076042c14507041200195002d0210151055020a11b40050f138220b1800c101d450700910f442c020391254040102e2925403404000743d04945003801c90040c0c03003024001401c1502e00345c0ca907a0502d105915006100410482e03150380b5a0703401c01080340b503501e0002c1c42c104036050000c040802d0b241c1161103010306040020001c5030b0010580000b00300070300181c0114500781101d410110709500e03140e00040d44038001d030f88565100c0e5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 203935728 1250 203934478 203934481
    0xa090203060a030f05070f050d0c1e05041d07080a050307020d020a121a09070e0402060a03090803090d0e100e041104090c03091406040c0603090302150405150603120f03 74
    0x361a5032501c2d0b40119003000341c605110341503043c02d94407403205014400c800060040c000c9860b08080c020b4003005540b050074a02c0451501500840400020440c4c040140d680c2d08001119581c80c02000103005407120484181e1048960103441c0c0661a0f20204007500088102800306601105407590b00382c041d00d141c102c0a04920004505c0c00c030540014046107008440001400340b07030f400c0d048503c0c550004010700c030344400e07403074540d5010f0500c83d01440405040004005003800c4000d48401030f06424080f070305130744694403d5801e070001c89010407254059001041c042d588501c020031920b20556030200300c1c0690500c000c080048050301c3d20702072621940b08054031003200c8210350090a40d600c003000700b140e02c814014003410768258252003480c60313000000008440808c211340521f03402aa641d21040c9013800c190050442284207030158014001480186e280207069241b2a6210704090704058007480d0380210000e8015102174080c1c4d2202508207105070b0901d007213405410060384059143e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 203936978 1250 203935728 203935741
    0x7060f0507020a080d0305060a1809050c060a21060b040b03180105090a0b012c0403030603120806270a020f0706020a0e0901080102090f0105070516060807021b0a090203 74
    0xc0d840380800003034004500710000107045030080341c81c202209403540d050200361245170820440503e6030090020401203031901c1d5003d034195500c1124042c0c404e1043e10110f10078440001c404d03400040980c40466000f00182d000d80078070044003041d501c030351002000803500780702c910019400343e40600400303001d0000202e04021715a0806806a041c18002030000d868020b0020f503c0e1100c074001160310060000000c18004100001051000341540d038104e11240b429030f101110160160042d010300d90b075a000400803403800002c00494654035250100c1c1030800c3d80030701c00340c56940c1600c0e100c1c1001c0040070a0720605100241d90b0890700541d0090f072151207207500102c82d4815803038018030309072000503c0c001703440e0000c40880900c14100e480e00c000740e0340c40c90100d00340d00c02c00765032690051856441e03006c151f025101614045e801402210b00e125046010100003110341d0f041480418104420082099810408492800d540a00007001d150783c040204000070224003d9202d440c0c0c022000445 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 203938228 1250 203936978 203936987
    0x303040507060819050403181703030a111201080105041101020616140c0601090b240a051e0d090b01081902091e042913110f04090308010504140907060f 67
    0x441c28843c041008030b4205481e008d0802c0c2c4400d0a0300140c03040e44100001eaa04000c92a5210120f00c107014615590310902010014a05c0440b000a0a4410b1041c00703000078140c2c200501070a481c0c40005200d0400d420010760503055510006c1c1103506c01c0d0100565000c9040b000641c80c4018204503e000d00c00c00030f2034449002c0d903500c014640c4180e1000140700c0000e42c010300d501d0682541c2c0406039043e80c1c040320404110010300304011200811450303020720300c00c1c0014050300300c00c51640c0ca0000321400c1501c0e0242e1241c012028000d44911070881070010785a68240108000001003004d0030300010060442103108402a00c2004c0c0040041c04a05948220b868510007900d030200213880c00d03203494031210515034540b160f404161496044004841e14005004a0564036040a90489550b4200b4001c2070000000c0c1c000345d00e4000440c035030f03d03103029141003a88039848900303056040409100444070b000303504060004094007480162030000c224042a0340d181d141140e4881c5110380181d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 203939478 1250 203938228 203938261
    0x80d1d04020a030b090109090503270a080a06060b031005010c08090d050604030906020d120e010b0a0b09090c09010f1115071d01090503030912010618090203060903030405070608 78
    0x6800500020710341c60070603032641c130031520b59108a8820040f0307601e400c1c5250456500a0004105034000c100d40704285d01240f0051203050240c0c05100c640d086140d020400d0712105601c8080755604c03070958813041181e240104400741982e820070604624000075107280118503440703901d0500c200c01815000f40b150300d5040342d00c1500d014180d410050780c3e40c509503035107201c111000da001030500080031076450f2000c1000130911075641d4401f110b0103041403200000b0142d038150902a03643e1010102155203c64001c0c0000f00040b44040d03440e10700c03010078844200d0b001407880500000401c500039040e0303000707801491005003901c0c0c840b201d6443c6610640c54400b2003090044000c01c044100604280e00c034100c040c103e412640700004962419005503540050341c0940c0da0b0640042c000c40b50702d410b200227400320041481c0000b01d030a40e0303244440c01503440f12891582025440310341b6041036007400c108040c0c010b10403400440c0341d860a03848458803207040d40121010410000c002c03400b140b04115450 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 203940728 1250 203939478 203939537
    0x180803040305060610020303070e0603090a0b070201020306040b041b03020717040b0a03182102030412080c061003030c0204020304170a09140a0302060d0c020a050a0803010806010b04080d 82
    0x8035a2280c981c18103641e107100c104c1c1c50038400c1d20703040c0c00c803076030755201006a038007400d01c0783c4501c88500340c2d01c0c04014081d0001004446c41d0b10488110001184020805a0140c090b503000161350f42081d4013884113444151000d107000b80d003440d21140c50030122880c044144100d0303250044e12341c111441c201c00208040350000d400d10602050209950801000030000400603890410042c003c0480580070003094200140c80d102c52041c2061440044030346103107800c612881541d15040c1c44503951f5501010034101924448400f01d0060f000314000c01c40c00b03130829400b1000580061560380c000301028800c010003801036401102250030403150703201c010382e000e46034040542c4035150204001c12041c030f0f51080010052202000c1481c0e41000c1041c1405c0e079070045d0515142c42000341d6402d0140001341c0e030190851103202c02070700c04039034207103c0f094a061095000c5940c0b5494005618a01b00301a0000862403034100b0003040135150006000300721450a080c070308504031000400c0010089454943e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 203941978 1250 203940728 203940733
    0x71d090c070203060403030510050a05090a09150c0203090901170a17190e0a0905150f03070b040b07150606051902070509010801060314030310030209190207080c1b010503071808 78
    0x45c8810140c0640005100e404005000000070b555a8204402c0008078440d10b500410300d0750108000c440d65030400c409040c000c2c9026441040074204220032107000746502c02c0140c0011808800c00d2030408a151b004156170000c07040d0040d0401d10032034a840c0001d00050040300d0003000a030f007006400065681a4200005030344610101300c030041c24000646844a100300440403000c00d2178030722031250502650240081106030006001804403010560302c0c102c2c9c1c58462008001450300c82c100c000e0014180551000e0307211415440c2151000b0403083c144c281003810310405000e2150701000361101080e000d03c444880d05071040c416801d00d11181c0000340c100001c240041403000054100034102d80c85090440d0000320b155030019103c0c00203440080307800342510000c10143c50504030f1a9001504460095032800c01420414101c4e40040c04c120356a22010a2000c030030141846040c1846098940300c03805d81142d1f400003400c03880010241d60500440c0038401707030744c614110040b00180036800e04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 203943228 1250 203941978 203941981
    0x5030a030203011d07021905010603060203010816090e0606100509030a030f020709020306090a020c0f01020310141818030405040204081501060c1e080c0123071d090c07020306 77
    0x9005000c1e600900804040c0205042001008040c41090b42d1191040c6e5001d40b0f0b08581e807451584c072032401818291070075034a036440400403514a200071070007890b8a0b40180b040780c6010a4058808030f0a41c011a1450701c1c0680100d150980401c403d948030004035048400543d840b142920f241c010041241c0d010701c2100101020160010000a100319154080b00e81346540c070781580301a80320480e030b0203030090801408150f103010130341c001d0807205225009a40d00d003480d141da0642282c104481184094080240c100b06990300c070768082c4004d0900380e0b000c0f48030750341d08034040641103070207004140e09980828000790202d1052003a1000751000800175035a40b580c13428a01c0c4d8415110b0702990346000c801c400041c0300c4d4010700b110740410361300170310042c1c118032180a00e0b0340c80d82409009990440040221580022080c0324140004034401b00e61035908030b06102c901d80f41c1c403005001b0002e02039180700d2400103010100c0d0f00c200c401402c407081209541e864109913010700600c64020b406110386070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 203944478 1250 203943228 203943247
    0x70e040906090b0702060c040b0405040b1c0f020a0b040320270115020a050a08030604110f070c140a090506120a24090206030a020706060f0603020705011d0d1b0503 72
    0x30402401031340781e58212811503d40c0d4584041d00d1145100e40800e201081100700680d040980103648007210040441101d000200d0302c5d480031130356810003190321050100b200011480c0c8030b00784001402d1901c100c0d0f802d003815036841040e405401c503140341e022100c05d0910802550b80d10140354031075010346036070305240104c0c0c1d85034020900203020f85e01245924900000107684005403100410b070300000244483d02a0f41c0340c50ba650b500c0034000300c1e001134840b010040c0c01030b9030724024040d699284104903903465882c1415000c505c22030b00000070b04070401d0795480ba00d075104801719013582c1c1c070500f0004071030729201c0001e620054010090002d500601041a0920009043c561070b01080024044254031040c02d2410032240b000f80003e606c4082400422046031040c2e001e000424418140003864544400307010782d0500141c3d001000080d000900b07a02000828091582120b42e031445040b091203c40380350782e40b208c0c0e907011100e080260008200d8140d8041d8032000f5002c2c1c3c2c101c3c0640c3c0d078074030041 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 203945728 1250 203944478 203944493
    0xd0b0a080115090504020d140c06070f0b0a0924020c061f0b0c100b040b1806030c04090b010608060d060204240c050d0e01030209030105010806012408070e04090609 72
    0xd600c01e40c1c8088507600c00292100140101c07417103281e00030100ca50440c8290741d0490b001403204c00c504824460401400c2594035224010484c142c000c064840d2200c110349045044d001004080319103030341c14008140c00080403020380000904000d800d08072044000850840203018607009180305200d40303814016a04003004c4150604001c014403000b860b40c450190754150b11442c406203000760711000040c050f0f11080d40c002c5000c00340050000c03aa000314000060310b032900b0000d4080b02d03200210240b200505c0d0420600e071001d0f40c166801d00c1422481d0702d58440c8008140304a20038070007100c0014031540d440f00b11a000280d03026070b045495a481e03a07d25000c2c0300c0440c13000e264604a40b80d0b02e0140600410b41004035903403060080c0019480f4140854000560071100c40c18550203214010b043d41c0d0a00405010702000c00c010000e031341c035105203a0702514001001045400c03030816083c00d0180e106810300c1d8000502d007001c0f15018009000700b4001e15503440d000e024036150940c05000c1203241e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 203946978 1250 203945728 203945741
    0x20d020d141501210506010e0d0308180d050f0702040b0a0e04020f060708090415050303040b1801030c080109090305070b070e01200c0112060f2705011a0d0b0a0801 72
    0x9010a81030400102c0d0054500e80309681c9081c008919601e26094544503542080d5804003041c9004452101d828001c10b0f2400304410040340410066070420818008511903c440b510b0000000c01a207903000d080030f4028450030460352460700001540d4010740d22103400514000b000605920011030390755800e02030300c980a4038202c1c418500c4a04104151070640c094070800ba400a0442d0301d02441001044028070344c0700d0b2a11941b00d4625800125581c040c00504010038042d501a40c0d2041d00c07050180a1440040e242c5050626203180d80311080d40c0b086405066903225540007841540c641401c0d202401380c100002d150072840010044103d0f4881e1008000d11000e13240d80d000b000030862005800364072503940d440c2c180c4c070200e41000150b200d270601410001410f000058000d4071074003903003240c03880c070782000003981d0342d07800c100700c0f002003080c010000c90780201c40800540d41003080040c03000004040c600c030f5030035011440c010500c050b40d101440d80302d0000e00541d6038503561005540640308 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 203948228 1250 203946978 203946991
    0xa0201060b0901090e040302010b12010c02240f15040f0902090a060e07050f07020405070c020102060c040f0b0f1605010506040b032b05160503030402210c0103020d020d14 75
    0x30300900050340440081070b2409240140c46003104c6504112800e407603508010416000c640d01c480c4810625150801c0c90b00c0340481004c004034a0205d0f40780064a0b0801407401c5c001c803408019183d00080d41c0032120f0980000140340101d123a512144401c4d540000c05045003a8014079044d0142c800345016405100d03010b1081e6802c10459860180c3e44d81203400c10301c9000020b00640d0b0014010900c62001080c3c41076481e25520306050b4542c002c60101e070412500760003c18841c0000d1010741d03804201e0140c0c0300c012080a9840c140c10814480c0c69203515100300701100da408500000c1640821040ea52020740e03140303007000004140d042c41406480140c40603800780340ba1942c0d01055040102c1e200085250b480e04901944013440042d2001103c0085a04100f0405010186900070300c0207603140f11a00450055442c2c0c2000d004000b00d021118070388080d098001000f0900c40640401c008410200908006880d8160020203001038032903940c60000452603c00111351101c45420355500409 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 203949478 1250 203948228 203948231
    0x504051e010510170705061e1314120a03140d020d0501140604140d020a08060a06060f050a1b03021c020f0706030b06042304020d020306090f130204050901021605030a0201 75
    0xd40c4c5004029062101d4003400e0741c0c0740c0040c4000d00a03818403030020210780b40c2c640141048400d0011034009070f40c01034640c1080203898858100f00140441000c100c005c0c200310b440010303000918041994501002c60300800380b02c4100e07006501800c8a0b8195429001614025981c41128241c140b00514090084a810785078000b40d000c89404c00da001c0d182600d20580b4642c426440990401c10203050f1810100d82c001e16504011840d48420301c1014007421821001003100d50610b60080d040414280c200c008124041c0b008180c0f00340c0c081d54201445902c00413561800e12a41401ca0800c2e228601d00b05285c0305802010f01c1e000c2d400280189115105000e84550a85074a0300701c055508003250983d2010089c48180031100e4a01780c1940354116615804e080380d031428010034181d820102044080c2540031080080c03034140244031035800306d04082c20108600e0024071100002c00e204c100680659900d00008064120941c12201c076065004600360701147c0601c3c2c030a90304e0380480740003401035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 203950728 1250 203949478 203949511
    0x10f0504110109061b081e0705070807060503060603010b0d1103070906080135160e22030206010b070f02031203010303020d0503090309011b020424080a02030307060504051e0105 78
    0x203172242124101c2c0200091382000c805841d902c0d4a503e07a001034aa11400b414003410710f20340c02d44008010304910307224001a04640d850421110f0600d160750b4403110600408100300207603a45c0310300449040d9014511f9184e00c42c20605070b00c400420510b030b50340d4640c05000051040c07694000c51041c1c1121025035880259a0300c070031018000003400c90300d000002c0494a0f01900c80d04400c401c550046c08854100c84002c091035944218000d0550f0207030020000074810720113840b040c42d860464000502c025020540142c0c4d9009540315414451203941c000082140800c0100002030f001080f03400070200c941e041e51100c41c44500341e000b03102c12030240c4a40502080c009000d002682c1c4158000700141d0700741800c48c0015503020450b1498600c4000d020b051101c01640c407440352544a1610a44030500100f1408e04210101c84980182040d80d001d0291203005a40001c1141c00d400d911203000b1500d0344862401500c0d100220180b1450341d03043c1c1201001c0142c0541c00b40340308004a041e4542034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 203951978 1250 203950728 203950739
    0x1806040b040b0f21011e06080c010909180501140708060a030f12050c0f0609010b03011a04150e04080a020610050d06050c040f09090510020f0d050702010f0504110109 73
    0xc580b1501c48441d08000a8009a0510b1a0110038260405000c002038603040074242041c0b0308513002e99840d824840b40302109840e80800c1889004003a1048100606600c808140007801085007449000902d41d00c0c1c04264405600348102c0c401400d600500034041003910950704011a40200c1d0b00100180d11840000c5041ca4062910821031b0742020a24103110000d840c0d650749030715428601424440204840b4202040c10828a080081100017030469414880072243c00e698800410922980c14620f000000310440c2e0115030170880c2c101d400180b55008100b034458443d02c02d41c807511b41601c1103000c10050010380002401001031a6033070f80d0351503481603140444c081050040f160001c40500c440800554981e1180c2c6c0c02264000c2aa4241b40c2d907141c00c0381c9084415000303031204a49440600701044010080450031440c040b20542c102070354881507882c80c1c040e0086565056840b0400300d45804d0007944a1405d404111400384841e1819090820810308404480390001c4e0625500055 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 203953228 1250 203951978 203951981
    0xb090402060d200304051b03010c020c040b0409080c0304061103040e041401060510020a0201020f1519060503030a031e050705032a030f01031e020a0e040609021806040b04 75
    0x82940d00401182c10003510064003030090a01e400c0c0c0c42c0c500c0981d500c5900c441158440503500ca41d21950060548a22501d880e5050803c0418600c0c000d80c1031100076032406070045281d805500d4161030001e601c00210b40010080c054a81c0040c0c800781c00090b100d500700380044010029541c40351a5030244102141c0b03115602d1099100b2030b880d920802c80841e0009900c81c0c1c078200b04418410001c294507840e00d0000d14010300507150200541d209c001c0c40421942c0506c800c840c84080c03440505075600900d40301c40c954440003000e80072240f442d008040c1d01c0e1001e503170140b4080e04000d02100d40301e00380c0440c0070380101114074a903000b10ba442e00082c0c117402540d00603e44507498907030700c8070306544844c00c0f40903505482001031417044005503402c10b4600410805180300325a8005684400e5141d4245001550707183c2401588011000f420100541c890340384032011540099011482c0c1e03030b60b5042007402030183c12402075202425921044042c190400d920740118400c640810070780400070100070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 203954478 1250 203953228 203953231
    0x31207050c060d021b0123091c0c0503030a021c0b010c021e060315091803030705212e0e0c0901030603080309010608010c052a160803030a0b09 63
    0x100654030120400d000760070054060008070041d441d02600305030700b40206440d0a0307040300340060030360341d503040711300e800c0c1c05410213084114003811510003581055282070b41c40d8140310484e42a40444480e001c6c1051348214103014065030404141d9489007030510382d071310207944240702c50550395540c1800032040c1c03100b81c441c40b000f070300d030584501440700126804c0c881c0f011006a42c40d40e50b01c10034440100d00b521444021440380003034550900b2607504a800700050100007902c8084c0360a401c014000581800004403904440301d801c00c01d84803031603a1112042c0d45a84940500240e1000701800050004008441071580e10f000c0d025408694854903107416400713a20891280141c08004503040e240554002c2c099054181f5022455644a8940d4030950740f0603602d00c01079039555403080051100a10404150f0700c00e80c54024500000066140e1207840c00c1c180d0b480070508a068207440d08442001180388092641c10908102c2d95a24210354983c1c10440d00142d54a00f0448a14810724042c030119 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 203955728 1250 203954478 203954483
    0x1080105040c0f08040c12030305040c0b040302060406050715110721020d1b0606030b011703120406050601092607081204060507030e09040609020102100507050a0e0609090106050306031207 83
    0x909000700b483d00722140301300544140d41e0b071494404049042c100100c0074004450203a1000324541c2081d140c140d454203000e0380f01c14860300041c8002d02c01031b51108101c03030450302c062801544418a5042031021180120290003000345005203021008030720303034043c1c040c45020350240141c8000103030711441d0000000246100507003085000c141d08500901411000781000503034031600d15450f0351010201c89158106440c1611100e00400c003c00d00c0030241e914102c3c0303c001550400d2131120f9181803010000e04000c0115407a400010b0540c0d2244108030010708506659007100b801d5078012003204901100292054080d89801242d46071002500140442886500610b011319200f811a516004880c049007007050400020080b0b5841519107401140654130001ea8400e440c070005e0310700489408619440c0d41048200006560003005071101302c0301034106034402414000008106200d000300050b40034030748500100f030641d0b109000d9442070400b6400c0300e81c140000c481e000d110b80200c06c0700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 203956834 1106 203955728 203955737
    0x120a030219081f0608180109021e010908011e090c08030a2a020916050403050105041b050d2a08030c0f06010b13170a0f060b01080105040c 61
    0x40c03038400040307282414840349003200285c40340741d0007803021001d001e11002ca00d89002d004c0d003001440d00c0e4002c00079034016a480d190728105021801125000610b03180b0085403141c1c0501c500c4441c00c488241c240702ca02c40c40b94207070f40a000450002c0310942c1c558800064aa00b0800151090f466540c0341c0c141d0700340f051000003c4a0f420801052030a29443c8800e00160b00c0d171111198100c03003c07400790340a210701e91206540d144295440206590b283c481000140710303030205080c1010008007410481e00342d03902d0030041d64442000000e0b01106c0c2a070100d10721400c0c5403a5010460480d042e000d10400d5071601c40d5401c0d6002103015130901d400c11001003d20010030301c5114050700035a03036003d05013100500faa2900e10014062403030a1045401c40340000c240402c00e030b400a40d413040345030300401080d150510240c0403440c2e8690100307503800c002164034542801110000b03032290340d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 203776978 203956834 := by
  have h0 := BRFrame.cov_init 203776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 203776978 ≤ n) (h2 : n < 203956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
