-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5472
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:58:23.522911+00:00
-- url     : https://prove2.me/submissions/eeaee43e-1aa0-4861-b7e5-0ec0740c171b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 983992805 ≤ n < 984172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 983994055 1250 983992805 983992819
    0x90c060a0e10020601030b0c13050934090b0304060e1c300e1213030b0f1501081f1502060906090c1e0307030302011401080d1202070501020702030d0e 66
    0x14102c1d4070003d882810b03694040011036107520741040c8502e544c0c001c03010900e0400030102c00400c80ba01c0d0f0400c03140c0503204402080710880c50414040c1124a038995005c80da07614070350003641000394800f0006c4110341c00d012816139662200d0515130003030030001c400a402c900c50400400784014034140b00b4a588110341d0703208001c07000e502c0710300700039125009190411142d01a5003007101c4206540000740d4102c003602119090141c202070301c00d85d90064603c00f030001c40300c0b903010018490044001d541c88a4a81074981e441e2170101c941e105a00e0100100e0381c10040d07804001441e04000082074aa0380c0c01c40841c0500065603222802c084400c484184401401080003003a0000400030b401030041c0a40d4010703045407181041844103500394110b010303803201c410f04038800150701c0902c600c0c1c2c081e6000c0d60002c40d00d8428560101602001a840b0780e01e598844031035101026803189181000c1b04c80e0b82c5e00966503403024103100c0d0281c040c0a00c040c0d494000c0d4001030008981016001888400a071101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 983995305 1250 983994055 983994079
    0x60408120f01030809100c0c09020a17012d0b0d0b0a080a1203150f08030a0f020d02030d05060a09050907060e040207050c150714030c0c1215090c060a0e 67
    0x1840c1c8560a1000034880c48091000038a03601c2c2c0240c1809100d9524034095044000799260341c041e600c02a4407900e0341c19400030b0172409060740614080c003041400841680707954940000002c07071442604174841103034a00801e80302000717a880303c404001c10702650503d40300d5440003603100040188100e464130500421000017521807000c545806030540103903107903d103840c41201c1a40135040440e0210b81c503031209800458401c988051a1000c1c04a000c0215140c0c000000085c0004c440c00c0390942c1550310120070130113217590010071a802c10400b400085801d0300c0b541c0200e1100d580c5900b100c00c41d50704000070404c00d9000001c0c401e00700c0e4000d648101c46ca80101c424442203104c3ca000207800764000101e501440c1c182400d000304400d01c8404558034010090300c40081c0000094044691600002010414064200b010800c80d400c1124103031089021390074082e5070b50030001c010440c03664281c4005035101009200210091138087c0c8115036030300c8030810003440c80f6105c030410740c0320350a1a844 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 983996555 1250 983995305 983995321
    0xb1b0d140a0911040b04020409020a05180d0803220210080915060604091e0e07080606060a1d01090f121b12020603151801150e0303040b0c0f06040812 66
    0x24400c042c0d400c01c0380e80218114036030500002d003c200380380a802980030440003032103c00b04e200600170b40720f035551101e8482543d01e00e00e4001c0820300c401c05204590380c0e80500085000c1c0d130116900f080c40405880c000340c04903600101c3d004900d24002e507100b0340082d98160550380000040344101190300542d40c1113106002d2404040500b5500c19403ca81e00344001e00840d01140d02c0254203c200141001007040700340c05103401e0f40e03031a0404c4103085d0041081000840010860141c0108048030440e04041b03801c003005020a0b506480107a000c46075081541d0700d64050b0700c040d00509488408e00e0406603c0d60300440041c5113850301110181000451040300003400c0910006070b0b040c01c00304600d0f81e480c1d502003143c55000507090460115442070380801e10707542c507040c1c1d1100031a0054104010f42c50404c0c156410301900000b40140303c161900e620f0551b60210449080e01c6001d01d800340c48900c10a0b00724640003000030384460901c034803010f00041c022450f0152190509182c04280c4544e07580172 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 983997805 1250 983996555 983996561
    0x909030e030a031b02060702150403050f03030603190f051c0e0f0306040f03091d060112020a080c2d09040c02070303020c0103050a0b030d0c03021e06040b1b0d140a 72
    0x1001c0c00013010748400c0c20f601001592141d810600090102d42401041d80008090b04481004030702c546900140800c100141802001c40c8546518040d506514100e40030a0305c0712408500840141d8940d180c03e001c202d00f0102201149400408031024000782f00e840c10112401b0b90014408110b003650804421300c3c0200c0d0a0034001c50180c0905000e40f215a0380d02c40c400a601001c50501081d00404138071040000846500520040b2115070241407440001d00824002c2c4030030115540104410b001258110990a400058102c480c40c0d89070322a0b40100c81d401006040c0c00c401c0c0714044418859030418002400d47e04008840c00c004100000006907681c42e80c1d440014007503004142c061500b58040d07407015511044180c404603c100c88000064108010302c180701000c2802103003000e041c10307410031030301209064110002011880841411781d8a03d401007000b009143c5d4200000d03a807140c1036031070040c0052130006040c0c4034008560700d10040e060460440f4048401100004c41d5164030380 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 983999055 1250 983997805 983997823
    0x5011806060b1e1602030f030a1206050f010c02010e1c0c082a061201030f032c120304090c051c0605060904020c072309060409081c0b06040909030e03 66
    0x1050f145121112991903442540155048100014141e144a030140e2801e03ca9010000c2000003c5e40c0d07101000100540380f07101c40c0741c2c6003444034039005090180361100b0f501c0801810090a182071030f10b40070700c0100c0300c1d00055042c098100a00020b407044640003241e466421314883c10f107210f2500d40300d950342da03030303a070f84008502c000d04104c46a101420350111080320038110003d410b051a0a8008841e00d080110a0348210f40300000748200c00d0500d0351041c58103170007903040c210880c4e01c500f10040c09039a04c68541c3c0e4281c469248406038488040742003044400822103003105026030a800c850281c261f40100c544450686254600035100311042d04c542000d40344d00600d6142083c07209801d2200075042440c421443c1c0c820643c01107189130444100000c140c00c40341200d10700d0170130701003030107888400a00304038007581c2098400c0001458a81c16100000c0c181c0140c1d06181c82c84002c041c01401c401078480750080e40001d03002c40c404c1d00b5074000d814624002c0c0c80d01c0602d9810315083c159180640 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 984000305 1250 983999055 983999077
    0x12010606140a021917070308010608091c0e0a080109050601031b0e010b09180a2304080406032c011b17011802040e0c0702032104030204110705011806060b 68
    0xc13804058100a1004503001103405240b980024908800000103281d10155003074000c035001c1801000001c2e0301407656a441081300001d402090080c070541200b41c4040c10f034003424030038202e5954409486684c000c0f401080100020700280300c0504200d0380340c2d40e0a01055807584207510015542180d805514401c641c2d00c8221415aa8a0640d080806402c4407007159400303104002c034000d00b004040ca51500031079541d08001400d0940c12101c0c0d060403030b04401e182c45000004104004240b0200c180c404454040c180400d400010b0381088400042a40751250742c035002103000d04441805602085104241000c8495498004041500d950782c2c59104c0780481446000103121461088840c0d8200082007200941425268043c506020700203d40c4020001c13008100d0b5402d501c3c2c1008030b5001520144058940580072214003400303032280d4080680502d4031040c590403000586421102c4458001d002004440a241e14200f01c1c110042030566486061010200b21040b844045030014104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 984001555 1250 984000305 984000313
    0x3280809060c0d0905010e0105071b03021c020102190806011d0d14070807060203090310020a08041b0509010e0f09030a020a0f1703041202010e0303060d08090f12010606140a02 77
    0x10b001d0281030158800000707903400944448242000804c240904040a401c0c0b9002180300d107001d0708010140e19461060300c441b000440d01075004039802140d807500280d4803241a001d041c01070a011781c0a4402c004462500d802c014441001d040e03802690607000391826654182256100c0d1035001c000760110781c8031540038508145500c00545042c8040001c01d078071400f69075038542d980c240f00c0c1c20016154000005a04002000001d91034180100c04c40e16046800440c1040c5c1d0140005203c10350080c0000c0c80380941424104a21014440b000000c000041c40c0c1d0201c0c0d0703100d40d0204500c5074155103081c000c5030244085800040c01000350313035030714500d64000d01c1c007442180c441c040e2403500040103807500811380d08491101c1c3d00610007103121b0780c014110317144161481c51000b030031606c00d00340010040e00300b4418406560756284508800c25045030405031150141d2000803104100141100e41c1700740c1841450352400b40642240301128401d4540c0e9501c60b125078003054403403040c038100c6001a00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 984002805 1250 984001555 984001561
    0x1060f0506030a0e030d0209091312080c070b100510020d0e1908030304080705060112050304031502130807090c0c0c120312090b0f060d0b07050307110328080906 71
    0x80c01c0c030245034061603001000c00c141030072200f203600315440603026241007500016142113070300340311181340e0f0021010158414020314a84800403100060091407080020340e6001c40d031460152016105460340102c1a80154108444c0c060038a46d4544207960198010940500c80b4500218030591100341c262201139048903000c3c00c00903001c942c01001c0d44041c900076030211f1720400c200003651040c1d1241c442c0725590246410a03925040c1c0580c001400034410459000003e0f1000c4141c070b04895000d40e8501e80c1e4a1800e1032440680500c02098058048290001a00c6180050360104482d255281003011602090301103d00c1c42c442d100c00b404007241f80b0001c01451581840c030104460181c50044640d695000c00b07142512001c06c0103886002e0160b061040035022099041e0b002001204c40004c80f40c0700c0c3da54000c0030305000b070803c1c081c06030100010300c2c0e8034001c5155081107d01d210a99542c0c58040c074010400300014000b1442e8107900c829000000e50140a1540c0200c603030b90000c0c842d40d5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 984004055 1250 984002805 984002809
    0xa0f03050a020417010203150604290d0504050d1e0531120b060909100b1f020106090c0207050102100b030a06050405010b010e100e04110f03010f14010201060f05 71
    0x1090180503091030703580c204000200b442ca01001c03080540e03140000903a03207041000d0440e000a41c038011180c802c047c10007040203010101e07280445a1702ca072441c10426140274403900301583c002c90301000b0300d05090608020403c4808100810b94450316250030444021a040038910824021803403800315108014550444099031001d41c894086c60b00c01c203100c000e00212011101607a540442030301d0441e000b403c420401800380c1568009000e50384035415141444440780c1d50281c00200e03049080d030f10582d4040c640c03103e00040c414aa141c003425810140e4609009008242911543c5902031030711300d0403294544045800742c11590140e0082c0706048080400c00018a0118629a4144074080c10f80740010454024a48a1401100006440019000003501441140f61b809201c1d209010181074103039086182a0b100d02e405503000a600070550056003443d204100900e0500c0d6000300000402e507007a030b007614081d079005410901c610400a401a4242c0e01030340034404540040020a001034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 984005305 1250 984004055 984004061
    0x60310060602211e0301090e0a0305390d111902100908010903030605041a060414010212070f0201110f0303010b180d03020705031209060409051906290a0f03 69
    0x448003140140d0700c4d05503a40100a50a0200c0c00400d40441c0048010404080c05100b44400b01c11210084c0c1080c807038540e0000d080d44601541040d05205242d0240c51410500c00e0300703400d1586000202061000c1140da0a6642d44e510780d4240003d8101210307210b1442c0b000c614101042080040d540ca811115070030442013642c220580d10421a000f5030000d8003e00902503038135064080d03200000d0080c00c00d4140700c250389030030b109071010845002c012182911488215022034080003405030184042e10300413405e00003a00e0305842c55410110b00b5030f080c40924010002c078640300341c850383d400c0640481001d0701ca004000070a1401e800a10040011003599001040050790780c5440c01c801156840008a10b843c440c0320039801a8003603c000d00480c141001058080701d0003407845420a05000001081c1e40b046010f1504101e482ea80840e50951080240c0008002c882c1000e018190f19400840d001544c0c590084402d5602402ca043c0c2928428007110030100040d070b43ea0014100200c8140c0c05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 984006555 1250 984005305 984005353
    0xd06050411070602030603190809130c021f090506041b050d03020a15060b030717070507080f1602060f13050d0302061b0d0e0f011a06030106032f03060310060602 71
    0x140078403c400c3d0004411003100e0f5003409d206080d030340e85134840c0800740301e0844180c00421000505e4240f07800046600040c5403088596018160089116641040009012010310007011442400180010061482d801240d000c441102008810391355600300810740d0102c80c0c2c050301603000380b9440c00c00b046500394032108aa5206d8800b03e070040e942c0910500a03801200c1c1c1600041a5a0742200480803072000c0e15040a07040c90030342d0800c4c0f0710b07840d02c1009220710303c1008460040082d04511516058000e01c40c07260f002801541c0300c08841514800030b6002950501c14a1081b020110f4a86400b52741c040059405034001c02055540b6061118151481000058a940b0070700507003401650a01605115040803000740c1014000d942c011801d42c1d40b1507461600e140b0042c0544003107501e5040c00c2d030b41151118600450a0001c081c4075810b01c0c598405e00e02900304c20280c0c551920394030540114010f180c00d604684c01c4d10070f14102c00c4201c0d84180282c40058203c00240c1c449026840d240d461 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 984007805 1250 984006555 984006559
    0x240c030f0c110a06080a060e15190b03010b0406090b041409270c090609010b0a1d1306050f1f030e1f1409060f01090207060209040609020d060504110706020306 70
    0x1a009042c08002080d5140c0b540c8842c0c00111014200a00c40c44140100f03001000d807649034680e81e04200d4102c021400404407114040d03298540fa400f885101a141c4d0401811111607480d41ca50b11040d042d012507100b40074500214407041400078407403810804075004c07104c0c3c4c001c008030404252000c107c4a2540904540c80c7c0c0410040320180941000384030380030500700107005100400310401802441c00004281501c20380403940104030501c003010440718540c2d21341c60511090004006410716600b003003a40150020329840b92240070706030781e46c0071701d003034450445000e200c08801c181040054160250800a04030003184480c105d40e020713800280100f00000c0039034603248035200140b007a00171981c0c0100d1400762141c242181032080302c0003807500070303121401078a02460b203400342c1042290180304803010943d0000d04413051021646c15100342900c024400d000c255542d01180001e5003001c01b907605501c0c0f0b40390b070004131850240701350307002040000a541d08010507926144001e40004106036 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 984009055 1250 984007805 984007823
    0x1101021c1407060b0a0b04091404020f09060a030f060203041703040314130b030903030a050c070c060f120903030506040501091a150412030f120e060f040c0f240c030f0c 74
    0x202560b541041700b40141c1000c0d15550380712403500110100b5140180013018030904142e0903c00580c841580144041005555402c12600d4400c081171a4030259407000d001e0320604c10200c030401685030011402180070f0034001340300484001030300c2c40e54032055400602054428041600703000e4500c02910a03c20b40c02540ca5001d59244211174440d881200da01659404c0001003210b010311900c91160044c0503a0100703030500d403c0d0341c1d40303c884000358011203040c407042072842801c042c801e602c2c14200c0340d54281d05100c501c006180c081c004c3d020580742588107904090001ca0038900f544550145003400380143c004281c5040c1c02d01521202c18041441e24500400000c102e80d0b0700101a440c1f554429aa15040307043e160740c000780036a12851940440381d00b01101c2c0e03040c0540001d82d140e0000c1007000c400441340c40728600b000301c03510a6880324003a01c101400000707001c90b0f1424035030038040d80350304d40054684040f0300c100d40c0e44081c000004c0204400c44003400e00e2600c141e2105018500c90f44044d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 984010305 1250 984009055 984009071
    0x1c0305090c0d081e0904270803090a12030e06061009060509030f03070507030b01060e06030a1a031b011101150e0a090602070803070e0414012c041101021c140706 71
    0xc526401007085a80031355000004904110382054070a034640310030320044194081c5064400200d0848100c0c07400b4007162004004146546014440c5080c00d6510040340f0300742c0c000c820b1018010b0038014030840098020f4a0000710789084c07040142d6440e9045070390b840344880c1030100c2943e4942100201a0b014418500c1010b2032820402c014580a80684000d18816185143c07503ea0a4030503080213080110900b8644540c1e15000103494010b40034072004580c400d881400c26020081806c160380d49031003541c2d03071034012070a03030461081628420b070780c0c3c4145840c5159545090b81d1160b07010201e1810706440070450b90a4000d4130303a801900c6074101182ca070910f901c41c007045e0f0300130880c10b850a840000522140742d0b0000c40c080440c15007650203008480000e50850100c9005100e02e43c44c800540c14582c0c91160301005c200b20324001051004400e0809091007420310300142e03046400f52260255000300084101c01d000120061a62010f0b5050801078914550b0b800c015001c03908980c40d6000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 984011555 1250 984010305 984010327
    0x201050739030908060c0915030c0d05010306062d03060e031908010e06031603030302030c070b0901050a0b18070e010504090c030b040b01171f0509091c0305090c0d08 73
    0xa0740000303010756204080d4a0510100e1800e2440183c951000c1031820442030546031100903142a0041490300788948a0707507081c03049a0b0a204034200850101e04d06400402000300c3c44d40301c0000e4560b030980700c1c0208101c2651007915500000c60b526402c5100030803c0000607101d07080a070300c0001120650303080039902016072906103c441c2030300021414130b030300612032484044c0000e40d00000460040c0800c418204952905441500024041503000800150b040d03d0745002c0714105d0340d02034044d103e10700c1c284140c1c500a10b402e407103038022903080046950b09480e203a83d1000401040890410301500d6401c0c064851000007a4602d041c070100b840001655180da11030091400020f442c080b0350010600d04100451718100411414403086000b03101000d064200300b03036441924603050000804171041d0b4801070084541c003095001100f030003006030043c40480c000c056500034000c810070315044c078101601a00c00c200c806c01855031000c183c401c07862510821768071001d4040c500c018a880d900300c00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 984012805 1250 984011555 984011657
    0x605041a0304020a0e040b04020f010825090b0f12060f03030a030c123e22031712010e042103060801240b04211506090e0c0102010507 59
    0x1d05484502a10042005608008014401c0340340e01346018160751030050dc11900d4082c550703019549120328050241d82c5503000e0120403010381848000381d500c50320b40e504068030076401300101c4001500940081061400d0084405a40c004001e010f5070401c04d03002400c400504d2100411010004003401c00c50301c00c0c0c034510075004800c007210100c40c007a106000440302070344a0359018100c0d0342400b03075241444080321410b540c110918206418011415003599001600540d00090144500e002c121510400c0c42001002e601d140c001c0b1400140c0c5c0e86d2104202c51031001c440c00303462480300d843c6404139000b5003020440001c0050800103078007030300c5801071400c440c0c00008802024040c3c0d0b41c090701001801d2070a00091190454140c40c05007000001030300800007000c84403141c0d481c1d040690800c0203240b40007024030100b49081000315952036061002e01030041c4007164a0264200485040d48180680380c46641c0340d4880403c030300740c030704200500c11107911040b0140001d919800c5010909400c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 984014055 1250 984012805 984012811
    0x30b0702250305190503030a0b0609090a060807140d020f0d060603050304081e2805010507030207110409020a03020f040f140603061006080609041707140105010605041a0304020a0e 79
    0x5500600460300b5864424500342c001c50000e001c08180318031030000134a0000031698014400c04022031010041008200a4092900e00c1544901c40340c08004c40342980e94440b008482601003246e00c0d655880201c880c1024540000a4201c070401c00302002604100c018070035000360180c401408084640c1718202114582d4108542507040040c1c1084031040070048600030507803d1a03200810540d11420595407580750b518005600d00b026200c2da04802c42100560196030004000e0155250062006000790f0008900301c039032490300c5035601c1640c142032140c1040543e01400c451401e5040d07808022805803072005d220b5015440c0d5400e0f140c000700c1401a110420f20345840301c1107506040c0c04041c00c00c0d00060080e04980d42d1850100f041d2984100c001d038004000740c0700c0c00354030b480f10b00785610b1005400e0b1880360042000580d0740f0800c240310f4110010405441e001304401d90300d8045c225490301c580e200340311031180640b01d00c2981240042c000d41c1c0161008007448801e07942c034000d1902c0304c4400c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 984015305 1250 984014055 984014113
    0x13050a030f03050a0213030609060905100510090c0f080901021303060603060b0d080706020903031b03070605010f180b0310111c09030f1209080d06140301050907030b0702 75
    0x79409604245415008071900080b10702425810940e11a4000700c00099a01c4080c11203030701e0300c400b84280003056100041081e009030a890800743c4440790030307002d00300540d42c41026208280c800035641c40144183c8100c00d490343d8606481200e5404202c80340000a44680082d55081008040e00280b9000620055104000200d4200d146080c18421101c0e4801c8440c007031030240303492100140c940c10448040310350002c40183c0b2112030f00c1c0441d24502417441c0e1502c140344404c404592144001014048070b51280a00b27106581e214085101c1c00b04442c415501c10503580b840029208403660003508810002404403040071f02d100c03207144250b9002c1a0041e40300100000d4004841c0c000842d246820342d9a880c1c10701c040c4590380c2c4e009041086603803a110800c0005070b540c800c16880c1d40c000300c0d49a50401c40c0c0b95141d92420589034001d2805200e180115100b0240c4040e850a060246a109e41280d00280110324599100c140103040c1c020070007000c50040c42d070f6940080c114501710102d030a201c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 984016555 1250 984015305 984015317
    0x70f0c030f210b19050a0510051903060503010f0b0907050a1404060809070f06050a0e031009051c022808040905160f0206040f1203020715151d0a0513050a03 69
    0x880343c184003000c101c21007290072160401c035080c00786840e0015000c04039a001d45118803170b248002d0045896028014850a4411005c411416840d034150896402d031001203000300540c5c02403098400c11610b0548000b41c1159005000070011409a0701800944600b0f0420f8103c01186a454a07120790160300b251010079001428800040d5040214102900038002e18428480c10600042e260303004030800441008a01c18443c50305032801c0c0300c00700d0648544442405400d40324a0b1181c3c41e40d2201151010f4800c41401d01c0550510000d1146030000f91080400c29120342c102c85a0200000f10006949010042000041910761486030f071b442020325040c030600c1001c004c640141080a5010385a0456001d102400007082001105c1305070ad540c00401c05001c02003584060307010f8007a07140064544843c40c00b00d03001508480e08501c1492051520070240310351622036107100c0c07402300d6040052001101c800210980300e9a40040c0d08002060011a00040d00381e450510b000c4641c0300840025030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 984017805 1250 984016555 984016571
    0x6020d0c140c100c260103060b030d121503020d1401150602031803070902070b0f060102070b0d0203040f0f080c0706091203030908040b120f070f0c030f21 68
    0x250045498902080640d0300600d0042099000341c0d403401807000310f244450351405000f00d200c1c0900303814000001c1649003030b074600e1442d0f40192142182407000f91011801c0450a80300d5260116104054031020385803a0202402d071042e00c1d004003040100044103032105a070100c050703640c024501030618810140408406040c00d40ca50030b59100919030251406100000d20a15030003009541c200030081840d0f002c08520580001d192280035440602210300c00a40c600a04c80d81c0101d640c85030310907990203c447d8507280300490f6175180e03501c80c0c400480000d011a40800a20f0303001107800c01e00074a0803110100b1035489041e41000900d204a0b89032a0000d10060760b11000e010070b100074207950800984d0a841d2004084e1004034071300b4020b08150f642c1c0b030b04804020b40c64042d00d000e028500c0c40b058450305000b0a070f660030030040d20007501000001c000608401e21510a141204038541c1c0e9610098207076560660340d01254404503001e001007801110b002c1e48602c080c03550300d02d05040010072029 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 984019055 1250 984017805 984017807
    0x140f030406030f090b0609100b0406110111040b03041707120c11030a11010302070618030f022820030d0509040b06160b0606070c0806010603180f030809030706020d0c 73
    0x501010f501e03640181080e5001010a89184909600140c2690400780c15034030760400c107107488259044005025804036001c80c0f807a0744101821b0390416000c008002032041d103000318055004038401e04040f06410400180002c088005a4101c128900b00c4c0b10f090081a550324241c141407400010f000400d1647d0020034410041d003a1808c3c280181c02918004440791207000355012105ea07100d052540000c0c5200030040300b45c2c041208800d00c00b51200d109140c40c60700074404801500070100501c60210faa41c90028180ba014075100741c02541d840d0390510960740c2248800b03600d412060508888070310007400e502c00b40905501c03d1904d6494542c7c0380d88500400c400c9850054000303003e50014041e64403e59081005120380a401090703a41043d41c1d08400541c141c031410704001c0c28140c5840000866500006189040e113003151400e0040d07664080d00c451501d090303914050300f420300320507054012038055241540c002c030300b98007900d240100c1c0e6100c42d010b0368002850181ea5940c2c42d02121112 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 984020305 1250 984019055 984019061
    0xe0901020a0914010e0f0d0215070210141801030207020d060f15050303030c25030c0506010905130b09030f0c06010e0c0c031b16091a010f0c0f140f03040603 69
    0x1d40f035000d81610b00e030381001c4002054004000c884600900341400d000b4a241d442a64510405034002c0504000424504418880341c0044000f24050704078008207615450084d410030841661980c1114240b41211500f444d403030017207095071418150308100d800c0158440d4041e040300c2034016072020a01f083c50103440002c6410803c04d4800300340712180d0600883d90040100c0760001c00300310483d51a012172600d101540c808020300910350030003401c482003c2540203071561403694055130940c0c02a03070365032892100340c41084452201d42889800b50500292190307201c5c0390400d090000301e030706220026404040c06c0d4001400f0030141e6003c400100040d0a9a542065120200940c0c0c02d09080300480c0c0701e0340e280107800001c1c4203030344024840040b4000821081c501c0200030030490805035981c5050f0002001049039030000a2400e4144140c0c039401501e90f014081980d07a0b80f40c044008a4488410320404424121120090b00d4004180f4400811120203442404000f4665442c6401400350403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 984021555 1250 984020305 984020309
    0x3090302070b0f040e0a0e0102070b150a0f0b07150614091b12040512270a060f03020c010207050304090b010215090304060c1a070e130e0c040e070e0901020a09 70
    0x140031080042070a100d081c5401d1318111900000908001d0b1181d5000c800034020100d00024550302c04292001480309440605000f4070312034200d2800e0b05280014081c070006c590050810f0310910308010040500ca4600500300c4038050f10204d04050001c902d00ca0554035503512600d9003c000c140007008501e00580b000e40c0260b4801a00038550502010010881c024103690816140b0000001001c0c001c081c000144c45801184240d55121180b1000040710022802e80032021400070751a1000c5050081100094803002d8450220030304001404901960021441602c0c0c1e5400b4000600000c100b080504050040080702241245020000900c1c241480410b01004040701d01480742200780030045405550603854110801c0c01c95040c880b1401c011f0300d2510007950340c0c80040054503580500c480100c0d00e411241f41e040100c0e072420702000d58140c203681141da0340290a800c0c02514290303001040d1400b01c0d00071f40d1052559076510040c0c201003110300c0191a500010809000c1d40c0c80450800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 984022805 1250 984021555 984021569
    0xc03020c0a08060907170c0f0d1b03061a0f09070c080c0f0f120a0c0303021c0b0301060b460314100303020312102111060405030a1118070309030207 65
    0x110017941543d41c0d1f14804c04124500404e21048000505c0d01d9040e000038409030068002d1884024240700200380031914402941c2c0c6070700c0c0c0502c41c801009003078081822464000c10b03a640c104503280070481c0940d400750008060000090143e80024a00300140a82e055408040c000301301c00c9851007818035014910b420303100e412599030000303d8558082641c24100b040d18090258071443d280a40080c03140d0100341c081c01c0c04100c038031218550305401c98040c001041c0c0003804203c1d90380c00250041c0c050200e4103c00c6440100c811000090f001802e03101011a602540244c1c408080d104298190f2261000380004c0d1a07858200380a807080c0e0203d07400131101040c3c011881e02e940c5000f51a8041c1000d0300500c815034001051340c0c03482c00c041503405001e404c400c01450042c2e000c40c4081c2416510b200f00ea003a2600d1807a40c4903442d004007500c003159800740203006802000c0c0d44d1015000c4c0320741c3c0015803010700f542d002002d914255411038896041340e00c00180d419450b0401034a08126544421 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 984024055 1250 984022805 984022829
    0x70b0a1b0302190c020105046e0603060307031406070806060f07081c020409060f090209060f0c010f052701050c2a03030a0c1707020d0c03020c0a08060907 68
    0x900140d0340a000c490840b010756002900701311404054005040b0b100e0b040c2d005c3c200e400c0d161860302c1d1011031480307072940d14610100c44104c0300c0f1082c4083c1215040b027079285180c0c10300000d1440f0b4100f8100866004000130180c41c64a40ca956404030b20300b4174141c0c0c032013142d0b00c01c1c03040010b81600042c0c1c554100c001118604d08051441c4080302d414400d089000740050004903c23115403140c40074050302925082c0c1000d40d12161525100d00003010b003031045030801402e102c0002480150740c801c40300c5180713016250030302d4041900210b41003980106d010220f107650b070302107800c3c2c402c142c1d00ca601c0c01400c030103440c0d083c3d2084600203514440220000001164076102c00e22014020600894821010b0082e142c42c49030303641c00043c03142c0c50021001c8122030000004205003101603a1011042c04140d07250300f05400242207050014000880c4c0640c050307401030010381c00c4580142880b501c000c1c42407040724051129100428411001075200e8041a0301000c144001508144894009816440240 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 984025305 1250 984024055 984024077
    0xa0b180103110105070f050703050609120301120f020109090905030d06093309090614070203041508061c0b0103050c060c0a1401060815011d040305070b0a1b030219 72
    0x800e8182c010802c0581403000004641c010000041d00d49a8180e8000b0300742c581e560f52300c0c14000e88850341110001010300030901404052846201034905881c0c00010b022400f41c0c075035644080c0500c2400059041c0b112029000540103440d001e030040d414071032000f8507100c200c2001e400065440642085e03605505003807030a0031003407111301106001660300401210b0141190340080d00c4856940203000d0813404c000640003403000c0d5800c86c440550a501410b205652000f80882e124000d500a55003002d40c1c554003d4000b0b032050b1602900510007c01c50400c070800c1c0000d502c881140508202e42a0000d80d0040045c071800b0700112094503c240c1e011840c14149811f4a0740b10650600000e010566a0f440050201030950005025002d00c40c2180c800710009445008111004d21810445848c0e46800152182041a0280c0a00d80c50346405d818291f43c0d030356144c0060b600600400b81d0a5841c082c20792000307080400fa4600f0300b00c6803001660b81000140003201220707904c0c607010030300c05607000d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 984026555 1250 984025305 984025313
    0xd081308030a09020406090c050705070509010f060806271e1b0309030904051008101b0e01020f2406030a21052206020114060a050d0302150a0b180103 66
    0x4482d48070b5100e07200050301c1c050381d00c0020300510701c6d90081c04459180400d010310307403a000002410030b140600c08860b843c6550340c0c01c21010754801d01401100d03001705001000307030500a1400c0c5400075402800c001c001000300c440304040a0721180f0984900f81c459080c450b01e0307203d00800d004000d002203030141240c60305007211700805e5002c1c119032500e48400000102c0082042c030580360031510007413080c030940c18011503540103c5401d0140039411b01030700d8150041c1c1507503803080440581001c40c1e40c0301e070a68100e80c2a601188101c0d01c0c2c5042d40030700d50349103081d00c10138020080d030049991103440645840500126510306c0c002c0a0a0207640004403440110303e0400310340c800d01c81400c00e910101c1e00c3c107100440301d90050700c90075052030300754040100c03906c03507000c00c06016030310070f640200900e8441d100c00b0700c2c0c0440d055800703a8000c00c107401c081c80316080c030203001c80040d03004c0d0045451021404002d0a2404411181c03004816aa0b883c41c2055183c9403200410703209402ca0101065411915 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 984027805 1250 984026555 984026557
    0x11010309110607050a140313060810060309020f0a08070618120f020d0803010902090f010806090610030905060f010501090807030503300702060702101e0c0905120d081308 75
    0x1075460300c40c0c0e00204022080240422028051642c8482100742004a98072083d0780d0f500507416840303e040d83c90501058403485101d81130300c41c2407600341d80e00400389000d00650062804050903600700750540e014491036110f911981c0300509090340101009880c0900046c0380004200200c4a810450f5a00704802e04d40c0c00c0c400c4814a8011501c10050480c038400070702440e001402c000c018920200c0009015081a8040c0c039000c0c0b0300781c2d000f0010b6007142c1b0046a1070070702210850351101121000c5005401d10542c807550940190600182203880c5448041c5451012140e030078051040d4030050105582c881e07400d0000300380100c020107c02d0b045990f22070b00ca001c1d0241603030040ca808495840404020700c6410380c1c2d10b160502d00c0c3d106051040307009449d820b0894010015126010030b03038503010404d22507040f581a429000c814051000b041c81c4016041c1000120100042070781d02103a1640d0380c2901510340408000102090959084081c0c5445401400c0d942d514580c0804200840c2c0020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 984029055 1250 984027805 984027833
    0x20a03050f09010e0a0e150901080607140d02040f030507050a0b03010b1c06080a0308090609030a14040801110705060717040206090a090213030204050c19081e1311010309 75
    0x24001c16200d182d40c000413241e0001100ea8160700180c0b5803c002010040c0b19243c5004201148030383d18080381010501004010a04c188241c603440400003821042c81071913680000d08481c1109461314443e400041c2c00d80e007240e048100041c0c00030008204021042003207000810090303401c000c41a252441300e13804c40c0014840c0c0070407403000003040b0305203c031000302520002402410800c107140e201c50741940c0d205078400049020400c088007090800400103400c070f00c50683d52004500d03100804104442c1d1129070051886800b805102c08620400c080c02149024068001402e803900050f062003860a20b02422030030a20050361003800300d00301361101c0c603603005806940c180d58601c0307142c01080e5281c1d0b150380301d00780580c808503044000c0d44440320301c14112402180c00380055264116001c1040c27061401310740103035403000740e462141d90141604560003902e600c104044040d4402050000e008121501d02030118000315020401c4211241d00c2c0440034207181c200404401540d9004440c0001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 984030305 1250 984029055 984029077
    0x618060f0403020703020a0906050907030615050901030b040609200307021c11060a02210108060103230303090a0c170a03030e012d05071403040b0a1107150606020a0305 74
    0x450000703042c140208440e100440d07001e454045c10a954080100061285003d441c0c4a0303a0840c0124500301d11a01990054500c6001203144070840c3d20310560315170340080072143c14103489503d4946169114401c0000030a694140070030004112030314114146003040754004603040034024450741c0da900150003012028450105d8001c000090404c1c0c4801a60002c494802d20440e4100100d03401260040d041c0c4490340c2402c1c000c2d6002d8400c020740301030b8090140d280035078003a00c01000030500c010801d00285496030300028030716802200317041c11036008035003002c1f440e40010689020820000707403c200034049400c140251303010705130301c040d180e00c04180041d0805441d00c202c4281f11030300394809001c14103905130400032000c03a40d441402d043e100c03c005400151501e0009050320703000c1d4410390904460034104c02d16503500d0b44d491861241c0b002e0b081701912035640c50700c9002813108100070107186002d42d00308055080014400780664583c4d070030070000c6409c000c00040000c0e8004041d5a011004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 984031555 1250 984030305 984030331
    0x3060507030f050711241b13120c1a09010e06090d0b18210a0e1011010507050c030d0203041703010f0618180f1103090c03061806 57
    0x358031411006803000c0622440307050f150000b0b00c0603807a00000911402d04c424010344074112070141001c6100000805e040e00f5500c2100005007403100200c1030394000d0700107602040d0500f2424a503003580141c0c03640200c000600b10504040500c00100c6c019001001810510445140d8102030049903004580c023041c180800141c038030b03c1c10354171441a5040c0d541d01070f0003450f49e04d02c103060000a9900030b480c1d0880c43c141180c1c0c03040300d02c100803800b0810301d03800850607c0c1005811843d410141d00c0034003020108011002d8110b92652030500d058100f180c10340e40e8010819410a9860845201510300024860100031424600d017000c000e40380d00e01e070100303001038a0741d40714280350400700c42c0c0754400707010700c000000045841c0801100e4401550507641e15160f82c13410403a01000c800601d4000e040c000141443e00d2610b5200c907800c0b60340c051154502c0801e000081019010007500243c03255880d540050001d64010f08080028541c080784040d1100410b00082c2c441b6038039494054040d503071143c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 984032805 1250 984031555 984031561
    0x5060f0d0f0c03241107032c13020405011713080c0708030a0806190f230918061f091d0703080c2401051002150a0506090601020c10030b030a0c030633030605 69
    0x44500c0c103400c1d00f2300240098040d6020920414002d51060040902140000003e0250000c028070424819010240310344001c143e1604c90301c4041e04a03402c117040b144100c00c2d012a400d00c0c103102410344041151548901c6003004003c00c0b490021803142d20071100341303070301c0700300f00811215031a20f0440c0c8283c0000109a944403090402013030b160701910350090060803d000402c44403185044181200c1016a1015268a800b580440030301034440c0c02141c003098024040105603900440c50322103852006884070801645042c00c107010b0340d0003034680310703c081130b050003603503043c040c0421000108140d00c500308082a21200006010b0140d603028401c0050b8509205000700108030403c600c8072400c6c00e6030700d040c00d80307880607100c01ca9544d07010361034200200750154000200e843c44200000e20001100c500c60b00110001c0c8041084c0c03503818421448904080b07620340000348007075402003401051400762a0704801034020b420b00c14100414280d48140880c8448402802c26a50712020101d0030b61 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 984034055 1250 984032805 984032867
    0xb0a170c040c120504120e06070b040209060402120f101413020a02150a020c150105280b0a02030c0d0c05070b090a0b040b0a0305060f0d0f0c0324110703 67
    0x41d00b14005000f4a842c110522050041c40392188074050710036650740200140200501982d8091660b0050000320060040b0700140340001f00943c0c04a00680300600300440c0004126140809070340d2030b44800c0c070320300030300c0107011980d0060b00182c12402d5100b9507410118000c80c9401101d6072000740003c0c0d020410f9011140700b444070382a0341e00c00e40d00d592014123044565030003d6005c0c148801c054810308074900c98040d41103501034100c9030018091840d82403040340f06074102601c4800707810034050036600401e880d0344000103002090040d0303000f962507a401c0712483c2d142c0110143c1360428485c000401d1000140d000507030b481640d43c400703041d07a191450750006c0384190403c1c5c0c0110450b800042000300b403403504080581131022803550203000c16290001440420000022800d40000401e44a100032a450ba030a451800e8400c03070b0003050b1542c0c0c90700c0d5103140315a20210301e410030081340c4040700101198040d85101d41200b4001c6464604503a801a14114244403004e50008600c40c01000302 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 984035305 1250 984034055 984034067
    0x60f180f050f042004080d021204060e03010906060909020a0801110313030215042108040209010b0703110312010501020d09060203270a03080c190803010509041e060b0a170c040c 78
    0x10394083c1410304c450301e58209540b281c942050007910064858640802105440020220620108079070b1080c07a0906002e812501c003a55404155095900d41c02a40001041417244900070050320100042610710344c4104000e0100d182e10002140c1c2c100942084581218001c5a41284115003c0c41011001e4074050382040a03241c4040402c00c0c00b0000c10040c000b201401b010071031040208115031303505154058800c0c5906440180d04540d0002c0140162848400241f040a0290400b00d0440b408281c8031407469001c10f26070301700c0c03104002c010001960104061442c101482c1001c401141c10680300a50b00d000d030140482ca4201c0322032800165211540311f11095020140100c003400307403a0b041000301580802c03015415803091000007074403565030802503041e040d0b004040a286910b07140030408130040140c420f0b640100c42080c085658158900c000c582140304201c003092605107481080107007191540018880b042304030f5102007510700414002c3c0c80704030844000890400100f0f044403c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 984036555 1250 984035305 984035321
    0xe03073b010305151f0501033305090702030f09010503150d0606150c0203150c1201030506060a1202060a1d150c1c0807030b010c060501060f180f050f04 67
    0x8404104000403050060200e09550f0721444180250013603129407404070b501503c00704900071580c01e0142c0612003984a42c100301042c41599800541100320f024244036041c0004000c1800f22006520400a505191503c039501602c280040c41c1030411a8014034024856124040d04203c0d000001403c0e282c0c00581480340000007a25001441680b131030940c004151900540042d103d90782d030740480182c03003040c515036511343c06409000c09151f242c072108081c0c03102400c401800b40052025041c0e460007883c5144c001c5020f80c004003010300300a0140843d1340c070160408061004200ca080c805a140c0c2001c03280c0c8bc01d2980f034040c08150382e88900960b190307045020958000028400d0040b0f001c410f1014200914401003a200300380740040c1004039001f55500c0c050302190400e00001c0409001764003c00c0848418105000040115511401101c9098200c04007040002d0041132000303500c00070440300390703240d40d080d0501c0031300745403545c4031403051032199074820300f449002d20209880b0307034003c004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 984037805 1250 984036555 984036659
    0x21203071509150f09060e0615120c04112107140306010909020d060501090e043215010e0f010e1306021b0d080f040b06060a0e0307150e0307 62
    0x491301c0c2d641c901e101074865508180d6005003031410030f80c6542008035107c0d008406542d0240070807083c540034012191110143c0d9151400f07040410a4980c03500c0c090500740f01c0400021030b0f0390b020442d800e040308050000f507800301e11824804010380c040d004208042400c07143c0b0005902c80ea00c50004030348480643e0800000035001140f0000341c0d104642040302652000d0701d850f0600c90710f41c5880d09a0510454007d44440103200390010001e03c05000c511400c000b1780200e88440d46008542071900d21010f10038005021500010050705141803482e0790040078400c000b0185501d05004070510b01c1002d03080704000c40c0102048810410303d070b8110364540500400210b181c032b402080c1680c84250780c43c001d0021030041f0700018140e6007c150440d2046900c2401c1c0030503901c5e60300a0050780e4120780c20b00b4040c0084502d20080655040104100800803820030f0380030084c5c040c4000701303040e01c030b80b64150182c0d024480c103000302212121004000c01614a41c8881d00340704003d50708994409180b000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 984039055 1250 984037805 984037811
    0x10611030d060b1e030c030601081e040c03120507020307051324031406132d0b01082103011419030803010806070e030a03230a0c02120307150915 64
    0x1800010b02020f45203a0348000c13140d20910502084009861200300c0710204000700c108002042c82d80039070351840d0000294021021080c0c210640782d10004402c2c3ea09460340c0b01401070070010801d44e40000c040c00314032448e0035410003603140e0104c2d580d90340600400348511010f072200030030301e1645ea101035a05220000403c2c0100b420401d2042201481d00080e50403140100c444203024a0014020b030046980c9500d240300d0b5410f0380c480c810712144a0818503541e095000c0030404400c6284180c14030680078128449a651501c1c0c0d143d480c241c12250414500f042ea90f4005181411031826641150074a031000c113800d2a1540028101d40c0c02e031100700c2c082d01c400c600d01106012944002d94141c407040c80c215403d80e01c80840c10758010052400c1580c0c140c1c005241070300007074802c00c00c24124024020340c2d9880081001441d072590b4100d10006000240b10751480419881d142003205840d80e2240080c6d032a2003000d40782d62448405007004039004c6600c07540c010303013042814a007204519024000030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 984040305 1250 984039055 984039059
    0x30a1e0c0903020a05060a09030803070507020607061d0c03070b0c010f06120c0f15051b06013003092106020703030b010809070612152103090902040b03010611030d06 73
    0x941507840702d00003a40a1610000045114180041220b480c0d01d4540c4507000c0e2603103543e803007031090390004000e4030412a061025200586540c400f800b50207125160110fa030103141d0400e95010001c59403440320a901070b640310b9a440c0c90200b0040d06a070070354081c03240c1d5914003100c050302516045000e01c83c100c1c50300b50001001542c0542c1c42600718800c01d02c00403100c0da60302c04010040741a004180c44030004020b8181818041d900901d82080c0c84803204001d4081030915a0801c41c0036400640b80b914526541e100d940b40520b40441030051002010b45003d119440042040880e40a00e41420981030060f0b03a801d8110144083e0540d0300400a5548103100c1c0360040c0039000c161440c80c003203250035021891003034011a241381520034540d90501881d030310b8030511024002c00c07006041614900351010544442088110f80490140443c21740c44900500c6c0080c2400790550000c403900e44180010b105405441e0300b00d07070444c1ca2520746185028180d03803125056220380c481e580d16992030b001c40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 984041555 1250 984040305 984040307
    0x170d0b0a0801050709060504050f0603060f0d0602030907051206220501051509010b0c1216062f18010f050c03030f04031d060d1805060708100f0b030a1e0c 68
    0x200d0f0f032203100d50360784080550340c0d1603030161494011801595070142c448240351145041c01406160b0105006000b455108a0040495044050103c064a4954000042189420040001c80300500302500c11407010720740c08020a88031640030781107200030210411a02c080200c11110b280040d50040020011420406c0c0c1008410071401c89080c00740504c0300000440c225400241e5448400c1800038202d000940e4215070020360044c140c840172050351000344004101b039403107490650b1120714003d00c00708008800c84064040c01030030f54007585404100b0801500c59506248440d04000e080c613030502100303420709445a0080f24000d00d014807002c800c0242e106e410f182a113000c0c40c02602d9500ca41440e88143c4c685005e2051252034001c4d00400441c800455103a100c01510007803252070002948083c0c1d0b482e81000c50556030400000c07804420b00121040168070000100035441c40044164039020b41824103000051100310304643c0c071741418668010903400c07514185240d01041001550540c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 984042805 1250 984041555 984041561
    0x1020d050106090806070f020f07081525080a0207210e010f020c01051606020304030203070b0a1509180c0f0317040803040b070809101713170d0b0a0801 67
    0x1061102142000c000040d40c0d03018400803401e40301814054510341d80d9800060380c400c40300c5100345085203d16a00005004002c1c0f2411b03010740800e40203420480c541564141ba0090302900585c000e4203406d421a001640d5101d42c0c4a0540360750411000c20382c0c600c02c4440080c000c44c9006025200c1041c0002c0b0a0f400070a41c41000305034644481d5040041800115000c0d0106501c0310091792101100884560040000d000341362540c0c80f400c08644c00c0ba0b03070381d8402d9030401d4400702c02581c03011a07404204003980070302a03032190102d6410044000b038425800310740c15040c81601c81150b5144510407484211781106070070250850315011686503200b0000b003260741140f0040ea10484140d018100c00000304080b94121410b0000840c1070500f05a08440d240d0b020003c01c0390725481c00c103d50245500d80001d0b122503d0040e46622201c8241d6100400c0010030040c80e9000c000003001b81c0034000b44088c0c001032200c0d104204402d844400c0288101c00401e10f1010480d03001544590000d11490150 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 984044055 1250 984042805 984042817
    0x20306030105240f0607050f0705030f0f190318060e0f0303032a0d0f0510090207030c0803100503123007140d090312060803040501090b07050c030f0102 67
    0xa03008210300c2e6100c2000000810b03030b4a0140c20901ca00c9490503189207480800141000d400070311061401105503503840c600f021030002d0941a400c2180c04110515085c84290004219031001e001400b083c4c0c03030025101d805140e205200340115441403018544901d2304155001032440031180310b1501c448020b80985462514103200f1004880903204a04020040d01c2c0201a40210040fa80130b03000c282c01241102581101d00c841d1050100710030160144c06041010300b814200080e840c2002241000301c9409034102c4100a8010049040025032041c00540565008180b40d6142d032105010040312001641c000c983c944600b207c0603200d484040300600e206842070300c085138074103030260154a071000c00b05005103403e40d00e40001907030180200401e000b10f05240b08403078640184812024100d03800c1040c150001241c003080f0032800c071094801d030f2000d00924001182091f00d441d00080040310306010f86812011701003007075000c0203020415510428002410b0701d03549038800354203078000c0d0004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 984045305 1250 984044055 984044059
    0x70501050a060f0503060c09030f06070c020a0e360102040608190b09130f1a0603010501090b030a060b060708030f0406060f03030507023f070918030f03110d020306 72
    0x81400050302c4441001983c00300c032005000b804590b5102c2d440719026800c405d64107070f0036010304030702291604014060a4426021070b01c03040c0c00f03a861801804401c505a4000600400c41c500510012003506010a10340d0b0104020242d504140e805240d55043c021413000103481d03001140215010360483d5585101c7c06c0042800008807090207408810380d180100c203c0d8002c0c400001040c9002c59824a00326040e00030361101c41481c64a564a00e01039100006021850789094103100304c614081c0291401030403a48828000014000c0001c1c3d1542c981c60270040001e550762001c201c4980300c80e42550206500120b40039200d203031003405000c41810445086641603d4030364081a035000c100c01c8001034030340680c4c54a09050469003402081c504176202d54042c1550651518406011001b0101d58461001441c02101c0b503542c80a0f0315000355038004031607013401c0c08101000c0c2080e010341c080680c1c5d054989600046ca480340d05400a09030f64616140d242c1c000182090030107419001940a0340c41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 984046555 1250 984045305 984045311
    0x30102040b0a020c040b010e100c1502091801060206070e032404120201090c0b0904020d0c0e0f0a12030315080105011517130206030901020f1c240612060b070501050a 73
    0x44d43c0d00300421103105021540c0440c900006a012a0519950000202d040341c104008001d500d900c40200e050302070f6031940d50298000400e446c03242009d21008500000594001c012541001070103901c8500042c20f8008000710300c0040c450030b0742e04110700440c25041840c0070081d0003181350140d2412400300c4003500c040c1c0c41008000702041c814071529140e6500030f003041101b40e08007005260f4680c421200303a54000c0c0c09109240d241c4030f0600c82c0f4100602d20380c0701e00019a0a2070f0500c10f10030700c0d0901e600c0c490034003150308015104281c4038220341160301d842c00043d5010384043c03900c945a000d41156066610384000418007a0805007001400032090311004078051185030000800442214a140da003a01400050018100b000103540c101c0c2003000050b00b0b24200c5e902802c0641c22a0301c40740321080c0c14012007400b203500e501c01d01040e10070110640d008505d800c5945440e80c2624420b40d070411010702c90200b04000c00385d00001c06000d641601c1c1d42d83d0f00b0340c3e09145021304000d458002d1080d20b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 984047805 1250 984046555 984046573
    0x115020f030715090222050601090503010b0901031e0f0c030309140120031c09060605031c0c051612030f02011b0302030c13030b0f0106170a05060f030102040b0a02 72
    0x40004295011694001e14000d1560301c003001c224060203124a040380c001201d4040c4580d45c0c02000c400c2183d0001880b03002a1f9032078420001480402290720180c0280d242959110098440c0d00d00503041daa041041500366170001d4640301e2700e101641401800d107900940e0100b040009100c15a000c03031340a0f9841510480d1950640450480342e100018045504514000140b002d5040380d2400328a008040d2410300c0a040e010b0031803482107941103084150748098030750400c0359500c6114042e02c4183c00920001c204190000c000741c0c0e580c0044800d20010503540341c01c01070108078071054003000003140b2020981d22600c0c0c01600313001000072000310b080f22661446540c4148110098104210800c51603c0c8420809500941c00a03000c41c0c034a10f020000c18042d096800c1a06c80210b119505805080c90800c403405203014040c1c100340c04121040c03840d000700300d01408009810200e410340c002080c0d1607010001c0c2e60410a043d1494142d40082030000b0307400c800201400000c070003a0290f40305a5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 984049055 1250 984047805 984047833
    0x17071a0112020907210c021209090103020d140111030a05070315120c05060c070612060b030a0e0c03121b0309130b0a030c0f050a120b04080d09060203011502 69
    0x2a80074003a2649101c210544100540f611503030040d00303c50f150401e0103260714581d960100401081100c1e08099880c0c04884511513810040300b086902c0c000c12190800f120b01000510726103041c031001c1d00c01d8520006490a0000702c0f041400c00c17440f004000c020800c8072980404440c0c10480312189500d00e840b0000d10600e00038010740442d4051200101c2242c0d040c20095040c048124105031035191504d4000f06d01602c5540040ca0328003400c5006040703603403400704010a540400c594492200d4108241004460f800d1340a81c3e41018500310007003680104440709624080d8100261030b07041c0f2070124940c040700010401800035a4204141c4400045403100d41075070f070b110302645960440000c020380c4100140c550b11480e440708008043c03011096803500d030071803101c00c1500b06010b22510b130441003149107486c1d18010028104040941c0549000c0d885034444400010000b5110003c0001c40c6031076200c90381e101c0e09c0d1060340128215106d5840d00898003503007205100f590050300c6220780300c02c055 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 984050305 1250 984049055 984049103
    0x406050c070b010e07231e19050d0b0d11030d02010e0312091f0203090d0807120b03030d020403060506120c0a062a1101020d391707 58
    0x109030070028921150b441d20a80000c4e51034001c040c50200410500c4007503040c000101042a0618946c1800d9200c0320488217000c00542d031142c40c001c0d213200410100c16040c0350070f20807820700000b60800580b150200c03240b050191050040c0541c0c48518142c00100f081000c83d5264155a0280d08a031503164030400140d0803607840c0d03010b11800303a10038404060611540500380c3d6010700c2d0582614120005c00c04203520042d0840745469001e9008001c210340e8440030040d000c85194281b815284900340050b028142e40e1480d01c0301818592911541c0003036441c00c00490302d80c0032004070110340e59507a0b4103080c1d00526065511034480c604498000040e00380000381800c86040007000324071742911f000419105844050015184c85070a0f404450070406909003142c070890180413502261400ca4000900b04980d42d4220400c0c480640c409403e5919070310500d8880070904003410b8400d24029828080a102c6031a00402d0700c1001c000040741501508058400644148011110014013403030701e00d40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 984051555 1250 984050305 984050317
    0x12110711041104030f05030903030a050a260f04060e060c13080307113705090906091e0304080a0318290306042c30030c04120302060406050c 62
    0x101c0905000900201d0f0213005c2000c9411300c5035048a04e081005400b02c1d0458001c4a054004030b4004111111055042a42e10350f0041c3d200800403030b04080004843e907219000f82150b0317203100310380e00014208482d83d4040907420b0030320402c0300c4c3d080c0780140d0215031951100030405809840b0402c0011207410020540b103e0f954041d80d0ba400f0503403100240542079200030741d04050042038101d110304c12800311904820b079207860701940307001d103040005011403000050051182d075032001040150300394004c02c02c01d40c4941a0070711100041414001585140299000701103a80110b841c81c41c1015002603841500c0700714405e410314403c0e6116034401e071a088010010800608450041c114058000c0055600480052000410184481098241d14846000c554140c805113600e002c81850030401c00e072035000c5540e001c10f9000e100c1c000d085104200d0f480701102121000c4003040801e0141c505031006003280d00890350405440d420001e58850042d6026500149000c3c0861a00184401250a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 984052805 1250 984051555 984051581
    0x7060f0816030e0a12030b0406060c021513030b2a13300f14010c0921050628022b0f06030b041202070503120306011211071104 56
    0x80070811119066003d0808001c0f100300901074003070448002103440c03071740544404050b540010039a03072620a000403a440783c1c1060092010707080b516030050b52034000002120b1882ca403050344070010105000d03807250072900005c1c114540203003000301803500c21440c0c9515500302c40c581443c040c1c1d000b030b0504240c82a0029030031403405a01c0d0900c0b07181199030720b6912240d1015003401c00e100c040c1600742038442c0c10003803c440c00e0311900b59070300c02d0080d04915181d011040c6402042141030106010740380c0c0c41c1511a0700505a00e90388916404203d580b4a03500268202d0251803180c030307018545400162100d0640030000b003140d004009940b0043c825503018800e2145103214800c04d15080304160560714001d081e009032a008184a9124140207441c0198455180d000050600d45054004039815404880841d4070100e01001035540000b00440e02c94400d040701c5649031602030040710240c6002c0040403440c0d0038159000e1800716518020254607000e48844000f07007501c0c804100607a201481180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 984054055 1250 984052805 984052831
    0x5090301050124030c0504090603030309030201051501090e09150c0a020f06060a06030e0705060a0903050c090f180f15060315010f060e0402130b0307120207020a03062c07060f08 78
    0x3d681c1c0240d1005040f00b54905125080a58400c0e580003900d5407a00210000381e140c2c1d005804142d0240541600301c102605038100e00c0c0c10031000200070a14074804d4039840700c00400401e43c1d018082c0010660f0180281e14a0300c84d2500700c030b64041d40c0d4840303600c40f401885006010340410703070301082890140c000100355500301482e20b0411030103024885881e1004d0301640c540000c1a6072000c00802810000341c541c440050f146003009418503031507204c0103006103540010050904040f04003d54420804104408040c07882501c1c0d40c80e11840c40c038004400e1194280482100185561840c8180812000c696981500c4280008001c90070b103d40c14406511440c180f1005000b070441103442c2802400040c2821040d0342c10b0580c40c140340c0d2005044c0c030400020f1000301070b441810022003c0c1108410340c036011556012854214183c44042e00031a40c4261400d0154406003c25842591949804440b08203c4440c1c0740c949400e40315200102d504c0d032407900181401060a03031b2151089208103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 984055305 1250 984054055 984054119
    0x70f0f0e1504081e0d1d0d051011070503043609122111070209040605011707030b010308090604090c02010b130b330408010905010605090c1b0f010c050903010501 71
    0x1e46003224001d1b16074000003096002241c850b00c4101701d01c840075010380020075003e080715183c00200d440590380700c103221900700700c0c05001c1b03040041102c044500c14010554101d00c1b0403040c0703112004008542c00c0401c031040d070200c40012990003000100380a00e55005403a1030031b45055450340383d0300b50085881c15100141c0c021505665003c125000700e1145140d24041644d8009190800c0458040790003e43d07410042c8a070702c0c941070528000c4000703003004050107401d64586c1d0200580c1448001d004501c00640c44006495030401e84006210b1603006000410004d10003078041c00f0070a48090003120040c2840e10f60104a00400e24581e002802c1e010760f14270310805007104001454641040300f92000380d45807100385001d004100a001c0d03034000060340c807290301e045429502c580e48a00e03c01c100980074022034900d91710450300b100f40301d8010350742c5032071050b541281411500714545500f540392440060099070010000d1000c41d6048008102036a01c88500c20800340f2024000120030000d8002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 984056555 1250 984055305 984055307
    0x18030201230d02070501050f010e0705031603060b070f02150f0f030a0e030c060712090b240a14120a0b0115031514120105070f0f0e1504081e0d 63
    0x1d07124154191000341031414070028025800e0784c2c80314030201d80580d0750340308000d041e44a5400f40c0380500b42091114609007401d0384010007d0001078a940318020030080d4031200c0b14001e91188000b8440d034000b150b02c40c180c0b4100741e08840815203080c0c0c010444480003040b10300101c0100d0321910031011000f418200c40c00600404d50700020300800b022540c0cbe1444460110040025104130328000e8020a103034074000b0313001000001c0da03103010b2100f94200300c1c6040020721411251980a8000002c80e00c0e24080c003a1013855085444843c42d4002890450200382a440c040e43c0e103800e40010b1701d102d58596614906a956640c0307061000d844419003038014800565400180c1100b040d89141c0841c0d8100074600e420701d01c0410345d100320001402c50b9948042d40c14540d0444034501581c034020051464010b401030150300000030310004004080c0343da014418094002078407405409803003c00154031200c2a20000d034800d02076440c5030312401000f1400c0f04120305c40d000941c0e08000260401e1000400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 984057805 1250 984056555 984056597
    0x10c0c03020d050c2107120c0c060323040804050120070e3c13023f16050d08072d05101a1c06240618030201 48
    0x54080c502c0d00802c07900c4040b0076042500c1c0042c4000c103030a0682d1b29101480c1524a00c41e440c24400b090007115403046011071000b8441c242100d82d00c0c103010403044d10210003d0304a01c44510880802c0c0b25110034842488601009081a2042030300d8400d501410400c00d0a019001c0d00907004540d07000d00014041d50302c0c01444030390130040403c041030516618018414465003c2509420706400f03148000c05220041020b5980184030807804401d0440d40e900458485403211407008107101d440706011f5000007143d11002e91400095030850b184c040100001360b01c81c010a440804003199286000c01d80e0714044e8500c000c1164407510042c81c201c415a9018160b40c2413002e01c1c030102d00320401d8401c8102c040004040c3c007600c100043d180c038000081281d0100c030841d414010681d4804071113019030b5120250403500241c9a46825100c01d0030a2403c14007801e141c8181c1c0b0505a1140020001800c244403044150307800c40d02c80c8910462046c8110201d99120711003c1d0000d00e04801089024850752 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 984059055 1250 984057805 984057817
    0x50709060e15042117090f01080906040201080c090307081c05040b0a03090206040308030c03040b0a0c0e0108060604030204141008121801030905070b0c0f1c0f0e10080108010c0c03020d05 82
    0x40c41002c540c04c2c01352a4000c3d400d100d0703e40c0009070580015007410b149442558100d03c10b2003400d001307025051002c0c0055840000400003030500c012400400c03104001c1c0c000752a4410780c002e048440941d21045070355110758540308511604580c85290f0003060340500141c1d0159410070980ba0700f0310305c3c10b580490140c01d0800d016038000008000c04400303e0300c01e10045101d04008034105640b8100352500f1000d1031002848181c000d0319010080c00c0166001ca05141c00c0c4c6000d107450032098940c00c0004e01c45102d0f03540000c0d072180c64086d03403000e00d24403220b4452260290340e0040c40440d0fa0707010801d4998040c0c403180700c0140010001d04d04c0400511042c50040721040c0b400140c0401140d4a845c506242038110032410540030070750b042006010450f00c10040c0390b81002d0043c16110300070700c0c04e511180840d0074090210001e030110441d0f1044045030b0203910001d2100c3c207066900c00025106820a004200340c80d400e0000072200d290040522944265040e402482c0803111858129a242c0000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 984060305 1250 984059055 984059099
    0x21014040f030b010e06040903090501050f040f06030902011803051c020109060f020d0b040608060a021b010f0203060a120c0303051305040e0c011106040b0c03060d06050709060e1504 80
    0x500001c5501040e01045601651048054074419414900110b9004500900851041d400c0031045e40c0020713445800102145e0081c00e00c2c4e0b8a81c80c180442c54202d0045420441302c618080d4000a40250300d0380288810b203000b80c0342d01c181100301d400c1c12816000c5500010348542d11030499681d00f1a1240a03400300029a440001030b03101003940d5450a0b03c4048550400c40383c2c0204492000707040380c5c0710340d40784481c0450301003180c186400d05050711540d0040c9918080c641c003044005011054204940000020724001c101030000c0c4210040250420340300c0d41e004100169002c5251045940299000e64001d080340c0d10540c51035404880c954001c0c0c0040b010200c0b03200700003800303480b503010b803291403207654024121100111000508441d5203095050f03041d8042010300010070000d508498110341301309581d40e034a81d59803001c01c01c580c1140300c1c020407461403d81040b2030291310150307043c00c2d644180c0d1650f0415041c4000c1110203880ca0004200d00c0e001004200001d918000180c481d034828 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 984061555 1250 984060305 984060307
    0x12170f150316060f02030c070b0304111003021806090d0204052a091009060c120e060a11012a0509040b06041d0705280210180201030b04020304021014 66
    0x204022900b8240d54180c40741845582000c2071102d140c020303168642c0307550070b84025401c01c08503030b558a6851406104502c900c8a000001c201030110594010090440140c244100503a40c110020003d51100007002e92200254074410f5042c54080200e503001d54009041a000d40582d4003080010000036208092545420f4a2410401e20b181e00264070b42040100c0252140d00307280c00d11010b20388105c071910070000b100340148040d50300107500c0c1000c5034100b0f092001c0743c0285482505e8108030420fa41d0b502ca50701042d1200410340c080c6a541e0880b2204000340110a004001403000416800d0503800305d0b141003a0809040307209002170b00b00d00381c0061010860240380400714569605c16040425400000641040108418017016400040d1031400a2410ba40603250010081552030340c020703201300c405e03c01d6258034403c106800800c03909800c01c0240880003044104400c880c1002280441d0401440c00e10302d1408e4803d5034852a0003800c00020900c85e1401220b100c0c54104080c150310b10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 984062805 1250 984061555 984061591
    0x319050a06051807031b020c01020c1f14040e0f090d08010b030601260c070209090f03030403050a020c0306070306080709060f1e23090c1303030e04110f0712170f 71
    0x1501c82c00e903e81c46c1070560080c201c082159000281403410324500503000d03000440d0f00441d0b00425009040c6401200c0c039000f41402d904000c2001c0c148116401740340703074165410601100c00d090500e02d50044181c0e00407501c0300011001f040d6201d22003480380700741091051000900c0795006041420780c034129281810110070404072200701e85802501c400303204140103d803840450928550094100b008040144101119944180e80d6480020001004c200c00443c40c4000c86000304400d540004004050302c0940c900084028010710403131107100c0d0140701e454400103c51281d0720410b820780da05020107444090a21b04440c101c10b0104044001c1c1810174800001c6442100e5401c40c000420002c0080d1415051007c01201c4200508080b01c2c40c034081002862244c05450010100ca07410708159011400c000c000034002e0080f4401800c0302030b8000f81490700f041e110002011b06600c510026850152503602c129651070b9600804039004007002e0204405038120001150300003084c0320b000301050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 984064055 1250 984062805 984062831
    0x60c030c0405030a08031f030503180a0504140601030c030608030405040209010c0b04060b090f0c090f0a050d08070b0703060303050d11040902070503091f0f11120319050a0605180703 80
    0x401c4009082d034507017070f01100740641d00c0703084141c82d01019000091180c2017402c40c0c8845481e0310424440310b442c058107050700341d250307141c45802c24004c0000800c200200680d00011415881c07080300c1841c0080d16002040c2417990281c410a415140281d00550a01d803d200038480298481e0803180e050101406000303000402d05c1024a01c07d505ca0300d00425040c0448060049400d400b07410706c542ca1342c1d410708210180450000390390b036416040300c00d002e4420060000c101c400140380c200070b81211014102c182070080c4540101480b074403c0e8828001d41d50343c0101101120361501006000440400c40c442219081d50405000360544512040c0742c50794918601e4200d0f841000100c400783c0000c90070300c14919164000e02c00b0349020000001c521460030b1401440308403070101040910084403d4824212010800c68512807560035010344c0d80c0c2030409423889620600507044081e9800c00700000d03040301ca240241e504031000a014401048000b940c0d1103480c07880100741008140d07480070080703094 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 984065305 1250 984064055 984064063
    0x90a060c1d090a200d060509160c061506020a020f0409020d0209040602090d2307031113270c060203160602090616030905030c090c090d031103040306051e0702060c030c040503 77
    0xc5103c9450681d5203c1c03281c0c42c2e00070341b0b10640c8510310400915007006103540c9240d514900111151030500550002858040d000b410020424860703a0310014001c034100da000501d43c42014003c440f83d40b18001090104000c1c1c500702c80e0001c0d00302e00003240c01e40050030720100c0282c2061161002504100c4520003140b0400d440d80015036200c0004040300410b48110340c40315160701000c5000c2e02c040d5046843c1c0c8607a41c540107031550301074003407036413060700240d1a50301c1a200194010361111045884103c66410701100da0801e80e8001542c0000007125800001201c01c4502d41e45e0140071850807580b9000d000350031440c0e100303810842c200301d41519400402000058540300e500c4a640d1982082c05040c42e003d0035030318280c0150389100c240142000c00005942d030000b0f003214003100701941e40c0b03130495200c101c0801140c52f51001040100c100f05040c1c108904c00e00c600d00c0200311100383c400307589000e50b4050b12202c003da0084004180c1d502441c00045034000012462645000e40d1031012a1030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 984066555 1250 984065305 984065351
    0xe0c040608070c240e010e0a020f0117010b0403050c09010e07050703030b090f04060e01060614030601020a0b0108062a190e19080c10080a0902041103090a060c1d090a 73
    0x440203400c0b0003030360800120712640c2c1e405c3e901070300204010b88520381c11540e50140402c2c0070380b0459280050354490fa220f048180001c44003201d2800480d60368090004a035041070004840d98055014030010a0501c84080390499840304000010754503040c20543e003644c400310040e810961100d8181c0c009445c2c0c0c03005140940040440c040e0302c3c0ca0f09050000c215044103c5a20850741000c0003042001c1c0e202110305449600c5810700c42c0c0c2d90310b07400c0c0182c0c41d20700e0103403004102a035200d000088001001c28071034030a03141c00b01100482040415510040041341c1a099010314061108150804071001a03100c042c450b42082880c04211000090001046686002101c000d9241c28840903000b44801808400103941004a00c00301e01d0f4050301408005180000761980ca40d80c040541d900d41c2c00002003145001d4103180e0f241015414640c0740c0015080a0301c813242412242c0048900c14241c84425182c094141c860b00502582000005000075048a0354661180356100d00b4103000501198 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 984067805 1250 984066555 984066593
    0x12007020d200102011d2d0607021c0804020607060f061a1b1606050c0109120509011b2d0203010507030b09010608040c0911070506070302130e0c040608070c 69
    0x10159002c0002425529448080030010050146580c61000000b80e1100c0c0340d48048401c00b0358459503200d1204007115a04211018810300c4c0600c240160042000403000300c0c0707a48840404e4419080036600401c3c10340d80250042010440702010607480d40c0720080e1038090400c08104942d0b00e2100c04c050060786e40d048500381c0000640140441445442c103142400007070040c201341005040f14030420b400c507102d00f900b030180003e4013042d005c8085d40070907100359001025400c800c1d0820801000c0ea000841072902054583c031603600c0d82000000034180041d4003e02c601030415842d800c28005103800240007514540c140340c410016038080c080d4a10804640d03030009507820343e0030200042001e06900c50403d0061303086c280f10221b811f01c0000b50588500e1400402c5204804d0300581103842803550150940c001d20741803200c0c10360f25400402440100c03100c910005034a40880f221402415140a0710904d8100400c102c258042d0740071690016990509060841c12a16100d8403600444900e83c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 984069055 1250 984067805 984067853
    0xd0902011205072105060916020f0304030c0e06040203060a090b0d15092108011a07081b0f0d021b040605120106050907050c061504150620012007020d 66
    0x15041d18000710b402e103450134107010901c01420544041028420301404242e150309510140c00c002c0c9008200c0c0002e00c00e4210212940c955403814440e01d55040c0d0b000300f00001d0315400120b03140e45498000d0300d001e40e80050403000858a056910301c001c0520585e0150402e06404800c1e0118420003c60b038400700c410900410003030baa520380225100900c0382d9001d40c0308241c0c500e0708040c980c000707096030548040c038000301a0b003001d25015110070301501c44010644100040d000300c3c15400b045101103a075080100703c4900910202d80300e502d0340c1d002c00702807005a00240440c6269407000352b01d00c03104038014100103451920340e808120141c21000c82280d440e074449008020504269a10a602c2015851b015041c4442103900036201d6102a0010100e07c040d07106102ca0b40e59a948000101c04550243c00129651104068002c00381d0300304100c903000c240c088491001c40c06001d144090420701d42e01c82d62200c0003014039045604206000c1e80c01040802081c40007800300f000c120800c0380f04072021 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 984070305 1250 984069055 984069077
    0x1b06060a05030c09042a080706020105010b040b070303090210020109060516020a08090f03010606020604030215010b030f0a0b1c0b130b06090c040b0412020f030f0c101e05030108060c0f0d090201120507 88
    0x1fa40303800415070210046a00d44001001307510011002d42e01500c600065a55076000c0c3c908045014000307801c00694005c2e1700a006110f003070340550089812a10a80c8140000d41e00c030340080840e0b042c0c0c051100c2c09030f00042c03030840001d000314000301881800149a00005203c00c0042401c5a029030006800751348a0b00c2808207242e01000603080d4980343c400e2440b00756060000114070360001a0400c120010707040f020441d1554030b500010030400c0c01810011b011000c10043c0c020800c502c440584041d440a8045400100a10b004128994015543c550661a0304060143c007400003000c000940d0410b000100d580d40010700240014074141070840b0000d80103004000c10200701003c075511075031000d91070620607540820607640b0400125090320310651114001e0381e100d16240c54201c3c030380d01a0305189066941002c06107041c1c0701c40c00103c2c0e1460752a0f604a15452043e140c00c020044002d04c44926440001e0b0450101c441c03041c985800c090721800c4006040d168295a12400301e8040004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 984071555 1250 984070305 984070319
    0x6130e061807090501050d0f020607170301050109060c0b010e090304090527160302090606071415090d090e07090b0a020c0f030c060f0313081b06060a05030c09042a 72
    0x10142c040c200911082200e545440c00040c601a06141d00804044400080070705641d10902910309080d00040303a04a61001031a00c3e0805510034055940072a49415012440500c81c4501100f60f0fa401103640c030b01642886600c6060742c1004094505500c0104404903c800c524026a170203411000840042d40c0c1d00c072181d0070020301d207111201405d60b001c1480d46003000c2c00040043c1c1103d80640c0c04c4411078a8002c0480c4051050307080152004d14100f5044403940000100041e6840f0685a64081a12120039141c1c60b100c500d850080040da6941041c062050460a440d0b002440c7c0c2c103022142c50780c0c80b150803103c0d401010b15030015800100d070200444c1083d1380d100c05c0710881107018120b511034010004000303000303005019201000100001c0d0600100d0100d54144d1908104401d454000140c2c0382107006d0300780c540401c094001c0501284160038122100000d94000070040e02149001d84244408254000d01c140c070074404c0350503656401c0c4071000420721400291102440540e0601807 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 984072805 1250 984071555 984071563
    0x609010501170d0f050d020a0e1504050a0603020c1f1a030d2111030f1801090305030a0b180c0d140105060714010b130b0f01110606130e0618 62
    0x21244407810314060b8a4a8101c0010800c542c1103c41800d0840108090b02c40c1180d160040e00f1881520a10020f01026899002300302141d24020443d02e5100d801c626241400300b074055485070340d0700300c3c050038000c1c40258025005000e5040748902141c5012200f00e002c0d00c0c1c04440c0d10300c074400444c1d03034039902c403820700441841812001c0140c00030081903070040310082095102c0795682c000000e0007080459919180c0d08203a8010702605401502c0307040c10910500d0245c000c3c0c0c1c0104664220303220b903100e0f081d03040c080d0303035541e070f405840d1903003545d0350404180c014084200c05140d000b004101a6190358034540d00050244542600c1e0503190000201d40700c0445003203800e0b0501002c1c03a4001001a90307100800c42c0c43e600e9000d04c5040d5050f143c03a40d20340c09807840007030295101e0042d043c0411000d40b00c0d40800785460048030120500c42000005580d440511103440f21150001400a40c141c244002200c18080100700002040610700005070b0501c0e009940900603485102c501e0450300c84200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 984074055 1250 984072805 984072809
    0x60c0f0f0b0420010914010e0301140f24090a0b0a0b03090d2a0807060c020a021509010801051207050405090a021f08040f080c01020304111003060b03040204110403080c0609010501 79
    0xd003443ca5a0304100010305000c00038032540c090750310100e03040c000b40e91058900340e0040d08060000d126036041c00003510070600c011034402c0ca0145400d00002d40389880b41c02c1e501c2003000b43e0000030120a101c20140f00d0040d500500141d0059100c1c098201c081d1103061300340c2e0080a0015540340ca90419441d0035040c5005003d0710010400401560029500c4902c10001e46615601c1404801c80c0a403a0501c040e000301e03030300685035500d0401c211800d250080380f41c0c40036504c00c4401a9244041001c040c11038000c1c02d00035030010301114010b200c24101043c034445540608000c6402542c0c0e500000740942d142110070001e10f4210725044021410403459041450303070034180001c801902804000c00c8031310020405000e403840c40d01014280600c02003140c41c41c3c00c24100a5540b480d00e4102025007055400800d8010401d06400c3d40d8400d00c02c0c400d01c010742d01515091455901c4036001c000181408a80c4004c128108020010011761064010541e035410382d40a000185428007400d400c580c816 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 984075305 1250 984074055 984074093
    0x20d140a08150d060b1c0213200301090c14040e130813030503040306050a0204080a0f0f0c0e041202030c10021c0203011701180f0312060b041e080f07060c0f0f0b04 72
    0x341d68904016a84c0b407400c0d01880a00742400120340c0d0410350301802c940d275204040503901c603000002184007862600000320040c2140c994041c40d5060591191951041c2c0c1300d020064058040416031024070303c001d601d000740c0101d900600780340c0141c429207030b0100158411a03041d03000103000c004000f86d43c0a59948110002d90440c201481d203099a912141c00c058010080c00021045200700001c01030a002055044221408080e848a2440c1d00e240c40c295400d6407035420030728880f11950300c0041195a009110380251002920b0590a04040d401419940c801f0046880e40820480c80c1480a14024042c1e105004c040787e8801025034219100148130499800b404070240c400b0900c5040c0511000d503041c83d0018426103201054402405940c0240030400380014000400a051800041819645002d00c0341c0003a92900240e42e112410344008005404c107500400043d0b0013481909134081c040d0141043e03c2601e07035501e4145140a0790100c4258505106010500040d166900042c4602c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 984076555 1250 984075305 984075349
    0x10506040b040b0a14030a06080609010c091202030f01050f0402011710210506011e0e0105090406020c03160f120c15050a0b0409080a020d140a08150d060b 68
    0x100145101c15200728080c101d0320030301c00601d0001240c440d1503c0401c0ca41008241d940340c0c01e00380d00a0001d042e00d8844c054241c410280411411501841a2003440003507440710001e10b45001d903c6079825801c0d031400c1c1d80c18040e500e07115000250a02450b0b1140c1c000c251070f40003030b14081c8009801c000f000079100f03140b000703190200811017a5036035190050b92524540c0d070701c05508058502040d400b03081401401030103020300002d094610703146666881c4440c5900800e010762101d07075040c0162030900c034843c3c1c00751110300850f002c00c0d120340c0142a00014102a20300e01481c8035040351942c40b80d998200c403540e039a00841002d01a1005a031007001c801341c81e00800503141625a00d289803d01c901c49095203980c2c402041c0c820659510000589901130814020001d1317600340701a040e081041682c000d406600040095544155030886c034200b06000710038100584884122074840c40101820004401014400150340d0b400340a4041140309150204a22605100384421130a144010900c1241 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 984077805 1250 984076555 984076559
    0x15051c0209180a121b110405040c05120a0618020d02060c030910020304080d030b0f1908012301090507080c16080408060403030b030106140d0503090a08070812070210030c1110020406030501050604 86
    0x1004a180601c3e80d0100c130085203275115802c2600c10070000c1c1e80080e070301c4484901800c07542c200105400c0d407402e028600c01c000f4403071442801d01c510040341c280254000644003890005140c820060622501c990084a08013110000804c1d11441d21004c4580980d00105082101070301c10416445130303403c00d1a003440f9440d81d940129a0801d21a014030307115813142414030980741042c4d20300500412180000b0702a00940d0395040030520a440a0101c5954100c00041034480c140e000703070303030050680342d0351081030366928250f60040350010001c65010391100c020303020201e800c2c41d000c0d0000c0c1942c82e0282040b41440d18014040f81d02e03c119a0f4060b13410b0100800150301006001400b117181030711600f440342035900e0301b83d0440c4a4545019400302e0301d80b0002c00c54001c0000d21030140c4104404079130311100d1245215100f4082c11000035889080d603401e0040c1e2a120380c00659000752a810100341c140100000242040758040011008581c0894200010ba5250007018010f12041d0f03100f0303181034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 984079055 1250 984077805 984077813
    0x1110170903071109060310020307031a0a0f030201050304061506031e050c090d110312040501020708460302101d070e220615051c0209180a121b 63
    0x603200f07110051103900c0500008426440074806401485d148a504540d00d14104d18040c00419007424074001c1205a4034140c0d445083c641d00880a46401030911219103256600465071640002c100b04e9507591140510320030b0381801071030040a00f4040d1804590202c100d0101d07181561402104d8080904013000c0c420040c142c1801c0307074a00703001550703400002c40d0903041036010300000352007441d011300c41c4880094002100d07402400075540240d0131b03034070596a11014150703121200b84030449401050422170b9070201e460340900d40050030000c00d04a80d01d14504140031025a501c5044c0e000d60851034540c01403141d58070035041400c60944a1028070703d40c0c10300141c0e03164072900900f92000807040100c0c20180384a041c01320340183c840d0000c0074850051910002402d0382d1284400310700700e02c807004100c61601d40307607003511409468400560718000d43c0800c801c42e280034041000b0006130840044045509000148207940548199114542d4691008040842c410007008400340c42c04c003514001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 984080305 1250 984079055 984079073
    0x5090a0b06040c020102041d0f01060810090b0d06021201090615082a03040501062912190f0b10050a0c0b0702070510030507020c011e0c111017090307 66
    0x1c40c000341c81c0011003801e0341c40700740d00a1065400c20000c51020f40403403600c9a00450180e449031003d2402d03981280d99820042d200380c0e80540d1801c180345405101400096225070006c10403100c010141098100c0c00d031581c1049a0107041c50b02044000b070070061000846a000306030042400c00c44d811081c1c009004000c1513848040d1009240801303d4081d4400f4410a0094400c0c11b441030030079a03a64102490a070b4003c060500c00c400f28400701c00c0d0503040220f60810748088003410040c109140600c07184440c9440c0701d004080d8850301e00501c01d070140510052082891610300c400d1700180c601c5c030070800c00010321a4864990200681007280e2814075620107000c03064250312505030301003500e5400c806e03802c020b419085075821020711003607080d0070303039160b00542c0c002c0a01d034013951404040030004488003d83c0300704135504803804d000500280c0d03110310601d1100303900402c0c40c0f450342d0070b45000041c0e000580c07601010018038030208555400880d00d04582e00150a02d0003980f40ca501340c0c0e101c1d808 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 984081555 1250 984080305 984080311
    0xc0a08070e100305190c050f090c070302010f050a060f0909031403040f0f03080106182d05060a03150b03040f1502090d0b090d02010509120a090801061805090a0b 71
    0xa4044408041040000002c00260146038070800761049508007142c14450b80c0398400e02610001c01c1030f9000101401d0108403030008040160003481550b90b03115403103440f50b20a8508904541da00e04c0c04110300307191032140c140124001000418610f1070b100100303514800b5030304001d5525192502007000243c0140707221203101c140c071040d03036101c0d903c030f042c58211000600300c050b207021407200c401010568000f0005058a61645451602c580740c5c481d0400540c1040c00303200884001c036903800400455640d42198403214800c00130301003d4484e03011410b56041558541c1c0403070303222203154440308404290000941400f1241394290700e495150407039424280345c0007510b004201d032a80c25100c0010740440d64026405440d02c840c1c0007651801a107200c000320b425940900178013065449451060260358000c01803800100303020b42d10401208056400300d0089030902c840c0c00000903e41c1400c0c0650001090420ac45065032030108943c41c06650740281a08013070741054007100005200c54803c250 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 984082805 1250 984081555 984081569
    0xe0303070f0f0512030109050f04020312031b1204050c0909191e120e03030f040e07020c190e281a122a0d1403040e0a0207050c0a0807 59
    0xa205071250400c150702202c10000076040740540e072100080c01d05444010b604959803140200000d07a504807a014541100f924000d505410240b0400e05124010010f982c02c060f17800c40390313142c078005042880034070740c4000340061062682404002c01e00000723101842d151072055076440c805240c02020f068079164000c51030000b03800703151415400c2c0021211442030308a01c00e0341003c070007401030610b000400070190200001812020326031410b810b001c8150703910049041012400c0900700172409414120060482c0214820910100220744e0307840503401c00c2002031504040820b007031030010f94020900400061418608250040c805111000702d0403a4440305000012030b00c0d40c04010454980500b07076103690100e6403007645064000c000ca19910030482c1c040922401d0420341043c02c241000006001e54001e011103c61000301c1d00b4800308651203106002660320302600c0712003060200e9070644003d0071140d408501e035420007604100580b000c8034200e6010400740c0c41d015190390307100c500d401648 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 984084055 1250 984082805 984082823
    0xc0b0304081603020307050f0706050d09080f130e01080304050603150a0f0602031201120b04022202030f0f0a060b0901030f0b100e090109110a0818060f160e030307 72
    0x606010050341511a0440b03401c80c01054044036007802943d035000880d00707036030070b01401090f01c0c854000019160220b91142e1a040c3c00d19216022010050035041402c2d1000d09003042115558103841004250010350200d20245c584e081c60304500c2c1c0d600050700300070429032081106002d582d031080292503200028240e0f8a1406c4040400f0403008101540403a514001540c80444d00300c0d0003202030882d1100858400c40340c0c0c0c0c1c1e502c980003c00c681000c030240c03070300703042c40c0200d405814120081060040500008680000c010b203805040743e00489480e04600b803030b11b090001d9142941a4550041c5924400b400041d080c00319011461040d000080d050595070340300c0c442d400c051508001c02c0e40400501c1882040d810180250007414030b0400c1c0352040001400201e60804584504500442c281e500242041140708043d10040c202800c125851301240d80c2c4041c0703a95081020901c92841100106913604084144001c8074180204c1c21040c849284120910ba8500009030744440e40c10080380 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 984085305 1250 984084055 984084061
    0x4020903011404060f180804171e07050108010501081e06030c060c2b0e04090212060403090e0a02040302010c08070212030c01021c0603020607060902040204080703060b030d0201090c0b03 82
    0x6401020100342c0e900d026080202003000b0711400b50310101c400e2039000414003204292401d17207600340302c049000903e604004c5c0000d02407025040e0740752000e2031400c02100c0d255a01d08072003201d240440301c10f440003a07004203c01d001c55640082020300401c400e091085040c105011581480010420002c00d00d003101030004010395801c01803d184080c0c0649a00c1d40c0d840302c542d1560b100c988484074002200781c1030300c0b501019840075010f80f070019100c1d41c40c4110081894100000303805403282c00d0780d1080c810144580521024406980198481c0e10307032661103480c00f048a142908010551001144144000c0000d43d81000e2083c18040e400b04565549105920010308100f13400760b2684150f100115801101000550042c420000321203080b0643d52503200c5c50400b40c903840d000094109206000401c00603101e600240d1420788018405414a80c0b100c04451a2a84a83c4180c0340e0079150300188072076060522044031601c01510080c4040c50141d201c0405010030f81c031400315506000000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 984086555 1250 984085305 984085309
    0x3180103061d0403091706150913060b0a030c090b010801050406121103030c01240f060f08060f04020c010b0f04020307050703050f0c0a08030f100e1602150703061e08030306040209 79
    0x17800000d4142c8010203c20400b0300b0214668850080350008040c00c14641c6405541c42e000009078803469095141001d1000341341d5a900151007071010054000d08a98000b20018043d003000c100905518400006c00721405400104100c0060748a40d020f0351034114107120340007180c08000d4030785d41c0001c450101d03040e02c13902103480c41c032510441186551a10313a00741c3d8442c050481400c507011031140320300007241d290b50040c2c80d100c2035440b030600440c1140300882000b074051a4100d40c0700d80002c0c0080e82c0e00a49001140590744007603a401017603503440d0850501c2d803811403900b1a041205407403c5082d80f5100074042c0080c03043e0a000382c14803d001c20480d01005040b030454030406140f20a541c1c414070b0328503111000f50401d41d4a0741143d203105000907040b01c0e084652504841802c1d50810098442039a0740208207084161030007140180000700b0341c42c0d40a0301e8590301031001da6500041051504945207030304820080904069107601d0010000d4827000000d694001d20211001070340d4850001c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 984087805 1250 984086555 984086567
    0x709050a05060f071a100605090112110c0f0d030e0307020904080f040b0403120f080403020c01120f060b0a021212040303050c1b0105071805061b07050a0803180103061d0403 76
    0x104c002d1a03100641d070003100700101040346500601072200ca0b51310301602d488090300c01d8050741e0702c40c900280e03005415501692451b0070502042c01c17512013031031618114035610390038591070304039005d40c940c01039003002c42c500d9041c8503001805102c500603600340401c65001031500c6401400151080001190503107201c88203030101c400400380903812aa07100d0303030391812411402604001402150300c41c00080f44060080341e110313220b80d5040d40900842003550005542c40b00c21101080206d0f0340d03606046c13800300c146102c0c103000381015180064075004006402031400ba5200fa400c41150800c4c058580403813a0000300c6a081070780341c01c0c04281642c131f0a04000543c0102028202c2031030340741c41000020103041d4401c50141120b90303180c0600b41014190762410b480c25119042c2c000c0810889021805403103015a5040e8170414250365145680300c00040c80030170710b0340041205820005d803420040400081070a018002802d040c80450b2400103100d14407070f005000381d5600412a0001010188120 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 984089055 1250 984087805 984087817
    0x81b0c0f0c01020105060a0806040b222402040e180307080a0e0a1502280c0b0c01051006090626190e06060319030309021003090b0709050a05060f 64
    0x1a04031084038240301012581c441400c86220702552130100810315509048803880140e0b11f2800080000c0e4445507188244808010650522070700340002000142401503200161240148682e0107040040000441c0345d00c402912161801c3c8104402c01c03c10406540442d40b08681b800d1880f0100305c004e207402d045109440d0010024400007807480d02054005020381e4142c0300540d40b07802007907203601200240500442005016900800410141e0152400d0481d1814541c19800c082002d0035928000c050019400040e813a00300480e41610b86002407040540c0120a002c0014285203000c0001d000e141071801254100090018405001d580014906440d2601c0490844013840d284e04504184c40183c00c42507103c0e402d0100840c450480044c4c03450042070004c001c1c0000300c042034a0760101d03d4222900310305041d11540c0d134001580d03410b03861096129840d2004242c8401518050f21b0703000c002094481401400007042c44652a800803030803d483c000d40307400340d490312100a003083c240654 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 984090305 1250 984089055 984089077
    0x30c030513032012061303050702060304240209010f11010213091d070302030d21020f0d051305060424020304110a2304020702040e3406081b 62
    0x40e40002001142c000754903003114840441d00070f2100756010032080d0103540c0d1100c0c1543d88000080b41400d5558100074040a20a041c030703071f140580550210b200c94004840c19a80038004000340890000161130000024507142011881c0003d000000b816044032600b150b410404504280011380c80c1c2503040790340c1244441519019665100e5509014280c0a813076801c45000f50310382001950b400003000c40aaa41c014042c08403404000000c407038804100801001c0007040680c0b00100f0a440c0c8010300120814043d603ea4808805e0054026143d020b082101d039000ca654190002c10030219460307800607400740c0101d40c3d40c404010010140000c6008207540783c1c2c400020b0004002903000ba45901c90800e444a4141071b5940c090711000c0442c007084403002d1000d5000c40302140c64580e0081580c148028400603181200c3d194040c64110343d80391944032780b0200f000e40542a500d00800b00c04442103060710040840c14900010040321018060b1800070030002140f510030507941054413400520 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 984091555 1250 984090305 984090337
    0xd1e1b020301140403020c0102070303081302010e0603070503150a0605030f0406201321030c03020a0609081216020c0126091522030f200c03010e010b030a030c0305 72
    0x103000d43c140301c54256000c4015201e0040101415400821460200c98041d160b5403101d958143d1440840f514245049040280c20f400c40f5400f961240059405410746a41710b40c0c49242050742000760b1010031307200703d03c01d54a5060130008070341d10004607603011591554101d00c0341c0312031a00101034460b199518510030000c1038425860b4507050003500d1030030342c460741c0d00d0ba9250780c03070310103c049103c1c040070f91540409884c1410042400341c400e80341501e10078411074110310941d40710304040300c00f030007401c0b00c080c4800600307019000703012003603d600a01d406002c0c5040118002000e991039151000030381c1072100c0d0b45801c401461401e601e0a61282c502900d52101e0325002007855210b80c80f0050068a0100d0440821119610010080c4403810740c10484c2c8e80007005520255440f1803015254810026129100300c402c07038811503803000c00caa089004084416114007010b0a441c42002650040d030315110400c00d040d0740008001da45941c1606050002c0d0303c80d030601706c1d17451003514019005006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 984092805 1250 984091555 984091571
    0x1309020a11010b040603050a080310091104030203100c05220b040803070201020f07060f03110c0106030c18150e060a0902030f040b01120c030308070c170901020d1e1b020301 76
    0x80c02002000450701d140380200310301038201c010401150000d01000e00603034002500f90b000540700c07000460b04a01c081c544028481d41c3d4140500075201c02c4804a11100004074040085007410040d5030300d48040340b0707400e000400701c414005002e40600d41100701412030700d00307111120403803d00c0c0c2c440192100d50000b540c1d65441c1d00f6480d95a9000240032401441800450030042002149000035070392140d84480506040a10440c0501003106074030750024420403c445818000b4850507009520840d101ca40c41d40c6003000ca00300b10369120b5002c402c0309081895400909944550410559042d000c10784c482c0d03142c8101103031701c082a075004070855500c0001030003c2c04c841c203040603100c0c1e8400d2990030751903a00c400032000210031990700200076181c05141840021300a40f230542c0d002c4418a00584000106d456003580810003280c448940c440018000e03046503070500c0103d00c0021941810b9510045180b405062512089c0c6144100041d00c0349d910385022041419038542500203009000002e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 984094055 1250 984092805 984092807
    0x150f0d1a040b0f01080705041a1908060907080613050316030c0501180503160201110a0609120305090a0b2706100e061c02180415200d021309020a 64
    0x240c1070301e09958611076100001c07069405a00d02c40e068071034940c060510300d40b901c410310018000100004c06150310054600080b9291140071814402c4080700c403c84061801d1540f50401002800da0080340d0080394082c420301500240540e0800c14072041d034180c2148a044c494190f0003984003041e0040c2c1420710f40c20900d1b40c0701da40040c02e107001e07000030000b0304844e50704100c010360354101c01445500305002149098102101d080c40460040c101144161020003240d800d0130441c144c1160041c2d0303141a1030301400946c180d50440700d110750804101600700b0ac2c00a80e95420783c40c0c0010300b0900c0000005030b0041c040d0040b4146000140a5000310844030a102c9443e000110354050915a80e0900020300101d0544c0c40c41c0211006425010701d850013010100100040d1101a6041602c00b900e04004880e0b142019200e14001e60000b01d10075040158401a20040d111400c0102240714601e0050300009040740d44080f46041c0040c2c0d103070341080d0350500d8601a58015900301d031001c5179406000b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 984095305 1250 984094055 984094103
    0x1815060308360a0605070606030501050a0c02010e0105060619170109020d230109020f0c1903170f0c030603011e020301090f0e10020708071e110306150f0d 68
    0x103410a002860b007000e016a82c01c0e01d040418212459120964000c208065801400141801402008003060540d100d0f16071a0a42d003007681c20b500a20707541c01480e680d080d17080c481c06000131080380c002d2080e81028400580c81e03014084940601d86c0300c254540e0130b22401869400c2006e03030146501d40180d03945034446402908003186003880c0e182006004944020809000c2115080000905c0426401d10780340b01d000707400000d60610340200401c422200b00d00300f0003400b2829041d2110441e08030700c051500402071203a01c281c0a050210708814809038170500c00c1f0b042d5001408101c03d0361243d8070100000c1c003406030780010001c04134000303420600c0c90145400a40c1600c21000c814460b070610509003000711003681c07144804030780203012400301d408990b0300140081030103aa400380c03e200c55a2284c81000700e180e0f120400ca1a0340601d0002001701c140c41d0000018402c9000c0c000070b01d8075044819080184540c01889034154905a20031561148801018940c02c00d200d44400c61208a082da25 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 984096555 1250 984095305 984095347
    0xc06140a0509010209130b12011a03070e130230011b0f090306110f180306071103181908010515031c050d020909130210031815060308 59
    0xc55040c9000520350580500032182c0008000d001c140303400d410340a80c040100210b80b4141e9004541200601c15030509019544d000ca128103000d9107400d00740400c040c607102d8694448125619071200b000100c4038034508034068203030144c401801d2000f1880105c8030104100a490509a4040c0c400c1580380c00c056000040f10541401041a40300740031409032000e500150160380004d08110302400090656000700d503803500b00c0d0b81e1482c2010141c54a03040303940c100500c41d80c0d4180402101608901d02001007130741020003401d2503d0300000c000390305c0c0e8032485040d0301b0340c030090703100760003404552180480d2004890280d040520340686a0402714080e00c0140d81e101d0302c0c5168084031a40a00d404110486504940c40f00c0744d0308144000c409032146c2d004402e0310b6400c250f00b4050110b5548840480502c5180c1420b01c8110010a078410800d007412030101140406183c40002241c2c49151080d05c002c00d500441c01e48001c022451603070303000d41080d4000034024180401d40e01c101d0350082d100d0400e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 984097805 1250 984096555 984096571
    0x11d040b100314420405071101050105011403060607020102120c1605030f15250f12050c040b07050f03180102060c13050607060e0a03020c042a030c0c0614 68
    0x801c0e40c844c000c51a800e10035008010001a680c0c040060742c0301c840e9031003d5004007100b20080410300e18080000c0445208540c0f10000c158145210460b1003c20b100d19400b4150908203900328229242c03140d2000d000007000c0c2ca000340341c0050081c3c1560700810948590384003c0e401c00d40d0318042c10394881d80b6031584038034004487c1031010000c0b81c5454085000b00661110000603c40711070074040c00340306a000a45144c04185140f148442c21003410441408000f1551700c0d003461940b0319a2000705004803075103071035606d03500e041c0a01c00442b840c541100d04032010511060748039040340c1803444c14240c186581176018400080c100da404070603003528021520303090302550920b5461461401c080d1243c3e2000c6450542d040d1001d201078640100a84400c50181c200001e010741102406481c01c40e40d201c080d80940d20103d204001ca2505008580c0d040764410640703d101c1008c210341c0d007c0c0d030003024054818540c8410050750740c00d2041c02c20140342900300c0c409024080051116600c0d0141c2503406107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 984099055 1250 984097805 984097841
    0x60504090216020301290d0b040303200d0213080303063304030f0c0803031003020405100e07090f05030a080319140f072d0c02130f0501051c02011d040b1003 69
    0x90301c030303240620054110f1f90300306442c00015500c82c2e40071001002600c070007088010078a40320880b40b402c000c0180c4000300c14080c0c0103940b61042c06403040c116031558800316081d442003007000310b161a0fa152500200040d60074000840e1400c0090315a0303142d201c11000740a000c0494004240544c488140c201c00d1b00070040c42012a81b5480065203030f100449000c4001503070210100014101a4041580118450040076020307445464540c0303403035015240c03e07001490b270400038040d8075a840105070003407108400500c203040440d40c071a001404001c01181465030160403a40340054903401c02001d00710a0030600145203400340b00d950144078151000702c00180c440c084100703109000d49603100c82d400c0800406c40152030300582120b440103181402c80e0004030325264042240c07424041c12000e02c1e80c010011506605080c140158a801d0207098818035a1522074040580d0700100c803064180c80039a010f0828120300c401140c0a4444221010340001c000300344a0f40031030385544001c0100e84841c40c90303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 984100305 1250 984099055 984099131
    0xc0d15050a080601030308013506040303050108160b090d060e0a05010606140909040f020a0f080c0d120c061812030e0a0209072d0512010f060504090216020301 70
    0xb43c0e00c5409000c000c01255600e00144003444d4008044142e0303001011455103071442e10140115142c0c07148000701080c3d88100c050008140c0c05000c3c4d01c1c003411310b43c0001d00c4506260f240c04608142d042c890a002c1400000e1455626100c1c0c0100715038284d001003013031004614151809c0d60300c41c2d400205903501d5280c01c0c004a2024480c1c3d61824108100c1c01180382040401420008600c001520031075514141944417401a02d58440f0400180b030b0464188100234602400181011f4a200307415204080c01e540d25000191078040082001c0810320b00b003c0c00904629000e8024285c0c11009200b084601805104110444039100305858066030306021905016100554411a101001b98807a85c0000040e0096210710b5060400034503c01d15040060051000d580081c140390070103900040002820341545a10302100300e00610101c00707103500052074114003e146019900800400316000103520306807010f6000180e911a40040007000317802c070b10201040c902611a00c0350000d0001c46801 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 984101555 1250 984100305 984100319
    0xf1005070c030206071a07090b0a0f05130e090d0513030605071716120e1002030c07240b031912090b0c010f11091c050a05030a0c05060604180b0c0d15050a 68
    0xa0084505d0149c1032810005c404106a0303c12400b1603c00c000c10000340b0107a0548060354000c0002842030300044400c504080c5036042c18034110415107014003200700f145051068034030600c50210b94004a001440d51140d200440b18442d103039141e40d0300a0701200034070011908281c1548030f80451a211781030704091003d00c90b41a10b005544030306083e0020745d4010105002078008551003202c030141030b40340480a40e20291840c0429201d03c013a180344050640410f440c500c00c081150f40f00300d00804010b0790f0175911008840c40c551000f000b00200c0000114454040d000c504003910510402c1c544400b00311a24500030312061101c6002c06003085248003c0140040c221280e80802402002e2901505401d500f5192100041140d140c8140116000410400c0c800361001c240240d452001651301420324901d4140c02601040c400c40c81d004040785114064a560300000ea0b10000417803055030f82003410145801030121000c580e03030405120000a07820707040114150b842c00c4500444d0700703440c1c1c24 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 984102805 1250 984101555 984101567
    0x20a090501081e071808030c070506070203060417071505061003051e090a080f0703140f070f0c080d0e040e0708030a12060b040311040b0f1005070c030206071a07 71
    0x501c140146454038881403d45054104a0340c003090703a00381080245055007458420f01001d50007050a45c0002ca506003d8007405e0100c0300003028200e640d07a06140b02900001d45400740130304001c240e03030001c1e51190044101e03c42a1200729400c02044050080c034010228080c10040f0341e00c91080c0c8620b2001c059031030007449801e0080803003820440c54245000101c08070301c034002c0c11480d2980714000c01f800001710804000c29403080d403141c00c15122085843c2c09041d044074450b074403800da0000d101d000344907048002a50074140e0031001c001007510700f42c20310001e4442c03140c00131161801281804652650088031441403000251001c0101004210681d52200c2403070040344600e40040183c3c40e15140700c1d0980c0c07001481030740c070001009661419580781d00d612652045030a007006000e80342c542d00e0940b00c0e240c125602604c4180c010281d0b103002440300c4180d10f0304441480305c0400e40400340700d4034219a01c0a5580580015502d400a003000d50013250108480140d56110100255840d0f214074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 984104055 1250 984102805 984102811
    0xa0506011404120201050906070302160b180108150405150f030c09060603090313060822030807051c05181603050304030201050d181b050105070209010315021c020a09050108 76
    0x1c003010300701420000c81c2030700803811000c141e0401c44103107c6903416949810080100511030b800404000c4448040c10090b620030b940040da281209000300400030043d201c904d20049400d190241c0c0070380d54240e0103900b11075069000344d04603250400300103d4450082904940000c00c84a015401c1c0f1801b0405580c1c1c10700a0020740c221502d04c01146443c02c0c03840282d41c001070310344146c07030810301403d410319400911a40b051001a44440c00e024015146050180002e14850412406ca0140c0c4d1000380000502900000811000080001e440c0d02001408400c01101b080c0901150a103d600d0301c80b42e80946d1008482801060102d500c192861405501140c0e48140910704091a580055078250800d500441840307855403201c01c1a000c4014120726114807034242c00280e07001c1d01a07040a0f50202d5000181400000c000c03150260381c505885c141182d03070100310103414540b0301c254031010380241c0c070403504c0510030042c0141d0b5400c1260084e11544401c1d03a100c03007081da964801125600816 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 984105305 1250 984104055 984104087
    0x2100b06160602090409290609010b09010f2a0c1715040507051f030e032703030415050c210d02071b090c090b4b030a050601 55
    0x103401003400040c2d141d005009940801400020120303c242c88124615128042c807190703403001d01607591484d04150030200c0c2c000f081a41c6a01c070030f40c1010407424062080a0031310f814824031182a40c2010700c6841d0404101c401e81140d442c03840c1a100c0c14580004e00b10300201c42070204080040b880c1c0c01035000a104e02400031006003032440c00480f20501c1800003900591b100e0081603408513050b19442c1101c0d04034030702e84140d001c402030072000003801c0300c0c14182c222401c4d400c1003240c4034054410714417001c0701d0684180e81191000810700024514450343d4444907804048403180c0314181d40010203840c0300719254054444141c1041d0160b40e080b00c8114075055064001d0100a104004560140c003042c0d10610000c54a0920840300e42007030070b071740d9100641c0c030b50b15000d00781c84075507002203010010481d03007401c0e50070400411141d2001d161649418002c1e440600451108290400b002018124882c0d03030300860201440419540355004841001045003040e000c190b00e5442211103844072000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 984106555 1250 984105305 984105337
    0x1f11010905030f1c1404020f0d02010e12031902010902191214010f050c0d0612021f021c020a030314240103060b03180f06091f1b02100b06 61
    0x112040c40245401580300c501903100f00c000d40710300610840c801d01c8200a803000c17081881d40f4052040201c400182400b00d80a1001075100340c00513600580d0324207030800125407540040c10501c06552450203420107090041001e5217801ca8225019440111703041e009070f42e600d0b907408554000d60814221480380419666160303d1280208034800034403403224440c10b0010034001e0107100740d803003034800035108081640d8000841c02a10203403441550300416140c9044070240325140c00141d0300c14418a6909138503092403100c00f1040b48248001d06882018081c424070200d403210000b940d038031040741d0490100e07141c015010400e000781c58641d07100d25034403500d4600e42d11034170b11441d100c8003070105034a042c1a22080e010920040c01001b640c40b03a0106401d4841803d00302c03500d1894085025402125500074070184075441001040c61030141c1040710700d0400c02c1700a100128000c20b041e55140748800c0c81340c66400e000907030225100c0321150f0380c03107010f006550003c0704101ca9072242da446800c040344 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 984107805 1250 984106555 984106567
    0x60705031504050c0702090406050718080c190e01060f02011125080d140402180f07030e07030804090e072c130b040b0115080c0301030209151f1101090503 68
    0x140070f8014540c85402d1400c61400d01d8041d90100d01403500a40702261100c1e142c1c0c04002ca015400101c2c054006035003120b01d08540c0c07404e901c0c41d841e6103145000303502500b040003d050781000d1040c2150014915925a95030a69550100401d090500c1e40094015424808415900c5042a058400455000903104401061556260048160700718221981441480515040d809a01c034689801481c40c400e64103c0c6058410864071120315440804288030302c4050000c0c1c00c9048040c1a4801801d08000503084001d0304000e15000d0a82c0c402000f0900004004c26503191136040000e003000e03a0021201c1c49a15400f081114020301c8140915200041c004be9080b0b89011038065001000c419001140380f855131070702680e440d4200c90075200c80c500f501c0104007250400107001380209c81403412810600b0051909842d070312041c40060300c9041406c002c2060b0741201c0d8070007400700100030701d01d049002c40c152440c1800700c3d42110007000302d0800d0200480b01c860600400d0401a482005185401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 984109055 1250 984107805 984107809
    0x180303100315050708010b0d14010f06120603050303040b0406020403172503140703110106270204030206070f020111010e0601051804170c07080115090605010e090106051806040f06020607050315 85
    0x81c011948d0040804d07120840e99120b403446025442c06400e45603040c5116170b06011014180c4010b113102d290240745420400c00c00700340040150781d04154044445046038031a81810006400b807504050301c0340d84410b42c58103094809100810f042c0080d003002000c0140c0d8954280300d05c3c0d541c0c00002e800308400450460101050301c000b031660764800c0c10500d880031000c9040703c2c2141e625030004881080300801d01c0301c4d0703801070403c428407410040320306502d0b0505590111f621030154a60080062801c603013400700b10782c01841c04408080181000708106c5801a40003aa204420321400d4003031034011a0f4842003200308040d151080b5007110800c9244040340b01c1891599100c10003a83c050702418a01240c00402030080c1c7c03a510401c814503800c100d041200750803c95a45500c240d040c02041d000421fa5500e844540504542144c240349844c0d03e090310900d0700c0d440714045640c1d849440010041071030b500060115042d02c8881c1d00b03c8504c0d0b920b180c3c0540395440141d81600d903190540102140e030b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 984110305 1250 984109055 984109057
    0x406031a131e090503040627151e03061e0501170a230109110a020a0f030e0d0b010e09030309060112150c08060103151a03180303100315050708010b 65
    0xd08010040c0308044042000c10b008540300302800b11080d8100103020841e00e0781c01008921001401000da5024070100080051705075064814494910000c0c5040e42140d4020300300715201804451514000c0d121200e0004c000301410300482048101c603c200901caa26071100000070307140f0684030001e008030b82d0201250302e054001c24822180d6220171035810741492000075070404a01304107a0046030750511b415141a10a04140c012540c0800d0081d8aa5540e00007400f901964008800701c0e100805400c0c1111045110051190000142e80c490410003803840c100c24122041c1281c004541c2c1c55040c04640c0b28402a40e010000350701c4080184100c02c0d414aa420386148240e92100e21007800016003402e460681c60204040b8040104221080d43c25015003444a4400301160784a10700b821141c500301c504000c3e1081c10100040000341c44030352100d030022841350000c0100c9880f03140c103408108240419010846546140404502400d1400e01506000b1445a00d965041d6801c1281074441 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 984111555 1250 984110305 984110321
    0x60f051809070f0305060f01140d02090a0b06191407030c080c0f0109060608010c0801050306150114131a030f0103020d050a1202010b0109060c0b180f01050c0406031a13 74
    0x39004160001403a0103d100d880e000135441040502118503000490044010f0142d04c50304808000600d0181c4540d145070410b009107038100c40d40e424507281c08400d038004020b507410441d0482400520340002101083c0b0030481c180e80e581c3d5101c810340d5200d00084180c040d8640c0200850582d05031040003440368009095154240c6c403c0301c1c852800618600d0035616804001c0c0c034090b94480e01072001010070701030b9505904080c00c15455a5140202180c0e40314030003488090205013504504000e41c0c410b46070810a16070501d41c1546801894242c1400c2804511030302c0b0440c418070488a225500701c9081e80d10444104002c03c800340e2071a001d00c401f44088100450307050240c200d00000080c0e1510284006608a85c0001486442c07040050082d445941021092060302c0a01e8000114402c0806d0351101c1c07143c1da02d81003c0b40d4540d01c40e00d0302410000c1c3c0c00c042c0d4200000c2149048400000e80110381c001d81c0c05000c1010f10001485844c280c100403250807035082c802e00701c200c01580d004141 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 984112805 1250 984111555 984111571
    0x5060904200a120c020a021008071412010f1505220b03090c0406120b040f23030307030c0f1d060405040906020c010c18150210050a090303060f0518 65
    0x10308034005180e06001036210008070008a61403d103860403151241c803c03803c0c018001e00007011050b081380c001a2070440d1880003074003000b8a2400182c0c5152080c5c0161041c1c600848449846080c40010060a94404d0040e200700f07130070002d4001040b044c0340161550900f0301d81c81310b501d8448541c03a40301e412411620402d1214005900005d1800c001c44021442502c0100240144c05641c030104029038040b0740c807085250b034516404001041c041502c10b030700300d54050a030075003504403440d0142446482d004280d0f0712a403e8071030500000d6004c0011441070f0f0441e40c007042a100402801d8500c80032000300c5100088420403147c151803c4102d401340c81c0f400050a590515545400107070595040a00488000342c000c0340c40d806242c002d00400d0003c45040c20465181d04c07020f01000141c608500c03c44181d240396050410807a030080c045440c44e220280000d01441c9000c0c8110809030624680c02c85c0080d00c1d04000080d07400102c141a4142c4400810b0000480200c0c9012074104101400900d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 984114055 1250 984112805 984112841
    0x109120c0320010915021c0e0a060914061e0a021b12070302061003020904030c11030304142106070c02120d031e0203011a03190e1c02030405060904 65
    0x40300b02c0d1910101803030700120b404008600384903545403c06001030940510700c0c1c17060042c0310b0070400f21140b42e0b0b00820000c034400c001848440381c0c10b810745405078028024002c145481480c0b024804e0012900f046403141c00308407406500d03180600c00352941440e42d4040420f80e807101044d201c1c1016002458000300c4c44403a01452004244810b040c202c1220ba40540c5c50400542c2c1c108042d0184200c07940f094004c142a85602e00d10740100e030710528020001420440803c280404101042c0080c0c1c0d50709101804507501c07a52261001c0e444800c48103ca54400c50750840030f1030380f01b140b195141198200c0e0401414041d00e030b03900142c600206941c0d00300d030b12481161003514200810003582d05079202550b408906004003e01c5400e10082c20f0450b001c4a45c010001402504030460303180408004a2554603641e80c1c0350f4000034200225250b09064107820a82003006c07c140004a08002e00c00d4440b040c0040b41c4800300a0783e8900c906e03ca081e4000c0410311041036146802c1e4040a85640e07481182 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 984115305 1250 984114055 984114077
    0xf180b07021b21060c0414010201051339030605060402071109280225030203120a1103190c0908070b030c0c060f041a010e04020f0a051e0405090109120c03 68
    0x116050560803240c6600064021031b0402003400e0310410800c0741003080c0020082e07400d1102108d2207001c4401d2025040e40e40302e403030400f0420f101d00020408203d0345440c4442d80302d0582501d21444059101c140c8039542885e0208010385413030320855000720740c401801c00034016814240701002c03100900c070101030b010f021101414011040e0213100382c3d40800c100184d4400b1808401d049a0035206c0e080c01020440c88030000c0000c2d0004225031032081600210301c0c1d80e03580e002910010f081c109104000c0e01e8004414020080c0c10302c1003582030458024424010b4500b81076080f1821491031085407115803002e1020400f0300b640c1d500075074024100840b01ca00d003001255480d86000003e892a80420140c18104018030800a8580100034090744030b0103e075501d4848140b80042000d40041d10411080c194101c05681d014840030003010003034000c0120b58030114410b0405088404018069418400043d81314413040c803508003140d0b44a40d544000108240040354204080c6508406000e0380c181c003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 984116555 1250 984115305 984115369
    0x10c0b090712080d0e0307050703060222090e1203160518040c0807110616030c11060a06030204060b03090a0807080702090f161701060e03010f180b07021b 68
    0x90039034902500c8202e6458540702e91310005c56a00c45a004040d8100b8010340c2c0c0002d1000c20b6810403260001c00250301c0c1c03101c6c10030224025900304000c01d000d81c07038180c0003d81c50046030044420000c071352095401c4030512030b0558070309201c1200c00144991510880358040b0b4050070152000030411004001d050207110041000c440c40c614a0700301044484080010103070f4015241161340e49030310302600003400d0840041d90701c2c0346001003040134140c9440c1801d000b04c0c8a203610703c0c100760074042101e4041c02e0550804000702040d0200340c1c000d80c2031080100715981c2120440340540c034410010301000429445401c1c06403c49007040340c800038104030710005030b40c440c03e103613000301002c0aa286c0c29051418240301d661140c0b441a4061014507400000030a9241d003002c0d04440245c2054003a804c4880700180c010450283c000051900e4155600c401807200c40d2020003940c03181c4441d407a1034941c40002c0c0d98910b80e50032081c1c44890740100d1000c2c00d0800b1031404a00201e0404009070922034011 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 984117805 1250 984116555 984116579
    0x5040e07051918140105010e01020a02040c050301211104110418020315031903110a050312090d1e0e2d0901061412100b0711100e010c0b0907 62
    0x4030540608004241031051080b1103c106105410408041188902902d12254403100500c42c0c541484400c000008059000380310251041e039008204108081c028080900290030a0041032030032048540320010720b109039000328800d280c110300c07041d120800100030007000e040c2800d00d155901c0070901000a4501000c4000c86800c80c205002583b01e1518185019500f0b40c4413a03114440e9000380f8004141a04204080103155014544000c10340c0d1082d15007480c2004050005000d84000035800100c00015403245006004940c00e0b148201c0c0c4d80d500c112a008000c0d601c10301d00039262403080d01c500d4017550b2080085000500031680c0100ca500300d050410200d10328492290b4480cae958900a858000c1049001d45402e08209008014940402201d4007403000702885103030319040822a440054407007400208001c40700c2c1079842c0c125140c41e0320485a420551400382c0d4a50203504407442c002c0852004100042c0e4600d81046040e8445a0008101a06a10803400707800b40c00306410745411 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 984119055 1250 984117805 984117829
    0x7060b150a0302120c090d06111b010614030627011416200309060315031c0909180807061104060306140607030e0d1704120b06031605040e0705 63
    0x42c0700141c90b1500008940c00c205002400040348520800a12800781d4680c1d00e200718868000c0070000e410700ca040c800c1e0b140d0384a0141d000e080d14603a80c0e20b14ac00c0060540001c010365120700711048410b8030040034559260026611008400b01c050140e02c515003c248628440794170080000c0f400c2501c030031443d61138600035125408100004410003a000341c000552504081c0c0c400c1092003034034003507100b4031740701d028644600d4821a8000041180b0a0240217600c40110f0b00409440010450008454103503100c14290b5022034030340382002468000740d03c20340c018001c0200e11036a1202007580c60301d100e03a02041c4100c440d60380da900c030318604c080c00c880904068100741d140010aa07080451440b0b05096500e251845110104684c8001940c08104000c80040c02d81d1007070a40000f038600046c4c81d1aa004048681c480701040018003d503d01c500400101e00030702d01c5000d5501c0e610140740d190210481c1c01f252041c100e0804004034203095009410600030102550181521080041c00d103150304 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 984120305 1250 984119055 984119057
    0x12100f090b0118050303160c0f0801091a06151b060a0507020f0a120c0507030b040b07080a140c031009090f020901121709010e090a0507080709080307060b150a 70
    0x446101c5520b58100030400302c3c002d00000300f114414a442c000035502d215a000981d1600b00f00200c680400060301c100310054a00e14003000b4400d0740302c0a140c0d000b00880d2100303881504401020b015103250105045000d282c1c0500494001c4ea940c1c0f250403590340c80042c2c07a1002d156013252201d50010184042800703000e40b0300c00410141441300000b03242c015290081c0040340c000100c40d02c0094070103440144580014208140348806c039040060421302907505c06031030b851000b005c02040080e4691981c2c843d03902d9485100140d01c070310030000e0032150b15201c00c0c2d50006403000403500d4103500d44003569111420710720010000b40c50b12120810384083d600203c84d11a11181003204600c0d000d452030f401b4107900316002001c0885903c543d10f02e00e841c2001c0c103100040000d102940c03039200e040c60030315041003d8690041410107056010061000f121514002254500800c040300c2c80303655004119200c0600079418650130341c072214000c0210340f20350b07580f1854030442400340003240b0010702806016 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 984121555 1250 984120305 984120311
    0x1106090d15061406210601020a0c08012a080a0504051c0e100f0207030602160b0103080c01050105222a05030f010801091509050c090c0d2012100f09 65
    0x28003c5074605402c0b4440196110f440c00380f20000070b1000400468a001c0d0070700000101c152074060060b81003043c2004080c180190062020030350b60415041904681d408180c0140c8110081452105601000780b0480008040001007002d170842900550b81142c09070082e145400c040c407200d16030046c1e4920b04400403400101e0001d007649415030840c4042d81c1c55040c842d21a040041c8000d48454850000600c0998040f412201c0e040c08094918a01e640c40b03c014405940c40c8d0030000d1042e0000381407c8559800d00300042064106035008000e6007484138003403c54004080101c8000d09021f04503983d031204607100d0000c0c80030400c60010304030710860701e5096490a041c0425240360314140c20560702c90703040000e030700e002503c40d004484622001002c00603209001d841c0803400d124010041603403090078182030284074002c45008080798a5070740d1040210b0300400302c400210900c81d04035080f0701e840c10b102285000c07046a968540c0300c41d5103038402e003d081d111005c075062060781e50401200300fa0703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 984122805 1250 984121555 984121559
    0x190603060e0f07090303080c0c1f0c0e060a110c0406140102060a050108031204060209311107080309100c05070c080303060d060b061b0105041e1106090d1506 69
    0x1200040d0a030000ca0400c0c00b20001e1400c03000251401d5418403004041190003000100c80e2104030703055030b141c01a04c00984505d8040000740b500c09103011102491700c18030b449440a0818082c03018042d0700040940a2814085603520545d0340c0700320001030702a1806140341e940e40700e580c1d6204030005401000c401d0310003d42c021000a1504400419400941d442c00005119a51002050750000d403a4591b600304d65a50ba45001c0b00640104a44190002a10110301d1809104e082d40400c00c04206601c5030803c4222450040c240c0b00a40e85810040d80100031400118280328011640501070f80304072403004644203019070443d0840d4403140000358003c9001002c002150364481d000700380040046055040c03082c005070440704100c0300202129a503008608943c0c442c1001e03110090100e294601d61110118082e6010301000c1310121051200f90700780c090f909908801c04d01d00b2640001c00b42c0f102000c400d090002036030010160075400001441721000249105c0c002c400702c0d509090011503064 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 984124055 1250 984122805 984122819
    0x405071d0103020c012322080a050d0c110d021504140708061302100c0201020c09060a12080c0c01050301060512150607050a0201080906132603280603030804030e19060306 75
    0xb01500e901081c14690034810324407d01c00350460500d5400c560b41c103a49400080c01030b1064810646d01d00541030905144181107a040403019400e4449030041d01e050103820782040b80c9943c0ca10345604040510100414007082820b018109900e603c44200c88060b0703220303001c5c00e00c0c3c00001c031907071500d40941000041c2141081071103105003442a05040e900361b6513690004c1d4603a44c4482a16010b428518005100c954a480011009007403466044400c2582d50a098400d0350080b901000c0c1c912680b2a02c0420354400d07401c8038100e420f142e856900b404c881001314400d120010b03001c3c1d00c01d42d2010041c502c40b540c07020024110140304400806010789180300140c0f820078000d03c0c2200d10b030070442c02c0001c0c40c0e0301d65034007906056100014200100145405100e5a01c900b200d82c800010003000300024541d41d01c107140800d00c95030500000c440e0f00c1c2c0081000740c50b00c03800001c002a2610b0003040000b4080c1501c199001401014180c1800d00365801007001e18040c0d2281001076101c90041101d9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 984125305 1250 984124055 984124121
    0x110304030915170402031002030c0d1401150f03020f160201030e060c0f0c03161119030c03060209030a1a060a05060702030a140a0f0605040c050405071d0103020c01 72
    0x70440c00e0918020080e001070040c1c40882c3c00220020209030540004003150b4050203114113007040300b07038115200d091606940500c2c1e084001520000c918044410b0244241e1344c1c456412580c000320b81c00e01d00000b00d4021a08514641100380500da002c2c03060170810740f40341000d404070585a91107000042c01a00005051b540c0e0480c851503560800020b0101c0031541004032103078168001d1a265561a40382c03002c03455480b4001c0c160309080a2406a8410047c0107000720605020440e00035801c0290445510484c0e0b42510009108681d02c170340c2040098000d4029100807000141540e4030701916131139090380341848003440c032a10b0f0f01c4002085150314181590101801c1d042c0d41042c10503065902003035642d003000d84080d2051700d100f054880d0b288410040c0c540003a520510010940c003032407402d600581000d9078211008010703c0b40129075804d09201d060711485655650604d52000380700c03502c090007800b580b2141056001c200782c40e921002405541e4506015120b008015012710800f03c1030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 984126555 1250 984125305 984125309
    0x20a1b05032106090c090a05090f0103120f08070804030c12090603181e0f020a17010b060c030703080c0c030c06180307050d0311040e0408070b090c0a0303140d1103040309 75
    0x1030030314180c007803041d903031558480c13540d00107040d94500d035598031040000b81907401564843c0b540110b4640401000e002440c600786d048a114400754200885c52400c00e6079031a03601c207070620009000a00150b00c4912900140350000d00031b0801044105040c2c03121150810645e03103030310100d9011a410011307241d0500c100007402c40300703201c0c94100d41e01c1a9940030f4280c5102c01c3d038013007203211403454005000c08802880c10301580100600700c503503501c2c011040d203140d191102900a5103044801d502c1410040220b5120442580156103404031580e010b8070b00100250045101d00030501140c07861003070800c010b010b0300d8110030045c4483d16107901c411040018003041d8100c160414444880000c800240091100742507041c040b43d54001c50860351000d000d1503110328102220217080c03000b4025607100070038035940501051040c1c0c1d6200c28065a42c2c00c1803070340550f00002040e00820104e403203030300c528030584085040c584c60000012010b42c162218040074200e408800000e10080503007160302440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 984127805 1250 984126555 984126607
    0x409020403050114280f020c0601180501060c0b01180f0e03090a081204032a230406080c0402180306100807240c080702090709090f020c0303060103020a1b0503 70
    0x2c5c0041c00c1c0e09004500048003005505522007070702c500061000c0c1c0689116030440340480c1d08940e07480c403940914080c0e804058010178075040000c40c2c030134401c812954001e0b8010600850310392911101a0b05140803c0409201ca0f6942c516040584071a004100c805040b20004548a0f40020200000303c881548185281d07404070342c0d240c0303416900006590441e070f0044000e80c8100170551a44154407620444940030b42c0305d0307402c0410392903202c0f41c0004c00c0e003405181c039001481e603001c00d100440e00e00b8018601558004002e95030306107090303002050034641820082c2008076a00002c24600801550072010b814012103080c001400100000d070000c00702c030011400307034650710641c00f110345c007007661010200032001924000780500c80c82158029503002d0190f40d102c1c030385114000c0c4590080d010302d140c0303d030609a001e0b4a0f8800c0b4000d451340e12605101540c0703185c64441c01540294004054901480580030012030349064402802c203d06000d040999070360b048100f2425100826031010385 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 984129055 1250 984127805 984127831
    0x17040b0a0b01091508090f0304060c0b010608040c0b0c010906020f0c062211060c0d0305010807081f270302250819061b09030203070b0703230409020403050114 70
    0x20416038018042441d0040c5c200181c40c1d8a5140180b4144800a425170302c952100150004030300d50b0210582108070b01412048510340d0701e500080300c2d05002a81e0140104030380b4030781440040a43c2005181c010100310000034006680d9403068280e801244031081b42c00b902140c20b4031040d0701840603a074400a03c1d500354442f41d078150310b060300c1003920040c0500055650464030b41151541411116003007500c00c21600320002050303008002d00800d008003100e501038690009401c2100041e43e080040c07005041e006903004a10440c40141165280030310407038080380b214a412502c040c603a610040c0a68064042140380380d440d1100d8995140384a0640d04440c2c008100c00d400114034200468802901d031048070f0898200340c40545405004429168410304030704e0ba200e82c10038980c108032803081d402c2d078200036038546840c0414006c1c0c440140c00300d0302900c800c01405018180b14a0394010400f0130b2800c003502d50400c0d42c12600550401c803160381d9100c1000c2080e90030119055844032040c0c00c15 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 984130305 1250 984129055 984129059
    0x607030606120e010f050903090103060b03100303120207060e0f120301050f010e040b04021b1e060f2208070303050f01081e01060e090c120303090604020f0117040b0a0b0109 76
    0x40900b490000d03003584182d030760b65002c00007100a4010101403000110184168148065030940700d510034076007107002c030b442c1090014414404e0b00c192885140c2c549604048a481d648050302e81c0c08100410b00c468541c00c0113001c0c0050440c5c40345c844901400402800541e01c09480030b0720b0001004a0020480400e0004006aa4880e03584407040c0c1c50030301e005c4419032105004100a8140080e048e6031050000c00c0210f048907008824503018a2071104440b51000a00c4a141810f103042c4402c00b06070b00480300042c800c07100c07007d040340c104032540d0190308000002d056014050b0010b1408890700580043c0ea0700134554903010301074000c802c010a0003602d51521404580d07826000c41000403030002543d801c20341420030f40c007840042c560400c0d41c03141071070190b076104d4a80340440a085d1041c908040c00340003c1e0000000e50344903038a1400100429140c80d001c0105040c0850502410020300c055203c9196005a02117401503220323500304800c40c103003e6030000c1554018070009041040c98202 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 984131555 1250 984130305 984130307
    0x408130603090809280b0c071d0103020907050c030a0215150f0f13020c0c01020f030a020c090402310b0d0309091107052a0406030b0a0e1606110607030606 68
    0x4941005204440442406104082c842c1e0f205e000c2c01e00424402044510000b0b50204602c0200020142007090710382403a101d007450030041c01c40982c3c2d50340e2040d00c600103100500308440d0381c580044e00c40c289542849161242280341d540191008001a00451009003840c226000c2184d00324000940c040b582201940c045020b898190060724410281c01a0b4458582c5131000c0050b0144032000003559141642d0071a141d4645001000d14018032607100c41800510002c810768841d82020760182c054517408504125103940080c00999020007400980d510091a50549410300d02c0881c21380b801c1148855143e00c215074030205075078058101e102100e40041d91020050f010703192880c000085860b0011050384140c01401c400138698895051583c1064a44003110444603400c40c0203c0d000c49071079800d100c10f80d040c9100042150300304501007420180030340c000000007213030300e0210355141138007038283e84034014070740d000401007110010707a65a144418000b1343e03841034843c1014820117241080c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 984132805 1250 984131555 984131557
    0x304111c11150a121a030a0b010f060305060d0b041505011202030c010504080d051602091905060d0b0703020a020c030706050a030f200f040e0408091003110912070e04081306030908 79
    0x240c00b611580c1c030007005d44035000942801003000c00190840f80c00e10a03918000141010a01a200ea400444403001440c180b182c040c0a1013884041c00408842d4055600c0344101d010190044400344c0900010741e01009051050314000d207110500180a41d000707006150030003840c0c80600341005001c0100f030200d500005811580201d0a1a10951718150003094403081446024020750104140086c800040b1035000d2502e68420303006e0b41044192110b20821000c5407803000002c2c42004400f0001360300074000d03405458411101e0050b1f8050061380030010b403c01c03001c1d808c020041100480d464402603403500c582d03000000d10742c808018038800380144603001c44e04041c1c100d1a00c00000381440700900c440099400411001200200b00e05042c0340c1411150403503001c4038094511180d54104162003402a880385140502e0f15a2078054240f044c0328904081031f82c590020b214000001810200c2407030001c0c80f5501861140f52070392000b40300c01000b00d02c550300a800b00750511078203d0209070020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 984134055 1250 984132805 984132827
    0xc1401110d0c03090519050a08030a120f090b0f070e03010b09040f03140408070311010e010c02151b01050a0b03060108030319060801020c0109170f0304111c11150a 72
    0x70425801946043c58129100340f11600182d030003408030461114019014641c150070b0b02e0080790742480c01a221f14003983c0d03034011582e00d8400035003416504012205258441000c1d007a80620124544003107072520040e028068a0707041d00c0c15544410031801075071111003000f2098040f4020b103d8008804001444c4240141000e030548140018240070140555a61003048030784903d181d4030b5699441000d5214105444180d480c000d084d05a03214a41c480d4074a511141016110000390300d01c241c082c005014515045011803040401045a4601124410104002c82c84002048510b0702c210700100342ea0185181078043d900160043c861f031031011064079800304040318000c140c04940d0032560003405203940316042035440010003600c9030f40b06411490400b0b024032180507a03100b07400680e03001445140d40c01c8600903000c0c0b0100c0c000403011b144048804d0b400600c403401d03205040385500e50703441184c90211602d40403058040210f007020100d02c083d0007419170300315040007801c03103018120401c06 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 984135305 1250 984134055 984134057
    0x40204200f03060d12020a0209010906081f0e03040b0714060f0f0a0b1c0611040f0314011b1e03140f04050a080a021e0d022a0603040c1401110d 63
    0x1000040d8161510184080c61380c0d080b180d504000064600c020703440e01280d8106034010061b040000c11054510700500003101c20803c0101040900520f480da04100240321005020382c403020b0f40382d1102d900700007400c0900821802d8a80d03904691800020424080da00040150000401c20425041c600a00c0c1ea10119591a0402a594550240f00240100020180d11140c0c0c42805090807072001c401240d0680b003810100704006101403c10104e01452046198030015140e080c00028424401a100c1c110101e002080c0704643d41041644001c1c01e05042001030a0071142e45408005040e540502c009241010010508070242500005c0d00080c4131100c4c403509040400d081100800c001058190000d20260300e400d5005002034a5400d806840b0041d0303101040c1f030035403111010803c81018521500200003c803617003003100c401500342e0983c2e071400c2d0040c5040e2060322740703032040250320132403041c294090080d0030722440f40502d0850100450400c00e101000c00348002e40091042e040039a1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 984136555 1250 984135305 984135307
    0xd08191d16091d1216020d030c050607031b110f030d09150902010903020f060d09030807091410030c1404060e150306010e061e0c0304030b0105060715052d040204200f 73
    0x5090200364401c402080080d001f1406220740070a05501241807686036114401360345103500c407468100d00b038640b801c2d113207061400d860302e1442246000d845013803880c00c0301101341c401030050301c0c1816040d03400202240280075151200d00c0104101e051940740080038800c003c01c1459042c0e00001c01920740da010090180c0340c600781c80315103542e940c0103175403c007071a11809100c003c107986401040d00744d040d50940c01058401c000824012200c00680420a9004d0040501c8811040d01200540700e443c0c10034083c407482e002c0c11028507081d00002e10290513541c86940c0440ca00a007805401c0c465042c2d8101642014014031025a03449540c0c6060540c04891154540003207925400201c10ac11040e500806000500030043d070b007010025101702e84c05071580880d00c0c0e0383c803800d10a0703600c00c0d1500204400c46c000403584c440040c0f548865008040700243c0b0241d42040610200b84d03001042d00c180e05801d02d00c041004600e010700405803c00c0403041e8802d00c00700150030382c94841c0a0301c051442c0c5410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 984137805 1250 984136555 984136567
    0x2011d0610062105070528140403031205070c02100519050a051c1820040501050904061505090711010c050c070303111216050d08191d16091d12 63
    0x72013541a641c5e0526914140e202203a9420803034650800e03410b20001c04070301380c8c0e000858242401c1c0f0a0700e048035016191310f048284040000001090b0081100c0c091164030700481000d0307152042c1540502090b40c45040c2d40d01c5400c6202c903070620f00315000008102e403c1040c1ca40b140c1d030000a403014694440c911045000080032210090f054009610100c0e40001114505001c8800d420000400e08441840c810301080710601059480134002d03103402c140001c01050009105a001204850700055268012515480040c0b282201a035030312001440403450001c50039000c2c0300300700381f0302410305105207400c0c800840d00c1d451f007040e4480039091110000041003041d00600400701e41e000d800c1101c0360b4442c5030a004204440601d0801da038188280500c91200074010841940261102c0c0200c0e00b00c110035803040c00c05420051104050814200081d00e1003450400a0469101c464291140070381c1c240708448046420302c800b140c6800c040300c2084001d42101144c2c0c1028003005c0c4051603a107103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 984139055 1250 984137805 984137807
    0x305073f1a16030e06010b0a080a0219030c030c030b010f03110c0d09060f0206010f140f090a0608010c080105100324060201061a2802011d061006210507 67
    0x4101d030064540802509000c02c03062907448004244074101945080140340074002c02035986503024081c900d4030036010080a45c2403409840c9165200d0151140035242181110038ac925001d180415500841e40720b0700003810140d0107010b200b0185409140c208424052140020800071020124400385669281c0100308403513403c045445600d030040480d0200c80100e84018580c209500c102c0c0d0005512040410328a03101180c00c5048540040c55412020b040042c590401c1200a00003640b000310007070800c801da104d040026120384040b04000407640d19000e803150a60316030004001c2000b01110040c041c540d1504c3e01d620079168140760005d030707042600a035012a03003444544500c40d0b545105001034800d5054020b0f07400e40e0030300d030318440e103025412400d1209805414041d0242e111440346000308810840c0080e64110729a20000c01c01221154900c10744801101c2c0ca5280c40e0006010001201e080b40b0701c110003086280351408501281c3c00701050000762061145010507240e0021039074032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 984140305 1250 984139055 984139073
    0x190b0a030c0b07020405010803040e0c0a051603090302130c052a060a050106090b03060105090906031608070f1d150619030e060105100504031106130305073f 69
    0x1840c1d0001401e01059100e003680d442c56002090101d104a05260000c03403948030204c00c0c2e608940f00c0103a070081c151592555084580c00440070082085024003417419051004920004681d000e0b803a074403945030550040c481d440000029031882c0703604055030100c410f80e01070125041d07108100d80c0c01c013402c104a8403240c440310200701819600c1c86007209201c04141d40d50701141c1205ccc07060301c1d0329601d141d0310964490b403070004640290120702d061200c0202030404010182d0b100b10010143d48403981241d60304030001800b0b8118440e2a48140790500c40c0c0d01c8040303030301000741402d011030501d400c9201c01c7c82344201000800011402001c520100f202d81c456500740c0d44006220710000b1038003440070000070001c012003c00a101481804000603650502171b00c0c004283c0c6142e036070185032504603299090306070315440510790054004c1000e070382040c8503002000003135840b40001d0000940f03002100300075802518038000704000c1da20f091024124410041001c4c210700e6294401c1443d065017000000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 984141555 1250 984140305 984140309
    0x50403031101061505030708010e0c0d0f0b060a030c0908060606092b0f021c1214070c0b070312050105030a060b03012a180311042d090308060603190b0a 67
    0x1020403141c0d103c62140c1d1700320011750320408455480c0480c07a039032004010031564003901c0460209904104017603252800c1c0e004901000d001c802d01142e103500a0000c1421a070245001e03100003945c1d512407280840e4000c0d03080c401410000c0c01032907a400c20308001003640c420003d10318454058411403100310090a281c50100100030764070100e020505050546a603685400e04a00c18100e2610f8203003610b02801c09030900c107400028490b136100c0e512806075814448031f00d23034001070b500034070655000442038050700011384003400c40d032130b1516442d04d4058050380409840c621660b04000060146e920009000902640c10520100b03a1480342c0e00400e0051000b1500754014481100360002640a524100040c22500350303118440d6981a0302c2c00a6420000d010050094800c108020220314080e00204181580c1031000760341d1042e0f40b00032040001c007024404556603242d114040615030009a00f81d449802905c0d540e184d490624006141e401c8071054000465a403003900125945038140d070301340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 984142805 1250 984141555 984141569
    0x20304090e3c030d060e07020316062d020406020d02032104080f0c0a0b0703110306042a09081006061b15020f09030d09060c03080901112a030a05040303110106 70
    0x81c0e180a0101c4c0e1601034261406415030030b0303034030301c010481c4248000201d035400d42d08003c1c50050f005065a800b4050442c0c0c4102c0c501a0410178003219108545070780410060700005801a80c4529121003c0c0c00c0200641190055420520550200c81c2284103290060000c04070350381c113556503d20f40221030f801148281200f0040200304010212400141700024500544514456a446e800101c042e101400d451600340c800c1840841e009051a4114000c0310111030010120000c0c040110030071a50410a9403000034240030040204000038002c05107803c1045005000c61414502e01603e008001d19640884045041300c2500f0b00403d0b15405000a0310040705641da180030311404101e40d00305c405144d1203806901200c0b040b0a0049600004890082d100d0201415650301c05844084005080c04a00d54a80a00324454007102000700001100c1070311442c0c20240c07400c001c03540b030010300b40083c130785070b00c100f216000c43d542010603142100d0f4145804078080c0f507001500d901410389548240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 984144055 1250 984142805 984142807
    0x41208120a021803030f0409050406091b030b010e060604060f2703020108060f0a05150c0607080f0610091a04090218150403030e150702030d020304090e3c03 69
    0x3007200c4000d50028001902c071a0388490503608a4010107440b403045002c00040d801080004200d0b284140d040143c1c4240101030000f2001300c2c80d100c0010400146102807449051401e00f03200b00b00a4a03501303400342402c074031119090300e40940030070f0702c82c4030350f025400502900d9511a442580715032550035200280e1680d401c0480e5a0309601001c03064039000480c0416102c100250309400c1c0070340200300c044002441c1012051505041c800712075480104a0170b1200300b009200102801001418040c0700c00380e035803910030f1030040d0b40c83d0f00d98440900000d10138100c80000e002d841d83d200c414070302550394003c0300d50440140740c80d10700c0c0180315a9000c2c6402c00c0c004546000f940703000040400030004103903010b0301716808921640c411480389000c010042182c0c4e840c440b0030390804407500b10fa0764071440700035482e282441e00000d1400c01c940d20440016880024103010805841c000da01440c40500c0040c40c001c00f0129050360030469400d02504501c030045410007841107031102458000d076640b0152 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 984145305 1250 984144055 984144061
    0x91501030803062110150e090d0c0c1703030a06050103090308040b07230306190305190618050606030d09050904020607050114010b03070f08060d03200d0201020d050a060b04120812 79
    0x180b00a4038a4001b04002c03030508003c00110740c00300924041c801c02a4030050171913607203045c005494805d5003110956131684d900c003000c07485034041d01c4012402d94210340215220f18080c4030f004141d50160300802e04050802541000180e0441403182e0000e5203c3c600c410540d80c1d040e030480d40183c2c444507504510801e02d214030301d1075108a008601945050b40c0b034001407200e800584810354101c0c07100405135441005101001100809039201c094410702d0007149042c207002449840b003040e00c6003070764150018414010146410804440082c205050100d025803a20001903a5004010000790090100041d03100c10800298010a210b500f420b552808558541250710350303a03041110a10081511f40e140c1d00d45241c0180c0003244a00f4000704880c5d80480e241d5801c9034104407120f10808106040719090701030f810300b0310402810304000d074001600c0b00e442d001d20f0010b984c0b0140c910300140b4030386001407040001d440101c0e0203960700540e5041da43d941514004985200310044840c00d00070798018 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 984146555 1250 984145305 984145333
    0x20f070803090c0607150209010e04020c0d0e0a0b0a03020319090506010e0c0f0414040b0a0603021e160816300f05090d0606030609030302030915010308030621 70
    0x2840c060000041190310910341c0c40188104c1e441100c4d40601080d01043c031000e80351170f6580007882e5456043c5440300394042008040780c20382e006804030030f0b6250002d0031400c01096202942580302407049416139451464082254600d1007500030f44000c145e00000000e40c403a00b2108510008140c010080140402c1818083c0c0c8900d000c2c007030704d010240000c010035552a440015104654000f42c1c50914151034080b100752445468400a07030895115000d80000c2d83d80c04804800800203903d000d039072100d07000000001540250000e1544180a0090b0b0082854071906e00c5501c690061b1880e070350705222274002c41200b034a40c034001c0401341804610b200301510f0100e410740c6500d5030640d008820040043c150749000341059a4000200240071155661402000759a0540d0152200144440e200d40301c1c8400c0d5101d00805401107500007081c030102901c10046030701e00d1201030311781d0242541542e0303c035070b101d10000e00824401d2403940d105075080641c07440740d42084000e00044074010310031820 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 984147805 1250 984146555 984146557
    0x1e060702060c03070308010801020c06150f030f0601050a060306180c0507060e0c1305162003030114010e0d030509041e0912021606050910140a0207030c06050909160201020f0708 78
    0x1350172400201c0340b5000241ba02014002e950a4080e00d00160001d0381e603041b00c021540c11541d081c16882108002c060701c464a080c0007404230701100700094a050341c1007400b4402280503940c480400c041c64807408108010f020b003034102040742007180c04030700f148480d2004c03105801100d4000c2d0910740b8151200c0c0503810300085506003448192400424184030100c0181103131422107200f40562450341c3c00d08590361041c05490b0140c0e4410444007881e00c1303580401813542c2c000760000207194040074241d10301c41da0080100c0924072400c43d1030390b95021040d07030014807900510f4882406540c80f01c648900d881140d007101c0f80c103061685c80070004080e0303d00307020360714519101e4010090300a43c103001041c40742d1501c01d00103981182d110303180f800702080140f05400d4040a15001000484d03c20081144000401011004d00e50f90040c01598150b040c24604068554000c1044c4601005218080e84820310240c5c0d00ca201c0b5806821031551040042e40a4860321282650708080001d10100700103c140c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 984149055 1250 984147805 984147817
    0x60315050103110d0206070b0a1b02071811042310230a0905090a060504050117010f0510060c03020c041d07080d140c0106050628030b1e060702060c03 66
    0x314a240f0304200d03100340a450745140c075001c0d403c40d20800c0381d4004988444c03603040d080220076000152846061038803c0d55003400d100030100680005008100c5407500c003d091445a881d504100500348451600128905c582e1240c041004007058240424544404203031080c00c0d0040d01c0da2214a2500f200104800140f101c80000d030981062070941081100e001e403a80798102e0b441c2c40c0c441900740b0080051f41140208092030a540700e001c04546c0782c940e40141402041c14201c1c41518451158075a800d540c400300340000300a20304030400801d0f0907940040b20403a201030600c0c07003400049040032800c1251004d005034100c0e0030070b2342040c00c8a8001e0085000e0030103c509603800b66031100901038454640121100000310080000405a0403681c0103100842600d03000262450790f0300e0205105400491070031030301054107000a84900502c034003040e48040145030400c043c0340c401002407050445035642c10b02d4045502a0350301d01d074885008842d80a03030000c00c420340340c0201d03407022aa658061 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 984150305 1250 984149055 984149063
    0x2160b100503071508091c03020d2703080a230405011b08010f090515150d0f09031e081f0e09070807051c060c1b060b0f030d090306020d060315050103 66
    0x1703103000444905c408038640100a40ca03100c00c03003810740c0b01f1108a010307400000d1200c110540da9401c040d07802c0e08080c110186404036000800911003a400c0260002d400101000c400e182844c1c101000210f14000201825018002c41c10b07060711141001030040c2018460b6400300483d00b40854151504039918034101c0b0b058055401d1029150034a0106031002594102628029248201d03054030f045442441e80c0d90a00c041181001c8816090704203132a00e111a003d07000ea40c49491100b819804a00c0c00e0b010320310003400380c103000c0701003c0003000100c00900003007641d85144034001c0d042c50081d602000504425240e210b942c18803855454407003550380b0071010584120500020503007880c0220743c4040301c040c2c008040c004499110b203000361412401c20820800181d400e041030341c0310500e407200500d015200016200300c141046c00f4a0140700c1c0c61061013540948030441c62194000684000c0d01e81c094000343e00c0700301d05014280a04900e40006080c0d210300302c080c0d1100b0480c0c3d030085041700d000b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 984151555 1250 984150305 984150317
    0x70f0b0c3c1e280302030f0630071203020309031b0d06111e09030c040608031602030f071d0f131202150a020703020f0102160b1005030715 61
    0x4507469080c10710604126088250b103000405200040c80006403200110f14000950500c42e01581c3d0f01c0103102e65104180402c1d8040b0a000c1d041040440781d0350b2003101500d0308402d28000c01941c60400742c1c001e18080c2100d02c005501444d0040070b1240200070720f8071200e002010700080c80d002e5243d8003da000030b4000d10034002c80e00305503006806481c0c0f07a070102501c0c207205e059458a520000d015421403203d1048400c101c0d040d00c00c030800803000c00012012f4841c03a2101036443c2010700707000500400c98800d40c1058003d00041c0707004012201c0c0100b80d4041803218001c50310200e800d00228505044d500e004071a0001100c41100325a03820340300c0350766241b1400f5036403222241070801c004d0319094242c00300010781000261a203400c18005d0341380c40c011904841052124041100000c0300d00c00c81894001c14034404143e010005041c101b06240000d506190150b412a044840640405486809240c010070546200c1314541d001800e005003c0da900c1c1502c40b14071f4801009103000c40000100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 984152805 1250 984151555 984151657
    0xb09010e030607090e1f0608160c051f1b05090102071203020607110f010f1d03030f04060b060f0d2c1507030b04021306080c070f0b0c 59
    0x2501103440c83c80b8186503100c54825a09029420038410070080803424140c0c900212681c000d03443c2c07540e000041819580d000c1117858540407180508010405031001c1c00303181c1c3c0640000400108070921943c0030402444031118141940c24054544440503c2d00b01101d500a8581503034020000c01300c02d142a02115980b640c0c808030742c203c888400c1800b0300140c001c1008904004c0c483d84020300780c040208200c4650300e08032415103086802b5500c05004050380c07003900041c0040d000210078000b800f000c01450842c13500546088020200400080219980300152010342e5259030070345d081c2c140c025003604d80703d0380c607020007000030070400303290f801c00e91542032144580c004c04080002664041c0000743c45d801984000404132004098075860070700da1108a080c0c072940f00c1e071000d002c40340044078140c0c0423245840f0300a41a4070700500f81c0d1943c141c080000f0300100701c1c1100041040c0b41c1c400001d9506540b60b902c9201103002d2455002c40680601550b8072111804440c00528440c040c0c2517004041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 984154055 1250 984152805 984152809
    0x11190e010f0603110c03071506150c05010e030a21091203050912030103030c0f060b060715050f101401090e090c030c102703021210060f060c0204021b03040b09010e 72
    0x401031041c0d845c0c140e0300c10821400081c040361a4100440110107010940b00d4860041d070500c3c10704009040d0009007200c0d13602050002c24016013030000401d4000e03500d041d481c22001400076200c0c0d035074840c408004032030041648003143d01c2081501d0300a0a10200500c00e0f0f18000e0142ca070955011030288030f0031311844040002002128100da525032103c002d4554a991568080e4140d03140c190788003940c03034164104030b4450000412a00f4421141c3d00003140032280080c0845201415210038030007848100280d500d400f100c42425100c81c0c80c075101005d1244401200c510b007031034001c4045841e8110030301c048050001070410a0748021070940f48244010b1040c003892451188004000030900102d4508034100101204a0580130903464000d0030307165000302d0711920340c0005404181d8046826624400c68070710958000c0c6c01c042c901c10103d585420780c000e00120140b0806440350b039000403442d020071385e44156071130124121004d80c0c0e200c1d0764845041c011900107004040c00301d081880185654 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 984155305 1250 984154055 984154057
    0x4060c050301140d1703151c0201230c070612050f10050f0d0203010207111e100813020a031401061d0a0e0f15060a06080411190e010f060311 62
    0x190b0050072503d0f002c58680d01c100442d108498a080d1083c402d04204040319010072401540300b804002e01503280140a14180122000002c03000c0d500d401c80e01c0c0d14200140e0380023000c42d0380c90f0a06500141c4851040301d00600c58815840180740382e10035a100010410f0700110154108686d501080080e40d450140800c0f4007081110342c90800d40c1e009000f0b00c442e242407240b1800c5148060141c1c1c0a208066011030f089901c0a06d09031010341659036002c0003450146400640b107204504030700c1051860b040492083c500c926042c0c8103002d0302800261040b00c66224201c00d4940080075a108103035641050481da9a05012074143c65007055000b089070600b01c0c0f422084c0108444501da01940e80201010060003103a51000d0345009046c0768001d021410841108000c4425403030101c075060880402000c3d0340b041d031100051012900404c00890492a90b80d408040155960070703007440c0180520711454215003120020000880010038000380c00141d81003500c1e000e0300c0030450142500c81503102 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 984156555 1250 984155305 984155309
    0x131a041d0a020112020c07030b1005030a0803040308040f081b10020903070b0c013306030507080402010e0f060a030219050c07150507060207050318010e010e01141306020604060c050301 81
    0x5568801c881c4000154480c2520500c0000c0741d0b41d0060030f00d1003500c070b11801c0c030105900036a039030a51002440a130300c0c502011030004000860060603019501d950700841404000d10290070300c09420005400e12004110803860164408411940c44d00404000c1084500740b8203a1481446400c00c00c0c04540154400c460341400c004004124991504c502c01c0e1040d4044070941586540301c10342503507400d00d036040c00c424100000032814445460a42c0b10a8142c01c0e0b544190b00b01810700c018880104d0b00201e01c6508140c0a103890302041c00d101c404240004a03001c8866084030f00000c8012030550702d81c0c090709030a000000a040914110103080f1541d019032102c0c28006c1c0c03c440d404000c00400d00c80744440c080011b091990402002c1d0701d422040f600000001d4401e0b420000d0000e51003402c0c0c502c0e0341050740003401c041e82c503180250002019144008440c0d8103000074108104024520b80701590009030345402200c280613102d410094951006a80c00c4038000c0c20034a80c1480c5c1809142980c0c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 984157805 1250 984156555 984156611
    0x5070810050405181603060e0102090609190503031b0c03150c0d090501060608092e0b01021c020106180c021c0c060e1f0204080c0d02131a04 62
    0x55541c1410200401001c0c0500481c03400b01c03000304e003030702508801d00005403032100c0b1141049026180d400c0c00703020b45110248400e800d910400001046a03103110607685a4201607801c0e1800500038206011b100002d5008958544004900e5008488401000c101082d5140003a5950508204149070703540444804110308202d82c00c0c002101c45407034102603c581a41a03401241d42102c5450356400c41e2141d400c1a800030303289008010799901e04002c3e60361440c40c01114401d0400b0384020035041c800320b4021100000e40c58030711800260384204a112040b40014012042d540080d0720013038000e0440e44030b6444c4440007400d0100150000e84525018402c3da5000340903254140703801c210441480c98144030500c80181d02100210700184106802c09000900624601c10b820184215600c0c4c0090007021081c01040140010600441d201a8004080e190805000c15910002d00303442030240c16000c10034030b000c00122102c100c00b9501c3c0410242a501000480884056228904890340361a1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 984159055 1250 984157805 984157831
    0xc0a050903011d0714182e091a1003051314030301170f060a180803090d350403090b030705040510110d0f0302041a07020301060b21061c050f01050708 66
    0x458014200780c99126151291880c0a42664487d0704020540c02c0c00c5514a060448802d000c10840d0784102d02e800b034503100c0c100208840c8440010340340d0610805150426880348040b0300c80c6007120700301c0701d000c9520200d0825048440740019549420903c1a10300180040c58160039008001c95140180c002110141031681c0d150700c1d0b000098903000c4829100b1030900c451903c00b00700104040d5006d80222009410190400c040c01004580e101d40302c40c00500f40c1c3d4180460b00f904407003580000342540513103011160b17a00d04040c1c81042242c0d016100100000007048103541e4048010816103404039461180d60a14403000c0700c02009445902000d43c3c4a00d400d041040d0164500c500040010b180140c5020745404240c01a004400b0340d040d042c490204160045250a0042c00094000c824485003010700b01d50396800c0c8111680400d0b0041c0006e1030120302c043d10394901c086c0900d20f42000c1e1030055841d0b803070150b5030f4041880c0b0b0003213154600004503640c90f2081240074012145c8904103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 984160305 1250 984159055 984159079
    0x2040e040609050309370807062a0c0608070c020604061b0203030a0c050709021206060304060f060f091503020a060f11060103050c031507080c0a050903011d0714 71
    0x1203004202e084010382e0b443c8010721401400744e49540c0b2540122800c0b6041c0340907006c200c10881341c89280703070000e0300e40c046840b2814844860000b0300c0d001201c3c118509412616031400c0c481002080035050014451024030b42d0070180203c8082d5001111515900c41100740c0c1c80000884800d5040c0000951150080000704805880f03600b42c000c803180041c0700c5110f84955980000c0c515070248a03180d010070301c40d00c008414060248802c0008003588034081d131401c400701c90000c0c0745203001040140318201c080040f1301400034076840075011001851013000815150b8030074800b0382c08540304428440c0e08000052800c840c01c503c81c5000c40398003419412440381412000d49420446541d90801c1040a452815100d0010810703180254001e002034000c4111001c00e2500b4145820b9234810110f1007580cd20140940c0840b400b5884407a0388456600c2c2c0a002c0c008440078482d11303c17119030640c2802100741500c2d5041b0b5801210043c00340c211890107640b18210f4400c030401c4400c69900188400034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 984161555 1250 984160305 984160313
    0x6220b09031201180b0603090a03031e02030c1803010b10050901170a0b15120c0d02071b050a08011e091e03080a18150905030c01060b09100302040e04 66
    0x151500264010141ea08280410341c8401549800b6800003903d1a0701c41d400c80ea50752514170549590190a81e03405d0716610740701100b20364602451000a0401d651400fa10200740c10510401402850000081d5544d007020035164030a9081035200c85101503500c0388020a0340744c14460394800075800b07054100c860800391000d40e065080300300440e0502c12101000b82c1051001000c081c0f00e040c02c8600040d07074000600500c505200c01c0088400d10781e1040040900141c15258069400b1081880580d0b1310038000c400000a40113405008002c43c44a0849000c1d112615841406652043c0c030010a400c0da1400d01e14282d03983d4505d58200e00390840141c2400701c1c03103600552501402074050340c103008102c1e402440c61058079401a8001480501406012002c0380250075113109141c0c4a9000342c0b0154454041e0000d00c280b0703044e1b10a68948000082040070710070f95050101c0c107802004003c0e03035040d5444855200c039400900c2141c4808079100b655000340b003903806640000002440c4e551b56596 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 984162805 1250 984161555 984161573
    0x2060c070b04150b06040803030115111c030b101106090105010b160503250b010911300106020a031403160f02070312202e06030804030c080622 63
    0x2d42050f41030b11030302a03010903115034008000410740b20008696a602d0303c0c0d02c0e1403500d4640c014007810803800e07a012103840c4000050700080c01d5030405d0f92040e00b0400000641c02044588a0035801000f01250b400c81280c10452004410190905403182980c880601a0032942d00740102d40300440280303d8031030400e22a803c08020140f144048070b25040314600c112054000b0041d0f11148550101c40c0d070301c01c0100c0452108d0041107440300500005890108410070350058062003034280c2124a610340d40d401d02e00040250750100070180e0040e558581c50000d444504a200640110701d400d1003d84162041504a1344200149a0a214024240394003110440c100c400004218031030300c0000300102e2140710305038212a1540d140c05012520704201c201100001440c90001504020800c6e0400030084102100e50308032091320303004c00e811500c140401804240c1014204030301c040740110030000201c40020940701d102045410b0390740c1f0341d58001c030600c4000841c4000f0046843c800c0000641100c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 984164055 1250 984162805 984162833
    0x13020714060903032e0b040602100e150a140106020105011703210c1c060609091e0f0e010e030306040627020d060504050916060e0a05060c190f0302060c070b04 70
    0x6000c2c5c210340b004074217508203901e150021507a81e02c0000d001c000d01c94040041c000001102c0c20103008165a12180eaa20350786042804415200e004002442c1e4810b241d1003000004000c5c05c9413a0a035842e044020300800d024000d00055030024541240171200c004152034124440c42ca0b840c041d403e40a080b01d5402c1f4029003859030400b0180902501c4d000d804560803e00c804070040012210314110000b02107440c0740e44080c002c1031030408848110310300c80da03e14868410890020611411211039000248011030f07200403030394640304820003500d20100085d03004640c100c40610030076840350324151001c001c003001c3c181b14803800300390100c031035803150007405004001800000714141d41c1d60104099a000b29004402d9170480c8121502c00003954440c0d001030100303403800744140364800d8086000034a4a018a5114080104460038040e104100402441c08580302c02d080c82c11a42c6030000032a51007030001c41c0940204000619429105c20a1341c0740ba581000703500c05c4a445540b05d21080714004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 984165305 1250 984164055 984164101
    0x10b0a0203162405010b0a03051506070b04060b040e06010303110a1212110307020a111201020a09080f06061003091a1918081e07021302071406090303 66
    0x380801c25035102103a040c0ca02c11401105840302d00100c80750b2007220b4803411144200301e01c2c5010014440c02e40d20f1000da64002a40e4140090503450b110501d001d117001481c88554041c0e00007403640d040111b0f0560841c0074501c22482444400c2ca01000c00080c3c581000d402a02c0c0d61180c801080401c1c420f84100050307600ca0b40c1030385c840401d642c46040010390144090004921440005007810400b0b1040038140d01642d62054158240030074000d4031000030507809000c0381ca01045a05696441320030a030482c0c03c0d0070700210355402d6000d00c06080341c512442060564041c6d008461039480000c00d034144100d200501c0d03680c2501d448103059000380701c400001d80b02e0b83c080f4442c8c40520040440500c2c0280d03104116000c090f2000c000c0501500d0010303900c0003951190b4022a4001480f040503900002d0760144540300140c5c900d40840792034002c40300d010f540015000740a85541c1e98603402042c0032070180261544100d42103403001d0361003105441001055100b000007440c0300045180030b41180d152 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 984166555 1250 984165305 984165307
    0x70f02100c0804170c0111060606090604170d09062a081605060a06230621010b12010b07031e0507080c070e0f09100b010c020d12080106050909010b0a0203 68
    0x107692184100340c1c001d500300c0011118030301121000700208205100111000b441d0181c000b03180c01980c40d8403107101500d49802401c0114611440307a48000a03078015180c0c1403a49103a2200c4144032540d45c4005a14100200340c8103040480c61b64818441c0103041d0101d00d50000c03445984000c0e4154540b6040f800f55204141402800c0384411000b58210b0300d44c0c02030004041038204141f0300e400705c07005540450000b100c4000f05252844916402c1100705404440d41511880148045a22003120803020108414003a001080075440000541001018114508156030701c0c1d015928a5102d25803028020075500100a118220340b51428100d108061038079504015036655000c1023500700c1c03100c1c1010380d0040341c1c051103414040003040343d01039040b110844290524481140e15862405d203043caa10381c983d5002d501076406078541c035001c60340c00780c0202c01907081400d140c000c01c0c0d842e1048400180c030010001410381e21070000c2c1c46020500414086150b46801c88400d141d50104800d0029400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 984167805 1250 984166555 984166577
    0xa0812041e11010306080d08010902090a0807150836010b1507120e0607060c02070e0708250905010305040f1b0306050f040b070e21010c090902070f0210 67
    0x410010070548a202e40b01d50800c02c40d000903085d070344070f03811209403644200d008070003003a80885040d04440c00b08100599802c0e440e000f065011000742c00082c0caa128076540010441e440c41c407800400d080f160b9642401e616820614500c00488110010402c3c3e0100365010728201d1920361340c2c2c80f0000200000400110400224001403030300c20582e02e00300000320b0348c10184851444600d988071070701c0c5480c00c205501c880009a02c0e020346880600142c0d520031701e10403110300070070036400503115082d5880c503a4500030384001e0124904481c00340e541110007180c00b0b981030000803400c01e06080ca485408442d41006d00450040c08000c1c81a40c4a60061810a0201e40c410011807202042403034080c54050030341c2005416500060300002001c21044c04020104040c808569001500c624102c0c0491008100017110491510f600c0f588035140032008901c410015807001c4141000364072200300156603202002c08038040c0700b1020340200310b08140c010041c0ba184040d0100100c8074200400040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 984169055 1250 984167805 984167843
    0xe0109030b13140703020316080a0314070b012304050906130c15020f19020a03081c0f0b03010608030403081206060d0606050403021c0507090b03030d02190e030a081204 74
    0x540070b103204000f2a0420354080c429401c00303010084c00078142c0a90b50211514007407106613914000c04000c0c00700401d5100c440b18400c1c5910480d800076810800c00311455071607000700303e00d40101c1c00c0d081412000c034001440460800e4001c3c2031044c5040340180c0b4072595900a404400b2181080880c0c08501d4900041841c0c1500d5031000c11450396580180710074051001010f242c04c2c1410304620803036041040640060307a8103098401642e500a14450700c440d590a208401094000c10f400390360344c10119100074080b01c07a48841ea5040c4214006d000440d41da5034465101c5c8214000038010400800000004043c0b5200c000d8200501520244c5003070060802d0800303d40890300711000195000400700250315155020302002c802404890070141480c0e550169110070314070610556545843d41368495507410b2040e2040e4584d5010159030714a510002141c200302804a00004902c0701c41d560181800d0010700051420b900416140c501211000f0301c07001c00d800204102e0b6085041c2d00340d40c0100c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 984170305 1250 984169055 984169073
    0x40f080c04051012080702150307030e0613081207170f150a05030c010f093f15090510020d0203160f0219140d110d0e0109030b13 57
    0x2010010050864050035104000950704041c0201c05654440c15007484a400042c0892a55951101c0368950351016840801d40c044d6901681d00031101c0084100b12085806030440c04019200c007054882d03c0c1d4500103428484207801c40003030f100320300a22a26952200040d0180c3d0840c1103804c1036128a9842214043e007503c049641e911600210401c1c4009009540d00b8004070802c12586003031001d007440c0c00710303649821024446040220895003c010280920741c2000600400b0001608010018010782140081101080780003d408d601d900014800d02c10360788215948281c108039803489100c1c005014040c4841c062b6000d0003440c07003942c0c3e4485c05100400c8180341e4000c000d80c0360325100002c1014401160707452024091b44030040f00d540ca50118000e0700321551000344440d10070301c0d800c0525100d400f48016900b02e01c03801803414001ea400c00002c68007815a0000c50310440c40314242140c00c0c49000400d9404500056420700020721420700341c40e40501004110608031120761188011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 984171555 1250 984170305 984170309
    0xa0f0602160f031e080703020a1812020306220f0503041806171222090c110d090e04020f031923060915041703070206190513080c0102040f 61
    0x48802455000c800c254200c2d910501c121104c1500b0840e00c00c4145001e0b15810000780039008050380010400d10703035402651070100c49640400003008a603152603080300c842d00c1c0c082050b40320340306000c0044c00200403070868080c40fa0074015009005401030703580c195214107045003200d003400b003484081800c0c29114000350010303a9124001c01c010745000032034665030941d0014248283c100900c501041c00104c0211183c200709071104195044207501d0198041090b6041001c5450401402c0400709a000c00011420483d0340c040c2c8000c400110f4087e07544200078442c802030390074054000340151070700000d4034117002000341c16210030060000e00e00e0213001107100100c80da90a201110411000001034042d401c160940040140d0706040918690350850f0525110302805a00d000808118110200001c8a54503c4c03000d0346a04104102946840e0111480d0321140170b1507210442c0b2410900407280901d03200300907410f094140e40c407a07801c507910034050312115640801000600242d01804600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 984172661 1106 984171555 984171563
    0x108040210090503031909061d040902010e1c0b0a020c07120807020a030501060e1b0d0b061c0b150901021902042309070609080a0f060216 61
    0x30700102c907504481e80600000c298008507031048015406020780755140c0850f42038407072008445030040e0b5210125603144d2008981d489081c0740e8030003280c1c18018504800703400102004074202c4009040c160240045558044042c01443d105883c0c011480500952410103210706440c1d945405003d9450452541020f400c100010781084804499001d405078101903a2410b056008084a00c00c00f01c0201240c40040c428110440d80c90758a0008400c459041c04006c0710001e00500d504000150020800c00a03407444521032014020ba1035141c140104480c010300042c84500da45002180300580818044100281c0e0042504405014081d621500c4986c150001401800d0840c01008403004002c164034195405681554461007140c400c0f90b10060707036000112502950b40c4500d01c0076402c0480000c0014001d443c1440d03040f40150000340c10f0440e1042400208840d6010440d = true := by decide +kernel

theorem cover : BRFrame.Cov 983992805 984172661 := by
  have h0 := BRFrame.cov_init 983992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 983992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 983992805 ≤ n) (h2 : n < 984172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
