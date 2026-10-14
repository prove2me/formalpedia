-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2998
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:22:00.111734+00:00
-- url     : https://prove2.me/submissions/ab37ae96-eb91-4fdd-b0f7-bb83443c3cb1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 539028776 ≤ n < 539208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 539030026 1250 539028776 539028781
    0x1120506030d1209171c0c08060f0d020a090c030b0a060e060a17130b0609060f01030e0709021308060a0e060a090318150e18040305070f080313200306 66
    0x1c1d00c0c1010380043d1454840d031265100c6021803030507413044440b4201480c0c2207a859600e01151400240200300b8000486c3c1068052001180d02c2007110b0f400c9030040340c00120348200071001540da5040504001c1d0806582c5c2d07400107080c84603034840362071040252418440c15614208000c40c076410b0707000c3c2c44d010500c255841880c904241000c0c3c080703420181080c43c0c12010b8085950300110007280d500c0002d10640030b40c0c0c0200101d40c9400c0b608010141c503880e1403130a2150014003410b14960015040590f245c1c0e08801011041021700700802c00704a0031583d4840740c0307800b400c00d07001e03034010402c6910560b070106074036807a03610840d10350704010800380c02c03940c941004000150007400c105804001d18071240305401c5000d00401c100600d61510902c10841d81c68102070214600c0b200c0700d41c4100411004801890304140509034029071600c3d0a5949400300d240403114081695000f600c0c9503404010080050305030042000030501400103920610700c4450300d90460040320b03030440d0f00340d00810003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 539031276 1250 539030026 539030053
    0x20d030c0908151b04140103110a090e06011b06051602070b030403200f0c0f0103020c070e04020d0c1502070b071e02010e04020c03070b130201091208070b090604020112050603 77
    0x315900400311003403260000d8102000c0250175001a04103240f0304901c400f0800c101d41e014401d647e14450700807406810301340c01a001800c0e40425114103250308041d080004e607582c0c410b0368000100c4203205042d048030b4103d401c11800400d012a400185075148070400f181040c0002580e004448664102d1441e6503115601190111078504c08021240400d901c40119244240b184409641903080148072000c003190030080c801c2a004d02c40c5050620422907034503031410210b101c2c4252074100640360520f03200c520101d0020414110064200006000c012801241400b43e103270b022800e42c2c1c2201c04482e2900e04a5190b8032400c03000404c500448002a50f0034588400280d640b503005040c003080e004c10341004130b0166400354508002d2500000f4110041007100525290042002c8446900d440d10aa0020303003101d80380c0c040c0064010301601482c04001049007118a074550081000040c1d080c4820070a548103800c0c0c400f03c2c00f188040b41d40c0c0d10510b100c1e2080c503203c0c030030050007495100c01824 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 539032526 1250 539031276 539031313
    0x307030507030207030c030b0a0506060c03070b09030d02041e0b03160804051f020d1119050304081603030504140a020901061809060b030103020117040302032a070303020d030c0908 79
    0x412025402003544c0040070402c548050fa009501410101c0c11615003030301d00c80d0484000034401031007048107125440201c84000241c5002a510031f0550100b40c4403024914594003501d01e80c506100c0c00042c3c003040844102d0301c1904044c8014074141601c40e1140c4e004102c03404100c03203021264a0556141c141b60741305104035a0031500680c16a50b10171030015032511022803680344070340e4054000603500d6072030f0014880d810541c4110442c00e8103000001d44644483c2d455030f0050400c128010000c02c01381b00302501101d0002440c40f01441000b4440d01e80940945801c0350b040c2d4080001580e400e90400c0f012030300c070308040d600401030745203682040c805075070700342c0b00d0302d01680d2450709a1008a5000144d00c624009042c1f80f8109681ba0362442c03000500c05581000c3d40e4840c86884800e10001035000020b032810407410f40418084041e0151203c0b0a00e000031003400b0140c42041000804c0c10740100340c503440c111a83d078041c001255220419030b07180700309200d4000d0b40da00ca001c81401007096030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 539033776 1250 539032526 539032537
    0x604050403200c102325050a120806150d0b0303030114120708031e070203010212010e061509090a020412050d0f090509070c0c260c0402090303070305 66
    0x904004a0003900d01c0d140382d103908160150092642e12485414031030b4070b404100d804841c0410302c1c1c1072800e00c0044443c05026021040c4005606001240e206524081005034040208900500c107000c58440c3c104147c0e100c0309814281c400404030000d0300f803654454052035210784005450031925a15070782050a461380000359007a00651381301480c14555030103100440c0249541e03451056503030442c4040041c40f450a0940c1ea800703610104041103561710100541d0082e4420501090706032050f10440e65207417240200081d41540300295841080b44103070b08246c1600e084942e022010350303c0400b8804030403503007441c10445a00c248003003a49464244082030f80304a1240e000340c2400c0e50780d1080086501408000c42d5250411810b811045a01148900001459180c009000c84c40d1a002ca0100d950290002042040340d600000500810a03105401824100440308641600d0030036640c9413204100005d00d10b00038035120010358034050080c0c0b04080c5009015500d042c1c115681030b18940c1c0701c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 539035026 1250 539033776 539033783
    0xf0102030718153209030114071d03120304140d050c070317070606172505010c031106010915050f10050c01060305070902210f130c05040507020c0a09050105010806040504 75
    0x400c0011601004d1582c150344050b640e8145488110900c101802e40b12030203060071100036543d0401410079441080c0b030461040c0040c50314485001c0b080442e042113204d52130342400840c00000d00c41001145100c6086615480003500c54401e20f18408807128421190b8000255000c91010320228036903981000c0c0c5118186016490003015a440318159007440d070080e40c40f04000405840164000d0041010031a10044807a201c055a0314000e0603d048a016450400000b5100907040501031200301c4101c40d00305045400d95a0348000140280152512002116030040400900b0742401100303400c90340710040401090350144a0110f507540c1014605900540d01c4510003c003080043c01504082c019896000d0781d80c41c0300b60240c1c00f0b551000c40a10340c084082c042084803801028841d190010040350030410301945504013201c0c040342a4008507409843c00303043c81029a000250b0784240d080c1540c0514002e0303178610984040755424402c00703020804403c006003040c905540207a0f80a40b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 539036276 1250 539035026 539035067
    0x402031c030219110d0306050d03030e25140612130503220f14011d01020c030f0303040c062c04020f0a030603060e0106060e040903020f0f010203071815 67
    0x804551000011088803c81c1d0f0100741420b00e00b00342d44006110303180c1e2a800500f41404954603060100e40d142d181c581b0041c007010354644400c02c11020900000d488940c00d05041c20846801e00392a2120900340d10841040c051000307840c580f181003101c29641444102c4c080314125590750407901240a4a01340103d8540c00100100c52452000754042a802c070800111aa038050801480d0304140b055608036403010014401c10906036a44101e10220740c020a40390503410248000041c3e241030203904c40998140500014040f480c1d500002440c440c1c0e009011305004c25a4404c001d07149560922030310340c0c1e04000c040304c10340c07907100700000e02c4103441000d840140340c40200c102841442d049a840c010009484460800501071a80289040180a503008020385850482e01501d241110a1814002e0303445407641c1c8241030007440060004c103084800d075079010780c3d02804207000394422136a20021801d1040ca1183c003c55481060055500f101d04142c0300450000050703600c1442c4140d031800d11003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 539037526 1250 539036276 539036287
    0x120b06120718020c0d05090607060c030b0a0602060405150925151e09051c021203071b0e06090103060905100e01061811030105360a140402031c0302 65
    0x190015402900040040e0b001625040f081c0e84d05410080c2040d048020060709000e203140d59610082183e09040e40010700003031f1440d5070301040d005040892900360307200b50a2400041c08507004034a00d84a1840303101603409200f41c4140b4100d5020090f00d02901551050742031120610358079581c50b0a10030b401c0c4044002c0760340c07030052030b20807420840e800e800210318200050707800c038820b102c00d0a070743d55030308006100a041c400810420007664041881c481202300401081d915052040184260720406903680c556550400400c15100c074104c041140d0703507a00c0f0005a50b003a007030361240281e0b00189520b9082e4619100c001c0500a80f010030f0719140291082c03c403000d01244903e06080c05130000100d210391418002c0c4511503860040d000349242030001025010001d0341c112419207804030745c5c9058050710080e004020003070b0901031444103808884200c042c10f01a01c500c40c0710301031a080c103001d1020344420140c10150240c600079007580c44007041c0d0180d6128507481541030003181c80e0060502 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 539038776 1250 539037526 539037539
    0x230f070501020d1a010e0a0605270907020a0212030301120212010f0608330703020a090b070303021206040b030c060a0c0206040f090c090b0901030b0f091f120b061207 73
    0x144c800d00281070002c42c18002d002c4503035802c0751900d203041c9001c50b6444511403414074080c003d4403031002c0c080c402884541503041051220340250351101000f608002c05840d0480c03002c1c4d40d03154000b00503481080504808911200c001080340e05803840205203220355201c135403c0c01030699100b0300824483d500c6042200e4844982c0c0304110082c0a120000e003100d4006231010440340304000039040c1d1810601c034950480003000c00d0840d402a529250041c0e81d041c9110302121103803c141c114507622440041e03610149a80354024080c1200107050441c1c041e16101d04200858051103001901508040c0394408035140510280c1a031032040d040c4140414525400a881c580c040c1c1c00013405c0940c503007810700001c000c0744190b00308a03496003000312100342420b103451480d01420401d01c1c10952503440944640c1c0701c0601d2484592006480c0c0c5046003040e41e540f11800c2d04145030710b4440741e90007200154120200c20981d99054100038001c001d40c840c0c40030701c20101030181c00d42c5500e20070003600080f00c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 539040026 1250 539038776 539038781
    0x204020a0c030822111503130201120513060b0402130305160603090b0109020d0605040207030c0515100b0706110f03010e09160b0c0c130c230f070501020d 68
    0x54089070356910404a00703464050814200a807490922806000c00070b8021600440f4100307001d40c014144003d03810301c21340020307122805480032a81d006400300031301c414100c042940304440ea201340c031103015105140209004482e001c03651f214500742c0ea1502070010a20540c400620000003800141c600380d00300da98801041110360040350164098600740d4141c2c9004001c0d00080d000034136051014441580303c0044075501030180341400c03070740014500348000a0707030300c041c0044c500035100b03540340c816600700039100280c4a40140d40300c1c01088403d00c2d40031504145070348104686007a4444046c107141c101c1c051900552400c0b140030345d8445000f03403c43c0541c0041c20b1f1401441889a64940c14890090b9802401030404ca506d40e0111a5011620740340200003001d59142e45a00c0303031604403040d082803030403405440d103681000e171501c820b000a400e05d4010141d4410a0b486010b0603201c280d5021400044000c16221428000d21800400780e02210081c920180908009030400314013101c0b0004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 539041276 1250 539040026 539040037
    0x10c0506070f080a06050919061a07030206090d0203030a0c030b03010f0219050a0503060907020a1a220f0204020921071401020a0b15060409021201141903020405040807020402 77
    0x410b0301c0e400a01c5040d40c1c00301c44954405004c50082c4542480c15011466809000e0108140c140b820b8542c0c0d85190030304c2c0d201c038006194483d9410b5544480c030b900100c49900c4403400340c0040c00b42d400054508900080c0410042010ba40250700d95030310884018001c1018102c00d00400da1100c11070840380d03609002709151100003580050b601c000b072a070000d401348003030810f0006001d000d00ca00c0707025640000941e41c1c403e030103560b00142a07407100710407420700b4141c40c0c009200c142040c008100d58002994a00e2140c0c110f80400405100c6400402140d003100700d070300400d410307501c14141c401400c01e5005000c001c41c0c05080100b041c9202181c0498160710746042046582c880e440400000c409014007a030000c80a0024007a24070300341d181c681d40804010900d0304500705c1c6184038422034440740300311001411071410441d2900950780300540769240c28824503d80c1d038159041d102d40c07864080d071400343c03066680070183ca02a155a080c0805400008c10a0740c00c40d20038421080941c0701ca0000f4038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 539042526 1250 539041276 539041291
    0x10f0e03040501031b090302041e0c0305070f090e010b0c0f060412030506010306120f020310021308010e0d05070b0a270b0a060b1602130c020601030b1b04060e010c0506 74
    0x5844900b0100018203ca50004401c0307000c0300ca402c101c03800c4d1600801c0b0403040e2501a14080381056840005020300c5005e61074031904185455988251554903600c1103000c0d150070b9a54844807034604400300c1c0e1415950160100c800728000040101d00d1042cac005124000f200b509540d01c5805008030f60741170060440d001d5404030341c901500448258107106290380101c003400c08006140c20030040000c038502507100101180180440c210943d40c081240100d00d0004081c1955640c87c0f030380b07030a440308250748200500ba60034901c019488440c0400c0070700d0881000d070354144c141120fa0b00d0720002000e004e0100c403034055481490a10501400501c03c1c606000952407240611031440c1580540c540103088481035858a00140701c8c402c010421210b03001c02e003e0329285441e10900024040d0900100c40000c01480c1964208226401050f0746040305c0c000e0b0b09010259441d230038028a5400013000110158508001c00d00c041c501030761f80282c0f40e000c10300d002c0c2c1c0748120315981c0a02d081020744154 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 539043776 1250 539042526 539042533
    0x50a1b0c060c1a0c0306040b22060302031e06040305131505070308070305222f030f0c0604051c020d11040c02010911010509130501060923090c0309010f0e 68
    0xc000c2c0181003a41000400f900c220401c410719094808800e1800041e14a41c401c030344422040050381e0341d043d6003198554401346c000d000e017286021301000a08a51008034024012500603090801229003000440201030010704010790b207640e4111925401110014101e0310140801b080650405000c03242918442d290340d41c1d114024180030300213190003040c2004043c180401c00c00c6842c0401c00074045001c0014850010314244e03d00180510300e010030118240c8040e003510401010030708480c4044000580640e0502440410455254400d010720241c0114040008102505100d1002c2d00075007a0244101145003890f4006144003140200a036988018074101410a1629100b4000201d62500081007005003e84e243d42015641c02107180c1440382c0848e80f09e034903450300480700c181030b1300c01d0300100041d6850f044040c1005840c0d010381c054140078400c290010b0882c0c15986020010000c000c0400b541e55800c3d01c000c2940b0050510b07019540702c0ca4103043c1a4824000c0400300030540300034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 539045026 1250 539043776 539043797
    0x3040503070b2d04030c02040e070b07110109451416090503100c180b03010315020306060306101115090f0a150e03040302150702040608010507050a1b0c06 68
    0x3c01c6508468403807603280a00880d0280400030b40c0100c0521005581910003050f0091003045940c10000d265009450036100040c072001040510043c40c01c00d40c10907210380801c2030b101e043c0c06140314005068960a680360035900c0c46160310b0003142002322a150403100e0410300080c00300310706640e44907054056203281c034024024601d10240311207031540c0ca5407400d46080f0b0f241c00006642e0710900100444496914003e000c605031143d220180c0c4e1103402002040b42c60390740e01904071164801d10056481c540300b081c401c0f92404040c002c41c0d02030000141101e00310744480e81080340d002c03503900d00301050018224040d00120320611207106802d80481c66100240741c80c0440600700b20120444401a8000c05244000101c64200d07114059400c001c00040c2c2c101580e0400307143d4071454001950041e032200c2003806081d5a40c0c010449a40f0a0710301b40131a6175103854140c00e07520203551450205609214100d0440d1140c007031103030202c040c0b00303085120040c0c51721030b9294038101d50400380000310145c10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 539046276 1250 539045026 539045071
    0x14090a06080a2f03040f08041215090c0902031504060906080105010503010905280c091a0a0e010605090f060a0504051207050d081b060f060102150402030a030503040503070b 76
    0x180b5100e80c82410411000c014107600708124003081540300c0c3c0d116000800442e00303102e1442c104d080071561040c00329a036642c80364104081c814040c48201c0c0d02c0e12410728400c103100c445006400c1000d0b80801020015070802000e400070b900300412048800c111010b0040c11950341d405464000c0c240c0c210700081450030030740e8580c00e44405801c10782c02681001000c1000a00000702080c3e06484882c5841c0e48030303e80c0303000340c000ea800b404014025102804003c40d03650a50382c8408442440c8a03413140301603640d1028090303104013030310500d890105034000410103240036030000c00188100800d0350555481c1c0340001a956001018540700003000032070180010709282c111522001c03a0f4030020b0107205c0c42d003000100324007a5100000c20104000c10034980c01e10002906a40443c10799054408600d031200d05001c40e0b1b00c044414a0040c41520003c00750000c510044c0c501032500a405440b2050706514281da41c0d03400640201c42c00d1000300580008116191040b9019291035242072089174140c44 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 539047526 1250 539046276 539046281
    0x9050105070c120201050c0102191115040303050604021608070611040806070f120903020d0e01032306061303052d030d0509101d1b1014090a06080a 65
    0x1001281484030802020303000c03034001c00c582c40441d2a000c2000003196268401280c40d4011004800407541c0085030120903171052100c84511311502d0ba0f95001c100001071005981d80c0e0600c0b015000c0030391007401081c0440e2190300050350000e030240000d1b00e02122020b140ca960840681e056424540101c1c0c01401c02140d4000c44c480a10b070f41c41c102d4101400d006d5020f40f5080d01178151414094902c07800038080d40509038000b60340d013175031404000c210814140030b515603001d502c45900180c10350000181942c080c0c0b09124502c803040d01092001d122981a0032041c20002e000c15510280901030320300031800070841d05004d54803d0001d00822001d04017a90f40c00c81c00c040d4503038000c642c0200d00c00180300c2e0000c10b590b628a0f0f041800701d0f260316500111401d0100d8032641407d05401c00710100f030a00f0691800c82c2c1d490820204030340300ca580c0d4481d051000074007406035a038849003903110001e50620424250740401d404400e00e624182141000071440b446d01d52080012500c1401000fa0545983c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 539048776 1250 539047526 539047529
    0xb04060b1605210d020d060902070602030a0b091005010c0804030807031101060603090218060f100e030c040e0a02130f0203160f0804170c07260f15160203090a031209 73
    0x83c0c0c0424070310200c0b290154080c040d20501d8111564045040c0d01c01d078815400c614000c1c00d0b9080110b6641502d410094041d52044500c0d000903810107005c004581003100c0d12a01c140c4000c50b81a00c1103040000454403002000707010f503407241044c030010002c50803400040c64814425241d0582c0189100c292500f0b60b11a540200140b500d014442d00251700c540c0c220520101000351a4801c41d039a08000440401100803056007001c02c0c40602c00d20690000d40889101104608544d6010004003c000640d501640b190783c00d90411219240103060098489030804105003020680d1300e1000380500407a00121100f144080000b074041e640c098102c03101c0351103c1c1203881c2c00c0c6410710b06a1503518141540181884040e400003800441031030060007481c4c043d040301b010300980b420350200801c00e00e03001009001803038055013070f0040c11050005015030310100380740340f6100c0581d1100d1986003640105503000c0252f0000f00403c143c6130340d950307480302d0203140306540c1040c0c01000c4103070040c40d20791a03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 539050026 1250 539048776 539048803
    0x30f010819020a0303080711100203010602010b0922030203070b0406060e091501061d03010207080301090e0303010303020c010f09050415080d0314150d08070803010e1302090a0b04060b1605 83
    0x807003410700140e29851851000e581d014104400e441d02d52640440d810040665410664000d0003600c4407420150b030003c2d41200c074039500034002040c0b640308010800300241c034042e40b1400340c034000d08060b10180340240c08840c02070050300d08201075516451030600003103a080311003035a40d480602641d8601e055003030f0003000c4040202111460070504021080044c011a418460030740b2001e1141d012910251001d03800180003136444a05524003d2040c3d0028044c0c1141181022402c94041e040041540e04807a0103600a001c01141c410054130304243c0d0301c0e47c04040000c68038011800f1786403801001c00c03404a244694042d240751601007030500e44050044c1f0101800e0485075281c400354240e030203801c10104640d01c810300f680140010902c10207080c000340180404203200050140000c003550484281d036107848555941c5030152141490b00c110002c1d4007047da1804a20900200d46c44614190000340c000192952a00441d111903005403201005800c0300145807000c1240c00d002c907040700c0c1d15 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 539051276 1250 539050026 539050063
    0x5070503071502061803041205031e0702011b030c12121103100509060406030b16020f07030803010603020304060b150d1b021c020c0603010303171605270303030f0108 73
    0x501d407200135220380000d4122840240b40c1c00a040c1140c00038400c4030001c000144c0340061240d918070b1300c42c2d129000031a4a083c0c03030581811307100c1040404400c0311102a4140d58000b210315911068002d4484245c105174100040e05030302c0000039a464440c0d04444010b91201100700000c0d0403060241d4606074144200d40c0000e100744400000ca000c8980b0585401710341d000c010381d4070000414003c000700e5102800100255081c048510003180e254404411743d907013585c5138071504104843d6151864480145a46e0080004008540c03103540507640140c4030b8500400c455034000001010030908540c0c28610540015a0510b81d0181e44035030724024031485041540e06a0640b00a901d540200b0303c0c1007801000b0480150b8410300c2840784070301010005140d9501d139616820005d0200483c02c40b0741600c07103120b00104100d02064070f108165003c469903843d1819243d40c090300e280c18040c40c0d018410810140240f401c90f0303018070107540f1035400f50513a00e8040d031604202a15001b1402800c0b1440c49 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 539052526 1250 539051276 539051309
    0x3120307090e090c0d0c090c11060115020a05010501030f050709060b030609091f020d0b0d020901030f0f050a1109150d080a09081e0c060a021002090a050306090706021015090f14040507050307 84
    0x140040740c2b542c1140c68002114403140c10001040e0708240321204000d010b03501e000004020403c940c0703840b21645000d24211000c00b45c4070943d0b04202ca44501038603100c10030070301c0042d800c5d151181b45541d120b2016400d4440d8600308a44806481540c1c5d4105220745d60040f03a600d11030758040c0714540e4984422203034074503140c0385074001c01c0640c503041c00050000001c5210443c20b2080503210f0405403540901210188902410420303030703c542d00e00009100300721880108082428201c03082030a420000c0024440ea14203503102003030b603440400e950041c0070528000007601c000a01880d1441d1720084002620f40e0001350f0305609100200c00c5961042105100024071280d0000310041099001840180d035030240e00001020000c07150300141c0e1505c1590100300780108089107c07801c480003902126400c85100d02d00c0000e5174000881c40c20030185c5030300100096103640e0440003c20110401c009408000c541400580600460302a500391b88460300c00c10041c101041031310002e0032043c05603410752 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 539053776 1250 539052526 539052557
    0x6030b01170604050a240e07082404060b0a020309030d020607230d0f1410050d24020c0706022404082b0b03120307090e090c0d0c090c 59
    0x203071001e022140501da80c2c40c0050004161a03103c05d20700b6661142c1c1905480080e04150400d00c0280182c2100f01c2164001c076051314081c2091078040c00c505080c400300305100c4024114400c40b180f0180d540181c44000000e00340f401e500c014520560158007940d9650148010b151810342d15001c074004551003070f0200210264411002207182c10840b007449950b0840e110383c04403501501205240c0a4030300210080080080d0340182d03070604604400d00a03a036100f4000c540001060b100d070f6604082020030b800005510101c90803c4540a0b017072000800503805952022600403400031100356002a406008150b0104200a212103000207140bc0c282c441001981070482d025000506c0d40c440030600d500322021250043c6004007600e082070f00c01d804160615400b50142d000c0a030f010740201d2035114216500d44044034407400e059155130244520b084074490b4107400040000d507041c0a8802c1003506555049400744c5850301400c4848815410000e0f408212100c49000a05100c5803040f180001e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 539055026 1250 539053776 539053817
    0x1270317040f061407050105160e2209050102040f140108090609031c090b0c1c0506031c1b0305030a0c051804050a1d031305120709320106030b01 64
    0x3610504c0c43c001e4941c040c80441113002e4041c0a00007492942440100200e80d0500116074171b0710880303543c8051050b24201c0a11203d240e90180c1e500c1c815090240045148805400014905201d00001440c080e6604030582c00400300c1d80040e0640290034a1355801c40d0303808a6010f0b0400c1c047c0000c0d000750706006070303030a40d81e1040c0940ca603070740110300300314440e001915400752645a07040090040507103000c1c0058119076010500982c401d40072203d40510f4800a44031f02440b809001c0d0082905600b0980c900c0e503800f1b2440005003c10108088100c1c080005000140c1342d20b110792aa00e03220304054400e90290b548010480741040020310040300d001e40d6401c07450306040001e82c2c2c00a0b01c0d4503600c01510260441c0418401c490f00c440c4003001c01c00c10f0010040468040d6090000740141e00c0750b04002c894051b881d420365881e801140c0a1180c0a40340c1c0c403541100c2c11801151034268014035010a04224107030384094604840d0b001084215010b015000c41040240b0309640b581250110320001c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 539056276 1250 539055026 539055029
    0x70b0c0a09030b040221070f12030215180a06090218190c050409020403030504080c0a0b03040602090102030d140604050903090a03110a240912020901090b01270317040f 74
    0x201e980b00c00c0440c1c2036441e18240030402801c00d41d8000006ea1015030a55a21446031081200b8805070305800503010991400100da21a4140c0c0989208600c8010034440c1d031401410b10340f114181d403191007511303040801061144500c0b07408080b070300d03000c14010000b0f80d00c001104190011000030800c07102807107100a00f451029210400103040303030300440468190061fa00000032041c80000d01109042d008000b51003200c0881d001c5031320b42c03020325052110000c6a8420030305410014004100081d8064001c1c00c440d40c03041c41180e0030407082400c6541501c010000c6411032030702960512107a420b083c09010390003000d001c000d40c5800511004240c00c2c606502c8003402100c0300501d0b070705c80d5035182200e410040202c401e0380d610361f4800880800450028506500209120703420000302d455044a059054075001004068243e2a00449002074804e00c071100c1c0c10440780f94070890007008460346000b44a0382d03280c07a01d44c00c103003580b8210310802002001319010000c240800c00122104e84042070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 539057526 1250 539056276 539056283
    0x3192f040b0a1d09090f0717120a030e030307080105030c01020c130903031b020d0f090807060e0d0c030b07030b041104152003130b12070e0607050f03070b0c0a0903 72
    0x83c0160490b280d000d0540302c1e41441691210b198001e0004203c0c0c006009004103a41505485a1507511070740008040040754001c1d88035000f141d03000b40c240300b516014101412042c1004149070180da180e41e411503008480c1c80001c21100780c01400681801c0004685441d800e00003800f5045800c400648404007045040302e105032209015010103200e81c000443c030b00030705500c0d0382c40c441c0c00c60400f07510f8500884c91100043d152640750f950852181009500300c3d4000c030007600d911401d19408484018130f0301e92268003c0076400504c0006078003403441000035400750380904014202550000c041e90368110f081c070b12030360828002640c0e1041c503c048508540110703d07540503051103d10165007051004640c1c2c469280b00903860f24840300b000c402040d9810101d10200e0072507458504c40180c0b40a0000c62180340120301d030025031802e01a928140c4451401480039003408402d56a1781d140a81d10020076503180c201142600410020310250350300840410382882c14500d44407402821403a140c030015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 539058776 1250 539057526 539057537
    0xb030309010804080d090c030803150a0f0b030a0615090504111c18050313050109050109080d140c03040803070c06090503060f1e1503060108011a01030203192f040b0a 73
    0x40d17600451707551008407400d0703000000d00352030f542d42d080140d1070f0f42044032895224071002414210f5468242c0348507040d14030061050b00f201d403e000f400c2c18076410050441d1102e913503495010464008480c644403800b40d5a980d6010b0a504207020300040c3c0c1c40710101c1050980c0180700f54070068072a0040c0c4822920010400a88103065640c0702c0340003c072108002d8424080007519010810346010900159034080e203659607190356070401142c079a00140320f09074283c0c00900050149030b00c948030003407418601591f602d05064140030140d0840d800f96129070310702c0e4400075551040040d1b803135214000341140d00340454141e103800c011030b466503c01420400100e4160b000540d5100c02d81d0b0ba40414010309046030300180c5410214804281c0c105510785209100f99000003803090310500901c115001403036100b46131203004a0040d0069040070b402400c101102010603444014184649030b4501000800424440983c0703441c41862405100c246032501410070044c82002403030800c4032030303440b450300e880c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 539060026 1250 539058776 539058787
    0x2408010f030602180414151c260d09030206010f0302030a020111031e030114031b010e0607080c01060e0a200d0b0a0b1b030702030d0503040c03140a060b03030901080408 74
    0x100c480070610b81d03c0c02035100e0300d060701d400108a64014044e01c1072030500c040d03071f500300e0706c000c1040141c51420980454800780c0014160002d80319503070b02d401080c801d50713104421000018500080d50041c0c0100503420781e50310490818076a040050900600c90109003245050458000c2a110f03404050040d05200001002c0308400d1420001c680326400856891901d0003010200180940d00a201c1ca03000d060000552407964640850903071240404031120303040004043c0c005513000846601d0b001d03170081c004e000d00c0c404225035100500100820710000148141024090519500081d08080e1401c1c0f81404d0b62440001e040010344039010403e210300d8544c00919407410103407560764030140d000020158005500040c02e03021f4001e41d2441003906052004e07026003903a80e8025803c010b5410f0f0700c01d120b25603419018500558009000303000d00c1c280315441e83c64001d0000040144d000c405c1e40440c0c410014003000d80314800c00800103c014500d0141e09800081c00e240c0017070005018440c00050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 539061276 1250 539060026 539060047
    0x5031504050108250f03050109030f080f0a0b030316060606020d08280e101a01032703030e0d020c0108010506210a0e0109081c060b03010b0a03020d062408010f030602 73
    0x4031000600d603410301702d01d0b059220b15000b07003e0680c1e040200c2c0401c01c1c4032001d2946900640000b403044400007644a040d607250944400034242c49404960540030400038640010400c036505818680950320100f4180d181500c02803a00d1045000304c001c0164417018001140e00007450f40140d000e83c111036010f0a40c0d0394a03003100411300408201568440c40c200b9401359112500325903900000b42600e41140355801c0019002e0320a464141e002203500251403404801c040140314245a000307280015102d40442c11040c03418011807550009640b061700c6041056034000d240d1030140200756060307410318222602c1c03a01c0c0302c0314468076002d4618001c4000340501c5000c0c3c0c440b00003000314100030b02107d003183c20500015442003100d0b0301244141d290f0204140351a01070780b000c41d1101c0900e545544c6c6448180c184641201454008242e020005490600000d00515000d40b203c20402c45100d00704030300300510302c40031890010602801c100100415146c1c0002001203a8001c900944c1e19081402e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 539062526 1250 539061276 539061343
    0x102060c0d06151206080f0316060209181605090108070305040512030c0a030621020d0606030615050f1f0f0c14071815050f04020d0c05031504050108 66
    0x20010015201500380d060516540000c902d07030100d5000108101c5c0755202da88060301c402d081c0d90100090382c000c00031920b40212160141403001d003d010010308000600740001c20300d41081c070042a4500414050103d0080d0600040402c4003c0d400d12503d0302030846d0003c1e2103548001c0459050680d140002003d00c2414458481c0d81c0c054500110b03940d18050b00341003400c0d0000460003000a242c08004201e64000804d801d69800c05600c0d880c00043c036a50802810002c440422284c058483c0c200000281c114051080c10022215803d404541090107001c0580c42c40300807030307200301142150520304074200c01c4280c00c400740a280c944400c54540c0001e8a5198024000629070b0900b680081d080e6000841d82100360340b08070301d05c1120182880c441c40281e812009020b802c01d240c01314104040d1414600000e0003990181000d420505e50304450000ca440e034528103000b2800c00000c22200d03c0512030070340012070040360100495414050f05640d244956101c2030001c0400d40da11059191291 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 539063776 1250 539062526 539062529
    0x90a0207080c0d0f0201060b0c0303011401090f060e040522020105030a02120a09230709020a1403390412020f0a0315050c040e1b0f040b1201080703020102060c0d06 72
    0x3046511021120f41d004014118480c0900019460140003162011180044840ba003076800d009609503400d0880013216044c89820b2941880000d1a0015801280380c42041c01801e190701c0c0c2e024041648403e00040c0e40c4010700f02162610090701c400746110041c01c010071015020f2900d5500ca40d2013841c003000a2081d020060803136004001044001c0f0017a070829500703030307202d18105e00e0203021a414555003815440c0c0d480d800d42c0c210240610804451f41c0c003420300c00b0400d00d05407a040010304044c800302c1c1d200340d81030a84007401d8694101c2c001d001c40e60040c80c00018284281920308ca10421a0360f500450107000c503007100b51100c0f00250741e101910f4403541200140540e840503500c0c45c2c40000034174450040090702c0c0c113000015400310312980584049850210003143d5a544005046110400703450410988100900c200022540280701a001421301c0501742c40e034804895450020500059001204951002c04240f0041c0d0340410b4480c0c01801040205403a000000c0b511400b0342201d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 539065026 1250 539063776 539063797
    0x1209030f07051e0316120e0406090e0d02161e0e0907080c040c0f0c0c080d0e010905030a031704081e090f090709420206011202090a020708 61
    0x86241014040301007014400048041d00881000f161003542980300e000c0d0008280300340610700d240c030700460940c08804c3d4002e00d051602c0540403281c1d00c00076085981c02e4101c40881a0707103141003202c0e4107040221002c0303401c0d10300080c405a00d440080011301801e0740a0683c0d800410504c410200210750f488501070076100902c05245d103480b04030f06507102c1c60340c8100c24091160000d0f080c1036050074424410303106402c1c0e50b80b940c2c0501850017500c0c40e5088610842e15048141e0000075681c100f4840030300100e03426551041200d42c208001000310780707143c0100f8402e8100c0c3c000c031800250000790324100d4a17140c00c4d0701801551141003c81e154003a401c2d42c41c00701c000302c07104c0910310b901c250000c011004040b02d10306ea41e0f40083e0140802000101c461201040802d0001e01450001076200c1d6a015134010101014450400c0d68500351415540c01705000744c892010350241c6901440b05034013601200f11541c0358104142c0000c0e005500180080d0091075001a5000c1882110b20840f02035510 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 539066276 1250 539065026 539065057
    0xd0b030309040603050123130b18060103200111060f07050c060a0c11010c0806040e03090a0b0909010e0f04030c02010e370503030d020c1f0519050408120903 69
    0x1624107201d406032041c500c1e080c1c0c000150007103028420b10450640c40c050080500c081105200c10327611050b040c030006e002c10b802c2c1c001c0c0703421000c3c181c0810031200e40614070445500c07100312014190003030b2500754481518140264046c0c450104240080c88560000048130856840d480310181078030b41d4887e40e80c0d1076402d40940700170003080c41d2190b0441c118080c183d548006203a40100c034614200c8184d001c1442c0010b07011008101d481c0f6141d080381c07c00c0c181001c156407411510a001848203030055102808640000c10500b2480c81d0061203140103004203001d50070307585054030751400d81300b4005100400780841828004150391182c400000c0442d0b01401038009030b01d030310745010342c00d07182d0388008070b0301041d521040c180c0d00d40f18101500803160084c00440c101400b100500010b9000402d503100f0f107100b0300012603100c0003e824100d007508515100007a8034200303112244040803170701608000d03083c106003e2100195100e401c43e01000d45085040407203403901c800c55815403140c42c484a45408 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 539067526 1250 539066276 539066279
    0x6120c151603080924070e041104091b08090601032a08011e150608060612040807050f0d050a050d0e030f0405120606090c0d0b040c0914010903080d0b0303090406 71
    0x19000480c0d20b005145507000c9554403120b42140f44041e00c42034464821174010840802e80a43c0154213900030001d0040000c0b0341c541221400a4680e04683c0c0500c42c03c513181c140043d00c081c10b1200d082210032031464001620f1030b21520031075440e1010f00c030062907500c002812001881e1203011035030243d40b9401c800100c090761004411702070606240ca8600104410310101c400304001d00c146c07800011000c10f00c1c641946402020360340540024006a04000c040049601c404254407140e07204611800303540752074181d18284149401c055800801040d407024086440c216000344c20b68000c65074514202d5a600002c110200103004550f418400a100102d2a12990490000540142d41043d1030704c80c3e06004403481c4950b02e841c00d4070b00304c1e00b10741c0d0700000c144152810070040c250a503107444040303220500da80201d81154252800d102c0020301c460030510400e82058502c1c0644042403800c0ca0b1001d00390313115100c0c948204000426013640d103143c06074240c5c8090003a500c940900400411107207 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 539068776 1250 539067526 539067533
    0xf02030c010c0f1214130c050306040b040b0c130b22030309060f0e09010b070302122205101d030f060a020703020c0a0609030b0621010c0806120c1516 66
    0x3c0d210280c2c1040400d00c60306449602c00118400c805100ea01c080c08248551030b42d10780c560b0b101407012401d0700e20070440c01c40030510307440070050300340110300c42d10003074041e8a4181400d4101e210086d003454403841040002c4804401d0071a812410745042909141d503510380c0b1a40003081d00789400010b985441b03c501c0020a05403c81c490340b00320760f0903840352401c00c5440042203503041002100254085940380042c000c809002c0d01808807107110340103c4207000750395040d50032036401840d5020000c20381307002c1d80f103140c80040d642c0100610080c1c82d000401100c00700050003900002445001d0002c16403001c12155408000c0808143c0500302540c1c3c8078103040c4014400380d8410f02080d40948030354804c0e42e40740d0a02c486140200c400300e030303500c18501d4110381d0340c0e1580380f40c0500b50951041195101100080c0403030b4031244041c0c01c1d03a000213071030484030401a00d030300c2c0c00400c00c5209810000b050400f01c0400b003110080760104851843e40e405448030551121f006142d180c4907404c20402c080e4042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 539070026 1250 539068776 539068787
    0x3060312090905060109030b040b0a0e0f03092407261b0c01020706080c0f1c152312030d05040b0708130201170723071a0f070f02030c010c 61
    0x2542c11041d000e01031580c0b60750054440c0a06807000a06070208c510008000ca03074520480360f00300c107806c3c0b804242c001901c01c070b461900d40b4425000101c0d80001429034a10b1400c9098103120130012035411284203802c000c0c1c90320500603605c0152100ca00081c4290224130341100028038281440f00164513038505240e40b845203522611150b0452003070030380c040140e40c00003685800329031031640c400c4256a02c1ca04220f07156000340382004c1880c0802e01028030882e20302d8600c00802d02d03150a0014070b00d070300401c200080703600581c0810061541e00c00c0300e039413098185004d03035039040341554011202c0c107a9080c2c50346903100c0c21840762041480d090074081000303003190724a13000744a255a448000d80310454002401158080c000f800700364081c112640c4038418610040e1700101508220701d240340c0b01c0002129541c041c3d18000802000056404d041280603000c0d52014080802c0e50111803406688509a4041c054010b1050000c2d040079045941d1081080721803140400f130092000c0410001c1c003424 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 539071276 1250 539070026 539070029
    0x90112110d0c0314060d020114091507150b01080a020a110a030302090901061706010c021206010f210809060304021908010204030b0705071211100207080a081f0509070306031209 78
    0xe4200303d042007000740340130041e50141000030040d0b0541c00142e801521078524170a060030b003150080c01000c0b20b941da0380d48203440900f885401260340e400d9501e0520341c980348414807100f107549044240185a40e008254591005400000581d00d07541c0c60720694080303032041121106031184a4402040640c550081c04035035901760cc2e4010140d0720780700180d4010500d600385046880303005002444540c4030780d04107400350340090a6900701410180000d41803a000f40c008400340c1821103010803050701c408244640a0203c2d04a4000712001a51010820312034036040910506020000c10255136402090f03403074034210100a08000d5560f01e00c0306010307410601c015100045504002201d031030054088808941e400030a101c0c1c11000d1200c19241000300180502180c410790100040480304ca2008100d00d90140c421603032101107070346005003c0321000703103000d900854411104038580001e9140005a0b001260b20341007e55400c0f00880c0100496880074000b07442c00600c01c3c2c4856005400d100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 539072526 1250 539071276 539071301
    0x602031f050d03080c161208040c06030612021014070524010e040b09012d0507050f1206031c030b15030c0405041a091f080a08090112110d 61
    0x640c407691501000300402c2e4a00300500400e81d4031001603203c0316020020483d20500400d008601206902d4861000700b00c004150040b403148802c0c4000e00c1010042e5400800c1940303010700c003c0341811903a034400d4004c3e400007030107103040501860f07071107009013042807032600903c80301500c030069410896582c4541800340310311031042c040450501d80b02200e1a5061f1000c2242445103a11103640c0c1640c40e500c010070b5100710b075590340780100c0505080c41a113584c000a0110019807440c05810140840381c0103002e410038000c0801510b04e03a0060a415100010300d0900300080655030000400d080200c3d2440c254202c900c0081c541a5072609940071040c040070030380d40300311000c090b1602c0040e184030942d0b21107006c0100340010082403501da00050300c02e420001100060b80841c401190421509880c1400c0200712032280381e4007211039016a800074040000101035205035611220f03454801d20382140d040090000b140c0031580c11941103c14017140b141f9513039a8411003001043c0062292a8510 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 539073776 1250 539072526 539072581
    0x702030403120e060a05090a09020d020c010b0904030f050315090c0415030c0921150e0607021f050403050702030d0519050702030319110105010803070212032a0109060203 75
    0x400c0c889100f014600700070100501550f2400c4d411890541e07a03a044440303556403109130500085a074003424005860410b4a0940c0580c0355030040220a0079521841a0079004403a40010400441c0d486003445190890605000740e581c1c454440b188107a046c1e0094040e04804604244102c9080d04c10040c404c68080401282031501ea103003040702503d111102d050700007460403d051254005075241000e251021050460348240356603203102406801008000120b9920150307024070a4051013400d03400741c0c1d2480604055414004e40381103e2071440b0101c40d4040d41c4000003030070103000e0402c0f01e06a41d00181207a0011034084801841d070f074862003c605004490039414401f19011320306030b0741c0b0280d00a01071414900d0940c080a81c201902c4603240412480100a41c1d901d03000b031080c64064030b1054061a9a05486c2c0107000d200e026203981a842a44208048040f070b40c021b80c182d107814aa200d40741c403451082c034050640035158105c40640003600c00418030007017810250f0130301e0f51346d00c0c2910138 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 539075026 1250 539073776 539073803
    0x210201090801090203150c13030f020a06050322061e0c0908030f0304200d060c030c080405030307030b010e0a0e0415020c1e070e0106031517030a080603030d050702030403 75
    0x1da8241d9150901c0250150310031401101c44000c07600c413140d44880101c0305682841c648074054107440829520940f680c200041100065080a4544102414103410858036508142e01000c2c0c16200c130350f883c000c00041c0703d17220804000441c1c00503e0200140345001c0003500f103410a5100402c4140c0078078000c43c2d0201400504142c3c003100790b5985440c005889415552103440300034a90314180d05a82c0c0c00600322021600d15522800700115441c043c0d10005150521450003400b261844034002051101407010000041e400100300c81d40000203103400304080314060f0040e24500124016a5400304c43c81d10085400400d00203424480ca018a1038a00e107044d030003102c0c40072882a01d018032125080b144107140c09070300c07402480e50780d03200e4401105c20035903031070300380301100e80c020b801210000b030b01c038011840d902c0d1040003850045d00f8040080d407100c0307505103400c50380e0703115003001c041c02c0c090000c2c005100b0796003d00a4070784a01c0110800e000da4906150002d4590380f0a00044402c140e05001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 539076276 1250 539075026 539075039
    0x92010020d0525020307080607140403170a090f151e09120f0f0809131109040b0109090213081209011704020d12020d022a06090a21020109 61
    0x31040c07150000d64035070900d03010940b00c1c0c241c81c00501c844002c403c1070301504a0b50041e1800c024000090580d400503024600305010010b02e04840c00a51013402d03a802e2105202103900380341040c103492501c018041c0c0d40c0b0204642600d01032032903480000c148607140000603541e12460721200401c0170a640d071201401600300c14410000801c0841c2d40016038400b424840c01d24540e40d541c082501a030410b5020342003907075594110080c0c2080c11150080c02041401742814400d49280c4007c588000074800300c07100100540c0c0c00d00950035000d214940f94400f0030a66402060002d000c2c101d0f056055540d0312600c5100c01c46141103200d510b909201d4080c400c0058800c4509941460078140c2daa5055000d1170160344140600c013500582c5c3c80928000704400040e0119060032041c0040c3d00500783c00c10301c0c40701c00790800c0318001c201d4000c03540d0b81450740185441a400101c0ba0f0341c2c2103035495100c44140303011807011007094100c008020140060f0141c504150161040d840e4800d030b0f40c510301c0039240d21 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 539077526 1250 539076276 539076283
    0x11224080d020d050414061b1002070b0711101d030409051605121611010903092603040b1305130b0a0510020a06051834060f0302070609201002 63
    0x1b08421144086038107150142c64128000c180d040c03005e6a0188618085c882818203040040703601d541456400902d54040000c841c82d100d6000c02c95046c1181c80e955126240d948541020320420007584c0da40980e8503526106410019a41c0c4000c0c007242d8070ba58540700c0300e400401e4182c400e0ba83c0421034102d10200c031489481250f117401c40d9072408142c240c46e0360304d0043c0c01580b4840c0e80418840484009180f4540034441c80d940c0a000b5520401110320f4110700943d140c09040c205444c20003e070501c0840c034000042110226422031032625598a03014040b00c500540c01d40001758002c541c0c0300f11001c0599680c01c43e4a40c1141210054451a541c10400040c00c40e11700c144800350f0401544000070804036030000d82c4c0b1246a111a03918018511007003418050802d1880e00c90603c485155554a60b8900240c4c51400480452091181c1440340240c48144564007590405800003186010088650029440300b94001c42074010004425100c54a500e08102c01500604691640008c01480003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 539078776 1250 539077526 539077529
    0x31803170a0b0d0803060411030420060306030a110307050603160e0105120f190c0203070b0f040308060d05010e07061110090c26060a0920011224080d020d0504 70
    0x20001d50f00039800350f03601a02900014200c07680076641d04401034219807860b008520682c85002c899950884c41100011200f0000310380314040c400070300c1080002d44000903003404d0305800c16540d51288041c0c0001a1814031b0726000590007a501005111900201b2040c80f16180c486464403000c094100004441e00c0c042d8030115080d0a007800c2c0440d200c0000c600c00c40380c11104403403040c40032107044031118050310b500d500003900590000a9000501400e032030003580000f018402d0b4501424036071402046010058001c0740320b0b02c003061180c8200107003503020740c01c0180008142c60b8500d40d5500b0143c0446124008100e0f07034060003066010a030420f100d903060389917005200485032030900d0f2103090205c0c0348018498410b540485800048079042100e94402c0c102042c011440724849d140c40c007810b40c00d05217482c030440620f4000c41440d0781c0100784007200c0400c41328001b480c00c0c80417802c00103000c4c2c850351900c103148203403c01160002002c030340801010501e40860b201c900150740c0c200d805202c0c6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 539080026 1250 539078776 539078779
    0x70212180301292b12021e210d060e0601030c050403080a111e07030212150a110417030301030c0b0c03090d0204020403120c0605010812040b0f0f030a1a0f01050a030c031803170a0b 79
    0x206200c46488c001c146542365101c41422246050100e501b054000b2101e1503041011521491400c000b004e607454026401460024a09030b820b00c1e10b1591046c040d0f002d62030a0100f4018030640b00101d0600030030051030000c0d007e00c03441608900040059844040c5400117034007a000b4080340400700c0d0300004000200708481d0300031141c070f690785000c020000c00d0402c0c24800030510400002483e040303000310202d0315a6644000e95075a515510340261084000e502005180000b84a10940030b9008425500010019207911500400b04d00c0000c009200c1c40c0c200800320000500710b100c00360ba01a115039a020300c00d800400040c0d07220640d456441050300b000c0c103505101044140f1181b070f50031024041550032030130200e09000301040810001d420443e042848541c1c1d901500304995010401d0140b0004240d441d88206c1100200003005d91280202250515458224485446119600100401180c0503400e4000007451500508d900e0300000d07806418002040880c607a041d280c8684035030b2000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 539081276 1250 539080026 539080033
    0x601080c07020108100b07050f01180b16050714060411030c1c05010608060c28050706020c0c090a0b0414070512070212180301292b12021e 61
    0x30250b004507118400200750001c45204000005082a41c49001d02031700da01c40d4026001940313020f030055007102c9041d800750074907151002954010030702c1640741940000c1c030b1200d01007403022405070688480c892307403600414455409000101102000c1640b5002c2d07407250003034202c41803585c02010b940e1852030032070591140100300032038040300325820408255031140e000032a00541d650703036683c200001216090414000001c00710103420000c03403074594181d0100140e0540951002d402440c1d400b0300c2d80001c100c40d500184020704e600007000a851081c40080aa8100d40350600503203005c0d0000340c1c00f150081d4100421048400c0608112901c00d01d0143e80e81070420703503406210340054501902c1300b1306502034031081c5010b030a131200c024a0700c400d20020b403801c401c5458045c1421100c02e54000c54101618094054011003940d03d5581d0341c00044a145261001c03000b0680355200503005440149118040d100d400c101d002c0c01e840c60f10384260740948070203101c2030660b40d02c13405c0803808004a681 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 539082526 1250 539081276 539081287
    0xe090f010e0c0c0f16080d02120307030902060d05150f1e040903173610020d02090a0f290703050703031d060a0b0a1a0a020a1a0405060601080c 63
    0xc401a02602e58880c0c90b100f01c031354240d00090303814108000001001886505503000344207a850802855540d03840910003450800c00c61400c01c5003500010b00280100b50700e4200c182d0175956101c0c00d41d00712040704001040740d4204001c15040a0b07805d0010744d40540071407040c6507424540f00e02c008011244510789404000000800c020080040b00801c0701800354183c17070782c1954052103002d28030031034080c1c2d0700d46004000070303d078440e070003a01d007a004203181070f0500341c0d440d03c0d900031030380500411159002584400110510501a00580224582145c180c400001f4903210302203810b0b0441d8011a0a1070300c0d030071500324802404040030007d1501817810403c01c3c00107840b403001001030300d0003480c0014140b00c101450380c240b001c0414401010341d012030140f02c032103101e921584080c120700b1282800303c0c51402c1300c1c000c14000703172a000086403100480d1000009000380590260160301a0300b0812403e64402180c01d45007042d1000c0d00c4612969000640d55401181254081c00203124814140f4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 539083776 1250 539082526 539082541
    0x3090306200d0b01021b030c010c14030a0207180902061c020706020409090201030518190c081c02010e0a0305030f06030c10020c0405100e01030b0702030403080a0e090f010e 76
    0x300400100c84001000c207007a111541d6804101405051100031004110031403060002490118071940700d0004c0120040d10603960f0f40c0018a85007602d00070b007896a4241444e0800d040f41810120100c651400005038201110364041400c2082c0c0e00d070f822507800410806e0310800121190740d0402904148104060000350030810451056072058400240c9445510340d185000c0e46c00550103d0004ca8580d41030204540e0140520750b40441d0040300e203c5000b00070381106030f0300c811400b503d4022000c40075240052107014141c0f1000381030100d04454450029020b0341c1c1c40740114140140065107040f824400f41d410204a000f00250195143d9086440d10b00c000b440042c0081c1c007995140c4900d454280f0b00340c0b0340d0080d064131110f940d0090700c6010240e0090100340c0c0c800401c407170b200c0200400c0600c080a51048040d0640707802c800c0e940700740d595005081c1c3c91481a0b410250603500007003003110130507610050488403881c050381c0d801c4154035000c403413424540080c05403a1240e50400d0000f201e8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 539085026 1250 539083776 539083781
    0xc21090501110a02030d0f0e030c010905061c0608071e060e040209010c05120c0d0306031208090f030708180913020f0321030115020312010e1b1206090a020703090306 73
    0x2100c42c00040e0b408a20140e0b000034908200f61070707010003245052040d09035160b00100e44c0c2c51851810b602414800701001d00003041c1142c0b600840b84155000f080904484c482c4045010350b41004010410442e6140c0d03615036a40c6a1b20720600c1901400a445290f010548001c220200c1c1c0440e101ca8006400040030000650803040010f8100046001c041001c10000c00c500d4508661005195580710b40b11000b10b400d2901c55500304040c1070800744200000740d1066840e602c50004c038a0005030356262404400d060a00040d88038503076120100300c1d00c00740045403004101803494074034207602d120088401c2c00200d110454061400c902c05140f04005401d00a030f0349148100028141c1d03802856082040c0741c2c400c00012880c0e404800440140b043c00d103c4109100702354501d00056003040700486122a0f01c8805002d03807001041c0c220089a102e046910388842421a1000803580390f00c0c684501c070301c00c01c404a03030040c4500840008112400160710031645015055601d0768181825074954901 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 539086276 1250 539085026 539085047
    0xa0f1209230d0510060f05030f03070f08091e031005061305102615040f1202030909070503071707090e1b070b0103060f023a0c0c21090501 61
    0x80080c0b400a944000a2040c4190340400214203000a455401d00307401000e4008190000e5000f607108850070b45100d50f000003925251a44070345640d0101d0903500d0210341a000710880c10303820190030b030f10080f9000c004424020340420141c00301c034808150303042c40c1404d0398000d40c1d42070381083e00342d0910f64603403026400469000c401c903218409005e581f12035010040b1045070103c0b003c6501038000341c038668000e000d1902c489e041150b0341d00250910346c480803442010b5040080c200425084218100d9000303100351022207030001c004184600d4007080c00342560303104403001000110520500c080c0040034810407401404a55182c504450401e03154001d80705026014121014910610041d2021424020100750707204414802607949185081810f403080f800000313101d24010300010014a600164040e032100789030800504581c045c01c40b42e00607496a03a0900f8010b410a0303d000d8000740c0000d40503210602c01c0701d2014107050090203410b412030440050f40c00041c04403000304801e40c4126030ba0340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 539087526 1250 539086276 539086279
    0x60301150207260708010e06060d1703010303050702031009240e070b0703020d03020c0d0507030e0405040501020310051504090e2b0e060a090302210a0f120923 70
    0x540e03468444610791105007907110540340001c0125003c0c4100082800307004c000b070400500038009900c0640c202525070300000d00c0c25025805000c1c1e0a818007461071820f41215560808035940da503168100140907611a0209074000d202c0c2207801005603800c1e1081005d0303142c000ccc0380d00c0c20411100a100c822420803a103070940300f50300c900d02d16403201400c1c0b0928004104007850716031307503d0851a006e0309042400107044281071040c07042c1d007004400820051b900760b40e18030701b60b42e644c0000d140599000c501d001540da0803503e04800c10041020540c021805200b04111454815a8440803c080c40d000741d0300405405001b80000c102180d901d41010300c01c01038003016262034454280f0745c0f503023880c0c56500d0705103920803600c5503429140e000340840308480415909245070203142c95028020000e01c4c4802801000043c001c128005018842c0c4045c2c2140307501a910000500d003840508140d0303c1c1e1064400441c0344c1501d50b0041d00405010081350401903144100c200b1600100b84800000382009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 539088776 1250 539087526 539087533
    0xd0c0809030a240606081608041e03030903030b0f010516050106031202030415050c300d050609130f03050a020a0605041b0603020a0909090c030f0b1f050603011502 72
    0xb0001849102c2d905184403e001141081038824a804010703100c20f0351000342401480030502842200847c010001e040180c04c11864603200e0b890b05441c68a81103030030301001031aa0800c41d0402d076141d045064054003d81e07052103c1c0d40c180d0104011429140d0b011404920200160801d0409240f0022142c900400c00081d0301070396521150451455070704010010381000505016603621001c1290f095050351800d5401c00741508810b80e5104194035100681d0011101050f0380c03500342c4c808042140303544520b60b68031000704107000380c003425098403079078405c0310203800140b000333194805032004154100c2c0c0b003040e0050301610f0550705a0b110821100071402400700400100b00fa5001d607a004522844882c542c901c01081c8101003000300f5017166007014010030070505450350003080b507401e5a81c81c1c28005020304039883d200750751a403e076000034641240d911450b07050040d035002c003030301c9908050a420f1001442d0b41014003c0d4065000e0303d980044184010b100c0407811440c480500304403030044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 539090026 1250 539088776 539088793
    0x30306030c010315033504150e04060b1c14060105190302040e010315050a051006140c070b03060901060903050a06050a0e0f0f0c010203070203060c1e0307020109060605030d0c080903 80
    0x35030000c0649100340050100c01c03086d101100000304200080c02a4030f400f289070420f4100002160719a1603541d103a41009a40308030b0303200580e6550f00420050661000c02660390800c3d07040754003c0c00c02c0302120000107141c07d141000c40721205520314801d2605965461901e8840100b241914031030010600030554240000b0501704411000b0a02843c02040c0760004917924a0144d010b4540c0100401403440c100350900400d00c03200c10b0007a040c0d4101e4103003078001003640f418408643c000c040103841248907150b000208001040001c60241000382d656842681e200c0c1000e6451103420700c00241ba0368400024a0041180d40e030005030881281d100c080790390f100c08180c442c80c00055004017000340d00040164001da8070700300a2481070190a001031810141d030b603000652202c20041441200c1c100018200610280300450f03115007848000b80c0e9622401c00483c000c2c005c002c0420211501450090045001e15000809400081c0250b5402911011642da026501e030050324446416100d40c055 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 539091276 1250 539090026 539090033
    0x1110d030c12020c15090102090f27041104150806160c0f141006052d06041203091226040803164b060e03030f09030306030c01031503 59
    0x1490419044001440105410440c050841030090700c6600103a01c10051003827142c0f03d400d2100340030300e8101d402c4151100c0c00f010803512000959601e245072155074080100f080109240003131070510075102013012038030448842c190b012181c0521800c552200c40011030901c1850340703003480c81c090751410100000e02551800c00501c8014011a0b001c030141088100c0d1203020003d03420001040c9006005041c0741401282d80c03144418400d510244207840f1a01500c513140400001c07805010f000b05640707603a01c5001d0b0b0004d4480c040202c00140c407006c00040c0003202c4520306030300142c00241001001b18039580c1018800a0003080c2042c0f034106000010b03420740d081c07001c1c2ca80344500590700c54404c007075407500703403072110003401c1810019610301220040e405419000004da29080b0015140c45100108992140c041780c0d0b070003d01d03160030300600c0207542901101550189049252000043c0c80cad80c079100b41c07640400c440c207075050b50080881460f80d40c4240c04c90b0040080f540383d82081d0343d40ba502c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 539092526 1250 539091276 539091281
    0x1b06080406020a141204051c0518060f0f0301030303060503010218040507121d1e120d0209040f140711061b07050304140a08010605060714010b040608100b01110d030c12 74
    0x142014200e40340002080706001c004d008c3da0031038079010318040c1540d43d5446d80280071405000c01d4504005010010301e0001d80303030101240e00c6440b01000985d10741121b0104003007690700c24002100024200500042c01c0e0030140243d035550302c0218aa031303c0414a00060000605008010304c08115440c2410300750404144204031902400e034040c0080065441202480e208403521152412009500360142e02500880e40112109100e00c815540d0000310052402038010120810352140c40c164070030103844d050f075200040084283c150b4003400d558651050b60040b1300e41c14040516041440000c0380c0103031410142a01c54600c484860410700203845e0145160000d410410341c01e8402c03000e030310191500301d109600408448009214260820340442c2c0d190198030b10040200202c2c500c2505d040f0007c0d0800742108401510030080ba036620140e103030b07650079809020010145030808131801035105040d0701c000d5020002c010310181c8540c070012002402d07400b44020800600b0000070801b403c490 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 539093776 1250 539092526 539092537
    0x1e0a0210140106030b01080405100b0d1202150105040203042312030907050f06191b12020c1201090308040f020a0e0103031215120311070b0a030203041b06080406020a14 74
    0x301d45400e055030408901a00b100c2440100714148071040c400c00c1300040f4002266600c0540d5101d0200d501d9100b41c0109000c4020f00b1001010510800d00d940e071003650010790141c01818a4081da81c00d039030b840e01400100c2c88103a80152804550390715078031141140440303106034100f11074211122904020301861154109855401c61600714001c10041850506420204e1503800c0b91500d1600c00301100701c080c845032071507090003032100b080e0005c0309041403510084030752a0087e941c40580747c7c200100949070340c05c8076207180c0708090001c20500c00440510440038078650644400000f5103d685403d100c0901d010412030b48281c000c20040394501ca001c111500840c400d450303080b16140d442440906a5aa01e8024031401088040401006000030101007115405050442060080c01405400d045c03080d00003016034a800a000001c0719819070003507103e503009601c2c1210140c0c2071500a8261741c482d205200000340d08001003030104916500420454a01e4145809801c615000c8000d280c1c110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 539095026 1250 539093776 539093801
    0xa060908040f120c09020a0f030506010917010b040606050f09061b0d170c03041707150501062309030d201902120708060714040503061612021e0a0210 66
    0x303003a100d030b0400031000a11340c050b000744c510942c10003540540c020840004030703034411304140c0c9a0b00070a2079030b405075507a08003400c0080d484090000d000c000b054064014814241d0080e0301e480c00005881d44254241c401040c04421280e00d4001074108110650f0000c01200c4252415001032103040780c4200304954000c11701c0c0e01c50030295002c0c5402c1d2142208014001c02c00d581d408c0040000107400184458141140c031503140ba211019410141000c0010366030303101c2c1c1da614060000c07605580180f46101c03608000036000c051107240d50340c028458002d0720700094155004100f0303e288180a0604468001c10b003131444c000c80361072891010703e0880040ca0001c0c07100d420300c0341402075041c0040c0c04501d45c01d4a500405040d0b1620180a6988800502500401000706248401c1c0d0390084201c6006040c02011140b190506241090410310441c018001254070018011480520b0380250382e820038208000641103001d00800d000141e1001d111081180038803541d00c80241023911580c11030381ca4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 539096276 1250 539095026 539095049
    0x20d0c0903051212010e04050c040c09080f03040e15030f030409050703050a051009050702070504062606090d051e070b0405010e0102070b15011103040305150709030201020a060908040f 81
    0x746003403071800c0005000d400d0702c18003c01c101c00b0042d031100ba60114111503107001c20340d8155956040c002d041c158805140d981c40b90800075810003166218560005495071102603401d26041400c0c4265240320328401d01d618011b400001610700206403e110401d084081e082c2c507414400600190706680c040e40040081aa65809000e10716a242c410f035a8006111002080107042014071540400030922804050307980301c000282d8018401d000711002800d02503c00d10119494040544001c41450711104075250744041e20280301000042d502e02820480e40903104046241400712181d030f010f00081450408c0c8500900582c8245d000106072042c09590f1015160074140781140c01c0d9002c42d6240e0750180c0c0180020000302d03050261283c1c1005441c14203003040f420003070041c2c850030446064078100d4000030400200f48030001c41c4100c0354083e08442a0352994a2010984d0401003602020340164002030b00c2e2400220554000031001e07008050761405d0076550801c07c05044000d8000040889 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 539097526 1250 539096276 539096279
    0x5030406090b0f0313061e140703050403090618031a18061b0904060f120b10060c2010090303020f030f0909070c060906050411010c17090301020d0c09 66
    0x25070110864001c0c0aa4001c094940f0140f01000b03c100c1c000903104003049020191003078100130b190782c42011440c408100d1a540c14412280b807000500701c1e6100c161520070618009200c031846403240610542d4140c5032550b1143c1486011034200c15041d110191035031090001001043c2154581000380e181d5840c5c1100500e001d240e403040301c0b04e590701d03e1a160381c440070600c0903100c04407011980c1782e40c184100c55104d801420000b8013900300c3da0b1140c01d040542c4000851154100c403030900b420340c00303241c40350030f2904c0d00300e04464022001d1040c0030000e1074002d4158006146000300000709200d00141d0803030803104800051812010080340c030042610610b007002055011b2100c9028160500301a60400d0a045640b495602c41c1d60611842401c49000282041e400f400605480903000310040241d400c03586007000003808160313802c0e01c0c13440740140410010f6209186924407107078404003004141c65940d005d0070041d000002130303a60654080c0120002c1240b180301d40c1c00410001d646400303415 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 539098776 1250 539097526 539097539
    0xe0f1e0112150606120207110a0b040302090c0306030a021320040906090b1f0c0f2004050601020c04021e03130615031703070c1407170a050c04050c04030c03050304 72
    0x1640c2e80042808102e0900404000440d008010582058000203015945904614041e04000124403101d03500446090000c9404c18114000d07009aa10a0b1100900b0761640d882040a60104071040b95140d070016010600604103108000b000e14034510010036004e04074001409403403001c50300c041078151b000c0340400c0041d415001d13400040c00c00b180e04012400004002ca0080c00c04030450310703d0803e1114408081c28450450800d82d19086205184008201c0c035244001031449050700002d4019080d04106500d0684030f014003400050b002080d00c1c1c551041404040e402c51400e0300900640c0764019914402503000552240714040810b11142e42c2e0380c40d242017200e132a8680d4008440d1070b01030038030004a2110036040b1101d403128215440766128074080b244568112401001c000d090074000036201c0700080c1803010307504505681c041410000700c060b65100d003810320182c0640e00c2641285444d0030283d01094000c8001c0310454581034494071006801c08440d8011251540001820001c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 539100026 1250 539098776 539098793
    0x80703030f0c18052e0305100b030702100b130204270902090c0d02090a080307020109050915210105270604021e0f040e030a08060a0e0f1e0112 63
    0x1251282000e041c420f043d103480d500c003400075000d80c82c040c100e03040c454404c00310200c0701c5a400e100c00c3c656003032441020f00340040103000140c40416084514440100701d140111090f40d100320242e0b4003d16410420121010160512000840c1c11000310001108450640c5c00144045c05204006140c08916100444844800c06240d0f590503442c0043c0c000040c0c1d20111100c1d0006158042141c40d40b0104520000a224201045a10000c681c500144140022018017041070003602e810705002c0c2c0d1107051180500c01200c1d08482a0b4003e0300c0340d0b9151410502203007640c036144140701010b00007803010b2821200207407007806134a0042c00880f101400d100d9021680c04406a01400039418035901040600050380d02e144c80449042000014507100c0180504040200400a110241040c10001e49940c0440103643c006140000010a2401d001810004442c0d01a40c9400181d0365602c2411104101400c00b801c00a1800e201c4529400e803480168042c1031201c001580c405114981b6001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 539101276 1250 539100026 539100041
    0x1e0c0602160b0f0618090c04051e0f01080c0607050102070206121014030312130f060608010c020304150c050a0b0a020d0605010806090714040e0108071a0c06011e03080703030f 77
    0x82d03203007004200162a21041d8500b400003480040d00c202c20380706c142045080c07000241e401500b062900b81000a04550012400e80c00c200c9007a01c000c5640b594100880385071001d00440d20294013a020804842c24040010901103001d14001801c040103640003405a602140307030f4030800502c107014449001e007400d199400406600c42064a41c082c100d010a440e40a0041c1c0c06502580740000640740300c281100d000304080d0b100010010708000c901e491002884c03907026101c074643c60716207603c240c2c500020480b82a9004500c0b0102920046102118a070240803c1201d05000700081c078070010780510300d031a00403c01c0d00300240e141c0a00d803400748100d402551106040210107018050f030354031000342d0107070002030341d00d000c0350b2000800c1c0703100c50584a2070740b1901c1c1000020300000b810030800b00e0078000b0b988010222220140c0000c6035500e0f580142c00c1440d019402040040091510860b014210b05015588903099141d4a480702003a1b90070803003040d4003080c0c0f5080140540e4125124000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 539102526 1250 539101276 539101291
    0x80a140906151c0204020d0216051b010c030509121501240806011e090519091503230c061c0c080108280f050a0c0909031e0c0602160b 59
    0x3c01d01c40c584807400d500140903000039001d0b1340d0000c1c903019007101603012030702c144048000464200a851402c5992039031007200ca03401c200a03a0200490541c071981c40c11007441d40603902d0b1401c1c400040708010814018468010240c0303d4200030740b00c1d41c40810b00e001d000301007401694240b0a55000d410440d90034060300304041025180c10000d20341c0c0c0114841c1801d502918100c90030200440d0140c8401036540c0003aa40081c0c0b440c8040016965100342c2e6060741c00c528401c1c0140b0b40404040e101e00b51090100800420640075006d0031049070b4403a558003102010111909081400d01190140d800280d1400c00400c0100c80e1543c0100c42d40540c1c01400d00f20710b4865259803401401a49480002a0504402500c20715440c100f5511000319102c103034102c4140c140e82112031604a80d10849841c0446090103285030001780442c1d64401c0c0d1144a415449007410001003400803c1d258076000090707018810075901c0580070600510290113440a0050000410b036088d0502c82c0300d0600041822 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 539103776 1250 539102526 539102539
    0x6030c240f090603091703010b180405011412010b100f020105070c1101030c140c0a020306090615010f050c0a140c0406150f050c060c0304060c08060a0303080a14090615 74
    0x7402003551082c02c1030100c43e9103140001c1c3d038600c589001c22181c2007011440c0c07102d120110011800c501c500005282c00800c8403882041e200c0e05d2010302003517502c240720710204225588058040303401c01000004280c07244400008204003588009480c050980000100007070004071144009902441000c1d00318405007401a59945640d8424181d2020040001c0c10903071a0b40401e14400d0040b01d4540549551000307040d203440007140c0150f40c1d01c0881c0c9060344a88203000c0451610100407901a00a0849140b995843d469940040d102c00180321030750360400004001103c4448000c0c041c182840e480360b01c01200c80920740d0035182ca400e1141904c3c0d17200380e01c4d0080402004030795021b80d04440f211418034008002c0d4600c002e4601e4010007240415601500c4100b0500845803002180705910440c010040c0040340726080703d42c42000c0300c445802c1401c0c900d0910119008501c03484d807051072290003180c3c00b11500008612400c0c1903c5100141d886642401002c0b40c40300540c203d40001900c22 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 539105026 1250 539103776 539103797
    0x1204030806043e09030105010329011211060d0f060303031508071401022503060606030b13051803120f07021f0e070302040603030f080f011206020d06030c24 69
    0x4585001451000040088403011000c0c0c8030305010006442c13a024004008002c1c56035681026203c46640320700000b511000700075148142180403c0240c10780310700308050418502c1c2c0f6914500800200d40c50305504c40800c1c09a202000317401e028074030210780f1920010841d1865450068265603000000c0d807425114001d00340912000096050129008540e4541c0648040300043c1c1c00c0c0164000c802029215201c503103e040c420b200d0881e81203d21078101003044e16513804e0308a00b264440d040d03013503100c2c1c510181c054807070320950003103608103401e440c1403c022052010180d00d56444040e00d2072a8140304020081d20412900030036900c032617540007504942c9a44046d007a900c40c5600c0c58a00010343d00e804412003000b0802c4100c020f198042c100700185902c9040162000e003d05507200005521400080c15844503500901d0480701600c1c01e07031901c480d081d60395501a40055486225417562410004045100003103070400401b81da0050014070b0207104012814190600460f5003400000317500d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 539106276 1250 539105026 539105081
    0x2041e150b0d180b07050a0908120a030509012406020705040e030a140f0a08060f01031103150f0d0c0501111b010f11150603011a0d1106120403080604 66
    0x80b900c80c03548111001400c20010b94215421414420001d40b680100320104085650400010518070319603441e0003c10b6556444819a9411803002003004d1490900c074103450030303020390402030300f240314000003240000b00580d141340c0e0f4192045104d4a500c5a03164204901038040c0014409454107440900c030300261811380c207170799118601c0c1d518208002c40762844030303201860059859508840e0341c030300c1d900c95020a0041801e5020744080d0702c07446609200d9407256000e446009455a101c425442c10350b5580c80c9803210301182402d0060300070000010110701d603a100340790524842e2140442d245040c2c281800107040f24946004900703142c0c403a0700b070042c0e4002c461400030b0801b6030900c1c0c0300f001d01c005004202d412410080390075855215441c1080102074034640040d10421050313000700030220840744010b00c1e000b038501120340c101c030502071520f01040b822080110440000b5020038545950824501081a4106e6080d07001a400c0024403441d80780500806102c4103080182c5120380c4501e01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 539107526 1250 539106276 539106299
    0x121f06050a03290906040b01081f0507110a0b010f170c041d010203090705010f0207030b0604090503120c120c0415120617030913050906041106040302041e15 69
    0x202524541c801c14074503c02c0c002000c800c8000c8a00318401d040c1c14103001070740d69075440080d501181c160720420004a0b070349400283c8400a10303500100c40113a030354500d082e14000d01014007181e0070440841c0d5400c03541c1c0002c01c103c101342da10560320317044c40d903141540842c503000daa500f15a400780100c43c03107010140d000040b15805100c0840340003441e4041100d0711250b0b590400c22200e110b50000c401c0141d85000032800c0030031034800f82c07210301c00710441a8080b03860307401c03d0200600c10f10241c404106142042e82c07060381a00e01c150b048914028100807820002d88085402259070f0300c0020354075600075085600d00781c00c504006500360403e400c1c0260301e9107a0300710011413002c200b0348048681d03c640003604104008c1000c0c0c40c8240a080e081e071405a120350100a0701c5020320441500ca038a000401c0c858244140a0354014148981b541d07a143d83c0c04c01100d025099108009202c084050703a034030b20501941030070480006400780260404070041d2982d06842203d00d4401c50001c00c8200c1540 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 539108776 1250 539107526 539107529
    0x1050a05060d0203060402040f080f010606030c17040c0506190f0c0f0204051e01080334080d200a170f0a0902030f0a06090311011523121f06050a 64
    0x25400f40c2c407035465401150013800740c0e038420400901448400517044c80c0110b40e40c00740010350002400040d458113001e42c162880000320f0304c0001c520034040100e0036100601203400c1071140300400c1c041507407000010040c1e0086c1c0c1c050b089104400c48030266403504542c106030344125604000c251414191200344514081500c0a0f00494a83c07000401c0c3c1c410031004032003215071288520440d540c54011590756a003141441200300a02c04240040d440d400a0400388401019459134548076140d640380b0795550081409001d11a0b100d40c622009030032004244140d0040e001c10103500c605103440014003010280000c0a00242e0210903c03100725001021941d204151240c0802c5042a610109280004900143c4100d010300c022000402c901600300300d4205000e81e9450101900e80c203000d9088503c900d4080c070040d030b040a010800403642058814414494011403460980d4203400700d04440c1c0709140c058803903040176100188100490b050104c2e698422081001b64900309000302d42108100d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 539110026 1250 539108776 539108797
    0x80d080a020a0e10090603230103020d0f0b07030c080105180f0613050c030709082a04020706050f0610050928031b09050c0f07020d05120f030f01050a0506 68
    0x707000e503000b41c01000b203c8a961006400301c4501c022146004101950761300608000904180080030444902d0600c0d40090b02050350303016859103541e003000381e504141c803012540380c81540e4840020071001b00d83c25200307054580b800b180c0c103084c02d20014812107058114511401c1c0d40080c40307031044d246103026039002000c03d400083c10780361140000d213041010484800c0b554145002c104015031101d0207180250a90303143d02d2143c0d5110f4841584a004140282c110043c046102e82c0c26548610304146000d20082d000506c0c210700fa407240d00c140c420841e0501d554107805000d1103014104541110402c11451800307038100507065000400740a451140f00f94100c09102c41007a42042d9144040011540101c0028024074100c0d5a4004200b180c40f5001b070b40341c58100021040f00303a03402261002001d0154140c0761020390f5080010320030b107800080d1a2407054065406001c2d050394000c000a01d07401401a4807850030300440e94421105800081c001e41d11b140081101d0f413590b80651f62001c40c3c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 539111276 1250 539110026 539110031
    0x18061a071226040305040b0414151603180b0c010b01112406030304090606200102031306020d1409010e0601050a050d0b15040504060b01020c0d02010518010c080a020102040609080d080a 81
    0x3c1c0da04084a00c0d00542c4c102ca8949034000800241c7d070744040c52140c05100c4150b51410310205e02d84400d0b1454040c03e40003100c0c0c0c40d000c215038000684034140041502948100301c00d135003a04c03003817440d88581048107810010307995291001d80e01d603048600c00d041b02200d5001401d0201c010415500340c1c0a10001011064401d640070806035a01801074802504403100c3c1080241d56038003005203020364650041075480452410485010010300840f403240742464081581c3c10440c0d651800203505c203150681e0b441e03580b140390510003000d06903594054541d03107001249521001c0c0186050a01c10703840244240c0703480004102e240c0b00d10000010107600b003480c542d4030350b5412800c0b41c0842e40301c60380c465000d4174000400c003c000d165403004582080030380c04c5814800c65901840458102a8000307070100b5000d20080c80350a01c551130490030540180340042e6550800e6580e013030150045102500540d40104081c40a80d40c80107110004003000310040241242d009405000d001000d05070521154 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 539112526 1250 539111276 539111281
    0x10f110f0901030e06090c0114070c27050403180906030b010b0322150608030a1d010309021305011e0b190e060d09050c040603050718061a071226 64
    0xa0090b4000031301801c014080e01c1c22860b21700c401d45c5c2c403492194034a034003284240c5c0416883c0d0310240141c1c0d04559000b0300c0707400b20b40d0506d1440042ca58080c1c911800e107111212690240c602107000b014041c43c441c0e1202c0d18485540d0884031402c1407140c1001c1031181c80d1400030004070318480e44e6541110310008995541c1e40350316802032400303000c41d64030b8280030150005c080100320050070800984000350008008a1383c6039008580c5910940e001400000e00e100b1307141d0081c1e880c060a8040303491050400103a01004e607404154000020400725004603035450040000c0c107014008800c40c2500300540740040ae003007803c01c42d19401641180500c0003c1d0020884096015141203858428010b00c00c98407214041c441401401c050b41c0125901d008043d072545107418607009901c2520361190281000c01e007814100e040e642c1d41154091801503d4039400100002c0344114030702900000c44d5895036401440c00c000e1000d94941388608100812000311400540401e00d4030007056003036060110980c3c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 539113776 1250 539112526 539112529
    0x2010c0203150402010f09060e10091508041a0c03010e0402060d020301030f020a060f051e0f04300201052506050c130b040302060301031e051c02010f110f09 69
    0x6110060000390580b09400110310304001c28400750380f0840c403d0f41da0741c0031608020803c6071903400502c604404611a0501c0e62001d241190503035010407021301e0581c1c071040c4c0d25032140900e41c1001d520140403484500522050088141c038078a018001081018050f007005894034005100510a8041000c0a900400c08560b00c003070071220f00312000302056441396101e0400c800d1298500d54100d100d00762450300014003e007d20401c188010440c0c440c281008d45c24400c0700c0e84034280c0160100b420004015080c0e008200c2c201a10142000c068544000002c5501c449680030180300c9841e00d4142c0700847c2c40040c1e81c80011100121040000398041c2403403521102540ca410a800608060408c020000030050300360241000500e61182e498030345949800307050040c403139800041d400050030801400451000b2581203130002000001403011149500c038981030101180906c21500d240070000c6001d607a090080d43c0b411604050208000080c003e0b0f2041d040c820b010000001e80e0020035500c0c480e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 539115026 1250 539113776 539113787
    0xe04050106031b171605011107080a050d1112030c07050f07060e1003050609060d0c1802041a031603050603010b0418020901080303070f0c080f0a080712090209130201 73
    0x210b0307200310700ca141d500340c00d4038180321004640200341540b071106100380248900001c5048545c2000300906072a01c3c141001151b5002c0f407844805c40901c241040090350000070042200c1c40c50090028200903070f14844000c15480240905140b9503004050030a191030107202107980010421392150b64034440c40c07521030b083c6440036181c0c024034019010000b81a41e00100d8035843c4031000c940c4403880185490090701190005d45085402441c040002403540c10800020b241280c0204200d1851a81c2c8a01003c0704140412035000100c0e00800e08110030b44440012464901a0840280c1140f0704804050200840780c80560101601ca40100c1e4071f50714207501150640101808c18001000c040c80c0d1b40c80a52001581203004480b440000961104080182d074011560703a0b40d00c2584440307a09007203400c800080c40540d00300c20304011480d214000980200820344203030b01c844d9124941114040e00c81440100c210200741c0c208282000103a44014655900a0940665146c00d110900040f42c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 539116276 1250 539115026 539115029
    0xc0e04150510150f02070b1b030703020d030b1215150d060b1005131e05100c020915010c0314040918060609020915090411210f09070e04050106 63
    0x100c051804050209000601e075000302500d460010081d1903222118046030350815000e0b9600c0160801d050600190007408000d00a1040c2d209050040c44002c0940b04d085a21048003280540c3c003d51000641f6901800307210302503032080311044a420f807856a65a200e0514040c1802c1510f0202d002481c10f400c0c000c004500360074050170300d60366222507261190092000301001c910800d10b035443c641c0241e2040c2c0440b0742154060850a20003458a15118143c0e1581d24002d54140c004c0c0074041001d40305c904a0309011001aa00c0e01181c601c00c4c014440981c4014040f18242c104064001c01aa42c000001c107524541c035103403500520004411401c00b40c0641c3d0010a0b00b0f40c01d141c060b6080e08104201d00410a000d0901000603907034030845a022440748480c0290000305030302c0d804c0ccc402424240681213111000e032002c514400ca54800308003c1d4081c2c54180712008490042c003100301c151a04059000c120300c603080980c2d0900c541c04a6440240348542d40080302000001002c020080d00207a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 539117526 1250 539116276 539116313
    0x61e1e01060e0301050c040b0406050a021009030815040e0309011b0c090522020f0105030903130f060f17010e09120304052a0d03030b010c0b04080405030c0a030c0e04 73
    0x40055841c0c0030700030706091204a01a21960802d404254101a40012101147c4c4882c000a107071519208040d11103402140490b82540a6000034018070502c0d0301a0b03002d02032003982c0321107461521841104008030b14810b174a004d1464a4400824107000004a0700030b480c090800699060082101400280007500c0040682c1c429050000d070100041c0c10142c05032594200b001c4810400080d4003420070000100a035008000100c580d2103540200015500409103e0a036450241c4020a418902840e580040300c108400c16081001c540c0c440841c00c4260300d86d261078460504405102200810103005804d0b042e007401d404100d0b103d0301080036080e0000c0c0007603650703100d241c83e09000d91a0312041001040300c0000381c4a000118071048891192420300030b01c0c2120007140d9490031801090f245c00c14a0500c00c9900003180030030b20151309a031141c5d109110455603503040c00c0a160401c0800035686000c0c00c4505024000114a1210041a56806816001d9640c1c40f0306240c008a10000e01e601b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 539118776 1250 539117526 539117581
    0x3020d0509130f090506011e0603050709091d060108190b090307050d09080c0916030e0f160f09090206040303031127090c130e04060f02040b0304030809061e 69
    0x15034186503d074200700700e014007801c1a10100d030381c0ca80c1c0012024016880118442d0594007003030281c640640d000c2500074003d03150071250140c0398810501100e03061000401c03503010400340101c01260802c00316000d0039664000d0880002140440146035914032402480310300c0d070a0000786005420029075418a40008c12030340c050036400406412a02075019030301050007500307483c1d151030505501160065011050040c801d03908140210024060360b410105140202502d04e20000c0c02004100620011074003450302d26450091280340703010b01c0da1b002c0000241060424005a03442a050710200c3c0d8040c00e01189528400351515907a01c1020703440c171b030a078004051342c00980c8000e00032100b48181c1924540380c0383d10380303000d07e0311036000e03241070240002100341e414411041204550b0350028030443c03006c50100c80400500c0305030f070030582000c41c8c49007000c41000305041d840758900d600011910060020b40c101444140011020120201c001a4808000c500c900624080240c216101c40703490 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 539120026 1250 539118776 539118791
    0xe06070809150301150302250203010b030706050d050906131407031e020102060f06061e0906030109020c10020705031213020301110a020114060904020d080d05090c0406080a03020d050913 82
    0x402d00c40390001c2c054041400041010940080d0091003110032050061508000c503009685400542c0050444101d0f01035484042c40301e200e0b202000fa0b440500300c41c0e01c4003a21400381c603c2c4842118402403e81c0e0040d0300c840c8c28058101c150124802480e604060728008880304c070301e0924540a00b59100508100e01d9264426010450100c071000180c0300340d00359885a00c40310502060000180c43c1254064030030054809951a1065008206030384400c1c03031414411442d00083c06a04260701030300c0102c0d000074060340c041d84280040d90389529020340850a207001929010f41d00d0040520340c80d0101100c1010410390040c110264a9507640280288218680120600125000300542c04003560808606404e520031850400d44660382c003400c41011591507408128600d00800c0060350401d03400c10620103052414040c5500c40c2045070018907408903000b00344003c640e02030344125002c1d0091041c2c2e00020768041903a48a64100f8500591102034160000e202c03070314800f0f00907198619122a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 539121276 1250 539120026 539120059
    0x7050c03070f06060e0709050f0d02040e01061409010b0d02030a020405130903020c06040e130f050601060207031703150d0c0b0a020a110f090406020307030f05151f0e06070809 77
    0x442d032120310310615091180e141d503040900030140040d280349001c200c02a0f414070660401648008146100a1512589a01c1900440e040b0340d01c1c07040b0128141d4480c0c90a21403070062800d010100714096441410380c1d0316110500240e030003007202145c401c03074001022a45441141d01a40c0c05003070014030300c818a0075400003d000507c0500e0085015006664100c14140340600684045400c4a43c1301c5295030798510218039400014101100c19900c0d203000d08000c00e1041040764046c14182e0002c0c2903650843c2400c03a0000c5551b0460980c0003820410801d02c003000c2002c883d4801c40c15100100304183c28900141c0184081c1c001c03001004000c285151269070004940304518007641109940c06086000c6c04005035400345400c0d00101000003160004095900559015002e0302d40080c140c84884405003e50b942503c0a001603034016000307809501e130100000c00c60a8444410043c0c0b100b04000142140914020f960b00c1b03243c0100791082402955800c4440000000388591581c0380403c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 539122526 1250 539121276 539121293
    0x4110d0c08150a050f0607060203010b07050f120403020d03020c130c0e0303070507031b050d110108100e01060c030908070f061b0203030d1112152d010807050c0307 72
    0x80da0140000c441d41c020841409640b01e80c881882000341418a240c0e00340428030107506450300441d5040b03001002940c000c0703440b9101450180c00c0381804580c2d54100350420500d0410301400c204041e400c840000d500d403240c10381c03c41e01141d9059580d80b2103a00c603801c05a04050300d421075650480e4544024400c3c1d03208941c40082002d4007a00d403114902c1d40e40c8241a80d9004080009207242e0010700c0038000315060300e100d10850518020f000480d0750300d840101c0d13035000380b0343d104603124014048803250750741c0c00c0840d440d480251540302801c01c82c0b4001c03031b00f80b038248107100341002d0140c034510400a16100d04590401b9100300000c8498142d40c402140340b00b00b44601c0f40000054100d4503800082100c1400b01000e2500100258100004004964010074120000003102241041f10106000b071001419228800c0003403070140700760380c890a000d0702c983e130705a40384140c190081c034503419803003810700406485000786010300851759100c00650306449031071101e440c00d01c00403130742404218010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 539123776 1250 539122526 539122541
    0x903050a11061614040807030803060f0409050601090c02010b0d0b09060705130b030a0902090405010b130606120c0509210d030204080303131b060e0301060e19090204110d 75
    0xc0c0c0d10700300c031841032881c0c45403180c0081c0d40701001c20021112280c0654415801d611100b8251400c0301d00d41380c0c0d00c0154501d07045660b070085038004004000c10504d4a0f0500d0270360fa004005441c28054000259034498449905004a0841c01c1c2d840705100310b007074400d5005078051034020f804240003da49080c00c64540800b1207005083e48174010020b0303075252140050726400421400000c0c000c07410b00c28000081c0e00010849a4111303035980340360002d0381c0e1700c0d40d0240c0103d004000004240c40084213119002c027003042003050981c104001000a1584804510000c02c5140c50010303940d114036504a80c00e2080750a07060f84020305510702c2c84260004514103021035000821100c0490243e00140c0070390080b4814020241c10610000c2c100d0114540b902c551244102500c2c0e1b080340c0d500d0070044c010b0070103030843c00c0001c2d0b407103440300b03030701d0070244107110180540d10007114051401102900c003c51034040d01e94042030b12510400219210340d0883c60555520b0240c2c43e40f500c0501c0311590040849 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 539125026 1250 539123776 539123797
    0x30703080a11280e03100e03090d20031609180501020c0706030b0a1a0c100e10061a030133052703031b1603051606021501030b0c0706090305 62
    0xb104a451541070144c469454032090141c003910f5503c50003140340e002001a44000e60032400b0410540d500c80d51070850360030119204001455109890031a101a4602a070395000c0c0268003c1c0300301800c840520048800712151800e01190302d0021215405083e803004100410560010803010b04480700480c0900a03520195800c1000c0d420b07000c20025086001d1052a10104d1070281c500c42c100d030100b000707207500c80c4080d08070b03a440740d4084050011240c5581842202d6007101d00c00460040b00e9014110040c005180e014482c085140c65509052006108400f1140b04030f00f920380f8500d0114240310301219050b2080341c2030800c0703c1e030081d01e281e0100700c080113101079054600c4c00d103240c400d0320b040549002034000d45c01c110b102903852440342c0341200041000d10560300122140400a1055005540324502910140c108164500b80c1802e10f600a42c3c1550450001c01d05003000c0d2007800f50459412120f07581d800d0300c0b602c228401c507100700c0ea0301415036030030200c0030070500da04075000b40300f074800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 539126276 1250 539125026 539125087
    0xc0f0c07030c2c0a050901290a050607051207030903120503040303060b03041a060d02030610050907170411010e0d14071517040204140915060103020903030703080a11 73
    0x3040074207006a40e902c2c40c0c00c00d0003440440f0100b40d00403816440540c0c0050a00000101056152050454600081c8018888901441c0903034114101446054001c244c140d030b1803400e042441d9201c80d200c640742102c104400001140380c405061282c942d40000396000903d1110f09860740c480180706070301c11074095001c0783c2481c20004e400360024044911460b08080d03407000164205800c0016601d000d4040341e03100020b80d100a002d60360034004540210b10381016203003a107103480203105405034002c0c0b00205020401242c2034001c080c610758035070b000343e00070b440381d00001c5100b00590f00c5003401024540c01101c8a05003a00308582e603001d500a20010034210396249075508000c4249149440c0f41c06d0014105180701001009110f000c250001d20040c0301080840081564181c1703203600701c40f00c9a0b581d016100031450301c10740020382c542003042860203510301080b840210ba036900c10160000c040160b40c02c0000e104a1860788141c0c5014000f00c0070301d07031703c1c0000080786100b03450b001c14490002c503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 539127526 1250 539126276 539126309
    0x140105100b041203030f060803040602030c060f070c0f080f0409020c101a150d020f1201140105030f0414010509030a11030a08160e150316020a08030c0f0c07030c 71
    0x80c004401e030b40031200303071107442c1801001a58089028042d10580c01100c0343d2960400325203c001400070b480035046944c0296110f402c1c165a144c50200080c08807009910114103106c041684004120052900500d41c00200401072416510341d1044408001001300041008110300c01640c0040c0b8030016903000b06c0c0c081c164600c40780800c6514a14121007000d01d070382c85050450400d4928402c50b10030384400c45040c0b0310062003203026641720264040340703c807000803844040301c021443c0c0b1307000d07042d885003000e41c4201c3d07080060b1842c030010740010415900c20b80080c0030000000111684400c03048001d10560410445c8540d0740d80103034106c00c011403407020314807095200010030b59850045170741d00c0346619103440c1c848800e422424540d020810070529407a40003034494100c06260801c0d8101402d59915020f49281060710403103c82004542207144c10b040812868410349811401410342c1e070340e5408081c4000310a51080c46200c20031401290130000900115440e10380440da1491440c07128403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 539128776 1250 539127526 539127539
    0x3010b0c28030e010f23090301050f04150c090302040509010f14072006072d080103020f0f0d081305030a05061006081605070c231e010912050a14010510 67
    0x10790b03443c60700d1700014501000004402e0300c0e101d0100c0880b10781800c03042c5080d1a10340441d0a4901c201c9401c0340c040b80d8001030004002a1441d01d201007030b559602040090f1090741c1c01800502c00e448082d1082c1e03103032000301c1e60f2510701b03500004801ca00010200144c4240300020aa92202140e60b00c0104450303d448148004c290419840c00450401c040e04043d0b45540307050300d84443c070303032078a072001220801101000c4040702c0b030407209103a8a0321001d68561652040103034100d100c400c03d60081000314030300c084980f212903400c0385075503106800503103070b0b20b2500e40e00d60103c080d50b20595262003400008818000b0106006020380803070034207540040e8031100103942c86203044d1340c942242d804070694030700380c50b1203000502445845900c04508a41e0b5905020715103116500d07042e072842a28ac110f82d08546000710b69513000c07054640c1b41c04030b041050700018096224a10940040d110248c41003020804141b0003410081d902201b00042403060215541c02028100c89200c00b5025600c008280c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 539130026 1250 539128776 539128787
    0x60f030204050319030c080f0309100e0d0c14101401120302190302070b0a020313091a0f150c06010905010f0b1815190311040b03010b0c28030e01 64
    0x42d180064000d22050404106015080204820950030000180c0310140012081d000601042243c2e20f40e407522810702101c01d41c108622500018042ca151038401c0c006400b0104000603035a610b824250700342036a03828038800c401031415014990f401351019141c6850b0640d40316529588040300c3d004043d03030704d42c056001e480480710b1024015074800480341807892504019048114400e00c140c0382c4e4190b44280540a17a00080d5103000076030400b11b0554011203003100102d004115404040c0600c0c500d000c03100200c0300c0035070401e5004160011200503103480d42819800ca04140301c1d0a103a4075562051015103c5200303005101801e810b0000001d4146260b40309241623664045085180c0101c0c4a21104841081d0501039000000500810210307014103028260700341000c4005e0381c0036000203400800300c485000180d442e03e40284014000086a035094a040d19821034495a0700d080d0400c0035483c080d0b002004480c11007aa000e010402c4040c0d419500046101e600d034000c4400820006641 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 539131276 1250 539130026 539130029
    0x20304140d3f050703120b0609010509010c151407030b0105340803150402040315150b13050909030306030604020906120102071223030a0c0522060f030204 68
    0x510401000d036400410312882c408915030500380c0525009542c80440c01440140324910320110f040441e41c102855048600c1c8544501d02d40c00800c4554100000180700f801101401410000041100065a40590044590640c000d054941c0107552600008058000c143c15001070050802c08100d456000e4010901032240507118039040003032400249440182c034030050004078181c149d90f00a21042500a02039a600404d91150b691601c4c14207070030a84040440c03d4080c41c4108810004241c0c2110000000f9410040c04a1201c4000c80d08040c0c140d11908410314444001540f0340300b444040e07442100701c50003944c90241d10741d643c0710056202d000c1140d9198054000100042c0140f6000c0e21860b0300000c000c04400703900e00742c508464226040150100c84054422a5400d61513401c03a0300800540d41c007003c041c55030344203116032620741d00015003041c4020b138a80f0724030206140a94103545902c0043c1c00c2a056880700000103078154101846100081422072581c004803d1190081340c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 539132526 1250 539131276 539131283
    0x220303140307051c0b09090c09070c03090e0c041e06020606040504020d02040c02030d0905010f270602032d0406061a0a05071104020c1b06070c09090212010c020304140d 74
    0x7418803400030901d2142c4804030340307126412555845001255901c00c00e2184c05649007c0040c0381d40450f040503c940c2100241c40a002d01006034a10000250300c400c035032065818076180e14640c0e449008414401d03020303640190040c0a0018812181c81d1801903880c01151000d50880d04d00ba00c483c002d200c100c443c00c0e40c0103900099120340b48809401d264000d455506080d1041340e01d06202c03c0c0d0305900300c03207008a007201c66945510b045c421400e40d40c06a80c0f00e41c8545a0580c858441b810081c0b800b00c0d24002000307101c03640200028845001c00c00700071016495003644400c0001080d414001c0c004002c17101225082c0c43c0c064081082960140e40201c88074900d001c552400b6441c12040c2e030190030160302100c144449150000890310b8031f00140035560622402080120040240c0780c514958100d042c85c0600020b001d098082800e20285208076205040009000041400440d40300d444d00403014180c2e60800f84400381080e030000090044540d1030003e100403072030800030040010390400c0d015 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 539133776 1250 539132526 539132537
    0x308130b030f04021c02041820010215040f0b04030915111b1c080301030b07050702010203091e042c0304030506070e0a0e071d01080906011802220303140307 69
    0x14006003000300e015004442072500017007000f07005500140c02d4400944000c2d00b04e1102550050030814224070908060b4800c0c05036000181034a00001c1d5544044c0c200ca46004c050f203004141445074229031064080d42103456528146494180540220387c203201d035500d10014101c1e0a600e0a11802808041ca0b0044016000c0908245100c1030072030061820661304c10050503840303407040c2840741c048040d10b10400d000307a160f40c59030501904501c4002c2c580c0044c40b404100400050381e0100c00c0b1170840001700c41150083c0d03000254500022025061190030910349003114003000e200e00d01c85140b218580e900c0450740070000c1009603d0f4002ca120041c400d50201c800f0076800c602511503809801006042c00900c107031f80e94500c01c000d4400f621040d02245080345d85504607800220001c141d10030070b00340880503042492500f40d0b02ca90501c2a82c8129030031203081e9429041a40440d845a081c504d0031a400e030804da40c0706604603c41d0300c03088022404240a81804018140a0720b100d0011900c50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 539135026 1250 539133776 539133781
    0x20a06020f2e1806050709060813060219020c03010b0312040e061c030c0309060305040807031d030f0c0f0a0b04090519090809130b030309010c06150308130b030f 71
    0x300d034442c0d0341c048441031410b0310795904582c100300140719808004060b080310100d80c0c0080c0c01c26000302c64000e052602080480307007050100c43e802440351a0000501c407910160020907051090084c06040c51140160b081200607800080c3e001413400b000710012802005403080c0c5504143d550a0700c000082d0380300c0d800b80020003c011070000395035070105018008450301000d841500b038509200d14401c0300031400e6510968141035000c07044c04040c040d03d0070200110306240d21030309410301507910003d04001c2ca1041c041e16407175091010390300c807001c09022580225001803c85494642004140b80a079000b0004082280340c02180361040301c40006440307141c103041c0304111011308270080c0714682c040001d100d0b80400000920903400d80a001e4000c0c42d482e80005001c00c28547d42a0101040ca81e00348904135a0b01d80d008811520810401d081501c0a8122460300301c018140c0c0003044035a1070a252400000d10500c0c0006007044039080f01c10028650b21070f15001c3c05400191442c5a01d1180b2000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 539136276 1250 539135026 539135053
    0x70b04050114060d06050a240801050a05060d1218080d0806041406100504050306040606050102010b0406030510020a21051803280201021306110705031903050304020a090603030c020a06020f 83
    0x1500604651400314190340e241c4400c641303900c0c0314a4100066230702c035002001010020301c0b54a400032403081041c015401c000c000140d411200c9580500f0101840c1d40e40181c4600803540003140410041410001d1552100303080d40b14407010303d1203000b00d8460b074001000c5260034460103a0700b02641d0000c0000f42c80340d0040c00400031020b0302d00001c0c40010480412669800c2029902c1503101e40c10100d04030b03007020002404c0da444000d141c3d00032030400e082070000070000b20f8501c08144640074010303220a00c811040701c41601d40300f001710000c80ca2855503885101940c0049103e1240803000042c007000110f8043d41d607100e01100840850240c03d6121800c60101c00f12110041c03152001505040481502d245020030aa014101050214207901d10078030091244000401080300a00310040725694039004014401c6c4000f030070004000009021580e80f14803010280000550400440e07441c4d01c2d015080064901c0c00340c2c1b1550b107185001404a10001b015090b000b4400d01400c0010b40461 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 539137526 1250 539136276 539136281
    0x51b06130b060a0b0f0d11160b0a020d06080102071205030910050705070605090601150908061609030f0c140907020a030e010e030f100f050c071b0902070b04050114060d06 75
    0x9000d540d202008080000700c40c00e600e400f820138611782c201da069071001c08141800032151a0100c0b015540c40900ca8803000610360854948610b410626440a60742ca200d2500000d100b08140714113580d152000110b00000c056001c2c01c61944108011702c0400d81070306040e54280001c07219210a58045088d5224800701da820094216032141407203803c2099985e1a001034a40444004120354404170041240d5480c81002a1400c940c50611250301410115101d0300c85200610741a0011106201c040c6820b01c5881408021604024204044140303480c1224802205100d04120815480224011403400c001110301608641d001409411010340e0150350450045081d28140020002c2c81c1c80103171010b2104030303200c160a0016203c510a800e035500700709c2d400c00c0314040e0502d00d81010000780c14040f20844d00b01a8210740d03641c1c0c07206040300c2c0c01501500d180d000b440003903001150a504000d042d06035280690f01c154028460711540401d1380c100003004480342e030f40c0030212a041d500841e03842d9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 539138776 1250 539137526 539137531
    0x10140105191422090c05011b02120a0b1e0a0c0f18090204080a05010525080a0905151602010c091707050907050712180314011506051b06130b 62
    0x9003400004085030500040b10028240001d02811303100e600c030b141040f95611081c00a0182420f088085c1711001035403c042d030740c11940c000c2c0030380e10050000b24154070800c582c3e1030003640401c0c10500ba152841d8503003002213181680240410410000c0380c64803085001c2e6041e607610b0b0361780b2a07520b49071b059402c89000e001d510010080b084090404a0b05002d0b500013000540000f00041014003102e203000c508441c0001c102198071100c902502c014916640c401c080c020140e03244c2070f40c403071320f940c1e0448000780306070a0000c02510405901e03400c0ca015840c4014443c00e85081c402c2501e102c1c072501682a03070040030714040082c42003101440b000c1c0420003822090020101140c0c0030684034130205001385402d0b6844400b00d007007c84c2c3d0004204007544480854625481c100d100f0a92901c0e104660b11700d00d0100501c20a10f0345407038100c0110952007540c1c0ba03a20b00504004850b42c80074042c0156001c1c104d0100c90002580e80884d050b04009011400380202000499940310147c541060b0100d02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 539140026 1250 539138776 539138779
    0xc0b0301050603150d060e010b0307090b030d230409060509090f070603020c070b03040b0a0b060a050a0302090117070f03241a0c030403030801150906020c0d020102010e101401051914 80
    0xc0c94286010030503e07c0b410985c24903004c0001004488a01003614080082e40181d01043c00c2a80000003502c002ca421114041541080302d400071040d07400ca00c5843e80306000260210010500144481107134004008032201030301c60054540380e10030080d40b11040e141406405501c03100b8200701a80c4640c2c0200b0000301413500313441c40d041e11802207052907072041d5411340c1d91301c0b0000180029a212841130344107480048420602d0500c0865001d0843c2c001d4030b82380000c0c1903010810403202c1e40159818814842c0c880001062403a14140281008091440c0c0800107850004043c81050035440d0344006080f0310010740c120b141c40d041e2800e001052221616181d14401c0c011201208c0040000d840910321079158130705150b0520800050300968410310304100602c5550401240350045400c80000000342c8a2007024171841c00180e02409500324500d40f94498181c0001408005610110f0002c01031058041d0f07590b038440130044070541112907141d88400644003040600000160061500c0d030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 539141276 1250 539140026 539140039
    0x9090c132408100f090f1104120b130803190b062d071209061803080d020315150a020c030c030606090403030e16060e10120906060911070c0b030105060315 68
    0x4403604d04028800341940904d8449441e041500d1601c2d115019004401c0c2e22044480d0500c3c2c904501c07410b4800c82c03d88068801d0070800089404081000035030202c0c01e400c86c44896403402c01f0030311490850511a00242e4061401c0354070013003858043d04480f442016101914100144100c100640860080858000304000c102c00d5001814002d40e4806404840d03c0780200c0501c1c040c40503210009031141495281746080341400000e01c13680035101e4030522640010f0701c03561800d44884891590820721035000c1d401c400705488940882c1c0c02003a2400b250b80c02e4a048075814000d0540d15101506015415000000000c2c054103041c02d6060344140245004038016061240306820420020043d443c40c5107515424407207140c04c2001c1150f0800260b860211540c80108010032034400d9500c0d1610702619560904140002c40d0444805070100c25000c121007140d28410010b05d61082c40c04071200d41c040100050782c2c40c0c0314419281240d601525041c03465490382201691841c0c1582c400342d1101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 539142526 1250 539141276 539141279
    0x50901091806050a050601020f010c05030a0506122a0405040c060806130e06160509030703020402130308040b04030b010501090b030f0a0e060703050403090906061d010509090c13240810 81
    0x50150040c44c1c01040082d40010741d506200e4002070404040c910090623a038102112038404a0b4403a00301da81c000210000040c0315292000010071030711581000401e0742c410510203c04200d004007210701c5511a40701055214401c40c01404243c5004440c042c0100401d0f8004000c020b00138240e165001c2c000811042c0003842d92480c000440750400003d00c1d00764089400c100c44000d891180540313054282c2041030030305604000290383c072006c078000240a1038010444044045828010002131507100b0318040d2182e4460f41550000d420031322040e80d04080360000041d09500a5040700e007174403040f40f0994559a29000c08410640000e0803001c0d51a035144d1032101055000e03c082401404650340100c1c0314142800e005004c1290381d0016000145003200401006030050f411041c2d5640da00709042d00c03801d10704010303103040c0a007940c2c4a030007210407403c1026400130b85008107403c0d410048000c0080740c079440c40007565400c81c03880c2504003d100b05c1200c40d050081112070f505c988a000040310a5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 539143776 1250 539142526 539142533
    0x3020403050303010b04140d05210d021b01061202060a0c050c0d0503070b0610050403030323040c08071a04050607060e101a12031b07080a080307030c090509010918 72
    0x198005d0f40300e0b000d01d1002060030b00215a1000d204202d19004498a881402d015181d4a032900114890341d03000200007076951305904407101c1918400c204015085449a14001c48104030300710030326106031075520b0042c002c100c040b0f00da0319208103160040c203558280b552410007680c1d0390424800c240c41c7c1d88642802248141e5030b411212482d10303c1040030319210788081c42c218000d00750103015288602c3d1000381c800125940f10050b41c080741d816213000b19070301c0e8072420780380c441b000200c101090300d0350803608000910038455404002c85d0303500003c88403540ea45041c1c14400c01080c603424081e100c01000300300000d182c600041c00b9201e00500c1c00161000015083d10b1602d0294146222460b4441c584c0c200b0020510500301d0742c404084d621041e0160101031415141c1c4903220310580645a10f558004d40d48a0030810309010304401c800700c94604185050005a44d0012151400043d00302035040b05061300c282801030840340064500300c5264240404030014014044070011102c0c880041500072 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 539145026 1250 539143776 539143783
    0x12080a02121302040b0a0303050a0e04020c0d021c17040f1a011806171c090e0a0501090b01051903020a05130b1306052106010e2e02070602070b0702010302040305 71
    0x12010195001c21507696032040c002601c0c5c4410071184201c1e01440e041000c03039040400c4514010452401c580011680f80020b0000c0c069241c00402c58070039407240500c80c80d000a1107440c10441e500c2c4841c04105907034021259003003d0040d4803c507600c003002003000a110740003424171640c424003a00340c1c40d80701b40c03828003140102680300031070310340041901d4460425503104031005840c00c00303110300700301e03580ca82110f942d00280340701c1d6554540150a8255100d114003003220240c51482402c405c0380c00c200c0c550201502080c06100070301840d01841e8480ca41c00748084500100400d1152808005424000d0f0001c0d0489050f160070700c5802c000c0d215085110840310009003501019158031110741e00040e48071001650400000d000d0100000c00c60020f1304400e00000003668142d0032004d5580200480391480920212500906101c0c1c0d15058004c103900010f24900382d030754805000144405e0200d03580c20240c42581c2c09604100340a1184881120080204a0042c1030142c500740d502e40d80c4a26 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 539146276 1250 539145026 539145031
    0x71b060608010515101128050307030201020703080a091110090f031a07050301030b0a02161202030316081605090d1202060703050709350115050f030a12080a0212 71
    0x40c4c80030400c0061041d803503c0c1d007600b244e4258070701d04005000c541c0984503a032400100301c5880c050044003c0c851400c10340c095024121540031094070303101c405a180c040d010750000c3c2022030124800301c0009592640d540315010740c160700a804490f0046001c0180030054184103e04000c00c0032460000c078880209020501c0103620ad49400e40a140c09034100383e009560280c124010007004100402c0070428900f80150011407080006a4600c04003180207040960a500100120402e5944a0011ba00403001d503106401ca80011003c0c10030307209045486010454002c0b160003d0307500040130042c49440504003c0f4170142003230142151a4442d9051034045500c08401644900d0400180907414051550802400d041811782541041d826800043d4040c040c0d181c1e010480e540329059600d4050500c0c13007140710300d00030002c1009250207103d13103052a01600340549441041c038a11400c0000c1c010040315080108000e5105600c407046480e10000307041030003030704d400b40590f24440f0345c400c02070b50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 539147526 1250 539146276 539146291
    0x605060f0f13050a0b04030c140906120c030712060506041119091e18021606050703021b070503010c0e031b12060106170a0c0903290f010303080906071b0606080105 72
    0x241c45031f145150640d441c1d0442d400403c1c1c4040c2480408071180c490029042e004031048030303035810465170602c80c9840d203500d04150302c5c0c1c94403500c94002004402e10300000d1196000c0d442c1401269a0706080c00103a514103511b01e40f4182c410046004e03110305005a1091105440c50f2814a0341c0e0740c0c04208541c50103800c011a800315042404114808071618181200c45908200754281816000300420b04d074075840014040c2ca440d01c0001d58100d20940c11502481d01c2c2e80008035000a21440d40d0b5511940350080500962a0080d00c102030340c0143c004213042c400c001e0080c650441c102c11711104a0107080c0541e900071500c1a12400055010301c2020b0280c0000d8be80c0c0d482001100000b03c00e002c001401c00f4041034a0202a4030005501210b85400c0d07079001000d52000d040c030800c110708600044604040d8143d00c1909200141c01809041030482e4022741d95949d0360b4503034031207242d103991040d1070a8010445445090049074082d59201c05258003c6200060b40b07070340d50101030f081d00c00445041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 539148776 1250 539147526 539147549
    0x1e02180612030f190212041a0904021c0609021218070302130e060f0f0708060a120b0901050106031512030e0a030b0610050c0d1803050102040b0d0605060f0f13050a 72
    0x10020962100320403d8504d440100b06a440b1980a10070307078459801580540900854001022400c49084405440c0e0183c030441d1703240c10940040b100c07010001403030750340740307003880e5000426001d01e00a90b0b01d1705401221017110358403814040364100005c01200451401466000005aa90108042c1c0005155507000c640d00c42e10232509414100e0062505d191142e020043c00700c00c26550b20160362103281402e007941070f91603000000300c606005a0004d5515080044003c0030810031000d071500440c48540288420b03600c50074140c003518200c2c020ba4045014102e420032803c01e907000d4220109010341400715821030f143c8040750080509400680d02c80c2500710a10070542805425040108003600d8024108288004110744850807180004100711403080030411214074411000b00860b4883c00855481390380740c011418640054415441c480d1610000103803030f0600a0850300081881450349260081070f400201c140d03005200012034515041002107105c0e103d82480354042d20005010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 539150026 1250 539148776 539148787
    0x4141305190501060203040614070c08070b0c0105220308070c0204060b030f06030d0806040c0516110108010b04080303060603041b03050c10020c03070b161505041e02180612030f 78
    0x1c0c030342039607810f0303010b00c0440d402004208007441c1d21881140c00c0d8010b80340c440e0342da0704150804410400340343e0401483d40c05801c10026100048600609441c02e90900906c480c0c0e507071030088503a00c80c6000002074113082e102803120002c0c4c030600200b603212a031828400d403519089e1f0081000c5030b001d030700700032458a800018402000b811010146c1c1c40502140140507203851103800800c0348201400060260b515420042c07103d41c0a481600e0b200038050b08414100c03c02800c0102c055506d20160702d012514100c004125101480216025581180020f602c3c41d00e4007401d01125500041c800e0b40c0e003050a0010f110a82c854441c0301004600480080000720101803c0050324811484203005662281d07042020340d0b200410071008075a00d144105441b841024100d000c460002000141480c2500004502203040383d03016500a41c0900340e482140007100d5014102d0f9900c1c2d01c4040e41c000e04d01c0c501a5502c0e014080d240d0760180b00a840c8090880d04198040d01d150000c0703c1c14840c1480c0480c0e07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 539151276 1250 539150026 539150071
    0x5041506080307020d06020307090305030c06040b01122105071406040507052d030f0f16060302070b0f0601050f0d02071a060904110303040302100c0c080d020304141305 74
    0x1000040e00d00c01c1e01540c6028000c3c4d0004d5100d00307050f44d0040819401000180c00c403409030008400840c1c018040d6030761240754203011500d95000b154100d515445540002c240e005441031804030b441d501c004540c009180b4001800001d01d0068940020460104458000107094800e511145500c0f180244100c2c2400e1910508008450f00654000d414401003000b403040302e054400344200c50101c105050544440100b41007103070301c015180c03c600c540a0001c030051000940400800707805a030000c0040d4484508406030310980c88042c00806464000c50b180c0210b9400260704000141801307417a04c01060801591031308403084400d031055020826806104008039030f2050000d03540300b005040c0c03400c000015139840000c1c0000c0c040103218103801440392802c00403680690740007050b0003104a8505001800a1000d9104403101b00c04c40c03c000910400c0041c41790b1180e20203030065803d2508209035084120031a248181c0c0c0a0110070403903100400900c00c060003a41d1000d122064405241c9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 539152526 1250 539151276 539151281
    0x2100c0c080102090a060e04060e0408030f06100e1c050d17011409041203090f06060602010c080402011b02010311161a090304030803041505072105040b1f09050415 72
    0x1802a070590f4010000c10302581e40d8200f92100750f400604102115880c407001040003000d40340c02280802e140c8000780010710402d10040c0d4418103401841c1c9080d565400c041c031024250340c0f2084c1010407101e0b1020822071030200d00550307405c0c0d400384005228800b00d84600d85401480c101c00f101150610400031002078400c904107024041c24400c815101c002c1001080b207000008102034401031000c0c07441d5071043e100360030040d40183c102c0d400c0a40c0365568180000103006500c40e0030301541c6800d440026041c06803040c0c44c425a016100d1281600203005282c214985580080341010b036182a01c036140c00c1e21030701418101050610140c01301d003441c5014032402c006500014110240e140400400042c000111400e0720707407003400c0075225195031808035010340c1d151860380080f0b403c0a04000800c0c0d0f1006c44840c42e030211003001c5017080005001030048071026203001d08884041c60001d070045401801ca1000341500080c5445211307a2421544200c44090350111007040703e641640941d0390090 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 539153776 1250 539152526 539152529
    0x405030c1f1d100506190609050109090516030e0c06030f090c2b1e0f11040204141009051f12020406020a0204091b0303030e0105091914010902100c0c 66
    0x1c0c0c4509800c0c400c075040d00f980c440d40806001e1070152030302e00080030307034903584404102c0d52448000c204540342c5a11014080d00d040303000351400107407403803c006070414840c01918050b071640f007000301c010500d590044026024140444a961142162182c490340b9044015172040c06c101d9550819410181700c61418503603000d80f21445000c401740c5058004070b0480280035820110342103030380d01070103a01c2c000401c104000c03241030400c0b8450710b4000c1407021590307070b000e500340c80b9440d034801600f00c500030403040f0301441c001c0010805d945a400321f07050802100954030150301d800c12906503991500000d9040343c03004000d8401ca00d1035a4489415504042d1000c003900392140158109824400000d545989901c0003074071490303d80181e03005024901c000c0c00c004e250f5003806205000e44a04010300685043c1e002400a0340c80c0200103080090040750081d1542c1c84158844845c00d50b5444403a880030b03260001120380e540e140c04900050340c54080414081c130303640e200e401c080302003400d1401864426 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 539155026 1250 539153776 539153801
    0x1315050d081b061012050a06060b030f071110020f1213030e06030103020f0112110a03091505070c140705090a1a0307050603011701020f0c0703120f080406050405030c1f 74
    0x1500784142002982c141c00c0035285c544411030904940c500301146000782251000c0c1506103420008100d112101004500c1103500001d59043c0d42c42d01001242d003075245a140300310f030350025500c2c4403000c403558004107c62040c2c052141d090009824041a0a6406540c0c0c00030b03000001a056080642100b11400708040440d161400c2d585140c011400300e02010041c54100324144461403111b0000358440c14820b525202c800d0b40301c2c42c0d04900600100384418040c0d82044940038030b01050001e13406824402c0c40740e561402d010000d29a541610000700005041c0103000e81c44001c5020748444022b10310804882102281c507010340816211604000d408260103500704000502070f50715000c04681c111458a0440f460070702907081900d0081c018070070340c5144c6100005d030000a03030100203889025a40141030f21200b21682502c25070300d0ba012404c4d45800303e401c0c6000200415040e9021035030103405601544d00e04004c0100c80750500c80c00d00c514a2044900e9090881d1006040c480d00112a08 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 539156276 1250 539155026 539155033
    0xc0610050303041202130603031112070809060310080a050312010509101406040323071e03080715020a12110c060c0d061502061501030b1315050d081b 66
    0xc0001003910b91107580210606016102c1048046489801c0d42d620100840001000500e03124075006003182c0c0103a180e841c6078800e0203113620140d40b80c80101e4219552060300c03146805070440034041c071b40e0001040901e0780b0b0040340000a01071341c01c0c001d15018610a0001c0c656400c0d2803c0e04500a071410b800c0640500410010400301c80c5150f054601594003056032001c3c2409520000380c0c0c14030458000410780005a0018134041141e2082c00c6148204c080680d034820707484400006210a060602c500b40903146402080800c1903500180100c41c080e10310105210904881d2000b42d034460f03425440040c00c0003c1e04c3c0190740e82c511135843c6000c0180c13001440c1141500c103891303950030040d0014800100020350080213509644c04440140b00c4100304544610400c407019440e00b00464880b10021070401d420718280d8440d00c6004802c071801480710040340000c1c1000e50040480303124540240b6001c48011070190395003200504005d109003e9103540b16261305103d400d410b00c20200c5000d661 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 539157526 1250 539156276 539156279
    0xf0603011e150f23040f080607020d140904110a120b0f060703030f1506080f1f03240203090304170610150302041d010302010e031203011401090503010c050c0610 71
    0x181c0c004044440c00d030881c40c0504501904c4042d40d554902c4600c40c00c00e0f072500000380003030030380a2603000d0b07011035401405807101955510300c1aa00ca081e6404207034005050450351800e541141c5024201851014000043c40341c1c40c1c1d81e590f4803941c80640c404001c42d206e50928000c4800c2070103040260031003a12481d40d80070958000c221b00b401555801000e0607100c41d20143c070b09200707034000c1c0707104540500480c09069035150003901d84030054450178150030300d040022f2180c0520300080042178010b03010003140d0f5880c4d911180305039040c00c000407000c1c0054483e81c10002c00b5070f0019600440044014540d00d500e8040ca510400716000c5401a4540088003001600328003031035100308462030410392098607d40c00350210000c0c0f055400140382c090b0400302802032100010542030589100380c0b1000c0303803005403004040d501c080a00c40c6460402e0b00b0001070000000c102640c0340b680c1c1c01030504d4450603444800280c01d403018141580300055003c201c0e020350200400c000c54020216120303148106 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 539158776 1250 539157526 539157569
    0x60603121c02070213091502032710061e08011b110a0503040f1d15040e0a08040905040b0709080c0d171201030b060105160f020f0603011e 61
    0x600a10110010512000410301e84007585501201c0c00141d000308158000c48500b98500c0080401c002c06079030020b0b030b00290140c40c078a01c0c0b08580c00703012402076040a2003410180807a43c1d0b041010001c10b40d01605901c50161031541c021103019042c640c4e240c000c18214044501e110110782c1d4810351050781803d4219060310804009a2045c0505181c03800c20403407414501450403041420080c145d200000303001650803018414202075038206000345401032911440c60440076400d031041d03904c9200900e000b1180c2d1070580c0c050710030803e40380e0580720340220035222010290800e0744100c092503100c0e410081004400b0f041c15500c04050b080a04186042c0540b41d81d44180008808e806142e000000c0700a04c1443c101c0082010401850301d42c0c0c80c0410300754519110800e1104a400301060804100a5800303401503540c43c04100702c070080c0c80003d035201c40c48000c0000b08107a170802c070b242d428802503490395070081d406080041d079154442405405100030000d41c07588805448150700c5c90011a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 539160026 1250 539158776 539158813
    0x1206030c1804171308100b011106060f03100f020d15060c06111207050909160c0602070204060b1b0d0e011d0111010c020c090f2215050a0905060603 65
    0x1e90800e030001c042881e00c1c654080d213449003440701c0d00e549032801030001c1d81c074038005100070510308509810301c00c042d600c50056801c1110f5240c0c0f114140c011000156003818004408038400b1001021100c100d040003c01500b11038182500104e00354000402040b0000c047c001d0341c61032041d45940d6400b0510b40400200f02a00b00100101600d84070660441040e0010068851000c561901c4614a04120744003400340d5000300c01e00350250324807a0000303040800f11413804800e0790740c1c0d8654a1700f4044540ea18402507201100407a030050303448030081020094100034203a400c0480800c45002000725500d1441c3c03c080b032241e0800c101c3e5003113102401e80da10019036025100c040c03d149206440752700050b11441e05455483e42075620b8860b0780042c6c154001058084500c0c1a10610456262010141c1d1040300403108040c030813841c41400d0b084a500041c042c00781c41d01594600910000758104030007550070569540d03580c035490340306a500340a4148250360700400101d0007001950300384c0b14030110307 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 539161276 1250 539160026 539160031
    0xe0103051b160602040e07090810110d0b010203070c030303290607030f0c1212200403030503102301030624080615120106081f030204051b1206030c18 66
    0x48110541d188001007003e00d4050380c000d01300307055a0401c03074600000004c0c010072242c4507809403442802d03c0381d0700540c02c40c46040a5921000c4a43d441d2440e01100c000c00ba1010b01d00d02411031000f08005004100c8020501002e50b10966011814803a400f5000d103c0c40c2a02041a18245612a01303003441d81d41c40040b034181950608010906400c214401d03944141e22080140c00010641c0d0022240d81d031102c03050305441001c80003041105039030741002203c0c1414014501e0041010041480480d002c0d10145500134008290b40c280d05458180304070079040d1042c9900c40c1903554105200180d0303018001c81003e802030460951226000e200140f90202c3e2140300b6900b800100400703d82c413906c071503c0c44c2040080024040380d80e1140544032080703c020034400d600000780c102010429803500e4200c0c0b401da81841c0d205140c1c015003540c00f04402410040c0c4640c622000082017140c030015043c5c0500402914540700790b9403460a1f009060a000d2440f240910030f00d1a0046a28080a00b642e580d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 539162526 1250 539161276 539161297
    0x718060806132a0207120302100213080a06020a090b0306010816030e030703020a060b010c080706020d2901030c03020c0709020d09020613060905030109080306040504061b0e0103051b 80
    0x2000e2114841c00000100043c900108040440c0c01000303000e1041d0880b296103982d056400c90301d041e551840c00010b1107800c2c03100240140c200002e2030000100715006004503a011600f4010015030790071805150800d80f40c01114559008a8440b62890b00064414010645c1c000003516610f00840000c00a21009106000d43c0b0541e956107518a8800c3c1d11410b42840c440003102d039600c2031801d02030340c3c429400c441124298105048010035520070b4100003680f80d400020070341403400a03078564004c0c1d000141019070003a03541c2540b01c00410860760840c1c0301c4828207096080c844406000609440c503240f003890615004020b000f4128800240001c21103018100c0142c0355040714122070054810b03510060351000f00071841c007070328801c0400340004940c000d4031034450b800d5075441810b00769000c021010304808400d000003456410a60400b56006105000003d10005d14070b42c01d80715201e070502c5802c0099070040e00080b05507014480d1a400007503d080040c20340541c0d03460b601c22441107031106e2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 539163776 1250 539162526 539162539
    0x6120807051204090f2f1605070b030702060a060b180f06031f0909110f0d060504030801060216050901090b0d060f090b070507170a051b0102030718060806 68
    0x10014400d040c05011800b504410745150340d29503410858000d843c1524081301528a0310010741040c280280001c014220107400c0b9140d1604041c0744030980d03800844001c1600381d0980e81c002e002510500c0120090287d00102689a040c0072000918044000b060000b070203203407420902001c81c0c0c410070f6602c0586001e2260b20302618420114001401c16600660401004018800c41c0f8a5616a00e10304201c107034110001c80d55582c5400d001d89040303202c090502031007000d4601d05d90034401d00554642d040980856440b001968a903002c80c0c4044505400141c3c1240040c046654103100c0640b0444404c0a134194250520000445182040c030510080f582da815222549031217000348614002c0c0c010200b00100005110504050207080e542294404520b0740000d42c00d038007503401c0e03d818541007030360040450300304919044150b000824850030301009011420340c03030407100c400181000e42000090f880782003448000c1c240300b040024000000c83c540c5014480150b00526040e48514102c408 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 539165026 1250 539163776 539163787
    0x3021908070c0b070212070609020427020f040b090702011d160e06030c061201030201020c120303070806030f030a09031101080712020901090909030203070c050a1809020f030a030f03050a061208 85
    0x5d078a08040f000e4015039159021800394184401644003041c450f009440070312035922041112200f00003501032000708002c50380c40d01000b41c1007254000689100140c40001c45490440c00900604c208072009001030b9120110803d40820201100801c03505510041c000c00b00440b9040e07d00311580d01803400ba0b0051100042e08079034040082d510f007184003030161a6038500c280544040450309001c1a030151080d695080420705007800b42c005070030340034806141580c541d040c040700e001c00702a050a51502c00c200391403001c5603040c402090141015112081e00c0c0b41380d80307031402c41140105c01090601c150202040382443d00032101c80e0f19a00387d42801640c600c16100140c54481c85034000c00c401500d8040395104041d0008000c0106600400c24040401da0381e42c01c01200c0c0010b030041c03e08002039240d04a0591105410890038940b0007018000580c101c1c4010910b010082c00c0294000303801e81c004012940e8251050344c0e00031681120902c11181400d003242c44040d8546401801410300040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 539166276 1250 539165026 539165041
    0x240b03030a0503100e0403090602160302011e0e04020d200f0301031e17030a0e0109020a05151e030106120507021c051b03190305010f030206090a0305060703021908070c0b 75
    0x40540150851440801c17860a1a003801845480035003c1c0001512032030522280c646100030180b81102c1c0c0c1692a182015006654122076080c00c0000d2021f0214041c90a8100d54a074005003504092076840003074641000c50500d02c1d0240c0d420741c5000050340c1040645609000282101d065a41000004250b407404000102c40070741c3c0f01c00058a004442d0f40000c06141e050300003503009a550031010b0241c0860003080d58204c1e031030040d000391702044d40c20080220b4141340034007451048140103035134140001381b8400f0a0581c02d0142d0400c00400c00001413100a0300045581443c0802c480100280d1a110030041d46d1030200c040126006102030541c468000e00c52012200071504802a400d20040c2c00342500d47c1e80d811441c03007052900c442d21000c07540b0300c0c481e00c6000d0480d400c00c03001d100450300c1c54003841555440600703040d400400700500400441c0c0100b03c1c15024290780d40e80140e5860b654240e103c1d000400c60120000c0041600c01e1014643c0d1000804070441e410190319229511030f000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 539167526 1250 539166276 539166301
    0x1a07020d050604030221130315060b0d020405010201140c0708030c0715051801110d0509030f0c03030a1503050d0e0105210402031b010c030f02010f0207240b03030a0503 74
    0x10000c0c41d62180404110400d9404600c00c9410760003045450041008040041040d024441c1c0c8401290817507501000030519660001c0c600040030200020659100d01c00342e0070035403142100c0b110341d940006003040341c0e583c24410000802260042c4801c0c40c1421a4030340c0252045110140c201080030010480d603001d050111000c0a07449021003844101d500c607031001900b411202d4455540030310124076031050042c041e4050003003200c1c0f00e0a180100c8124070600070423016005103014802840034120f20343c0160020595500c08000468032464142c8480d01503a41042c00301c034002da1140b00800004000180750b08680825007070566400b004180126100e029660010000050a16035510300300a45c0101c580141c0c0268180d552150100d000d2841c143c601ca410140090700c020340c11004a4891684040414000d00c000302e6100104075a10041e6001100d05580da10780d3303840a810322003100102210b824412080a101e030038024000691280076143c01c030806d00c00000001040010b080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 539168776 1250 539167526 539167549
    0x20102040b03130302010b01020f150c0408030f03090708010b09010302061b061006020c060306030d0c030c3003050f1b2a0d02060603070302010507140718060605041a0702 75
    0x107521240d160f180c00f198140000e0b070101c1054001d9403034580b4000e055440070900808080300da070010f00c241ca41003141d01d44040b200410340c8481400078040841c0c0442c09100610b07550340c00c504815203c1c02c100d140d05042030007651100da203d80c07418803824540c3d182c029916044940466071107483d400040342c10140c42c041900210b686015080030080301150100800040c1c90a40d42110081d810000c01d00210740300c00d072059980340c1d11000340304000c00c0c42001c11011140c4a0b180c031022080c06655180c040000c0c40703041c079051003034140c031040765070100b034024803100d44540c5428032650034010981042482c02070181c0700580c402c0c40900707002e424443d084130b9445007038503c0c05038403841c07070003c4403103540131513501d5030a90088010110b1064400111980500002009005030618690055500b03a110100499200300c1643c2520b141d00010300000c40100408128900b50020200c582070031148039030402802d00c10103100a1113160a6424204043c9030b806134460ba50714a107000154002c02030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 539170026 1250 539168776 539168789
    0x901021608040f0b0403020d0f170c01051b12060f0a0f140a0e04080d0203070c060c12110a0203032a030c040e010b0301030809010f0905060c01050f07030203060604090c02010204 78
    0x1200400401441c000100b0498034040b8801e45030315150381c1a41c101d48203911020f0740c010044a20b110102d2615440400c80d5803144100300c071400845890004141c208a001d6112079550708208019003240c5c18888040d15400a1118508103803041d0940d54280007501d114050a00d0311f400320b0041d1510182c4502804030f800c40c50040356651607110041c100c9408404c0e000781c9030004006118075401c284280110340c80300b603050901c5410b0038510029040248254200320a0390b90300004500284582e086141e01c0d651102c0d2101841c0900100740d07070960300b01004a04042000c4105a0b5000c01607903004030034000d00500182c6040b0240135900c00380400690703a90000814444840003c40c014000c803410885246210381e40c49100d1455808244800303050807404003c5955150703c95031075464408414141150641c0e1550f0111b217080d0003001600d000e580d503880a004185000c2100190720034030f1440c0540c510b25005001c0341e440c1c002c911071245442d8440b21050f0641e4000c0d01030f0b0300039220 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 539171276 1250 539170026 539170057
    0xb06191101110421020a030807030c0c03030302032e03020603040c03050708061f03031205130b011203020606090103030905010804080d020325020d09050f030328090e04020a0e090102 80
    0x4000c610b481243d071240c031902118004c41c0d194141410801c140c40c0c10300d16001401c2007421451911000a00d80c00803104404106407010180d0008440402610146001355001030320391800301481c524000c2104540c14a0398a01640d54440c25190070700003041c3e0f641038801548070740306c0e4500554032088640008041740079004010401e40c1002500a1060f4102c3c1c21802c81440314541f004802d403200d001c0600010441040c12002a0060300555000710b80c06190088981881e00c40c001102000c2c0c00840075801c038003005205042d4100701c031540104045a52110952540e40c000d0a906124880c05040c00100c40c0058280040f00c0c050741c40010309070740300703560740e1a02d804420540b06a405129000c4406c140c51064810301c002806c000200c41c50b00d890328114200b03010840c0c0704c85108011549440700700200800c8a403201170004089d01e0820060600164440c4080c200207665003040c00d074442640d08000140c4c1d01d20400200315441000e0007075080d02c0c1d80d120f80d0301906c207801007070380c6510 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 539172526 1250 539171276 539171291
    0x140c160203031315120e0705060a020f060708070e060309060a0e1911040501290d060810140105010206130305090a050d0f05010f0b03120307021603060c0e040b06191101 74
    0x204c2e28000d50749441035039a15074144101d101d0390b08040741e440c4450140b0700e52207050203205038140940100f02c0300304e05004454440000f030701d00d94900007003111500000b030040c0c41840030442d00944000051841101c40034194504044441c4e9104c100900d460540c54803200c0d0700c10200c105002c2050b1605803942c5140d0610040d007010030f0044041302800d4000d07407900000180700096030364080311300001c00030a01c00c0c1101a14120360ba6400000071980310700d035545c0c000106403408210074815400400b10101e44000c010301504206001640801c1c1550403241c02c11004981e06003150368243c0d4107013003998450140001160040b0020b801c410f800404100d5200b0900a040b41c080ca880c3e4402d4009122300546035541c1c000f620601c041c0ca0303415600c02000e5400740000d0b0310107598480010720460b21030160442e5181b030031021650080e45c20769500d610310310b00700d6400351002110060564043c081000b03c0b0010400501c500d07440e02d0311215808481c0814207100303010407200300c03201c00c000307101e0030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 539173776 1250 539172526 539172539
    0x708010207020f040506100804060f1509062103081306050403020c03071a07290103080c010c09051e0d02131d0c06031f0f18140c1602030313 62
    0x1d500c0440c0030ba2250980d0501840c8038903290040602c03a0701d015101e00c500c0f10f9100030559042c10701500c12601284c5a040380300c940f031824422043c880c3c20402844000a02d861844c01c112000c60300007803e43d40c0047c07048031503c000341d440c101d03005a0600d0401410f030340e600a00114041000c000a0410f410001400103156001030400200b0200728140c0e0404c075a1212a4082c802c0d08850700c802101c41407014101041068000e04030b032000c01d40d0001c0e0000941030385012105000d800464100d0b001268a0364018024807030400d2001103030030400049400c000000d2030304030f44040c00303550141244003803400c0e5031244030f51020b0f1254003805581c3c517011001e500c2c0010f0001444110108040450014000700b4009030300041400d000e0f00700741c41d503120804048170141d00d03000c03040408844072000280f122100e8002000625040450303002552028141c0020f07210b034101860f080c0c056040c140404100390350100c42ca21440d0044c403200003620751001c642140581101040400690300000480 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 539175026 1250 539173776 539173781
    0xc06010311041802010207120309120f1407080c040f020c0a06050a14060d0303091b06050301060f0507120e030c090c070b0c0f0a030908120921070305031611070801 72
    0x710404441c14080201c500c112010011003080004e401680480c60400840c17a00d50140c00500d8020701d00101c6040d1102008640201116411a503a441d105000c0081c484c84940300c00c4020700034000f9010540c948159955100b01c0e0711803042c81540d88002c1e207002850264102d8407155408016251413801504002009000480c1c006604505205104070710521344102c5c2885000001c2c00d441c0705007041d403004c0340201015001103441411480480d544a08050b00110040c0030a40c4c50079929810060010035083c4a030941001780700041c4584400140300c000300d5181301e0414540802c08070100000240780a952080c4250080340000521911200c91030041450b140916002c88031600d800c07100003540c1c130800c2684010b0200500c10008101d200340c2194159501503550603041c8205000550641d82081d1181141a03108458428100206410b1112a07501e640543c0d41005000c1e01d0190483c8001003080e0740b455840030a000b400c038054010703140301b030321a901124020f54840342e88a00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 539176276 1250 539175026 539175053
    0xd0e0a0233284103100f0806060f0f22060b04090e06070203040e041e0204020a03050603060108030306060a05030c132c0112060e0f06090106051804170d020c060103 72
    0x5141c52440311403c9540f070302e041804441e140241100601c80e40840342d82980c2c002500201c03020342036000004060b540213039840c025000b03a201426a41c20a1010032400c503a0f1013a00328000c9205103502041640c070104d50000c030040310352107000b1004151214200030880794004030400f4501007004181c21a09034052120006500101d8446880e610003c1c0d07070f280a28441c4c6070741707a10400d000500052084103081d20b2040310300401c00420f452039000505036009000000d000940d103004103c1030340340800039180140717000c0014514509210f400300300c0c54480e0a141509018001002c98415488041120000d0f6017071009a1502d5440d81c018840000c104ca4125200400580b0b40c842500450342c43c150484400400d00f95051034030381d0760200907190241e2141e089002e07100714180552024800544502400c0d400001c4090402c400c02c08440030f82842c4030340502d882c0003080b00080520804a0381c600c805861144c66403084081d900203071082020101c00e03400740200000401000620f080c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 539177526 1250 539176276 539176307
    0x180310050702030d050901360f1a0609040503090105220e041a070c030305060418060506010f020604081204050a050703121b02010909110d0e0a023328 66
    0x280e443d1030803d90300f0b039400102c0e0307030329500f004807411644080d04509151102c0b0121500549079401512030300706448142d09d090b151046030016100743c0134400720320700b540b0030800c4410004604060702d65564034003880720319a052000000e0448c40450460010711464000450360703105564035900e216114181c180e40480d00c0e100c84002c1c490355480100340242c4030360000c0d6035370401400707651400c80240101622440d040799582440d601100b400c007000d880802d029000100c0c16003449000103110704001c40b1940110740080c3c040c000011343c501d084890300c0d40e4201c05114280c407907052290a011614000810360310039810008100f2844200c040034022050b11180c8290200941d80400c40c548403d000380003074034062050142581650000200119000a041c1400200c3c0c114208881103c81600041d0b0302c1480c0403800c40c6032071000d002749410300a008a0407800545c42070540250a40030124400001107003085072201c0542c25507200380c680c1d90200201d16202d0701c001c1e10102d610141c95 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 539178776 1250 539177526 539177531
    0x30815030604140d1112071a040614070201060f0e0a11030f04030f210e0c0d060207050c0414190b100810050a06050406030e07050a0b04170c06180310050702030d 71
    0x404807a8010745c0445840d44209010f004060640845280d49511110f002c2307440407415805004101c1e446001c10380700b9031060800144442501c5148020380c3d000609030801c5a0401d2018404c202000d180102220101d80f1012016200d8000000241c8007a12f000f01c8140d00200802c90b038030480491980c090341c0030391254120320401c89021190440c008055544e040700a920100242505030700c1030160300c11241c00c4d51302c0c04072010001110840220019580c10b500442e0100500c4010710031014603201c100c03810013094001d80307150650760030000d10f2691151a1801d0038400d800040c4c00072900c4110007808410141400d50004e0036460042c3c41c12020030b050542c01041c0b03403c1c00202c0c44207461068951505041c90068114054a80010b503140a4010f900c0d002450b5140c444401010701440c00c6015221070415100025a00e00b410350307408140c0c0024140c44076911000200c90b0711100021003032403450042c50219107882000c0c0e841c01d4105107007d007080301c2e4650102c060305020b80811000d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 539180026 1250 539178776 539178793
    0x130902030f180a02010806060304050c03120d06090506031f021204080406030e0105060618010509060c25060c150e060702030903010b040e0601050d210306170d02070303081503060414 80
    0x10790750315000f04500a0119001d1030110b0f4031441c202c0080d560182c851b40465103c4082d60000c00e04000d50300c24000302c0d00310082825504030b042402080702409410400700818942800000c0c4ea851082d010040d065540040d82e03c06070300c0300d80441e0f182a499013010186410140380026040d8442c0c40307600700103440c0541d20150b80e0418003842d4003450009120a0610031034030600072a1140210001c2d0503c0030030080202a6102c40003d4400c2c90b0610303014003400002145030641c801d6100615008059401d0003d0004a400c503c000c00722a400400d001a01d103e9003045034010f2076440c080b50b0052056004004031507034000010025091705400a0254450f40d0701880256090804c070b0b0b00b1180c00010050045090080e05621114000c00f42c8421108240c0c200e61443c07824080c0600010352a540c0a00501b2403000ca100548004000144101150400b0081d01e64450303000090400400e007002c02c08800854445803140480101a540e06040a1819010b800c1d04501c6903109406010390 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 539181276 1250 539180026 539180071
    0x51314090604051506030a230a0501082109040f02161e0b06061612031b091d0a0f06060206180303011a07050a120e04050c0406050d02130902030f 64
    0x1920340101406000c1d4004201300c4c40c2003003030940005003c2c603a0700f42d540c4c908030003010820089034104807034003804a0050502202c0c070029511305030400c03015031340301502000220b140c158415521204001f2110303140c180900018020341042540310500d2030010400c20154090b1a1844002d184902095081d40c0e042e500070290155801d00043c1c080010170f0001641070030503038001c0004658080081e01160310701c4e82c410851011a004050000e030752482d101200e4035004440060702c240d03504000b54503518140e8081090705109140b0b456100f4035401254580b0b04607008800c80c09124002804000c0e1909002951000121020b060030122080c0d104500e88001c8100c03070507100c04000b00101e1281030300740d038055540408407c45807441140700110114100891a01c1089000d54405180e0a0100100300c00d40d00060301c5015030701e80401080080940000031580004c1441001581715140d49814040b258850350158403a07034000010043c54010b032070b0481d032140410030800c40b55082c5122 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 539182526 1250 539181276 539181281
    0x30f031b0c032319080a18020d0507030206030114010806040c09050108070e03060a02070605090601050121020f0409020403031b0213110c0f0102030a0e2b051314090604 74
    0xc51490104101c8030359400842d10034525114000c14803070000d08851984000e260141c0e00034014000314800500425000a52007021103420a659030310500c216407038040440c1e40c120000340000e00c1b802c20322054008008003031000100440d00148501d4580d0384d180f00c680c903503507003d10815001621400c001a41c525040c800d01c925544a07594030503a060800006540000f009440c5070f0600c00d20111104a5030303000c0002c0c5105400341180580c850146191207c141c41c00074240d400c3c0d6411510043c403059900c040100c51002034805603a0b0300d008220b00d218002c1c070611042c47d03d1074100040204119445030010000c45e8460768a420302020f00d000b00c2074645041c101c00951110820510b03000c041440e400130b040b203c00b007040c10b629007018409403e140a90b028842c0015035004010810f2100b003c1c8141c0c42d903c84c00e50060030780e08140c0c031422051034010b02d00404469001014455405105030700f070380c80300000251103211290b141c00c4c0792500741084580c928829604840060081d003051b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 539183776 1250 539182526 539182571
    0xc0509030f0303010f090510150e0a0902090330030f01030201140a0203190e130501062c0411040806010e01090f020c19080f0d05160e030d0507020d0f030f03 69
    0x41685d00119424a408100500700180c0b040750307070800c1c035113000c1112098000610f01e0585c00380c41e504c851100c5101031108001955000d88a806d02c1488082035580b004100341010081c0e460b048039207180c135000310001000e0101820a00d808011040010a4607090754090503a8001d8070303003008c0c028440300e46070001d00c100282200160030610010b8241104001400b03651030aa0170f080030800241c8020130600014015031030b14a0703840313200412078603404c440e200c650000b40500705034089203001408001140c0e283d5185001d5035852241e40c420742d40035402d40d400341403907106646055a40f140d2510f80841d0a0007985c00c0c252030481010b648a00620845903000001d402902d4001d80d4101000c00d00507000d8415111b4400c02c05c02002e132102440d005002407417104000083d281000c1941440d401d007000b441d8800d0003081544000300c0d0340d00203901c68070300c0803030700d08190740d12024400b06040180600000304070103200c452410425400107000ca5171500c113a9000c20129450300315214884421 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 539185026 1250 539183776 539183789
    0x506070f03081e0411010f0207120f06061509060f0507020f120a0615030318080303012102101101050619120602040f060215011509050609130c0509030f030301 70
    0x1100c24650000e070080d49803e6000c014036881e10444020191450341c000802c841c2120b5600c00100e060b00590f8000d0f02000c41016a4030040c1045030604400f40100c181182e800b03882d83d480c1030421401c10595070043c10107000d0711070005019100740c10f0050405a1513006d00c2c0c000c43c2040400d81c124610036000e9070f184a40013004c4030499a040401d100c0d008901426803011806011000b001040080c02040200c041d07040401c054a031845c2030040203251100c3d0400514227411104000d155000010b030b9064452110070b4602c3c51004641c1e1000803449584003d400c62003500580c0b461582145501f09521100002480965074880c200300240c20b41c40c00c0c4265075580e45400f071280310300102d1102c2c4070310310548005142070b031520711201c11410740744c0c0001c0c01641f00030700d6407244012080d40540185580c075200280d58400750005440b6540d54003401d0300580020036460100da4490403205040c0c00840000c00101007403010050542d800b40d00018040c1c400c0c50b1507101c0d40c4400004480c1228030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 539186276 1250 539185026 539185043
    0xc041104030b1e060409060207062a080108030a0e03031303050106050f03030901020d0315051f090803031b0a0e090f010e0121060c17090601060810150c020102190b04020307050607 79
    0x102d020411005000302c035000c0c0d56155007800101c00241448c0304e0144804d900035885403a03469044494a025032024441c2f03000c004100d001000541800402c0e41c4460405040640d07907803072070b007003c6442c0d802490142035800308204000400e2040640c00042510000d940a0308400c852505040d40e0388174030050180164000b00006450510aa01042c1c80f00100319a41c60965503940001e00c00407203080e1020020021405003205450f0440d0084000300300041c00f0714103501d0f00810541070240700304403003039104070001064451648514009044840010126070150410110b0405554001d00840d54150180000070500803158074011a61a6540c51000c01034041503540300081c000a40415040c040c40c00741107600c03407403581141352040318504018a202e40c9050310040600314090404184041075110038070482600f801780341c5c03441404d0304000030301a0750340c40101d1400000c0c224054070045540803603020042c43c1104580181c1c001c504407008180c95000308070f81c030b10079604010308490 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 539187526 1250 539186276 539186281
    0xf030f0e0607080402150708210f040f03030f0501091e0203090304271407090603060b030f100515091f052a01050a0f0c08070f110c041104030b1e 64
    0x5100d400d00c07590045c40500580e1001c81c1c9100a801550010340044440b540041071750301d107240800740414240340c506151004241401178000c0601e40c0042d001030556180541034100741030080c4c001480200c05101c04100b5580d5072001e10004003000314412420800d0481403080049150085cae80c0070300a48406140380910700381e40d40312000e90390798096a28000038408102500c0707041c03003075809072002400580550320740100014140c0e201c6030800d905142c60714409010070424441900c0d801091401810440e44442d100100e42c0b07507455129036804001c28a08030a148411005854010425074000c044c000950184488103555a4420000200d090040300540c01c1900c0c40c40d00700c44d4544440283c109100342030710382500c00464140c1045602d81c0e40101d03d443c031b6071003035a0744038500340f0345602c0500741410028492104c82075000c08010000e0913500c040d101c01d01c070140e128100140104401400e00d070321032845800c0ba200c10703603540c004c62001900d103a084841d87c0300710b40360060521400e613 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 539188776 1250 539187526 539187541
    0xc0321070311030706050f010b120103020d03020307050a05030c3007021804080301051518040c02190c0305070f14060f2a0106060c050c27070f030f0e06 67
    0x5800c5032a05404100d03007450284020403050000703005450084501050926204001e401c00e020107030302008482d1000c11012110141c024070345819284d04464450300081075081c124a580610030300500140961000c081c1044400802000401801c0d4141e81e426044503903500500000c049072040ca60444000c060102803103800104401880241810b04211605003131120603682120300f00d500300400001400686441d00c01e48114481d01c142c034614200041c00840044004107510701d010719150408850324500a2040550f520030204c056040301400381403401034508941700a541c03e0003410004038600c1d80c5802e0520584800d04a4414002401010f00800e0342c0801c02401146600707004004800300360785902c1c22400c02007940194285003a000e141d00715402903104a00340070100048000042d00402e80c0d1603510f404030342e95040e0800002c0d104803401c1071190032420045200d000c101b4071541003484400106400d5a0420440c0f5005051800b215061007640b101d5030310050004814 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 539190026 1250 539188776 539188843
    0x201020a090e06060c030a030204050103060b030103020f04050a1e020d0e0105160f05120a1407030b2206030602070f060501050d0c0e060102010b030d020705040510260f070608090c03 80
    0xc48090003041c540303a45c6603c50750a41e0085154203002a4002408100540e8540950381c0903010310305000380fa5502d55030000700f0800c0b60000c0c0da0f0259840728001703003003680c0590081e0740c003849000340f86200d02031007a0954000e601c020180c158191405803064008001441101d100c0d0812401021401c00164001e4440d440c041222108214081002020070b24610031043d0040e450101e020503884c1c50304071000442c00e0f00500f0f210070145001081070090f5203a0302000c1140820aa120201c5007200a006c0050b01080e040602003a0000581004001d0050b01401401d0b01690341000303c1d90300d4800300704100900c060081c140c00f076443d0090011451501005800c524140000901d4442d4031004c241003103c007030401e1700075070411a8100141c2c1007501a4070f030301040050300400c40c141411150403caa07440f411070300d03070300914100716500502c0801c58204005004c0084446035640e404000b006d04400300c51001d83d0380500400010582000208455802000107140110408082e01d5592 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 539191276 1250 539190026 539190031
    0x507020c0d141c12050606180d05030a0c0210020102070812070309020a0906060e01020c1c03021501030503090a060c210212070605060910030f030e0f061611010201020a090e 76
    0x800e050b90710704184050340b080090f8600240c5000c410b54591200c00c10161005001034800c442e1281808200441c1c0d40d5080111510030300001c480c01c0c1c030183d40070080b031a04100690024014440001d8003880e070394022441255007071080341c1701d0800c1d54071510700303c1c280c2c0901c140c0140b4292050010080c0c0607031045040741d001030300e864000b032010515000036900852562011801d15600c04003880540e500c8001c0c250b51040a000030310746ca51040700400c0c1460864410480400a4041d44108140c828410380e10f611000701d00a00f00d43d41c69040080c3c907507100d4030100344289000480014903a0044294400ca590412420009a0707400750310400130f00c480562400460244c254240c0500506001400c11076020304400101031030110144042c070360024041c49050010740c002040054103140c66200c0042d0f051400c03000e060b24000100c0c003c442c030b98858a51000000c644c1401c101c00580f55000403e0050406a83d28041000164200d00c42c80322507000003403103660240800001c0c00112074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 539192526 1250 539191276 539191283
    0x20f0a0816050322290c0f030d020c15070e0d021c050c0306100513020c01090f0b06040b0a0503070501140f070b07090801060e0112031806030b04050a0507020c0d 71
    0x10103140c0c241d07540500b1940301c558040b04507030b10042a000c180048041450103400b40485d80310058000100c00c1880396a50071090802d2240062803848421052160300c4811026100320780c0ca402e4070603002c8000c1c0d00000030b0041203100b207500c10940300300ca0811860182c46141c0f140d5080c0c400c0442400210302200105a0708a103d059058418088102d104001a03026402500d0052443c104041c00c060024000310494005140f00b48840d075500020000c50000c0c1d8040180c1e03503401405071501500c48488007915024900781c0813001d104c800e0020520032079040f107040265200d0f0400b040066407440c050603425030720034401400a035002c0c00b070811424200c8203515040441e4014400a541c1c4001001c8942c4085e01090100c02600f1585260240c204c05c0c0c002d0189070304040000041d0001441486070a05104110406050041c3d11010460480003c5000d01c00c0c1c441740082c0280c0031001d082d074040c0e4644000503400b14000d104403401540150301034013550038107004004802c0c5d50506c0c1075 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 539193776 1250 539192526 539192557
    0xc0207050a0609030506090105040506061306051003022508310801020705072c060f0306090106080c0102030f0724060906090b0d0f03051308060108030712020f0a08 72
    0x100382552541819001003006075500b00b4900d08510300941402c5004c3d00e903d819038100018040000e0001c512643c0c00032082d104144c1465440440c040075010a500c00d41c6c00820810900503096070540047c40d802040310080c4031079103c9034900c0803e500c02007202900c140030a0140322440140100011080200036034144810140710402262642c41581708051b66980060948100300051100b08000d208c0c0402056084403100c6540100114240d1804440003590b0300049581d03403040c0d40d0180c99030020703048034060f28022841500800103405000a2031141501744815984000216140284903062450406002e0707035810301c2c40b5200600750044031428441d140e1146400c5d100e804003c04c1402c0010a44625109040080f20607480c1c80e140900d0b410082100402c1c00501d04841090f414a8020b548a0340c0300a44480840315411134010f84c0135000c00050019000806800e0150140e500c0c0c1c020f5070b01d0241c0585c0d480141044c1824240c004034052008211500003910750b180e000e0000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 539195026 1250 539193776 539193779
    0x70e041217040c18021b072103120203060d080d0e19021509040902030d120c090e15040b0a030b060f0406030c1a1201150806061c05130b01031a0c030c07060c0207 71
    0x24182c506d000301000e11407503220340420030500e20684c002c0781941010130044c1c1c2c00d07406251401840702d081e045400b01d0300e6400001291858071803a0b0030f005455086420f45484045284c008809488a00c810512900c26541d00e0305e15109290100024107074010220042c0154031881000c19400a00680368001e942c0e10b030759405038805220310003006540e90b5915000b4110400050308492241001900304866148180030350410381e00c0c00760b048000c55030b100c140c00e0803000c00100030b000c44500c4280c001c460810000100801d0f4020386d401585e0855102c4403041080082c0700031150359100140190728416810071191454040c030803260f5032495011864104103c00c0e61403244030a0b40400340b4075084c00d4002840ca0780c800c440c02c0d0480c0341200c0c52450b2140c1c03612416250703030503113110001c05036840000c43c0850201c0d41a0201007548002111450760f56401c08480f90004034651075003440303810001480c410102021244202c460104140c141401611000018000d1020080c00c1d8450003c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 539196276 1250 539195026 539195047
    0x70303050a1b0206010e0f06010e0f15040b04090608010c17041b0f05120106060e010e0607061404120509150906070c0906180905060a0b03070e041217040c1802 70
    0x11420102e45440d00181540d526142040e1445540180001041b01808080c0205070381d0000c485800c0c1501110b00500d40585580010102c0c19015002041e13440b0009001a02c5040940500304a815005e42040401e40e101001c07800e0381c1c4603201007400543e10a08503003161062400c1c0940041c05012000c0d94001e00c130b1a513120070b101c2a0020110580b05103402c00c00d92502002d031403201030a100080c04071030328002c8054410100e080180341400601c591416684d250a402c2d101000d030000405e0220500817003494561007010f030b400343c5100a01c041001c1da4180a1401c5504d08000908191210303248040140101e070414900c00c1d44c46001041414080380c110044d45018041a0303000150161904408201c404007007480403200c40d041ca03501c3c0b0003007400482e100e42e124070001700101d07486100c0c80000342050615000758441c44008001c1c0024007044145069801ca41c80e1164043c0c400da400640b0641c4004540003400070040d03100512a0a00003010401c000760200c4016040004010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 539197526 1250 539196276 539196311
    0x6030f090a1b0f150c110310110a091706040b0604140403200f0312090313090f0f06081911120a0611090303031501140d0f0e03040506070303050a 64
    0x702401c03102e4540542c148501c6804202c0800280b81c00006031554510341c040c0075000b220351050161988080c0841d8403520344060007040000043ca031700802c402d80c0c1f400b8116000b6003104c400c0301c0000d03420403004114152200410307081c036080c00c1d0050000b5030b04e6640c0d40c29800401040c050b041501d0700c3c02048240384521005005a00c6074039004854480c42c1c003194200c440840400c44143d1007683c03250f910b12004070444101040c1030140d9459543e03a810810b280d807282e030322002d1042c0703540640015051242c0d403210580c01c030055004c6c0300410403050f0f50401d81e901c81c00b40e6070498200c0c03402550b24201a54180d600f07e07114441d0750500b40465000500019403900c001952074200300c541c0010080b07c0d21854641c460f1100d0303542d00700900080032035501c3c0401000755924803104454801f05031b024102c1841c0004903250b01559070401019400c000e00b00188a0404132030078041215003480d0040242d03030a071140681828108100ca8904801811000d00306030401c40c1e848101602c81c10000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 539198776 1250 539197526 539197553
    0x4080a082a010212090c18090a0218090c0607030e040507090306020f0901020f07030308010302010c14010f0209010e03010902090604110d0c020604020109090501030c090504080c1b01090e0606030f090a 88
    0x4000103898101c13041d007083d0440001040002140c005004031822030303590100718855200e4000158140d50b8442d80a9803900900450203540008003580e41d0855403008070300141326203028815903800c5011407061150601406200802040903203080e21040c2c10f280c0e00c4590300c850586003070481c1558a0b1034450882e03000c100c59000c9080d00040001855804100048a4100342801040654903603180140301c41410300000b4100030300c0240e1041401080c94014918491501c02046619071194442c0001d42c0146000f5000c100035910b2400e25141c18400c1d04070fa00d402070804c03071032a9203005c1000010071842543d6505120103008403810913801e0701c918881411700b50010002800c060001403e1030003140d010440007814040184000380350000c006080b02c400072404250768546141084141c003401074507000510800021000340d5802e4110724003200420b89541102d079444019840400504507400c43c0c001c20200046003414048280450340140c14405071018625540c0d04d401c05142103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 539200026 1250 539198776 539198857
    0x10b280f0f05040b0d020705101b080708250513091a030d050703080709030515040303050901060f140604080615030d0e030a0b1005060a03150b04080a08 67
    0x4854094251038010300580241c0940e810b007681000c0c5084070b010340307600c03480201d0005260041408000c00c64100003100d80c15015070f009011010003a42c01407204004446001c001940c03600203e40114000c003ea64015826101184c1500d4501003000802021054000d403c0140401407008004d002e1790360b5801601e018440881d1110161281040c4054812455880307908190b80810249805c403040310307410f503418101a5251b54407134a00751401075041e840900280200401d17095103000011040c0c0c480c602c651810008c43d01c901e240f4900302e5840740900040e042140b0000d011502003184024801c040c014107142c540741e01c41440c1d608100341501c00b8107ea4245560161813460240800400c09509240903040c5040c01030000342d40345000300010b000107503183d000c1a0303062000c50740c04c40580b40150606540d9a402d2078024024511101070041d401070401011171407121042c2101d00321402d850092404500b00e4648400590001c10088910040d16494a1008103024032200d01c4190 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 539201276 1250 539200026 539200037
    0x9020913031b3002061f050901030609120906021b031212011401051201060c051203160e030f07270c0f301d060f160c0803010b28 57
    0x5152110fa40d100d1214a400d441c2504035110355405650300050311a0f01181d201202c844156450070442d00780c54041d04080d0b04140100d001106114040d0003150074144200000550b0100b01c0d030342110700560b14084e01c0c2c01a008440f1001c0410700300001c003451090003c0c03e03a8030101200200c0d2034540c0c4100c071110320812260004201c0501318945400c00200300f820000c0c50721100c845842440c40c0140101c0091145492140e0284601088079241400280d40560b0b941d042040b07504618540d280117010000320b10040d0220786080229030258801040301c01400d415051080e01c00000b10601700d15111044c54204490100405004911a00c000c9803038980c07292112400003000e098096072442e080031062500700490071400081760450002110002506000818102e00d5a0701c44041800d103a02c83c00c01400701e058481c81040340106003e281c42218500018000d0ba410103030001c014051800600041101040c0c840041400f000342041b0300180020717014141c8507025414030b01d240006c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 539202526 1250 539201276 539201303
    0x6140901080a0c091e050403081906030f0305071a0717010905192d02030115110c130b100f020105090111040b0a0306051203030402031009020913031b 66
    0x1401481680034011030009000c2c024556100c0c948640040d219010301c95540300800340014002e01001c840c003419001041c40103081504001303105c0c88040d2070451800c40903510881030792403180300c3c07501202d81c010f0f080c80c41d48200d504c007541e080d0000a800e46940c130700618802d882004405540e0710130340f000d0b2244088074006103556501d03000141c0210342007a1030402442141d04140c00302000d0296141c03004501640b10100300324130b80556440307100708a10f0304001c0c0d2007081029000785058980b4802d1101440428503411030302021041039445881d00182a8041c2c1800c05010b005100d03080f00001103010580c2c075000c00c02e0748000c400c1480000703010001c8800415420302a0542116244c002804984180020104107101e0351107050306090300000c80b03c0030300b40280c11040c02400b0090080160307610007642030340c482d402103a003280f207805403e40e002c0f07258880303114240225401400c8548c0035555100c401035000510310094041c00040188100102c00d01c2081e08802403158034090102e0303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 539203776 1250 539202526 539202529
    0x60201060e0610080f04032708010e0a0f0303090c170102130f06090b1b070f06030f050f0f1009020d0b120708031e091f0206060103060e061e040614 65
    0x4580140015201c1c8080c400703c07100c02680000c005400c401442c2510310151500c2c9800c2d01d651305000d455410340100f01d0361004100703aa140c101011030380f4181c0284009103030441d51a8403000c3c408001040e82e0190140b030000700c0d200c5d078840000144140e88200a013511502200340884610039611440c0e900080c3d4110800120b40c2c3c107038001d100c1925529001c50401c080542124408c2c05074001240d804981064488060a882100340c2a640182d07841c003600c4108109002501d8000e03c008a0304100550100c030409e48102441461402d4440080d1b0f25001e03610956150003070b0608100c6594043d01080d8036141e44002c1540018a0764006003e040e02c90a04c21071014800501c40e1640007030b6000c11480c80080121a803400e03605407854100d00c110001034826001d640703c0142c0001811303c642c0c24210381101c02c10fa403400190200c03006650740c42c0044050751001d00809481e0206000030541606111030482580c846165001030480303000d1001c1401c6841c42c0e801146025003401c0f1b1628503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 539205026 1250 539203776 539203799
    0xa0b04031a1009020c010603140705010f110c0d02270a06080a12030903171006090b130612090b0c12060105070b010509180105091b0102030c060a02070606030c06020106 74
    0x701040381c1d401c600d2840d104920482c607081902c00c102c0d40540000c0d055010820a5000602546d80718590881134040d1315034059960247e802200d001c9031002c249541c080f4042ca00018071080800c0040540c81c0c00c5c44103000c1043e50a0900b01e80007002004409065094010f076135014500c1c07400e00f0800c43c60803000440a80d43c3c03507031100610781c0000c040c81002c0b41242124480400c01414007090250461800301c80c0c000008010300501c00d03401c4240031a00054038005011140380d6a206076490ba11220110f000340b2038900c142e030100014400070441039000d445100c6012048400015901c500f80d110040141822a21852910030018144099480380308403190072010078603005040c0754090f82c4403240301b10180560362041703e580d40040c8003070901d00241440380f510302d8000c0c44282020b0741c3e103e0f6941c001e0b4154810a484040c075010702075100000ba03428003003003540101407a444400016000354803594090390340680740d600210105080e800410b00828444d0300000f045858096003845 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 539206276 1250 539205026 539205053
    0x1e0b061c080f04090507020d0e1027150c0b0a061202040c140d0204030b0106030507090306110708070f0203300c03040317130f05060702130b10030b03070b03010b270a0b0403 76
    0x852b01010680c8000c09034003140006142d070f07010010746000c0611043c5000175130302c15441101243c6841070783c036204540c0031807041100d0348603201410403912483c00343c0080d114140035040700f0101c0142d00c0c00240c0b60076004034407a44081c3c00c00c4103ca0703d04c06002803445d40500001040f20350001010410800c4e07502c3c8950060100d841c081015040800340240361200f244009088207460746044030396540080c04540509501c401d810b80d5815841c5482c0a0020078a141603200780a0283c44c0c0300e100700420b003074100c0f503c20400c818180c0c5011010004d11600140d13010406807105220100004000d0b04210003854008100c0715180d00034001c90895503a806c0d0820383d04540e00d150100724640f1230304241c0e040580d040304d2400c40340014441142c020005000030640c48155859102101c0d074069100c00519130003070381580d4a41d034596044900b00e100a2280001c82134042040308081c5074440b0484004050b0085248500300d042000610340861070b80100c02000340020702041000404a290507 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 539207526 1250 539206276 539206279
    0x4110c1605031c140d05040605090a030806060c0705060a08101707090b0112090b07031a090117210a030605040b0109050103181e0b061c080f04090507020d0e 69
    0x3100203003424003080d142c000c620280381010308001403640500c2d004e0a103100b0400880d100c0036481c0d120003613150b00907203415502500c4403072808021965000300070880d0302c106074140d220b031000d540300c3c0000c0c00802e1340520b401e402d41c3d0081007408030340c80d500c0800501e501c0034030796182d514508040c000168103c0690703020075603400c9100c021001410300800e05030201c0c0c45d607080005403d00d0800042c1c2d4042c0340c0e004461012464099120100100800443d000342a04e40d406c2044046e03424190b02c05c0300550b440e0941c0b101900700104030b80801080a00300702e401039400e8a1080c04800b82c11000c182c0c48100101407040c010a16114031139140c4990b000428040f06c0c14800c014001780064448002d40c010700e81015210034003150440c0039021141115940680c1c8032a400c80d0300c281002c940344486404680c0c1d0803150011503418a4500c010602420890144c01e140702d01d243c2da10140e661051000460b180b805004c0041c1a40c21407003070910515454014010001c0e000340c1c0144003c90480c4403a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 539208633 1107 539207526 539207563
    0xf06061203020a14070f051009030f11011706060a030507020f0307110f1203041203020a061d0708010203070e0418050f03040e0a0218060706090204110c 67
    0x19940e0340034248120742442d51008443d00c1740024425501640070b0381030180a14034114264818001032424036901d660b42c1c07a5120410300c01c55120035134013010380914042140d43c000e40e2903584640925540705080c540300000a00c0b50007103580149c10540d03284000342280f80200000d0801141ca902180e8942d40e59141c02101000701101040c0241c02e10100d41482c3d0a143c0144000c1034030300800b031404d20782054001603616121401c00e5003140f184584c03041c04980309100358007a1200c1d41509007c401c142d100c00e0b900d0280240d00c140410ba104000300318046030300c890341c03918001048030301040d059048d4160b14071000c14100049c11034040d240c041d80c9013680010040c01103410240d00c1524650707a41c0598400c078082c2d61015a668602e94186500d2444c1810042909621450b00024044240d4012900b298866015484007240001d840d558541080218003803100c90200311 = true := by decide +kernel

theorem cover : BRFrame.Cov 539028776 539208633 := by
  have h0 := BRFrame.cov_init 539028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 539028776 ≤ n) (h2 : n < 539208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
