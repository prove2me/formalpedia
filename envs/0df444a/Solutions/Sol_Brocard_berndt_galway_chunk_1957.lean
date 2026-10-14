-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1957
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:17:50.826988+00:00
-- url     : https://prove2.me/submissions/d3af5d9c-5dec-49f6-88ab-abeb333a3f8e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 351798561 ≤ n < 351978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 351799811 1250 351798561 351798563
    0x609150f12060109050f040504061b02012a0e10030902060f0702030c180c0a020a0c060504051903050a06050405011410180e0309060a09180525020a0204020d0605040603 74
    0x5568480103a4900c03040d61801401c1541081340e00b00e0108280da0700c20b5001010a901100d000450b6202e504e0002d00520b0741075040104030300075a40351511583c040d0312600040d05203480c04d038a005c0c2c0000180000a0000a265000c20440e00014045003001004000103000d82e0800107680b8034240c00042ca103400c1281003140000300084d0500441c18180002240d4100945111400c01c140d000c0c0300c0c45803c0010008c1401120200b0804030140c030804c00015141c1e04460112407484d1a00c200400542c80b501805010707081030456503054a0002c6204000c40f80c201c1e001d01201d941c0d82c0d070360a0103417070b0103041039501d90740320300d240c000110484c2c5c007490040c140101880c102500d007508a0032082010750960345414600406090b40d2100801180e580300000c55800c0d41c0d070380380d541040e95032085541000240d5500400c00203064000e03580054092b518460a4080d038200004000c5001c80a603500200141c01c08104100142403a401410305180c00800106e8403945550101d0f00322140303030380 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 351801061 1250 351799811 351799837
    0xe010909091b081507050c0c06030f040506160e09150414010303080106140403060903020307080706060906090e1b01030b031b10020606011b08070b13020f030c030a02060915 76
    0x42e101d400b00c40300032800d0024501e2001801d000c4080d50300c54131501c0d100034109424042c00060b031200c10b5030140117100c01400300508440e100c0c207103030382c13140c203107a4044400f05c40510808000c503040d4040d50020081d210380a03520300c1c01e5102070205200c125030020303000344242500c4204804140c1d441c3d02800600495003030305041c0d15895420700404280060f40500c09100681d825804e0300f4004104550030780c1d40000c40402e04089a10f0300301d180d4450039101408030b00010071417a040003010740000c01168601c5505020440d15071450307400f02c41e41e19248070703010350184803c000c0051344141004c5203528141030004031070140c800031034104507150040d207400c3d070904c0c009001d05140240310030018805610040c000c41c641580068440800d41107403011003c8081100c000700500141100c11032035000c0740c400d80c0f6080c99008010100e00a01d8200d10230602560b88819900300041c84040e030b030100034010f200f8500a82c00340807040d4892800c0f12341002c00c90341d03284104003060b0300920700b001101d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 351802311 1250 351801061 351801083
    0x40303090c14180903040503010509030d060519180b030f030409110403020607031209120c120309050c061305060703080717010305060a0c020a0f08092e0e01090909 72
    0x880c080c00c0098003908508840d00901c0020300950321140480081650f0320100141c4544508100074914040e40d80120351560800080000d4400080090014002840020300c007ca803107404001841880c20741c681000b040d109030812080d5558601c224111a605100140601d4031802003401c01c051000c0055803544006410011710805115003c203101940b55003e003458250b0380050181e104220002e002c011041d810070007084d0740340c1c1c0614282035005024051601c8040e00c0035049440035202680d2081d0b1100341c20001034002c0c001d03034490307e40c448040d0080c120341700200401074126400300101340d44400b9003c41c035a1a03800003801100d000e038072a130342a40f80005004020494209092200300c031207400403c00203000146c1640c01440315000860583d907440d04c02c0740f800f40380d2640503001018107806101444020030040c050341000b620311b44400410404102002107010004818804483c1c44000300c05100300021546150145040170a031541d402070b240c152614290155040e417044 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 351803561 1250 351802311 351802313
    0x61c0c0e070f090b09040c210f050c09030606040c02030705100e07050d03120504060b040f050106120e06010e25110c09070f030b031009030806040b010e090115031404030309 76
    0x1c82c14522516903c0c00031405410320b00d00d04d900d0300034800881d000b03e88410600000c180110030141d4041025403803419604464503c60001d081e08890040810740380c8400715094150f46412950381c01c3c0c0c094028051034880d14113000c001d1401250760170441c0010701c21600024000c0c841040300504203a40843c01c0c4004005142c101003003039100910071a411404040041d4000d2410701d101621188005100d0303481d418041c001c0c141c4150013075809440c02c0100c0c0240002079011605032a140d035a44408080c40b04002402c944076040030301030f04c0c1c0c410801005000c2c040c18845621100b0426100c042c00600608800c803501e8904150011400c041680e0403018410003001c00401303800ca590040f14148400064024140095050201f6440706040d5107151002c11140f0803514220008004030880c508000304010000c0d1080c500c9035041031642e659540c03090a4070700075403100a041c442d059103842d03004034114109050403000e00da201c4c1014482c0f4200e002400e03219502940f4082168202 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 351804811 1250 351803561 351803567
    0x405040c0216050102240705070206070f060606080114120c0a0f0e06180610020106080f031b010b100810030b0408090907030c02060a0b040b1c0b09010203040209061c0c0e07 76
    0x50307400060440d40880c14502d11b0500140401c81042092805461242c890001c12212031243d5135000c0e4100c40c0c0003400204101a001c0310f503c40c20f025607400c110103611000d080300e02e00d00070311641c5200e080e00403000d8900e240502156010307514030700803503c00f0150140802c110002c264400080d00071100810032084d60800c084035400841128041007d19080e00180481c1e0405000c85000da01d8183c61405140d000f54826070107000701000300e40040d008c0280e1103949501c002111f01104e001c01c18158102c08050050900069004111041c85012a00116103a840041c424005128591000070101c0d000580481c0a0350044201d10b0795061100240203444101400460800d803910850318949980415403a4000f00310715004039404281100160240c03120902c526030041081e84090181940701140000311413203441c5c01c0903180d03240100a4202d0100300e03000781d00b01c416900050304a02e0800c401000806403040e01c1c0f40002c22940b80c56000c480f0582101c141800c1e144280420290 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 351806061 1250 351804811 351804853
    0xc0706030b030307110d05060405250305030708090a170303041205120f07121a0a0b031b070f0b04060504050c0f01021c090b07030518060703050313080405040c02 71
    0x1503090a01584024801203a580d1065420203014044031aa02d406103944285034400056007100807681a810142090f58850441c0d44090b0500788401241107140d50318010b0f8603040b65081405582007c0340f644483c181580030042c01c035842640040c001c0303000300010744024800708c04c0a0040d41c0700d282070700d00100d8188111805400b40081030007070820403e00d4611440d4801c6080402180c1911200d0050300e856840400503222141059002407030030340701100481c0071103011900030303213010b5441c0d500c022944025101c241d031700d1152074040480c0c0280c0200900f0701922840344068850070302d440c5c01105000a440c02c03902151240b00b80001d10504200c9201ca010044032a06455030074800080d540d01160901c03099807841030a142903050740100b0308000140300d004030056480c0031a1500404642c00655445030045080d5208826810101c0030380300000d134183c48051841e10f0b5400c10840118000408441101c000c200119041d01c4034080c00501e40301da6001002d50014500302da00d0741b40317 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 351807311 1250 351806061 351806069
    0x3041a07080d1506030b091501050f040603091e05030d051009020316030e0f0a02010e190303091703040b180307030507090e010b03060702030304030f18030b04200109090b0301060504050c0c07 84
    0x18103000101b056076881d00b811755003050b02301081a401d61003440040c0c5460003013004075081080e000c10000307140c075015041904860721443e022000c2842e0303030108880c005403850018142c0c0d0300500c20010601503e90040ba004503641d404030400310780c0d4044007003c3ea4000c89d62001e05415421113a0315154141c01248600c0e014103000d454144010351102d642c0d110b2813007001c0d0401464020001494803804500d0800c1c040c005a00490103489080c06050007400703210700714003403090f10156044100003105031015168401c3c4440d143c80301449180e038004600d10340b05d507070501030004000300040040080e5070080413892008580d03490140c00f12421615185a07a5000341c10110820070715603800300071a540242d05003486250401881007c5880d08801c103065132001c07048540120910200c0c0300081e00c41d910511400301b8202202a801194071000d00540c0d02080110900b0320081e4420780028005200203400052011340d604000341c01d960040d141e003004003030000b4000d0015501805400003070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 351808561 1250 351807311 351807317
    0x40c0501031a0112021605030c030c1009050d050a020312090616030510031407030b1f2102130b0316030302060609010308070b0601141314011103041a07080d1506 71
    0x110b16000a0030944090400000f05640010700c80031380301030046000c0319181c01c901101d81758620914041d5403540041058191846a004401c1070b010140c000d01080300d5000c0080c1052500d040c0c0306079000e420164411041d80010702000ba01410401d029038420710724800206094280310120521b4604880001c808140c1000d0411120080c46250700301102c0c1e01140b68824500d80c7c000d00790408142d40c20090007005000140040c136070352601c41030700c01c000810f100540c103035444c0300507481c405400440c211840b029108480c050f10301802c0341d5405c00e0306140f01050307559102000904010001c131003c030001d441d071300042c0281941000410340c04003058507040d11550441e03c803000c81d400b0340e01c001020440740000117640390744111402d0002d5240c0704109070b00c42d2000340c6461a101d1040c0030706d0280400d601c0990703640d0341c4604920180001031a028520b01800c1100b0361044c0d5aa24405080b040d070204041000503051000411147c5490400094449000300080181101540c051410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 351809811 1250 351808561 351808601
    0x108070504230402130b0703030f0603030e090702100c05031f18020c010207060501060806040507051e031503032a010510290d020d0b04110702090408040905040c050103 74
    0x842050880381d60b800081042480e0200030500008010340b140b50807a4034146660803001641003a00000760140d540310351010300a030703c15802c04004650301403001500043d484203040800341042100c10781c01c000c482c4103403102c2c504809040410b407074401043d1000100008204514000c0031010401e6000094084410b80b500c0c0c0810140b4244007610007a07035843d130000e1201c4504009504a13680313558044003d0105694425000d000300008645c024001ca00f000000b501312886801203401c0b0180c0103130805541c0e46c0780200c2c0303140d54000406104e0030202d42c11402040b07540c03c20250074465001a0035804545240c201595000d98801e007540c02030b81440248444598145025000d0700da0700f0000c504100034400046100c070154018a804851b400500440c1003e056001809038001c031a2060180080080c1403000325052508444400c40341440304c80e0040c40c010501540081c007030503402c0d0925444006143c122441903034122025420124100401d50301802403c00742f400320702c12041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 351811061 1250 351809811 351809819
    0xf0b04081506031c020a120f110d0206180a0606170f0703050a0314090a0609050411070b01091e050a1401140a0303050a020304031b08070e090709020703120c0207050108070504 77
    0x1950320744c00410400c122113001100c0b22418400c12450210580000c907854585030b00c40e00140c21680803c5401000403180014484072120001d020a5104626401008190780c1c10009050404410071000c0c09802409000408624540204400350850020b221224116001c1140c90aa0303201180d202540003c070080000ca00040380d1001865014144041a03464205050250340700d801c002e51ba2224101b00d010a11a030f1091121041d50790030754040050600752440d100c00c500500e0310060501c1c7c0320344010702400d903c0c1d400101060b4140f10345c40c550f00c010030111205480f011102c000009503100074007031800303010303040c00da004205280d951041e5285040c0031030148042e5020203070501c07000007503015202d4400c1040f1001560448810400c0208030081040718030f031a0710856400703215050340417420392001c2d54158025040d140042558501c1c0c600800301a40024400390144062402c02980c504d54038000c900884017564041c040c120b0502e0000340801c840030b814641009002d0100380 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 351812311 1250 351811061 351811063
    0x60405090f100f0f09050d1101140604020f070b012c07200c03031309060e01050a1202061e07060c03020913111e0c06150a06030203100f0b0408150603 66
    0xc849102d0803000c1440c503a04864440504020083d90703601c1480c02c40303d0418007001081c405440075850b619600018a10441d9900342c079420301c4240c41c080c0030309010401514107640181080086008024200700464880b895010004da0091003081d00e40c1207018a4040c41544050480c411a040c41001c2d0402c500010700d511803050091076080311003c0e5160700404200120004540014122035540b617030626541100895032140d40b01260800c14081222010098a28140c0720080c103504d140d2407034811036210540d804182660003050410101c0c8944160806003007411001103e015034403407851a20601b11590880d02008140c81401031002a80c0c90402c07107800e010710b0756030100740f901c91809864280e105580700d81c2201105214054640401d48024095810f440401c1e81c4060303482c5442c0d08840f1501c0e060566100e500c1003803d000b498003d50242da0080081a80844c030700c0d840307004551103400705422411080e00b010804000100080011500d820180740d0f0f03080150414038042 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 351813561 1250 351812311 351812323
    0x20d020610090216150b0306090a020907180e040f12031103161103310b0f1b0d090524180d050a24020310170a0203010603060203060405090f 62
    0x40180c0540004000d04070344c840c20364401040c1d07041460b00461007030b035101c07060081c164412401d0180c00340c0b03030000c0c804c10360120300c0300f0316a60050401c10050303482145c112400110768404410f242c1c2d03840c0020407096880323492544110300c03e01340001c00300d10504180317181c0f48403850404201400c01c400309812a007602e003540e0308010703025041c10282c070300c90006071012501c1c621481c107140300c0820102c103600c16650034003050f0400104c08032807002c2030620500340b49485010382c0420344010081e0011801c1d040700109150104a461080501d1382e1b26852802d0000224806001500c0940180041c1c90502501c00c4003915000c16210103041d860592609400340c01d0a28404c0101c0da0703802509034031482e005200c02544142698086400e41c608030721407001001d020755050182c1d43c03582c4c002160794400c0300d02410152440302c0c00c1c0d40c540448520110742c0407403c0202c0f801800e03128401603c09015440c09580b0034107002d612454000300703010403a90f00502c204540d601180d000594a8030120f60 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 351814811 1250 351813561 351813569
    0x4080403020a080105090c060d3b0d0512060d0b09061510021903020a081207090b0307020307020d150213360506220e12031605090a03080c0a03020d020610 68
    0x915602c542803103454000400042c070ac20600020071403a4003402030158030078100b04807005c2900403104246103600303581c0d4008082413080410000c10a95501d040310315a1142d101500510309103040805580e50700e0428025512050075a200d60180241a800e0001072488450700741d402541102039148000d5895620520440e0440407a1391100f044c0741c03007441100091504452500c1c1d55400d111101d65900404407001000901040c001284003c800802c983c054030040c0d00031400d10501d0f0f000c004203c1803030341003203a10b4a0001103c103007a200900142042c2e405c121a042400d5282054801074070141c5004000b50700c501440c400c0a83d150b054140000c84226400016079a460a0203d002c800d103482c0e20701c1402608000510306000a60080450440c0f8002603900b400650100f83c442d50005807034446c1a03070409a00d2a040b10b00c510003801c503121000b8421300403140d0720f0715010170741d502030f8011080b944c00c03074101101410740411156545d518544014035040c81c00e51118a1400e083d401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 351816061 1250 351814811 351814819
    0x118030c0c0504060602030c0d02060103020d110a08010e010204061803030f1b0204021315110c010c053f0c0c0103090206280905040515010f120504080403020a080105090c 75
    0xe4404240070712816608041c150151007040003135151170010b540c0340c10040100c5064820180742441c1c5500c0820f00c00d0481c0d40c05402c7d03000c1c4400d0303135540710401082c41060b10f42100414800083e091004d01641500b09120340c00160744030700b451002041822012400348800154450030400a0342c044150090500c541c5400e03000d1121020002991199401019602c80d001154080111b86001080400c84a10301540303205c0f08520b44080d00c4689840c110461036070003100700d059042d40201144000280305200395601c141c04040c03034030242e60358102c581c0b1841d00c45044448454004111003d01240174060fa182481040f100c0c0d140c2d109200c1c030700c80e810551145c20301400c54581d2001d84085110340105241000c0703c0d0080708008120351a080d800160800138001034a0a1522920b80a500d00346540151701c2000d00065a007445448024020848100341081d0049118030860b40650701c5880a2a0744600d180100700300c1c003619030880c0c40c00e07902d84070520109200010f040504e0071000d403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 351817311 1250 351816061 351816077
    0x30b0411030103201c030f030b040e120f090a1d0c0309030307140d02072d0f060510030503040902040e070e0d0b2e0f1401050a0302030c0d060e09010608011803 70
    0x4400701c0e1a0000c40e50340002d02c0c44560180c40e04154100d0f030405c80311903842da000c03c01e0f409c2d454100400e07610041104032540e00700700c503415614007009004008010522505ea0300d030014040109100e40c01c65444a0030f282ea02012202c0003c2440e03909036009043c8078017141c114141400000c1e2a0311004c0d01760b40601040c1002c4414600544c0c0a0301d010400d80703941103480c1c00c41070a1400d10310140d00a5400280c56010120130340c0125060a84c0d0030390341141c9140310b01c260075a1820000c101c06850030b0840c0c0c02480e80003001900130030040020301314211003d0780f50703490f00303007449502040039103a001403114110f0038032040c1d107419003030359609078000250128540b901e410003a00410b00d50114000303110780c10b030600c0c001d05030754004034104c81c94519044803882c0c0d1c40102101d24004106590b0004100b04040c13a00e06100c2e8010b9078001c15542035043c030344001940d60340103d40c2c00358450400c25410301e0801224032400e02c2440c0c010039626000380041c51020b199240105814a00141801184 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 351818561 1250 351817311 351817373
    0x31b070f151e0905060a020c041103090d051315090801151203080703090c0602071406030f0f04060605030312010501030f0e0c10020f061509151c0f0210030b0411030103 74
    0x40d9400d00300801019140d691b513140074000003511111700c080b0142c003035802c2c8005500b03822440d0b021a4030402e1064081c00c011203103548102c1e400d5211149102c030034025007001041c01c0c0759040800101110b591142c1c1e0b8002e10b003805640c01e441c03030040719040c201d0b61194100511190b88408440081e0b051500f0b03580f980c0e509005a00411410501805030302c00307140003103095034000405100382c0381011183c555102201080208501c030445001156a86020200d00d121160482c4107810910981c404540e241d22540400c2c950b402a08500f549190181300400a82d40c00d841880d181640c4190b080c09000c03100500d0607594140d04924900a100d9200c90003146c91081c00303245001d1080d60103813411804c3c41e1704101c000150800b4000e114020020108181800c0c80c2c01d17035203100c20040d022107904155070491b01a51124681e007a201e10000040140059036410401c03900d4626546000520686503070030302080324410b500b20740b10324404000500124505c0004400109070b01c0e44056184005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 351819811 1250 351818561 351818567
    0xb060406080a02070b0a0609292e020c04060602010c0e060a0c0803010806041202030c1903140c10060909050c040203041b030b060103180f1202031b070f151e 69
    0x4c82201404c04401001404500c3c102500210202c1d0015801485030f03160500c51609220200101d4040201f190a104001030038a204c0c0c04030041c0c212012040244224400011034809115403600142c0014060303441528052042d82c016140741d1000308a5040c2c0b081c0041c00d08280f80e590a4031648003c5043c4c24014850103174004603590260155469596908816599400070f9400300e51145107032400c0c3c01c0c1c4a02c008203031185150f00720700a100e501e03441030400d01c110301c071007400707a00b0002c800781c0301203552000d80c00401e5068640001000c0d24406601234078122110303074200c03503112420040203001040001890f5400114111030040c0da070b440d5480c0a10011320001c40c411109601900c000060258002540784500360a0300d0501c4418103200350003595000a81004001d042c0d10800a800704101001101c603038040c5004a0340b03045c000754030070280020002940d00c410380c4070360700c00c0c8103035000e62091600501d00c281e1800c00202150030040c056a1240302400208080c1d50035607404144 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 351821061 1250 351819811 351819817
    0x11103130209070503190e0c060406030204050a0902091e030c04090318061d091f0305030301090510120807020d02280902040b041701020418050405152514160b01090b060406080a02 79
    0x1000520152b65076546400c00f0303000e508a80b190a11920105170002040007180c0201c500380d0800400b22030890040444420070390311888002d50b01441802c801900c580c41c1e500c41d07014001c3c029180d07050000460a0100081d0080750040b104210103001c0c9500f04820003200c8145114044802c00c03a80d80e924182c840305415990314007940801a0780c0c002060000100c011410b13141c1251090050340da0301005000720100b00c0c8070300502301041d03003e0300380454071800c080c2403041d1004240d04244071503074000980c0d04610b03140801c107180800221444052840d8039100c02014161010760a051030310030300d55401d020300d105100c850151401c2c00d84d0080320a5040307402505c002041e404689004865481c000c00c0d048a045030035101e4142031524030010749981c0e5100e032007144040c400007410000110751503006082c001e402d216100003001e0200f89400003509500300c3c3e426020f07600c2185d03810a40f03070201040c2d010b50020b900d0714604000d42d0301c4078030894040d5062420b10340076a40300d14500c800248 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 351822311 1250 351821061 351821083
    0x91e0a0b06070b0c121308090108060105120403030c02010b0307080a0f140313030c170d0302090a0b07050d03140c030c0319020d0e010b06131403011103130209070503190e 75
    0x1c03c001003000b0080d003d0b680640800b83c07000c04e01890f0342d91450482e032544443c200018204460038045486990701c00c2003009c2d4840c4040c0340483c04c2001a01100351481c000365800c8011a8a0715400b00c9090350900c60204000021401000e549142000d01a00c03601036080180100c002d07082e0b80c4d01032008000c050500203906400300d030764650182035840d110041d2030108407000180030b180000c0b0400e0102d5200b15071117808020b415500000b20094009500c035600d0103803c00456280040c000c81e2050280c25100d001d40c010700012041c50a005085841c2c400c0d411f200c1401100610003042140c006aa41c030400c984500c980d030b07031540c612814914040940d40403481d800015000c01c080c155400c02a90003134904c0c000d00092441104100150141510208a0000100c030400803001102403040f15980c015000041103c0784500d200c00c2035004640c2e0404500c50242c00c0011810005c10302503008546152840c19070030b080503601d80041800c4903007500252203440054501c4803d2056020720 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 351823561 1250 351822311 351822323
    0x302120304050a1104020406020c04050a0b060429040f0e040203010b04110c070609060c060b1f0518010207060509210706020f010605091e07020709060f05091e0a0b0607 74
    0x28075040c41e01c40d548450100040f100020340110301080f5041c58001d4070140d51858028002458000c0306103c02000001c000c4294640c603400b03c0c0000f621100300400180c200340000380360000b1505007001b800302c1400c400d8046540200b004125004d0f01e62403001c19189492403000381340e1241c0c00000c2c050840310000c80c3c1e00c1840c0059003a4880003140052084c80e030b035001680c10b0566208001d981824083c0f1624022880030101c8038000b0310642c2c00445000300c01040105158601100d94503c00410703245400454000a100a0070791201140d09088890901c02800b00d02d081080c014514050280054002c10701494444030b900600d141c070071204200c14003290b59607940c4c1d09c0c00a50343c80e00309601c44415468035201103103d0410510a03072044040d80c2000c3c1c2034040d90241c1c3c82070b000000340300c013007140191000800c001c0001d01825004200800003120140d081c4000c00200b280301400b81039040b10300308050740c20501c26082d45075025078032441c0007500b16030710808200c0d00e100d01c0c2002004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 351824811 1250 351823561 351823567
    0x40b0d02030c0d031e030501050306071701050120070902091309020105090108091f05060a0614040501080405071701090308090c0a0b091804120207062303130609030e010807031401030609030212 85
    0x2c07a035411361115048132811012103406489540040d9376005c0c0702070341050000603081c01801130b03501908160b13207414282c140802d0160341d9502507500b003610581015141d59000031704078450b0310344040e00300000c40308444104849102e5074006000303031007460b0b400ac0c180000840001c241c0340041c0084160f80f210401d2401c202d920100e030f510001c00040f141948241c1d4100c101248840c42180020f0020b200074014900e410b080100542e1002c20003001100d080c0f060364000b0602038114141c40b1450344218001250002c0240780c0035000c10801001c0031030350b86c8205805502c1da920480040110341d00810055070f40d055a038042181070564400800c1e83c902204203210800c52074000b003018803800c507803e48030307081d441c1c0c0002c440c4a8401e0440c3e43c0700c0b4070016a84005000800011030b04032490852035802c0240e555034150030380300f910b80d09902003402001960076a50304201c007240d108103149420014501440360b40d9088282c18003001c0e082c00e550300040d40803d40204000e03044d0804038007103962 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 351826061 1250 351824811 351824867
    0xd0504080408010e06180d05071b1d070221070210030f0207110901050405090a0b1f15030605030102090a0b0c16030c150c02012a20040b0d02030c0d03 66
    0x1e9121707030070764905440e4074080041d5501c005012402401441d01a071b2000d01d0300c5ca064940e0000540a804410404082e0020015500840d8040c15422509050009015242c071301d601a04104820394000740e0b407900f0035080250000281c04856403075a049945041140828808400410b010a101c1251070710007c1c0388400c1c0490070030310a5050074111598002aa00d503424801503903005d86036900e007984000800030014811251296001c904400503008030b241000028a083c0305d00d034044203494200d403944503000c80e40342c054840500070a81c0294500a0b00601041e64011584200e00d14110003040d4280c1c6e649041c003030810482081040c0f0055036071a4100000c1d4290750b44103044440f55181032075141d86006038444034080e41c0503182d0054a100c0612605407079000404009115420060039000003034400110145000340d10780c0b017500340f007140c0d810300088500364614a40701c0e4110411907801a40c0002d0301c24140c0f0401d86011240320004d240c00d40d00765001c035044002444a40c0c003807071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 351827311 1250 351826061 351826063
    0xa0915030e060c0414040b1c0501020903010f141b090402070c0e010f080706180311040b03010e03030a06290a140c0d0e0603270c060c1b0a0b0d0504080408010e 70
    0x40180c407005d071801d07903507014044104800c403800809101d812804041003452001e0100d42080c0116002d0800940303003d0a000000c1d0840d071800d003401c2d9100390f481c100c0050301d401c2091140d501c4072070380380d003400f04030f114004140c40e90084141c1070340f00701d40007c8c00d07208100c2800410401450010071b240600e58403402090382a40841c028032646105d0500001a00e030712072490b0300e0904585901b044846402c41d01d840c04031184c0c240c0f00c1900661036001183c1c80b910240309905038004540d010f187c072030070240381046c1542c400c1ea0190103807070150310060b204103000c08501595518125030041e42c0e031380140c5050703941021042c0e10800c030440105400b070044502207204449141303680c0e40c070100700101004000e03c030b01094a0b071044995003030001c1107050000026001d000b0035900125240302c0b5010300091110b9200a544680d1500a485100c0d45801c0710641e05000d101e00b25451040d0030b0a148200c3e81d41d009401c000d00b481278682d00841c0900040c9411100038041c0000203024881c4407050503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 351828561 1250 351827311 351827317
    0x1505160803060337021507060f060803040501120504060b09010306020d0f020a0509090c0f04090e070b1c090c090507030c0206060a05010905010815060a02100b0301020a0915030e060c 80
    0x5500a0080080c110b9241c00110140f40b41c10b0100d51924500304c0700100c00ba007040001e040126005441105525103503008080907001480c89101d01145200102c14080e058400c1c035841840994030506c1b0500580c2c1e0000c0c10300e14040d00242c40000c165883c2c0c28040090100108003640051803107002200b4000240c0041c8044003078000140140c4c41500348a900700d00c1010702d01c2e000220709001954140c1351144540742c0000a0303246040c202510716100c903880307620030b910002d5041d98500090b03402c1035051140b08000c2066500050600484403d205404071015000102c0c0035600c0340d0090410082802d004003801820104220600d03000ca405802054a501210301510405002402c1460444280001d5540c107960f058112458000103440541c4050056914002c4148140b042c030749895014090a85032a4014120800820a4a412199030281d021301907401000b94070031080c0c00260013011111007800e4944032180c40b99040b8000e20480341600301e10300500d0305003c9410842005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 351829811 1250 351828561 351828571
    0xf020c0d0801061d04020a091a04050405061c080d02220905060a0f15090302060712080c070203030403031b06050106111005012d0e040b040b16091505160803 69
    0x1070038000340d0f2151000c0e1503521070f1410590000b00c0310b00c5088143c0c140342e00600905e03001d50401034451510388083c2c41a00c00070001d081400800070a04000a15141c002c0c1904244192010290344c8204510315005a0300c40c1000303004143c0010703100040b6000c030381c1110b90071100419111203400c114100742412301c01a101e801c40042c01d000c00702c0d03401d142801c414000c82d080001a07007038543c64034813400c02054120911005010218200002603141c040c010a1158072544400c075030454404409060050b010706092014541404540f005841c00021202940d40500f0103e00c10201c0c0605030392000707545040103007128102800000c801e608042c50004000e100360980d084060000e950300e0031194240f00302500320107044514000d00f86800d440e0b45030252489007000344e003916032036402000d0b04207850031206140c8410402007032000b000c0c051034005503030781802d00c102403000300c00034803403201c0d40156280f0981c0441d441ca10b131406001102c84c4042d401c088441d1944a5003016100c9420841e4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 351831061 1250 351829811 351829817
    0x210702040516080402090a15080f070602060c1c060308070501090501050a23090c06030f0a050709080a11041d0a17070c0b070c03060e0307030909020a050406120f020c0d 74
    0x100e007049039078185010b00d001883c1d44031459503859408200044d0005410400215031b0b0b60740300a2106000c652000241c50768100030300031840128185407800d01e09500c40c1d411034002009008280d0409411102c801d959414116200042000e942008101c075a1005041d0140058203408200043d0000c20311103001c1c2008000302c0d5aa0010031094030b4191890402d40d0360a13030510410340c400c0b0000349402800d00304c12614140310b5003010031100e9000b0b4401c400c0e080da5250400501d003c4901800350b0021040c0b43c01b200c21494480455580d8818200041180502811000a5031102d910410207164140303000d01903025481d90b2141c0361025500155a03001492a602c03160299210171103090030703401205000c0341ca00d01904418240c111000c1252a1605c04d6000008a0954083c488401c0100c0c40603580d50011407030003070108a0540e006d2500140148101d02c0308941120640b000c6503110300340f801d160107002071a50010400c0c601c01c000300603c0812152110000040c5207071400810361 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 351832311 1250 351831061 351831071
    0x60b07120306060e0a0e0a0209090f1b0906040b0306010e1e0a0509010e1902070633030c090b061c05040c1205060103030318020d050f0d0509030d0c0521070204 70
    0x201044a00780d85580d941c607084018048104034000006c101c0c1c3d640588102401801c0152880015410b120f040ea00060500c61107428008890145010550806500c44800e45840c00100c081007071030055104200001c0008400a0001d0340224138103260712800510080300d10403d1003103c005600c040c81c01500807601d01c880803070310b82400c02c040d03416030380f5a440c01406552a200a60780040f060035a44410b40c0d024010000011102d0041e00c001404072039945904080d41a4290065204a03500303010922400c842003003c2401900b200e42500d03142400070a101941e0800310381140714440704082d0701205003525250400060b0310942c0607038401e004c0712640564840c049002110b00002c0030b041d80d080300c001000064040e60000c11040c101d040d00b03046403207d075000a03903014000c00003a0b6540c2c001002da41d90b075003000d10a1030312070b0a560400a0403e01c2c42408030380d0300c11458143c1020300c0540702a460900508000450702068594000340034000c0311900100c0301e421421080b40110b00b84 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 351833561 1250 351832311 351832319
    0x302030d0b0312040506132c16082205100b0a0506040806070e0a090e070603050c161209080d030902011b0506130221010b03070905130312060b07120306 67
    0x11850709815141c083d02982414102030400c00325911821500c2210403803444002200ca4050849603107408400c001c0105d01030b299001200c601c1e00092446d0b0854055240d4601e0b03142d0403440341600078501d0700408074004095441115040c0c1810b82c082c00d1886192103600c6400344541102c0d4890000740d0380343c043e05a0f903005106a602950064440355002400090381c143d1080c1d049a842000080c45801c046588001e100201c1d042411050003e400c0398105105243d0180a840e402203000d56456143c607188545c003401280940d0b0000f00601600350000708203911580300b078805800d89105640104014500280c003c0040c02c00890100e0078807511200c060b140d03a0300101e031140c0c000b8094403060307450f89441d03031780f010b007003001203911510382c6100000300114800258105100e001c0000b41400c0581c0c20140350a8182e40b0080906003060304004e001c00d0302c0c240d07200c01d065043c1003e44200c4980c4186070b010b001c0c5900261080900481d8130300520000b010b1030100d2580f581c40810243d074803 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 351834811 1250 351833561 351833563
    0xd0e01050a0c1106040312020904060305010203060901140a030b1314071d01030b0601030e010f0608160b0f04030209040501062318010501140903070902070f21020a02040c110a0302030d0b03 83
    0x40f03c2d035803070071600050009800300b40900720380400f480410314018900240c0a000800302c400680040d212a0b5020040241d20305182d0481805090362100d04440780c003c040000d1003c00c582d0100500c480d10f80408100701c040140040242c455110006075124211884050303a50b20840c0b160a8406d0f0041c00c000c2e1004003840e8505041c0d9400c008155025544c1c500158050000700c903001d180e96603242040c0e6030454285c0f00e00d4014040c0306026000d01c0100b4450300d00c415400c2d4202c10340c0000300300150054001501d0880b42100d6068071540003a07629070030064010100c40d4000383c6280c80c00b1000468030740c41d11500601d034143c206d49860f804400c0d00021118100300340038003400310701e012007980503440400f0040d002840f0020102c42b01d454450f10340700140e8000020896804824403030100810003c200301000f401807001c0114407501a13460029500c044240001c3e004a41c2e5441515001e032107516140c00e801a4102101c400024501c6c1c0207644c0c1c0e221019240c915031401d0441403031490 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 351836061 1250 351834811 351834827
    0x40f110703260a0902030a1b060e031506010309020a0305060403050a081302030703021221030a060e100b0d02070b07020a0b060301090206090405180f16050904150b03030d0e01050a0c 80
    0x895140140c520f5659112040c01464010416130b4540701d03810454001903098481c100e2905c7c640d0110591052078100c025101603104000c140c0b103a004200b05032480700011a007140d201c5001d00c3d0205032405940041607003140b0701c1d04003030003031700074401040141a0002d004050406541d03031303418410340d04c030b5001d107a8455240500a5250304603a008101600c1d02440e01020b0594900c10b1701e20510445020400158030107541d0310041901004011207000c152144400601891032640310302c1c80e01142400040c0c60901a5049e030000114145d000060150b055803542c0760300000c03980140c04d110702c1c007a41d503400788582202d030170f441c14002030b00f981018081c0102c0160301614403410424541d082102400c2c0c010300c20040102c084540504040e070400c6030312400d8080c407021340012005e135180058030750300c4c2d90000c500900107007062000260a0341040c84400c40302850028400350940c0006e07013144103941e4030394030442c24442c43e046e0246040d4403490045211010400c5410644881919401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 351837311 1250 351836061 351836117
    0x5093a060b01120b0f040c050d0f060315054003020307150c0233010e01030308071418010e0603100e01083906030c040303030b010905060405040902040f110703 70
    0x1100a281758405050940144503e075402c4d06060782041503c81140d000c03601044020f4004d582c07245010014841e04100c00724114150520620061410101100040082205140148002000320000001d04803d0640707441807101c02c0401e00d00c007034103000350340760810071041e03508103042da031074040c0c0900500c20141c0c5015250042c2c00a0900614040e0300d05000a030400054000350500400f2814414281400303400300b507182001d19411802c0c0200b000a0081ca6041071121034003070300c900c083e07142c000d48050051f1000b64030480c0041c0f1004030383c0e050091702616004200401801020001c1d001e0200564038551040c2801380c3e69940c83c3c3d0307a0b40950071003284140441c04140360010150040301060b00e5001010070900701c8031100031800700d500c02c0710427680b10b0401142c24000c140e03141c025000d0003074091800d0054a820100040c5103881903214580c400c6a0b140d5001c1c1c21034a43c2d4001c81e0300d8050400303041101087c100381303105580c0d10a0004030009110725011424858110b4002d0b80e580c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 351838561 1250 351837311 351837319
    0x408010f15050120010e011d01060f05090c220801180206040e0c130602011b0206090c010f0e090907090c091208070204020408030c1c05093a060b01120b 67
    0x10750b103407400550b80242c000d400a04d200070101300198000609001d41c0020b0480c040c000a084007100c000000701d40c000e907400030150390500100300704a003009202d80d0705540d4111001015612030301d10b01e00303042c40368030085030741c90319070902e80044c07186888008821115500002d21921036981c0c0a00c100c50080d80c4029403160090106000d03000014240ca6444100c8100042c50604a018003d105600e83d51142005039192072440010800701300c52650151080c0c0014007403800c00485142c2c50724040264941000240c4501406a41c89110124991007024000048900341030501079207440d854080d400d0818205480191441e02c550001411100031300020440b80165a80784001640400d809036070142d024440800d204d54144000c00c24511481e000342030302042e01c804010040c00f425210000d03c4414084244552507039207105590900d201c4111411140d81110203c20403140c0780d04074082950103170224100034465002e0300d42600c0980390010402e9040100500740d441300d4200d50f0304 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 351839811 1250 351838561 351838601
    0x1050a030b1308040302090127060605120606091c120509010c170702060d0e010b010206060607080c0708070806090118030c0201030506210c01090806070c0b09030408070b0408010f 79
    0x218201c2c01d0402004103116214091400e40c0da600001d015140a80002124040c00300d000e0341c1d00c4031481600203500c14400c0301801600e2031302c64050014000c0303590055203103900e4800503e90f40c8e580320407a17036a00c000412040d0a80c43c02c4000c0d519040c0d03c0002117907540607030323010080540d010724241c9450782da0507526903540010540d10444421015642440c08a505002c003000603079403000075086503c04040001030240c0d595800720f003036941a10800341035400c0242407040f5902c401c003c03a0403282c2c212950566807001300001518210b81681b1001290050000c04544403201181081c0241e4508000b13118903291044c0710400e401d00c1d10001000b14031407a00780c40055010b6040385a219400900300c41c03442d401c0c0200205440320840d604115500701d00008022507800281e0342010b0002c071001809245440b00300581031039188a80a800329444500241007924200210f4003c2c0c00044184c0e0005a80c03858922455002402524a65407c240c0001c4a0003110300c10024007464885010030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 351841061 1250 351839811 351839821
    0x6150632070302161413060501050d150905010603020306130b0906010f111f111206190803130e01080c1e011101060803032d010608060d02030a0507050901050a030b 72
    0x110076889441c040302580204410116030b4110401c64900511501080d00c11464100c400c00154441342e00b4198043c80c5018010b00460364040e05071040c13400d05100c00034005400800c0440708504a6000c0e1660900f01000859500d80c0f42e0050344c0566815038049010104000c0c116041e50519658503070001311481c000b485942c130070b000c540f10583c61170400601b0810b60303580c4941400d400c284082e201d800d061040341001c0003503216080c4618031044281c0c1c02c110201d0b00e0107403100350142c1214851b40018464003020b07001a145000104160310450380d8440700404000e000e0001ba11541c00740c3c11014000040b45800030401c400d094500500c25581031030b0031044c9184800298000c00c1c108069814900c610940902c2020060b010780e02c0195124608181c01c46101500c00b03041084140b100e80c10045124004501241500c0c102d007000d01d100d1f03580ca8081421904000c1000e07606210b00070030101841070204c0c0d048166641501c0389000c03070303803280c042c000611164031004000040f03440c0020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 351842311 1250 351841061 351841157
    0x60904030804200d14061b0313020a05031b0321030a0f111611010c03090303140d14060f0f0a0e04080409091407060e0d020913061506 59
    0x2101c81001c15038900c1c10f032440b0501190048800345801ca0700108980b440c0c04000c04100445c96002584c90041c9120b0482c0c00c00700f08041c000a0484424016500c00d071000f1541c4070400c5101811010301100c11407558580341d81f0000c05903100407030180c01400c20101544242c140c0e0481c03844e00d80b811080ca19201c030f99915004010300e80720700034980da0f581010795140245070010461199148041c0d004401d4904204100c41405c840c80e034144948140681c0009410480a00c1103c0d09814100107012856003200313028861000c20ba240189030040303560020310090300035401a0015241c10140c03452040a000300300160b84400c540c8440103c10810880000f004c025900030710032000c2604050340c0f40c600340180d40340f04104903400a040403c580020208200729002800b00b89086820f0080307090105641021140e400390141e00d44900103010420842c4649101303d41c0243e081110b005541a01a0b0800c0c40d40500070009001c0210810211846484010000d89801c0c40070b1003910250400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 351843561 1250 351842311 351842333
    0x11130914130f020306090a021309020d080304170a050a020c0a0f180603050616020609061902030a0216060f0c080c0f090114070c0311030615040c020c0d110405060904030804 76
    0xc0b1500b01c0b0070070251006881c00d028440c00b03411034400804601c5810b10401c004100b0b641814000d880c40c0610395800360f95018059448260822860f550729104c50610200020351401c0d864010280010304c1b0700d58591160041416500319403e40e6070507039602040100503200e03131041074003619845000303000c0032031014150138901d00b05440c0020303c1c0e503a0399070f81814543c048139000b82007043c51401c260501c2e01405440e510401680c0034080724580702003410121a94100484441680400021580d421550407a5070b9003500d80800d0500946926100c0094030285440ca40d64030704010003102a2030003050160b01855120201034145031a801040c08140c01840c456810495180d260094400c409402007412a0103081c003049941d045040074003030503000300c0680b030003540010f0802c02403021589031411141402c82e4041600e11241ca0200c2c6007881c503c04031507020041e6289a400c001124500000c82a8251420302040e40c42008000e0501400c41d005800b1400c0e40700010300240c824814 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 351844811 1250 351843561 351843563
    0x303020d0f0609020d1d060408030402010e030f010c0906030c020705040f090f0606030204060b070203060f040326160302040b1c090f061a060901090512030403061113091413 76
    0x10006907815450722490680340d80ba840426040e03800111451030100c1800b41d0380d51181d81c1c070307a00e504048064224a90f1120b00620181c6000000700105045a03c204211428401c004085804180030100824001c0c6104051440843d13086840029614028010341c10544504d8001d0b25250340340001340400751240c2c02e89054100c3c0d07a441d486002034510302444907014010343c800200d40d070952043c0022202240c0104003282000d011140040e6000a141548105221400392079070301d44d80f40a45404c2d042a400c041103680032035103040c06080c50f68190b446040c80310100042d010044d023080d000c0344079600400014136803c02108412019400c05141b82c030040c6d00340044d0004071625003e07000e4640303240c200c0c0d0b482d850300b403191107006012009182400341203d00501e081d00000018003480c42c14419240580c0c00c000801d04500018010b40c0c0013150402410f01221400c0c680011040e444541441d4050f503602a000c02c002e4000c0c0f00300180a130307000710030740f01c00d450346000c0f500c0703074900040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 351846061 1250 351844811 351844837
    0x9011d0910020a09081209130c11011107050105011e150507170c0607032d020702061b24060f1f091d0c040308030705070506071701170604030302 64
    0x4084042003000d8070040c0f1288045507202080c050400d07903000d0a003444204060b02e01c00c070902120b800380d9a019600c250511700d071480041c10100d070860a031040d260741c0170b0b20784e03c1d5481c02c0030201001d03440308003c1c202c8900c80e00c0200030b640e8903a440c040040b4910105440d1240744402c1c24030442d16a074004040c28202c1d420b0590511800e940ca141a00c00401c001071015040403410349480c42041110350b8024129003402e00024210180c10032803010481060415210303816845603c842680d03044130741054010b40103699030a000000b04400d10035120508030320303104130416240c5d0486020444d900481001044c0100c030344410381005006442846003c1d402114034450898401e4060003110310510962100d09155242c0050103001503c8402400311051446d010801b002c0702d450121001d49500c4649142c503600d86030001c490500589000034410f1040c4401c2c4914981c20555400c00a000221144800d0703803200e4812a0304500010f813441c2c96442a8080b40000c1d001c3d401421300e4503c6c83d5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 351847311 1250 351846061 351846073
    0x3061611120313030e0904120806040609020d1b0c200a1212081e0f1017070503010516020a11030f031c200f0306190605030702010b09011d09 62
    0x35540481541c026582c594403244083c02d07030000c040d00b240c04981c40d0340f0101d80d0450207181030345400d4101d400c0c90640c101044480b00011350243d49550198000d4550003004648500c52440901c00030540c020010b08006001200700014500c00c486045042d0b900200503c0b40510002c4403401e11f05d00404050342c0300185050218940d06c018544090340c50140c585070b0b00e0001307110300c05050040081c1100e040074100c03c20ba006a4084503d00b60340100d059040d41500d0b50310b50032142200d20300c5410181c00c042d0301c080e182e02601000140f18041c2d4104400801064440200010308482c03002c40d002d0150b00704406000200b100b00b02c802c4c00506015003a201300300b5202c1038450440d80b141c0c062040e84070240c1880043d4070002c5c0310b10541220485204071003204042071076031b0305003d07403004814075260020020301e2944401c00402406404040500390154a820000d043c0d60411215000103600e40041580a80b6090641d141200c0045c2004901c0d21078043c4030450106004026035005e106103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 351848561 1250 351847311 351847333
    0xc0f08040e0f06090705090303121302030109050d0f0302120612100c030e070e0403050418110a0e1309020f150c0a0302070e0c0f0d090f1703011403061611 68
    0x201d0822441420041c1c2c000b0054a000030401ca025400a409002008030510401c40161000000c4804800d4103440361074603903440025020f100820050000d406500b040c58010401000141c854400a642c2c0c80d6000644103404084040380510720310f00c5580c00382c3d64042001c5051010720134038402c88000a880003e0080110309040d103603c1400c5100003a5145840c01f010a810312005014003010000c412242c201501c00410b00d005a0148401d002d14003503512003051324130340c0284400c01c121344442d40c13541203018001e0300c813401032001b10f8000e040c8400d20140541130707803081007109039006000211040c0c4010038052140d10307036540310001d001d042282c42c841e14007c1084608562203640100300c2107080ca5a003031508980680b418502103c140110154800d440741034135406007503103c4c005141c01450034003140320004464041c1404a00d1f045074010004500b000794140c0340311911142e01c1c615075405140d620501200d034491041010340703012250901ca6081501440904002ca840ca141c41e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 351849811 1250 351848561 351848579
    0x22d030106320306040f110a1b0203060105013f0e0a0b0f0601050d09290405060f0c1c0606030b011701030b0606090a0e04020306060a26030d06090209090a0902010c0f0804 75
    0x303d103400098a480102e008e5404c1d5510130480b0042500c030140200c0240015404a503840c070045c002c0d641440712440340c400d0749403851070300c14821081c4107814505802102402541016a40700d800600c1410300e44c0406d20500001a84a00540d1007901311140303070341d03002d44a074403480058940390421508011220faa01110b020b4400c1c0c090082e00e80c0092002c08604224000204030f1120179006540c80422000c61000f10301e00740d020420000380b5086030b580d000100814800c1422100c0c900c0059520b00281d6031590344a00c041d61100d0f10200083c0108000540b0151403464809104000040052000a0030b0b034002079088500038000d181829400340018201d00c0080d0400141145050100029407800308203003504a41c065600801040c103041e010104103a0f03030f4401c0605450b414a014910b0a000c10847d000c80e000a00c08100c03d90700c0d00c0c241d1003e94400d0318490320401c9140d02043c469141031140d2408554141c40e05000b009803965480100c903c90740003030300e8042d000c0c48001000ea070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 351851061 1250 351849811 351849821
    0x91508061e13020d0b190803030a0c180602160f0b04061101060b0a08042f0f0102070906141302030105010507120c0206030a0504060c020619022d030106320306040f 72
    0x150075100481c05c05100c00038007180d024003100618860081c8402000214404000c5a401406101000c00c241e2200d04050343c551950600f9042d410050003c002040c0782e006c100c010303041074031b8641d1b0500780b6901c080d5070045400341c0c0070b18134141804000c1004518060300301c0c0f19141140314008660240c0d15051004d0fa5008140c059002c200351400708420062402500200d030401c020207064814418007082c0007851100507041d01a4108503101d0b80107a00800c100c0e801058240410711485450b150501540700010f21054040c0300250210781c4e141c4040c1c02500d06840043c1d6540c0e080641944901144109000e00c260500130391140c40e00250f200c1c403004600c10040004080750f2070900b840c0c03841c112800070380f28800315023119050200503900194030700a4045100e10260b00c0f4422103071035160000888103052091a80202030384a507510050281d4100d078203a032117031000080401c4c409804408034111104204110070a11050b564154003d1500101c02500014440034030008000c00c81e4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 351852311 1250 351851061 351851077
    0x2109010e030a0c090c110a030503130204140408090f1e090c040801141909030c110f060412060b0a060509150f031302042409020f1207091508061e1302 66
    0x10b5281ea4003c1709031030f0880040c01002070b01c94010020607829440041146c04050114800c690001600c202507544a80090b00d11303d10180c91200700d4142440c040b822640078100040c0510000c100000292601d01c950072441914048035013040c034080c204000107400c0c010b00d84401200140008561042c00f440381e00c90342d5503009090282810502c1c02100040070180d0800ca4450500180c0b40c00281d100c100b20021030341c0200a040b00d40c400303c1c00207d45d025460480341d0040700100300049c000030000820f0b003240e4001e08003008030003404814841000d40700e002d400c01150b0308112540c083d0412000c910540101c2d8410641409004070f6007192562042d646031829040032110b100030b5140512a209103800c020040c401d1441000601e41400720301c80c0300d006040e41d404101440342041c400d04440c0c4038145000502e020345400c0c5c1c0094401040d50046980742d1105032403401d80c05019800290161000802040000940e0011098411044242c1640201001c5a840300440c1e141c0003800100d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 351853561 1250 351852311 351852329
    0xa050a0308040b01050a0602100e0717010b150702150309030d060303080f0f012315210a050c090f0a0f0906030b090a0c12061503142109010e030a0c 65
    0x350600e82040241c183d07060300454803ea030311050800034950006595584440010400f0803c589003624003030400c40701d503001200702000c2c80c0134900c0584040d40607442c8000201e070004100603001c160005140201e000c0290400340000c6240c0300404c10300003442d03019500100b00d034980760721059618256002c0d98400c6010528000501403030141d050300300c43e445003c100303034030703590798508421218a2502812030381141c42020824444a40380c80240c03050030030040030b40d2943c480c501040307040c014076040d0000720468050303404500c801c00c403801501d00440300681401c0c10210781008200003007541c40c41140c0e010f4015040000c1c000781144840004010290000030103504d141442d031800e400c02030a10780941c0200b00c1801c0061284404181070f2034803401400c0700703806c552030030500030070410040302004100e450300082040905030100820000c0311090300e0740048072a030480d5510f0009494510f10340700901002c80755500c10900704200748401021585220382c035803500351403240542c00c031101c6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 351854811 1250 351853561 351853577
    0x30c090d1202010507080412050705030c070e16020604030207140f10111b030d0809070e1906080c0a27050a0b040e0f07061d10110601060e09010504020c0a050a03 71
    0x2d0302841620b074000c25600f48944940307080da648072108612110f000040c07180104520003407000410035130301300d11041d00440385d10546a800f540f4549030100c074030f002e1201059000e03412403880410690b00950740740e001000114142040c00c081c00c400449a5600401d002600300c04540e42c403820001400c040b40c4404610207549400319013007403121300c0940c224404002c40c1d078440741c60015038031080c2c0055181c40702e09a02c17190b66072401c001e0b01c0d600001c4828130300d200340001404014104094074401c2c2c20f08108040c0e444d080350741c81d07508110750113500c1aa40b4008000c2018000d070440300d04100c0a2244505030340d0049000100d810540741c85201c01e88e42e910004e0130b070805126071040b141400c1c0040a00c808100d41e0160782e4a01e50148000300310218a01103407080500280c01200c81c00200071045d0405000d0004107030103100d00e201c0c132152107a00000940c540c0220b01c007a00c03011019160024582c00c100030b100180d40070040521390f902c91000c061001c45c00c01c3c4203921145103c0e1b50340200c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 351856061 1250 351854811 351854843
    0xa081e04030c150204051806060415020d02240a090203070504111201060801180b191e21021c0b0405060711030f2a0303010603020406110f030f030c090d 67
    0x100c01015001401d1113481044140015512030382ca030070700c440300c80c800e40c807540d038407080400c40360f0141c0c1d8080d603c42e560b8566400400303600800d008035080c40d0340e07080700e110b00500f5421080760300d0303400078440009600394046a0101c2c2c00e508502a89400602203840b1195500c001c681100d1000315403910401021490009242400d40c2c06401400a0710b0800100e5042825052803001c496007107081c0300341d8522132440c081e2140750f03201040444c3d005089007069a0b8000c03092006107400e4045200225103030020408000111700c08020007207107080d000300c0940c6582030156458807001208030510124071004001140d10718005e00c074030b2254015003a21708003081d0140c40220209401036090300140042c68a00702c000d4151340c6100302a800204245e08003002840c0f070100c130140807550a0000000108015416800a0049840703683e15001c1c0c2c19030031444291100700c1e00c0301c595130baa0001c12094240541410242d074120b0002c444051510315620f0009400c56491101110f1000e41204150 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 351857311 1250 351856061 351856073
    0xb0301110909010b1308011406120106030302120f0909070306050111191203021210061103030c030403080c2104021003140403111509070509090f030a081e04030c 71
    0x1a03400146015414107040c07151000581d0000140142e414034039010a075050740395034502400f03008000c440700820000000f07180b47e01c03002000b1952a805a5039103030144c0803202051080c9000c03a60190702605681c0307107080c03800f800c0750320481001d0b412810030b10500003565246011680144182e440c001412881c2c10005410f195503014041090380004540d038034020700c01c0c1011110183e21203034801d80050800001d4009002e41100f510482032100d0800940d500d60303c2550007610842e840e54507200c0310040b0300030350320302c81181c100005c40c0d81030000c540003c0c0900e458940000000304035500340304454100b1244022080d0010f000710200c103040c001941007170f41c0c000d000f221062905008071030203004215908107014000404111007040075900ca0002403050040c20b4420411100d02824150403581d612103003800350501c947e0a020204842e8070f030014060020708210000366003091048101620400402071081c005410109039048000e42e00b0600ea9120310710035250291200b034541050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 351858561 1250 351857311 351857321
    0xe060112020406170c131b080a0b03011109040f0e03070b040b070914010c11060d020316030203100306150504020c030309012708030604020f03100303080705040f030b040201030912030b0301 83
    0x44030000b1402c540c20782e05804182c802d0751380c0007500c154410101d517018040080081a40101101b0341f04010102504d50158016008400700403090240e0000720041500300d40901401d044004410480c2c080e0070706042d00008002042c0c40c80014000800078901360450303000d10070440d00c94074000108000c20200c04516500300041349460300c0c1c11801c0001064000500c10042410f01c031780707901b0364400c01c0125038580f4000003000d042030303445000440d8500080e41068601060200300d02000350b004c40d00c20710030b41f4400e41502c6510f121042c6183c071898001d12401251800460b848000401d541c1c03542e0004007200e8076031308000c6030f0368640400520b007116944480030801400940d01000421302d21f600401c4000d030810300b501c4d0303640c03100400200240b01b907502c9500980b801008005000e050511200d040306e000b504c50146e02d030341c3d9103412112449a401403210f00002410b0500c04035440b400e0741c590051042c180007a800603140c442d902e22a540f8100c81001a48850f20384406040130300607 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 351859811 1250 351858561 351858569
    0x1b0415080d0203121b04060c06060504020a0f081b03011a21150a08061b07021009030209010b120411030a020a081f1b0f140403060b04050c07030806060d0e060112020406 74
    0x100b0005032217400782015a84154811001040741461b040e030140145540040001e10004208542da03601151010342112806001c20001c10122000035095410380d059010025034484181840c6a08207103034100f0300302014401060600c42848810728031190f00071454a15040310600300042d02e020b2411000d64940f00d1007441c05124070300e0b0200980c240009081d90811a401030707203010509905055440c0c5c0c003800001a41c440036a014030a00290070810200640c1e00a449078082a030721894501380511805544220300c0c0c0c58140007401107940e64115402102c00202518030303104540d000207070211503e41012400c3d80044440c1c01c081d042003404403550211403502440074138048054036008000b151190024070984c03000d104ca420740300700044a503403103c0700c00f00368070b0340d031030f41070007402007490414140c0214078010200301c2c1e410300d440c10b450143ea03040d50340340380c180e1340c0700309210716508100148000c5030340711980c8804c503c00921545010b043c0a021074500e4854038010481a50001d41c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 351861061 1250 351859811 351859831
    0xb0403060b013e0a060903110a080d2003190f0e070306050c1306050c070b180d020f06070f20010f0f0c060c05030907081b0415080d020312 61
    0x181c00510141c00141003010140b0030314407208041c00e2070f10303100d080d4002d00c5107030180900d403200740802c400307588a0101c8034001c6c2c4d42c0e0303040000c203408001c1c0e403040c4213040074000b0b0344140945d100a68058000c0d540d412000c680c40d240782612500e083d201030700103a4150341c040c1c045410540303a0342c10031f102d001380c00c0c041600180010303507a0b24841e6403150028000940021f84507400918020240c3d42220124800701f07007a04011981c4a0004141d03405c00e00c0044840e0080b840c0002d9002c40078016215109154851400c03208918002c0100207450108100e800101000d2403c40c00d60f11900500715042c085d140112429142d40340015514140c00d20f0a062802d8201d440d0381d03913903401a213510014041c0c4c280081c4410300c95800750707500d20407000003c7c07400b4103008400f0072032540310b4081c1d0f024912100c100c5924507180d1141c6601d501c0b00b4001c11b4540d0012141501080c581500450030002d4110380c50b0031100d81b104286070401d003011946e1005a03000049406454a010366900da200c08052 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 351862311 1250 351861061 351861077
    0x3040f05040510031208100f050109171006080d0306210308070309060f0b090711060a020906070b0106090f0f05031b01030e0a0b180102090f010c050a05070b0403060b01 74
    0x400a04a0441180030309801140d4403000200311480d005600400b075604110741140000030400001d200110403195450400c0341142e0000d9096141031849060300c405854034030380305081025800c86401c42512107800741c4511030100b881da544a20030030024102d4500035000c26004480080c0a844a643c4048000060b01c03d841e814042c1d010140400305505280c030341c0480c4c44501c021000340401e10f1001d042c46180460464000c0680d50080305124426542a01c0b10380d907401041d609426642403807101c1d600700e0f20014980344050340c000c000041000b800c2c2d45c240003968440050b0300409811140203c1e8481600380a020306a184601c01000d02d54100d44001c1d00301030110340c0300c0c41c0003004010301c105102100807091303010303401440070700403000c0444401e200e4a0801c000740d1601070b03510360f40900e03581006420080e8180201c0f4040c1d80080c2610748980522801103e01480c0c444041d603050160556810000300305000030402064014891501c407429410540101c441c542007481c1400f2481d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 351863561 1250 351862311 351862319
    0xe0f0307030807021608030415030c230714010c020c06070f03030506220b010809070e04020d0203031908010f0603230a0b04230901050603070e091207060f0e0304 71
    0x10840349000e600d4a0404015280c01405a1500546500d40300700040f12101c089107102e4000040d1044503654040c0301011071903040d0580c01c8440000311000060a40303009000c01c0d00107600c500200a0015004518003140c070b03201c0364600b10450080003266515500072010455040103261b040c10f40407100d55113080f20513030f41d2000d03c1380c06200003020300d03407500001030890303407031a08030307601a054644040c041040c001101c0e001081e00d44540d50115461102044074008005070400603a907441d010080240c85617020002020740b210000c0340e142c03004010104c03141e228034078070080c440010740b00c0d84920750500c582e590f0240081e401240403d403900c0a01c00c0302c0310141050510b0100e01d06000740c2a80c5603946510040c000031424142c0260505540841c0f014003903011078076002c080004d1a10704e844c2c03002414283c6030162032a40c7d2650100905110112505e241160407445240440350482840c0550f0310068002c0d5605803806550f419840440701c0d0390b4042c96900c00c0303001018500c0c042c10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 351864811 1250 351863561 351863563
    0x121b070b10080a0503131a0301060311040b040605091305061309060e0d080f0a11030c0a0207050415030b01080706051209010204050a03030519020d0f0c170d050103140c0f060306030c10030608010e0f 87
    0x10500c141e2b0704060301c0c0c00004140300c000500300d8019210750b500340d07565940c44440c081c00d5130340f00510550103291140360608400585104850082c038001b441d5224070002d0901400242c10511400c1c0d03012582c6101b080100c1c4400c000c020212000e940300d0300000e1a080c10940a11540245010312990411054158070340300700080300d500c46416411240ca4911100080746040780c40d4010300e4202d40740145c9061402604800e00040303074411030808455a8a92401039150700007403140c0c0c0d0100300184400c1c802c9a0742c07100481d500980c501c000508055841e000100e22002980c800e4002c200009003500140301645030081d140d9095000410302582e60b00030041c10480c10030424820404030440d54800c0158000003c2e40b15004207281c680c440f03005211a40091900f840708884440a103c540c4c8030360080850700f002e078500018882d211140c0b15000784003090f8002400c16038940078011001c501aa11440310b00455415a50001034141c01d10307008030f00b158483c0c4d8440240f43d00c038600c4008000c2c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 351866061 1250 351864811 351864817
    0xf0310210f140c1809160b120711030a0f030b0103050622060f0b040503010b09130b060409021314090c0d06090305041a121b070b10080a0503131a 64
    0x6846005032424004481c00c2500700314002c0708899104400c413040c606030a03078850b0024020420f020583e20841d4510b2280040740c1d40074410b207001d402c8244003a817502107800340700c00e0b4801000e0074034854102c4000903290965214030b0822021440b002e4102511a50511074200c00b100207080412050809100044415088019008888441c03003d0000d0990071904203400511400080c030034016100c00c600d4200780c10a0140d00d0081d881c1c102e4a00461411a40090150b0503291990601c0091078a0b010761014000304800c0c1c1180c1c441440c1d400588418ac682c0e50039a40b16140010049003041246c805c010019010440303540c0980c500100580c0e0f01011940102c0c3d00490000d56207804c4d00e0300703541a015942c0000450036100d510031800211800052410510300900301080e03680307090803280080100c41d8858044281400f200300015a44028681c00074408020390030f003240d480120900c0d000704107501302c80d150404243d503040c0380e4411f08808040c00c840b42034510491118400030744180 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 351867311 1250 351866061 351866063
    0x30f0415090b090924180417041a0c0717030304060e1b0402030a090218040b07031a060d0e030a030b120105150105180306130b0a0c0f140f0310210f 65
    0x1078401d2078070204610300c0000c105c6001400190b4042a050b41c585421381049800b99407820360300b4085c4509030402c3e0300b100d06850a540b4038034055903480503502269000745081c1640d82c414808007241401a4a041490010009009507543d2900740313448403e03600c95024090f0154081110010003c0404000c0ca00c0440c00340c400507125581c0b0301d00c460241c106120046d42149034040d2441c2032000681c1c0c2d03148941d024900c0a010390b15031000c21030071134016405010350085400c07551f01003464130390020020000901800309004440d081c000b0304560000c1182c00110340c0d02c288003081070030b240c4081101010394800810041c545020740841000346984440e040102c0043c0314004001001c0340580c58050140444000349403001101c1c15401001005031074601c036802c00108a4105402500b8a14806a5848407002c00038442940c2c00c03290114203c00d600d03030074088040321202140c0550703c50342954103149401c078034040300c5030703000c9400d8001e0144c0340c0c4480001d2004207501006020b551 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 351868561 1250 351867311 351867331
    0xc02010b031506010e1c08040312020c0306060d15062402030906040603050916090c08063001060801111e21040809040c090311180117030f0415090b0909 67
    0x8191a0360011b00d901c2003400103002500822021241030140c24006001900e1162100b04a0125078040907644c9003c85011194941e000a0001d252800d00e0034894050300d1040103000300c06402020444280d031455000f0410010070b03800c0c3c50a00d056005102c3d440c10760f0314000b9600d07045404005c59071034400c5018002c00e00da122000710b9624801000191034140c501d8800d4040035880d8009803000d00f83c000c80180001f400c82c0302180c00d40c0b4022152000ca41c1064030703011f2600202c0c601c030300d5040c400c0c500c2c0d29800395603e4400042c14002070041600c24203000046075540c99007806c040c5c10003030001c5102642e12505000010744013078201050f4510003045d4078139682d541e0792850503165502c41c000c00c3c550014180540464025004031820302030300d205500818110440b8428003001144500310322100028050040000030040112801a038041405492610030380d42c520041c1d90b4000d900211441c40b42101d0000100e61000c00800036000b080280d92030140e4000001c0c102c0342000e0b101c4100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 351869811 1250 351868561 351868577
    0x10510020c030a082205060304030c06180f170a08150d0206180f041b030f0e030307050406020706030203010302060a0503090a02190609080f0d180506030a0c02010b03150601 76
    0x1046000700064007807804020200c49046015107014a4a5000b142d000c2035000ca0a11030882c58079681140141540d0024103410b04560b29603d04503500858110300b695620ba4824000385281a0740e5007843c540c601508040c2580003551408002900300d01c4c2041c3d290100911010754032640c006940764202420755452015a003103500020108200301600941c84480001c50130381e000303184031440300c003842c04a0b240c0315003021950502c41580c1d041c4000c0840c480b0585008160360b40640e01503503e03403d0407d00010001c08080f40c152a6620694100010600103c1c04014681d81089401c010346034074507080d403c40d495907000c1140d5000e180c0c3d1010510602200280015408000701e500c50394004181d81e050b556418016100c90586000b01c0000910307000c0c020809250024440f02000204c000420f0040c080720400c54a40250400301c403007101d10032178006034039984c0da4042c41c020f020401002440180c58a000390031101c52403800c0d8002d800c0b204055200b40110038405a1002080c280850 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 351871061 1250 351869811 351869839
    0x110c0309031506210f072606010303050901031a040903020a0b070f0912050f010f0b12011802040513060207030306061d0a060e03010e011103010e240f0103020c0d020c13020a080105 79
    0x801c0c4124840c4048403481b130b0381d100240048204044c0c82e0081e03907020044040022140c01303030351541c80034000540821810410f1048551207035020400703075010240c4004140186100003015a0306500007580182e1000c800c15041c490081c8840d0b030009074506080000502e88c1101a014445901c00d01c0d1305488520001014043e050200c41100028a0020420f4500e0b40b0784071802452039076000e50091441c02c0561101880511800141030882c10780051080c0d030550801001c0d01e00145041c02c206480390304ca0307000074582e0010b0b00b4114480d0b2004941d4605080c002841034442841400b02c00013408540205901e03007921404c10384000e483c1c02c5031100c5950b40842e01500c81c80030b100c41c00350320389401104080006005141a54071180d1412450b8940ea40100342094030000790080f0720002d0408541c0900e0040101d410400041c100541810826000603041000742c40360900980c010700c00c02611407604958040108103007410440c141030041d88000c11071001405014020498403c4102c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 351872311 1250 351871061 351871063
    0x2070b010909210e01050a09051207090e07050a05100309020904030e03010f0209060a0f0201061a18040c0f030b04090b040f14010e15061207030c090c030204030f1203110c030903150621 81
    0x1034049d200160140c60700800c8500f28a54a20b030034072928146510f4000511030200000ca0218101e0b14000c01100480d8108810031400603c0c034880e03c07080c580c0d07401d5081c1c01038481c10005840b0318047c1e2034480ca10b00301c500a060a44440c030703144001003441003204983ca5030714081511191645460b0402007640041d105900500150300500002020f041c04140300d00702d410700824502e400d8861544000e041d200c288000e840402e00290040391050000d0a20350348a0341c0702c0c425985c070042010800181036100d11108800a48041d00c0e005100d15040041c01901c2206c641c0c28480700c0000c00c88504001041900c40c11b150b07011413920304584021a0b05079840c0130f11041c855800b0400c4d40d5002c0c3d6207181c12400c142d01c910803000303540e040101c0000d40901a10980303080700e0704407040d0489940d00390b469601c03411031101a03205060384c6140c401140050a400741171003003210f1008650f222034800803d8600500e100c0d541c03180c0c0f0040801c01c80c440e02c4132885121856803491941c1400c1c081c401c00700d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 351873561 1250 351872311 351872327
    0x305161208161e02031015050d151b020f071a0901020705030102030703020a0f0f020307121b0308071b080904090822062d08060402070b010909210e01050a 68
    0xa0110305401d03840f0400c80202548074024140708808641600c0010070482056410540d100c409140c89660100f01a00b400b00105c04024851001c13079030b08400400c00c000031100c07070165015205842692a02c609a010442d400302d0344044c40080800a2030000c3e014040c22071400c2030065401d002c543c88466900810654018090050003075469140c0000014002e40081d98554009140740e00c20074020b600032034091702e40b401c40b5030203546000c11984034101c0e4000800307052810855801d80008141e000c074210000300c107100780d0f100405420180d0307004004650480345040c800004802c04400519220b040f00e940e02020b48000c100d080d141d00f005c204a0103840c50104821258101c1403000c0000c001c4844156265a140c60701c1c042e40b081c1c0071b46a100d4060100801c01400d5000f1320401500608a084e80010f00910140c074000c070301d6840c081e00034001e03440030b500661030388841c5080000002900c004040c1c4803d040b1541000200c00400f0320f51081982410700c800000ca40201c0c0c1c0c030420345 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 351874811 1250 351873561 351873563
    0x17100209040f0221060108071e0c02060a1d0303092413030506010305011b0e0409050304120b090c030a0503180d060504080703121b110f1501030516120816 68
    0x2085496451a210240b820b41c0b44180c10213001c01c2d5030001817065070107038542d94040d00459454030312041e003108268501d04040c240350f40c00e000c03000301c1e141c0c010ba60301c0c1c0082800b545640e030780320081d10f868201c03126a10f0181e0300c070603c643c009011989042d140c01c0a403c01e040300701c68180700140c220b0403c02203036114560440d4914200344101009002c80006d038281241e20510003005120712280700310020040005040c0006124006298502c0c9010340140328010300501c01d407803078169980e031051034100c440ca8003155032541001c20021a10018005110301e40d81c190701400385501103079110390300d0344203031403035601c90441ea460714680c1511107d641c0c200c5558071241c204031030f080030b09003010650001d42c81100010701180d50b64401c0207990095490821081c050b243d032902c0d1210092b60810b04e0902260254401d00008030b0180400704426440048465943c1c0120750550505504000318803c0f00d0641118110023003110501086054003042e811051194603034030110200c1c00f0740078100350 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 351876061 1250 351874811 351874841
    0x509041112090d08060603060d060c2d08090309030307140c19090c0c0803131104090f031103030f01060c060b090703051e04020306010e06010c0611030106091710020904 74
    0x10069103041c0002e009088034101d131202c0c07941d40c2c3d60b03004000c003030310086a009802c210707040851000105142c0242802010358240b955190070006541c0421000a12140003002c1000040240050304100200d070880f54800185140080c0316001c03964910a40c10020481c1a001e0340d8100e4048091000104402000385401d010301c00079507000f0740c11207590240b0f0350303001e1030800d082203160b000c0c2240400c09a4045400d90a590722018105001100b140050b21100c041c4a0952441e6136244280e0205501c40c030b8520040b1060b90034014130225681001c0004d650080043c4609032054030300d0513044910502c0c2c00700c40000c0c940b42c10000350081260f0650001c28030070034030881c1e6070150409441a51000c240086810f007540c3c040383e0800e801d4a010707401d81c00690040c85141003ca006503403000041c10482ca0b0400306035200f504640c05031117003010540010005100859200c070b1f8502c01002c0d4070a40c0e1450030400c10107540c40c1c4160b039000300009039001590007800d84440e00f1218004075140c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 351877311 1250 351876061 351876097
    0x90402210a031e0c030c02060a0c08130e0c27060408100506091003020a051e030a03030203040302010c050a1d130c0302041a04080709090f0206040b18030d05090411 72
    0x2140241c00c080000f204140d10300c1d0094490142d252054007a0155590569a9100310320502c2d003d00c012903025002940400c12046400c8012599100060150002c80c1400003101c3d1b25240c00f1a0803408094030500c509102004401c201d20344520034080b0f80f40500002c0c1c2c034078295810004c2c0e050303c902e5100ba43e803809010004289080c10741d011a01c1480305844450165440c07040d41c04080b02c05000c001c0d442a1008400e00440c188203408540054407000c60000503154070b0002880c3c8003000c071b81103000a40001c01c000c1016828000e21282c400d1030708249040440091019000220f45451010314600510301d59005685158007441e917800c8101e01001195203985009001c0c1d0b000b0301481036403402c0301040302c1e1420b001c40200c408849099020b461210b081c0640c190107804081d10a071055082036450700c3c05079a500c03000380010458210074940e18403074200401104800b60310581c2c8690898030382207840035044070444603d0681200c00281000c200282039201740100c4003400781243c010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 351878561 1250 351877311 351877313
    0xf1302100c02040b0f0d1401021b0601060f0903110603073605090103080415090918150608060a0b0d06050702070501020610150302070510090c2102090402210a 70
    0x11864007088280255024000c83c0003407000d005d82c1e07400da90503460300700c0003240c032802c080b502d510001d6120003035810001d864264030544d64070401c039080e4208510354000000410000e600584048407043d2281040012140303546c4400107802c0700d01c038141d80a04070000000f110544510207010511803c100301d0782c10b0030a0341d0060400542014016401d40026160129546ca0300399140740c102c80d8031200786481d06051001000e4030b040d0520151041c028518000f0031004002d02900c020b41c4200c0c800c418420405003000900345088e05000054a4941001409601c001142242e403205408230089100b101d41000728074006100100500454984002e0069059012030036000701d903004da00711051900c030071440e05074100d428070030103c1c00200d881d00c05680b180281c001c3c1124034001c3c001d4522205481842d502560100d000455088008540038070501000c0c03d040e0307a441041501c0e2103682d00b000d5000c2104a000500007a00c130b503003920800c1c0ca104081c04000300d90f60b2080010740c5c14035421 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 351879811 1250 351878561 351878567
    0x1051608070b010321030b0d020409140109060f0506010e0f010f0e060313061b090521030a080a150810050c040b040b070c090b2218030908010c08040b0f130210 70
    0x8803007410004c1d02140b03941202c51754881d00551004500040a11605101c9582048000e0840c924111f0b91400c0c0030040c500300403001e02c102402c1ca801400040f421890304c000440440b40020925030502c00c00c103021140c603894101c241c0d010441700b824024080700c441d8070183c0d05e07290300c080c049600640010400085000d5000e01c449868803444040c00030300d0090a800c074000030980c0c6c890f40090340703035002080035280900111aa419072041845101041003108030308540c042e0344450049059a81884a00312440c03142500090f440c000c40f12440d03090940c1e064460000c49103242c0000c1d03e9a001c031300e4000040c800c44008050140c000d980d2aa0340e0420341e1006d030080d0340d06964440e548103000540d44914061740f501c044000780107103520740c040304642c940c15821154051103603903507401c0b40070340c1d0300d1103040041c40d14007076110344403030394681140282524082e40340384080000b02414000003c0b800049a42c2112000c11107600594507865619004880040c01a40c030600e4400c402c00c545070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 351881061 1250 351879811 351879833
    0x60a090c03020d060b0903060a020a05071202010504020a090c0e0607020a0506070f061415060d150f0503010e03090d02130e010609290f0409021915110c01051608070b0103 75
    0xc0c3d41d0105008007966030f036020b01580101080703039406401020019076120a02da00410840340d0500b041803c1100036112210503039003020003000540c0d5900248415480c020400400910300b584043c00383d8000d540000348180d011046042c0207000c04115601190384801600c4081c003009800e1036100c14941c1404142000d201d401544d105143c81032501c2c121808540040c8a0000301904050304408241800415408000b280306083d984101d022483d200c0101da402c000c05120070051580d608020402d07084403900c56001d902688100000c8459454030400c01076402e4040351203518429894034420040c0c0082090300140c0c0d407034031402242554841e48800c042d441c48a482d01d8030b480c280c0194014182c0c1c0c0015441c1c0c00310307560b58100424a03081d0403c500940c400b8042854031580600e030075a501c1400e8000584a00300302e203a40e608580d000201000742c804a0000b804c1d0703245c0900000c2c04901c01c4058052441e10071950090501c1201022110716a900111045440d07a403800c150a80e42 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 351882311 1250 351881061 351881077
    0x114030f0f0c070c06050901050d0507050315030604050d0c1703070306090b01020c0307140d0501111809070c082a0d03050a060303121802030d05030915040317060a090c0302 76
    0x41d100c04081002100d00000355006640e01203400c038041801e100c1c040c2d5140d0820070300c03d0f040146c01c02030000c0312282d501500317000310f000f9103419440e1304001c0b500000803a00500800c0c040c0c2d20950801c4081038001900c0b00e4007504604240100784500c1c102032030030404010b160088000c0000901c2444d613413507804070701240c50215003000100c400200480c0c07240400071344254190300c00702e01400035481e182500b61102c100186040d5200c102e560b20a400d480903504465442040402c02c403c80c1c2e00f0303d101640c6030707030000c0b10341090310710300030340068464041802c02403c000804509117020b1582c480c001507040c000040c004002600010310a030350390150f1a1100c000a0505010074028559802074034207681d40b45e260000d4003200e08441a00911540b501003288400c4408d401c80561001e10242e03910036150341e12a542c030314000c2074044c036006507200c0b560400885481007001290323100c0b1b07101d00a02c400c00c0f04540749440701d00001c1c04181091300324115a0f4600507440140070380550082040b6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 351883561 1250 351882311 351882331
    0x3040605150628050c031b010b04060e041a0601050a0c0c12080a0314150618090c0d0b09040803040303050411150a030f1505120106180e010b19140114030f 68
    0x400400c8400300d130f40d8083c0c0d01c00c03030b803203075200f40042440200c2060f200a6210f0152000140e600c481100160585d0896406000350000c41c034140010703c082c00e540d004807001940301c641264101140000c00038482c0c2e0448004001418103954100010302c24640001d0013410041c4074440303a18101061035071b005084030004203183c078905128a075107004101d845541c051003a40d0204500070f06100d04c130307031200200c402c0244480300d400711150f0310b0340c41060189040182007612200c054007601e0454a503051054410030b1100d007008005544031003240d500580c0362801160341e442d42c0c64603082d04103420702a56800080f4202100715180d000018080200c1190b5003440140100c1140004680000c1252003e0040b20101400603050070380301072400e210710500000300e13281e566410595000c03c18041d00b0841c4d464030b1000700f200b0800d02941600540483d803c18046e400b54407100d2140d01d51f0300c01c14180c5080e88000b50003a070700a1000e03480d070039181c1c0481070340c0f0b00d0304004001c03020381c0464071b02c529 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 351884811 1250 351883561 351883627
    0x103060816120f0c17060907080718060e09060103202202070506010611070906080703120219051c180911070b1801050702060c0f03060f03030a02010b0a0603020c03030406051506 78
    0x1f00e5030002a1303140c08c542059000d800c0d114140111030506010a45110b146030792036038070010b0315a00c42940302c0d04c54443d0030042c0c612541585011070500c4035100360000c21104203d400c2140b5980c0f00c81ca42c00000c441d0054060103810300744c2070406801800005041c070f0003a00c0000926036000000314201c1e80d500400d449841d619140c000c01281c0d03690007100e469500091041c400224440d40c43d0322200440d0040780c03100b80b40300f0030516010080210844e900e4000c6007190246412407400313041000b4940c00d022a40301d0700c00d2030b4000d000c0c0543c4a4a1030039500d44c0643d08404200e0300844244a80103c0b0342c02d09840c00c0e0000141e0303a405040f03c2c0009610385000522014030208000780580b9103c944103140c08450038030525150800751160358030030001d00070709019580c01c100034103079500e1030380011881d5282c00b0208020351046034041c1060600400070310301003090201c00c4030381c020f601c000d000549807500c96102e1104e1550a8060f900000c000078607003d00f1110030500ea030300342c10000880c80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 351886061 1250 351884811 351884821
    0xc0706030501080304061e0207050d11100822060f091407050a080d03090204110415080601091a0c0a0c0f0e280507111b0103060816120f0c1706 63
    0x1990348030717600c07401d0009801140a212007510386c0d11190520a030398070403100e18680b140001a401d5412041c03c440078800140c0c03646150402b00c41103d46145d09061880d1146090143e4414800950b6140d042d5070a8031a21a0308000595000b0354035155002e00410505281e85046500303212450980c902e18803441030002401d151202116040d5546080907005501c440703501900501100d01c422680103880b222182800e84d203001c05400200850000c02103c8400503030080c09240c0d0240c01103040040c0450140a400340e2008000311503071114000075a0303006496021420640c0e500d030000e02c0384500e60700000e0b403c51026030400980380c14141140e83d07500c400036000f80380c1101c20101c8000d5413101ca49410b010241d540f01c030b9804942820302f02d0016501410160900c07000340c01007400e03140c1c440d042103401c1d40c5c14400e000180107000014070340c4000e81c9022820310b0240307200d40d0b01030112903850700007000904800b107080140e0100c4a40303412038682200c020b02c0418040300e902d107031040c1b01c0000c07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 351887311 1250 351886061 351886063
    0xf163605150112112203081c0b0a0b0301051e030d090510020c0f10020c0d051608120304080a09031505010914040c060806060f03041a060109151d060c070603050108 72
    0x119401c1003442d51851700d6031a903240b50071861408240d01d00d07803000f030f440080456149402030a9000850f00c041c031041980c0c071503510849012925180c0100a0300c2e80c2800301c10140d6080f0ba0559204030348032042c40c4440030131442044680010107805000348105204080e80080003901900d03400c0fa01c2c4034094404103001c0340c0e02e4501342400e0b03600401c90070b001d545e01e041000b200d004550542c410754154140d14004941410f11020088401368001d010b9000600c6c42c1011060260005902070302082e2107000010b54a030002500c00741240f04001781c42c07099a400361081800079a8881002d11074902c6461100009003401d200d1002031034100b600440011080c3d083c0188281d0f03108040350702d0b01d420304600300d8030724000038452900114200282080c001191000c4c5100354030a8829580c100c80d6004c0c40030501d50b003d00b00c0d905210340482c0520603c88984200f1410414034030304134109480d400c0c0d0341c880c13802c880042c02c0d422070341c00140aa29881c0103c6c0640030346500345c500744440d90741c9400c19 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 351888561 1250 351887311 351887321
    0x709080d020309060715050f04170711041503020a0f0305010605060a0210270807210c0b040203100507020c0a050a06140f040e01080f163605150112 65
    0x200c001604100310141040ca0590003601c54503004411480459441c450728108954064405d05a0305a018003008200301c40c0c164026240006040300318141503d50352101c5075a40d00d01c00d00c1e48120344071100841c07000025540e241c000c6400800720340c10340f03170380c0c2d81403100c42c204600099403907500308040410282801c0c822124000b0059000b04000c11110340442d0041065070100c0940c5440c1903c0152a891200d038030b100b08a0040700b050b5561ba03403520740182c2c103845d4840207072151940054200c0e240e640181088a01a8100040d14440e40d52440006e04103080768100c04641860b141c20b00a1071a80000c41d41d03903035003066030842c1c5103641700c40400c01d0761070b0280b1420000a29a2401c0a0248598000ba100c0600000c194a040903110802d180e44034000344c000390300c00e92006003d60340b10030742000700702901c0c40400284040380782030008101c0b420410b8400c840340c04440100302d10901e11b910410071802e01125408001ca402c041d80010f0b00a504803803018005a03103000f069100500b03034494 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 351889811 1250 351888561 351888583
    0x90607120e15030403030515130606081509041e080703081e040c090e01151e060305130f0503160308090c090f0106030b150f0301050111030a090b0d2003070908 70
    0x5107500f541d9442d0f50440140400918244440040d95031401090311a000038100112480c640803a1050801c0c00041110100901028030345442d24442011070703c0c0c2295168005801080d0301c50703d0307101c85104400801e00300500400b0004000740120074181e0244985001c4c01caa94422840d91013901465150281d00351000303440d0101c90710003040848960f0780041e07102c070028000882d103010304c2c038aa181c0c40031607640101e0100b10000750641c0c42c0710342c0e644010301402140c2030030806802c3c5514200d100400c0c610300100210b001035443d00900c141003080c1c4845801504440d810003503207150040c6500c3c802d94440c4020f109111510b101441d00045580c0b09060740300302919140e28108040b800f4208220156030004550307007080809120f40b8008121116140e2181ea690354036040004040301940380042001d40c10030f100c21540107030b010100354210368694610b280c075582092403600c011300b8040c0d102141506142c4041c280e45414030050f5202c0c030620303150b410001e942c902049486240d1300c04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 351891061 1250 351889811 351889849
    0x30b0a0e090c090a0902031203090606012d0e0409050c010906053c040b121005010e0f1207080c09160219030909022802030414090c090607120e 63
    0x1800e4107042c184210f481d507000d140c0400c086a50f08240c1c000c80c0c00e00d8403020100c01508000401c10202600c01c10130150460fa0a00c1c000c04c480081460740341090002c50205000900c203225010840c40c070a010101281000402c20480482149801d90b42c900c044a5028003040e6000000614a0b019006840e580d00948940c1d01c0c2c01403049a04081c90803120006480032170311034400c202e581c18004050030103000c40e400c845513200340001f0990201440145810321281d10000c061240341d0340300b42e04450340300c2e00f038450205007400c4200051026205c13003240045442290700000e9400000190301000302c5003610901010346864060000c230844000d03070360000d0792000c0c111401203021401200c9415001740307800c01d40d0b075072a03c40e400107a0380b040c0b01d084690f05c040c0945108800034200c241040d189240011840e2a02d4011080100c00464007070500c07403401c038000a5000400b240856220384801040f0703030744c1c550382840c0c48910002c0d180b006d08006059050b0300d000d141442800012281688030f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 351892311 1250 351891061 351891073
    0xd091a0403110301180b0f09070303090b0c07051023040b0724020301030308071e0f1b0803010306020715091104050402040906060303050319060506030601111203010303030b0a0e09 79
    0x82c450712403028214402d00d40540d40c54a840b4101405400c40c00d00d00d6100e0540d10703045040041105c0da0302c2c2c030050303c45455030f0407102041002942280400c01190421b40c1025106c900007100d403030038082198442a0482090400d0b15450f545c40700021580c905101d8180d08400e5613607030700300d00501450003a80c1c6a68810004d19010803000b43e8004015002c1030768030b015500310300030800142c0c1c1081e0300844c04600103505011115401c090302002e03010b540c40031003040d103903101e500402642c0c480c040c06042c080003249000340459020441840e01c1d821030b090701d0b41c1c1c0d41e50b480c0c01d000070340c01100c060f0b5503032034042c0311406030606900402c02195000502c001e007000d128002c11004101c0a0b00817079100c0d507501c1a20f030005041c1d0280c04010740c0a501c6a80c0c4a14050031854022003034141449a00351400d2028843d9903100c00640390024000c0ca0400894401c1c0d8091603d0b28280b40d80001c180c11011000204040d41030704000400802a900c200c417899484028466550080d6640702d2260010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 351893561 1250 351892311 351892313
    0x20d020d120906300e030409020c060a06050405240109091e060602030406090317040819060f0213030807030507080d02030402030c0901030809010c060b0a06020a020301061e090c03020d020a020d091a0403 89
    0x16410002c0c0201420040d41d01d8a588c1e5040c44003282c0c004481c0848030b0300302408100b660300042c46000010441941c043c400f6203044072130048134046100c142e01184054102e101c0144c0d10401101c00500030100c82005040904503000049641e1102e0410b540750500d00f004c070f141440801920b089807581c0e00d0303900301641903071b0303400000e554800945e1a50038000d000c00988403000b0400204c003402c031101001260415401c0c030805450320f56101c14129030042002180d071590084a02c4200c0750041209529490980b0b000c5a80b88620517010b400050041480400c030f0155034000c6014910031002c030344000d0340e401c041c00380c41031007480082c0480740c0500c1600c60a5000703a9a410b6298070440340040e0590040e40016104842600800010fa010500d01c0046060074401e20010b0010311300242d08941040700000d140e1000d034000c0d180c1c0e05407118119280c60380a07405440f081014070000b9910b680038a00003e5036402d20044200004c2c1d50a00b000412680f0100621a00e40c88000c2c00d40c500750031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 351894811 1250 351893561 351893657
    0x1b09081509210904140c1b010e070303020f06010509010f140103060e2e05090714070b0106050a02010c080f07140d050a1b05090d020d020d120906 64
    0x1d00038140340c0203044210100ca0900c00214021414a4014945610500301408100c4d080c18a40c2910440d051003031000f180600c00580e0184610071040c0350045203c100c0c824050b2002c40c0f1504120b2040c0e0f0f0001c01095004907400c04d42e90910002c440543e0380e21410040e81d50f4083c0b20350803891180003000e000c581541d124054900b0410704000c251140c0d0342d49015184402164030091403808005421041180c0d02e9580b0f076003103000c14254442c2401c0100050301004003401280c10302200428554032140080244c0d03a021fa042070f0f0801c013540e901c04000d007956100c03d000400551829410a0b0900d01640c1164000d00200fa12800c0307550781c07500305555030400120a03511041051081c02400c1c480ca014045c8030f486e01d91400304000c00d24455400ca03081d01503620a06101d001d100300e85007521801c0d0b203100c101350121864202c1b034803075002140c000301752000043e00780e41482001503400c58015942d0012200d41e81d039054007100921100055040c1c000c180305100281080c203070499980 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 351896061 1250 351894811 351894853
    0x61311010e01020c0a060e03070f0e070804170f12091605120703050f0f1212060915041b1101060e1605040b03160f2615030d02011b0908 60
    0x407041c0100d90810104000040c04c88256a00800000d04110f07900d14060a0901c28940148070421010171241d040144011a0703002c010003a1080281c09000581803118045038840001002e00c0c840d40d4620b80398000300301035401040c0e111000900c4070045a02c070a8006600f01800e184d4400c10720342641486c040280c404410009106540b0501401002180741804042480842d801c01407020016201c100d5050503140440091050400d200107008541c00d8605141d0204080303940240300e90b101c455502d10207600780802a0800d16080c041c1d403043c0040c3c461041245065114410100344100c550703400c1e00c460340200a03c80500340c0101d44c0b02000341030003540d0609181040c0d41030a4807541840c00c160022900200f1441d1200c80c0c0c0110681c0000350300400c1144d40c0341c501c101e502d04102c544204a444081c1c20010100c060000765600303440d03442400030086c0101a1003005024032802800303000004040e1603e00c1c0c0c801c504010450007036030070004a9400002810320b08400e200640300c026 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 351897311 1250 351896061 351896087
    0xe031c02030c0d02160801022a0109060f051b040f0605030c04081f06090c0c1101020c03160515030403020c0112060503030a0807020610081209011b060c0206131101 72
    0x7100c144448044842d061003940c421400c0c6500401c0c1c000d40040c80c2071100040d591145506034410000c1d1034940c030820810840d00c910503c6034050601e0340e42d05542c01440d8104000d00114502071100c3e0381d2907000e4000501802c100c1c2c20803501c01241481c118690321551059901081d240401002000d00900142d40d016102559050601d680c1d20b0145003440100705c0e5900d00640300011020503060540302d5400a803079652010002c21034480c82c0030304400703000c40000d88908a00c4032a000c0360381c400c1050709112580602903c44210740020340c0040c2100754000c2520600160501410300103040301aa44650340540c0241100c4000310010b40c1e0714600140514a480c0d180e0300702240a0300c041000b00314200031942c820f0701c1c41c600850b00a042078005001c40c0c0c0b08419185041101003c002410070b412548941070954968031040103035900303120b40c05810495a00b000321b8106101e12503000184544441d000d0b10140c1c1d5414888204180d854480204455051558481035510902442501c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 351898561 1250 351897311 351897313
    0x21c1a0d1e03020109020310060f0501110f1b01020d0e0f0d0f12050d05071701030803220602070204151a0a030e010203040b06030d0504060507060b0d080c0c010806010e031c02 77
    0x40c00701e580c9040745000c8954026000350b91107103904003c50030200070301441520468070800c61907007400e100451402c503074030440e07040012501d8103004c1c40000384100201c1d1030104084a40f080c218a141c84041c200784107241d400342c000d012400c103005018400750500340d20700412060185500000300928880892410740d01404c544505800081c007072050103001d0011b64071429140d0300544092010360b140207001d40c0c01c002c0c00c40b00071020804500c0402c4e05496010348c25685079070f104180014800c55021205003c003c68003032010900c10a50300420015000340c80910100307111281428400010b44a41c400340b04099003120b2000c01c0036405429100c006280200f055041c034005642660000d49003541e00000782c40900c1001c1c50200040c007018031644c100b007410a4508070015104e80250308010308516116000e1103190b0f80c07400f03500064241c2c48580f117611002d0000c400d0741d0750140c1c0302e2aa40480c02d6000400c8081d800b400140c00801070043c0103109a856165102001034042d00300b0400b5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 351899811 1250 351898561 351898583
    0x414300c030d0603020a2106110903011104050405010b09060406030b040b040c260c070b04050f061303020c010201050c1606110d020d0506040b030d2601030303021c1a0d 74
    0x14040c001031601c00700d502d1000c220303141540104204441d040c0c0c010006000e54401110ba407680002c0c01002c050340282c0c1c001450300515844552034411b031445103505528000c01c5240e601c41010280c016608203a5040003582e0329000c1110141c480c02882690040c1d0501c010080203101340c020360f000080143c00868a0400c030804202600c4028601a0204190701c1c40d2005443c940c11703400c0f82100c01030030401854140001002c05078400d000024202c182d0140c0051f00b4004100100d030001f0700000300b2100545001c2c50b0700060100b241a0403401030182032103e124540c4140256030040d0a404011450701b04641c21442c0c0e0526010004c454168840010316140d41402001d000661500800903903968610b80c0000126070300240454400c071319004680f07015840c0080e0034010b4a403241440e00340d45903001e01010b0030524400c0e1003003990031030b040080101a81500079040c0030a128007517000d440d20690320513050303a2508403809001c0441c0c0b02440c03a10b16043c0020010340d801021300d009 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 351901061 1250 351899811 351899827
    0x10806130501150b03041a0c040b070c0803030f09060f060a0501120b120c030c030105041713090f060504050906063a0c0312170604091a0f041430 64
    0x8403074a420344c031030490301d0804000c02083c024031100001c1000200407441480b4549000c01103003a0045000e2049424000700d80301c82008107a1050901400b040b01c1140e07221b1409001e000d00c41a01103032030141502035000401c0340119000c4000340148001441035418904040044400701c2c80c184120b01c9050b01c0340314100c1152164a540d01000c0b90500282030041c42c42c9003414607004c003280b02503000368948400c002c0800c140700800000d0100e1b142c03403a0340d45c0090b50781481c0614900c0d0400c40449113014400c102841d0540c0c000400c48205032400c1c0f125903922800c0743d07106c02c4c0450b0315580100d440c0c10039005544030252561070038443d400002001100810552100d201c1d0301d80221501024503605000703000c460b0800440b64031080c601034014004150945120004c090880c6015a444484903030421050102c055103010360003150316102c0c9002d8141110005080e1010350310041440103117900024086103c40842580c02d5542060080409003d65160143c441d0040c2c49901401208 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 351902311 1250 351901061 351901091
    0x40e0705070b10031b0f0510020a0c06030212180d0c0203120c0105011a090a060c1109040b1605030c04120206040b04030503030106110a0c090c03150f0e0f010806130501 74
    0x5800f882d1009035010620341503103441403410410484c84980740c4500c0d401040305d9643c00d41c03184107a41c0203a4010110300301c0b0b044140d240c00a1294000d000000014004c200158154080d200c2801c00720010441d60315150004c0c06480d901c00c103d013985403c03110b811200f843c0210040d581c083e2018003101ca824101160b2143c00e80c001400300b40e03103039440b00c0c0104850100c02018104042e000d000461405016000103100c000c9140f0a440278046003402d0ba20501030082d0340c10084050107081503c0601c0c00c0d24210b0350a160860306a200303030250b078640b032101034425400c0e20300c140c0281c03c90601d8681803803020021040680812030b4000410800400c284d001d54014100640c0708800540c0c995041c41d00c05064940300c00403030a1b241c0d01082c46040030400104070201218403c5d0310001c1e600001c8041140a41940c8001a50000401500094400c0c0124450342210f0740d621140041c0d403034808001e803400c42c080c0f1456905506c50004a03c00b00c03582145012200d124900000d80c6010120b103034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 351903561 1250 351902311 351902333
    0x110a140a0302150c0d023a0506040506010f080702011503030e310207110319170f0a050306030f07080d0f11060a0b19140f0907080f0c072406120305040e070507 70
    0x7d142e00c8100703040c59440b140440d008407074003d43c0031101440340d03140c9600000c024802d40d500d0b0f84200610b0002103009076000794061042c4803014011100460780340c0c18041c082010002160b40160200e00c0c0d8003080c132200c8428044054020180310840280705410b034000f81d003126400382c80440c603810000c0038a07038041044031006050403000d0900c144c090b040c09501c0741c180c80e14004e0341d00f07410414911152122800c5500c000040e05241d6120b8440750007103403070145205000c104c6445215008694204005010551410385079a26000b242e0100021a4404803020080c1c1c0a9030240003c16007406070341d00007085140014203003424210b40c1c017026020841d110340c0003880c028600300071030f0303038900f8601c400d105410750070b4680010a041010005040c0300380140010580078107100800e0006050b1000c0b60741290704941d03a20b0460142d0701070041310034450030194881c186020300c0003900c00c030441c114295203a05502c401d4181071400c0180c120f4508024180c00030000100b000d07000003803004d070304 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 351904811 1250 351903561 351903637
    0xf16050904050f0a06230402070606080322090207020618180a020d0c0f08070e01090b071110090806010b0304060213060e0925110a140a0302150c0d02 66
    0x14083e1a414000c00c1032040300e41395000400761614094003200b150b408a003201c2100741c07040d0b80040e40c0d50286d0030000014600c079009445d0500000520b501050b8118290500845451101d420f40d5a900c1d60800704900ca044802900400103020700e6803041d602e88070002035900c0242c004000742c40f0000e482c03400d45608072809003090b0f6000c40c0540105c00148541c128250050074000b01803038160380041c08003071004104a0802038240d40700b4540b0b900c600f002c0ca00a01504401c0740d01c43e192031130200c0c442900c120340301d406034003102400f002103880384d01190f0440f600c030340c00b9240513400c0c4000440d0300d502c01841070720480d8003009449004031030000144014003085d035642c1007400000d4200102e081014207154009408800d071081c0882c41004c900d01c03880a18284514540e0f20410031909200b103501c0c021704143c404544105001c04007044001110b8465800c2da480783c50075492501d218a026a088246030405000d00100d140c02e44e8010716010301c0c0f404002d802c06602030581400700465444c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 351906061 1250 351904811 351904831
    0x530030d060503190803060411180f090106081609080a081207080603060c0c250807060309030e0d0203010b1f030f06210c091b14030f1605090405 64
    0x16840442490301e20500016220483c05040c008100e103691021405121401401002d0004041522560380364040000c0600010b06146c442c00b000781945026102d0708481ea0107a55045550032007460010b150070b05130b0700952920b40746a264a104610402101a54102400181c2c4d1000c10550300030480029020b01c2448015590040695962070161002d0721400600c0030b040c062001990703011400d16800b0b410b0341c1700b440d282c4502158003868111200c0c00151701c0e650b600082d00405010107400400e6900c00004c032550700c1e03605c800440031209400300180c00901a80f8001c15185800e1120b0390155000800114032003446200044440070407800450907640b51440d0741b5041c641500070350741d481003040307420400b0b0391800b4109020800c4554002d80740d0f0b03545803010310030003201c0608000541800301c0e0801030306040c441405800248241540046501c1030340f03a80b03d0710000003c49114180c65002d0300d402d5180da6204420755152180b0400c140f14040c00703000c4107501c45200f402d1240113011 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 351907311 1250 351906061 351906067
    0x17040b180a120912030e0111010908040b07020108180d08150301020307120614090a0507050f1204022e0e03120a020303061804030c1106070c031101031a010207053003 73
    0x281c2d01904084071544009901301c212240d141c0482d4000c01c0d0415014801e0811384000044a103940b401414041e5000740000c0c0045804140c011501001d403090a00c00c8e260050140c445854100d400d01e84403854120751ba010585000341d0f00c0c4501d40013900100c0c5130060807000d0000500081c00c1e0380044420100244680d243c0c205036401902407540200b05d4000c040d010351443d10041400d90000600f01052a5100c001190100703204c3c404031115003506041840e211200c200c06400143d5041e10305038460b0521700c02040504040700482448a40c028180003856a24004192420061241402d605004440d00616821751000090070a020540d01540c0e0340c0c9080802c02c8103140007110440f840e50354072020840020b4010350034220700c5421030f6034504504485000500d0610610100520b60085800c0000800c0301301303804015100d409032070030b111581c106c0400c01c00d003000000d20380380103078459001000281012070348a642d5004601c0324043c56521203880c05060304c18072516182582c000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 351908561 1250 351907311 351907343
    0x2d06051e0a0e070e030c10090603110903030a0c120e090f06030a020303031005130e03030612070305070b030a0b030a080910020a06050c19080118021602031204090c17040b180a 77
    0x5206c0d03a889080e003291200045410000300030300c007009600498040c99910009001a00d1418003a5048418001d003101d680786601c071001000481c1c3c0710f0381100c80c0401005036400c030340d000e134017180141e62000d0b107141c000b9611a41040c598080c06031180d82c042c0641800c0e100581c9040c8021841a240c03144003800e20b42c500740510600543d06848008068500000b003028000c02200b180c1d04540c08580c59107035030fa000e600c3c0a04145076540010f020f44100d4400264141040c0c015500c905079242003044a81421400c0c541ca4a11040f001029143d0411008005103444207844110304c2d80d610407115400219910300c000c4450544621540d11000f0800040c00d094030040020b48035141d140c0704006500d0310200d080801d00761404c0c00d04480d00420300c11040c1112980360706845030018115500001d203480000c0d65540540507403120306040a000d2912140290252040d960500c0707080780d00b03950b590b25114901040545207613140f000740001d02e07041c034408115208049000d01c0c6694180c0d011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 351909811 1250 351908561 351908563
    0x50d0614150c0a060b150a020601050a050d030c061107080301140f0a032006071208091905060a0906020c03030f1009090f120e042d06051e0a0e070e03 66
    0x903072107a400c0310754204803424040d2404200c08412607440344020400314003801c006004020040320400001c1008500c81e908144d0000c1e00d6070480d00c040d5000114540c54105204000b03c100074003030082140c10341c0e032000081079a442402054220706c0900d0400500c0d640324185503201b03074803c00000119681c200143c0ca005450100d0a400031200d20f802c0518540d19200d0b4418600303008039210030f0210720300d01135454103411071301820b070320000c2c2d03050003c40404050003200701a2004d00803480b03412020035a50400b1202c1c0c02c18030350080001e125035035549090740003400c011541110115000d024211009104201641c00f586180c40b2011b11845e199903003102c286410b5011082c00c1d03007424243c4010502c01c60819003000d400c03145501080460007820b4800003a0040d00b16003141c036100780c107880302d100d032220025264441e510340d14058204050b581c05682c0360f4050a940035910030704c8139555082101c56090400005008119000d646032650000c01408035111710208088400314a4503141c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 351911061 1250 351909811 351909829
    0x30105060f031e01090206030106020d11010e030904051009050f0a0506060f09060a090e1302121615020a02031504050f010c1e031808040f15020319050d0614 69
    0x6840045401034aa80080d40e2a00300000040303543e5007441481c00160740a41101042c2c903000f604561752540e641074000d5072596040c144a0000c0ca000140f1100c900d41805480780c4004450001c40c105034003a0200001020060009d280e82d119010340040e00c41039a00071039110368114006498079180440c041015110010561071041d0402c20880c0d01d4210800152801e0700001d0301c00b59180c012110042d83d8441c00c03a042948e200200c0410011302015009103001e0710f03032007039405114040507400040d550780d8101e51048408000e9610a200d51003000409000d80b0300740b07104650385100700e600803d041007040041d40c1e039038800c00010441440402c10106900a03941d038000c00c0400c01c520300041034001e181d58182503444a20000f0080940b203030308088510000106801c452200c1d81c5801401a400303481401c842d80d41e094000078025102840c02c0c80e000380c454001c0d40c039042d41800b2016a00344181042c0081c08000c0c4092400d0030300b640710f0403018040407800302d03040c130744800e00300300d0011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 351912311 1250 351911061 351911071
    0xf04420b1c0203060c0a030f050405060106020d0306032126071403040b04030503090c04060b03160c0b0105130f2d0908071707021009050405100b070b0c130f0302030105 74
    0xc8a05800740c00103032000030700254403000c00d04805440d1040400103c01034200220414211810a0180b0003405008603860b4100c41d665001c940070702d15200e03030581c241d982c030f48805002c2500342c18941d09080809a82d0380b0143c50946002c1f8420b000300039120002d035402008004400300c68400700034125410414180000340d0920f04241145080c1e96502c00403d00200005d00b005000700200d0340036001000a0070220074001c200341b1100e904c1e94100c0905400803540000c034180220807080c00c09001d1455111415082804001540c1c2403400380004080400541c3c0c0c80d05a540481c5004060540308020807101414546150000150100c06100380351041140c011440e10150070001a24082102c038204ea00c0038210f04640f02084031210305000341c5d8006500b003039410000d030580307907840181c040568004039010081515078140040381c1034070b24050415500700400568001c954036250090740881c20841d9245000c90807200d4410409c40c5900c40c1c0e040200844c410300441c0303007e001d09036000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 351913561 1250 351912311 351912349
    0x30f010e1e0613051903021b040501050a1703040909051f0608100b0409050303180d020d080708040c080d17181c020709020f0a080f04420b 61
    0x50800507501c15200d0381d0140c000d40b50115502103079010807409001c0940c4698071450b000700f1184050170069140e4001070030000b0300b00300444800e001494644600340c181c44010305800d4525044c80040404040000e02ca40014842403000054228450040d81400e901c50406030400803c41c40e00c2e401c2c2190400d0410f0b0015080100a00540d00b000400b219141c00010012900540d2035002c50700500318200042c0c5a40000810050083e031050040c2d51106820705c01c88401102c0d101d8201e132184140c1042c50000340041c00800d541c54411001a9049401400c1c0d030a4096540c102442c604170b458400e00300407411a05110030810f81601c3d1090348804022203020020b00782e030b010580c83c0c3d0240d5040c00780030076003940d13103821407882003201708050301151608643e80c1561400c0382c0c01a411003960034001441d031100113003071880010340103402682e0101d03598141e014024805030303113031412003106042814105005031003c480000202c2c40e01c0706c01a0f0000764901e04a051000e604880e56400c101c0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 351914811 1250 351913561 351913603
    0x6050910030b1b040e01060903120503091b0f09010306050a0b150405090c25060c0c030c021e1504060905090708150d020d060e1b0906061602030f010e 66
    0xb081e00303505501c1d4049208140000c0307000801280000070300a0f60040d40002d02c1440c008250a41c01c103c02c2c1043c0c074003401d611800a00c403920100c803684400c032114040c60304151300d6600407509000c0c04101d40e40004080c1542985c064000c074803000b00c00da00036925142c0f24020700c0075481040c8501d120010702902c0d020003c1c030348000220002e100f51710605028859180006940142d41c805031002c4ac206200c1908580920b041d4404110954040955400f480c0210407400c15000b481c0f00b00c0c117103a040d19400da0650641d020003540e130345c0102c684600103024505d00403290703482c0198441e28082c0111010b464a040600c0141010703800e8000c140200060000d00c242c00c0d40210203d0b9001c030900100d5500110f03080e01154419444040c000c0d001603c41c0036040800c1070344c1d0425032450b41e0220032505100604141008248212912075400c8010304010880340d00b071010040000250700304051850302c01550109240200321503501031280d5641d24124090342003445404404440080c502003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 351916061 1250 351914811 351914813
    0x1b01120b030c1306121a070819090311030d020403050c0102060c0f0d09170d0c090513321b0715091b0605040608060d0f030f0302040503060a0605091003 67
    0x90303541c40044410f07102d010b0350142c4100f40c0589411001c041d20760b01140c403403088980e1921404d000400986a61100e41d030a000405d0075100d044014481c1c581280c2d0440f07096141005ca034003c00e00741d0416020403a480a100c80e105008000415a400103000c0040e519891401c000c2d00b4100070781c0705141190401000d1252003e440c500350b800c401c90400450360b40c0d00507080311000a00b41820001d00164044e100045240000e001400320220016010302a050802c00c0448409240340a06030384107903118040ca18132241356020443d03030031803202c00440040300115098144007682c48141300b41c83c2c50400300300d02c2d240d40743c0c81b1891000e0b0100809041c07408582d83c1b900d85101c0c2c1c8100c40000e9070b50354002002c1c8589001c0000040f034200c5e9604080c151a008002c00320b6019008442c007144000300800c03601d0a2100903280542d401c0b00c403c085140c0f00e80d4007143c0d01602c1e10f0901e82050780038400403c0503035080c4038490099104881c0090685e15101c02d02241d003c00078101d241001e90040204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 351917311 1250 351916061 351916063
    0x60c020706140406230d06060509040c030618110c2d071d130b070e1c0f14030c16030308060904050601030303051b070c0806011502150703020403051b01120b03 70
    0x2c1d5a24405203140e17110780040d104000c0d541c041d0060207440c05043c03020000b261364120b0004c09030100b0a48060101d413a8945040e000d1791210f00c83c1d00d081d920000a610b12880c0d0540c1300c03454424480343d07040d10308030280328036070702d04004200262b01b9050402c00e82041d10508500042a040c1545c0c050024241380c40c001d40c45080d0304007001c2d011140d03000001100c180d8201c00440718030341e220301d0b103411604104900a11101c080300401c1e0060881140d10b1100300c2c10141c5c0144a954010302442c048461540c034102c105c075218840800078441400048002d003401e002c06030701c242955444804251540c200200b001d07202400550041e1004028000403500106071981984d0701414040303040c0c1c66039520340c45849240c0040507500742020415030204009100e0813021902030703d080790307150b98842c9a2411000244001603015a01c003180700036000ca1189400340d4007810b00d090040c100760b0b4079191b039414440c01003c3c80d01c0d04440700d56075403210341c0c0103402c10102c0c52013034608000c08003080d4086 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 351918561 1250 351917311 351917327
    0x3011508071b03050f0d1a030c060f090f030613050d031e0b06090a0807081c09060809030f03180706020111040b1c021303110609010c1e060c020706140406 68
    0x800d0380350071002d18241c00c0c580a0b404407004409075040c41c0359280811031002d40104040707951a039900600300000714181c5000160503c8011000b000c0c3d40c940044141500141c0d0b00030078000c1d4012690b502e4085403550305010103071083c9000881082d20203028640241800e0400d00301d00e00307051034090a04003210500c4a14404005403240020f580440c40c00021418040c01101c0c0c0e1b40249841404201c1460101d24041121540811220b0b5200880c3c107601c00c5022080113500018507a150400c8007600c0703101050741080c1a5806c0d0780ca48102904009002d501c2280c0b01c1c200c100c00e45101e008100410072010006040c03510003044610003000b81d0b011940b081e88155801c409001c0703120032956400c0022559200103880b0115603d652582000c1c0e011900c604c426660b10750722146285050030104100d50244005075100786171840b0716500d22459424000b00c2158000000122400069042c403401c9860101e580040c180e881c03900c1d00c0101040c030b281c1c11004c13880b08240310400c90b450b0458a2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 351919811 1250 351918561 351918587
    0x70807090302040914030c030903060a06050105030f1b0a0c1e0b150f030d0903020a0e090c090403020a1a0105030c0a03080901030c2a0b062d010c0605010b0301150807 73
    0x110b031415040c200400017109041088549000c0020107111100d800030082c510504150180d40705541c0c2c1c0040c180460b445403003800c1c0416010000260814480800c0c1d035400741c016000424582c07c2c81c0824503040d0008080080820504401d40302403042071500000d403c50108151691600e240c0da42440700c00b005081034008208a0607002042d68410b4200349030680040d080340c802d03210480000b800c5020744d1006034010074800d040450640c1042ca00c452092040b10000e1030248042d10030322000d030038001c0c400d03000c5004a9010000141c0c034540408190704152480b94015418a8101420482c010311218402c0309001010000190240159102802d003405c00007062405004240d80300224003480c403d60100300b8102c2d4010100400c1e003200703d20b004040400d143c1d9550803d00000b40070381e01d04c0f40d4814003113201640350016085040042c041d011303d00f102e010506a03a4070803c3e00c00a07004401004030110050060208010384680885a28074101c5c001d130401c00c0024188401d0b06007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 351921061 1250 351919811 351919819
    0x8030a0e2e0e03150c0406030e1908030403050f12090105060d1e020f03160e0c0702030a110f120102030a0c0f170a20090109140a06030518010504080c06070807090302 73
    0x1c06250380d941c3c1405200c1030600b0341c00045145241180c1c0c540074950082c010400441e1a101200c143c1610009048051005440300f444416403240c40c0c0e5100e40c0c0000708201e0401008210310724659010002601c4a03120b8903a48610301e0400e210241d003034800050049001d11111040344020440301a907901c000c61407400b03805240190350000c1641d0381e09542080c0c0e0035101d07249807036080d0540780c0e031500122040081035038180e0311101410001380c42070890207981588002c00100106002950001e080d03d0001c2110400051410118036080d0505035101040d175800702c204414150f040c02103407544402c07841e203101c000d5200c034400b42450a4080009040051900000321100ba8643c0700c1c0c00c65103610020005101c285620350304643d0300525615001a80741503002503425030a000064a88500074240300c209800c4c10350490080600404106850907008007003c0301c00000e118803400744e4003071a00a643c48103000703041c03803034560094104810000c1e040100000307241d00903000e000382c0f0b034111 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 351922311 1250 351921061 351921077
    0x3606030705070212120a11060601080709090b0d062f090d14010b0d06060302030c120d0e15030906042102070506030408070c1e06090b16030908030a0e2e 67
    0x8944c051412181ca40140807590000464403030b40d5400c860b4500d42508104101c070225590b05004648480040d5815404074099107000e01c42d03a40140c00009010601906101034058113403200300903900140c1c2840d404805d5100c0b00207450810300220003c010a08007070b2441d000c075003800700e0f000d4220300c0c2e0054080311a0040002801c1000c5d00685d101e408001c2c890a0382c0c00060402900500d003d00c0120310a05c0380841031144e50506076101d000d591040c0000c4d090300d0b01d00d43c0060392001244801c083e4482c40140c0004409034590b0065030044500303034000c24544c0303428580300020441c5a010f40c0000c07194101605045540015010309582c0d00b581e12a40b20344543c605101d00d1302507880014035040440b08049011103504030180c4000e000d82e101501403594540741503407004280e000706031b000c2008010078070361400e03003e04040140c5d02ca071400a00d0f1a070350b040020300f16001800044005504207010040030720703110780c050310407001e42c0000e02d070411030942d20b1403203482e1035081d0b04007402058 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 351923561 1250 351922311 351922339
    0x40f09180206160b010f050906040e06010314150c030601200316031106040515060a080703081303050d031b1d041e09051f090f0803090336060307050702 67
    0x56110f0500196003c50980010b5840d08442038015102e4050030380035031502c100103041c918060140358846a0540c0148c10700e0b900f586c583c00314009841400700000c3c4140205d14010802da08001445141101a06030303c81c11f01070001010f1164880d0f004100241c152640107a030480407040351007601d4a61a00c0c5e000043c02c0c9400d441082e1490304017000760180c40e041005011001c034803840c0c550f003201107501003030762083c0030049040c6040c0104041c551001c2014000108020010100664001009010140d50391780701460700d8a40900303040000c1c1c88a1a00c0c0c2082d120050010301c2140c9410301c030300b100c2180e00c00c4d0050401c0c014200340c8161303241c000d915540510008035954140c005541800081e0103420541e6807003034107244d2241e0030002c003500c41230b0000f028402c54046986c0f01d508110f000d01107807541c410a4001400c82030041c0020841401c540320700d070443c0600207440856808a401592070072500c1c0c4010f01c0609405004100100200c41d40d2140484403c20350440d1306c41110044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 351924811 1250 351923561 351923587
    0x7020307080d2d020703080f22050f03030412080a05070f0c0f020406080705090a0c050f03191b0201051602060703090c0e010b13140d02010e1f05040f09180206 70
    0xda031405a03c44140e045002611030b842c1c0081c29028001c1d1200c041c9901d030340f02c6200c04200121481c0141100716a0001c0e0813514031030841c101c2074007840c22920782400c84c1d0101415988107030780450b8040c0042d04040701c038a400c0454154031a1a8410400c454900040301403ca8403203510740008008502442c0c000704500080301100742c903009041084200d80f40c551881d6259141d014907441981d50f140015851001400f40f940d146049589050038080040b80b0340e0143e4001610b00e465900c4006480341c00311542d8422501c02c0c1541074180000304036114030103130031100007610798107805103000d1140b01404d03000150340750441050718002910002c0d5040100a0700d40d07a07049680c01c00341c00e0340001041982040030b040300c4181180c24105403a83d80c504a181c11074200c21140d0411000b44a0b00c02660040010007800880507294009000541c0d84000d100752400320307541d002c503d003c41c00340a8030a48801748030160141c3c032002c0100584c1164441154410107d00074845d00000034808a5094 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 351926061 1250 351924811 351924851
    0x4020d121107150e030a020609040c091707090c02031305090a061e05030c0a121502040902071202061e010e2707301106160305070b07020307080d 64
    0x20441640d803060740b901c400b6408681003903d900002440340c920204a443e01042410342d02d540200140d03c0c0c0400b007428003026103841c48080051059410001682006000023034604800d150094a002070800316064112441020318900315030003441600c1c3c40f604c0b100b21680580c0c01c12180170ba41940c6008611020b41655004640d980b100007451500c01d048000b0000f0544108400b50380013071b80204180b180d103610601c2041182d03828290b541c80440c0124000700340e00c131003001d070252601c0e440b000031005991003c4821142c00804000795000f8560510500d5001100c40ea624021300800c2c3c0c03e0440086410301404815252103004100e101c152844207260360302e0000980c0f0f101d260b2100100c1d850300e45620813602e000c5a00b407483c0f42081c41e07065000c00314810918903511621340c9038440c06c91003003500e008180c01c5102007202540315501c00e006040006d200e583c540c2d60740c401c546440030480380060100d03020741d4800d001c00c1c3c4c0011541e40c10340f01640703404500040d9012061080b510240c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 351927311 1250 351926061 351926087
    0x3081c0b091b0f070f23030f0a0309020a030506150f3607180906060815010309080301120c0506040e0415091e110a03150c0e06040e010303110604020d12 67
    0x9000010513a0030000001c3c1d41d80045030140110300c00000b501d0103040308034402c508038601c80f40c00400881400c2210b80c005001c039030125140001d50174120394089584182c103500103a81507404002003004d61240200980c02043c4181d031000740213100e80022610581101495084540c005513080075160b0746181400d17030542c00d921461110303051509001d081401d407404003405440003800701117590103840c042c00080359121381d1041c1c1c05035150000001130080300d00c40e1030704150310b1f140c0c61008034014101940c0609185262651034a0861034003010300100d82e4460b034083c1e40107010800120002c4034205138820342100a12100e0055071150b01c00500715802e0003012901d812001c844840201019004c0c01403007580303009543c801800800030318a1641c44024000031002c5004100100b40390050408070001d0f0420f5810010007400040031500581c2006006813881d500408c1450341c051007060103e48904084d01940c00e181d000300f401c0404004000e00f840b04503600c1003406030301c00e07180ca084007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 351928561 1250 351927311 351927337
    0x5041b0203030a0c14031509130c050607030339020c0901140d08040909020405091b04020f0405030a050c09060a060903121b0308060906030708030423060403081c0b091b 74
    0x2803601150a10420b01c01f12840c034041c440d00800514120003c0421824054202417074403049807a0000b009031395030101100324101922944203600b90700710316219151407005006014201c0240720751030990410742141c82802c66000c0d40d08002c10751251103441c0d05661400c044a490b007402ca80c00300c3e04808e1102002020710350300050001e0500b03440e40c04400c2043c803c541c148850340300d02600c0d03903441c0300040303900200080b4910b202c3e034649881d60042c9104100d007074580c1d0801d0b90350340002c0d05000b55940c00f92920f400c169091411440e0211180d80d01044c00c44002004a06041000f0071380141404001c0c101c51400600c165110300810860401a100800305050364641c2d10b0f004088040070740e14240104901404500a840c011030b1280075504110021410a40f0300041440c092400316196005174844a050040c1d075290303840100041c60040c0b2950f991030100c148040c02c00c01910902c0b0904503d844c07042089035032200c0c5015002201801c3c5480070003c18240b5103140d210324601d007141 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 351929811 1250 351928561 351928567
    0x5090903040e04030c061103090d0c02010e0315010f090509031801030f05012402031809102d0503030304120f0905041a0102060606090a06080c2205041b0203030a0c14 73
    0x8140d409504029114030446c1d06010185c60f94111501c640801d5840039110b400071100041c1a6100380d10881c0304600514020342043e0400000c01d0800e03100501ca0000e41c14584018452800c40d5107000000304140b240811441c50081011616801524007280385034100500f403c085d60f120350040440d20407000410000c5507581d800c0c52442200095081d800d001c501d01c6414040c5001000381c0c3c5822a08114001c2c00d200c0420401c000c0301001014032001490210010510b241d030348100b4200441840044404c102000c0d549402144856004501c25030081040100040c0b41410a41c0342d01064281b2105249003e041501c80744013680105030801d28001020004e041d103204100b107400f00c2038094903419105c6206000d42c03403040c901520b40040f0741e1103040001c180f09116096018004240490a08000d501d2000504580b00342c4e2a144045008041c8040c0c6031600c20100b59100c3e500345030310360030540000651070f40070003411981c02d5a501c01a0b228454014110f801100c82c030741100940d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 351931061 1250 351929811 351929813
    0x4140304030c0605031609030b06060c030706050a0b010207080604030c06020304080d0510150305040c150908010510050901170d051303050304031514091207020103020708070c140d03050405090903040e04 89
    0x690401c035006120101b104003400c00e864024800801a2034002c04c00748601d40c0c5820070300c051644481e03000c400d1448100450350104540d807055a01480a40001107036007550100024a410755503082860160030407014803000a400441149440381e100501503100c0d034890501c1300185c042c4c0c580c910f8000b030034a402c1003100c4005011a00980d1010b101e24404011500c1c81201115000c03140185000c0314010207104580c0300390b400b003400404900c1d00341a016110021207095401c1612840003015904200748028505000e03054003602811740154030801083c0101c44d40c82c2c414400707000601400044030303850b140d10070540c0350143d43c01030204c0740d8840d27032031510fa5000b5083c8904a00818039108501c100184d009507014003982c0074600800740008003040b0800c86d61300007001203040c107a00308061300c0040c50001c0076180c20740c040d4a03443c0f511840c000300825100d048044442c4100d400f02915000690044147e400741e8105031038680150f43d0f07500010349907105a422510301b800362541000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 351932311 1250 351931061 351931067
    0x7120c0504241d0913060b1309020913081207181212020304181a0a08010902030f030f071b2d0605040609141f030212060307030b04140304030c06 64
    0x414031a1564840e1500b0401c2902144240f0b0302c1c245480e8041d25070f2022407044c1422142100c14079026141c00908903080b80005400034203600064254151110380310f0f0190b01c1d0295042c0d52102401c1005503005045580f68031052041071110020403440002190040340700301c0004080d1103401d00b603218003d40312100d20f1881a0f4001e02100c1c0240000f9401d280345201200b0345080316003041c03c100e0f00b1801115540301401d540702c14440000c00c80c40c00520f880d80d40c1840c030001450070500000740b070101401410f0900b03e050024145980c0200b003151119102001103a018079086544030024039902403981d06080025400804503000d40380c0803a4001001500030302646507403620107601e950707942c501602e1b43e000d144100004151110310804c5201881101c0f140180e000420744248034050240710b0560040e01c104903000a5404601d802004003103c01050300148118010101c00e80b4655940041e0100200000c200341d41c00304140266200400c1510b01450348100c0040c0581d4540c0360003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 351933561 1250 351932311 351932369
    0xf0501180203010609090302070608040303020c030f09010201050901140a1d010e01020909011401080a021b01110c07091b140f0307020105040b0a0e0c060c1906020702120607120c0504 80
    0x99100b075182c548002030713800d40f52140000007a0f140c1c018200051900002f510a200004d109400b4503400308244100c1d0302060005200302d80c1400003168841a03000002801c440c03000304010896032605606142d0307124140b204030f50000c80c0c584007003104203100d41a03010408240380800300c150300f001d15420704900c041d005030241d52401da4160304140eaa90700707003503250015175100ca404601100c020a401c000c054008195000002050b1070008076103165981c02c40b002d042c02d50306150b002141c4890543c005011040003850704c060f06010290b1036180080c030031100c0d29a014103012241c640c00c20059544400c0d40d0015092059064982c40c0c0204068040c1c80c3c03c46040700c070004e10000090322a03003240324225031890103000402c000244078040c4031442c1c0c840d60445c0c0c17007486090640b00e0880f1005413401c02c2180718810250b00c3e04454030501114440402202c0c2c4c3c0d0f6085030003000401a0f0206204200080703000d004100900f0465081e0754030b04c6140c000d101c111041901391901c181181c040f07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 351934811 1250 351933561 351933563
    0x705031e06060319030804021513080705060711060c0a1406150114090f01020c19051c0515060103021b06180705031509010e030301060c03090503150c03040f050118 72
    0x980e640c9980345010561100c4d0800000c140c1e60001618040110b03201e00c00d269402440941007d12843c10b000450132541c1040c0d1b1840401d07507014005210381d41d000e00c0200000c140654240307051181d1a40c8421800040d58a00d5000c3e0002090180201d8000c1001031482a04812448030401c0204a566120f0340212181c103a801540c90000d07805520407c0d20b420451750408140781406021000c0080641103007100c1d0381103101700000c001080d910307081c01c0da240e004c800400c00c503014900000e100d508100500404a0ac0c2c01009103000031844c003180c044082816002100001e56581c0700590083c040c0b0041c41030082c440c84006225400006010b0380124100d4202c00c0f0b0500c85101410340d1440e080c040c01e0b805410282421503960622903034943c0046410001140d03048440c0c600c00d1860b0002d0344100b00149140c0140b0081c1a0020111000707080c003039014003845200d40c192501250303000381034456500e500000090034030061000a0485942c848002c1c001e90724803401c004075a1a41c424 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 351936061 1250 351934811 351934813
    0x192c03041403070b040902130512010c021c0903170708160b0a06081b0f040507021c090f060804050f1515061602010305041e0308070809011e020c0705031e 68
    0x7000105032034006034050449200000305807409061a0014020790048000c0000002851201280e680d8408241c11124050070000088000c440c3c84007d00d02402000000902c004808409101c95803100d4003809403508032103161038212202c40d50041d20b200b81c0350040c1000401058107060004400130000180e03008074400381103a2a07010341c00003110600e22a450981c1e00450303c59000d0300610b045040129401854400c0081b188004641035520446402c2c006800134400014001514401c83c100354030300d03181800040e4103080a544910392030b0b00480060040e060001000c002e4200044509941a00142d40c1d071010f8500500e45c2003c0b06560456100030561100f0f44181099010384207503090b691848401352074160015802000c0c00781c801d0b034102c0e40d5121498040c048400d004131031240700f5901c41d1141d141005008001d40d0b006401014140d04028103000c203803200d02200440b85c0f40c14400141c0e510b401000c91481c0100756400319401d40200100c00001d0304240c0c014bc060760354408 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 351937311 1250 351936061 351936089
    0x30b010303081e0709031205040f0b040807150842010206181c050c0613020906060702030616091e03050106140d03030902040617010207020103060e192c0304 69
    0x700000742029048131000c0002d00b800703104001241d45110f20f8003150700b0b141012440c01d6103e91001040710059001803008440c0014100801c503801c02117803009000d003c0350300344803503c0c07540f0007005100007a10b05504040100200d8540310450300108800c3e08808070b8400e4540303540840300040760f44100140d4054024103002454042018480601c0b00c00d0400c050542c0e030034030301c03c208403500601c0d01300f008121041c040c0b409881d01c104901c9004040c070600984a0312018410000c2c0c00030000d0160b4040d1805120310b40040e1070008106401c0700079141c00703440c00d21801104485c0788440340c1c04903c0041c18030b520340011100e01140c0c0425070b801000244460703510341d011b020243c220140c540b42c10805074411600400d100b6403040080600c0100301151842d5603201541a449546640140d16503001850200310360305481850001c2c0044540800f42c0d240c0740c45000300508082c0191000162948a10003030043c100a960006a000e19070070086c2d0342c0c179501080d603070f60007c0c020390310460a41 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 351938561 1250 351937311 351937351
    0x5100e0316031103040306060e010e0a021908060f060a03060819080405100c05030f1b0c030706050f090a0f030203150c0313020d050109060203060a09050f060d030207030b01030308 79
    0x401115140440e0304900d41c00c5002558003100c0300100210b01016a0000b07003c0030001134000e0040c0c03801010103d81c1c0443c0e0394101780c4080e007040806405121041d1041000000030761003000074136808240da0030841200c3c2d942401003114001040b14266005100040504c2002d40544c408029130f69035204680701e03880f406024001110360590081d042e190140f104020925060850300b07030186036440c2480e04a00182c0d035551641d0490040100003c4000c19201542800da6240c4000c01c0d8100000300064480e580200e9100c1d4494050001040400079003100da85149504840003180044c10344001c1c03590700d180c54852040c460100f00d210b07001b0101719482052070200380501030001c08a901c1c0c91600c8500340300d01b09030603403c4104d0300011101075060100d4401c1c824614082e024a1015039a868000200103e804203900031103100c80c0341809200f0741100840e00540d1103182615003c000801030b00b4140c0c50400540c0c0010a2900b640b0004000c1560106c4101d005002c0c40d41450341411038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 351939811 1250 351938561 351938563
    0x4020f13021b030f030a05100801020f190e130b0d050f0109050d0c0c060c02120105071d0a210602040e0412020106060c020d0f150f02041805070c11040605060705100e 73
    0x14138480150210780520108601151075408160001c601d411100503035036842040500f6608042c4540f00440404280740030300502010a0700401c40700e071300c4d01a100c20000b0000032104801c2400d40300300c1540c0c990b103400c400c1c0c450803890105250841e023103131746095000e01298064030207402d0031984e03401040800308046004c4c400401d1035540c01510b11100303d0030100100d540d60032024060342d02844140551848040070310032035018200c540d84004c0700d0704081649040c01803810219034000c0030f0216007000104a80d40c036082102400c0c8038540c078600d54a04040d400303030203140c1118202c0c80d1b044040c4800c20800840e070101a00641d0003c0c068550381712002c3d1020716401101030b4225080080290003d4007001103009414030440d00050054041c110b11800c441d01d1334040003580b50300003400d2120010b400350310000c0200d4060b0522541c548441c004041c1901071400030010240c403a4904c10503562034010402612001d040c1c1a190b4800c0d0610300e0740c5028507001525a2482e00c0114007030924 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 351941061 1250 351939811 351939817
    0x60f060c061609052d09040f020f01090b180d050105010b04031406010b160311070803070b01090b150a050c010203100905090604020105180103060f080d020d09050a060804020f13021b03 81
    0x4001042c8003940310f58284614824211200e1485206550003400805c41c1c1e55010114001c0c0d000300380f05111912244107000b150690300c11403a040c0000b50702d08100020803902218940f48140300a80034152403580410702d04059010020955401c10b000418084c0442014008490007050710a40d4000201c01740f03074440c002801405035001040000030000207864005400080c86442c3c140130f100e600d01c43e081d04103142034001d0711068200045180034000b0200302d040c05071069903c01c2207005048000203030b04500070300003a520f00d10040350900d00e460269068800c0c0d0f400d10002590b891400c0308a030000c01c0c0840c0100c00010b03151101140c9010400107105101d5941a103032149001000c1102003054010602414102340d187c840c04920502000040c80003046914000c00441d404841e02900b030440000580007046041d4004200c0e956502d000c0004940d52410b10b00e40070307200e0340045490010b1802103690030030040c44c003082500c0302c036900030680c0c520304940c0d40b00784034443d0340320a803644 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 351942311 1250 351941061 351941069
    0x90603030c0624060f0f05390d0309060c02030c1002090406030204020408010903032a121b020d0f1b02060c0708060f0603011401080a0b060f060c061609 67
    0x54101203000e000a02c6a90140c210031264036201c807010140e990f0401c00b0451641c0102c00024400b40107501100d4110456400d95851406d0460801800041c0c40c0840c1003000c9042c82400c0c8804c419001030a1000c2d40385070000e41101c195541045807038000f401401041c0d5085030002e01d0f01d00c030307180d84a01c00b0003600c0c4400c0c4450080c0289409003100c1e00041e41042c40202c7d402580c0b1100000180e480e48003c0c4010682c0d103001003846407480c00c01400f242e0505c5440b40100d00082c1c24545181008082d0f050100f41c02c0c200469a45d4460000700c1c005d010312281c0102500e048041d4030034094000a1307805441e1905c1ea00c03060f00c0104001d04a920303918903041c40c500b528111480e42d005260100190203081400d80403164025030740ca00007031030a0025584440d04a80503010f002d041d04080c042c02141007009a040300082d4034180352695101505d980c003600083c8001c0209645075071340c1031008c000980c0206003d8560100601d200e80b10704c801d49503e004907006c0e081229800340035201c44000c403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 351943561 1250 351942311 351942317
    0x3090b13061107030215011a04060804031206140a0f080d0311070b07090f09020f03150f10050408010b090408070f03030b0a03080306010e03060f0105011407080a0203090a09060303 79
    0x2521840d03031198a0110314081100c4103516100c0394240b44480801800030345000758024504860344180b0f16403c1a0180c005c03150303041c1002070040c20014114208d40455515142064003503031141021140c00c042c04004a07205824107000045021003012901c000b84000c98003130020f5669510a00000760b001c0c8035424558001000401034240284d012101c2d12040103030b81403900c1280e80c0c4101030740c001291084040f03020804207014480e692a0803402030609440c0440c0303050300d1524000c0c040d010092010b1074100302c19009100340e4079040b5102c40c518101601c0009207a80310000541180c02a00500c600c070740c0381045541483c030b000301e0742c180199002485a4600301031a100c003c008144030200340c05244d00c512a1400a464004040c0c000714080e1008a07281e0034240001081d5030740ea210391912941c0510140040c3c0c1d500c0c0744042d4110303402420044d001c88081c0c1d0400655005a0002410240c4085400c0101e20b80120081a428404071009650140c589200c0c4084035500d010203400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 351944811 1250 351943561 351943583
    0x3070905102d140c1e07080f0d0206190f050f061c0f02090c040e01090603021c0b01050402030a0605190501140a0f050306060d09050115050d0b0c0a2d02060105010309 73
    0xf800014100415546048000351091201c10740601e804201074140e01034401c0d07101800c2041140c01c24064038000003200400707002c1d00004400000d64452001d40640c1c480c500c9040f103480d044510358000301084405650901c5289040d130291500b4000840d1058000c1d440c1c1150320400a456895802d40c95500010300704800e42241c091000c03603040280b01c144005820000815000151b01c200c43c0280410348002c5900c0b411841480154411441c69800c0d02494040380c400291041c0d010b05e0555005850068482d6285015200540110b0b840310350000d08458484000041281106096a00030788405a5401c0800d02c884039070300c916981180040c0c5150382c0001110b105800641d0804001420a402e2200081c6844211054010b0490740e5030f644801100c0b5492800b95140020001141d180442c046951600e03980d414008008001400c80080c400f54502e0007003400444070300f40300c204d01f02c80668005130f550084040e881c200c00503106a400009a030341c400d000740c88101d80d100550b450 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 351946061 1250 351944811 351944837
    0x13030801030602220b0d11030105060306010c17070303020705010b03120d09030c15020703030b0f0618030a0b1006020127022101020a022503020a0302010503070905102d 74
    0x80250000798240f60003818141c4202c0040d145182c0110151a80008095550306c903920b0510440783c000c444800031250500040007603658007000e0b039138402000e080482e610f0030540303000c0312120105c0341159100d100118045061540c0355014190b510300c00d400800c0b0030810b00c0100342c0da40341c2c0c102282c605500d0411101c20400c00681142101e588070b4105100740182d940c0d15a081054059000541c1030703070110300030381499494050312450034401c2d00d03c1d010820508001c60303c14440c803003414034910a400c280c2c10140d1010001b003c9a00e4000b125903c1a060008082c45500c820388513000047d803d0140c0c0800100b0310210302083c040010810044080c0c1503030a119540800d0003421854840c00625240b0300007080c0020b22002d0314590240c410130309941004445090a10040c085060f10700c8400d000580b200312617841076076024246113450781e941c0142211900542e40004da000103480e00c0040110750050040d141c0210140e8060004a40503485200c6010400c03411000245061078005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 351947311 1250 351946061 351946073
    0x608030703140f091509040f021c090201020706030c0908060a021b120301050d030507060f0b03070819060509190c050a050613060e010315031103060c04030c050906041b030606081303080103 83
    0x1400c9150317004c2c0906007013035200007038202c941c041003425403035400048520b0390049507a002c0c0321490760620100300e00a580e400007944c0308982d0150000740b5944100c007a0906000d005004010404903044038070303901d064041c41c4081c1d0080b070304c0c0b40b4640710707581d038507003500c40700481e03a401c0181d00a400c041c02c50f0320306010404055080b50055040c890f04100100c0842c1882c020391003548806040801d03500341c00e0050500c0c0051a511011440c2c0016100d1106421082c41c003940c01d40d040140403410f9101d40b1b0050381001040300440313403d48902007185003000404c1001d0022514200c0e40401b01540c2c40052189900c101e00300d82d001c540726603001344202030041704501540740c410b141c0060003612004400d50394100da80c000343e982000410040708945410842a03622035404040c89007090310b59542c0484450716401b4981c1b0801c8400f0025400b5160b550008410745100407000320040040b10b4081c4c02000c0c5e0b030140f00005800d410009440041071512445825819624041541c0c65601d0f00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 351948561 1250 351947311 351947329
    0x10608300a031a06070b040c0b0a080406020d0b06120f070302040308121512010209150a12050705072f040c0e011803080301170c0a050d030804150608030703140f09 72
    0x180804588501c50350f0341e20340e007000c3c0811a200e00c14000b0581094208640112221b43c05844807030030401c01c100c1c11641c0b1003425a0055484800540c55444240500014141e104c4540d43c100e140400d03032000b0028251038031030161000a01c040040d40707544000701c003a4441c5010140400000b0010483d8032418070315400d80c84141d002c1e5562107203200310001582e00100702d082d400c860b900803510f82d0b424a00a0300c1c0340050046140c00920f0442e29480180c024180072402015040d0750b42d0000e041a07000f14112006203a100c441810f103e0341a240135106003400c1c0c02075660880c80450b16502c6802d080c452803203205000e86614070541c98200c011100203c64402c90681c02010400000002d4500d070702a40c0a81071401d0412009403c0d1120a46082d480c1046c0c10b104c2c0c0c00360081049244c0f43c285441340115010f2500d81a0b030303038807800d042c802100884001403c86141503400200e040340800580040c03403283e62440703102442c410881c0064001e503408400d224400700484000d43c602202c01d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 351949811 1250 351948561 351948581
    0xb060102061e09070b0c0c040e07050109181b170f072003040b04121209030c17030c0d030e1501081b180a0903200a1101020f010608300a03 61
    0x444401e2600c400d03245401ba003182090818aa2001080c00281c2c40c0a00420301c201c0400307001011050301d0031000900041040c40340000130148034042c46042501d0750001d800036011a59a41c1c442c081030f440c01001300b070321040b1551000d501d10380800d20b0340250318180c1d801340783d4039640d06c0d01e114076103007400c1c40012036010f17924180d200400c000218140607402401c0102904201c1000130f507a18189004504000606e401c10403690000602c0015001c0142c1010f40d4243e18582d86043c03c084100f038998440d070b40c0211074500c03d03031101d00041c6130f241d04550b203800307191020b4030358030515800a00d003401d80c28001c04029400c80d02e100c0803120000840c1c030b40c50910044c00d5075201d5214980a03001e519046c2ca030901c040c2d440da0700d801c0516800044600b003140700021501005015141c456854101d1640010448540f034119200c090384200f1040c43e11489141c0201704880d41c1d05140e0395502804d01c60b10b01c0c030340e0207400094040340382d192a0f005c40075180c10100e031410800c840c1c00c600030680480 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 351951061 1250 351949811 351949813
    0x2060a091a0a030507020304080a06020d060902030f0103030207051005070215190905030c0d050316141002120906011a09040603150b030f0607020a03080901020906030708040b060102061e09 83
    0x56003000504820141082011000c0c1d81c0e0780101c80d00800b44d40c4024880000d542c003c210810034440001002e0381002d400c000d005849092065190001e4003141c0d002005460000c014441d9618940c042c05040380d100c1c9c1c00300c4a21a0b40c49042c4078a50742c404210001041301404040c001d0301b8200c4114180480148000c3c0ca80032603001400d8610314003101c1c01001600502c01407001c0d00702089806103902d01110744154040c41d907610746541e03100d00c920302d05560300c800c01c80c2d8040094403140c959014001c0030940d1070102c400107030721001707400031030b0040004603480d404604012008201603041c0c0720343c04900e47d0881114880d076a504e5105040d01900700d40c1d10880040400c100903104084d84140c5500400d540303003082c040506c1c3c091800310041964021100344848103070000b9130405500d41c1070500e241141d80c1c01515500a0061100d00c0c1d41144001041104040c0c3c4504080c1c45240304d020f8960403034680d030004aa0342d4071b085541400005407001551804c2036400b0b00c1950001c040c42c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 351952311 1250 351951061 351951077
    0x2130b07080301080601080a120e0a0503070801150f05090f150a030b0f0f150d030c05060405060601200606040b0613030804081510061b0c030f120f0c02060a 69
    0x90245085611140c0107442209010006000441081c40410300403c0590010b040d0104192545001240d07919403000a04c803140040341d0113070700d6049100c4001c010050030717100c8036540c0d0407000d400307098481c0260f110705003542d0300401e008204162001c1500c0020341088010781c0c07800041d224500020f80030041c1e01c20b8400c103600c1e0980c0c405403070001541c400c0c0500c05541c24215a5207000c0040a002d100300070b900c0030308100e2400081c2d510b070051203204842d0046181d031241401d698064180c000603205005a034100810700100085050040c0020b0341e0b2001c1d14056148d00c1990403e215554400d43d80049001c01c2d010b2905800c86024000000c02051030502c8a040c201e05c1d84407144c1c0216071030304000c50100603100d002d0082071003d1500c00400700300307407400039200019458140100418085100503008085000404119106d5400020590a05d44904240086080c4c0290880f40080700401c03841c02c4c0c0d031080c2c82048249030162249031601d001d80d820808540c20406121040015072 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 351953561 1250 351952311 351952319
    0x1209040c091208040609061d091905011401090524092709060a02090a050d1b060816090303080f0c0c15040221030a110c04050108010b01080603011503060213 69
    0x1803010303903100ba0700c0b030842507903a24507100340500003034000d911020078880c0101580341c4924854040301400e000c11642c01d015a5a00c200800b400007004102c000010701d03002c00480c01c1c03082e40300c0c450360490090300c60b2100250388000f00850406200c0300c1c1003117801d90aa406c0b5030361403003001800e00140e00030100914441d41400c241410722200c00840989581041481100f1800b0b00a03a40c11020b00c41e0103600d40031b12a004a0500c10607031043c1809034407101c2c11001441510051142c03581c01e1164035412140c1d603003100070b013949004e444019042010004103179409004001000c222079158881c2403240e80c2c0c9807140c50813403600501c030041c9850108414101c0c00000c3c0052502000a00b01c0078000e810301e801407062400d2548404040301006107e01c201c0c42a0000640d9400041483d12000806656246905240c030342c414890300141000300104104c0410341000749004400c1e6030b18201030f900d80c0200b5090726100354202001001c040800c1c004180e003034006040300f0030b412002e4100c1941d5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 351954811 1250 351953561 351953579
    0x1c0306150c0204140c09090606071a0712020a21140a02040905010b03010b0717090d0b0402042405060906040f1d01080c03120a0e0a09061401021209040c09 68
    0xc916403480000303241421240852405100d400d00301c80762900c1030030a928002c40c0d2064640302d0200c1c86440740101c0c0c1c00148142d0b03558000ca8007040e0380a64854030280000d80d0148000d0001c0d60000c022030000c11b0000c030110000d10944030404142d0742c4da015554801240c03103401200080e891234019072102d540190901c840b40040c1d004a8400b100107030346501d854103800032240181c20070b2503110001c000411408040c030701910b58480e007103614003108107078413405400c1a10600380050740244040030030805004181140920460003580c0500540076050314441d6101958042c103030400b0ba5031001407205040c01d00c0a2b1840810140100d403a007070710340c605422990700550203034a01c0b48003201c000844117051004280104461001086409403110009407104440c40b91401c0d01e031030225603d0441442440c61101a0201070070b0443c00d40c1d2519441e8014112a0043c00000e042c005041380a5510000f08080191040c21109081402c050f0420001c1c0c0855620201080301c2180003041f00c2ca1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 351956061 1250 351954811 351954839
    0x6090f0c090f1314010602010e0106030c0618033c0c0b0306040f060806011508040305030a0519020a020f06090f0304030f03110f0d08060105070807020d061b180f0302031c0306 77
    0x701d0800309044c59850240001d0130b651041c108040e090341480300820000c1c4207052841c00f503a001d401c0c0209200040200303a22018241d0b8005480c581881d0351414419141c420341d41852001282c0c19402c42120301c9002c654020020401011012042002c01100c2050005560400340040000c6228002c03804c0c0141903511036007241105801800042240b00c0210700f813040c80c060300d420700c1800303807034262006415800014407007c207040d203d000040040500310403c2d610040a01c0e021501e81250400080d0399000c4220703203040e14131540000c030b08007030800507485c800540000000d601d02801d503910a610014081011000e01c04101c90414607128180550708000e45002c0041c40340c004060cc0050801c1c9010b0310706410b000c4104070f050045082c4c4001c9442980d0190390b84101410f00f0301e058801000d9201c100f25000603607294a4803040c0d1302080c0403c401c9420700d5001c1c1103d440382d0b000780c0f041c01c240c0f000940c1944400d42c100b00006c030840c42400c0038140c5050004240703039154039104c9520 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 351957311 1250 351956061 351956081
    0x40b13050c0f0403110a0608040503181504030b10050406080703151808030405120a1b0f0203010f0b0a090b010c02012703060903271a040f090506090f0c090f13 70
    0x2071804817140082c104540500e0060515150048481c00d09440d5580c6130300c90780300c03042080101220103d4540e00c551650007408a18112040e565a41c2ca003131071034500806403404c04e2601040d200025907482e190151005690381940070301481031460340d89000c624401c880660802d910b5007482c3c860342d20042506984540504005592450030f03152403401c0010700000b903e6220b10030300440d80240e51105c4001400014002c5d001c0c04040c007400c140702115502c0320003d42c503600b0b01156400924a98000790742c1c07002c0542d88000316035141c0795468141c6804c25500d40c000b82c0c3c1e0b40034000156200c1c0b0030303200801070034144100c820100c1c049803c10f400c0d02030300144c800d65156107100041580c4030404c4140b520100c0b0300044070143d801114500112103110717024583c0f600c0340c2081031003841c1d170b070440340100a0003c543c442c1550f02c0004002900c41151003900c911400c400082581701241c14062242418004031840d240c0680e0030002c1c84009140ca50f90081c0702da582d5030074110f00b203100c0c2c51125 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 351958561 1250 351957311 351957323
    0x61c06020f04081204060f0c1a01410f0628081303080703021809010f1d0f1303030608060403030e07050f0303030a0f09050a0c0305010506040b13050c0f0403 69
    0x480c104803183d4500b00c24154010394000381003008000d8140d10918103540d61803e0320f02200c042c15a420190900d40101803041c40c1d100c0842c00000d00c02100402c082510b1a2460329800400244035244910440440c42c9088180f1259502000d900d052403d10f841108020032690501c00300c3e4403a92803030b051600c070105071f8070401c0048462182e00304030159844800a4024841240699801411040003408035010315801080110100402d010020440309010b09030f00c80313a42c0d40d00e81c0c0074194500c52084500862044680080309900340070b110b4811007000c4102000c5071540b601c640013240d54110140d0406aa07500c0126645c9400d00055006500a59002c651203604d40740b401d0502100341d000c988103480d0b1101242d4651408030941fa403020f140740d00024021891002c0380043e0820701c0e802401809400e81c506c04025503440c0d90300c16280150005c0040b56105028801164550a6015030240360702481480800d01c0d41c00203a0b00002c01040c8504117107405d8241c509507001070b0012181 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 351959811 1250 351958561 351958567
    0x10051306052104080a1815080612030f030106210c0c050d0f021b030f060c03150d0317040c05060d02120f060612090f031911010b09061c06020f 63
    0x350200d14080030700d64030031840a0380e409081c2607492120138410092440144020311508141b4041c0050040c2c00a100d0b2003960030359006909001800380008030340d8030344a09581034050b01c07510000810f560303440c0119052103103164201070056440221102d0b02c659070650701c1b902c000e01c8040300c1c0110350810920744c880f00c4505141d0329040341000243c00c0e0078010445c40f809140c000550025401a4400d4000300a42030f03104200f000c00d0514210403003a030307650f1042409100701c44400750025441a80300c1c03803510410400301030400c02092501e46000d00000c500204005c021280511500c0e006481580f1008000f540c03400480c240380c1050302c900d1816540450080325401020602551210140a035100b0702c2c680180065150f00418142801007c007080002e035001c10204609040181a08201da40b1560303c102d00e200d13007403c00c031005070009260300d020f141070326014058000d2000c8000c00c0d60140e5503c0d4400d2020001d015000501108161442c101c045100e510080c031610351036440f4a55 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 351961061 1250 351959811 351959827
    0x60309032206120510090905010204030c03110306070201050603060f070513091a0405010320120609100b100c0308130f05060405150c0307050a11030c070e0c04030c051005130605 78
    0x4104000000c00f0015182010108103200b40040415420348010450004680005045c098028080c3e030708010071846020b40003000b03200c40c2ca40c142d9401c0320300b10202d0b41c0d01c1e80c90003001c0b800c4c1c403004d445840e0503030f000801003001500700030380701540528507150882c10600c1d8601c1030000c0802c0c0d68040c03121607075109240c0819841d80c40c41006030301011f42d03090102d949981d032548c440000550307030947c0c6a8680881844259101e01d0203810300e01c0074908442d09418840340040d03c4141000c440b82e505458010320018905115002500c0b00100d83c50b40d00c5048625101640c1e09a002000d02000040745280000094050292450242e010302e004208514007880d0151410464001c4001d84001c000e0800c07081d003100301c0031241c2c808100c0c0b401e20b845e001401c000b5900100086090440341c00041151050600000b41400482c2c1d2901000002c1d030b100c0440e004054800c9000c041e20320300074080c040c4442c0c20140b10020040b41d6901d052498a1004142c0b104011059040b41c00094000200d80e2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 351962311 1250 351961061 351961067
    0x501050f0402090702010612110103021204060b031b0303030708070207050604080a0507060503062206050d0602070c060503090706030e0a0b07120609140109050601031b27030b0402060309032206 85
    0x144e00c0320f0180020861070b403d03c1c142000184c0141c00041482c50240c005264507446501030760b41c03151134020000194202440c240d0060b0440e88515400f80c882e0303c4401d11540c0040c1d0040c1082c0b08040e02440c0b071074642ca5411116402c004002000790710a4990000d1661241c500800050001402418208900f85801d074149011981300c002001401d0080c403449a03142c00c20500c40902c98986911583d150035038500c040d10f0359901c0150b02c99a1134203004140501174004104180c0302c0c144603c1d147c1c1d00c1d0300003070781c0600064409a403503a02824003170210070700a60001c001c0d801054100c03900b86c01c06654065000c0300441d2b41c40f000079a9040c0700b01c182401805074a01821820304280007140f2403800c100aa00b0301445864881038a800114006900a42c000303e4402a80008400010850240a040c8281041400c030a1007040c0c0d4805100151100904051b01d9026020400e81d031103503001c00106403c00f80841030b05000820034100340c005483c40b5100400003080503c40380c0340c80d1280c05 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 351963561 1250 351962311 351962329
    0x30903080c0111041211040e060f100f030f0302061003240f020307020d1d03120a0507170322020319080f0a020a0218150907030b0603090618280f0501050f0402 70
    0x454025030506140840234440496140c3d032101e003140c0d0581e06075540031f0b20350240340d80d04c3e0321400c1407603141d403004018030103500900d54009000340c00312125a03c80c1d130500c5103200010300c001b601c40301501e802d80303980031400c0b881c00406480c40c040110b807800340320238140d0880c0d10507110744003da8845451514065040200700b964810700000010441c2c3c600300100b031300c846642000085a0100080c8840301074040c0069a1510313800c040310303040c6065070104001c100d51042c3c40b01c2c40b594240215400c8890b284c0c1000041c09940503019103d0b25000072084484552001303000c50740700030241b12150440c1c2c050806000031380c3d002e40c0104602550740c010704c40c841e46001900e608104030007003084101092450340718940b0754181e40380700c900c0e9942002100145807441c0e0b031542c8a040013052111a03000000c1580c003ca80c12120040419080404a03a60b140e81c40c0c0080186d0f0003403402c2c4980354012104580d48a80110700401040203e0381d203450844d5801c403213070f6214000403414001981804005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 351964811 1250 351963561 351963593
    0xa0b04020f181912061503080a02010608011a010518040209090a1a01030e0a020f010e0307090b0405070c030909090c0905090f010b010f1b02180c0c0c030604030903080c01110412 78
    0x25203e010f400d0118030401d1100029002d0060703a12020b04d45200310b1000d2040d0015500260717115156103003420000c3c041d14143c4600744044d8285070820381c14140c1320642d05030b42e0318143c44480c80d00820a51000f643d1010103000390b44103500b4003da098648880c95203610500d2140300c0002c20034950801d0000685001c5001d5040520b07000820315191030009159500507012900f03075000c80310200040702c1d030440304580c0a0701401040c80008042c1c3c5981c00c54400e14100321408c0c017090303a071400b00b182d103010b42000150029811396801c0008000320740c02111000d0041c01071175815030b22504868161842903c4004855101230400358401c0c44c28814034035555001d00e0040100c140a800003010002d0b0f82c0c40340c41182e4602c1082c08115a6248603084500c183c9540c0c8100c9850074401c06040c60b00801c40101240c000c40d100071025207004a002c038402c50781501c440b0007947c00c6840c1e802850304501c02980f100d640c2c1d0000440c0b07242c0028050070007480121140c02c0c03401401e20300030007031400080c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 351966061 1250 351964811 351964849
    0x60807020312040b040f150f140c030103170712080a0b041103400c1a0d02160606180e07080709090c030c060503100b0c060a0b04020f18 60
    0x2014948440001d200150007035000342444e00c8a40b03e60a2100000540324801454041a0080e0640100e0580c01400305860302c0d41003040f0800c44619000201c40c03084a100c442014100010702c0020400c54202c1206010380003031030f05140b019a62040d042c0700b20340061000c105110704010719010345005a03903c072441a1024000114064409c00450001429203c185190714651018140c145200d0a0040074941800802150700044c1811704828000b4151140e035003030340d8049420304410000740c2c41282940e140500c1c000b44d08803508001e42207400186051001c94083c0c4d0003040c160b0203004083c008007900c8141c0728080641c500c0407101c0c1ea04030a441c0d90411a8100150070000c9200742c21030f81e0307045012404140d545042c82000c030554200502c00046080045907060303000c0081c0d84258000d01440400f80d864a070031200c0d5000b604c000c4002640040c0008541c0c107102e070403403454014003410142c20a80282c0ba018082d421810700101046000008400207207000b10b42c104003100610 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 351967311 1250 351966061 351966067
    0x4030611090f01030b03010b0619030638042408090a0b01360501081605100e03070b0406050315010306031208042607050d0806010c021306050d05070608070203 70
    0x4010402c2803036914941814159106640702503510290009950800010001039032414031007001080e13507024002800c0028580354011404418a40900c001c40010220b01402c9603502d5401070880c0852469803900600103000028920301107243e46182c1c0a5004003580004052142c010250200105200e2042c1d112024600210b203038440f00340e040d284000c10b2000040090455800203000616810f200c4400c0d1407800c3e80c80711003551205050300d50325003d462140506101d000400f450340d00982c1d9014000c1078160b643d283c02841c0c00f618100003c0c0c1610b0495644803402462703a0000d0740550049140001004900031002e40b8210340c1e24801d003030400c0200d055803244c98696500070124401d02c440c62000c501417200342104068007507000c8602003200b24031070f4007161650708101c00807a0703d40300e542400781c110350054000e680b00304c030b060f9501840300340300d6001c03c40304200c010700c51400107944403008101030321a4054801c03c240280020300c0c000d4a05070008100d404014031040c00c42d0414 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 351968561 1250 351967311 351967327
    0xe0f06010506071b05120604050601060507020f131103091608070e01170a0c0f03030e030d080c0d09020301060e160503100902090f030a03030506120a0b0a05040f08040b04030611 78
    0x10015519001e40107141004008011101380c4d44c001c004c1d4110030b90004076202005014000004c0070341c400d620074400ea86099907200405d94281c060000000d5105404000034121824404045056640c0f080c6010a0015450081d489a940183e41c0342545803c4103980d03004800180760170300018406000145159803030141c0b1080b181c2010702800c05802074019500f40050420064842c00c0380d000000c0c00041c0d6603c842098100310984400c40100f000c2049c0c03a6001d103008211440c80fa10b294450b80641d45e00c016007410551320496a84003480e9a811111026072824824800601407040c82017880382031010b14120000b907403184141c2004401c004000c2e007241c85400800440d507450701e0260716005031800055030003064034070241d05442200030080c2410350640005000b1642983c000c4020092011100d894007420000680180c00c01800b1981103801d0358462a40180224034210340d81c2c07043d9607442d41c0e540c8517510400c1c10440200e014814064248540341000c10703020122443d0411f4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 351969811 1250 351968561 351968569
    0xe01140117011403031210060306170601061b08070828020a0b04031e0c060c0504050303041a0403050a03050a0810061b030306050310060905060a0303052d0a02010e0f060105 76
    0x1050080c0800306035108a1500b444d101001550b000d9414500e04081c20b14200410004082841c802c4100203800c1c03181c00240d100d003951500c032140001c0f90113801d040c2e00302101134440280e18084404603115001c0d10300007003a450740180040c3e0340314002e541c1e82e61002506510345c9a81c212101011040503111081e900c13900040d60b80041a48450100116641c034182510000b01c641040c005a0003220243c9200d60340c0b10340340f030b108188120400c00c025003410300d048680303000c0c0c0e000d8960141c1c410001484455030074000042d5445d400c0d0a030398035140c0c80c3e43e0350b40c8c1060580340741100441c40120396451000d40010506502c00c0b0f000d56001070661030304200501d86008020f0303111129a030140d4500525200c1c1e0080030281c00003a00b12210301c8a1488504003c003a01c3c031801e00074910340710200f40719250043c6140f0071290113a4a440c208040b030a05400509007407981a20041072501c02d44442d41d1000001d0700d076481c066000080c2c0b608005503d1814031001e03100846aa4001000500540d91 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 351971061 1250 351969811 351969857
    0x1008060406050a090803070206041502031504020706060b040b0a08090d1b0c051e03011506020304051203190e0918030d0b0d0c08010504030f0e0f0d080909010e011401 73
    0x74024001107200d4481040090051481e03440241290100008000400342c00144860241e0304c0703104070b10762080c1101d800d80224081a00c0ea00b1501c0d202c0500009189825009400903501940300040c00d00d545000c00f60455016a00c0103a40c44004100095015002888030354030020140c01380a107034148190043c800c0b84131200114080d51070481031403e000715040c20038060716014048071ba0310541c502c03107a00340c055082030041c465030034904540a403110385402c00c01202c13000d4008500300386c2020200022036004454011350fa2005018454201e210f11000b130400041c152030b1070055102a01c1030042d00032004042c8000c0020410f12000604000012150310070740022000170420b0075080000c00390910003078040c0c411001108003041407001907228a01840c0300341c0741c40c4090103500e0b000f6183d0000b40c4140641c0242c0c18208900541400d4074480c6209100d82c10f4545410060710018454005c00c1e00f040300c042c0b120701d0052046214201001c2825030003403d0081ea0311028019409000c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 351972311 1250 351971061 351971063
    0x9030307021e030f0601090f06050a1505070b0c03011503092a08120c06010503070b0d020304060b0904140c030a170f070b13020901050909030a030e0c0402160b10080604 74
    0x801d031400c2c0c080b00c900d002040310710703102e0008054510350501e0400041c0d8481080c02810140c9140036401162200644030b001d04880c40070303185101aa141101c40e070300e6a180d540c107a0b028080c0402052000907440c6124511031584829442c1e00c950400e03d01d94074515100310206c2c24503140914107000316055078401c03541080007074821070401582104a41000050b035100403494030404030600d007410040406404040448008c80701e03141e990f13804065030b030040c501c9030080306a01000f040c1d03400380700d9400840c0d000d805584007081580d5a54081400b5003800c1b10141d07030ba810361845400980c5000c6c051300284150450040101c080f00d512008403c1c40c1142c4100104400042ca001c016030442c0e060307868240d04407074442502d26040075113010102146100b28401c2496000102c5c0c50f1504510242c05901004020b41c1006200b000503001080b00103911406485120001e801a60ba40c0c001024000c00121000392008400d00c0c00148000d005002152a8003450505100d001000038505902c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 351973561 1250 351972311 351972319
    0x70509090618120a03060e0604090803070c051c020f010f05071d1f1206050301090b060409060603020a0b0703030605030c06160804030f121e230903010212100b0903030702 75
    0x3030544070481480c2c083c3e80300c4220040500404c0d10f0040d03980590101084454007401240030740d40c0c1b0b0041008440d01158010141401800462010b5100c3e440b007d40c80ca228000315a4201158841c0e00b10f0010b11100000050340805040d0324198400e0240d030214550010040c002800d200002400710720b02d51548408800d0082a6006141d44000c281d8144401000740d803010001064001008824000f640590540c10030740005220308052003030940043d00135013040342c26101c1d0300410010300300c00d10b07054580301d403243d20100c0947d5804a41c8001440b0b0000c4240da5131146141c0502942e1320f070303884244250002c9079180354a0311038404a0303106182c21443d442c1d00ca01c0b2131400c0d05040c0100c3d000946030524130146d4a04000385060309036415107080e210341e006210a489035002da107071507282500c0045c001c0041c01c3c2540b402840c0c0981e11742c4003841707110b0811441202080c01c83e00700c8180031500200c05020701c41b14205154440c3d001d080e1600c881d618115808001c81d9030b9128800c402801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 351974811 1250 351973561 351973591
    0xc09040c030522060609021602010f09050d0204180212060a0e0714240406051e1c0507020304050310140f0c22030807200f131805030d0603050705090906 67
    0x10001c1340e90000340075004010b801c40d02e0b044021080407910411040413800f098098502543e0b09000312603480403244000c01d900381e03080d215400e00018080b00b200301c070300c602c103036080303c00c0107035191040c94644106d01d0000381218070b400398221042d03800340924000780360803a10781802142c0b4113103c20000035070103851040041e488070039081c0e12902d00302540d8011400c0403038082007030387e03101004200c8546040038010070a01c80b03400b0945144100c51807034103400c5911300c4d000f000340701e036070003061f44031980380103503820299107601007420041e41e0000841c24595030800360300300c818044492600f18601070030402c4d082c906010703181200c1c86808000c0d4080c00aa015107803402d5a80c0342d0702d001170340d031100f28244c85003090707d060a004004090882401e0840001000c0a402c2800e142c1910481c0104600e91310307019058a58010300e40300351a6090301d900800d6280105404000400c2c1c039000d10040010218a5818000d0a00c00290003040c8501145000d2101301280012082d80141d0600c00b0700403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 351976061 1250 351974811 351974813
    0x163c0803060f011b0c0302150c060a15150305040c060f0813020d021203030403021b030a020d0606050405010b040303020c040b010519020c120d030e03210703090203060c09040c030522 80
    0x904401c02210790703950445130252101000349400c8248100e80c800ea0340f1000c1c10401142800050181c01c0c0041411b41c00240003070032a03072131508070040c0c0a040c0c151100101d5100d0390803500385d001c14035603400480c2d128002e200030011000c07103200007481c561030110701040c644200240340c040050000036820040b15a50340c01e40d602e550720309100302d500804112045040d0074200d500d0307400448040c0e0241c0540000200e0001400c0c50300c80321000018045c000b20301c216401c01001082c0c00c5002d44800303541d0200030410b6221485000d001e40306280b410b85d200d40c40c5150003858042c4521085004038180010b146049e6000016100c1d0070701901c00800995900c14001c030310703150036140050383c01011101c0d0701a00110203c4d102c4020350700c0e03139014001881e42e4090266203100b180c1940c001d04024800c400303101c00c540200719401c04100c0c40c6c04100706151b500000e1510800b91500c0500c0c82c00055282102c3c5401c6c800d1480304e82031810300b03005600c0c00f407105000408810046002c003000501003c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 351977311 1250 351976061 351976067
    0x120e0a050f010906180f15080609090601050d03050408030a020c090c04140d021f363003021609090209010b090f030f0d090e0405060705163c0803060f01 67
    0xc01525901101006c42d03955862000c0800c0050411000072512020224526040003503c3c18803510001001b001c0c264a05010b0001c103001089090342004402d00c004070711000c042c0002e203001d2079158014011098150100102c00074050040080e85038200000c1002091313005070610980c100b21100407000c0028004a0940030309080e800c220391f2485151200c00c40c0d0020320007000c0080002c08500e000d1444a90003040b004d02111401c20104103810401c89101d05041031441c0d10705241c44200c02600020101d80c0e40a20b0315002c6015030040e1141081c3c10b80c00185d0080100507c110a01800c64907401040700c0074010b02500c952640700080880041d1901c054000600b100a01242c281c0e12a07039030a07a4552911001a00000b81c5002d40041c00d400d441032418010ba0704140900040c1c0c4440c4010f542d590b00c105a0b05001c41a12103000300419442024448540c51340350040300c1d1596034000fa903212a40240359204100c003091102c1000c280c105042d20781c032903410748810300701494001c016 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 351978417 1106 351977311 351977357
    0xb030a0f0b0403110304180c0801050f1005360f060a0c03020703061d010b100215041110020a0516060c031209120e0a050f010906 57
    0x1400200d00d40a0400d90440c1c464100004881859840e00c2d045d40c0043c1d1092888440d200c4040d241409980140da8a440c12440c00594a40c1814002442c890910034094000ca40c16910a00014022400c5400ca60010300e80e40202440c5103003000c007030000c420318a109034217424010324810b0501c0101c4004503503006020505048503d107040300d0001d0540c0b010303000c5120303c1c040000170403c0c80c410b94003007210110580c0c42800944808a095400284009003c0e000303030342c030b01459550b0100c1d4808504114031810a070365120789c2000c03200d02d003004001e190f1000b004401d080207070350005000911180300d44107541061120806480c5041841d02c5220085150000c003000041d120301851480c8440b00000000c041c0904c1c0c03580341c01c12503503040c0080403e030440702400c082e1400c000580e005103030072650f02041c60300c1003000800901491007840d061000c4042da02d000e2902c10191 = true := by decide +kernel

theorem cover : BRFrame.Cov 351798561 351978417 := by
  have h0 := BRFrame.cov_init 351798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 351798561 ≤ n) (h2 : n < 351978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
