-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2900
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:05:00.700818+00:00
-- url     : https://prove2.me/submissions/2d1c0ce4-353f-46b1-8da3-eca2e5a1d549

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 521402877 ≤ n < 521582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 521404127 1250 521402877 521402881
    0x60f04021e011215050109080115091a030607080603010b030f030306010c080d02040609150f09170106050424050d03140d021b010c02160b03060402090f030a050115060503 75
    0x40ca540001018403020005621a601c07403a00050340e440e0003002c0c4030890035141c8440040b0034031403a64084119502a240d401c611a01d408203542039072402e44c0c10208601c8103000420500c4150703441000f00000c0b00716030301c440588440c0003905120055411400041e905428481c8918082c031480452040460040a091041814064503404000d001c2030501c8901c0c1c14a2003885140340481d21060002030301103590740e407119400b900a0555018800390742e0b80e09554181b20500500c800440d001180d214100081c0c0380c040310401c4507121030003400d403d54964400046030f4946004904488414840c00d08411010585004103140d5640c0001e22a910401c492400300b900301040c000464050030310284d4038000744800ba0064447d41406180340d166140329458a11419801039030b102c2e41d00c1e802d80b85010004540c10b054004103020300954441c040010820614166000344150301c0050045051a02c118001a00b45000100c044d905030b51a411001c403481e4246600c00094a01c81c105203040d8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 521405377 1250 521404127 521404129
    0x140a0206060d0c05211509061501050408070b04080f010b01080a0c0c080313060f0c020c0103180c08060f0c0a0903110f0619080903040e060907120c050c060f0402 71
    0x40c4001030041409403080c10b000310140b11030520000090680070b05140d074040c0401c54085c410440c40040c1d4001400385031401d100c0740d00d2412819004a14000040c1240d403100c54450300f0324941d03140e0b03081c18080c04020000e211742c01408080300801024804030f450b945072260b4241058141000101c140e450300107848040d030b0b04004182e40201502c0800507410350098000d480d2405081800f40070000c0c044108501c0c0c28002c2690f9144900c640e1090106240800171402654241000d00d030140e00890032400842d403003540414408078445009100700743d403a440360b002d4088240c010704100e42200c0304000340007100890a9804c100c8500d03900d454046c00300305c0101440e08034000140701201424004400f1758a015454814000042000369540c807043c507030181c0500d03c3c0000c440130038041e1000400d0f00d00088103940c101c1d04103602c3c042c0c00c3d0340d030201000041d4000820030014003611745100861000c0500c561901d050261f2901075643d20000d00030742c503000c0001d181403980c4a01c41300300001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 521406627 1250 521405377 521405383
    0x3090f150a110a020a0e04060b0901031106072a05091005090a05040614070e0301061706071404031406102112030b0301020706090b06010c05120306060c010c0f140a02 73
    0x2040342140340581d4802c0e002c0d07400c0d40c1800d41038800030354401800b5401069501855030b5480c0150310801d003c00011641d0000e0280602c0240b0002c2c2c0500308040908000341011002454045c2c45110f83d400268503003080f20322817100c080c800c00702025500502340580c0c10a085055000220658440300c59894000020b0401d10014003d60b0201d88074804a010003465400000300c21b007005030005c00c0ea2078071ba83c0c010700c4001c3c00f14040d40f1947c240280080d0601035005d10105121400024100f1a82c48440030b0310314a1010b00b90141c0d04030200000004103e8080313103007440201d0400074004900309405880580480c5800403c00f600317a15900203001c00c02e101c0c2010407664000482e241c078080d0024150020495000720036015400010540100001303035004c6030070244106001606a11a003004540040f039492000b0700d154003250a1807044150503024560260703004140a01c0c10403041000c60130b5404008406002c120905609024141c00600400301c440c01c02c4800e50804001040081d6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 521407877 1250 521406627 521406637
    0x6080f070803030132061c06050105090f0d111c03081008030706090201090506221406030a090f06060608060901081b061c02040807170303070e06031f0803090f15 71
    0x550701c03030140c00b940100001c40e100c00e10f246500521032921503108110703c04141003107d4032120110b1405102003029030050040d42d601141c09080b00040c004080c0510041103507070310003a12401521000c010482e0b4900a220340c2201c07030440e590400380c50034074020301041c0c4060301040780b040403c8070030300070648000f007621041c54102401041e82074180c00140c908200c07503081190004400034403004100307549003420b80c1c4c0d07080b8041410752a44e540c10200000080e0b9205941d400340b001c002059010080790803044103a4092010030703074180c003103607500e0b0116002075101c4804101c03070404001041c5001078295004003241005400744205854062480d901c2607201e1501ca200c002c505145d0440c4c055480c858980158502195a00d848174416035590a9500c203c070070b07000034503401d46c0c100a00401500d00800b0302e9101d0605c400d00c11030421110707400003060341f01c40101c3e8101d03c01282405110501c01082c4220145aa640c81d0700b050080425003024000d019107041a4403056280e10502111 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 521409127 1250 521407877 521407919
    0x18010c1505041a011e0b030705190e0402070303090b1f1503020c070f0f27050903090415050102160819050709091109010e04122106080f0708030301 65
    0x716640c803803401c0c10403412540303150001064420004104205942c2902c860301e1461819107808569a91440d0803502c000c94000c0e0000d2070500006444291000381c0519190882c10000d000c0300a400114089070400755068000075140c810420901c420b003207140740c121501d144c03441e4007400c2031908040c1c404054803e00011180340010401080d200c2d038141c0780c0103402401903030f2986644400400c035102d1540103d00b03c8034070700c2d900040d000030a0141c0042e1203100403112100f40e0501e0440a005120041c000c24042c042040351081e180c1c0e0302d00c01c66101e512141150a00581010002840c201d00081480207444501c0810f0003503000005081054030f544814190303140c40645860780c280402035200c0390791242040000d50810502803409040c00c070f8182c2d01d456442c0c1c0d0300d944000301c541d0f05031400351126088030580040300c3c0c071981a0311703081f08480e0800c880c1420044026000c68030103500272500341c0c00102c032034400c02006010305030061134003030002c42c1503506003915a01004c803001e9580f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 521410377 1250 521409127 521409131
    0x12170a0609060e131203230a060f140d0f0204020d090605061215060d0c09020a080705190c06060512030408010b01091a13030b0702012a0e0609030a060c0518010c15 72
    0x1d540c2507201c3e0f0410f6001c030311541031714001640f41c0d8010148580007a036041020909080010422995603502b0404440c1200d02300b401d200307480000d02031550f03100d90041d207007050b4a100c16030240e103490000f052002600388001622800c1d9081000403104040c1c00240708144408407801c291200050384000002e24025418840d100c82002451040000d00000c118a403020000a60104594040d003200d14043c6c035000c040d03030340765401103815100f05808001600d01d120060340440c2c3c81522542641c0744917240c000344685c0c41e10000340c00d001c42285080342d40d43c4009424090700e40b082c02408040740b021b0078007885d0b050514070580c0c03400740300307161011350141c1c0415801c00102241c19518001d5410030b001000a09000300000e029140c02b4002c2e204400070009090003a030050340d0f4100844582d030382c45000c8441140100103641c0c1c0310703072a0380f6030500c9030b44c3c0e000c2c011a10714441c20355070035000e4513131507925543e0221440104181004860510411042800c08601c400c0001440041c281c140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 521411627 1250 521410377 521410403
    0x151f03060b1f0504030506010e01030c15030603081b0c0d02090711030d05040f02010e01210b0f03030a08060a1202090a050c070b07200601050a0312170a0609060e13 72
    0x104004080003070040c1c10b1003140b1030b0004000394101004005403405113064034016a280d140020740f44a083c40010304844505504100100380301c3c9a0035040b214514002c00d000d0b40d80d4a582c10b4580046041940c2c40781d0b034240c0030040d590104450300404106a45803c2e81030065000580c0c002e9004040c0000d110032102d0a90218400303108607254030441c1c0c4810016820300d818948400190701d8022808101c040c0804070f45e40d03014642510141c1c60001e1500d40e0307007005680c00006410311106280c3c00032202c0111202c02d0342d051000e400880b0740d0366174100fa245403503401c1200c42200e0368003112040036107100b4440561102151035070b103c01c2da905d000c983d80d21402c1002150340709003a406002c50f00314070700b0b00240300d030311020001c103102c021700c2c00e542c52950310320342c05450303980c06c1c030803543e101c507014500b00001107820380c2c02d200310030702820a40203002c46c40801412500e0100e038401000d581c7c414040c80007a000344503183c00b4200c40c21301e2001c0d51400c203103480c0d4036140014000e0001118a02 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 521412877 1250 521411627 521411629
    0x120403020d0c0308030421030b3f03090301180b060616051b010e010e01090e0c0c1005010614032703090607080d060806060d06020d0b06040305151f03060b 68
    0x1e910020b50740130f0395503540da1501d1f040004010140302c64684001080c0c01000c0c43c07140c820b0213401240c0c0c0740148000c2000950614002c503440005000251400d84906080c20000d02045401300310391120f4080e42d030f1070302581c00709400c40d030841440e4070807624024524004a1440301f260b560110055881c959160781c041da648103c052604001040c1e072040498030a03880d00c09407410000c03002c0a0300c42c01280c0003000010340d4003080c40e0b0b002900140e881d8038100304003604850303082e401c0500d40100900d071200c00000c050038a404080e50000854481c801089002e5004901541d450105500d0714154104a8030769080783d80f0991815400ba00c3c600c00c081201c0d1410b104465064000504066a42c801807074401c0098000200c040001407074180000340d00d0602003401c900c030780c100401c08210008555101002508a1035004903455a501c090700929110350000700040c5000308010000c001407503e42e043d181c0001044d506501c1c3e0162144d51602c510b0940100c00d60758026004600e01300200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 521414127 1250 521412877 521412893
    0x90c0304081b1f0c08150f01050319090b090c0d17072316090c050415050d09030c02030609010c050406030b0613120c060f1707110706050a090503120403020d 69
    0x1051007103103d144030506200902c41a40030159a0782180c442c00c14030f50754080f03c15980c9200e40c80d050f40100d41400c003400c01c1d6100d4801503500c0b00748040080341200e1240307000d408840603004100e40d0000c2c1281400003284040050480e000011101c001711103400d036882a400c6901d0560b04280014003054030810042601d0301240618212015044440c65078940e0981c0c90302200f46007504d000c038170b034008034051105004030b81d030b9500c4503220146024942400202045001404001048000d0001c1c0245003a2070140a1400f40603035a50f13014040507004040c00d103031001d025520b8580c904032080c0d07200c0750000240c130300b110110304000901500c1e130800310742c0302d200700c01c01c074412009035410108030540550035640f0740901802d94a08502e80700d0900381c900403d103100c900003168425504041041214110560221741c5241040300d415111503140c0c98198180c20003c04200701040c00e141da140d00c542c086008100440003455001480102840c0c148a98003002e4020f45034801c490080c88585 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 521415377 1250 521414127 521414143
    0x11407060504081308030711060906041a180d0b010303080a0603140f0f0316080904060806040302010f0e01110301090903020f03030a1509090819021c0e090c0304081b 73
    0x520240642d01d400e1030200604d41c80b58202a0380040a14804030f040380001041c6c43c14507030b00c10550b020001072041044003540011520759440301e804c00001caa1526020704c40120303c41d100e1000c036200c02c9200e407440391140d41c400880d8099088031300e2910101386251425811a80c040c208408152034244404000d016207400180000b1070151042c16540c000151101012241c2015903c040d03075100c014a07280c1c0302c0d650705164001200d18241d4049100c1200130009003500802c0081e845944001003400d0800844003500584d54503200040044481d01a0460060492000300321034210201511030300d01040c0101c3e081a643c5215903420180200941c0414030000c00880e6100d20340346404401500c0030103085031524190b4100042c1107120b50003110300060740554590306140413100c0c04042c5618a0b541d20045109036454141030942c0400141c00e20300e801d41c0e502c428081180700780240403101405031414204100104004a24460300359101d440c26042d0345030055003142c04482c038100e48 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 521416627 1250 521415377 521415383
    0x905010f0c020907110f0102280c031d0f040c030506040f0b010210090f020a030b010609060503071d030c210c03032b0605090c0712020d0e060f070b0c0307020f030306010e011407 78
    0x800100c8018882c4c0000340c030240d00e6002c10626038400049e0b1811103000c042113000401140d80541041c3c541462040080c6c51b4480181082d070f200c800050005042d10810030040380400e56030b005101031800c042c0a1460320104100c8184880404200000d41d80c40440b134171f0b00c0380d881e0b990110004120704d5248240003aa00100300c00884c54690610b400462420700c603020119292050000e0382901407010790b4401c3e02c0c240c0b80c039071844e2a0106c2054600039102c030341c02d0307141c083c1e61006103c998510341180d60201d00c050700c2165a16040c0c504918006001850070321a070700074840301d041201c118181840d140304031644104501030b01e01064002d0100c40c1c10880d4450424410401207040b070001030b01c0411b0080b5500e0013140141e400036602d6800202d10340e030006a4080c030070b80385402e02600809144902080384c500c1c05c0540d0316003200f00d00c070540780c455966200005100c1c4107903040003411010b1070303d03002462031410480b00107009000030441f183d05000400d1440040c41d030209040d00c04ea02e070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 521417877 1250 521416627 521416631
    0x70c210513030305040501180f060c030203130e01051c0c0311060f071a0a0912080c0d090c0f060504060c1704030f05072402030d0f06050d030905010f0c020907110f01 73
    0x280b01d1501130140c1c0c00c140102800a1180f1aa03c00c1d4041651100400c5a0b00314030280300090800804407803c61403900d055080d03100400050603001448040b09000f00344000060b421541000c0401174034014011100e04801e03448040000070414100c1c1e080110795100390440ca40107850720102d8102d00440c1c0d00e03a6818480484d0220500891403580700700c0c18a03a00200081ba9034611a0b03204413401c880c005400d1624040442255500a00071642c01060440c4039a003011010180d60007507030001c020480e070300102e00408001511041c540e0001520607428868201800c0c075000500c1c40080c90300c05424841d80810f10708030285140112800745803c00300e041403108290400300c0e92031485100c0d510b54840c402800c200d00403607124200841e401281e0145140403002071038180a00035482d2007612082d0340e104002525030390881000e2400e80310b511145c040034902000580041c0141c0d414000348941035070228016074a601840d40d11904e40e003000440085903003155417604070b0b600e54590041d8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 521419127 1250 521417877 521417879
    0x60d03021c1805040507080a0b42030610050f360906220b0d05070f0605090604090e120d060503062d0903220905070c210513 55
    0x1a5002ea104500c10440001200d5120b903100140070468000700d4110300080d200502040a41007a600841c491041c028901e1448400074403c00e040c104020698903890000101d100b8034800c5151b502a03003050041000c50f00314500a8003250134100c50010b80801c2210000302c40c00b03415a07160a4410301d41442c11003002c42c900c820f880144540c040c00301c50200003451015258540b4190b81414031500000e4030007000706aa1004800c40b40e10001d580f9940c0c141c580109441a454130040802c03041c0c040d0004208051506411240c0c00707000c1d40240c0704120040001040c5903c03520102c0e811101500ca0000b20070f10030950b40d50030000f031078140c44a4200b00103940321000160780c00c03540c01d44008506a49542d15032420303541c0807080d03048090150643c0740c42c140c100000c40c2180e00c0c1d4010800c0042e28a055481c10f042a08404c2007448070569107a0a4001d0100c0316091080e9948003c1ca4207000424400d2602c0b20b681054404640354114200842c8030307034619115200361132041500c1c5a06000c11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 521420377 1250 521419127 521419183
    0xb040e0108010e010e0c01050c03190302070201170c030c28030204080115120f0201020328080c130b0a09050d060507031410030611070b040609020f031203060d0302 72
    0xa0000388200c00280d070030007001403031020701849218801c44c2d4010013441c070f0a4003d0010358143d04002c051001e00d005c18418500d0182c560904850120115503005035911518400034058200d0405806400200c440401980c2c88981c000c4070703007081501c0b4040c2d03100d040a80002024112411790500c1030318449080c481000d03059009401520807000003030000c070907110309021005420303202d20001c40340607104d400003080c0c46c0d51420050301d0061040d20f00c0d10f120148140e2158803003280c050340c20704040800e2002103078806d4002d5008001c15520324540594203107c00c4880c00b031781c080e080c024003001614403c0c542c0101003010050002030003000703e12a49051180080100f2281c0c03001107414407034400841001c1c9180c641c480c1e40e002016910160030f42d110758004102500250300d803900c2c00c02c07004010880600d40d9030300c44c0f8441c0c08041850506881030200088051040341d000c0c0d40614248400c4000325810b490348503000361740d9014000c2c04c6040c12480c1007906044c40d180c80c41d600c81d100110b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 521421627 1250 521420377 521420399
    0x3080a060503190b0c130302060d240e0709140f030c0a080102120610020703060504020114030910142415071515060c30050a1e02070b0d02040b04 64
    0x60303140a584e4407452503446120000c8580306104c4070b00500c0f00055001d10051825001400100c50710380400a1302e424100040c5545800c5c00c2c0f0b00c0d0007044078040d000c20403200225030041c0d02106a1401c2c0021038030740842c40c0b240480c0c28060718400d00032042001f056450810104004940080015070b4450ba601c030424003d50003100078119040e003040c00503d050404600c408110070b0940d00a00c0058616200c440050101500c2281001000c12266a00c0c40003e40914028a5080041c00404000a06030400c503046003420400d01da41e410200502e8402c0b0590b590794a5200c5030340710007030104030300018280d46845c80101d10500400b080d018284514040c64070840c01840c0c00c10404580c0d1081c1400d402c0a0a00c58180081c941324031000c00240310003241c42c58160820300050f90008980301000c00c4101c02d445420001e8404108041a25030003140000043c08088101e8103801140000075210646402030500c41d0700002600000c00006a0464005043d009107040c0c51315169804052 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 521422877 1250 521421627 521421673
    0x20f150315120a03050301180e0304030c170703031b02041e0212010807050d062c01020307020c0103090f0209130803070306030201501c0e1903080a060503 68
    0x10082c54200c042407000180041c02c484015055120181580c5c03901d900071700f0808040c0c2c10b4403101074a40310211803204c4100054005144102c00304802941456105814000c0003d18440c00d6444001e080000c660020803214036000440490707031000a141c0003080c09084402078090003c40c2400072910418850703030160813001c6c0110308403d42c0d42d9a412485540c1e0015000e0141d000d4801b1064000050b00d50384805008a125198114041c00a50340c41e54510390f00c04816055940000070484082d42c10312481e910321400b4202000340f548142c80b80074460080c000001d015410b9400840c3c0b00901e458250300300306500c59491580ea140c05000180a080a48403c0380410301c07040726210341c0c104205002102114041222140c41450780350741d40042d2021580002c4e200c02c2042d140400104680103180c3c01d0b82040c201c1703400c2407502c0394840444d1249459900140c000385502003108800103200b0400d603070145000306181e10388030001002440558402941845401560f400c1024401e10a46c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 521424127 1250 521422877 521422879
    0xf0f0612240906090f10230f01170a0c050609011704121d09060d150906050f10050d08180901080c040c020705151c0e1e010606050403020f150315 64
    0x3c0060719031401e442d50381c400d08403040c04540c010303903005014468940e1200040e003c600e62406003c080c1e003640c003074401c0300950711805049500c0300184410781e0107007180d8100034420341c0101865051506c1f840c3c0220030740e0148502c10480010f98201b2684162501460b00d10714203000150b82c02c0510340542203858a0310401e002c40e04850940b0341034043c4000c01c50310f408025002200b0769443d441003100c0300020003030407607540c1c013401146001c01e0190300c90b540005108200026240c2014900300541000080030b0f03401b4042c001c803080c49a9110f13001c0c00340c0116440000d407034607045d2400318032090f83c01c40c411180c0c011008a000040c00d80c00040e030f140c2203443c1510100240d00d400720b4204d8980d4443e0103940c0d00110351040c0e01503000d10941c0208032184450200329000079400d9118000e03034881c1454140c080c0e01c000420218840007200da1000d0b80c4c00b0720000c2140300c0c0b510750701812500403840041d2044501c0c0710921560b44600d41c3c41210040f924400c0c5980303203405040d221605102d18495 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 521425377 1250 521424127 521424133
    0x904020313060b040c08011203090b0c010903080c0f040b03150d0c03121404140310050702010608070611060105060d09051213090207081e070f08120f0f06122409 71
    0x3884403418148a14817404c080c0d0360b0303268180c0e030070a091190841c010b00001c6080101e0050700143c40511140501500b200c000008035100c0d10342e040c000c25404000c0e0040d101600308024161181c0480c0c0100c17030403191144201c035141d65440b1169642c42c00c2c09048250840f031451401c20800240058403000d40c1d10910054210fa5501c0c07500711860102c500300c420b9203420801040c840305000e8803e0420f41e0740020b0442e80d684c6c4e40c00d070660050710416150640541e45404003801840d200344007084c0500518600708240d04012803965641e800b0601c80c9034068100001d480d0b0a00c0c41d1070700203d500c90740200c1210001a510100700c0d9065000c4406411031403895000461500c4003402103031f00954000c0000b50420214100362120110b800c010306040d203100f0000e410001b01400400b00c2e482c1e00035641162101c4803170014030105500201080c540c0c0880100b04001003c1d00c80708640c00c940300303541522207888064030180c03a0182ea402c0142e11b090110340300114046c03d0324500c2c1d1260441c0025 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 521426627 1250 521425377 521425391
    0xf030a090905100302090a0b1c170316080c040308031005090601020304050904060c03061701060303201b0a091e0f090c0303110c100c141917090402031306 68
    0x241002c03903600303954448100d0050354041025240602c640c0307030043c24602000031000804030005412052480c00a100041301a094005100d2142048840d06c1101d0403500d203145405881c5030074840504000400380201c00300440d514a80304011f95010b183c0c0120030a689040a1410b0704030080360b4845e652086840f140010010351020055900311500501060f06503202c0b07a48183c042c0c00e90b00c08000400d07a4400c000a4200210204c1d100c40110039400001e5481c11428020311442d00304150280e24a607414015100b213400044100e90f500304c500c0d50b8103003001e50400080c8038801d6544061513050070010008100001e4001e05610704803408400c00042440c3e003420001d40310901b8014140c0c030000070703080021070300494105117010800000d440c4034202850004a0044a403215072000803039100c610b0f07042203044600d820010210310010035440d500d010b401d070141240050001d00a403068003501464030301c01e4054a24a0744002d00554484c50081c4880c1d0001d00d802d142500c480d401c242c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 521427877 1250 521426627 521426639
    0x1312050c0c03070f0611031306080403080f10030b1b0c1f0912050a050d230a0603021507021305280b0d140c0301061716080312090f0f030a09 62
    0x90ba030b20495913181000b10000d8070b050002e480b161050031801d18240410002281022003504800001c2c1c91240c8400f8041d0601d07041c010725554000b044414114007500c10300000408001070a421250b110101c4102030f81c4003504076100c403040c0d03610750a14102c081001a000400414103881400c82c0c8000400400c1568001c00c040e2115110042d04806c1024040640c0c1481600141640c40f00703401c11618085041250800300c4490841002d413900c00798141540ca00c14202416400082001e810700c003690554002800040d01b802d8058802c082c00211401151100100c540b501e0800000c2000780c4c1c6070212404102c12400410310b040141c0d618083c0c5000c1c107851103041d102c100040c02c04114220681e691a104260540359444248100001420156024001d250182c60f10000c0072058a54280e051440c20802980f000c0000601c0d031003d1003015400025a2140d16031002004602d840d50f00019042103d59910a6024020079440a48614000006041f89080d5940d500c4560f59548 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 521429127 1250 521427877 521427883
    0x1204060c0e18180a0b070f091e1401030e030d05010504050705070f03050a03020f190f02030a05090f04060f032901080c04050415060f050406080705010503010306051312050c0c03 78
    0x421800d016a00b14000300b00e200600b00c010a01183c910022201181c50680311841c07000d01c04c490440001c0d60800740c8484c8964049581c82c000e00002550075240003d0010042c4515140c1c000d96144010382c071800380705603200c1d401040f180110041520f645251700c003d0034000d84401d01030140903d04100c081800c09210380200e40b085078000d1100d0000d0440c40c2e400310365a81c400480e131400c041c2c0a100142c9900c0300c5900800002c188482c440000c9024a4009801040c188400800b550000c1c400000340c9031b00a0210b0307180d50005c48078040c2010342d4500040003400190081d0740c42d01c03e00d120100070041011a2101c07002c038881d40c40c0c5d6240418203c51b0060b600240241005500400c01c65070190401d13400180d005407040084c07041100d082c821a00844200b607012031081541d172041042541094030070200648044006401c000d41040e001030614441880020440c981c1d90000031071443d10700c29003501e040d9100214a4911550310f9000700700b60414440d8480718056a1104d4090b40341c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 521430377 1250 521429127 521429149
    0x506010e0f01082808041401080106080c0414040e01050c180a03020f04090309031b0e0f070f0c050a0c0306020d1503170d060314011407030b0d02151204060c0e 70
    0xd50010b003160084000c0300c1101d204c1d442c0100010700c8104070450001444800544041c00004070420503481042d000140031900c181e06c5001840041030501c400030312150201e030300f62044000410100c6290001044c02091881d02e600099441c1505000200c180c0300c0041a0180500c09070081580b03c00f010002496102d00c8001c0d4040310304a00d07140181008c2e0814140c450003420010003180e929100c5507c00c5a2419101c03458180c2120309001c17118403d400035401003085040c8105500c2c1000b80035040e2a01c2c0000b800c103200340c122002c0c0401000304542d850a80d88101c40d03014955480c9065800380d00240041d881190030030110000d1a9160403100003100c0e00105546410b4144503014546540030306100c1001e640c40740000310100340305612009200b0210301c00041c101e0b07498086c00c1d80c02c041c0035000717000301414902280401d94412003003001c0190111500e2004e0b40098084030224811032800a4011a00c1400c00041c40200c0e800103020100075110003446e03040d00400c1000302d50407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 521431627 1250 521430377 521430389
    0x40b0105130c2a0c090204060f0314043905010e12070b250f062904050a020c0a050a021009180b06040509040602040f12030f0809010b06070506010e0f01 67
    0xc000c60441101108910300003019450a03000380701420f00c0d03103070321812031402e0304843c0b0001d80000e030410980e03500c0100040081300c1440c0070003440040314882d0701c0c982030191014065080480072a02d81d411100c0c101c802d421492100002c039032886081d0265194036500c19580455115840801107003410780ca03c03030f03103100d140700039001c4d560a100e0940620342148032428001e40034060360f6000741c088004c03c0c1811501a0016803da07001c14034051042e150041c0300c4030300e406908480c8482908405201212051040b200407410b952801b003008028001c0d85940b9103184240d00420003441008207140003480d0013500c0c40c41071140261820703209482a0300c2425100e40c03108074050ba003400c007a40b0034002d580008000c585065a01c9001442040065405503443da034006020410100f91602c00340090120b0b22000c1c0d0b20000d00d84002e8a4903101441c0d00050015080005200190a5100c10340c441030042038240c5410050030184e940741e809026401004201c2d0001c9162407504410150485403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 521432877 1250 521431627 521431637
    0x3060f0e0f070c03200313050d080a080a15120302070f08071202060f07140d03050f061306080601090c1205010b0a0507110607061a0d020a14030c030303040b0105130c 73
    0x82c1c0701c004568035004040c00340c1c1081200c0c4811080e10740075030214010700407000011912018140c4403002d8519042d03000c2c0b44680b9845511100045400c0191600c1055030708200324103980d0f240824001d40410640d090407292200c1e00418007090f4914a0140c0c18002e44c21112140d03103e04120100a4407400b80e08000e40c0a00c0d4100321450680b0ba5a80740703544050310590420410308080c203002d400c203000c00c850b007801210030702019070820031141070130078003500c2c0134044c900300010b90081c0242e0103454a03000d0307810300700318040c0b03100c40e034000034000d20b400c504075880e56942c3c00e1031000400c80300183c80b000920311031600c218130815016550607107400601e201d19000120700d09880c05c4c5c0c072a04040382c6a424134007100a483e030303500b00a807230716500516001c16811403d1007000011030200940d00e04c2680300204c2c44001d615250304840583da6100454161044000c000a20b00040720003842c1c0d00d440300208000801c00113003016412a0300648000c07800301d02918804054400e40905800064 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 521434127 1250 521432877 521432881
    0xd0b010b090117070801080d02070e0408161220151314100204050f030d2c040504050a03020d0503090a06051801020d14060f0a0b0a050c070603060f0e0f 67
    0xe5400c00003802000814180341142c682c007590000c254900c110f03409400329000c2001000216001d100c2070044040300e1018080e10340c200079650300200b42c0500054034881000c503c040100c80007400304125590044015500d001c11030b14020141c043d940c0080300e03a40700303450500b2030f261000034610101c10982c001080c0d09940c0c810748208189a640780903182e04001d0070049400d60014003c0d9201840c03440005039960b804e1106000d000910542c0a40c001d80c00b101074252816800981008030080c8002c004030895100c058900c3c0700580d4a103400c3d0301900d400184010030100040e000300d458440c5c1c00350362070122403810640d85800304491440c400d8200101060004007940c2c041a800400032504841c1400e6402c1d1060072600280d11125102e560b8407046039100e0710f049462544220222a03000404181a0202e0134024151094458083c004212107988501400c03e49810074500401c41d0f0120343c2d5200e000b40980060b20964008600010700480c6030051021950700c11044a11861259 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 521435377 1250 521434127 521434139
    0xb070b0138030408130806010905150f0d020f030706030b0a05010503240a03170703120204050607030309080409020f191b020f01110d0906120603050d0804110901030602180d0b01 78
    0x3580c0003c0c4101d07601c01c82085196458621044103030301030900e0070010005581800c0401c41140e10182818209070484818110b1558603003416261168054803128072224151002c906041c1c0c40720030487d0b050140310404200c49038140c1c004030b46101c0c1110b1140301940c0d940010340707041c1300c2030380c2a80c1c01040c01545048841c40808801c46822030107008086510382d6600c5098940207166031006100100140c0c0c0404c1c581d0107055000b203682103c508625051404000582d640315504009041c592904107200600c402c120590b402410744507419962201101410489580030b181035010640f080204413160310700c9082402403c865109000d00c0e01107241e0204405011708410f41e07810042d02d003000303081c694030600485110710402e48440c0c40312410514050644056290244021464081c040012074400650a4100001c905058042e40c699040c00d00c5c0e4008501034132904a817030180000100250b5030700800c58164003980d034041c000c405000300702c01482007000c0904843c14880047c010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 521436627 1250 521435377 521435489
    0x2003070c0e040b0c070f05010624030c02030d090c080d021c030902090103061805161a030f0103060b0109150e010314060906041d070e0f01050d15150b070b01 69
    0x12050241104124000187da44e090950f500e40d0007031051803080719034014440e0b1036890000768810072410240407030103000341c0083d03407030041c2400d42c140b6584407481e41e410310007442052000790040900381c811203020010043d64410b044c8883c1902c0b1110301c01c500c03114520900c03039048030550082840d0700381d03481c5848240203001e80540411041c443d03500320a0000b1401c228056001c5d2400c98413950a52400e00d000104c6c80c0b50715500c844045007002040403e00080b030100d030641358420070020b06500740c0d4004940402e690f800948841981c881d07442c1d0400d0708101d01240d04202640c041c081e204140c48075a54120040c3c40c1541c101c42c202c404520145031035003090700c402138940360945110385150304d545c3c50320b105584402d403d02c18041c00e100c809208281071741d015103070554840c40b0507003465440c044d508568440c04480107650300d9109240c00d00f5980b00f00010500a03208603100c1c02d040c18240040303003080c829034459a4400803060360008140b40304c0b2a214401c4d001d07803119a8001c0c240146 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 521437877 1250 521436627 521436637
    0xd0f020a060207020f1c05071203080c0a170705190309050318041107141002090d0b04021c03110f0c0105040521030406110c040b0f0f012003070c0e040b0c 68
    0x7905c0040c420a80240313403103011800c43d610030300405c5444c8001a40c241142460119000400700300d01095922001c6600024601c0d00411210080340d81c41410560440b0f4249410144100c400640424003030300c0342d844005043c02d400001c103c00303282c2d40c020030181c0445909400041c8550800e12850071000d00101e85417032507000280c40405c1f500030b101034405507603000f15400c803004551816070204241003040310800c2c00c84204401c600c0c250800c00001c060b001044001000202040b0006d400c42d01c501d20901e45844603030f0043c0458203924078016101d0441e25000340c86a02c06c198803c1044e500002c2e004501450685030980713864240b5041c840b180c10405c0d142130840441c202402c04250742000200001c1c80180c1d50400340c142841407082c28000c022201c90720443c10700c50b1000d250340e1030380804200094100c600749505855800181ea0500340750a96210342c04d1803600d450130000700800107200075407040300c00d00e01c03031500c0e510180341c4024140c2d006400601070800161001c0141c0000306 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 521439127 1250 521437877 521437879
    0x50703021c030e06010b090a120f021906111c0e0a170d080c03040c140f190521031b1603030306050108010503011e05130c170d0f020a06020702 63
    0x150581c4915210080c00079a84400c801c0001d99500790925140010b01c4598090040d038502541ba200040000490848590144a5400507a295450100119080305500881d4050030401000508010800c403081007842800003040c0300d03e4000880e582d0200c0c000341c601c0070084203440030304c075043e004031012548400c0ca144c02811080b40030401202c200701008015043c40c009100101a9000082445001a200c41d06003501482400002140d0a20030801d40d03e00c802000488030b52070001894150800e4403c3e5040241c020b02118a0180319010500b0396800341c4106110100d445400303001c10b001c1c03070310b8043c45400600429080420080040b40075152150840311424041c010381c00c410b89540e0701c101d01082d62950100841d58002c0800d07401000101c00800c050020f50760218043e4041d20320b209402c1c0c1d602c500081f035420034506d00141160f0011401d42e081515003100304042003025610480c94403c8041c10f0580e1407161040c00c08040e800d03030244c0b030145416650f00c0d010b500840380403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 521440377 1250 521439127 521439133
    0x80a02070f030b071e0e0d020109090213030b06030f21040803030c0306040b060910030b060c0a03030f05090309030a110a181e020c070303140f030103080a090503071505070302 77
    0xc03059040948400518021801e0f44824105039001030054030141140e0000e0000000a91030220b03085100e01d8461801136401114805040c80100c039255040c1e040841c000d4404907029503058a48145503058911403581595283c40740401c140d03070740c0d054000001d400d500044041032011500688a10010254020141000d440d03803040c3e401c54200322205500d1a4021041101900c0c03d4004c1c00210302e4180c600341c0c0790901d031001003a0112600840b000500d521160f0700301181c0c6401040741e001c009400180c0d039000100d8a00240503020092089410a0401e004034580344004000c96242120050041030350001c0d0f65581031031041c00054081d80007447c1075001603050450210703020311201400c1c0020b0020600c030815180540d021180d0002030b40f0500940790107903030004103001a40c2c0c16041c440d0082d540740190920302c0c8142440f00a00c241c0100c000006c0120341009031240a046031107080045444c1d45c14180e0b2021207124004401d510b040a9060300340c026001000c3c414064810307 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 521441627 1250 521440377 521440379
    0x32d0c010507021b27100f06020f0c2b060b0405040b072606060705160b1b0d080115031803020c01030c320d061e1203020604080a0207 59
    0x12003030031120112100000368000c12000c411030088403200c900300080484900c500c480d902008080d5204042184c01000b019540c00301d01852034000b00f05000300008005120410780310100203403980a0000c801d1447c0c4941c40b110245403900358150380c0c0c200c2c483e5011883c00040c285101d4840c1e1601c60064a03000da40c7e880c0703d007407510349000e4103218034020021807181d41410303a07000b4039014880414048140c61014812140c0a02480858228400300d8440e038447c0c541303050807400c4c020420081d81e41c2d4a255180000c0c81c0e0f9800e000741807011601c5240c104c0b00c1800c0d400c1c0544403040380c40f00c4c00c0011286070041c01641c80d250500c3c83c010556103000220340d040e1030002c00d9050031400054016a100300100d0b640e41d03905000e2142d00380c0c0c4da80303811440326440b03013002960300125a80b030001020750300000c80c48055400042c1c0b024804c106500344030031035803817a60106a4207140c02855400c002c110300850003e0340d1003240054140d141c3d004000680e1980c4a4409941105200c0f004501031444 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 521442877 1250 521441627 521441647
    0x6070807020a030b0a0c0912120305150402040906050102010b10090509041a09060f0a0902090612030c120702040b010305130f080c070b031617040b090c060d1a0102032d 74
    0x82c054445c0c010f0607000181041070380d00c040d100000307990001c036403c002d103e091000a01e08039100a01d086203410089110380311004940c00010b480c0d42215045071011400159a10441e0020000c0700c0081c2c0003000074025103800c2c850050701d004090382c04200740000401807401c1c5103c015500c5801141e2422030340391200003c4803c0c41064a1008417079002d4001d2052000c80341c03250540100c480c020810819103290301140ea00d100050906124010f65841d15000d444140210b6010040a80c1aa40f03111412001070304035801c1300f10164000c510b800980041c40d4028401d82c3d0007200c810025100c1c0209554468583c0c202c264411100503500b8840710813420f00802040000e000002001512031414081e1944035901c02d541c0b02e4100043c242280708441c0788442c3c0150010340151451085548000026203001100f08815400541c002410056403900c0e50060b00140d808610070403040320001d0049940707000b20090b5600e03600c0203001c10a0003c00309610719007120508000a030919400b11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 521444127 1250 521442877 521442893
    0xd0f0c0609031211041a18060c0a0b010909030828020a03140906060604031203021e030105040e0601050f01031808030a0b03160b122206151406070807020a03 69
    0x181d0304030003140450a41403c0d4003003a0203040705246407400600c0c1000e00d003003e5081c111030695244200424001151030321841c0114004002010203072516a41c0c0804000386a520045454190b03903c146030000410001440c0c000d00d0340b02900b40d40e85010036203811507034511041e20700c5542502d8a5001b0100c0c500062140084d160765050707600c001032032194031024038002c0c0c3c10082103401c0c1034108504101b500d980d041c003034500340c1c0c1c0c00175960348824854070000e4000b8072824a1144503060200c100f0f80e40b240070b00000b54161070b002d030340c24400100d80c1c0c0040344d6522001c0c041c0c1035200d80d0028100003154444e40c0810602c0d18000b20a104e40764030740d00d540000750310588148010700d446070348080031401e0070000780ba05c01d0f50348600d8108030751802682400500071449120200240c03100402c0290f104a0340038962103409031481a6500307602c3ca0004010a075800300d0f8080c203081c0510000d5900c01400080c0200345000e001d040c900301c06030ba55100e0340d9105102c2244d001440ac030f008000b049001c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 521445377 1250 521444127 521444141
    0x705011d0d0302070503010b040e060109051f030b1e07081b1e0408070b0c0318040b1f1d0609090403030612050307020f2e0318030801051905030d0f0c06 67
    0xd40180c03004c40d04000c1410b09442e0402d8565000c1ca00300451581c5402000800f20304582c802a00002c0390b0311016600f4020244040c2d10040c600d10a00c07011050003500351000d405051980b00d0000d03038000700700031003100c8081247c0f80c40202e010080043d07149002081060074030343d8410340c11841c1c40b442c031165090100402080c3d440c041d0380407030f09102c4040b080080341c01521002402034241526075003015600d00c40d801c680010701c0c180400380b54080c1c942e508040880790000f400400c100c1d0020030091040d0004031010000a00300c1943c90010720307a8000c0600c480040903107802d103004060300602c082c20b400a0022010036540d842d0015101000c4011007840c03900c900042c1d0b07581c9100d8010060040303044c0e418644207050820400e4180080d80005501c0c1c001b8456171001d003030303104060a50042c04a074030020041035a1810f02c1c010542e01c481c101d81031b183d041b00d600c44d0001f2145200d400300400c81c001c0a40651010b42c2c070081090140c030351400d0080c07040c64a1040d94516603a078900362580 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 521446627 1250 521445377 521445383
    0x1060e090a050903091905090901270f0206070312110315120f0708030c1213170a0203010501060c0203010f06060f1b0819020c1e1c17120a0506030705011d0d 69
    0x9940706c01d01c942d01d01018031603003101c0c0f030b00b000f446240c0c100c05e11014020a0381418070340b10011101c800d41089603050005149030340007480c0070345410744c0d410083c0c110f01c840c400180300300e481c0c026000700d22902041544d0140a0403c14500711080b0a41444504c56555a400215109098400c03138800c104115400152460342c001c2c41e01c40340c00e200745929044101500b09001d4400344400e42c402500e001c4008101c482100b80110604145201681004040c0101070f4155081c9800031581c00d81061955104a01c00d40081001d00c29025010b01203c038207028000c00110311401c80b510284c8545800315844c8034881d0102c3d2030480c940da400c00316503c40110320080c1c624905010304115010701c50742071070744800e498200f9401c5e001c4000038610600381ca42d061182c04094142e005800b01d040b00c0c407403a01e600484c4214404008400e1202c9500030703407540e0807904e070751100041c081c207494065140260009002000000d0500b401550000e49543c0c2c01101651010034841d480c2c1e079610301c80b41460b40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 521447877 1250 521446627 521446669
    0x210e0603130512030105150a05130b040f0b0f07031413080c010306080109050a0321020c011410030c270f05090f0312150301060506040b0405030601060e090a05090309 73
    0x5580c0ca44141005590701c0c00c07501e015030500040211f500e0382e00704d0100601c4169141c0380d0b02d01d82d120003990640103165043c00c00030080540495426001d1000301b0648841a2600168603698a1440218071402da60442d50380c0c004d100b11000203002c1c40c036440d1010300c080802428020710040580301c019440d0300c074000aa110a00c078484a580500c034510103441030700020711050310940c40c6c0994403080854018204170507410940f400f00b62410070000c103810351501c02c0d5900d150700b2001d68081e007801c8008618244000010904038a003180c0d805049a07809501d0050f15840d205511440e400c2d08649912843c0d00ca5a22840c054018451062419030146c80024581410140320346801c0320303401000c40300d600c100440d842c1c03008070b000441e510400c1c043e0707002c0722803c505000c240940401d602c501d802c41001701d00030420400e540058410740300e0980880c4d4007030703903900741c1111b0310313552030707003110b4010b10500e010505142d03c41d000b036030340f011242d000c036860f08000e03502107040100d0300c0e10304405203c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 521449127 1250 521447877 521447911
    0x504020f03330408031b1b030415090501020706110a0618050d0809100207050f030309030408010513210e0a0b0424020d081504050106050c1603210e0603 67
    0xa8014441c107451000b2000b0480d1030707450310380d8641c4200e2002510f40000000c241802040c200000c000b162402c2d501540d54600c49000161100d41e40c0d0480c3c098961017850701d048480c1c02501c15090081103900590041c55028a000001d507401003030440740b0b014034005c0e1007040c0085400d5024810800a01042c1619802c607103007002e600701940c004000d03042003d00070911805880c0051003048007503041c1001652038129250152400c2100e070640c20f0140004000c00401c0080031000d8030444500400074419982c84244103009007400007802060b44c42082c41c159102401040d21031a402c0700360810320044200d03c0000342015075540c1c0302241c0c0d5440064240492860403050003088803d2440c200280810bc00008e5111900c055051080100b4400000d20f0b440b40c001141c3c0416601900400c05075858000061565201603020a8144a1081aa81c2c0d12582c0101802101d8000c0c52000d811414001c0980c50000c0c024400310400581d14079000d420354541c0300941c0103c40c80c5880e50350203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 521450377 1250 521449127 521449183
    0x212010b09040e0c01050301091107052401060c05030d020c03090a0f0501181805100b07060902040c020607021c020a0615031a0c1806070602070320030703020c040504020f03 76
    0x2d541c3c040260800740e04051420301c816604802500d045d03411240300032540d0390002c801c607184d9000341c0c00050304500c50345d60300048003072481142d030141c0c1d07a41d22108032035a0380303410741514103203010500140203510801c040a081840759018206c170394948026285081000400544c03881442e800001c0c034006501c104111647e0401c881c40d00c40300125083c000420b2501c440204810349821041c05126183c8001841a00220f00501e0242c84002255925043c241c188a0021b041010303080340210b10b8125003072005800060703043d228004541c0144490141c04000c01500844c954145056105e08001e500018095004403103800d502c05d51401c805900d1410040105540031a0200d00c1410240501842210801c1183e08008900302c0f012a43e02140001c02c50034031a41e4000f614142c800700c0d0100406501004803940c00410300d02ea40b142c005440045034036403143c0c00c0000c0150340b040591600354100b40c0c20240c0c3c4640018402103820405102207400c0c0006440400c0310003004540321149 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 521451627 1250 521450377 521450381
    0x6060111190615030506131e02030d1805030f0f060112080d05070c06050c0702120c0a05011407051e07061d0928020702030c1f120212010b0904 63
    0xd051003210092422418080007400d0880095001400d01c0c1e0b1034058035145510540c0b08031009580c800c044410915046040202440c0001021500c0e140d204551007200e28126031b228000302c0c4c008010340102d1822810542c0c1c154410b034001c000c0100d50560004143c0d4051000300070005030392024100d01c01148038541d04215050308019140a10b107030802000c00d40c40000e0700c00702170009a00182c41d40ba4000282c0309045000c9008049605100410404107045d10252403100d20a441c95a185200701080c10780f50100003444036007054044404200c1584070390324558541c0d40700e0018602e460350325120035003483c0307580380c0e16245107030411047d5185400030400c0d400100711a2501c540d2858490740b01001d11680200010310600c1e11201007a0845020b020414441c1d1520a650a00039640581038001e9000000305070310a0140c8810f810741402c00c1e450300350030091540c481c00e580d040540703001d4803c84404544d00324036035401d10a846648040d40c6c249400381108050064848401e0010401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 521452877 1250 521451627 521451647
    0xe030a0201060512190c080d0903110a0b0d0b0d20190501080c03071e03380607051501060306050901060302340501020711120607140703030b040e060601 67
    0x1020f2401514041d24450011402a02600c5042c5485c20304000d181080c0300302040503000508a4002c02c94010340140d0041d11900c200ea2060b0001010701030307908200001c0082500c541001c08004001000c403403480340c3d103c21180b0400501c80d00411100d5140c441b1b100180109110f9010072580c40308142d442c0000e252030240c0707045184410081d04200000305501e00180c5413840006020012400050044460b41d010212040c2c101e02c520400500090281c4401c1c0d20050341100c0e03185004045000010720100300c3c8000303853300d000300c6410000744060360b44520401e0b5113a00801ca60300307000340c1003440302d02c2c02041d103681c5c00709030141440c04100608006034880f005040c410001c1d030070896030901900c00e031121000038200d190341c40c0d0306030407020200a080c02843c651000904c0030401c025170700c440b136440400360340825180c449041c00c240e9400007a54100041442006880c1030910000000c2c0303e0b0911900d80030821101e500040340c1039480300c0403010225000f0f001003040c1c0307590101c0055 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 521454127 1250 521452877 521452879
    0x1e031005060408030f0d091b090c020c01020a08030c0f0c060709050603070f0c020a051005030108010b04020a0c060c03060e01080625090e0408070c12140703020906040203060f040e030a02010605 85
    0x16181c1483c0c0142903580e445031401900f0b940201103030191030903160381d10030b08004c0e070094065420380c620f50700003030f115410310f005000300140780c0001074038043c1c40002d500c4240501a00105115602e5880f403400d10b410041c182143ea41c0108240390030088040081e00803103607000c0c01000075007007901c0054100342040d0003142c06140d09004101030039521034001c541d00380c802c0c03d1401c5540001d00214125840076000183c00c68070f00207143d00b2243d0f000000b181201c80080c02007010071019010001684100c41345000060211480c10303000c0b5000f9408261145468200080c0031640c8062814680d50241d0016100313406c020200300745c0c0c00a5a01c1458004903051400f4080c4468480207044251540100704134200b100000034100a10a02100c1c000358103c01010034a5540782c01d480c0040048400c1200c600d800d44405170050301e00046c00c04180c950003030803090a40c0d0b8883c00d000081d003004100640c00035074619001403e0712584202e01c44002c154000e940e6030050260040d003074078015480a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 521455377 1250 521454127 521454139
    0xa050a080a09020a050913140d0305011703031b07020a12020f040924150e010618080c09040501020d0501030804140609061605160e040b090c0907030f021e031005 71
    0x3000103a442030316803401c0d01c4049600002c0d1f500c85210040100e100e59000803c00c6a24a04000102ca0001442c1019559556040c015aa06d6070320b1143d03e05a00c10002c5980c2d401403000c83c4460000c24502040c803102c61642030b0070180c481e0001a4030344010740c04840c2200584044000f941489000001803000581e001e101900761662180340303488441010754001c481010303050740012103030340100c7e03814648440d103070b25081d8a41400800c580c4085c4980000302d8581c006506510408440c0302c0211086000908800c2c1c00800901c020181e000b4002c44d0340c1d55080040340c031042e81500c80c003030107140030351480c980b81e50501118015031003070424400d110344414080d2800560340d607000c03248204402500c1e10b410207001c0c6481c51610b0032202c2c980801c0d4044c50808070341c01781e4143d40e95200318020540742e03c694442c828465140e590001c0d0142c0c0000800d000501d24602035044030781d022000356001031504528600307100d540081c0c912744c40b00300d620020070720040300380421900d00075140403121 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 521456627 1250 521455377 521455391
    0x15073203071407110103110708040f0503060105030607020a0b06010c050d030c1d030604020409170712081305061f08011409100c2001060f09090b0a050705040e1b0a050a080a 76
    0x264180b45103107007513a6810036840b980030340e280d00c88220540c1d2501b64000001610740d5201c40c3c2c0030640c4400703402010b01034841e08000241d10b1a000509030300449094000c2c103810480c6498482185c140204003d042c0681c00401c200015000c100c031701204d0000c1d66000414a24cc107000400c0d010a16240030000180d4003d12995554045140b07a0060350403030340000e10b103c4a141c400103103540800760502c2400007041340028006040d07100d40814445944418403652002d610039100f420040001c0c0a6074810000900c2c803800307000c032500300212018485080300e0303a03c17010b260079904040015158220038009104500c807003003124403526582c0b0103080c481504944001040c0d80c0003103401c0180f4a0a200d071000031000c0a52107000581744994040402644540742c0c40007070311410f9411a5020b000d01d0009070502c01602c00c1600910351036884629251401c1e520300d45005014005106400c80c840325071500d010707940020040000641c0707030035458920940c0007400241c0d0041c030091805040c181303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 521457877 1250 521456627 521456633
    0x50f010b0a080a18030f090b120105060307030f050109090c080303070f120204151d090705030c07031b0f1704080a02010309080c060f0a0c0215073203071407 69
    0x3a0703000c0384500d02d0700c11459900d08003110050704422003881413188209600d8000d050340400c84045012142e210708030b0b45961500742101c039100e000044620140c07004018421450048015134001c81c041c1750110320400c034107881c0c40c00c8650a91003524515076401c40030301084487c450503001040800c1c0610709501d0642c5015080419446003a000c100303e8401e00040006c103581502c004d81207050305101d802059440c06001c100198104d40700103868540a040d0710315109040d603204064035619941162514040c49001c0d4000a4049090043d4500d10206042550074154280f074050821480f40c42001d04040b03104010003071100b0510b071800c10051000d450001004408640c3c2860300085c0440941805812030040c4041d0940314003443c8180168803003015030b4180211301d129020803494081c030500341d130b5448400c2c514402d40008000013825090050204800305614401c400441602c2ca200c05040d40d15801810b118130f0401000380407515911019260000c01d1904000303140100d581c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 521459127 1250 521457877 521457899
    0x609021317100506030304080f060a051f0605091c050114060109030c03150905010c0207030c0b04030507090e0a0506041a010504060b1b0106231002010203240d0b0a0e01050f01 77
    0x40c142c0002d45680c04949940c5040048500900d25817041d107400d03001e4050420703192201074900c1c01c170107420200030600007010803400180702202c0380035442c030380c44c0f60800664040c0c100f110a29448980b030415814485050500e00d11811b01c21800090154007080484112a4010b40140c2c1000507116061001a400da482442640c2e0010b0740c0c1461283c4407420800074042500c4010305550a040c0c94140964000402e001560f1080180201142d11001348092600481c070002d00168040b200411808545501003000c009001c4107460b074009007030701e81500d4102d040e9012075014490072051400e2180c010303869805840101e900340320740351911030503003914007542d142d81642503202085000c640c002580000010644250044504a040c5070450071000c100d4207140c2c0552080320944026a2061088900c5020026030a514002c4203103000548400c680c603181d074001202046100210702c15101d0503100e40442c440200d903402c8a4600117080d030f03a01400c0f19074503420a50050094030202 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 521460377 1250 521459127 521459143
    0xd050708012108090406060e090109150b07050f07060c0b0609040c030b090f060108240c03070507080f070c05030c0f010806190e0f0403020d0f120b130609021317 71
    0x50503025100010505103003280c0e200300d138842ca42c402e1a1aa00244179508800b80c2c40c40020120392801c0b16a907907138140016103010903011070030440030580c24070808250030060680355024504032407900c01007245103032038013070181c0090300410426010300007005620024154000800c0c2c075042c845040558407210350400a020007404c0d801d40c1000144042810030000d503151034818215002969140f41c3c1c0ca45035103100041204080884100701120356500701c4c1640240240b41c0c45a1469a401c80111080d400198003101c050b101089502109080c8001800e030f602c0c022460064650329020816140a141c110514003c80c0301044060300c0d6a00042000d5201c40107581e00303160050030061580c00c60495400041c6110000000d114500c900368520764410b52003a0229460b0b26071112003a950841500b066500051101d48041071f032104a0304804121400548a0708106400501c039a081d201d44e41c22401005034080f451200b203004000d1031400a11001c0a20560720744c584407d252100741c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 521461627 1250 521460377 521460419
    0x60801060f030209031f0e03030402031b03070305030a0f0f020a050705011803021f11060c0301120606050607050a15022809050303070c0509013309090e030d05070801 73
    0x80c1812154058002e4040b40c04d50300d00281030764894000d82000764a4840400e12541041d40b03005900d8925100000449008603001801050110840851442c401503130743e68280e05809003c40010024008001505001000b034880b510740d4074906c28000c00302610040c4400856016034425004142c0104941c0d09a80c0e080c80d14400d82e030100401c1c8084403240f0340c0002d411440a90709140b103054054000c1c1039030310040c0e59048241d400074410666643c01903d07902d00941003003004000da80b02000e054007050b44524008900256140009411900a0b000c16140c98024925220801480342c08419002608510460401260001000c142c8180245880307071098000454005a4000e214007401008020b00b00c3e40c0c2d41e0040d28000300404e07075521480d4010f584060011800580011081c8150310412500751303580000e0b100000380e0040340c41050b20034400c0301032b001304030814a030084450481541000303545d04c65003e0000400c582000300448204030030740c00144145451030b001ca4240d0700d8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 521462877 1250 521461627 521461637
    0xc0f04091a090102090a090b090c03010806180106030b071205070503090c0f03010e0a030c0b0105060a080c0711061605100b060901050a020c090f090c101b0c030f0602031f06080106 79
    0x3a405040b10300900c40d117101c4070383c044400d000000302e0b2000e54012600f440d20a403032040380c035100c441141c144c030b0000b03015007081600060700207000c8260301082c03040803003400000880c506031b81c0e40741c0650072513040c1d440c4070016204644501c481c00050050942000b15443d10600d0b619003011425126150000c030603101d0b500b41c001c52080c0b583c094200b203501c01400b07030503100ca920740c9180180c000514802c040300d001c1d0740c0d44000680c600d8a070088d18500306464550411641d140300300280c0d81d42c012003084480c0403062505858a84500003d040401c000785800790b43c0380100c0c2071680c0340c6404510004a0107041c110725610310389910054803d40300080c00c0441d1a94102c1100b44e06254559801303a800a010310b08011045142903e4103020b050108207950010500900740410881c80710b00000202e54080070340707070006420303003101c40b0580e0043d550f464000b0b440366650710802c00240c5054512980202c1440b4441204c40c500b58008026400caa400a510340400034140005c140b282c02c050003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 521464127 1250 521462877 521462881
    0x6050903010e030a0c17070b010905090316080a09050d0206040303140c010f061403010203101505090d080306040e1507080604060504090f060f0627090c080c0f04091a 73
    0xa00d09411041c0a62607200940e511602e00ca03900400782418400107407440c281c9100c504440000340d404a0701015040340c444c5140b03030300b090303501c1d130182070302130301144030741c8000c21001200ca8000904101603502c1240020743d100040d4400411241450b00820303c510000d4400c030340181d80d4101120101c0b541824a000c4400d80005030300064040c2c21071401142d4206081c0255985a5601c5401034035250400b0f0140c4005200900d4200e005c201d40031084c0d181d40744c1062040140c246000c0e80340c2444c2d850f003e403404080c40d0200d02d403022031000c1180e0600005c418011036291900a42c06c0004410000b8680641700f4401d5100b00c4c800505090148011180803684646840e040705002c0e00b030141050051401074544071540462810054031000d07c0d00003400b80900650041c44200d070701d8428504030400f802101c240b140060510804245907885003c0710024144401841c014200c50000c0c04948a204c0140031a20034020035440c0300b20b103800701a20000f1041400341440807803440f4111003d0b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 521465377 1250 521464127 521464129
    0x513050a062310030b010c02040e0708070f03050d110607030b04060314031803030c0a0b0a060509040c0305150f0f060a030506190b15040506280302040603180c060509 73
    0x5100c140c00404040814503141034024500200382c1d400e5002c180d603c1030444002e9102142111000f092050010303250401c0d0030701514003a0042c4d03c1c14040c07030b4240e807100760740c50841c02d24000c001d501510600f55a100d0030002d0240034041240c0d07081045c10082c0c021402402c136281c0300c1100030043c42c241a520b4032003e400340c0303c1c4e84c0700c10091540010811414140040501c0e585e400080784240408400c407030203941e5040205c1a1841e82041c03034003d00308030b026039481c0340100c1002494500a071390b070380d02e0008460791216a9240554002d000c415001815410828246119041c0010380100140d0a0082c0d40b500200d03103a521490740460044280c6980001410388007081d4409041031041005001d80d00070044030b4800d42158503142000759421403000d1000c00c1c0080e82d2a000001000c0c4000c200343e041030801040c503401c201c2d00e080b1000050505100d8500440c02d900d9000a44c003080900019425105d9045180c039070f00c03194040080203684a100903001400340500b0040d0100c3c1e0b40e40300f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 521466627 1250 521465377 521465381
    0x9020702010921080409090b10051f02010e0601030c1508011d090c090901150f150e0a08070806040c050121180204020d091109010b04060f0504030b07020a021203040513050a 76
    0x1299404030a082d505d5035a076000f04050071100000350307400d0072000e02090551020107a082c1c1110405040c1c03803c3c00e17043c200c0c0c0d6214009019084030555480300031030050b002091107294040d61040e000e582c4d1507400c25502e881d42e01d03081d810071018040343c0001400100300d141c0c82c1c0400410a00c10000c0aa920303142c000b420800328079045500055608148a132590381034000d80700700014000c1d0411300075595041480442510b115401d1500c031181c0d1300c0c0800d1071140b50103050918001c2c00d408081c9940b50005854003203543d20040a5400441c01d00c0208500006840000d201c2460180642d500c02011944100d100e10f4500700c5451381c498005103a4100c00f02d00c60031294000b041151a000045010b6002d840003000032248601c18000240c0305140040c41c0d11f040e01e006e0b8441a040c0ba08255081c0c80c601806030707204042c01400d00c00080040c142841d80d91041c020750340542000d664a10500941c25081048001c0903041031205006a46030000203a0303182980110200e1a03460b01164500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 521467877 1250 521466627 521466689
    0x80406020702130f05040219060c020f150a030912050711010815040603050304080f160e04050c130c140a020c0405150301090f1b0f0513110406020f07090207020109 72
    0x1800300c1c2400d5050000013081c0d8401c1d44070318020f80e1803001840300e003414403801c111036005407070105049141c540003605000c070000070701c580081c2119401103010600040e01da0428181c40c400203454401c11303401c004002c1d607041107450050400501300700d540c5d503c01440741c0f000f0004504200c64180020702d418800c0308656901500608204000d680340e00b070940d02d990240c0103601d03940c07040741c07c0b9142030500040c05030b0480c074400c00001c44039814a16410202c20010b80255640e20440d501401c142e81c400503a503091214220001440301c1e401c1e00b0152200301c0400700c610324400107100c40c07481c440c0c021409103101002120300044695a030b8403559035521545c0703402030f055860a00342104020032042500c100758042d08d82c00202e03403640d201c850b11544003405241d1826214200030416810000c0c80711006048070340b03002c60706904152811202e81c2040d480319005134070407180b03200e610704140070718405003d500384150315281003a0000b034203c030304600c80c0c45607040d0070303418123400c040d40003905d01c03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 521469127 1250 521467877 521467909
    0x30c2615041b0305010e060105030610030207080d0507110f030409020a020a140a0b0a020f04050906060d1407090b0f0f1b01020d060e06040209030604120c0507030b040308070f080406020702 83
    0x100c25040807401000c2900b80c10b607100401d140c01c00205503405c101d541d8900c1908140c1d9024a5540c0c0c0c0c40a00c00742001e4103041809040c0c003070040400052004024180d092040c00c1c0004191800301001041d09200100c0308007241c0011010f00e03200355000c802c41c3c0c1542c581ca1400351352820b070080c0803803515001d07220240ca91400c01342c0100251101083d11125103015049207509074407261949030482c411102006110340003000100054204852000c0d07004800400142c20b144010511005540c01c00c1100310640303c0e2541081038241d04040c205015002542c006400c000c1954100d8034076104070381c0f01950400010901000e0301c07910664807920081030200030b43d1101d4a0142d6000504050300461069500100024855050078401d681c8540c0b0014020680798895848403440d035406036840d2010401c441d140c590200f00200b11041c029031007020080d41d030b441c1505000b002010080e0030a41009504003d0890050b40440302036001900040010b0b61449a84006104840a96034403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 521470377 1250 521469127 521469131
    0xb071b0b13030f050415030f181b090b031009020a0302120715030b0607060504020103020d0c0909150f171f0218010203040b070605130501020c0d030c261504 69
    0x50540c081e0540000540c0c07003911144001c0e1250002500c0034011030040704249085c01074800e01d054402d0b08085003020079481e000610980340c80036084801607501081c0c60722510b0908035040000000c501c28010310883c40d080000110100009450748100e001e0420f82c0c548562101c0203650351010624019a80109019084140d0800b01521004075110f556000c000d85450003071804d00034040d164488030010015890030020f95640380c02000e014200360b04140e400d010f664a080300c288034520000440303440d9002da040c540000c44080e1607001c0942c801c0540040010002d60903000c000d1010781c3d2659801400607280f070b2603010b20b40001c20b1135950411140c8074100d00c84040550090802e1030b102c40c1c2c0d01403070084020041e642d0b0f12840c0f0035040c401e901004401e01041c7d1644c0074a4001c0010b4840150808641e02d61900761303040901c000354079801103e12042c419170184542050551b103818280c0c48918407038440d2004100740300e441c40c5540400800281a00300410603103811031001041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 521471627 1250 521470377 521470381
    0x708010612060902150c1c020303040f030f0c170913150501080403050d0f0c02060907030c0b0c011b050307090f0303050906252105040f1214010903030b040f090b071b0b 74
    0x951b560f40c0f9001410355281e102000700542c446813010080302c0c0b02d070742c10207103403c0020466a021140c1d100510404410401d80424003400103080d04a82c0e0000d49140d6282900d850f2544100014540442c0c032482c54145040d9018902c0d814110070300044480901f010a1140e485041c291610702c0390f50218513003c2c1ca84030300800711141c40d6101004400381d6a00f02c40d078030754488c840300e56100d90901000e814900b0b88070b002c000c08003484d0014080181c0050000c542d9035201c1900050300c01318400d1190201e40c000c000c101030254083c0201000701031540c81484410300d10b403409401846980c0b8030f10b004036400100c0c940305141844107600304c801343c0c1c0441c1190301001d00f0070241f400b0040107411301038225031302d91584484c401c000b61810b80740d00ba030890a05138500f10321804075040343e0b2000c41d841100e6503402e103082e00080c801c40100a005e91000308918018008200484804031012400540340105450224000301522a4000d001d41801c034070700c4e0b071001c00c0c407205550784200041c10b0401d0303041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 521472877 1250 521471627 521471647
    0x503150904150c05040e040609060e010515040c09080105090f1c080a09061d0c040b04021e0c070f06030609110c0a022b03053403051804050103030c0203070801061206090215 76
    0x220611016002b920100848003090825501780ea90550f1001e2000300d00707c2000c1894900350f44804002c00a81c1000030300156681400e50a403001101d00e1805504000d4a034102d20f1010700c040d95814005000079100c082022201030700300200a0064074450390350708091010490240c0c80309040e00603240f140003d4444041c4650b07031391108045014026400d00220a40c54140b50098a071444400410a001c0360005c906d034902e00e400000c1008054882c008000540401c450074010240c06566804105142403a408030240c80a8052944e1001c80800c8400e07c0507a01040c079003111641164411050340009200014100c82e032880300b001c40c0b0118524004240d0002c00428074072a113642c000c60007980c1e0140f003280c0380d90441e8a01414102c0342000400003131181004000324170380c903100c00b0548403c0001090032280d00b6081200803940b902030110035403a04014190041003600d00074082c25040010082d04032000310001048076490305521821580c840c4900002130f10075540f0162aa05a00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 521474127 1250 521472877 521472881
    0x608012102130507231209030d14070206010518160c1707030e310905011401030501050f15010509011715100207060e010503150901060503150904150c05040e0406 71
    0x2d51401d000c290000b011030b020390517100500c50000381075140d0f141007880c2042d0b4560000380003003040c2c0090000308409400c2c060544640300000401d5602c3c0051450000b6000c1d18101041c0c000500c1144000d10810300d80d12441003080d8410003507815914000342c002d43c00c0d901844004402040c44120501090007248060301420b269406a61180051141324040c0300300c0290b60030301d000d0004503000d00c2042101d0b6411444d000e4441c10359001540307100a8507560708444094a0201d410721f5100010410302109018481d00040043c448122604019008a01c402004c5a809040c01400f2880c8011680907484603480c4a400030107900c81031601d21031425040038600e80c00c4d07104020308107590300000e100140d03003019a03207079032600801807000000640740d2f03400003851981d081c1c0c036a1a44401580b04c0300c020030700078030b00350311034503140e0802e606541c1d0700e507034141358003409034008808110206060500700155103404070b10002d1021000b682c100d8070f5101c4d5400440b5810701030424007040124039 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 521475377 1250 521474127 521474131
    0x1a190305060d0f02130519111e0a0917060403030e153909030d0c080a03051b1b0c0f0a0315020c0d18090b180712090305030f070906080121021305 64
    0x22080100401030400c0000500400110000e444102710000030303004014002406c051200e820021166a9034140c0c4004d81c2d20215810b0701f43d50008000d0104164060244003078600120015005690209082c0380c002d500042804550101d000060040420303c00758407005000d500b0610b09550000850020059100142d12400386c0304d8000346010f181e100d2807041d00c0d03060f4407405161601e90400702c202c02800001c3e180401c01c1040360f1611064012002c0100306402020b01070190b001c225078081030a00d465800c0040c00b0381ea104e14000107070303950721a044040d0307944a00800104480c4a895000074020340001c0c040300c4c46880e4410341d0064000210031800101c4c050140b02546d162800d103001d68540d4020f06130858092a180c49078080c112030038035172020043ca8140e44200d030601900064544043c070545c04070758000107000c48084002411940403810341454040c051030800001e0165505205444054080b20310741190540d280101301d51403a001003041c40c2140007000040001d28007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 521476627 1250 521475377 521475421
    0x30a0c03110321010b040602031206011205090c010e0f030712080c010e030c060109270f062405030a080a050a0903020303120a1419151a190305060d0f021305 69
    0x420000040d241800720106c0301a00d840e5800303141042441c4114507212200038000d503061100340c566034848420a0301c20b0500c01d4501200600e1508a41000544040100e034402f5014120664888942d9203000410a00b103801c00c000400c0003a24134181140030340151001c140055080c007102071711804001025180c400d110f6800c0e0350459a0381d603003a06c1150120700b02d180021901c50038040c044c150780703411010300034010602140d4680c00381ea1010222903041a4188040101054010385d4a040c144103402400d0150000c04800341c4a46818500d2b005640c1c034001046000121010494810b00e9544e0045502a013100d8441540c130002024901c022100c882610b4581212242c40d40f805a088500950b9609020801224940b02142c045c0c03107440c0c1d14481140544900090010403488180180001001410749541100144204050150074070208060510040c09256a250f0a00d00e00030340c3d000010b07100904151012a050700c10401a01d50780d10b01c0c060400080c090505004050281 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 521477877 1250 521476627 521476687
    0x1e270703120e01110f1c1e0804020117091f06030c030f0203031204080322030e060a03020c03040305010e15011802031005060a030603060506011110020d060803070516060e03030a0c031103 82
    0x4208400c4908800104032824900700040012007048c3c044d800a5030403030300616100c40032403112100c00701801030958821196034803550002142414202d0350211400b65090240714031441c6071a08020781802e40000340401c042101084110750301001110070400230440408520300e880c1c14190a00d410489106110080e50400143c50388507044948145581c562201c5083c005d40703c061120540210610b601459400c000610844901b00007600040d481600003003103051049506d54141483c07003039184410036105006000180681509241d01d1404140060f10f9507030704001419a084241c4c802500034000044032000301e03a15410820660303003d410180102e440c0c90004441c02694130b04040426000341030315888c4080c0a80040400902124011810720780b41c0c0f500d6815a400140e0840b0a90321455114400400c0700205000400399070900540c0d104900010a40701e2094000141c100159a04003404042c02072088074401c10300c07601101d894600507419017100205804001c40341d0380d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 521479127 1250 521477877 521477923
    0x9040b0a06091e1508010908090a0803031b09030133060519110c060f0c100b0a090504060f020408160803070f03081e270703120e01110f 60
    0x80d4203401400c2030601c1e007500502c0002c040785100c9001304035080701860491128a40040d0740f400034000c440009020305000c07990b4098500410035110140c0d88110300e40d4100f8000c0103008502c0c02040b54200c070b08464240e40d40c500c42000240100304e80e81001c8204030501c0780d103c1150214400c07488106080c00600c50701c0544805060711035000e44180380b03030007004541014503a01e200700e400000a0005400316040d517400c01c2c00180b5241c000303a84400c003407000840e0265502004004142000e030b4845800c01081c25840d01091105100d070060102242e1110b02007030812146a1000001c407551500854079191669a90341e04e40441c07600c1215001004103000c00e103000d01204586110764002c26101d000000f6941c151011180104000c00c500700100588090b400050016885201840521440900f2507044426004485142900a64003805040c80010300d1180c582c00c0420f428100680d81410303031001211401c4c5041c5000c4c0c4140100c0c514021211300000714402000c0d40012115990 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 521480377 1250 521479127 521479139
    0xc050408011a060301170c032407090302010215280605010306050105040b0301090504050f060403170f0403020a0809120f010f0b0913060c0c0803090d08070201020f091e09040b0a06 79
    0x20740b81101101e0740a642007004210f1040044045039858040d0306c1034844040400d000079081c03e401e0f500c2c00d03040e283d000601c0d1122410210510f98414540e05184440d82c1c02c640000b951100501034100c0001c8540d00851518501c8040182c58040b4404401e664188040c07899005000d0900c02c0c0c43c0441d040c0b030004101d070742c055000d44081c1c0704200034507801e6030303c0c008280000e000b0161040e00c03540560207000d07881c49001c3c0070340c0e449103000c3d40b50a0220b440b1040c0850700c0f03a000620350032112080c0d605010000c1e5001c1640e166941d045030030207031508140c80004d07905100304011070715035104031036a0004034041908401d841e0000c54038100040c2d0b00c00c409000c08842c00f2603032113090f509002011400075606900414802e0780c01e03e00080400e0107980c0d044e03601c0c2d00c01e42d20b13801c4a40c0302420408995034060f84040e0300200902c025410411400c03c0711455000e000010ba20883d46c4100c00e4420051515000f8040b0034000d104500c14281410b080400c10000d07544807020b181448004100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 521481627 1250 521480377 521480411
    0xa06092f090a181704050310020408120a0c03030507110f060109050702010203010302012703021c05010614030a02010813060908190314040605070e09090c03061006091203120c05040801 81
    0x8100703469420f4018100c0c00d81d142c000e841c107904005821144140408280303910100110150070300f00300c00c01a0b440381081d8400b8a0119020f80c880c008000070802d031000103601c450400d0205525003008140342c2c540d21002d8481a040610b680c030036210719078102c01c40321400142e4504131080284100590780711001c04909038030003400080d01103403c40d00380318860000580c03111110340142015810440d241d5000070100503643c0001ca03421014201101c0030305c8403e1050800400390400b845c003080c000b40004c00d40304c42081070040d0500070810001624514807407410451203a00480801581d0064030b405030340e5030410200109112141d60343d0801d1b00c0c0c0203100d141000d0b4442c00300a01319a80f02c0d80d401001d46402400c0030200800d07801400700c15100c081c0442d00500400001d4280003c541e0181450b10000801040102900c6d031020048142c01c000800155500103243c3c030b1410032941400c0e600c1c0002d5000150381c5500d821041042c0760f5020000c1c20543d40604001d0108040600c5200f81e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 521482877 1250 521481627 521481641
    0x9030a030e070605070209071b0317070c1104020c031e0a170123041506030f14040f0b07020f06040f0c0b13050f010e18060f090106020a06092f090a 65
    0x4039400f0080b00d005458402c80b01d5600008614015a1848031680c000c0d04c1054040c27000c0300402c2264031015400303855407624961040191800d40202c2c20192900e5519400d880d00c51401641d0015420a0428007441215030483c24080808070380400c94101c45140c0d80502a41c000107007a50820101801c0c414a0403130407540103e0310405407802c02420402440800100da0f54031a9682c60582100404088814000e01079030303e0000314182000d5032003082d141815442c1030300904010802c80028508800b0155198200c000c654883d42c0740314080e440d03e01c01d03110032000d1b88115000c0104003c480760361b0440062142000d5401c00b03980340e228009901904500206d020184001405141040301450550110501d00307401107249000202e441e901c0300c1694030402692500400c9024200b151f04002150b0003501e1440407980340083c002d4032071000500060925850745500c20030f00111142c0d488580c5031008039032110a4868021091550f5840202e0380114444c0000412072001440340351 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 521484127 1250 521482877 521482889
    0x50304050604111c0b010f090903020304120203070512060603150c030604201b0d022e020409060806040308090705010e010c050a050f0601170a02010f0c0f050609030a030e07 76
    0x1061a44459a030350b100720750f0301e080c1c054100804000c0015100340c074005550201c0c1c024024000f45504000b001040704420740c010105d001e08140c04400042e90000c1180d04480e11a0303004d83c80c2626038800242007152603442642d10004001703018140190100d1600c0c0100022401c44004030f0807004024a01441103841d403002481c140005002070400341c000f5040e04a01404a80d11114071082c4640350350080c0c9950003e2200ca09001070007080d0800801050900c03c2c0000d007050f60092082c079951059200032150100e8800074121580030558050300c002d0465070f2428040240c56100300c6a942c4811281a000141203401041d80d0302400305014081e0790041e91610b166200210054500381510301049451f0712490220300041070040c4004004081c1c100003400e00d41d4941140c1d00086c610f020301c0800c0507041513895500517130704840c000052040c6402d0865205010781007001710103040aa0140140c0600410080c815034080010590116a52400c001c050400441d0700c1d44d41800740a08 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 521485377 1250 521484127 521484133
    0x150c0c11040b0d05010213031131020c010f0906140f070311090907030507020d1706120c1002060613060509061c0f1a09060709031202010b040911040b0105030405 71
    0x80e50420350400309001001800c1c0030303006146699003508980c03206c9034100c410800721b442802004110600c00e0f500c0c04080399003e0703c0f11501000c203880f2651540100100042440031613420144940540f10340c820340c00003c03c0581110b00c3c04801038400e40c0b1088413a1450820161201400e1412586c052541c0b00a20040c640da555415001002054110060b24005200000303650b510382d02014800d2015039070108003070419840c040d1800c0086080c100034401181c11501c4005010041e807580141d0481d51540452641e91034581040408807220f60000385a0403a000f01c0b54000511a000c4c0c4011b40300c805004100e01c1c0000c0444202c1d00603503a01c40c040202150383c81c030385040c090303844003802c1c45c2810042c42203035128011003c5010040341d03900702418950850044000c4500d901080d848003428952415100050860300540402080d031200306c51101e0340b0b54400d6212103410075000c0c100700300c90b03142401c164402c00b2180f90b403030707200d181003080505035944128241c1c0e02441e440002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 521486627 1250 521485377 521485403
    0x2031303080d020d0f0903030c1106040308130501050a0522050a260a170a0204080d0c03030204080d031a0f1806060d09081909060c03080a0e030403150c0c 68
    0x5809a02e82c0304100205042d80c0900507011103044500c54200b556030004000101b846d0607181c0682a00c1400c25a40240140b6840e0100f151002003030b80c5501680c9490210901d69404000f0041c41d0344405003d4803540c64401009580059a800680a0000010549486281618444588280c4a100a160341c00100c80704000881007044e8003a480a9040714100011103e03410506641140d000d40c00011358203c00241900c40341c044d0340360031107841c5400b9443c00d8200070145a031401e0303240e208000c01c200e511a041c1458840d03815140030700325042c1603410340c0703040600043c050f003010550681e02e080b111060b44814544000680c60303029000d40918208034401c41b503107900ca0b000415035070f0400f0081000540390b00c458440c200d02c541c40b600032252640b1380540440900709a4142d004184865643d081c402c107900000740750460307a4140b6100340c140d81e95008040140404a0b010b601610000c100031082150b1030402d20b11900b001d403010418500c804600703c41368903021302c000e4030b500e1071462 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 521487877 1250 521486627 521486633
    0x6050f2e0b0309030403080705030d200720030d030c0908030a0801060f03090807030f12090b0105060f0409090c17070521010b0307030b09070905010506030c0a0207081203040c0602031303 82
    0xe03681c4040050144c904180d030700c5d11080f21580c44454100c615400c00180411400d20500c10b51082001c2d90902e02241c040e00400400307244145a0003600328a52401b42454440010720340ca030500c603014080c1d4003503214031580540601101e002840108140846c0810105400410703289529880c0c1c0d100006070b444c00d0810390303140340702000120070180c45251440c08a81400c0041c1030152003540c3d03c241c2d90064807402440742c410040403c0d24241000c0d00c9001180d00d2444542c15100100e0729541d490b06080880c95081c400c651005944909000004061000110782c40c411285c0f01340c1d041d4021018078200ea61140458001c440e031180816140c80350101040c00201c40035a100f4000082c1d001072031740002c0c41c182e0b440d0701c125400c4559104104003110705001900c000c0580000c2403000d5414040010b1990100400649a03043d01140106a8600c01c000e13010027480e1040c166a44018142c05824141e4011a802d803400940ca105c00035410348000110b41e2800c2c41040c074000c031141169 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 521489127 1250 521487877 521487899
    0x61407150e011118010e1f080a06050f0a0905060f0312030603011113030f030c15090c29030402030a0c061d010e060912031c1b02152206050f2e 63
    0x40102600940903540000c42e9550b87c241d00e004460560700c9811311441c3c0090302c2c905480141c1c0059024004161048019480310609401540c100d6540403405660f0903001c50810702d046410a641840b80ca90f039411080341c2c500c002c50046100303a000f4803001d101c1124a178087d01c20307510f44828103404020b00f00086010290744030003a82c481d10384051100c8581c1c4641d6142408050b62a40c4242c0c0d81210302d04005074040c01318020146980c905403410006508500303000c0d030880510f840e10342e000000804640c0c003404075050440e8000ba80030b2419464150081900d602001c0324410303211001660780e000e60140e15a0044124000c26103442c0862034022301049007818542003a40f480f05100e02e41003228407004914402c0440e04002420040f00318202d031120750359902c100155080a0020300c030b02d01d450440140d03c451b850540149a0306141c85803850031520000142105241c0070900035078003a4050454002d02805010089181212500100b042c3c0c0a00070780c5244d400c5c0e1502004103040360 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 521490377 1250 521489127 521489147
    0x3040b070f0c060f140105010f02030915120903070c05041107030c050a05120901080f010e220c0b04170105160c06060e010e1b090a061407150e01111801 67
    0x41d2608401003030495848505542201e413500106545854140881c41040700040340180300034a41903540704507081c8042d4aa00c2002c3c2924042c0c14041d00540071130f10200e046910f441320b5145506600d00d8840300203516a004503000722011207a181c800100f40c42c05020f008a00581001601d10b4410709a40540c1c26469400084030b180c0176074414100480c0b0140002c1074210403408829030f40d07110700000140003020051001c4000c0900303000511a0f041d02040707042c0d00441096200c04c00c1e01554002c0500241c01c1c8a0041c013448080b1008101c651803040600101c07610102c1d0720060340200b01c04107003a02c004540c0201c03c400b809241181701c41c89401100469400f0300c1c0006841921582c0070308191800340c103d54155500f4100380203080c04a1060901160f92982c2d0041c14442c00c040019400c258a100d100104400b150300c42d0601d10105040354000c99002004140458040700480082c144201031040103501c1d2145044411414004540c1035144803008584101d8441005645040384 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 521491627 1250 521490377 521490407
    0x50301180e0d0504050f180106050906041806031205032e180c020d020a050c130e0d020a02090105040216151b050c160e180c22050a0203040b07 63
    0x5801d89030110550902014144810590394650380d5030070141845102103200094a004051400050b030300c0016600610341591158940503641c0c0aa120001e4560b0103160004418100041d01011030b40c24658000c104881c46100b04040c0c0202124041d14180401c83e1500000c03402103210b100d80c58024414029a15501d419901d070f11a100c80721088940050043c4003078440d5240103003080240c04000180d2140c9032031009000c481100d5071001e850b0714821903414019412480300f00c020444a070001001c001c0d59100301c805103250210000d55a03078042d070080e40500c00c4000040740c0d506090084441450298011300c0c440c140d10b41d5543d841c14150320304403264503070b100b000402c10400c0302e14032104050b0994580380c0307643c40070a072207040c074a00742d020100c10740c591201000341c4100558429030000704000012441540404c0a50800c07003251201680411107000b10159208080c1080c1811000c00c1810030a66581130400350480c4400c0d43d028201610080004440920441d140d14039800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 521492877 1250 521491627 521491631
    0x405190501061d04022e030515041b03050f062b060203240d0f060209220c020705120a08070c03240c0206040825020a0608061f05030118 60
    0x141e500b0f0001c0c242003200c0071280305150340e88180010351405502d98801480038503140700ca81210040305203038896450816509150721030300020200707010080c12000076940a0030522600c100d251001c101070100c10b5964000c40d1410000ca10b043c54410881d91040d1800b8040134101010420038080000900300c0342c1921904001e00c1d5000101107002641c021080c0c0050302c075100703104040d0801030580343c00c8024040c2c0300c804a180042165203c903420700301e4015000681e903d03024408100140c1d0320601c0204100c0f85007091220010540d032207800350060a600342c605d01521201000162503030305155448542c841451007011a8605006202192081820515165495590816484401c64104800d41ba0302403040000a168000c0408400c041d1001d008140b07015540d07003042c0d000d084110304c2440890301c4d007445580d5280b030f02c08403285d4004100c9440240d52380002004076001301e46050145c504515801c0040150b0041c0980401182e29801d08680c00c00300b004a03108144140300c2c02c000c2d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 521494127 1250 521492877 521492879
    0xc080c0f0717030105120a0203060a05090a021e012309100512090a03030c030507080f0c09030102120405070b0c0d0e01031b03240e01090f0e0f060f070503040519050106 74
    0x2540c1401c10301e0400b00c0241002ea1258540340401800060702800009a50000300704000140d60100d038081d800423599900180b2602c07454007540c40d113459880025000024100c065001c51500c01451040b540d0036610f1040000d0320564188120041c44002200d2940c10310103143c0c0c1d85040038146045002c0d504e803650500036000140c13240c01c402503644080c940c11003d281d03400e240d41800703002048602805c1c10b0055040c80710008040000082c070001800d42100003003030164a07208105c0c4c2a881004000795142c1d40740204010804400b03640858813842507203400121141c0c1c1e80c0546040d500c0900c00752007026010b04050f40c90101c00ca0070f150401d40c0d20010b00e01c212421800071f04008105a400140c401012188083c4640e0806008111969143c40403c10380c21920302c0541511408d03c40030500003101d000c10b8000c0e0011244500742c1d030040158002c040070340042c8007482003020303070a91345e030a441c1d0440039a9140700950740030300f2940003075000c00303020b50220701420883c83c400c400019043d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 521495377 1250 521494127 521494133
    0x50f0d02012313030f050706030b0906100201060810060510110d0807090e040326010b0405010e0a03140321070905010e0f03010c030b15040f0302090411090a0507120c080c0f07 77
    0x842c2d00d40044500328a11500f16062000800c01f000244c4040c1c2000c001009444000558070f010092060344110212910070309002d1003900f00c5002400500d0469200070598000580904001c1c001d060042c4002c007a403200d40d81c420340782c802039986c5000207010170400311301040b0703401c0174001e00807024012090000603042c1c2c0300401e20780c07140c1c1c041d5403404004121038a41c0c05000f0104600d0b002144139890043c4031140481c008c41d4211242420120300244260020070170100960b800986111034500c1d000d0382c0d40f0000710041203007800059003080b020440c1c40b132519024900365440800038003009410701955003d0b40012503000c800501030240b1544400009003903e25186c80700c40002d44450640480781022550030700c0c03010364494001c1c20141091840c42c0351606520004c0e01c284207100200b000e000d952519040000c0700039004684d0340c581a88000041c0c00c050351420000740c00f8090980000795184140030b07201a20751b603480403645138840b481cae9840c1c00c00306114556000c100000000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 521496627 1250 521495377 521495407
    0x9010b0f03090f0a12020c010c020306011e26060a020a20011d01021b070e1519030308010609050402030402090a0c0e0a260f0309010c080c060a0501050f0d020123 71
    0x4c160b1003032600302040f0b40c40c0000203042014030442c050500040e10382d03000059802081d17180c1528503032000e1b0110008600e8010403034003450343c00942103234901302c600c118508609035060140e030134000c1100c4240d12140c2d060000c92080700c0da5000065600c41e00c20040e001301081c0c1d01c49480c61800041480e25138000c0c1800e1584003032000790b0890b0740c0040d02d2001c0a146442d4400c00700c2c082c002801c1c0c103516011034000c0d604c070020f0041c0d1310081d0000c01c11401e40e440030b00c04803030303904070079105144151a4a00602811000e011700c00c04200c6441000078145454000c5a214030750181009015072900c120b54005825030490400c2805034014181c0305988480c480000141480da44030b00900c03a81401128079580f11980701401904101c4803038000600000468115402c00c2c0f801002080041c2070181791405501c40c81811805010140301c0c0311425900b0580c184e40c0101c4041d00c0081c00138080060220003124000d011520041600415201880009100001051a1500d0910582d1074014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 521497877 1250 521496627 521496643
    0x9060403080d0501050a0801140f250210050c040b0714101104152c0102100204092c0703030e1201020f21060f210105090307030e09010b0f03090f 64
    0x20031a50f1803004110602d0f1850000c0010800c8900800007081c91204502103071400410b207942a25410020441d414004003001c000c03201d00300380c0020b008080400c000c0d00c41c240c0c2d45480b203649060102150303c17824034008980458038000728143c80c00000d55200481c001580c103102c250f9000c0c603070b000030419038280900092001003201c10342d0384038181248004800c0c40103050340d0801010a1501d007103070055009018040c40c902d021a1821400303900100d24100ca03989005400b03a0011400140c1020035403c01c000c038603584880b69249643c0145905480d40c004000e20000f40d114000801c003087c0036801c011418003029110311040003044554500b60f9000c40d1000246d4680024a1020760441641d100f44a086819460701c1078200100010048040c5040e440d229000c22002e8444000000498000b070001803c000d111038548100ea07140c4a400c009019070100c1d90250707076107507507141c6050203d068039440786001d801c00c2d0070540303004c0d80354000903c00c0c40b20340320740c0f201015141400c1012032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 521499127 1250 521497877 521497897
    0x61908011803030f02120c0c031c050402010815060a11030c01020f0310140609040e0a060f0e0d1418060d1e1a0906190f082409030f0906040308 63
    0x108040e00d64030b0020704446150328040c801c50300c1800fa211468000b00320a50300034480c604040e44581d0181c0c0982e09612444190700403a040740a4090202c80c1140c1080c1e00c20380c001d0f201c00555540780d006d03244452954200e0503910480401034031101c54000c0016190459900c42140e0400300907003d078600b264028903142405c0f40004c820045103252030390664000e400c50148070186980070300080b50350380c000c01c0c0c015407203241c42d0100b2005a000800c22580c902d500b003007052103514103c1c441071004082c0b1200c200140e008283e50b2000c1d2170700030103440c0444111112528942550203a801b0b00c00f00c0c1c1d854a243e03120ba0104095884030320103000300701401244541026032a20070a118904480d1442030780190001141403c96481c0c5d02c1d229503076882442a11035101e054400302030710724200780580044407038150460020403a49400204006234081030038126003951000050b01448840440781070f83c443d4010002c4000d00e066841c081e00b4014405000c280c1899205d42c4d466a060b000040d100f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 521500377 1250 521499127 521499161
    0xa0207120807170408070306020904090f060501050a090221070e0306010b040608011205031204082704140f04140127030221040308070206090d030203070c1a0306190801 74
    0x814040707099104008058070b20007044c5824644080c3c00d49441d031511015140c16400304a0316219100c0d034010110513507011404504c5440f282c64001c0040500b800742c9401115175803400315401c01d142c4211111107418a01c086a10034400d42202c5411000030117000801c03100c440c80c400316450801c1080c1c00b0b094030b8440540c1710f5042002c001c0121038140c0c00340d42031000700000503001c02d00c00300c1200e042d030941c0c0484019594882c00d04940d14402e52040d1241a450907150ba0808164046c0c40c1c13049070301c03c8406004405a14040710051074042d1621002c0c610740300c012a000914503005818102c1542c4000300f40c1c0031400d00250950114045007013000c0504040000400d07605101c10035412456800c1c0301c07501408044140d446002d20f010080500f940000c410f4291b40c1d90200307562108c90000c0ca00e40e520035148c50000d45039006145c1c21104410700e03840215801f0b103900c0240c2400e2803900d081d2070071a43c5003802c10181409150300e413484076003440000302d96021b081c0101040350707a8032040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 521501627 1250 521500377 521500387
    0x3090c04020a021005060306010e0c0d0603020604060207051306050307060503092d190b070309020301240e09030307020607050a0e04110a20030301141206041a1510050a02071208 78
    0x710020b0305c04c0100b81034880e401400043c03001203120001c240e0407030080510345440e4201c211001f0000c0c0310707681020758440404100091041d43c001500b0054400035120511004a140d10001c144c84240c0200e55268012003002d00030580300d64055940b2500f81c008a0319041000b100780d00000c01c03440750551210350454205280c880c420824900000b121424501003064a42c91300c140103030020340541c00301516140c41c03d0640d982508100b400c3c0952119840d401003541d48100d02000d030600c1369050510346075000039084003000c01030300d10442054010f010242e42d4244200c441e544001c0380c1c58140504004400000d4a0350712801124089244c2c640f84d0f1072000c55409803201d528070f0a0308401d140a140c08035200c0b903021082d60304640d0340c90fa100e4490400040041c3d41c103011001c209000c1e108420801060241d00f442c2b00c081d503000400c500354280c507031315090341c0008107800c07066800080120800d40154824401440c0b06103252040d15540c5444098805100c0c030501c005071081d01b03001c15 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 521502877 1250 521501627 521501653
    0x20a022a0f0d0c030b13060509061f03110f060409091101030506030a031d04021b010204060f030605062a030a02060405101506030509030d060803281403090c04020a02 73
    0x407050030107001140d40d8002440180e58030079181000e404002c09050300d50f0003242c216109003003649080c50f4003070801c0c407491500103101943c7e80c40466000c0c04000c440b0069010301c0842d503808000b602c0d008480c0000414020b030501240b19686680a60411410030001408c0c1409201c5e100d2803500c140410341041c0c40280006060341c40280c4003500c0b9400c0005481d000a41110440c9200d1407542e0200e4072090004c000980280130340c00c806100c0c89a900c0480200f03801c1075009109035181902d4015401d08521421004c85200380941904642c041000350403400141c9030500306034003c2c00c0c500c0c100303840303141d40b8030300b507070031000c111005680a0f80900c02045000c2c40901000a00c06504010f41941c00e100ea1000502c607100c4c91060513070340e4000c00c0c071042c4140111400c000b806541800b10320f5503102c0b41c5a50364083c5115015a03000003015100c2e00b1010419001949141d07035032451041d030900701401c51540054940c20a512810b9005002900c85001401c3c0c00305d4a5000303000c074414040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 521504127 1250 521502877 521502889
    0x2006070e01030b030c0f0d0803041a100b04060302091f12110f030103150e01050f0a0c08100b0d02090406030305030105150a0c120e0a091a03031c020a022a 68
    0x10300d410706150078508490001e07240083d400700f1140f01150ba400c01d05141e500821725010b400003026103030341400000c100a00880d15051440f40c02c101503410b00c01ea41e403000e0b103940c81c00c5900545a0385901003200b0001a407003500a02441440100702d2221142c1410078a10004080c1ca00200450307225030000103039500380d1080d6100540180059494036031000548000c1e031005002c0240448030407140e400003100c250b440003440300107400080020f0b0400b00e5500031801000c603103410542e4200b5498903002442076042c5401000d8451107014550b05003c40743c4480c0d0402400d104800345e091010485a68950042e03000460281e00d41070b581b541811706002c2580750700c17010600c10380420001d6146095100c4a805c0440d90821240c1c1c0041072407490403106080403684080c0d014401000c0820001c400ea4010b22008440d140d1140c042e2540105064030307030182c03034440012111200c3c085c200d0422150010140c3c40018410340f9203800c080712014244000c00c2d40c4002c50030343c404008044900340b00c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 521505377 1250 521504127 521504147
    0xf09010915120807032001050118050601020c0a052202030c070303180515041a04050c040b0a0509040b040c18090201080604060b180a0b0c0f06070512010312200607 72
    0x5640d80014061141c031001d0403072040c410003e0820403111a0f6100e01d02c111941b00c203018101a00a20107035960f181004000f05e55440808101e600d00004150f0a600019080e1400300e400b03001008103034a04810412018001c600300046880020084211308119100440c40f420900707103e281c40d00c001d403e00070101d03104407111401400031030b080e81c4d004c82d100141c41c0700742d804084107001090365035140001e4084d405440040c104200d00040c00200074010400c2c40000780c068400b00306041c1890100200d81c040c0344150341c1c200d4899800309001c1410400380550060154410240a85d41c0c0e003241d0b00c0004181141501c0d055a0307028040441d83e00c4040c294200d0011079051100a042c1030045043d44a80303045100c120b11242d04100c41d0351103c1d80d111004002c0d0010058803800a4000d42e070311500c028000300400c3c0500300000f424180a1800d0b00d40c0c44810101c10300103a801c60b6204210001c10b00c001c0c0003440140e00c01c001000d4020300c407200c02070302c228001c0c08003401c00800c090108045 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 521506627 1250 521505377 521505389
    0xb060d020c010905151b070204090212150a0203010b070f081e030403110309092d0106091a0403051c030e030a0c12030b0609040b0f041a030601060507050304030b060f09010915 77
    0x20003072044095070a4607410150b58102821aa5500c448c4000343c0100488440290014005c21120b0f101c803101080001004004d011401115942d001a0744101e20090150040400e0b05211002c0458401082d0032101e503c141c040a10b0034811001142c10201c80204019000f140007003000101540f00d0120241a0b011800960400d410380c3c0010f41c0854004100c1c42c80c042803034844071040030b149680d6000040c01d079103022096584810700100541c41c203024803000ca5030031687d600e01480c00c060464003200d030000042c18500c0310740d15202c5107012000e21580c1c02c0680700d03150500d040c1c45c10f2004180001e81600c801100f21441d00e401c801c1510b1410440b82858940380c08140355485010468440c4582281c0005095a4420005010031050400301d5082441d1550b00301e045441e161740500000c00490440d01142e81c3d5034022500c0380f06d0364070020025001804101300050420084035080a8018801c0c0364101704da00c046042c00800340c1c001502c044e1101c4003802d2042d003000354a00039040d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 521507877 1250 521506627 521506663
    0x40e030d0e100b0d0f030224090c0306011a07080d0f0f0e0c011e110f0c0301050121081602130f0506061314040204210c0f0e0601030b060d020c010905 66
    0x1480c03c0009403250b81c3c0e5507018214044000a003401c0504c2840050040d204590030540030403002806513070034250880e1401001c1c89206d49203074892900045481c120303080144a1040307014598101552600f19510031561440c042c800400940c446000c0c0c0329407907542190000b04a000001c8581c1911188040f00c80ca54002c0b200450843e6440900460341c0000c014490080301a4030f0307012a407551201506004600a02840c1c00700e0110100360847d10040c202c0090003181d0701c4807000f003400d4071f10f0980085012040346510001032030107005030000002c48445d442d001d0f41c0c03035000728240090340000c0c00801c2c0e50381c0580082c0c2100510845800c402c00f0307262103050180080340d04440d0710a5010703103213001c010045d80010583d0b85404a8001d080003d072000c8500d1368502002c506030704010004c4415200212021079460041880d050880c1d80c0415421071907164200150001e148549401303802210070045540ba000441c002803d048400000029080c489030800a0034000302c2080707060204 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 521509127 1250 521507877 521507891
    0x70806042006120a0903050c0a1a010e0601050703110a12270b070b0a0b030307080c0705040c1421010b0703090b3402130218030a02010f0509040e030d0e10 68
    0x440100000d91340301c0c2c0c01480005a0345194242641d282c02000e078640318902c503001c030341d0003000703101581101d980041520003200f69880e440c2d503100580041f00c0c82400140c2c140f080f0f03070100e8420712242c10303105622020303600c41c03c1a40c1c50340c60f40c43d903036550a407000c180d454060300c01d222180382038254a040c4080c4c1c3c4521450034503895200c1d0f4495500054802151180403c101a07155071111303819000041c21a540d072401480c140415410491a000300e1303000c0c003c2d000032541807502543c0700942250707032521580341d03072140f2009040e00020160720305c845d102c0e048694510416a020340c0648103400308103032a1080b03407800500700501a045624100428482c2240503c910304510f1640250909041454606545200c142c00d00b42e1102940c0181c0b24004904440541d41c0185040030308c007101e016501c0c440905041d0f0340d02c20542c000b400100d85991070b4400c60301c80c0f0060030840b00010004511040200c1c0b00c0c034a50f4000002101d501c956038900d0284000082103c0000c005046506100b64 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 521510377 1250 521509127 521509147
    0x609050a06032306060d020f0303120609090a1703270709060617010510021c030207061a10030f0b04090c1415030c09130f06053d02070806042006 64
    0x9a0307001741c14a4083c158001341c44046585d03106000b500d40c04090122600d4104007600000558029550239005500a078049052480080350382d502641c0c1000c010544841d041039001c0d8207600007017088001c00301090504451a40d02c1d007640014103401c0d4005d09116060003842c50881d030b03032035001509102c0c803a40c940454004c0c020303086046610031598042d4021003503109904021040c840142c072500344104001c842a095800340150b03a0049900b08045100392180c2e0483d00c881e4004036500c82020707c281c0c0802446500024641040e0f40404070b807904000010030b0079200703040d40c22589000c06c1c03101404001d401d65003022086404454142c00898030f98410f40c450302c80608202016000043d2507100341d01c5420820307010408400c010444024515486002031009000d103034400c5041880e50b0041c14407000403101c0019044e1710720043d105032a0001003012804401e20410f60199020002d52500d003030000314443d902404511402c00706604118140d040e500000500c00c502c00d00c801c18074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 521511627 1250 521510377 521510383
    0x501140a05060c150705072303090d0c120503030f0a02030c04090b060f030408121f060e18011e150c08070309030b07110c040b0d150609050a060323 65
    0x2264000d96140e60343e15840030b241c9007407002c03440500c3ca400f8809424013401c5940030000300982e0740205400041110161200b0381c5000083c040305c0e0545d803003400864200c1c5852a0441c0d101403003082152401d07960b51080159058202000b60f42c15000801001413206a46030069803156040c0e10843c503501d0465545030503400389001c1c40490640d44c00340310b1030350340302d04003128107809030f04200319140e1900345003400c00e079441f180300565000d00c80300c042034050900480310300a01da80b0070307054101b5904080045031a2400054001d51040c100903045180b140703c110f032503002e00550740714034000d000c1d14035214540c01890740c00340b02c1107007400d10b2034000c0c5d5900074420011554000a05581c55013541011031300000c01d2740000d071040701d2490520500f10f4003e00800180c0d541001a1000380054004020441300c00c070501d2500030038406130700300024241d1800c86030240a00c0b000014101d48a03a00c1ca01101c4040315140c40b40e559946d01482445400d41a101c80c142c000c0884008404215a905403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 521512877 1250 521511627 521511629
    0x1b03070f06080405010e0313032001081f03060c05040608011a0a0e010c0501060e0604060509060303030c03070c1b14030d090e070c1a1503030f220e04050604060501140a 74
    0x7080503142c0414100002900000d07644541031007200e44802c41041c00f03250300341c854441201c80c100001310303010340484201182c9801181c16101d0400702e03544c151881c0503407400141100e04480c20ba14022000071030320700c5403070a0340003a036658948032820580003901358101a0400000c4000b84925180080f2905007180d04809081c034241c440d0080c80b50050b00c1405c60140002c240d54200b900102d04800c2e041002d81c8142030456080c0907481da00c4052011404058407895015002000002d030421042d000440d084403862800c00890046502c5202e5400b403003050b400740d00300100908011500d4580e010405000e030440161400301100f5a0180440c01580300d04a101d280000000740d00b84e0040d500c0b030142a81060010408031300f4202074180d000404c0341e140d40480400c564071104d80c18008107440d091415a0451868180f080008070300e0744a05464401c01004c074640d011403c0c103119070115000324440c0c8010181400c1a00e0401e0590b80305802a02c01c00740904541da4469989050100c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 521514127 1250 521512877 521512889
    0x118090b090c03011419080f2508120a02030913060e012c07050f0403060f060f0e010303180906120b0603031806160b010f031b060e060c1c021b03070f 66
    0xa008841907212206c5022180c1c2c0050818003a420940c559210b020031000d85d007822081c81080d681c155041043c2c405115030107412041d5004421400c407a500e01c9000f00015106801200d08054440000540841101041c25010703901c0d903104004840d100544580503082c0d03809601e40c01d400b030044042c2071104240d004d1038403042000104103190f00038800c6420402c251000030f50340b0368481c24064040c251441518120750710380a40010765402c1d04040c1000d6884603008840f0b103034695181261604444071003120000c46c4540e001544c000c851203040000c0400703207400b0b180890746080c1041d00e0b0fa030040055000781c0040011078406400c6541010000b0000c4522036141c40c2100e40c8105507990881000302040900e00002c0b80244a14003140201e9100310141c0e10b00c900324181c0406010400d120369801300310140728080702d0b454100050701840c1c00035805c4a041450010f10004400070480501025070013038260702c441c541c60403020f50030914065000f841c020b4540390711808452140e02c01c00d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 521515377 1250 521514127 521514139
    0x4080c010e0f041503080d061e0f170c190602101506120f0c0305180115090b0102030909010906050f060415031d0703030e0405070f02070302040b0118090b090c030114 73
    0x1030003413200121104059078001c0692a1681c0c41880b2010080c0302d240226090100e40b00709454a0681d060180d0065070141c0b55034404041c40c2c240d2800145030300b02e1101c00a8000c01c65416440c0d25094890003514928001811001d03241032006800c08040780c101d0340909041094110b1650344010041c805ca448a1610b12288201e20420ba4020300039041d0600f0344500306a203001c241641504403a009040b144d842600901030307503415508891125180051403004548108038508090703102c04071181043c01030744c1c1760012203c001103403001c00740c000f0302009944420030300860611401a580b03125054070500d1505087c1544200042540c0524604058842a01103080e510202e94002014a00400c6401183d200d10b80640760010020b400303030050b45064002884144141c001c110207007416005403110754115000c0c04043c1c2040040e5506015000c603004600c6c0300c003498407100904002d0703400100400e401b0208101e0070710161481d444074400f0700061007a62444a0381200d010011a04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 521516627 1250 521515377 521515391
    0x50c2b033b06030901090803090105070206061807080402010522080c010903050c0d080408030c030d050f04030c141c0804020a06030207080d09020a0909030503091507020c010513080102070804080c010e0f04 90
    0xd13003400740c0041900108100404420f0120803241500300d980100380540030317112141c0c1c0301000e02600041d02d0380c580d02c59200c0b03d07000c82c0949000740001a001801854517a02d002d42203043d07002000d0203110b040030503601000c410400341c181406034564164003460880e00040c650340350543d4074901042a0741c03041584c038204008014121048070000d00d20482982e0702d58204100694403a0403880c0c2482d109821300d000070783c5d0b007002c00d0560752040340d064803411040f0304a42c071000d240342c2c051100c9942a1081c1102d03800c42c4003403000507241629080e074941885150501c1030010724030059220106048c014401c580010791100b0668515900d60000042c02040c80d00001d829801540c5c0810111490002c010060507440b00c015482013800404071020365011a5807205404001c41d81c010050b08440c0e088002c0350312600081858041c00001c200c0c0c1a5121102142244c0c021001154240000038003040150024080d00b1042c100074200b0004150320385020bd480351601030f20580c8202c0c3d0b1001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 521517877 1250 521516627 521516641
    0xc01080c120c04091529160302120c0f0712051c020316030c020915010e0f0a0302040e0c03101e0b010c050607031d0a050c2b033b0603 59
    0x41950000d0190704010301400f41910690b21750500c543c094451402e1318040318001001a00107140c020003945006c5603d00400103144616420003890304804500400c4110500b48500802030040c050001c405003007188040c00c02e041ca4030a05a0010560300088001c010128402051811031040725031b07541e8000d41aa2242241584500c562989000c550300c000c000134507030712240f9220010700c00d9880c0c201c15140c0d2007400300c81804030740c5110300082d42844052010b04242c10103544502001c0c040c49030300f945035800241a98907429008002d0703404040c6446041c54200a150400d4a40000030045412034030303900408100c40f43e402114854546d902072096034800c5070300540e032580220550341c050820b018001d0241c5049080c0c0386007070342d204070414207141d400b1444008550740080200340a01c0603405000061b810226016583c0012801020000c078140700c010001030310a980d0340074807910412000b000448511003d60528422004480791600790070b40004050004072840d6440e82d803641 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 521519127 1250 521517877 521517901
    0x13060c050715021e0c0901050105090f040c030e0109050d03050c041a070c08060a150501050f1206040902060c01241809050c0303040305100507020606090c0c0705120a02030c01080c12 80
    0x700d40c0c1102c001401c00410120750300801d400f9445d04040340c1004091360303280b0044070315010382003c80d40e20609502c03104410740380690265454a00c035080115503011403039078081c21a47e8039041501d0941052140e0549550306214017503014860b400c5c5181098100010415510034000e1085030382100013407560140b212200280e0000c064202c100d404924100020002030012072490011810321800003180c0c641c05001696544d0500844890800d4400840c001c91109c005d0b19054129913118010400740e2100d03001015000b45c1140080f40c03079002d444200210038143d8030084c00f0320700460300901c030403001c00043c4c840e1b6001000001c00c0c0c183c924244141401c20480846130b06220001c2e0010812101054003030410b801840100141e50b102001662100c0c0d040b02d800b5400826000002c3c81c1c01d416401a00348401c0c00380842d07191039151004202c001d080750708440c41039480f0078095021850108001000c480c07007842c1c4842c0b41e0401c0c445c814620300545480d00708648142000030801e902d42 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 521520377 1250 521519127 521519143
    0x507090f020f0313050f01020a210e120a0909060f03030e0112150513020f0a1b06020f0306210d0507140a03030207140c03100209190b13060c05071502 66
    0xb10710250307902d051200044048500c0c0100495a0303000da898100340601040c8252510141181c03102450095240d00c0c0c4c5911000034002c0700300244d5103110560b207500080186018282d0402e0307200303035145150400500300c40c000c2d038080180c56080c10020300c000c4044d450300704222541403d01001d90009100182c0b0000c01049607003880d286042c030240740c0d40c0d440e2001d0800311801507421111300d07180c861080003684100c202d2424103400401c9130071040e600c1406031381c488050010f90380300300c0415070340c0f9a401d0b0f9004104800383c1042c04024440e462408950210b0700010540b00008150322080f0304139103a92030449840240040810f000c03007800007001c0f0140078940264150343c03d84131589400780094000c07040a0b00c0d1590000300351030f0b182d1000900003901c030030007c0007018078101894000300603600c989a1140c001500d0207160302420752107000750b00a018104140c5441c0d40d04a01461000e0045034007050400806004d100301080d000300700c2c2e5041e500d82103840b51704800e01c06c100b40e240a40d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 521521627 1250 521520377 521520397
    0x30f0f090904061b020a0c03030509010c06050c030105040f050907050603060406080105040b04061b090504110c1009330506030307021e03010b092e05040f06080d0305040507090f02 79
    0xd0700030801040015030200c0c41c0299842d050022042400004913511409840001d1002c446d9120502c00700e401040503265034081450300c10a42c1c00207686881c243c5009036404a4012404401401685020300460602900c110b00800003490000785136030f036800382c501c0b6041c0941800004601c030390b261504883c01900921009200c142043e24103051b045400300c0b007e03200c2d6803130a8103982150351044540228505e160383e42030f40301030420007000000d14000207000d02080c1c080104101c0100248803c8001a100301d030300281241c3c1606089017010700c907404200404280c05c00960700030b000302c900e0b82ca071003500b6500002c0507035490700842d24602c038801003c1c1d07000f9071070706001003110000c0401c500c488078190000d20417601403c0030b00441c04829111015900ca40880200140341e41d065801140340c2c0c10788030411466a12004202100d809145680c4100e4854a06001b204400c000020440003640390400040c0b520b911125122001070255400e1244c4030b00d182d4142d100c00e90180d03152104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 521522877 1250 521521627 521521639
    0x60f0c04091e061401051c090b040f02011409060f09060c06040c090b03120702040c0c0803310503271c20131503170406120e030f0f09 59
    0x3030821084038141a146042c9107840c0d091080100d050301008070211140c00040e1241c0b4101403120441c40b15200d8610500c919481d07840d081403022801c004d0581d80554010507040341081d013a40001040c1e01d200e9030580d51818810007150714a621880b0840d00c07900101d002c01c540f03620305c0c4000140b5600c900c0c0c0f0303400c48a108030000c3c030090118003511007045032011344d810044510600181512440199250400b0076401d001e080b0160410b07400010f40a0080c2c0360a8501da607103555210031640054a88040e050a182060391382c403d40f204055241440d41e9204042c0d13a08655502c2c1c0d07580c4101408000624065015081d0b80003d410000310050402442d00104107a1256506070000c907070700341621003009030b07221300b12022080800f81c1c00203c3c010307050101461b103442d0850060140d0203001c0020700b6044200002090005060315050661803072030a540b0380c50400d00800c9042c242101140e610300d032210702c0703000074400004c861240414544454541402100e00346181c02040c02c015007080c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 521524127 1250 521522877 521522891
    0x1050906150d080c0d051c1a010324090e10150b0a090f1202090f040b0103060c091205010e0601050612010306111b01051b211b04081b1002060f0c0409 66
    0xe1700440500401011120810344000014031100309231190a90642c84a10305081e241d1019442500f25100c0f0b14400c6416901e20101c1d600c510a043c03907168880c001082d901e0b080c5c00801c003001d001181d148400d03554141300f00c2c3c1090002d41c0c40e040c0103202d43c0c0c64460340094265962801480703400020801442a410342c1961041c80600719030f40410102d02c00c040c69800215400c075070352401c50007541c000d9242d203016825035660100a00300c040951080c4007807503500007240c96100c000c008445105e24001320b840d4042800f101d10304501a001184181d0382440205080c41e6400c101c941142e800000c085451490905417201521504010300a9418900d10341003181c1d0701504101d00995040d50040c0c00070444004489003401a001041000100784859103501054500080e800401803a82c40d00107020000c800c1c0d03c40d40c004d90042c1c00075001062003007a52100381c442520000026906646440c09100f002074440400074000e10691004401203030741c044100040e01c0243c8103030101001b000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 521525377 1250 521524127 521524153
    0x1060503190c060f020a03030b031204060e130c050f0904090209040807120203040b04030201030b0f12070303030606020d0e01030515030102180a09090215070311071701050906150d080c 81
    0x4400401da06541d00d003114200080c90038418258580a840c841e80500440c1c080d5540403006804107a441035410300c112246204d001e601d250090000b480540c907509006030319802400341c1e030026440e50b4100c2501c0c0030343c0b130b255039070700003089130444045101000e135540b01c4500010000c141d8a0f0300650001d990000308800c00109c80c008240c20b9000e00340d0282c1d2095005e5040740d4a21690084450950701440200015406504441440400204501c45c1d8003010404903880b801e007407040c140c540d40807d50401c14141c161041402038041803020f01345004142c9009804c01804070149410195a20005286445240c0715031100f1600103000355a9803804401d6907810300c900341c07907481c401c3c0d404003c001a5910244144804bc0358060405540000b100e8a00c5805800582c030036000c0c844809941451482d090182d030028080e000141d0702a0f2000b544407a007100d13070081400140d40c1c011401d010154801d2052a50303106011600180c40021915101d0034500490040322028400d40014101d9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 521526627 1250 521525377 521525413
    0xf0a1803030b030f0c01020712060f0207060204053d0309020301110a090608040515280203010f1409010504110c0102120906060a032001170a06031707051b0301060503 73
    0x2e4084114100d443c00041048041c0c1c680c0c0700d582c80b107400343c0d000100404c607415004940d007484600a0000090b42d0600d06084020399000341c00869400d41d0015003800340740f8080c03a0b681000c022040540031150052044c0d841d0103107594600c1119120f0f00d00227211814420f4209030322580d0b01600a02101c0e41011191456030403464030075000c90003500010403100d129425141c49290050000d01c00606446c00d00f1220f0540500b00344801c0e0019260f4183c0c442c1c4100004044441e90078005030b80703601d4070315019902d1069801420704180da2450301c0d0b4860b07803041101d5042d9a4129070024401441c0700003510030780f01c2d49480081030350020450b960f81c03180c00c44540b445884800d080d140c0c90355403e020005e2000080c0401000c14028202d40c3c900e080710803006c5061801e06041c0041403404a610b00c12040404640d020801070b01c5850a0040000006010301c040c09054a59828201c042d69100d072100203e030a040c2c1610313803000201e02203517004d40041c1d009040c00747c141d5407203e0b103101d18441 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 521527877 1250 521526627 521526641
    0x105040f0f0c0e041803170403090e0c04090b040509030d0f020405040e060f0108030c1015032013060602070605030a1404140c0a03030e011209050615011202030601080f0a180303 78
    0x101c903178a800407000012003502e000c1c141c42580755442c0703060300b1101d40040c041924084d0054042013503640c0d020481040e1260f15034080c5507001e40441c1c44074a0078800005843d25507400900403824042807201807940042560a55202071401103070541d290f1204d40000d0086a01c00e80e80035040c403070368001c48903010540d240a01c13515110420340d42c5c0c8490081b5070340d205800c45c00526600803100d0010150160b4042030004072007265807110159a610303040390780c1c0d1010003001500e99184200542c4c07440c00b141040c190442400c82809290310300000a5101e19507841610140040000091071325405940843c070b00c20000c024440c17040c10603040c00703000444017290410340d5101d5140800c2381845c262500d0821660301d40d59405041d00c00c14011140c4411080c0c08030300c001e84419181c40010414086140b140440d0700407407004c0d6210400041c10101d19200c017898070b40c410428040300340d0f48411200d1b4403014039201d0061343d444102d00840100520100160700c8400d101c99001010390580001c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 521529127 1250 521527877 521527879
    0xf150608060405060a0509070e0607440f130f0f090209060703030b011e08060f01030519090302030d090b15030c031e010e1204050108090303010e0105040f0f0c0e 71
    0xc40d036540c4810511003180c0c0155526588610752403000c000074540901050340c0500c4918002d27211500b04808a01c60341c2044100704d8001da0881c42250070390405143c0b0458031004090044d014607000408100746100c440104000c10000203080303040d10031044103e4201130490341041d81c0c1103a944030441c4c01070703441d80100300068440c1d11002551910b20b000b580c88484005100e503180450a41c1c2c160010034010115074103220781c140d10801024055002500d082d401510355941c1c0b49030010030040c070660320240703541c1418944000d104022496500315220703407901d204002540496030405929500171806074a844d0f508002d000d40400000c08059400381a484484408489030a001c254641a00c0021aa0198011220000d04501e40e50544030901d07840e01c0001041803482d0f52190400e200070300b0207440c00c08002001c100c6942c0c00300e003283c0d02084280c090750a550501000403c40c94041c46064411a110400300306d0380c00c082c5e0300c510105e08000b042008900c2241d080030305801c00d116106 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 521530377 1250 521529127 521529137
    0x5010c090e0c09010e0d02060c060a0b03161505070803100810090515150612221e050102040902030f040c06050408210d0e03030f0702010c210f1506 65
    0x103141d200d000d652070301800520b12054208064000110380c140303149810345038400e2070f4111410150301c1e040000e061001d4140302600e01450f001c0300c402d0680b403144c1e0030580241d00629040030861540d071840c40940c2c20340070340090340075860882241e0754002d800003d41248000030602800269010346801116880c00503203100c2c0000009035000c6414030503016015400c4002030328000c1005031541584442607041100880c0000b0f80400c0c207a42040c8100114a504c000502032b641c00300940d0710701c9820340d11008245241d15951001d403d07008004420302810201c1441008104d02901610054681c907803046441e8640f2542d0000b9403a401d44013503400d00410800400c3e141e11690895056504010040600c850380c64107082c0b42400924520151074018410448080340d540181243d500007103000b1900d07824041e5054691100150904096a140040310540c10f604071250902280c101d40043c405c030030300f642c1c0740009090b240f01d26003e0180303050100c8964403d4440c0c0c20040e203005550b1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 521531627 1250 521530377 521530379
    0x30403020f030406051b070b04081005010519030210260105010f020d02070b0f07210909060e0a0f15030b161701090c1806080609150d0b0603011805010c09 68
    0x40d65203e10443c01008002841004886004220912040d040c0b214034000c07034080940c4c0700001401c94100c3d820014207034101c443c03913029406030b07402864090301040b18100d05150301041c01106407002c500c4000d000e04c14100100300c18501900f02c09065414608070707221460603036011080c0569090060502080c007842181700c4980c80010b40300442c0440344c0007001002c2c102103142c1c2c6244c1000c5034200d007090003001701ca0300282c541d1540062070b1940d10b5000380e180c5c1884802600c410301581122240c07914140003000103040c050681508101145400155002050701c00c002410081c0020340e80441208800810801d40040d6184240e0400b452404145164402105da403c400c03440c040c1400c1c070850040c030258515a012011011041c101040b00350742101c1c54041e00c0d004d41d800b840109215000b000306134180a00741c1a84250341d001003201800030400000e03180c081e120b07006021640c1d00710000e402170b00c3c254030098104840d40b8010310303901c54034a0b02074040c01b80d0045460028401d080 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 521532877 1250 521531627 521531653
    0x331210060e0f1e07110c030f0601060e12100f090b13030f170c03100e1504060b09061602040b0a030818010c120822060902040b06090a231503040302 65
    0x400004848080108a2a8480401c05c844455681607028214000c042c0b607441107a5082081e40300902419000d00103942c504017016144105403c01039000340d01d4a159958a180f001c507c0d03484041c1245000144800d05960840080078405402010070010f203050210400717904500003026407090395114a8080030300d800715a851402641c0a40300c51046010034044102c40300550760140b100700030340241982e00c1e03609518804098505101c4003059022611041c101401640c0240c1118000c130361802207441c0c0841c05501c92102d10700c5401208410039400c540d41c1d42c02860701603400900c0c208a0b1600d90034600b00680c0b081103840c510301c41c101c280d070002c0d501a19000031456000700007910380d20640e845c10f8a440130b000b016082c5d000800c81c6a007581c035400c01e140d40e42c0030340282c000050482c2d1520520044130030305003026100b0142445465605d43e0703011001800d807a004442c00b07a0391302c4e02c0311a03103400707034009611281d000c0c03d02550310941d80846405540718500130b500b00c0d40a5803d0324 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 521534127 1250 521532877 521532901
    0x20405010611030a03390807050304080405010c060e030a050a0809010e0c130902100f2d050c030708040308130f1409090a0c0e331210060e0f 62
    0x74002103080c2d00180100d104c0359000381c0c41003200c501100011020060103008000c480b072071242c5c6030702501c1440403860b038107181e00086443d030011640c1441c0b40380d42407540364054640a103124641c1002600408030003000002d0304188100407a071011a9240c0003403d074061301d150030840400001404200018401e60414042c54060102c0203001c7d208010b007110902c00c1c000030803010741d0026034540d4078070300040c3c60722079641501520559402245031a0048002c0940c00c0c603035034402d100e00419201c0e5030140c0349110b80a0340030809042403a44d602800700c1e1903040d4010180090034011010600200740403024004003031034000d21100c0a407440d280d6500440d6103802e40548400520407559504040c1812229075400c444040b080ba24001d000e55103050781c10009401c0000c0c000f10180c00c2c070408510030a04880e911045120985800d0564125400102540741801c2d1082d201c00c482140d031040140a007443d600320800c024400c3d5616150f18011014003911101d50a55002d00040c104650607 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 521535377 1250 521534127 521534147
    0x111b0c100c020d020f060f030406091502030709050906010c0629010f0909090c0305010903020a050607021908071b090b09060a0506090906040219020705030706020703020117070c0f0305070204050106 87
    0x1807104911190980a0040344841e202c5c0041d08010700b04105a040600000550f100d5803044170049007850709031a000340d00306d100d80161441c0354010300501c8855600039154405076417003502c4081c1d6a543d0f91004a81e9a03219034409003e6030710b00240350b000b00301c6500c0d50601040001c2100040754a80000450742ca085103900c040c0007600c46030003440aa0041d41005a20364020307903001b84256101e403074450071960300700e8048026901906100c07041040504c0032039805500c07800078004544108038120720600c01c1c507500401307441c4c00140c002d04111a07040144c01c1d06c9030920305400540d0b228144140103100800449108a84000005006141c0003030107a0a8810240c44c40341001c4142d014040e40306400341401c1c1d031140d0240b2007489a0300151501c5c20403002e542c0d0003041007500d4042803600340022500f00200715041000c003800981d800244410440b01e0810040d084d40e551524210b0386141c2e406001489240740d030380342c0000e0540c410f0250807014000c8900b0003907a41e83e410240c85803040c2c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 521536627 1250 521535377 521535379
    0xc03180b011d010f0b071703070210061e1701020d0504050f160f03110409150b0a050f180709050d03030c020d0804120c0f080d021e070305040504111b0c100c02 70
    0x1800c2c000c1c884170310013030802c817803182c2c04a1503283d004001100e8950004c40c1c000c00141d12820003540c04244074013807440180700c845581203103181524680c142ea10400d01924000c803c061280800d82c074425812100598200c880c10016400d0516002c0e444105a001840644c0f284500924a2140750782c0c0c070004603814541451071540c55540c48072001c4120710f990a9005035500203100219801601301500c4c10215180052101005001c1007072030314a45c1c2180e0700400701491254103940355801003000d42d80c000b5140340c80540e00e10b20300701c0710780816422580d081051883e1100415815400011307a50b001e580a80d42c090032004421a20b018013240e01a01ca0b4001d100e901c01254007595100b070303995000c1ca4102c2503044181c0c846100a52201f1812100541e001404800c0c541d1680c29240119180c1ca000e40c0c42c02d03803d910001d10b9409a8015948100e94031134401e00603041440c100d45848000d0200f020380c020440f810240c5401c0c44c032124602031820003260080040c07088001d0203101c1c0e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 521537877 1250 521536627 521536649
    0x110105010e010e061807030203010503070e0405030702010c021909020310090e1c1403150a0503030412062307030f1d061f050a0b03090c0109030210030c03180b011d01 73
    0x210300101480a904003802554104030380c10030940c5c808402c4004948540782e2503d015036a549000241480c0042ca9842102d65039410020b00001460100c00c4449564091030002811031560000441c4601c1c48410401c06106110000891192640246100700b9810010400d600d03900c001810540b08943c1d00041550031607420030100c506005204d00c030000b158039158008140701c800900003a441a0380511803002e120b2103a1245203800e0385154041c0205401440c2080e2a180480b400c0700e9200c600104000c4d11990401110110009407260916003044031103203904045402400401980081e100d16a044c520140c00d00801d010781d0719602e0f2071400050030103594407540302078104610120b465241100e2000020140e6801624002400c50300c01980e0340d900b011001940741c1404045010305200c0c40d49010409640ca006003904802040d043c045143c040d500c0c0110010f0000800c41162a4212817800d000d202c22458454182c40c0000c0d50440f540180c0c40d084012050240301c2e07107103058 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 521539127 1250 521537877 521537879
    0x1080c010807110a05070f0602030c120703031b030213050906100c0c1205060114011812050705040e030705060906040206041a0d050a0203160e03071a04031208010303110105010e01 79
    0x3520030407100e90b10a50a00d040c10750100c1c140506030803c0240c0c0d1040c4c502ea4058035040c4000740701c2c0c00300140180b12a000451818101107000f0340ca48280054004c40035401050700018140690401d000380581c005180c08490400d050160094200500740310204d000308001003401c3c1004d44a06000d41e10003003015801c9115031504440790718080004a4044018081c0051081e142d1a00700140d070384160054035803907050802034001201807254503810040700c4181c012941107040c42910688108601a445280607400c1c803038589022079201d644c01c503107000110901c00c0008805080c0091090090351000e44a00814595420054902a521001c1004200018a50240102c0c0c03500c2c45000c50b00d0500030783d15210000c03240c0858070703140714940000403c00051b000c40c511549454460402c11407040e0b9010109650b40e403a0700a100d05061346d24180401400c1c0303d02503030300850b440059102d9011544100400c803240a01c0206c0104051f148a02c03184031045c00703082d0684062110f01c10403a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 521540377 1250 521539127 521539129
    0x501080c040f020403081206180118020c010b031608010b030a150c090b0319060b07120509010509060d020a020106210609020f060c06010305120f0f13050d0605041a01080c 75
    0xb444401c410110701c640c01c100000003d40094007820007003407403129154151405100303001e05400503c0b00106843c0c40e2000500521103070200007070b11516922030040e11640300c0048a070040c803d03c0f52981d0300d4030600d40100c01030741d0100c200405440c11035000344418a92041413554a440b41e09005004110201e041241e0041c2940861000801c51134503201c52960351400302030a034000c1d5115122070f101c4209010301048140a04c0d0001c08112030001d140000ca41c54805060700036001a1041180018500c0315a030b2244098840ca640000c040c90780e00c00180c0000c8000358003054066015500f002c1c030000712030301803003104840e40c103022072201401d01482e6a504000e01681c0f00407a0301616807064428552100c10141a40c032100030300420703141d411070800031701d015100300151035062001c1060f600700e02880810740315006d0020103440c1d10303460751800200041c0d00313075007100f82c0104541e58128140310f150740109000c0d601524400220711442600c0f02d00d056002d020781251580009054445 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 521541627 1250 521540377 521540381
    0x2011a10090b0406170105011d090402040b1302040305070f031208340311090303180d05060c121506042303060108010f0b0402040f0512120313050d030501080c04 71
    0x108030241d282881d0182e46407582502a900a0707000301d070010f4000d0043c070000c9141c52130224050003003401d110040c90704145802c8180310300d6146013405000c50310045011910380307802603c90100028543c584590715048005e000303410030302c007e95142c030503a00009500006032000c00107480d000398000412450118082e107070050050940400c3c1e42e00712092012000c514041045c12409901c0c14034401758000b04010145c071780382c844489850400b08038024651780c0001c101c48221110003000d20903080541c0010f0300b508100030016256008440410078010700b000d0050a41820140f0f0301e0455031180210b12416688200c0120b410804c04c01062180008039103159141d103081c1d05080e100410204007003800d00c0001c0c0d00c01d01650303444201c2da041c0d203103150140d40200801600c0440c1400d00c0d01c0006180004a072140e14002e52022182c1e0414060902c0380350700c140e204c8029181d0342e0510700c0c207070f0426140301079090700c0b540240000622298070034041d440c101c0e4100c00060042c041c1a0b420440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 521542877 1250 521541627 521541649
    0xc120e0c10092106050a0606270b0705070501090608010305060f0901020702040e0706091a07030e01050c0703030e011704050606060f04030c0b070201230706020f0d05091c02011a 78
    0x9201c4018070005100f0560001c510580c40f10080b030341c982c480680b40880c1a1040075107070310b03a50b608101c800d2020984c49290910394950501c561102c041506a01041506e82a08000d01e0700c00001034090900000140c030000b2501c0a0f40d07a0909155140d01c112820346080c080106950004008282001c3c0c04102c003680200d0008001480c00002e540020f0450302141020401074200038410001c1582000e034801c01484080d0001c42c02c9070056034100b06920030420000c092081c21a04001164890001d450340341c850b100844411503100e0401400d07009542c5501030002c0d40d095040b00c0c1c04500c1202560040750b10000030b1495444d82070401c40d45410a052a600c004014000000462110380d51040242413800380a81d80300032500004044862981454880c00058103550480d144140c0c00c4034040c580221006855125040807400030380302e80140615143e0400080c401184004650080454007030354001010000b049410b90030b0315103441c0078050b02d811517004580e0b94102520708203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 521544127 1250 521542877 521542909
    0x2060721110c0f160501020c0405090120030103061a03030307030902190f090b120601140103200a02100510060819060f090606091211040e100c120e0c 66
    0x8120312004003001d45168000410200583e4080804074020381070510210142404441c100e0a085081000207946c403030041c081c1d280580d64032000900f60442c03e501c041c0a00b6210340c0b03d842d001c41645001e80c00f40d0428013041e1170711881d00340300b0b180c10030316001d039410001310103009141580d0301d5040913801429142420790304181c0b0f07921102c1c00b403244056000c02034100380e415039040c6030400740b800d01140d404000c0ca500913116403400c0c03607015000044d0b090441d8000e6010190b50901580102d01402e0500d080050b956a243d0351940407085103000f4002e802420390880300b6103002028624143c940954031256100980f04003880035911800d421680500c49950a50300c803540d50850508a403401d0f0311440081601d40c00500039400680a480020f00a03482c0c82008c0c1c60900c103402c040400e6401004002c941048410810313038459070894485aa034007001c0e100410907498038540500002c0000c80c0004880241c0e0070141103180c0b0039505080e95441c0200703000500f0b1030a2025102e4941e00034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 521545377 1250 521544127 521544131
    0x70b04110d0b070c060518120c070f0e091006050906060a020c180906010f0f0501120e0d020304050a210305160b040f060507171605040b04030c0f0602060721 69
    0x2007000306815510480c0101d0300c960b80c2007401d03040d0703081c0324045032000342904c00c003070f2012024803046c1c000028843d0b4000d00e0380c0c203207607a49403002c40300c041ca8003441f41e00005c0c5a001c900b40c001450300850200368030610301c19094444441c9041031020440f83d042c001c4c283e10606207000300301d41e401d181c1c000e01406459801224020894403002441070500d000b650b180050f00c0c1010080d000a00740a603c2c010304101454041c0141044103400a001041c000d8504115801c010440032640640020008041e01c40549108010120009480e5030041c080c2d1401040c004200280407941828402860800f0b0008549890308d186c0e81150907501c070f040c0008112103400e610201003116400c245009038821405c4004180d001e14000c1c041c0e6800a02440c14080d10301096500d5030480340101e0780c80303001d6860f00440066810300c16604d502594000c0d2100d40300c049000310803c003c02d01820140d5100524084103a030341c4003003ca0b5074410880b202000504030f01c4803001103d0b0480c5800801c95602400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 521546627 1250 521545377 521545399
    0x703090b04060510050904030206040303050c041e1707030302030715020f180f0603040519031404060302030612010b0a03030309022205060a0608150613050d0c0e0c070b0411 76
    0x5280400041500c042d038500e95600e040c8800720075940c001c00e0007400d0641d9000454601620040c3d201c24001304040e0501d0b8590000489031802c140448000c1d114100401006600055201c0d0341380909008a420320786510300640c046074000614101102d40c554001c0d45454803603500c01c01e0b1030b60f03d90600036002d030302804115001d04150b00607152140740c1070312107080711900c00c0070041103187c80c8032100c1c0200420018000420390200da04200d01c1545031540d00208828139080b16003116079080c074842d250000c90085602607040d00114080d25003103410340c2c0c000079400a00f03800c888080d0015a400401c4400400019000f500455034481c0001c1c8050b00000500b91212101c00300401003540c0650380c2c8082101902e003808100e005041a40f500c1442c610f060000322070103141220005108400115030984800341c030004680140c40702a0048540c030715585020901c00100d030164170b071f05100d49070008000c2c162850945c0e02168001003c1225500c07240c82c2d0000d0304c014200303200c2d042100c4200c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 521547877 1250 521546627 521546633
    0xf2a09030d080702010b01030501030c12030c0804080d0806060a020c0112180605180a05060c09060c0724030506091602030d090c080708030c030a0e0a24030c0201020910030203070309 80
    0x820310740400600d80760240c0b14500381c0c500030308580c050407419050518240062001c54000120002581c1c021014160b0008807424256088500684001c0c400d110001d80403900b08000308100200005a80b10404507841d040c040181c64003a08421500584c040d81c0c41c0c00b10356214402c4209107280e0b800002649910203030040000c4105548182c5410791030306c082c0031842c0c1204903c5800c030321006026040c0d00505a95043d00e4110180500c410f514000c518082669a80310440d100000300100300d4211640e118800384129048529401c443d19000c24502c00c0d0301d00a001d918803400300103005407415952218808021300040c81c00c2021484140200c4000e804188034541220b80592105c1a466141252080c41c1504135080040c0c04d030400d00a10380b0460380001914070810040c20b00030b044c3d0314000d0101c1d004407426400501200c0b000c0d1203071100e04101c50043c00c280c510541d410301005011030f005900b41c2c440c0c0030006801c03001c0448851181c82c441d50240d904100c1503d408204070085417 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 521549127 1250 521547877 521547883
    0xf0b100f06021b0103020c0d14040b0412061506020a03080a0f0c0306080c12070302121207081c09020607030810080304081c020a0b0c090d06020f09090f2a0903 70
    0x1070000c002603804100c3e00003122141036a0301c1000039003441c0a515014643c48040d45400031a00444240482d40c4140901058541d054802920004080305c0c2c8880d0350302000040500030150586140303240103940355050030b07030f128800c06503203164005011005c0e480e6000c44d41c607400280f50300b010583e25407a8851140c200e024800c990092941e01161043c1415102ea0a06c0a08555035229940c5540707803201c0741a010891400322a01190300e020350492441106052011507021a90344030720004090040000f00806000b20a4803400e0b4690b003001c14407040b134111550b2010180d4848010b1001302c001034460502203601c2054102d0304601c0ca40c0c0c0d06106460b50308540c01401c00d41d08481c450403603408529241760b4440c40103100500d900d0b03c15894282c803981c0068100da0004600240c0030440b500c5600900201560002003150741c3d8400713001420207a04101016480b07011000c0128078100c082d404d03014020700411000c0c00601c00c411005e40030100c2c259640c1c400b03c1c0814031550102d030f5024 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 521550377 1250 521549127 521549129
    0x111209240a051c0f0905070b0a210b0d0b010e0c13090c0216060f1128060e030f09040e060403350a060315021306080408090a080f190f0b100f 62
    0x132000c5644074042c40e0090604086400100d481e0b6400c1c00090517080c2d001600306e50344208440c2a01d54110707400303000c0018041ca13044407600000080219000c00107803a410038102d4541032204101902c41d0903c840e8030340714036101110010b4840006008545941c0c2c00094038142c0303801107520600c6210b2203000b0145455100a000c0342000041c001510b40008603000307010749000280c0071000010707121100d481410341401240340100c440100c10089640d010104030f1914104694491049855012142d40326015441c001d600b45510541c640c40009002401590f16490710110018103580364240c200041d0b07250b41001c1003900a2031031802d80c40c081e8501401105c4c601040c41800c40c141200355110f5403081c60315243c810024425400811741c07044007950300c1e91521411940701e03030400c14400c0c081c8104140d4010310031040000d111000145250403103540e02c040e2850103040c0d000f10462443c401c00b000d054a08481c407880002401e1130801580800103404000710261600c07000b084421103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 521551627 1250 521550377 521550401
    0x222003010603050c0112050103050a120504080708030d0e030a120f020403380c07080a11061003030e031f09140d050310050a060c1101111209240a051c 66
    0x440580c1d004c0559000802c0008060b11070424030003549540e48250f69802d10f090301a007189016204090380c20300c034000b1a0000c2c4824411600000d4842c808251264040c2c01051141d621b020500d500c0400080140c41e03450a45448008008240c00d0032a40034090b0500e00d138000a07030800002c00050031801002d071500f0200c24400c4800c00240c0345c410310f0402d105100240400014082020801c104422108443c3c0e01c40060364031500c0c8150300b80c035200000703680d4038030304c0c0680c07420040d441a0f41d440501c103c81c0240d441c02000c81b02c0c4401d054548e00c90002442050401b48880b08100101da00b105400314450074030380c0c500b040e4131401c403802c091104c048100011400000c0c081c030701040e05e60382030207898200c80c05414549401400b80035840041001020f42290945804041c0e010f4001042c0c51404035060301c100000401a01280e9801440803030f1060380070641ca00c1d1803503980c030307404005c00d00d540414070310300004020103035101e40041c0c0040f07003010500400081400154080c5010890b1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 521552877 1250 521551627 521551633
    0x6041b030c0909151e1811160b06041512020618091906090c0507020108090f06280509071716420c0f0516060822200301060305 56
    0x800d00d20351701020050480400b54146134414184011828800b104040e00180307400092030318580d00c2c0002e420b00510341d080c10f440005120650a1021406180d403094608440c2000f440c2003131320500c551854240580c1a0032244030910f0801400e241c0010700c102039000c00d4940c0610301d950001259000221180d60004040303980780250391885004030006002c6100307040c004448034800c0109503008826000e810842e51030301142c68002d050041d1031406415900b0350b11240b4200410f5036030244087c11101c1d02c80c0d81209640e55800d154402c031390142e80315901603c480c5160498000711200041b903614428000c4100c034250000308004060010120810003128000101e0314034410074142c00d10350b9070241c1c000d51001c04d070000c80381c8100c21085010700300424140c0007801c0414006420341c0e001020761042410740c1d20f80e800784a44282c1245c04903074034001980e84031b200c1504040903441010700c958243c00d440c80b000558010360501006015030074100702c4d440a000190070f6607001d9000340c0d42a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 521554127 1250 521552877 521552879
    0x20103141617040f17090d0302010b030708150f0709150c060b011d0603090c04050406090c0503072301050c0a0303050103050105150f210f0106050906041b030c090915 73
    0x582c1041c001d0b000d400c1041e040484074a0291608404601020f80040003100030b483c4001c038041d250400d07104d00040c0902200004141450043d00800c20a40b42c14428032036000c2c0002c2c0454000b40c00410008502d90f4000d03a92656040040e5031000900220240706044402040300e00c00b00001c03c0707000905903103c1400e0b403084e0900340200d500c26040181080a040050001000540c03c100c03c401c0701030314600d5a0f9940c054204e0701700b44804c2013041d0302c11304040174030090142c19000003141c1c03801307076200c030040310303910020036603600381038032440d0801d0114001c0c554030741e01481c045000840f0103042440c60114a1900c1078107040103c4070460200341d1310401807040c0102403203031640c01408003003600640d001c0200001e100003a86503a1a00c130f045444013849101c400d40300030420505800080740c231000300018005010b4070a5001e524003501119000078034a1515000d414003184201000600c84518207104502601800000400744028104001414110b0384200e507032a0126454003282a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 521555377 1250 521554127 521554171
    0x4030f09060503070f121b05070203010f0c08041104060f0b0a1d0102101e0501030b0a0b0409080304110a032a140f0d060f06170c011805010c02010314 66
    0x6200e9003060741000002d004114034590080d52800c0a18098203000051502c294032140140040203080713404079014501203000030f6006806003035403034806c4009000d44440c00e00d224007152030310700e004e200180a03034010801241360780da501892104041d101050312174413205000224840d40c0c1c040140c900e40003801e003001c180c2c000c030740000500704100311440042d11880000e603122800200d0300c190710350700c081e44041d001c0c03607034803040c1d082d5003040e401d005640c7d482c00d02c580d12070411104000c0160402c21000501c2c50588900c003084d0b548200f07003604584541d150019551403140a6682207141402c0220100e2800c428964000748041144214182807140c40a040f907015804226210410810b8050303c0d5a840400c418029060742c0354200641c4600b0034402815046100c05400c42c507100011030740b007003113009901d01180700104441d04030345071400440301e8540d0484901d1040c92815002d20541d0b200340c40c0c0d0b2450718014074022501e4411440d40350117614095401d11501205c2001d43c8001c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 521556627 1250 521555377 521555387
    0x31302090c03041505010b04171e0109051c0c08070312090503090420030c1c020c0d03061d0708070201021c0b09090f0615060f0a03091b080304031709030604030f 71
    0x101315075801050200e54075101c0c083c40f80340251300500d004c2c0e0008440116100404000300c1c80482d011403a4000d01d0054401118004d06500714192003d01a204008038a02d510030078485016005070b031070308806940d039101c5005035001004110204a0258000a192003003070052485c06802540038540d540b880c04204000c4a80001480410101800d0803054108084058aa00c1607400e80703240c4d610900610203100380403001405000c0d0070301c0801c41c2d0194400005e01283c54004986003003041e103440e42c0d584480d1198041051504205000000c0d0140348500007143e002002800094100064101d0041700344007000906141d0700d9640500c18841d1405030000c50b0401ea0b400050641d581d418030450340ca502c0000c040300300300c00040c101c5141980741e0000715036680031002c2c0050788883d01280000d0203881590340589520890101c111840c0c082c00500200f21481d48005506c1e02d443c0d80c0c0c403107440e034203c50720140320301a090207086402d843c2808120700c224860394500040120790500580 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 521557877 1250 521556627 521556653
    0x5130e060a061215060e0702070915030f060b0310020f0d06090c0507120509061b012007060b0f040c09080111091c14030c010c020f03120c031302090c0304 68
    0x110345418114104003000418010720445a040352188020740c00051512005c2d12103a408020310305001d4081010303150340031408205468140c0000d0003020340031070701c1c0c48459003d8000030300892201d0fa2100005941e03540400845400901502d0980c441c140d225000c91300301c650000c600d003400041202180c6028072072040a015a0320003040515485040100340b4041e00c00018000d44400307502804050081d0283e40340c0442c01090b0641e1180700400d11000d01e110280119029800c1c404803411102c5545010f540030503000c8440c6007000000d07207802c40a44640100150042102991240c13151501e0141010155007501c0781203080740343c01d11113400c4800c60902c0c600c09a0046c0400c1c4801d07510403c101b181d214002d20140c48141190400e1003441c522918102854400084c0c2124490b07410f400840940782c503602171301c2d01d0b4141003450036102e11451594404220311100043c038000c1c114400380d074020140104071102060194045801c401050311031400041d0080200420401c58001c50f00c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 521559127 1250 521557877 521557891
    0x2100f0203010608060d050f010203331e0406050409210806060d051807030501052d071808010612060b0f01171f030f0c0e13061505130e06 61
    0x1480d42d894400010030844d0041d122900c00c0200104540601004000924000c29000d0085642c0d0400050120764401c85001d81401c01014854029260803c6480a03180746406000e9070051840b4400e1824070f11a0000255881641d4400100d065101d912032620060310404801c03003001b00f003254024401c12402c2c440000c1241c280100b1001391585415100300c0c85c001d04d8003141948400c21180310446881b940c60343d00748500e041c00028800c05402a501030350801d40d00341300c6d951070407401e042c540b8205005a80e207001104d01207551a031040407203a000c2ca5a0b120400241500c5003605425150a03612a0050400c160395207030501c6074500ca40c500202e006c0b12084100c0e0b0885002a00d0305006090701c601030101000016007001011011080c1c207580c50f041e20710290703201e14080402c080c1c0050f0a4500300b05a031408941080c803440c1e128010540280b030908048925591607020340304590128030300901c80400010b40392101c50710f448520203007580204294466090b00c80c5801c0c4020205 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 521560377 1250 521559127 521559131
    0x110d090b1f03020913080c070302120c0f0907090302030703060605040c0c0b04061e0603031706030a0c12150c1110150303050c030408071d0129030403090b040602100f 73
    0x30801c820800d0094003141c0d8141d45400a40d6110801481e4544c414000600301240010b0b0903002940e000c2180801d03241b00b103507200802e0394103c5142e5914101e8000058006406864070341c01c40c540028042c0d88030885280801c0682d407a40e02013400c0c000c441c0d20840f07150b5244c890500051400d0b02480052190a1070003104040c2c41d40c41d00c00f10480003078805050f540e81c80b10303552034034600000300000c18500d80c40144411613592600a00550f1050400840c2e4101c05010a000c2d15011070460399042d0040f400001c2c00f4148465092200801c0078100da1402200b010500020902d00815100035150b85804239011101880207040c00e55216a50406920300b0b01d2a050203d40501c10a040c0c4c0e400d403920035182c041d82c3c5903c61461013550070400e11031081000c005200000440000e603230703244006100c1c04d82d99807581c2040e00034051180251040031a90b10784084030310796501a5030703c03074000d1400c1081c1a503200c03246001c66201d42c0003180140c01c000c5180300560079030f019181e600c404402003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 521561627 1250 521560377 521560411
    0x22703061605090f1002071a0316080a0207060c03050f07031523030118140c0307031e0f0b0a061703090607051f021305040209130b010201110d090b 65
    0x1407a540c95910041c40d000340580820715041c95221807145004103280074204201122241300065602e4415104642035101440e800c0284502200203907400341d9074020b552140c40305a0746040d41c125200400c2555481c0c0d0074480c0c480403450780d0007410403c600036100050141041527181c0d200c0980285503905040c20314401034002c405401680c400c59202c50403e80440b0f00b481d8801440c0c00d003c04910340d0640c200761444c842d8281d008a8400b82a1103082006002c1800b80011600d0300300c250300382945504681810404520240002100f030300b108404c00c000d0042e990354803480744042c054103413000d900c00c0f81007150311182441040040c01070b0b0b140707291001c2051840f495482c07040d030b4682e602448000c11041e003004001c20404200711007402082d8550b0081060110094004600c0340c400c80d0000e0310000760905141c801c40c0c50511010b8079580c0300d901140700701c5000c0d128081c200e50456590700c1501072946284800b90000f00b04040000c100850141480b85025030b003e89401400d1f900598 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 521562877 1250 521561627 521561641
    0x614040c09140310061d130807060c110a03020c01080709030b1807080304080f011503030512180a031d01080105010203121e27030315041104030602270306 68
    0x1200c4400c0b00e8001140c8140340490402080c100f4501c5404c0c0c2c01c0c1581000000329003110300c80f640da2610142900481d040b0703a60036003080300100700f0b0f0a0280c20714a0030000d15000c41c4154000d400e070344080c0e05000c0e07901c40740000c00c2c5160030584901030300143c00882c0f040400c0d40e84002040d030094441c3c0f5000c10002e0540d12050101d04004e80309190b040340506400c490031a0611601e001080e1000581c0d41b07469603440c14a0305c0b1035844218851a5181c050400311000d040c8544609032078169a07a1400d001a240d144499014042e01c850254034903080f0080a46e08100510603149200b40e4564a2989594102c0160320b03050500c1ca606000c490300c01031205903800429105124054060144540c6400c50040103021907200803047c803242020420400840c00b48800d412228400011030703014034658605134403408282e9540129075810720f448400780c5020380180c0207200120f4011440c1c07d81c1d07030395140103d03480008509107091140818540d0990b03600081d40d080441907003d0165840c00e21 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 521564127 1250 521562877 521562887
    0x30c041440022719080601060f02030711040207050a05250e01120b070c0203012d0614150408010507080105090a05091f18060203090f01110403060c0212030a0614040c 73
    0x2030001484400e4000303030f0000c82d0b500c0000c10549078500305206400c043d2220603054440c4d001f401030304003090014400c01441e5200004030382c4100d400c241c5000c4507681940412001e503000352010b4816200310100c031008a44280114040038444035820380c201a1000c0d0245140c03505648004e10000145004003d804103c0d8103820000f87d10000002c1181d80d100d8040e03809a5840074040c1d01580303008101c01c1c1c4101d039024580c03c02e41e590400c100e403000c2da0358001000c0c1d80180c0940c100f17882c0e519100318414209000c3c1030161425441c0c50780e0a0a0b100c0b2401400c4850481e00800014161401000307141418400703140c004200c01e109010a10303001444503602c4052881c001c009041c002001d0000188d543e00040c1044015010311551840c2c50a003000a90000e0398844158081c040b81004211b1051140e0610001c1134004a0304003407a50711048014001c8007500c200794014803011601c000b003058000c620030034000c1c80014940f0b0900021802d110240c2034254007070362428509112080c0c002c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 521565377 1250 521564127 521564167
    0x8010f1a070215040f030b190c0905010f03060b03090a060e0604050a030804020f18040b07021504060903090f03080409060504050645040501050705030c04144002 71
    0x151190103402e25401e41155583c400c0f6405800300da807030201c3c04400c100e03031f4042e014020a070f440c0c040b00c13100038210503401c203d56200081401240002204000c0c0b94010742500380060503d0070700080a81e91903000da466039104840c407903542d407c51703801c0d0020068240300b019400c82d251300042000e03203460b40d2203139507411117404041e0070300500800060443d520b041c14104a40c0d0040c0c1710341a4001c0c00e0700e03000a44501079a044800b0fa18480c0098041b6100040021400416002041d250340381c03525054010911808107900304000131a0100d81d1002130240301006502c030308101540d0354035049000e03045681ea500950310460038041444200d584d00d100145600d8030881c8946211018070140b8074580360b1428202040840420b105481452502101885140114005d008650343e0000c22243c42c402115800d000c1401844140300031004824040000c10001e0140c0320400b19840519900c0c2219050340c05034280c9103011401d46035800c01c440c0d030341009500415130030095485c03440c0c0f078141d81c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 521566627 1250 521565377 521565379
    0xc06080c04120516080c060a08060d0609051f15051e030d05090405010801050f0f0714030a0203150109031e0303061a090a061d04230708010f1a0702 65
    0x108102003000500440201d9000704181c2d40c040d0300354001898029244c2c00c040c540308440c8100031a001039081d5001c0348404500800074402ca25140418000f80e45026000d040b59410a1010300c054002555502c07035410100e0180c03005015030707281024642150381c00c0c03445400000c0d0a0031002d14240004840705402e80340d088814801410780700741d8080340801d040442e40d44c984a074000300324560380c21100610f8a60300940d01031006070b0301e50703551500303030790f42a55070246c000d0912000884908502c2ea0490f0040d80d00d2400c0b42d103104142c2c41591458006071019420190b0000a020040c8410040710300340b05002c6c00d09501c11807440d20b800004075400c200300c04d01c024001c12920100b620950141000d442c02d400b42c44808042242d42d040e2541080c2d000600940814001080150040080c1181c281c0c2d00d1154035207003d004002c1c40f015000700240401c050403584070761121851440c0107188250300c166296a080d6240003100000000303264040040c404100388015030b8612500c044540e10341d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 521567877 1250 521566627 521566637
    0xc0206010501120e010609020903010605150a030203041e1a06030a020a0302010f0e0a09020702033f070212010e1207080409050903040305070e0105030d111506061c05100902070c06 79
    0x3a4100a41014040304c11103401503510b07100f408152901d2950192099030300c01c2c0d0007041032030784420920005458581103890483c0007886403040c0c1038444d40042d503100b4841c0080c05c0c0011480103104400d544d801d0411243d030761040c03a003001c9100b42075445c07550000044009081c60a55038000c03c0050545c1d00010b410404e141d800010382d503008500314954924007900c00300600b82d655086000135003044004074441c1c042c0b6880c0b001d4200c8502800000840020751000c07003440122402000b0480795032003812818014042d22000da80e504c0451101d10510300004160000c0c0c040285003016400c1d006600e8500050088002190044003928141e480750040010640c444070340c0d00d4610f0003940d0000301244074004020030310010f0404820304941040e001ca900301c0d0821442915000c07840d0245050550010910401d045160f0119641104002d002a4034011003514418074000c1c03150003100146032640309100d5888143c0b00c500c001442c10201c114100010381d0750f58480c0c01d4640c8a040d0402c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 521569127 1250 521567877 521567897
    0x30708210a0f0f270314060609130c0911070b090304060c1421070c0905070507020f2103041a251a070f02060718150c020a03050c030d030c0206010501 66
    0x20b02800513180d070440d034000340c0d0151106001c008080d0494030b0200300c40c10802d407980001c5042c5e0010700f16000d071100800281107996241400c40c0411000041074070207640c4c141000034405060300c500c0c880064400c6c002a92450a0b04195254600103070110b11140d00030802000110f81c41003501040070307403206501900d406542506481c2c4900008000003054022460681d01c0850720300a1850f41c0c81029040c08070f81c0d0741c08404003121f9045030140b022900810501c0014941000d05100e160f02c010001501e810201c0740300301c2607040500d951200c0764000a01407080c17011804444561400d4041400c0c9404d860138490619051460341a420801d40300500204200100d895111103c0e200030300b1125520b02048010001d11120040401600845011070441c034400c80c2021400314020340c00c420058038082c68900307116140108101000068801d02c40140c0e41c2c840f400c401103000e60014071154640108043c21b10301c1071070304a424146400c50b1204202c1d004a0b0807811103900342882c103844 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 521570377 1250 521569127 521569157
    0x19110607050304051c02030615060d0e1501090617011a040504030504080604030c0b010608090703080c0106050a092c060601120f1404032c06030a0605030708210a0f 72
    0x500594000e41d03441217020b0000f01c1c80f41c041480910a17503008038100c2d6141d490300c0e80d00e1a184000c0e00110b0750030550400c00302c1c0802c100e82d00b189901414a10841e100900c0c0511030b20f40c949401e8118a280d25120f81d0100131203000c5500201c3c4016210340200040c1300c901e00c80304c04002751a84d0240c0240e460728000f805050140042d02c00402400040d034485180501e0b0041c030310079070890101d6610350f8480011803400d01c240da9540c8601a420028880281162140603064100510f1014190b490341400308041d2100d00d5440c00404d5502008200d50181004605d1030110000c4c001043c2e214200540d40100c8000076001c1c1c00030028200118060030300c408100c0604401c0d800010402e0510b807020b140400e805051910580c040d0f561007c0500200c42c02424040c10700790000207000d04055000e042d807602c400103580008207002c0000b84142d441c40805e060600d00d0303004149030b400c155038101040c030362046804642861400c8052401401c1c8038090300070021856041c04100c41c5245400103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 521571627 1250 521570377 521570383
    0x3030a150807030605040605180c040b030f0a0305070605010503060702150c0d050903070210180608090c092e050a06031503150f18030c0807050304030b16021911060705 74
    0xe448860181e60a00d600e0f404d208002d01425202211400d1400303000500507004644059498140c600c0079207943c03d51001003102400c94440625418040d600181074090410440d410b4800d21a44849031206614200300045481c164040ba0007500f00f5400c00442c96030201720310f1044c0b201e000080c0b0360394a0302d50910619000303000346a02010315200901c0340c08400000605403c500c00c803403c04140c0c1c405041102c2d500000c0040710540141070740248000ca0040100c5a4000070380412142c507405000d001a0b0304074403d07500110418a0300c0c5130080c000504a0341c140e00c008061504115040c5040c01140c0d034001244240402c1503036441520f081404e0a1140000540d0401104070880c040100c0c090001d0840582245542d440e10300c40030700d02094030384609034858044d1224039025546032121501c030390144c10112128002040b010000903c44800715005600b4820118074800741d401d0007901d003072903000f400c207d031040c0501c81c0390000e0f5441c1c05010301010f0907541d054541c2c41910f0701c58a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 521572877 1250 521571627 521571629
    0x8010302060a030b030313140a03021302070305070b0f071805010203030c1c1401050a09050402090c0703141306120207240b150d1514060304080403050d09050102010e010e03030a15 79
    0xd0f246c04001030310a00d120241c0e60039010354101040c0740828500324002c009420300c080c131000b500a610f0000230140c90f074490340a0300c1045d0190802d1440c0c55520350301d030401007108035a2011039007500e5003400740095004141c0d0070013001c011900c4208905200c0040c0d40d82c000207120003942c4000140c041050030744c1d4485c00100180030f840078001205c91030003d1384260b409008040c020502c10300c7c001034060355401454051070b0040c0291541f030301c1d0119004069400381c1c10079070901c0302d4403039200c500a08490040400400780c1821a5100c1e0400200078108500a16203a2040c0e00501c41c4070041446081410b00f881000c100c4940355961050760316003d0421201d0140c0d101d1101c540303007c0d485507414000c05030b00102110401040d01a0036124030340d440e0342e0040716141c2c050012008001e0230020020368019000343c1040b8101035581e41c0f0b0034900402c208c2d0060024000b0b0b03c0411865070240182124505c20000030300c6544e07540b01c09a03a0300d0200502031507000c3d03105d4280000048019031010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 521574127 1250 521572877 521572879
    0xe04060c0e101205240904111201293007060201150f080a06020f0403060504060209031204061d040905010c091707030218100b0415030b03010b0108010302060a030b 72
    0x2901c1c1c1c1c82c0c082c4041c0c9844280c4421a0640e4200340010300e106414040500a070325820000c014103242410a124031201c0041045900d240203000ca0038042d070f101d80c60329402500500001c28840319126090100185d50300d8402030245449410340000c2d0b4650b06000c80c0f624000c1c01d4858441141c14400c1e425210000d580e140c94007500c880071901c40e5064100c0d0603900f8020b040ca803956551740048481110603440382c40400d40202000c200060403a40040c2508a8130070302507030030a900c0e0b0b110b65089860540d0100e44c1e85a00007080e00481c14184524079940002c40b0110f420640342020190241c07107107000d0a042c2d40c00b442d80e059295511640440c1d100d07500b0038003c0040c420688406050707400107010b08a4081c0800144c9940e600e00020140305480d40540500300301c800b0445118504c1c50040c01e20b280c41d15008a001c1201f003c010082c00040c46000c41c040c91082c00b844000e41102c02c104038050080c0d04013090000a43d070002041d070b04580d41522550769542d40064201d0040810649ca5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 521575377 1250 521574127 521574139
    0x1a060708091f02010b0a0b0a05120c0c030409060303020d1d011b0c030b1b0a210e100b0a08060f0f06060d0e03041a03070818010e0106030c1406040e04060c0e 69
    0x60050560541c054410080291b80c01448643c4a6a4050b0343d8081d001c10940001e40410030f04c407030900750560940d04844044000c1d414150b011038401d040d600190040504150341d807004205040d030402c485d05a42c1c0352810a00c1c10300d21098010342010803100c0049050020803070002c2407074100c180d6124103064201e03101030542030f164a0a030b59544019102c080401c5094600102c42445650803259410282d455443d10b50f081c070a06854402d4410100d2a030f00c503551541408400020f00400c002c901d6600400214444840c08202941c000398200c044154400010012548050b4208581040b400e594541d02a51a100026447e1062401240046003002d2a190704000d000002e0804e50b0100304034501a02c0641011f030300755010441d160000144607002240c4880b0b10035040407041040c000002c9140c0301100606c9094560030761040701c404001620800106003403007079460601404031111480c1920700080c1700e11501001d00083c060301e640b030036100441409135180c10042140038001d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 521576627 1250 521575377 521575429
    0x2060717061810120b06040b030f060604090f020306160f031a0d1b0303080105040f09050c090601031d060115050304030801060e030c0a09020703030e01050601051e2b1a06070809 78
    0x45000d85501b5100c0310300640c28146450301311328021480b01e400e42e403241d0060050781d54000030030000c0c1c9000d000942d1001e0107a40c3d4031015071000c0c4203082c0700e00c041444030400005410801840c038400041c00104040c0742000c0c181584001807494484e8800c1190325800f40610390411103140c0700040310342c4040100d40c26001042580044000341220310407101044154044d01244013621203210f0014116085034805114616042c40c4aa400200614002a540242901640c803442501c1d8407552554001e0b00100428092401804c0d03000700e183c68403904505066902415580060003101c0c24440e00d120a459070fa00c04001c180311000c801044a243c940d0340340b05500007540f020405400181c20041c458418070814000c85004010603910680b80c44500a100302d11012040103984003548100072600f68a5190307180c8102c0b00800340341139204410961641c0048901103100b070a001c0e00c06d909040082d40c3c3d80b500b0780d034815130450b00b420f40d500c0c03e420000307401c0107414459002d80308903103003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 521577877 1250 521576627 521576633
    0x30318070f0b03250810240813050601060c0b1308030f130f030f2303060105090301152d08030406050a03140403110c010314070e19060206071706181012 67
    0x2c001b800b902400000b51a65601c504103c14000094103040281d0041100a410003c1c0b00b983c0013540129180764500da504059516581804030a0b0302400000b040984074009001c800300c152a0000b08214102131032412a90312018079010040c10000d40544510010300501422003546422960080c00302c1000c5c81145130141914100d4842680002d039611076050361118000b44444501e02c07807a60b00350440d61a6401160f256114100c85030b0155221620810414020340c0e44a000e4242185003007010740201006005556450a4460300d2503580101040400703408402c89042c2c2d161850724036076840800000360064a481d1000780340d01c104420412081c580e0244804581a040700140e44a840051004500342d804004079514a440b00d82c01050701b190141c0613a020000d070207030400d8513200308403070500c01c1c100070b40d4800405604090108065140c0c40020044900c1c48135030030601c01d09040003c43c440340c0000e08030f145100004c001091264a1120000c80206562a60310220300c401d03107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 521579127 1250 521577877 521577887
    0xd080a030f05151503100b0304080703020c06040f21150c0f03090201080c160b07032c0316140a1506052e0507080c030318070f0b0325 59
    0x54160284640740c000403d2521440f40350600248500600b90314180541c290500c03074913403010b40105252440000d0009010301e5800c0a940f2840c05248180e440b802c0070300340a03040210b41d2115a02c2210100001c0c014130201825a0040c2da2091111300c1e65400514a1075000480d1928003400c0003e048091348030703122464001c407894904c9a82c54003514800ee0b1402e41c2945d1084100030b000c0346940e0f0000d03100f101040098a10900400f20300200e0109507101c2025011094451000180d11601007a0030106142c000256a01000365060880c40d6051262603d030301810759140380502984002c07605108100c4c1c100c401a0f040603003034910441c1580b9080100b10185901c50107909c1c10726100081602c0c000b0f10100052a803030240321000e09103031802c01001000d860799034041c401d0030720608010030030880c06012345580c1e4a006550724181800d0081500e600c00280451940c0003410a008122500007854110740a80c445140c49844809061200040001003200c0f0000351180190842d5800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 521580377 1250 521579127 521579141
    0x41113140907060504080c0d06090c030b1803030c09100c200a0f0509061201020f16021e1e0f0306090a150903050922110408121c09020d080a03 63
    0x1d0111901143d9610043e6601c0c0143c2c81340e0525600030516803035a07818601001c0d40510b1061b480058070011940e20b9000342869a0019120007928004100712204c0f54182039940b1499000210304528040321a541d8034410034a03543c2c040d05010403044000c5018515171a0b1450740704078506011805000240030310303003900003100d1094818440009680b680c6070844c070103896000c0c1c070343c4404d82ea982c000e101a600b034109024820359401c00000a5010302c1e040989250300c8110131200340e03070802c4d004020748000c19940c000003e480840e032405496440384000d81d0354100b00881407109442040005019440700f012503a00f40c003444041250f020306c0400d10503100c6120319031218403540640c040720700b20381e22060020049502001404410f29040d44003584910010025261134034046003004c05036078600f00b012a00b214049018806200284182d0a07004609480c45003800404080b8220100214400d03080e01540d0340c0d004815034136610601140c254021410342d41e42d41c6a1a40240140b1103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 521581627 1250 521580377 521580391
    0xb0904020c2e090b1302010903170301030606060503240604030b01120b091b090a1d010606111f0e0304121a0112051f0605100203090f1804111314 64
    0x510500e5a200030948186466036804c00004039240e81c41c4000003000b25800041641440308181d000030025074110200034014002540003512949145441c1e82502c0c1241c001c2c4060000901c1040113441c030000380da202000429110801422078000450641e1046070000747c01006000008959000103075000d5007014440c0300c8101d00c0765200e101c0152220009001040440c2100d0001c80e42031501e030700039a401c002035407400500c40800403064440c802e0854000003171a510f80780304020060700f0031070b01c0e07840d290352101038400d03460440341e00c20080046404045030a40d441e07140400c540c00400948000c0e28416607142c4000c8914140138900c900c4110410b09102140000854600c01214070360316025413110007400600d40c0c2014000d4407086039640300440da60f440000041075a540010303c80c6010264000d0340d5071b119444148140706202418450281c164044000007440c24107050561083e0003070840c513a8004100c0c0040d980703460047c00c41a440d400e0030440a41c00140c001c0c3c2500520b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 521582733 1106 521581627 521581693
    0xf080613091202010608073611040806060105090607031b050601230910031709040227040902010207060309110904080c0f0708070b0904020c 62
    0x81e4448281c030011448001101403c0d0284940b001400540c00602241803d00b12000b80e01100541d00510701d0461180c0700348803292034403a4401c050b80180d002d001c9001c01844060070380e00917005400c024043d00703011507115805581141c1a02d0006082203041006546042c3e8120141d1007025480040c10501000010824031240d03010b40040502d08100001400d14810001c012919442c01800700400348141a41400d105100300c0340e020203418000c450f240940340680c014555800d0700f050010640701d403c41071124010341c036840044000030300e800700361041109691080c01d019000d2b8104420900205e8803980010405a0040022626628141d00401c0313a1800803030b001e803942c00e401305d90350305000307400c0c4840301094581301e0041c0301060070b08020a03150305880c4151021034038009000f0855481c0c4da0181e80c0100514825510510714071180e02d1114109400340100e031003 = true := by decide +kernel

theorem cover : BRFrame.Cov 521402877 521582733 := by
  have h0 := BRFrame.cov_init 521402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 521402877 ≤ n) (h2 : n < 521582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
