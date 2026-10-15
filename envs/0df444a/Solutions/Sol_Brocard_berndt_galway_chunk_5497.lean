-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5497
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:03:53.574206+00:00
-- url     : https://prove2.me/submissions/0bf76250-c302-4bdc-9a9e-fc0aa210a111

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 988489208 ≤ n < 988669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 988490458 1250 988489208 988489217
    0xd0e01031806290301152606070c0605130c170f0f0d03140403091e0305030d050a060f1a0d0b030304060e030d030203090d080c041a120a0902090a0903 66
    0x59000c1112800764041155000200302686983d262400795000c41200001d882a41440c05010441603040d4151040d900312101c0506c00f1440380e02000c50801501205405500034030040003845030304403041111090040c103040c00349996800c1030900c21010220028a0080142c6051001803011312070144912031440844010600891441d4548805040031206079480140091145a030500171084582d40b0302588003590f0501c0d40d80a012900a4040c40d85000d04070035407000a072126802480042d42c0020035a42c0e2000c1030188900540011283d552080d42050707800144075031103840c22011540074583c24026404041c0403031b101075000700909000c0d1502c035603040071996410300081009014544446040b1030341d000c181400d0031783c1c0e0754604091510500400c102c4034400718010380000da4500d000d00169036210460b9240d40507942021041402c40305812211003805c000401883c0c42d5042101132039500c50200205541c08100d000303403c002043e020030000146074015200c5140309040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 988491708 1250 988490458 988490501
    0x1020a150204120605060307050108010b12092b080609071403060d02040e0a0c230f0114040602011a1002030922050f04020418020102070515040e0f04140d0e0103 71
    0x10038074424080f05105481c1103076148180601403404102d101c0090070282021215513140120704495801500500383c03c40c0d09060004a035090244070500d40c0751820301c10b101d030650f0300882c040118481c81d01c0f10f402155210000c9002440c00c100c01c24801c0080c1ea8030404050300820700380c2440d404c05082d0395003000d5503035001001643c0300d0103810b400103140710013031a0071011401c20102c6400ba40d4800c0d4074000c0c440c45030104d044161030341000001001c0d150034440c0c82e240401281c0d401c84614850079020400315010a0071070313064000b00d1684070f00c51050081340301403000f0040101c940c21442070240c4e00400c604036081c180071200d03182d81c1c00d440d9842c3d070782c51514402d07000a0b20012a00c159804515038200b00841c50180b00305180c10b2071058005c0304011160b40041e580e00e290380540792251480c42d110f000440511030807100544040001ca000d0707410080380081049400f038400729040308403220301c0c03d0900000614902d500200707503900400703d5442c800640050080700c41a1200345000c64 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 988492958 1250 988491708 988491719
    0x1603030e0d020c090c0403020f10021f05101a03161107090c0f0503040c03030e13020c0606030c1503072d0f030b0402040b030f1e01030f020103061401020a150204 71
    0x4006120702106030003a01c24007141c00100000038000820034030030b88401348403e00250325810906016040d0035030304005455a02d00d4242e1800c0c0394414008102032111500c0d480c2c038041900003a006481010520f00e0064541d10185250380412004603441d000500c00100c01100b6113561440c031601e01d0401d820307004894508203050417840d40118030206d032185904644036501948034201040646065421410103548181e580500741c4005810006100448521540d500d0030161f01d4200c070540440d034031440d48900680b201da0490f020303442401040c20200380c0381082e80b8041424450110720529651750043c0c2510350b40d0408195102800c0107a11003954103c2040788544481075a840b904000c01910b074008050314106004180128014401017081c40d01210540383c02410000c40c0484036501c116825800400d240b5200f2410b0115034000003c1c000303030656002d0080c0c003e80c0d0501429403100140c0221004480340d0300e0050788410b1549000c1003c4003950196401d83d484003519140e40c50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 988494208 1250 988492958 988492963
    0x406021902180c070b060607150c031104080a0c0512150903040f03050c1306050d0809060915040612090209010605130305060c0901020c0d0b061e06070605090d141603030e 75
    0x2160f96082c9104009160014000410710f00e0368000000c0340d10614120066036000f0001280c00e2078103d00640b240d50000100d4040d41010822071000c481603500c5a940303403900c0d6960041d940d82660941951200403456007854084c0c01c0c68100c3d01e000500c803075103901408511a2074001c10440072808140004a00d808142040314025400b40000f010321108140421040707800303200300c4140040c43c00307608204c5511a5507a4199481c0c100b8071168980d0401800725941e48503910f0309652007071083d00c80ea403a007003041c80503200390380c0300380d5440e40040c818032084070450704260406940904943c004001640c4668000c0180300c8190301810240380e0baa0f07941a103040001c2da0740c0c504146001c0b428203c5541c0c10003c100d03000d0350403660140b18202645a40d103043d00c0140905008100c41441e422007100c004414071200c1030084d00c025030726501070034070320700600b0251110800340c00381c107000440c80351050301ca401d542803144040328a072126070032441202d005203040480906858020446654105 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 988495458 1250 988494208 988494211
    0xa0b09130503190f0f0e1f0504030204113105090a0b0409111518040c020f24060301151503150308041505030106020601030305180904150c0302040602190218 69
    0xa07201c105082c180c140c0054440031700e6a0084081104030840e540d081d40d01d50500d101c5400d001242991400c1c2c014104862521841c0c01c080c0d002814058440002440507006085004030841549900c0f280c44400d001888180710603942102c010120912052412450f07494000000c0780001803031040c940c0200e4180e40c0f070810165202401c403160141642860030b03010440d540045581407400c4129030743c20340240b030050040c03030007141d48000200e003443c002c00524032003010781d00440e85490025180e150041d11407c000180074205000801c40b141814011701c030400e040011050202400c14940d81800c0b00c0f01500c0d0070406485403049840406042c1ca01406180650200c596440c05c00700e01e00f20a10800c144c50b810020100f00400110f075000c2007007819640e261074003d540303e07088044061202840c0000503031140c140400e110030403501d400f0200540140c1c680a1005c1e42c01100e05400706d0045100d0440075800c080344820305c074a038244003803021030f1001f0003540400030b5144548022450 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 988496708 1250 988495458 988495507
    0x91413050f0603010608010b03030301170304050a080c100c0b133e06031012050106181a0603130201030b04020705010923060118020307020708030f04030b0a0b09130503 74
    0x7080d2080c000c40d82400c0c05020064400280240320a503100390100342d517031105114004c034103c40007a603442e480704240115002800300800303003540d590f01d6288403601c9a03240d4000d0b61080f60441e023825040307405000301040d026041449240b1543c1c403040d00d2559621542801c0b5502e260902080144548100580200c4011071101074014490b0380b5214005c014040200d6103c1d00d003d00802041e503178400d100c101603504100c884640000301d0700d0014054401c4e504000c0c18032580598203c0b91550552003c2c13035000a0a50a000c090b01120034040300c2c2c401035600036005c0807031701c0800f0090350094004400f83c4a0203407005240403619215142141c665030401c0700c01408070700310101b00b16141140075610107003c00190100d075161685003c02d4503812841c00645a0300440002d942900030b00600c0c00429001094a956101e0445019020b034481d000880c0d0f03030410318020400d64005031144d545021405070400c07410f03440d0000e4004410030100011074480c402041f001480ca0011a03444603881d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 988497958 1250 988496708 988496731
    0x90307081605090a020f040b0d18030806031020160507260c030a03080c090909030c070911070311070b040f0f08010504110915030724020d09141305 65
    0x2410041000503c0d200a8841400c160050001d20604035104080301c08485440d1801541c031450107015001900c94449940713140f214010009060503040045240f0a82d4201c0544d000e911102c0d211104440c034040b10811103d0314000441c1d862117424000b400015103000f8100421300450b82e80b07138a03120b46900240070b40300d6072900e00c0d84056161403c10113800c1d40740001e4054a81e03604080b07651805442c43c060204071481011034080c1074001d0449090b48000b400c1130004d490310340295903903a480b644203032240b41304164000034060418890011003000131a1554a000100d481c116032107180407036400d8450041e10800a0b40ca2a2100284010a0720040c2620075510340050020300e42c200758089001130341440100000180200107200c074510048035400000e0310f50750b01121031045102c20a9401d80320b5003001061000149110380340c8024920030600d074029401c8812600c0b07010081c01500454a0800180003180980b00c0704129000013810b98800b4015607500d40c0c09031202500e041088070f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 988499208 1250 988497958 988498003
    0x5060706150b0c0d180b1204021c02330d0f143603040e040c0f210501020f1b1b0109210f0308070f080c0a0509030708 52
    0xc00545071440018103401c2c02003030400a02c20402a124882019224108081e6102c040044c03880701607400701a24286100c0c5403188020314201003a1a003d8070103a10400d1000624003001072480404100e1a5000d801b24600e03068114600c88400c0800f001012020754000307580c48094032404c0940304820840c4070200e81c1111100b03181c401c54900c0002e450100007090100040c2d100b42d80d00d040e0071040c214001c0f8902016074440c03150300c40740d06076608010380000100000c01d14051091907000344d0003128211400d0f03684030041410000783d0f01c1517007203080301d000c15052881001c280381d43c1400e01600000d072400321104c00501ca9940300c007660340c00b45600c000040c10702240c00c02011403607a00030410304142c031a00c1c000180225460380b01701d401e000d0041d64801070703640030103040704000c07948041100e007030310003615026090040031110003000030f040714080000c45d03100e001307410700071108001c00600c0d03e008072030102ca850b4003803a030f12601031080100000e0040420045c1502c0c400804a096048 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 988500458 1250 988499208 988499231
    0x1b05010c080f010b0a1403040f0203121e0a09050904110904150507020705011b0204020d0f06240806060a0e10020708010f0605130b01200c0f330405060706 68
    0x40322041e0482c1d001c1c01400c5c0003507a842c0c0d800480e01e0440c3e401700d440141d165612468007120520381030318002d403d80950711000c4c2c0310b8900c910203400800d1050165401c40c0b044100f07205568000d481f00035001a09083c0108201e003008516950001e0180020b50820307405940811440401540e04a804002c412a03504140005210b180d8001d01e040c40503214242c0341400090044201440c1c01c5001c044003810340d401c542e520f80c100e800c0b03040c0085040c4036001c2c884500c00010b22482c401ca0707400d01a00e0303a5103d1648000300c00300300400c2e0903032a54101c0340c81c0c2c1c1c000d00089400520556040c812002d50740c5007159031b9940f0820803d42c141d0300521100d4200740749035081d20076011035030140c1400c010b030901c03481e40c44400076000b250407001c3c0041c8803900b0100480c0d00354003c02c0000010030a40c1726010171008082003002c01540b00352190b000d0b00d0140d40c284100c00d0440c40019000e0561070341100004501c0300c285104062182c00001d0030f180c2c03208002240c580c0f0001007121000d949401d507843c0b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 988501708 1250 988500458 988500481
    0x40303120e0f0601030210090e010f1505040605030106032304050d0201150e010b0d200a080105091312050c1509060f250201090c080c0415050f011b05010c08 69
    0x301c84001c00240010080c580840303a43d8842c180070080c440c8040010320400184145c803a20000e1011501801c03007940d40781c81b00240c1c0c44560090044095a854542801ca4052421101154615a08c1e24034507840c10700120000c007110b140c8100e0507049017003087e080300704011040e40079500403006040444540c11019084440c10840c51076503d00f5820200100310404410382c0c1110f0240050395070701c8060b0100c40c0000c107500c0e02681c10f00080d100d00e80c03901da0070090181110b02241c0d2188030b000d0f43c80c3c0e0200a00554126400f030007105920194030b000840a40103080c18082904006040c04042d218042c20500e808680c2d28401d00808100320808208101c000e8101c10212403114050403c1d40e0b6800455150441d13000c0d131600700020a081c003038401d62140d60340b240c00c002c003018801d45800d001070f1900601400c06114600301105140010303401108042198401011081c903600342d003005403080e440300c405c01420010000c43c1c00000c90000e02420b405001a584e480c262791504c03044050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 988502958 1250 988501708 988501721
    0x20d0608011104051c120c060f0b130207020409050712061802030606060c070b0304030801181a19090207050109120e0d032f06010812070b0c070f0804030312 69
    0x1a00e60381007004018103461144101ca060316001d40e8044200e01024000c04c0c140f24070103400802417103003041000c440300c0d440b4040070505849900c003404a08403221010041d2101d00e1001a400030314505800d0a04006500610782103201a2000c01e25004540707409040481680c0b002e543d0302c02c215a280c1c10002d42e0710071040d1a0000000c0c0800c0c2e1a401d80109554950050090340100300004d410350a850082212074018071300080465600c1c58140380c0103201400a1050a588403684084800454607602030169a100010075030314501c641c000400000008412103410011450f510100340c007030307860005080c414020000401c030321581d85814078074044d8444140042041103561815555103800c00c2c03110300c5400d49022241d00038080d0404c1d42d514400c500c1c0c6412261011070354030f1184004501681241d5500d400c0c1d40340d0302007401405c000d82c411f440c8010000070b0020300142095070717004050b007106805202a0000031003541d8502403158440e4100b41c0215018141c0c2046c1e0440d50702802 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 988504208 1250 988502958 988502969
    0x60105030f060408030c070c080109030527130507030f11180306010b0306130b06070c0501020c120a06020a0201021309020301030b070e0d110609310e031206150706020d06 75
    0x10410b0b440c05031500515400b016049602212000078880b0030720841100301070160580e0002044280c01925000e071643d4881040100141ca0760303640007101030080314043e0389030304010b0039424003e0380c1410f031800280001801e82003030660300c6c0e4080b0250703038080c0301c0c004a000a0306d990030b81d1640061701c82400c4164059019100743d00c00c5005000d43d142800a907504800103032281031251400c03070208000b0f042d00414080e04540b020507154107100150b403111086940a07002d4a81c006010818800302e80c134002000011640000b020300000b800075401082e508034644001400c1882d511340f05000221694000640c8540100041c8180180c1c092031a0b003041f083d05141d01c07000448c4020410a800c035000140079242c0f104603041540c0c0301d010440b201c072203000b0040c0c07030b140c0b205200c05e01c21040d9404406828420347c41082da42c1c0b00440c4502e00f01141640000c604091820742d10b00352400c4004c1540ba000120303000f0005e1603c0b28100940603540c443c1402582711642c1d035040c1011a02990b000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 988505458 1250 988504208 988504213
    0x70806070912030509060d0902120105160e0f09040b04050606040225020d060f0f1109061e0705011103010510031512140d1e0c030906050a020109050f060105030f 71
    0xa021085810039611000c440b90512051040c5825090940300b0340285100941c00050010744c0e04c06841580e40003c000714401c48505421004c648440e900700e440845400c142d82ca12610946085400b42e0110300050b94010030404c42000c0c5840890041d010076603089070b908603428244030400406202c2e45601550075a0114140481c0214185401c810001406014180d141c4000c01b903440c2c0e8002d4141315900300c40e0501034403480c02c0c0c9040081005010500391103207032902d0070601601080c200d40341c000303009060700d0421107100c0003030060650059a0940a003010000040016402c1c025403c00c0d040105030161258076103403d101c21406065021000c02d0310f41459015041c41100c22201514411400800c0b142c0146c980416004210b4205a045204004540303c3d42070380b00464152858401064160807070390a4000e840c075152805000f030200b002404140b01862040020b00100000c0b44004668060b9944501d81081c20301d02c2d04003602c1c1c0000b0014451350030208800c00d0501da00720300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 988506708 1250 988505458 988505461
    0x121e050f0915040609080903010507091e140f0109090c02010b120c0d060216051009020102010b1f08060d060911120708030d11040f08030306010806061204030806130c0809070806 78
    0x402c440d000010402000345560300404010700420340c01340c0d10000c801500070402414240d10251005110744241c0c2584051290360304141485241ca000840d8103803200b0105407802e8004201940f003014481c02d04024642400040c00c2059016070b55a101141e000001e004103d8820302101c4e80c0715000d840500e0740300c40300358006a10b40450b003403101500300d140140c0310380340b0030301c15908229a0140038209100342e00c00310f003074898242d00c25283c080c400d800030490380240c0402d0011481165034066004c1804014101659003e5101d03141c0c420401041850348403402d640e40b000702c842e00241598003070ba00c07050454540c10700345864001420007000900d1014541048076641e4030400b484415010b40318003c042030a4011b1042d1400b0700000643c00001e0b42d2100c044a540345c004551850015040743c000c14014100744c011203000ca680201c40c1e0445640f82d4074250380d2448083d003126000000403128848040c05840f40c1e814580305562000f040e802c02c40030f6075240ca040c43d040304049402840 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 988507958 1250 988506708 988506733
    0x170a0803250806010e040911121c0c081210120b0417180d1401050f24180712050112021206070c030c080708161a0c0406121e050f09 58
    0x45202417001412940803c3c00100e61070b00c52a1104a5030405070881110121441d0040002c5483c40480d07080d0394060248090440c0121404640f0082c0504501002c00200b66402d251030703502540040c0c503000c44541c01d40d640c0101042070210040a0702d00072440b009010400030301075600441001e180c0095410801c10001181c4040303107481315107206000c01000e4504122005400001400110b0003c02403490810f55400b0700c04012600c5c40c40501200303c0c2d048405080745007242003950068407400b0806018040700e91890340c054801d20a20204424072003c8003140e004481c064018402d58a8200d0300c13a20510805a00e01680c400305604050704000403598000b1031456050380502e00005078040c00e040010f002d00c980003000d49412030014144500f4510403080d04482c030322410007542d0903840c1e0120350302e0000e8282c600300300c4020200020860148511100f014000c20038034001031510001042c202e40201d2401d5080305141ca500411041c01606190705901c2411140136088000081d07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 988509208 1250 988507958 988507967
    0x40b0f01081305120a02030304021507030923030109060605030d03020f0904090807060f090b09011a1509090112020a150e0103050a14040b01150f020601170a080325080601 75
    0x908904010b0900d854007002e00a04000c542d019508003e0199039132074180f0380081d1a17500c2180d0aa0242940707941514078001004122021950581d039104060307401d0042c00440c070865141c08841188110300d03561226a000e01c2101d107824420302c400504a464681414200800e007501c3d51b003410320620400410f0b26014080fa0441c0c0d008450000301018249401c420724050500060549843c00c080c0301c800c42c40c680e0146c0c600c00d00032410a58150f032001c28043c262a111340c078005030105e402d000e40ca03c0d82048244002113484061078242450030300d00108242400c00d1f84070035001c810703c4424106500340307000440c0c0a0009441d036030303800615954000d040c1a4080705514101581c450005882d40401d41c441070340e1001020312204d030b50030903090280c0407001c01c0c0100352201552000d600d0106008120b01155a2150f40281405070710746110010380c01c1c07900c2d00c01402030051541010000b100b0300000c61140240713400c10040440700c0780c880441140d18218400a104481003404550b0380c02 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 988510458 1250 988509208 988509211
    0x1807080c0d0602120c0a09050907051204031101020f030a050601260a1116020306150a0e0901022101150507030c0209060406030203030d091b0510110c030d0c02040b0f0108 75
    0x5884294000c041450020000e00c1482000b40c11312681d0420f014000c0c2c020740003000004007613601d825105860b0000c0051056042c0c6200010903010005a4006c84c0d41003640c030b6105001e820003850728042040c2d11800d990100322101029a00081040400e441c68403e2640040007880c040118100e4032004181181c44241c2161910300007200150601c400da030007400b00090880d500303a4070b801441040d002540d4038030004034800e00860b03000462020404040c480d04040040140003c649807400c00c100108026206000759502007050b0b1640384180c604100e080c0320300c040120030942c035208a000c13607100c0017511101080410046000400d500c100280c00503501102c000c2d980d516000f002400400542d40000d4160001048481a0030481ea1024560a008443d690540c5155012000c41140107025003940310071208840c23100981720700c0c545450410860106e848140e00343e400a0700d0035128412003400605002c1d240c0c002c5003818040c449003040c003924462400e103e4000043c0030102c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 988511708 1250 988510458 988510483
    0x1050301031b050d08040801140f070e04231012031403071704230f12072d2a06050a03020403021c062009060d11030906180708 56
    0x41c0c0c54680806038140b40110001c05004010079805035845c41e02c00001c1e00715202d61002c951034000ba400e040c000b0042181c2c480d41c01d01444002e965201c003415155001046030302c0c1c1d0015540c07040402d48602c2c3d102403a280902c84040b00c2101d15280541000c51b0b4030305e4001070001c0382c540d41400006900322140c6039070704200c4410961242d4861030115100c401401d14154440361040601040c403140c800b19071250341c0c11911240c0c141c440d070b41c14680d07600c00c0317100c210340740d6402400d1a1551244180290100b40c1c490814100442c004094507109907981500c170705010303441c4540072000c01817100c810102a60b440c0c1c01d400310304203808109002c484818880e000c144030000424a2403544603a0403036001d5079000b0500c00c01610407100400a0400225086070700901d0006129004144030010000401e002d00300b05150060300814002c00c2d8000c54211a022a141d24014002c95014005141704403107401c010611460070901c1d034980b50385404440c10054201d08401d01c0301d0100420b01c4640f004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 988512958 1250 988511708 988511723
    0x903060506010e09071e020703030206040f03031d010f150e070e060c0d081b0f0d1e05070c0203060a0c050f03100905010807030c09140103020f01030e0d05091207050105030103 77
    0x568000069450f0b00e07103a0350455020307008204100030035800114800c000c0c0703104202d4403a000904d14050b40d0728040b41c000903003d071780104e0001d0005200880082c0c8198428130b008642c290b80d900741c520540e410940090550703512810724070310380c0c030319441042c0440b010900e1b0315600c240f070080c8039412444060400c4041203101200c4000315143c140480f954020b01004590001070301c480000d211010a03142d499415940e441c060300b0100f10581510b07912403d0780b00b16890b02c60a410740070010700015912050745100e500b01e01043c0035103413041921510580c4c841d243ca040542c8105400c103c402800d00800e0380c03030980c1c20480560310400707881c040f4051215a80d90ba8907941d010071029007060b030100c4a1541040004940b018010410070101da02c6212200f840b00e03141d07981c00341036507150800113141112400040025140c2040c546500d00b0044c1000908901e40d8140f55040c0180e4110b6007012410005140d807103410700440790b4200181e000e0140410754209000200325200611021b030469 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 988514208 1250 988512958 988512961
    0x40312050418140f0a0b1905011701031106070f06230a0903020c150c010c0e0901060302160807110a140a06090b0307030228020706030b0607030c1b0b07061d0a0309030605 75
    0x31401307522000070a030004061f50700c07a201411100c0b49080103402160300003100c50306050482841290001d060380d42c051290108030200c0c1e014000b450f040382c5415a00001b0305000ba10204003a0311891881c10705105c00e2000d4420316a4560940c0e40e805054204142d02d8074a020000c280e01140c112882c09040303954640f08807120140038528010404925404c1d40703011070804400342c0000d4140c0c2540410340341c542640e0380e2640d040d4203d02840042c044017003c15619500000c6904008102d10b034441c8003070105a16640020030144411500224107a403241c94090440d464150958001812a403904003115400d080c1281d5490002910000a0540200700c0190401c1c60380159040f49640c4040b0b04126044004003d5489007144039060100746080e003203010a05048048034100c80d0182c42c0c41099022a03942c030700c0d0301139445000c1e200d0031000103c04506041c524004040b464022440840d07001390091600d405010101d280800344d520100d001c40c0002d4001d15403004491304480c0000342c1d07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 988515458 1250 988514208 988514221
    0x40b060103090c08030909100e0c030c040e09010e1e0316111002060f01093b010f0b0310140406020a120507020307032003120a02040312050418140f 65
    0x1612120500904403240e0300d43c0451281d0b00000907005a040465000c0040c2d12a51403200c00444940940c0380a44564400160001074100044d604040e110800e00e00d055942e83c42d0030f0325084256200c0c02907075190000e0703805203102000003610074003d028a81c6011a100e1420558a20550030380f81020300c030950000042c003014403031041202002820280c030082000340d00940328182228410101d90074080040381c003d103144250340300b103032184500501c250180b00304000c0350310388d01407042c0c1c540e00c441401d10350004c0c0a0050003001e0202030310101c3c2e44802403040600300a8640c003040d081c0e601e050400c0d00c49500c8041c4807900a508444016960035035600e00f215003222380301d403c03404942000c0074002c040b07900100400c00b0500954900d041e17060307401041e40c48040300c28803203e034503031060041e2040c5000c0074040c65049001803034014070302a62039a80700c08010b044107c120200b140420200600c050500391000002601e42003084400811003044585103406040000400d0016001032032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 988516708 1250 988515458 988515461
    0x15130906020f0d061a0409021b01060b0c061e01030201270e1f060e0f030a0c03030f080c0a1209051501091b0309050304060c17040b0a081806040b060103 67
    0x1691a00428155590b4084080c01c90155012a541d505824a080c000280701304c1c1a0300c80c0c94100004040c260310b001d14000210300030b508050b550000d0714407400c2100f880300c0d80900c50030008108003103050340c9845400c401a030404000a00803034042260342c00001104102803042810b507030342401c001845080301540080301d41c507810041d02711183c403007001064030302000301c005203d10020301c0c640c2901400d41c001405184910b2250750007140d0300501c003000c245048810a80c42c010050b0403505500c0d2280c4551001c51915070080c2d000c14420860034800c0785d44820103036405030046484c20f14041c1c00d403400030000900b03522602030440d55100008100541800100503500000c40b6012407940c40d030015000400c0c0811001c032030100241c0011a0041c0203000c1c80000c20f130840080c44c10305140003800e8808144010007201e00b11410010400300884440281c0040c08401d40c0994480380e07000c5002d09a050013800b98401c50565200c01c031800000024683c0e07000d0340c0884500100e49507400141c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 988517958 1250 988516708 988516721
    0x91c050f1509071e0b03010e0402151e09060d020d02030f07090e070c06020c06160e190e0603250302090c03010320010201020d0606031a040e1c05190e0a0e1513 70
    0x1701440008000110b00442c1e415450046000b00c640d00c00102038004410001c5c440d540a001501da8141c51620500680c0030240c1140d11001d4082c5282c00b05248024080740d00200240c21429404004c1c002c80443c07103860141d0020342420000046800c000000324402c90003041036040080c80c0c05100200710054042c0d0300400c42c080c0481e04c0c14200804440080052200d25000141c011588000a4070f042c0d803181817900c904142e040c4009040204c4081514401805d4980610a6491a62000b855000604448240c06070b03200c1c41c0a00350310400019240280c071030300114030b0a00052010860003042d140d140101d51070340940b60f070701c5140142d019000d4a4013100c0c800d441c0c018002079094054204c04540243e8940003560109a0002c000841e850200c2d82d02250f0b000c81024600b41d0701031940b240c0c142901c2e0800c1414a110b900114a200d640c125815001401014603840301d818412034003005001c45442c0c8440d5880d09003120620807041d0654a4403501d101100303d051144143c1c03020703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 988519208 1250 988517958 988517969
    0x30606070c060e120714190807030305182e020c120106030b0606030907061209151b0f050a0c0f050a06020c160b0d02091c050f1509071e 60
    0x807628241da501024240e901d1000185000e20b0303401090864120300460860705548419900765541c0b00c4490611401d0350700051164480c1075128004906036508200310740040d842543c6503655110807a5252081c03540c030030312041c012804010802807a280c40d070654540b4103080714001c0e0b070f4414442c0d42245040d54000003160015002c0000180c0410190080d4050320b001d41a040c190741c0300d80b810310003584400c480b50159600704010030302c1180d02c5000c00b0035050312078100204c0c914174640c40780945548a180c2c00c04145d65503840501e1999042c03c084241d0b100d5605090304840401c40700500b90340306806080c810412800b060104110034004070040068212044980d05845860840e000b0f600410341c10800784107584010300d1541c45000b10b0030a90746d01985641c1821900130354000039400845c4035030752000c1c0c00c1d245400110781081c4003804081c081c0000b812990484140907061421076600209205103803010888242000030b01042269019200700400340000f00303c802c2c0e040e1191b00700b03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 988520458 1250 988519208 988519223
    0xf140307170a0b190c02060411040e1219080604020a120209130e01020901020601210605060d080a020a0c0f0509010e09031b010e1e0607031a150301090e2103060607 72
    0x511003200e1451301d0003500142c05210410201000032020b80c0d85600840d0003c0040600e003480034010b0070031b50070569500c40c2500403600035503e10344103940c0fa5040741c40e10b8004544005000e0303000552044410307070032034000c2c0d801314a0000807910050a41d41c94440503168240c00142d00c4001d130f10703400303034560b03503402d00c10b0b000c019a10712021194040d40c80340d0034450041c0305071400403c85848070039490304800d4000d20465001c070481e56655014000050907180d100c1c02e9010f0140100351804c0092180341c045074080c205005440c900b00f03803116142d40103e42c00c8954070000f0300032902d0b024449410749102908840c50b03540c3d1150ba1368614401d00d01c40c1e6146450080c0905901a015048000e80c0203245003035078080c030361104d48030981c940070504e81c42041e8050004111450b001e54403124141195118494120ac00340012510841c804081c06241c3c0e0340010040180c03c0e440e2260081c0012804090079000d80e90712080400300c020024a2428041d000000c940981e450b28115210254000c66 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 988521708 1250 988520458 988520461
    0x503030d050a060905011d1b19090f0810050408040f030c060806040b01052d0a120509010b060a0f0e150c0f0f1b030a1b0f140307170a0b 60
    0x9900c40a01400d07244840c0d080e007480d4010a4000d0f0074041c0c14162401002c0d40c40307414550060203500990083c040303010b850441003520b40055403110042c00b1080070722011240c0c2d1452070340024907a61780d9a00000c0721107600b0700144454034000c00d469141c40c08070710300441d82e0340f214207090065200b160301041c80034102c04800010003a14101c0c8004450050300c450340d1603036910301448152080c4180c202c4c0010001c00040c1140405200c0412020a1a0303900c00000e40c0c0c2e040c0e483c02c1c150720030030104020400007444144141124080d1680c403900d914004e01c410301c5070300c000c95094000c5074080780038802e0000e1a00e14492217045102c280920007840c92007074010a405200c507076070055001c0e812a001c1c000091040303050002d030140080041e0002006000d40e1017036041c80c0350300314150030b66160140307d490101141a020051074403012029441c2d10092401c108202c0c2d4048070391140807020f01e0340c524036440b941d0106801d411118240388148940c1005030350305040008504009110180000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 988522958 1250 988521708 988521727
    0x408091509040c0c0b0702030403020105091509041409010e0313031119030c03200307030b0c090301060e100614160c0b18130b15251104050c090d0f0c050303 69
    0x30124805240102512104c1b40c440f694120f890344550b00020b0b0110302d0401030701501e07040c42c00c40007121282811b000d41c1030828080005080d100300107900d02c5c03848840b01c24480013038003e00c01d15174020001c4006510307141b07810701412000c0d425440083c0030801080c102e5405a01c5801251480072800110081080d450346003030151118070b4001514242e440390500680d02d42d0000c0c8070000c01c540280100110352465450008200d0024641e140600090221101d41e031424002c11000e440314080d400344c5803415800709003100c007041d40000c0800c094513420489035041ea0007114202c60550f03028200800c06c50820035a08886503000d50b090182c0000cbc12003d00c0702c1d5504c0d56500210440c2e441d041500078414440a840b48100300300d0388110120103225607020071a00510745a800c0703400c000715410011480031090440b03d4405e462021609802014501c2c041c82555440304460441c2c41c1045d145d00003040d423002d0303001c1009000094400c802418000710604000080070010300702d030b5648032240b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 988524208 1250 988522958 988522967
    0xf031b05030703020642131d01150909050a0206030f0a0b1f0810170f0f03071e0218070906020c040606081b040306060902071103060408091509040c 65
    0x41000b40c005000d01c0d03021a0003650f206145040d105404405220041843e0500244920700b0205005450030606082d40017620340c441e1f44108072004910000304905011140ca180da00c161810080c0e991500b940b480c088200021400c0a503521000d000402d100c151819134a42422100081c8d8411404030821003051030b582105840b86e4034509003030280d07002001c00e226100000c2a45501181403031160394281e20710900600b9404280c203026150110360300e007251414404103c1809299030030144e00055400010006031a000055000840c544001500d50605101070b1109003902c84a44469103003e641c3c1e10100344414034251202e411442c2401c107030107060580944198400750007200301e1080103203454410300003124581d40f900f0b48155035072481c00390050755030083c0e0703c03107c94244804000b04940e40b0038030001e004010320040c0d0724400790a0030078a203144040c40520a42c01041000002000c41d825140c0b2540160781103c162800216006802d02812030700785c1d041461310143c03c1030035501c07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 988525458 1250 988524208 988524217
    0xe101101231e0412170c07051e03041e0504090503131a0f0a120606020c01090b030f1302011b06021e031933030b010f0b27041d10020909040f031b0503 66
    0x180220348584449c08074006034000041c071a14040d8006000030025002d43e140312102444005101d141b5240d11200098100d56841805130382c150b0012070000c41105401891030045c04402c2c1210325010f80360614400c1034401d030440d00c40701c4c0c440030400361903e074010880440c09400381181401a1504c03003170020b695850503c1c007a800281445000a603048080342107a008501c540300306405c1b0360321241e050b4044000c45004078100094803110060070281c401c0080300d924401c1c400581d0750018032a61461101244507203000440b02082031000300000034141c03461588403064003048880903441844a0341d5a643e440b000d51028900c5030301050070044101d00240d92103100880c01a0340c032072140a0001c0040d0007009800481001100302e0614a004d401c40f0003207155500d40d400e5109400418282d070f020242c04280c400c1f5034040039411140500c102c6010850004085050018440026580d03031405400507290385240c0e900c56060500c6045400103806620302d0403011381f5031500d030541d500c5d0f01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 988526708 1250 988525458 988525463
    0x9231501030f060302060711030c15040302040e03070b01060306090c05040b070b10090204060207090e010204050d1e060f0b0f09060a0e060613060518040504030e101101231e0412170c07 81
    0x11305525810394030b4180c070b00c14040d2f81c00503030550500d030035030342404000c1c08140e91160140c40140310340000646403004a501a080340c4e5004600b880c507118220741503843d541304090501c1014001408601405d8003540d007c0c54001200c1c5000e0740f10700410126031051500074640d00e0303000050100b00325400003045400c5607182c0300b04200c540a040c7c00c490807400f840c0181503004603000ea0381d002040201d070091695440301621100d15030340c15511315080b90f00003040d04141a4848140342d0309451b2503034003d811850241c4202049150a20000720f04990a000340ca6440c0302c1c20700842c141c0e840d03210640c0d103200d01001c3e00d16980e0ba29907001814681141d800c1703200500760030b0000081030419015180c041d030751540b00e0529440c410342c200681c0090644140d8204200281500020b007424080d498480004c110500c004805008004440072002080d6403140014026401c000895003903d00d544103030001403241850268a800b03e070800030640d00504061420024020094610340041583c2807 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 988527958 1250 988526708 988526713
    0x3090d1e23100b0a050904061401031101110d0906050a050909010e040b0903090907051b1f2d0b06120a02030a060518040816020a09231501030f06030206071103 70
    0x10000c480c1c40301666040ba0a8903003141c040042003002c0e041c1ba00b003080e0420700c18200481e07003d008054814002c2c100368026680b011003102011901d503000b0452a10909054000c2c19010030700c490054914041480341c007040080024000110b94402c230144c0e0001040200032038030300c4d65600851100460305a900740c0b0b2161410005c503102100000840c2c01c66000130301014815611480183c9030754001e041c110703543c0d00040c1203c0d2113012042c851624030900805c48828070740c1d441c07100c12045070348080c000108014400c04040743d07040400c0b50000001039070a00414030b0300400021030300034020044080d190010480501010903031036005035216000c040400c01103540c0d144100a4880d420f81400d00c120b488440c0030401113440200200032000c03e9146440400960344e0104030812495840300c5107555880001b40100030400e034034400d1161a02d041c051590a05540c40c560740915400071b42d041c940d4403052650507518a0300034000840c0c006040075190300c40342c20081401c0d110028818402d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 988529208 1250 988527958 988527973
    0x60d020309121312140a050a110303120103080901050f0a081b1c11160b061003060302010203032809080a0f031e090f1b060801050303090d1e23 63
    0xc01456041e01c41210294400101c028907080142600c0d48013400180c901c5041001c2080d00c400e010050389031139038400c40040c603440c8c1181c00c2644460802c01040f43c803a8004105100085000b00e402a040d0303504003d6a666030103001d00140e640380b044000c59598030002095a81c1102d800184141c802c5218040d0b5100c0c4403800006186070384901c424810b1000603d070075100c201d07003139a0f0000d5441101c010743d01d45040c5003151030580400b620f07141207420302d0020f402c2005e9810210030800c0b0001e41d0381000c0c0f0101d070442d40041d48078080200342000d07201c04103030740d2290800780b0304000d121188005020884c00546081010301540002030b00000b26000c03000082016120740309882c04294034000520b070440c507001030039000c0d01c801001640c01c0a090501c00002c130300380c0304010400d20503c0d10030401c0c0f14a03050300540510b40513440ba41c0701790030501084907140c0b00d02e04245100b07584204107407150721f1610703a14240c24208240141c2000d103914881031911900340c498038580350900007280c01d0b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 988530458 1250 988529208 988529233
    0xf030806090f01140f1f090914040210090320210d12140c0c0708070b0306040b0102010e0a240605030705150706180b0106110601061d060d020309 64
    0x40d6800342d440d60810024280104110414503240348090540141594440d241030000603402c1041148081c1c5403c0b210105502d0350340e04000c00701c00a10101400b446021050f00f022010110000c1c000ba004404031030403840254481d00314a401f0715800f09964020300d8002000b01c0700c480300c000e2040d0143d41202c90303c3c8550540f0724031506400c50702c28010207080c82c094500300c030b4070050704090300307021601c50129090403054280018880c1c40000003147c0c64401048001d45400d0035903001c540700317811001d014801000311404990b400201520080340c0e82c40740000407801010b80fa9030449150256000032410000e070708610a800c034040141140480c01103020030000c40c0c02c036120b11a4141e2202904010a00f13100fa900802c0603020000c0601700b40c041e44400c010350350b0300301c460502c0742c040e41c0c0c0880801640b8241180542064a070035410301160072181640d0700170600586c014860b9405141d203000c1103024554000c7c21010b07145a0b240c140d001d45c1c0c00065042642c20324901d000d07010072100c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 988531708 1250 988530458 988530469
    0xc080408010c08250f11031209070609030503070201030207230d0809011e0903140a0c03080c12150303040504020f0403061823070b1908070929070c030f030806 70
    0xc502200e280803281031400b400c0d80c200000d00810002e000d9007900c954606e0b442800548100e1250801e1503011703252090b6154107014141e00504248007182d40c0520124000100380c4450700c1e428200140d89901d10f0030040030403a582000075110641035100f002000b6808200412035001035102c001623600c804550500360342070101c0c440030300c0d075010b100900c4020b044d8008034210740c0a4100000249028040d41140398040a03240011640c205540802c140c0d00201039540001040c402b2810114901c406d201c0c111000741607161106110581b0340c0080c0c0d014402c840081000410455940800080d03440786a00070784820741e03015140903401040460004600d00e1416445804e1840040102e0103202d01030751000c2c02503d040c40b45200101d007441000005141041011080000d05a920440104510302c002d01020170016181803c010000320103c0144205801c0940350050410000318040e46014a8402400310764440307100005000e0030001d80e02d071240c044c1c0e8600e801a50b41c0300c14440c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 988532958 1250 988531708 988531741
    0x3090f04051e0c0c0105010b040f062c010e04051e13081218060a0f0b0103061406070609020414040201020601080c0607020d08090405090313080a11100c080408010c08 73
    0xc4022103105071203044088201041e4082042c00202c1c0c1044d40003a0900d003129001d0701310341540400041c041c0b00460560b690f04c00140303864a807050348404c4c092000c0c1c3c80101e0401061440c4001481d010344030b03030700440300d0000d140d40141c400c2226241c05000c0d100007042c001038002c07120080d68045011002c01591546442e0b400c420140e00e00f0012011100d914040205180800303448090721340b1803034505010007401181203400c0403e50344403541940d000c40f40b0b0842c02c98181450310000f0000301030b020f0010b18006030112121a11201a4100a000351100c0403009510a181c020303400c00620403d00c0c032a000d01e000ba13003221031680c0c903050b65590f94004054181e5104c40140301d408018904000f10b100e0a03442102440e003400c2424012800b680c8068a01420703036080031615428142e0542c0ca25030003004968000c2400034040d440d400c2143c3c28003d182409406660038a21049010714030540c5810b074400845e6940c3c07a6034030421402010140342000c00215184007245464402c03502e100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 988534208 1250 988532958 988532971
    0x80d0e0d0f030605121509100908120610090608090106270605010207030c0b07080405030a03030c0e0604030314090406030c0306020301030b0112231609140a090b240603070203090f0405 81
    0x401c117610300c50703200c00c46d0304000401d02011440340440ca20300b20f05090207620942440f07089801c1c2c980804054042800100400480c081d40e940032164031402e41c446844421912207081600d500e40380c2e05a041c0c09013426410003080c14082088261480640c035144d450384902d4100204046070320385c80121b071101d07010312002c2c2c6040c14800d000d00c203c0102c2c2c00101141886a00b09600c5d15a44001090034482c0000007074022941e07a080c0342030b41070380103030235481440d208448840c0b4250441d9005000040502c015580c6400702082c5000c283e241d95000c07030099500300c001810010f0740e9107032410196009000c102c8001c0420720000078070a4507014511610399200c40da001d000c9132a296030040d10b0901118100c400d22035400e400d154005902e41802c0506402c410204100001c00301031400a100900805030319403501c03c0380030128070249440c90b000704440001c0c04080c00a41017400400810a1016a01810000078800090380010080c58020b0096520003200010402041304a40084400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 988535458 1250 988534208 988534213
    0x3211722150608210d020d0606030504050609120d0e0a140d030e03040b0703111614090c09012705032b14030703110c120c06180a080d0e0d0f03060512 66
    0x7441c901c2104002400014500d03150041c01c054601f611041660500d07440480429a20820710003400020b0013082c1d40040c00300000c21145076000c824400c81c0c440e2100c0e08800d1642e5840018a40005200c1815195044818440c0303a078500605561a5582d03a4940741c0440c0c64100340d51b41050010040d0f0b011150710000180c208040e541302614800c4404059501ca401690381300a5208101c0b5020b04c00780c41c00a20f180d0300a40c480781400858540a0303e0a45884001e01c00040300341c4c0c0c4217440009582d0320541800d4030b00408000c005047c0100c0d040603916029505069800810070116101d002c1c070300d820403000c03444130802e00b81d422030494005010010410000180e11134000e0300701d1911041030300d11541ca0054003041050038480d058401082c000030000343c1c5420400304001c03194010400b10308603402601130580c0e155488901d040c004201384000310f94241090000d600203801590b4140036140d4118101c40020b04100e0014400004245400004613090034495401c1d186050000b00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 988536708 1250 988535458 988535503
    0x6060b03161b06110d110408070902090604050f1c0302030904051e24120d2007181e0c0908010606050d0e0a080c060103211722150608 59
    0x32000b01415a44210724050340b4108080c000b080034511a100c082646c082406444504004a460030300089501c018040e80c01030110400940d40e4a040328112041103442e4001d1401030300102d9036180c6580c000001e40c1a00c52032510500da000700060003400400c031403c00c1240e070713000170007003030f24500c100a403042101030301c00a19890004085d1740c1c0c4606612540480404480c00010118140c0c0000e00e03200d9003242d58003058260304000e854041c1d10300c501d2311075102e400300e0000f5555030780c0c01e00c0b8060480105c07031496070400381c040e0b02441c40d2680c0e40d44c602060100452600000d80f4401101b0300c002240c0c01c80018a911041c401c0c0750680d03501d80c0d42d59141112813000040030b043e40c104080c00a004643c180d0001030100c070000c0415400399405000d1940c51030500b0345940c0781a08018000100350300300300c038141c0e0748600a0070075000f941492103160b407108030420b0800c0220400d8042c00340503444514081c0101107a4802464600d501c1c1409001c4d02d40005e10740782c2800c000050381407404c1d0003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 988537958 1250 988536708 988536713
    0x611160c0506040b09210a150507020303011a2a0c010915171506190206011203080408070c0320030105150f13020f0a120c0c0b0604020f040306060b03161b 68
    0x41c41c1001c51109031b50001e0160280c100881c10607805020844150f5680f452203992041980217456000811340040c41c107541c5081e2110300d140c0400d984101d09040c1c00950100e1b152003618002d41c1324420081e15909008940c200783e42d880380c2e544203c60200d1041070001518842c0d402011440f11483d0351043d111015094008000c01d401030003016064000c09022001030b200da04c007401083c2510061040d110b4041d0102a041031010380043d420303a02d11440941c0801d0b00902d000707810942c4038040c142e90341114101031a4040a541005000030240000c1610f03148040b40c1d0707100d49080884c020022900c40c0c0107202c4009141d9044550000d90311208007003a86405009007c80080c07400c0090f01d001d51714016a0021740c41140100003141c031458210703e0892440c400d0700d0f0a82407905102c90482c10039120700e000e1100c02031007140302e55000101865901c00e03a40aa60045500c5007007400030340e0300d03040c2020b0b250700b04403002c0b142140d40b88143c0d80d0031b070f10600c5000d000107072649842d14540d2440c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 988539208 1250 988537958 988537969
    0x3030f11040e130206091009090207120f08040b04030e0d0c061211040302030d082508042f090c0d0e010f1401060f080c090d0b01060f17130611160c0506040b09 70
    0xe0031741c1d87c284500030000203040b411500042886c2841400312504118400310f028001205138525502041146030802000071705044143d42c0143c0c050a110040350070401c0002e803c50340007030000f40001210701001030095000076480c200341960402c20b05c0501c00c1c0490242d0309000354070019515500058440d1560b902652344190407021002041322030340000004012a4051081c20310b0010303000700200b00900c0b0b1072807400100c02007203e50010b018415503007a400307801c100c607407824440c42880c17021449054a40d0120b0b81918868607003484402c08c4100720328001c0c4810041140f07941c0c2401100b103c560290303002c083c10b9039400c3d01c807045c0600c041c1e5011114100010004201404200a000c54603034401261298a9100d24a42100c0c1e60600350b0040110b03410b07030807040a000200f07002c002c4014040d514964030090810f07021740d41c002d2301e080c03910290411403c610840c40c00003c880701d40c13038071026084003020b014619080c6015903070303000d1100ca0b104521401c049108140003c02c002e1814 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 988540458 1250 988539208 988539229
    0x305120a09090e01150b13140907030b01020f101a010504050102030406120b0405090d0f031a0d29071106010608270601090c02241303030f11040e13020609 68
    0x14000081018419142c03040c03144180d0024006c1c418017041c4100e030010031071282d00103441c0598080e1010051000450141000503103d40c040c5504c0f4044011310381d02c200548442541842c08640c61070383e20045a4008013030302d80d20640305001d00b01c001c94042d40100f00300c5044079010781c000d5251a14000b42100c200e10b0300240c03118415114800c4a07025501c0e40640e6014030003902c00ba01012000040c0604a00d088070002c50a01d801c1100b00240e098680403102402c0105072000e500605030781c50b001da14440085a00202d40b40c2c0c098511204900b4822400d00c140c0d5541c4808100b007082c2d92441c0e588050074407441c0e00150040c0c0019007880c40850b01d40129101103141c0704814240c0c0d0481c0360904009806c513842981d84c8440c0102c4842c1d0402c0402d00e0440c41440b0440c0d841481e040d0f80410300001014000841d22100443c402c2520a03840742407800200c1d1001c00403803100c1ca6aa41150307006101d5030a2010b2000c021030303882c10200d00b040042990083c010f0f0320b04034040003400000c151 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 988541708 1250 988540458 988540481
    0x702030c010204060e03010b0a05031e010209040f0501080d050403170a02030c01050a02090118050603011406041d06010f02031305011409040617010507212d060305120a0909 76
    0x28441040d40e51424000341018016907110010120100010306085404100c6100e20030b4514480400440c0c0300440c0510410700c18a44660001e05e1903c8020f0181c820150000c1e0442c0c5460358803a850b2032158050390507121400181e40c180c01002c3e0f0100c60f14015800003a0081c0152203100c44407200310300081c07825000b1030042c1c03070800c0c2e0740001c0c0d6030840d842100d8110780c140d0000b403c0f44a035030703000894056050200a80b07030900f034146404200700f40014080c1048040003402c43c0426070361070308241c400601030f854403c20180301c401c0c84044150f03170683e440c0740414140001c00d01d00c503001006440b60840380000c10000350385000011604030036171900c04036890404010125003602c950090002414044121002c3c5000070300f940c5007102d000400c0f10041080760a08844464001107044440c9084d140002c03035000020351002c07c0b0242d00c0c403981e44110100c0d84c40003190038981c0e04440101c030b00039010f0300ca1001400340044154401c6205850010b82c44050502c134004140e44109500103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 988542958 1250 988541708 988541713
    0x5090c03011e0e0711100c1d04020912010b04050f06031c18060503150609030a031409041815200c071703040f140604150c05031b01110307090e0702 65
    0x83e56031904141c5060107548500001e2500081c499912400b004215201c2e164500c08214450902da00280551006d0003e04001e04400c1d0140311b6641d0b40380c0603921340c074000030f02220084031240c5c2c15074020000c445a140c002c50500d0001031069032802c8010740b280704081c1c007406100e1008110b0301c1c03a9006140c0304205010720804008188400c4803a410003410341c0b41c131415500c0c145a4084041e03070703000c0c0000a2007440204207224642c0c030003056120f1401e90500700003c4030402020304079000e0151045440d00185404100840c3d40c0901c262601c3d00c0b802150154180c2030140d29107029560000c0c030240d040044540000303981c4807400001c00a00300078074140d03449a502e40342d5a440c010490b10380c06103654030100b000d01c4445c00002505c0d009021001c141d40e44968554041401800741c0d102e240700101f4488020903900d80940007200348154000b0070740c0c0c1d4802001070b0450b400100708000040715032900c40040958421070381164010b0180b601c03012802c51400490f030310400001083d850450 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 988544208 1250 988542958 988543019
    0x8220f02280603060f050a0605041a04120602090108100b04050d020117010f030209010902040f090c020102070525080a08030c0304020a030b010608040b13110603060105070c030803040c05090c0301 86
    0x1404400c400001402c40382d940810f901e0310300b2007110724070085c68010b00d10a0f04d41800400c22150071804440032148a4110048482d112604c0210140595444080191420100d010812490b40e00500d0b00035801d0700d40520b01d417038200707500e0944c0d61140294808000100024401803a20b0600540b81e1481490138207510b90380c13002c110035081e2007a480000780d1420550244218608041482c4c003601030144c0443c10306107803d6440d040003000c4e1013080c0c1d815607036110040074940300b134045400c803507040790858a900f078020681c03407660b4180e50800c0240d03d80d07004010424020204500c2909600140c80a0940d11608034040c0d082d48060001c0764031135100300b000400214000c0c0403074000e10840c1c60b5802d0074078142c10100c2c0304c0b01008141e000010301200226001030101007803980e0b003c0003502c0c425203c1c0e603480e0040e2918440e808014285603240c520000421604000440c8a280305400d00034003a43e8400038896110425a0303041900c902c103000501c040c0c50401c541c1c504076280c0c07102ca60b00b807 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 988545458 1250 988544208 988544269
    0x906120f030a4a041127010219111203160507291b190b011401170a1508010914010605010903082a0c01090807151b021008220f02 57
    0xa0750310003a04100d4001c0685001d2102145021901b04a41001c1c000340501c1e07112500c694105004248004040302c140154000c2580c42e05070031403052003011802c4a0399100c16010464010031120011913692040c070101150f02c0e05400201800c0301d464480c1c02c039410f40c140038070060300c1d000518810354041000c4122182040c080041c00c407081070046c4203c0100003c0c2c02c00d210180350580150030280e004242c444403c1e42e00c00c404408840d00660845034548902d03401c0700250429003e070038601d01400c1340116001d003045d03003c02c010600c6a60585040b800d85a251400d86030a0301c038030f030b02059a0501c2000407a401d04c00034501c000481901000c1d07186901450900c54a80c0819100c00d50b001050340302003960000415005041840d0007044c4071071528107008075012800d041c403810040d220300003000115150100742c410950003080380b030140281c454002c0c801441110103016051004542000d481604020341290540242d40c80312041c805d40c0a000d004840c3d900443c02e000717000c1040040c1c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 988546708 1250 988545458 988545491
    0x10e03041a091009090e0627070f0b04080f0606060717040e0c0d0b0301061503020703020a0206030a0e060709120f0f0b04080301091a0906120f030a4a04 67
    0x84042c1d1556800c103810000c00c0800c0790901046c00c80c0b254006024042d81e00741d145000359015203c0030b40d4510520344410124140302c415400080504590900890b4a01429018009842261044445000701000c0d9103a843d48252030190300100d0400040002c92014440c0034240c1c04000350180c6041d40c0c1c0c0c031020700c0341402181d1708410380c02c0100341015900741c14095008084803c800a00c845800c0540e4003082d0700364284840189540005c040c01098001d004042e9225001044581c0781d240146004000e401c0d58006540c29000d0703c1d0015090900644403031040d21038030040700061403031940d0741130040c00055100303a0f51030b11894094000180d0480c20584914403a401c3d080d1294908426482131350f0541b12810928008400c40707080380d4a440104507070050302100c0007011280a5408203040c9a046880549070b40000215070f410030742c0082090b03182284902c3c00300c6120007a09002c01038100c0844819040d04020003000a41c0c1070420100081143c005100090b00800d22080b0107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 988547958 1250 988546708 988546729
    0x23160503131506090b0904030f08190e0109030e0a0b1c060e15010906020118060203040305070210081f06020607120f091412191b06050103050105090f010e03041a09 72
    0x10b031081d840d20700501c0045054007408508100695007002c0707074109507802820350f00312804000c04000e00c0170005a140340d12040514683c444211342003201e1188146018060a100c0e0000e60200c0ca8000b003206071400c1180080c000c541c1a44501801c050807441d2220f03842004111300391450f41c45060126040c0c5890141600030050700388408103000d040c07000501003496981c001070640e45030070700820364006102112a03546500c0840160741c1c1c1d80b640f8050b90f0314020071038040e400c0b4000c9080350880e1600880442c2c00b030107110305410356885004481c42d90030305150103a503006801034400714030740c00e001d502d14102403405d10300085400c17038000302e2903812134050f590151040a08031303103240715030304091000c1c1002806c560500c0c2c1c0391507a1881051100c5400040314420403084900103260b074022148070b0001d5a134041818000c650b520705000c0d02802c1c041e60122070500030f65a581c120000148189548810480055070400b498010805401e00c81100142031940c410400300305a50395818242 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 988549208 1250 988547958 988547993
    0x702042408030307020d110f032d0a121a060f0a090f05031f02160f02011116090b060c071509090c1b14010608012316050313 55
    0x600d9128845515820186681e0090300260020818040c03096808240212140220304240c00080c0710b1030811454015114a00c1392580404580380220340503d400d41003c802e900e092002010000c101c407000c0da881181480d0300480c0c9440464061464290000c09090031a0682230b4010312010700810840d40c01011081e0070720800284082255812600c0c44005e01a640324020a80f400c00c004650345046500850f9200c0c5400d81c0e003480d6114041c1c0455213030030014202c1080e00d10700761400340d076403a0303055108070302040300c1c1c0a030310703881a07030008a94440b003000321441b441003032800b051880105228036001d41c000004100740e1440c01420400701004204140d481d040150b0f110788001d0403508c198002007a101e0802c6e030b00410281d03000076410198080d5050303422100806240071050001801000c038604c2d42012130000f0589010b40c002402980c181072440401c800d07a4100340d8603820101c46180081c03800000c4803450034030808c05943d00c0845055a0b114212542c1c96599140080c14400e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 988550458 1250 988549208 988549241
    0x4050f0d0f03150e06190801090c1715180f01020f07060621030305070306091a01081305060c0a21050118090b0a0515040218040e2a0303070204 63
    0x189441d440c0d0600c41c155100112400c034a1442e41081c01d04590140d000e08198411074000c401009041e0003000d400f00206100ca000701700d0f528071407400b030b1450021480345280741e80081064425280c5d010480b0126035048110b0602c040c1d0f10860a850b0840040103810800d203e072295002d03025030309200500e420481924215201c1076545030100070349940d50030480b08511003491040d1110014490401e0150781400c0110303141d5500101100101207651080a00c00d0410454120b4007400312184403290800380e1325100d0955a800c924803005168040042081c1e02003030003e079841d542c52001e84840060b40c9003044008800300c0c8291465415000f810116640d1400104002809c800010400004480084c4105c40c065120034002420041001140c2d90b120b900007aa00d815100c5001c61141008008640702d4468603c0c00300b050300c09298490040d45061241c1e042c201001504240e26004d800d115003110b283c44901c240b41040d01000150035210a100d01c0340181d4443c040c8204030f00e222402d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 988551708 1250 988550458 988550477
    0x1214010f060f050a050a06023a0305180c0f0f0d1a250e040b01090b03090312180a080a050408120d2a051c020a020c12030c06040b04050f0d 61
    0x3c003c0010f013030f50701c8a403240700c04100400c81030f80c012502884c2221f91100d0540d0f424081400010340e8400941401121407405021042e90754055200d10b0194484680e59001c424160700341d590341d00a0000c10542c0441fa0160034911807800c1c0050302c0c950030002e0300b40080180590baa10b51100d103c0c10109108115810801110b594010707408150803910328440c040303c004061028201308110f8543c0f900030f0362242400705082c1d000d41103800007860450300c525524500462490740360781000d441404501801d01c0880c030890b644401510300040c010028040200c503c0d51005042c0d0b03c01c09600080c044107200010303140105000f0f0b0807220f080c00c885141c0d2856005c1c00c200c01c5800075003040446500403a0806103401559404104010b203505001d80c1d641d9452000100c00002102400b8000e070000402024555020440d600742d8401a02e60202c8a9402c0c140c4644074041e5078124010340d03110100041c04583e001010981090055040d12580c16580c4856400d14a0701071284010035480380 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 988552958 1250 988551708 988551719
    0xb030a11031908070204050408120a0e15100b1605030c0601030320070e06010e040f0b03060f070f140d0207030305070929071109011e0b041214010f060f 67
    0x54200ca44510382d88100d80040240d9030002d150150a1000e4000d84d510b60016040251420850300b40c0c0d25614001031003480d1a41d903420251944024400c2d00380250081030426682078528203010f40390410f0300391085804c000444225070071400c10780c04199210b0056002041092004000301d02e00200604450f40c10760501905100050900c0401c4849211202d20071070008203090007610503444a0500e00d0f2943c0740100ca2000b8542c44056002c1d00e0080b981014181c26400350410b008258107603070f100c0d40c0f540c3c880c2583c02c404070740400118101940c041c2c111303486039201d142d4400c40c482c2d600b030400070b484224404980048a0407404a83c0c0c42003400f040c81d420008420042c40602440700c500115150300c882404001c00e9241114100030502104010b050f400703e150429002e08100015039603900381a00080f07a00072a04103001c5508004a04040490300702c0d4113840958200c1c05200d14580d80d0900f110401ea4844000e039581d4000344c00d1158468001e1200a02420551484160038030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 988554208 1250 988552958 988552963
    0x2090f04060923120c0d0807020c130506040b090702060a0b0109030c03050d140408071806090c1d031c050d091e03030e010203010302091f050402162303160302010b030a1103 76
    0x1401400704030140004000540d00048205034038035135103800e0b41c840e00d4120007688ac01e200e0440d10b80e07004450f010299202d450681c48984500400c1b1014000c0b511a4824095000019031f9608010b0304224006101e00e04160001501c50b2010714154001c5a40c80c0c84036001d220b040e800c101d43c15001201140880755000b100f560304003071030003030300742c41c081c0b908074059035800040c4100c01d41d50601205205c1c000c845070b4401801003410700b105120124140300010030000101d440c88001174030094031302c480380c1000107000b0300c48a508032100403070740c405c5602500d0b643c005c8a46072840035264250315001400180341c81c0c46c007020301c1c0640701002c90316140280503904519010501a84140010409a9202400d07a600180410210201c3e0306d15803850b10f80622a64100b6a007090000444100d0306590b1030003800e405000d401e070b2640701c4581c448202c500304c290038110001d55000f40308800d902505034503e03080040c42800005400003036000803a0900c1100c1400b035405c08481c1d41c00f0300803401d05 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 988555458 1250 988554208 988554223
    0x11030a0c05160509150d020303130302090f0f040209132f0d0b281e0b0d0203071a161202061602030a0c03091806080c0a0302090f04060923 61
    0x42d55148607502c0c3c03c01c0041152800000e00c00360385124500031200c2603881c0c001e2000782c1640c01600356603645107124459000c2c803003e448100e01810340e8000140d029502800c4080c0a5468079040c9056601c49400308011144050200030042d69100e000c40000b0701e0075407400003401c04501d115200601c1080012820041400c10b40340120f102884140020b01081d4509601441c064100c5105030358a09604424011001d60849120300c0c140710000b5054941050001154100c04240f144025001c240819000c103010300940541c0314100900649040701e4144282c0c046142d105818040002d806198940a80c8415907a070740d00000100d144c0c0f94184039003a40603400c890866651004503000a41e6807088111000800c0800c250000400d80700c1d200031001024070700e2044000714080008680185203e1190078941d100c2c1c83c6041e40c1d6802c1c02101c81d0300f103c3e001090010103503282c404c907040c3e40c40010800c40e50241e030380a1510000d4140e00b1600c0d9000e4011403607240c96684120914034001c0d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 988556708 1250 988555458 988555483
    0x170f0d0c0f0302070b0f100308030c04090501060509030c010e120d0e15030106080106050c122208061009050a15062001050c0a03091b080a021c02010c08030711030a0c05 74
    0x100b04d81c00c04070340310341c4d511500709180800100c0c035961084442260030b04079420080c00ba180c0001071005d003030301c1d0b03401800c199950040100416640c48100b03541c2d40c814410b0341500360304030000c1d5564640c01800e50703a040c0c100207081c01c4c1c0d10100ba1032166040000d00301501011540d5002c000109007042203500e4002c8565600841c82d44d418858080c04a1005214036010003100081e00c417041d510521049140440348420180c07035140240c0d021285110302501d00005c00340b03002001031034410001e19035000d0188410031205c900c0c1010b5204001d0300c0300400c2040310f00e807219100b001c081741d4001c00000810240d6910440c3d03c51800c5409403d011031200000e2980c14041481512a0b200c002c0300e40d040c5072401c00041d403072030301d1906850342039070b200c4030900307410140c130000a00b444042241d1401038403c82d051a42e1a00741d00000416100082003e40041c42d00a52140091000401540c002c03e540c100f4082c030403038074a002842c40c1d02140b044000100c1a0301400100803082080d0a1040d8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 988557958 1250 988556708 988556711
    0xc01020d061d04021c0605071e0c110f01031509020a1101050609161b03090611280507090903050403020f060c060c221e12030c170f0d0c0f03 62
    0x2081caa0142d0300e03070b110103007000e40300e0032000d6140011499010359460001c1e42c0100c05020b14036050034080e0406403543c002c514200c011050803000544207210611038154081e002c100391a0035007052040d207100e0903070300a060583d10601d0400841c05019420010941c644000da62103043c2d00c0020800451074804602d268100018012030f1f0b502c8807401d6611802c0388600780a0180d181c807088580c0f40c4120a800303106070340340c00c980007456400789806040e00c01e5515800d10b0401e46004260741c0c0c10b600551441c00800041808681d051810b18440b030240c0100111a02180c41d6280c1e2400c903624940100c0201e40c00040400441c100b00c0c84510004e242200c41a081c00422500c2c140c4805006090f282c2c620b0001030700310101660450394000f0480400c280c244041d80f83d901c581c02c1c42032410104009144500d400040c03045840040ea010720754940d940000e0f0600070303a80c20240350000050311180c3d140601600c4650b11004002d8030024504030380124040100e01d4001d800d001c10b0340961810903 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 988559208 1250 988557958 988557989
    0x3190e060d0f020309010623010f0c1e02030f03040f0b0915120a0c050703230c0a14100606090306020c1507031b0f0c080d02040305010c0f02250b030a0902060c01020d06 74
    0x140041035030001038070086c00c180e0310005011002f158000f140500003000c6800c107007251400c02100003446108640300b603003198035000410312000e50700c0c041e61060f90b5058014107000d12056a00300d0140a180d50043c0810585060308044d420386034001442c0841b40003800020401c003401ca034082c00024400c0350a2080c0b81461549004000340c45030003004000039070040003240c0e40400e9808540c0d11000c140c0a0f108060200e10704003080121409d8002e04070300c1100840540000f044c8070300c20032240750780c8075450040d00c0d568800000e504154483c00680c082c0030200913140f4040d0351a14420584c5680024400311540300d120498078020403554104815812108007807070f0410a00c0107e90303081203145032281c1502c0ca00001030b102d0750708024102e509000c02800b4540d0000c2c03c400341103500d9001c0c0c40c04482004d200302a16140c0341c02c1d54065020704c00c0100580c1801100a61b00064440350200c0c4520721500402c010341c3c0003a230020503681d80003801c821110118492040034104403c2c0348002c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 988560458 1250 988559208 988559249
    0x80711062b090b0a1e060602030d05060a0e060904030c02150301170705100c02030c0a03140607030e0a0b0702010b2d060c03040303030e03070f0c050a060203190e060d0f0203090106 79
    0x6030a000784104215940d0350b20403000920704e84600c021141d0030481c11b001d07040d25140025101e41100503404245410440400c58502d04036401100307031011640804140d0382c5a8040014150001e001a000d1202144000c000740c0c8510102201101d48010302961725450500448165141c0f000e03040d480d904145c0301405965211328095000d0340700c80ca401811b034881800040c2c1172800032103c441e40b0903a00c010010070099581200c060911848040d03480560ba401c8083d41550101c400e440010713003180c003060000030410355481360448010b20000502001107400308194441220354414a00c843e08402031030002502d031210761144050b07941500b0004200c1c030700c0703a40e400780d800018141030b2212003c0d1b1007403604001b642da0a940218505481018a00340b02e040804140540c1e030040400c0c000c0444c45031700000031100c403442c0c0c2e000802d01e80c8410010881e806030b0383c2d8801030f038013100801480301c4400450061100403a058000181d41c1e04045101900f1228517902c0703044410785142c20050f0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 988561708 1250 988560458 988560473
    0x1508060a0b0a02011d060a14070e060711090708061f09030803042d02010e1c060f1e0b03011802030304180f090b0f010b0c0307080711062b09 62
    0x40303420200e0700940303030001d10740281d0140c41c6140318010510f85184201585a600065481c0602084007040090701e041e0605680100c4007115100f01181c1e60f03a80c00042410b00500800100780924840d01c40109501c00161415400740d840d64000b921400a01c042c030310380020304c3c904c5a000400c01c12601c5413106000783c4010700720f02c400742c07140801000143c10301014031011203690317200f501580e414000124010b01036003940c14051340000c0004100481506000d081c0001308010620094018030142c3d032110081c1c0000303411ba50502d0b4559074079407000a440410505501182240400c190002c0c01c20b050840c0c408059022007400b21200c20000343c1c402000311000d40360100c1e1154414810608050040d0800c20242c0e01d800b460a0030001c1071050214019008130160302044015999404643c0c8640c0983d2410901c1074200b041140c000500b490001d02006200d03500b14003805100c40d0000301181c00c015102010b40000215400440c003521812040c0192a0381e0104410341c165104c00381d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 988562958 1250 988561708 988561729
    0x30f130506041d1f0509102105010522060c020a0501020409200f1603030608030f0307110a2f040f0c0f08070203070b2e05041802060904051003081201150806 69
    0x9000700e0310140400c1f949441d80c5141809080070038003801c948059847d907800780c255000760030f45072540303000046001c48120720a194454800e0411141100700c064039504000d00b054242d0700154071400e212000052000c0c00036200504d00420005281e6004450101d4041b1443d4602e42b82d2200400c241f80c030700c1d58000203907040503002503001e618020740d602d4140e0045c40e150308001d101c2d00c000b2519100400740d5100039032145000ba556980303501a42c106d06980c45401c10f0700101290003103441c0405155003c15040813000c0c1c004201c1d04042e80400c0894111a48181203804007500d410180030920b0300544204100600c0c0e1a2031905e03403038880350094036405000002040790304500d0118a00294400d100e40c4104001245800c5000d0300140c1010451042d215540c091401c040c1003400754003800050903003241d00a015a8500001c0380c0405c401090003c2462500100312032021020400140150038020040114010554107040c5002c00200030391441e0000c02000000304500380c0c0751034007842d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 988564208 1250 988562958 988562969
    0x90609051003240b0a0f030e0d1404170d03050903180d030e040c030f0b4609020903013b0309060a170106030e030f130506041d1f 57
    0x1400600ba07040410112408002100c643d0864400441d5070038024004001c0102d09455102c090b20368680c050307081d1698480b0ba245207401400341540c45901800c0422282142c52901e00e00d06030322040d005450101c04000050340b83c0c0407034045500c464241c4100394210380711100035400c0c80e43d4604801028140c4040090003580401c003030004141c001c0508508903d4020014010150058401401480e40810109204ac2030050408150030580700010203820441c2d024071402d005030a80481c00b00d40c0141d20302424891100328000b1032196401100980300450380541d9401400701014250380c1d0034151522030a2101c0d071007031500040c04030300d4071101021050f040b900b00f1001780301c42d00b580607640d460fa82180313000420b0031945601c034440ca10b220188400143d2183d03240c170340c12821100c88030308400341c1d580100700040076168490003511b502d4813114807a038840c54407140407610036000390f40b0041038100142e030f1020702c6420001d0b1440c2d00c00c0004c421402540601586200c60095a1251 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 988565458 1250 988564208 988564211
    0xa0602011814150c0c06071e03090f1b030b0a0605010e0d15020d0e0f01020c250906060e240f0a03060806010b0304051209011e02010207060c0f090609051003 69
    0x2c0050074000d10850705490a604000d02c8240b910003007400c120740c0a0004900320740201000500e00d14007030410500003c030f410926405480d030072070042c1c0003040c51a00503151403d100c1769820004005543e0f552103c0028107040c5411844c52410204c110350145c550f449050030214240322a9900a0011100a004407491200e495540c02e102c425885928801180140001403003a40080507070000c1d0040020386007140c0300c00b03900c07452880c01c0b40240300420342d407a042820f10141c101c407500c00c0424034402e000041d000e615a10703c03500301160101c4d40950045046800c004000303282c5240e104103a400ca006544400d000c0c109041d02c050300c503c142e4080c3c01c02d0082000003d00b4071a03030002c0c01400543c4110ba08558582540080715001105c044816200e101e1400c1c000f1036007582a21642c4106840d85d031020b50180c603c016019000c4660803045640c02d0000300d002c03c07418000c990b800d007041d8860720b0200f8452000280440304070b27005502408403545040109440d00d41d00c650042038640740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 988566708 1250 988565458 988565483
    0x10110706020a0519030b011701031e0515100905011e090c020f0115030c0518150f0d06060e07141e04030c06020607081305030306190f060e0a06020118 66
    0x100f0348460203088548024880c1184e0021156605a400940358031000d880c1d401c2c03000d050285402e4001d41c2400014815030040050041c402c5e216002007040c141300e441601d50840228220480b4403000b1a2000395603202c08030100604101c5104042c090150032070400ca4110038460010700004861080da00455a5113581000300c0d80300b03101d0a031142c40040000d000030020b85003180c0301744240380426104005560400211751800b01e80800c450074800030340301200d03074440c0700002aa996030080990015860441406156901e0054072809485460006400f40c10900c100303448200040004c002c2c08606d17034a8000041c4088142d0300c020036041c9140c5601c038030500c0500d80b5400746a00c010b010000026020582d40c0d00482c405100740300658602040d80c2e222461501050501000036016800410110343e860074007036106606140d16107424034403165501c00085010245500040c00190703003030341141480c40c000c80e14200502c1c03a84024050002c7d81c07010540411200100240300c14889203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 988567958 1250 988566708 988566727
    0x1050a081f0315060608011508040f210f02030903192139030c030c080d0b120604022b08131d01080601120c030c03141011070602 57
    0x16944016101100074019a5a20708100407030500007440d41d0403403c000010505034072603070905e41202d110032903070200c1140f010320640700c4110142c015504a0000711951f000f0820003402480200d52a10803040012292240149600000030701082103400c00c215500b2642c1d000240701c400304103e000e00c09030514130313440e00c20043d0503500d010300d03c0080c3c1180071040140d0171860301440319884001c2554203008211103c0400c1c41070f907110a051840442184022900c114020608180300b400c040d24280e0240c1c5401c40305803c068030807034055455042010075414030b16160754040b10140000c10080c10143c0c00030310311083e002c2c00540181c15002000c58404502c0650400882d00030042c0c1e41e41d06000001c041b900f5035680540415010030700015503c403020307403144c00d04896845001e424141d00f440c103406099002c0640035509848440c1d80440442c8010740d00740c00540c810070202844400203005c032030511061030f44240398907180580c60040701417040115081c1d0340d0f020b100180d83d804400d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 988569208 1250 988567958 988567981
    0x90e1807030b04030504170c03070303050901180305030310060804050a0b06150c0601031e050c09060103020f0c030310080304033305160206011a040302100302120f1b070201050a08 79
    0x164006002c5092076420b01c002d01d60403034001d00a07101000300d2480b148814032000c0b40c2d61aa05000150540d0004c001040400e00c240040d10741e240b0705240c0300300b644a0164040340f0651154006aa13a13800010502003240e40c2080740100801e443d0a10500c54606500d0f03c60b01e4840180d000b400b240c249400103080c0d40c0d41d035681d8440d07100010fa210f0fa1100c0c00007540c2541c680c801d00040314111028134200e80e020f03001d116950803d603840401000140718080500000c0c83d009054641417580070b00102110041c0704002c0d01d0a00c000c00001c40e01c900d00401818020412644042d4158000300014000325640058100322800900d58500c011004450140407100d203500f0302d074280398070f4582400701204000c8100c204040140e0300310760403a601c075041081e095041c08040c6170114020401000141810189110b400203141001800c050b200d00440c00c0401040701d80c60814400384003008502d688465030030300c1c220140504d150914000c0d5002038410701c603c141201c107003c00c4000265208042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 988570458 1250 988569208 988569223
    0x1207020102011409150105010c020306060f0f03100b190b072004050403020f063102040f0204060c0302101104050402070606051f03180f0b07111b090601090e18 70
    0xa210444914000c00132544030360001001c4144240003e000145a62054640c03a0406800802800d003e840324000c100a028103005c0c2950000c2546140500381da40a003c0322240905c0440046007000d00310007000603901088101c1d039036000c1422424071100c1c012405442c0f0160380070000070900d8000204591402121f01546a4811305040402c020994045002040c0d10790403000c45410303441e0289004e9150f01c0700d00c4100100240c2081c0d403800d5a110781980c0180030f001400004918001d11010b400342d03800750f000a0b0204100d402d9041c00c05d41c0c1007140c17005400b80707490108444001c2c2400b901c058400c0384070b031510a94022039480280840e41d40700340010500180b10b281092640c07003400512600541c18400480c0c601040c41d0b003051003003052090b0310f952000d44200c00c030f89140d84140c0c440d0700c007a142000f017050031000742200f60801c0118103800b072a0352201c01c000304101000c0012029000b00464100300350144208444201c100020350804860802704c03440040101550b4a070070070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 988571708 1250 988570458 988570481
    0x40308191407030c020f090f07050d0b0a080c01140705060f090c0a140a0e010b0d09030203300108010e0a11180408030f010e16081b0a02010c020c040e120702010201 72
    0x400081c00c030101030300136080340c0c8103a1081d6411301c2c800e00440c041000c084022617140d4208182180041e40c2540300308020030902c2e05540e80051002c40103130118030700100b0b94010340a0b41d0b01c0142482655a00306c3c0c8a20b4141841200c550320f890080d540c1d55071102000741107040c040c81c00d072000c1070300c4039800e01c403091740201c01401d183c49403a41d44403040741389404a0081780c013a110000000c2581801c4c02225030507100c400c21403c1c034007901c1c1030700d0a0003000619800e0f82140400d1100c50542c1071364410192011400c0100306450288220341ca411034007040c0c3c071603106685440050004102d000c14003004603908070008080300b40101000c2100050311b8144600d11142c0c000401003080310107009140076213280b008140f4242e0303c4407500d8054540c113840800001c4d100c08403c020292044041507440703c3d080c0301e103403240007001c140f542446d00300d0041c0b800544d4580b801001da039a810003851702040000c607401d00c5160826441c1940b6280d50030280c103102400040c45c141964000d4112040684 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 988572958 1250 988571708 988571747
    0x80a120e060d0e3018150a050304030305130327090e0615010201060501050f07020609150304021008010f0e091213080f07420201020703110304030819 66
    0x82014003581325544e071a40c6680d1074904410810328540c220700301c5200456603002061921882d540c070b00c507103100350359110760707120b1711410b56140c400401801404c01c1c0c0c1426101c190701d1342450724001e01034074401800e4003580043d222252000c20390052503280d61b049c0c550700d0001c24144814500311010b00d181c12150105041c01d8520b4501c0030006850340c8680a1407050b4001c400301400120b09880823441618001441489003070b810181400060588910042010f854101d408001c42d10740c030018011244592408000c100550800d1001c40480400526103c0000d60500c441903511140c94042d80002134200f00005009035002c00030420f40c04508030344951501c0c00c80701244203e10450242035441d006090b210b00644000280400c1504c107032000b840c00d131229510000d09803400000002c03689013070005071110a45803580000034048016400980e0307855450901030000c1c008500c034501598000c000800114004100341c40324100b0607584a0028100c8501c100e81103416444940c0700903 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 988574208 1250 988572958 988572971
    0x200a050306030f1e0c03010c08010e0a060305162303060a0f14010e100806150f0123040f0b0304150203040f05100203070e030109021e010c0c0b09030601080a120e060d 73
    0x84c4001c0d52160b0340600c40c0307800c48aa100300e640505080e21445450480410550801070000b0b0070600a9203a0104c035160b00001c5056030790300d46620340008035920401f03812010605001c01a080c022500c0e882c413542e0800380100b044200404d0740c40740000c0c49404a80d59407010344a0382d01c0d40303030413082002c0790901d0103401d503584600c550410780e00180e900c0074600c484118001072450300071030128072912070702c0e0240c0c003404850b0041c0f10031024090625810000c240c03012440a0300d141c64403603504c18400d10442d40300d500b40400120182c001d6004058183c0303040c001c000000f424002c401040260800c805038481d141c0385070158090f1100034004140340900ca0320302c0c101802580c080c511032002543c4204c0c180d8050720605080302c03021039001e5040013404090108001962490303c2c9000b0040c90b0800400c200c0381c40d00d80103080760307800540e0014400518418076140810a180c094010080500200e43c140da0700c0511002c5800111018428412400e03001590742c507050302c4403d0803210084c03152 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 988575458 1250 988574208 988574233
    0x5030f0c21150904151805070509040204020d1805010c02010605060f0d1401061701050114090108150a090209040f05101806051807350a0e0f10200a050306030f 70
    0x801041405c0a528a14006848041d160042104240d5980000250403030b01e003410140100c42600030b2040e03820540070441807a56000d14803c554040d1050740180000e4000e41c6803007130075240c01c5068403046a0400da000e201a540d07200890b0004040742003001d40c1c2c2c4000c0b01d2243e001d000d0741c09504008048040000070344942145660708041c48462240310301d44c0c1c9030401555100318a80c2c020000d84401e100e01070055019803915500034001014481130b050038030300014203001c820340021800301c1e00414680c500381090b000704c001001002c3c40030311251a0a940c41e02c0a1005480b40d00030b405102420000b4001541d4080c03409014007800380407203001e0440341d45c09a150144e030b40d42c000a414660340d03940d100d03281c803506e04042010003400f86180e80c02414a2107515000d0030a8901503134400c0c24001444003000650b54940040b0040d007648078007842d5001c2112491201c40c01d0340c488442200d41e01c00d000000712004005a0700f496501d907118807010a02d40100e54800020318407410811245 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 988576708 1250 988575458 988575473
    0x307030503040b090303040f0b1504060b1c3810170702012d1113030c080a08040e0c1c0b04110c0d0f05070b0705030f0c21150904 57
    0x442d5008049296994580c00c1c10356684e4801100c010b4a04044420240c0001e0032820481e81c01c100e228040706001006240082d04642c25a800113000c05400204601100c0010320700c18200501550100440c44c40c0305840c003041c42c564941d01c40100c0345070380d0320f080c0c849020038040840d10700580615992828520050900710f030305d02448180707241c503000003050a841402880381c0d404503042103020003034161810301400300034080c0741c41c070300b0341c40d0390001502d1502d400103000307200c40c0b80c0081907030b40c0d10350709180c4860102d07900841480e0700f0010b828170104130600d04507811a1402d272013000d040c1d51000c61501e224000d81031018008410051040300c40620394001c2ca0407000201d82c20480320342c1d00207a071000361081d080c1706081c075042280e071070703a02d035000d46c001400c80401800c0085c6030040a43e248440d045040710200c01040001c0107011440c7c2c55207801d640e001d04844002450600c81e0401540020550404842000801000144445c0c0540000d400118004d4401407042c01c00340340090 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 988577958 1250 988576708 988576711
    0xf031e02061902031902131a0a11060708040b0406020903100f1a0114030622091b0503100b01140d0605030114060a1403030f0307080906090318210307030503 69
    0x1060000820b140b804066014400ca0380583c004a00305415801c460300250041c1d0042c142d842038144003181c000030700842d622200b520014140f0030307141d0744840c0d00f10007814075080070303103142c03100e500940400c00a00d40000400b5001604503109010b40c2d5102d10309030001c2e02c40c3d41e054a800d4007600701c0041414009821800c0300c00c3c081003052103250aa104030300d801f400384144150005001d00c0c0305046030508600110f80290b0f028141708c82a0f19805450582c11400e81581c568041d80e602c040e2060180340c41d11541092202484001c04901c0c2100007961000a02080c00d692981da11034440719a000310341000190a41082c0b583c0c440050380003201c0102410300ca00c0c2d02035400c0c007500d0800c80c03c2c01403501e4400c03407004082c040e115080c10a58150801c0c146003c03905440200714440b14075107804091442451190703500c42c060300c2c00c8440141001005000f10307045520900c8403015401101e81c903807400c0308007650803901400160350b070b894a020301003401070182e000c0010f0074804e0650010045 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 988579208 1250 988577958 988577971
    0x306090c09062809061b0201050c0c090f1503030301060c02060912060a020d0609090203070b1c021201080c030a02060d0e0c04090825022d120d030c0806030a0f031e0206 74
    0xd00710160390304000d0344c88550500900c00d1b620310495030800150300a5029200c1c4080c45411900c5c1c48540d600402d8a0410035034100842c68492000c218441c3c6512408280750201a030145055500d441c4014120000050000340314083c00303d20b101c010346644c00d0143c000b0290b0401c407038a42c2030045000e80258403500000d2901800c0260100310002e1f00d01800d000300c3d6001c0d00409245180510b044015000381000e000110551000d802d003407a00c0340060030b0101d21510f955002e5524000c0424034104025084a0098010004440243c4d4804060310241d041c15640800d88100c15074a0904020600d444aa03000d460013640d142406031150103400c180d030040c4e0402c03000048040b0046991108100000c0d40030170741c1e54100c0034010404016528a08513050324030103291002000448102c2c1e160f02010070f80d44910ba100e26210740c10b0052402602e600e0034061541c2c200b007000300b03071107501e181000713017140809102c004c00f014843d2040c1d004080c044084940000c80c4120000c0d00d81c001642d44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 988580458 1250 988579208 988579217
    0x906020a02010f060308041e080a12030501150c12050702120319050c0a1115162618190603060509070815090403180603020706110306090c090628 64
    0xf6060050071442202d050381c3d0400e003007500301031411014415000380555200d4a51409040001d07001c0004c202d40380c052841780f10030b013411480da08801021920143d1201010343c01c4284118050fa4208000d000129003058101d0ba00d5082c0384420740e014030440d000290007080c01c0c0d4140c14140400f0001d0921500700040d245608491040c0c101e465020f01190640c0395008441e100c0c0000701c0210000589003405005180d07418000301002625402c094104c0d044001c528500e01c04000c1c80001c2d00c4d01010003d000f001c0b003d0750080440c9403900601104102c05c00503040805090750740c0f8004e0710000e11424800303038070454aa0328010060a1035208103405820f98002140e4124025a1001d01c0746901c10420966034110b68201b1050280c00342003a024411500540c21a0030303241e0702800f024040544001d80d131040186030000480d080c1d034001250f40481441440750303981d00d10110503000512171100580394501c40b00080c196202c0c03d48040424020301c1c0602c19200443c0440501c40b10f22501d4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 988581708 1250 988580458 988580471
    0x19060b1b0708030405130b01260709090612080f040b070c150e0603150d0503040f05010e030f030901050d140a0c02010534050c0102040609170a0c0302060f0c010906020a0201 76
    0xe03440e959004d107020f80c980c401c000301e503078101c00301d0b582d481000f01450503d4112409422040c03980704480030b64176000c0d0b0030f48e440010401e090360096098001046200c03410081b680c501065200c2041d00f081c8020701003070340003c015024841d800140c9019010940e5042c1c1d903500946415070940e0014030880042098003400c9401160080003100e04034440134012618540e50035410360042d120000304268004c07094007800001c141d0130000b80010b86440840300c8400d0b81000b001501e11400b80345014484e80c000a00c44d00c44500100907500d620b8400e0030309549504011440601070044034640c0000c0000e4142009419945038200e503034501140d0300204800e40b03e0070130303c400c803007900c2c0c0801c4012440041428011051300b400f00c0c100304d08030300e4800d041141c900701050a90f80180d000130001030314128280150441c05094050000c1000010700400c4031070b075112030200005100c0a8810200800c5070303034902203200121514202c403080208100b590310300d001c00003500203d50401c01980703080f5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 988582958 1250 988581708 988581719
    0x1207050c160e011a0c01090309090e03090a030b0612030d290a0e060d0209042d0c091805010e06040611090627150d1a01050319060b1b07 60
    0x3030680c0d080d50380202c030b8810076a003451400d0000e03c241c1c4101c841c54410400c210240c116080c400d0780301e002d101c0e0360345c801c1c8685484c0e102e03016280d04600d000f4540c0c00412125a10359941c14041d4205c0e54464129806642c5035400a0a0842c40f41100c3c00d8a000014001e244213000f036002d011410700c520501c4140c1070b1400d072461010761002c40001e400c807842001c02c1c40540115040103500c10740041c8590000c040a6010034554601aa002c5529003940102141e00c9224061044000044c0780802c241a03101500c940545100500c114140e480d502c45400300c01c10001050402c0c0103802c140207000c25030059080030b503507003000c44058500303620380503041554007442e4040b01d4070114000e100754148160300e1013031a40006820189620018031000c0d0f654140c40d400342801030360010028407500e800352181500d080d96900e9141f2801414044510303c0c950381c00c2425640c2041c0c00d44211100c2c4c1901c404200d00804240d04580202c170000b01c7c4c21003840c80c405080100110101082d1007155580700c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 988584208 1250 988582958 988582993
    0x30f060a0c35060f040609060305070806040b0103061e0231080d1d040603081c0b0a061803170901020c150f0c120a0518010918020706021207050c 64
    0x407840b01000500260b0400b05003082c00c4002e41121000302040c010040742e80009003182c0c1160b2090840d282c4842c010014040148a03060060104102602d80c510f059550012200360500000301030a03a125101110300381d44280103107824254840444d80c407120b02e01c180a014500d4410109070801050601100d00365092000c82117078100c4005206a2071514420307120001c9400e03001c4e081d42c500a04410302560b840c001c410046005014195072030084803131070f07441c10001c0c0c0a060721050410150301160340310b101c11a0221281c0f40350003c0ca211101d00b0100c60030b40035510241c06400e030384001105643e072050052001e030000740c0890302001030410a2048801c52900c1508624005212200ba41d840080080c4440104042541c00000c07813244080302c03e40200300c461001410100e007030303040d032420f0101d2100c48520900b4189034452405010b00c00d18040084150f4071180c002c2941801c011264040e2003001c10040050315661804910040c00b40d044000301c20300a03c9490913408011301107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 988585458 1250 988584208 988584257
    0x30b040f0614030a0b1828030801090203010e011211040e34090c050d0606020109021203030f040825050606040c110a060911181609050f0f030f060a0c 66
    0xc00030134021562500d000200d02101b01c0c05010791030281c02d00304822031419807120300304c1055402044020300020308001300842016008040394920410040c0300048540c4181411140e02d61018540300e00680b40040000c5e880c40f4035140c00c071b801c0004011040c0c0c07001c15802062018100d041d00120027a1148540c036803258454103a00310206002800080101d400100000309603003042450070103010009000c44550b0b5001a0050355210f44ca00c04610300b10060b040c04001d68001107041d030508200c4100c0702030b4050402068500001640701d5240755030340b00c00008100700c15000f03103555524105542c03a858110354240c82945805c0180c4001030145801880601c460700c0100404003a40da2031b84010240402d00b41e0f01c6000501c00c418807540d449403054010b1601c0da07081d0301e035402d040d070641808181c546420800c2c003580c0441031055866454400039900c0e0222061701c2035550043c0440e081c41c3e2000462019070040d0400c00041690a801000c0e00341800d54a030f00350122850a051203a00c0c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 988586708 1250 988585458 988585463
    0x90c0109030b0c07050303090c03010c030c120b01030e011416022d010f0c020a17090303120a0b060a050c070518060103050405070b0315030c0a031a07030b040f0614030a 74
    0x10800000d001281d42d403100a07500c03807040d0180516210f03841e26a18a1500221410b0b00c6c00e521006a4650328102030041c1189103c0a08042c4000362003407101910002c00000d0b40541c00365034034920002684607030048038502c01900020414803500c00d0418000350746c00c9440b060f4400456803003061152001446060300d100008007813185080a280d403480e04a22030049900940d203a2505d08205520303449500c0d0310000c1500241301c52181c0f854040c403a000202407542903054107221740802e40e02c1c08022244001d4a441000040380e69000d42c800080c00c009072120782203078010440c450020741100083c55440031920850344031130f46d14020030051010090007040010352140102c3c1030f40d4040d4001c5908180300f002664610f549410909406820032941f03178209071009001c0052505060141504000c810303260010030301c1c21070b140d05001a104240380c4004150001c0050041803095006601d20b000c01001400b078400010a400e000e0200ca01403128420080c0c020b104403403030009040030170242e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 988587958 1250 988586708 988586717
    0x3021b06070201141306091e03050705041e05040b011a070201050901050c0a050f0d11070b09060a020703050d0905040f05060d1b0b04030b01081c051207052101030b090c01 75
    0x5001d03801120f41160280d03e8030858481841620a042103400317000c2e02504e030540d202c4201c41d2412030400e07099224038640b80c1c00b1501c012420300200e0008595541940c0080e0350118020b10329050342c0d07a00c107a494200050b4146000c082c4020400c1c0070301e00c0c5041b20801c2c5520120390501a031440b8140c4a420700c003d010540400210645502076009004009090341c10b444401c8030719228541010320403090308280d50011a0f440e06000d400c5510040c42c1d00051f40100382c514140350b0b5201e258402d060845118180c00304844c96504d2003040450003450307200781504c180b500351080252400d039040c0102c91113a403c00003110a42d202920505100e0350000b800c51202d9142c0d5103410344001c03560020130204003040744010a001100c600104011446048128440c1d898280d201f414801107421040401d107001e1000282d242c1e0041c01c1d1200d610707080110300340b030f40c0320050b054070706102d004e0200c81c40d900240c00704821503200d1100c1078101c0b400355210026680d40c111810b912011403202c5980800c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 988589208 1250 988587958 988587967
    0xe190b10020a17121003061b0903020607060213180f0912031d030c0a0203010e06060901060f0504051c0b06040b1c1a0f0901060e100603021813060303021b06 69
    0x155031804a0450200980c0200d240c4071011110444480f0b0072115417036480440038040041003401c1c0310b4201e0400c0380d0000203044e0202c11000508061582c0710180c4101d0380030503614103011441d4100d4180450000c42d80010590310304c01417241003102d109205034203140030701c1c1060f5051203000306100c59070301035004600f610300e00b1020340041c8001c0701c81d4036a60148d4113605501000420040c800e070744041e001001074205034410903003034800b100d10003016500008144102600c0b10300e8010705441007800c0c050760303184005000300e030b680c02194017460788904000046405030544220b08009140113000105071942c0781820b00c000c3e5280c0303608080d00b000b0104001100c03c01112030a1004070322038000784007050318600c03882c03c2c55141991525004001802406034800d02481042c1c014810541804a90700d0480c1d030301e180003005441050145600050318400f010705101c415121014000d1040d07041c1d5000300703941070080401e404210098072420f011204000415000028880001002ca5107003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 988590458 1250 988589208 988589213
    0xd030809210a08100e100321050405090415051003021008011401051303080d0b1c0519140d08090c0102070f03020d230c010f080402091602070e190b10020a 68
    0x203000140b804c031140001c400e010851141c0c001140b07000340384000b01400010b0442c24100201807040c1c1c00c1250b010a030031107218006410a003542d04550301110112420342c0c2c0c90800d868001480514200075a141600f08211380030850300c00401e486c0262124800e891034200255035408080c0a01d5040b415000a196040e40c801c00041c400101c012a000d110a556a525a50550008248128815100c1c800c0080505049100010455640c0750390b1035469074640320981c4500f003114499030f4081ea140c4110042c84945000000d588200c0d0f8100c486840040c14000c0c8041d8041e2090500d6002e4100c541030a50b100141c110281c80707201600301009441d41e400c002d41009005021186003048406640d6401315009840c02c100c0b0001001e0f140c038080700800140b003030078580d404800b1700143d02e041c40701503112609200d80c8014030401d515070b440403240b400c1c1d141c20070f99405540c0304a01c3c2c50801028012406141c00d103148841400c0c001102c0702d80c100500d100e0b1864070000146e012240309000b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 988591708 1250 988590458 988590467
    0x30c0408031c0e0609151906260a0305040e18030a17010f030c09091110030b011704030e090403030f0e010f0e4b030c060601030b031e010b0d030809210a 67
    0xc01402660410204001c60047c0e4002d03918990b01002c00d41821001400281005110602840d40e180010b081c4a00380b03580d01800c0ca01660050030610701d40000040c12031088140201a0751309603a08076a107072400c8410040100b6018020418a40e245000019401a802c0361a07020b0700c2d400364418802d1030030010b120000b0981007030144c40c0380965080ca24419241d210b031203c4030302c05a540109101c8001d000141284070b5045000620341c013800d04110110394096808121204115101d0b04251100d0404401500380040250000c1e85060320321018404158003000060308040401d1041003c042a8103171175076150300d8142c4502403e886c4106408462520400020b1042d01c41c0610114880c5401c040e03038810140e07900700715800001c0c1091010001c000da03990100c000d03c3c0a0140380e515202003512007070080f4141d0100d0304117400c108107021080d0000c1500c008064020315040b040d504004103802010b898003051401498035100c220485c440b059805510340d003146502d04000681d0888 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 988592958 1250 988591708 988591711
    0xe010c0503090406060203041a09100c0609020603011206060e0603030f0a0918020301060813050c010f03180b06011d101d040905070512070e0a02030c0408031c0e060915 74
    0x4600d4042080000300c03940d103a1060301e001e00542d40c002c540355410814202045134801418014141040c80301d00f01c1c540e2122620303035012425150104546080340b4020015041e2180000c0d8002070101c008246108000600f9503668003803c41409529039550b40d1103000e641c1038a0b2190150410054803c410385960001c103503100803454009003444da90031031060504001e01d58014070a030004010405035074032464050f08004ca80f640d03110030320150347d5595039400507207640a0500c1110303902c01e413a0b607003e9406054080030103601d81c9140c440910341294504011100070b40820f49050340040445140310081201440141481da882d95640106880c40c80d1500208000000c2c0c4c00d503025096207950142c0c2c003841e88a41c0c02030121608060400c403c4505040c034000159100c0c000030841c121000203502d40090308010016076948a00d03034040d11170f110b5a00880824800014002d8207020400c44840051a584c0c004005500f4000b64440d1500000d90303103603a40c0d40c0030381068140c0303122080009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 988594208 1250 988592958 988592963
    0xa3e1c02060d05010909020109080d0804140f010e0a0b1303082206090c05101b060507090503071508070503041a0a0f0f050402150a080f0402220c090b04060e010c 71
    0x1e5051071081648001568000d801004a03c0c0d19010444215600070240002030720410000d0000044c5038200100061310040c005000003810514984241c6003e020890b561081c1100900c40b030b40c154040c9607910344400204440ba128480001420300f18480c84922886502d9561401c0b55222400d111306040160517011814014000d10000081c480784620407250f88901503c1c1c01252600c01005140040540f0500c24480d210b0706401d011254a15520306140e84020006495210f0f503c040703e0412094010300d07014402c189001c10204004403402000301e0341ba80d6060005d41d6114401c690741e00045c0c81c002c02031403030650f01d01c0c160700c4544102940400d43c52000101c40056180e14000d60b12104d0850044654410070302081d401c0104080b0001b40c1c1d100041e900d041000500201800402003180540c003c442010a0440d900c5010488500e180c140c3d001d15031100520189000300701070a038080104865000c006911340400342a10101d40c0c440c0c0702c0e40118028440152190143d24004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 988595458 1250 988594208 988594219
    0x70302070b04031109090c03100216050d05040e01091107020904170f0a020f0a0c051014030a0506040b1009090f15060201061509030b04140a3e1c02 65
    0x4900140070201501c0103600402400f5076110040091004a90000c0d11a41040c0c1203142841070a4800107008a07c017039005100594800d44451040010051101c1c014542c0c042c131482c28511584c460080d10507102d000b08450001c0e41d90340c002d00202c0d0040883c05000c92011300c07008c07003d8600301544075880390244a014480100341c54034005180d03c10f41e10038201078408a00c0c02e1505034100400c42c0c50400610050480703007125210084081c260b0b1246512a5010815443d2131b00d22642c0030105040c07002c0f40c0161642060304003440500001c44c2c0060050345040c014841d24075003000b00c1c82100b2051b4a454002c94200001c0300098100c02c0c81d91001c5513111401d10145412000d0408010304039039000088241c140320841d004085035840700720402299550500111f080007241e03079003050740040d00d480303000c200c2d140d02c508117041204054a00548107811403081182c80da204c1050b6000020440075050403004a420b44840c0ba4500f65000035540485080c2681184106c26100b40000d16 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 988596708 1250 988595458 988595473
    0x8060f0405281e140105190902070f03260f090c0a080a06060f03080901031e14072615030c0306070201020a03110c0c011409120312180a030302070302 66
    0x101210310701d02100c612842c807503a880c040400a8400d201e25540740f200300c6014403c46100b54255003081c1c0041c0107a034851402c07141d44079200c1c144135001000030402c44009640310b0b0500e061506061541c032001360b0103d00d05000030400e005403c5240c14074000807540340b1840351a070343c030002a0150300400040c454464400c02078030603513540141c03030300074000c05004002d8880a454807006a0300c1640c00191908148001840001c0d41c000070364041e10b1080c42d0008000242410b4031030241c0001d00038190540c64013041d40a82039003251000c1c4aa000340c0c4900086a4505010180440b41d00b8403490041a03c60049264501e0084440c100407500130201c541d003007100800039042440984c0e0040260307500040c40004560140590b800107c180088103003010706c612105a15120603500c080d04000400703041d11000070703480c02074800d820400703801c41015144080c1440e03502d40c020b040c0b1085070590080052451032140c99543c1c410780048004d044084c10342e03076064019411200c0b00703d083d409600c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 988597958 1250 988596708 988596751
    0xc050c15180f06041109040804120c030b130302070510020a23010c021b0a060c0b100e0a09050c0a0819030908011e14010503030a050d11030106030c090608060f0405 72
    0x40e00000b0240040c0c002828030b0b1034000f288414034503070503015200c65000c2001081c40e9000740d48c100c0d0b0b607483c110140c0c00800c2c076060341c0c80042904000c20300c070307408010b20280c0d01800e00540c0c1e01030701c41d0b001c0702c0c1d00688501c1000544003030440140c0c0141c1c130402208d0000303a10b8416000060b00060081ea031842500c9901c642500e0301400320741c005071302880d145170075074200842c081d054100507105460f8142c20614014010580030101602550551002c07420114188441070300501800424001703a0520800042c0501003103041582c091103405000e00c40c51038800031810032684070000a022040c80f00c00c5d83c40c402000c5d04029000d20200d00000121030f0006e0250b004101c1404114805950412511004896090b5030000760801040018001a240001107680110b000c5c100540c9840060510001405a10121200401020000244040e010340000300d51402c5500c0f410b042c107803a000c0407507121904546803980301c040d4400c40c0050742802d5128941041d00074500f12400c0c110300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 988599208 1250 988597958 988597963
    0xa11041104081b01081510110307021f02241602100203040b04210906050f040f0e060909030703020d1218260412061d1504060c050c1518 60
    0xc1c0b0b001c40003503c10b5241002191303400075611b41c0c025031441540709031021981c042980c2240700300001d420f2009021a4a1000f2010800e0300d034100d9004050f0004240d112551b01760014154000340d02504c81ca510300d514070160000d40c006400207907860100345682e8103d03041803c11710440007500b0345c0658009100e45107020300086201e28014424824a82030130319242460342121f00300380c0041d03c12035699160103540f007604207044500c2880c12a1720b4115130814000d9034892035002070b943c42c6a02000040a464034520140f140c030741260854900d544d01c114082c0c80384107803900100140c110b18855094a40a040821112400001d000036210051400d150700782e003003028251b9180c0702414808461003000c074182908596900400340c280b41c5491982038102c41d84050081c036803500d8140d00b1403007503401c035040800c4809040881c0c902c00d243c807164140b18042618142c0743d20f0700f0202981103c900a00c21a007000e80000c1c020803041000d402c43c0910894090180b038810501c0041080d440c2c5401c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 988600458 1250 988599208 988599223
    0x6051c0f0f05060f010510020c0d0201050c0106030b06030c03031e1606050705120606040503150405010905011b0e010513050409020f090702030d050114030607110c19080c030a1104110408 82
    0x80008065904180c25213a60b514016401288600d06d07502c2c00c035020503070108241308000c006072804044540648016036190258661960072036290100c0041070008000485010719000c0d02614428070000c01855160301c5245d6000c402413500c00c10748001030302200018502a03042c10f007003804140c025541c01d001d50f01d081d162580041c0300440d8030078440d43c001c880360360010821214580f802d0710b0200800d443e031001009401514207460f00007424080c00303400103124142e201008001000b1b2510354006c7c40b4107051a40380c0010404c03400c00c50554061002c5528248400301d441c8a180d03c1d01c0f080101a007542c80d0b040b82c00c1a80c3d201c42c0421a11403200c034034000c440680155445d081c0d00b0130a00101d0300c050f40320028000740d8880c1d01d0a503442c042100e642000d980d260000010a0300c0c1b55040c50000d94817403058001204080400051000720610b5060ba003043d400c2c0c940c485260820155990080000600540010703442200b0914060b8001031000d41d1400a103401c00da9524060740c1420b41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 988601708 1250 988600458 988600463
    0x15030c031b07110f09090c0d0f05010c170705040612050415090809010e1903030305131208071d0f10030b0307030c0503072c06040e0303040606170106051c0f0f 70
    0x100b1000300494a4071200c40c03a11101d0603601c081c440d240250500e61f80d0584403200c5802840280412404d01002d641e48840d5a9042402480b16440280c002400c450015600ca81006601c80100b40c5983c4514120f030701302d620554403902c14203240d5030404001e08001d00100d400070507850b007c0030550710300e01179285035501031041e09807907002c5d0200140590100d116480d10489040745090380701905454881d080d00d805150000703c640d1440c1a100c88000071801c090450401d0010b03951081c1d030b00020051094601c0d66404c5859450f031009004640911001c59902c0f031208c40725130031700e400d01b44043c14090f401c61901051340b80b000c00c0420308200c41500140c8031846290802c2c00340f4141040610700401e40c0d83ea9080840e4103c000c51080b9140340c01040c0143e05003000071503029560380d007000003090000800e60b6502e080078640701000340494400c0b20301462002d41e1042c0c40f20010700c2044120381003e00026000d03003000210b440c1401560300e04803118500801c03c40041341c9101a005409403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 988602958 1250 988601708 988601723
    0x409050708010c03060e01151b05071d090d0809070b040e040203010c0c050607080903070b07050703021b0a03060f0f05090708010b0319020d23010b0f15030c031b07 72
    0x1420044201d0a480c51407103c3c42c00e05080240c10409510740c1c902050440b880c0300c401494103404c0e64021500760f000c01003144209080680501d041c04000302d25141201d00003250ba03180b07205044013621000004a5010510307030042811180440d0084500b1a445200141990b00ca00c0d08e0b00c400d00201c0c2c0043e0031440b4100110360070402141000d00c92a44009014103010399103e401d540c6065442c3c0c1c00506000412002c0004198a1f407030810079291810707031000082c00d00c0c0ca0031410040850308a460305500500c2942c48400346402070000e40c0c840681c016103072851860035900c50380050808c40554400c500d41d901001950030130b4511402c1c2c050107004000d0f00310f0341d2a08000d6401c0d01d0150759242e1003600200d03686540d150344a0f0721818031540c11784680f0f044003002d082440b038081d0f0b01c0301c20f450f2036850140000c0d480d410640c80340c4424002142c00c042c3d10400c01d0180700b8481030b103030f81c102c07480481040490103590b640b02c040e59011220310200003240c80e21031500c40880e00a8841154180c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 988604208 1250 988602958 988602973
    0x60a050c1c11070e040c15090801060b25032f06070504030c090b130c03090f0309091109060f03431b03051e0301080304090b0d08031f05040905 63
    0x28000b8440ca10050040c3c04c0062241d0030305848152501c1e015100b8242c1d003449200c402100d0780e005100079001084514020032515a44552402d00c40c2d020005001c81d0080001c83c51f80d80c015102d1292540b141c0541d201503074013007401d070079001065041403640003551090b00c000e0702500041092038802c500c5650354645407071551429a200c21f0f03058110310201303410481d455541d5103c1c140b442e00e240d0441d03100801c8440b40140305030001c2a424101422007030100c0e1744182030503040180d42e0100c8a071a2010403100400d21940041030080d108410ba2207a001c000d4002d601101c41d02a41d003110360f08076604408a410300141c0f00c819070600c082ca054100b4410005806c40002c2a40300401c481800d05401d2404060135208601c03844001c000c043c001d0104410030401c0706103580060b070703401c81c101807030790ba5844404043d80d0307410510510151906204000819050807013405d80c016070301c03500880c210346412a0f013021b13039011028040020644840005205d550354003a00c6040c1d4022070260540 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 988605458 1250 988604208 988604237
    0x90b0d0b0115030e2a0a0317070f06020a1d0a0b1204050304080607020c0306100b0d24090917122a031302100807020a1b03051203190b060a050c1c 64
    0x40c1d40712100703103604c46c0020400400c045040c07480152100300c095040719596003c40d01d03042340da24000000203801c09101080344001941c020f02e59540102c007031007580e00c02800340800c202042d034180c018050340e02c80c240008490440910503c03a009032081007035a06043d161060185018003c40e102001603114260b00780850074107100a40e006040b401d80395074404d0038204008078a2159403040c04180b40d85032034800381c0e030071034070424902d201440040d08200350399400d644001d0141c4d010191a41542c1851000444620301c0031110740042d41407042103d40e8505c10a4624080e00615a60304e1402c004010300034114810001d620821044d4545209100385006110340014405000400e00000c00c0522100ca900000c0d80d100303059004461904032514500007101e5008241c0c0000d00078401c0c0008850070980a401031485200040c5030042d0007141900000140e9981d544800d80025003000540d84061041004107510a404c808844201c50405e038039180502d83d040541c400078400340b80c503101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 988606708 1250 988605458 988605523
    0x3071d011701090f021c2001080f01050f150c0111120612120702010306050303070309060f030b0f04090f1a07091e0905061305040c090b0d0b0115030e 66
    0x41030681d0001c2200c800c0701d50724071210a5a1180c064801c0d0514180102c0a1031200c5804080302d500c402d01403404400201514180c0b503041c94128082580d106c0040c08954184004078120380c40280b03088180072042e8180500c4050320030301c049541c102040000302510003401111710a4045070322903036550918184503911075002528151103000c200c3d9024182c2500010b4924142007101c0301d26580d51070510050b0b00421950b40901d0305070002184850905070881c400400b1a42ca40e294164040c01886007182121940c0d0b4141d680980400a0505141031580c04a00d18a1044150300c41c000c00c1511031003041c000c00b04068100225a1040242e000c0d0b03c10300c00cac0001c21100440041d90708055042c4928800103002e0358060342e558000003029559042003030442144062020002d40c206400c00340f034100304038000c0044003410a45ca401e483c0c24112000b6002d5a081680b21301c281c1d080402840611580c2600d000400d510780c03110b9522450280040c0c06840d60103144407103503a140304200c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 988607958 1250 988606708 988606739
    0x1203160302070506010e090304050301051e0106020a080a0818032a0102090a0b13031b0510050424050904060b0304060b0d050a06050a0207060603051509120901050903071d01 76
    0x810540144039500004900003151815102c1241e03081650782e03942180075145004a40c4101d501d90308203c140028480ca06018028030708503210101079aa0b201d50b4103a0303858a02110040110744100040380c1118442e490a5800000b01d801c4a10f41e0508002c000d4915000303e03040b103094440c00707035415540c491030700041007010301020029401c200381c14002600c18945407264403c2100002200801c4640c0101c4160145a0150500550300c900c814811084011402403a000305103289000010324003400566044070000c0e022204410307040d00b52400a041040d40350820b1020500882c94195140e000340f4010b020f9135860151245018100381003591120f81c03000d4003410050710020040b503804588002c005400a10204098540780e0442c0024450300e000070f8000e6142207000700404c5008210b600600d02c55441602054803891940743e1182c1c15051400e1004004200b032049550251014200c4190014103444100350b0307609008900c200c2603112280c00100d00401070006d142144004c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 988609208 1250 988607958 988608001
    0xe041b1106161b050106060914090c0306060a030b120a03021005042f0d060c120c081503070506030f070801090209060421051005090f1c0e0a03051203 66
    0x104440d0420110700e80d02d000c8000c0b15003042103040d09402100920f50340000200c0b80c4d202c8000c00c0303643d03030f5050000d04400f5140503100103480300e000c0220051034081c030303068080d845c41029180b568603003008100169100c5a0b14105041c0c4039020641955101c1031312554500d50071001d0944001245002030a2142c1040a1a58140792000f8040402ca58400394440000d4194040540284020110041c2d01040c000d00360b001d94401d02080c01c2000540000e041200d050325000303003040c14030841f00f095400d030045403000034002e0000558070290070b640f0910303400d070b0140541701100c1d201c0011445581c41141d00c0040d002d088400d0001c0e41ea03005151300d0041040a108500704102440042c0b1984541d02ca52610303440380032550021a8585054107035402e44c04021644040e0040b905000034060468030700d1054003a482d001c0c1e51280340800c0c3c0c00959a00700030f0800341180c0009003640c07550050f425098110a0200010000842c2000a0316104904020325030f140d10f444c01100c500c00314030203c0c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 988610458 1250 988609208 988609213
    0xb1609080d0f02070e011508010b180f0d050a0609020a0506030f0712060504020a09050f0105090607120c1b050307050105120a0e1f06090510030507090209010e041b11 73
    0x10080e450001c1680300e40501146031810555000141c2280360407810b42100121800c40c01c00041d598041d40c4011801c0388044e241c07961560398070312004065001d01c6c1004407440d040380804000d0f030702e00500464503240c00145000d000302050348981349403d4a94102b25211642c0703e03a110b082d4a040c0c007d6400600046a0081c518036000ba080300005402038003580a0000001c0c81204101d0350703820074409800301600071500e603140800000c1c45c0740ba02d07100b1180100360b03469000505510410403500c180c0405060301c0d241c69015580d003c880040c110010b0304128020f11101c001400310a204500d0080508602524030b0070321040509043c100d03401181401800c00840452401d071000060b88640c074070303900007102d224000c9040e06040701d4801c3c41c01c0d0402c000c0d5426a10038499030105060320400f86041059598075038203008510807a000c017400355170009408101c1c0090580040901f01010f2400e14981d8010001087c142c981d041da084400203010180c15090310f511594800920410303500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 988611708 1250 988610458 988610477
    0x10213030b010f0b27220b0103020306010e060d11030405030a0306140d0f0302070312021609061a03100302090c0705010f0c0e0120032b0c0f21090b16 66
    0x880c8040e81700d404802d0400742c80f40304450000103110540480180805050220a0380340d2031641c010009041d0619040d05103480c5545400354401d00c241e03031103140b06844d00314100b59a01c041202d0b0360001c0c7c0106000c1625038124a10f07544215014500581c0308400a40d20b854a00402505541c155000540e5a01c150695103040c0e64501c0c4d00311040e190440120b084d0300e4000d0400701d0411126800250124100701a00b94009034000b54110342c1344001c000340c0207a03903201c00c81c1000341c0c6c04c0741c070450090004089071020520103190055802202e40340c18265182d6880d804242d401a044800c111303208408150203061003400e0042c7e10820320311003c10814020401030141070314082000d00c0c0c2c10003a421031220500d003691044e502c9000045000c0380e450340307007040191200b101c5040740840c05010905c004078064026001e103c106807030644440310884034860080354080407402512030513102d4800001010b10071403050450709405104047c41030701e41a410000d15103003c08000d001c0001140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 988612958 1250 988611708 988611719
    0x30209090a1512050114090309040b180106051b0d0201020d0f0506090a020a030905030403050d020f03070302060a0902010e1309020f190e0c070c1d10050303071112010213030b010f 79
    0x42e1041c16100205220512542e581c2806401030128210001144180340240701c40c0400c000017411030b0600403102880545024404c2c4940740c11441d0340300c504d03c0d8454005000650090b405030060300d41f51110816140c4800f100180b03030220456060026075800140b4a451600e240a501d2040c02900428405420070310003240401c0300040441155680c041102444280700750001c5041a81000440e0340b510f841c0d0410540700d8880190403005449400304181d02011f012081d6080f954042e0045e1009550700c0400c0c0010f4145004228108403803d01040d08130390780c416490001c40c1868500180c401094410300032061141b004540c803030104031411040051000d5110320548100c5400c005040c0c40b041d9000300c03680502d030703001000101ca010021905014020100d1042d0300c034100070f150f00361a04020000e080519028417901504100900c0b03000c150606c2d130743c0c0311a2001800448106242d83d900908a130411080c2060900d07aa48003003042c007141c0e0103a140500000b94490b1211480d24 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 988614208 1250 988612958 988612991
    0xc11010806010f030902060f07080315030c0306041b0b0a020d08070504050604050d02060409020a050a0f0c0c0e070210021c14060d0f3809010b13150b0a030209090a 72
    0xc00c03880815480d812172030210346034901660800301c0145941e0340c50301482e24250318035410490354482c5890055900800754030300064a03211038180640904840d8446442d402c1041196425450f000003004074002290654440246a42900c41e40a0036001403209401040d0040190030031042050620090043d99101e8040f03501319001101d0542c90b0303001d10f2000c07070f82c2401581c3c001450300b8804984045000d41003001001941d4043d55491400580d221058583c4e2070140000382c25003204c11382c14000040310507501c603082081801110000c60803c040344003aa400101441040c030141c850511420000740500c140d191440d000072000c901d40325000c2070100031441d201600d10f00103070034000144078440c4401440d420900e1004542da84401038038a2031000d01100c0154034100003000071700ba040b018424140615002401400030380c00c8010804081d0100b08d40b2522100289135001848400104c000c1500748581d0300c001d6181d115200130030200540042160100c542015007c4602c0c0c98403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 988615458 1250 988614208 988614227
    0xd060b10142212050c0117040506010e04021f09180e0d0c150905070f090c020714130501142d060a12090b04060b0303120a0c11030a0c1101080601 64
    0x1000c07101c00e903803090303408202c0c403100d00c40d8089140c0c6141c44842105102010035505210142a21424001a80c0310050107020508580c050800d40085005010b4030002d0203000e50420f000511a5811031040c1c5040200c201d0300ea05c00c00b001c030700703140002c00c03c0c0e0b07555030b00d4494140c0091808100a103402024540c8503003090140404004000c516207081141c11800f000c01c2881c610000c0200d0241898029550000c2e4001c2c2d642c04800c1282c000783d1031031180510394500b01c4590152504500d01411840780485505005d07610490b1001d03510050040391203118020588003400070080e031092018010700d0300d629102205510780c1b41e01411054003100c02c500d400340e9010394403650303610001c01c001c685e060407040312460751074104103403a41444241000540104e01980b402c00c00406440d04055582c0f0a002002c00f4804000300061494085a8480d0700d11001608004d03250003003101c815420360f17025a0814002c503e01c0c2c0440010b0013100100c2c00319081f000e0800c00104d007480000079105016 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 988616708 1250 988615458 988615477
    0x3270618130b010e040b010c120503010504052409280222030c0b0c1c2613020d060b120f060708010e01090e100509010207020f0306070503011802090d060b1014 70
    0x40711b40306070312240d01c503010300000d05400120245143c0300070b15000f04603500030300c0cc2901c200c0c240000700c0c031110710011038070069000e10710b0b14900d802801030512881d03103001404002240700410104000e09804e400c840b820089420f00145d5031842e48040b0451420103030500f45050205450600029000c190345c00183c5035002c0030030ba00e8440c103044c114648500500b810342164000441c08410981081402d00c5060130800f5110301040c00807502201448200e8039075004545070002000981005042e00d070b59240142800f02d265000940421105250205e071511a80d11001c0280213142c402e1011a80024103854038150a51502e090000b01c1b401c18042e0301c1646503602d0920008900402014030100f02f000070506c80c41c0780c07003c19607000790040b80099000e80c0700c0052000d4145000b165030b5100303040c103440d2181142d0804a6114428410f0804010030581c00c0292a006540c3c00f61219a658810700002c00c09004201c00e01080300134404c052802e00030030309400c080a40041094411215 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 988617958 1250 988616708 988616711
    0xf03150e06012316030807030920130513030818100b060d2d02040f06030e0703050114100501081303050a170103080c010e060903270618130b010e04 65
    0x5100f007020425030040345002034a8440001403080401c3c00189910305014001c1d2940d1407140c0d17441710140c0a413040403500404034100460b611034541407154150013000c2d000b8102208004c211401541151415140c0c0b1140c4d8604a9041c0d04042d80000041ea0005a8000a403801c0e118182d5540d80c8080f081d100c01041a15181e61140c29101d101c15900c6641170002d080c0030054070004424941070a880801c03900ea80e007500c2004201c0c0f1140215812968075034070340c4d10501e2504000b240185442c0c0c3d04020b890007001c0000021600900400d0421000c070002e4a40b50b0a1003540c40c0724503085070344980c1c140b2140108200c514503284175160030407505800c0c49030350350b5050382c005c58003100008454683c1c1c0c00d8100c004800c2c00b40354005461912202d0000304aa00d20034240d0342d13034030300040760071540c958000c01091006180010000e810b1119209540041554030400141140c101a404281d403045103602c1111900d4009000060070507a0340003044114658000203041c000c0d5080100c3c00303039 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 988619208 1250 988617958 988617977
    0x510140405040f0b0603180c03010c08150a030c150917061807050312070c360b0d26130b1809180d02030307080a15090c0f03150e0601 59
    0x141440c2c01c200c15004004242c1c2c1c6c1e480c60180e400c0404c81c0380110307502070180b19800b03000c080f50905205061080200b0f1f02e407410990341e26002020350605852005410056949000000070b10d8032042c900036040da4008001c030b0101c0d02d00001d08554441d840280c100b4090002042c001c1000300303e01f030f0001d0000c074040145001c05400b41c0d1408141d80d12a9400d40700300011181c07140c40760005031119600c520b15889001e03a446104010088000300411000c0481c400070202500c500b100311810980b80b28400b00f00c0342484000076064a907100015140c0524121f426540c04175000c115002805140200b6424240210205c1450b801c0500a14054040018811400c0c004040c0c2507003064000404000903032808a0100d440d1440d2040002d07424450700713201a84250021007500c1c4584101d90303079140950340e0714030f0748000b0b040c00f400e80d0040114440c82c0840c030310302140903d002c80070304c0b502da8400581110000904888525082c0b4000c0c2d220701c1410b014000d0f4101c101c50b0003003002d1804203c10b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 988620458 1250 988619208 988619231
    0x1e070c060f02060c130b1324080c0f0316020a0b01140405091b0d020a08060406090203151302012706051803031303060c0210020c10050106020105070e0108090a1407051014040504 78
    0x1401f507070b00300f540c000c0b903c031120808002000f82d40c0a0a545255903501e5030352184506051240110029441030346001c1c00041c6080007560010f0151200c2e5104660303c020740da85075980134250a801c060604000c00d6030048203401c003802600e800c042c0c124000c104032400500c9060004a43e143c580f841040e01c1e1080000350f5031024032090285c41d0000580d0750170b08040c500038000b4160b07010304074042d0207004840305180036183c0c2e44034403072091003500310117100c1c40e503004448000c0078540d25043ca89548011144402414500b0380c0035100b1901c0b0581d0700c1c090111a41c01c2215007011051299004001200d038807410402c501c42100d40c40000410078010342401a802d00c00210036a6501c1d910201d0302c4041c0038000584202d400b40e180c2c6080107540d0326218100c1c2650303c12251400448e8074182c0c0c0120300d51007209841d07804030419040d0742400c9181d6450305102c5070043c03680c0100b5805008140034a2038844e0a01a0524241c10174400100082403d01050b00a0703118052162307170b44000300e142 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 988621708 1250 988620458 988620487
    0xe090c0a05040e2409090304210503120702010b0a0501022d2a0f0d0f02060d0c110f0c010c060c120915050106030506061e070c060f02060c130b 63
    0x50890f112800803185000603c10401c00c80328581c400004645000c05031a07401c0640081d8000d0b014900510b10341414690300c004404d02c40d56001c1802e035001d00c80324011640074806000c1000090b5808202030520000007403e41d0403a029142c403440152000b0030103070707070002401400c420035449490341c00b10104010b6802845101f01aa0490081708510480300e0080e656003011040b50301c0641b03840c041d800b814007440c0c2d0986200c498029070101c4c000c00100700640c1001c0303003a41c4010261441d08103511114000c2c0c1d004e600140c400f040c018040c1100001d4184848600151141c0c003e1603002090000240099091540901003507a18010f4100762882000714550380340342e070502440b41500b9403400b144145078251107407090501c0c040010031040d201e409a140201e1000742124100000096400c2c20212604000019200104400b0f000126485101e0006162984400300340020324040a810200000c00c80803440000f0400f544071800711151520a84500c090f07100c1d142c190354001902e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 988622958 1250 988621708 988621717
    0x1171306090515090a05060c040609031401060929040e030a0f110d0f02060601021606050901091a0304050d0f0c03030506180c041806050d030e180405010c0305070e090c0a05 76
    0xd02010310304003040b4038038134000b40308262544504200c0b1940ea0300c0c41d990350082c2c02607025210001c0e400490410202d503002000e0f0400e54600c400002d02955030320040011900804400c0840c41e44a1621415011213400f42440c044c1e020384042c8001049001d00d962648a11602841401b0a80b501c158440344034405449013085078000315000006603280207000b000210b1407100041c0b240000080d25540301040fa02e440c100701040300c0303100c1400e11106556540040d0322160401c01d00d102d0014011103000c1002c408141c0094940b65607042900b081400c00d00211003110a000780000d4030704d03000e07030300c15583d010058162500150f00c2d1a07540000e60142205c00e01d008400c101907051101420054000b00125240ca01000a050880c001c1c07860684510b80b06d4594402300c103502c0c11011070b001d00e401c04075048000340f4002c03108201100c00c24481e0402d1300c0540b0781c0e13035640d640c9101c00c58062051503041003035400c140710550b81000c00903c04c250001c001c240c0d004c00101380d8040450045080d02c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 988624208 1250 988622958 988622983
    0xe040f0e0f010c45060e04050105040b0d030f02010209030316030801050102060c07020f1804151a01021b060c0d0504030c0609080c10021e0105040c241107091a011713060905 76
    0x51300c003503030311400184003061106031944981d260038000159880c2c03074411100d0802016012070b40d00b41c40380d1400d0314000c40000311030301595000c128001003681d0034070042000181b0003543e035000b40750504004002d040140c1240b8113641c008418440f007812076909460005604a8980703102c54840d102081c000f24003072000620f405a0402400b00300110b40d25070540c40c0f50710010401480e20054000c1d81081c0003480c1603805072300040710035182a0404120302c010100d010b40500c3ca419070503401d452030310039011013100c00540041400d00400c140084800700901c980d291140c030b0242400502e98548007400e02c004d00c1910709100380141d0900a01c5400404805055218000c00951111030f000c1d00c81201c0490301d610b00001d0124050070301c1203010b84030910a4480007944200b802e01a9040500240000200e108000d0002a201458000c209408241e0007894680400314400504401a0300010380c081e0035046040002e0f0683e4401c9000d02513801c00d50204511401d420440d0a200481d42c2c070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 988625458 1250 988624208 988624337
    0x8090f060d050a0c0f1202130308040b031905160c0c2d093803100c030c0c0b0604020702010e1309030f0215070e040f0e0f010c 56
    0x220380100301c80e48000d1140d8000001070001c80d032100d40440324036115024010204c6c5003000c94102d41a01980030b080c0100c08042c00b00740058403512115150b070010f074841002d110f400030030001c1072000c461111064500710041840a810452030b014042c41502c55040304000c446200c00081c011924040c00003000c10b806828807040d114200720b41c0400d10103801e0002260607800c0007508101d18030070001c0d905c9104241c00d0b011101c40058604c6c40901d4065a1120308002c0800b111554080c0f05854020810141c0051f00007440440a07040d5450004004207200300c0040e4403010402c0f08008030ba100c2c004440041e640d0074503100503140d00c900115695041225032000403482d03541c540c48104005c0c041d403211a9a40e000e040d00700d90b14910381025001302000070000c1a41703540990b0320000d42c0c0d8402800803400044281c4202c04a803c2300170340103d00d601594812104003428442c0038442c3c81e03246084040307181c00c1404109a40219012181d44d1400c140401c0e00304415404004140004a540c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 988626708 1250 988625458 988625467
    0x60d021c020904060b16060507020703061a0f030d0903080903030f120916030503070201120212040506270606060a02070503060f0f060a03020d0f0816080408060108060603070308090f06 81
    0xd101000307400007207245000780c1c40d200001c41c00d0214041a03450003044010740441d124043e0b922140074000203461030056111301c07600480045c5c500e015840b005c09010b48143c8108990314104681d011243c51118001d400c0000b40c880400e9008035580c064070381007060959a24030f0140843c4c0f66105030b86000006180103d521003090310040d280a020340e16800854410010302490486403100034480140a58400c201c0c8100550240420482d02010903170014100700c48080755118914040302c085400d5002081004514034030050a00f1100a900a03001c203c0e14182d07180c0e9548240242042e4822074000c100c040159208009580c060140038040e168141030070340702e108841d003080c1d41070841c61040300001500ca0074034440110851303030000c00e940140b5030141c98121279048182420758048808000040056000d8080450110310a07000c0d950b4462601d8400703410400181c202c1c2c8403d0704100305201055400040890641e03070400e607095030302c202e1032000860302d02d80480030a4100e41c0104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 988627958 1250 988626708 988626757
    0xc07030e1f03200903070909020402040e011202030d0e011b140f0d120209090a090c0f0b120c04080703171e070204180302062a0409090c08011a060d02 66
    0x3000581006803012084a42100380400041a4000c0c2a2441c5c0c0561108800b0004211190058031085001800040c98140c4903051045050b1f401d030001d0b4030307642220485c0340450804100760822001c080c070f00060300d07402000008100c8441c1c3e00c1c100310281094070004080c030a41c0b0940050211a4000b1200c1071030868600d03e0300c42d20342c03030960341c0400c0c4200e805811207201c50007201c9400100420210b01642c41042e4600101041d61094a4010000802080117503000810300080c0c41c0e01c4d04901c0d101c0e9080b1601c1c07041b01c0b90040c10ba07a2080000d000c100308500740010171500780e130b501900c0110b4100307028401c4190ba00030031040020301100c2d072400b0481c500c200c4000b031003054000d5600740100746040812080d0035086043c01401070307100000150303035421507000c040d683c8140c04491240c520010351035816680c000c2d13080001d103941d454030083e00700003881400c6401081580300900007103101600941ca1070b2805009203000b0240007d40101499466040b519402417492038010340386c4031320 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 988629208 1250 988627958 988627961
    0x1210050a0c18030b01380c070504060305070308071b03030c1110020c090a0b120c090115051218060907050a0902250f120518010302030c07030e1f03 65
    0x11140701180c0c8140109040a081075596400d590304042c45800b564a8504240d600c0c8003141541301d001c0061640d0501d4001d1000085c90740d00000e4600540c40d0304442d040d807400c01800da4400c0e4826071900d801040002e8020680004072034010145a8840780c8906045c0c028011607031001094201c1104040109a001000100313014020098a412121020140400e12001c0c00c00c01015038002e01c25000545040005158415404007003c1184526400400c8040b240d00c0607021003908031000c1c040e01410450301142c014558614240112200f20380c0c0a82640326001240040003495400078000010368106640113440110403542545400148183c941010340100740c0f01c3c0c0a1404009251401c6009449401854000350082401c1e8142165020440d28804070b926000507001a808900b0008034880f0b0070b0300b540c582d55038450044401352075003400700da03c0030b050510500501c102000000290340c2d13501d5141c1004030a001ca800002084da500c04511500c504d4080d40403600f803954503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 988630458 1250 988629208 988629221
    0x90a15290d02280e0d02090604050714070515220605061903050109110603240d08030c03010303030624210204140306130b1b0f0d0204151d1210050a 65
    0x560307402040c00c060404001e2200c2160038061f50140b024000b20707105161a50100d074105a80e03040c900c40d1159403105031841782d04504420394064000b0310b0940900703003080c8002c0f0f0b031041091240c206891000c50150504ac0c1c04020058a00da5807000060382540340d09050b05482c011a022a004955a924010f40070303200440d02150609580d000c803041c2c80c10a40181d81c0503040c000b00d02010342d00414a1a40f0b4550014034445d4003901c8440c2c0100851245030080d030207001200049652036046003806016900b407170740882c800044540c1032107030110001070443c00c2c4c9185498080300d100300b40415101c40d2591840c540004900c001000501100703665660079142030183c059408650b2890300040000c48100d0026003021000e4001a206112058203c42e190322021416420254400f441d1806600301e0807504d10303072950020701805140c1c04142e101402c03010b18a0424200404030188010414200030614020411070249a03000842801100308230389035503c00b00b21610740f032082800034084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 988631708 1250 988630458 988630537
    0x1e1b0302150c030d0216050d030e06060d03050d090309031403030108120d0912030f060e0c0f0c07030525080d0c080904060b030a0b04060501050414061305090a15290d02 74
    0x40303414120960f40030b07000c0d01000c005400081c20b01d0755103100c2400dc0f50350205404030100501003148407040d032030703d1180c0c04895010303980d450100c60852400d000e5030015594081d076075074007c1c0010070007817800007041c15840a1000c0d40b147c803161900c0310a8090240e0341001094410442800c5086581c10f80c080c42078000544814402c855503074444911100060700c512040c40c1040115001d510b0030b80d0000e04440340103004507150f95550381c0b100c5003411422172103024000e10300c9240c403040a0307046094202a201c0c2e900139010848807a4400f0b00241150304c4020559140410444200e9a41d503108400400007800f07840d90b41d2610700031042c000c0c088140039501c42c1e071502c840401c0c42d510a90956040c1c503034140315412525079190801c03081d5000b100000d200c1004964005c039858681d02c101c41c2c024048a00040313004a003843c4200141c0d251a00005482140404071f00e07280c84c94003209002c0b0103040340c0c00355a280082100c0c2000b0f442500ca84000070b5102d0041c0c035511841c0c1d250382d0344020f80d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 988632958 1250 988631708 988631713
    0x40609080c0a061a061312030516120212161221021308010509030304061806090b0402010e03010c02031b071502030c010c08040b04080306010207031e1b0302150c030d021605 76
    0x84c01104200c214010000c41c2442c580d1011400c1c4500343e220b88042e06a00c0c0642401800c00ea906000c00088000500c01160300c00c240c9524403424640421002d070000c001055039508120f420300764008108038401028103154420f20380001420301415012180301c081d0f080c0b92064980c1e040704480a9880032031a11120038401e80000303120801032245600460108010790f1071622140c03145e01c05000c01040030081e210b5000800350000d0a148500002c0d0343c41003645400910b01781c000502295290a501c901990401c1048601c55502104486514949026540e01d5076a20706030790b1f140030125006a4070740300c0d1850480c400f5135000009080700b414401c000f40703e15030202b242200d00341c40c20b45000f0800c00c0500302103000079a07214061680058107104503050982c0d644c403101d00200b0390360310301034003d10718005c0c0c0c80900c0340b4850004c002940d80580120b4851555002c2583d280008010520780e41c00814045010b1109108880191015402c29525440c40c0c1c4d01d89034421007004401c68861 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 988634208 1250 988632958 988633001
    0xc1107090e0c06130608041103010903121401060806010f120c08040b07030c0c06020714010504260c0a080903120a0302190201090c03021005120406020406170f040609080c0a06 77
    0x1450f0901c02c50b44d4007030100710b01803441032800a00345c07400e48000d40101c034952900c0d0701264003a2824031406d407105019581c0c86400c1503030300522404071079058112040140d03800c0c0c0140549604150303490380084080c40c180f010041000e004540b0364189100f00050213042608003542181d0011065000701d0140340500450340f1860030613001c0b2900213207188003258480b240d00010421580c0a8041c01d03016240c0d200380341329643c03440750031114102e4007160b81c940124101d000c04261045920300d220912080c1c00e1403c0d90f100b520703941c0d03000d51000c000c046a400041c0b2407550b0700e00b40003031503c100780ea690080e1195041c42c0c0103400b80d003000725225660071048080054591050181d40015a0032040b1071090390b007940c00344604081103d0808003881010080000300c007603d4036070306110314000c4100503244c9007010760040a00400b46000c00101c1003050034880024058002903401c103502160006803441285490103440c0149004404240200380c0800d00b400110340150303801922aa610307a600 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 988635458 1250 988634208 988634233
    0x30c0304030e060711060f25140102040311120705031f050f06061204081603020717032704060521060c0c07270c110607051c0c1107090e 60
    0x4900403100068200140c80c1211761803414200004c00d000e1403000c0c3e038036182013000030704145a42ea540e444442004102060101800031411081ca000e074540303002545860300e942c4503800dc000e09840180d05c503002400411012540c100607010080c02c002e0b040e540041140449441000400c13004080d0f51420030000074444809912040d01ca4240101031508001a800c0070546540380100300b00c62540c030030819681095620080d10540610a6008090b00c90038500c80c8034020406443c26201030780180300ca48400d005d116200c1c0820145041640048072107000010081c180a074031858009a45a100c1e1003260715550b40d00c0a1b82c015078045918585540700e22036000e02c100900c60700d06030404181400468003039803180302c95400c180b11850240c81c000f1102400c4800940c0500c0109040d0061208044002c0c4035a50380800d140c20542e00341107100201140b107800100300799a0b820750b10b81e0f4406105008914102031020b11008641031192200e940380000d100c507820741c4205100380f245440381c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 988636708 1250 988635458 988635469
    0x80604090f0f02040b031b1813031211070b061e010503070c02010c05070b03040b100303120f0213151b021309151b030b0105090907120f02030c0304030e 67
    0x16081c0c0c0014030700210380c100d4072400c500510182049900545420740c0d1001384d80e00300842541c001c0218490030030000b0840c101b00c020f95480c0181c0041111220030042d6202995442024954140c101080354010107030007107004052240140b66410004111401800300c2a20040d10400c02038549003608480b0114002b006200301c00018005442040024100d600c00c000045001d841030424950082e401e6276054100314040e08902c0d10f20402104000500820b640d40c540c000c044549042402d500715100100000450313161081450340350700c00790710101580c0d0304640c00049161008044a51158058003015546207803440010301c400328030058025407890507003071440d80100701d03820b81c00c0c2586501010740341228060b81c0d40300a0400c078402c81c10143c01110035000d6000c001304c0d40800548009012100300001003030401c903007400080056164020b40c581c0046490501c07030411495075444070054401c94a040800302d00101c1030050442031200518041c40c841e85440c03c007042c03423009210 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 988637958 1250 988636708 988636721
    0x60b0315010e211002030f340c031e0f080903130302090702010605120f07060c0b1506270f060306090f04050a3906050a11070e0705030403080604 64
    0x1548050f080c00c04022040200500c00e5209100405944003024802d50301c004903001181c50086003801d80c070401000320108082d40c4100707a040c80080841c582c0958500c95000001d91651040c41032040f40300b03003898069080f00c3d10f401c110050b00c200c0c5881188004040140c40ca03201004140074801058540c02c0200903165000c6286803030a200c989182c003000002c10001c0d14400940d5603c62001c01d250b140e1006128140c0d40c44001851035501450b10140352035107030b0b409003081003c0d501006001904400c1456081401500b0000c2c000c124007000502511a441d0100c8000310340d48010014016034501c1131942801c111070b490084100c8206010052004885169100b6000c0000035000c040c1800e160390050700803400c481c4550800e58078401c40c442c821107201d0310032603a5108400e081c8000c3c0c4803030078081545101d40c000d0a2400760003526901522300d640007400300c03002c50301c034261f8000c115030390080c910080c0e12041420450380181c49607000b03507001d0380000d0b28240000d2060624dc0a00c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 988639208 1250 988637958 988637987
    0xa0207021e13022502040e2d06160c030311191101060821070f0f060b030c0a09110f18011d0d06020304081909090b0306151210060b031501 61
    0x1284481d48001c90004d0f94010402e049038025a02c0c0d02441d5401802c01008034000d004030072083c002040315000c6070b558a0551040c100b1540400c0802c00120b2254010b07140d0180a401d1010b40c1061601e42500a480c000517880e070500c00108201c0e186c00d0008135800070b0800c19403150685040000840b90a070741d82800b0b80001e40c0d00c003040c80118013908051142501061160950418130541c1d1100710221072540c2c151a4400c01810303003018440c8070320440c04840070850051014608107000304682d083d551241322501940c900b07540a05621000440e00c0c450b60007000c3d9992503aa0641981f070002282c00064006544090130316450115020201c800e0031008040c9400075040d43e031044041d610082044a15807000c1c001c510700048001110b44c801c85164844d1541d65050041d00d4007141d0303081485074420b603c5036041c0a40e084440c5040c512842c0140ea00081300c0c407181c00154900849000098541898442c0c0015079007407240c0558081e414624442075854a2100110341c40080d99185 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 988640458 1250 988639208 988639237
    0xc0806040c09031208091e010b010914011409060c0a050a21090306020f04030f030225050603190b031c0e0901061b020f03030a200106060f03050a0207021e1302 70
    0x42204ea0f4040c100d501d901102c02000c40c0d55034403c4c41c00c01d000c1c01d840c204031502180c2d103d0300040c10942e00a00c080b00a0700254000c004d01014402c002402e030b0b404a4032002d60403c00146200700380e21140112000c00303a42c1021240154030a10b01240e45010308076056074420301c0010401c0000c40414407007900142c0f0b940d612032446095445001c000d40c011401d040d4014801c000004c0090302c10a040306000e8000e801910400700c20080c00750070700d901c56a520755080100801444181d844c5010b890f00407400c0580303041e0b00c440880b0300c4402849001c0140360305104080150f441c002624004c0300251807a0398980700c3d224100f03c01d104419a00780207400105402c19010101c03020600310701c1d0003030f81c0020b00840321555164046400e65220500c0b043c001071a8400300c501c44401200c0500d1042803a100030403a042c902a0010440910210b48108160302e403400700d600d05a030350701510746003031300100002c540d61013840d541d92000900070103881c0114441e8680f550071007420310035180c0300c800080343d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 988641708 1250 988640458 988640483
    0x181d060307051005030f101208070b0c033919170f0f0714030109020a14070201050f070309050319050c03011b0f02071d01031406040f06021c0c0806040c0903 69
    0x34107035144980140040103185003007c000039004e00106113541a04e00800105665240c14202009500d40040c045c00c1c4180c800c20500c9800400002c41e0105400b600307880c00091045c5106c48a0340d0821a419800da9450100d04143c1070b105480c1030386501c13a0389c1d4a560805001d4110101000c2c8070841d0600840741c01c01000910403040c800d00c0d00c3d800300e400e03d4031001804c01c1b0300307075035031950030070313049070b40c44503804112604040d40140107141e9103084070208506020345980024210710500702000d031642c030702103190700401d801006800d010b408014280c03901c5a1010780b268094400d0745005551178070903072607240d042c0d050622401c1ca52280400504410802d014400d40e040100400c4041c2113200f00c88000501c080300c0c50f41c403408840c541d1000003441d495414505040c0340980da00000070341104d0140800518480c4a1401c90341e4042000345e281c004842190304046040c43d0820200c5090030340b01c0c0e14903036100b010544102012602000180c030061001c84150495010040c2201003045 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 988642958 1250 988641708 988641721
    0x603050114040504150e06070e0102060f0c160f0615050f030715050d02121609060203090f040e010e01150b04030203030d020c0c0d03020d0207090b0d03181d06030705100503 76
    0x8001d2944507004081402d440441c000448084032040c46e61449140c0009091100440d80900045040c00d000d20061005081041030503000c0400500181107007030300094103009554640800a00f95038214074038200864140c18010068109103201e0f103400ca804007030206440c50505008038103100c0c00340040021900707003605181c05880c40c12042d01400424028441035900780c0c0001e14500c010503881e60704a051840c6120541c02c0003111040c28444000020720000ea40081540d10144c812256400c80d42d0340b00000c10700034520000c036050594209100c416004c01d05400950f13203200700850301010341355107104036100fa00842c0002541a081003084502114154002d01498440c80c000d0b0f40d8100341c1d203800107171002c4500c5e10450158000042c200142601070294100a0007404014001c480380000042c0c3c45081c2510b00405102000b0312134206010900510310180c01c1c401044104403401d04000718116008880c03182c46481400f0020840341481e07424240302ca400394480904584504 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 988644208 1250 988642958 988642961
    0x1507050d1e031a0a1818020d06050606311a0d0b122b0e18071701260a020a06050318150612150604111909050307060305011404 56
    0x400c4106803200101c16103c11540d00c105814000303000381004064a02001002c240c02c0d03c8240c0c0c000c50202e01000300d00c0004d80c848505468805a00110009850351048000341d214000c403402413040780a0060350800020714040381c1112484040c1d850901182e40703000d1a00102100c400302e0024810074003c910f5501400d41000410b03040c01401c281d01c40c00c0011000e071602c100c1742c40028000007804242a61a0740c550005d1500c914503260158991024601040e02811100e10401113011080c00007010319110703410000130641b10920815803543e54801028201d078102111400846103070510070b0720010000380f81d9071040e9014156804e4203103401011340d140e401c010b2007501d903131103480d030745440f0540d00744100c4011104008000e192401c0240c2072180815000e200d68056501c16a0b10911040d13001002c950301400c11074020400440c042d050f40b8031801030b02c40a2841d294001044d42d040d40c3c21503607078011f84100381c0881b0200b40d51918110b00f501c500303106100e03100c3d05422540340d041c10036 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 988645458 1250 988644208 988644221
    0x4090c03020918190504050a030c1109070f090e160503040201050d02040e0a06050607021f02101b1e0e04020f042c0901060815151507050d1e03 63
    0x1810010b0600c0d105001045004070075207032202c4540d1031a01082881d10313000f030b004000d06411120420644c40d25680705c80d5210b11405000c0e0501000107124001c002104e0702c50f8090b058043c1806031942021130f0086c00300c011600c54400804c501711404120301300458100781c4941007000050842c0403090006450a52000e88282e0402000300044044804030780000c0c4014074001c1074664243c076003181c202c1e040f2031440d000a403064204028a4015a403060704030f101d241054600b03c3c0d149170200380180d1070100e40c48120401f40381048040000120f005803581e6004406407140b034010305241d407255030041114442c42003c520400000308035802d00303a01400b400d0100d0700840b0b24040d1200161040500c4687c410058424101c020b04280c10061f000307242c016021000034003003141030003c03058030b50624181c1107a0940b40c0600191a46007000c0e4607442c402c00180a24018101c4214601d0140d030010606880c00e02c5092850315a051003a007900003400040c070f001c480c3d1401c0684084020701007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 988646708 1250 988645458 988645481
    0xd14011203020312070e18060a05040c020d030507030e0d0801261203060415080d200c040e030409060608160e0a030b0a1d01090515010b0f070804080303041505100b0409 74
    0x20302c180e03551f91248190300c0d298190110100c00503140003000c2003602400f50b080640101d08102043c030000f1340005156100c03101d142004551035843c20002c800518a003d690354a5200703840d45142c5880d04419024140c1d9600d0303114500711130f000e0405a00e50f40c58010034182075440b40b4000449410040003a50b04800c00800100c2c64901c00070f01c10156041e01e4004440740d40098801c0c0e4030254018410800404000e040c0320158034211490907220003031101d01c07901594841c51007508400e820301c1101c028001202d010001c8a46620004240c4402100c1c0181441c4481291015480c0540c084940b91640141a81042802c2d81d07141c1d452080301404210360345480f100900408500048040e06001d009400040d0f07543d03c6043c030130b140c610070340e241c041401c44800042c031900750081c003115251130f101c000450f681d401610701100c0501c110351014040740004028441004001d40842c803025115a0061000d0f0304c81e0061201c0940d01407103088543c1e8400c1200300200d09498014400516 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 988647958 1250 988646708 988646717
    0x61e050901210f060f1a030105010e060112110708120a090c031e0f0b0601090905060310090302030f0708040e06041b0e0118081507110a0b060a0306020d1401120302031207 75
    0x16084e070703203103410343c0d030300d90f40040310b4640300c5203641c07407149550648190302c000890080c000b6515210203000d1a90700a08102d04210380340c03914064070685908a10890a401200e0799074510443c1884070703207604407240f01b8003001c815502251740c18030203008100d03926802c08808003042c2d285559006403415001c0342d00d09020b41a00110740070031090500b02042d280a9036844c58149490000100114186d41002d80c1141c41c1c8010b01400f0b46000900b080d4a1040820019134106942004da1550041c0c40640006401c0003078454200002000030703100b00c44620790010601e40f220000c0000b681c1110701069200040c1010b0519154400c040d4402c5840d0b060400500c0e2200d07500e0002051005600400c1c000e44c4042c2455200020b00107802d540003000745040c1d03880e098551011900d51081c900d028080e01460b40c081a026038510740070800556205208560790140748076900007419002d0b0044d008440c1c0c2c84000280c05404a45210704c261381540a10318100c202d000c01c0600f400054528002c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 988649208 1250 988647958 988647983
    0x703021308100609050a060806011203140408280201020a0303320906060f0d150f0207050c031501050a030212030c01050f040b0c040b0f1c061e05090121 67
    0x4424007080c060700d810100003003403060404d081c440980314054440c1c50070a02e0804100000c0c00c01003441810340700c03094180d552111703003802d003280ca00c0700c0e2a04c40345002e940017400055a440001e00019007400b007020702d8076081209280c90111b00340c0b11601a02581084550f180003d02c82d1340041c010000c1b030071a00000401d071803038031341d036100507506402c00002d00c19082c454481e008002480d4170180c2192409080c7c5000c2003c20002c3e01c00080c0200184982801a1042c0f2802d0f00124041208880119111303207240c00c1c50b540c2e0b0742600245e240640624403030200005851000030341a078801400c417440c841c6ca564213000c40394076204a48035060206100d003e410740000e0007000d0007401d140805c82842d04180c02c00c07c801d41c80c041c104642e404001c102c05c1044150f001c0a60b00181c00e1054543e445a190440700301da645480151602200c5c0350800c08a540008040b45040c0c03041e1205042601545840610030014404e00442503010054400221203076400740058402600c20f1074074000742c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 988650458 1250 988649208 988649219
    0x11090a0e0327040b011407110333070516030309061d1513031d030a080307031d0309040b0a1a031501032c0a050a05010f0b0a0e07030213 60
    0x39904842e40400020340440d2480c1014890704a04080340d01048504010711407203200040e01c0f1456006c0400107000c004241c1c2414014040da050204420150690306846180d001030382118044402407103828004003030240c003410362511094440e9001c1d865031858507550342c0c1c500070b03503c2d0341a40446c05c0584a00d501000612240200711010100f0155880040800c4020303500305038400021010011089040084c9480b940200d00c1d1580e0b05170410500c100c132030f10b10140306a65554012500b40c80f80040000c100145003004521440e50b41d0703000c00103c1110740601207034020703a00080d0031907481481060b209280c00e074011143c148005104004655503442d5500d804410b204804005001c080100709101c94214000440e500007460100b000c13400c40e424101c6565150b42072035a1011400410141c444410003c1c2c1c0c0d4800e81010445180c26160714026018082080700c8041e080d0420014500038208031035400f040c4c92080c2a0341a4a940d0721341d045009402c1781102142100d4141c20010700b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 988651708 1250 988650458 988650463
    0xa120e0d0c0f06020c030d230c2d0f060a0e070f15020705401d21030a0e0c15070624030f08090a2d0311090a0e 49
    0x100b0010401c1c00d0401d240c04806801e010440c112a030003500480e4454600d1a84503ca006100c2c61108103004030401e41c0d40c2d004920b000321011910b00d0701c502c0100e0b04402401805040301c95440c0c04410440045020b0342c3c90300c410b80c100c40c0c250658070450100b6003034003194002c0b104200d10402251102541c404614100c1c2a80c0d91140078000da602e04602e0b403590781404064050142640e81e0001c2d1080044407949950591005620428038000c0000e940f0300c01c40c612003032154080c801480090164031850a0051003002d031000d862003a61501e4071000646000300341802c002c00503443c190341d01c244240000d04581c1d14209501e00401c2e00c1840d50303a0b40d000181c1403c0107401d58954071000146080e2044a404081107040700c1510085900603180004600054a074428585d4644074414500704045014060419078018030000011410801001314084844842c084410710300d00e2034550b0610120041c0006010b01d120b00a01030700609142d01072070b820403025000000c0305607548a8160 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 988652958 1250 988651708 988651733
    0x403140a1a07090803090d1b05030102040617010e070804290708070219020310180804031101080a09020a141f02010e01060506130608040f0606080312090a120e0d 71
    0x180c5000241d000d00030007561044454020b80128001036250000010000c0c904c19201c8000a01000301c4440c900207002d03001505100800014000759111502c4200181610300e0000076402100130080000030343d28035110240e805028140c5038a94192155210001c00264810b56900031500b1180c80000115610100070300c44c5c200c070350740c21741d6508166000a003401d00c91b0883e0b048150104640c0b03030140c1d030081342d49540d007212000000380e4210703240c04c4a8649011a40301400c41c100101d800810310074120319a2410a40907682c1c103459035940d01c92002100c14180d0b01079044000e1000a02c43c07008040303e014082880100100c0104103100d403018015805e03100d0b1600143d4680702d0310074114500340140c01c003808040303445a090003035134859000400f030036120311000c00c6951030200c0d0134041241c03c001d05942d00240e05115294551240d642d0f070307900080c00c1c24800a08040010f81112021410034900341d07005001203035021380d1303501c1102c41c60369241410794029111480c203000102c0216221 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 988654208 1250 988652958 988652993
    0xf040803130b042d0201020c0915060403260f041203030905060406090c050d08120711161e03050c1002030c03040f150305281b05030f090309060403140a 67
    0x60400201035031050112102c001c0d0b0040319091410213040050b80c011901e40f002020584410040750740d8240000501d0403040c869540100c4c0004010080c08101d400d809001230007107000c010000201c0d14005101d1060030000560f0480610062040c0b40c151110621094068503001c00c14030040e440d06401c0c40b00950f4112101035440580d442001318600e5200300500040b500c09181510b2a02c4102080c45120310494a01c1c0400c8000364030780740101c0d0a0390030180d000c8204d803c403000940c281090600725000b0028051460001032440560040484007965404400382a405151070103100f20001c1c076883c5201580018000084260030400c06407005142a4400c901003910b42201805209503603c40c500402d070410041000e5200c14000082002c44040c2100500c880d030660b0000042c211191030501443c4102e041c1084071b5444000f45004d0441070803060038913103031781041d659684202038529412400070320003000820780002c046001003140d0000e9071221413055507010407000070341035071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 988655458 1250 988654208 988654223
    0x60b0d150504021305010b0702010513030f0803070e150d0b010c02150703031a2404090203010608060306070f0f0e12010504080c0d0c050c060c0a141c080f040803130b04 74
    0xb0031080d840c00d00d028055034800003104200550625100c01010b114030040a4184040090280828014620480300554200d0791510145d8040c0c40c010340c050740141c1e00f600c001074490194130700628050301e0707810510000002c058138050004034500c02a08510032054140300c41c185402c00036868a17000c101610750303440000d982c1c456540ca0007908407840301d100002400a03640a46100c0d840c0c52f40590744554050301048031459184a0007946807045400480c41c082c0040000074070940c0060019011b1030085058910b2543ca86104441201041c200030b80003a4403e400d140c08980501588000300300d000d440920313a0b00e4000305840c00d560041d0350484802c8000039071259140824851482070300b5461405600341c4c05142c456550391202c085100748103480000d091010540300704040301125034060031040604284081890f103e40000000c03044486056000050b8076100710031040c0b00d00f81e4044442c0303a07519030752504da120b03420041100d00d01c6400b41803a0b0002c500040c0507284503d100302403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 988656708 1250 988655458 988655461
    0x71d030708100e0a02061e0c030c0a020103110702150f04051e030d09180507050705060a1a101205060a0302150406120209030c010c02061b0a05070806060d060b0d1505 73
    0x34030b0002c030b50301c2070781419168000905103001030342e80704200c40a00229000d024480c0204001c40c0b60b4912a080502880d84070000d200303e10030380f01040c0045e400d0b000342c808108652581c645180c10340700f40c03480294010401c03000203e004a444024280883d07000c49200d05060b03c0d82d0110310810340022104803a03c9140501c06800e00c0d041007040b100800e585411101207280c84505183c10040d0505c03490780c5a120780005620511400586041e1a0440c084500c2d5081000d040030040601c05019a070311004411008628101718407994840c52840e80c074900000e881d003a8881c014400508200c1d0b01140704035001000d41d9889400780400404040761079a19403400501800c03081d402217204003903600600001d1600e9401150440c039280081c00c1c1110340150b50701c00288a846900740070074424440b1282d24501c0300000841e5a5014860130445048039210b0581079a1000704456803a404000b50040d000020700070b030401c10744078070302910802d400f07180c903134650110f499404120310700300350f8036030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 988657958 1250 988656708 988656733
    0x417040b070c2112020c090a02030603010c03020309032a120a030605010905180a0623040e06010f15030f051501030c0327080d230a1103071d030708 65
    0x2d80500007040c181143d6403102e480101001c600440e07507900508120902c5000640007030091140f0582c05000400c81c02c0c0354605500c80500940013600c03428080c0d0b291031070040303030b450191080303d02503420440114103042450541e84983c80290482e000c01c071910310f00c41030750404108994046804c110b00c403561140c2d500c0e040107003190350684c030041c10002504020061a120942c29280040858821007001d80d10100c1c4e800181031507612044001d4035266091002040c0e4803003151801030300325014441860040380b410b90320442800b89030314903207250404200d5801c10b203d8150034005941004a042610003040808440084401c0742100e00d01e46552081580d2510507090501c80300d040400603404030800c00c1da804614100c5404100754890410340602181e6070503194005035041c030900c03030f00c2c464600c003e03c20b040440654004000d0400070441c2400300b40a00018940e20310005400e41d5144a0f013242d020f902040f5488086510f0066089a03840070f004020107441540028013484181c107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 988659208 1250 988657958 988657973
    0x120c05190306170a0b0103030806010e03150105030106052422060305041a100e07110105010f090b030f0330040c03050f010c020606060904061e140a03020f01080417040b07 75
    0x6101e00f02c3e6400400003c3d00141442c201d00341903d4141c54140d9007503032800016200840e20101165241c03041580d800f281e44c5007c80035034180d82c0203400a100306d40d516800d21840485a12501001382f078008051258141c181014200000004408094107262940032410040e80741c0c2210001039207540030403040c001c280803121902c600300c0e015034440b03203002078490000c0300c16401a2000034851101185c0b00a00c030b481c098180880c131400800172960745859002104c09248a03030750080b42068402d4405140100d01e6078200d860a10240d841d01c04402000d00c04210703003003122045188403002a80b0f200c810314684604c580e10400420390024118180540ba00d014604200880c1e13042802c01000c9542c0441c000390800303000d4604544030506100050003030b140b035403c402441c00c60140c2d80c01c0e001104000c02021204039820320300f034084845043c400000000d00010790040f4000101642e6540710703401d80da9109000d2140b1504060211314140032560080c0d01840441001041c0d002c1401040d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 988660458 1250 988659208 988659239
    0x803030a140403020a02011808010f02030a050705070b192918060f010c170c0a031806051611030f010b030f0d020c130e0a0614130201120c05190306 65
    0x10412400d00724a45558001c0d07552485a900034100080e41c03a01405030359441003580b000d41a91310003800014038402c4604001c0d0800c441e5900103504040c045506c05000d0011100342c02c2c2c0003c1e40361180e40d202c526403000c0442c041c3c4c003180f5943ea6031203000400b000c100b52255040c543c42030740c04107002440701002608400e0682c0001012035150500840e55106403003402c1c3d104083c200030701070142d43d040001184004112941001e01c000994401854020451040d258840e071625036040080c85c0204264081e140100c40120b4410007588220460b117600d084106441000607807008031004020074244a0f203a1018409070791aa0400c0c40185818094a011284580001c3c81003610a00c8000c1da100034080d1001e01409000d0103246810034550448400304003d00d04440701020349180c980000c0c200901a410070b01515008280e4152072001c14548494050350b804241c000151602001030000003900828030800304990340b5462044800d0401500300f42c1c0300040c0c558035008041064121 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 988661708 1250 988660458 988660481
    0x9150801151101020c0d080121051002030612010603060209010311070b1f030f030503040b0a051311010e0301050406090606050d210e0913060605010509060f090f09010803030a 77
    0x55500601003440d42000104206140380ba0035620320003a40c01e564024480c10314a41c6040c01003400b200c104ea5040082c1c2ca0484100c0b80c3c80d80e41403101510000f408607800c81004180b034112401c44e110700390082d000f82d070b00154010704000d0381107002c0c4801402c407180c1e54011601d2503004900f00902e503801d8030800754250041034540745050304681d03c8403808200240781005110640c01b0f250050104208a08043c5501081c14580d2961608000c2c01c04d40040700c08452140c8200000307005806607006841c020b0702e26001d4904501110394443d20511b0500e03594a041040740d6041010710381d024020140114014040000c0a08c410300b40841034a6a98005500892140810a0004809071841146015030014440705513648100486221100b4a03d96134811762180c20b00400c40600d07042d40c841d59106e400c081000030703512401511035000e2007910710b80c481c0d424000012484220340003001e9085000b0402000820800001142c28000b0382001c0302076031000c002c101800172540b18100100740e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 988662958 1250 988661708 988661717
    0x100348050d020f040c140403110306060a0303021903020319030506040e03040605070303021c14070f03050106090b0708130f0303030e12030a020d090213091b0515030712020a0915 78
    0x8070a80101d02481c90b12207603180201c1c0e0b90401e403901d103807140a5202e1030000701d11080707503119502d003400760340c01c11500c091314424011880030030010320f080000d02d4101da0b4160042c0c80d00d24003c85c140039007038841d800d0590650204100e500550029540024940d04036500c3c005100d080000034001103d0065401415a5100300003e0166035008403d503590140d051070301503a01c040c0c5050711059400c02d60340d507401ca2414803078080c002d2150245150b108101a6490b203c0c80f50302c065040342a41c200b0310412000c00d410b201c05004516039140280401ca008408040c07501c41030b82c0c11f413905059940d01c1414000307480101881019403500950400340f5002c00200ba00c509618040d80c41c510014200c800e5941d400181c92020100703e401c54941c0f1a001040c0300100c080e248000400791900305130803a421149543c0c0000c80106c00c40020059600151000c01c1140d00110140440d51010b041c000c140241c0c0c074101c0e90000a0741c001028000301e295102a00c041c604040c00c01600c0e100004c000900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 988664208 1250 988662958 988662979
    0x1b030c121104051305300a11151f050a061103040305071e08030a05091c051e07060912230f01152112030b09010f03120810034805 57
    0x16210486c3e02c41c4991070441740a40e2291811810340d03049006491500941c09243c200c0d00d0240380b0180305034401d51200903001c9190f26540e01d02c600402481c094554031495440051040b140b0031000019114002c2d4202c91815071240c4402d417030030406520460b00364181c190005501c801a2845e603006080c00d43c015410300c0114074002e00f96000d842500303801403034904040c000201742c083c0000d00d5150848161444840e2104020708110310104a99000703206249000524612039000c11003140d000c0e40000840d6161a070307034051500c50080703280310001402d040030381d0034074401e01000c0c00300005c0704000a80c2c10100d009280307501700c69610030f400c44800e040d041600301840e0a00340c60000da2100c405007a1140b0018164000c0010362902e80e00302c452100046182c24003c1748140950b1f01468203001c0001412104603607240f0200c60054194881150130000286800484500c503800f036001c2483c203102c50350b4001742d4090541c0903c04400028600e203051641b08680100c0a00b10a41c0c407030880 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 988665458 1250 988664208 988664263
    0x90a0201031d06010b030703020712020d1116050d0c0b040e0f070c03020a0b040507180204050a120f11150a02160e0601090b0306120f0a1b030c121104051305 69
    0xb03d0b4814403480d110541e0000c0000c54861003a8119a0720070750021002d1440380052000030360b14100b403003258002c9070220342c94035480c00000035486554040d80303a20700f5819090a09002c010303104542c04171425040d0b00c3c0003044505120b0054000350030210030880c003629040031100f0040740041c05074800d03c045900c181021a9022650889013600100500030540303c520300070f8134168166000132848400500300b1888051603400800441d80121071280841f41c44a0a02180f80c81b0000300a10820341205694005018004070142d9103030000c003002010f04083c1e500346141d0740002150b000607000041034101a807112400407000d4404001031642030700c4d1040000e0041e42071800b900381d0740e070004400960159580020a00994081000e40d00011590428030b5038450849004880d0060130203513008544440e8804d050480380c0088140803801d1400f880c020f41c00c450080252076031900c3d140d0519150311075005003400350303d01d040300c5107040e00e00d42015400d15030046502618102030020042d02c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 988666708 1250 988665458 988665463
    0x712050123010503060a030204060b12010801020309032208010207030c0b07080103110d021207080a0302061636140109082a12060c0415030b15130e090a0201031d 71
    0x2150703402828603503a00d4403110000703401d07401e603584000d6116041941c00f10b1b040b01d20300091301d80c030741010100f8030560742c03243e9829080c0e0004450400c3e40754814055500015818000344960b182c0d59000034005c1da4590561609903401702c5415030100c0c502c0c0503a4804c0101d03089400e90722540da4900940594116690002c41c1d60910104030700c248420b004442c2559198003541c181860300000302d0f40120760702c0b0030482d1075100344d0a0560250103a18002181500707142410589c0380078580d501c0100c45c071417500030812602050084046204582d1200214455890380d40000e840c16a805070b01894450000400c020b4064003c028550804402c4140320242034200c4061520018569078a0180301c2011801116400000c20118030920080c0300851440c0001801522200500004003001c00a001d0f170554a41c040c1443d0044d400091541041c4403510240201142c0c00c1c0d2075140d410380c0d80d03910040045041c0c4d80b0748002d8001c5250501190b81521614031100c2d0743c010b0b00c41e100d44515030741d2394 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 988667958 1250 988666708 988666769
    0x130510061d031e0d1b06020d0e100915060b03150d170409110403030807080a02041e0905181b0d02091302030c041e020c07030b07120501 60
    0x906200c000e10081c020058215040c1541c500040d003210340a104104003001c0720603d0603c80c203058001e4007401100284121050140e4011442100c00c80d0f07400380d03840000a61158043d001e07801e648440c1940300ca030b0140a4000c450380000c0021909010a0518000c0c900c0014804140a403504e03c041144a8111082d80e500400c500410b40c42c509551020911103800441c00610807261406800c0c16042d80c04050429500384090421500d40300c0a0b083d00944140d0002802245015000950041c462140b859014500c1c49000d0f0600f42e49800d4a002c1040100c1803c41c09540c2c29001d000303000c02c9114069000390310202c1090b07001d00281445496500c0c0100d00380041802d954917081944815200350b40082d030141c04080c4a00d0b1034299041814911030040740300c0d024440c901d80031890640074024142c1204440c60351541e19640c1628004d500024209880d8051100c0010105012042c60341c0320311350345c0e2500100400b210100000302c82050700400c07038500303090000428840d180c1c170424 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 988669064 1106 988667958 988667969
    0x10b0102010207031421070f2a080d02130306020c06060f010509040b1305040b010e01090e060c070f050a05031801030605091f091406130510 62
    0x481c240d100d00d10380034001a070f0181120344100a40300051002001d43d07006180100d0a130490001d9406044548002040403246421a12a040700e0044c06c401000c2c1e05207080c002c81c8000c4800004000c02014007600804105090641d40d598121854001d418034034882055580c1b030448040c1d44112402090360243c400460b003182004c0c1816007229a050b1035150402d000142800300034200220a11780c030103010804030b03020318418401c55000d213025400e000455810495041c22070f25040e4400d02502d464020840141c076000303d041604400c41d4600710303036030f054281407400c4004e0b0000f00c040c0c0710b0b01540106800304003000001704801e481c0010700c03400c000c0c1001d005608680030761040c00d0700400361b600002d80a06a50028018840c0096008080503403504580d03403c0724641c1514030702a1443d481844124509005a80034662044100340001d00d407440c040403000c20300d1302c0352 = true := by decide +kernel

theorem cover : BRFrame.Cov 988489208 988669064 := by
  have h0 := BRFrame.cov_init 988489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 988489208 ≤ n) (h2 : n < 988669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
