-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0687
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:09:06.410882+00:00
-- url     : https://prove2.me/submissions/e041e4a8-6d29-4cc7-8870-9dcaf773d2fd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 123381294 ≤ n < 123561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 123382544 1250 123381294 123381301
    0xc1a18030a02030f0306030a0204020304030807091d0a0b0a15050417060f06120102040504110c010b04090201080a15050306010b2805070f2301020307020111070b0406110f0c030d05 79
    0x5940c80c4901020107000d82d0080c0400300118010200540c2d0040e0003130300750340702e8510303d43c0410240e81064504901107060390f41088015075100201c0703801024114094000c12801c50303e0785106400240980c0b0046440301c8640c14240c41c0c80450b00002c0c070b000303810390340c0800082c2d100030107a400a01941c0100c14118000c2c415a0030002041030045080c00c0d080b1030365850b90303c09c002c41c80c98841e400456554080c400000c45a0b114490403521a80c601e114684c0c8a41440c015401c513010f540d14648114981000500580d034800312107030b8414840800003c0e10381100002441180c3c0a50009500d84520000890130384141c0f40a070010760041d040d1b034031180c000c91030300300c10030010038141c040001c10038070416001c9541c03154580112400390300038540040c1d08481c190701d0b10a03ca4000d010a80d0000b040c40045642441007043c11448100c10a00700000b0381d4680c852800090000b030b0100e0388440c4c0300b940c2d092005085031410340855a0f00b0b42c0d5240b074080e219499400c092340358143c261801002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 123383794 1250 123382544 123382591
    0xd061506050901390302100606050d06050306091203060f0405042a12020114090904140f010b0a0510050f0307080610080127060803040306020c06070e030318010c1a 72
    0xa003020f009001d04d4402c241c2d0349404049261200340000c0d4114429851400c1e100004d921410000d0903956903410758540001e080041621080d521044c020f60080301081021900030072003071001c070100900c295407a190000014130a87d01c25900550180c0f40000784010000c0001e91111455040d64024840e649019000e50a2048a11030001b9215207855a0740c01984111001c0a0030003c003980b13182040307034101c0400c01e100403c0751f003140c000d50200c440c00b070b1903801081014014003071032000303105000100000c80c0d219a514418a030081c03900b20b20301e0504a000700191130141313400c082c1c0d168907894990002000c100b01911030038081e0040000254405200740d80c0541a80c0c4410240001c68401c000600701c111b08180d88140203566401c1c02045040d0107000400c0114020381780580c9035814040790909012010700400b0030b01214a85d81d0019072000b106071103400c458540100312050001d00181c9030140800c04c002c00741124001e07511142c0d00e20000c40c40c0030303183d0710300300d80000040c4281 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 123385044 1250 123383794 123383837
    0x110d060e07050301090c05070f150608010209060a03090c0503120d050109050106050711040e06010807181802011101020d0513060b01020a03020c0d14010c020c090c12060d061506050901 81
    0x720200014001c00050080c0680c0d038001200d0403450b403810526000d142d4a6800c2064100141240c03581c0310004403042e10501805075002514101000714038260900000400350f106130001c885c10306882d04c1441090250081c0240004d10010702541c805205c940b044030302c03e50201000d4540c051420002041e030801501c03405040e55030079201c0c1e514101b01500d80035040f06078003118a030311940b82c0d0741c9204d82d10700c00d0203220b00904400b40106a981d0820300d0301c40c0d07200c2a582d0721a040d075185c4224061083d200c40520b55400750213080080c0248071480305940039219400e5018010303410316050103240c140c130704408030b0782a0044804001c0300b0a000300480c0c44036100013002c1c1c0181d00c8124007001d20700e0312400e1110401e00c6011404842c0c039072030403407a089d14464200080503030021010700115051155801d07134002c152a5069150445c3c0d51910314031600054a69805001d4642c03c0c4420030146034060819800f006203191070050f558140200f455011000b1b041c001011100c2e81c04030040d9900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 123386294 1250 123385044 123385051
    0x2130c08070e240d0c03051b0307110703150b0105091806040608010f020705010e0609250909050601091104180b150409060302010e1f0c110301110d060e 67
    0x10344034011600c541000711490b003441c088081d40224060404804101404a02c100c42201c41c0340241d2a6000791001008580d10a1040300a141c00c080030440d4810f0107040042d10f8207280664980c494403014021210b40039445e0740b4080341c0c42890000300078029284204c0b014120020024024400c585d001102d481c0246d080e540d030402c403200c3d003041203594023510b401e921000191000503a5036851900030700303607060098100811540021007100340002070169222034421b05008010505000d0002980c9002845404400c4505070000c1090300c0360180040005001144003440702458604042d91145428494074404038030301440b0b5103d0142d0ae0041c6e400302c0d804d2060040d100524195040d014092410f5020360003070034144200484000a00608040c0544d00c01c00120b243c11480050400d4103a0680c0600c12580340c035071610500450305082c0b00c400300da4541454402c01900d4402c13200d180030810b641c1c1c035500300f00c0400000032402c0c014005000f60640d0a01089035a50b0007400040c01c1903 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 123387544 1250 123386294 123386297
    0x9060807030903050f0708070c0f0e070c03020a02100302030a05010f1508100906080f010f0504020d110d2306150a051c0b0f010816050a140301090503030903040302130c 74
    0x1000518031070003070384480d07042c0c1e0080c18064900900038051000c2680040011101c2000100b016400d1150100100025000d00c0c104d0f410a02e040000042010000034034050400c9641d25044040500c02d01c8400040c90307002e440c0d09005604c28002030040c0d0400c981c8580c0b1645041c000203450010381050f4801c8a81d02c003014007810400380c2049910703487c028130395280070000240000d10043c1c50710501c80100368040c050b1007001108800103007074406109500c0356490401044c803025954409a1601442e07124801c840503940c0c510100350003c98810000d000c2c40c0d81c030258103a801080c0e4481e00d01d980f0200707050b60f28a07036600b900a0348100fa00d6a2180e00000704100c14001420110400002400c01e101d420300c090702241d84504202d1811039540c0303d00403c0200400a04000b044003081c01c02100058500d420b040101060a8102038400c51801207600081d8414a44081d40b1989400c2e8000040e2641c0b8070341002165502d60152104a01038030f424140d101659865210362484289203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 123388794 1250 123387544 123387557
    0x30f0d090c092f0f28030c020d05040b041214100510060c080403060e0703080f040302090a0506030d030f0b030a050606090603061e1005060d05010302120102070c15030b090708090106060906 83
    0x298180801750080e10402021505001c900e02d078110490100207103d2406070760109015001550090921a007503040c00144081401b060205101000a88003598080b40000c400c403c5941000c2d1840c2000a131550058051015103079100403032500103d105001044001074155a100300c102e070400d0489074013070040c403404e100c10f0000904075003051548001840840740c41c43e8803a110781107594808202c1c0c66040e07500060401c11810456010303544000d2810082101e881c04401003511a05007110b5002010f940340312185c1c1c20702c1a80d2080145280c0070b81190444c90852070b20384d607a040c058030b00f03e00c90318203000020080e2030000340e170910481810b20317103451a6105a02d201d1348140d02030b040741c802c012400301c00305054840101500c0c081d5000803000c145035146005001d450000e2070501c44a503401004088007007040840c107034040710405100f0f81105490514118001e12005180d241e125404206012507a80d0005080e8040c0c03840c2c1000b004030070354403d8141c07034183e00d17807055030042480c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 123390044 1250 123388794 123388807
    0x12090d0908031602190608090d05030126120409020c10020702030714030a02060f0d0f0b150d0b060c0a17070209010524130f0b07020102030f0d090c092f 67
    0x4505880c0700143d8400f5000f00c803405003074040404520600e410820008107041c00b00002c64508010b42103070624a410510f1a40d41400784200c20900c483c2e5a504030b1030380c540403c80080000b0400e84404916080110381c60b29110340550340658403003225507a09100b40300404030240620f2089484043e8010000c050f41031a1030403601141c0b152007040c80d03141c000d030142e800140c0c903058000c140246040c0140c1c0c0c0d42d901481c000d001141c00c031145041c3c2c51440c2401011650711001c59103078142740611840c80d160b4241d40d151001420315091160740280d408140b0b04425a800030341d504005108031480130201c01034642015582c09040000b0b58003c411500401840c1800024401d84801040c41500500c4502c1307401c0a43d50303c1203004003041090500c04200000399003030500b010f001da2540040c44c2054a4000075601d004a80c40b010400c180080e8203281008079034442040ba070380c8421540c4199030b444201070014070540c42a20100d005114800c0450350f41495035100c0d9168070010503080c240c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 123391294 1250 123390044 123390067
    0x1011091203030c16080904020d060806131709030a050f06010612020325030906090506070207081507080603030403050a03120b120a060509010612141c05040605090a0b12090d090803 79
    0x203407004010b550b640c908001c4086c868566000401825000380300100721245000c1c110303850207800601581050203c05d03408000a89074010203840c80042d60125512080c403600000d042500c01c040050041c803c44040b41c000322004114a41220b1036503d8a6050000e1500340030f09034407003100e180d15919081e05a1400300000c801c50011b6104071881c0015a0010941c0c40d84c04898a070301094615521580821070256410000c40000d4518940603150301d2418102c95120790b5005005801404965000546a0380f803c01c160780007950042c044921040307160901900000300107c0300204681400001107190070301203800c0303000c0c2001300001c00030009030740c8a4000400b400b509424441d52a4100020301e00c503114a01440c250040a940300d441c001300414600e0b1952a046445103030000074520398406422005540032a48203091481e80c0c1c00140001401c08801074000c44100140420b04020121100d89641d01c0360780708004690700440303908000ea6400200340704207422617008114440602 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 123392544 1250 123391294 123391327
    0x120e28080a1a22170702040e0105060a060f050d0e030f03010603020a090609060206240d080d05060316170106030b090f0c010503091905010b0a0e09150c0703030c021011091203030c 79
    0x800200b9084c0d4100703425a8006803c0c0c07003041203840e43c2c581d110028000755242014402d001400c031414545c82d200c3c240c0300e001e041d80c001ca00c000402541d850300050041c80c4180203c409007610400303800e80e00d6031217650143c02508180040c030002117200320007017180343c0180b0400c4142c410a4000785503950343d280c088038590f401c0100082c3c491004858080b200c1d01c0d41d0007000d80e03d900c04c6c103529032107280000a980c200e410080045101e5480440801140b4289448400954903110708011058484240c03090141059500041030000024104140c800c80428103120f0001e0020990f103459400c0d0340111280d00054031008241e03040b015a0f10803801503240c03a000740501c80d500204100900348009a1145015032080d1300540e08203040010501c024802038000c02c2081181e45442e00300407502980a02034544011305066480030400328150003003005100e485400c030307418441100c89100900051b00140da00c03500500c404814a038014602005580c4240f203820b698074100000c202220329207 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 123393794 1250 123392544 123392573
    0x50a120f0e030a2012010213061704020d080a020f06040c03020306060904030801060509030c0303041e0806040f030f030905060c0901110303130f0c03050303010e04120e28080a1a22 79
    0x241307000403501317850004c0c000340640720b03202045080c4003490002c01800c0c0104000c20034140d0013003042004016174412540c0000181c118000b607444615103d4103a01e440900a02d41e0000e104030004c000070010040720b41410340e403095054481940700d01082c003081c0e00c401d940017008982d40d40014440c8a11803c0982028a002011109504010400300e825540700d40c000d000e440008892060303000c00700c0c101813402400c00100030001c61910351200740394656003090042c00c100c0780540b1101014820b4002e084959081415580c65051400701d40c04d2642c07046c0f92041c08242e102220901c030a00101c190380c03145100a0500c03250180030340d140c00708504115011241c0f08103000001c4042403041001e180601206a2500700c1400c050400481555007481035100300011900d2410254035170b10080d410400b180400d0b6809591003042d56083c903082034003c10a148103118203602800203c54400e101c80c008030000c2c49042e01d500450304c414508903c500c40341030130b180205c00c00190f40403284001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 123395044 1250 123393794 123393799
    0x5040b0d020d1103190b060108061e0d030909020318010c02030a1d04020712030203040c09050610180b07111908030301030b0c0415050d050603030a120504050a120f0e030a20 76
    0x12220300c65000f02c17081e50324141e015141140914100020b0396040b10465411940490f5a22506c25081d24002c8a07614001d80d85030182e800041c5010426004016200c080d101301d10302551a40383c41030a0101454680e4541c0a0a41c00e001600c0e18140c004401c03035040f80c0055540305041290400000d5003400000c21180c1c009038204000b80125461500400b2208816940503030b5900345170a2440c3c0d01e60340c40d04107403101803801050040c00c0c0c0e503852080b020754003141800c00c0b0b84e144100e110071a5119070b030300c60842d49500207600b804010350031b000681c40f01421614440284245850b400c10f462880c0203c1c0103e500c204011310104500360001d0b603100c10415241880c194507110000b480480401408001c1000810420407903805070142e1640800107500031814400ca90000074140c0806500701c3c1ca0f11030740d0344081003c2c80428000410760540000136040551507c1174002e1100010944441c00174100410413580e80c603000c80c4136803609800c6554860310b0401034610200e034410744d804455 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 123396294 1250 123395044 123395053
    0x12907061506080903040b09240d06031406060d03050c070317070501050a0506030c0409050a0203030a0c021009080a140109020a060210060b030c0a0f021204090605040b0d020d1103 79
    0x6000403490702070060792060006165200340d1030240e010f840c10a0150804141350420702080c071540324040144c0e01410002c45094035000114a03109202e40b2112845101a00703000507452807108042d000141128801d250340005e0021480c0c40d152640c00688029a10007220681c00380400e12400c0508138040d0301000b5608015503a644410032010141100d000c128030108010040c44000c1c460703140e00c05500700b000d00c0240b4002c1700281e1502c5000410b144655640d07542c500c1840010000101c0703d03640030b000c41c1d690340644070019003060720558040380300706034120390505c00d54400c2c4101e000301c0d240100103003448045035031072400c00e954a111000507903681c1e1030546e001d40c3d2203103800b800800309038003e00707031641a103140c0905403540c1d0b0f002904003190030070510490294040464401c14501c0c40c01070031403c0015400c90030508139508455440380007180116000310070384d00203811102e08030341c01c00108461109009448070a1440a0b5001d0141498000441e100b100e480d13004072030080689 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 123397544 1250 123396294 123396307
    0x2030c0d0203070804020906120d050a110714100f02070501050304021c0f2001090b0703090503070306020c0613031b03020f01090308150303040506030a0f0906110a090902030129 78
    0x690482e00100e411100040300703401030105604002500ea50030000030b4600e4620307000c0940c01965503545410b41f00c000c100c0c0001e03440309020f206440380c100020403881a84c40d20342c0d84001d522042050b0300349082c07240703600840603480240910025000d42c103c1c1e8003c5d03d0024075140c0103554517000100306a030000340c103041201c0c20905092082c2c22852191003a40d4013201e003801d0a8210400318500c100400c400305806000c1c580e0450300d440700f2a03040708049030b641c80480ca0215a451015401503415205d002c1e80401004607540140c040103140c20200d82142d5184403111200c0003149078098003182c0a8250107409000f4413070000303c9140a0300448501d038089850b51400c4034005042a40094040c405224031000c0c4c2c005001040c0204030000c0d030501d401c0c900002c400d840b000d80a201d016030345240c4101c840b206034005800755900044100102d004150402c00d090b44010092400a4040d0030003244c54103061084d030781030722006090900003060344801103529204031080003074804000d0025 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 123398794 1250 123397544 123397567
    0x70c0501090f0605040308060603070e0f060d05010b0307020114010609050d020102070e070c0b01050907140c0f0312010303020f0115140a0306020c0c01080c18010818070902041701060f0902030c 85
    0x82e1114900c1810009941d1800c0d0130018824a0050f2006218180030414030014541c4003460078000c15040f500b03201e504202000089080c400c00420004150070034000280c0700c0083c20107180b140c00c01c2d400a00040b0780b1a60b95150407031003401040c0115034028000c0c00786080c220f100100851060045a011503100e074210390090030200c2c0c542001810711180b41c0108004208188e005003415110304c0154103280501420001e5108002c06004002090801510804206400903606602d041e260345030781941c4191500082404181c015205050703110501c00c505204904c0541402441c4c84c0c487c0b42840101241c0080511169502464405020010803443c1c0300038841454103400800c500b015403030024164110050407910307141020320051801c010f228036880041d2109180c00050f50750b40c400031095040f0061048040d612681c0b44c0070542954641c0204103459560701c8051226031400740060030307600903000300c4111004682d001c00c07201c122a0055074110140000c40c2d0305240c2003071f52 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 123400044 1250 123398794 123398813
    0x170703090c0b031005010201052208040f1d0f040506071103090301060b181519050403080a09062318010516060207150b0d020906030c030102070f150203010e070c050109 74
    0x8026400c11001092081c61801141c4ca4070042038280024492403510030700c00d088910116804940180000c0d200c08200546501201d0150401d0030340400040d44900d400580041400c09400c0c18070f13181070105043d80004002240f149a01000908007556917603c11640710a25a0040c000c41c8030a102d071003502cbc0d07803e014800140c14882c01e203d803114070381c403412144a106440801c0c0140707114048140c0241c2c90303504645840c603500103010151039155400b160319101766030014005500c04500c1e1180243e0001c242c00031507400360346440500c06444042c0c2592841602c00c500764003000c000c014203980c5510118405c00c04141011801c0141082659980074070350b590848111368005004010410819214600b400071600100400086a000302d05d40050300d03a800b0388614040e40c0051071750b030340420200c040703100058020b648400036490070040458000d03c0c225040c0c03a001c8030300e08504142d882568100c440041e0000600d464921007501c010a0301e000c1560103540350050f040c046110102c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 123401294 1250 123400044 123400049
    0xd02011a0d151d01061814060d0807021807080a050705090d2a08030a230f0d090204060b070c09050601050909071b21030603050303071805090106110d0203030403170703090c 76
    0x31000d001b1091200d016021a80f1101e0f41103d03815110041c00141d03100d03c044c00d440c0551140c072503070341c8000500014080c00880b003041407401f18000200001107502c8202c59018480e0030406106544815000303456501070102c440d50400401e0b03841d0000309940c3c84404141409107000c5100d01e100e000410794220900c1c3e004010b10741d100095004a07151711040c4280569550b8401c40c83c070341644032000b8150310801000111200c00400c401e000860780f58800004240e00800803c61282c1d19440c078005600424016501c0d48082c0c1c40005250403207005032441000160f4406140c803c0c4002001030f080000b81c18142049160007100c40c0700c10000034034410b440c1c0a095410074030140001c50394515183c1a180d5400c141c202a002c00000784000103503600302d10076007800c4190140300b03d8082200990b9900643d03220785544000074286c1d81040303d03242d03c60951400c0e00e038210075511040c1c0c0d07a4070056a0081c0040c03002d2007282c0e00c40d12442050b68001c801ca04e070100d08807600c1c1d221102e041d025078 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 123402544 1250 123401294 123401309
    0x60903020c0a15120c020c0d03030e01060b03040b01030209040f170909060d02030a06110d02070b0106022505060702060708071a060d08030a05040201020c030d02011a0d151d0106 78
    0x18500030882d240510020b4000c20100e415180c09400b01c510042072201610b81c607905094440303245501c1d4900a110014100074090301032116240d03c0e041c0180a09194802c84000d5441d00c0030105d03096441d00c041707a114036041110b1940d2a46942d003440009038004200b5140f420484107142d0008848078560000240a04003182d1104059030400070164001340005103c0d1f22423000d5000142c801084a0302015000301d4005007090800c0c200300010302c00c11640c0140e0b50300c0042d0321002c21083c90000c5040c4c6555508850a46070b0100040030000d04045210320792a1004c1c2081060b443e10350010542d0500c0548014200b00660341e078903403079800400c42140c1c052181000b00015151005034554003034011910840381c04140e48035101c15100141549034020b4945000a0039a4005c1001580600d4050125122659207450080c024040550f01003224681c8030020385503480c008802102007900000c2030b5040300000c9400d200140349403030b900c0c030815203803008008107050280310310002030154 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 123403794 1250 123402544 123402553
    0x60c070e01030305030a05061813020109050a0902070c08060421020c06030c0a020d03110a080903040e0f150102010c1e031d10050f1303081905070323091b0d06090302 73
    0x3280103411f91750000c28844c0104071240c410754a400000c20302e02e82046402c000c0c215440c84600040b03a501050703401c1590421461000010b05404a50023001041d000d98048461a81c132604455141d0310150b402404420611191200c0c03a0359582440d2891031090044640d80e0040c1d002140390742d0011140013140e40c04c04240c100c19650140910f000c203121a24040001d11000401d00c000380c007401510104000c445400224081030401c02c84019000408450500349441b02544c80b0b0440c044418081c040088240380801d54014040c54010a2103916040d0f0000d40d503440d400704900c1e03844010402c05454906002da0840102480130303142c44000080d141d0614018600b0083e546d004e01041d160a88040030010040c40c145c4500c1c10440e494a080c20700f0b5110b40d0012403401c1c0380144e400b00c64515100c1030000ea2038241d403052811070b81140a110b800000d1038002c1481402c201c9031118550801d261303030700c2c2507100038241c0422040014803200316021961628012150407441c104c025901 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 123405044 1250 123403794 123403801
    0x625030906170705271203070219060801060e030a02040912021204030b07141c0501140108090c011808010f0f06051009051e030a0308071d0a0302060c070e0103030503 73
    0x3801041c400d14850340c4000b02c002800d0600b0010444d214001254400c2241c100e40840e8002e01c90416100d58040140b10203005100302c441283c0301c1e448100124491580c043c01c8500050101901c10b04555682c3c031220103aa2038510282e035188241540a076050041d00c5420005954138884c031b0040600400c074400680d14134000180c681144100020506401400200001b50034881d2080c1d12141500e0309492014030301045120b6401240140140885a04401500c030442580040e0494406003484c0c0d29a076012401581d201d202a00c002c0840c1d0000303c000300700d550203842d542d064141c1c00d103407090b4059554821107084541089103001d801d503c078842c209070440d40c2d01804029144c01c0b180008504100000a0300003001d0380b2505002e10720546600c105200d1074400341744031000c082c05035241c000702450010030007441241ca4001107003041c1c3c0340c0215404800d2008507280805062110f1050554003003002a400007460034103184107261740130408615800b2040c1c001c5110340c9440e512400c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 123406294 1250 123405044 123405047
    0x2100315050402070206180402040b03010b070303051e040f08040503070305011401060219030810090203040f12030c0c030e190602030a021207030f0e03010b04060602030d050105090c090625030906 86
    0x80e001d61256114500501c14500582c0e100d4088640f0103080c501340c2000b5507105004a0040d0140d584401200b40000c00009084084013000745420b0b4070a46d400c0185585000002000d00e81644050000d081040002800140000501c413401400380d032155041595900029241c41302c550800c488594551890442070242058418090030150001d000c10341d41601070f070307840c140700e000001d000c0000420200d00350080f03d00c0001d02800c0d90513030035566480e1900302213081c000d400e20200e6004402c1c600d624140b500c00c0c030403ca40301921351788881d1014125102100d00311054602903906c99003c4074000030500d2607800d0f0500800751500690b0712281240c00290a000c0e2165070608001002c101072800207034031000c20700c20001103040006450b210716001c2401000d201c425245c01030300e02800420f80c1500007025000709490300d44140002e0b0b032584103001c8804010380e400c0150510a00500120340b5009001d011a65205680d0800102103c1d01c0107541e0b003100501034001c91200003080c401903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 123407544 1250 123406294 123406331
    0x310020a02010e060105030604260403030f02060619050609040e2b02030f0415030b03011e0e07032111011112090d0903030f17010e01090e0706051c0603021003 70
    0x200e00400071340425072518011a4550000401c014510441818400410f1600d090300c82003101c0c030060440d4845442e450090f25034140078172014054800c9100143e40d41c584a014140f504a05c0840b24402e107291209000881c0c102551055009450304030401e003038074003081601e40980c0e071340440f981e090001031400810210964130500440d0420400f45000c85004c000300c0b002c491034150402e00d07400c41104114000d15100351495850b5080c00c03c098a0180d503945103841c22258100700b0401ca88506c0702095803081e42e88401003d264021055210f00c40d604048407141542a050901c2480c2c101000c9a003101d24614403c2a1220042084144401071341c02ca1640070314034100074074001000c0c0c1c0c40a02114610320008042002c07c52100030030a214100c0c450038082c070541c00024a5864040807010034074240940c4108034034203002c0380c034a940c0004030354045a0f13050720f0311450304060800800400c103c00080fa419241c4400700040180c848101c400307560790710707a6030018503569100f8209411 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 123408794 1250 123407544 123407561
    0x30a02120901270816020a091406040c09140d02010903050601030f0302060a060e13020a23031908040303030f02070c06080f0709060f030e010e060414010b1e060901020c0310020a0201 80
    0x220f100300c0342daa4000030150030841e0071054615008048140e090320000322442c030a40c1100503114203050349002030620b441d030300f03078090b00d421501072010000700001100c441040d84500b2030451301000f207105845c2003400c51a0500c0c0e0040c5056080d03540c40e511402e241020a91003154190541000d02d014503605110641e08200161030a219891408a0f0011100c9006c1c0180b51440b00b1388070b02c803046550b682100402481c0000c1c10401c81002400e10f00c01c07000c022151139001c2d014009481c11000b48040e003c264280c2d010030814189400c68400b20000d04e01450004000c41e400c00480e0023040030039080ca00100583c0e83c40646500e171040c5255005000505408203105228600f40030b241c0d000610b00b0b11440c4d0328900001d8904607820510f01404901400d64154005d0209020031300000f40c6010755114071440080c0490b007000028452500c60340e100d5501090f20900c030300481c919209000f0319018405204844100051500090a041000310540d1003643e0009011071081e40a01862a9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 123410044 1250 123408794 123408851
    0x2030f090d121e1437031a0306010807060f050409020f1b0c010801092307020f070b1602010e031c051305030102073903030c0c080604020312030a02120901 68
    0x1c01355403005400914042d840210340046940211048951380004001250008019181440c0000c5071005401040c200b4000041c12011021301c24540c1000180e0314101c51900d4010862517260500841d03440703040b40325140c2080002c00c0006083e44030b90005e413900e044428034065851392000c010b00d00e40c4080031040e1440790010908020706030382042100f81110f4070f501010441c40c9030310b0b1030240e000291240f2100154680c50134000d03215030000d0b01e441030a02c81c408488090ba00c032501d08401e4000d08503200540d0503640079007001940700720458601440b0150460704d84070003030400d00d014160101903880000b02c02181d0100d01c1d21420000c18002c0109400071031400459441e04580d207404204a200290b480d04c101d20300e000815040c21880e010a00d1003004090b46071b01c1c1c01000e0b0b1080307040c10345440d00d2a1102082d00c442c04907055015550050040c0082a1807843d43c070310903000104050081c542c24001658064501c0b240c0c00e214905100001440b502d808551404240c0310340c3d00e4a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 123411294 1250 123410044 123410057
    0xc0c080313090903020c0f0f040501030c0503010509060907031211010f0902130204120809060c0703080d060f061205041b03030e040f022104021c050309040c080702030f090d121e 78
    0x13185d000b1488040203c815039020240441040220383d026110031041604285400000002d11108070980810344000720024403030780d11503c20f89030740c035070341603802514076003025030200002a0b400700d002d81d0300c40240c1400c03265451003c07445801c403a400d40d10016800d0710b4400b041c00f1890700d5000100310034200701d4114103140c1040c2242c602d28101c1c00703005090680000381e504a40eaa05000d07640384c0d1a0540032103440a4507443c2242480d00320b450301c100c140781010008a000a04955103405441c019528002c542c041d1a40c0c00c005084013400941d640e880130130049529400d1028440c01842c0a5103807125491600c000f448206d410510940000510520210343c1401090941c06500e00c0704c0c8100340c910342c54074000260068850b01d64046503441d044001010000084043c1c560644212805c011088000400751207552048131888010b0700208044041d08501c2006807807a100003404c06040c0f1851541c503181a40c80100c80c400110710180c3d02540500d1100e114030901c40300b60303c0e00302c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 123412544 1250 123411294 123411311
    0x51c0c020f031606030b0d0503040b070308090a02090606070f0606060203040807150e0d0302160311040b01030c080606071a01060810061418010507151a0306090309040c0c0c08031309 80
    0x443da1002c0d80c010b01d4201526890380400e290356011800000a4106060b0791303a0b83c0e6154888001c1d0340c03140d6412404207004a00003903007044003040000c603a5401074180302071942c4403000c2200340d6005001c221148501418180c01051041c800ea0f030180100d50000c40d17803141000009458610b00380e0110002d160345d200074400c80d6501c044814264001500c2d407928180807441c06030306002900c120120368200030200002030002006032181c000409440400c071844e00d950046050f607140b283e0b018041008003010071068100000100846d501581d0451480102c2d003408142e425002e0303004800081c0b40c0000d200e48054011240300c01410a4200000700d00c0708500c50310406c1c040c1d0700150310990204214a08103034011000c0b00c1c0c010380c0c00040d4003d1a4040e018280041490f00c2a040c16982401c030311079214100003900c6da02030040303c001942080340260800010789a810740c03020070050103144490005100c80804030290511001450710703101c01c0c000b5100100ca2940c0300000403414190034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 123413794 1250 123412544 123412573
    0x607030f0e1c020307060c05040f050409020a0e090c06030a091a0f060607141603060605101205060a150801030204110910180b160501050a09021c051c0c020f03 70
    0x4a2007402c618404201e40c0d4209500c2c16800c50003010300203800703942400e88055401d613004e4002c00544d0640c103522018030351940148021030b0001e110003500103203505014091355070664010b952109003041100e01c040407000114046d50401d40e0745a01c8681c50b11024810881e00744554802a09000e00c1300400f40341c43c4000c0220540e02615003030003020005102028021000e48070b5802c482000b0440e404d148111900f02d45801c0248003e031380040c076100000c1000d150218a1400c1c0b030f8455501d0814908090581d0b2000b02409400654080100e10f0000b842d11141c20384101c1050f1581c407050aa9031560040c8020b80f148940c026021500c01c2002050300c0e03660f40206070310b03010786141600e40c03a48042c180d0380c684201c6400a410346c0340c012910300404407040700b030890341d00d00c00d0b0001d0080340c0311522804107a5140213030080d40040f04404146018081d42c50103079000c3c0c0144d00701d85491400240d009044103c442c031000c00528600d0810342541814074000703140d18001e0700241051100c0080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 123415044 1250 123413794 123413803
    0x5030a080a08071b0312050a0e030403150b04090821010b0711010e090117010f0501051518040213030303180b01060c0f05120c06130f0210030e0a050607030f0e 70
    0x544140068a00400d450034030504003c1c10030f2141640b40d104a02c2d45007170251403222003010519006043c100050032107540c0d4001c00c4001d1000f00020b60809085981340030b003030000d40042c0203403036580e01c42d02010741d542c60040768403240c0140a440e0b500d400000041c0c00a000c9081031418400310200100314680c56001120345040e000b80980111800710f500407140003282040541c0d024102d02c0003c90102c41501451034440da080008000d955110701902c2c080d03d800b403144a0b0720100e522048450400500c00a02d090480139140c0e0300746400c00070010b804c07a000f0494013132550310a00d50510405030144200e40d4811280e8002c0020b000480d40c5441c0c04100c14080c103002c01452003985420813000c4613001442d40e034000b0503640319004101103d07406403c010b2031040144070340d2002c5401028003030358280d606a040420440721001039000e20041c04184000c890800d0744d0307560501d400402c18044005528030640c01742c40c090801c000c0c01004d46011007010003070f01e403034108084509000000e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 123416294 1250 123415044 123415057
    0x6110a0302030702040e0f0f0309100206010302030604030305071205010618090203100513020405060c0a020a0f1805181009120e03031b0a02090112032c0f041805011505030a08 77
    0x44000c44c2006c0c00390b82c40740c2001012402c0d4030701c502c6050156003103540e002c0060030001c0c00548080e001101c0c1820100da5a007400c0c4401b94049c2c01090205002c80d100340c00c1741c4d0748100340d41842070084c5e00001c001801c50f40268448000208803041c1c0d05c01003048094000000c101d0881d00754290305043c4050201c074000c500c20380c6d10540c41e14900202810705601520002c0800034a550b48861000045580b18078080030100d1007565058404111895400020001c1c0d5101d20b80c009000501100100010711000d00740901e140503c0120402001e400c00074141e008000301c3d400302c0c200303400f4507000a820001c0c41c0c018040c0044961680f2803500d00006450711413464001d41c941010004010341d040180900c0e000c1e400c030f480b403000480c421f400200e04d010280d02c2590307000d0340005021501808000e82e41460141111152000011803403e030100304030000000340000f0b8080c00e100d80c0344803494916407003101c4030394603168000c0e558618422035400400054000d0402c008040e6a40c4903680b0424 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 123417544 1250 123416294 123416299
    0x6080f0708010b18130f05100b0301080319020705060d0903020601051e010e1c0804030c060e060a08060a0b0309010605041a0604120303020c060106110c030109031b060e0709050106110a0302030702 86
    0x644c100d81165446010404c0e07180c0f80380504000b00c0c1207200c1d66070054181101c020461041411000514410190807a4105c0d4900b201950a101e824540500b000d130b029282c080452042040104c0d1503170f00c0600800748504450000101d81c26240760290030110b05078411803040300481b0712601600e961700200442042c00b441d00508030100340c40003958650b14501c5103007640d8801c00807542040080300091050300e02490404082c04c1d59000115040942d104070990080014040c00003411b0164410540100c0c0041912442503111503842c101a00111942c40c0280e445100410150409100d1840d42d80800c0103420303090700802010070034501c81c03403140c2047c403405200d03135205051081c3d0550703034080f20f001c1c02c0d500c440d651250000c0c1036025408240c2160f00911801c100c8070301e014450140c2055060702c42701600c1050fa200c5003040e05829009131071598846051900c0c0240c00c0c0701c0103002c1c0002002c001055410150024410800941c40b42c8840d030040c6440400300307800001340c03035100303030304 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 123418794 1250 123417544 123417577
    0x10905090703021e030a060f0f0b0f03040503070609052401050618010903080d020d0c0512160201090501020301030b100509010315020f071a190c0801050907020c090106080f0708010b 80
    0x4816203a4180d10502054800c2e40302109105030301c1b01982140b400c40314240400d01020381c5480c03510300c02c0b12a40c4158032986408100c1003111500c20b00185034004e0003030381942c1c24503006490b11400c6e180384c401c08540c560007118545941d1590402c200f00007150f0345c14500709139030401010136403c0c451440181441c6040d0044400719a01c05c4c10400c029680c840225600c6405610745400079410841075205210300380901c0c5055180300303200b90340c44004507107030160b013649441c283c0f03404080c1e00000b031170119521004414045802400254000c1d40300c3c0c001111a4684220040003a8080303411003403289218400410108401d51a00c50201c1860b00d8016a28060f60156402520561038028804090141c484410a100390341301c52054a858005503850450b44040300222084103801c240402c0c0c401d00148440e0620104082e488001c5004860202400c03074009005010240d1003100082c00000800c81c10059900480d50041e0340d41c1020082da50500403903401901400c0031a40c5180311 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 123420044 1250 123418794 123418807
    0x10210504050a050a0b07030b010c050c1009050a0b130b0903060708091614090114010507080f040f03050303090c010306060903020d2607020f060f0a08090c040507030902010e01090509070302 83
    0x20610048190541c03000c116002e2150500d014480079204440e850b010034500320407110f40e035002b00e0b03e4040c04e5a0103000f0b03005651120003045140c10503081e501c0b042040078040440d0b561903180c9254083c140707002d03615407951080c2002d4206182c1903009400c0f089000d00c1284c0040d100064995080001402d10303080d155694071590703180c030300208000150162080340002d040c204240946488a500340d0301645903a0300c0b600b508600c07020a1f0b2107503001600804c042c0010441c1c0101405080550341c9a503858107a54044c0100b43d034610b40c006039800c0d08008180541079404008101e00743c0700a003824091103113440c101410006180c07001074001c2c0d01030030319082041450303120404002d4049070030340c590040e0301c00a40300640001000324040d203060100d0b604180740403820707a00c1104076110320901c0c0c5212050200d03184400508900150301c00d20134040c0b06079455014a910402e11954006020750840c00010316801040b40300505004c0313075002c14070407030f12a6140e1541c0200c0604001da81d0300c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 123421294 1250 123420044 123420053
    0x100b040218061c110405030114190b120f010b010f0801080601030f031110150504111e040e0a1a0d020a0b03060f040e0a120908070303031107020d0f0210210504 70
    0x101d0691600c2c1c640744c0000400d207484198041c0043d070340c0c142c000300405e00c080700241e5070000307041d1541c111148a100041074130402981002c8038400003c2c0502d0050700d105105145040030100202a003651141500c01403564841541d2180001500c1c0c10041545081c4c003882e10340506000161043c00c43e00600e105140c002c007030705c500c40304e0814203c078049071a0542ca00e004041004900c0c40004800780005031500d031500580074040320a2100d14940015914204d000f03005006840c03151501c00d1000254410b110f4107460b209502442020035211501c800300020724500b042c20303d200d043c4804844000d47c4460304444103440110940b41d68035118078000500310700c0a07902640d4414101048003905000c003044155015100303285030415550000303402c0c1c61401481c06512400d510030501000402d2080d04941510004481c07042c0c980b64a40d00425540a0000800d842641d2150060030860520803500b8652103094501600f514110f00600d240440192010a00094840700450b0601 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 123422544 1250 123421294 123421327
    0x30c080912070501030b0609060301050405070c05030a02010c0f113a110d030608060c031009110c1e0c1e030703030f030b04150306090c1502100b04021806 68
    0x600d0010500c60034000c0709000d150350b4141070b0090380d00090a0400265080c00c018095500a8800411003415070382400c082c000140b400178005c908105030020b03a4800700e80180020b21310f2050560010500b0304012401030154120042e203d020001d030414650503400001c2126111880c0410804000340c40c0c2e600305080440e443e40d00200301000e0300030103900c103e8000c030f8190b0110030308800b558003040041d0001e070121070341c03403040d000c45802030350001303031a081d11800940d40f000c078541c0035010041d266503c4e03070200c0c0e00c01954001c11401c00940c5400f40f903000c02400e40d2500f0036a2840b01084d410a03005134a6404901185000c0e5107000040341c000c078800440c0c88074448000c0d08803000250b8904004220150580a04001c07900e0162010b40a013868010140f50040c004842c03c0000c0c55603030780c68020a04d40c0016035a13021841d001013550004c44130340c0d601010055004080c9141c05c203d00c2001c841c0003007440c62045104200c0a00184851040700030140c00c1211aa40c48104140c2d00c803001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 123423794 1250 123422544 123422557
    0xc0306081903020c04050412050f070c0e01050f0909190501020f0c010b12030307020705010f0c0209070203041a090d03031d01063003121512060504050606060f0403030c08 75
    0x341c0100c80704040307941d28402450000714065403c07513480c00c02a0080c80300311503090b1805011409180044160280900020711454407980d5140f850501c3d107880d42c01c0358140300e8201149011186004101c60301d4000b008120300001100c0682c03031401c040100d50383d901d8202003413030284085400c4103002e0110039410f44238440340798001541d503030010544150080c00e0000d07105208a0380125030000f420000019640b0030941078000706540c80c108001580c1c28400d81c2031480403c00d8040002d001a20b515000364082c5046400440c0c40300d0410415a00c1003884a2420010341c01c01d01401c280da036103407280b5622182c0c05040024003041400425008a4500744040d1220340c2040800280010399040c1d05022220303001c40041c51080d2071090700c004041034107010700000e014101010007503015034080000405140c00684000365904034140d0134802d00d100540390b030b81c0d8030810041482000d1040d1503220004030b40141c5040c030a814445641c0c015070101508100c8003598100401c503004084465 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 123425044 1250 123423794 123423809
    0x318020927060105010f02070303170a0b030f07050909010209180c12090a021302040e150303091c0c0e190f0f0f1b0801051e0402071707120f0801090c0306 68
    0x189984424801d9030b41c5401e01c510760001d00e801c08001d0201d48007046034420780341d0642d01e0451901401a031074900e40e001a0036041c9280d580c0f1004855690708001c807801d108800c5014060162402080041c0c440c0e00410942d0030364010030a244007640c455600c40120305c82a070490008da10350041c41c0341c0038007510181508200700d00c01444482c11000800f41c240d28400c4940d0140401214107100c20390242d4403800300c4d071340c017000c0114103000384401794540100d2000c0c00700c3e401c0000c0000025645552080ca50b407018018081074424440c00b00f00d0140a4407011080c80006e052400d0b503017624080c81d141c41942c56030380f0700b488140c180d003c1c0c000583c00c1c8000c480a200358009414204c00824020310140307040d5900e08005080a401340f0710b05070403154002c0ca010040c0608210340098442c240018540c0907900b0040040000c003111300c01c203a04440220010f40b911107900d000900d841d52007000c0d805009808084e0620242c2c04448941512000007000c101c0c40040e17581500540110340000b007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 123426294 1250 123425044 123425101
    0x60801080d0c151439070204141611030408030306151e03071205190c1206060c0b0c07080304060207030c0f12030f060b09271303030c03180209 63
    0x2c180c4d0440c140214003030028106500c038160f4944201d01c99100c90364034240388900401c2010040910f90001901e10b1078000350020a55121010f400d4900d92811a91041c03c210080e1803400c2460b0320840036049002e20030300951916080004080d40c81c00010061445a40d46060740310900408001355002441c1105800101c01a01101c141c0a500201e83e018002049000000c140303013014082e81e409003860701c120010782e201180044000d0034419245405010482e0303030411202600f4400c000040215076603030180c22400303140c1031102c150090081080c0e0342051111002241c0d400c8210382d00107600c10b0740181c1c0c1d02854030301039841d040048009014281d1184060f024414408130260180c0340a41c1d0070040a924500c0d010304036281c0e070140000f0214140401580f074245018510303081b1081b4071502141c07070303004203c110400b803044a420b501056601c03205001c258040c0200303406007000b801d0502c00034090383d00054505070700c608080e101d000490041640c41c40d05604001c5a20070002544 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 123427544 1250 123426294 123426311
    0x919090b040b030606010804080a091d040302071a030c090a15030b0301050703060305071a0c0d0e010212040303080a0c11010c030e15010614030702010f020705060709060801080d0c15 80
    0x54000d04030503080a008a0600091a0043c42d02141c06031042c82c05840d0200192119100d038003031034108200e544240b05c11910042121540c1040c5e61441e0300105082c0801d601d0b181ca402410310f5100d5004000005020f0f00140307620012002707036039001111091041d00d44d0380110001d04050565408240c1540c003613410320120b03e41c150006004a0001d80c001c2c006c50701c600d81c0c100c0c211009440f01900300c0e00001c0341880b80e016000030100701c2c601c40c24599803c15003818291810014a201542d001c2071a40c105002256014040222280000c46400341020716640303016000321002410390000c0ca5448940036032850107003c0701d03600d000f0001c00801040c14581ca01400800c000e00140c0814820311a400c2c810059410040f81a2002c03582d544001c6160100742025641020702500c040d0354031182082d64801d82c900c040e0806078082c0d001407500782070074000502b00140b150006000c0228540040c090403000040801c54103c280c87c3c07004480140342450440c0041c0c0200c000304190900701003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 123428794 1250 123427544 123427559
    0x32001140c0702010305060a0f180209030d1206060503060f1309170c06090703031b0501090203060c04090e010c020d0e22050f0c070c06300606030b030f0303040204020919 75
    0x141402d14400c0e2410491500c5030000c000c0c0c0c41149114801e00030000c00e40c28044006034454121410305103075030150608035204006424282032041301400100802d011400044603801620000c02c0a070a0551035410840c0c0400c002e4203005910034000c507034101259040318284c0e84841c50541c0c0040b0b11002c089220b5407010620b91100102c4045442240e010455082c0f020624004030395043e21003444004103160007000041c0c030007100b80d5840d540c40c10010090380302401514491240321510343d42e00c6080510480c1101c103003880320144d0f0383c5003500d11088150001680c94040c801400c02c0c0e10941030910003d458014541d104c4528032900e400114000c01050700300368013525803002c168001c0d0f138400d00b00d6902e07805251009490381014901c00c0102600070b100c00d0440081c2c5428440070070b00101492003005007556902600d40f66520030400046526229400007880c0c12409001003000086030f182e600c0c00045d0000c1d00c01c0d03900042000c541d07621440034440701c402c0c855816925035680c410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 123430044 1250 123428794 123428797
    0x3030d0e10060603151703070f0803070305070e01080a1104090204120203070602030721050c010207030207050306161e09080a03020f070605070f2406030b0610020109032001140c 78
    0x75208807103402c0503408140f01d0f0003030044003440d10740b2410b414209882d100300d0402003142d8951900c0c45010400228021032a15103072481110300400303690359641450b0390002c2c11600001c2c07241c8208035580200311a02c1e0390020201da0030011b1074101154850031221490054070032030f4070140405200250008601c60b0f2034089060f03140c0203d00382c4000c0c13036a814090381c0301c0c0f1030020010a444410541c00f48103110044e4515198100c61a215013408141002c0b1422a4030100007507001d42e00c509404c07c040d00c0d0404ca00b40d48800640407124100040c0b040140548407400c40f1407411420b8003203040c3c41c8510a0380400c4c0107003000d40403651440a0743c180079460380419410050035004124000c03030180d006600720f50031281d001400000c0107250703884400c440e459031800002c1e40d401030501810000b101d80508000746000e89904602070506000700321418940c9a10101564100001000400c0c1c101400c0a81100c00742d48840d400301c0a00c0c5c0ca81e0040c601c461088140d2100b803018030810352194030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 123431294 1250 123430044 123430063
    0x90507030501050f09030a0f050409050103060902040605030c0d030509041404031d0102010504020d0807020a050a0f090630051504030518030c030d0302070611180102160f0e040203030d0e 82
    0x140200903e0711415242071450a00311650010307035100300a10311f085842020021192402032408a0506468981c1c0000341c1d5000e1b4000e4030080c1e181c3c5209425442c082c1303d00002403400f1401004443e114802042c0e203021203010260502c0310101e4034890303a44817500080d010610442d800d014519007890040d0044000d44032241c41000c05040300d0002e54014840c15000c1e075001848a5803c4074181d88a80d841d03440014202d0b00a11a240002103030384031160240701408548140301016030811806404940066024041d030716103601d4901030810603518168100034182c00282042d052505059180a80e20b08081012a81900400c8281503000000e81190004040c00c0703801c01135484105070f84d540550b20301c9503150b000040d4048100c2d00980c01800464880d80001c103029466a4001d0703415080002195404181080c41c0d1007503603418420510500079001b10500310700e084c407105a400c94074500070000c1180702200450b0655034108141d0740c00e80007840003400101032901109859070481d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 123432544 1250 123431294 123431303
    0x2102041b020607030504080714100507020309010e15031302120d0c060e0a0320100612020a0609150507032a020a120b0c1308070b0a090905010e0f0a020d09050703 71
    0x100080f44129100f4010131340142d03000034106d0304140d083e44450360400821280240c19214150400902c91190300859114010700e80280d43c40319034050003d0030800402c1c6090317100709594500101c41c1c890704800d6039001140382c8410b0f5048041c0f032001ca10000141e401205407441107182e0b20070416404094001c60500c00c02c000e1090170a181c05081d81ca699114005011403803001414100c08450810344428661040456003c2000094034400303c4140b504a40d180040c1d580010082d403d0400c0c400380201924030300141504d00e0b00c0100c58044e20317070042c04e130100b00c0c002454400f0b0601c1041c00e03420302440818426402d103050703107409885080d280300403801940c69100000b122500b401661030740755085100000f0586d907651034800198040000c0e03005071841c540004c1032542c010045d9a01504400f14425640c006c20748000c1e0041d0859071100926a050000600001c803803003816642280290401a41540b1103070006070103806004d900b040503034503000440051106c0001d111007200c0c0036 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 123433794 1250 123432544 123432553
    0x3080405040b0901031a07030605150304050c01020a031205100314030c011113060c0206040905100e0603010b060a05090a030b1303170405060103080f0f03190c0e09012102041b02 78
    0x400c03d10845010034803010309840b41503407204421440307406c01d265000f695460000340b1241c54100154140251400c00d80b20740720080b08100400608001909a4440c00d00080031855569038004001108080d0080b00c01c6484901080d071941c072030603c0f0800b031984450720211420080c010701d9074030f400c120911603440d0300b040c403144d0f06074840f4411a841c41c000400400300e200d04103c0d05a1700c8040100080740c0103181000001030683c4148a1540500340314840c00141a18001800404100150426101c0c0c0d00d880e22800c40380c0c3d680406c40c0c40030070302401c1490b2a418080002303000c0401382da1026180c0b941e4a41009019068541c440e020f140c4030b0741700c003006040110405240c1c500100d9000b4159400b910041c00411899000740c80380101c80300026203010b49641480d0745541081c8c5200702c020600002100790040680110b01d40c04842c1d10b800798100110f0000690624010301c680c09007c01805007104660544d00c2a10050940140050210181078140d06225400c44040b01005028 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 123435044 1250 123433794 123433811
    0x222181a070519020709051501021e03030a0e010b030a0302010f1508030706020318070e04020a06080f010504020310031a0103210c11040e1501050a140a090f0207020a0308040504 78
    0x1100308140038180c0d941e40c55041040400844860440c111081c4007580300c4c0400c009004612070240301d104040c50702d40d40b0720000303141001914081003001d5042282d01d803000c01c40c0f050440001a00c0e4443d40340741011071001503172581d00e4018043c8111580d09130141c400031409140c0c05400031541c03841180307400c000b008072005a030398500000b03000340d201e190410010100421203503000b4540245c6440c0d0101c50b1300b0741402d811407829000703500803c10f8203a150100029490f044000c11300a20b04c81c28142028074000d00307503003000c0c40e0500840342318503404000b103039030180d5003183c2d40c0c0516407110844440400240c41909000f00900c4100da250038282c81d0606803204c2d240c0c8a4500d0a07076a01c5e13001ca50f00301d640e200f50001450124240d04181c3e030380003000d0b2180c001c001500340c0d04020701d0000155410030050240400e03140d0440c40740b0705194482d80c441a26030b0040c01040382c454180c001221407601c040c0001a00c0744287c080c2d40150380a5000c020f1106040c0181304880081b0740070800d01d503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 123436294 1250 123435044 123435083
    0xb0703060501090b0304081308070509010b030c0a0804050c040c03050a050c0702030703080f130b0903150603191a09030316080103020603071b060f0c0e031207022218 73
    0xc016001e1140010070341001000f030481480c2c0a590041e2040c50342c0b82c280139a24000c80c06c40c0b1040d078800030311030f4002c000420107410f0280f00c4a0140150780a02c0d0f1070341c0f070030004000d194414404800100000c9034002424000d052185020042e801017080c0031090203640e004020b041d0986200101303030300d000d02003a481140c1d14126a04180d0180141030b401c2c0c40c1d034892000c580c015100d4100380e803c0811010380030010040350b10001d0050f6400c1075032201a414181407404400c05440700429500700e0920509540c00141303034120f111004081280c0b10304500e003038008040402d50303180724503102d0402e000d040340c00070014501c580e0480500b01040340c800700e4100c032400340030b0ac07002c4d401c2801000858460380c440d8010703107204a0001100b440b000403954a00c8100c548217059841c2040d40d41c1091041c20fa4480003600c1c1c65242280201000c940340c50380301c6807612410310024820b4075401110f502c80014030544401420b40c0305002c00280303a078020b03103e00f100c54520046512642d000c1d0781c10000c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 123437544 1250 123436294 123436301
    0x921021e01080f090c06070b1e01030c05060703031107031106161b1e061d0106080d08100905090601050108010605130501030b0a180b03151b0a09050603040f0b0703 72
    0x50005075140c2c11941c540e581e0310300c91160b01401c41d04007400340115200701900e550740105403413440381c0000840341c0f5028840c803020903a090b00c4c0c0c4147d40c0c00d4200400c08500c410125809554044a105075140f1003460240c0040c4802c0381c0808066001161005c1419040f1200c42e01407680c0c03905030303545c980e2003910042c2001c48801e4240c01142e4407244070b0300401d100d684d1170103c9500c543e1064580b500c00c180e5012243e003000304d08030340240d290320882d100e00500e105003c401498000091040c5401c2401450311200d0840502d0204101c43d00050801072944141400814607918200b2044c00c004d0210f0f83c40b14401d00a140c04509580000280786100d4021942c84020801001118034248401107010701101084c4540c80340040c280403e00140000409140c5101171200103400301c40c090506080c0b0071150507248049501c2c40c00c001115610f9103050f40c000c01e600300240e0740c40c14960010764800107260480c80e0820404800c1104004080c2021403403a80a00744002950b650703020102c054 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 123438794 1250 123437544 123437599
    0x1030f09051018210e1206150d050721080711010f0503060f1009090218130e030a03020c0102190c03020705150906030405030d1113090606090506030403092102 70
    0x9003450030342008207003d404d02c44581ca00045240200c00d41c1c1907079002801c0c00044810015043c3c20400900811007090070f011a000c600550390000c0300d107495100e080d2248414800c80003081c21404074402d180e040001d0703407400a40d11404854a0704124144030900328148001c1c203020a0520280d01c40b103070700460580e886410010b11100403040454207000d0f0508040380c0b40020302544483c0421003803118005803078030300c0f810515030200015581c20821145600c0b801d504a440c44d0080c01490b801c0c0110455041a041d07040250381c070700b0340c103003554020310914010049a08003510328080160340070b1002d80c0c400e4065400c40301e13030740d4a43c01000080b0b101e001098550407010458455942071030009540d105001d01c00707580c140100c000080c820740b110003200000031a00000c0c0d400e01100072041c04000751800410400c1a10b0400c4000352004000d402024401c0c1b0000c80050105485406034402903e010310411850a100d40e00107070444849400891107582c096600c58044003055120b02c15 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 123440044 1250 123438794 123438803
    0x1e0f04080601090501050d11010c1e020f04020a0912080405030706080601080906060915011e020a0b01091e110d0606081602030c06070807021c08010f090c020c040b01030f09051018 79
    0x40001030b0380e44107021180100d02181c1807050742860304010bc1c524642558940800c03602540c140b041c0c62040101c0413041d036140c544101c1c81402120309450780b040810003618490520104988200e081071102c41c06194400d5030305124002000c41d410380d0120006000d03801c20307200c101c800e40303548100c280c43d18001c49000360050303000710010302880d84d14103269418140605108502400c3e0030711409030a210b00d81140d0240e07000c0701ca80000c0220302858640140300c14031080001e404107242d0030140c098039a480e20601525801118a07005c840401c58038030000d141020440d0716a6400082c1c0703020b2003204c040c601805c0900030b0b5421180048119241d21280e60b029051030b650b407050a0b90f04130300c0a40030a08510850070180b1500280c9603002d01c0204468a4070001c1d585030070b104880e52981c1e900049482810070582c0b078001c0e5000070f113005d81288100e4010034800394803001200107100096082030036a0504040c04280b00011607084641c1c14102001d1250940440400803e0103200310000c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 123441294 1250 123440044 123440059
    0x3060b011418040c030b06070b0106140703020607050714030c060103200a0e0903040506070b090c04090519050f07140405060108010608010b03091905010b03160602030f1e0f0408060109050105 84
    0x101d10f000d81c05485001034030300300000e06005450110f551070b040700504480254092005201c2c103900501d00407040130880b1a01841c0c144c8a503002921880f0180103403040c007030041041c0c01005040c0031564000201042200d4641c0720110703940340e5451086c40280d6240840d005c80502c038a03c00e224902c00c00101170a040516440c0108a0101610081c00c2602c01d0001303104c04642a60b900008203070150017003580c00c082c3e04001c80d02c1c80c1891554600103208a00e0441d602001410108190241c0700015411811804103424070a0610b132180340d0f60b45050240101c08949504c100300500703e5101c0c250307820000342e56001d0041d22840400c1c0030754408240304c1d5004000b40340c0003100441d40000b0007026151740c0c1d403849000d8000b440c21000c0403201651183c00c41a02c50504019107030840c0501030122030405c2c58020702940760320492411055246c1d0028001c03010644140e6601603050320800c0155692154001e448030325000350150030014018500000345500d102d003e5603040c2c59000303103a00b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 123442544 1250 123441294 123441337
    0x603072318010c06020403050109050303040303060b03270703060509030c01050c04060207030210050c01090f060c08010e0a0e0f030f120a0204150507030215040b060a05031c11150103060b0114 84
    0x191283c591841007203a16075000c02c400b2000600c01e000380c0c903500d4807c40081d0307100d0400740343c007400b564240d8100451030a4240100b2000203003000518250604840c3ea050079805d00403940ca0030022650000b0345010f00b003034248101080004010540341c44540001c008546480c0f0303e21078503100341e00c03c40e00141c0c408041400075207004600c080d0806654180249010b040e403402c207082da400200b040d11444400402c0c0000d009660180340c15001192500c1c4070150b04001240c824040301802c15001c10703942d01c4021f4002e030f0307040048800501d1200e003100d0b2a401e90405c18a040e50041901c4012140071a0109840200d00e000b610140d804040100a62100300700003151b482e00804800e9085124000c401180c1703030f0f9414010342c0140c1c00f924104540386000d8081c8046c00706150311540c085d5120131340302039900c102c20b518000e13000f460f0320b070004141406208a6103008040e03414010160400c07000042000020351105512074820b80300e80c5400b1801c4840b00d000c0b030003610125482422100800c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 123443794 1250 123442544 123442547
    0x3010207020306010e07230729010308180301181b03080703030c030605060a1e0c031d03070305060a0b040606141c0f06080615041506030f0b060307231801 68
    0x1c03a50300c504240b40990003030f4079442500c10030347c01d64a000c40c0501c1c0005581018000c00400d06c8115203500e01c02d10740d9003802142c15203980700c01403002928046001c60170103c1d81c0030014510301900c60040007401006151027001d048120f605004071207042003c0e4403a202010281184802c07290001c80250a0043c01e881c1a40548150a5803104240c0d95000c0031615030b0303c040240240c4450b56655150f00310801e590014585c0b806c44900c0b040c0319015401c0e2000070340c082981141269845007030044000d100c1c0110785001c0d002e8000410f00c5c0129010804407140a0384501c0086108940a00030256504000d69941130040d00700c00310074104000c04850314658000d81403001107210000140d0130070000d110400c8500d15009079416810250500c20a911900580010243e0485003005800c1c107040f15203650102030722600003031644402444d1034004003a40544c01405018000e50355030f250201e0000c0c80f00c5140844002212003034406405241c1d1034000703440010b02040903030b44031079558000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 123445044 1250 123443794 123443819
    0x11d01110316120501060809010f05010b090d05031e0c0601060c0b0f090c030d030f0b0301062103030204050a0e16030c020d0c05030405271b04060804110a030b01060e0301020702030601 81
    0x100b48080c000c241e8500c43c8603a0041c4682c600801c1c0c00c0c0d452140c0740c10042c6c940d0342512807011002c0d40da01d0410300140301540d050000c031001800221445c020300e81d05840c2c05803d42c040c01d030815582000452401030f150502d1002000744803860419a12a80c0c1c030344600b900d503403859031000b40a80c3c0c0001d0026151802d4030860303d4011081004440403070b49804002403600e0107070301241c0c000030340300c405a0858403800c2c041c4071a1410102c00a00056090542900c040d00e032440044007030070040050709042c503010350b0446021301000f51058140940703034001d40d81c4c0080300380e0320101103041400000034814400d1203940015200da5028142208900c001107424103403000055649000411000030256154031f0051542440768800d030000d40781010cc01b0080620092020740c2c40d09000d484050030020103801c95068403880d00b440380050b02c660802003c0060a00a910741004a1980120600000c010030314102c5000340d0b1803400104814090500781c1c010b0042c000d4040e4458401030140069404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 123446294 1250 123445044 123445081
    0x2070504090f0506070f03140c030c030712090c0303090501030b0f12030405040f060608010e0907060807050c0a06050103050120030406020f0702090a0c0206011d1906080d02011d011103 81
    0x6100d040c0741a2921101d0501394180c42210219103001413200000742c1601070040480641c20180501d46405005015180b100800c207919200340000012220b500030598082c200d8000202000303158203600d40955042c106000c00d41c08198505400191903200740248551a07a000e4a003000302045c0900303110007005c0c00c0002c0042c5000c140004260340c2c545102d4035078000402e520100c2c00f581380c200040c00c20b00060300100a1400320780b01308032050744000340e241c0c121a000c2c80c2818040c1d40758142120380340180e0311035608038080c000c0301c0b00521489400c410305807405134000700100600301d885200c52403900b0506000000007440040c2c0850001d6001c1c000105544c000a490089a0360008210b1217040740c21002a6544010302450700c1d50420000e405004c030204540040130341c90000741303030203807000b0241d0903440541400400e8100280c0c000c000100071483c2202d0b8070844118010740600598060341078821580c1741c414800500500806000c140c0110286181d6102c2c0c401c1620a8582070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 123447544 1250 123446294 123446303
    0x1030b04110d0614040b090403110a1a040b07020706020a02010507020a09020705030c070504020a0509040c0c060f0e010e150609180703060c0305070903050c0f040603050607030207021f0207050409 86
    0x114403203900700203040000c0211841d00040000c410b03060004400c120b001c8104002d020314644803201d130300340d101e44c0512074020b41c160034000081045080728a1400c64900710051006699010200d0300c26440700d990781c01244114605402607442d10000c90f82d03210944213120040c0c0c031030783c14100554012401051031038000350084681d285c5850440081c0d0b40507000c01c80d20365000080b1b50316000028007504e4058841190150f241401c8075100030502d000d0045140d02c00e81c0c0e00c03484061034070f025400110310250700502c02c3c0240050f000b4494000c05025016040c10350804407200c1c000300000c28001d04154000c8055021612401d00b400b03010200108030010303c9200c4819a12002010400b44c0c5c0158826000030030101030044d001002d4403c050110401d006051400b400020004074411000d583d0650b48511800c64130400100070303040560014201c3e01810081c00b204a625400070305100340280c40b5200c00d8100c0b9050003080304c12541301c080040e0401e1009115510780780d0000d08103907006 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 123448794 1250 123447544 123447551
    0x1203050f0403051515011202090607020907080a0b0303030103020a0314160b03061e0a060302090d151406030304030804050f0105190e040e03040e0c07030203070b090304061d0303070201030b04 84
    0x1245090480d81c002d0700700780d82580c001011208240c0310020325550090440c4c514003100882100041c4c0690301d40640d004180d070f0041407000a5484405c241d9880030f40051500e081d81c208208040e15000090740c59842c1d0500309a814619400c000040300d0480b0707406003c034001031f45141c0b18802403403004190001c2d18081e4a00c582e2262034440e0110026000c8841c1140d03880c20014104005002c03141c0c01c0c28408240810f28000c039954a118020480c1d40b0381c03e015039203109040001d04903080d94a0001d180d500c070307081d16105059840d4072211410b00072582940a540b01c400070541d80340514440201041c0040109202a04180005071400300040c18001d080c07101c54400d01034203903401c036418030000740c4840c000412882d180c01039100722000400918940b500746a840105084028140c9030b4500d030000d1800c0030107208100302c0300c4090700003d10944a041c440112502c030782c0311703124200c0040c400721100c1e0450110401c03588201c8400500944c5003d480794015405058102c1000794821369 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 123450044 1250 123448794 123448807
    0x61406091c120e0103060b2b060e061002030309100902180a0b01120209100c0f020307080d080603011a0120030d0903090905040203030301230a0b0901081e01120305 72
    0x40410407075180d01e00c1689550a201e002a5000b010741c80310b449060704150a10204004c0c079102201140d074561f0060510117204280c10b001c1d0362031b203443c03c0d2102031203519001002400d14110890030b40191001c40d00c1d40d44404043c40101e9817800306544040254020245d0401307002c038107034401143e440c8094500c01140c81c011500300d44a240445007001c4064441c40045001d6030300001145201780c8008045007030007040c0e40810311480c1202640410b02c8406c0b400d21060050001e105c1030030315401800c4a445035280e40540c1d032034007469425080426000408140249418000e1410301230f01c042421020342c508100458011000c072056071f19203200c1c030103203c040e00070902c018084804100004a038403540c52800401a9999500030b950003860003040c0001a5808400c403811643d5a04881c0020f030790300003039040c08024501d2126808101640c000071260021800f400e85e008007602c84500700e60792500b1210002c1c84d40f42541c0b904056034401071098021080d86081454044e01d0001e08250 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 123451294 1250 123450044 123450079
    0x1e030c06090b011403070803030118021603091a040b0703080604140f060f040614010f02030c01050106090f0e0609010e090a0c03082d03010b07060b030a0f1506140609 73
    0x1d4a24009480a40010005008000d0480c1a803141d0050541c010400b075898a08950b850b400180205100080c000801503186282501660400001074400d0208082c1614010f0443d890030311074042c00d40c0035503030890a5900c1d0301058a04071103011041c0c41c54000d0a03034044520740c2e030080c1500c0d4450b49d18110340d190b040204038094400c0b251010040c60360b0401004114140c0e0408050512507800c210051004042050088402c46020b0034800c0f042e4945da081642035000300e041a1145601c0e050001840651040329902295145100040c4003501d481040288000071200300c1d8000c0c404000410003e007a60700226841076254050704e0b0f0807030107a43d074588528201c0d40155003606006c11502e038000c299104000002080904072070030424100980d1105020502c43c8017540b10000c22200d05004540c0c011a0508000805030f81c409541c5181030301c0d8054000c0d400380e8580460151090f044145e0f88504405c0c1d941d00d4030301e503980920140820009601505455811050648482c503491 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 123452544 1250 123451294 123451301
    0xd09030503044b050312040909020607020603150a23130b040c0306030605070201020301050d0b0405010f050906100605040513050411030f0a060f06030b040f210302251e030c06 77
    0x49042120183c0540f0014110510b0203070160409446070304400244803030b1450560448044440300403010454840398000141070b0702070354401a40094000080101e001c0d642961680780510072660f10072043e8595944034020080080d0088101c003060fa002c056918000b0b2a00707480c1d400315400820841e41c2a00414150b40c3c10700503004c04a520f64100703000f0081d090180550003080ca2000b1821507150a0000e03100d4070a15030054014004440480c06008080d000329200040101c1d050000741010704100e541c1b07c0701201c01016180e030740d110114110388180112021070350002c0c03d500e0390398071410342d020051030083e00440e0001842a494445a01c0c2400721112082c07444018013242d00084c28940d0594125108100c0303081d1401d80c06100060710fa19041e60000d0f0071503210041084a407a01d8582d80c0c0510240380200900c1403110118264950018041e2084000c1c1070145140c02c0300c07807010500300b010b100528290300b507200c0007401c104052011001c11b02900c1d105081c255551240400c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 123453794 1250 123452544 123452639
    0x8060402181003150c1b02030a0b13060501061d0114040902220308040303080c0f07060c0203090901080610060509151617040e070f0c1103010908030c03010303020d0903050304 77
    0x1001c4c0c07600440c05885e508020f0800524540e0115035180300300707039070000f03445116010000388004546400318903501e00d080418102c0e9540b11600b0021540c4484004d0240e203d141c040020303141c0d002105810b42e51040120a0703d001c00300805609050600030305d0006508807150bc0d421040d4119268240b81070000c4115000f0741c040e1903041e0342c2d5030560400810000c1c0003080b082d5510001c20180b00d00714200d00131540b545405c0714000602600500c4228214031031942502e0340515508008100d0032800b140003400354100f14940001c499443c5820788a40c010b104c18203a0207000041c60400030301c5507400400030030903144985d4142079250384c0e42d991030540f0318400405980002c00d05110f00801c5400d200c0d00b012260924401c0d500309210028115034200b41c0040c00c1803008400c051844d2001d4111409107a07000c15400c2c1c4915103090845100e400900c01500180300751025804440c0c020010101903c0d04040550324180c02c01d030803d5100b40b68120202c0c819244914010180a01c03075040e080d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 123455044 1250 123453794 123453833
    0x2010e0f06040f050a05010903080d050c040360270c0f030f1407080703030816090531050a140c0313060f0f02120a050108060402181003 60
    0x1444c1c181001e00040c1a8607070012130600241c08000d0011075900350a451444c80d2008000c9415980c001009a6502807a48003c2020840f44005022910f1103000000700f6100f503184440c0408d0047c441100c2d035021401c1d40c0d00c03101c12450307084c01e010342d80c0c11181d40f040900c044082103071301880c50110710031580100c40380403082903001a1810028034000b0784008042030030080030510b0075612140030003405500020102030820b5509000b0100c00d1002c0001407072100d090740c0fa030550740d05001e000c902013101c0010f1150025210301c1102070060312000e081d10405401c1c00210012840407040070190380364051465004800c0300c81440e00b141c01464032030301446031301046004046005010b80320703010700402107440042c000c2060b45260f4410103401640c0202c00482d07808020203d100091203550140b40c2000d000143e2078408844030b41d01c940c02a03e101c42d041000c0d80e65014003035202d0005a500a60144070303140c80c8218941001a80350b04002004801c000311550b96075018440c40c144e803070814 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 123456294 1250 123455044 123455069
    0x50604031412010501050304051609060e160801120f120c02130b030c040903050408060703020415030e03071401230106030605030604020d260c01090611070c0302010e0f0604 76
    0x10425034400070640c081c18092046078100b8807180d2040d034250405004a41c10007101000040034800100803c490050343e01626030044c50f01ca4000c80c019000c00e0085517a950350100c04591041c40440542d601d050050380ca0543c20390800d070381a034083d074566105458694200b2864004a83c0ca20003660001145445400c2da00f8010f20600400c060102490003c0c0d925011a80500d0340340440d141010751412900003414500368038090310300c2e00070342c0c0040405214140802c54026015030080042c6c80780c144c2c11400020b81c012049064440b903881540440d007041c0708000c0016220701c03104500141c40b00021828616906440084032204001131030560140b0004000ca55010b10914002e440141c02034851850b01350042500460f070000000d00c08a03100004c204000482340f41c022104070701405440e5980b54025403503003e01040041511716501c0c2c0041b89103480d221f1021252960f034403590b01c042c1b00345107800549094540c0302460350000240390f549503e994600300100007401c7c4417000e01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 123457544 1250 123456294 123456301
    0x1e0b07020a180c0f0813141f021809010605040b090406050d030e01030b102c060f0910080f0a0504060f020d060e07050a0504090e03070215030a0c03060b120c0f03040506 74
    0x1880e03850b5914081e01480705c0b10061294981002c0801d8115541008142013841d410041141c50700c824586440c120b2800e010580c50481995001061121400388400d407414544100300240034100380315010118104100c204810342105001d80110300e03008000142c202d0340c84000c14803851140301c00314001101e4010001c0c0c0341d80c051151984000d0203680018500028640c05802341a00c1103450135604280001100390481c1c0d201200d00447c0054142511003a07904111038840d000380003114401c402c1c4c2e2900355601481303840e00510034031403011040351507140e40d10300e00d004140181c400da5407140c450000b140c01c1c1071503000034213800c1000480002c84a01d00b060000c00d620001d460141000402c000c0c00794500d90100695040d42c030080400551440d404d50f6041c518440c6500081d0000c0c41440c1503a071685443c00914072507500e48009000c5508e00490440840c2c0d00c80c0500e150300003007402811040903c240020f9400188807502601d07200010310b01903015042240d085500394011002c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 123458794 1250 123457544 123457547
    0x1005011d0c0301060909050a23010f0e190207050f0106060507050f030f030403080a09021306060201050a0603080d020d060f03080901091505040515130602060603071e0b07020a180c 79
    0x10258003040c0031840c0e81c00c43d418a00000c00d910900c1c4110642c807500d40c0041004403000e0703030264403191031581d04085154007200d2029040c40c002d01c14030b6401051010000346420810980c00c0c402d40c880c0c040c0100020110500b400250072115060700e1f284035800c0d8182c500354013485030202038441500c2d41a01c40806103030841c5030607101040400540c2051001c104000a00000d580d006a0f05041204a694400002c1340c0281b090f85070181d40540e101802414a407600d510074415a10740342d00900c51a5244000034050310140e01c00105506010009019501226070241400104181011810b50b595606104610003d5003041c6c170324107000240d44030700b90b801c0b4481900426814030f8001990040d100090414041c40c402c2070b004144804815580d00341c0030080302c0c103650051f0146c800160b160940295510800c0760501c1c0a0b100b01440400d02d0b000c0d1000c164094102040d0f298405402d02c40c5545542d00100300072a046402c01030040380c04100700440031060007072400006881303d4480320 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 123460044 1250 123458794 123458849
    0x20112020d050c0c1009260d0f020306040605120c011409060325300b090f0105090915040809040b1c060f020403051c020c040e011401170d030e100501 66
    0x200c581d01070701d060403410014207509142001f58103503003003036083c1e4075180100d242144100b840341000303035140c02042010107180d607000e980a407406640800900303407500d0501ca400c0c001c0c4248428103a102102c81c4c4000c3d0301c80d000c200702070500070350000c1c10160740c08003041030f40c0c1040c6e035140000c0304030f00e11b00c07040119070b004000c40038043c40c54180d04403410800a0b008150705010075400c041c09282d034102006415403c03408000c803001e08012450b240030f1040904074102030190b9441601c0410110f03803a2000000c1e00980400b1410158180740c907940e54000580e400102410b4001d41c480085400e00e5039100141480401e03103038128542032481d40ba0100455511b0b4101300d019030300c188410310210300e00240303011444904240b2801030a014041c16813605943d003940c3c5501c60f040a040556000d819048a40c1441c920f10501410f641c83c0d02c7c0d552490329041c500b800c00f0742e00140c48144114840c0d0030080c41401040141c401080503c0605403c1d540242c100004404480040714034040c0c402e403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 123461294 1250 123460044 123460063
    0x1110a05030720150c0c090406020c1b10050d09020603042102030304080d090303090209090714060909070c030513062114070e0114040e011701020903060103020112020d050c0c 77
    0x100c034580001100c0001c803000b0601d0041000c00502017030110000d201005091083c280c01468190326107018602000654020700904078140240880320302e103850100b030059403030b130030080c078140094041c0c1404071600d41021038452210b039203c3c030000c00540c0700c0c0d000850146000e88007144011a070302440c003052a0b01c2c1417050045600400030880880e05160595040754074241e000b1459980d1030a017103028040211010790300c5501c80341800055440090744008940d0030b0085401104182e50801286008000c1d800b900322000c0ca0025404c9407061002100443c881e092460411030403d411118141441e003200011501c10003000c0c03002c0500d4a21030711400c029a20901241c0c01004541d00781d0903015000b401480042e125042840e80110001440e80d41002030880d1a155664800040f460302889591030b03502c180c1540c0c0e403882c00d041c000c4401039240034004100356443d640c01103503101650744000d503100e81c3c240400d000031400350248a000c7e0040d0076070940c80f1200190348509124054 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 123462544 1250 123461294 123461333
    0x510030203040b130201080c0c100614040609020405090c070201090306020a0906090510091520150601110a021309060c02071401050c21070b04030804200303030f0601110a050307 78
    0x4000141e81c06400783d513002008803200c62702d54030000e02c5145044400240100041d01301071021910514000c403541080e07000321814089141c2d941e110904900c5a8005d16400420f9a00000c0401b0b043c40e0080004c648180b4000804503501e885110498208201d072070000f4240741000c03c90207520030b1185001c2c0200305e50380904c00c01410800340480702280309600640061a000c1c0695030b02526020583d40007005038409010514488951561041440303500490f501001294455102e080340c0c2d04071038002002448104403076000c10580c0003044030900c003c561030f0100c0000081080c02001180d81c03140d0010070720141010316484010000c0e00303200b03040140910141001c0f400014100880c0c54001512040c00e801d4140a490203101c0c2c00006410141c00380184001c155010080341c3c03140b4000e1000300401c0480d00d04c613003075002e803050210303034035a1044c00401c2c01d084400040d0743e04203405040260b08514080d03016402c1c0165030b08299116040401c0440c00d02150124940312008075 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 123463794 1250 123462544 123462571
    0x10b09040b04050c07150e070602010e01060e04120305040206042d0503191e0204050405070602060a15180b0907020f010b04091a18011a03010b030a050d050d060510030203040b 77
    0x21060565005d8004041d020745001803600160800590090701c0003500b02e0241c0e00c4e0107842c2c4c3c00c0640a0700346010391514561030280005000700110002c140280e074071026514140c907104004402800c006881640d00400402c4000f41e18001c0100c08a101c08004c850140c40006000305c5a240c41c00a901c068042d801c10000000e9041c0c0c5601029101580011104501600480c50581303802958030000d41152401060009010000405000310b40c000c1e401c17110559528081a019035120f18442d1200c0d6031003840c280141c3d00080d00c40c0441030b03040f40d00015072400110000f44241e00607200000903030480da50410b800b080c280118000200c050700c0c00e00101e4400d60320707200329500c25800d548000d0071560103e984c0a03a102d541c1846124200000c0c40760620f0341399600c1e404e4006662052003903103481c05404913410301140b6000069082800780840c20b0000c00c4c00d45103580684410002c09a858a01040540d980460f011420400e42d900585901c1c0a10f0185e0000c03030094004c1440d901c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 123465044 1250 123463794 123463801
    0x90e06060108060906061804020c03070b07050a0f050306010c170405100311030c03040203100e0c0108011203090902031e040f0c05030a11212b050f0306041109030303010b09040b0405 80
    0x80e0300710f03415003000040e14400d99a100c0d40041024006c2150b481f6544980001a0280200400400741c0315290060499030b20903110700c241074683d44200105103000c513650b00b240350505802640a164840010f040c5045003105550383c13006900040103507145910f10104040c4043c2c24011080c5522245505040010381c1c4244000344050100030b14400d281301c0700200140031510184010030204d912540c09000e8411412025921641e16001883c00100c0c00000054030300d8844a80408264068894120260030300040c6006035000422200d61074070789441035880c80502d40286807050f8081c0192401038907152901c080c0d0103546501442c400e620a00b0000c000c61400e00900c89500b000f01c820381e0300342040704034000241c0c0490204030b801c2d00801d040404003892010414181d020082403402002448031130036201405480f404004d50601407002864a042907404003881c14040c0030700508008858002a01c0c580c000d0300103052003c03012070380f249282400c1c05400d000c050221420f010710724 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 123466294 1250 123465044 123465049
    0x7030609110904020a200604120509091305031b030414040903090e040303091505060f0915090402131104031403040e0703092d0203070512060c0d0e07090e0606010806 73
    0x51114503846a42d0000324a00080c0c01040d942a003000ea031b20516801c0700c42ca090b200d403502d204032020f0300d42000300f4130a807800600c603004491807000f0081c41d003481a280c0c483c0c035000e82c8402820440790b61000b00000c8429144800c1c042c2600381c5840021030741c1d103050280d400c1d40aa086d01407680a0303820f00080c0b900098000800105940d600c4040d06007a0b602d9045c1180901a9682d000d4096004070025284410f459000a840341e8410750310020102c0d40c01040c00840315041f0782107807101c1503030752a4075020728041c101107030014001010500e002c107860f1840002c981e800903c0108101001a0030402c04c032030300c500601d02e102e14401039400d103031078007044900c06080100704030101542c810360142007052416040814401826001080c820980312104034426660f006a101e0b00c80d68a0000e014608480300c0c841341d140e0540a4030154841c0701011001d50070246400d440d054448103468100340303081110000820421101242d000c41a1440c0f909206020303040e1410003942004000294 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 123467544 1250 123466294 123466297
    0x160216032103061a0403021804080d0b0402090a060804030f1119020d050a05010501090b04091101030209030a050a11040507020f06011502010902031509010b06030403020c0402032d0703060911 84
    0x168103154072030458003008500401c12504180d4a020200700030155070000c01002e401940c2c4262206c021750a0160400c50780024101d0b401000c0c00b50400180903096240c0d00000b401c483c01610160808480030002000d00c3c1d1030340c000741d0010309885c3c20071080c50750125502c4020b140d90300380303040e000303800c01c44940d2262100421074400d2203604000c032085445040190b46895000011b440d417205035842d0050203090f081c42648003e5040051185040c42d040c40f030548401d0b844104c50051040b8a00158080d40000915540c54041c50200f03034040b0304188106558036108030a000c1c26031900b01c0402048460140a0308110f5118000c448110312000a1042c15502d60001e0101c2468403698124098800581c000750140180c040c00420401040402801040c103c0d00230b0005111820602c000b5000454001d4010fa01c10501080b4030708060780159040558520148815034000202d82c000071042c0f001461001d4250042000c031701d6251184e900a0418078506020800d455030907405107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 123468794 1250 123467544 123467573
    0x5070611030405040c090305010221061002060109090c0513050406050c0307080402010c1704060e03071403060f0a0603061107030807090503070306050c1207020d11060106051b0c0916021603 83
    0x101e17034400c09640f4803401160030078000d5500c04001c0d543d4041a000c903000f101100d2894064100d80d100c0840c07080d00e0f05104102200c00254001d1001b40e10300002c82c40502020742090f15080a24039000c074168540850754800314004460100311801d1516160085038002002d8048040b014410b015805510a1f00c00b034026409180820b02000c03c0d05050600c01c14a00c02000500000900001e40c1d68104070080c0800c4022401c1e149056900c204c0121048400301c600740c0d06401850020f000c60540b9a10310383c2204004c4c6e070004101c0d07225596002150079512429501031008a0942c0401d41c0c843c1443d40d100100e841c02641091400c404a59140d804c2e0000401803510f400004071403480740c806032100c102003250550003030701746a071000c1c3d00d07140c680c1c030080006a800b141444a400c40001d165040750780b2a51014a018140e4800c7d00300310340207440501c614041c0c80c003481316036039440a01038003404100c191022003083d40036019252842c0309504041034046150200007042840504150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 123470044 1250 123468794 123468799
    0x204020a121a03060f010303050f1b07030602030f060a0f060e0d021507021e0a09020a18031103010f110928030303060914090a0818060d020705070611030405 69
    0x880d4815044151207800528415242092401d0300c0040d82100c0601d02102c01d00042e42601c589488801039031082c00001d010240206004120b14900072041e40300800103a10181f01c10700602130302c004000d051180c1507006480598021013440421403101c8541c90700400b0803030f0125103080c80e080c806198800244074500c280890a030502c001500c465028000d11035006280004603c0c0c00540ea40550b0040e1030144c4c041c40019a1485508a482511021001e40104408040351a0064500c080d50210a2180400041d116000164114a048a009580310303004041d411554107092500b16089490302e440c0d054201069080c000c1c04240448100c0d41007510320041a4207048014540024130501410200c14403003000024168907034082d10a4510b80042444281d40d02e0704501c41075442078800c168180c01108100002035004001006a0046a040d6415035405ca80024207103130010795100b200f003500050310004000e014040b00029051508040041d555024442952800b0b00d004450 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 123471294 1250 123470044 123470047
    0xe0f010f050f070c1701050603070e0c07030c0b1302040c020304030c03060b0a030b0a05190603050606040504050c03161502190b060d0b07050a030c050c100b0f030a0f0c09020304020d020402 83
    0x2420b014003070040f2188240c02011041e029552115106030030104010f084545500e0302c000f14185150101d0981d0458498000031480c64403014440e41d950340c01000d0031028060041b0700340c000100c4110303045100742804682048000d02c03070b005000075100080110011900108070900010720a8645081565000b0800250021025020070144a107907000500020640410440c40c007030036030801d911860a9120680d0683e000d210240d01707480f0315020050494100364001003450405504c9254424025012110300201c0e02e00071a09011505540d40100b00d0130040a125550348000005101c032824401400b2030001c40409654440d520310000703100d1030f800740118546a6401034a03842807900b0801103102801e00c05406403540c1c1c0300812000201e404d2000c200c02d441c0c040c1040d160720f1640c00014159165040f04034100404942443d242d1100315a00d0001c9142ca00300010800903102d0940c0110000c014203148200103515840420300c0b5004004000041c1c4840c0081d030b00d11641540d016 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 123472544 1250 123471294 123471307
    0x92d0619030f0f060b03040c0801060e0414010f05010b13081b060d0605060313061503080927040c0617010f060503090a170d060806041a07050d02190e0f010f05 70
    0xa001408000f115076030283d0500c940803405051450045000f284920120b5403200d503140140c900340e80c1640b240328868400000040c0124201d413078003401e04111400001402910640c60074202d410a811107102d0400c040b8240c0c0050034450380ca0300140950100170500f10702c1c1c8003ca8618540942c401c07038003501c004904944000080c3d0001009024000d003001c1c0c0342d181a41210901c4440d200081c0c602350b0a00340d908200404243c0d50005480d08192203500c0c1210300001e01c0501243c1c0484a01000714039590520200e9400100c140542d1154036060346003481c0040c0100340100201c8982010b20703041c40100304000c0700452240403645141080e0740c40e566001c6500c0c5c200407040f203001d000380c4c1c22013255510926400c0003c18440c03050b800100041611141665501c41003118010004240c0c0c1c0f813081f1002c0300d00000b040d0301199a152251070000202481003d90700718141100ca002d41d81400304214682040b58106840340680d0880c000d80340650000f00600d0009046500380000001c54 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 123473794 1250 123472544 123472571
    0x20105060a14011808010c120b0a03030e030a0c0e0f061203120411040c03060602060c0901080a021e0d292202090d0b010e0a050f010303050c03092d061903 68
    0xc4141140c1200c004c290341a40d80c20140c1c00381c00c400448500045548410502d00c1c41148124804424064050603440341150340a841400246031103540c184641090100000c804d011100702800036100f4030b411500f48074001c201ba605002c0e00513446405099100381c000580001507501c401a11000360405032034504183c007647c441070308115000b81c20504034405068045c0c01800403203d884c0d08641255641c005440380c40d010b8201d00e180003809080224803803006503006805d6205040844031507200c0380f4409908140d11102c184e900d400c0e141e01070f0070004413001c5a90201c61407a50f801048840d401d400051144515aa6110000d02d1510044070040d0407075050312842000a065030400820324100488500c500340710f03411591407240f000810f80021030044501410038000021616400c651701500e6076007004e880c0940a200502c0303030b8012a83c90484030003140c00c1718010210203420b01060052600c051521460240108100f00c0844035140c603400e10840e040c1c1d14001841d200030a52 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 123475044 1250 123473794 123473807
    0x1808070f0209070c1202010204081f0204260f070b0a050d14100f050a030f1707020619110d02030d0c1101110301151103090f01030905010504080a0f020105060a1401 72
    0x6900890508100f103012030b0030130fa040318990700480d0159040d685100f0102d0a0344100c0c010492207400028190011000d2040c520700442c80610026080944644070f0008000648c00d8020500300c407030282154a43c8140f003100c0c0b610108030040c0001031b0420940101030b1003105580d00401c00005034a9170b10092951000107081d550141303074a89401d003d02030b0003200180d0300901c0001300c0c0c806d600280c01d06e05458010100c940c80104018602d9160b1038545000e0710503001c54090341c504010010050f80c90800600b50705821841d0203440b40c09024004019403082044481c1c15400b01c000c81032529000815a0041c4810701c50110340183c0c84031040303c1000207440004030a42c20189001c00301d051100182d8160b4074108141c07805a40e071440c04841e4101c00d00310044180c0c004000c1a01c032400c214a4003250740700107040115241901f81d0381c0508552040b078045c2e03a110b201003010254150b0113020741c0c94281c4a07100a018a08080c400212a00f03151710800c3d03000d0b100316803003400a900030f00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 123476294 1250 123475044 123475073
    0x80112050a02040c050c24040206131505040f0b13090e01110c070509090a0b010303050d0207020d0c050406060302071a07021e15010905222103150504180807 69
    0xf80144000140140f010b0b005070032495103c0c01c14024100404c0e01c101407401840c581c2d080055500c10180c1702ca800b407002d03680c410707103501c407490100c603401041c210f518804c161050a400d94405030f65030310f002c4000302c1c0980c460b004650610410007071020000d081048540a407030b44180d002448204d400f092900402c03401c0e072885101040070965801c1c0400220706002290340130780d00300d030160f52440030b45a11100e480600600d2001c4120040c404a4406c001502c03449128180040c6403203402e80014200e000094012104000c11104c240035600b01405948014521800d041d400c0c94115514050521912060b4030130951205d030008444a100b080803c010114055502c251000792854080e00c6080710341020742210110000050710080328820f0074803030b02e00c2100c02d03260719a08158172455641d1050060720400c0020300021812481c1203081150214503442c002141c02e015400b803006900c0580c8118441c07482c00c2100f614002c00031150000071681700c1c031200c0e5078510628000100c50803c9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 123477544 1250 123476294 123476299
    0xa03030f06050418020a050301020a050a0f36141c05070f0308040303030b090610030507140f09270c030408070515010303110109021f0c120c0c0602010903080112050a02 74
    0x11190300d0030f1384443c4010344600039514684000c6c2c4400500d4240d00c9003030032800014100b0494441c1d180d200309c4590783e0810711442c0034400410310021154141c0b0780005544450a40f901c042841001e403078a46400810110060503514905030000070014801c02e4000d003041d1050201c42800c010341800300d840548041c90000c12155203d0800c5103031f078ac0207400304801080c900b5900c0491031030951001c03803189000416001706c4921a2b40101e01810002e00200180000c52601d90001d81054019000d002e072403035107494850390340c03004004c04031254032440041d1300f061038400e001c0868201c48840d8000e808a100a0b569260791070442c56521038404003610700e000303038580f10406080101c0c55a040741e0090f038031110315801e0242064200c40c00e00b01e0003940b0904a0f0001076904c1d0403180010490f444505107804d04071080d40f00c9200c103002d8003184400081940549504106560b40c803030000c1c020754402000403c900c2d5070064420141130007054501d041c180d0104041090800c954807509901 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 123478794 1250 123477544 123477551
    0x9061218050f120702061905070204140709060e090109050910060e0105010306061106060f010c02091303090f080c040f06090e15060f010912030201020c120c010f0203090a03030f060504 81
    0x40d4104592192568030790780150b80a8041c061074082e0b011025540ca0903002000381d49008505d1501d0700c1c4c055141c040410070f01500388028005a6105e01c07c070394051581c05e840f400760b440e0a500c0181400c1d070580025090001c4111607541d5510740807a10784c10348926040015040c2c9072229400d00d00009842c0e281086814454041800034030031850f1812100c017a03c2c1802241d4403618162448500f60309410503503441400010500d20f480110007501401c1814058980242c540110711060011500d26485c40c1000c1d541e03c0130145c0c440303a410020021070403004c071450b0500280e640c4909001c40d1140c852511280e03203038016866540a1001045503180c00c0061103000107a1544488400000d0030100070b084000440c14209441203503485070b4140c0d150140e0500f040d01c3c5502d0190080d00c26811598240501c8010840c1040490007051040940030f40705d0440344050b41c255601000941c50303c6005000b40302200600040c404200c076814180890850341d4007003424000e01c065840150310906 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 123480044 1250 123478794 123478841
    0xa0c06050603190f1a010b09010e1c06020304021216030620030901050f090102090310020319050c0c0615210109080a03020c010b060a020a02120f012307030903090612 73
    0x4d4407001c90342a81c8036040044400c10a8501d00e85070201c248240c1c0740300c02c0c04111801f603a6100d1505e851100c9002000500d14002440c20300c1c411114a610803240b069000042c04254a03011a401c0300c0500050020481000c0010b120441e104083c84010003a83e1910800c0d1500038042c42044064040d40400c1901d91410055050203017a040e111124841e491300c000c503c2900043c000c550408601600414544003107001d1034009504c010152003d0703d040500041c040c1d88140219800ba89440792900d4513007503140c010740d06245000d0800d01e81c1142c0f481b2000c410b070b01c17690756180d4682251904d9008a080195107540905491540104413440c000780090b2101e4056000d001d440080c01c002700303d0040c128041c00028801c0c2c0040030096400b017100d040040c5400e802a442260748403003600d4a0940141ca01401c1da099120300740c200d682404500c08441e0310141d4041d41c00066841c0c1400119913a480140c42240d607070003090204000802030045050903500203016140d55210001d86412 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 123481294 1250 123480044 123480053
    0x60e0f2407200909060603070b0f09030304080a0507060302131814011e0b0c0c06070213060308030a0e0102070201120c02031e0901091d150d05010c180b0a0c0605060319 74
    0x20248010310711442841020405851300090007500c5450083e0040c40c20311700f8481d01c0405500040b6001110b4607007003080b1a0075440a10251006014107030090841d22100c1c41c01a0034150b40341c2100f01010f10510250800c5109040c4020858084007405c0e80e14503400d84060019050702294201006d808a00009000d000799100d51550820140004c0c5901d44401e40c007a03252151514030b60807a4069920031486190507001046098070007840c80792070311102c14030281179541c00c0e4800e4841c164003204100340a01d0740e000d41d003d6001801c00031413401c003990380084c101c1d96000c0050303c1c446540781c0944200c5802042240c914107000c0c4170386070111a18805c84000d030390003800d0b02400203c202100080440302080d065100102c01c0740c140e039647d591400055680100250703900e6001d1460001180450000e101740103c21244d41e9442304030750310740c441418141000798480080074008205150007103500803850b0094035440880850b194030b41a0000f07207801c0e58038844010503040000b4640810 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 123482544 1250 123481294 123481343
    0x30b0d0209040c0905010b18120c090a0b01030b040204060522180203041e030f05032502030c0c01080903070602070203010608030c0d0e0319080706061e060e0f2407 72
    0x1c44613200140320907a01c0700d40300f190394091012000e50301c4c00380655112480c81c2000800c02c20103803240803280c00301c2580d00046c038203800503241200b0980d40c4d8035404102d0359150044d184400d0041d00e040d49000d1030039100511500c0790340d41608590004c0c101441c500e686144e0040c0c0200320190404e05110031030210780c070003903100f40d03800c448041c0441341a40c5411000b148400599405460b20391141c81401020341d003581c401044122128880091280154280c01c441c40300e052145c0c0c02561941c3c0c800c06418a84485610b041e4140601d0904000c00b1400000c112108940d000f0400350310b689c141c5c404a8090320068010510601020a0503850090b0000b62445184070507901e20440c02010414980c4894070080440408602c0411610100c0d003c0c400500d6100e2041000161440c0d0710301550203400340e2440300791a0080c030590104481c951100a08134070270021516003100d082010002080d541c3d00c2c11100700c21038243e08020551007102d1060b509410b030800300741c0610301c8280c16494401d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 123483794 1250 123482544 123482549
    0xc15040e0109060509071413090608100908030a0b030f070602060403080a05090a02010e130c09090e2a150d06030b070219020909070f0f08010b1c03030b0d0209040c 72
    0x4200003031000095044450044104454018068004546449401711380100c041c1240140f001d5081001c440408111400180149100382001075107038100030f0080d05251380310a08014007130402d281c51011841d804d0480307030000030075000020040c941c1408a0b003001d0405855401754003d08d0b0002402540100d070a620862107a40c03011120b545d40d84804007281c0013070b45d42d800741d6400301d9851801940a03d00c044950440204503103040c02290b410302e815682030302242e80000d008100c0070040c4001600505500b8842500984091600400705090484000041c030729000e148041100ca02c3e11006280054040328000c01e0307940724440344501000c0c06061000f02e03a92079107040081c0303080b403020480302095a0000c492812500042e02008001d81d409070071152907002c0e0383c900080c00c0c0d0600303520344d00400041c4c0d0800480351820030348600310b0f4000100ba6014071201c9001401c92034403080f441c0060740c1d06044c006024110880810000050503100a4101c040001403000780000b08908208 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 123485044 1250 123483794 123483809
    0x3072606091506030a0b0402010c02010e031b0423130804081204080c04020c03030f0a020405030d03050f0106020604030c030807050405060d020c07080d1b1502070c1509050a15020c1504 81
    0x20b02c1d0322180c0516035161401030380030b403000072501c0c007280c010741c42354003d280d03410b005240c04c0040b450b640c000242032440009003004000b084c11281480c41c00c09018942d1030342801014028080c060054800128400815070304078144a028403404010041080d1070250100e0011079aa52101002a805550040c002c4084601c00d42565a0032494107000300c2da84289920007441c15600e5401001c020803c1c041c3c030182c00207409000c0468140c80402c0310300d08101c4c50766000304113030030409498003003940103030495811500004100030100790041940c40b05246c1c14600000c9076920641c003112035000300d400195002070006030811014942e030b00507107000c41d803000039202956034901c0c0350f59407100e000c84002c0c04503007c0c803490b201d120340f9040052001405481025050765000540c0c0b0201c1c1d0080c80e0864142801908c240401c41401241c0d010800e1306040c4290707403d0a2400240b1017144510407050044000c2a9100e40d0b18424401843d26000180030403844503644600c2c0750302074001b0301800c0da = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 123486294 1250 123485044 123485083
    0x30a08011a031506030601030e06100e1005030c01051c0612151e0f020c1518060106212c120918060607150203060a050d020307260609 59
    0x10480e40202040783e000c0c01c95280b040e032070311005206018264000410481c10b041d9100c81702500c000091080d00d2082100c030f802d10030f500381042d041d403044000143c800e4401107041071080c0142d850004032481004000d0030800d4507020030103540c5000d50b1644038040c807510b040150006000e0000c00104989601c40d0904a66041c440e002001c201c551000a90b19018000710100000d04819031044400915070180540f800040d54180762800d00c104103a05250948001009144d102e02060080001c081401030081075141c824024001d0003e44100c0c954a800450034052007040360b441824180d46e03841800d880c00401c84555898031500c1c0c0302950441c044c1080420081c07180104444e0480350041107050494207200d00c03107801701d078010b00e200d4201c9004c000c0440400c0302c00c0d0110408200350900903a4074500351040c0240c8070040d6000d9405454800342d607a0059902103807007000e485600900d00890001c4451a01d003104090280c185903025003014014030202c04030300c00341858049116503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 123487544 1250 123486294 123486329
    0x70501031137110619020714030405040b09042d02040c030b0102280b0c130b1c091104150b070501140c0a020709020a090b0a0c0515010815040203030c030a0801 70
    0x5036414207011812482d80e0b00311300c0c001041c090081e25030b0810f26035009001800c0014a6079070031035241c03162038843c0d41640081020003861030140034541415009903070010786400c0550702d000c4c101d450b060185000c00c6c03141821b00c40a5a040c01440d01040c3c00903c10b101d40f0000001c094001c0440340d00f100e0060240d494611a440d100340b03103100c000e00d000b0001041c280d12540311008001805400110f41100c1000702699000710040d88201a004500300240d6aa20041000b020500500400010390b070078800c18401080c820305048160641c00e9402040d00c6000200802004015030000b02c10600c01003488824030805511000100e181d01c042c080182d100c0710041e452500610b08a00d0042e0b000960501000c0e4244e000340c02d0b948a01c0c140000450748070305234030050303070080c0e1422000140690000c1d400d01c04c04010000107020494201c440350f5042c40752960729481901c969906010312500800c04540301082207800341d0a0070001c0d2900d80d0464600106604020304c95512614101200b1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 123488794 1250 123487544 123487547
    0xb1f18060504030201030902060903160f0f0b0313150c030902030714061c0e07120b0f0c0a0509030307020618030d0e010c0b0403050c01050f01090c050c070501031137 73
    0x6290a4858503203605003442d2642e07004402502507640d080ba0484810b02c00f800841e01c0070441000c070038820b0580f44d442e4908028400740000300642c04001c5640320440b0403c00640c00c00d08503504040031094001c1c52040354200b03244000c80c4280ca800a00e8a45401c0810a5034141e1203408180d100310162841d180c1c0d1100c020240c100e90304a4694462410062184000c0514801d400c0d150400c20000c646a88441c1a503800d1a00c0e99000c03c40000c8000090f00422607040280d0b0740c86a002c0040302c80b5420300e00b14640c060b0103001400401d0160000d03811100399401c000352100c03a9070003030000c0e80d160795100120480348040107042780244500049107144600a089420342000c06a481002c51001c5488403444041d0107081a0284201081819640a0280540e0740305501540c0e403400c095252402200840e4070514030310007005406d01c60102100004540282224400d1802084040d00010300b54100d1041c0f5100d203440806000903001c0c81000101c2c0c142c5800340da21515011640503030780 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 123490044 1250 123488794 123488837
    0x60906070e040605060a030221091c21051008100e01060e041707030c0602070f020111030f0d2004230d080d0c0302090402070c030c05180f04060b1f 65
    0x136859004406101c15800688254040c011115081b03529203a241b0351403100c4461a0000e49800b002e03038004041030341020424a00640c0201410f00d0802d000a07070509160011a1104408010460300c420229499200071000c0704080e000403c251500f0b0340c4001001d1000341148a15960107500b028400515840b001400d5403007950020541742d25105c0307845112201e940324140440a005d4100c1504000c507405201400000d8401ca502c00c2d181030f07040c0009400d00c9011100403030305a00401031052a43c80c2d40703007034407140310b4455404501c258030140018039004107980901c01070038011500203400c40d1907801d00d07036840c3d007615030103503420300003105100400a84030005410300b03d08000c07600f00b0004561000300004a00d10b00141050140b00028007664003240302a110000c800d00c003801400000c800003802400101c4611001e400f026032075644049004000241400c00480024240310490300408140e0340c000b0f00e516050186a00180001c08108104030b0004101182280050380110b4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 123491294 1250 123490044 123490049
    0x30601080702071a070c17120c100504060e060f0108120d0b0303030403020307060b0f010c330c02010f05040c030b07170103030302041e0302010e0409020a0306020a030b030d030b010e010f02010e060906070e0406 92
    0x22309a1120f042c100444541d110141485c0a4400c81080104103000e502c989402907100780004109a142020228600305d4090152081401d64200400c5038860001e510900c5001c1d81c100346807a50075840030304e801082d9000c00550140000804c000070194040018510309100b01d1041150b05152014000101d005034000343c040b80b100420075011843d0b9800720203500c030000180c041d00c40e4640900e0801100020144c004a545a0103d0241c442d02070058141008007200e08119501c4d054640c10240e400c54480513203064042d1021070840c521641e81488101c5402c072103e2001c0d42d503464018003d5003c2d119a055592500180e0f182101c0d84c952410704981c1c05940b400c0c8681100341c04c00000b2f20361204100d91003203c0c1e880020000f400340c00581a07a900685000402c281400d085c1820140c0215030b9008151812038405110783c1c010380b041703403540405e10304405002c00c3c03a8000ea0040810340021b2500d4030690b8204240d0600002d80c09101d07800744c2d6914210504400240000d640090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 123492544 1250 123491294 123491339
    0x1020d020c01020c121603050c0111011103060402070507030506070c120503060a0306051012050c040c091d04080f03101a0a0504181805060714030903030601080702071a070c 76
    0x313034162080d01d08071000382c511103016001e8901035980f060000783c6000c01c5030700c212032a4016100c803040f20340e0070410888605103880300038099044403110004480c03100030241c03445154041100c4042c0002002010042c6510404039551340c2081040030f4503a004000d01200c0c0803000300101e100252048041e00e002d107002400c10000740342155515400f1380801441c41c0043c05400d040001d000c3e0f4940c2080240c00d00400c00f4141e0040e0080a21080e255098440f0090020580042201c1d0702d81260451112080320000905134a592410a00c1481038400e4801d405a020003401130198032140d04404440c1031001081e801c101e1301c20201090701031150fa041c00f18034148010000035480407443c41c02e003034445000042a9002d00800c0c5d211b03440340c01c0217440b140e12907000c01c8201c5820007142901002480c12240c00d62406801c2582d0f0303484000e01c1e89040010400204482038000c10480f0050007a4200309202d0b41381c141400040358200e08003c0d00d0801c00f8400000d14003444028a86480389003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 123493794 1250 123492544 123492553
    0x14071d0105040c0c0f11040e03040914010819120c080304080309060708060a090504051e03040603060f0e010605071103010609200a0c02061e0a0f03140c2502030105041101020d020c0102 81
    0xc0e00d5a8507800d1b01c2940440d0848c0d215100301a1030b0341d007800100060000c2c0c40e000030702406400d009000c080c3c0145c03c03c0136943d0140306607001e1402a80803707040c841e0700c104448440d040030801202c4034407000b000145145008814007080003102005948070b420094126030b5503940b483c104503043c140a85006800080d14082801418119040554800c1c09075088601d1100309250b040065030105034051260b82020400344000741c1d060003040010035800b12106000740c103111210072111810b02ca041d0034031000289201c02c2102d00c2d0880c00d14420010000c00c00c1540d1861860060005190080401c16580b04a1040940e641c403c2d02d00726601aa10340c444d25a40740d003402015800005401c0d501c0c0400681c0b01c0300f550480009005608080e618549020321921015040d9014410349565507409002081090f41004055800c844441141500302c01089030704010901c032a424046d42550801d8100400c1c1300c0c0580704400c40039020f0b82100d81324100701c08100d031100784d52112640182c01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 123495044 1250 123493794 123493823
    0x90610050414060405030d092103051801030b0406080c2d0f01020307050609150f04031d040f060905040218090307030815270c0408060414071d0105040c0c 68
    0x9002ea65510350409000140b4080d142c030002071800c0e03160810f000000718000c0c410301c2380400403441924480c82020488000d001250340c090201e01800305034040f81c50903500f0f0540700303a10079040710b6241d4070090410007400b51a0940319485507040311b00d940c068080c44114401c22400712820011001c00035540151352800c410821250080b1240c0c2281184824454000032460521260740200000c074000c00300d0703c1000102d81e08214008005a0401e0100c00030000425000b441803282501262010005544144002801421011520451549464404641c5509540c000360003140210344910104c055402e8188010748101c4251800c0e07003003031281c0400240240100340c1c000241580c10344e41c1208a20114680c0c00043c056200c07003c46403610040c06100c5000d001da007124140c40c1042c030303141c10010529035401014200900c05030f18008003000315003003030003103001614202c1c801c0c15008200c07100007540d5040078010300c3d101324500000007807500d00800d00c0c0c0c00c1c4590f2020118080740e5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 123496294 1250 123495044 123495059
    0xb04030f0207141c0f0219062d030b0307090e011514011b03031103091e0303090a171908041a040f02190504020309010c090f0605120c04150306050906100504 69
    0x2114103011550403110191079070061795400202c7d032245000090311844203141072801804080c0c104c054920103000380080820752491040e02c400c07640450b0501090700150000420300d0850f9940c80208440c1c07070b100304520327028010b420140624041d010030902c1c0b5a1036858404108040c20105400311f01d002005213000195168000655402401d0004105140c050038840c1640215900c1605402c02c000d0583e1241040300f4101d216108000114118944040384030359401f0044405031120b2818420303106042000030803a5071400c07084205020303a03022401c01900007401075034211060080c0507007070100b000d5182c1040d485135402c44214040c540c034607024441c0320342c485038850390100303640302d004586601c46000460164900c6000011500c10203c40105205080e0f004400072001014040040070b034810241c0d094400d0b4181c08216a49802000c0461881140e2004441d0314081d20520003858055020300200e52064590728030b00d9585900b00200541d0359400000031a00c240810301254 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 123497544 1250 123496294 123496339
    0x1a0301051531020a170a0b0310021b0d0801030507080a0c0b0901050d06080304090f1103010902031008070620010b03060705090a05040204030602030603120a08130f0b04030f020714 79
    0x40080c100d46840e82e010048041050764802500c81d800715150140e240140b461a4280d03580c070426001042080d001c0e42c07800241c8440311034a642070019000700344c140803002c5049152018003010400c4482c10038589001070f1640000344000d842d54080c60000149007400882c0140303000e0791142c80405424100800300760f1b00c0d0018031060341045814020045408241c1c85000054015a03008649a40c82d004500301a1001b4201b5800902d04240d0701010703c1c2103460540c1e040d281200030243e180d945018001c045000303668000780b090b01c174034040000e00b950000000704840400d440d1351b00c910710305d406445017030380d248200b090f40551240f8001132400f403084c4003800c04040c0c0201803c2c46aa602e00008084e41c00a403c1075072265400824080300303190421400040c1c0248004040c02c18841180107016441e00801c20400100340540715800c0220241c50b40e581280d000035821003e0800c0d04004100070101d013010070240c0705440d0049448103040c0c0c2c0c207004910004240d40c0a130000c249940002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 123498794 1250 123497544 123497599
    0x7050a0c0303051b0d05010e0705090102060112021f0903030810081902010201061a03060f01020d09270216030206060a050d020d0c0f030f060b0105041404020c0703061a03010515 78
    0x1000d588494500c000e8004c000100801105030b00702080b40e50400090400010000e058241400320801c01502c56903004188a0b04448542c007081414500b02d00126040003c030202c00c00c2110b0003140716601d80744d049003040c2c00f0b4a0280c1d403404203e07500d4159502c0032188030b00621030103902000105070b10503a0903244401540c41031002240260355824505450b901d045176505030240301000f00402c03400c1a20105000c2e2000744000c0c81d0310040740f40c0260a0700024000c0003800e50f1003803e6100711840d13501d00c4480c41c2011080840d038501200180d04c3c00340324504801c0340140034150100d121464429802400d6510040521442034100c1c1e0800c164030f02102803c07607034145881400641e004101c1a00c40040d80110b258030b8404016240c020102ca6209028905021003800207004800c030715000d095154034152401603440f15000005407801c405030340000d054600b401c0040355541448030445040c108250001d0040303440b00d6502003005203004100b181c000c80c00c00c844005900c02c07104030200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 123500044 1250 123498794 123498811
    0x5010b070b06180907061e051e070b0106080624030c0a02011508060609011a0417030c010f1a040e030304030318080c01050f130c0e09010209130b030607050a0c030305 73
    0x3024031030340f44240c128030031210440c4642000c8001c0012a4010016403000e0342650070518403007280340300c05002409844010380c0c581c00617038403900c0514090710071248007a401040104d455a51148003c140c850b0440c0c8282c0150314243d501c1000700d03105101c9038203030f80d01041c410b0305603581d09205910359000484940119901c481b0705c1d440e0b8801c030700a90f00162980d00b0191440d8549001403101d92401030f40804a40142c224021030451100820381d0b090b5440840c0d456583c2c070641040d103203180181c403681c4106500e0b00048035100e03256a84041646840965842e00403445c140803c0f003100d41c0603040c1c4e00d40780c02c10400600007a00c00d610469910904040c1c1040303407007003519040c0e0a50880000780307030a607540368240615450290354290f40701c860b10390318801c10080c607070faa002d0b000c009210300005103010b8408141c030f0b403200790103481e501da10180c1564060b02c246074400c4081d00c0000f51481c044d0261070040b500081c4220111015107119407124035008255640440080900610400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 123501294 1250 123500044 123500059
    0x1020d0c0b101208070b0915060105090a090c11010605010c02060d1d0706020109200f04050c090d05030405090c040e0f06220b03071e14030f0a032105010b070b06 71
    0x2031031404007003d881068014034559480b58814a440d41600401500d040c840f5801410b11a52031014101801c3d400394013841c005448000c120041001d0480d1b43c0c002520310341c140401b10084503030100d80c14a00c60310303a84c000d2006960314401545e040400c014041e4020000b0040d00480b080707180c10900281030031083c41740103200f03120001424005241c00841c0141d4680088209214030810751450754032068510048403080344d80000c040e030861541c040e000c4c1e601e07000001c001000003001d5818440004c2c082000c1c0c003609180103a03c1e54050700030b880c030811078100882d102c442d1200640302501c0248940030442d0311780516011144e0b500800d110350001c0b01070300024607480340c04021120350010000100e07054044a007018206100d070340108404040083c854100800d404240c44119031940d4010265000654040b03400c2822002c11451644907024012082503442002c0c841c10018038405403400c1201d000c00b5030281c580c03c1c482e0024501050000f100420b5180c407540307030064030040900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 123502544 1250 123501294 123501299
    0x606090c0a14090d050d08150a03030318120f09090203070c1e080f030103022d12010e120301030c0605070f0b090c12070503010630020a03170d0b01020d0c0b10 70
    0x8084c404034280c201c81c1c0b0b4106031600300185800c1010a5002040006d00b1000c4002c606c001c5500d0664612014040580700c404003c40c0184507841c211000d0f420003403642e8030500c46034014000340002e00800b400101020702c00280c0c0002c4c0c0c8240c90081304250307584118030300e00c1c0c2c40c2c1094448500f0b00c41024403d4100c42d00c0c0004020030b000305200f52004d010281c8961450040004002c00801c0b45000c091440307101b40c0e0801491101c0a42603201160007508a11000d00400e0040ca0700b451b42c031038035200f501300050ba00b92108002d181228030030782100542646401044030580201500108400090360300b50000030320b4400156480484001103c00700c0f0394480c0007864040c10b04a030240e4540000e101442a81030a00a00000e40f106048a46c01c0442403030042c00440c5d0046103003001c0243c0241e80740110354590781d040b0001d46d00f1442c0448042070b4202120034580c80b2054070014107241c9400c8800035400032401c43c0d01f9595988440f241c101041d1610701d031581005000311040c980b4400d01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 123503794 1250 123502544 123502549
    0xf1202120105070206040c060809060a0218090a0207060605031605210118050129040e070b030f0105010e0901060507031409100c0c060801050307061d060a0807020606090c0a1409 78
    0x142c600c5240203034014102403d26081c807401488450300400d0400c00203504000d60a02c00290403070300301000150050f076501408000080403040582c011341d002320307800e00748081d9500c80c1e0040c16070540162030402101c0e50360b004140c1e84440000321042c0b0000c1059041006251111284060100d003c040c015000071809030035085692104c0ca203003884800954407014030000744241c200052441ca8100102e00007a8940c03036440c12032580b518810740e1130321185124104144103010007000300b003c0141c0c803401d00000056082400b405064005100c04003070700030b6803811070300041c102c54680e11041e140000944003180c225010301c0c050000c50303d0400480c1c0e06034960360a524410125a80c1d90044c600051411070070317000c810741c402410851a940140302558010071602c1c2111007508020300074030054040020f18851000c200c0f40d01c0b00c400b01e40c91100c15000140d40b48182c4c61542910240e0391040100300300359209444036040700c00107000070003219026043c69003404103809050307030408510b03400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 123505044 1250 123503794 123503801
    0x14030a1706060a0c060b0f04090b090601090c02070902091f0c0b0901090b1906030804170724051309050a02090306070f050904090f0507060201061e0806060d08070210021c090f12021201 81
    0x2c082b07402950001c1085001901032220b580034090581040c4240409030b0701c02035682e103403402182c403d1540052440c89580d00d010300f80102c4480d4210700c3c114282c000c003000e42051040c80c01a40c0208000000543c0b4110610940c58525482040c2c140036403070b1110708c9801580400b0440c050169a00000304c041003907070001e80002e00a440412424000815030542440d4141c0d100d8610340c0501010652078059a500b62500c2c0401031074119110110b400e9000d80c11110341e402525514601414051000980c1e00240303841038054080710055240d00000300e9030718040c069038400003101404402541c1c5040e0300407555803405400c805021400949400f41400c070319030301040260b9507695040185400b10000345c0740414424010341c00940ca449034241c0c5900c030080c0a540310703500c2d1390030701010860000300355440140c0103810314403200c11036980655681845e40c05149080340c02d425440c1d040c0d100e803c4000c196040c2c0b02c206851075290880e00701e4828180c1d102240c2c000401c61180c11419402d21 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 123506294 1250 123505044 123505061
    0x7090f0209041103160e0307050409030927060b0a09150c051501090506060c060c0a05040902180301060504090f0f0314030a05070f0903120c14030a1706060a0c060b0f04 74
    0x2400d065036420309250724000c07a406100c0171020b0003800000003070b1540d00032554004407a41030302c01140c07004503032501706c5142032260080303c1ca103084051260391000c4000401c045d210b00c10760f810415035031070f880c10603c80d014031065200000c0054205020703d506d0907108580c0480f0600340622001003e60f40c450034141003154242c2d000881c40c0042206200324000c00c0c1d00800d003555242c0c5000340794101142c0381c203c000e001a54020001946800031841141124018002207400715150034400c40440800402c60031081e100c0e41c04c0481c0401d1034607291040140d850781c080f81c1c21001001d00c2d0794003a2030840201041e010304c038a000350ba62a011141c0002d42c440daa2003440010a89040100a0300c0013205074070400c10009100400e0000440d0324074603611070001750a1210f88840185040c404c0b44107005001d4000d8000072031001c0f035041d002603061900a0802c2e10341c0030195190303020f003d214019080340c1e100048212900601181680d8030070098580060000d064181318180820103503074828 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 123507544 1250 123506294 123506321
    0x302091c170703080609070e03150601090b030108031305030f03071704030b01080f07060507080306010c1103070b04170102090102150a0b030610030204050601020a050d050f04080d02061f03020307090f020904 91
    0x1408000030340c1b603d201d0b090f5000940d8144180080e8804001c80e0341c403100c55a425003148109400700f02c0c07507030050114030010491107810f00c2c1d0f01e6848a01003912074100350036128045004c00341c0413441d0f24021030030721b50244245008504121184c1c03140804040080880340520008100200c0868440c4200c0c40c0078001302002005640440e0003c58501740b1554400020803909000c0e10001814100c2100d1300003000f440c0c600b5184055042050384da1800500403541882182000500c2c0c0d40070101a10403202e04043d000354036501300900c1f03401d074807810907000d006800c0400c600f450f10350307400c00707864005061100004802079441c010900d0720b442a00d0f035889030084c1e404104114541802601d1b0310640c01c0c40500800d1030650b540542d2542221008424001d02140500300d680500090302d00514004045800784070b04104c0103500c0310000d5900302c2400c40f1190b9903106560704c06090800322580680148a1940b03004c908a0007802a0011605401d800704040c1030107550f680039108103200325 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 123508794 1250 123507544 123507557
    0x71224030804031b0b030411220c02010e070e010e07020304080d0203030402100c0b0402060c0a20010906050a02030301050906060c060a1a031207140f07030f0c060302091c170703 78
    0x40d41040600c00034003940c0051301c0301090805101c4081000c0542e03400c00d078400c0b998032403854140c000540205c3d0040c0134103c0356800c620303e0420b016260700000c03001c204070740007000b03c03158601d100394495160340a4104c00d9141d9000400643d9540584580e11403014415642842c0c0c6802800d41025414002e600050b44044180425850030640910306030449060030f5219114640e18039040d0200140040c0c85240046070900e5445020b2004180c072543c810310403c1000304843d000303800005241c600da4000b40311500f021840502400c1100d400180ca50029800c40e8070300030810160001c000d05039600b0260601c07241507460010090715010780d019660102c2c061220385c02031b04200a0010409100b640103503860404c0300408422103021070342021158071204a002074141c40d0400c2e440030040c1910881d1400028402c003070b040000d099201d54040c82181c0e41c0c07020b08405074080c51a000354041c0c00600103000e810343c2c01c1d81d91810b00340300b6840e001f0114000340e0404400c0d004528240c010411 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 123510044 1250 123508794 123508799
    0x51c060e0d032009010c111c0b10060c05060f04150e0102090f1c1106120414060a02190e010c0507062105070207030201050d02041802070b060306071224030804 70
    0xf0446003281c107880209030341401c4c002c01800080c1154004040038007a1a04194050115100c6400d0396100c60101110300140080519012114100840b52540540c1c840c1c07402240c1c580c13052030361070303072041d0000010155a01c40e44609090580c000c1c00c1156018226544091241c0c0a8061040c2d04411100010f0300d44040d40180008800c0f00440382d4810301000f0298162040001d04503035086070006c106002d088640c4000c2030a51149132080d0de403401649081004200c02d401d40d61842103803100c151000e91b25042c803148103a000e06c0450204514000c14100c1d0000d102d0380e14440785500524200c00501f480c0c1e15007a0900b0100d421000000e10081c0a284941e52968500c15041e40c078041c08000500d0320a0340251540b4503408024100039002031300881c01c03a031030b4041e074018100c80d2844004c8a041ca1102900961101e20b04456542a840c0000c1c0c0600e40403500318481d07401902c50b4800c1c40c1c1c10741084001010801d06540c2e0540743c440a01002042d140d030184007541c4614601940c860 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 123511294 1250 123510044 123510071
    0x7030f082b050a150b1903020403211704110603070c0b0718080f100b01170901091104020c0c120f01060e07030e030f191202160c0609051c060e0d03 65
    0x3d04d00d144078600b50303580e030070100142c9456030120344205415895034103601b11007540c114041e100d2944054501584ca800030142000e10240e042c00c1030290707880703004020081000441d0200d07401c03103000e0301c91300710100c100005017002001554094407a180c890246841540e5640072120141c55080005042603c000401551510107030081c088540003030001f02c81c107900300740d5200080d96448481a44a10781400141d0003420404006030088071181c80d280360006055000b4010358800b5079600044900b1049541001e100702c8040740000c501420034103015009100c5020f41c08020b0b644940300703407040d00743c4a01003031048901410031092040c4180c10004402015182140c5101c110b64004020180c5038016074000c45402c0001c1c015031030f2290840c8541505c04c071400c401251a1a0300004014181c0365158400306030b0203102e09034400c43d903a107071842111501280d001da550001041d100040c0c01080500f4010f1a85101c3c00020491005a41d031132810f1480c2c490711b210109466055807820350 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 123512544 1250 123511294 123511301
    0x907031403070b0114010216140102010f0204030f020d08040b0a08090c060c0712081b011d03090109030209041b0e040326010603020307030608030301080d090807030f082b050a 77
    0x4a00c400a500b0036095443d800c4100d10103110300b103010340480d0641c1085034028060343d001544001c14080700d203642c41c200c403040f585d075841c0800c1c0103501c0c1010382c110003c0d492003540c0c2036907007001c400442c15070f80742e00340a0350311084041910303085014840002c201e245240241040c4400c0d41d00c8048600304200903034940498802400d114020612001041d002c0009003103040b128002c104d620140128200050144202c80c81c2e82c810260000000000c003005400608620050f54146505090403260b0aa124065140c0150018601c46002c10140c60042c01d2640c0203030266003084100040800b65048442460707003e8461010110200400c0c03640200036110303501d000d900d07403126160300c610013100410414080d2401341503010021032521407007a0310800150100d4402c8a90f81c2d6150000d0b50781c1c03090303615401d000040e202c030000704504c0d1012619000316076008800c440440344c2545ca00c507690f080844001a0340100d070401007080c6540700a240e242f00800c1c0130000c3c6a080c61803c00c0c064 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 123513794 1250 123512544 123512573
    0x22505090c030402060313170a0f020c090405060a0b0102030d02030f0f10180207050c03011109040e193314010e06010c06021305090a0501060f08090a15060905090703 73
    0x2072200920401c070241e29400304980d40414104a0103003204200d2400d501d18140c10804038884082c04903a40602c1904080b1100c00b00213540c085441001c0c10b0001c11442da001100e0007070298100c280031070032103440c9400150103128140142c0f400d218505141c0c20498000301c50301d0703a81c0040d072410301c481e0302e920303501c040d800c09100315850940905210500c4191041101d00c0188660b000440701c06200b0b051080c4885201b00500a002d400b02c03d01088403c1d400200c40d03144a0362a0400640f00c4650000383c05100190706544030011888607140e518080100441b006100901000d051000c240c081c1e1400140c50013402c0700007041092561245001b040c140c00c03141c803c0d130141040c407429a801256039025182d0060015030303170341038216001551140c0ca501443e0030901640034815203c0a5802c100d069640e96a20b03030f00c080c5401c01d01100d8842050702d9907080c5411000410700880c0c002c00b03907000345450303440c0045001c0d65105c0c00c0b4011100c0c101c40510280c1c1041105100b0000c54801c400c80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 123515044 1250 123513794 123513811
    0xd1107180501141206010b030c040b07050114220b091c020d02010f0b030309240706020705060603070b040b071e0f0201121e02070501061a0c060106091a0a02250509 72
    0x102c491509092175900c141c18007039500d08410100015010500b8002114041d01d56101120f40399942c600d0298081c1c0301a90741c1010340710b20200054a60141205041000c00603501d0b80c07a52142a038603800c1c0300150103049440c0901600042c00c803034075141c580501800c2102c0c2e0003032900185c0c4100007400c4510702c00c1c0e02d100403810b100d20191035035000002e940300888102c0d40d00395202c0900f103140204200c0c00400c91750301d203408039901041c805160b001d0100e803401003066a0280d0341301000c16441e90207500548080480620090101c00c801c040a840010703c652501c43c4030901940403541d80c11051001142e501200516500c11942d1100c0358000303400d40f6110030f107c0f0000a0744c0c001000d072a10034042c6005503011a20f401403060075004407008000c04a441c1e052810320642c109410782c09a80c084406100380400000c0162261040d0801c4541c10b4012003004050340403c42d8440c4c0c000074941c02188104601820480000802c0c01c5100190070682c8011901d40380602108240087c01200d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 123516294 1250 123515044 123515059
    0x50607090f05010807020106080709090314040e2202030105040c0518070f0e01030207021314090307380901020a020d08010302030d051e0c0303010302011d030d110718050114 76
    0x40c035941ca2a800055a42c03d003000415543c403004201d0040030b66078880c90706403143c4d400000d8402e0b080d81c0031031041802070b5100c01003180d01c1c5440312800d108512078184080c8401c40081c607100c00d07c0d00348440300c040040d0002950300c41d41e0002800e454003540d055030100d8058034100564a010340881d07801800b000c121000500c1d0054019054418501e110301c14411180030350682c50784280e04485110350300901041009034400c0c420b0f0014000d86480380e90100d60100818882c1c0c2c070000c15100d17800d5100180c3c0601d0591242002e00b8108803d10044110710782282c64201014040a0f1600c07512580c000147c8500da1032400910744031100700150280030b00400141b015032400308d280820701130142801590b0724081b6441040020449251203112403020900c41328a080100046048900076038451150b40b080003824810300403141c03c60359140e031068510000c2c26001d4403402c101d0a182205032690a90360b100c610074289400c008bd07200e400c0d996401849101030003081210030300300a40700c2a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 123517544 1250 123516294 123516299
    0x1b0705030a1214060f01090801050a0207020103150b031f2d0906050307030f080405090406020c12180f01030f0f060801060b0c03030f060a170d03050601230f090d0b0405060709 77
    0x1c449400142100f4041c842c5980385c01c0b00c42e4000c41c03108004008030740c000c000928060305102c0007904800c90403400a41410125420520703a00d032504144c1d040e142902d407560300c4c0d803118180580758135a9900ba802815840005104c52a0502041c0802d030340000880442d070314503400e2015440a40100811a01e030040511207030303c0001c1c1460540358840407a440c00c3d2420f0404d100301e4096030b0310042c0e0000c09402000100219034000d402400b01100c200c3e075542c00b24284850319030040030015419402e4080104c2103514100350078441448040c1000148d42d000d61503800141c481c7d00181c81c1c80780b0344418040060441c00d20a034030040480b05992030425008203082364680c0b00107001100206c81c07800100c0c036a5500c41d100903009041071608440180001200c07240c44183d85a8218080381c50100042c0703095001d003464000c1c038920072903c0c1107005044950301c0702e95001800903862a0005000c03101d007903252045401c4c0614020001840700b89405d182139854240c00070103440030082e418104 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 123518794 1250 123517544 123517571
    0x2041b0c0b060604030c0f08060906060d080d0605060d20030402011715061b1b010f120b04091b09020c0705090426130906050312031b0705030a12 64
    0x5616455020402141d551107800c0015424010380d040500002c580800c0050b0329407003a0381c070008031044807081c1c0e4501e03921910f40a894000031180c842d00070712440c50b64000100310100611711140c3c0c000c40000c02d15251000719400760041038050040b10b550f0380000c01003400d5440c801c503c00c051040701a03d58035207540000c0a920715003d44142d1004808042040392219003114a00d0680103403007141c9800d5510a20404421455001d61846c01121080c0a040116100764282000107845450341c01203000d01c12a840c55208003006e0565549554600722541c3d5402050a034a0281383c00b03188030b1b001003040c1e800205d05070303200a81244c4100000c030820280441c0c2c00044841c1101ca14442da50740e4249002e046a40e8491200c0760117026000700e00400a10000c2c140546085100c10650b584912400d401c540c03442c00341c6076041d80030380ca42c0464054008019540310810300580c18048400c2000b2408a401c10101203a41d50400710741c900c600d543c0545043c038207042089050286c00441d018 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 123520044 1250 123518794 123518807
    0x9080f0a0b060607050a03030b0103060504051302010f180906060806182a0307020f010608120403060c0201090507080a1109010b030f0903130311030d020d02190203010f0905010902041b 81
    0xc00400704510180040e00e19620780003900c0744560003d01751880d42107649030090003041000b03d001d000c2860281e01040a003880e1080c070348607146541c2c03105000403040d001902c04003499840361040141036040601c1c0140410380b40402000038440c046030302814001c01509203072009041c28010074003041e2445100707985000594000c0502070800b180c00d1115407030340c22004104e004648100a000061080e415400244442c1e540c01c0340e0020042140c8545860f51940807101001d09840b9091205002180c032030f9201d0b100011041c0000590144607070b4a040c100b4019900c4004603400c42c012884c14008482a030f400c3c5664100c0c0d072040d4a60400c1402581c03400003a01c074015282c2c00c0400035002d048200110785141038200d009500340340d942e150581216842000c0e40d402402034440412a0f240001004070450300190041c1005513268454445020540d00c0160f0349907403641c090700c040b44114403034115450301410020401381e0403801408159104c101050038034203084110180302c294083d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 123521294 1250 123520044 123520063
    0x41401090c151806031a060f03091506010c080d06170d08010501020102090d0f030e1f0311090a060804030c020405041a1003020603010501030f020d11070b0c04051005030a150f0609080f 81
    0x5d00040120a042c444940c49807115201038000000280ca1001c0c80801000b46100b0305e81601140d0900041c0c42c1000b66640040c2c0748180410200c01c1da01c0300043c95040604900110300f980060510360700d21045410b1907007040c0a62454125080c00407550768444211400b4110a0000303501d000c0300d91010420b81840326101418060841c0b520004040c480e07151940710b031400820102c2c880c40407000d5038400f000007121441c0464035110840420240c00425252220401441c451f05a450484103550900000b441201001351007007401c00140c0c0d440c070806018034007880004024803454440c0c486004000341c96611400d070810b13401c00040c0c0c1c4603811a0305640003842d0106404072001e119001a0041c82c49054440307060180410810348840090324107680910503842594580c14598425841035010351500300d1640c0324041000c6000e1001150420b0b410354000603281c101c4108070034200915086424007001c0b0a07030400400e50300c61030b003202400321b50001c0e05c81d41c1e141d031501a03956882c05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 123522544 1250 123521294 123521297
    0x160b0f0618060f0112020d050a060602010b012309030f06040506011419061107030213090203060105190e071101020c0c0a0915050d050c100e090f0601020c0405041401090c151806 78
    0x340500d00340c07079491b01540d40d5030710748050900040c1028030300c60b006407029028000041d864103a007540103602c5808481c040b5422805010814110000583c2c04d6a0120801035058400c101d500e01c80c0d030074104152071242d4014000341a05504103041d089024034840d120b64411072540d0307003060400d0040351508048460350700b401085c0700d0f020390609003070003802e90001c0e600000f41c801041601e00c039a000340ba4000c2c801c5056580c5a0b03210707000c00203c0c0072540c020f00300d07410540e6820320141c18503c50949d0008414204444095900c56182e82640c1c4100903110f6907802c001100b03259820000804000761007100b00c10300074a04005c910800080c02d41c40ba003132164070740880b05c01c28803506010035078a0f00c0c800f501001a40408101c040c0441c0d4408070003501800f2807000203180c100d40c00a9460090605030b0140010704540d00421000e400c028006480186031044001581d000911452025901c18800803916601c0c1100700c05140e41d524001c4010311520340e000c84103003c0005801c0054078210f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 123523794 1250 123522544 123522557
    0x41d160804030315030312050c030702030a180b070602090a09110901140c011508161503020711130b030c06071707051f0b10030608030906160b0f0618060f01 69
    0xca00b0100c0142c0401008641c0100c0c0780b40011007070503400540d02401401002040c01192a00141a4028071046500e003005800c140150b85d01c4600c5034a1a280c2c10900c40385285982c0d07224010324415a0102c20100c0e44198009072051190900004800041544820410000101d40c517a01154841c1c4210b440c1086a0b0544070361350700354110103507860b0f0301800b00208a030308c905007542c80e111040da0091019601c034580c0c0310700e001d1038000e000000707482d410104403004220588003038002c1d4011040441e441540090101c0050700d079021928401c0042000204d62246c03030101f41420540803c24076401040e040211102280c0e0802400668a014054140e52000142000740c20f20030b42001c19100350269000002400f42d681d00602c0307617054110f030003072420f2a005505904a44191045020980091001d2001e07458144040e0032101440c250104010345542d60302900700c10101c41058051000c5018894641001c170740c0307010a1501e00c10008100d051003000034010b00e0840ca00241002003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 123525044 1250 123523794 123523801
    0x190c0b07030504121115030c04150309020d05060604150305060f04050a0602040801051015020c060901050403060e0105070e0306240609120f06091204031502090a0b041d1608 76
    0x450b41c1100c004000c0c10700008500c081614202241d095201c0010713200f4881045210406c52200040307901400415644510b014035155480202d5001c41c441d60b4281561040300340007503113500c48205803003445003004d08001e150045c200310442d172407181c0307241c1c0c62802807005000140000864507044001021851999035451400c2c03880c2408180c030050065002080c0014090b005410160050481c50b050686d0300ba242e5000d41ca81250400c0c56100590182d00e4039181424581c0082c120b003103042c90401d04d0a07440e6160b0000342c0e0400f0500120b03983d03407141000129a40800d480d46845021070140500c1d0520602060458a0501d500100c6908200c803021056a84808607907a250f0081d12140418201e0680c0c0340d1611450918026280603410000d10403070008148406215507241d0342c14141421900e81080c60340049100c42c0301c0940c204080080e45d0b9038048410001d0040f201100d85c1c40d41421041250460203014040c030441c0194140050703004074880349010301c0c0452402d50010303a13 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 123526294 1250 123525044 123525047
    0x60c0906210e19060506030c040513020906131109090c0405010507110d0606030317151c0c0306020408060a060603060e010e040501090204060b090102010515010801030f050c041d190c0b0703 83
    0x428220760032681516400049042044c180c008521a150840558000c0c2c06030000b40001e03501304961903080841c008441e0030046c50701000b0b07250009070107081c54084d04242c4205804840761b0450a0482035004925051146014200c0661268020580c0350405203003000207402c034080c50760002c014954075644a111070701c541490315822608a807052100315640d040140ca401c011060300c1101640100004208401001c540c03540040040d1440c85110102004d40b0060f1040b1001144d02254210000000c00e0b06400540080c1a0500291000e820403860400c101e5140340c0c84a018507060040c100000b01c0038130035950441d0b62803826482c0315984c51400e1401041090f070001d42c058908030010a010160714064481f070402030f0000c0007540c031040301d04e41d580e039080034549002844c0d000041c80011009280003261038420003c0711403c459a40c000380c140d0305d0001d0351481e1604840031100c0d5880e0b00b04020001108842480d0080030320070389603540344141c1401049000100062520b0402d03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 123527544 1250 123526294 123526303
    0x10506120c0a021c0c032006071101090206040f08071208030a020a12050703060620030912070812070c0b09010e1c0203070e0105030609030315040504060b030307060c0906210e 77
    0x1031800021140b404502020041c05d500d14584003500024800d500c900c84603255a8080703072a1303080040003405141c2d55640115643c40052904036069500e40c1d00e0700005840e0100908084c1050148448020b0b040208440c541810303540091040441c14120350003084082003101d8110036602c0300980e540c2c0c01441c06407a182039100316504850b1801081000303880d810352107001520595502c80d00321800e400400f94480401410060f0305030402c11402c03119280422071b070b140c008405000e843d08640d44908032424500c00c400140f0000c1c000084600c00c0101001051001d0300352070340e609040c09280c0000801505142015601030202c183c020b444905100404010507030340107040300d01064580018417402202071081a02a100d01400b041d04a100401500e200b400000e58120400f4208401c05c0003401028000387c0e1031940d5186140b855880138402000c246006050201c2d0f403034000c4d81b0041c0410840c1d403000302000304106080e0319a00032070761984600980107030045085030880c218203080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 123528794 1250 123527544 123527563
    0x40f020303030703051b040302060d05070e0d0503041526070207080d1d01090303121109040f14090601060207090207060209030f070f12030903020d140f0c09010506120c0a02 76
    0x15100102c10042c2042d855000b2503c5148a41103c010070707001a0560701450043c1d0100039031080080c0038100c0c108030303140d000550041242c49c141d503142d9070000100d14500980c160507642500001018080d007071503605190f480480ea0710f00801e02254600d24800500e20700e82040444440903004140124030030052038014080c1070040d01c212076080000074000041d28410090106819208510590b000b140c2c6c43c412203401d41c6401106030320f05149a0b0003010f0740030307400b0904003061204603066203a0f4458005140400d140000300c00404500d840711103140200005c0c0c15500c140300522800c1e9000c502c00b012a01e6a440150300c90301d86182c00000ba000b4280e106030948a00c1007040c2043c00009a100c0c211004900d028200b2a100c41219160a01c040d0025003c2500c050040005050644141242034004c0440510200c208190030b810880e014041c03039141c3c0d00002003414140350003c015401000c1c100c821914007c00421f580200c104001c00721510751001041d48008a402809a00134 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 123530044 1250 123528794 123528799
    0x6091410120f02160302060c0309070e0c041a0304030e03010b0102120d18050d08090304060801060e061c0b0f01020601030f08030601210203010f0e281103010801140702030a080708040f02 82
    0x440300032981c804c0e09110180813084d00144507003001302d40320000c05401c490141f0504000b410b5401c1c00c01c0241c0907903c50183c070401c40324030200300000d60b4443c01c1c09203c800b441d401110f1946c90800b410018461024400410b200744d14002c00212140c1c1c0018003580c09a0491a01c00d40368140414001c00519003040f56070581c0c80c0786001101040404a07403407001c1482c42c0c1780e603009074803440c404595a000d2805a8004942c0399001403004600802e02d0f4101580001c002629200c24140c8010001d0311840e80040300c0c545071141d144240c0380a880003801005c0078801000b0750342c55130f103c040300c400b45036402902c0404000003203017182c0d03c540000c01445149002503d4003010080b20080258400d2080795200c86c0800408203042c1c0724070000d20b015803060302d131444c191303401d1011a20722150800b44038440c0e030365104400b034401d11700c0701c002d940201031440000a208800382240403c40e88000c0c00e640854108009904c200c582044e100c981184092401c00410f548901c0d2401ca8100c00300006035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 123531294 1250 123530044 123530047
    0xf081b090a0e1207140a0f08030402060d0c030c0210140c0919060e04050a0504081b1618050601020a020a030b0903040504050f04050106050a050a06031116030906091410120f02 77
    0x484804041006025551141c002c40400b00c1320016111b44900c0c040000070410f500503100e0b00089080c0e04c018680040c00204000d14050000d0000c0c2d00b2289001080360100f0b80328000444040d406200d44095958011010302c2003240410390804904001003100112000c08140d100040d00c0345202424420152001c1d60f1050b612008098000090200302c944141e003010009402c500441c05000e0045501c03200240c1402e009a1182d20308080d1090100a60300c24206c80709041c10f000301045004290200414405c0e07441e042403602500c400514203419036124009880c0113131039038110030048980001924a06445a0100c7ca04511440e800994032a007401e0a005243c6110a00f160142c0e205200070406540c1d10000c0c858540010720440303520901c94902044141c1c0a03030011190365001240b0301d4500609002e4044401040d0b44040e000034090950520800b9001604a0050070340105401684c201d08000144412003900040041252158a03401d5100164004460707021000d00c00b503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 123532544 1250 123531294 123531313
    0x30609060f09030901081513061e1505070f06020d021206030c010e010e04090c0807080d020607050903100b01020109020909010b150304050601061b0b010f0f081b090a0e 74
    0x85603514015111030152441d050003242240e140003080341e401d002c068440e10100c1d82d6911100d2140e03c00401020b800070714a400600034410240700d080050718180906452515290202840e549000d410104071070042e20000c81e200354008050b1241e00303500410705582e8400741d1030580e010380552091850782c2800814681d003100314229000d807050710700764110b85288040700011141c9003c50142c05000ca4203c101048050400340c0210710660b000314038991071165542d10144c40c10650381d01118061f0403000c1c01025096060250301d4001c080d92500e103050401d01e0700001d4030b8503456004100c129640f40403030340160b4002e4004030551ba4000b4083c06551a0004580703010745012442e103441240065445481c4155020950703004136002030051501da030030080c041d1007334502140c40440200d034031160100061084281b9901804d003170304040c0012864500c1c1030100303400a822030100780d0801402109c41030a0f65188040744001211580c03240e88404050100030203000c0350390761950040045c00c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 123533794 1250 123532544 123532561
    0x306030601050d0305073810030212030705030f030a0615121e05180606041808090604050910090605060c0604060f021b0303040c050d12080402061306020c030601150f1404050306 78
    0x100f00c590003110504808098590a40b1f080040e41168130b21041d1058080610140c100000740b030521250303040c110f03454040c0b6525524034540014441ea02c007000f0010400801c60000d01846000341034602c0036418003626481c014003600704c400c0a044401d60b440e241164002c00c080300d408420800c2c20000c018609000308100005600f4030440d2442d8420310001c120310381070a01c1510080c1403401c1721101035181d1590740c40c005501c0903441c5030380404140004102c0d91340310b510a6006144446644055502c0c1030f01107803d1700c02a6010900c80c010512030807a40480100b24142c2c0030760702071030028040c860700312807a0090040800382800c0d120008034030b05401900100a40c081c500540fa20402135588508110580050b070100401c00140a081c0e8080036000300661a0051f02c000c4c13090341007080454180c984c512156010b140140e104211107a05401d05001803409400203286191158107050000351080384076000c80c0c020460701e10162003180c003061080d10082e2800606880090034403120 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 123535044 1250 123533794 123533843
    0x708072603090f0d020d0c1109100311010302030c09060a110607020d031d03040e07091d0a1b02060105190306060f060f180b030a0b040c0201060603110306030601050d030507 76
    0x7607082c414402d682522020042c0090030100c04000b81d4028134003c4404907045030514035142c2c044442580c0c58910301c001c0c4e522480303110b02c101d0300c14109004461450801c140301030642030806040c1441007040c4222000c4032400c480e1484d00c02e441c426581d10484c00f08581102c25180321840901034201405502075000c03500340a175008554091140001403240d6080611b1055950701c0319601c00c21040040350f90040c1d00f2a800784007400e02810860f90b4905480124400c81880c0032010f280908104201c100c505c42c00c2c012588a55810440d040b4074900030f907031460103018492195002e500da80389a281904181c0029660100d02480f01580d0340180c10001e4205029080c0800e4103c4051070540c0d11600441c0c0d22003011650a42c2602c2c6030611300f009562019091070441500c0d05036010343d0341c0300d6004400307001800f5400011242d142003030080880d50300c42030440c103000d0100309020455500040b600d055840407039071007200900a180039515441550002810846205420b04480ca134950 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 123536294 1250 123535044 123535051
    0x509041b060224010b0406080903130303020304060809031e0310030618060c020a05030414010c02061c0b060702180703090f030207030b1b0d0b06040801060e0402040b0906060708072603 81
    0xca060141142c4180c90f003070a40024000c4103a03003070050104001491040c12a980c00c1175101d0705591400000304101020312119800940150b84009010841580c2c002c00307559000c41c0e10400355050401d030810036542c201030161582a40000440403500850b141302c1c07100015940200d00b0001d003440c00303e41502e000030544c402d4815614122046055500209241a82c1075001d0b0165140c5401e1141e04030140921501031810401114030420058a85200400c0364130325003401d40b071084040000e00c00554121384542800b076001444803c0040c0c5840c0e144000380720002c074201265581d603c10841c01000e040c000034041441c400c6117041856001f01d49041543e004080504c40c1e561003034445050210784605403000700d502005000c40c1e0712043e600201d16004000c0480746001d944000450035245160008900d41c4c00030f1060104600d040d118001c1112800c4d10390f12030510303100000a09c1d82c0100c1c60040c00c44100086ca0100f00508440b00c1188a01400c400002d500c182c109001c2e40b940049 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 123537544 1250 123536294 123536323
    0x10605031501080c01050405030d050a021f1a030c010f0c08090a030f050c0d0f0303090c05031e010b31060302090103060e0607020f070501050a0201060b030a0213060f0206010509041b0602 82
    0x10130a88200d5104000b110155400a4010000e000784404c0c110b4044e800282e040085018801007401c3c08041b0043c02c1d003025044050101d0840c4c2e62100c0d078017140f0242058075200307510011045c00c00e640c200194002c101c8607410f00031151140ca0401110324401d0418513540b20740c2404002c020008001906044e99005d0000c5648104008051110421010070003402c00c02426141900082c480e800c0300c980c2621031010300003141e5072100032900d404200c070000f200030a003581e05d914060400b4841d607401c400046030b80c0e10b0103040014405c1c04c203110313540e4207000b01d203808072908004048a8101c40010f5a0160240c5500d603901c4c2407000040500c00041d00c40c0d0300503c0c020035400d0f807001854400d11000304019200c010300c0c000064400d54401c0c01001e00355501c401000a20350004c1c0059482514800b40251703a81010040d003482a01c4141c000034103000401c45680c45842d030019440c0e05640c020b0f50307080c60356161414503400502a5084c1024064100c2e00302180ca0342c2d010541c01e40b003100d03d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 123538794 1250 123537544 123537553
    0xc03040e090607200109052b02062401050f0c0a060506060909070503070c0c030501060f05010f12091109040606030606120203060621070b09100306140f0301060503150108 75
    0x50480c12510b600040d210100002d01d0100c0c0c096103420081d1a9000100880380001003800c0742c0d40d00ea900703100264014070f1892a58842c0388036900640365a803500f8044510181c0260301c3e003141002c200b042a4001580c0121000d4000c9030036034002c0c2c0403620a44400c020141c2c40d6040307a0392180d076410380c503e011141d075406c4c1804511582040c1050302c4104000600c0c50f061652448021102a00300a001c0400c0149021168001c2800415a0400f0714040c0c000030404078104440c3c0594121141c1c0020704001d07181d240d80344156405504079200c05501c100c0440c0c1072140c1d0606403003540780c4913100b651200300c2d6018441082150341c0f20004680c807400b401d2001c203030784040307188010025207401307901600000b00242103840e01d0040e40281d5034200650550800f900b81e81580760100e5031300070307000c604070000f1403041603d40746080c5001800b40b032500303100450811000c0350704540c00721402c1d40078094036603101800c2d0f40c0c2904100040c02c0081e0032a6100c05414100000c9100300703210301d4106004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 123540044 1250 123538794 123538801
    0xb0c0a11010809031e131403060c0702030604030f2c0a0902190c0609080a17090307020d08030a090512040302040e011b1107030b010308070b07080f06100e060c03040e 73
    0x1401281c0d1044107090055405e00c49044060000b8025002c0c01c00740340c2000b04403000031064420300c0321029111540021919a200406042c5005006404000010390500142c80160340010b80a60320583c580342c8521a400d4110090b50b044580c06800c1110307688100c0300c00d4600314980341020855000301c1f21041180e660709640e0089106c2c03404400c80c51a844801450840d00404801001c540b203234030002034112403501c881c60f5941140c03083d000062690303081d510440c2070f40c0f40115046025000654642512607002036181141068018028000403001078805030040d8049291a904281607407500c0e020981c800e903141e4030600003240310301d14200e01080c04460510416205401c28046a038080100707a0040c0d074013180395840300c1c00c41e11865001100241e4100d0b0f01c640203501c144406600c0b841c2c6440c2002901800502c00c004102e000c104200c80e403d01c031001c0b544c10400c2503446065080c41944102ca03104c1c070403c0c805030841c1300021001c25545002004100b01d86440c1b03909030007a01c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 123541294 1250 123540044 123540047
    0x4060515010f1d030708030a020105010501080f09100902060c060403020618011a0d15020c011512050a030e0102150108031e041401030209060d05130c2903060a0b0c0a1101 75
    0xc20140031640020100743e58800101c0025800302c039054801000c60307a0301d542d5610010302e10b0344444041c000507515540104603030750304022019009680402c1d141c000b89002003040c1d680e00c0e513810020041a1300c8501840540d201c140403100c0c440210740607154245807600b000380d44d910040d500102c543c05a41c24a00190782c045c4924421a040c1c00c001966541d401020004100100b01040d12465030600d249549440988003c0140c11185000803549080303d40386402d000c10307540c4c0012b01c0c0b04c4290b80c40b2800600d002c6130000300304ea0b250515aa0036248840102d190040b00c1013024061004280041118400000600b0700f501c64900c4404a000c03107840781d9901e82c051031041c140200c1500000344060360180e00a050344400c00f03001d40b810100010300c0d8400b0b0f0b0b071003660b030882e500000c0e0307160400380b00b0035003840030142850145d0702102c41d8210b101054a00c501d412160301504001c4040b441e5603075000c0c06000105403000d1100d880301c140d2821f0b551180800b140440e0020064080c02484d0b5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 123542544 1250 123541294 123541307
    0x5090d0f0507150c090b0d0c03060f05010509100504090e0703120905103203040203010b0f0a090203090703050604051005160801230a0603060611011a1c08030406051501 74
    0x140c2d0f0007200e0715103200c80005020007a1540194007018017080001c04a45590114043c2c942c65000000100740425412809000c0b0b5295030009800441510414403260760040c080742c604c0802074400602d0700351022011105030140360400c440300b0341001c00d49200240006140340c2a45d028042d602400b0030001019250441584916500314410101051000d4050008040b82d82c505400800008000c001c0741202121204000500202c0c0403040c4030650800348113010307029034150f80c08540d410220001030390040c114864520443c0d0004009a1200c0042c000300005507842400c035221400c081c54413907100c10202c078240b80e0700b510300300008200d101e5200c260281074059488104050f4203150040c1c17a1b00707640700407245110188401d0f840381512991480c0f40204496900040d5103400c05030003d10110010b40031040f541e045c00381c900c0325010f6038000829040002c450100c510034000e00501081a0f490a0140c02e0180110030082407101c82d401c064495414044540400c078114030054988 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 123543794 1250 123542544 123542557
    0x2160b03090718060f23102a03081e0105060703140a171f0e04051501081f0b0f0d15021804110a141806040807080d020d120507030207020405090d0f05 66
    0xa02c034082e64081844d0a0149810280c1d02d00741c0340040540351240140923000c1c3c0045004180395030388800c45c6e0181580010341980000b0340d240b1200f048449024110780308441070180c54440d01d0700269100c10580510410200500d40e000ea0030307200c061718200940040b1001040b0341441d141c1c40c0004090141c0d440180500340c10344414500e101d810803140d070b00c026030020022120b911520180c8002a118107040c14004d00720040148184030b214003541c10078490103a1584002c03070505801c541541c2d104001c84841f400e041e00c18500030b12540c10305078104207162500f51002480000c0c040f0001b0501c0441188410054501340480e07801107100500c18821030070003200042c03414218212042c102c100520358140356144211548000350001603182e481580aa41250f100d910200301c5060107000d1626405558005404040c0200354050004819002d0105c40107a036480041d00341d0740a541954140340d001b410821152406520495543d948006141c001c1130034041c0c900c1c007262180c41119207 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 123545044 1250 123543794 123543839
    0x109110a1b0c08030711010210020a09030b040201050f0c1606050301050108040303110d1103060406120c0e09011803030b03070503010c14071e030801060f02160b03090718060f 77
    0x810510a80079030300a84107180044501092024002800300000c20140400307900905c6440c1605d0722190004e40303061340ca405103011060061101c841e01c5604100b0480440f0f4110002c5503080e030f15480100d0306032284036882030b00d818000c500190004070000da13113105925503805034500707251a03400540f0b15000900c580e900003407441c1c0020300000e20a8006a428000020b03003d400c00e0f012407481000e95140050801102102200300301d990f2400707025000042c01d51007440f0b0001912070300d4107051060180164940c604403d00481d14280b003d61004e802c0449460b03070310360340d0100d514008000d020501945403003480794500c082907614041c0300b01b02040059803184034406c481e6004500351504010703803d803000f20303c400c001c1c0c41290040840d000c08a22954070700b4159810f04a000c0d015020200202c411136002649194820007412442000d481036620665181e80d66011410318194982d0001080940c118841c040180410340103281a9185141c1403100380340c0705c3c4190384034029112131125 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 123546294 1250 123545044 123545057
    0x13241d0c07140601080a020f090601020a0f051504110118050a0909060207080a0903120c02060304020f030a050d03050714070f06020c0a06090c03030e040b0d060c020304050d0501050109110a 83
    0x400120a490007040003510036000710140e400b21422003428410240d000f11059040300c2c03e0202145000507001c42c1d450400c41d0990640e007403c10000355035001c2c170507004241c40010b080d080d0a02104122440d00c42c00500c802d07446514151620350441120750600601040c00c070000403160616280801054800213445001e485191450301d00240c01c040c401928919805c020a20201e80305000818483e0075580b142503c103840c514181500c2840402000c007000049042c00005a840c14200d03a00603404562540403295850000380c1081403145000f0402c0c032645c00200026501500140d10440c4e1984984036018000a00e40c0d030345101d0b464000f4214001ca450040c0041e69a034090b07c5a48041021100b5060035540c0d580101ca000e11010380c1c540c0e9040d40c2c10000c255000c0502c1c0c041d22025102400060f01480c007080c4102450440103103050b07211021380c01e8080c42001079a004140007041391300c440710141402070080c2028081c001845d403c040c8003101802059048542e04200c503034a45 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 123547544 1250 123546294 123546301
    0x70309020d17040f0e01030201022406060f120a090b010f05010203030408030702010605090106050405040c0302210c0d090c0f1e1401031107052409030d020913241d 72
    0x51120400561085994142c1400040b401000040e1040041d121000040c6015410750001911b0180740001c035a0b0f49814001c0c0b01c404404580d42c20340d41007001581c0560312a2040d0000b5800f03400b51104400d0b4507443c0e002001520310b0550003004060307010f912850000d98030f5016282c94614103000719409640200013203000500200d00030f50340445a840000743c2d0a8403800007511505082c1d21003c001800420244864549480f0b804002e1b60744d030404524005994450807914120000d0007000016800000b5814032590000c9802c9801250020059914149030800c49010980078101300010b0750840800e40500080762140c0703156032003c104c4880741c5440c600b04c0030114800e1950741050307115541c8402000c0b000c1c01405441d803040340a01007913001c0c0300b0a0500e504207600d84141084a2005226030007401008491030134140392805607032005c088020541058822102540c403610340344000700281c10380c43d500c103019442d400c0e0342c0700d0103a80e881144840c1d410013010740c907a100c00003011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 123548794 1250 123547544 123547553
    0x2030a08040206070203060412090603020a0806010c0201020f031c0f11092b152406270803090109120c060806190623070b0406091410060e070309020d 66
    0x3041e40c01440240300034507140e0b40307901183c1040000d98040700d09950800001e8607198001690700c018020a15003141400214900240074000190045052020001c0304105592003802502038030001c0104076680d0303011598085141b80803940710b14032110f1074019031071040303082c5003c1d107100c4044e0103c2050600c0e480c0010000101c00150007600d10f1041c101400300300d1041200c0313480540d801040806421203c402c6003038241e4000d40011601c0051046128070401c4183c210f03001a24020309d00b0401e5991801425007082c03078186040c0d42c5880018030b002a040d4070000c001c04500c0b00070703a204c0c80003503a2030302c90f0010341c8080d403401000c4026003141409064481e240c01c990162004120310904940440e03050a94113007a00722000150b030780c0c00000300c90700c180c40721408500c0700810603d20f0000c0c0768403607031100d4501a000611080c0c4410140090003240000c0c6c810010350081079810300e04d0300d480488004e050034451b08821200340d00c00039148500074170076400340580190105084070080d541c0d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 123550044 1250 123548794 123548807
    0x602030903060411120d080a1805061815090703020a0e01030305090f2e0306060507022419050c010606030501150e061c05010810020f0f181003021201090b0102030a 72
    0x30f503e82001d540c01e805481c0f40d8040209a8021b0030f140c5800c20503091088e0309006550714100120b480258210320200003500c009841c0b58026045250b101148403000082390800003140d80881c4054558400d2041d03082000c12020120791084802142c40395403030001744100c2070300f4403001d0041801031004154034104440c0050350400000d000074498480c400c40d0301e1041c01829020100700340641400106c1d240c15100e150007a015a080c82d03424100c0f6503001420141044100b00019420701c003210b040303694400261020407080301c0009248a804440007025a0030466405c2500c1d03081c40c1c00020b0050003442424140c880300f24a000c3d11000703442080d941d108107040699041001003194140c4a111801000d03d091a006000300d065450042c0c0e4070702d4070041c0044120014030400420441d500c020044540a080c2c0c058082c1d10740b91703610b281c4032611004030b2049420100981c040891158582e0040c414800c805800565590b02d84500608480e0840401c40c0075900810882c0c044030300601 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 123551294 1250 123550044 123550073
    0x30e120f12090303210a050a062126130519171203100305100e070510090905010e0f07030c0206060d0213090515130506070e01032a0906020309030604 66
    0x1001c417440c0c5008540040d00b0383c01041e0141268034117082c24400304411a0003590b4101102c50800c0c4500c030b0a0824000c04110711640311109100c1e20301c40070301008203003400207040c0070500d0540c000c0700180151389401ca45c00550b2404c0b26013031904000c58245480075421032115100e01603245014101400001c0f0789039054000d03400e07031040128404004203500010751050a8444545584a2640c079101d4134194420203405205030505500380c00c41880010b4090894000b140c039001c070171a141c2c0e000e5030000000e0b00300412080c1002c001003181010307040700720b00480340002c81010326601c00344220100c0d04040f410030016040b41010802c54a4003020f0002c4080c001005041580e400d040c84508840a0030002c481a80020000c0c02024149080140e446100180f411171501050340c0da0a0f110040203100c2001e11540240d0062180d100c1c1e8084056003207056444000d0400c20345104ca44100e030013a540e400520104030201d0203610110980d0307241ca00140040625845564803080300b1f200d803d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 123552544 1250 123551294 123551299
    0x1110307120e01090c05040606091802090612150a060f0c06020d02040b0403060608060c03040f0b0a0e0a050705090c04080606040b04141e1b070204050a0612030e120f1209 75
    0x2000a5414182d0a12940f1035041c410300d0110b65051601d01404107031042940f004050060a030010030130021100150780b40c10380c1d0380800503603410300c07800081c006000310310380030050858000401c01c01c0304031103000004070041116260300c0507030307a464121210031142401c003000a070171760051800100d054020740051004401c0c0035080c5510f410718500650403641c82554442e03204c1a0401c214035061014523040725443e08001c1c80c510f025160720181d1261454002e0080201c507000a80c4240e556000c10070070309000056403811412400c255a0f200c00705d004052042c0c18800108000700003440842d403c40320501c0143c40c00c1e545001c100b2000700100c0c0b02040d00700c2e440340e0000c41400b1650240c2c2c0e00c140c1100c6800146020144900e41002600070f00716200c0f100c9a00e100481c0542a0301074400c21390f4100c5c0d01081e181d0f00e07980c044000d08070580c03113000e0300c04250b0b042000701038000302d00c8191007800307a0303100741002d1181e080d050b0342c0ca0340e40c000e05080da085980e500c501002050001c18104502 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 123553794 1250 123552544 123552551
    0x130c020c090a0e0a2001080402011b030504050a0b03090705030d09050405100f06050d0b03120d020a09031b05040e06070e10030e0312090d020606030303010519050d08120106020111030712 82
    0xe88070881d090040c1140300f15643c52031800c0c1405c81d0801480302036180c0c1800e1800700e01c1441d00742d001030815120900304542d110202c0107100e040500c11411100904070251100b2011640c0d0714401d481500295048611806414800303d51802c1c002021100b4201c80c0c0c0d40c0007540c80c40d000901005007000b0706043c03100c003800f01c004600018410b400c40001c1c0b010780d8486513680855802d6404031420b034148580310307810030006100d0005c281800c1d20352409441800603500e14107a4400d66032000242c2c40140080c2d840c401e92400132259000c05021030b04282e80070302c0005559101180c0b5070104466010115545000c1c0d021329003404c00c070180c42c030006400e001a212016605143c95500800821824100000100650300c101840300360300281c0e040c00213041ea4244400041d44078001401542d00440219a021060702181c001080041001800000691015042910003a44440443d01440c455600001411481440780c24240c40d40c201409003582c40d41c40c8200c4a002250b529443c0c0d0548 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 123555044 1250 123553794 123553811
    0x207020402070c0602060c03090a081c09030302040815041a1e04050a0311030c0c0105160f050d0e03060103050303072d021f02120105060d1b030b130c020c090a 70
    0x2910310042c82400c0c0a03090410074a4a804070092600a00800031000c1600902c00e12614020028010091070390142c4e100f61a0011b034102c05c0442051380222072861800c10b120a414141c05034024815a540001900c3c03590701808528007149506440040c10a5483e110000c540700d0a408800d030000000004140680c05100c20210200f406640075201a0004a003500c1015081982b21f800c4041303c0c0051400c10360500001e54641c03030340c40300c041e052140001700000a48062022450700542c4170350965595130850604507900c41c480303840107010a943c004816180e207400140281240d61000044d8030715a240034085403110403001c41e950081614035116940211030800d107a000310400d07401400125a20200c0001c45100c0e10700300000c1a02c1040854042c000c035800141c1590001e80d800e0b42c1c0c62407070302d0100b4010800c420704243c2c0c292000088103403150340340e001042c0b94282100d4201c6d1050b640180c180468403c00604d201613480b2035802d0241d4108414800c3d444040d40381d0010301c800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 123556294 1250 123555044 123555049
    0x70e09070e0a02121506070204090c08030714160b04060507081207030e010f0b010903030c1a01061e020106060e042412021903050601032a090608010e010915090204020702 75
    0x15100348407a0b540104514402c4804986030544c400150505580f0103920030010406912a08402034000c41d221280001031015041d0008000c0c1913a0b0704072651040281494106034500e40140c1c01c550154484c1c2d84c09034943e490b00e41041d250b000070014070f00742c507040042e5402d612401c81141d0900042c00b540640c0b801400006106404a8802040c100700d010030180c211595801e40240c01e41c41d118848032180da103c1036610507240d0504003102d000003541004994642070012050814071803100101d552a8080040249100254045818840c40d11416402d98009025040001e289000e5941c09807a05070081c100d07050240403288080f540c2c0140c0c00c500300c41d23640c20004000001642400450801c450707060140400440e202412500310b81d20307544c40e01810710026120b12080340301d01c0b50007004e034103400d000e00070300c0140b5006a558825070b0401500d60b40c400d64800754030704040319055110600540c0e41c003540c44815001201c3c0e808602900030195644c0980e00036500b40811001038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 123557544 1250 123556294 123556319
    0x7020f0106090b091305060711010b03030304060b03060703091509031101050103030206060109080102040e0601030c110601030f030f0f021f0b030304031a1b0304030302090d1506030308090a05070e0907 88
    0x8204490000c10480f04040c1070140d180d00181510440c80c002404000c04540c01183c2d484c0c1011181c50701e41d400d4000100901c4c05800201e2445515000c0001400200052a800206060b10507001c0d0341d501c2e5034128040d01100c000350405005185a007985560400b041d501c00200700e031003810298006c018910100b821518260002c80159000ca41407105941e000120100280000301c001d514241c20100c031b603006000040e041505260b245c8280b040c0e4035000e55207090002e4030030303412140250b0392414000c00c5440d56034400c0c0c02240d61000240c401910030101c46601034650f800514900c0a04044900c11482c01240105620341e100d00c046801d590500c0104001c6018003030041c1c00b0030304038a010181740005042c0301440040c6a240d914019090820b40b030780940c01d0709005032039031000310106500800d1058001c181429a84040340e950210354099801d6901a954125061341e402d0500c50355504142000391182d44280420004020394042d62a13000c3d506206a68011b0713980c1750001c1c00c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 123558794 1250 123557544 123557549
    0x1061509033e09010918021507150c030c030c020c0d02011e02060a0e0c0108041b09020301060f030b03240a1b050403050d030506060d020d110a090f0e07140307020f0106 74
    0x14048891000c070b03640c0c50040d03c0680545039894042001820300d550740d04021890b00c2000f401008200130681001000c5819980707980d4200d80e2502c910540406400003e210506040e00441d00d002c1e1a00e900520a00c01c1ca10142c10310340003096100118410041c0040914100b28100904850b9102c9151503108a44503100400d4000b4021030414806610560742c00c03e000105540c0500313201c2400d0f80e0b11614103a045a0420039249d003d18514040302c0555405800c00380d480b5000000004200340e2200900100d13070401d54041141c20303140d44c10035884121416000d807056441c41000c2c20014400c0200982141e070280000881c8031400d000d0b500c4841c5054100008075401190800c2031201c01d021140600c1004d2030700700420702c2c2001c0000c00600800810360281d50b030104100641074030036070191415450a4a15a44400111500508200c0d40b40034181d512807101500155090b102c149940c000d00d030716250140600032445210b03041e50001800c2208521600501021941082c82010007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 123560044 1250 123558794 123558893
    0x51803030d090c05040c0504050d05010207021009060e090603100b1c08190201060506040b07080c0a0b010518090d0309031701180b030a020d14070b04090e0106150903 73
    0x2100c02c4a414403000780d400c15480705010354100724042e07940c0c0340e02000300c50964008076015130a009246c10224024040d04030002c2d000750010880034600c03604135600408403541c1d40c1c0c0d0b41488520b00402e003ca01ca40c00d0361a90381607413160a480c4e04c0e1071056040039803c2840540010030103944040812005220f25106171085180059441520720b50b410802412035841d00007800000c1c82c000c08170740a03103d103118864001101081c00710030064a04210344401c3c509108984801080341000c030f520420030322440d4850000182e4012180c004261002d220f030303840d20040e0005139082c05040d009014484801c804004480c40b0440b500c5400305072090280c030f80441042224581d00c2004070440344401e4100d48294042115400180d840b005128100c0e540300101401110032080c0c01c9247c1401c0f0b4000010346503000ca40880c41d204981d21414001140500900085a5074141a1800e081c51845100044d202100c10300104183c01680c01c0f6004000300d5000c668404421002071000d0700130000d4030b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 123561151 1107 123560044 123560051
    0x6080c0403080d05180d09031103070806071e0804240b0607030e03010c050f030c0c15040807020f01210509030706090503070b0703140106051803030d 66
    0x400940d480030392540c49019842c0f510026001c101ca010500501e90300103216010030001d0900107018464880700b0301c003400c5031101c1000744520309920340c040c8140380c40000d40d040204091403054202c0d60f2205049410708690400365811101084100f2a14600b404080b402d61b161480350020503400e035004402e90701102c01d0103002c03960300341680726502040d0f0406041d00001c0076241d020085008000802c6030700d10517140c9010300702c1281c0c00c5003000d20008440d030622000a1903001441c004603040c40c01002400484c5110031902142d001401141d06800c60810140c000468082400e04444041000c0040b031714803d15403480440241c2ca8030b0125103825014003c80380c9083d00a201840f5207007007400c1c21a40e0364017207002161840e1b00c19000886061080c810421030501184084d01c1d26460601c0484140d00700d004054121800310410b00d0355580c0070070041520400540300030 = true := by decide +kernel

theorem cover : BRFrame.Cov 123381294 123561151 := by
  have h0 := BRFrame.cov_init 123381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 123381294 ≤ n) (h2 : n < 123561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
