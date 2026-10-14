-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0909
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:51:57.837323+00:00
-- url     : https://prove2.me/submissions/ca587923-0468-4b86-8419-8a55c522f22f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 163309352 ≤ n < 163489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 163310602 1250 163309352 163309381
    0xe030a170c04050612071206080c010e06211305160501020c0d0b0c070206040b03010303092103020703020f060d060f08250b070c080d030f060e07171018020d05130803 73
    0xc010810001f8041c00d07a10043c46e02421009040c0b80006e0806c442103034000419012203221110f000e0201000740c2c1c2e0030a402d840c40a480c8442c00c00b046000750300d510b0340d40d02c0406280742000d442c80c4101d02c0d1845c2d002003001000012502c0036002c80d07107009903000601a030384060310006061440300c0d0001516000c90701c03006102d820720040ca501e10702030302d440d0b584030160020381080c1e000072180d410600c03004400040c0b5440690300016820040c613165a8029614489400000d0003541d1205c107441c4540c4560701959a90505d0800500180d6220401d490f2003031064882c1c3c404502c5007502d800d8032100d0a400c855a0ba0070300c004021011402c103048540d40c4e62001e20112032000000030005002c2c0d00a1100001020b440d0790049800701080810200740d034080c0d00000c0f901c000e0306082c0008640c10981d24a80c071014044000c034541d49004081540503243c0d886060400c66200d10721038400b030765900604d8094001e9404003c0c91f01ca5400e0540d078010101001020500c01f0008590040f404003030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 163311852 1250 163310602 163310611
    0x6030c020a020307230607060c0e06040819020d02040f0902093105030f0d0605131107021e19030510061511010f140f06030606010c0f02040e030a170c04050612 70
    0x100c507001200c041001c6450355100030800e0752615501c4020804150f4003141c20103c000c42120bc880c14541080e4580ba15101039850300039030140c3e10424070045403207800e0b002c104550000c0040020000c03090309c074001742c941510700700e20940050000611440301000b0b1031442c03c1030040128004895a00500302d030006104041d1843e110038400114a0511035004100f60034200303402085140c9468244110101400303030608026050118004000c2c8003c2c003039511017501143c010760f0480860103600c01401500440c2c82e000002c4900a4010390030141005044920440c00c80e05100761800d50601250343c1c9001d82e60001c00c205514406a074441c8080c000302d01604400010b810f0004c900d42d20844003040e5515201030441d804000c4031100032100c40742d00c074100b640039290b28600400024540340c501c0f64000d1401c0d031503607401010754645602856080a01a040f00d07541d1043d924060100305454000b0201140280001600012940c00365021540054041802c1200c180300f0414071090041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 163313102 1250 163311852 163311899
    0x15040b0a290f0a1a0406020d0c03080402010c14010e0307020108150a15090e070804050c030111040603020d0e06010b120106020109030c08030c0c06160e010e0d020f21030406030c020a020307 83
    0xa00100c0c0000c130344440d07207000341800c8403150f41e1185000006400c101e000c490f00c10901802c4a0a100070a800c070717003900d50140e424a0b15a4032031590745441e000c071003e800c5914500351f1904000c814050000001403056034000d80740c2c0d81181c0c1d01c2c2801440801c6842c0300047c1c1201c4c40c01d10400480d5000fa188000d44245401c0c11043e06807103500129064000710360a500082003282400309020303090000c08aa10000c1e8001d110500b42ca000c405090710407481040c0030160b0004604540104c0365108034541500340090742c1507540d40303d0740b55a03650010b55055086034a80c4c00006081ca0051040203420b691503103801e60000c0030b6884200641e00000d000c2d5450940070030003485148024801903100b01020102d4540308a02c03c20010030342c2c914070802c64188000d01a440c5240d544030440e01c0b003c03030340c100c8840124202d0000854289603024661030301403a41c0402c4001c50030800310181c01076600b140e504015007441d02c28120385e207410100d00690113400c01801888564a401687c200498540 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 163314352 1250 163313102 163313119
    0x50321010812280306050a0b03100b0d060801060312080f04030210090f021908060a0c02100e0319050403021009031a100b13080712021507030215040b0a290f 69
    0x440b450024001400c9250f0000c2c0d5245000d101c01d01d01100280050300a49800c242075113811140d83c107031649517024002c003008006c2400c50f4410280d1704142c01600c0608024030032140e5038038054014001c070600c80c0c03002c55048000070f4007510f0302c6181d041c813a6401d80c0c0144500d403000103199000344040c6c68280c4a042c3c1641c4800c0150b00c0381c20b4200c2407030103114000742c078041c40d007044241030903405020100401d0a00540c002a50350008880080c1031400724001042c80403184240e196220300c1c09024803104990f0602e0b032075560828041c8c03045034029682039103401c1c20100c1c02c6a142c01940801440f124207040001c0c0c0f10303500704098a9002d092105042e00c20364032407050140d01e030030503a40f02140409181d01400740304801e000c21001030903038040c803010007815680040c90028000039006540000441c040c2e007414801c00c50140e00d070708c0f105600030700b50800e07081926154400702c8404101e00c1c2000940c0c01c1c112407200c03018500e22050b4500c800021020b00c104000300c0c0c1a441ca95610440d00c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 163315602 1250 163314352 163314397
    0xb04230d2d02150c010c02010b18060402210103060b010201061d150411091f170703021201031208150108060d08040833010302030d030203070219050321010812 70
    0x2030100c801405003804001c16100c0304e0301d2080c02e0950715603604e0310086904103400d100c15510741c1c09491806110300108641c19a036000c0200d0300a02601c54154011880300315105005248861828142c0380072340e0341071141d040d90f8001a03099a0b09849008400c0294a1031240f01c03220280c0055040407110741084054007048002130290342c0302140035101000c00180c00401480e042c03048200f40e0045550040c2500c12000e000380511580101c0c101c0700d0401d440000d010144260b04072940f407944400140c1203541c481c1401034003d00c03040a420702141d081c40120352481c5030020301d0561303010165139101140d61400148414010f0401d0111000d040c18080410900c4040c44200034074003484466981d0241b640e200e071560790b0f4580d169810013102c1d2070f005001586002c10114595103c60a01580e00d460341d8804030f180021902841034104d030345c10004401c205012005000d030000c0000d07032585171200e8070807030001b4a1080c45680a554000ca041241c900030a0001d0240981e00307040c8000311441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 163316852 1250 163315602 163315609
    0xf06090c040f0f0e0606041a0603150324060a062d030b03010203150a05100203030406090c0b0c0a0302010e010204140d0f0b010308030402041812080408040b04230d2d02 74
    0x20313007011401030700f0031000c0045a051034410001075041c62808080100003080109810b488090400420420000001e15042c1c40800c081c9545d0086581c0c40b1900358400c4091311803100b415144103204607020744001405a101d421341c004128800758140b4180360002507400c28009624550310145619a80fa01d0020343c0c00384042c42c4901c1c00c3c3d01444503449002e50802042940c0e47d0010343c86840b40740c800420195001040d254800e522640001c2e090300207040c00440b0749a1580310020840c80000c281c6031391200030801c002c17003034441e40080c00a4002d2480c400d00380e00581c0a41d000241000c102442a0314002c501040340500a0840381c0b640b00140d11404001a4240c00c1a608400000140421410288950511070407180c040c09034900b03040d41c401c038a00f001005401e08010300040400c0c14081403004440091516807110340e03031542e0b41c12241030b0f04406010102243d4007859506480b500b03080800c020040c1d817108210036091240034500c202c910258020043d040002c03800c0300c00584 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 163318102 1250 163316852 163316861
    0x201021b031216110a0612020304061506030209030c0306060d020d06180f0c080105190203181009030e0d0302030403032a08040302100c080f1b010f0605030f06090c040f0f 75
    0x20107145496000e4409400e20740c2c114001c21a055001740007240782000910ba000d80c2c5440c90740d628440140ea291220f09040d806071030b50305203088806091000024020383c042d0300070110800c06805035468542140c0c02c0540300c0c44103d03401c4c0d1b08846d103440e6003401454580080074509102c1c1341c001031170840102d8520092202c81d501154140d00d2440d105042c4100300304c6040091000600a1003903280000b2008228110044103a02031a0080081038900d1b18009803c810707070303042000301e480844005c44208060b28180c0d0781134010490840310048a41040846c034410303250590001c40c6858034503901102e110320041c07101110608200720100d03600802c0161030000501400c0416225829801001a00d2104c0c451050900c00005504000100c048042c1c1d138406519091103038868410205000840141c804004515482c003054200c100c500b0742d010909403003081d0b0441d6100c0c0e9150494555440c4162510000e0768070461109289141580141d8079203c50b4003008501d11f00503030349480c1542c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 163319352 1250 163318102 163318117
    0x10201060909050d111c050d020c060c0d14010803120907031a1602010510030b06030c090a060e010b13150c080705010e1c051207030615121103040201021b0312 70
    0x913003100406103000c0754401c8108504d410080701400d102d1101e100e0400c401c000848042040c808042003000c0e0400c00d0b541070304c001c844c40d0002c0d260b261031300e40c00410040d401742c50344501d16440c02e01d03003484203d441800325058031180c1004615110076000d0b104000040180703841c2803403003a898040300003a0285500a400d40c84164114410b00f04140c4c0e100340b40c0e800320311040840e03141c4000c1050114000d9081d03402c40380c2110601040da2643e5011a040c800c1076140d05810010700401e00c440107005601c21402c0758404841c1220a913240c54030b41c10b0521035001c4002c1d40150780002480414105100c58203029601d080c0100d0046450b030364a0182e4110360415900d0765940c00030003540080c2802588a10b861240700341c500710002110160041c01850600b501c131000d0b070000200c84600907400380c0094184582d1a003c04005004018080c0020700b450301e500e103041c14040c16081c14030754180c80c0101d0341600581408803252090b281408903440039140e0501c40c1511050204942c0340082c404cc = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 163320602 1250 163319352 163319363
    0x20f0f0f25030905010c030c020907050405030f0304050a090204030308040b0c07060504060209030f1c0e0d0206040824040c090906140115020f06010806071b0516030b0f010302060f0702010201060909 87
    0x700041d05018201c0c0465900180c1403102e88110710001941c00100740023020f42c101d880050135180c1032030460301d83c021600101d415104458201d02000b0000000d4801c88200b1200750f01c6481c1c540700c00405a009510006003c1100310000c10b000030b400700070b41507010b001c200c82c042c14014251a01302c240e030303816101903404560002d1039608500f018030022941c060854000c0030005907040c2001ca44002d1001b840e010440c0c80c0303500e41c6080e507669103680c00e8150000d111070340b05d60f200c428141c2c44060b07400070341c4d00003e5100c04041c175001c070715030084c1d10403070b040550440520700d4600600060818ae0000301c4111780e41e1266540f10388180c00f101e5019215584130092800102c00c40a483d000c03400d40d012502d544802c0c010803000c0f100040c2d40d54050310a1800401c1c00c90099031008003c0c00c0904002d20707600508bc11041001c0c1e40b00c00800850340149655200c540312409001c2d100304c020b00006c0d410041c00c014101c00240084010070150b0b106100011315130741d6a41084003102e51480007101c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 163321852 1250 163320602 163320667
    0x150303030209030105070801061e020c06030703020307020d1b0f0f0f050d030e030712031e1410171c1803050a1704080c0d060204030818010210020f0f0f 67
    0x415050074800e2646c400707294202158954103100c406000c01088108000c49001b00362800c0403407910070300444d6043c0300040c0080f41c41c0c0c14400800b81c0a50400c6501000620400e9003124804e48207400e084070484040e2844a4024030f1615803040c48101035606596094424402e01e00007028041920103450182015060b143d0708000024261600d042848015a000b4085e200100c1d203c51000440c025103403e000806a1010f6914142554000d020003060707031a103820400e20003250b55100d48604410a00807d034103480c0d101c100140d0001c031104902c5540301102e8806032540c4014001003010711802d003040380c1c0c40a161041c2546c50706400403280e0b034000c42c0e001410000c10f8007080848000d00e00205041c20b05100c044d82d42c1c0c849160754580f281c1030310141f1030f0500c103542e41120302840e04007003903658a0341c1d0000300342c0180d01c00108042c014810050300c609500a20300c00e9400d14103035840f115140c440402c4254206800403611024000c008000c42c441c1448100e845d154103c801c001c4a00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 163323102 1250 163321852 163321867
    0x20c0d1106070507080d0b121c081e070f090510031a0607051504021c0b0907050103051b0717070309060909060e010e0a06031b1811090d0302011503030302 68
    0x5081c1100030300707000240002840403000182c00c3c3c000380c54070303880e19900c0020008580780005260009112401040b4040c040c1c1c2480711030203c00c0903111000841c2c231441055100c62023080b040028080d9030304242908a0301049a140c801c1d05501220601c51402c41a0103890f0ba002410114211a0b110b0119564200590300d5100390702c15502003000850b0400d007081d6550700d55980314110b06501e001c07500403040010342107540e003a1a0904043c02c420382031661050310b2405002c0200d042d100c007003003803040c01000640c940c4203006451140c2081000424000c1c41c3c80c030400300d99040000202c0e210038905000d10300790010a00a09030003406030392240c410070f25004000d003007912180c00a18926003002801d000c9541c4240100f41107900030701041c1e90326550845c0c00402002940c20081c000c6600c010304c2e050503000740c5001815a20741d111105151500e103076001c2c045803a101034036080c0700c0062024040c18a82181c031142e80c1c0b0301900010403004010b40d0403801c0502c1507041100440c1e40440c101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 163324352 1250 163323102 163323137
    0xa060b030c1b0f0718021606020c0c0d050304060c0201120504060203061c0f150b0904050606030d050711010f0908120d0c020609060a021602060f07020315100e040303020c0d 76
    0x490a100c000b501074918060010344003504d030701240c02602e81c104105483e109440902d84d04076a4014404800c00f500f0322003600d4080702a50104010540c64030400e0100c81c1c5074680a078001a03070f41d074400300031442c0c90320b403410a458000d030040d8180c0c18011044e1361049a210113004083c440c41c45003100507544d00d00a020003041c89107400854290342c0200c0007103400100885105501d1030341100c0994028a041d000d50f002800e03c2917801d503040486d81042c00104031002907500d00400e0708806403000f00b0100d00049903a8062400b010b8180848540d00548d1540603900d40070004480346010301c42542c440c0c10141c90f00b14012050388034200009110403030100300f1b22407103000d800c1c0c510180240303040084030036a44000103046240300a50018107119551214500c03440020350140146803070f0380399034014050315041800241d00030302403048d000381d0a002d4980b216210f4031000030200101400c04002c10f1402034014811400c1c550700b0415000345d00700c20440000c00d81800d903144040c026225144 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 163325602 1250 163324352 163324387
    0x2010225060c050c060403051602040c1d040209150f09090112020109051008070e061605250b071403160506100602010c050919090908030a050907060807080a060b030c 73
    0x182e00700071041c010704130707000c1010421642054251030a95151040240340319a0902e00940c001d500910303041c44088069003040c1c864040b0300e0805502008180b011092000f070b0301c62521015409120010031000043c00c1002511010a450f02c5440c10804100c001c6503c5110a80004041001c02c040207021581c0c000b0301c0c40013510041c0c81c80f401da440d00b0b03a40549602c078003400800601803c5001052640c840c041503498188000046054400072800c10130b85440c00b90820340041c5444502032014404407041079002c94541121880c5422a1912086012a540020030050380010810a50016000a100168680034038041c0c9034901700b07002c4038944814141e00c070809590504038500d4100b41c0050079034181210a540c07104d0040317040481c01d14091b00c40d8000100741c51424859500380075000001d50321a8030345004c200010380b90410000d40d07540c0c0720f00c0703000700051051001658082c8541d68042d004003048502044d01034035800702c800184c108490501800001051810300d80d403010700d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 163326852 1250 163325602 163325621
    0x1e09010e0a0b030123130b16020606120c01050a0908030301150f03050609010b070203100c020604151103011202030102070b18010c1812051006080304090e010203060a03060c0201022506 81
    0x2c000c420341d5015032174443d0501e00602d007480246000015003078203c01b5403c43c8401e070f01000486103842c012404900080e00780700190014462407001942c0303410401241c8090b0001c0d40024000302c3c0071840111020740c40b102c0068100324561100154111081000e140038003543c8640c03107004203904c0700c020221038422038001c0c10142040140070300303500e860000e1070642c0d40703000300e541d0354140a001083c070b00102c150b0914811890030f00c04081c03450b070202c0c0320350240d0f01c00e4007400c031020680d0303042d002030380d02d0140e048007180d07010001000708248085c02c20010318070240015061010b15242d000ba40c0004480b4000c80142e030215507400c0d01428801c6248071f81c0207061260415043c28010f24036030344903000f00c0300002c00800c2104280681085119010b40201e4018000c1649660000ea100c0c0c00c41c0c4681e94010b401e040c3c545403614018001c4c1c910030342c0c000e031840d007203140345d030b251200036155034445d080540d5401c1062080c004e4056424050190fa42d4030308400c408610700d841e0049940c42c84 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 163328102 1250 163326852 163326859
    0xd0c0f082d070b1e0f0903070c030b16050c07060f03060b030a050f06030a0b040f03020705030d09050405070311070219050607030302090a08070305030732011406030d020a021e09010e0a0b 82
    0x1c2c2d01301400c0d00342d1240d26400074802c1c401486143d0f0354440303080ca51300c00d80c20050812122407800108002016014a20030341c4c88140c801e030540400e540581c0e550061075444981a044440180310040c80f0f08201d00d109820b510300821807230b035900d840390015441030700e0035403805071a0b80810000b94a15007000b5000b0700140c00400140740c413905d80080300b90001e80000c210408482c90401854800c01403030014100080c01d03146806203100e00580001c85c1880303102c0c00b0320300740130001c2c4100b40a4860750030103100d1942501c0c0350000039420804482c41e880b001554912507503102042c1c98640002410138640f09072001640d03107101c401000744441a513030054505e41d11481044c030000f034010080e40c44940d8002003d0b07007000000c04107602c9124820014040c407020403080015500d505401506200441c60206d041c980c440b01e0038103455894401d92000564807400e80c01c0c00508240052104148000e0b110241501400c40000c540361407c0c6c1c04007007c807660f542401400405445496100740044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 163329352 1250 163328102 163328131
    0x6150b0903030d02091206090a14031204020907090b0a03091b0b04121a250f080106120f09030201021b030405011409030a060903030606020d0c0f082d070b 68
    0x210000e07540f807089210703921140da0040f4000c11580c865002904403c02981c042d1744003858148610b0b9503070444001c0a07a100708075050f0036030080902004555130660102090790300d030b07907035038003403082c03116010305030304208907c0c00300000307448009401608800509035408102030001341018024003032400611152030b220080100811460203007241c2c101e035541a103003000d40707030a414620f0707000d00c010140440258042d000c11118481c101e54800e075240d5a03005405541c0d0400d81c040310001000001d95021590b801c5c0144043c50040039100745510640101181b81c20101d80c511003643c82c007000c1200913079008030b19402d0b480265030003000707600d0b901402581082d00c0e000008100858540d180044540d002400e01400e40f000e20029101940004c020720000000b0319008004000a20034040140540c55460b03448901c1880d50750130858120b03660040708041c13130701c0c0c80046901a42c400700c031703810602248014583c0c0e60b616460182d14081c4407207485090074201b0760300001004201280203480f9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 163330602 1250 163329352 163329367
    0x13060e090f0f06011e080303091e030306090105040f0f090803100e070c020103090c0801090c1a12190b0a17060109020a0f0e03010b19090605030609030706090201120906150b 76
    0xfa10604660a8001c01161000c281c91225114041d03a0446201400300100b0001510f02c00140c0a07101c850140310100e2629940f9906900c0e4041501c0445c0e1000b14000100861300c1c094004080300188064000b48030036960f1818000c55000c00000c4a8000000c410030405066845010005207912000501070340303419480101108400b40d0028149a43c4008071000c1c4001c41958a025001001c000c014241c00d90070300040c088000e10800c41580d01500f407000f0825201000d540c18540c0100584200703403104030100b8000d4590300811059180c0e06c18800b007280c0c1d03910310131800030300a042e4480c02c0100f42286050410303005800c8210110f0042011245042d48429144c440e031044c2d20b042e10030200c081c40000c0c003402c42141a5507200429441075200d41c2e00b200060710803034920b4101003114694581c203258649801721036000b217a030001d01242001c6140c68000c1c4401900c14582108140d0084003c001183c5a044041d1102961086554410545100d210300541000c46010742003520 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 163331852 1250 163330602 163330633
    0x2010207170a020a0b070c0213021e03060f06030c0a0806010306050d02010f030f050c0901120c210e06040b09012415020a050d080603061003020d03050913060e090f 72
    0x540701c070700c06699440091001000d61007403001c0d0088561003544102c0a05058500512a11054006903c200010894405591040e100b101c2c1800842c102444100100004884041e040246006e070404007444903501181c3e9114010b510bd0201d649960707072220b040c0c40c0d0007004510000d1185041c1032030800300340450740d214040c03004920341c240703003280003120340301e9088002d030941f240201c2c0c516003080c084c000c40441d1040a080417001c280e9402c0c8844840a070179606454100c00f10802041c0060b004000c0c1040300d401c0300085c050922000319440c5581c1d14103d141c494225000c0d241e03030072f504007842440c0c0f00078010b01d100240d0115050828541d003c82c9014071b2680d030300c50030540c914030104003080b69000740890889039070401c0983c1c18450301d001014159400464545229005410005d002984240c00b03041c1a01c0c0c01404c50303800040c850341c041d80c10358001003101d94013002030640700721407075014011500644402c81d2808110305010246c186040d82600c240742245c0c105001c090382490303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 163333102 1250 163331852 163331873
    0x209030304090f090b0702071a13060c020d08040e0f060d0b0601030f0e07030b0a0b010503010605090d06020d050901200c1b06090607110319030c2003030a0909050702010207 76
    0x120b00c4000000c021000b640b4070380c020107400303200406403100201004242c903000f0502d8401c8891400107215002d842c41c420359811310850100c1d5200f025146000c1c8102d601c28030150502d1840a0310606006046856420880c0c00c55071020210034002c10421001915140800ba00801c081d81d0101d2142c006540e07150a1040080c0054101562150b800d84105c03001c0d006540c41644a1702078412183d1203080c025a428411100c98280a09242050807154811811207049031140d55480d800c06003110100816550f101d04251500c5400340003a140c9400184101c50042c800c0800014500e030603140d8100f01c061100c11901c0413220144540090300c90302103a0442c1d080d425000a0314a04d808000040e00c41c0544900d69400c06804115001040090440003140400840448100031090101ca01c2c602d10443c000a0000e401914070100040c3c0d180810070501a08001c12901c45110f640440e155400c40c0030b0750342c0050050041040108094030809800c080c852000b94a40311244c0c40e07a48050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 163334352 1250 163333102 163333109
    0x5030c01210e01050906060a42050c0c0108070e040203093310051305090106081c1704050613051f05071205010e06040903090915180209030304 63
    0x541001202044501000400c400141d200810002100156081c6000700401c0b90281e0341c2e03105500106800749002103100301142c00b541c080b44003142d20007507042e41c1504003040c0d201c885a9a90b03142e4a004072075040713266a08006076500c544070f402d110a654604414004400d040c4030904c4144024164440f007070034070072a4103840241e96911042c3c0003501e800710083c8581c03031813620301c1a030212081c1401601e0f421800c9006410b103094030392941609104aa5103e4680e0040840c0900101c1030310541025510102000000519565441d1680d0605000128001213a89002040d0101c2c0c0d8000040807011030345441038030a00e150607502c00e6a1581d025121640895000c0e0f440410010b040003020340301c6409400c141049042000190302030b11003501d081000c1220703800e148200f58142e124841c101c440a600b0100103490f60303c02d2000401c3d00c500282d0803c800c030000412000ca03a4054070880031590070301140c10030301d016607411191700d1401008040034010401112983d03400400c7c0c0c1d056 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 163335602 1250 163334352 163334357
    0x307290a14130302030c010f0b0a0f1202010305061c03020f0d030603080a08060a031b09050901020a0c240e1c090b07150939030c0b0c0102070c090b040f020405030c01 73
    0x101002420107074a107024111b417140003076003002044000400c1030303000b174501e0200940d80e1840719922811000503290042c012600300b500c3c010b41000c055031194001a4102001400e00b0119030710508880300e5031403c04a09a0150703001c510100300000080001601502d214901001030314115600c4c48010f1103002c40c220b0400011502041c41a9103141a01e0021980540313500300c0f01b0110ba0035001528124480e000c0710502d00000103400d28010700880b105120681e40341410000035640398018076000c41003124840740c01c01160309902d2028418010880c40030310041624401c4c0c0401c032003c03404c0e203140540c2000440c980404c564580300060b0f40700c940d07001c4410030040c1d1000044000030011200080c04c40d00c001e000d00300e1494142100e011808881c203484002e080134505d0082c0c5c00d14041d1100400100c0400000c02c13800c1401e0f00584804100300c80094542110b944990f00d0742c02481c2c10a0380a40c1d40c0c1c04056036603181520a00c0250000ca01e019030405140c60300080d11540441c5401c2d05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 163336852 1250 163335602 163335631
    0x409060e1501082e06080303090d0323063f160b030a05150d0f02090624090d0501021b060105090106050904050901150b131211120307290a14 62
    0x1045134443d00036001800741c0100300c9849240106d451030361600b605030b00c000880d14000003540d005030020860800c03d80c02c00e0080740540c5520041c416007030440c415003540040342c60500700780c404900003555040840a01c09007861483c142c1e05e9820000240c04002c113000b804a0301b04041c0c400c000070b07039034003a2580800148a81e01c801002c40f43c0c2c80703035001c41070340002907158010407c110f030456030420300e00980302480682da0b03050038480307072072503042c10034413000784030b031000441108a00001c081e440e4014000240c50312040e03880742c0c20380c1c106120035480d03816124006000380d01c00304242c5005207411250404036514044029005105030031601d8000c5da103410005d00858006d4110103654002a100403010b01d588400c805160781107080038208140c0410800a0303d58000701144240d035411496804001c07410720304004d5154526040003d26010a02100f0301007266850344108070303583c44072402e00560401d007586085810041009040610b08003504000111110b54039901840d405160030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 163338102 1250 163336852 163336933
    0x609070e190b030f0906090105070207120312060b21060d061109030a080a020705010311042907080d0e030a020a02060d020421020a0803030408030a0b0409060e150108 73
    0x9204000300d070030000b00840300000b03000c1c801220360029407144001806503500c0c2e403103456209082e15410707a2a8001030340010401d10800301400d40c1ca441043c030900b810261742c10002036943c1034525940c00391201c004041010848101800364114180304082314802d41ca00d881070001c0d400b9110404040c1c10a0b54a0b4610302c10f4008042c11101e103540c0007070072580401c4d00c91500c42880c2e80710030b1f00030005000311900010154080e020f80c20713450320080100c9041c181482c0610242e0340c11a150809250400c0306202000802080200b0300103001c1c02c98035550f000c2440303414003911044150b00300c41e50300030066041010b074081075210075180d040320100d40d10307070340600b010000e409a40c100c4850b80c40b02c0e140c0c120b0240b1211428400b428429954265400d58a451403900c0380422074015159000070000079611048035445407054443c002c00020301c07510a40c40d03c40845584072117004203940030320310003140100150800ca0041c00100000d10b08090310800030813542c1000b44582c40100300c80c2c482c91 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 163339352 1250 163338102 163338139
    0xf1b08190513060e01093f02070302060a03060306050f0c12090c031006030506060406060504120606031401021e04050105041e0815071101110f070c08030a03090b0609070e 75
    0x149041034200000740281c0304c028035220300070034002c00f044820144590300b908007203a0b06e079030503651440340300b400c00149201060311010f1211100f0102045003d208400300c010391f15040603000aa5072994009481803c1d0b00c0c08004944020f0400e407201c4040303a00700310b5501d16220071034205e0286580d0081c1d6588035107210900e80340300c480d50282d00d4081d00700b00c0592280382c1e6200c18100c0f80104212280340d1590b81c188800c850303040c0202400681e0800c414040000c0c00445e0140c0e85202c2c0343d00044040e0389441d5102a058546000907040e5000070320b6210b181c80c0c1840000103942c0000455181c140343c500041d246101e036109a1406006041c0b6101c9560074800342403005041d00700541d0540d20801c03050305e002a0085404001040f41d03441c800c003040070144a038681c41c1c1c0603488032501d441c840000e44141a0030260007282d4031260106d01191503442880940350444035520041000441881c1c18a1400c200814090042d51210b08124025a1018180940ba00d09560700c00001130845101e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 163340602 1250 163339352 163339381
    0x809010c0201020703020432070f0f0c02180712140a090807081602030f01020405090112060e0d03050a0c0e0a030209180304060c0b060d0c0501051b010f1b081905 71
    0x41d500504c3d00010315812440c1d26132034030f585008840400d0450f000e00408c400c02807020b650300c6000603000142c2c4030090b0300070680803844044030705006904402c50790001c2c0b00f4043c00b800400401f150b1a082c44011a08281007580c0c06070784041c203000e06d602c1000002c1d21208028269440c0c66281c4003c1418810214200c030388058010f5038141c0d4446c0b5840300300f00e091111000c100d000e480b4801e00d188105034103100340d1781030b0350b001081030010340d181c8106542c0c10740004406803461980c4040f00045c8500030042e9001d034203890b89002c07425291155550044a03101710020080c00f400d523045140c03d0f90b90f0a00781050303d50450300314200e40c41d02807604404d1401224480c81504c00080c020400541001c03504c00c40e82e20920821030117507588410f00c032010072000002002404924400e000543c0540301901c101a82e181120014420342141a42520451080000d295541340b00f5010051144030b02c03040f0411050a0450650408040d003005c18441084606e81c82ea90300c40109a0204681c0700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 163341852 1250 163340602 163340609
    0x1106041b0503120408060f09071802270108070207060504150e0d030c0204051005030a02041a0406030b010344041211040c03050114040213030f050d0306120809010c02010207 76
    0x110b4040401c1000a0002070b4005d01860300c0500c51000007411380000400040e00c00c010700005080c416141040200811054580204c0b9603038082c44082c4000b04d42194010582200303d108038007403400c110015047c00d20151402c0219007200400303100c4160040c0c101c07002c894003904c14418494001404460740c14500e02220f40c002c50303a140f1042131544c0040c044607018000c0301d0400040d1901000e00d110458503100f0240c00d90008280c440c0545041d80c010300d0040b0207880b0b220022100c040004080710382e1a00301b1100340d450303400144180048a964250f034440c0c1c00041c464820040b074001a01e65440e0824a0503200e050180e1a1011032640b0995004152503001c020007140c2d1840d2001001c0000141540240d01d4101c11843c5603210f03004150481d19011510b401c0c584001081c08007942c4583c24800d034001d2400b40020002c0c1140c0b8040b0321203809030b405400b9500541000a003a00d00d20750002202c0d02088151001242c000d5089a61b582000d0074030800c5c0c0c40381440180e090070b00950 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 163343102 1250 163341852 163341859
    0xa020918070803041401020a030c06180221120301030c0e040c0816080d020d0801050d24090201171009020705010b040e0f0c06040b07020603091207050705101106041b05 74
    0x510015640800001520984260740c030070f5170b100381040e0b00490b034a200c540000360009221254190220741294440042420001e030400300780c25103a00440d0000c6492440c0a681c80404080304c01a00f00c1400150600d9819280305403455145071203140d070410450040e44468540c070382c046001c04c006003644800510980003502d6500f0001d100801c9210300f035200360601405032400000348107101160341c0c035241d8020345a03140941d00b8401070284101494038120742003400083d510046010281c80d4104001c0e0355440400c0a0200744001400350380c000c44039843ea404808140401c04058071103c1c81581c0500100580701d64041c24a82d016201481c07807150081e191a200382c81410005c1118403411301b80c1d008852801c480e410910840e44524486c00f2400c00041c0040001498848021904141404200c959040095419443c994807802e002c4650384d0100c14104440d080503542d940035501241469030751503030314025082d2a0b82d00140002d1404003800c101410f66100b0105403c0030f4840075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 163344352 1250 163343102 163343113
    0x20f060c15090105061c0b07030e030408011e0605060315010e04022107031104050906190b0f07150e0a0303051803040e01030506060913110103020f0d021902030c0a020918 75
    0x80b8016000f0181502c00070b000b06034425070200c0e6140190382c4524007a80c402d44c03131003240c2e80b8182d00b20000e00b042204d10074075002c10040020000000d008016640c450600825000304080c6500380455070b04d6804103001d54400c0c400c1003508a203c00745403890030400e0a1850841c030072140000c0003449441d0f0400c20300341e01800d4440c04402e00880c400e225481d20707102080100944080c40d42a405684117480d801001c5400080180c20215840130030f620a04240541e03061b00c8202c041c0c11504a21248584990081103880500500c1400a0109028000d00300501807140d00010b4039608040806418541c4a5010815102480711503001c9e00d4101000d9a0311640c5421034a1962b040030300c4162514410100401c105142c646d0090340540c416071040400300b404c83c1d50320b4400300302884049044c55401c1c8401c0d003451225400505032013050000040c1e540e4620030b050001c04410007a0001154030034000a1019400080c0041300d043d0121914456581c03800440404800ea86a041c00750b0f0252 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 163345602 1250 163344352 163344361
    0x5040306020315120f0714060d06080f120412030e031006090b040e0d020307030807030b0405010b0d0515130207060e0a060213060e06120c09030a03020318010309020f060c15 76
    0x18210a1000c1c043c04413244450091009140c9603103081d036a400c0750305c680200c8800c00020740c41c113151032a203200c050015030078110000e1000d01294606d070720802d2260445010400801801c2c049440030141040e2098181401e04c1c002d03140700321824800400f07008a550b48541c0c0350707600b08031500010360521000e00865446501010203410040c80c01400345041c0100c441186001184640681805900540c10840661000c640d8040d02a0910041c540c0c2ca80c0038003801e8a45000382c6000e420010144c9903a030004640800c11a0390042404541010030303207022020380d9800070400c041d0400c0c0140541c5404040c10401d005150b120041e014a1084450345010050660007800181110102d002e02c0d5a95903103041d80c641001420082d407021007040701000c2c004a140040da0004245164070703040c4130201c000320385404010721080d005a44041640a80001e4104000c0d8203a002803034240001000c41d400b0a1403d40103040c29071080741c000c10348030019181002a60302d4509403c01e50310f101d042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 163346852 1250 163345602 163345621
    0x20f0109061d030304150c11070f060f05090d02010e0316120507082103071b0515070311090402090118031202060604140f0c13090f0b0d0c15050403060203 68
    0x84800b900d0031040c2440c0003000285008001c4d02d11864100507480d400390b44981c03c590003452600079a02c20f005e84100040e0080c1c2c0100b064801414100b400e61815034105035000e041039881d2803603a000c03c10200211142a141d080100301d40d80d40c20708003203503985d045400007418003500305280b80110dd2902d100080045c3e10b0140320360514010010342d020315848004081d100c204140e188002011000c82031180a030f501001198041854948800203091800c04c0d00112004144182ca8a0b03101c54004100032400c4041903801c09540c1c1010046500070200302e0b0800d00902411910840c0d0200b60556964040c010852004005e02480d000c50307500c038a050081c203102006084018400d03000081c2c80e81c2490b1040151980200580b0081541d86120840c101d8034000d1240c2001c400c02d019050a1408426500e0040c204000d070204150172a100e504048545200f4000d01c642c030717a11080400b0070200c03c0c100040d6000c0b442c002030340c68000c080940f0644240e42c0000c0030240300208100b8040b4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 163348102 1250 163346852 163346861
    0x150c0c120403061803020312091e0102071202010c020c04021803070b0a03060f1805060103060305060903040302040506030a080f03070903020a03060608060618071d0303180909011119020f010906 85
    0x80c8503400820070701303000d034058003c910300801000340580d00400448490140401141b0b510030036030412100d8201012000032290014074400c201269008681e180410555241014858110348020881c1240141d0029039543d01c404800780900d0340060b202c001030203010001082c03100080c0c01c80307009503955a4051100d07804040d50000080c0752500108003070140079412401c44541410500c1c4090544a403000141000342a85040c1507407210000700080c0288203461041c20f6180c0515116881c41c014801540c000500f0188079803c040780200016250000756000c2e500d0303034810507490f036a82103c00e50304983d29400196021842d0200001048220303080f00d4280c1d001c040543e040341d02e0b42e5044c04140310540f4150f4850ba05018006078100c1d11894901c9031729580150501c481208840c0482e08680c04000c03440032503a0343d501981c40c0d605045090903082841c0c24000c0114540b0a0400b075528000c2800102141d02c1e05062500e80350302c2040844c214564583c004c00c5031808a19041e0b0040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 163349352 1250 163348102 163348109
    0x9060915040503060a1404030e13060303030203150d120e011403010b25030906050c0114040605060102010c020f06011e1d18010b010801032a0f03170301050102150c0c1204 75
    0xa218160005e5401c0e00a030081c95030400e4509460103041c1c540341d4080d10542240394a041d0000016003d14103214214040d501c0251300a0710300581e2818401b01c007990202205603000d02840f41000d4110001d03c00740242c0095082518000300b03240115001211501400c1e03034180d248100100c008074018134408014001400c070284d0900c024810004060030070100c4c070340041c0203c1c8000208108050164006100c1b06440000000c0d1010328011603034850002503070161030086d0f40d00200a040d5809124500c560765150008204850700401c21a550722014001c045c1000e9020710b1a03a2031000b140f50382d9014028401061031007114100882c1e621b444100c1c0e031440c8085460303182ca00740f4003043c89076489085041e90b80700003684c295111420140d1100c0050005810b080d191896107a9032034086c071004e44220008181e0880c51402e10030715445170741440111007d001c00040103160780004500c48456954641c812095a5800d002e06080c010b02d9807a40082c000c0b1103400601c61565001007017134 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 163350602 1250 163349352 163349359
    0xc0c03030702012306061e04081911040209060706020d0617030c060f010f03030503090a0f0507031a0c030a0f0e0f0706090b0703020d0809071e06120908030c090609150405 75
    0x4d0001c0e0420746407454141c030516040710040040c0710321031800340000c2d098804403040c06450281e03200405403800c1071020703460f00d00008204020040292510214180820440b0154100012000007442034070441d1002014203500240304002c00703030260003100081120b88107680808541190942c2c80e94421034420202d070045c00b0004549204081c00b042c162401e5080b5802081d0075603505480703545c0302411480d503900c503070103861000800d900c0709180c80e20b21803c00380030040d00c3c503d418090f040705030301c40a001e826404100b24546141c00f040d82d610004ad0000420000014204000104a8501901d24a010300d680b840d8011200087e28030444840d0354170600c0381070f0b8440420700c290159650042c0160011a070450845200f0039420344c000120505079414507030b40b0116821900c0b034600313160b0060b2000070010400342e034112924145407049840d0a000c0405295140c1445210041451080090100e1205525282e890a0720643d40c3c002d4142001754188140a100c0740d0040d20400c0e20 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 163351852 1250 163350602 163350641
    0x61311090c0405100c080a110c0d0807050d080112080a03201305030f0a0609080d06060909050603010207030927020304050a02031603110907032a030b01020d080a02030c0c0303070201 80
    0x94a1140c400806a603400c006d480342807820140301181d00721410107090020b40b1030110503290903550183d12a250b58402c0104a50310701c00e6103080c5081030321066058040c0700002c0010401549042603503110385a104c404203070785070380f00502a03004040000c3c804101c03000250700307020903141a0006204401c818400314480c69604c10406590303075136800c2550300d075400c64a00c0e06e000030358580022002e240315402c05070504105e003401c1d07800c9032980e61001e00065640d540c00c0051680341d10640c0e030016829402940342401c02d4070042c140b010386100c0e914040705a1840c1c1003400b402c0c184000548001c004041d950307410142003050359804800400e9103c0d014899415002218880140013229400711492072000709a5003013091604c4020300c440f05043c2c65010380304c84d06401c02d0074611707030244000d450b41104102e410300a041711592807405043d503011071a0301d000d054028140960051300d0030809039499035601c0c5500c03c0750203a11002e400511022051040c03464044d0407040405107074410164 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 163353102 1250 163351852 163351879
    0xf03200f06090102071505040204020702100e0103180201021b12070f0806060d0209070509130c1d0105040f0b070c03020d08270f011d0306130209090c03061311090c0405 74
    0x1804c1748510b14000301000c00d010b44140394880742e5042030350f220380000d200500f8001c50383c0100700010080080303d0000340c10f1004040c0c50b07681500c038141d4500b003050010300b1181580e5001035664040300030384000c101c144003d000141d664108001d0400d0100c0810794501f1030741c030740214410703119038040c2c40c8950045d82e00003402c80c1410850610710b00d07001401403c26480d0001c080d00c465210b1442250040b01c2125002c6000e4424051410310809036a81c1000141030400d0314480140c40600c19070411404110400c803403040c104d100382c00c0d42c100340704107981e5180c20710f40780354065102c2c0c0c0002c1d00840038280b10421701084001618030a141c1da50307061158814103600107443c0484100c119402005540300c4c260a51054103841005182c1424465840c02d0f0780e00080d107024021240301c0300c1c4004066145007141042d5a0442c1c2010b0020001d0607001246000261914401000c1c0903080d0303046005101400034224411881c00d0b005800b58100341090102d4040030f50050140500600c61015500d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 163354352 1250 163353102 163353121
    0xb03030c0a110613060f0c08120f1305330c04050a080c060412021201092009090c01050306010210111b0604020a0e060a0305010f0e0f060103050a0f03200f06 69
    0x40b03440380f54012048024034180713401901c461b950030321107004200060350484005208200141030140e292250396643d49031040c0c84000000000703114081c50b285a021010004000044801d9851103543c2041c0c10480403425014218080c00ba040494090000a0007e071445180c02441a520300b41c0e850919a600c8a601c40d035100b0342d0821544d0481c100704010888606200c034022403440c402030010b10360310030101415003910310410040c5c50307504403550240c08444400e03450030580801030b034050000d4600341d01c0084e10fa4114819040c180000000015620383c801e020b848840200c8500c00c01030303010080c03240b10044e00604103d94101d0400e01001841c03010005010f0704c6141c2c0205260280760802e20050448180546103c0c0c018980000100000750207001d0740784e100d030301c102d4002203a5060390706952410508001080c01c0750041c40040c400b00e1004a00955200d4100608114482c100d2404446d07140301d21588942961141010560b610404201058000d002d5011640c0c1c41d1140302a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 163355602 1250 163354352 163354357
    0x102010e03041206020306130e1b011d040c0c0206030906041b140f03073605070c030f1e021014010602030901210c0c0c0608011a0c010b03030c0a1106 66
    0x2c1c443d400d0082241070b4002016500219404600604688940420805484103071086c0e1005681590000350041140240030130b00746403222804d09c1c1c03403880c00404a0020b10000500300c415400340d43c4683c0324a440701d006196094040d98094021680c83c03030800000360320f884041d80c04503010358858881141220302300400c44181e600d050200c486048030320082180c4000d00014043c0c1502640000181803501c510301004049000010f0008507500400e112114601c80440110781d941f401c000e2100302c1f03900c00c40f5180b507154941020541004000002c1e1240d003600301102440c184074908036400c3c580c0c04a219401a0991141408100211100080c01030b000340640e4006a205100041482d849141e030040341c0d900100141c65015000400d4805030342c0c1c0324990b031001c96601107943c401c10030b100f0440c0d4020041440c00c070340d040d41440c81c20301e0f055540445d03a000c4040003248179a2815000c1d40407802801008080320394135880700500d603450f0b61110006440c08003c64540d0010350401004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 163356852 1250 163355602 163355609
    0x613030b16091419090b01020c060a0504050d0606050a14030d1716090803030702010903020d0206040506010528230108040f0b09030d0f0f1802090f07030e0604110102010e0304 77
    0xa450110b181010802e075901c0342140f0400b03a04c54910b00d4040c1d0f405104c562610042e00280d01c0104801444200192500c0d86105603a0301a010070800b40400c968801e00756415034204075654542e80015040282c0646003641041d82e100100f010009010f60304000c40000c02c8100343c06494411101c203105031050503041101600c41a00342c4001205448018200d49411006040680030941c03a0342007503185800448451740941c0d551444041451380400950040560910080c0610310f4903030707610390701c580d010b121b180e0080c1d81c80710189031804200140d104050032038140702c8001e1a41d54003a21704054041c110a901d842c030807118a00306511070f60006206d15000400c0c4810034601360303242211035200400140f000d020500c840740e40400d082c001c0d0b43c0c18072060344002c00e0003d441d44074034040f650b028030680d80b0704545150340d1005859900d03055610000c0d170241c10000341d80300d1400380c019020910090f41340d40129002c1100b00002200c02440c014000c0c2c0c000c000b41c610884031565030b40700d40d00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 163358102 1250 163356852 163356857
    0x80d02010f0f1406040b01050c0105150a0e01180c0c0807060609060519030209060109030c0315050a0c1e05090d03030203041406070219020301140705030702060604050c09010e0a050613030b16 84
    0x100000c41174205508217180c40403042c5449441c18003825049421120240c0e1004540b85a0713241203034252034009a484003800280c01d80d500d00354501a2100291101010820030b070b6038551442103c070b0340c01101e40070301d8503400518056035051a4070700b80c030040101340078140c80c0368078104c0045558140302903095103154442c003540d0708443c00c6403704120410001e0030941002076030440400090b07030300e51090000f58468132443d9414010005241c0c26140001c212020841c9403001904c40a94000e130344007602c07114682441c1c0b1038881742a040764a4402d0802030361304060340d41080010198981d00640c495406071a00742c221b0800c0010302a102e0700d00b9241180103901000740c2d082802c0808000100c03c2d03200500000b00c1030b010144c0103069400843d000404a10f01000700148680c05100007075001c0e1040358108802d1502c0d101c41c1d6180d0003214011070400c400950141c402da160a54140d001e030000034481074079180489413044106101d400201c600d00c14203004100100e40400e04a04a0003540c3c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 163359352 1250 163358102 163358141
    0x31602100605030d0c1106040b1c0212131406150307051905060309010f090b0906060a05092a030a02041505090a030807030302120f010807060516030e010207080d02010f0f 75
    0x2d21040340ca405d801d20701a51414001e40300780360742d070b40e600b4020802440088d401d0fa0b252040f0010030001d08107100c1d00007080e1401000035804107804050002e0b84491210500018a1000e0409001d04a0750114a0b101c520809081c4039140740031401d8038417500412012207000d9070302c1743c1c144150b80030003888214810b0040a401d102c3c0c0d217003000280d07034001084000011101c01c5216460b0684200c2041660107a64510034800c05500a2100662051086e101d15821034600000f00f610048002d244251514030034a01c014149040c022001080c0c225a1000b034880c107082c050203000354000d00c01d07480c800140802c100c071107a000300d0941d14070b00d10060604d004103103180c5529665a000c1d000803420941c0c2000b440c200c041c2040b0f070707407030241011185183c040d6060090003440e04880b500118148001400b0200384502114050300802e40d2514091031400304010042c0c1c94402c080d00102402d011b0f6221181c0c0407076055000d15003d0604490a000c05586000000b049078558640c044c1c21001c030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 163360602 1250 163359352 163359373
    0x30f1516020a0507090209010e060a0e09072007081e030a0302090609040f06080c0609060702040c020109080703020d09050f010210270506010906061115040309030803160210060503 79
    0x90300d00c0d051200c900e50056540b140b4056940c18188515600003020a607404940301e5115640400700503c54002901c001d441d05d80208400f900d20f0150b151458401c021403000101c0c0c0510518400400c400321a036144c0040e44070385078a50311f81005024806e80c92103038516410828041c16260180482a403000c0d41ca400761210701200a5802049a90341104080103480d1b8a929188100200130403426000180300d0300700200c03581040404030010748150003e10080031555600d00c2201d0340c07158104d030300080f520f8210764180d014106102001e00b94030030100f6044141074000c20030340110301041d0f4800c0b0206407104100900c80e15a540210300507800300790107001c000c104d98000c030110600184007100d01c6000d140c2408a822407040125200e0304540010001107140e0b0040d0800fa050f9800d10390110351442d54a1680c41c0040058600030707113059800704050600444c04600511382080461741e0720702e00070058812192102402d0001445204818816140c640c407075001035030401005080c90024 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 163361852 1250 163360602 163360621
    0xa0c0b0915150402071205090109090b0315040204090606060c0605060306010f0312140c0a0209010801050601081906241d010504150e0d030f09170601090e16090506030f15 75
    0x400b2186034000c2d41c200012004615070340c100a0860780c142d555943e075090305000051210381d1030b07400144881d0611209500b55500428a0141c0e11600d10202c0010b81d2240009000342c100985c3c041e0402d4507180010501c10340c806e2a4101c0a80144028030007512000241560351000b44940e040381c82c00030750306100042d860708111071020240c1c90700c080940114400404141d0110443c01440c5c1d00c068404002c60070102500390052101c94020082e9180c440b0000e00072910040103419060352000c9001242c0ad26544004042d00c0f022081c904c56049160307232203007d004003250613404200400005540110b80340850307142c42c141a51007a040c50301d030092900701006d1a082c140c00b80300740b100c801280787c0c86aa4030201da1034080ea948201c2e000c0300c1400030f030880c40c064003c625915066515803a18020000e1030f641154061040001d04684401c4c016081507120700c070002040d110705e0000924904603800c21805000700b1800d850551904403001945c40804100b001e000214010000e1160300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 163363102 1250 163361852 163361881
    0xf062712030809010b09070917030c0307020f0a030501020a08180105041104050612030d020a0905090403020d050f09040905070510050c0616020c06030f07080709081b0105040b0a0c0b0915 82
    0x200418004036241d01c0a0b000030355280d200301c503120005000c08604200380980640b89e00003061140020303507e880542840c0a40380d201d0f0600103402103c014520f86203684030412650002d50708080210340b40e0030401310042a0305e4060303d40004100c0306010740344401c4410701c0780e5401707154466240c01560507a4001d0001600c00244001e41c803c2500c03c0341441e5020900c014003903213042d8038005036104103030800527040903855001a401040007a0420000a400080103040b920746810810388818100c03801000d50310404114a42003400d15001318200440010803500b61101102c0c050900d4407034800403511401400e00344001359000401245441c18140442d010704d090a1040e113404040700008164281d0043e00c80d5512425508204040680d00c070003001e4100125182c0a5803079860b00120030b580d1208020b000e01c608030400070712400e43c1e0141c000c980060030241200ca89442410501405000916a00703039440011040040d802c10300110b111020042c0c2030550b01c520b03855019001c2020f1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 163364352 1250 163363102 163363111
    0xa020f012105061201020705060405060901060509010303140d090302011a09071205060607060c050d0b09010302090c0310031203020705010605060f19020f03040f2603160503040f0627120308 83
    0x200040444d04900700c0c003800142021382c000d82c01408282000d181151504038000c0104030140d1405134103200690714031401e681100e405240140b80000414041c14072841000488907802d807800204004042d010f4100e0020b18216610782d01000c590b0106206021504480c3c107400160200b03801da103012416400a600300341c014104c142081800d903191001c948511002c03001141300891000100c0b0a580140300e82c102003030710002060b5141d54007260522402805180f140503010000461000070010392500458100036415030342039000002070020b5109040998081d402c1610200380f50510400712a250b000b0303040214a4a80300d44c2c5001c118000c280320900c11030007001c9902020810800240024000703055114000514001014114007901c240181604a000c590070311400f90100990b0145030f03440030285c102915528005003944115003241400300b0925a000c5526540090030200003000040814142a5604d45101d0607400500c1b4401101500010f00c000081c4142030a9411 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 163365602 1250 163364352 163364359
    0xb0a0605160206030a0e0609010b130902031c030204090b0d0f060b031207110f0f0d030305070c020a241806140d021b1603020f09070207080601080a020f01210506 71
    0x100340e141c1e00094584d8001c0d03030f141c00f42c01e464203811000171809001c81900042440000c00101c040c1101003400c555180c005c8902c0c00350f44600e10800d6403400d000c140c0d582c070300c5260404801000041c024009411602800705500d00d031140401d01410b048107400002c80d08040042e54903a0070790344d030b800a030082c0350b0065010b0080d081030960301d82d43c00021b0030304079100d00e4a2011a04000c0180300904040c3c1c030140b48150b44c7c040d541207046d220700031503406064041c42d010070340d41e4401806489590540303030002d4004011440000e40142c58000e4202c1c0396520f014600e903200c134070701d404403042c0c54000c00811000390031241c2044850702400e0b24401d1000c0c16058641441c607024040400c17a00850300140c1c5105190030080e01c040b43c14003544181043c00301d9100e4050f815070b00406c0c2c94181c0210002d000702202404100414000c204000003019200211401507844545c0e0a403110807006040f40151000c0c00c941c0610b40c0030391407640121195a070b10301501d101444213840a4000540b00342d41 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 163366852 1250 163365602 163365637
    0x81b010204050d030e09070305010b12090106080d020f0d020304030201020706080603010f060303020f070e1005040f09080c071410140a110d021b0607020102060402060703020c04061401080a0b0a0605 87
    0x1030946950b60984443c5010780c5903400d408059805203c100c2100412007010103107018014001c55403410203076420074142040141c5e0715034034100494014515078000da081403043d040e9403040550f0000f4585502d50500d02640c6031040c3c240c40076030b62130003240402405600440c40a11420344100e203040da00000040021650707419800f642011505190001d50058108a84010701000100b00f464010450b10312a5406898038034006005181c05000b4544030703644450040307502c507a294004030041e5801109003595041c1142080d5030ba11450710500d0845548850784111610f0007400c001e030392047d079468402420500c2c0d0140e640a42c829071020f401d000c01708081e503104c0d40d001c0141d4108244c40360000e044404082c1a0b0301d1841e411007001c144184000c0104100507680840e15580059043e6644d64445400e46016400c14110044030342e040340c6001d82c0000d0b40c005004610301101800e8031074151585502c1c1e090170659003207000440c0c1045444078104602442400100783ca600c0058201c0c6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 163368102 1250 163366852 163366859
    0x5070302151030290406061403070320012303040c0e0606030609180709020406090909080901030902120105091b011e050306030a14010203040210110a02060d0204081510080a081b010204 81
    0x7003004c0c9040d1401d6403c19900c032030a101ca001c0140b80c225101c0720407002040310a184d550f48060203065144032000c462002d440b0008164000c1000c01c00c50704400701cbd4440300c406c00d40f40901d81038204541c140c502d003101c0140000d5908941e00140d00400d0003500c424070350b940341818016407002c080d0800283c007800d600c1d408058001440000003504101c10007607036880c90041c0051206809400c21050b403460510f600f40041d11034021900c076072100303090200d44c0c1038881c0005480c9c1d49c111038a021265082208002d01c6903c04500503100c0080829551406841a0b00440c0c0f1241908110041c003010100246411405000a141e101c50001c00b00c0320003805641e23a52245900c1c0079208a020781d004418001103151007410078080902c03a20706209600054400715642c0c1c000550080c0c014140060100b072050402d404450240c07039064101c40d6002c02a41c0c03001d01c00e50080718080310003e01c0c200d020480e6040800c40c80142d07500508041d00740703d13410102400f442d0300c10100c408903650822002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 163369352 1250 163368102 163368173
    0x518060c060a090308090d050304060c030b0a0608040b011211010e060c03070c03050d180b0306010903140a170901090b0d0b030601060c06050f100605070302151030 72
    0x100d1103540c10342d1000c64803203083d1401405586010b46030010039001304c640c1c081e0881d8403805803a40550407160124881d40c80c450b098004040c4011169049015480d02040c3c0a400c06102030190b0700c51031280c1030316a0380b0308600b24000d800440041c141c852860750f08003d9841607290240d03c080003000540f0300b4400d00c50252031540448000c44004c240703a0401c00c00d200050140c090b0280881c20b0900f038070a0300100012060299005003410303901d01001094031a40709450282c007855000d0412000e50f000b20302091360b142501c610840d62800c80b0160802e005c14070109403407030041c048e10b96401d024100781d07038036050350002d8041c040a90356401321401c0b540e9003000690f000301880e0301d170f03000c007100d090801c1419190010050b1a05e685988240700031101e00d4509201112040e2600a466009500d000c90030300703000940700b540429105040c00071085032180c00038100c445400e80c01c0d440c3d840175241c5480003500c168040030b0f140c04000340d104c041100461103240d04400c500c241d00310b411540402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 163370602 1250 163369352 163369363
    0x5040b0403061e15030311121e0c0604060209031c021b01260106120c020703120c05060708220c03060506060d020a0e0f0f0307150905060403080702041104060518060c 73
    0x3d402c1c07140c44c40c41001815000400d610348040203002416801ea403480451407144140c840c100101c15601c102116030100500640da16143c40350181d03036403070410b810480082d42090314103500c02c3c054407000b80b003042e40c5250030074902c500d0790b005031203214280c111004041000148040c1841b00903c10090051300c5104011001103d0800e0a20075505186006042c040780a4800329000d180c030b070302c0e9074801d40c00040e040c044941c4003030f2030185458940c02c111080c80b0090002420f61288105000c1c007590481202441a01d098078482c1d208110420014101d202121000d05010710454040c0041003494005c00c0e807052000d0301492519444050110403039002190f11400141843c00481c05407404600040030448122821001401e078800040d1b00e842662042d810045032051501c1d0840c0e005900a20040c14001e29040d201c0c0c2c0d0b0f82c1407182c09540440c800300c0c41986003980f484010b03007900007503d0a07181560b4510342040105001010b44003003000784141d21000900c00f544c00322a04024 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 163371852 1250 163370602 163370621
    0xd020406030f060c0504140d06020f070308040b060a03150b060c070902030105040b040b13050907090c020f0106060201020c03070807050c04050a0e0d021c270608010e0705040b0403061e 81
    0x900b40d4000060704050003200d1103880755008001741000704206140b400038a044000c6070440c1c52501129440ca440340c000c0c03081d482c2422648801080c9101415000107440c0d100300c0c00340d41049569500c02d02000550042804002c201c1d49007003a02c03240404950b8010107112201607d1039280a00803004585070241650045509a80000061007141011f000300c0d88008402e07601804081c502c00005220b110399030600850041d40d803000039804600403c40840100035680c0b00f0401614005002501c80148403260b0b4025802e0601c00680c40c0e1052080700c04031680790004c1c5081c10600d0391946019880390320b0030341d0207100c0ca411400b100e944c0d6124280c0580c451900000d020410350303143c18141350001a4038415500300349046a20401700030915941020603240c1050ba941480400031011515602c00c04002c00300b03100046900b81e00004a54107840c3c1c1105846031696405908484a220350300910b0301569041c08104001620340c1c000c200c801a4014808041a9208240a045500141d07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 163373102 1250 163371852 163371863
    0x60c1b0708071511030f0a08040f170405090c09010c150609020f03151210111b03030402031501030f02011110050a021c18080f0f030a0c1e0f08060d02040603 69
    0x10000c034000d4000c0c07804e40c1402c54000145007021038082c0302402a02078840c0c20010f001500d0005401c1084a60900c00881e42c44000c48404071100d00703004186401600510380110004400315012090700020b5a6503840140e640d03d0f607150580d82c56030b40c0c141e0101c0040c00b016845d0703a00401c082c94140054a100800e10b01241e440b8548002c2c0c041007d8140300320b00e801404503e401900001c404103100d03005295a00010520707034058010a80c0c248503900502100ca2483d400d118000c0790040000c50285008070200ca84080b07004a900007840f1082c40024681d070b01c102c4070503006502a4a00c900307280900010344805000b01b800300c000383c90301229000300c59540000e04207030350302201c0e0b0340a500c00402182000003941c9403100e005424005240a0020900480c1001c0581040c004039030380d00e0b5494071016105d05195044070003601800980c1c20214590f400100c007070048481c0000e91401c410b5817404006200402c00341d4030000e01428643c0c010340d01941f4500980c8a9000300300c01140300b07a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 163374352 1250 163373102 163373129
    0xc0a030522120213151712030f0106090f06090e06010c050f060405071d06040b03010902060703050d05161b1b120b0a02030403050403080f040f03061d060c1b070807 72
    0x500c10461415036541200300c0607850f03d602d40042c855031007034505c1501c80d40310305494100c3e0107803545464040c041c1c2c0c482607003500000410844400d81034606049900395100d07a0030080e1203800c0c8400300340703c5000304000203084000070041c003c030800006802c100c0c10f042c028001040383e2503840c18290b0224450309103502c070b0801d200400200b00b00100040500c0e07401080320701c220354290031b04010060055880b544d142d041c5000c0a507403c0d4410040c0c550b0082c48a0b5880d03820b849c020b001070300005946207110349000e0010713070141168003440a0b10500b40c0e80f021a4640d0b00c00050800030f94141c1c1c15151560407540c84010b00c401c45552402801c0f00386c04400803070603d841d00300f0880100508051140b801441480f000903004019102501da0091450791590302403100c04065001f913038403010f403642003a00c000061010b41e50007002c0d45802c40410300741d4034846405240d0744035401d8641070620b00c0b04100b005074148002c84440c40f624001c100740c9040d50307a00c400e42c40c98801c182c2c002480c080c154 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 163375602 1250 163374352 163374389
    0xc03040314190f0815090a060f0f030c0f0302061c06050603070302070b01080a030806060f090301020307050c010f0b0604050f0102030403050312071b0b01032d06050a0b060c0a030522 80
    0xb01e0303c9038a500155142400c207624100c0302c10502e141d841100b40d03004008104c00700e0802001c80d000b4002410892000105490791070346c0100d10126148404d07100d2080000c80410310103064201c00b0306482e00607101e45d14245440051045005910b540c031204159281808241584c40500550190074a65409030700c0d1100c2d0b040410384120180c1c01418103a000c0382c1c06100180c0c006920341c1c0d01650481b00e10340ca5003015045510a4072a100e180360b85540f0002c2001801a04100500445520705c00200841d44030b0f483e405046a1b01d52030220b5010809000030009442c01a0b41c0000b0300b08184162030030300da034031b079101807950f0011864183c540038800c0401c00103031341c02500c1075010302010075440340c2c1e0215529201d00006060101900142c040115403004007019042100d0860300303072800000c3d050141c00e2540007440c041e1140303580b180c1841c02c002c0b440c1c907010b01a20b0b40540d640000d00a03000e403070f65040d912135000100300c509049010b00b8100402113448999401402c1141d0404200c010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 163376852 1250 163375602 163375607
    0x1050d08070605040c1a0c251d010303090b0913020c010b041a19120807020d02090a06140303090102030909060312070c0e060402032203140703030609060801060e0c0304031419 77
    0x480001e0f00c058109005084031f0b902d0000c2c0c500c0c41c00c1c3d1125901681a4000a40b00b00c000c1010380000050710340d120441142882101030f81d5048901a5880103701615402207047d00d11132505940c1d8419215401b030054a81164028404210361400010394070741a02c000c60182d504d403040403072a0316110507920702207050001110140c900b40400b0300140342e00700071402800040d00c040192044a01045c8802151079042a640c8440d400601e450070514040366442c0284c2964082d103065082080680c04041c00c0000599018100507000f0f0b40c02c0c00007543c1800f8416400822056041c4a5100030f0101c0f0540f000c0100721550095004140072070038000081505c900142021307018034410020009000d6062140d1041c1c003225001489411140f0305040750405060280c0090411001451404241e015402075088800e4160f040c0a02540ca15201e400c8420520070300404041010005030f5645400005560041c464108855000481c0300d000710b0b81d8000016400c07400089201c035415058 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 163378102 1250 163376852 163376879
    0xb2d220b030111030705161505041101030e0d090306020f0d06080d091e090507020a05060a0f0501120302030a05131d07170103110d140307030c020907080f01050d08070605040c 77
    0x1103120b000c40307145040045c8018180d10503044000b103090700b580010000c0041c0d2504110244403007050901290a2504000300340301d491008550211340780001e001100380c004130321900c0d480015101c201c2030525544440c00070f5400b8071004400544100401102c02e441d40c4142800b501c0d82d500284100001d140c4003038056141a0050f00102d107088026250700904020101c017a500f0a41c804900340c3c403100742c141d01d0b00c40c150030001e18a018880400c03800c0c00301a80146014401d104052105980c3c4940e2914106040c10010300103800400800c141d4034015401007a81084841101920682d2452401c540d160f140300300720f5603148480f0034002895400071164030251300c0b020040016500d942d41d0b0448400d41d0522041c0a42c0d0b0b0103004070305001509071440400c41400b415170360350b517003e8a0028810440808200c1c401c01242c00400c002602c1440914452030340604a400300340d09101c00c0000340c11460004907900001040041c00003500ba01a03a8003851040409040300c9042011920214 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 163379352 1250 163378102 163378121
    0xb011d01060201060e0a1a0918070501030e060c070302070f06090f08010c09051e0406090f05090f0a02010e0d021002060109050105030d080112020a081903030b2d220b0301 75
    0x6a061a074180201c603151a160394005a949500103180c11a810610000440f421030b2143d024028500300010034101c82740310320694a18070140c4a071143c40301e0040d8100e0f42c18400100b42c580c0210000741150a080000740400c600900440e540c1c0d90360340c0200b8009214036004600000c001103400c000244150408401420000c1b0083c081c524031a81c0007004030340c80e8030035035103d80b40380d00100b2400010060809403130b10707001d4410b0200c251551302c0c02010f46880301d85400314074030b45800110a4080030400080e070f00181009001038041e650011140c110034449140e42c032094251a00005948a0301c0111140d0303822340180006600d089000012110b050b80200c0c000d400c045a00c01000d030744481001d0645544242000042c8620f00200d102c01da020303084100d5601c0350f003041006840c2c0c0b00c0195255280f01f5038040c4024105081400780d00c000180104100c41820740380c2308284000315428480441015084002c006400440044883d0458003e60f4015645038403c11b0700c0c2c1028010324090 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 163380602 1250 163379352 163379357
    0x207020f0a05010e0409080d1d150402090f07030b060a02060702061008250305031c050112150e010f020a090f051503070f051e04050f0301140601120204030b011d0106 73
    0x7480d203048000780c0b10f03620707a107006442650b4030f80010080203800c0040c0e5480c11140310042100300c16080304880301400c1844403600c00d00c2a200000034442c804d00170548110390141c0f004050b03849080d8240c83c604e0000e80024141b42e240c0c140c2141540381d00c4040d12074007845900030f1495060106019040c00005011060890449030040c8050400010348150a0700007000d00c1c10b001d088031411211804d81504010030901001641d2445440713036510915a142c41c8030f004000c1039907101c81c941000189020700a01c98900342000600e1400c05901c501d000007820800800c5103820a109101260f0000300c0e443c1c08103500341018410000300040800190009542210680c00004040c10060000420300310411038600d4044032428414800d4491160560741c201c40c20041c50048804107802c9800361071301600c0e91440c90201c5142c14040c68000b8010030495801e192603035030045689460310a031040502c2d40130840000003c2c0550900e40c000c01100981c0014400e0030141d2107078090040c1e1000c0c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 163381852 1250 163380602 163380619
    0xf0703060605091207030f0309080607050703020c2b080a09090b0303032a040801020322020904080f12010f031a0403080f070c05060f0a06080a050316050f03030a0207020f 75
    0x315580000072a105880300b1121503021113006000d0628100181d00020f000c030296040c29000c264100c10700405450340142a209180d59a8500712440c0c020100003a00580c820300e8018a18185000402e22045280405079445020102503040c03c100c0c140003168900000604000d00315444a581409050312002c28800701280c42c0001e69a40400341c4a590500f019480c65000722070507407602211010000106030310b4030f95a84a040c000d406c1203c00f0030703504400ca03103c0750340c072400c400c10740604690052a04103181c0b12912201b0054000c0c10081c4c0b0702c0b20b003c10558616103030000b046402000c0c074085111b40300c0e040d80b4104500c40d040d29107902508001105000009170440b00c0f10394002e448407945d19190399500401c40d460041d9050207003c0e80584024450301d44090380c2003601c5510300c48030078083e80da80c92840380cbd50ba040c840d1b0043c080360424400c1000c0a8541d0010004241c0954211040c100c495214581180c0c810b641c9007406540c005148400c50030700c038460013003100c1c0c120b442c043e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 163383102 1250 163381852 163381859
    0x30507020111030c030a0b090405071d06031c090506040f050f010c02030d03020a0e0619110d09050105070218070c0c0506120402040b030f1b150a0e120f0d080f070306 73
    0x10344a0001134000b14240c00080005446010150b000d40610000141900c20030706150400c25115481d0307000341d8032264820600051a940070340b984038002d1402600400d141c510030801000c1e2140c1811a920822480403800240740d5076403c09000607150511800c1722180c504400c02c1400240613030f8441c14400300c0442040541d60204001100050500b0301503620032007403070102d81e03114440c01602e6003ea0046000d0301440415031443d440b028040e261001044d0241780050b0791500d03007a00ba0000109100e10500c01075200d02c0141104a101030005088a000c1240e003110f4000300302c031503c0001f00160001c4040c80207000c400d0004010a071440ca1801c0c20250100305d10450040c03010740207030f0f1911043e4910762406c0000b21002040e010940314091a13452007104c0231642240072622030340e040c0c6130305843c41000400b2107001c040c180d142d034201e421061040c4007558036407449140d410b0044c640c016030405420300410200390456903445607c2e140c10480380c0c12501d009030640e01010f140181c2030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 163384352 1250 163383102 163383131
    0x8030a0215150907031e020a0806011d040b0d020307090b01180b120705090d081b0c0d030f0203040b0d02090a06020a05060106051b150403030b01020d050307140d02190305070201 78
    0x82560b031605480f83c0c0081c0c1d4481c002503000c0c0a02c8041115100c80e0f03c0050801c10750a58080e20044a20365502000c94031448011030742118441026140c20040e40110303003840c0780c0b1360b0225140c0c4a010f000c800c0480100d40020b41028200c1d4030120680e074a59044004e25031b44000340c0740a100708007a03c1c07528142032071061203050148a5440c00701000c00c0700842c00007070188040d0303039202c0380c020300c0c00950000500c2c0c80e0002e0b402c01054490b8080c2215034058980f4400300d007804902e4030242010040100944080320030f55001700200301940002c000100340482e44600401500108450150b504d904140070f00c115080154403050864000c0395440d0001040854614111a441e10340291500f038042281941c022315140720a560344150b548880050070b0840329144503034026141041000070010059840725402c01348940014020000031711000e0003400e40c1814248130081c007500b0050301c8450481268480c1d01d516604000010280c4034041e4140205940706469200a0012002401c1103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 163385602 1250 163384352 163384381
    0xe0903030f0c090409210306060912060902011701092c06070c0501021b0a0c09020a0816031d0303041407050a0603090501020d0617060106050403120309020a080708030a0215 76
    0x6000203031070000c2e100790b150b5516003250081d1608401e00c846c0f6195040605414403082c120864080703400c1820004203140210518022900055107864103090280d40d804018126603a00328144441000d01c070000403802c0080c1401782c03101803400118021000c12810810400b00c14207846080307180701c040030760400403550715000586801c000300e040400e850030a02a006615048100014103000c0c1103030104000f84104003140602540c150080e00d90704a40240e128141c00790020a0709140440d00c0740d420030f0340380f008043ca9444c000030002e06000040340c0d0029032040502c030b282d0021040c0300a01602d40c0c0340301d10400060005040451a10b00418110740c11441424285a40c0c4c1d6045014401e0030740483d1911159004c04100554a41c5880c0a41d80380c0900341079001d21443c00080b44803402a411030781602c0c3c2040d10400c4030004030800310007815035070100b280c000d542030744e000610142c20810780f0301418280000c1c645607081044002e2800c210140cac440d002071808001e201480d6410541d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 163386852 1250 163385602 163385611
    0x201050904200a0e090c07020d08030414060112111206070509190801050403140a09090b0d0213020d0f050606070204020703142a060403090e0910020c0105010e0903030f 74
    0x50100d840d10b5080d210741c0300d2051503041d00410600c00100620f0450788203103010034405049072420f10303d80312940145140d0082c100c0094021140302c50900108940c200036540c80303403052030b0552203400e964801c01e0800100303078400e8002803800070000c0c007007244524054180c01c105a80c4140c51181e000c590341d54404026142d0414814009130303010498960349076600607880900d00c411a0103548441460080c40308403000d4001030b42143c0e0303454004201e0b904075000c02d81c036035071400007070b5051401d403000410703400328039a80c86020361100c88016250200700d43d141c80040c0c1c0d0010b89913210a480002035030782030000111000d00d80420490b117035991106541700c81d40c0503035005803528003030328003959101904503100d0003045000c10140450308183c9041d0700d203000070a00150402003000003803540c51400b81e42c000d01003920070109024079060000d2465104800e0f400315108203400340e107642e0480e800108a21081c1e51102c2c0144003001d12828071a0700810b884004501e54540302d581c49040c0c00c805403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 163388102 1250 163386852 163386859
    0x90b100c02090c030903070507080c011e050301272306030708070902030a0204080a05060a060905060609040c0927060f0302010203070f0204090803010b0a08010509270102120906010f05030a02010509 87
    0x201140c1045c0f02041501d40295002e800c441d445070f141e50034a0ba44800306510140021680150444c96840c402584642c241250300c0d801e045d40d003800148044482c0c0f8501041c0b118440c1100d006c0c540402d03000d01c0d0014004201c08104401001039100003210004010324000e500422003003040450001d170f03410403207052100c010f8498032008031f4000030340324a62281030544039480c140024072402150341405011401c004000155403480d00900350b440454610354040d9050040032010300313158010541d0040207142c003022081c0c807203c5108000043d50444241c0580440008400050030304ca9070016000c2090404989851903000039968072850f01c2c000c00c160f15907481da600319226908a1918507511020087e180e40c2c6402c80003031150840000000090002c0000250a0030a050918020701114014640c2c10035480060b010081114440320707050342d42045910301c00300300111403078040c101071000342c140b030351500c603040700c104404d40c209520a80104100310010303a00801196040c0b0342c01d8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 163389352 1250 163388102 163388107
    0x90f03091318020402120f06040c0903020f03100f0c0207050402030f01120c05100c02100801031203090c050402030406020a02060907140f03010e0d02010b011d100e1504090b100c02090c 81
    0x3610301584900b15214000e410600100741042c140c941010041c0c0305842d17000d401d040983d00d6600300310684450b1001e08010074440d00040c00942801a04009000c00c007900312007401011050840403210f4850b01c80b821903983d1402807083c03542c1802010010001100c0c20741c1141403021828840342018420b6103088404030300040c04104100d000d030340003420b000b8500d14040e054200050814065100300300d10910486889040c000d0091100c0d9068036000700060480350f1029105500506505409803641d0151038000141c55951340021445148541400768030744c030340e407a03001c0e00c0d05002812614182e00f18039400d10006000a050ba22501400c86001c0707803070501c40e00428018101803508101a00802800c80d4000313805410136034500800b030340c83d942400715250140d0715100800081c3c960141180302c901c042c3c1c602c5800c8a1443e804000d045198203032120ba0b20140c25030080d03007c860840d03215980c030812460515101c249070215420b05a0a1035501c2d400034002d900c00601c40b09005102 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 163390602 1250 163389352 163389371
    0x1b0203031b070c0b040602060f060d030818030705160305010c02190f1515030b0a0c0c080304060e0604030c0c05220e10020f1c1803030506011b0803090f030913 70
    0x140a0f000030400c0c8507a056865807101c60080d129801150720600d002001000320320315007015589180c0486d010790b2441d040c2d841d00b01a4200f000350303011020ba0688401e009900201340240701201d4130100d039a028030317503151541c40d109003544c5410401c0c00554212106004060708a400307058030495000b68800702031403082c0b524406002503500b0b1680e0140c50040841e0071044001c16100507240140241d041954410240c0015a00d5022000380004d5444107030300000b40e100805550050310032035001c641e041480e0030312032404008984c264009003c14880c1818449104071200c00b070502581c840213104129010040010b5021104d0703007105940d401003c0510800780141008440e091200755034a030b15103901c0349407d0704201104082807015061340c0040c02120322842c054403c060000d101e002060f80c50942c000c020041005041c444d0341a40f41c2c102130101c10b101102030340302c0c2488507140e05061560510300307042900d081c00c413544100400400c558a65030750070b00c05440f81d000410711000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 163391852 1250 163390602 163390613
    0x7080604030e0d06050c0304020f0f010906201c0305090606090c0d0605090106110708071a13091107031106070203030c0c1006060905030607091a0d0b030a061b0203031b07 75
    0x41c0320501625485c68030080c0100070010200950180b4021900e51701000340c0c80341081342c80600c54803818082a244030042000034054010640382e0400c40c0c0c0405100c00e4800820790902c0340d8035100c1d01044005030780c1008500d40600c40c05800c030400f00000e01c01407604c013010454003000907004102d86000031440440907211342e0020005410040c0984405503501c44001e030042c984045140464040c1040c00b00b2481c0c0e000941e007044803140d9061507100c0c05c04842c50440d0f035000d0428500c0a00381240c02244109403030051060708003681c0300f100d170744032f9160170000d0800c041000303810440c3d00080c050010341035001054927080050f191f4620340c3d49407001d00309480c15502d90214111107082c2540054100d4104115000702c60040d41a60f0131940c13546c1d01100d07428041d0140c0c00c40005010f04011185080c107010f0060030640e01c0e40064001900800039241980f0007004444107601d8040300c0d04e105602d446000c0501600d40011421800c2240c1941c15a81c0d404d01212052803010698000b03004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 163393102 1250 163391852 163391869
    0x30316060b0a08030901031d060604020702150a0801050a0b030403080412030b031c02061b0a050a05040e18010b060703080a0e15040b07140f030402010e0420070209070207080604030e 80
    0x141c000780b10242065903182625103c0e0400e51070315011034604069100c10088c0d40c02603502400c04000a80440c2d50340200b004001e40098000766004044184040c0c04c10f40e1050040c482c001c465201d5040540c9400100007100c541c43d0401c11180c00c0074030901c40080e40002c41c0e40e801550042a04c440e400711800c0c100c1c000c1281c0480c0c15030600c00d0310020080c80e1511030000c18030065540c00d47d2815505c068015180d401d01010101100d0010025400310038031603009000a000075160152405a444c0580d502daa401910f0203460054825507440c1c0c0e00700240325240044d0402d8650506102c03c64034050801d2200401096080341c4900d50070300040c00511018891520368003003000704d402d250520f100040c4044400b0b002060480320f20004000c124815100d4111050022515684e034640c01100d9669a024030316801035111050000d56002e0000301c0101c101c0321605241d01c03821280100081c0385030183c846030039034201c0c0c03205005980010603125403043d01802c18803403c003c43d2000c01d2102 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 163394352 1250 163393102 163393121
    0x90f010207080d0f0501080703061509291c020409080d020a12110310090c181419050307060c0807020a090b18070801140303070213020301030c0e040203031606 70
    0x1540300080100400075260083e1402c00102035040007002a0070a440088400a0150706d80c56800b01808000003120b54104007143c2603c0c200141c80b503599001982c0a80d040044440041501b41910114114801c254107a03207070811100c424072107400c40c290700194282c0d08806406183c0300c1c0c3c8104240200708044130b001c00d109003400c42d5108008580102035000c07025031100028242102200000280021b0b40c3c010000c0b40c401504a6141c480704900500d13601032100f01b801898030345030f0007040802410a0080c07504144042e42007a0100c104200c201900d408121006440002808a03480c00101a026618642000c010311080360400100c04c4c003030584020360240118002007003284d15504400303a81401a940440201580314102d4140d8508968001c00928450010410700000c1c0c1d200514482c000f03070549141c803009401054001d01d9240000f11901c0d0004010410851030a403084010010070103006041c4c280395000a46070310900200d5458895420100000e12503994041d4002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 163395602 1250 163394352 163394383
    0x20c0703050307030918060806071d032a0406080a03080910051510020109111c060e03030f0105060c1c0306121112030c060606030c0c070b0c1b01080f09 67
    0x303509144c60010442031031401360043d6102c01039648010780c0b5881c020709040c3c030074041c080c0515940719441141e501c001c0480000d90300f044100441001e840a00c025280c00d941c0f01943c4841038280c40c1152144a01031240c240142d10b80407040000d98000304000302c41d10350502d000c01190300d8502400e85018075039a007000d8918a80310920860410400e61845d081314291410f10310144400d500b03071308031000054003808801d60b03501400094a020464180350718010180f80800304419150700c0d0403507811041041141e403001060080c50142031100500501c81103030350702e1400134072000e21a10351f0352400c4031094032020018800d10541c0280c00c0403001d00315500741040c1c0b0200038205240c02c1d030401e20303c00b40100d41841140300c0325000401128840300b9102d0040141d034a6442c11310480768401481105159001d000d4001c84000920030480286400704025441d440d004003014240f00c090100054084c803c14031680070369812240f401d40c00890407100314030541c3c0340c000301801e14000300010b0304e5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 163396852 1250 163395602 163395607
    0x5061303051e04030506010e0c2209020c0303010f080a05100f1d030901181d040816120e100906031e060b040303110c0307030f081303111201060b030109020c07030503 73
    0xb9456420058404c0340c3c024400c0301c40343e0341d03201210351944905030748a00c429002001313018001c50940740a1800b0098801445003020f50314003059049800040d041d03820b41d000000100103401072030001c40050f2001c076026040301d49040e500c00b44d88030440101c81d008291142c900c3c4440c404154000b220981ea0000511115801ca03030595490346e0080884901061440e00d42d1410f80700c10040000664040d0811000790035071035100813143c80c03001401110b80100800050308002410401c0a0700d5030b00c140000c0030406503000d4003612041405520701d0107020700909440203940d200c561172044070304a041c001400050810990b811020918540c1c50f4103041100000c0c8190b900d000920480c1c3c0240d8444000c1d0304131805803a16040c00c0e00785194164450380c0e0900100d401e03448220042d510030b141c19803802414200c0120354243c1c0d031b0b2050341d88044440890183c0d0401d9442d2007804940d01000700051350800e070000c201808107018049003954003054121102c9400c004d4040695004000c0303a8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 163398102 1250 163396852 163396897
    0x130f05030a0504030b07110c0f0d06090c030b071409040b0102210310060e0d060b010504090f05010611010203040f11010c05100c021204080601030f0c050612070306120506130305 78
    0x5100b43e116100490302c62043c000010840c61050b480da40e09448090080c0ca01d00403810108800c4c1441102d00179031002e0f8840480c800142584200c809a921410260b4406803460400c80c81240005191400380001040c19032406003034030084500c00c4804580016483c12003000403440c05110b2030a034411445411010280c0540980103188504510740e82c0460300c585075101101d000907941000ea8000f1050344480002500980044000781c03410724000381065a11410b11059614400729895215580c40042c840c0e0b6074001d48a040064910380207600d581025603601c0c0c3d4070364450002800c08a01c112140620381e100c0c0145a0580303801004a80d071006030300b071890008118a10301c690143c42440c3d02c0604203401c2c1402e5030101e1300e80001504d40e60786540ca401608a1102c1021980c0842102001c21283e540e40c0103005062182c00140c501413521820140481c0e006030403c02c1038682070040c101c0040c1001071890762103201c81205030042a4203242c10b5440c0c0c003504200d40d45000100c02c648 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 163399352 1250 163398102 163398107
    0xf040308030f010503071502031206010c170403020102102915070c0e07030606020d0807020703021807080f090d0507050a0b041416050a0b090109030602040f0f140108130f05030a 78
    0x78144d61048050301e0009540740308100460b860101901c0158000b8051084101610039200ea030104041c14070310038414059540310300c051888191148031000c0403c044c015542e04002c0c00040740c1000d041041240c010058448620740780d8621124009000c802412540e1940120559010714803841640c03138440c070b803802c00201021805003841202c40340b00000c1980d0b00c20302034041283c00070b80142000380b0301d4500031603203180700404101c1035114003100000180c840715031004d50200c1031101c3c40b180d42084100100340405c080c02c403141a003080d80c28040c2441010980b03444034141810319036554200ea28000d4203014134a13401074841101101007106001a5554490b0803c0080069562049443c40e41200b1805d1501900f5040f808500062010843d15401450a45414180b40350341507904d81e980426a80142c1000840c002c981008116014440d8601d001900000180079211042100000e20903c001080c4851000000301d074074080c00901d4a148103e00c0d00710302525900d00520202 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 163400602 1250 163399352 163399381
    0xf0c1e0305010b030a110118030f03050c06100b18040e0102070807171e030a140703020406030f0603022b0501060603050709080a0b01170f0f0703020108060913080f04030803 76
    0xc0d281d550800080000344c3c82c01040000f81c050307010400414000c075410046030340c1781600385480804c00c80c4540100c08a210700901c041c4c3c0c24829a502c564a00785c401c58142031820150203031086208040051003241440c0050315401d641c0ba14100711a600c0d40c0000501a0041c0707a40b220040d440020032205010100004107181c80c09550700c10905c81190201e1503003480342c5000400604c10a0300d2600d522000c0310021a003086146001041e40180d0707100c20745501109135000720219900080401142c1d81502900c1c2c95442c4029042000744e242d500415003014104030300040311403081c4001c11034030071030f00134414120380c0040c000c020280d101d600250007803405030303500c40203d8a40000010200b10005240c1c20040d03110072001c08a03442e021200c40f1030051502c50224500550103400c0c1880d00c2089000c50003000c41d0011b1641c0d900d140005800008007406c2c5a000740d49203420072040c2d128228901300203d40c44078132240c3d074000d4581102c0a0740183d0300003d201d154004107204100e009204ca = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 163401852 1250 163400602 163400609
    0x13030812012105071a0d0e0601060f0207060806060306360a0b031902060922060e091c0e04050406090203100203090a02010315050a06120608030f070f0c1e 68
    0x40d0700803440e44000812025070b828a802009580041000e002c0000c50460460f11251102c007980d00704001110340394159407240e819454690700000040048660151150138031000500151540380e00744100144ad80c08018030715801260700202158190325001840c0c0501519000c41e8040d450502d8010500000000b00240c84a106e003804103204075414401c4d1258208020003e01080d6003662107406910504d00041c3c0e4400c0d828455284291a040103e01e43c1001c00324031880400034003114041154103980018850002d03841c108145420000303050003c18204111010030004e0320201160700c10404c001c0c00e80c009040105000030071002e50440b0780c030b4174403c8040d1144020401e440c0c1040740421117881815070300091051015500039400209810205000280030a480d0030210b149041c1c1a80800d0004c2c000d03d200c1e00b18038501d8810768002c1c1c85e01a01075403a00064100c01c1000e03000b080009410b564841d4000020400111124130050514030041d0180800c001d0025280c54603c0c070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 163403102 1250 163401852 163401869
    0x80d020105100608040f060f0c020c1203070f0201050c01110a080402010e0405060f010c0807020405010303022406010804080a02100c03020a0f26101a07020109170604081303081201 79
    0x4081007101030540216003c3d0f910390380d2407100941e80c98440d17800d05d0f0039110080d6041580c5119461202c00c072405010300880868008260709011a800c2c400b03030141c141000e50154205000d0440010341d104e040d41c6034903409103041c9840341a5400c00500400b4000044040d061002555600380741c1c1148541b40b14500076201c000d4007400c0300c82130001b40c46003202c10307a82c810ba0080c420002c030360003020904000c80c080d000260030501d45a011404641c070070307042600540d01501400c00704c00e10708000720180130b40c1303060310b0241406c040b0000307000136030060700c02001c450340443c681c51128420040101440c0c00808280009801d441c4080d009501550b10000000ca5081c0d07914003245c0500b00040030311915440d0f0813110050034103040900c0c0006082e0034040e106500c0002131072884d070001c1851803607138614030319900e0f40c1510014001c0c007086d13030050322a01291000317001240c5000c9041b030381c0907820601d42d030768410220094040e004800c2d00002c0507100c02140c1c140303c20781c042c00458181d40808 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 163404352 1250 163403102 163403111
    0x19061509060519030509010915061410020a02041a0301051303021b0a05040b0411030a230405061306110d0e01060b1309020a03090c080c1f2007030c080d0201 69
    0x114000c81d842c0c42803642c405000c4150b4500f07000c42e11310942c4280d40c80071800b0000503e86105954441060f0090041f642169442d1101031110890408010740c011380704455030240107010038000b9403221900a000f070b2269680e4032005075404924000240c190f68020000c10151800035003d90300c010004006a005204446030900d0101c0300d40704c02c0d00d03040320003000003c00070720740b0007084041d004003d0026041912038010030704c841a0741c03000c0d50044032054008120b00c143d0b202121034a40c0c0d000c44980401b445c130801d10011510100d0100d4102c2918015440791002030300f060b0018000300d842e90806510009a54003000c2ea031907204004602c4a14000e119255652403040405d000300106022032102c180020028100c0d16402412840641d05000c80c91a1003a100c0240b4034803a40d0011000d80c01c150401c010f00c0c505440e88a00b0040d124a04001400805100510f00f0702c0380350034466a8101c00110501844003000700f44015540301c10b5076080123444040090f02c4071000c4850381c0140d801c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 163405602 1250 163404352 163404359
    0x4060807030e071406030408041a18060a08011205151302010e030a210306081f1410090b010309080c030a080709030201050a0e0d02040e1b0609060406050319061509 72
    0x101c2c803102210f0a68102812100c0260108aa01da201402c11288c80d401004001052298003400c2d074199404982550b488003200001180d804030120205d0380b1503a07040105405040e0003518460540310100320030000c0070501c0c0381c000c2ca001d0480700b80c621014181803c11400d86000ea040850241c0300380c6e19800c4410401040c581d5612800d5002003040e095201e94044164400a01c1040180c4d18a008101c0c2035a40c100c0505154210b0300d400d50981082c48818003d000d00d0260290003010041c1c2c5400500d0146c41d0900401070341c0c040d100c00e50b510b40095a10580c483d810a40c1d9950f080621940e481c150000c141d50703203a03c110501d0002c12084d20004450314003c403042801c4a4040e10780d1071600c4280d180480d0a0761000d890301744e01c0b400e04050003016032100e00c1142e9500000e02e0040c02160164808043d40101800240b84145070411000d4003588176030341602c044031100d0801d15102e480e8404c840d010244070110440300710b480c001c40090200d809000c80c8904200c580ca810130010744 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 163406852 1250 163405602 163405631
    0x905100e041b03150e03040f061b0609120807020d020c040e031e071101050a02060a021e0c0607120608070e0403020a080d0204090506040506300f0708010c02010b03060c030604060b0406080703 84
    0x2480c808c6080b0216044030802c000e03801060f00940442030005001c107100103a655003000c86009880c15929415400308a2440b542c002d44d2031078012a55000808120801800081d901c060000c550f41c0a0781c1c0712404810560f00070001d9800c000c0030340311018039a0103840c0101c502504940400d940c3c00142c9070715205036502680c11182d4050035540602000d0380c440e03407904007960101080c2e18811040c04c4022590743c07010f102409854041a001e40101c0c20681801000b41c002d08407034081e0710345403200412040390001019821107204c103024000c240d4880c03c060f0b0031f11410750720107001c1420010f82c0c503480c52096030091059401d840010419501c8440a010884508641c542d411000e083d6820b16002c205514102d0a5a6100d90000300000d5000410b4203004218002c100b140c1d0011000303005095083c0551400c040e03152008208107800000002d541e070742d025010f65800e0318000045203141c0c40d1904200050090b10200d66510340d50750390300410035841202d80400091509000241c1c0c05c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 163408102 1250 163406852 163406857
    0x115210f0515120304090b030307170d050109060602030a141213030306120206040b030907151115060a0e10090c0807030c08010503100f0212040b010305070905100e041b03150e03 78
    0x8583d0000f18101800d1480d158010007a5051083e403512086c01a00f002468629811814003800880903899090b855840740a40340180c100e03001d090304000c5c06001c0c0f55400020b44031034407034a242070f0012288440e0414258455002d054813112001c1e03041040f41054201811000b0781f10b554208440ca569580e01541e051000e00300940c0050100010089802c014024507000021442a0b940d140d590b540c0014540300003002d90804100c034020b5881608805002400c8140c1c060f114000840c94684000b4006014600540c070310180c0140204900c425800702301809448140c400300030a903035080000c5d00036041240e001e0002400c000c00316444900c20f0110764100c40380070340248031500e606494040580400030040128a50a0208108281142c40141d000328041e0706050b6282d41103042403400c12484d0741000001030305142c2440030b0f005145081c1030440e14800c90482039a103442c5403404042c0712034005070701821065823021080c040d240c085080440320394036040100c0c1d07402418940e00ea0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 163409352 1250 163408102 163408129
    0x4141801060501141b251703390a06060506070c06080a1103010f03030f1707080402010e03100605090a0e030306060703091a0711090115210f0515 64
    0xa07594107486040b114414083c00c000c1180c1c450400454802c40c0c4074514040c03440e5842004800301c03401d20b0f11b540c81e410000502411450039040802140b08903203594070711540f00180d20b43e4004102040700313410304020351412a0030035696070f003541c0740c0a1780742da0759541e04075001e50f81e4074548800000c85141c00b40c101c681d0650300c0307140f1510291801c0801c1d170300f0384002003013001d4032515071000201a103139180041d8042e040110311a41414150b003002001e003100312142109024241440950061070304940301d601c82c2440c60324804a503a144012150ba01100e030000e80c03d8810b046180c01f500c0110f400450507684195120f948a44c0c80d00341ca0390544803046101d2141c0d4000b0008070f80d950500c0402400c42a0003401d1a20702c5554624900c1101c1e41d0f25100d1107107142e03010840c0c004104070380c41c0d180101c03042200c0358800f950511a107407403842a260420b000b4012941c2440e40e00c044100c0c4402c44913000350904026011840d071080000e41012600c010120400010300c01f00d610f41a02e515070407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 163410602 1250 163409352 163409357
    0xb15010c0b0a0b0a0306060e0906040f08090604030605090d0e011b152406081b19020109050106260d050f0c0c04021c1514100e04141801060501 63
    0x40400e26201e5156100c0040c2500c04400d4640c2d44031207144d01c0302c0300908000c510540c0006883d9140100d02d481e008405401900b8940005e8144804a44900c0d0080800e64114a80079507801d5540000340ca50700c22984002d100c103003000204487c8950110f104c1c2088402a01d5101458040307800444280401f2005401c400e581501417401081079a08020300c1c01d0707185200002c2c3e1010081d100829680c0b41407014540c221040c00034454550700000e83d40c4c00800c200c446004900e9408101036050180b10b440d00104501c49152a445910035040940c0c140e8004008001442c2c0f00c8100400400f11448160700d0b005036500d030a111f0500004041d40c4003686a6101414100710040461541d4050aa200001d22403140090819030710b41c4002c08454108203541e030300d404c071045295010b40e0350020140154080c020000c2044500d41030791020404401c03122510107000c204801c0d1524030281500507000b03840d00095202c14008a1841d0380110310310044c100d084502e00c2640b17030a891036801800d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 163411852 1250 163410602 163410617
    0xc0c0d030f0c03110303040501091a0c1b0a0f05030a0201110310150c080c010507110d0e060f1303060e010e07080d08060a090c02060114010513051c0515040b1501 71
    0x88642c803480d40e008181e0300c0391030049000400240d040e440d540059405440903559030115030200005098111405a03441951884510300300280c0c411b00c1c05103100ca03544556540140e405154818021407001c1a80400d00c0e04c2c580200b814500e1362030b0003e09051026603e0b10000e040d01c1e02c005030940c0e1085094103003034000c0606000400d0403440760401140203011100c02454001034860b0098403c82c80368200000e590310380b83c04000c00c446101b480c2c44c0f0854000b1180080555488280c042139074000750380007942d4842803908a0030360320070025144125064407801200300310881c0c00403501a6841b6001f030140b44c986502254075456a0702c03803c180ea900c100070061a0f5401016003542c8004010b140d03000c0903a4030380a180551700d21490b4040141c1040c401408001e4558060107009030302803920707600703240d00e15105c0c0c000110107019691060801c0d0b01e02445010407401c50254a6a2010a0710901400080c5046840c50280c03000c860341484100001c11400c0300ca41c1039002503405964144 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 163413102 1250 163411852 163411877
    0x902180609030c03030a020f010501060509060331060b090a1e05070e1c0201180605040513150e1504180303020d0b04060f060809120406050c07030203060a020c0c0d03 73
    0x11959101d400d00541600445482c044103980c103002405103512560054180d450122921700e0840300145c11034018040c09100409803900c440068036404035908109040d0707158421501241c1c80d00064001440e02207485500b81001403507000644101001d640710322554448280c20015034456408440404103e0b0340606c000e87d0150f0488e981280c003a041c4281c520030402d002c218441d00c1580901c0e403e2002c079081e1011945e0105004100b000550507281005041c041d00414a01c02c52185511441c044201e414007000c6a50041c0c6480b0803412211031101e03510002040045001c41f00b510347e20300c2c2c07175012445a0a143c0110484109032510952680d40541d5040d40207400c040b4440c5127150f5541000d80298441c2d10a030009451204004400d0b00d00d03000c1d0003000010002e11983c6207402c01043e0f01000c0601e00b09413019950f183c1011500c5034032800c80d031407400080340c3c0301941c144280014000c05444a40c000c0c580c003607002d019251070750a9002441010b000410000f00021070940010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 163414352 1250 163413102 163413109
    0x609030d05030705090a090204050f030610060c0302070801020c070509070c0305030103030c03050c010e0304051903050a020f0607120306050a0501030c020604030e0402040308030414060105010c05150c0d02030702011401090218 99
    0x2c40d809042800c0c0682461044000310b0030090040e0065240c541d400601071003280340c00d05900017540001c40082c446480e00f00d01d40364100b00984100700c2032214a0755510205070007844010050400380b40215180e849002d1580d5840b000c038840d0034003802001021543c400e12510515502c140c1540b83c0502d0351b403079a54200c403440350b40c0c4001d40402c0f40500548812001c28007a50600400f4840115121810705080108144154000395512075000c0800c200180000c6025402240c046410034140c9154101150304c6105141e4010040c81c03021a20880c240d8060b840501990016260076000580740c20054040712021303500f08002d60701c100001000248151124a82c03400d0207000035042c031390b81e640d41c1c48060304150780459810200000300203140504220450040c6024030340409042c1d145d03140c40740c40c0d0510151100780c940c8600e0000b81e83d0301c3c0c030800702d4402e440580760840d520300d052100240244801d51308001d0000310480000381040e02402642c846c21100006964410500b9017003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 163415602 1250 163414352 163414357
    0x3010f15050301031205040810050103170403020d020d02030c090f09150c0d150506040303021024120203011b0c050708010e1002090f0405100e240409050f0709090507050609030d05 79
    0x1711040003810070001c00c03c0d40c020701800e01ca2101004001c0341d02e50440c07a03c0f044503403a00c10007072400311081c8010009a80c4070702a0102160301550b03aa42d404400380013203030810560324400ca401810f400d0074440c84510f040740b154880c19880003540d0501022056610002000380c3d0390a05841c1e003401102060510307a032100c0586c0c0340c000b04187c400d40d6242b02041072a0090351080d400b50300008414803045800d8040c2036514001d18071842c1482c0500c80481032001c800d4000c141d4140340180e810000c5440946c090050070780314464600e002a5401d9006049118075101100d003405019400500e000c014080c02d4500704610025061425460011000a40007035018591210588600c4c01154442e803184900920714500c0808a0905103124440e101e2005041c0d1020861700070041c11102c1141c41010020042c00c49011410100030b09000d490010342ca41c004000e4040ca1b4000601c04e030705580400f003294810816900b14903039407010002d590240380c02060305504114440700b00544101c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 163416852 1250 163415602 163415633
    0x30507110f0301050c0c07090c02070303080c130b03091c021f1415100503010f030b04210f1101140105010309081303262107050903011103010f1505030103 68
    0x40c0441c100028000a094030010348410395121400a60925400c0c014002080600100e00042c030103948800f034025030b59042c91001034100040c41010450600e0396400300c40c0480c8501e440034004a44500102c451580117507440c1d0003d02c40d03407854105a4016002c07000089541b0307006091514000001d124a51503a15842c440e015a144080319070b401c51402c20500603e05524101e20382e030151024004e20303e000303c11000038450184010040c0c2890b4140d008141c941c0046d01d101d041e115031030f003d02c0c09038103a0300980768010740554100c40039a0004032102c00b2016a900d814001128040060032922030280300b07040054000014450755002c0d03007140000a1040c0751355498040b028020310000d040b240c104482181c03055070b8951800314044086040c2e042030701c460300d2804100d0b001d03c40091003500c41d0540c0680f404d82c000f81c0d03c00e010708142c4080703032009002400a00991074142a00d81e00c01d005070700140d00e031100b000c610f8601c0c01110482040030f0b512240d02d16400c507140d00740b2100700500c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 163418102 1250 163416852 163416859
    0x50a030e0303040605010302190f05060a050f031306050109150b09120a0c05100801060e04110c010c030524030303040602070215070602070c2312030d15030507050d03050711 76
    0x16051181140100700451003035024039030018003541140304014010070351100100791043d4001c0180040400044a0002c07250111201a9505a0128161510701070b0340000382e203100b00401002281c0c031403d40d0301109140300d01801c101681c1c941ca6680e0031a48811350984004120203400c1c06640504002000b402c0d10003130840001a5260304e2261410521003012a60342c1000c000403c10350034a40c9004500390200e051000b41c660402c440207049918141740d482c8101d84070800b64081d88070000c21244140710580003480000c0e50090301401508043c1d401032040500c500a0351200d112402803002d13040d0b4014051451910f81e07846900c0607410083c0140c0e40000c018242014000c0120028a20640310709005600c420580c03d00200b00100c42d402055040240f10300000308541d501d008808144007201c00031301c40100050031502c1d500403040f403c100c40749000382c11300c61031301c0f440d40700c4085a21400441704515202c805124151002da007008000c0746d401d0000030002022002c220780c803c2d138080c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 163419352 1250 163418102 163418111
    0xa02090405130317071b020409121808030403030807080a020903060406050f06010306080309012d0e10022406011110060801060501110a1b09020f0d0b1c03050a03 71
    0x800000d0846606440032044007481024072000c03d90400a601004c1044402000f124a007510024090103c12541655607a2003482c0c5801195038550041520607000640340a94a503030381030262404810703107115004070809141c00030300320a000044806403640743c0d903003141c3ea85404500381c4070400301500002042c2d8090182d404591802c20990744180d00980000c01c0e2801c1a003001c4807540005000d4030f0405007490710a0024404c008121091002c007868000750000b01340102c49074060555540204007921082481445d079030280c803400c4680c108072904466002541c9003669a240407044000c1d444483c8d40c0c0038190b00411079130032613120b4070604100300c07180c003501566400d124a44040c40d11075642d40506101d024400d1140398060b003801e003841c5505d5100440c3c25640e801342c1c010028140341c56081440742c2c5408020002d0700410000380159103988070007185030074a401c4075140c107400a240c0001d8880f1481c1c860003440c0c005050402842080903241c50481e002d60004009000389a100d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 163420602 1250 163419352 163419367
    0x209030a0512070209060f03070b03061201181b0f12080c0102070b01080d020c0d08130302060a020f100603030c0605150d0b010906050f010215041704060f0f02031903050a02 76
    0x502c601c00706500401c501c0c603034814862040210109000d0714850042d80c80e100c9031a425100040d03a0419a042d801f502506c1e9038a1400098490450072004100d079400e004202e04c0084402d01c074508124414020200219611408a10194080d120300c08224500b4401001482c01ca0301c0402d5085018207d41c915100c0d8050503582039a0107280d04980240590004105200040c0039413a24101135101800044c6401e2000810b541d000c044050510306000680302e02130070021411900450b03019001d540c0310b1501c6040039480e60b4825150003030500440542c580f090641d03100300d00a4960688401c40750056a407201c0b0014040240031170400000d001200c400d46e5580140341c02190312a038041003407507042450000a644840c1d100c02d00400c0c03001129010b0f681c0201c2d01d100c0c00700d45941230b42100c0da40c1d410a001900c0c1041c020300d48400c00000c02040060307100405050308019a00c9030084041100002c980d240f0492206007410041d00e4180360082d80f1a0708090741041d546a405414440da = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 163421852 1250 163420602 163420613
    0x30609020a0f0e0906030a021e03070608090106050f0109060507060e030f270603010e1b070c090b1012020c031c02030702060f1302150d06091d010e0c040209030a 71
    0x414803a10011a905201e006050b42c0d0203403203104540d1003a07131164030341e040540c00b00350b44444200d40240b04581d00e0007014288540402c081c95489801003c54070302da80d0fa484c0183c520081a5140500b95003040d8000c515410314461142400350103035144000705240240c01c49850704200c1c0c0031195640c0fa07042d022000d1004101030480a05030171441c40d61400f00d03038100c50f000c0c8040606402880324040343d038005540c481707003601d04690024003021090740c2d0710103e031150401101d03555442c0b01408200c080030701800b4248a400d80701240c00820000052404008103403500200301d40006146810a05e004150303030f001747c01400811800c6038142221400c4000c8880c0c91803c6d01c02070b0f907501208000049070304005036900031040300b030007a10350b040c0040c04900043c0c00d0000079000d12030441008082103844000c68a10100c0301000f0000350740c4900c00c51018209155021030391500665091501e60390600c11440c05030507840c0103050f03080320b140c10301001e500480d82155050045e03000080100f80c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 163423102 1250 163421852 163421857
    0x2031209060702070e0108030a0f09030c0b031605090f0609150433020c0904030c02190609061403150604030213020a09061e030504020418050105270d0e0103060902 72
    0x20003005004146040301000749024095030140380407080c0300004101880c000b0007200c0600c02107180018031040008010b4612270195407004004c20044d090025150b051503014500581d5440c01c840a2110500c0048400c2c0c01000032080d0700c2000d0b9840070b01d852038102c0041c0101600580a818650355130000080c8030b402903030088103400760b10a95054440301c00081d01e076001005060401c3c03880818070000756585141c529550142203500045020b2501903406020455401003e03401c4c000d0780d41c040314108003603500c11000400d0206001252241c001c0d04480c8424030aa03070301500b140e8490324000320b0019103c00840d0010020800400542c07902040c8901c0101c4081d00581c1d07540359000c00824008080d1301160411018030f03030300c5900512040700181001e5403440c0200c0d0903200d41c00010300810310501d00c00210b41d00030010104010064201038170420070b481806209401c01c032044400d2425042240301c06e50000030844943d140244145581341c00c06150000d007080c2ca0b540031000301e9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 163424352 1250 163423102 163423111
    0x30b03071a07150603080415200d020c010e011205041e0804031a040206070b1f1805100302061603030b090103060506091f05100507120305040218090606010c03020312 73
    0x8180025000306005a00c0c040c00700640f2902001c001261564a51419034001d500920203140844214015003030700c0703140d145000e03484021001d281840340b002c1d1159209008915000035001d550500340466010b8800c800c44080c041e1111074000700300c800540000d0000a00c22900300c801000c101046100304013030030b040f1920911015a80d13604506026455100a4440c006449460000c020058130f070002036a032060b62083c2c116906031124014030072920f2902582c0e1103035504180c00001e1702c031013000240d42074044240c0b08004035203822502508050003800045d403c2542001000c94502081d42005030150003881e0002d003540c15040003d5440d0701c2a4401d40340700d5241d0781800401e10303090600c20f411186008180003c10304903c4c00801c2c00115218040c0b00b6122641001c0703406008404642030f10368000c058062000089070040c00801c2c00f504d040e4026004402085014a16400414002c082410092a40c0d076034000044600043e081001c800f14003060041d5400c030901c03050024000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 163425602 1250 163424352 163424399
    0x6041a0708041e0902210a0e100507030e06010305071703040b1206120c010906030b010509030105010b0a020c0d0c12030e0301090b040b071812020105040e090a030e0609010f030b0307 80
    0x2502100051400320400d41110082038030400804440c500946c40000490132080d0400301d40c0d81d14000b0480082240f240d21207403a000d035407000c00c007880c140c1d480980721304050740b03041205031524003100b40e0729482408001c040f940801405d01c060540c08d0516075007090550112480c003030b1034210910040d00181030040c88030404005004007441c0c20034083d5010701e1080001c01280594100084c070704c410910a0782c0c1803650715041100982d104204803100031101400034081543d441c1840041503101e502e15000600441e00600c080d880d010740540340103900300d030b04140c005003443c1c60201c1a68509000f02e0a0005c0c0002e040455202030140303a0145014481a552130b00d45420015500741006021008008001402e09803040308107083c00709961343d04120f90340c1c0303840e07901c0180c0e443d03c617a80212001c3d40c020f404100c1ea001c0000b414120451080d0b0303e01d1040c0e003280083c04041e0003030702c0503a4042441050542051403190340000032849009040325441a42c91240364400d11090150080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 163426852 1250 163425602 163425629
    0x30c1606020c01180812090f010e06180303070c0303240e0a05010b0f160510150812030c040603050402030a06021309140405121309051312090506041a070804 69
    0xc420020301ca40201d030f080701130450b400100e895490703100c0ca10030904042800c1c0201c2c4081041220100314007000f0b51035000003000030381e040d03000345542c2c0d407000c8985002c041514180203150307003001320030340b40200c0d0309031505a940c1c030007a80c0942c0a0a01e030002d0903000184203100b00d0840d11102c5c092002044a41c6004800c2d00340100d5403001c0d150f058101504102c01000141208106481181d04002c0e04e800d91300720405261400c9410800d0545003c0f00ca203040640c40c41070480e00d40300310700440c1c80711421200fa025203010381640b030b80030032500300001100501c402c01801d070081d009558800d2006040c0d03040e03581c05a40b400200d810078902038920541c6410140180340703151141340e250140d20207840c0042c0c54140d40c0e29540f9540c0b600c40700c9142034040341082042007502c182d030000c3d028020042c060362800e05613000c4520294102920b89044640e400080e95000c0d107007020035160080c00d21440d190510b41e0400261071019510a90703000b04101c1400070070076031000380c0040c200f100d40c86030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 163428102 1250 163426852 163426867
    0x80702060a1115070f110705060c190503040602100b060910110f030a0e03120a031d0f010203151806060306150309011b110307031206050907030b01020d030c08010b030c160602 77
    0x1460040b0170301100081c0500708174062148440041c508046510032584541d550a0707072103406040c0707000e0980700001500c040340780d00100318010000d070054960340d40c222002110038000c03120680b0403d100700381c0c000e10f081180e4080c500340f071100f0507000074040c20154086044640c0b140d1902038641c04101d06a000800c0d4030010036400340c44040745101c100c008201200d1218110a0702e4844c21181c1340915aa130105203410319640706030b81200c0c5082d031066034140040401e00354081d5100b1562900b0040c488989004945411541a410030901c406011040e030384100602015a202504039030b44926007104495030201d4480c019881030440c080042060b01100c0400910406031880c80d038244410b15901c0d0400103400025510314942510b0a1007046213014403201c0100401c0d04160b80000c00c0707004106590350150010b03c2c250303070203030b007241c4080130326500c1103080300c040c00a20000250b280004200d68886e240c00317580c1105441c48201d1078a160f141c0403a01d400e408610403212250080f4120 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 163429352 1250 163428102 163428107
    0x908100c0306061809021602030a0b04020301061205031c020c330403020d03050c090604031a0f01181a0901031a09010c050a120623120109080702060a111507 69
    0x80010007090405168140218201841408007401188015035002c600100d8003a05500903407c811707000b13419903103490214207142044180840d4180d0180d82080000503500d00d05104510200d0342060281d0708000d055812500748014504081e8401a0207008801c5111024040400030122400c400e0412003190080c1c2c03106c1541000030000321490f440200404a6004900110700d22164940000c6c00d41e1100305454030740c014854080d420500c046004820403440700e944210b50200203070115a20b1790307001c0d8180d1454034240502d06141c1498590107030147c1c042c3d0080040840600c1c8482c10880b0014041084003000340d1094648014180c1510441c1543c00d04054100b0303d040002d1044540e480c0300a400341c803482c20a50100320711070046418444c0c1a510800141001301503800b1013030400e40c5e484082140704000d80b8030580340c012aa51034500140324141810703a000ca07596041201c55020400c151f004482d07101c050103085000d2062401092003241c0704c0d035030500c60801d4a0306150600 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 163430602 1250 163429352 163429361
    0xb03151203131203050c030304030f0e0f06041206060e0408070212190206030402010c1502041a070506060409020d05070b03150103090c090509010b031014130b01150908100c03 77
    0x6485141d001000040010504103a01d003007075500809103000e40000c2d40c60111024890200701400342e01010080c4001c05038850301c12403030741d8421f645001500e81a001006041c486d108036080d44080108410480040303000b09141005006110000d002a562603d42e02051001c880450b601e48c80015150114a0040880040c48610400410701000301c04410b50f0304815121020f407007000003000050841e03100e0141aa05030740c0c01912410341016040c01c00000c1d41243c0540c0541c00100135850f82c0c80140340c0240d0f0411500103004040e242c864800f40b000901c40480f042c0c1c1c06c80f68100111000c11400c001000040504540c6c6c1980c0b40390131151558548944080b41d0304042c200403000011842134a0301800b5610034000000e0240c4070304030b10600502c140700960303405d03000b40c840103c2c4400075584800b81c078480b240d504501e5962074070848001802ca8480091041aa8400500030100007e2148501c1c4e401c90900c21f5129417201425854034543c842404031260303c0c0c0e410014215418000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 163431852 1250 163430602 163430629
    0x4090903180b0301060c021c03090608060105340b0702060709090204030221100612020907020705060318010204030b28020a0c081602190807060f0e06030601090b0315 73
    0x310107036050800304203068520062064500304403003100e00d68259510503610b82002c500740d42d07110001070071030310b00a0100941c9125030f01c0440c1003180010810350041c0101c840150001c980e030702d001215900740306071410103101d8401406840341e6558000034903a10045029a0a5030014419031906240003411a542500300c2911540140010001a112504080359031030303111300d49096215243d84828903002c1c1801c040d041c1c59003000d00010300075412141d0240214000da0306040e5559460382c00342c1c1c0d40d600f07a01c04c003a0032500400000e4039449004518250b0184510009454681d03070b500c900380e0b0720a0503125402041d0403003e10038401d000a86264154200d403407015814901d80c0321000c0c1c0640301c0003902800d03030500040c030034a00c5480700500d8a00d1582c01003099800d02708518221440c0d136200c0c0207004080c441c0d5003010501d03900414003026400d090f41c1e03620410b0f41480d000d0128581006e0302d01814403224600104881166101a611543e0a140110f14003114030b420858418030050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 163433102 1250 163431852 163431887
    0xd0c1205060a0b0d0b0111010218030f03090d0b041b060915020a0201050f1b070306090b012403020f130305010e15010302310507080403090e07080711010e0304090903 73
    0x204100f201c842d9480680703d00c90a003041c00148814441c00684e0503072900d4040c0342407548001607601d80107000c4024116104d406904075901441303182c1c2d10550302d120710030300c3e980e10882d840350400008034100c0309250720078818282c4070042e0400304001c80e0020400d4000134040394035030100340180c00d1011010354482c0d01c94802481141c0da0b17900087d0240c418011514640c04002409654065441d100001e03500020001c9902403596814104000c1445040886a0b00051000042ca41706c82d800c0d00700c4411716070031044071114034501c41034000b0360200b20450b11155080c002e0501c450081aa0000107501460020584514101e2000c1c10b2005c1d00e0365041940b4107000040c400341e2036490100300c001406000c8460345020000c1140c80450031010054103103400e08042100aa030f01265940c01244286c841001081d1035662040c84508105d4903000000da840e800105903d1081c4140104550b400300009041c201c010702c4642580d01580041e24040d403980400420154400d816195901940 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 163434352 1250 163433102 163433119
    0x50a0c171005010e03010b030f10060806090303060405220b09070f08031b010603080403030507060606030203011404050709051201150806040c0311062a0609010507050d0e030d0c120506 81
    0x40842a0070508140907443c1003000c030b05204566604c095200c802c4800c001001c031100310041604280e03079003941040346455242400d100107070441e0b000800700d00490019000e18110b98860041c00000c200091030300303d170f2680c0c10a140c030f240c0540741445450180a030580c0210fa2404084881c40d041d00c0f07500c00b01800c5030200007008207010200607518108500211324220313105200d01c0b24003512040d0400380031004001800400c054110b4020405681320702c200344602c940e1140c0507030482c0000d2003281040500ca488030003040c507240e80000d2b40302c820303030401d103809030340b01c00104000341e68002102c00c59a43d20300c1a1210b0340f40c4074003100000c2c41f03050300904007460b095440203203042a03032000030031480846080c540290b41e00c0048c0d0310b105000510b030045e901501009980b0014040340200607032b00861000c2600c120040c0101c40c4561269100e0600d07280310b00984000402e44a03813421842e0105010f581c003034010602801d40402c60642d00e0250602520040104450340601200d00c2007856 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 163435602 1250 163434352 163434361
    0x10909030305061c17040b04080a0303060801140703050405150106050c01050f13022202030709060816050318030f12090d0c03020a0311160e0a110f0301120312050a0c17 74
    0x700c0c02140b41307150340701e40710070030269180500c1c0480c0d008580104c8404e01c000326021890140016240c1003440c000e9074140412503507461118201e644100350520407465030b80024014901030f40080790014411000c031003c004801c0300c1c0d150405400c0c0c01c4200040c000140300180b41c8404d02405400605d003d200310482d040c00000380c1c0311400c0c50300d4024080d5140c2c0c64230769050251145000340010920000790364a1429280040880440f4001d034001300362108081440d0172441900c3c8500c0d002d00d522894a99200d0605034100e90000f82d44150541c401044400310340c0000300b015081c107214080184445083c1804010b003003940d14190741e420481e81c100200007080e400520000d500c1e8040c00e100d1103d100e071a54083c1003120303c141201c4039281e011000520640d04049091240e282e0100400c2082e1140d6080b004510605c01c082401d00300a000500110781c80c80032800400d8400e08040d03520704800c402501c26a00d0441d001c441c140e65035020b4400f8a9009182d0318107100141e102d90710a0f240 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 163436852 1250 163435602 163435639
    0x1090b0f03032b0c0c030906180306150302150909160f0e04060e040308091009021302030a0b090a060e0601030902030a110f030a051006050a0e13031701090903030506 73
    0x26003124081c0c014001211002d0f01609040080051581010a02400f10b40700b00182a005161508800058503c0c50005403503100e091205082e2048140400c2c0e401d20b107485646c047c0c010180a07442480c00c0010010040c2e0310562108600b280014000d41c40c2e5200800b000280140144000441c4524840581d00c039a4050000c10811406003803041d0860068804070300149003540221488600e50002d10050581241907907104e40369800031104542ca0703100e02c9800380c4440a40007500321040740010414088950090742d4400c0d00721400080198000e00081c1c000001510303081c5103c1d070754200138000d0102c121032507a8002821300f0140b2071090304d540800d94404964001a00e8081c541418030110781e240f0080e150040001002c60b40404494241a40c940b04c103104100c3c0a03510b040d600180c2400d00c4589030084884003a10f504541c0d50356a6402110f40020b00100e0400404100098030b010501c00143e010300842040001e802b18585405801c580d0040c04140c070890324484117106052 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 163438102 1250 163436852 163436857
    0x9050c01170a05090703080c01150f08030703080415060b07110108040b040204020a090312030605010314010510120e19020306151e01020c040f141b04061d030706030501090b0f0303 79
    0x50702c0b8000041c42c2c2da00c10100509244c0381b46c20003051103000040c00381d01058150031101c41c0840c13a0b400e4010b620782d100b42c0b45070542014802d0b00b00300c1d002400803e01082c012843d6603030240c0603038211110442e00110310300031202c4c99042703980f0401c6d01084407414807407540c103101e40001007809c0c010124105034076409840040200001d1046400260004400d441900400003c6910802d80542c50f500044080e019240502860b40040c0c0342c28040b44a44030030600403412500060711001c02d24031008000c0703c1000110034503151160b1108a2580784450412280c40d0a0a98000444035481248100342c2404006008003803001c0f01c03038060100c10703510000400441041009540070540d1404010703810038444da450b05600610345201080640f007039800000440724012601d00c607a55900c40500005520b10002e110403500c140814003c242c0160340800350103182c500b81d00d000d200802c000905c3c0c051260071080000303458100420185039640540040030354101c034048540081075021981c0c07130 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 163439352 1250 163438102 163438111
    0xb0103051513020f0d05011406030f120a0f0c080a02070306050c0c0d270e0603010e03030403020a0b0c19030f0b0307030b0415060b0a03060e060a081504080d0f09050c0117 75
    0x34030001d104c121590fa211644010303415400030082c0506d2340c0601120034802000c961180c02405541c00983d420003003c0b840c00520200c40d64018141a0510400c85000490300c081c50103000b007070034400c0003285994028181c0f4113401d034028403006045251003401d464014180d0f400000b003e02403900380320400300711105146882d103400b244203408003414094490000100d0200e800c04c181000c110001d1000207148103540070b070b0007030242c0c041a2444580e203101c12180600180c1000340d1440c002400d0030122500012580e84a0b800d1032194618421034001c07440414010941d501003103080c800440c042e01001000032400b421001780385488030407800c3c10080004201300c070f000c9001300c0358180540c41400540040c040280d142d01e01102c000c0c0050400d8060109507580b03210015909103020143c040507501d40e08040d1102c5294001d05116900001e00100e60341c180600407a8912045481251203034240701c0004900380580c1d003841c60412041380c1c0100d04111080c000c4c8a1240d421103401c43c1c01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 163440602 1250 163439352 163439359
    0x50a060c08040f03110304090f02180a050618180c030a2004090b120d0f022104060c0f021e0a0504090b060919020a030212060a06020715110a0b010305151302 69
    0x1200d85c2d1040303819072040b500041e80040c80c0c0640b01d404072480b603001d421014080701c500005048484200844036045110340755104078200084001d40c00e01403401ca161b50005083e403480c42c070315001a801502001c076040c10906c01c001c0304010940c0b1060040001e001109a03000060b1310040981c0c452030304c20b9010b41d0804d507031602010181c40d1145481c8001319450201514080550b1500061400d80d26824860052080d010000407050340d9450783e2207514401d0407014a418500101030328400103080d000d4882c0b5541c00182c0700540c94000180702c410000c082c140d540070385001e0401c12114456041207000f02d02c0d00c40c5050004e0142c900d0030390441d0781110784080070341d141d4280b80c44002e8100c1444841d1400454122001a01034028050aa914551403099959640107101d059481803180d90016804000304101800c280200042250f0f1289082c0401100074000303c1e151000c40071040b01d2003403240004205105050080c071210f802c40b0002e00141e0700b003030741d541400a059000c01911 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 163441852 1250 163440602 163440617
    0x105090409050f030310031203050903070609080d0e06060103060e0402030c0d0203100c08100518011e0504020f071a0f010510051902070501031a01080a0b0a0e0103050a060c08040f03 80
    0x20b008040103c608008050000c507940c900d0060161482030b00d0504c002c07070b18004042d40c5411194001d00499200c5d00ba075500560900f4469214a0050000c454040e5001c40040182800f070700e1143c017503030600141d687d000b003407141090070005045070110f0780224042c0502d48240300041e44c1c08074016402d03000032618a600b82c800d80c00007a081c940301d095150b00301e62400340c010140c41d42207800d082c411122114002000741d581d43c28052a82031454480c0b650021040060001c680320304580c0900000544105642649440104040b64407146044107803032030100d080e20801030507800e0081c89190f085444900c6d1308019a000c0ca00e040103001c1d062082c0c8a1080c80114a441740040d101e21004030250848540c281d020080e45910040c041c050000c3e09201c54001c81e0983c1040e5607007a644103030344050050360f80c464001c0061031001e03a2550320030522600062909078a07001940610700450107049203000c00e01d4411f0480311081447e406001189041101152103000f09265654042c10040b9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 163443102 1250 163441852 163441871
    0x1106180f0a02180702150a0608060105061216180303051c06050607031409040c0806010206100819050330130305030105010302071a0c1308070b0403140a1523010501050904 75
    0x82c102106c040b102106000c2500030801b85c4c0142d03401510441e42d92205403189640c030b5005003c0315114040100ca080c1c0c1c04880451004000c1c09a5181000c100380b0340074506042c1c080306d07a40c80051541c4140e00244001c15480d1280d50584500c00644060303100c2040a1854100418803d01859802a00344501081130310900c03400d50742290712100c0000c0080150310300487c0040c000301c07810b403030150051041c0d6000518001c0c001941401f51202c00c030003810b1543c1081d821140d0b401c00e84400316200d000138000003980450400404da405a641600c5418035072050b451409c882c100108000828010f032800680445c0c2c10030700b01c0781900d400f0f207030140e6162403e0030840301c0e03604582e00d24000c2c15001c004000ea500c41c504040c1055650301402c1103403040c2d40f44905565183d20f070050b010112000c1000300002250452807186c4030b005da4013910308040540e203c0c44198050000032900c8a80ca03101503151040c981d01c2c010b40143d407030358a2a981941000300080541c003600c41c010380030725650080103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 163444352 1250 163443102 163443107
    0x6130611014d03041505040c0510140301060f02120403020f010c1112011d0a0c1203020a05030c03041508070807030213050319050c030a120309031106180f0a021807 72
    0x540b00210400001550040e0000101da507000300d40a0341c1058038010030f100b0000180c01080d0095800140c80750505040001304a42070040c0000001403102e1206090702c083d80c42e0b0003941c020b05142e02c646281c8620b02c04040d0030050002c0e070f2a45984001c00061005075919902e8145019081c60310043d10803a40c50300300901c2e107500f28000e40c0141c0f070017042c14404a05401800d80c815a500c002c0c6220545d22690701d503500b0000d2802030000ca00514203100d0441c0400d1210f031154001d10444140c5c07031a688074141183d000b01c46214403600300103020310000e5012241e0300c031000810702e40318100d494101c400a04901003e04044109074000a039050641b1442c1c5061020300802800d0300e804080700c1c0070341005c50502079821075035070107004804034061801180041415030085140540d03d00103090480081c0600501207084c03058403883c146d5100d804220740c610400d885a01c18242034107840401e46000d10840c55000154000740c02c01005840f01c41c0c403034100d00c0c5242e1004c081500c48030001e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 163445602 1250 163444352 163444451
    0xa0920010806030f070333050907062105250305010302150f0d0902030313080102090406080102120103080a180806040201080109050702033c071704030314070f020613061101 76
    0x1000c9000705032081301900c07d007079440396020314200c0044510035a96883d0603900e081e0700101d082c9905202070b08450b00e10020741c001d264444a6141d001c4010b2015282400315814885104000256680b0042c411400c20b01003605004000281040c14043c1548107100203106205502c1030b6030781c0340c41d680b008644041056800060350042180c18044d1548903483c001d41124000714071a609005d0002114035043c8220340c0c0808200c10700308d400740e0860b110010b170760340696a500104880010300c1c10140618000300c00141004e00d0141106040c68000140803842c103800285840b03182c4002e03c0200d0750008115081c5400d00e0100c4012304070640308255055032080340e0048841c66640c56131540b0102d910003442e03840e11078503619030180790102c006038803030145000060100e1000b000f907225581064003d41903c51150851130510851381d400f01d0b40c1a003210489007407070410481c090000ca80c0040314102842c540000800102c119100e0200b001500c1c11004084840d0001c141400b50075032480 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 163446852 1250 163445602 163445663
    0x40b180a0611180a0305030702010807090f0906140f010905100c1e1e02010c0303020903030d060306020903010e06130b180a03090303030c030504020f090a0920010806030f0703 77
    0x804100600740110724280983c071008280300703c5801d04460302d0161404a0680041da90041d00440c10700440e9801507a000402030541000d010f20160000344100520b51950080e000a1314089010b0b49000c0c02c4440d00c00521580c0343c403400d04a08604c1199a01401c0c6104840c0100c0b11001a05444a029212412400e9001d003a0080c003070a0f2002c54243c01c10303071034901c5d07101e4510503240d01070090785038608800c101c90080c00203a020009a000c60700c81c1d000b42506071b6000742a41d18200084a504c0f040702c45a40c401c84001da00030407052810324003171040302c00000f18900a0161840c205038452004004270100030105032052000c0340c0c3c0f080b0038103004050b0020300c900315528045d05003000fa181000a11040f40000e00b030110700350b00700e842401141d0160b5400303054154044035000c100030400350002d04203131b402c1e6590036440303006c100c609554540080c104001c0220181d1101e0004101a50003400740340254860b50380302d0141d000004540741141d4011400c118600400401040001202003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 163448102 1250 163446852 163446863
    0x10e0f090f0a0b090f01061803151a04050405010b09060607030903120c0b09070e0c0a08060120120309060705040308030705070201090b19020105071e0e040204050612040605010509040b180a 83
    0x401c0050030380c0c28207180ca069400302d4a40307114080700e8401d440000110f49c000249078421505420f45100001e410131000c4000c03084030881c0310a00d08000c075003142d0b01194155041d83d151000e03040c06007400d140f420b0300107030182d03401e03880e0441c50313140038180c0581444020800401541e284c810035114a90f80e40c43d4592040c0c2200c62410205d0002c0c1c2e48085074000e81c1c0008071080d000c5600b41c1c4850048032012503081e00c90070500d60340c00006462040e4864041030a10101ca103400007824024052440d0000340780d0304190f02ca0404111041c42d24200600e6039040c02010081440031030504d41c03e50340d005802d4a0425035a00306480102c90300b140580c000c2c1603610380403500186842260007861040c085a50003081603658021080343c0b1840b40700310060708600c2c103096000200c1e02c0b5405003010064058405498151f90300c0200311181c0c00301100e0b85c1e00300d00c11002d0100b000220301a41d0300420702203440b07a403d4106070f1907140f11400050400315aa140c5506281c800766401d1062009070f0b80c001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 163449352 1250 163448102 163448119
    0x1005040908030a0b0604060f080603150a06081005010302010c14011e02030402091f0b130509010f08160506040b0315120c011b1a06060705100902010e0f090f0a0b 71
    0x40ca0040d01c29081524105151818081c0c1800b09007407100580e0700f2a411a030790001144980c8106881c58000a0051a018011341d0411940c4010301011280900c442113000170b801c604e400c400d103040445401c42c1c2c00c101c0381401c0c01000583c2c0e01101030b04401d80c00c45c40d20410000750350760043c014049805460364110a100348000002920b9025500c644c5c001c0c1c9e0300d0071b40b1743d940c1c0d4512191240092004400303040c404000784007024041e00076100c1950080c40e02c6807130680310400241c051000364006100c4c05602d01003400480d8081c064011224402c800c07080c806410100002c0d194002d81c00b03403100002c0c010001640e1744d0b852114111007014040c7c0080b0036001248909034a4208040c01ca5010601c100041d0310303070301111000c07403005542210700100c4040caa44000d42c22080e0103403240e07901c42c9061090001240062022441903004010000345410701840090010b44d881001a131040041f00003051013a00d4035910554002c2d00603210312166070742ca8100e040203040000c1881c5d00102c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 163450602 1250 163449352 163449371
    0x20a0219050c09060306060904110103140c03010303030c0203190309031202181207051f02120a09030605010b03010b090405040c090612060e2a06040306141b21100504 73
    0x100d4000007042c0251044000c0e5510311044c903a985006461450b00041c24000003008541c0c8180210b40c002014500410a08045680080c58a605550b070b40450342001004104054061154281d1005640040c40c20210b100c1c1c100701e482a041843c44083c180c4402c3d034441010b21480d00c105d841400e023402107440f17403600c1400300700c0d00c1c201c15241c1d8048d00e04070084c11400440010307914110b4030001c1030309d910180c802016071120000f814200c800d5200311940030a24003170b9880540400d01160355000c02003840e500303103031042e99030607888494544802c00040c004c1c2503c0c80e04440c41c420003035601003242e0304d440c81c2c00130340d00249030b00038605140f130200e001c41c5803490b00020368801805503a00340240c10120601c191144440313a504520f4a49282c44c8002d940c002d03400d0750800220080c041800e1564030b4032084203507400d8403080c0c107040c0e094504002c0744035441e9409149003103004d51440c0c1046200885544030f0848050b0f40141c1000d010001011840c52107005005000c01070011301c0700000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 163451852 1250 163450602 163450613
    0x1c020a03112b020a06020c032a090721060303081f1e030c0e010e040f0f05160602010507020c06340506060901060518010503040609050610050a0801110d020a0219 71
    0x14405000ca114003001d160004101d0300c001140340420b1001405000e030001c0110707270b41c201400c40c150001c103d00c0c0c2402c9102100d80ea034803880d601ca101182c0f1040441c640c100c0480046200b50107141003000d00c0d00d041800880d510803140743e4000e90360b18640c0000002036404c0c0b40c00c034140d6445024400b566640e1084000d01404d460422280316072a94002c0940340d941d01c13040040309004505041c440c6400080118402e010321544d0381d0f00607802c00061080c02e4030364505045c10322001c4051503030030309010030070782e903092041542c807280c03500c041d040082d101400503c183c0300710807040c05c031700f9114140d0b50016150110030035641c601c250100c0c1442e061030300e4248e8485d2800c9440d10b2041d8981d40001175214040d9089a841c10007a01c079103050507044ad001503805400142c0155902076507403588100042d01081000d0080e000a43c071390094034500f0040113040c15081e0802401c0303904180d5201d09000c0d4140980304002c941400c007684421000c28200c0c60141410b240001e4400e076100c24000380038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 163453102 1250 163451852 163451929
    0x13050106080304180e0309041e0513020a15020c0f0a18140f07140706062d1202060301051519080901050705040b16060b0a030602091c020a0311 63
    0x4215041c44e100302c0718500001402c82d0012203101420303402c2041007100600d0264042d441c01c540011441c201810000c0031134080b41c808440c6821880f440c41c2142c404e61800c080114000c22450080359141044a02c00a48036801081203a004404d14020308a1a545882401c0046c2448001109800e6100490500542503400001790000503120129103101800441c0c50b210300c04d15203810301c1200380b2100c0001c40e5400b0003415124155180c10204103407400f441c240d0300402070603550840b103d1310300300002d040c1d42c0c0c254003202d1940d0038111a5401a00c039902980d046840031a25034807a07004c0040b5071087c2d407240ca12043e101500324105542d40c0303a00100e03002d0180f06400700800281e902d0210984051140b8040c4a6500400340100d001205500a020341410311500021480312106d038007140c240c80c915002181e009801007012007548c20500442e6080c009060b0f400c1ca0303642d5071074000c9040d001143c04050034007258060072240644884500c1660038103034036005410700c100407411540a4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 163454352 1250 163453102 163453109
    0x190203120d0912080c0a050c0115031101020705010f30050403050309010605090c19020f011505010201180b010b070602091e0306060d0b0c07020103150603061e03050604080313050106080304 83
    0x450050083c1c01c5280c4100c024501c03603410304840610707102103860141c0b01d03a005240030005564842400a007041e2200300f2120041d4801e0f403e0400d0b8018040019040040c00e4004604000700d603103a02405c2a44aa4003080d004c400101c400d5064200340f03c0c44841c52641801b0041050800061004050b400b40007940700d10480700007040602e4032501001a10700098415103100316040c80040801e014400d103030151480d50b40116105401502d81103820b484003884c01f184208101d1030204800d50702801101c000c00081c1300706855054460303544201d140018001d0001c465000b140580070840294111407c0c43d0b00100303083ca04280c4600c041c540305a1009a081c001d005801c003003038807400c1c011880c1a041e40c2c4541800300a82e40d05045802541105405038100b5880703803200c0082410b251155006071001d5600030545a0505441c04420000700910400016000c00d040000c1000420041e03040b031350001380f0940d03980b1003a448010380c0342c08100281003546000c0001030103440020051048 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 163455602 1250 163454352 163454363
    0x5014b020304051807110706080702010c08060a0e040f060203010e060406090b0906120703140601050f100c110a030618060e190b07030207050f06060f0f03190203120d09 74
    0x19000250040340c07a4000c620440780c01030381c104801000018407040700d0b41d000b0b6961512483c1c420914901e81d19202d21a80028040791258061104207942800340e000e034070000f03003000440c0703040c5600401e0b0b0504843c403600490b440302c600070504100c090610b550314183c0200c815900c958542810102e440d00948205100d5841d060b00040ca120b0700f0b001d42410ba940082429400756164410b108160a51014204850003258000710001d010300a180c1d0550040380018030b010b40c100818846141c41c0d03031404a10500c55860700070112540301c15204005980248000d4002e484000401c074000c0c0c4507000286500c0c1400f0b0090001d41142c40164500c500407e401d000e004100740e215902c402d001c0100d43c80d2000203441d1800403900003c00c07660080f0311490f0041c58034030991203440c14500801c0d0060602d03000308041c01818504040300cc00300300000c41c1c443c2522203071800002e5460140c06410340804081001100555030180300360301850042440545e500d4021000314801010340450403030b074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 163456852 1250 163455602 163455737
    0x2040803040303020d09210f030e040905030d1d0303010b09060403081b071e06080c0d0603030c03180e01060f020a02100203092805060c03070501091101030c080c040501 74
    0x96006521500700c6100190707c00e4600c104020781c0300d0309104405103609405003c204c69121150740c48610850003014080c001540d1114940c201c404207484400c202500d0607486500c24180000021040b40c1c1140c27245005969103480c9000415410f00444e48040e044007000304001c1a80701d00d409a08005500881c10340d0007081d194041e056240401c100020180180348030b003445850b000b40449a0072040b03000d42c41d828450400213003015a0980e4004034005244003d04100705074205d41008805500c504162020701d04040d04212107010511448003006100585c0141c1940280103580032650040e01c0c007a01640c00e154042e5880d80000c40040c080c000c2c10003403070070840d01110103c2103903400c1d211103002245490200700c10390f002010a0304090000300304490000303100740b00c0c81b40072500c500c1d00c40785482641b0002400710f803032005002061003801e40c10040c130200700350111030031f4400900705488103040303182d4825040c50a06020b504113a418200719408401c10342215080800320440680 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 163458102 1250 163456852 163456859
    0x20d0606090b0111030a031503150e12160b0408070c060908210f13090f0507200d0f180f0f080304030b0c0315031504020901150806100302040803040303020d09 70
    0x40381800b1241c030110160700240500040340e4031a0308407407a10402203103528423250700c1e41c0b607450348440700d059120140303962110010b02d610400d005984070008852542414110041e1400b0a9000420130003084951000009020840c0d44e41c1550503468204040050300740d01e405028001c0000c80c001c5802501c203100c0d440460f200303400341c0040e508070030341d041c5410302c410003048017010707040755680c0640703101c90308008510a0594414050500b040010115035400e010344040c00d03031051300c02d410961130a241c10b1241603520002d007044040c1c605140076031035540c40c0001160000240600a690440c040c0c9001444020008402c6e041e20504c44494044d1569050405d69130700c07881c80010100c0d0f0f1030000150440c040e84003e035a020b01300c6110040413420f0341c2c0000381002d1400c072403005141c29070014802076090002a6078090081c0b03030940101e900d600c1c0300140655900810542c45400b040001c030f0341182c031035010707180182203030f40440b9190760301d902c1e002c0c0d203500201c403480c0c0020310940c0000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 163459352 1250 163458102 163458107
    0x801030807061b080906100b040e0703110c03030402040c03060803160201050f070c0321081b0415021614010e090a0b09010e0a0f02030f150f03030a18171c0309020d0606090b01 77
    0x1f04035590441d01038a024540703d400000c0c440024240000d06644580900035004a03200070801180000301850f56403405104006c1294004450901018504030060000607000411541d6814070319001003140300041c80100d505210b00540c458216001042c00010402c00d080428196072003403461040b8012203e211010b82c44146014100150400001c5054941c0211a1403000b8040840044ca815145e040d0f412041310405910300050b488049a050044882064a0302810355040000e03da00c140000007000c1c0700500414a106404001c040382c0880c805078000000d5000280c1081c0c029a9144c212004080c1d0172100c0d1000c807070400c60454003103403a51088910038004009540c0c075640390100030190301c24145d61080c0e0007490721a0401c00564042000e030800035038640c1e400130b0030800c1e06000c5215101c2517104130a1315100d003240c000c5003a070202e10b01e91100c210000d41d030204480d540c412805455980806900450302c0d00c2c410b024422260021030540380008030500c031550548004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 163460602 1250 163459352 163459381
    0x9060403090302010c0309050d08040e07030c080703021803010504080307020607050a080705090d060609050105010921110a09111801020604020306010509090f060108100c0c030801030807061b080906 87
    0xc0005812940c00d000641c002d44810500500a141c8400c8031a1103101080058916140a5031060000306041008003000c28840380c0c482043c1c0b80500164081b070b00060245140601100241500810141004848540000f00000c40107000340300506090600800c1035000307031aa0801400b5101c0007811981c0a5821104032070781030b54410109680b2004200c485070040700c012030b440015020000049a6280518001b501e0ba2000008440d45010300240600290350700c000c2d40049070100c940c40003000d001c003551280d074121040d103140c8203ca900050040246802180f821864a4078824011400001030b0216064030075030140d0302003006005913a55001203070300941c03517480003006000501b4200110380d00b10078088215a000705480e40c03079030b08101c002d82100b00f071035010071140e0100c1800c0d80200b0058024070305000c508184a070f02d0040003148140800703400c0090010300b04003040715a6100d0411041c0d01400c1380142210108014000c507400d940000c3d55101c0c00c0b0101301c000c802943c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 163461852 1250 163460602 163460611
    0xf08010308040302040b0d05030703270e15040b0a090b13021c0b0102280b0109020c0304031407030b07030213090e0a060b04060509040b01031718010507150e0708060906 74
    0x74081c02c0030b185500300805009054040d90b0000042500c110010303000304090401d062007500d40910b691014020300603007410201884061340c110001c20040032495005454003d59600302c940c2d002240d60300800c000e0f00003c00f0050300080c1c0b0b590f000900319010782c018511078230100c0b0b480f203d84050401507003d07805031841c010150b0310b40502007a14484654083c0a044006006039038009038104415001005a0031281218504035060b0350108500030b00182c1c0540342000c02141451640301e0002d540c0d00030742c0001408035051080b050b1003040c0411482000710f500038460009890503c0005004e50082c4001c81610b4290040c0401c40040c28000c0d0800c02c29042e009000211258903510050041c042c9200d4201d5903540303000c5082d48903c50003500c0307940a002c00b0b0281b545103280c841400c541052001c0c4002d10148110900c10101c003e0b441782101007440c00da512a2000e05140c031800382d044a000e01180c2c80c2410304900c4000104114045030380782c0c41502c189580c5d240c00701da214142240d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 163463102 1250 163461852 163461863
    0x4090308060f13020c011e050405060423010501062604020102030f09040608010903020604050d0801060909020f1623060103020607080304030207171c0e130c0e130207030f080103 78
    0x1200307402d203402d4184941c400104048090146080400c040740d1080c680741486944600401581d4410f840000208140c551000c101a00e0300791140c43e00c9000140c03001b4010f5130305450303d4941580100b00041c0281030b60000300305950f55600c0c05420103040070081e41131100c650381c09508046074aa603d0b403155806801841c80c2032015491020700d60312401c0007030f2b440303542d8080204603030400b4450305a081c1d11940040401d400c040c2007003880c0c01c4c0a4504c001c01c000d008001801300d1540400000200c6140c03001c05038955101050003075590080100c4141d08180c8409408144440c1c161800d0903403503400d00a103402e9040101070341d140c400902020750402e0b8200407040001e00600010341c1e0050091055860321610740d0882d00442003c052000070a60000305148210791401208440540c01400c000d0301450400c0080380340140064042980d995885040e80101401008504801035005044000301c115240b240002900460015030002d0003403418170044038060348049042c3c94010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 163464352 1250 163463102 163463117
    0x60405090403050d0203270d020615010302070f06022110031e12090f0b040b09270c0702040b0604060c0f11060406020303150105041d070302130305030703110c0a06031107050d05030108010605040903 87
    0x1142c0d405140074407032540bd81003503400c0000c4030108400c40030183c506845075001582d01ca0900e4a40202d040c4401c0307004090144150a01c4070030031022401004403540a010130400041500300001c1c803824294000c2c140100244000070070130351007071080003a5802d080c09821425255402070420b07015500a61656003001c1280c50070760700d001c4050740020548503d000350340c5400b100340e15030000010364079503841c0703c00030441000310328041c01035400703100c411340b082800d00d4900b0100520b11150300c0f07c0074226401d45074404007804580115242c03040d401401046d995540c41c000203590760300854105800003400b0003103890030f6104404035021103001c079039200c0d1b4000044060300f81000c0080c08007000d25900700060034401d1000d041a90003940500c0140d91601d00504010346041c030100c0120401c0d400c003110038105a07540a0040054038454580080d00b2030000d07804004500c1610000b130b2140c810080b14100d8198014000d5040c0d80041c8028000b1594030350074001540e003400300040c0401c00d007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 163465602 1250 163464352 163464361
    0x120c04050a21120f0318030e010815031b01120e030a0f120618051b0d0b010306120b0601090b09011e0516060623060405090403050d0203270d0206 64
    0x5140c21802c0910081c071107101a4001507541c007020740310498914000c01e660210002c4081d81522801c080d407140d00d154400380718450307600145070800b0305145a05002e01030021500801349000d0851501c1b0700541240c02d47c0341da200801607071041c010500380c0000c820b81000c1140b10006d000381c40000490100030743c100794078004242c0b44040001e110404001c601301c04600780d500c05009040081481498940265083c11401c1056400042a4008d002c20842201c203100741003038120369202040c0700000030741908040048024022540c44095008200f2807608203000b00c4001c89400303041c007600e8440f407843d82c44202c1444c40c0103026915010504c1c104000401040a000034014000c070b5240243c50490f400e14030b61012000e030b01c000c1d10050f80d154400c0c003003178031400030240e92003d02c0060140f8200d41c0400042c447d105500600d070113491000c0c0454109070140301621107000c0ca419082d512403420501207034000240075020300c00d0510b03220305c8645401021642c084030030b0a5a01600c0d136542c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 163466852 1250 163465602 163465619
    0xc0301301101050c1912110c130207020a14040c0c05060f060d08030703050709050a03020a05060f072010051206040e070b070308090c01030c1b0602040f0b120c04050a 73
    0x5681ca0107814040e0403c00d40900b440d042c0038204030a00c080f0503c0d4040480e074146086c40c00c1d4501096024802e00103a84082c5400000300301c20100f50072500034a54044800204001c0d00400300000e403c003550354008180b11110f9020388600f00419181000305218550084901c002400800740031504540007281080030b58011080d80850003401c4500000095600c0e400981d0080710024006aa10000c0c801c2880d0b01100e08002003004481d6501014115000600312110503c116071080d0000101c0010031000d040654625540000d024100c403580c8040034104036914824140c802c0c1b4070000e1aa42183c01042501c00800c80e011114001d540d903101404000d120b4007000b10194420075100007400211076004114462096070b41c030010742003004e04a440c00580c1185c941c185428405071400c0e50740c1c04070001c0400c43d001503410000c04c0023424504000e126a402c01002030600e040081803200041d401002107982c140400d4a0701c0d0350b2070300601102d0050307000e03042c1d001e03030740080401100ea03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 163468102 1250 163466852 163466873
    0x804080706090501061a0c0c01093b01081516051602030a0501020d02040f0b1603081513090b15030309040b031e0c0a08070b09040c0c06050c030130 65
    0x78407580000440f5031b194081600100303840701d510905500e00140d000c2c00c80348140000e0144441c00c0c20228145c5041596842d0044100750309015000742404000d2080c0201118610144c001e9034200612135859009181e210700e49852100301d14103104001c201000f44803058002c2030700043e91100d0800f100400c42c900d000c04014001c0e42d2520a01c00340c2000b2030000e00c01000c1e40000c921300180d582d89450100c2c88428203650240c00350300001e06c4825410540e10316440700700d0394503181c01016a5200d11301c0345c010641c03000f032b9a03070031402d0f5803400d080c0441c241d1300a1b24414059480310aa6664090890701078a003101d54040d01a0018481c4a8050605401800450340020180e514418441c90040012049084400b0301580b0010000d0200d041c9020a13101030a200c00c05066050704005070800d461003400807841c00340d82d41d414407251884c8500c010b5050300c0d600c174000388040e0410101d00c000ea03070800c2c0038030f5260840d1b8805660004a042120582c28548100f20041c03007441526080380f803e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 163469352 1250 163468102 163468121
    0x4060f0902040f0501050f03031903150312020a1103060907271b0809031206090402010e03100b030d020f060a050a02070f0510050a0c170705040f060503160804080706 73
    0xa50310303200d400006035100e0007949000e080c902000a0150724220403c0000901402081e0194200f0450048146252400041d200314541800704c3c140b0000b0988180b51407050380050610380c10b011120786455408280d0118050040c88000c4000c8449800c1546815065444860b80c0e4044441000b1040c0781b116000c1c1e4003901c541c051383c030ba00000f403500001c0d1018000d201c2c05000070004c217021102d80001055070007119480042d4140104400303090f51203500500307042c0c800c0481c10006411603203d050900100f95001c2c0540b0f1b0724900489420010f407110341d000c948039010700c14001e5502440014040500440034005100c81d84a01843c3c10081c0f501034100940c05808020100105000007603d45035240308400030840348a6504040c800c03200c020700000d1203a410310500c643c01603807000441c5425a81d42624005580700d0100556030b0f13204070340c015100340d0125407000075103d82010203980700e00c0e10320244501901c1802d0003110084000c54005103c02000d0150201203906580030945a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 163470602 1250 163469352 163469381
    0x60f120e2e050105011b06020906070503130510020d031d07030336050603070215090c030705151909030606121406060310020d150305030408071d0406 66
    0x248010325001605008100d85031014800c05603284031075450641c0300040720199940341c204080d506141c00203102da00e820000d50f022007000d190910620906604581031050010500e070703918462403603c6600c82d0400440041c20614031000040c40b420070038001030081410b0b601601401c191418150000c198100d00320781d243d000d41440d40100181046500c024600179201c07040201d406001541090312140031032030240c2d9001039002c3c0c64000c1a1509400d0b00c908441a5840c0d46d2030043c200d107400c9940d40920502e000c01c81c1400071907100442c01010000b015000d8a07074098444040c0300c100413002c0d41880410404100416500c920020305200e002c8141c40e040c1c0c4c85c2c540d6622004142e40b844d0300000d148208241460007000107030209140180c048a0241c8450324081d00000c1e00c90074080001030109400059108034801c0b075a00060642d0520401039200544a0406c01c1d030300e130801d02900086124024002c640c1081c00c001008a03514020482c030711641d5a540d442c0c0140900d680480d81 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 163471852 1250 163470602 163470611
    0x130605030a030c050622061a09040b1501050909040314070b010602010605090112110907090504020408030a030b01090e070c290411010c1115040515070516060f12 71
    0x1159981840886030340c0303020fa910603101100d113040075428140050940010401d1062644801011104c045a503640c0c001d007002070b00c4c00007516016a43c2c0d001c103540c20381c0002507a04100070444004c103094090b200c12001c15100c01860401074030340b48281e000c01544000c4030000280024441c48940c0010a060104207003445580e64076080c0550003a0414805070351101020301c01c6007030240000e40100308400080a00000c00e80700e0021030507200e000b007405020a000044c1d14203001d0100803006100c05041155120382d144259500d0360020300c2c20360002030812804015a62149000505452340c0d91400355580c0c450400c20307102d4074240402110705401181c406403040c00c520345841e02d6003120244a0b8401e217082d03d8155501003030515020b05021103181c07004081140c94191100314071058802026009842d240740a641c011503020303c3d4016007100c00740301d602e40c14801070b05990f4411130071146102d42c1142e5901c00141c49004840002c0c0784031803440051440b604400080c500012400103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 163473102 1250 163471852 163471859
    0x30c0c07080604050d08060604050d030e0613030605010e070c0b240604090912080c120a0603170a0905030a1a10030c080a0209010812040315020903063c061306 70
    0xb030804030119020340301e43d0050380b80340c008680c102007241c0d40542c085400c4e51500c0e041c2000280c50704101c000180811a0386001c2d101661900c20454100e0340881c8a0b10500300c1e520325100001d407909003e14045c4540d41004100a940500c04080e0750561044050196070b40311440c441d61000750000c031408450031200e400a00d5203903080100003404040a01140c2c94000382040752518002044081c02c200303040b02004500c2100340b05940c441060902c11140c0350700c0e10350310200504126000a44014206044409003142c0344009140b205aa41c17101740c90155508205500e400c8880c030041c003c552001880026080304c0b0550700d500c0742031030760754505003a2a44c844002c5001c05400109541e4450043e040035440c001c910540104000002000600b286e4010b20304580560b102c004d00c5000400c0081500310025015031f03240c06c0000d400c6400c58605601302240d00c4944686052601c081106004072400c040040c2c0c1c03a00071070308112075002e5242c260900600000e000001c040c0191340f4030011 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 163474352 1250 163473102 163473119
    0x9040c09020d0f1d031911010c030501050109080c03030a080703140903181e01050703200c040e010905120c0c03151f0602060118180f0c0812030c0c07 66
    0x42080554108000a0319680e944060302100c00e55801c00200e070445200b501d101104c00002c88030b482800d0001d440700800380250686905800c03070449a2075509050b80400001ea240e03102d503040ba64241e07241210a81c0e95401075403217051040c4240d4040e001044070008441c00760340f1458101e40c842c9030025005003000c84500c01014161500050303500b0000b0600900c082201080030458812146c882c840011f00c4110503c01e500030a24905200c0041107203c24540039207034144000340d58040418809001e80800d80e01c40c7c40380900d1a10803440e10040855001c014442d04228940c0003000b030010070402e045d840700c1c9810070b001d0b46941e80315000ea646002d840a1100c2940304202100340025810300e080030700c80c0c4111462412003000319600041040d80c1d0b001a405045030076504829007040030414503000540480e03460205140d0440ea000c0c401c0020b0382900d5949140140d0b100f010a50310303580f0054a0704260324612503801c10500100e0070780e1580600601d14011050300f10380c0d1207903881404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 163475602 1250 163474352 163474357
    0x6030b06070231020f03040b0c16060c080709180b0a0503030408010b0a0509040201120203040201020c0a06020303060a0f06051e1909030c12080a4a041a09040c0902 72
    0x480784041c2c400350a25680c1200049001902c4420411350030040300c055144003a00000b01b0244c929008000444d0724107607848102c80000511400721031b0175142a0a05d00702030858622185c0c0083c107007100140d402031044038004d007a1421036021045180900800c6005002240c0140790301c00498000007400b5034040004000600480340041945019001082100e8000340e201c180212605020003005170382c019546803403c80c0c0d0b02401a241c1d00d803400100c0c034006001c2c02c1182c0113003100402007a40c0b500000514841c0d001140c14891040c1c071000c02d118051424030404003c0303481072010041040d414005a03143c50407010f030150510704901114607403052500d030607402142c180b41092061040c1d41e44400090484562015100340c09a0744042c51b5100d0795116200700484007440c3c15484c2201206914451180075080d421840d403007a100c2012001c01c1040210200080d105071010700f0180640b402c042c0e019041420013256034010b110512100500450300c40404100c0412082e066101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 163476852 1250 163475602 163475629
    0x6011d011e0b0c0c0102010e010b0a0501050d020c0604080705010c171801020c10091202030705031803010f1d010b0a0e0f0709090504030203040f060305040c050f03010b060d0e070611030406030b060702 88
    0x44c013a2609050004e03007120f00c040c1c0c1c00300c5070b0390402945003000d44035180020200c400a1802c0c1d0781e551980141c1034028016002600028082d61091005000c15000640f04850040f40200842c40340360030150f03000e00c14010300c03071501c0b0004400189100c1c2c207000c582d56118248400503181c140601a0036080c1b03030010841e001c03056a00c4801074140943c541e0300e41c010306000c1c002589040050b8030b0350755a074000c103201c00c040c4440110240105403400c0d000761184c1031030401d0034032001c60b0030328540b4941d03010310307080300810740c6000600503807883d01d900c00108441107124481400c2c1c940007580110810000c1c120000d0000d50440001c0030f100740c0c81502e02c114080d5010316100e038207110213142070303a405a000f0003c050034442840b020428034107052048a13003c45014000c4044480460302400072040341941c0300c2c0340440c02c4184103140340c03c00b8034042101c60a8600054848105541000700080c140c00c6962060006205e41ca000e540200a0108000c1403c0d0400d4555030004480b80421b92 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 163478102 1250 163476852 163476877
    0x9030a05060411060307080a0b040f02210c070b010308090414070504060f030c0503180c03011e11070302100504020102070510051e0c0a030e0a0b030f070206011d011e0b 74
    0x200020700503c196440101001191a64a542040400146508000740c0724500321a50380301c0d9203205aa441d4050803041035412425522519032030300016003a102c84060841c480e01200c0010307039081e0103c0885218075404002801140d09580380d43d61a174010750302184c0c005640e40074000c2111000c0000d1480340416031707100c0b59101c0c10108010302c1800503540d4103060504200c01e10328401c0c0c101c0305803980300003580340181c00e60503010042c40c40c2080c0005210340551a01840301c054605801c1c0380e8058545100060000040846243c805440b4040003d001030700007214540c0b8210311a00b20302c1e0031900502c1113070f01468607600010020b682000c1505c01180000801c041042e60081c00d068071001000c0505090280d800c03001038030703801c00c910000c0c00c12034801c0f8001110391350b48880002030300f0b01009460300e900e441088035441b00c109584000c050b01c12600005910f41c0350f082548028041441d440d10140d1a00d00c8400c5004e040d0200c0c5480304800c800d01040b00810700014040c03c1c805907 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 163479352 1250 163478102 163478113
    0x1e04030b010b0c0c0102011b0e0411040603060303200312040807060501060c0302010b0102010e030a0f020312010303020109140a0c032916030e0303060a171204060216050d0c06050a0509030a05 84
    0x1590303407a01c0c080804c0010b074150b904160201c03d0804015031039100540060070142100201c0724002001420900d0800e00700001c042400f094042d49980068143c0b8480d840b400100101419401c0701c04030280840000e0754400c01c485140401e0303040c0c000d134001e441840018203040b00f590380c0ba0241c030303004d0b0081e6000660100c00c240a060382405403284010007030008010a41004031700c41c3d12442920704100502010368810018103208000303c640a141b011111400b550f100e16009028107103c400564a411884080590b40d010100c1c3d4803010319800340c0c0d80c40e421403950b40e41c8000d4071010300b040304418041d9a9502c100c20103c000b43c9108200307882d00f020b07a52518884c054200c4182e002c040070b00313a00520410481d504c030341d2040300c01e0b5140020400c4a41100d840c84519002401c4d644851aa07004a00016269000030384101806410900c40540a46074414041d44101c500d50140c04030f00e642d501005100d00440c0200032208291030080d01d01041d59010914013000c91038210f50702d9006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 163480602 1250 163479352 163479367
    0x71505010617010e0f160e09090c0a08070806130c150e0a06020a022808030d142401110c0a08071706040b01030b19050f0a050c0c031e04030b010b 64
    0x1105654013500030b284038420b40703080c49500703c0080c40c1d0007049500405180d81c903800503240100307082c110710340c4000e028200510301040210340b14100c2d513a00c0c0380103480403400402c69200105440b403d66003a03100a01056490300c0000785d4542d50f006003911030300e4800c100481d52103800d5414075220511a110b403411030742140240a00c41c00b10394851000c641013403410724016a203004030f4a55400802040d1030b02401d2110003581a040144e102c99414440001c20340b1842d005600701c1302c0404840c8074900f4642d0344280c40803443d008001020036000041c001d10745800e600070091005074042113405c484a80c04c100002c41c40c000c4003170f04040f0240d40301420800418400c040d03c043c0d260181009070101e170030a40c1d902c0c0c003101018000144203415220020315400c910880e08074806018101c107018504001d103448070034440540304128a00d04000005081121010868080303849110042d440c1c07058680307550803550f40030b04581050f01810400000880c010752034250181011007243c0b41d13103445 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 163481852 1250 163480602 163480637
    0xc140d06240906090602070b2101060c11090601053c09030c030109030c02063103050613020102120c0309030f03131208030a020a1b03110d080903040b0715050106 71
    0x46a41c800010000013000074450181d000c10a601110199150309455a90b49a411009004089104c600c0540048000124561f20000d29007249009013584800c0801c80700901401580480d0164040780b030812034150826a4a21204030700d1560350802c50301b4429050368040c0c20078031034000782c03201d0f81c01107003031201e41c501445240000b03407003100200588907050390040c0c0300583c01300c0c02034890301004c5100081580d60140f90003130481220344080b40c2131000250120240c459010a5403203110b5540010141060355114840c1150160000e21101c1e01c200501c2c0341c91f601c10824403040d4081030007030303031083d84040080c16080c0c82018051030711040ca01c29121420a1160701c00e40d5010121120b031004074000e04200c0360410400b00740503035180c8030542c00340c40944030008800084606c500c01f810525612007040c0d201e24244000fa0390140070039650440318000c0550300d171a00364108110404c2110420b900401d81d00b4400c5510b4841c1405a140d03000c01c0310000d0f40301c3c2c008190b2200d00c0d0300c0c0c0c428 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 163483102 1250 163481852 163481867
    0x51606020f0106050f0d1a0a0f051e0f06010e03070e0a05090a1703150d0f0506060102010e1c0e030a0b0f01150c150e07080106090b040c140d0624 64
    0xc0244000f08896441c141c00662020040b1060364003507007440110000784005000101d211240c03004c0001164103100c1711483c004c201b0f1041c0c48002a1a00300420808801072200d00704420214990110710746034035440c03c1d09100060560350501c41550809080e54506014541c01072000c0d1a40029900c3e0001d02c040c1600d0f0010321800060b000140d54800050503406141c48041c004190a5120b036140d0500c02c4c1c0060554030b0441e4000e1910440c00300f0080b03000035540010f0301c220240c41054403142d00581c00d076400c4040382c0c2040d821100c440203075000198080d05150344031380b5000504010941c08a41030190000007524140440030402107452640440a801890703e00c51003c20400f040078024402c03880008010071100ca8100404d9000300d054020411540c10301c41074942440d5908451070007070045118080c40c650030716000f18624a0036118020010790140c0b110701490782071001310051030344518161448980d4400000c6800c282412214100c0c03c041544030a03401ea49020141584 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 163484352 1250 163483102 163483123
    0x30f0109090b010b0a020c0d080a0f020d140306041b110706093021080606090d02090702100204030c060e0a0303020c060c0a0b0a06061101180b0405030705160602 71
    0x14202070005000070381140c01e09044400d82c1001c1d80c1ca501200d0401c90500042d00d40c8282d21a04d200000814000700500a124850f06500c0c0c24400100c041d100360303150411102600c02007481100c00201d0640144000c50f40544014800a0101d040e0076281c0000b00c8200b6400c070001340300c4112140c0300b000401026001d4070003030a22661080c98500c81c4000305056840a81c1c0c1500340a41204503104a00b154000c6a680245e03034400610f0240b4882801d10740500f080000102c001021499604010084460260f00030307001007402c4c03440d9028401c4200d0081e00044c114070a03c0510079a160103171002d00b0181d44111800e520152600c0001856444950100ba10409809008000090b00000d01803004203040e03031800e413039030301d02c00311141004070b5110041c0c100c0e4410030404c080c04005038004401d9403825140e502d122407104e130f4030f40d00720780d05618140d0700301c0100704015001c0390342403040d103511610500031203180038440c1c0d54160521088000b091100c24090209014a90f018072001142 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 163485602 1250 163484352 163484369
    0x204030c031e0b060f1c0303050901141003030309021309080913020306010c1e0c08070816080304261506090a0b03070b090607080a0504080d090305060612190602030f01 74
    0x40b1003203501d0304034814501420052080300810400005a00c0d41d0b0200601c0c88904040c22012000ca800e01501800040b90b0350000c81d464090800e039186400030815008030302c0b18200044490031a542036004092640c8207a03485280000c031090000f13628052100140d2281c620075490f80400024407211107510035410043c2401842005000d036406407144649981100320f40c0c0740050540407c1c50b010000c2e20001d000c8841c603110100710204006059000c0b2035002c2d045130328103c81d4990048a044079030188041c0764100300410071003c822082944090b22142e0900d076520001001c45900d440c1c000c1d5020394100e0004020480b0919040031584d50140e00e14400340002040c2c0c1c0b002a0f211111400b9028031014081000e41031034441b441a80c0e44c09501c44401a510350351054050090340052144080500c540003440302494031500c5860210395212005000d1038440b001002400074044481c01407621407500381c41700c140c1d0f4030314850542602a4000598034180134038001d1074002e050700003814 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 163486852 1250 163485602 163485653
    0x1080705090d020f0402070f0c05010206100b0d0f020c0f0c0a0803120405030903030301081e030703090b0306041131080706080414010911041d06070c0f060204030c03 73
    0x28180d0410221000004120380508070000c103840001c2010a02c0e0010a401c588042190800c10621442001c070560041c1424089141d9078401203aa440045804224101041d031041000d4210540a0080145001f1000c1030001c103007002d0303001b02e03008200d00d0fa400d58040e00d0101c14148092101a05c0c22009990003914203043c07001c460b9683c0b03c3d04407030a80000344580001c003841400d00940381c52150040c2a01e0396540d6038007181e42e541100c49000340702c2c4410800c5641e41030340c0c00002c070361340300d0b038551605036051b03152001000d4142c00062065400c16111070502070b00300310340c40007403c2c80048001c1da0591080c5500300b2624605c9041015040e218840609000300b800008140007141d007a407600903020390302c41c038001d440110341c1e2a242000350300303041c0403404001c0290000045510260340c2000440402511281d803503a1b1140c0c0070326560440008039402d20b108a60b041d1059010300340c0c2040d641d00039a07030305d0106c2c0d0007030b070043d650b480000708240b082110514803000080b81102d003910 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 163488102 1250 163486852 163486861
    0x12090c03060f0a05250e040204050402030109020a140304020d0f050c03010f0e07230405040201050c06010603090201030b040903080f07090e09031b030301081513050f010c0806040621060209060a020703030e0108 92
    0xf009051400c0360024031a034441a0707081b0f565150102c030003814000c0c00a64072560b50b01c0495010390807048501001c903103008604144585c2e070f4005d0320b2080e03030020801903d0501940781d125044502d03040c02e5a560041da0b41c10700c41e0f92401d006088014a024030001461402c0441140c2080f00540002d0340d1a01c04107015405440e6001c25145070b038408490011b202e85442c8016209031049000c4400c80d405031500005440d90194480207440d8003c1e2410700042c009542000704079941032100401103803503603001c0f690181902142c40d43c8050b0074180315000c00d803a0f050540d00180100c0320500035510000f000442d1140b50b8a8050320421000011429941840da6181d1904103070400c042409400c1c00c0018103502c200740c4102d900c150801c081e20094115699640d018104403042c40d004600c01d0000301d4407506040c411502140c01e40e542e010340c001c2080c2460b00d104560210143c1d0182d40a00c10b000b100d542d800c0041846c0400c540040c44035900d075150140013160a800c819041c41805020003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 163489208 1106 163488102 163488151
    0x302010e0a0e16120906090c0e09030f0703020712150b1002070e190e0f0706051810211a0d02010512090c03060f0a05 52
    0x440d5030803031140510076003000500c1841d03155903450b4006848041200c0c00c02d072580d002031800018100c05440c2d90800e40366808000d9654030f6a84090804100138258031000410500303c42800600d01050390540b40c2c005c601c4170540081f80006c1110415100f84650b001030903520120b141903400d40c1c1452070303110311000c036a880302c00d1521044a21a203420803800b5400300e5668010310805050030107000001101034054000c074949544076003101c12860041503c940c40e504020039054000008842c0703403a034540d1050003400810024001c020442c0c40c160301030b00f20706031011000d8011340352046a1880841228000c48520400da4441c100c1d4160400c0d001240312848071150300b55213004009902c0c08000d0001d000c0380c010042c82e0b00080b4050050350b8004001400d0f40e00400c1c140002c00c4c1407100840c1c4c0461f15a0b405800c0150842e014410381c0e1308904200c4038400301c02c1540644 = true := by decide +kernel

theorem cover : BRFrame.Cov 163309352 163489208 := by
  have h0 := BRFrame.cov_init 163309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 163309352 ≤ n) (h2 : n < 163489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
