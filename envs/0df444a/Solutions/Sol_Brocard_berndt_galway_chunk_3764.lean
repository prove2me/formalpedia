-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3764
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:36:13.175556+00:00
-- url     : https://prove2.me/submissions/8651a488-1c50-42d1-8d41-10e76e18a410

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 676798561 ≤ n < 676978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 676799811 1250 676798561 676798567
    0x180302060711030f0702040209061201030f0c090b280b030a1a12030a03051b070c060807021204120303021e09030d03051608040512072609092406 64
    0x406800140150041e0042d0301e0303500b4000e1140e1225656131041e40c2418045481c140014001030a164002d0718007a00000d11660500700440d00c04001003400341c0c000c4d00d000703800760611024442d0f0068084084c2c0070780803017409604001c2c80414034808001c0345010000340c205d040c2a200c2810b9000c14000791601c01a516620304003415510701510325007000140c1d004001002c6482031901440701d0f00d90091400146051924808051307000b02030040c9082c420890b98800c1e0200e000e00d5000811880344524010180182000b500400c01a8010000001c0d50312000d12060001000000e44040301c9840c21004581091445e04034041c0c01008403042807205143c440000d294815009000e40c1e690550484d032111080e42812001c2c0c4800761049031148c102081d1840215200f40c500030b5209004608440700900b4001100742d00e940111010303500307030403005041c40c4151a02c1d88000030b0007600021841c1400030344d40c00070b0341c0c15030082d00c01c4481003c4800b10100c400045880d02540f060001d240d00c0d2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 676801061 1250 676799811 676799813
    0x1170103030f0c0204150b22080a0b1e09010e0706020c06120405100c022b05090f0102070308030709080f032b0b060d050a0b0a0b040504020d02190f0f05070314030a18 73
    0x4023a0008103000340c09111681c00f00c0042c50300700c0c1c01b240449045500030094551241c4800c0400708020780309090b0005918410303110980500c85003400790300341000025441102442103810481960001002c40d0407000c9200c1d481c0c2c0c2d0b010140c03174400300d10041000441c0c032240f4000345000302200b580394015041c0441030240c0340d000710b0390310315803205110141c803048012251075410400600802d0301089040c0880c1c0d22504041c80e803905c5000041c011030341059100d07101c250703140c0c004a40308030010320700b0700f0203000110703082c0100980e409960b401141403c0c03000c201028066040780303101d198804500300000094816400c011042e60300501003d070b65005906c2c0303104c00b901c400c65903e101c05045c541c0b4500f81d4204054250704a400c8409441d04240c140801c000c00b941c055881c49003282c0d001e20103001d200003c1035100a0044440d00d6260340350801160180003449100034440c2404001d1060001080d0050f500c500b18010810846980f6a40c45469a0040c0000d070700e03401d0307060070758648c002c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 676802311 1250 676801061 676801079
    0x7150e041b05090117150a080303060a031e0203060c04090f1a040b032b0306060c050705010e01020c040e0a170f120c0408240108011104050621070e01170103030f0c020415 75
    0x100c5046c07040c0e404017800f580702d5007038aa1741d10054505542049072148108081229071100e20108804c0c0d10307003006000810b800103490b050303041d2200d101c0140000783c200003110351885040c800340c0398850184600804248116607074a02c0714060b6001c1c0fa15410b80c0780341e55805011400d900f02035020400d000c60304200e10305044580440180012030314204c1c2c049281c50184000207022507101c80100826414440112100050300310700c00d05500c07400d90780c04619070341d0303005440d1410368460042900b44107038141101d180c00880103a1170b0b0b00004000c81502c598032035003161035802c01034000007080d40351a07990002500c180d41c01315680d409035400c00031050020000c40d8401c20000c0e217800320140d882d4201036080783c010100c2c5492494082004000714101400504038640c091108540403034100e03440400300c1300d0105c4041c2c0c0086e4485c00e0440c1c456801040521a1101c01004041780390704540d406401c10b0403559288041c400190b142e00115915500010828005003a000000c9591000d0131 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 676803561 1250 676802311 676802341
    0x5070e090706112a03010905100b0f090a0b0a120b04020a0b0306010917030d020408030c01050a090b070c020424050a05060c0601060507050f07150e041b05090117 71
    0x111000c0c000c844000649a00c215080c11150000b080680030002c608440d201044241940d074038041a031194402140317030750138810080803500800181500b0401400c44204070740010488521607000e00740a5583ca80f10918071079400701040000041c200003000000d0f2111400350f10036003d81818810300803c1100c8a24014081c0c3d00c00d641c0c3c2c88900d0340303a003680c0110b800200c542ca0300003601c0803020001c04401c2e091294280c2c08000650785041580885017041c0c4c0d10a400c40c8045901c00904250154070034440c11b540601c0100c0108078012269582c010711501c0034100c00100301d0400340c96000d65596607c2844d890341110b00c038030740b9416901c51401908045120300307807103220110380c0005c0360305000007244c00e07080c2085c0241c00c49a007042c20540c2c0c55000b1070b8085e1201e1203110145401c81c0700c10842c0c680900f03111f241d10303500c001030750f1001410001030b210709078082c41c204a0640a001c000c1c10b0600b441510605003076456660700401202c2e8a0020982e20110610490910814081001d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 676804811 1250 676803561 676803571
    0x206130804033309121b02090901020406080a1a04052701051e130f0f08040b090907111c050d060e0106020d110d050307210c02010e12040315020705070e 67
    0x40ca1201401c1e0344440c3d003152410348001c5c2609031056503100d0080c0c07086080d029603001034880070303101c43e5160b008541003241c1119402140e81d4005400d2010a4101c040c013a80310205240030702c960103080c0c000d42c000b000c00b00340050085846202149031800040c010900f640018401c1c00000d80d09010381754041c1c60140c404807500700604844800002f4002620f034890203030706003020208a41e9955241c9200025803095030700386001c04641d80010921001403006242e60a42580c54000c5a002c018104001805580a00c02200000c0051000c0815582942d1110444010f1a6113071294107551500c100300700f803c06da070f2501c8030100c9d60800018066041e00c2d4544c0c01c5a90103140d100040d200e0791401e41d415415540070309607040c03400d8170400c000c540c0041285054468501c10b42d1211840c6180851241c2031282c0b900c048000c8a642403140c2c0d4510302400d4010018542c0d0380c5859091032240d4080030300750001131442c00c940c010307050f0111401207912100326140d031a55840d44074844c04007610 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 676806061 1250 676804811 676804883
    0xa06081b04060f0509010308030402032a030c100f031d07121203091a04020616050109120801150305060d05030403051b04020405062a0d020a1a07020613080403 70
    0x1c0202c1c610207640b03428020703104003510541707082e4210b490700c1e1f5503504010000c9038540300b000709880c40041102042124500c01804403454a264881058240ba005611050044c5020b00c041c2d41115400400110130a0041c1400500002220100b00d5502c1d469504203485226014000490001652544100310300800007503200b541220f0080301130700c40c102d202510025448080c0f8024405004000c1e0b0800c0c8000c18452a02d054145140342e04440484103880f141d41d59a0a00240b0401c6000c09074410a1450201c3d0298100f652280f82480c51618a1042564910000b483c1d40c85004e40904521f03008411039840e50359078500182c2d20000b030007904020488800b00000039003070500a503000e8910007000503091030084c44601000d000719611aa62551641062035610003080c031092448601d6a805400c09600d541410655800040710b4001c6600144040045195001c21502e800a0076403165119841107070815002c01d02650700003604000c9140d1400035813540100d901105001900 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 676807311 1250 676806061 676806071
    0x3041b08030f120a050714220b0a1704020102191e0503030601020708010902010806010f0e093309150a090f0906180f02120106091a0406080a0c0e0a06081b04 69
    0x10784e11406030741d015581c002c0030410401d1030200d00d040c500e000c0d0650002d140a9601d00f174600508803440382c4080e030b020092440002a4030000f00d0390041411008800c20800480c060400da80000c0d55020b00c5100d00c2d05100035a504001000444419180802c0c2d154040f00c204c0c03400ca00b00340d0346946c01038950070f002d031103144c1002410403010700400d60130365016100c200c816981d600c019202801c6a5801004100d040d80104050f65070f280e00c92030080403843c2d000e44960f00c00713030354000c2a01000e0309070351502c0007000c40082d4643c1c1c49054865010041c0b4000140d5800200c0c04101454840e0b0000c240762800c2c00441d4201c00900c0d84481c000364010f400600c00102e800d200001362280382207018160f119200c0141015042005009a24094820000880756510f03c0380d0310441d49000d00c0000c4420190a000c89689000e00842016003c00000340003c13112950b00c603103111035613200d000780024407900050100c80150f48850002d041140c1a140e000800e5991801da030131001440c0b43c4914a00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 676808561 1250 676807311 676807321
    0x2130c0f0906020a1b05100809192f10020606030606012f030f04420c03020a170d05010e0702030a0c0609050a0c0807081203041b08030f12 61
    0x9030481c1000c441c0d85401501003050389881c0c030020403c8500d82c840c14546504400112511121036800c2100c0d02c50351400e185050500c40c0342e08251080c0c0c508003c0400011024011810810900701000805003000c4001d81c040d249464400c80804c00a40d80320203483e055080007078002c80c42c2413003440700714251403259498100648180201428208080501c2451102500356512548140c1d0900030304485c24809560f0300c141056019070032121507030b40c41285992268005c0703440c69980c003010b907a001100407600101c43e01c642c000610080100b040d0241038405060080c00a0804150400c40308111001c2ca00b41d161b4943e4004c0508140e8075190900001e40c141e85400c8583c003810340c590166242c00f04081040b41c1c3c030a00e0650980d504c642c3c4018410000e8000c008414a8a10030795960049c1854100103900340311315030707008980c1900240200b05140440d941120b0340141c0c481001048081802d160a001c0c2406404c000e0701c511002502c1c00e04040c02c44003030240304c040d0400c1200e0640d11 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 676809811 1250 676808561 676808567
    0x803040309120b0a0c020a0b01090c080903040509041205070506010608090c01031401050d0c090606110f120d0f0213030b160c020f010c03140a0906030b061c1802130c0f 74
    0x8200d0180c0f19070715560104200349410b81103601c001d091441110702a100da40c44500b512242070388415041a43d07810a03943c12034100c401146d201690030701540c01c10789420042595400e00410080401e00c0602c8a200d1250186094401c983e030000212501982c640e03501030100c16090358032801511610082081c158424003070340402200340c0403054816403804044c0a12002522401c0741c014524901c0441c0c401d40300d100f4180103240c15602c0380d09190f64183e1460030102c0c1d004007803440303400070003045c01082080012550300901e00000051041000300e40d810080c042d0300c983c1c0d000c02d40d07010030010511941803011800f5040f840e840040603204440300b61101781c82c0702d10013504448121a42e072a2580519080704004c4e000782440000321680c0d0410162950010720120302240c0850820700c180c0e6414820f14424542c1034904a25240109079032445480ca41250354480d143c880042c0d80000c0072014404c072006e5800b0705400c24012046103c2d401924904283c0b10006594403d54482644 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 676811061 1250 676809811 676809839
    0xc0e19090507180b130b18010e060f0604050d06060f0f080715050c060103030207061403060f0409030201020c07030c05330a03060e010803130e070e011107030b040803040309 76
    0x1034044010003140f890214644104600d007140100c103203544a01084081e2650240f406401d80c14a03000110b0610142c1040342e07828a8820030300c6205642030061000407424803440d9089141250411600700034000020344505c2143c001d0f44e004000c1e0313070540d4100301e1140c00c20015500d4070311500110940b940803034143c503074052007541480d501c051000c101c00d00d40815112001001071030424581a8020f545a1505c9401e0b401240180c4c4050801c000c0703143e008000c1028900030b4014985507081c800c00203040c00c400071480c540706a41e01c91043c01098001d50480384003120140a41c1c800320f54a040042a0004038483c1c1c50003886080d0b40c0e880d01d1030300105042d02000203148117890401c5090000b007100e400640c00e201c10305d69a19400300d00d40c005018000e0091580354001c641d5280705c001c442e0100305c416441031031104036550078403a07681e0304240301040c1d40f0300a10782106004040310100746841c50a80c406401c07200d82c0c109010600c58107100861060b0302940300e80d044640c0d00c21600c6a185 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 676812311 1250 676811061 676811063
    0x30c1c0c030e0a030203012a26091606020f0c03030403020a0e041e0b09190321141807081f0c0c050111030603151b03090a0c0e1909 58
    0x259400c510000281c0540e841001d20071002c2e007105005600c9034086800c44800184509100e08041120001203100029042c401040c618000e074882c02241190201c1484aa40f045618030400c1c0010344041810450358400b2404041c103038994607640c0101a454039101c6481c10340324080d070f40d065862800c0000c2103900316607014044403aa545004413101e0010006441114021910310703580000d10140d2041c814414044c00e035200b000e0411a8102d40790405500000c49070007100c0180300c0110ba04508080e40c01008001d40602c80104403000f14010308041011211000c0144180508100d520581c1c4110483c130404440d00d582e142d07000b5a135288080b140c500307880f0703c01c6102403103804410b03000101c0848507420074a008501035038171035007540e0000340e018038015008002c104103403808020880c4902c1c0011214035407410901c40801440c1c040c03400920740b0090000200711171010420810000d10b030010010181c0e540c94941c1091005c000b82c0b18140300041c26080138000e6002881031884403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 676813561 1250 676812311 676812317
    0xb21072102040b0a0e150c030a081510031e06030c05040509030c03071211030703031506030b0f04020c070b0a0804030906090b2704020c010506092508090a06020a02030c1c 75
    0x41c1314110445101d220284070603001240144000c00c000d220001802d216448100615200c0000120041070440c00a00344d00c3c2205004090b0131403911280f24120307000c02c0e40c0c5000b24000c0c19050120701c40741c0d49560b5071012140340404c00030a010720104004196982103030248119141c60702c0c600d9480c040c10464504941041140704000303000303171030290000901c40c100403480766000c1d041c5608540008a068004c20f8a84900d010f105056100107400703082c043c05c08001841c0b8200100d28100103220009000340c0c0c5c0060700d40c1c0707164070421010004210594980e42d44a8140d03200400d074110170750741140804c1d44910081200e0f0300440010080da00d4801d078590504a91f80c11804102172403030020754008280e81001292911240020075225011000210b0a401c050342031200d03599006142c1000c070007440c1c08003001c0d2514021a191045c10768901244261030f12080a414110b4040e401040548001282048950040b001e051100d00ca1010395203010403034450315151840c000700003800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 676814811 1250 676813561 676813567
    0x4020301081e0709141006050412111206071d090402010c02040207031e0c111009050904060b040c0e01170106320d090c06050c070b21072102040b 64
    0x10b589080807081c02000c07140855041590300c600c0b5200f01c40941071034241c156513407070411141c011050920002042145400351402c2d2821200503542d0b141d07640e0041c00383c0c900e4000c000c910350701c08142414041d0f050b815100035040954010b003283c1780210418880e10480700c0c07041d103076190500d0307078511564068503640383d1240d0380e500b000001d5210240413810700584046180e0b420891440c440c3c0c1d0380301c032a1a84940c1b280307181014100c290102c0c07002031050310b000418040503a4048920000c440003a40c003606561510300d040030180c252010803036002403a040519104942c004108142c45000b83c0703811240900400c04400100c0302401840085461a480400c00d042013109820400a051099188903440e411165669511888001440703035160006802480ba116802c58014003050074160301d80b00300d8908860319007915200c1e81e07406a40c0030030b805810069000001c154403610580101d4103142010340640b22820711040402503455004070328648020780c1c800c880503520040722340c0f41 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 676816061 1250 676814811 676814833
    0x918010f12170318161a0405240c011509050c0a0e120705030715030b01021c03181506030308150d121709031207030b091902090d200402030108 63
    0x8075034000340512822600313100440d6400c0d00c040c030228108030501c800380c41140b842e1404d41444017110ba05040c0c140390040008001955400001100b90800740d03e403401c02001c1902c20900a01032994121601e508000781e4401200a0034055800d03140030f56001c00040c0c88182c40203c0c10702880200c0c1020070f1502c800000d40b480d0161401a0308426082201c0e1065221000300f41800c21640c8022001908003005d80541c80d01030041c291f0b610800e01c011301c0d030705840040050444d2826140c1d08241507941910301c10000700710080b0404142c0091b1848500000c0c68010380c001c100740d00c000d074006102140401c0d00c141c3d1707640f86d02c080c80c0300081825840700555100d0608908e11145d981003440309281203030b060b0ac81c00d1740515110740610009581c07a44d0301810f040c008020002c0183c800c0610f491303001051650f48440440e0405034202d07642a00600314a100b00081c82000a456813080c00144201e08118002900d030422174548000a1601c03440300c02840240c0c002070081080940120020034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 676817311 1250 676816061 676816103
    0x132030c1908030d090605010501020d0c030c05120a0e040e061009021312050a0b0601021c0e030c03100608010609050412050d0f0218010f2c03030918010f12 69
    0x41d1000d110806241c140d07107a800e40e142da445101060081a11182c503401404030034400c00b40186001c0c00540f40300745044200810300c03007008800409000454410358103010040101080040f1301c020344603560780c40341d0005080d2590707011000b0701c19800c00280c0540700c0404200d00b401206c9418000382d40e141400d401c000a9000a558102d0317104c023082e130002e242d915014a003200507000340090404100c903130030300e09a0b00c3c6004040c281503510284418660300c00d40003540640400305e14281c1c07900c25010000a08080d0103003041d5a15105145051910302459803210007215001c00007041195074480d800002d4840444029160042c40c4207078444c0c5901490040c04501c4140100084d01403100c00550120b8000c940e0064403051710250000055801141c840c1c440b184505181d098450301803001240f864a80c0b5101c5017006000b0803158107034400b00162a140000104015004c00d0b65070400041d1754400d1280e42e0462980c200001001c0c2680814030009540000c0058000f441184d20a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 676818561 1250 676817311 676817329
    0x1b030607050c160306020c0601150e0d0203011b030f06060c050a1217090a020405070302070b0619030b0a020d060b04030c1203050c150417160209130b0132030c 70
    0x140a03030b006402450150f03054460415024601c200700050325062644621031606005800081110040c0c3c0442c4821540000b10743c6080001103620810640451010a016021084108400540c0c444180380000e4042d04a05e175019400201009802c4d0381344002c840b4880845405043c54101d0b003070fa180418241100b16020a6841c00c0c400b051406006804410007400c03683c5003516048800c3e15421803402e40540c0750042517600e020360800145850b03c55401d54040c0038580f1840f540f47d2480b1194000d500da0b1001142c01c101060080d1030040440c0d030296020358a22181d040c90310001007001d20f15417050382d051340c0c1c01c0740d808450799080c00000103501c041c1000a5041c010700b80060416120100a405000c90100384941482e0a040c90b041c0290194104d10804480e410f02141026083d48002d06032050b80403544100551201d00c2c4003a000186000050903c801c48000846e40b8002c4d030001c0e16031990300614040807569403401c9400ea0012004480d41d0640000c0070307000d8907281001c01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 676819811 1250 676818561 676818577
    0x2502070f0308071e030309030206070e013c08010920040b0901021f0b0301050106031109040b0d0614090c0405240411040609230a05060f04030c03030c051b03060705 72
    0x2240a0507000703440740d0039070b51300b000310300700d00207030301c45580b00c040540c14490250040402d06210345000f2521001038603040c4500036010241c47c0da0201a2500043c0c0b0a0030340a0307640c1c1002c0c40341848148100180103903024022034031960b05001c0a10a9980007056074140b425228882c20308060400701c000c0c034944e1000384800d0443c403801101c031603c9007090b2800c601c0c3c68003150b00000d17064402c40504d401d580341640000b051600e09041c1d0159010140b00301c41c5640402c0b40c2c0000c61048540000301000074040c00605618070700340d000301e11600c4e8019124003031482e103811101704134003840030402030b40c0040310f01d40c1e41d0700c50350400301448107484e50502071142ca0050021403400d40f075016005150708150b002800058107400c0400800041060502e81607950a014800001190001c2030b12440c40e44030700c5000340c00c0051035484881c3c0d200c00b0769010b15409000307640c0f0b0030340ea03080c0140458401d078001e03074003070203821940c4038583c009018031080303003101401424080c2d540d0f000640c4c582d000065 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 676821061 1250 676819811 676819823
    0x3030f1503100c0e090103021309030c080f03271911030d03020306040c0c02030606061c0f090b0906270304030b010e091e0312060f06032502070f030807 67
    0x3a040c40150703401e00a040350030310405030004804015500003819900c48052041c02a401540144050303200c80b10780052040310701c1e601249a40c0240b8007180c007030f4800e4201601c80b0b1000720719060b40d00780c0b0900560182f10300c40b8400310303802c08044808030014805503542440d507224419150340b180c0c809046050f102c3c001c2400d25080f18040d07011030b051614003071104000a500100f0008589000d00c5030f0388940040d4500392040f1301995000c20f640307480160059120320f1010510b1070000310790030522280e0000d554400c0c004124124001030103003003900b008594400325000024816480000c9161182450307012002c800741385a4203d4035031403010f145190310b9010410000c0041020500c1c25402404042410b030703140d10380000324030b040003111020100c3c190b100f51211119004000250703140a0100318061626031180350006482c0c0700e4890303001d50842e40110401c200d00280407294108115445640082d564819804a80b00c0d9085e001e0800000c03507891062000c0f442910250201cbc41c4110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 676822311 1250 676821061 676821091
    0x7321206062d1210051e03031c020708070804180b100806190e0105090903071208060307030c0806060a08010510180905011407140a0905062101171b0303030f 69
    0x1042c111050481140c4e402c0114500702e604100030309005502001780c0c400c03007042c058102d21400000c0e0b1284102950070580a00000d0020761180040d811074a0003507200b60083da68080b41e10346003013190003a11030301c03244c000e400043c0b0030740b25418015586041c200409040340f6440e1280305440e4824094a803942086d402020b8900c42507140d0b03a400040d2004940c1d42d000c640c588010072034416001880c0e0041074000388064400520688105100c06881d810442d18650b0780d8004070f460b01406500280060105c03000010310031801003a0b0385e0182e00c044d500000c102c0e885108060a8641c00e9940c034484e07404e003e00400001e50301802100400c0180f16001c5200704140d00e4882c20b4442004607425115403000903c00c03030f20f4204000103422180c0600403403c0c05e0a04030050083d800750b2284034010000080c00841030300300c0401030042c65508a0044065513192204620342d51401041203000b4030038403540d04440500c010740181c4074030004004510f90380c0c1300504004410030180005d4050140304c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 676823561 1250 676822311 676822327
    0x11e060c0501150f080c03030a054005040b0a050906040b060f0307081e07091701091401050a0e01020705070501181203030209090f04020907321206062d 67
    0x36003440d0000c01104c80461559410183d1090801c2c00d940c2c03210b0700ca503000b00302e01e0604680280a03150342e02018407000e2182038644215580c40e109051383c000c00286103a07420b0a402a003402c5000503184c09840410007000007009001080a550041e540e01064036000604a46407503004a00780d040c0141c0020b003000d0080c200e88120750400e0302d2582c0890501780812502c24003403801d40c2c0101c09008401aa00c3c18641c5014104003400d000300844420311180d001900c010135002160703540e60000080703551050441c080790080c40181c405e0922181002c401d0f50381d9000500035110300d160003902400c402460000103482150001a1031007507083c070141c00103031441048003010b0189001c5e4402683d2442d42204001101000601ca030488820480500000d80c54064190341c1c44002030420642025003850490342000100740303010003076101083c001e0000d68810010b0035a042102c1d1400306a52169406c0007501d0189c00314500105c002c0030128210101c40b40488802c504903a01881e29040310 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 676824811 1250 676823561 676823591
    0x6052e03110f012001152309010b0f03270d1107030519030e0a0602030a090504020a051611040c020a0c090605030a0602090d1e0b07050c0307060905150403020d0305011e060c0501 78
    0x413030f8407031f00070710300010412040c4511082d02045d1400d411184104590304043c1e031078605000314086020012400310001d8907040c00034101c082d205421149046c25014020742c0c09688040d54442c040005540d011443c00707a0070001801e0090700c0d80701016103d9406111b1803503103861091b507410f03000c10080480f80e1510380c40340ca5500001c0e10080c1c1c090b5507182c0030000003500342001548910700a41c41013020780c00030760313100c0f0913200302200001202c11815101e041096504076050a0154020f03c2c102007003012940004440405c28070500103824a681d640b9000c1084520a01c103803030f00b580010120384009121503008140c1180c2c000d02c8401d08c04442c1d280c400b030701890703809800440841d1021280030701120340d504d01c3d40103483d441c265180c6803400b008280c1b40d0068041c01080181c6408420003040414403a10340b0400c0c15102e11009441c2a040007540d4031200c40d000f42c0420300d4000003180c003c060105c003903000240e141c403070694903240c503804960080d503200007601c15540c2c1d00400c0b00300c01d0b1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 676826061 1250 676824811 676824851
    0x91e0b041e111207051e040501300e0102070b0a0e190c03060606120b2b05030c01020706051905040809060d0f110901090902030f010306052e03110f012001 68
    0x41e40e50b00e85c841013a112480c035500c44403000401c040c0700507c800c0100d60b03480030400c21400b060310000c0074850f002c0302008204180b034661550302d0314140809e03240034642c15809404090b02801200559844002c20f81d4111520f5004980980e0400816109004a50500c61083d68425410342516680c1c0740c445004440c0b00f6003000700001d5100d5040c2428518030300030200c580170212601030440c03014103055862428641000400d04d06c25252070020310009109541101c61008000d41d0b50f1a42480c0517401003c0031540e880350854540040307a0581d06074421142301300d600070b000d1450401c110081080681001d03420002a903215800041a012741c3e02815001820b20481640c6402e40c2d080058561100b94001454140c03041c8108500c08010f9a189030450340c0242c000543c6031508d4020007188402180741d4010049078568425864004080100469000b601b4400100001004006007842002da082d80007592913482030103a079140783d04aa03071a54002000041c044820042094801 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 676827311 1250 676826061 676826071
    0x9011412010312030c02060106111203040803180307081602040605040c09060206180c0d0201360b070807032d02011d0a120c0c091e0b041e1112 63
    0x80c03108001001003000c424035091041d407a9041c01d001658802d040255680c005105140410140d1491215401c40a12030002c074031000700021aa03900d010b040000050b4000c0d12644007400098841a040c44000b0041e91800b60b40803000602d042c8010841321030040000348103a80c03242d5a00030014150740c42384508444c0400c1c94846103404c1d45003940c0a070400c01c004000300180702104a55440440002c2510703000240100c83d040d0b007080417400100e0704804511103941c008400000b1502001600a40034103010700300400b8460320b241c80e42002e82d481d0040c003400400d1442c00303000c0c090002c0d00542c5801d00c54600c203e505407901032205140781e80030181c064480c000d030355140030711820304400842503030305000e2030402421540b000e0355031000340c1ca032070204a5040220200590003045080180709000305903411003880a103034003e104501c031803205440f98201502e40811807003142414000d0f5400e661410043c8404002e40c0b8110314050950468840c1e0f0390b13203007044203121012142c00740a0040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 676828561 1250 676827311 676827337
    0x703051501031a190b0301121209031e02040b040f021308010605030307080c100c0f02010c0c0209062e03060e010b0301030f3302090f24090114 63
    0x182080c140d81045040c080020030304040c10000e20141203e80c2e030342100c89800b826221940c000f10781401500c00103803290051204e0381c1c0004000205100c03030041c48005640141c42e41d039002c040b521804d441458091100802c034034115812790140780c1441150149080c005070002c00c4580700c040c00036044030b40345400c1820aa40c0441c49424140411a54502070441c1e50000c010480c01c2200280d035034000c20754010414440090800d084500a000c082d1409d1013404080c130032010440f10140a41d0086004c0c1c4006600e0000c40c46041d51280381d040c150381b074010b03145040c42d48482007030007824806001e2184c0d16541860700e014900c00124214000888551b40c00120b59041109101980406a122407980003040c0014000701d42c02e6068915111390000c00c2042106002ca03d04100100804e20a0075410b460030850501151355001420618402c4494801c14581c010400410103180d95200840c40d40c10340860b0320051441d03005110130041410300311013580d0070220364400c5910049025500b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 676829811 1250 676828561 676828571
    0x82802030601230d0e0304050a1202031905030d24030201050c01060803040b03100e090c0409231516020c0f0409140c1c03020309010c0c080304090213080a0206031f050402030703 78
    0x108000b41c4140e0550400503170286291928010009201007024040e00c6218030703440c0082811541c04010700caa01040d00c072040c01d08128541425526074000f47e0704021200d08000c1e5078082402401100c06508100c010103083c8a0b056400442d0b07180c00c035940105181d0750f24a408541c2650030000f4100500e103803d4007580e43c3c0b40c910080c00070705400340e0141014a0100c428040303648404a03001c40310074001d0311f00248024203401c14812440c3c120200b140c001d1000582c2401c0d846c800300341400001403074501c02d40c050725016071003080c0c00c0c0f100c0521401600000c1c1e94001910784404010007001d0002c2000c00c0b840b01e035132100385060300c80034102e003501d038003074542e204050400d581003810f54281c880f00310304d140d08241c4011b5108e215444a0a0400028181b000304021006250101501560084948840c4c03985001002035214000296210840703840000d80002c000403030782e10180e40074052508548552641c202d440000240c00d21846200c500082a0b0b038640f440510301c11035082e81c0100b2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 676831061 1250 676829811 676829827
    0x25060e07080f010617071a070212011d06060f01031a0303040b040609050a0f0b03100b03071713022218030f2303130201050d090b0708280203060123 65
    0x400c690060b4003032101084170750812602c0c190301003060400c940102d810724811414a0340114080d01c03800500a501c003000c02100d24184005500a08142c5e107000b10450340780501482c06a915a421911207034050000790003514954441e42150a490f000c01070300310b4080e806100043c3c04c50700f181e04071041c40d00010508009041c0e00960840040909580780740381f81e4200003500350b031801d16004421900b440000071590316044c20a1060007402080c03d01d03a124100000300400740301400460061041380c18000c90351004070807144407600ba034010001004545e03501005054a03980c010007a0240d59580301c0c0034a51107202403040840c0703100c0c3d81c40055103000c1001c05407000c0003010708a0b544001ca4401d804022103c1710489400c60340302d42190203580c8035840102c90070b10503c082d0003151403c01d25010304005681807140e00031a40e13500d40980943c2d8400050141c200406021410654a00c0c04a50714000c10350043d9003140062401e010300008a1440b401390002040da004e414040000b4612 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 676832311 1250 676831061 676831063
    0x50a091a070302060a0c05090d110a031104143d0806070305090d0c15060306090f030e0907050403120e09100602070815010e07030e100f1125060e07080f 67
    0x4da840325249001b00101090f000c0c00030100d0052540c82d45c02611750382d400c1d0090000d540f90030812000c000304100a01c94507441c100c0218080e5841241c000c03400e20034984803594840d150b0b148244100c403183c8950000f6003a603021103940ca41c040426403031160001c8103035030003080e9014000d070603843c00506e05410801002021101f00401d00070258008107002c041480d40199410350154100307254540c07520161880c0002450309510041082d031400303116608001c0a100d20008250180d02d608182c10402424070003244012601e4a0001d0410041800010310050000c4408182c524040c0e05007902200890b400d00d4060710100481800c10004002c1c2a03410000c52015040f500d002d021907802c2102c0b524a020011f020f004016800320780050003041c4250300a80504e0804070840c3c61050240a10100a00004155019642c00c8c101c80000c404407403400c03220180c03030001c1100d45215011071140011401b20008440300b50301c81300c202c490008200701401c090600c681c090404103103511041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 676833561 1250 676832311 676832323
    0x204060515030907052b080405030a051c0e0603011e0b070305070c150903030311070602040f1823094201030506061002070b18040509060f0601050a091a070302 70
    0x40d80318101d914440c269112003151311203200300100c002c507481240b06e4504806640142e030415500b43c8900700e194418070100247d2001c0001c08641000c15060307080000325000319004440c290004002c02c0100301d100c0c000c0c452910704144001c220a6241e440f0240c0103c103a1083c001a000240302082c06018001940f030950000c141180b08102440c41c1300c171001d81020080d1002400b8165034644400354018001c08940c4070310b91082003190b40c0e80d03c404211400780b0450188002c0341c0c811144448050015100752030840c0807841217160346804130800c03511160002440c00e070b168011400c004000c00016002142403c070f0300c040304402006061403203070310304184080f14010b04d03200400410204201080396034003c0b0003540d0089004002200c00e9103800041d074400384012000103030306c280d0001840c0700600c0c80d5404440a00160701d400c006681d641100351131006c0c403c403070f580120b81c10b980204000c0c405400305051107503c4954075042c00301d80a280090072880740b0b8001070380204040d414001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 676834811 1250 676833561 676833569
    0x40905070c0506061009030c09020a090b0c12071a040506150f0904020103090201090e0106030c0f020d0f05090a0b0304050601031b0e04081b1f060914130204060515030907 75
    0x10100c000500307502c94075519200a003030103009007030130800f240365030b485000c03688065500106181d10860351a11810002c0d400900c0e880001001d00740c1c0401c0c03200900040f03881d512110310040c003000203c0c1004155076485440d0031243d210698680040c544110b0a0031441607000310003404103440c0c00030761001c0008104244a214040044454010b9035034003400c1a04580c0a2038000345600103440181d41e960071540029078546144000010711a0f4075401120200419658446a0311882e902c03e90340c600707641c0f40d1500429422010f8001030b510610152040385d4000f0003600001c1e039661101a038039401500d0039921600184014421301c40b14003407008a0400c00a04045401e2810402c040c1c649000b030401031010341d00081c209508055204092000b035032401c190750018000f801188034844903455480308007424600c000501c80705900c200f121b00f03c0d902c2d80c3c0040b0f5a54a811602c1c101411613001c03603100340d44190100e6181c4500c000c8803c004000b0540a650303040c4501400e01c2c060350390f80 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 676836061 1250 676834811 676834817
    0xc100e061b040b0313080304060506042d0c27030614090d05071502030f04020f0109180518030309070614030106090605090d050619050a111b0a08070804090507 70
    0x10100070995900d41202c04440d80e04107150745a440b610844400c01209600241c0300311400700134041800216400715014800c04c07181002503c80f00340c241da002da00010314081740c8801042b059502e07800b168108941c500302515000030b81c021020103109285000e4003905540042d03021081c0100540340c42414034a0502e030100c600645018055507580f502442c0e42103080020201f6120704000841c42e9109051000c40d80030b54492410b034400e0320340b070142268207901c200b2418503c6c614550081c0c42c3e00090f0307141c04520441e0b8488008004002d00700103442c481540d9130750740305c00212040c280003950185888901610205281041c020139a54940058081101e020401003120541050412086507100c0c00d00e1516403207144005018070b14400030140550051104100c20102640718041c445040c07a2070070082d6403208014501201d04c20070b8020514841001251500803c41c00e050b4403039160501150f5002c002c540c1c405006400502044a2030500450f040c88241124081c1c140d0000d031900d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 676837311 1250 676836061 676836091
    0x3040609051e0d080d181a24060d050f0f090f0304050405041a0108030a1107030203061506040819141f0e0106050a03141c050403170c100e06 62
    0x7981800b100c001c0c9204092240d603026241100b082142c0781a1686403001410030006070518007000c5c8240080d0020031646416034052210100c01503604041c091500c3d80320b09911108414207881e08240000c0402d64015404e10104010007403c0c0141845151405504405810448164050480e02800201e0b454122070b02e42c1140050020642d03040301c00031180403440ea2114181004150600d118000040310b081c000800d88000020080c40c1c5030b846030307540d407800e40440801c0e80d4881c5054000298140c200380d02240701140c54003005800d0500080101d4500380e030703404841e481d04044510a003c90200510b0100c24451881c40e886032125a281c05052050091241080d680b081c06400202844e0b1b10803a59004210940c000006018003400551141c1d4407401d107003280300182e07000c0030004e2090181280d40455038074240113400103640c41d0f40c0c0c04c060035590742010722896500f00e520001c0d000e104071200d95401b003010f542401c0460200040608a8007107003401d201005004482d05007a01c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 676838561 1250 676837311 676837339
    0x100f0b150711010c081207020606040e060103020d03020f06090a11040212190b190e0112030503010b031914091b130f0609051819150911030f0304060905 67
    0x12404980750907a0080764250455140c20058802c11036200c0040c0c01c01e8008a44941e1817014450301c0c40c064001502110a995900c00820003580c2c80c100c040561900b00c0c000400042c00d1030381072810224400e0040c1c403081d03003407074007600d14005003100c48002c6035118003107000c140548082541002001518203502d041288286c105d80c0c944040d00c1e070342114100e01c0110000f00b24981c4401f80d00d180051a0503011411070b00350f0b62055515000e8001446070f940000944422010300480c8116403649466042d80e01c0e28890030301c1c60304010f101c641d4032100111a0300d6541d4151244001e120710010543c01c4504000641340d20307040501411403910380c0c070724201209a603201800401020071848021500321041c07580303500903011590082004905103c00e209091145100501c180d02000e400c403100340e051040c1041c0c0d0b10081001c00340250101e41084082c01d03640d40c201942007401012103980220207840401e1611402c0c0c041c05c460354101040c00e100fa2680144032034002c110498820b0b8030440c413 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 676839811 1250 676838561 676838599
    0x807050a0c0f060c03140c04050d0305130b0412030f03051014040e0114010815070e01111e030c0c010206090309121f0f0c02030a08190905100f0b 64
    0x1800400c141440071040800d4204100c03291108000c5521200c1030203c805901000b4018040101c0c100c3c50440071140001c24095481041d81d0850f000103120784203041e103d48040c0da042c0d1240b0070050809238100004100310800000600080001c80440306214800d404c0050058200c0d0307010100309414541030064458070524440c00b99a805111000c0c1040c61000007002441e160703076882d40315420300c1a01c40701c80a401c00c0c46412112102e042c5e0b0449800300d001c4011001044851344c01240b0103050080e05540b0a1014540c1c170750019045542c4500e0f0150604020750000300e500342c03903900000700d11603407120a110410104600717000800040c201070214a80728001c100300340e401403110491a203c211b500b003002078003100030301909110b01c80e03254840c00068101d900400903098149030420980c80e10020480e8a50036250b40d0b100084e07110030342e0751405031124840c44c0245580303884100c1d000c40e01c2441410440c80301030703200183c03030404903084d84150390741400b0043c4240c206020030003035044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 676841061 1250 676839811 676839817
    0xa06080402101101020d1811060f0f0730090527070905120a030f0e09040f05030f0a0908010e0d02030a12060b030403031e0605010509011101020403140a0b0601080705 73
    0x802418a01698481d8a110714028003601c115912958284a40100c0d2511f8080700801d046014416080c0a240b2100900034140300b440c5480a00500810440d2882c410301c1d0080c10115102d1a10011203003000c814940300d07000341c5003940450698400444041c5a000808500100302c191403072400148802000c03182b03410406403252303455203018001b460280c0316021480140c680140b0306035520005000c059640c1c60441d5045000c142c21300100f030101401303820a15101700009060710304d60b694a5076000b603051a8240c0440c4c040c0300c01c0c0719540c0c0585169001e00701488242d5038220780a4039100300300d07017501c0081c16010700799003014140300f0059a010044414410301760034030f8000b06890090000041116074008907504202205100400d54550400c640380c000c2c507032066480d00c2c1840c0c0302200301e07090381c03151300e0100308108030644555000c6d084201c4580c64480006003020b0b92500c611400303405032860080c4541000c541001045440d40c0055041442841c1c2008185050040603000d44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 676842311 1250 676841061 676841089
    0x2090a0f080a060b2707030506010305040c03020d060912030b0102213001141e1c030504080f010914060c0304020405060f0d06020901141c0203190603080403020a06080402 75
    0x58541403910041e4598403007101519000c502d58071041101c5c1003100c1d01010090b925000043e0809001c603034150700c0fa001e5076000d15040009030401d80e2955017000b8003d0860b200450300c0035142c00040001c00c980380c040801500a51711f0105103510b840c400241400100c3c0750480c005011800d40f003030900e040400351220741e0482c02c9520030f0000d01017502c00c0d08a9040460480e04c83d8444004117030f0069882200c8507000d4240e80d030341c0034502400c4420f28502810020344d900b00aa900c1d803e20000d4074160640343c00d6000307080051800e44c071703203862500300704002c441c0c10450782d111318203042040089031124449500340c00242840c1d042113001c0ca2003070f1001030000787c03196480304049010b603652031121245002c0d0040c25410340101a00d4000c0194101446660101d640032142c01c5604001c074085404400142003220006030401051074003d40028021903017108a076070503040c2020440c82124041d41c0100307192900d0b10b1840c41042a403100e250440b404014248090200507150114081065 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 676843561 1250 676842311 676842323
    0x9170f070605030727091b02120318010911010906080106140a0314070806150f120403140706050a151d09031317060603030a23040905090102090a0f080a 67
    0x80c0c807000c0302114074410210740c0e02050b100c6000301741c0086000040d050201d4504207418040010010424000070409001590268020440c10100c2c91140c2004651100d020212104001c030303064031040c00c550f003501003106e010f503078021076001030740c2c00c150070f54010649841d01c0b200560405000400c0102c0c07821f40034044810120b2483c2c030b0140280c100000c08003010201d02190b00d0710740c8000f000f104090350018001d2000c0443c08041c2c400c244121039500c00742c00c040c0ca14104c801806030f202c03540d0081055081014002c0621151f408580007000264010b400c0822a420190b501904480000111040c0c4c180d4900e81002038aa800c2031864034a00c81c00744090007a966034440341d095108544d44440c02541d210404a443ca083d980025400082501151007541e07880c02450b03501d2250b903204001040b00580866807460b66178078894110300c2c00b030481e28181507440b403181c0700740c40701660115856500450364100303030b0400300340620003024000a40b45403d0715006005494070420403025141c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 676844811 1250 676843561 676843567
    0x4051c030203040b0a021605031c1b060e0a061a010807050a1413030c09060e040b0403090504051302030d0e0a1a090a060806130608030f0c010906050709170f070605 72
    0x240350090043c0c800800c0c0504a140d500d40d5001c1d0004d40b6000402d0404048090065001c5514140060250540e040d120b0034a10122444501034850030348103480301528003503903142d04001500902072000c00012020003013030390440c03038680783c400e458500450800408641010010a80c1d01840316500440c041c02d0650360303500c3c41801220364035080e51405c00c030383c1000643c8240741c6a114046d401220b00480801c503900da151100003007a21031754030409245100740c1010038089090380c00301c90703081442400c011020581d2100800c00303549040f600150300b6091b9403108001c2d401c06100355103c400d01c80c0341096000f20820f001804201590062900c0c10031100c074889441900d59080b550716000017030452031101d030356000040c000d510880e8284d01541c41e082d04080a05068060113041c3c8180c1070103980ac0407a814440c85182d0003954880c8807540d00e84c580741001c50b035244141030152000e0381e00c0300705090400310004030745c107020039040c40c0d030303900c03d0a000180c0d12000c12410309440c1c503442d096035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 676846061 1250 676844811 676844813
    0x403030c0c020a080607090602030c0a0201180911181f200f03130605160201030b040f022703030a02030d0b06090303130f091b08040618030504050f0604051c 69
    0x2558180c200d8029004483c0c041d0100302e4110000b4001e1080420b603961000b9140c450204917202d010310b2030448040d52040c0c1b8000c00540c02880510000b40300310a440709001e648190720010303942c0d1444205401c440009046022081302ca4107214105000d990203045c5055202803408600c0c42c00b02d643e0108105c1c400d44001d44005144c0600585598004440c0d544601070034081d00c82c5d0001c601b5203090300d410080090824010003c2c0e68804e491202050010040d035001540a02502094554442d80d10340304030b0a0746c0302d2803000d020181041d102d240d0784099075090303040342072070001501c5100381c0c000e22203030580560000c1180c984020186e0040344030840140030035040c0c0203180030103038140004201540c941012032480412240d10001548110359501c0c282402c4407900c5c105100015004400848880d000340300807034010f0310030349000440d80c00241c644141040c10380411070000b00001000c1006140c003000b0b403240034208480051034985404000760311600d8812401800c00c8548130064 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 676847311 1250 676846061 676846067
    0x10f080f090f01111804050403140a03060b0703020f12090a140a0902121609051503100f060c030216050d0b15100c140f0718020c010207050309130b03060403030c 71
    0x30940c00301080084c0003402403e1100e0b40d041e002210700401c1c0d8180d0b00d58070f6281e4038060150600403501925403283c5020500240001644100100024941c846200084880740080101082d900035400342002602180030036088c00c02078402c025500e10240180d01503560303100d04510890705e02541c295a0f0885240120300c225180781d004600e51403001c11810340401000100920805c540c030884842a0007021042c1ca60346074900076030760800c000b06040400000020300840d008400c000b807072000aa500c2c40c5444100038180c10000000303d40b00d0024003010740400c03160420170f0b0010b96000d6014201400328a003046000301c05040741c00d0340004144e080708070f0a81c03002e0707840c3e015000f100d80500141015084000800c0200c076091035900c4506100070010481c07030308401800000c2d00c15140b83c0064441000818000549030b00d6007003022804072a004d10007015424810001f858840c01c55504000d190407824000c104001d05014007440c16680100d0f4040d40141d140c00c001400d000c80510403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 676848561 1250 676847311 676847323
    0x525030b0a03080d020702030709060803090427140d050c12090d08071a0f150f0102030c010f06171207020d080403050604030801030605101409040203030f0316030605010f080f09 78
    0x24028031800105004c001d1019001480c0007402942101c0a05940f81d0201e000c6422511038074180ea003051000181c6884c04c1e03000040440184902200c80c0742035280402030107258204121420802c203102160402d009100000940031142084d07820a0503a1b2081c6454038144c0000f1500090009800000381e0760701c524114071070b6000301585445284d9403a003088588039082003548130001010000e5014840c1c120454416800481102d0800c3c2c6940e042c418280c20f00a9254190301041c080030714a400700744504440292480000300e102c5d440e0010600150148000802c000c1c2c0051010004080d202821255881d9054600c82c0503020f40b0304140740340303001d16000100940140010b21003810380c81102c450590340180300802543d140c500f1042d10351800c621903030075207508166881407a880c3c4201d003541d00500180c1a3ba14004405504031459401191440080c5003403583c6100c04e00d503d407090101070f02c0d00b8285003444644249000d4a4240700a054208943e081c81c001111468103000c6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 676849811 1250 676848561 676848563
    0x70f061707141c050105041a090709050d0525050a03240e0f0d18030201082e060e0303030103080d0c030e030316170c03010b07050c100809010525030b0a03 68
    0xd100d44442810038409101e003c07210b07a5030350f4141070400200c0c4614143c46289004000030b241c0250f880d00b12014071952a100038038201c1400f45ca0a000582034441c001140c0045100710090301c174020080c8401e9021061a201e01c81c1c5c907400010f01401161a14180d0400703590700440c0c0324560000032058166019002c4d114405128141140154401400211102c0d1007440d90700343c956002c10307a0b03130403204201d1050b000c100c4045100010005035010741a8150031024184180c06541040f00c5594011122480821000400f898040025503401071541841c110228051440c5514584600f5030342e0040d48440a2481c0d0748030410501d1b6800713503001e504442d51100c00c1d00d44925025899200010380c86140101151031440103485140604204a12800b0031000c0a4256400c0100020050b000f0399411110743c82400c5401c07460341d54201c2941003244480d13850321074515103034048900b912005446170600446a2032600400c000903101c2a400d4042c4d882d001642c405504001000600c031540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 676851061 1250 676849811 676849847
    0x51e10230a05030108010c0e010e040b01020a0606030c050901060c03090509070c12050301080d030207020901030f0201050705010f061a031302012f010203060319050307020402030a020c06090a05070f061707 90
    0x1c20101c11070300540030b5812261403034020030402e5031400c81900c820749403166050000301040107800700fa1070b06034040d0101c44410310446000b00c01e980d4545007120480d400076610001540400c002d0303858590a41805441d4a2174031400014640e0380c0602070011a010381c911a0580c0c200051441d0302c84c6107074031140c907040002c10700c20714440440508280e0013805060340301e02590b6151140039001e80201e400301076025040108e10307840e40d11505a8008804000c038104030b4100020408103078240909003128050840005001e0700c0c00406014106d03030325880c00700c00c40040c01001195000c60800b07076842502804c10001207120225804100010b0404401c0e10307030444404d40780f2204056010f5441001d00340c00f00d80358501d00000d800400103000c00000d01a034000c001d0700b80141401c2d000f461b00648015005800c0000c1c40034490304100045a80d80701980c0300d032410f00c042c401c04005010050100c808040c1c0c140d41401c40080a5400d52880101f00084100110348814419000c50700c1c0c0c400503076 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 676852311 1250 676851061 676851067
    0x80a05060f1903060507050c0a1b0b0a0302040504270321090302010617151b07020a030501050a051f030b061c05300405040c02070302040c09051e1023 66
    0x200c218000b401180002c0d98518035200008100601502c201e4550040d140010302c5524486d56400e6111603003041440300006602030005a02943c003c054881803126840258a031820182030000b10350f0f42d4100000300c04154042021425410031000c1142030b05854404400f1061035421f420456016110103002d0b0300c1c0c8040306040c1030341980000c09440d000614407503d0b1210a044a42e107038507034818170b046120341c2808684480140e9805042104100a4003420f00381d0f0394001528615842d030060317505945400402c400e0b4107162107896401244000000c003a800300c0360080951480e01c0c000180810942c10210b0441e0381e82000c1e6101d181d8442d0400844003016203803040c0c5500403060303618954581241180c400303c1d1072101485c18000c0c1c09017002d050903d02010840a00846202a41035000b0001d000c00980c41d1030140c2d42c0500460340b50651901d2030074040c40355030400440c840380d0b40120780c12003407069600c480c5810b8101499140c0024840750716580c85000d03007598000041e0500d000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 676853561 1250 676852311 676852339
    0xf0708060a06122c10060909030e1c0b070908060a0e1b060906030a1d03031311010302070c0902040618120f050304080a0f030306051f1101271110080a05060f 69
    0xc0c04c84055400085c003400f68541d12503644060707400c44100100441c4143c0c11030701c4141001e20360540413900384c0a80c0302680110b82c807013103143c40007038540100040508109000c61042081420703000055400d0820480c0340c3c0b00745c40d0792034802c02c1b00c1a48080c0003544040d0150f40e07800080d034410341001000389a4034144101a040104522248038080c0360a2041407280c0710390200c1a030f44034212080c1645541318255507201101400000b0071414164203101c10400305c0c4480642c00301038404000010394a505040004c3c0500c070400311078a42d0758034001d1082c80707028581e00741c06050740d80c0400d9a42420a45141007030450181d50032003082440740300300803014491054400c484150080d1030401c40c240d251801c2c0540079201e0b00e4070089030340d0300b80c2c128604548246140001609050b0000032001c4c0794006600c1a480520300000400300250f07000c1060000044512441c81800c94100304004051100900301500081456002e01d50f9032000070115103401d100400392400c001c3c110040340900c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 676854811 1250 676853561 676853563
    0x40e0105060918060601050706110d05070e0d170309071208130509040819020106080a0503210907090c0e060d020d11030702030714070803030f0708060a06122c 70
    0x104403a4648108110b001050400c48104000d1010b6080c1d280940304903900d000045d2150750004000f01ca034555141c82c6c000340400783c0070103000c070309481500c041901c0c02d0226005011601c000040c030704c14100c003104007000459584c22803240724003c0d070708291269508565141084505d500c01c404154103200c0040401440b94000c20340303040c0004801800d10345540502907003150844000b010b941c810001d01240d80b0462a0300400010244008502261141030450600c560801c040b07d0560000c910030103000692502c042c1c102c90b40c0c0466040c50714043c01c103e541c90b01a4400c2d40043d65441107032000291140c107600042c244050400c1e6a00e0710704203042002980b05680040d015807805800c42c1d090049002101e0060481d640258100720b00c07502c0d4030051203441030081044d0f2050000c0081c0564080c170142d48a4480d401c10741c03606285c9020301030807181000b803070588100b003112010b2203240e0300700526003240c1e00c041c6000550301551941010381c01c00428000f107441e890b020146001000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 676856061 1250 676854811 676854821
    0x40306090c0e011509090f060f06020c04050a091a0915070f0f020a020109260105090a120f0206070c030e12010b0a090603020d0204020c0307240506010c03120b010509040e01 76
    0x916120300b50140e03a882e456207100840034a51100010400d080820a24460341c0001242903005079000030300c2c5603200b41e00720758951107602c8071015801440044039189003503c0360a5006100340003c2c0300e00c02d125601e01400380901ca0141e10038111201c003060040004200480c02c0900c008000f0409051811014008494205c40c40000480b020381c1d41001901c04510040b0107607041e11a6510700c1c0c00d00480c4003441403601040d80c0031130f52940a00034809002d00074240140d0f0b0780006400c49080d0360900b20b02d03421f40440213070144840f000030001050b500081c40c1781c1c0310100385080b02885042d0301d0110f0703044502d0000b0036801410f84000d0518a507042d071205203d020300316000c580055880d480303442520791620020b54054031019810015003000e40041000d040d810003075038900003082da03d5850041c660321445241070101c0e540c0c2d45614107076114a6410420900306000302e0f00c0f407035800070048115100d030030140e80d4550120b02100c0e4000c505803803400c1c500820034445518108001c9000741 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 676857311 1250 676856061 676856069
    0xa1803200118050402220312090e010e0105090c0c0a03180602010608030904020d2003010515042402120409020c01140c0706150314030a08060118050d08040306090c 72
    0x349140d0100e400320741c000c000c407040c03507140744040440c0e032031501d82000000d401c81c181081108820624080744c900d0741844000145220f140349403003981036010018024201038109d070206500100050000315070341e03e0083e044070022680f40b081641c9088600449005a8141600502c540d8618400700f5400184500b180c1ca0001031200c149542d58100720b0988500d449410030076041007081100c1410141c00406120414031401700c3c804461180342100740da002403013007011140200042c46603103410040d0310f40444c0101091410b113800c241c240406070b40342400940c030360441d211003041c80c01c0c024801c1c00700807510400d00b1901c0782c0c3c1d41d41240002c0e620900144030f2030f501c1d0010300060780345075940712400703850b00c4411030303060550765510075006080113822010000d01e01d0320700200095490754259803600341030000e541c0740d445403080a0b00c85c00700a850b507818001120000a5402c1725180c41000300d5104031210300d50181d890030100250305c90794001400fa242044060300a1254070314a480c211 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 676858561 1250 676857311 676857353
    0x2130912140a0f2f030703020c102c0a080a050c121f0e0303160f02010c052a01020708040e070f090b0322060b0411120402060a1803 58
    0x140107005480070510903402010040b03066180100d41c51486665290125025540040c500c08070906400c0c910301050181103105134400608041010f41c1841401c20032034098580207100c416403a0050024041c6030b40341e05414070049240102c3c1100400181c0003040d0141c0148091902c50300400e403a0805100155514412409554854101655804180e0044001400ea041c800799501c042020640118010301911514131031309252051000b1809800c180300d00e0114440c1008024000082c188009001d5903d071038904905203400c08111013038074030b142e9221030b10b0068400c040d040b2101004042d83c059840420302c0c00401001000800a03035406070041c3d100381d950350342c04603444450a40c5403c00a08100400c0280c580400091900026400303c1002e8844d0070345480c500c400f02504050b520b041d102d07000060103003024420001044600d00d030b060300d404580713500d0490901c40940024010b803800074440b81c0c150301c1100d40320540c480c00c03001c0c642a40d41da070401c00441103010444000d5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 676859811 1250 676858561 676858577
    0x309040510060e09040203060f091c0c0c0b09030615030f070f0801060b0f0f03040606080a0605070e0f0618030124030215090102100b12010c091806051c02130912 71
    0x1907213014500a44030b1503009000f0100365651102e00410640003415200281c4510500d8a11b420703000519100d00700400e503a400210342c1541414200d101282c4e0082c0c110480c00c1003000d0150301c000c110350307502c5003c07403440740752820101020920b811051211200c01d40101c2901050159081c03540d2800c0b02e00c1413009002c1e9540700c6141070400c0c415003c0755011075508010350201600b00300d0156a002e802204001204c5984110a9040803820002121429902d004001c4040e4008000c01d0400c901070700c0d001c1c00c1d0041d080c04110240b00d1400100070442c1025500c0342590f400750400005c1d55403042d556000c030350780c81c0b2010004403918001280f1401c581c0503045458448082564500c40d0140d004003510515006142c3c014951040480d82080429007600c0d0050804d01031550880072598942d15180d2400344c4015840c98003621001d07410782050800c014171f41c0c86a0488100342189400d581808081d4030024003220b48924065044a050036003090030b212508241914044460300c480803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 676861061 1250 676859811 676859837
    0x1d0414070801022101080d0c06090804090f051503030405060d062111040908121003060c050703080906040b04150f061409070809061503011103090a14030406170702030904051006 78
    0x3803c02002d001b402c402d0340c010006400c85030720840075444400c0c0951800503400240342c0f24442c640d4801d0f04500c04154881d00681543c07502441001d40c80f50141130740610320070010001907100d22803071081030701c600400308120b40000c06030f41c080b078024003440e40c000048140c491031494402c05010710030b503038070301c0a2050350131030742400e01400a5040e400400b0078501003032094041c03141c080c0036200443c0715111002c01720000e40c19118002031100035856154407040140350051103d48000d0030000f030340e0400014000003860071b00010380c00c16409080780040d0000c1055000c010000c4800c200070035420620006209203aa45140416510035220010680d40d404400d0390600b0b001e541c5003800d82c0c001d000241c50300e001c041c6400c0301d20300c0040010800c11074140c604003d581064078181d401c1c0d00714000e4a0304000c1c140803030144a401141c0907504041c40d020029001140c4c2c4905180074000010000c0c03412032082c0100c411028008000b0000341c04c0a41c3c1040c69290240204808200e010f07008032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 676862311 1250 676861061 676861117
    0x309152f1b0108010b18150c070801020f0a03090f15060911191101021224031605010315080a030e0f0f0a03080a0306030f0303050f0705041d041407080102 68
    0x1d98004180c43c0c105259182c21050318080d0f04c1101c08411a2100a0840d1880da94414032003842c203134220700c1c0c2911754405440c054144031541d48031041c2a84100b01c1e12035901502000c0d590291070a0800040d05042401e11555282e0354510041002c488458400d180360682d6004105646034002c080100f00894064052075101d8040c0c040107616442000c40d860b03521945020048980c3e0718000350a0840034a50007401c048285c0c0c50181c084203503018117031a4150203103182d9440c50124010400410b40807600f20700e4205c1401594101500ca818448280307041001c070b07100402c04101210050b8880381070041404001c2296144900003143e03200f0010305d000c581004145100500e803a850700e140d55140c7c2041d503c400262404e06807195000004212482401b000310740c000c1d10085541d10b400031251425440080005e02884018007040c040ba803541080e035980c480d0208213100c2c140d102c43c1400341c0084085801c0101a100b81c0d0008a808036042d0082d141d911980e00c0d0042c80400c41200da1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 676863561 1250 676862311 676862353
    0x30c01060609031104110d020d29060f07030c080d020a090501080108070b0d110403030206010905011a0405060904112b06063002071208060d0309152f 66
    0x252804139000d01d130b0300080c0340680c0034a241d404881c5205251941480701d98060742c0049440d0051160b0ba10100d00c1038200005000400708040214a490305043d0000150240144800345002c0c0d00c000c46c08400701402804440500e603004a082900d40c00c480c1104000b0307500c160211130000f900c4840005003540900c5a00307040c0e42103d406002464248480325a41d900310501c036060860b00d5441c0c1d038420b14281c07802080558007a902070080d5605140800041d15410790107038194800c542c00a400c00500203050701c05442080314800c3e9200860400500a00100c55102e030301c48600140c2508030310310010314154442591158010480440458081291014403585011801010030301051004c5e000000414403404c4001d060301002101c1c03902e040360060b1808584000d400c010fa141141d0b04100042e5100e5404c88242c0001c006581d00200340d55001d2141181d0421803150b01015103000f00081100014000020b640c02000d20700701000000c00035444d9800c9001d010010603c810051000d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 676864811 1250 676863561 676863563
    0x103080409150b0d243c03080307020c04050114030c0f0609042301060302041a2d22170307170d0207080c06160512010302130e030c030c0106060903 65
    0x60f95040c106404485005881d402a011464291080380103580c0d0504903c0d50014000501070f1840718000481e110100b143c5c802000007036140c0700620f0f501007101c0301c00c511081e01e522050441c0c594595000c140e150000f481c14240d48076050000200b180707e44020195200f00c070131001c4030146c07485201400008801c0c066090340140c4200004880b44c1059041564082c4440c207080308034034220700311010000d500f80c10030400a038001508002e006440ba1a80310b0f80c0b5103a1003c1880c158144641042e00005000c1999000301a2101c1c02000c141c0c44c02a505e090300d4081c002d0b0f4650443c4420511981801d02440345440d08801d1603c08418002040d108150f520a01e180241c40520240428a400c40e060451410b502041181e0001f48100040d00c449223188005204909100f84032102c2d10000d61a51000c100041c230940d200181b81180b210f04680d0103444600040102222080203440541d6203100d882c80005140440108000000c0c2528081100208185038540004448019003440 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 676866061 1250 676864811 676864829
    0xf09030e22020304032007050a15051b0106080f06040605130503040603020f0706060e04021005030c090405040c03020a081f1505060d061e0e0f0601091205030d05010308040915 77
    0x61900714070190b5008503001402424040402800e10313034520010300e00380280180903000741400300120f00340030718048058001c1e0a1409803098492000401c5405a480680e4000c22240c1443c2c0300c0160a50103800940511000da07255100841c0201e6652502990200c1e4194a060700003603a00340c86101c44440c840c0d01c0b8014500c0c0034a4154214040d40000f900402d110303a040158800041c001d01c2802c0080103681c00c444420320705401001b5020707501031f50110902004100300545c042e0000c0031500c0140e82118001125216030074100031201094000941100c1014004244503000080d811145e51846080300c0124902110b1807013030320310300340c0600782100f00400203110303514125014102d0410b0300c400004106554142107904d520440844030005101c80360305221b21074059810f143d101d190307641501000e003003041c00205035018612803400f2200000d01c0c00e0003089418811100344244843d0140902e5031641481c21a07a4098405c8080007441c00b480502504503151040d411245800b03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 676867311 1250 676866061 676866109
    0xc05030f03090d032a051009020a2c0717090106030b240a150f0509090c0307051215100c0f1e150e06061906210f09030e 53
    0xb8080c00b05403460701100b1002d21035400c82c1994100d90420348091040000c425462500000341441c0381400d4100380203140a9052449000241e142c819140c01202c00c3c10005c40750310304000780501d420300c0803100c04481e2140404240036a4903400810b03241105001884104540ca1303600205003200c03014030000380002d0710303c000100c0b440c1c18410a0b42e6003511070703030400581125840c0000d0101c400c1d904100c46034994418401e80d9190301c98004c8000030402c1c10181e03d000007900000300c4c621001041501640d0000002440461040341601c04a0001d015400800d082c49282540fc8041d141000e03401464502682c400d07041c46051501402508011401d02079070650700c032160200791038589202840704901007980084c01c0040484c0d4154143e070b0000500c0110141c50a04040018007000e02c074031035031940f06041c0c040c4140780c40101c17421801d120b4214918099144001d032040c501c800c29944c81c2241c590750020603600310001642c82981c0340b0711035038000f80402203aa060500d042e00811580 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 676868561 1250 676867311 676867327
    0x1080601090507090504290d02180402010513060e0324070c0c0b27031f0209010905040c0806100203340206070c0312080c070807020a03021302070c05030f03 69
    0x1aa00860f007050491401010140e212000f042c180c070642442c83e00c0600101c024500740c4505594140d81617602181c051130040142d800107060014001d10f600c1d121340c011800f050031680520201c0707183c003045802c5071402c20f0b528a405042c2c03118041005000e030041c107900031082e46606803031300f4410074140703009039040d120040111203081210750304403601e03804d80c0d00100b42418440003800c0c050f070f40c0306041c42401c002c12003103071000b528084c0c1041c0684e12401015100e42025081c803580e4040c2c42e0320040c2c40b1508031004913034003441540001d070010326200b41d00d0040303640105032620844041d2004403a401c01c0940480e564450311a00702d001c0b5649580c03005881c4195202400a40c54025030741502500b9034001aa460340540b4045806400c4079400b0010000e10f22020144041d24ac00e0940251a01080030070300da1103880b20040408200060b070404554565007043e01568001e050800c0c81171001c08041c0c004d40c085602070b69140380351100003c40d4035000800d4403000380c88a014500b44454 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 676869811 1250 676868561 676868579
    0x109030903060e0f030c16080304050a051e0a0e06041514060d0e07060818060106080a0b0310052d090709051b0a021c020c090613021c02040501021501080601 69
    0xc104007030041e4000c4c1100c0710701e40e14040014202c50414070010b08180b481070016060070000750780c00f14031980c100307200400059407644400c0d000c481d01965800500842400168100c181d2050300c1a404404660041202d80380c05101d144100d10640d41000030198a003a00d1100b042c0b42d10401c5080e00324200d41e051a824a0405010f01c198039100100e180310003104410300303001158000070001422402000840c265103540142e60880d0395018054a50400500421840d00100505012511007d1181c26a02c0c10819089a0038030784808000d5801e0084222440d240003242100e80300303c54900034103100c00b509280d140240c211130020031503039207004000400f50000401d062504100e0003040a601c8002d4802044412000d03805451820200044800031405904114045521031041c040c0c941d10b074182c8030380d08004120b40302000020340d210240e000e4480c01d5400c8a1403024520f620601001580103402950070076000e9401c003103c0c00804202412091041410030f40c0614010041120 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 676871061 1250 676869811 676869821
    0x31c1a030a12050c1b0a150801090b12010c030f05060f0f040b030a0b0c070b0c0c0615061e0706050901020a020a260403050d08010e06010e09100e0c0c0f010903090306 73
    0x9a600307103903040078004c01003e410803140051110401c0500042d40c0c90914000c00f00202174401545d5200490960307010040184034140101a195952080f141d20150384002407603a031180c2003c000d00c4101f0350b001c401405801d0350061003000314188000f00d006807811074620349078400040c0046951828440400024183d400042501809140c030904e01090000c0052440707000c41301e4a10b0350390b48480c07901841042008042614040c0148042611303800e02286a44c0c10603403d01c2d40000d45e80d140e00016200c1d00c18001c010000031f0b1454001d070500c0300303a040900030035400788404224556450040034283d101d141c40c508010b800044d508c0b00010b1752191040c00f0409500d619915500320b0031031011300c82d4800c0e00191415840f414980e0340583e4403452040c09840d243c0c15099060a01c0e02c0041c2110308e03203200c10381c81b9980342000298944410005c0600401d07a4045400a80c2040041c450f0164010401d0484a00804040a030282014099906200da0656410f1000c0d481c545554000700 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 676872311 1250 676871061 676871093
    0x906050f04150f0b03070e030a12080403030f02130f0905040507031b0308040303030b1e03030318120a0c050d0212030c030c2206030605010216061808031c1a030a 71
    0xb2034415400f0420f443c00c9000e0802800c450182c05580307080002024000c0200d40b90000c3c0b007070b4005400000010001640e001e20041e144c208007440d0307155841c05401609030388462900301403000c41d80b415848520010130044445061841d1b203400d4460049406546044074060403a0f4009c14003040021044041401100301d6990b0040b503489e107a640b07040e11907006602c154006910744010350b41d030746000300a1200d40c01100d11004031501d06180031948070f0000404d01d00c0006840c0b0700140c0200424465415044103401c0c0550399060740e103002030100f0040c154192240c0c468030300d101d050356000052032803101d080140780c6170540d6103005190b20a50b000421000f0b81c4034081c00442d14540380016100f04150080401103040c90524000904882ca5540701604542c80030f680900c0500030003080101761200c6140c0204091010900d03411102615805110340d480300054911001281000f0f810040407065810f00200d903980031110300ac0d007081262150f16810450840300051986841c100241c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 676873561 1250 676872311 676872341
    0xf01050f041b0c020109030b01090b092d0c0409050f01030c08030310141c030c11101b030e06040305011b030c0e010f02190605090f0f030706050405150702010212010906050f04 77
    0x1054403a41c805031600e0081c0e00402101e502d82651406338a170140c00c3c03c0d0300007002c0d011210411402c103090081208121441a4005100e001248981403518102c3d030180103032034402d000500303280c21002e050350024030003501c582a82140124802d403002c02124011080c5500d1742141504100d580080c0640c0e1100741d039440740c100e000c8060821111a030b4014040d000c0c0e00ca9000445144c00c0034501640c0750303402ca40c80f65484080001903103802030101c6401242d9403c5040031081039181c01e03216110444c2d011540201c01141c000100103054100800b010790f00b1401d00340d0307420a8034094050f1850045a00e01280444540c03900c1544030713401c120040c00b021b1040703812072840142c0a14a031902840107030b41b104e4559003041054107080080c05513030034078500204080300703c540820380c4a006441c0014aa26264408a82401001c006a1a004599011403203e904001d00041d0003540070405210720868030200018802030b4601c590310403a0006003103042e000c1040d0302004010b000710014429a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 676874811 1250 676873561 676873577
    0xb0609072f0d0f0215130c1701270303021602040501030b07030c091809030e04020d0606030b032d03090402030f01090513150c03060b130503070b030907030b060105120f01050f041b0c0201 82
    0x41f071100ba00760340003828091029840c1c0d10b004038500d8299005581d0303041c14034425909004030341d07040c190410282601840c0043e125070b80102041c00305903040300080d50060610002005001c0c0c0130700380900840741d940701044a03020003102030300c565449105080790106006070203031013003035507030403c00e0990b00c030b490222420501c4600040490300000040d03129a43d80b40d1060280540521528801120441c010306654402858034a01c4503404004003454030611282d5030b480d01400c04c1075650f0154010010f40d242c2c904682c030115846c2c8248a50301d50b0034108030101c0c280d55138100341880c050790400164400c0d1403400413294080c0146030b5008003090755801d80003c3c940502400340a4280400441201d0755160208051070701c0a41e4003c2d40105a04006000140c0303800110001140e03400040f041199480c1401600c49019100c84a000d4192020030083c2031420003040a058600880e000c49102000360140011a0030882072241040618410000c0c02c1d0300402c486851184149010710b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 676876061 1250 676874811 676874813
    0x3081806130806370b120703110906010e010e040c09030c0815070513050108070309150606030c020f060f091c080a06120b0609072f0d0f021513 63
    0x100d01e007815401041c442c2c210700d0500c5082403d4126030b40c581011403001c0c0c1082c0116000b5541c02d52000003016441959660b540055612002e030010000d680342d505803510a941e80c100607a540521090240c4940030040000b8410b60048508054105c8182e50303500340110030f0001d00c4000c0c41c050381c00f402480850740740040050425940d103005850400e02901c2030054000701c3c207009103000382030b08040c8a01402110b503180c25141b44041240d009290807061a2600141500204803408010301549041e00030038180c5003094000800700c5016076001c21021041c0341c1e00302d880368030b06009051150415804168108402040280c10004400c00d803109500003100b03072054030a0002c4050080b41c48441085148d03d0581724680c01455402c403000302c0e441c1f0950703c8501101005100d00d220760105000704012900c00c820710010000340f030f2010043c0421148820000384440c1200804c50710441c042e0202c2c00b440350050110b000b1a6800800b403020b4200454910190014a03004512104c884014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 676877311 1250 676876061 676876087
    0x2130e07080711030f1803070603140415020d0911010f0f0c240507080a060f1a03361b0609090403030f020d091401050c1e090a06020601051201050103081806 69
    0x3000000303c070900d1181e40c80d04820b050420340d007a84040c062514020f01400c0d407204c0cbc040415405548110b8103a107010455040c41e009000e086802d0940703601e44125403040001c1c0f494140d6203000c090322032041681c1503940403900424000c840303000060391081401e0002d4002e22810340e0041e0346e800e1424045051030742d040202c82080310550002080c0741e040c81010040341c452100a80601c9002114032800e00750602c40c02841c09030f020b0030015002001404411807500c1c3c001038003100a07000681c07108280900101d0628511310b0360554001c480480740c44440c0ca10804072800c001920b880c0c18030a513482004100d210041c002d43c20316440d5000814a40e07524801071071a140c41b0307807000903071031010304084000c00d22608203142d8a0389040c0501ca80d4404030800c1d50344035280140064582c61070202d40e059035006100320b264000046800100301150085100340c1a2442683d04541003c1185100c0d070030f80e5420711026005181c20449208000ca00d101d108070744c90390240c61a458490700384108 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 676878561 1250 676877311 676877317
    0x1706150a05160c0312031103180a050d08011a041203050723060403091401021c050405030610151706090a09050609060402010f0c0203060c07030314070302130e07080711030f 76
    0x100c4a08140250a000304211022112108109480c1c200302600300d01d04240008d21016050f440500c0c103140d41d41000000400520b06d40d960300c80c0660b060041c1c4014094402d0100703000e5064001000400c21103100e01002c00c1c2d034112101d00b19a10903240c0385490a451603402a5401d4a241c43c14003a18500c41400f03c41d242540024400101218a018100140310002e182c0150a10b89105a040c07d1981e80c0000d100d400c890702c4007400800d120419a0a840c948243d60106416001d4102004803a80b4515404012150300d00b81003e01610075607001c80d600580c2c0a00e0070300c280d0301030b400709a031402c1001c1c0070380d4020104a400602d020258980600d04001141d940426610803001c010440d64841c3d0410481c4e801c90034407170200b41c8581d001a48544000300a98031002c1d01095040515110350022005c1c0401d610003a034076810500401406903010b82100c5141c07440c000c1000a1902c40201c9852140740c465440102c0d94076501401c030f5424035402240c1015110038412074020084481c02 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 676879811 1250 676878561 676878563
    0xa030c1b080d0c1a0c0315210109050606010c020603010e09160308031524030912030f04110a031205070302100606020705041d03070209040f120f1706150a0516 70
    0xc2c82c40d80c43d4151030f0080d091004440f8002e44c400400b0103004201c00d4641c181c80c1c0002c07400c1c2d00500c00a0f0110042880d100045071110010f4414000700d9164100c10b40c4040139150095083d240c2c1c0d60f44440040d5015007404100039000724003000100140040800056004003162080d02c180c0e03079030700c00e10000818498105a840304400001d100301d030700081e1b218160b80e80c419528800010400807403445440c05202c0801141080040014803515041c829101040d143d03c0059443c1d0500c015021b02a16080b1008c4600c0000304020110901d0580f010908403648001d04540c4100412004c555907000342404409500c144802d51403080392500070f21b0094103656000301181c0d8035040c108401c1c1d43c85080c0b00e52500d030150148000007400072044030401742c0c054801d0555078586e86000c43c0c0b21012001d0240101c800c08140c40d40555015001c00e9a519081d41c400441800d0107a1000089000f5120690703c51021244a000c000300d000282c031181d00d03103081c014109402e06030154401c040000b4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 676881061 1250 676879811 676879817
    0x405010b09010b0a08100b0d0f0b0904120f08091009031806030e16030203030409020f0c07090f2a080a021b0106080114011208070f02131a030a030c1b080d 68
    0x1403684400359000c007645901c420001c03483e06507079251041d4052a231260220318804580c6a0080401c03203065074004c0600c549001d414615585880c0c01d0078918600c8a01202000544188a80703160502c50b41c90340b405040c0200140091071070201c8844014540c620f42102441266440c0f24404068a045000200090f0318041018105000c503541400710b000100c941c604091030080c130158130004152000c0d9081e5480050751440c1c1000a00301500905a11410500c80c1b0301c000304d040712040d0444050035000103c140450802c41c40c900d02000124524101c0c0702c0040200420319a1080e4041078000c81c07808401494104204c02d900c0304d41d40d98001e1096160b45400041202940910030503400e204484c4040000d94101004c0e211907450241c006441e0100101d03640e0f0620048403a901d0b40141e004140c600c1340303070100c500c03200038006010b0035848401707034510181c21a05010038245042c03585030756444407542e026903850301c05103085400e005c80d20b07105101c042503400080180d100d2184072030f1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 676882311 1250 676881061 676881067
    0x72703050f012016060b0f0a080d0f170712020904060303021c03110a0c0c09090b0a0e0138031504050f12090f120d03020c070f1a030405010b09010b 65
    0x840800048200c900b8114521101004513a40000b240d10b41000310b164000f40c0414120130703401c005000c4540c0031600b260704c03840310b041c0081c0c05071000070b0305250141035894403c0030702402e0700152400d80903100c2c00c00c00030040d0000100450310801c04d00f50b6030301c8400350040c1049511800728040764515001180982d003c03d070404103080c840110105140741616091103090102160b40c0030074000c2c411303c0340a01551a078218100035507407051101500c0050800c000c5842c15040828500c2011b9540040c0f040c50f0003071090440704103004807501510140c402d044060004228120841c200303000000c20103100c24040c82a5070343c280f0109005168900d45102a800d01d41031160420030f035040001465030000009095101006040e604143c03021503018010f0301400010034a54203030780e1b00b0100180140d0130703105442d54040d8054091100c1e007a08843e590f03034407021801004a024001d500c1810090308549142c0c0920344021503210740b1500c00820484410404140e0896081e004090519408 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 676883561 1250 676882311 676882331
    0x12030216090c0905060a0e15040801050403050414030f0601050f0a030209090a02090c07021807120c26010b090411070807030509090a05060f011103040b0301090f050f072703050f01 79
    0x3ea091005131a0072590307149410308140c8041d00201078401c6041c040c204218507002582c15103010b4400401d0601c0080c0041d2030980b800500581c06405444e180a2a0304501081802d002800d01103000d000d10003082e003030b424207003004107101e1441e130004c0e8402c10910005c801a15142c1d6040d00803c0003400801001820384108142043c000f805840480c0c011700420015948680d508008048906442085e9880701042141c400c02c0413004ca00060703042039000700160340c0c4203009a41d4400f4042c0c0041078103801c4103040350b1384c0100303109000d40d0040a0218145505e0154041c00c0c103110742e07054491902c1000c0d81c60b100c80303410260701500410004201d404403803e1008001d82d000c100140d040000303150a000050901e01400c40d07890411082600142d4003200c10400ca0b0050204020b0392500c3c1e40e59290444041c06640800d0046c00d0700301008511660b1900d9016800b03901d0399100e81620414604541801c2c8044030034000c03180c0d22105001001c40c00c1480101822440303000046076081c1e0f0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 676884811 1250 676883561 676883567
    0x4050405010605070b04230303090d0909141609080d081e04050307060515150c10060b1806040b070f0605090304120b0603010b060c0714060a0912030216090c 69
    0xc164070207024004100038000c0041e050100e90342d44158400780701a41c2514041140c80c200c4071210380303100c1c681300000034041c22580008844061016036524100f81e20344502060301039039140c85160150003101c5000c40c0c41c1d01070b074140d4011450341034076003190002c0c4d680c03030014500243c00d0340c1032000c1040d000c00d200381e21594031910280381313000125a00300c03030405540d043c2c5e0300d100f64a005080c065031a800300303010100b481040228400c00070256411030843d04c05940b0643d0150004170824403450201d40700b0142a8080c1c1c50440d502040018109800b1140d00802411078418241d4440004c00c004108444e00c4405010010b0144107030003001407a507d00795046490242c0b000b0041d03171003880200855001e000c3e640040950118000c030150310b8110220340980000e00c02503601920204000c2c50030b510014800b0116450540f5503e6030414401c00e010143c81828100380c001890f44106000114102c02c550361030b24464411510140c400c600741c800d40c1001c0ea041007807001c0e00c4841014915074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 676886061 1250 676884811 676884821
    0x4120812040804080f0a0c0e04020f060a0e0102010f1a0d171b0d020c03100207060e0d02030c07060816050f0915220b090f0328030f0e010f1b1502040504 67
    0x80c9200400341e8410302c4d107c000c150030f030314400e14600110f4000020110b40b5603a451a81102d0054441a140c00c0680c401500102200c8406401580b80145007000450107000e1b204101554030b440030b4945103031209000074524106015214551004807210648400f00028501c40be1000d907207103101c100181c1010300300702c81010124115800000c03180c100342c3d404541a914008003040c01641e85035546008006005540310b041c0d5540a0320010107021a008070042110482c42c409540407241c0310001910380000c107458400c0c041200c5802c1301e0300e0314018801010207441e40341c182410002c4c6200040e90138031070381011010324040800c11681e40407182400d62140c002030445003624504001c1c611019000d0800c5061241d801c2d56003600c0d06440c184403801c400e81810f04150314040c0403800e0328094886490b82280003035944c142e00000c042c0310325031203106050160741d101601003000c60116803840d041c040e01000295a1030500001404101c0c2420780f0016038400580c4891a01e0704000c2114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 676887311 1250 676886061 676886083
    0xf05062802192001021303030e12070324091406070e0114070c031709090114030a020f0406150c0b10030512070c0b0c0f070b0f0412081204080408 64
    0x180c010b0003000003001d04940242c01c0b000061400e20000f124000204881100ca101160419440007075400e810041d15445003060701e01a444030201079405505100c03200c4d0004071200c2140e007003594144002401c04268a01880700309000c1036840f50000090750407500d4116044035000d00b11030000b40803060510840354444078509051500940c5403002900c01103401014030810000010314404020b000e001000c09140c02542a550300801048400460790241c080380344036100a40c000150042203840349102074a010f000f400c03560780c0a900f0700602c90100c02c0c6481d800f54440c0d0000c01c18030351845242280c102d455503140c0080200741004030030b40c0c2c4041e140c0722462200c1c0e401403011030400248110800001c0e005139507100f01a00b4201001001d9401906900f0f4001585081102001410308032240c02c417426180b4560742e8901c0f46d00284100c0800c107030941001d10040044010040188480a0003524242e01c0c05c0c101004021740903034201c4088071b00140200302440110010410300300c0f25 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 676888561 1250 676887311 676887391
    0x6010306081f020d020c03040333050603010624120501061718060a0605030d032f0c0307121d1e042004090b010c1e0f0506 54
    0xe41001d160a85550780721181111410410b035044046454030f604961441c41c015400315140c01d0217040c00c6803a80c0c864401a00c40385800d000c240300728510000502464003100ea00d80c40441e008034843c2c4003400000301402d9141d566154009804484038403981210740d40c0040310034034082000c0c1301070251440c4100d582015460030b40140b2010350840d0107056200010718034a8000e42c1d0344c1c03a240d00c20b4081414800150301400c020f020001000341c00043c1610400c900761149a45101c000f14100e0703204031442039020444680800868004c00705103070300007060b010814a044400c0b107402d07180d43e0042608407032402c0c11500740c541e4540d000c1010309102e0151590310701e0b010394060008030703210a4207a01c01081450410340d200d191740c643d40824042545080c900c03082100301000d1a0494000d440707070040b00e904010b4065459881884000c1c00664402e2150a40e1800803005541c038407140c01c0121141c0000030408008100f04003d40342c131601c0038103c0d035106140c1510124142004a01400c011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 676889811 1250 676888561 676888571
    0xd0905030d0614090f220b162c01020f1504020306060306010324140906010f0501141b0703081615050c070212160b090f010c050a030f050f0a080708060103 68
    0x69549a0130f1a980000003401c0c445029101c0c80000c1c062910807500600c4a14100420a010030041c078074400c0c41140032071300c143c2c4452072821040c1c422004c0c10300b10250010700010414185204402110b0022006104988016110448051401c892030140c0140c3e80c15070390402003117141c104001ea83c490420ba0150205502d550744112100d048000780c80d680000908985c41d40c00c100e5880302d844d4401c00d055010b0035003444000d480d01d41400b0b02a50503803125840011480e54020f0101c6030300c03884a0303050589003c031700520403201d42c500c0348203400322401803000000100d0150809404030044a5800b9011040c66182450402491a00906009090104002000c80a00169484282c054880c151400005d04c41c21381400101c0450b1503002c580030301c01207801c0e540d2001508558006a070484080c030034940c0150381803595558001c20704c0d8022480c0c00000392040a08450100c010309107035050054541c20000c1c6c1c0d403c40d42968002032803020801c28059448002a50846428207040103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 676891061 1250 676889811 676889849
    0x911090d060b181302040b0a061b050106171f06120f051c120e16031b0f060e030c0d0206030105040c050f07120917070e0c0d0905030d06 60
    0xe422660500c040c08056a403108440c86440320b04034034102405002510540d454100c00b01030129000300c42c2a03000703a03d86000f40c842800d01c104100c0917202d40391581d00d0410030074503030a070780700000c20303800c0700c682d52100400200900d0b40854140c00c41d100c02d001d08a40745034180190300c00200d03840c240860a041c40c20070000504442440d403a415082440703080d9510701c505100349030901d56030002c3e03108401d20440d007501640c4450b00c80e013980f210010511242e40b00c41e800c10b81e150007000b0580d4200301294000c1001441c1104c09040b02c00d8458010030000d81d4a04031200d04c414a64030900101c2e034a02400040c515042c40940090717001100d500c0c1c10409207401052032400140101c42c00b42c0d40c0c40004c8803046008100341c40b00c2165030705030300d551807180345481405040e65080f004d011500e40140402c0a0700c000036a809020384000082800d18908181e42c1d0000c0700140903030360204400c2010341140d100c240125040b00d80030310010359603100e4000007107080341c0c043c3d0b20540c0c0700440c110101c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 676892311 1250 676891061 676891069
    0x13050f060409020303072a08070b0313020d141011031003020f1c060b010201110c0d030528060e060613030206090f030a030309020316062f16091109 65
    0x15000384060340e00081c068003070b01c0484c0c40c4d8499540c020308500b20510300426a01c9100008010060440c0240f000b0305035078000303032079990415024605140c81c0c14000940707001c5810961281a5000030421103144561b6181c03202c440884032500b90b07050f003119840000328601d038060680f0070014100711500d5454110399160800103940402846425056400f5249654071015005001495001c0505640762032400c0001131804a44246c00365013031070348042940d80303043c00365038001d400e80c0003a0442400140c411002000e00800e1266118100d04580c51091804c0201c40d4600d0047c03400012082c0c1414031070103070710308000c0c0040d01c00c02003003000c1c0b864100c40d04041000c495068400f01e86035803203100000c080048082c14180c140c8682071500041c968560400c1d0489402134090341c02d50540c46101241d2108640960380101e0400301c0004442d001a03001c100002136640c44e0300c0114100003844a0a0100c15400d01101070080d00c4203002d10702d401d105c1d12000300c13031070500146002030450100f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 676893561 1250 676892311 676892341
    0x140f0c12060a050c040f0b090307120305070b0408072a0f27090609030c12050403020d021327140a050d050a030b06190e150f130305120301051305 64
    0x66491a0344030380116210654800658001d04140c1110791403458944800e003580d5044041e01e00d20900c42c2b030701d00040490001c0703503208490b41c03d031b600c062810b2200e48942208040240049905a07010864440400c1c44060702c2140803210144001903810044008690300030329811049080024410811080c003050701040501f0384000c0c10070380c0c2c10344580f51050050513002c401400d607078100b082c0e0703c00f00369010002401181c405d001080d8480b05c401c10403240d43c0614000250402d644155803001f40c0f800944680c1c4404850101241c1c807014205810662010a0a0341d89002c880344542030802c600c0b2031403070705001c12407002014108034540b5515030b40c0108072100818440001990a0042c0c0710b9009007103c1c0c90003403e00c3da50380c2d581030b0b040d940b4102c120081030002003d01041c8003d0f860a8071a09881c44030703998455007040c00f400e08441040e404002c101c0b5420f40c0d4610000f001450030721440402e451941c9801d600d0750714000a1040b0410404030302c80603507140001b003202c01c40700f032008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 676894811 1250 676893561 676893571
    0xa051206010e030c0d26040812090a05010c06090c09020405011103030c0a0c170705060109110c06160504050a0305030a14131406041e03050f011505090a0603140f0c1206 74
    0x20b014202c0f6054140740101494409a80760541b251b902a001e0a004000003401115032400031202c299060150052250040b200b100d0346c4407280b904200a958483c0c070046461500400001540e92455070302c883c0b075040254001e0140b40d40102c0c3c100140d40e04107140d808500c80440285142d4500014003101a1103010368040c18800c13501800420302203d2142c0c141c80302d001407822170750380419040181d500c0710248034000549052840c904444038103c1c0980388201c3c0c002005080ca80c66000808400382a20195001003003c18400001c0c25500c0025003401035015030003641c1e1f20550103100510380d8175800801c0c48000c2e41080b0303103404180f03695100304c1110080004002003c48100c00544c080c402e0740e00c03183c09100700c0b020501001e0007a14004080b85d2040d0121040c1e04142c81c00f160a9641c0814005000200300d001000700e03091504005078010a0f039440080d04c140c603a9a5503610340d0b080e42ca581c00d940d108210710310140c401000b80c66440c071000c8075500514044e1000a950710304002f44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 676896061 1250 676894811 676894819
    0x6030307030813140619060b09010f0f034505030403030e030c060a0f02061f0902030c13060c060605180705070507080f0f150c040501230a051206010e030c 68
    0x8101002d208041c001c5090035001304007619641d0030003081e4034a13a81d5656060200d0b45107070040002c0c04a02a03021a100f910040e150020580d11035207065601403101c2078501d0525454071103600020700355010700410030081c1041d0080140024501010b942070303002441c0500d1205418601c0810000400e88049a81c1892301074004000040420705014508040c1030308640701140c090500c50b00030703040072424046513080351480d544003c1d82025004991418004812109000348642000c035002540e102441c400154504280e0401d0300c00c01b041150300c044005200110000100b00c09401000010f000403590580c1849920108490641024254105001002403018200301c0d0038403007040240305c03407420342ea11643c041c0101030300c82c0c800540103402c900508100b117509012541d0000d02403d03c03141c40303034142414400152200c0c0648080381c00304080e03042d207000e0014025001801d00c4201c075503c098403984644908a030403000074080c02d0600034440580d11250714001550445100100e07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 676897311 1250 676896061 676896091
    0x7030314031e0a0522020901170c0a06170106050406050418091202031b060906070807020f072306090d1506080f01090507050904030e090a1103090a0b060303070308 72
    0x1440e142c5550360306421408100d2001c01000311025140d03110500c100280c0e5601911038100f02282d50b41c2e4080080700075802086100184548040c1c01c40084002c800d01041305d503084034100001310600c146a0001002070a50790f00c4000c6940721207007060051065061203420300303081c414081e01134080c500499503007803a0303a90400d0b220078181d00b00c0e80308103070810f21b4030001f0b044940000b1749035844840b0000e00c1400c40c000d40001c0300e4000800c0741c07090500c0340c00b13803008cc2c960350f00c00c80b014100942248118890640340080d178940c140103001c0100741d4051320300d000790002d0000448207042501c820f0f20508040c801310034a80c9130031030383e04240f9a02000c00d40100302030038001002400702da040041c1d50702c00d007030b10541c5ca40e405600601c141802002110556a624400c100220104840090015400461506a81c240282c030705400112604001c038113541c4070300113800550412900312409620400d16181407098402c0c40c550001c20940145250090545000c0c0c1020782c050641441c00000c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 676898561 1250 676897311 676897321
    0x71b030f0e0109030206070b0702012d020f09030d0201230103030807030c0201150905060a0909120e0103060510050a1701080d050c07030204090f05010e0705090f04060b151b0703031403 81
    0x3d00c5201c3d02450b8001e100b0307903c902d03480c102500b800004507180c0d0b000d50700c2d0048101c1b00c00c0900c0308000d64030300150a400410703001c00d0286070107034204c44802100050141704190440e9070511a038034641034903900028142001081c02d040380300711400d402030008840e800500101717902070f0f94a17034409044c0c01d0121703c003000c034801280180700070103510390070000c544c00114442c4000e4010720b0081038201da500d000b43d522240e00100b16562482c1c000d0401d0b441c403d1a69105006e03015111088405040000d280d40c1e554002c9200754101540f20070005400160241c0c40c190018810ba00c1e08106800d07140142d810b02020f5a511300c03080440006020300810740850f407440410200020f07550240090100d02d0300d82c40c2080402403130321801c984550901816100c4985c000807807204a4400070034294058407110038002d013050001c1c00c243d50050b15038421250580701c1e43c0c2000b0301d2103030400c411aa20700b02942590308805401d0442080c1340c212140400210383d0186c1061f40c0c8180040400390384e0f48803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 676899811 1250 676898561 676898567
    0x1014060a0807020a020a06350f071b060504061401030c050609060708040b0304030f050a0503040f11090712061d07081021030f02150c0d060b0c0105071b030f0e01 71
    0x803075000254040307010351000c20502c1c1d100406072261850440304803840c50f514088e012442100d191040703011404600000c0d0740650218803a60060038508001c001034014060358a5940c850001c15110b07e0f0711141440200481840360065501c40c0421055031541540d840307460a08081c41110b1007060040703100d9000c3d640d0801143c002c00e0344500342503690341d41d03481c081c1c80d035400456007500400c291844803607446001d0030442e80c0442aa68445103142c4c1c86655545103004890020790f00d04a850240d0003168554130141c038000c00654880c003895164116441090701d0f03c640011080d024805400c49000030450841c9412103402d04000000303985007030340d81c01c4018455102e4200c600f00c200a11016804c080b405e0308882c0e0080d6070f5407000d00d02218090b0390b540c4254000240c000316980000d54000b00390400b801300812040070100300982d43d4103c50540341c001c0784460419035950340c20300c4000b5802c0106584403040403010014521f106403000707461266003e2401050241e88240450b60741e01c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 676901061 1250 676899811 676899823
    0x172b050712022d16051e0a080322140a0c09061202040e01090b2a12061e130501080601090c17040c0b0403060212090102030c0403021e04090b1014060a080702 69
    0x401d22202c2000c41941010f03950784a280b0300107400340f003521242c20031300100403c46645035500011b91601c9c40e00c07001d048404440210044000b0405044001c0c0700103010864884011504100200403016250803c044951000d9001024032480d00c0c2c81040f81031070131403d10303030310340d030101d500080003110141c1103800f42104510003849100040c00300050a251078101d049810008004414200c0c40d1a40307052103841980700504000c1c01d003e0001d0214548100100ca02c80e544400d840e80700c20a00d80403131140b80340140140c071407940341c100502c0801e10802105005192080051241a1403d04d01034410903411504d5141051081d001a00348000480001e00904403032a03c150b4540e502d086c400000c0d0801503000701950404004101c1c2050140241c0b402001d28140d4903240c54510790130058500c0000000400c2581d17848203c40f01592140300f103103103160248d0702503402c2c0c0c0b80044a007001c00245d0b4015411400e45155040c00a880b003509840352824607080084107520f40000903490300c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 676902311 1250 676901061 676901077
    0xe0a0503070b03040816031d06030601092903010609090f0207240608030d05060907020c01120e010f06090b01080c04030b010e060102010f0911040b090103172b050712022d 75
    0x110301100101050b500210325123021094898070a8681c2c1643c0800042e8032040c1e4455000411045003401026408011044900c8408100c5042864120304140c0d80c0e4109074040408a42100350400c071440b40e90168801c00003c0d00301c11441c00043d65144000d101c0031401300c425584e84d240041c8482c0303c055100f00064400c0c0310032213481c0c052062064010f80822101c2d180110991030200b20b0050000501032605a0161900000c1d03015000301c2d00000c02e007900100304a99260150310050014501c2460060403103400080b075000c16410025180d904060196020080d00b00802c02c0800c1a02250030706543d1007554040450700c030000100d000d072101c0400940000d160001a1003003000c03145101440303c805681c18404680040c0c1003048846003444003805203801250001502554a0000d040829101e03d910b40745038171884000ac09010000c1e8400c0146a65500b404140c54000c1c07103165002401c42c5080d4070700980c15009284400c0d441e400c40c1c4440741080c40c1c2c03000c42802d00b003c2d60f250f8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 676903561 1250 676902311 676902337
    0x4051507050d09230d080c1c061401030e030a02030702010c03141602090c0702010e0607050a24050a050105061204020a051818030304020d1403040509010b0a0e0a0503070b030408 78
    0xca84c00c0c8031944841820a4a0350300f1242c031004c0d8940c2c400403500310701e04202611341110f1b9644440c0403401c294001c1195407003000c070300426003402c0c9403140709440180c43d601d03d1002c080e4510038009002c54481c00c0f2500c145500502602a9030b40d070000483e1684c55081c80e0a00300014a03140654100100d030680e0003a4020108103020036445100d049080503000722030a400546a0504107003092013900d0001e40003400681180c08942045e5001f0864513110300c0854807401060744070720400d08030f150b45d028500b040107c0c410000f001580a8150000000d4004104651429002a945110702d5070f200f00480e640703e000030159901c0d6050b80c00100000340070155480e0702c07080404024041180d0b80000035100410040e08500004103480c400d560150803080c0340b801545902010b0041c01207001c4c401d1000f000b02003aa52100c0c130480d8004e109003100c9035202c038201c070800380000c0305a4946d1405505401c000300415540004c0f62000c9510302141103030f481d100c0e410a14014400d0341e00e0720003d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 676904811 1250 676903561 676903571
    0x5030a11190f270f0218040507020d0810031202160f24111b01021603030e2209320d0e0a051809060a02160209090f06090105090d030504051507050d 65
    0x80d9500b180c00411b40c026030388000351841000c0104100c03c403801a1900c1c2c005a0001500c0c41505004203012500700d0ba0f9003000c10b903810354940d6500134029600007000c00580090f44c04920907100040d600c4051301025101a56041c10070050070303461a0080142107103401007c00d011a014020584a00c15003ca00300340d801c680400c076441d0200e194500c11141c0188902c401981d602082c46161105a0340c0c0340da01c5119201c640010810310a0301032490300303191000249414011840d500c20a201548a01c4641000c01c48810700940c0b10f4031007851004a910210220345501080410b618040042a00f454041c0c0041b480100714a00c42d91303084075401c103c0c0390140c0c0c2c5182001c64021845999150b041b20010781e078450303011050b4080c2602036590021607182e40801858a82c8900382e000e03407040119414542000036140c5813440035031342004643d5403101840120102480f44c40641c62140c00c0601050078566a034030303900c45103442101004180e010100b01c80a1161080354404c452500e01408 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 676906061 1250 676904811 676904831
    0xd120318080a12050606030c0a09180605090906040203060408030a0908030a020d0e07030c09050c2b0e15040210020a14030a0207050406060c150605030a11190f27 71
    0x711036016156880124010700341c0800d22010034012140f09000151005042da1684030b29050741c1d4200c5c1c001c9800b4002101c0001c184404484082e2502040c0d102011440303a1820042c401c1c0310f2006440702001d038010004020260f1030006009400940c07200c3c0700c560303d540d0741400400400580100030b002180001c01c0c0202210650007805841c030002d1007c016808401050598900721440010b14240314440100440d011070b030702095204c041d070500c6c00c0c40d000d0003080440107031a1080c3c01409007200e0301c081d9003500030b40c0d200b15030356808050300030134000c20300d410401d0170b035480208000d02c502100803580c18170920130300c0420301403a80401030501c040d0200c1242522034100d0840d240c0140700324a400216482c00303002c0d5400721a842d460307403080b2420944440c0da00081e9081018406900c464001440e520100700944802d40100726842840e8404e070100021540400412502145441d100303022464114004c002110301c1091022200c108640d0525815104002c00c4100306240400881c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 676907311 1250 676906061 676906073
    0x60f09071a030405010b0a08060f100e04081e0f0d021b06072c061207030b1f0909050f07050a02010f0f0507081023010509030a06060315050103020d120318 68
    0x1030043e8422002800306480c90014440c1800d1944100b1038940c0c460b0f00410b506403070100401d40c115802c44d81c0212041e40702da501c000c00e1001940d085a8100c40091039040d0740c9460f106031003022003421402e0b4a40f409034910b0001a01800d4603090045170f00080c0300003205107000024000100c50b83c1551400d1404c100041c0280701e07004001055090386800d0510081200700103202800c00041c2031a00384690f614982c0c041000003803c90041c0760303030340326401d08030381e03c045121801040c080c21203900314400d030708002e20018241d03100c1c1456034109402e02140c10322710560281e115100c0d140054659204a0041b4050407501c10702c180c0391481c00d400340b12071400c0f0b0f4100074406c0e0425200d48580d40ca46000300c1a408003540304040401010b401c84095400b07080203440c1c0e9010052400a05003001c1748002400c003004a1401c880085d43c0350020420058403a00401d0303071000c5030380f00300f24544c91500402c445418100e00103084000640080d03060600036401400c180104104280405100d89842 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 676908561 1250 676907311 676907317
    0xf0405031009020307120f060902030a050f0102031602010e0a080705031b0604020103060506070b010e070c080408060610021207020126070206060306101a1e0f0a0f090305060f09071a 80
    0x60b8005d0113a0540880d44d404102410311202d07a0045141c0d80b24181a29810000c040c1000e040340c0c140520072442000c00c0d001c021280003115584001aa0303070900d00c451803014000c807401601564101204481585808500890303c3c45c0c00552981c2d41d0401c80c5012429441103540b000c92041105414641c403180000c0c64502c610301c00e88080180c107883d0010815207005132400284152522801441103000f400f4000d5000045801c15032180350282d50b42c0d01c8181c1003900513100550082040100a00d0503400101c01a105400906a0171042d040c2d409254130908001038140306201c440316109a60402c115a00d4040300c9081c4552030801c4a002501d40f0420340b640e80c881e2040c6004501e103c80501100000c840340c0b0741d01d54030340301a01c0300c0000084d0070246101c071060b104040a46040d000c400004e15460b81c60022455403181c0d1448040c0c0300488a408c01c0040005489040c400a0800103695401141400310100daa40e150b07034060b031400c81180c00030151016040c10b50f040c0d100500c0c000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 676909811 1250 676908561 676908563
    0xe090408040602101e0b0a0b0c160609060206010b030c1c0b0405010e10032603040f14011e0b03010e07060203040302010809240405010e071202090a060b0a050f0405031009 75
    0x4c0c0c1d0414076201c14048143c446140410344522404214400341d081c46601c01421440d0280007402d51360b943d1a071305000c542000c1c403084015044101075844141117400000d01409440c02d1039007045060841c029a90081402958002d11001001ca41141c8030701d42aa088042801012515914001c80c684040d04050407054002c40c1000000b14a0100b410842d0b0312922603064110300c840d00e1078507440800f540d198050f1142c440007200203285031109074000c5209900030030003042c00140360b15124588108540c030308441a407404c1807203c18400d42c240d039648a11161000824001d03809400640141040e41d00c900c031510400c000040e4058001c006401101e000742c880da50300c1d80c1ca00e0131aa48580d9440880c2103007803510074298a400303102c0074003150418054400000d0b00f0701090b4806241c40c055400c207540c0165840354900031840c202d0340590344920084c50a11400386441585407080c081c0b20541020b001c0c010071007807081c0910005a4008040007001c840880405d5000c482c014154100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 676911061 1250 676909811 676909813
    0x50307170a021909060f18031a070206160815060903010e0c12071d10150804060b04020a0f211503060b060307080c0d0b04020d0e0f0109050c100e090408040602 70
    0x75525405070140c000041200d000d40c0f140e00080205940032201d0001f01424071942d46400c1e03002001168500100d031a01c021005510005420b082034082d00d05400204108080d00c00b609104d80c600e40e01c03220380c0c1d40000a05a02d04e004241003000601c903405600c89054040d0303c1c00c44490082c55002460700810071040c0c80d01002010104601a2203200c1405000c0459110040b818901162000041d5101200c2c0c507083d135405444800c501d460070708003501000020480350500c000e10542c1e10482d000b1101c115003c41c60442a2940a046200e032100318000b03001c080340386002c070703208020000e80d50b80a000c6000c01c4000810f103c00a5589001e000035100e1502e065203a0b0018200141128001c003110748840000f40d444a80035101c50740104429194aa103418600d1500d449034005444480440e41c0003088604a0312181d0785800d00ac2d18401c140380c4e05207404c100120710041200c03604400c081d40c00d48aa01030000c2c066409a9400c04c8072a003094049081006020082019009481c0254 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 676912311 1250 676911061 676911097
    0x4150203090105010504060518150109030807030801050301060b07110904110406061e0f170910050406050a0e030a120f020415020601060906020c0643110619050307170a02 75
    0xc0103220045545172202700301c440c5404045800c00000c0c1000c109520014908801780c0741d01c030303900c40810f5006805c084020520110040c0910716080c05036002810540006904058460b15003291081c800000507002d03102d000045800d004104801040c030b15000b601c1400015900c020040c00c61a0441c1c200f40c2d401c0d0320203c4000320501c01c0c04d0380f2521344504c0d0340e066954510788042901e00c0c0d001810991940c4a0354140d030b00c82da0881e000c6d00d0b1017180070f980d00142c5464100010429101d08107102500d6410800c145103c50b80c000040e0000801c0d540c400043c01c040e03e010000080c8030b6034220000da0046c2003040c17020b441e40001c81034141e80342c40d40d41c8080c041d5030f2902070381e13110412481941d000c0030520509140402c42101820800703a8852400c14140983d641501e284103050f1a090502a0605000e024400c1141d10181c81080c15105185054541071402c0004d01000003a40d08102d400404070710303040d00c40c540c0c8000e248044068a02207042c06002000291b105003408081609070f2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 676913561 1250 676912311 676912319
    0x91801060504090515070e0d0311061f14060c0604081b010513030e0d0b07030c0906051623070b03100e04030c140325020411040f0504050415020309010501050406 71
    0xb0740506102c0301e600c10024017943c1000d00c20a89513800080074001040081800c03000640c0c1c0300d0416041243c02a141c0b6546046a004440d0030b002d001091810205408415400d0343c140c00302107038048407900341041c2e40d05e000450000e0344a08c504a00c80d00b007071084005100500c03000500400461040351041510840c801c8001400d9480c11111101100c80381d80c441340200c0e00841120000c01c00041050362030700307050f658400d6001d5050380c140e40041d80e10300c030300d0600b036420440c0380c0040d00c52810042d0510b01c17286240c9400601c960801001d07141c5141115565440c099211111525540c0a0390038064440e94204a981c104441003016640f40704030000d0004203c040c2c85002e25059501c2000d0142e05443c0d1a42d1410318080301103191200b00031070083c0a0700e0008070f03d408041204031400d40003140c010071040e00e8000c0c1641d000001c0800c010412880140c3d08401100d6003a1004201aa140e0925455004403144600c1c1142d0001082105c41c03641940b00c6416500101d070100400c90b11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 676914811 1250 676913561 676913569
    0x80c0f030f0315120c09070e0607050d0f230a0201110d050601180509040f020f030f060105190b0307122003040c06140d0f0603050307050715031505040c09050918010605 74
    0x24400318500700c0d400405849240c1d003081c03040994025183c1c140107522040101c081419540803100644050704003146020cd42640010980032018443c58074000401d0440b502d80402620010b4001001c0d4000070000c07540e81c006c0d00000189103404450540390340301050160090103048640a0029550000b0b000c070540e151001b25094800103050710301255282d075950007801c8806d081c01c0e60310070203298103d00155020000f60250140420260105500d02800e01c0300700389624001031200e01500c001400311219620540f9485210392411605219001c041900204588145828040e1514140d90388042d03440c00118000c0b84111600c480c8075a803070744115200c2e0140440c20343d030f410080004c10560311050b0820307088071000010014200d550307503503003c0c80c40d4000700c01210b054002d000c1c00c0010103111381c090b1461144906003032161404149041c00001414020f2030720440e41d4484403c68240704505820190001404422540c1051050100a4416800076040d10b42c2000c1003c245814 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 676916061 1250 676914811 676914829
    0x709090b01061103180907170a0e01050903160209100305010c08090f0115060309020a05040e0105071701050307170319051801091a0a140d0c1e0804080c0f030f0315 72
    0x208074908800403d650400c01030100360180c14041007001c000000003508803c08c2000c1e020344440b00c40050302000e488082d5085d00c5009004968682003440310820840072a0845040280d04551030306c1c05985c0ca00842c00480c100e40c102400a41c60541c001d03003040c0e000f00020303014221708022901c100310701034221750980e408a410f18010314060b0000300318980c002e401802070f0030302c02051200e00302c0c0c41d0004242142e100c0900381240740c0d1968148500150003840000e00424002e1080c80b1641c1000b0100743d5529082c420210b8042c0490400051b48001b8801e90700540803444030314605004071600105250418081d582e2421034284d01c0c181150300907141141210a08180b28400480681120009811075040c22050000440f03504d6081d4200038000d003080020b4140010f1078501022005010a041580341800c90612400b040f45054125030101d038070948c46401c1c0c0d9078624a1500700c81c10000b080c0380400c1c0130301c00812181c604907240f20146100741c050606c1a20604905c400f00300c1d07002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 676917311 1250 676916061 676916077
    0x9090201110a03140c0a0204050a090b06100203221203090e1008100b060c060109020d0b01090620120a110d08040c060c03020307150c080603010507200709090b01061103 74
    0x4e4902404440900c0c2040080d100310f0042c001130710f100c1d084d55000305023500d9003100c40e0171415036208003080402526510b000c0d040b40b401d8503034059000340e052001c0e40d00e104503811101440d05a89001e5524840c00403040040c010300b5040c540d16500c42e01e00500840c1d154080e80c2c003007040724400101100c0c419202801202c500c40014450f8010440c980d60041c0614003c883e044070b01001513101c01e032000c1140e14000e010340f1400503030302e0603104500012204007852460400013289810006c10340d0004000341ba08401d0300c40e02c001d0e040c00f82e040a140c185a03155003021080003041c0c0c0c6d1200303a008400700441403c080b080da015034010007000c03501e2407400c0303d000f044506040c06c01e0002c60b12840168a00900c20300441e4507254694444001c00c41848070708040440d02c81c080b1640703150b803001c01c05400600035802070041c2d0a1190700580043d41e1441034155070510441600f07903a00e401c000314802030004031420420881031b0705100010607070034050750000c10041d89005200341000021101c010b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 676918561 1250 676917311 676917317
    0xc1e0f0d0f1b0e0f190819050c0103050f0103110316080f07170307030507030219060b010e0f0108011404060e070305010f0b120708091e06010f051203030703090201110709090201110a03 81
    0x303802404e04101e0f0085441c842c1c030940d14801800071441d032a00f0013011045c2c00c01c1c80d05190601c07000d45081c500e0290702030f0b007403410141850140b06240c0000e900407415664069010749140c1d00850200b40742180c545070b0054244204540020150404104044220355120940d51a02c0d01d0b003100321903c041a81c4079002e03030380c005c1101002081c410006003041600c6407064481e00c103440d004200003180c0941c42928503542c3c80e5464040342d83c02150300b140030b10095683c1c0c03583c0e107014000a801c80d5014031030542110b03150600511030740e40da42d100a000d0900b200c0d03041c02038140080e00800400c02405004600608002c0c08141a044581a1100310210300e2150b4144e950b1b85504550b0220083c000c4441407081000c02342d10130b448184004c0380007402c500144500e6160148080b8041c103140c0c0007601500c0007125010032800040200c0740d00240310b0801090300d01481c03004072845900e40031010501d008c0c020300800e80c29807503002ba103e124000da031819074001d495916240c940c0005139004000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 676919811 1250 676918561 676918579
    0x604061e06051c0e06071d0f040b03120f030103140715050a032705010606050406140a17090109290403030b030304170f060c1e0f0d0f1b0e 61
    0x115114034014070701e002c41485034030b000600f11060401501c400143c0130b982e80e04203034100000c440c0c0c4030b801078501c4640714040002003101307000410321302103480c81210b004070f486005214543c0c904005a9885c240c0b00c0721a20394900b10000c100e21507030402e00044035540c04d605056514072500040e0760094811f403a004000c82075030103500b03a426038045030010341416203a0305950120710b980e0200051401104024080300b40382d80c45c100d821640e441c2c11070b10034000e0a100a208442d4441044801d400810401d1565601d08020555801c3e0514402e4031004038610204501140c06400206030b2078030800340d034440150050106a180a54003100c0c0000f001d8003400500828402c2e005400002c4010b41628601a20b6228604d0101a01810400306510110b291140d41404003c401e03440b4003141030981c1004d800001485128010034103500c0210808031700320030800702441c00c070352110070256010000f0844007041140942419000c2d003043e4080c10240461a038001c07150b065003c00f008002c840c2d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 676921061 1250 676919811 676919819
    0x20a120203060a05060d0207022803260c030d060e04020607061814010204030c050a030506070810050a0f060305180613030c0210090e0a0207030516030512040305030604061e 76
    0x250401021240c0c020380c03e00c40082e55031603440041440c0143c900300980d4401850050000c42c003982c0468a03a0b0300542c80b0f0200d0f94007401046802503d07441241c8174151800c0c0f00318040d0300300d1102ca034015605000210186902e400000400e0301c600155070a0010781e96802e032070000150201c034065089442004a100015007503886070310042480b011840880145450b00082070700c03501400021603500003818002c0c010340d180580000c00040f68010034107400c5590b150f40b00d14019201c442030110400c0030a0360f81030078800040152a000d008a60a0350390380342c25035001d8209205000101c1d16020100302c1c08a80300c690900314032a1030b80208501d4030b45100044004c0d071403607019410003200c080c034900141e0384d920b0b54104e450b46540c2c40c2107055040c0f200d40c10b581034016101000440c810465200060707040340965950504201604a41400760704042d582c074071500d90070070507400900701003000705a003000246000b2541034904100541e19800d16080740e1084100c00302444030281d00c100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 676922311 1250 676921061 676921097
    0x4050d032607050301140301061410110d170a0513120c0609050c0a080a0317060f0306041a070306061b1e030e011728020f04060c020a0504020a 63
    0x10707200703040703402281c0701503041e52548440c504107499000004000000401100e44113003690034003407034110020001103240101406a54850000c4036005403134004a01401074040e808a440480b9400c098400d550243c400091203064a078811485003034000000c80d00941c0288280d601c5000004d41c81107880724680c558100380c0002404090400000c401d050300002e02c7c0d4000d8000d40c0384200001d00e02503901d00b04001c07594003d90030609059200b4001000405d5000010620707802c2c5c412021050f03501e581c000300b42c1c035401e9829000c0c1c1602c125400d20041229015203828034020240c90540261944d4508809403031881c41154002121112403218590041415041e1584140e4040500300c01084100c90350004034903054011451000182e903d40d40c004000c14030000541c0408003180c0b03065620750709100728038401034401d22580c0a6280342e00a0b2070381142d10038001e66600c140c0b103035587e00c801410105994400c9000380c40c01d1800251509282c000c0d10080e4800b52a8195041c8428480c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 676923561 1250 676922311 676922327
    0x80613031e0804140f0d030615080c07060f180f020109060503010f030b19090302060f06060304120522141f08011a070629030c030c0d02040906060e16030204050d03 72
    0x118041c040c038141011791503410403170b280c1c103d0410b07100070490910300b4a07906103000800c42441c0a0020100801c44400070030300456540f00d9015100142c1c480c3d180c00710070010003005001c440c24080c1c502441c0140314150b1113000185200342d982224241c1c580c0421103090000384141061448045002d2000404040c85540d10030801d59640c00407030700c64850f00040e20036036801a405038014409200124641021b0350b81d201c01c0175a8014550f00b06a52850042c09010094104103d808100e41144030000c2c5488070744128114110203242e03450720006000012000b1f4014440c400080f600d1f070303e651506945940e40030f0b031a29002d910f40e1a154030921810203410311440720315002c2040784009029481004c00e100b00c60900c03601300030030305c02031038444281002100d80710b0703804061241c6e007540d00064800d114100988035401c0c806144e10124014142055009008506110b000709150410030403292040702901100c1900c05c042150a400301e00c0703140034454126001e8040c14010902030488 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 676924811 1250 676923561 676923593
    0x30c03070b09011d031504030906080103051005041b080303010f0602010509060604180c080304181b0f1b11030d1d010c0f140c03010c02070f031b080613031e0804 71
    0x4130029150490000a0805840b0021403264074005000d020034180e0205005010302041d08106c881541035450ba0340d036600500c41a070240c1ca4555002500700714940600c5024001d0701e44401c4580c0351504030043d200c2d04240103041003100d9880c80001d5103441409a40e008440710f0307010f0212902d80e8820b00c00500720440980303084110101e4010002410380800000401201d0042c0d51214144001441c02e000d601c00702d07200050401c4450b03200c44581000c000f94803590b90a061420118084045e10100e1035034a282162218020354802404545078800b00340440440c10350b41c42814508040e92408002611f07850740729201c09954401d54000d54034103892a0054041c1f43c1403c9451743c0e00012814040d00d00c2c8e14a800481d40070a41e82424050948105070900142224a051081c0401c01c44654400600514040c100400284021180784d001500380103058481c5454030310800907030382e44541000c80025449a52040c180c480c8031040d00e0003403100303507100c4819883c0e81e2180c441c16660426 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 676926061 1250 676924811 676924847
    0x400b0c070b012313090b061f200d02060906010609081002070201020a02130e06250e0a150203031b070b040f020109080613051002040f1a070c0f05030c03070b0901 71
    0x14011003e079640b1040c0c0500d4810009000c190f24480d85041c0c0d84445020701801d004810000c1c0c08c0c1100780e0490400162074595240016903078030100d12401c1a03141841e03800c0e03e140614001c91420581c00b00d41c191286480000701d4003a40d03aa40384c11680c0f0300c035900c00d0220903000048041c2c0e102e400d0b40c00901400340148101d589407003140d00000e0195039408440258965a940f125060640a102c241d0303100600e064014400c400d4000300950740c4030780107420310030404100c400420603650085042c0261002c0002102400140b0700080e50300d82c41070782e0a1107a10290789061300164440340807907250700c0d44400440c1c800c1c0c07219034a0031407202d13080c3c0e0200d052114003000441c172003d0030800c10b4807904074070708041c00d100e465003415420841000350383c80000b0f00400040c01622840d4110004444403107201038107000300503002e1a41e90140a0000b000d40f01032100006030540e441e60080c0544900b1001c1d5034141131002d0415646c0c10851250030030b0300c0389c1448200020b6000d034000d00d1223001811 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 676927311 1250 676926061 676926119
    0xd140f0720180c09120a051b19050d11061e0316090e0402090403020f070906170a0c030602090402070204020f070605070206040b400b0c070b01 63
    0x203900d01e006100511426205604815140c1c045482d08001200c0c1284801520070014100000c1d6040c1601c02d4441c200d000b5484602d201c11117240c01c000440100307800c54107540601468020a4820240d2644101e216800c04280d0100e004101d600c05000c85600409000780c1c10540c0c1d03145218585401c0303000d640110240f002621803600100baa0940c21400c9200b25901d2400d5103524a88003000e2510100b0000c0385002488800c031170241c01c07a04590120741220880d50703540f90072450011844072241e0680500c000004a0300f0b110342081003a01c002030721003104c81d001460382076034441c1005005098806003600c108041060b03a8002c000000300034001504c2d050b40e640220b82130360b0200c0e001551340d084c000350a42c244460b61181607041031040c405000f481c1841e8591980000f400341154503075403800c404640d100020300441240d030642030707800c48030341e03441e1101c804603161581901500d100c289400025501000300c8215a0000d510102091a07642000e041e548528015a500c01141c10b00c070b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 676928561 1250 676927311 676927313
    0x2e0b060c060103030216030206091201020f040e0103151b030509010b0409050303010512070303020a1401140c120a02040605040911040816080f03040b0702040213270b030d140f07 78
    0x40014510400c2100003404503500d035140c02450694080030a640429241e10140010f80ea0755003100c030080310071a804010f020250710460b0080c802c0400a84e03039417400041c00261860090807a90489001e4075040d25025422007201c0c0c26505a54510200c2070b0701e05407180760300750081c0d22464110610703d0001070010711141c0454100c0f41c620006454030f520203c0100414684105050801c88550010b0000d161440d5801382d503c20340144024404a044540e24900750030960201c0340c0302201d4030710b071001410b1509a03190264000b06904a0204030140005c910074400d0007114111211136079441e14291426600e01d000b040d13041c0c0da482522004100006a1810030400715040021041c00c40c4901c81ca8070b07a640349040c29401030045541c00501c4104083c607806016170300310603016140983d4809000b1400c0803040f0003900444214001d000303886508c08000003821203400c995007800c0041c1700034a800c150b603480001080713100040c0b002107840c0321003a071038000d007a0381804107546500340506 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 676929811 1250 676928561 676928569
    0x105041e05013003020c010507080904050c180307030b06101e020319170601140912011509060e0403051e03011d01060e0d0b071419112e0b 61
    0x81e80034842082c1110740e842c40184003c60b0815000540003166101000180d0f0040c0d2248004180141440b00100c0c50105000150b003c071400060000e0003041103290507108070070a81c100072641024142c1000805400303007000036502c01500d4111031540000d580308070130080c070707004600380b02c42c1045142005084020140e018400ca9105650083c0d61541c4040b80300030000c442c4210340c00c0c10801d11006980c0a0340038000600c0d000792081c0b0700444c14071710018549546209004280b5049074000c0c1c0746005421040d0b04c070707417800311680e00f4400c4403580c0c602100c41901c0d00c60013001440541d01c030220740064081d2009080da41c090041c80498001e00741400500750700241c3c448039520090f49440004040b08404043c090031050919040001e24003000c68520100a0b400800c462068804240824003650b20b50400035030b6000511740d9440c83c1c50800301c0d00401f46141c0004101041c1a0802d8120040b40e62556040c80c0d480348a4406000f58402c10012004203880240c1a1764030f0f072501050715 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 676931061 1250 676929811 676929821
    0x1e14062202030a0b01080f0c0f030402041d06011811030c0322030503061822150c0c060c0509130c2610080c1c0615030f060501060807080105041e 64
    0x1c3c42400903041580100140600310000c0640c03200d45040410441c0a411040c02d1320050808806c100e901da58071840802c1c028030071039422030710080c0c143c0a03075880300800240e8035050b101c0c2c40503010081454880c410341501c0d000039000e070042c00c01f440041c500c130410402440d0f002d2600c00c43c141c07a9000d1441555409080300009a0010390004200300b1a42480c00c07002014111490750f86455280002403041c0e0b18903100d5505921210b0f5403011820302c00300100d908179200408108100754403001c0c2000c0c4c41c444640f0000c0740e0041c103100303070401c07424024001d0b0b984c011809402108090007035003c0700300406da103c0e08042400403c1516000d0703540c00c00503200920181f04580541810030201400e000b41c620707402a40d1079800800500b103652076a180c51554a03500c5884540040101d2510340054030032000c8104c02d80a40c0d51000042c84450046d0500140c0079000c2003126036201c210858500408403802c2c004101d46600400007410581e00c0b04000d500500030145c00a1050b80206043d60 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 676932311 1250 676931061 676931071
    0x5011d04050c0c19021c03090e07020f010e01050f010513231f0302150f0d0f0c120506060304140a05010e030a1803050604140f0a061e1406220203 64
    0x440041100f400760541002070000d507021020120742004030790b50001d507809004d14508140000c1c0c0004078000c041c01499000c01602580c00900740c44d2404000080d039420080c01044900e44c20064005d0040c603041c0301d0240168080025400b09030309050a0290002c1c44002a8184075599041040e6404425074000d0640b040c02d00f40580c2c600b04a00e884081d060707808048407003031b180c1c1c8038200b0040c0e680300d41d5410010381e55040d0580303a1000c000200c110b8014608020202410640d4601c685899507000e0102d003403042e16000005110401c825045560860700c17581c01440420100b0081202c440524000e003401804a440700c44007503450310f095802243c480319840d070002c10001c29079a0401b00382920000d04081000000d855a2140c1da518000600040c0207252040f42440010304144140710016401c00c080710707880c070350300d1911301c004102002503030314180628168440d413103406018124030605821408401611407004201c42412080f29040280e8150f4240d08068503807030014600c19 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 676933561 1250 676932311 676932331
    0x2004090504020f03030a0e0405070c0c0803070b0c0a080c0d09020d03080105090705090325120f0c090c020d03240f09060504020f072015091005090a05011d0405 70
    0x2070070244103008240c0803100c0504d10035007003403000749103081d031114480000d1101281c0105d0349880390401604e040210030405010303200c0b0f0000100b0400700000003064a03e10500b548410303903680d803e15150600808540ca40000ca0040200302c2060598018041004030214000303580d5407564006120101d5400701203000c42c103004010040d920306805095130011050910500e4040c845001076141c8590610305d03404a00003405007000340c0b401a5510000d45141d000310003404459003890112142000307001c0342c5a18400501007840c1e111401006403d10141d00200404002000b0540181589001c050f20301403948200d1003501c803051403600000d141e8030390800b000905000d50b517010740d101c1e41c024a004600400101d60350341c0d4804201d4040382d4001c0f00c07442c130f2020003140c0c4004204424952580c030061100c480000013143c0b40c01051459801c5a0014980840000644807030080144141c0d1095005004020a5010390100d060004c512529200c1c0100c0050014049880c10703100d000f00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 676934811 1250 676933561 676933571
    0x1d0604030f0908030f1b0717160e0f0915161412040b15190905090a0203120c01060504060927020a030f0204090c0306051905041104200409 61
    0x14181c00800211400038a40b81c1401d6581c00c2103503283d40c078440c0071803100c1c10050020b00303000c1e01484030001c2c60b02200030205950550b541c45c100c145200303444042030b0003640503040b0701101190f0742c0c1942c00c0c11030b41c0b80c40c40c64000e59100f065502c1000c0008003145c01d00d010360720100d004851101300035841800c80e044640840061018010460304202c00708900b00d40e001c00441048658a08282d6802940300403000d0307640d134480103044804031529403444d030071000c640168105c40f0000213800091f1f407504101080701c0d54801c0301507540d030900894041d40680050b02c03441c56601921008201109000001281984d50b88000c542140e15603800452503542c1d501d013169001078841840c1e0504107004004500d5054650001501d02d4854071006010309003603001d000464513643c204048040c4c0150484180d203580303041210141401f00e81c100c001054101601c0c4c6070346513501c181401141c1090041c840c002514040c080104000510321300a1440c4880820284034a000108041d0078042c8000c20 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 676936061 1250 676934811 676934813
    0x1020d0603140f160b0a0c0c091407210b01030b0316090b0306041104090606031b03050c06070503090d110a03080a0905040c0f030b130c0201020c0c04020306031902041d0604 76
    0x41001c290104500c4150800314104c8454001485a40300313481091a842c0e996011140c804d9a003042c92050040030360300844000551310740c55070322090a503c071640301020346541c0d00d9800c6410384c0c10303680e5190800489400d20352a142103907101c11118901810002012110f2100003880c180490300008a0ba4005034001e01407143c050080414805082d030007040d0b141841e80e94000e00115020f4864007a0ba505d046200c181314658010000540d0050f50118a040c4150703005c590b484610b0000380c07554807500d56181e006080c000200d400050b0000c0146081000c91801c00c0034100d8840415526a41c41c0743d0010000e40c0c1c2c1d420920001d5205600240ea2201101000781105005900203481103250103005800c0540150039446c038070f00b644c41c00064140c1c030100001c0e018a000070fa11030f0102e2810f100c0340130141e0154018000b00c8540b200300c500c542075150410050348002c5600760380640000d20440b5001c0900154550801c0c8018000b02d500803000c005201944c440d030f4604e01450380b0503400c1c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 676937311 1250 676936061 676936063
    0x307030b0613090807150f0e0a021002241816090c0f0507152a090b130b0f16032a08030106051e03070314010e06010e0d030201020d060314 61
    0x1061011400248240703d010f480380c02c8980281c40f4083c0c80700074070300c2000a00b141c140d0300038250802545002c20000200c0c2c0c0501e99944008001217000d60065011244010b0001801188042440e01d0104e0044218254110384060141440b840c950035107140c01c1e2407680503c094048103070701c1e01c40e50558624096050013541c1390042250184801441c0300390030355522904941d4850303080780d54000351520b280d02040c001c04048112031b16400c2d4043e2069000464884010a0038400d0b6856409941c1c48551404013403182c1c0c03440c02c0500c5c5002c041044000d0241c4054040035078025001402e00d000010b01030051604060700b18001549040c0090304200d500850022031060b144440f22016a00ea80f15132240c8010b0050209000001c18400c00c03403943c8418014100003094103054881c24015800f80103048909224010b00d041c000003c07440965003141503115200583d030b40c00e82e400580047c448103507446407054046540801601c6040c402500a140c011442220310081510a0158607 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 676938561 1250 676937311 676937329
    0x521010b040f0e1c020d030c020a0510020c211e070f0503040905010b0a0801060e060408150a0516020c010f030b06120103060c321210060e0609011211090307030b06 72
    0x213460182d1035a00700007960008070001c08040d1818000b401d80e416100a03844c200b50340100502520a401d40000f80300103940250034411301360b900f03c890201445640001c00c25948000c80b80a4000703102d110a1649561035030f5114030300c0c03091218138013546502c071000514a5801d0556040c2d00010b01048900f545104003401040c01011880c00c150f1a24001480c3e140113100750010003c0b1008040526034520b0304440048c0280001c84015160700240c05446500c1147c4000000c0c4c41c1c00005080a101e00602041a5126501405200312070328015100c0600c05400d11080568806080080380c1b900c0d0300400b410186881c00c03121561440c0b502e01d054420130302c8040704101c0c0c40308410350035441d44900310310310110a003446946441e54840c805803500403501341803890b400340d07014041c61080019020054403e1a036036840a508041c00780318181c030501c103480c2d0004a00000c40703854504240e100955030802c19601c0c0346020803001c00289403198540040d20f202c0500c00c180701c902d00e002902 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 676939811 1250 676938561 676938583
    0x90503161703150a150c02040c140a0329030304170106090e0604060605120c0915040606080411061c090c1a210903030f0405071d04031205010521010b040f0e 69
    0x8088101140104010007006d640c41c0002d0085844d62172251001d0300a2034508141800c040340705031580d502c0d1400074050041d03242c401580c080300c3c0e640603803004500c8864003403070380d005002145400c2c075201841c0c400d1480c9071141c0d22903550ba400302081000c054010b295284d00018001c194905103400c0080c201c441940c040d910644a0140801c3c003150b000c59000d82d182c1c400c4600c2005030b5164450240e0410800900766070152802401003036207074224410a00480c003902c8520080380c190010b0021304d02c075902c0c4801603002003003407403071416107650007000c012071042c4c0e10180d00d00cbe950341890668284183c0e45d000d4074040419100c4840c1c02e620b00440c10101ca00e0f0422156007450030750b842d00c0c3c3c80040d1030016550354502c00542440b50800503000100f1002030080e81c07034403040081928070a801d40f412000680382c00480d11381c1d011039010700d42c1030b50b4005090f098505540040c800c0c0080844420311069526007001a410381d684d8070491000ca8404000400c00e1105140100c0c02d000900740 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 676941061 1250 676939811 676939829
    0xb04031a150f0d02031005090313140901030609030e040e100e070f0509041b030303050720060c030a140a0209040b0d0327090f14010504090503161703150a 68
    0xd0200166940d03402c03002010703909803940c01c103049650003c0390504e4a078924240c6042d00300300c140502c2d290300000400d0b26200007140b00c8a02512144a1564001681101a80542d0010050010a080381c0c40b84108611a04082c100c0c0e0300b000c0c3c0400c060b9801082180480e8006010751030141138140038070720300e15801c4006404e000d82070000003004e1981034020303203020b5110003001804101c0d11030003500b140590b1501c01c025070741d03032454000c000d000300b01d85820020f41c603115040c03030b94060380d180700281c9034408011f0303c02a034845204410302d4200821101c1c0ca280c4030b5400c24031042194154500408003600c1c050780e06c4100c10244010b80d0382c0041142c1c0a450340c02c601c1c0e0081781e800b9001058440d4140100f031004c0704401d0b000600102c060308a84411880d0845900c0b080c0c5956000e80c6400e02000082c2190340e071f80d0006c1200315450140041c0c1641c10407c01c0b0116500c45d12070f40ca20a84c49140d985420701c03140b00c407000700da40040720f250b21409034046070f8148502e800c001d04001408020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 676942311 1250 676941061 676941091
    0xc050901020a060e1e030408070b030c160302100f090c05181914190e010510090e160e010603060b0f0901030911091306060f03030512100b04031a 64
    0x20000075aa10b400c0309001c0c0101c2e0ba03030182c581c07440c0300034072848060003070b149100090b16030b000088070344035841845040024403c28038000340020840066902c181050b007045401c00400d01002d011104107160110110302800c40c60807101d0056100d030340303030004612030005500011441c219011001d1a000684140c844030b40d203164482880b2100b030b51202501e00c261001195180c0b0020240819001000311121f40500b0400203001a00d00142104810481484841078a10030a0300f241c000307480402c0e11402440060001c2c12254000a90b180d07070090480c0c20029000003402c02d0b80801e90041c40c03e564a00b0300402150b81d250260314090860010550319284040b03c101e0b04034814801c85505041d2606440300601103102c2e188210400c0c00317050860780b480c007061642d1286a01c05402c036440d0f86414408210044010b14000640b5410b4803a1480c1c61030074443c00110f4a0002c00c0000078036a09000803c40754809000b41004600c50450402071000d4400d40000200d0020500c0d21407000f15 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 676943561 1250 676942311 676942327
    0x2010e04090206160c05030102030f15010c03020304140a03060c09080d0306120f060f050f060109060810031b08120d0c030b0f060c01020f0f090301050903070f060f1413060c05 77
    0x26011201c1c2c800011185400001445ca0300103511030640d840030b6403652022080004111107452414400d0205505402d0082c0001005580c40f0203101c6025005a00c05e01050060400c0324150400901f0000c0ca01c3c3d901c181d403a59a031095403200c0d0442c0f4005020000100071020003007101c450350824030b0130184051400c2c1000019500c002c2500503100a803200407240034054a640040d109501c049c034217115038580b1038014440c0c000256181070000f00024000580b051064a40d00c3c010584501c18a81561441d160301258212030b141941c008541404001031905041215101e89112490344648030034902002104a403c000315420a060505010702d02590703480706070004065044a4064544a40303c0790b8a00a000724100c01c0070307100300000c0300e483e03600010020b80f03403000b002c800a1041e41d0310000f0b079689030b01450b1401855039810a5100300003618980143d26031009041002440074005890021030005c2940c0b0444049160310340f41003071000d81d00030182203c88500309680f5006607 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 676944811 1250 676943561 676943569
    0xf0617030703030f0b030f0601050108090a170a020c030706022a060d1e0e03030105041b1d0f090106050306031203132d080409051f030b070c0c1202010e040902 70
    0x2841d20080400d650341a0650002e030507640000d041400c060f0449400340000c9000aa55200030b02a560104c0c030080001100210006040f004056024041d160f145480d400100b415030001c01070b04c020b502510104084030780b410004507000f030000d9801000203144008005c90b41c9800050781402c02202010f511600ba01c40fa0111441d195140c840041c1c1c1024501d0f407003462403600441c2e026410b08040080200030400030146060310b004441c00c1180d0400c0c4c02071603510b501d1440445000c140c03000c00856000c050580642c80c10400903190740b0040c0004030002d100b0b00026004100840c0b004000d001041c20200003445044100e820a24a142404418a0f46850030a0360003010080014160010000381d9101284007400061020140700700328517000d046500103004541d0b20928200010304080a4002c800001c05e490004101009045464405950400078180c4041c0b116070802e1a00080012414800404030055200c0e43d80d0082d03c001000139000791a81c0b03110b00d04050102e800b50369 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 676946061 1250 676944811 676944817
    0x712020405010c0320030309070501030b09043203130602010f060e1f031502090909070f0e0403020c090106051c20030402150c06041202061b1305130f061703 69
    0xb0309410010178031041410201d81c0c01d07000c0000c980c0b00d8040030003030101502c000500182691403d881c240204020601404200300045401402c05d0380a4040c141503580c615486260051814101c0c1d61103981801d0294a9580a00e03806d90403900c0a4404000255080c4507003240040c00c03c5013800090701e008000700035008040c0c0b030340d01c401c3c1c1182002c110103030200d140d190040d03a00440c82d8000402501299000350000d1030031030b00543d030100000b120b509000c520241a80e104078001c0c083e0608201d4008581c0b04002d000710b0030340c401d6509041c916500e02e541c031030091040f603480903a181d24000050106001c0c1d2000d00c60340b9410086031544103450200d130340301030520845905441c3d80d11800003ca0201d0720f40712500c181a000142c3c2c1841900104005200740d0041c2c070490085032002100301c0c0d441d101219562a00340b07105010308901c0340620010040703055407145031211103403a84000f80c1004c606404031350007541d80d10701b04100302ea41401040c00500000c03032490031071a540c01102e0b403244 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 676947311 1250 676946061 676946063
    0x70b16141c0b1903050c0118060503010303080a0b1801030203011a0105030a0f060b0315032413030311041d0c2506021204061a030d02070e04051908030712020405010c 73
    0x540c07202c0c003140c0d003a110102d401450401c403105241c0010380c0c03800c0807074840c24030b800c1141c00540303002c01400c02d0540980d40170f8101c0da42c40d0384141c0345070710350b40f41220b000801500283c880c50311002e0200480d82d40d50384e00b504010010404902c25491403041600712400303490001804050051000c980d03a0704801941c0d803002d6255008115099161441001408540c0040e20a404080300b032000d245040495241d1104c4250221405407000001c1101e2040e01c980013400e400b40c811000030200c0c0c801103100c140c040c0c801d0170041031000d508400440b4540003504101c8041b804203c00c030f2030781030240c2101c0303030444140d030812407620294100d10011060391170400c07a0310a000307020b21400c00c00315504480302c485c0007016085003800c01c2d10303100b006040d800da004244c025031a90038450030314002c44c0301800da000c80d4005062151034090b600c07240c2d1038001c02c140c48a0091070403507c0380c0c0a42c020030207080380c4221000e66492401c500c3c082d010003426130760504401d03c180000e10113640c120030300e44180303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 676948561 1250 676947311 676947367
    0x150405070903150603051f060501091505070c09061e050d260d05161e1b05010b0303180a0b030405030a11030c1b1c110d08070b1614 58
    0x280380c183e4081c0609000d80c002860b5105140740e0300b0410f101c04c1c24180244610003028003010356150700450380841c083c003803c402d80b0558010140300a003d00c005003003543c440d0740c10b42040b5603164150003c5039555806941c01700c05012171006202303c0d0410040142c50111603c0c000300c4450307240c003182e5404280115245032101035200960000c904182c501e120800c03107080c0080d190020201000d03100500044011400c01c0b400c48844100d0002040c0e4000b0390f41d82c400120030440f429000500e61485815101035607111829502e9460074030040040c08111140300400e0403800c02030001241c0a50300c4072036200424000d2100103a000700803071b12011124a0640350021080c0c0e00d02d0701310301c44c000b00a11640304c0d1082201ca102c1b403000000501070400c466400c450b4107105c500000540312154003d00c0002c011540b0040b0f1f180c1070200c80f069601543da01c03401c04505607500c19140724152101090f04600085a0601c203038030200140d2619000851241004c039860b003920303507001190300c880f009 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 676949811 1250 676948561 676948583
    0x80306100507120507030807050c06041502090306040602090a06050f03192c0709061d131505010e1803121b0a030b031b0901060e0f0d03020105150405070903 69
    0xe80c5200c1c2094504080e0440c9000744034540114028100c0e5000b4403007200810080000544002e00920507141c030520102c000c3c1c0103d40e1669101c4a07800f20320004c0582c0242c0c244000344036501c040006c0c5118520440c0c00607030740c0544d1020402200f2980c0c0c06481005020802e1000814282c8166a00f01c0100040f602000c4107a4032520041d0405200b10001c005510700020b5049003144503c503440c802c1141524256034503882604141c034618010103003028000010341510700680c3c000d0980c003a07265170300852007146540d121321400400d90030314021143c40da4018420588004401c80d0800c400c50941291f003803419140c0c82e113a00800b4480e070260351040c00043c1401c030304205402c007284e040c400e500ea07507008400700c09001003070300c808440d020b40b1403243d195942c0a00010100b070480d400400700002686400802c8418a28200809402c040840a00c601c0b546a0041c2c02410900c60340020469180003041380d00320509503991203124504080030701080b1900081100c06807a0000500c1c12 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 676951061 1250 676949811 676949839
    0x10c050a03050919050c0906010905030a0201081e010605130621050406060b0c0f120a021c0516030305061810120f02091810050106140702130501060206011d04080306 73
    0x8208400d130310250300c0050794502c02030100070000c585410300c09000c03150402c241d211000115002034003130103280c0d0194400b011241c090b60044a0980c1d0000702c46c0c600210001d29800c1d11500401c0c280c1c04034000c05e130040744110b004640b04d40298040e240900d004820040f0440c0481d815401c91400e0110050790b4401003010300c440c07500700d50098500402c035656102c0842980c16a141400c1512103e907000300394040e1614120034040b41e0086601da03008088440e1004004030740e0040c200b1640c400d0007410000841c5030150f140885000030301070f0b00c00054a1402a060284608d140c0040280b044012401c001c000b10b83c030106502914485600d100c1c614105241c803a2888004c024003950042950003042410b110f000701213455541944241d5540c0750040d0490401d0328402e00480000c54450380c1442602121400503154a5000408160b00c82c2400c404500490f442a004940160002c0e001440f00c455a40130021003018100220031480c0761988950065010103090280f04180d82e90bd802 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 676952311 1250 676951061 676951063
    0x706020c2b08090d03020d151818170c070e01090203100608041205030c2208010b1039030f1409011b02061308070801110421051e010506040e010c050a030509 69
    0x1e406000401000700e1115110103050150352440480b40301c085042804009558407a080b560700f585a0092f2611100c40c64041d90207402d0b00b00308007001c5c141c072400ca00003a00814113100f0278000d11501c1c0005070f5034100746020305421141038110105000d12007007070200080301c010040740d41c0086440d00300d80700e840320300720030a441c801d50500001c3c42004c2c07000d00700c3c20580b10300e1043c111501c1c60000c20064030ba01c8203001030704502e582c004c03010400024883c2407840804951954031181c2d4030b680201c2c0403a11402850b00b03034491605800080c040d00d200c01c5801c2d004050104003404c400100b034203041260300000e02c810a07086c5000b00070480d001000c41103440f24801d441d80c0d0360742540ba1404051715030000c55a0364040e8071a0410b6907013008040d4940b840004211016114401c1e05400d186107006500300000a03150000c075034501ca84c1d031f0b00120100800c6240c041c2d4082034800405d6504284040105888100b0004a180e0740b4001031031318226000310480d16500c50a003000300c1c0300d5445000d20703 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 676953561 1250 676952311 676952321
    0x614100e060d060b120f0f0c06030f0c090904030809070b0f0d020f0403211805090a09020d0503031006020c0436080307050304062a050706020c2b08090d03020d 70
    0x115421590012185031001004517080b400207245504031007c10311000643c41c2c0d0307030b500c21a40c03641160041000c950302038a4044842d1788010715120301d0f1b141200c2800822001c84040b107043e40010010002d0000c850340521402d80185109c00546040c031560002d84501c1e485424000c41c80c81d5400101c0c0488444d05005031801150031201c01e101644406422064500c10a0240790000e40048581118000104249400c1d40c2c8040c0c0048116541c08904000800300300005aa1004146505a0000d02d00b00003c61090307160240d013920b05442c0c404080d152195010001d84200d0511002000f40c03510032030280c1c2d04240300c15220a81d01004a552444092590f6003d814540c00208200005400c030000798091842400300300401d2403031040d100c055000c084640d040c0030400c50a055400781c8900042e0904501510005160030b881c1c140d43e40c9040d802860071580c640c4140001e846c1890710550203030818603142000c8003c1d140c01a8000e4940c01c881e040002410790200d07056560b45501d500c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 676954811 1250 676953561 676953581
    0x1a0405071b031803080a0212030403020307021e0a080c03070501450902090f030a03020d0302091302030a06030501180b01290c0c0a300204180614100e060d06 69
    0x65050040e1217051441e9240c1c400e03800344000d8820080b4041440c0e40d4202107901c5a40c05034003450030042180e00b0480d10b11031032001314030514035014041c071031684c512245000800341030006083c04031002d0141420311450394896410f01c404480209a41030140c250017200e07100030012041400440ba00505481e00341e498140611201264081400306080d4010031940101300c5805078010103082c00c0590f10780c24240c00800513007280c002012598041e80140c03680f00801010f601d60a07002c800301d40e041f41c00443d0404200d0751074600800a1000a11030a500182e00043c100c8401c4415252008405d4040c40354005840d62103041d1002e0351043e25000244210444a981e5140340c650b03040c079a1038071080b2440c4e10408a4a00c001240c01c0101074125449486440301034030220315101000050f5087c1c035080e600640c450322100c0404060000c10041d040c850700c4000342e40784203450310f00021140144603c2c40e142400c207080c004940050081c580c0200c00301ca00610302461031031303c0b001411303410f10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 676956061 1250 676954811 676954847
    0xf21040303020a022b1d0d0f021e030d08150402040e0609070207060207060c080c0607090e060603060d02093103021606081603060b0d1a0405071b03 65
    0x62008165068004100606507642220004210941e00e40060300707119940001d03034990b1200742184240110140c1210fa0101c0a0100300c05625a02203038240c0c001c200101c2c0e080e640c10348440c0442c0341100d8000c088410072a10b0b02104641d003408207645180c0d0b08184030030b20a0100010b05020381c3c1800601c28400003800964603a07943e002c0300785644500359900b43c070440000340001c0e01184000703039150450350554000c00d141482c00109407a152030910098817000400c01114025020800c034090241d850ba655405c070b214500302a203039441801402c00e5102e202d003041408402e58421581083d00e0342c040341c0034800358903200501d03001c1c149aa1410304602c02e94130301c8405030950164040c800c06009400f0350b11807080d201207206056069000780c10101310002c002c540001000186807242c11010304000a9164452110f0905038100103810b98210f0b88038044000e00403524605602502416030b41400790342041e02018101c00c015481d0071601543c2c1006400a046c85494408441607242c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 676957311 1250 676956061 676956127
    0x2070b0d150308071103060628030b0f161805011d0d03020c030c040b1e061201080a0309080d02250b0313050607080114221503110103110f 61
    0x40f918903055000044d068030410040c4109403c1400c0100d0090f200740e80040940c410403007103c0d07030b40030b80075003942c4400140c5949242c003000191800c1010b90140100c01992266440c00d02000150014170b4298082002048412628000002009071041da03200b400c0c540d40680c6100760304444820707003055959000c0520340191042c140c020540b0940f442d0b05400751000200100184000e0b1902d00c51041d401a45003103c2680e414440540319010722001405245803113124415070854000070303081008950408100c08082540000201c0f00410048001e403003038802034100070b902da008840410b201d00030b0085c1c40700f2044511144d4a000782075000c8005031a8240802c1c010420225024221501c0c46820081848903002e030040e04c0c120f030201d000b1031414511040c04c0c0030001c20b90446e1a4a550000d00384104c0d242d038540038881c10044841780194559107503042c41500c14544c031104605040c42c210b25200d5035805501111040303511a80c107d81d07158407208801c1c0c0f4424a5004e1111502007070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 676958561 1250 676957311 676957313
    0xc18090f0b09061806060d080c06010311030c0a06120e030f0d09060f06050d060b011205070512011a1e0c0102030103081e0a05092419110109020102070b0d1503 70
    0x429507a000e055200103c828a6448400b034010070f011aa00b00c40702540400d0001d07900b4078110042208162086900e01d040060400c0740c18034100c82a0000c5400301c2010303500300f515090400844401c00000c0f900e070880d681c030f08a0041d24028941d00c201c0703002034039a589200380311820400c40d00c504c400d035081e007607440301c0c5006403c0003040d103039008940c4103052032a0448045603038066003003652070051800312440d0301030b510306009282d41c1c90340b00c1c10b000071100d00200c80f51303131417146921400d00c684901c0c1d6504000c0d00da2800400050b0094501c0c425003862202ca501080c0040c1c0314203c0f013140404d003510390980e102e8007050050140c90340700c640c00000088108a000405440e802c244811002c3c54032418540c0d0078a2401382046071000208203201c282c4aa02d450401030340da07400c00e500c0c585034401070040b26582581c05a0181454245040c140308407055111b10302d01c1d03003404040d000700254a0344d540001d44030212441481ca0038140070884c800c10713840340d510810070241c80c8450030581700d5807 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 676959811 1250 676958561 676958573
    0x30f070905090c0a050907110102030411030c0405070915021f200c0a06050c070209040b07110c030a0204050403141303020108060105030708010e0702150c071e0c18090f 74
    0x1460048458035400c0c50301040781030000241804002000030700e41024141030000380140240000d2484d01001000d42901e15070040a10041d80164000c8105900c018800014140303400706103211603008524003810061030b40d9004040d0000e0700c4c0441c0340540300603142e40d022854a0380d03a4103868858140d00242078005041c581c0326020598050a03252154409040031032428041c01c01e103070324680c00815141d400501c9507401260f206159201c56400c22034190042101c50030120f07002c858140003e01403001482d040100384070b8050300b010003014180c0c03094010940f01d120f90000203004a8a4002040415000c0c803003090900d041801107503151060b02e0318041800040c0d200981c081000980451041c4d44030301c086900c260a00d0303c1c0c190341e69291040c041c84e10b00b17005003141c0c110b0142c0b100c80c01e0b403581440b4405000e40d440302031300d0f40c6801c414106641c403256070b04091840c240480d13510000090000c4140801c9468100a40b40c80300c000d200d40c440030b825440ca00810f40014956444200302d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 676961061 1250 676959811 676959823
    0x3030a0b100207030503040e1321030e0a050c300604020a0b091f0509060a1206090216030507063308070810180c0f03030f030510061d030f 61
    0x10088075010103003401c1d44030a9841c0e03100740c00003500e184c01c1000244036464000121540010b00392050442c519110b848201c00011072003000d81e001108141e00140c09a41350159541c001c1881d4046c06000c0000d0740c80c107a44148030b45120380a0512040b025014440340c03044404640000a1021642c0d11100d801584a81d0300f114220300c6040302031004108400b2000c190b48801c40080d04c0f268000038091152015903280700444000c00804202d0f04050f500c03028003500144246898021050a442e4818000e9032216041640402e205210990041c4a4903030660241505800d106036603010908004014140b07000300d41a02900401000c0541195403600300039001c1c03076111b904403190700da07011300d92510024822282c00c0c4d400740e00c045030074094a41c00600c00c0c0301c6406c40c140880040c0d94441d41582c000354000b1034141400e450030028150050000407500c417951504005503e80101010001041400b5020400011000c01401295000b0711682d613904028119031210411201d4550341d0750b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 676962311 1250 676961061 676961081
    0x5040f06090b091c0c0803040c03080d320705130e010b091809030f1804090309060801091103040b060301090506090c03070501090e010902160618062405040b04020c03030a 75
    0x846406030b6041600545001d150b1070841c0c658034041841705039100c610700c9810107070040d1079905404e1400400602c42000034011251120008644002c05280002440c2e08043d5040c0d003c601e032884201c00325201c00d400d40d038404200e09006032a40c006010340b040854241d0450394056690341e0000c079110044101a001209003202d591410072847d140902c0c0150003514200c00c194001d0056107030451002000c0c050400070714800130a001c4020002a085d10380d254030076000b0541c40d041c2130001c50390043c0014050880340e94107100036081030911490611004002410780c070940300104545d03a41c2034008500d469040710403100b1034141684103940700c00ba100206031191140c00c0d00007610b540117045030411904107031540d61003686022800c0f800303940045480a090407000400b40c0c0040d11034030a003001100c000d40072041c103a01c0c62402c0c40841c1d101c1501c01030240d483d0800c0c11011681c5041590a5900586001c02d4804582001c80c01900070280702c1c005c070b1b000200410131540560b0380600001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 676963561 1250 676962311 676962313
    0x203100311061c0e031e0703031410030809010e06030a1b170411040b060a3f09020105040911070b1302031009110409050f060c1c05040f06090b09 64
    0x204040100b001428032490303000b03540e0405003140180d0035109591142c0300140e08881520f15100d06240c0f10041405e4400c02021401e0000c60b50b441415414440d04403008810138000303d983c149040c0303c218489840c4801080744c4400500703408903034401d108600395240080c0819840c1c1c100314484030050400314140404031003a4030071082d0307118803900041c02d025001182c05074054565890390b11540c07103280c200c10303001038617004041d51546540380184601d01c0d441d5181540c0b00003c15190b0701d500d100e0306c0364901403001c100c0d400b11700b51072801240760415011364000404010500c01684e2900903503014000a915107641240050381000041c2400d0f803082043c2e243c181c1e2500740302c28240c18a2100a50103074032010f01500300714a1a800054030a005400c5040703e0060140041e040e0388421004076019000707882c0c4541c000a0810040da003104620601c0b80c14440c007000c034040149190b8404c46145910383e40804d0500004190700e0328040d0700314206000b145440d04121202d031905403403d8440d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 676964811 1250 676963561 676963583
    0x417130e0924130201030509150106270501090608070e120109020a120b160905030613051c080a020a1e2a39030507150801290403050102031003 63
    0x2c22030840d6160b84502c0010340e0340d4030403407910b400440c01000001d00080c29840340070b4290705000e207500c8a450080140d80c1d150485028190b0416400b0b000d004842d00400e1b554407400d00003130b03800c1034800050305d003986410500c43c1d640745001c032030116048004507082b600ca01182c10f00c03514190080202c203402501c1d0440090b60718189041c1d030540720200500040c062001103483d01c000b15003100c0c3c02145030701e4034401144c0c59000180c201072090716642c000c0710607002203004000d0305000700041c17480a41c5580b1020004400003034900c0c0030060691149942c001110140ca50140c0c90081320f0f8070580d00d180810720100c080142c00e0008985005d60400b030103840140307400b20a481c10342c2180e07034041e49091001002c2841c1e455003402e08421650222581848130180c0480d50100e80f0086005000030a4280c1c075011811042104000c200f104203d03031000140062848498084040c101083d890792152180c0003080890f0b001e107400060941d400003040c410070720700000000003568003803815004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 676966061 1250 676964811 676964863
    0xf0e041a030717060610180909060e0319200a0501020301030302010e12070b0c12090106090e0a03020705270c1c090f0204052e080609060417130e09 65
    0x301d05150200391044d4003003400110182840041c05803001c4e09410190b5800c80b60310003841d2840000e420151a1030f6a662090b01803100c1409410145e00d41c0c13801851038201024001d440c58103c12000ca814814074042124030718035803942c101301c1c0003040001e8440b58440e074504903020350310a12040d8010740c00d01401c0c050b90100851401d180114081070645070100d10b0b500d80c0355040c0000c020400c0540c007440f500d03400c009103d540324403039081280005002420301c003c1078221100c80e91175401543c440407203040029000a04034040e150103d0f0500103400b00c581300c0142c1d071545083c00210341d140076814041e5900311240074144414410800c0c021010b000c603241c1c42240c80040c00a400c2445520101c40942000e86c0700d20340020440d07508141c0280040540048004c0382e10701103002e141c03900d508001e0082c0c1030003d10f0b0410b020358042d141c01e0a06485800d901c60180400d613602c00b85c00204d014046409052480040c0f0700c0c0d040502191800790721903622441401041400d441c45210644 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 676967311 1250 676966061 676966079
    0x507020705010f0f0302040510050706140601120b0a050d0506070f2f07030602131a030112140109020d0c05030f2a0f0301020d0b0a12080a0f0e041a0307 67
    0x95070010703521002040c241403000c81c0c000c440c04403075034103040d420480412682c42c0e4102c04e4045441c0c54503045d54071441451310000b00c0c7c0182c00075560031840302c2c041c8000c3d6030788200f0070308560050078004a0070050150016521855551110b0341c8004500b0011040047c04507080c2e210304110340f902084605e900009949108604012545c0c2042c1c2c9400080c2c4d0307409041a04500590a40456620b1510303a40c90000300e0b401240032011003116005d04100d201c090303001e8490001a889251821540b40c6011000a1040c140c4000c1002c8034080051014210940c4440802c82e0014180c0c41604520700300030361400ca075401030314028080d1548501c0000e0000400099034a51840180c038411007400001604d580503800f0140d004040b51801020f660303007400501501d00384400700280d850000010081030800a034050802e1031050b02100c0045100300d0151066210b9609291813040f4a100c02203d190820400f803d40c0703e80381c501c0040c0c1060101820403600d0200340c0850750700c66201d80140c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 676968561 1250 676967311 676967323
    0x1306030504022e030507031523010c0f120c0b10090c030c020d08090a1a061009060503060f040902040c021b30030c1e1902010c020d15020c10050702 65
    0x402441d803250f41d1201440c1d11a0b400144d00c03510030301d00002c040101c0400ca84040c60268001560003030441c080544003503821044001820013400c0c0503001e4000d5584500048102001c0078202416016443c08030500400b400140b90f9400400000c0e180781128007400c00d0112401031085492034488982d01c0a4024462343c00c4038034803a00242103c010311201180c61100017040b0030414040d60300308000044c520081a0107140e09980362802c0c5240050601c200302031059040001c00066140c10881240c0040c2240d80004007503443c120103644100210b4050602d04030001e401c545408128031690307602282040d0700c08405050807511030300c0c880810880704101100c440e005880c1c208012043e0134500c1171200c260010100b03070307410240160740c02820700c0e032401204000d00c2c80c1804008400c000c140440350800210349000050700c2d041d80c0000b0102c0e446220004d0103668580101c0041c820590030796184604102015507968107004881c5807108000000305810a0421300032805207400490f00b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 676969811 1250 676968561 676968619
    0x6060603191104091802180709061b020d050a02030c150f0738070306060807052a0106050112020c032209060303210b0303090f0303130603050402 64
    0x41c1d04101050650000010318510408041d0610100400500c90340d540c000c02e001c42d100f00ea00c540c0101d40900501c0309480b400c03165400c844112008010b25150020540b1058881e0b40c030304950020302090b541c20b000c4101e403001940c40800c88030f0703100800c08001427003000c1a10076000d485248084006120221726801802254070130280840070914801c8400b602c00c507401039a00d41c0703005940d02030102c0000041c04400c02140403d02100a0203001992601d0b04180301e484e00704801403809000a007101c201418000810500085040c10030181440003c0402c405646031440c10034032403506d43c02070a4602c9041d003c01da5800401448200c1442940d0a2003441c1010f54a0010410282480200c0c40e0840c00c504100b020400715846845100d2580918402d0b103501c02e40d040282c60f503071080310b92410b0b121b1510381006c2c07440c9060f0310048107031214100c040d0703a0800680f03c144002410b5000ea082c9a050b07205420b400003038201d80c95049240220b0094400980904200b100400c141001c451 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 676971061 1250 676969811 676969831
    0x30e0a05010f1b0218220b010303030c0c0b0906091011030432010c110109111903061a1002060702151513050612010e100c020102040b04030309030506060603 69
    0xa640080030301424007412840031000e83d440d0040041d500060603c5008191000d6030b1042c0300802100040030945007400410b8004285c181d001e583e42c401000c0c107014000201056162401d8044a50041c0c01c0e4000140d4042c02607406403908071500b907500c40c02282d1062591064010a019402440c41092407498100035102d14558903500d940004140002190010582c0c0c80641c400f400c0e0268003043c004200e0800118a0720b00d10b120040881d00c4484180c1456407610b400b40000402401d0324800c0303600d0544000007400020100c2414112850b800a88036906182405003c8081c2c640e20b1014400112002d108074001c840040b41e850908691a01c0580e2024440000040c024201207920000c84a07504282d034540301d004ca41d81c06803260402244a855005015840c0741c518441e0885081a04c020046182ea012702d680e500c00087c0e00d80c00000380e6072244540100e200390100c42c0a001c0020030559201e03960b1400502020a82c80f040e1124042c001c0860390a103400c2c0200c80c06009042 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 676972311 1250 676971061 676971077
    0x2091906330203071202150709050f010806030102130905010321020303010e040809062d0f0403111305040b18070609270f020705120702090c1e16030e0a0501 69
    0x18103454842031a1070010310a6120030700101002401021070082c1a4002c0c0d4040d001d0421000412044854064a40700501440d4281400591500820000125030919141550740c40d040302007802446000806003420178484000f01e40c040098202070b0403a0310a2001040302c01e003c00750740c803900c6000003620303005070020401002203903000084c241e003103405182c46500e82160000000c0c000c1c3e01031a43c0e400d105070201c0342c403032491401c1e118dd05030003402ea1981030300c0c040380e060304021039100c7c6000040240d6100540300c1490f17107550030f071a03900000c00e19080102d030506043c0310101c004d00310741c8503100c0d02030400c07100342d6050045045004c0320800c1e01c0b00c0c22000e0404501d50710810120104000800703a2407500300c11028540a4251104d0100600603030f5108503040140c240b005c05000700e07940c020b08220001c0180c03038440e02e0760350000f84050102d40390201c02100003140c0c480c0203680340c04c034140850a0f03a08001c0b820450040188030b91603d4600303214103003e01201030007a00c80e0901042c040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 676973561 1250 676972311 676972379
    0x2060c0f160302070e01030b060915010504051e091302090702030a080f18070906060e09060609040203370b190e070513030804090506010801030b041502040302091906 73
    0x1641d00319503024468015103c0003512460740000303905090f80261038803400a014081c19040c8100d026030810003a4007103039501000c82d030020342240320702d01c01ca81c0610400220a02c07034130814000f00401c080000d02c1040362381040280180081c85180c0180d00c100c0340c0901180c00c0380e0001003100c0c50340031981c035401202e42ea0204007204081006207280042074540c01441030b40641400b0a0001e0003041500003031260130050001d01d01000130042c6400790400c981800a240d9404c3c080c1c40c0c1c000350413180980d40e9902c80c20100c020040c040700401c5242c5031080114a00c045510b6003001e0080c0d14181009400c0c5c4d44820800303070040314200c1da40720134400c40040c803103a2015400e40b40e004603182407181ca00703c3c1122044907505010b900980c1d120402240038040355145004040d0050001d207840b0580b5415a12041902c1c04003900040500720070100892110380030341c0641d402180c0042528201d45401080c05031721101c806001400d062414070080340600300490050040f0200c0031807904094a4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 676974811 1250 676973561 676973587
    0x3070e100b0a0522060806060a1b0305040b0f040905060402190c0227040b010f0b0a0e010c06090303150803030c0703030b12060405030409050903282c0102060c0f 71
    0xb440030030003080b40c100400b07144000e42541040035020213502c500c00c5945450340c0107080140241059120795020440c4013489940041e01c42850b4804148a00b18500d00349070954892282c0d07400841c500f41c0c04111a036150301040042d1086a0300c03d107040c03000790740e1102008100d100307621160514a01052141e1780407440b98a001d410180b014200d54162a000f48145454805981501041150301c2f0100020054002022341c010022090401c4440e401d00582040f10f000380c803000010400e5811030000741d60b10a005245105400c10010000807100303007002005440a00e15900c0071100024001032100710002c12a80300f000316685403401c0000c265411409440c080c0341281d40f0034a603d200d101c10030024816180201d1007800216923540c40c25202c030041e610001c100c004160405e1042100114106003143c0503503044074150803030049003500c1a52010f001440044183c10f6104211a00e03083c003590720074500c00d09030206e5019030f840e0340c42c518542c03081055001221009001c0543d034800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 676976061 1250 676974811 676974817
    0x80c030a0308040f0c09052818030f120c0801050f0909030901030e03040509010608041514040201051b1024030206090607020310020304051006140a0e060f04180203070e100b 76
    0x200c85c0c40c107001001d07034034030000d029120306a84401c50749040055802c103500b500441c295030b0041d1484140700f1800c003410000070111a1203005010302444148050045e4440e041c1d003400c000d98060100031410f000c403401400e42d9824081c060080f2000318027407100c2d190122400744601c0d41d1500035854225007500450203001038407e18940ca10083c0000301b2195202000c1e03501074241555043d0492901e801c000120380e030400026140940b6003030140d012611040c00b001c0d030041d02800c0207079841d00710aa012411011202090005008080c10b6084412454100382507094040406400c030143c0030034142280103007448025403044082140d18410305200b00070b80300d0b84d40001c043d0340460555503004002d83c0c0c000c0f2421200c0382c00c0b2880300080c84520f03106681c081c0078a281031070000c07a4003001003000880b040c01a200120022800115941e4542818200c40c850140050000c50b04942030710303208400d0301d04200c0c4640542d1a012403010543d402c0e01c0d21460495104034846882c11094169a40c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 676977311 1250 676976061 676976063
    0x30b010c020d0f030813172104030c031101110d0905120a0903300e030c0d030804060506061c020f091203030709090e030d050603070e0c0301080c030a0308040f 70
    0x400c811844801580d281d02902001d10f00400f070b0001c1051941c0f50060075000020a40034000c0300884404002c14146481c50741c804642c1c0c8000d503551011000c46511400c0106030f5802c0c1c54840c1000c100070598000d6100302507a12036154003080c0144484d000c2d09035100324103030380c00410301800f800f004009550041c1ca0f0031805801940d0020b0f10502d13502070b9690111f10301c040441c502e042c00b0410052900c540303480030b03051110380c004240000c3c90030120807520031152508110381400d41001c66a014081000010401040360126903801e00e0085d00c0c21400700c4068030f6240c6841c000404500f4130108a030f01e0000440816061982a0925a0029005100084182c01040c040d084003503e42500240964a111000319100c0c87c00038801414101150803003410035080c42c149100c822800800d503940c03007a041030042956034826010a00c2e11880d503201e50501c070440300500c04070321b99071401141030f240801c051303404486a113070a1564415400400800203802100020007241030310300000101 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 676978417 1106 676977311 676977317
    0xa1a130b040f0909050f0715080105030606060313050708010f060e1303080c0d0b03010c0801060908060402030715050903010f020c0706140301140312031003020f12060106030b01 78
    0x5001c2c0ca100d2000d040b0340303880825007081405c0c046085401030480889a4190351000401c14800d01d6090600200b01d0120000c05c0b01d0801060680c400c05000d0081c1e855500e400001280f42d41c150719059980380219400407889200a0042480071012600049104c906000c44480c44004c09098682c03803e02003440300c0c00103501f143c0d400c2c0c0e201c20003428040e2102c49510402c4003402050780342c140e15510f0031106106ea540c1211256060b0340003551030104054560308166030302c40d020755001e54140c0c030410003002800050040354000c50b42d01d140250a140742100806d083d034031205280d21020b0740100740e484600740d042041500800451606010184809540900a102c107014030080c004443c0c81590341514100101400607180c0402c1c90354901e880100002c81c070240b800100c0c03060218078084201c0707190075841725440c7c440c40405030030180d203490020341c01800d08268084c18 = true := by decide +kernel

theorem cover : BRFrame.Cov 676798561 676978417 := by
  have h0 := BRFrame.cov_init 676798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 676798561 ≤ n) (h2 : n < 676978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
