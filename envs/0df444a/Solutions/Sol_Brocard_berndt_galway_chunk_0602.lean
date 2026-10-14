-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0602
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:40:41.420194+00:00
-- url     : https://prove2.me/submissions/01caaa0b-91d4-4b45-845d-5dd485c4be87

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 108093525 ≤ n < 108273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 108094775 1250 108093525 108093547
    0x203070b010501051215030a020402032e0f060c060b0d0f0308090607390308070f0206060a06030c05270f0301050c0a0f17040503030a0b1e0907140301030602 69
    0x40c2c1106041c81814003425900002d040102548540c8828120080d4400e4001190601041c2031010390802c0c00041009000b240c1100c920440701c2c40110f0924008910f081a99950350041c000c160a000c0c0c0080200421803181c5071141d62180036900c00507082e1142000203140c1d181a000454000040280e2003043c5600174405560020011020306018a8085c000a00710007820840648c3c0008805464081c0880540399a104440c02010200070710150300b006042070004581b0400002d2004105d00c94440c804a074603030060704042c0c20326102c02e0800394264040c0c086403a541c42000814082c45090b060786200f11401e0038101544c00d00d444d102e440a02c040a0420010140030741e040c036051111581d4064100c0d555101589000d03c60850032520403181c000314144003103140c94204c414801802400b0004500440a000c0d0401c00a000c44003404411448030100344101c07116880c05000c107040c2100426400005c4d4941420600e030400b40d55001600280c02c01d903101503000c41c117141c0139 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 108096025 1250 108094775 108094793
    0x6080109050703090203070902160204020304050c1f2f030a0305090706030e070e0604020903030a080901060e04120c081e0403140a0819030605040504120815060708130305030a020307 80
    0x10000a107400c2c00100030940110765180d03508c1c42507014055002070020200341c0c4200105d025150300410641d80d900707150030300b15916182100414891400342580969242c0a00008001030741203880c1c090801c40981403201121031040317a2807080780740304010410100c10610082011050b26140011141000b2105074940700071a00010241860144150808440003a00c0012039495003030f58805951070002080290264920340c0c1e4040c4008074402d100d003038001803049d100b000b40100030028256034043e1800c1500003501c002d09043e0151280042c070a1103032245408250140102500e44920002600e00450004000f444240c2c8045024001c104c0e0018030f1500c41c0044030014808001309451700c02462141d804400d40301c04400100704181c60207500844000c1c03074000e1042116140c18100641d690010010b014009a00940043d600c0d4030103460250030300e00081c0c4440d082000d140e8034040d80c0d6001101c41c07d8040e000240020000c1d030700700020028005c1c2c0740e010b5501c07412540780403000c0c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 108097275 1250 108096025 108096031
    0x12030103051c0206010f050402090321030714040e01120204091e0201031b0915020a0204090b06040b09091f110a0f1e0509280e1005031b01030905030c070608010905 72
    0x441d04013400400940400c0001d440c140c540c120740041e60342601c000000e00d407001c4a0b14265020907440e680c2d845407503031000034611a240700c0d2141d010003e030000351601203110794041e40c0d50010f044c000520010302203124450780e0a1020700001404001d83d201c401807551801484014a0016140e040071035074940200004001103421a1724140201000640700000300c1c0036084220110603c02d140142c0300b0080b140d0401c0d00074008218a41290810340311581c1c0449545004504240e05003000b410f0171300e9030301e10459200380940391100c0c0f0444180100301080382030351007154880004c0c1c05d5120445006100011090301d03101c110100002010f040ca2154542c0361540321028080542c0164014003201ca507004e00b210412070071014450b0240704461903143c0e80050300038900020800e4800403644500802c41200c031080200c1d6030700d042599800c40300078071000450148050060950094204a100900c5042540e082281510486181440769440f0100203107402c0c0c01041061054822150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 108098525 1250 108097275 108097277
    0x2090108030a0e0306040b01062d0207090614030d080a020c03160c06020a0b04030c0614090a11040b13090c1205070e06100f2304030f02030606010302090a09050912030103051c 77
    0x41714900b549900c6d07400c0905200d01014000350340380c2c4900c1010180c082c1056080c0003040858480b5039500300a607140c426000350b030001880c02c01c3c00b1410b6490240382d44a80200200142404100c000088801c560040c02602c413841e0240a9030440c6041840603005294404109803242003c508121204151551028045d50024110300000c0358203080c0041d8002d400d408c250b02e0040391071400000916003019014046001c00050040002000c0343c034007007103402101c2c03c8507030400c0c80b410441150b00c0320100c280d00420110008203091000d40200d0441030040310307040d455503680c07102c840324001c42b50400c40c2c0070f4100b20024000c039081b075549a070f00100252400c20b0810702c0350b0005408041441034000a01c4201042031440b81d90200c604c089100046082a403115540d24140360b2540f6000c10883c82030041c4400180e0039446442a030780342c4440140180703140c614000f41c0b10020800a001d6002902840c1c100903181c405810045000b90301c908024209440c0808100f490800a480104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 108099775 1250 108098525 108098533
    0x90b040c0f0602030307050901090e040503030a2004140609100809010e010507050708030414120a020105010504020724060906243b0d05060612010204030506040602070204020702090108030a0e03 85
    0x11002d5940081643d0344803005082040d646c42010f8011b0f0b503a00c4151f4409030700c809a400810040290200c0618064402c0d8001408554072002502d546410720703061150170079009100c10400c00381c50085422403000050001460100c032000803c05000510541c07402141000d41400001202449001c030ac6046c1840200b000c0d0038028002482032144500c0540040808000300b01884641d06541c01c80d000440e04943c00c200e08110082007c4e00107091410140d40307840c0000810781090b0080342c47c1103500140440714407204411958034580116501081a80d5440001c074080c8010701c00e04001d00341c054045211140003040e41041c40c01c03448401000c0001100890184101e0443e0300c2c0301c500c40141c10092000100f820010400041c043e5496010000c0307907049050100110300302e0302805080d01c502e500806800000c0e4240e11076440000d2169100714005004035819602400059200404c0949441d40c00c0d00001c803241c00a03003045240c0d03040002c1229170301e0f4205502e400c000340190058 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 108101025 1250 108099775 108099779
    0x1e1b050d0f0501060504152f01020c0706020105060102010b010801050d060c120f02090a0504090c050405130602070c03061b08280c0f0e0f0a1404090807060605010e120303160909090b040c0f 83
    0x503101c20f01230481c042040d00090140c038420a4054500040300e802c1115081559080000d010b01300c10f517462409940303070911120b01c1d5403003080064181c1c0c0d0082d02c421440039a40c0e4484004101a81040041003801801c034104417080f0300070402401c402d0000036844148040812040034883d9200328422443e01c80c03003c00080d29400300f20120340c2e04442c000703115502c0181103c04004124001031480f8800a594004c000c101c1d521241641d0044404101d004038012189060840f11203002d030204090500160940350804201e00d6600d02c0070804d1300d04650082c45100a45182c480070101042c0e40100e00c4081c02e40c45a100100f49104840b4200c21020040210b404841c4e90301481d12802d08000d2029130780e8480b600461a0503602c1200c850340c400080c102103004210500070180040d081940840b05460660650080d0b80041800f46145880e0809801110b0404000b40c00038800e0305d0b400001c490000744200400c40307004e265000460b140c14580b0260003030b42c41d00460b003081442c0d081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 108102275 1250 108101025 108101057
    0xa0b040204110a1b062d18051002070c1a0d0e0c0609010c06022203060e031213030903060606090509060a0f060f1707031e1b050d0f050106050415 64
    0x40998403540135606800b02282c100000a019000e104550030341e0701005541100640e101a07488088015100b0010107403e481340031004081c5000140ca40e5116040351014034101d43c2c01031044a22a900301140941d6800240044103000000c07a03442d80070100b018500407003d030048552070041c2c003018000040054000452b14059805402c0c1006596040c42040010540c11140c1900002109410080910441e501707107640f0341c00100c48080c10120010381c8101c000042e120003a05106d20408140e4410712800d540e030354a000246c1c1001020134000010038180e00c51440542403941e54952045e0401d0b00340710341c6050240916006888a45081203840c0e40407941e141940c049180203105640301d200c0031224207100301a15003400300d0040902640d11f4050784522010140d00400103880980c071100801100c20404c144203040d40e42c4501400018420302c010705900c0905080000c1c502a0214000c0481c1d500341c0000c0c01060700003c042c0104840c40480150400052411180b44007008a0f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 108103525 1250 108102275 108102287
    0xd030c11150f0d0204090204090c170f06060c0a060926040305061506070501110a171b16050a060c0206060919050c12091605040902010801050d0f02030a0b040204110a 73
    0x51048102c1002080c00d501c0704400b50121401083d440d1801c0d5220741d110020400180580c1c0b010001080700320b007001c0076034104841c072244114032031207508800e40e40b10400d0020580c04002c0c0ca0700280280481080041c440388180901d541c040c1a0601d9002c00c0f8401441d110880e203510305500100910041000500000c0d4096100d603040210710844400480850014042c050b80200345500704034404092001c103c000e8141d04216690310046920041c4954040c407000341c40c0b000001c490702c1280154090801c00500a4003245208052040403c0e1107c03414a40442801c694460300c0f47d8100540076810020103401100846045629040600c4000d0314228020007001c0f01030b0700c480005030380b03d9060045e0341d2a0304840c2d1180900d03107880c840702a00d6100f800d040e50010941000085918103061082e01915075040e1142082c1781d0902c6c0411a04511240e0215100f44090407150010303103043c040118201c0c89800100c540d03040501c1000b013a1a0441066800040c06001030340391030307078400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 108104775 1250 108103525 108103537
    0x6120a020c070b070305120606180f0a261213031101050708071209090b0f0105030a09060c0807080601050310060f09080609070602010f020306060708180d030c1115 72
    0x800590380c0c042401558140840c5030702c6096002d00c0454800e05058000004000351000b003805555141e8404081109030300a204070170485506501c0c3c03104960803c01c13004600120000c10b81d454041d66102d2040c16004151942d480c141c2079000800c0030701d00d007000500e8800e0070b50452242408980c10071040403081621028060107010288680103034003420403546003e07048500941e660700e0030f00307118103146c02c4900c810002810034500010502c000d40300703401c8048401080710200c070703459800445003908050200448169035890900010300a80700d0307a4a440e00e107445403e2203151045001c0c1403504002c1c41d95051000030800c105151006607050070a0315407a0070510003100f2003280845c0e80710700d242c005900c14890041484600c600016401040b00c8407a8024011441c0081e459000c1e40030656000d60444000d0207883c0001c0c440d0005807600c11039081c0f01a5500b05d080002864030804640c0c16400300317400c1c0c60100f06000050891040512b010384440c0000c00340f1082c2107140b80b2a00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 108106025 1250 108104775 108104791
    0x906050415051f0c020303122202150d020d0f090b0705040f0302120a05010f05012d0515070501050403091703030609010e09010905010501030c060801270c030605031b0a050612 77
    0x61884000c40d5801880384c84110354018040301d403a85c501000742d0401040584401d1440d481c240b828001c0c803d0098071160000c1c0c0c0c0603150544006820a001c00b0b035420040210701c84a03024000018076544610480300349040b841408121154076080503a5061001744c5010100a4104410b200f001c440004090490783e040c1c91010080ca0801411030a002200000801950924601ea00c0319442038000d00c0c1070715520400c143c90380343d43c1410020032083c01c0d04d2000e003603412036208020614002c0450340a09070002203091074030701c0a940b11821034604581c02c501054041500380a10b555807000c61010304694401140b80d41009400120903110510845090100050004031011400e40018248940c407100030b001d90358692070030041c6001c16004860014403170b4000040c0e034002100e40c00c00c80740740051542d0b40342d10990050380042d040000b140c100349a1600030006603500c0c10880010209103070404121511300080410a89002b1507100521496090101405440004000b15041501 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 108107275 1250 108106025 108106069
    0x31503060408030717010b120c0909130302011811090603030403050601080619110720030304080102030402090c0910050304050a2a0905010b04300302150106020114062404090605041505 81
    0x1c89c548600c41c2d200d1000c00c540c00c404da4006000022400c4d0310642d14440c460340090182448048180024802110018103192102281d83c8181e0030705440e5183c00c0500a42a2032608d502ea0300c85c9483c280e401e078402c4282d039000004101c003001c80403400c00644112541d040c0110300c103158643c4054002d42001034107c107001a207007030303c00038252078920030103402500341c80c1c50b141e0310000325000307410481e800e0380504104000519a00001000c42c0d061003001080d050700d480016400300c54031741005004442038481d40c000400403408250440d696001c0d60384254440004624021480f1011640300c1c016203070405005011414116007a60183c03030540c1405107038208010580d4140450b212032510419603403025200600d68007007200038102c24070014406041c0d9907148100c0c01c0320b0310489003404407509080400c00320b00c0c0040307039120100c076203003040040c01d0155188912180d100f0344c05150501e03500c030700401042c00c00340240301c01103c0c104071003491180b508011440c41072124200e5044044 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 108108525 1250 108107275 108107281
    0x150106210b0a0f0807031e0b0129070c05120703031b08120a0501050109080f190201020c1203090102010608031303030509031606090e06040e0a0305031503060408030717010b12 77
    0x11681400b00c0100301c0c050302e401c2d20a03560703000d1a40f203000500068403510b001000d00405a20b4900b1108441d03540581440f19503032a02c00c00d5a41120240d502144044100b4078007100c000c4c0f04809001540e0007a030405684601d01810491012400814000c01d42c001038010000300b034000d0741030600050540c030041d94084c0d65113410f95681c031a4403150340900b001042402040d00f250b500a0f4181c1c0c2003a01c1e07940e2000c0d02d50b198035950b940821061a020f074400f26456841c01001411100d585206004071699526154001220f20640320b4240145078400304800b1000c0d80d090040000410601c000717585040703055802482d00c52011300005e424004000344840c100e440400c1107010124003649402e40d100d441d460010b00000051040518191f907000c0420f41516140c82286441c01d0040010b0890455964090b907041d040180140100c02e491110041d0a071018000c40748264850b5101039175074600010f01400b0355406e0302103a021407004600520803003003c801100c211940c00c5a644805039 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 108109775 1250 108108525 108108529
    0xf040e06150a030f080d0c020721080702060a080a050a09110616080313060b0906030a020d06020417011d191401021c0b03010f0b0f04090c030b09150106210b 69
    0x82c999403008000b080c00d8a41c2c03100740040000a8804894581c1080c404804180b40480e582c0489003c3e42030311084540074407801c030031042d910300d00e154403070600030341822429000151507402800d0708030040b561100800402e041a403084650020b84e480042100c5c4103251900500b008035085200c2c098a00040c841c0c4800c4000391600c1c80203980591440e680b4a40025058240e040c2a40e08a0340d050512007c8006450418022481040e024004216941c6250200001e56040722415566550308000100d0041c0c140484080c1551030301001140340c0b0b4a10008003030000070304d00340419a4118030118140d08c00501c202442003030b00440c400842c00c14200c44640244510103080d02d18445031111004448040e40000070602404c6008103d50000054140181d9806904c4594058007422200c13409143c0750380b025180d14061000030000c81d4907592000c00d88501540d9a207490f505c004264040008142082409080c4a1816040100f41c041071000d82e498041c0d11059000c1d1580740750f080b0b075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 108111025 1250 108109775 108109789
    0x908090306090f060a0203160305100306020d0b130b0607230604030c030f090e061e030105040f0c060302070201210902091f09020403020a0b070c0b0d0b0f040e0615 72
    0x101100605450341d034180000072641c2c400403203940003240e00504000031880035007882960320888152140c44910108040704070010b010007044010070f0490200c01002003800380c4054080c081001c000068148201d8040041384143d40d45043e100d0345c1004c0c0000c035903491b210183d404140c0d011103c401c00c540031203a404542416000e9800c07035441400c2c100014190321103030b0102c0c407900a48800b04e14003140207084a1103c0c541c043c0303517045015400858440e0801407001c413410362800070007881c4682c0003000a420b54805403000c2d10340c1d84207840100188002c01030b1120051903903081c1141f07441400d034006880b196240c040024400c001500300d01c0c840d103050304140311559004225a0452400c00240c00c0c0e03440740c0c3c076421360b0303003044502020541c034040d8400c4a054036001000341d00114500341401c40d42d9448a001140c07d580036400004000c002280644034000d5a201c000c1007510f103c1c81440100c080000041e881a030400c62031004280000c28a81d402c003480d40c83d900c800d42e103444081014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 108112275 1250 108111025 108111037
    0x80d050711010c0203090112020309070311030f0312060102070506070b130f02040504061d12090607030e03060a02040806070c03124208070b0f0904061706190213090908 74
    0x182d500b003180031080036601000030003a5050988401c001c40800f4140381007207000440344100b20b076000c4541880852603e06000c07903810b03402801c8422000d10f00324440e00310b1b0030007901d00d50a950404140f000303e680500014016203810344075036080190759259603140c800c5c0580441300c01020b441e840c0003405040c00700c4d80c500d540c019000340098286850000014410480444032451021070969400d0034041020400310910080c4a41088020001c0003020b0f03021640807814442018072041c41c0d528144403041c4149070103800180c0391841c2c252004d0610000038140d1040043c2c1c05a001d0010790010305841e59003071540d40014911110080740c1402d10309c10141512110100429048106096408040c29040b0305000207501c40e80c402000c2d684008901400c2c0410700d003031050514021030003001c1c09090000030f0000c90183ea8402d01c00702c203003804084c440465000102000041e05802100c249840103035201103242c0441d100886140c181103000340600c82e502c9141c60028010401c0503206 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 108113525 1250 108112275 108112307
    0x115081311060a2003030c22120b040303200a030f0b040203010b040f1502061303020a0b0132010f0c030903060510210201020607030e031902070501020c0d080d0507 72
    0x103a682c00740b40010301044c1c04080301c004808618014900106400310a072401040f684140c0c90604669081e1005c003100781ca401102c400c84981d000007a00b402640300980060302a20590b2001d0400d414024240d0300400b6030301241c4002c07110702c400c0703a000c0c00080707400201c02454005030b401350024105024058039810175a1050000c400810038080b1040200111b5010381125049280d81303c1c0c04200c55489c0c0c607440310150300082d00144110030b8034050480c44901c284143c030b141d104075950b142001202038102c8001c0c3c00c1d20300e42101c00002c40c0d601c1100d0300013403841503000000030200000c15600c42c04544104105841c0d0090301014026400c0c00055640003d05010354900a00441c881440900c56100c800360710904038a40507080c40c410304141c6406901a000555032100f066005d081408003070b040520041141d181202c640140d03415220035240d002c0c1515903e013000092403c0c1180c000303140710300120410032001a00080483d00d00d00c48009021a40350358101007074810080024080c1c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 108114775 1250 108113525 108113527
    0x10f06090c020c01170103170c060106020d030c020f0706140f0309030706050105190b2a01050f090c0d122007030506010e15010e031207030206010509011508131106 72
    0x105021005030800300200d07406500301d03046200d02c0c200444090501600e1442459a0750b801440401d40c203007009111040d481a0031854050300840c1549003200981c850001a08083c01481c0001c0d03040c040e121200d020761004106941032019055181c51552140748244040001890211282c030002d40c5c550b507144003006512864110011a129400403a040342c102d0320f8007002284601e8035001540707a01c03901020000d180f0342019542c0306285c0c03106880440d8860814801c414a22404454141f80c1c2c44210012845081c655204502400080c1c41490142c00100510200d51162611400c00b90381110164503807405100c003d03101c82c4030020010801401d05c04070007606000000da81c2080340d22840c1115001c0c0ea0300d01d62009000d0080e10107001d441502e808103d0558440c0c1100c00c21068000c0a5410b04007040980c00003681c003c0000703c016820080c010441031502103c00ea00604001020502d40c5072480700c0140a508c0041034020f0307004c204901d200510501d940d850841100c003612103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 108116025 1250 108114775 108114779
    0x4030909090b0f010e0c07080a020304030c0b07111002100b0406050604030c060801050402090d08030714030a0c03051b09121002070b0f10050a09090f020301090f0308090102030423010f06 82
    0x3410002101d1902c1d0034100c24000080e1400b2841a0710301c06c010302c5001c036040007019a64815140d000c01400021440140408004902c040d4403010081c4101c1c4030641d030350707411881c00750f141ca050070008500c1a070f100007829042c550003140c440e407100e102040001d00703040329000040061103143c03c81e541001d4081000300c10051950001405e45050f03464060b00c6a030303240100070030b920034594950340140303c801060740002c803450b003d10740103801c030f042c40c00034100c1c400340d0045c1582080f1400c00c10341c0e8840d00030110720b81d054441c1a4015282d80380e429000d003c40c0d00c190086200d024070807405901110a001341e40c62051062342c503075444282083d076440d00c081c10704105030001a541442c15003038000101c2c48604900a210041703590103085000010702d421803c5008000c010030564885030711580030001a9020f00c140c40c54144031b403c15600c2101d15003002082040c00405c00b0140740e10400c2844080b41c0c1e0050300c200001c0c0340d10550f001403100d810340c00f40500b4900c1c020389a490300303010700 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 108117275 1250 108116025 108116033
    0x40906090507110a030c2301051611060123060403061109010f022116060e030301090606050301030b06090402010c1e02090603070e15040603020a0902040630050403090909 75
    0x29006440c1543c1d00388003a00c0c0181459100c54103180c1c02404204045914000601529402d00fa5040301d02e908003015050b4650340d13402e4410481d94461002506115502c41c036030032061144001c101e440080c80c456040414034035084205810003050a00384164004030703643e0b034500311006503601003000e1100720fa4200150080d500112030140c04640d42c446003504503840081e52161005820355018008100c04609a010f40d21004865555059885450000c0f440a02801031039811400003955a0341c5000b00100071144903801500c2000410001000400c50403800d158000e403041303035a082182c58910050312741e51b60a540040c12168103d0351100000b010440d0500031a000b80c0310f4a0303480c0d0301c074810191254018068800c402090a0200e40e014410007c4c000704200d01902c0010084e44903000106d124003079038001280103400046c14042c2c1c079440600790b80003021020711044003c1c22030082ca82001c805103118a00542c0d180002024103201f40c01c64001030254007004c0000700f4041c20 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 108118525 1250 108117275 108117281
    0x90402090d06090c090b060702101803030801030c06080106020a1e020a180b01081303080618010e09010b01031122090f0b030c0a0602061603020d11040302030c0a030c05040f0204090609 81
    0xe402d64281c0c8902600003031984486c052080d200070b00a000720715004440d420443d20003ca0603070b000400407180d8507640300113104407100d0059806521401d01ca507141d8070700102004a2a0001c00400455000400a00d0340000c1c2e698007a580c414200200300c103c80005004044000c10b019610080700300002074078540320b4003401ea0880581009100c040c01000054482c600d0540b5141240d242c0481541c001c03a104074407007604480000e003405201504042c0c1503507940302c280c01c0a2501840b0340300b4844007110034882c240c007520742801c0038841000c036007200e40124090000340c04c0d002103070440c1c0031600900c5e40380524040d0809800802502c0c502115010040000c1d845241c005d100e282030f00d000b90300c0c6c9008498206c8500350f00030002513449054540038400311020580a1507000d0103080c5501c41c140c0107030f00a440301c0c000c040e5115480d500401d8038103030200b002140620508801440820b00084805c4140e0b06d00380c034042131140740301c0c0c6d219000380304582c8000e4000d450110045a00c2d0070f2380e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 108119775 1250 108118525 108118541
    0x1a01020d11160b0705100507120b01020102040806070917061b0906070c06020c03070f0e040602090114040e15011e0e01050904050f1503030a0c02041104051c0b010b040602070308090402090d06 84
    0x100c401210b8211b0aa100325002a601c0b4008504034802c0e20b1004010b80d040817580040602c0054105581c030b111072490080281d615401241c40181e040c0040d0b21b48104440358200c2c0e8074000c001d90700b00f82c48186055000c18083c4e541d005d10014005201c1c1c3c54200449460702d51021602c9900c41c1d9610b002034032500880c029910900880000090544040c0229400d45d4402046040d05490341c0d40ca01000754043c1103154140500500c074482c0003d100e40103400140b0205440c1070040c034080c0300c071110f078690324001103041c08022509246044082c0814015813030782c0b4100361508604040059030140100180e20b80c1c014145010482c504195148203402201c51034166a00710050504264403800b0f42240c51002810f400961005440c0c40d8010240ca5544408854580303038540000c200c8980002c503190804030540d4008108016100e0040350052500e00409814907003803050003034883c2c41c03e00c0050401c070310100304601260707500d90480e542c4540c020114055104146010320103469a9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 108121025 1250 108119775 108119783
    0x12105040615050303040b03070201060f0e07020d0f0f110c0310021c0204050112050402040f0603030c031409010e0904080f1b010f05040f0201110c0406090f1a01020d11160b07 77
    0x2140002419081d0010088280c43d002030107942040e06002e0070f01c001d90401040502159210280012136062041070030303015101c1245032040a141440303020340b4041c0b80c007607810300300a02a203841e10480e5000001c1c0801c883c0c145403a0403401d5910351041c1c40c01c0703503000029500d4040d915003524121043d40c0200b44448004000e8042f07940088060001c90245100e07050225480d03102c0d20380001c440c0d9120950082c0300400009840e0702040003030007180c840350030803004100700304014804c0c03581000440f031030b8030000a0907038502080180028100d482e407607009805100ca4001140c10000f400d000d0300c50344100034642c01e0300d4441c41102510303d03107400d41d20500694a060074283d03111000e0300840748215081802c0c04400200342c0e004590040103c0d581c40002d0040744141805a40c490140c00020800c0940c040390100345103440300b08442c0030404400c5d007030348250404042640c02140001c00e0b40b0141c02c3c0803500e19503540c0f0340381c102054400c01c403414015803600441c1c0300817000701900202e401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 108122275 1250 108121025 108121031
    0x1050412050c19031112120d09170403051006150309020111100507080702150f0403050d0c0e13020403050c1215040812010816050609010201240e0f010605030601030b0121050406 78
    0x190404d0100c0d81c203040d19a0b0000e0740081d560306031200c0c0400002c08024489000005202e411341d15088ad800d0008550550040300005d07040082c0079040000310100891108100703c4585080e00d010310b038404401c0c1840602d07848800c0340c1b041d60301a020002416142c00c098403c40c6070302c4592400209000ca44103030215215502080c04070344000b610b24030084440c0c0071020241c442c1c05035550011001042107041140c01c001410304c2c00c0f0280241100344040f41c80310780540246d00100003100d00309030200210329206000410103e8400920182d2158040e58002c0c45030041da00e50b2410b0000304072040400e6084501030004100301c0030010704c000c0c0c1c2d58082c150810398070383e42400e480d1613100c010b2442111000340e040c4018505140101102d0f42d05000025400c07131402810480602020141581f01181c518200070140381c000301c2d00d50140343c04071000c04d07a47c107185e00907209001c0070709030740e04161340d4103e094002e0740a8840c508414a480c00e45034440484101c00002070102103034100c400b00c2c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 108123525 1250 108122275 108122303
    0x1203090a0311180403020303010320030d1107060e0307140402070f0b01030b13020306070807020102270301060603050c04181806050403020d41031602071401050412050c1903 76
    0x354180c0820f021310b034542e014501d1039203140c403004012a81480000ba00743d80072544d040d140d42d4204000c4002d40d0840e2604403009a1002005081583d990300407000e00c101c03003286c898540e801244002c1580c40310142d40540708035210215000307014035803000f03004a015080d5142400b408444043c100d9101c4d14413800141d540c11040a00b420705160025010340c400f00218170b00c3e60140c0e14aa42c0311170316200060078210f02410560032a000f01051841481c10114aa29903007420f003d4000500241d05043c00541004503020500388030754403480c07036501801011070007085800d42001c00c0080300c01c41400d00c006062b04103040280829a0308602521031003e0700894540914505811040081006000c01000b03c40701c000c0da0310b10000302140d00e0300040c50604a02e07058409180200c1811100c47d2441155400c040c5c5843d120790040001648401036010070f03aa4000200d4003601e00700c0e601c1141400c440e1520514081c410074190394080d00b03882e40c1d805059402d0b8040300449018850707044c6000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 108124775 1250 108123525 108123559
    0x90501241409040201030504060b0310090203060a0509030a080c0d09030512090105090606100201060909030215180a08070311010504030815011103030a0e0f030c2a0f1203090a0311 79
    0x203165400d440b50440c90b89800500550b0003030b40f180f640300307025000c041340050416000078249080550200f0480f5070791003114056040802c484ca500845903402085503081c010312142e030307a02400300f6030b008020042002071503440450069030f00c0f480881d24107000c0700040307160145c480d81107984107104811581e0700080c082c010501502d4020402000a03205503181c40041c844100d25011404040d592100e20008118402d4491015494002c1e80502154444a407007868280e03170280858242443c0422811060346020030840681a401903005561701860316007a680c3c00e49400641005500e4a400c00003410b4000028610450a00809580e051009001944c1b02500700545c1d11584e4814000a410320f101e070750100414180d00400c4504070168015414915884011450040d030022140d000040320034484a0324001041e0b0420029042c0100101e9450a8045c400c07500c521101c0c1c149190b4900709001300c3d4041400070b4400d4014544a040844140a24022040c01a40118078840c0c1c80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 108126025 1250 108124775 108124799
    0x120a020d0b0d1511040b0c06091c080c070f14070609080a030903080d0b03120d0506010c262a0c0105040e041704090e06090c01051306050d09050124 65
    0x3948014161518485009410010b20b000140000c404c001000007089110030107010b00100c0032400c005210501d8110300c03890a001071002c070301041d0b024000c0855040368012411581c401c441015003600c0e40302038280240152110007018118114951030303004041c0020070400d0a4030f08070b8407a12030050340d42c0c14950740c480020102500140c030034403040c80000c20f404001c141c0c0340704190001ca07003007081000090034005041312400000000186041c0030020502a01d9401582400c19540c5002c4a4484204000c19800f00e0040040c0003912818a52445030590781d40412002500000b20110900148040040410b44100d0702c0b5078203484603158450001c542c141c1c0c507001c03884d0b0a141c0b103d543d90785851010b80145003c01c1014000420800018420070340d02e045004d00a0146041442100b800c0003400b808860401108008803030b050100142d8200c11145075207041030343c50514140c0f8400921b24120000d04a500b8500100c1101211307402030014140f1b5621580c189542d0f03001140700f4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 108127275 1250 108126025 108126049
    0x3260402030610081902060903030c0601090e01020f0a0e040e0d050a11070501050a262814130c05090c04030302070807051c02010c02120706030b030f031e120a020d0b 73
    0x2c4c3c0d07200c00c1c541a183d6003044c0c03404041902c00751000f41840403100000e411500400080089980400c004000c400400d0054451040c000c3d4000c62822840c0481d41d8400e10a0100031802d010100030301515a44842d8410b0405140350415604c4400110340c1c0201143e00501036000061441e510200240702d020079104c003140c0c8140c441c0d601d8030804010565074130090840004026110100700c0c4000038140d001c89202e6203403a0b2402101c80444540c03104403466102021100c90303c0d080100c5605203101401c00e400041c08510740042001c1e81c03038510f404826541110381c11070001018045a00708240151040c0d034400d4003610343c0d1540784d88849986d4421442034590058580c00e00301450448202154109070041c50008816402c64012446821028520b030549601018040041c66071621420329285001c4001d4035942510486142c0c0d28000c52200464210100100e60b210301890012100340100c00322107020135103440031100b0020740140c00d41620301418810501031602e88282d10300d40c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 108128525 1250 108127275 108127289
    0x7080603010c031a011803140304050109140a030221070801051005100207060c211106090a0c0e06010903120c0203010b090103020102030316121409010b04020705030d020703260402030610 82
    0x62161a0350300445600c141342211006c0c040d1102c0d000b0010070725000d06501d4000b03030340004594035480d000c0010649685644050440d030107048900042d44c1c5c03408001401c0b80d0b011038440032808200d004a1054019809400381c40c0d11401d01c0008601c40107400481c1306d8080c1c0b103801c00d4034582d104c007408089000100d4a03401604041000d0000e40c0c000c40e001c0c001c0901440e2010406c40c00340034124801d4943e90000d101184002d100708281c0e02040001c141d101c40544048e22000500303548030003e01140b40140e0b1081a1310cc1c000a22907407080502030001d50f00b015600984c0600c0b08805440d05000300300990080d405c0820740758560509012042c100c1e5810b078029851a07075184032001c0c1c018030b06220740b800c000380308100803081d0016000749803d00404c8100007000d4286079000c00d0855035065041030140d03006004407008184048242c0f03030400010b0f00050703500c0000c0d1400700c84886000d041030b82c054001c0780f0b00000c0f0018a8000511580c400c1e41200d856468240180c40c5100592043c15 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 108129775 1250 108128525 108128561
    0x2101404050a060903180b07060e012009060910120501080703110105030a0b060406030c120603031407030c0f0606090b0306040804050d03020a0212030c1014040209040f0b07080603010c03 82
    0x2000511150700c004041c0380a8540040d800301386c012141e5404003d42c0c00595420b0b00815888140035451007414030202c2e07024003c1081e0160070101040c041c0f00c95001605140002c1142e9829403100b204607500d500300203000c014440c144003005090b03031b000e800050340d010f03117030400100f1070b0b003800100841920382007001c61aa44c694000119a0f940c401814109059103c0e807440036103031a400040c2018052549010030103210070080100030b0685101115200d42c1071513010804039802c00d0400c003015100b0390348560b5600d80340c141540c3da8a08004020300d050050301d041c009000c01a4026010b44003030407000d00020700b0300300406940fa20240c2e005007204030100000c004a1511482202003c0e220340103442559141e600000c156005a040c0000710b5000011a14034040c2e040c050b40301b800c00d01c1c41040106004d012034241d90035100500090151290302d0226041c07116511510403050f601030a80801c40c43c10b814010700c04c00c0c0a54030140070b9803c022040814500030300826905000c844154 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 108131025 1250 108129775 108129793
    0x6180207050d0e1c050309040e03030a0c0305010b0904050403110a0516090504150b210d03050115050304030f0e03011a0109140f0402030c0702090403031509060e07180807060210140405 81
    0x36010180c01e55003105c4074401003283d0f03001511203008414041850001070758a92070501580400e68840c80b6049007007501c1c01c1c00610040c480107003521141c4405580004440c0e0361480e099038100340c024880da415100321382000d002c000f030000303001c43c1009450900154140da41c05605083d28401c6c0c80040044645041c44d6a0040c0903610007110468000c05030181410012040c0b80c0342a880b00b200ca2841e004200225003964042c0107043c0103191490648402510040d401007240c00060001020412030966103101c45100d4002d4408106004000700408440c00c0c000c1d0000d44a040421404221100c03400546001c0340083c505000d18041d040b103a403503880c1810400298001000400c0e484818041c1c030003d80c4a004050b84220b105c1c0d200000c2c03641408104c6031560b08aa80100d0344141809003c0c03018405006140f034000c049814101126500303003004139800200c0e03070018107840c07050120008015a0003c1c400300080000300c420000c8031200031042c400004c00712400340c4290300ca4850 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 108132275 1250 108131025 108131059
    0x22103150a0f03110307080a02090406020903150c070308010609080307030804020613030804080105010e070903031805040f02090901140f0603040309030203030304080703120b01020c1306180207050d0e 88
    0x2049203040c0c0c004202003011900c410000b421185a900300f40c8400306101841411402d04110302406004058000d10440c1907580c000303000724400410040410342c01054100b01070b2010402c107500050084030001d0580b030041c000108a0300300c0784041d00090040c0307000041d124002d58010f01070b55480d002451900700d1603201070300c3c10341c0c0240049070401d008004410aa00d00d011441d0040c500c10a41d19940768a08200d040c2501c0d410382004043d088207000380510340e608120b61303004036503060034118054101c40302050703115609548410f401c64140741100d600245581e000f0102000308960b19070842c3d0b00c60301403030902250303210b07803540040300080030000743d140c400e01a603401032291411600054032540842d00b19001614100d07810000820303a4800c254002c3c101a505581d00141000002242d10001350380792013903200140501078111034041032031301b04e070809400740c526079071076042e03042c1903c81d020000e6012140c1034960740580440d4812041c412908070001240052003000d201010f000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 108133525 1250 108132275 108132301
    0x30c0909110a1a0a0513030c17060c04270f051806010f06080606040b0708040f050909100c0201020f16030e0a0f090506040905010903020709060504091a04031b0503030601022103 78
    0x5821000d218081c046c841c56807142c5614a0080c0d44560040e900301d81c035090740c01108081003013200910390080401c001c5c20f40e07000700030b41c0c007240d503142c10241d400d91402c002c084040d1200301444103c0790a000b1804000310303564000070300405518a03203158840d0322000c03d9484440a0090100c0401510750800c00c051184210a81102009122070310745039440c1624191035000540403287d03580007081c100104a00300f85508000c1c002910012918901020144d4882c0c40000411810942d0b650924442074400d505481d072442c0d41c08425650791000e00c1c41070ba07280c2c1c1d503444120300180a03c60030049904144d90614116030240d8824848641800c1035003010301802001c507a0000c2c0d48102c2d142c00728509020310726103c0e0103a009806802c1c1010b90680a0b42c05a410a9000d0b40c20300d070260300000d640d0510102580000a0707680c0e80b94a40d49022207040043c51303005e00600d82490b880750107020b000302c000c6004190903006c0710500f003840d5059400100006d103120b102c680c0705000148800400034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 108134775 1250 108133525 108133537
    0x10905030118020a0506091c06060803130311120309120102130b07060f090206070b09030904050f100b04050307060302070f0c06020d0216050d23030c010207021e030a02060f04030c0909110a1a 84
    0x9c4002c98010b44807182a49103400411486840b4055000e081084c40034985030710760700c2d0034180c3d4105411040c41c080c0d13a950303214019815024143c42a002c0d000001c081d8150341d0103042079101c8a180a94400810b046500311203000c2d01c40c0c9151501c000880300940c42062a926030103801542000019295080f000e5802041180d442c0010044140e81d603540348142e40c40303404020010030301c0382010003880440703002c03507040b040d040c440400c000c0c06140c1e00001e14504441c07491901580e42d41a07803070034110307400008400074a03411441d400454002e4000c0342c1c0c54901c40c01c540c203c0352412452417940c64244024450690840c2540203c0c00102e85094100c0403075805441c110034002e60102441c6140d0391210340410400d0754080392180851070000c03000381130950625a94001e40d10700f000000d4461861b560024414400007034040d050b09002c83c1950b00454000c203200d5040c5654007902000340c91001c90440b0509844580049545803c44200301a1104030b070300b502c48140b040102d1001a4844 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 108136025 1250 108134775 108134783
    0x1120f050309041d06070c0305030a0b030c0a030c0e0a0b0a0513180605100e150402070c0e01030b0615120a0b010507140d0206070f0806010e010905030118020a0506091c 74
    0x20000908280c0fa14003a06401d043d10107051307000d58034280d0460b4140003001d09108104080e02030500f0100b50f1101c20303290007054061f000540b180d00c2c0c2c40020b240441d00105a07400c81004c040000601c4180d48804007103d802c24121040d540e01c403407000b422104920091507010500c014240103178140306a12082c038011403040000c035014400d14000074101c1c14407040360300c41d4860013048110804855144001c05600c5030f250101d08080049602d04001c0070000b41c06141d010580e40144140d6100b40070003009041511841540c507401e10080e122400c603145409490403429400c11100100100d41d0700c40784a01ca050f0359a260100f4040180014084550400200b40190000b18906540301c200403c0701c08000e1081c0d03808454040d040c81c0e0b0040102c8284980140c111450319041000c0390f5200609181804d0f0450610380161b4140346c0a421a507055880c010039820041d4201224404080c0212150304055a4a2042000074417898100d107401c002001450b0700340700305070f0300ea0140c000e00c9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 108137275 1250 108136025 108136027
    0x90d18090213050f0f06070605040305040509040b0702010501140607061a0301020f0903010c050306030d0c02150f0a1e090603020318010903080f0108120301030b0702010b030304060306050a05030601120f0503 91
    0x55a014034059030403641c0c6011070841c260604001a24000d1080b001c1e8078400d8480c2d59800300940c1c001103c90084001c098001d9494000080070944500d0845000d00320052520815040c2804c0c03000d07c3c04c2c01101d20310007540c680b0002040d84400d104d0140c2d5818001007450b442c200603070385c450020307000800340540c50000c0021402039580d001c1c00500317074200c00400c0c0c103512024070b03000700740c2515160b848541c01d2103010828041c0036240403800c4640074a01c0d007082884ca905910225406001c80c18a540ca03681001c90000d501e040a240200902c000c81c0d0386080301200c98181c1d580c104c295000b440d202283d9502410401d15000e50003444d800700c542d130002912045018186400c0d82c1035454101e0002d443d80d010084103000480e449405071028000500750311110700300001140c8010300016000c2c8400c00002400240b007500038003810035019003039030303191941c4000c0580034124501445101d0404608003041030700380000d400d412652449402d81c0100000c5d1101e1400f0f440140007543e407400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 108138525 1250 108137275 108137279
    0x23030a02061605060c090303092e0e010e01110c0d060b0307030b010501090b030903070201050f071703240306150310052401050705060f06010905090a060f0608090d18 73
    0x962031000d403a260310120b4010a42045915005050140040c98140c54460074400000c441c0c90000c1602c91102003502e100c000c440c0020001c10f2081502904107010310f1403082110100795004a000e4038409080c0ca81801e4181c203a001503440c0314040c031810403554801c0709840e07270750321b04a1000d4140c60b0203405c00080c00d020800c0800d0802010341c01c10740789003000c0c034010842c550f48a440328004007190a401400c50903c041540e407248200300010303041000c0410101d050340082000c8880b52a40459100e40e07000c1d150341c00c0007050700210b40304041100504801503442090394003c0d0740000006001e450142c0c0c81c41c0121003414800004682c03d44101140c0c10311480d09485218091182086940e05040054095900c4000e20303050076810072500380003d10028030001080e94202e146007a520f00b259030b900380100c40164041c1e00281d441010a81440070700c2d00c00380d1240c0f065501c0349003801007064449a0665032034009440d0509141d01822030751510300d2054000f01c243e0500c00003e20076142e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 108139775 1250 108138525 108138529
    0x70f030506010c0512031008071404020a110a0f060b040b010e06070c030c08030c1605030309042d020c0f0c0310050903040515180108010f180605060c06090d050423030a02 75
    0x307000c00103210401c1000000380412104005803c2c00100239080083c0034042c140a25118142907480080340916008100054164000d004062519058400300c503081440ea04200030200800b86041c1c9025240201402c0a4207280c080c03c0d40c9000107031a15040700d0074006c18407020354061b0005440021003828007100160001034000012b10a0302c00850b280c031040441641001540000d04020300709a1004104c41d0710301009551018800300c0f400034030f040104d00500080a00400007a00c642007e5030703846148889940a0700540d00901c003151081d40340040b402e581d031074010204c1c5a040d48603111201c00040c145d0040e84d4041c05808c10b81e81407039a15801f2500c0d150022284e541e1400000c517043c05180c1108580300d0312058246401c2406524000f8005081e0b01a4060900d250015a281c03a200c09010b80001000301809000d9507916512104440e855041c00d44020085000381e2940a810510880907070701070f5800c4a80b402c201d40c0101320707a00c0500c2c1145d0105a01070082c0c81004000d6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 108141025 1250 108139775 108139783
    0x2030a02060c070f06170109090201020c04062909030601030b040f021801030b07030b1c080c0d0503040b010f0602123016180303050a210b0f0603070f030506010c05 72
    0x901c10a100503c909414552030f9403040707000760010010000340440c5001e030140380712076480c1161102c0300002940505400100e042a01c85444540c00070300342000011a00419000301d0038284415480d50341c101c803000302401c9144200c01d5460303030681c8882c00600c0418000307481c7ca80c009100d20801030f074440312071340070520503401e02e0522800010300000400601c130702e200b140c41d4002000e02d010405078080134002030660100c0f25802610400055281040001c1241145c0c002c80b040411074116076960f8200a141c2d070b0007203804407400d0785040000620103201803003038130603145603402038504aa46c540d0f0032203490300480342c0460410301007248034001466400130071603201d80003075070300600b4600205943c0c040040c100c80c0c03004000c030004503038130007103820142401580d03030600e0141c0e55002d5491080b03881808490f400072040050f040c142c4490121680402c1940c00242c804100034000c000400080b40011690f4502003542c101440d5052440f0713603c07565000c0310504100184403559201d081c0381c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 108142275 1250 108141025 108141037
    0x30c050c0a060209100201090c0b030a0e1b1503040b0c07080d0f090201020c0f03060604020307020114010605040501080604020403030c020904140f03040302090603030f18151c1409030a0c02030a0206 87
    0x2e9500040c00010380c00c12840000c0e4104450000784010507590391580845200c0744201c940e94440030011485142d5950080518020b01808917140541900160702d0048004640180300b03010b400e20009920072a0001e4a100e19000b1500030311070b58032901c0030300c440c2d403002030700319000c2c03004001c102040b400c28498a4400c0c000c08400180020703041c400a481c100c08803405a104140841c00e208050340c0008181740d2100c0e05907005a101d899400007a805030048983d1412908400000410065031100140c402c42d0400d03a204000f40d140c2500f400124821800b000d00001d801c1d842881c09414050185504684100d00380703c40e0000e190011801c01000000780d10968200203010001e600d072a4481d1a00510102e02561400d04444078040ba58454002c2d626a803903030240c000503c644d11503101e5217014030050011540d468a00740660180380d82440000c1019160108104088860110311071007518100d006501e84a10100166220089040100d81c940319580001005890300805051 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 108143525 1250 108142275 108142283
    0x38030403080a240501030b1212031b13030210020f01061202030f01061d0a15090e0d03060f0b09030115030c0e070f02060403030911090405100b0a050d03030c050c0a 72
    0x403141072001e00300d0b040d6000c80c42c1041080310b071004008082d140c05140142228024200002c0b4005147c001c5a282c030115841038406008034180c8038a4000c400c0000d41c07040c02d031315800341e5036603c400d0031800d141d00540c2040410114861380a000500784881c201003034040d940100c681070300b50721020509464241d0419550041003118031030442c1001c2004880c40c3c0184002402414104400c420400840b45141b260303040c0d0810202d44041324950001240b801110700d101c283c03a450b40135a40140502540c0448248250240d0a81d8580710f80325504c20713030b201e0150001180d480c02c0120a5a030b0020008940e055584030340404452036080c95000046210310880c10919180c01c0d0781303400001d0010082000d00030100c80218503642e001c101d89070b200380d06050014581e2454142000011890000a80c00030f90030700611041c80800148641c11400e2090b0506c510002142480440e01440c4200360b0400c4441c1d41310300c0040d000c0e400c05928000c080c0b0b8007070706005c40182c0c21031500b1440790041d2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 108144775 1250 108143525 108143537
    0x41b0908010605030105090c041503060c2f0a032003070c0f08030307080a1104050d0c0e070f0c12020a080d05010f060302160b1b0c07080f0738030403 66
    0x35008080c01074074000d010840082100d864180c54140d1100c06103056948a40e6480c03035103980d84003100074110055034000d601006403134845200500680c000500810100740302451842030140c480c484440c4a6400c0f40c042c01d004006682d09483c42c042a94409020155084a203410700780300b04050404280030341c2d11502d00500d000c04088949510b42c0040789617400802c100404260882c0e0043c0c0c022503034000004005083d10601c034900c1c0519000168014a0200c55005110604502c2d205913090001da4002680f500c3c1001e650141c820460072010400301001c4002140c5c00092521408001d80150ba00d049026a580086e075030050101443c011f0345c0d24014010b140c5c8050454000d000e0328142107262080d60343c2c0c040c080005000006080e941500001031034840391950300b807020403041703605030303140c000c1c2c840f0603929000c1502941910f0b01c00c151001041c0b840003e080400c0703a00700b450220b1080008296203254241982c041120300c040142000000d00f0a20019403186000c2d5843d8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 108146025 1250 108144775 108144779
    0xf0d050304020a0e13080703170f10060f0c110a0e0f040303062913030c08070513110912070e01030b0601020f01060303020616030b06070614070801080703020d02041b09 74
    0x200e510003e641120000030907440404c203044241400d60180d164200149507266031292078212002c100800001545486160a000712540d102c140c160180850440d02c49060343c44583c100c4190340c1c540ba80c42c0009a1629941c40420315440d5096010813019040e182e06503141d61a61071802c02c280d4804003200400002c01c014194544200005451000b200e80d5400c508080444c280c0c800b00701d05e050240400040184081855045003170007154131410310010503982c0c229441d20390b49144203141c020252003020030900c030f95038820050215000302500c1c3c00c10b500103090007010070802d04900050b116943c008501311a440c0c800c0c5008611548001c1c91501e81040020704000b00c407a500d000300d030f040490501c0001d0b004501254005508450014600442d101c02c03400703003241030380c0c4d10340050000645406212803900701c40c0c2c0c0c01d801c911809455440320780341214145000d20841901d508401c0c3c0034801440c00c034018102540c0001d01c0401c0d074024601180c1c5100b8090400400070607031002c41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 108147275 1250 108146025 108146029
    0x408030907080d020703080d0f0e01060918020a1202121005041712010b030702031309090b0f100b07390b040b1803030f0304030203090a050d0201050901030903020f0d05030402 77
    0x280014200102c050302180020b200302a503200040c1c000107060440102d000485402c0e550720a04c20703017400d030100340300c2008030700c507414000c00440c0107025800f8101840c4140c9100001c041c884010f5010301040030407490911030060345090074108071380c000c40c2c1150503c83c0c4001005440103981d0b00c00c1d00040c103800d09192020305501e160030406030a0ba000d008054010141004007811135400368516640c03070b0384469080741036120341a250366034a1810400171696803015440a41164803503042c080490702d8200c0c4481f0f032040220303285a42140b6249003400000c40701d5001d80111880303400400581e40c91030340c03a40007504440d00625031442c00c03082004200d15003101900700400c2608030345c500d02428606000c02d54411380402591174012070440e6003d0391000c0003141c0c505c0021819164580c1028600207440e940440d0344140302d8001d0107004030310341c0341c80307014101c00981c141c454034506202d40300103401800d50000f064007907000782202030042403000e000005000d00247d0706c181d5240b80900c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 108148525 1250 108147275 108147283
    0x50315010905280906111309050f010b18030304170d0906030b1c080c1f0b010e010507030c0309080706020f01052406070c0b0406030c020c040e030a1805040504080309 73
    0x120504080240084010703c2454100304901c11254075400440c40c1c0e680d070304114000d411403688420040100180030311600c880f002c0c0344402d07110401001e01c425100c22565118007042070050b00055101001868907524440280c0074100401034207483c14540d40d64008206803081c042008000d81141410f040410b1b8030049010251603241401c02c2442084d00200d1411180703116102c800403001c0c1001c100384106041034030401c059440494410408450703d12035a0b00d0780c40381200307103d401c00d8030380542d646c001c555120014106030b464605000302d940301101c0f410302c100006d034148801c040d008145200140030384c2015049640041c84014194040e0b142140c5d4010400c11545400961341c2c0d008401c064031442031001f080326407a03101ca5260424984003003d9038450802c1400003e400191103403d500807071420301b0a9000c0d201000315040900c42903600003000d0042c50f4004200c1d04000c01e0041070002051001184800c440e1070312400810103c034010744041e02c50300c0012040bc400403c00304 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 108149775 1250 108148525 108148531
    0xd051519061203020d080c0d02070501090209040c081e1b0f0301111c291201020301030b07080a051b1e0705060a0e07060f0813050a0b041203020f0f0702010207050315010905 76
    0x201d00b1b4021881c00554020050048046403400b5540008089040c80025040890408c0d0000c14000060400b480c2441e840c48061080254500400001c10007084112460020031022200030781140341840704076400411004105a601215280602c01c59803000d204643c928000d204210340d8a00c0c1c070540420740c4c8003407025614600790a0103404418682c2408201c0701e20140c0c0f204290710b015207140020310030340043d03e080341e05600c0800000705210088581500071000741d2a020056202e00e007040c400c0d40c80485402280c20112390b2a0160403490a00a0201403080356820302c075050030b0702c0800740b135510901059580d0b6101c4005d1090400380c1d403150805070070707a101c0100405e07494a04054140f410300c182800c24410210001030a404014081138103041e8044192480c403020f03803504a045000955003964200359150814110f00d00038400c03213000e50000000241449140e001188455101c48030890450090030742c0010541c508010300c455100c03504469038065810018410700b190401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 108151025 1250 108149775 108149777
    0x1a04022209030e0f1e040204120b07080705031608060105090604080705091f06120f0207050307150608070302121005070c060c0f0f0c0c030803090a0309050d051519061203020d 77
    0x40091107202c1d54420070850012010a140e820a517010f05000400034040c070750001c05442403401100d02000b02126425218000644a1356000c3d1141c1808403440d0100700d40b541c000301c000c000141a0280905130382c0ba4007110500d0030b20310749140310011808940184c2d101c40c0b115031100400f07000300e01d0700c4440290703c400d4410004200c4c400814104213050f290380300c1d0800b40000303502c0b81b00082c2c90f2500500403055400034295507468603441c03c260350b43d00180080d40c4004440030203042d4200039009e8002203443c040000e1404d603083d0707000c21080406400b8001414820620705604001c070300d00415205044544600ba000c242c0740c203040060320041600e0404000c8200401003010390003a12105404031546485000c00d0518501121070200721380000c1c1c0340d030030044200000800c00061342034a16102e960790f408c14960360010f00c84e944401700d00c001d0258000280300710802a080c4c0d00a40e100480444c2c41c0300c08521107000004440503500318040503070440712031009154040240c0d095075070007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 108152275 1250 108151025 108151039
    0x3060d170a0f200a08130305031207030f0e10020a0509100c030207151706031504060209010e06090604050d150e0d0f0203030907030809010302040b040f05120a1a04022209030e 77
    0x8040f070380d1500da001c403103402030039410042032440043c000425001d0103950b10404907a07a54031168140c0b2407a040440760700c03000905081c859003800f559401a0b0440c610702c00c009289880c0d402e042100079400007005007007003140a100700075490395030025200d503a000704d07100d0142516036420001e090419980080401281002da180b0746154401c22100e0f0315100948107413455117034680001e0501c24000440240c0c070042c0003c0c8400c1c0511075000788101700c0e00345ca401c00004c500c182808010f001e0042c405602802c00d101c03c112600b490714018502903c02c03c40a041c0304000c1d00c20504540c2d039202d4078103440d03003c00312000d0059080b4050537980e02c1c041c00214150302e40604d05c07d0fa900202c2c040105800d40100c1e007410180d0094044d1406001c1d54002103846948418802030444190301ca458814160107070900d6070781d0340105003a44a030307810810404c00324100449074480088068030891f00144d021a0315080c905040201020203d9001300206180c0d609040081c00801e0400c1c903076102d860 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 108153525 1250 108152275 108152327
    0x1109010b0c0604030f110a03020610090902151e030a0506040c03090f140304090e061b030f010303050304051005070507060c140706050a140709060318030503060d170a0f 74
    0x61490781c050f5041ca4050145c10307006030201d6103c4655240e00200e84240c4160004140c0c02040799446100201803c81d059640d0310190f0065a4124401a401080700003400d6a450341c0703000101045480d0443d4052000c000c9038280c1203d9004451050486a5503018032900d4a01401941d1204101780307803e0180030801e4030303400054041c41c0002070041111250600c6254424000d460042003440d80400103060b03d00603803902c503482140c4404140b401c0400c013100c2c4010800a80e80030325140360210314541c0c01c40da026034040c0e00c00390041d07805114030302c0d2101e030f0b0198500446218480503138134031b0344501035880c100c0c0603594458501024002c003a141c0c2c02034001200c0c00d807034280e500500085000e03111521103000401095180040b0804054200540190824104021240c65690402c50406d060012603a002c0e2402e9004001130000c0011a11524040d034001d2820b0b8003416a841d50903d800170b214081d940507040010105265001c5200040d40044000000e200c07090044c02e0f0001c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 108154775 1250 108153525 108153547
    0xd0617280209061c0503031807080d02150a020408030307090e061e0f04020705060106170c030f0a0f0b0a0f14010504080d0f020a0506010b0d1b0c110f0a031109010b 72
    0x10702c1c020102030050b4802c0c1c003002107002c80f034103e0004064108041c5c0e6902c0c101800703000110100122100d05510411300001491303540020020400745031640644102d1001c0310750806803030340151603840075035002e10010640300307401d00007580103902503100d1200c402e1410340c03001c03800e9400400301445440440071016001e8030601079461440350454000c400c84428a0005000340100341c070182251142d00008100d04c0d030003029110300d916180e00250610342c1c0c1c070702c440c90040c80101d80d07407042000c1213404601442e46a030062800d050b400340d4041013285070b000216031840150391101b00800014101084510303d0050a80400082031074507500d4282060820b0f03642c0d04403120844c040144100410b98040e10a1062000c96035000d82030321403d50356000b0a0300c09411250a8800c5c140c900b00c1c12074100920b82c903c00d45212420f071500c8415036280d4803804044186400f03003e80140ea10200c0030385603520300505030055031086550b40000d219200501401740016040030b080d41c40100100c0c2880d03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 108156025 1250 108154775 108154789
    0x412030c0c09020421241103010e0601021e190206120a0902120102040e061e060301171504021f05250b0703050606070f0206090405041202010c09050a0603020d06172802 74
    0x24480710481840203080500c100001d00c100b007807d40d00080c000c400802d02000c2010002e0040209034226501000c8810f084148694502d8801c4144d900c42e28044802c1002c40c030b0520010b5000504490a0215036a0344405150040300d402c85207580d500320090851408180c1d1a01149440b8000c606040c00c007524021190000303003007580b00741109240040d8039100890345207a44440580a1601c0356542c00f03443c00b000401d2203e0304041d0080c441c15401b0001c80c0c0007900e102d2900241004156401000ca4443c88054960321804000c0c3c00c1290500c180080345040000e4044020001041c161900342840e405030f01070301840825041030b06010442e601c40d02170303030034580d0017240e80300c1c80c00820b10000c0e4092080314001034001e818007003040305200500d8804564401c0d141c0080c00840b10750341084503450040d0081580c0301114442c140b2040d80329034040e00f00c00e8007424000a100307031141221310380d007140c2e05032240c8540c2c8000c0c05c030309400841d00ea00c01c16286190812022400280d4006400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 108157275 1250 108156025 108156053
    0x504060302090352060e030f0118030810060e060f0c010603060218241b03130602070902040302030d0c290a0c050f0412030c0c09020421 60
    0xc1603000b007500b081c15941801911101c192045044030071082d92000207000301585444403059100b003500020010b500b84800010541c00403050130301c01030510038141d030151000c0307005d1038051050700c180c510f151000344203401c09464450a40541010a854000d00300030008200140596a901080015030703000041383c02010000c0300c4868440003480002c1455000e503441e09041e40d800e000b0000b00b40300d1150b000f0704410680800340e111480a10342031000c410304212000da0124601c004d102040c000040c0600340700c00704140004031000c2c032010400c1c5982c0150058039102410703c00100105501000042d0003040d115000307604051458001a40b03800003018071030305104130111041c04201c0030000d4103201008000d81c00c80d2491990303200d455104800c44541c000146481c040c0c03c90039000ba8140c5014640a001d0b6900d818100084c0c000e07002e1789100201c0a001030b140030880080c07074141075400a081c84040040e21075203400e0048000060030a10510003c140f68140320228041e000c0f4031039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 108158525 1250 108157275 108157277
    0x41505070206070b150111010b010801050405090a0602070605060108161209030e10030902090c090d0213021c020d14010e0f090c060a0302090411040b07030e0d0605070e10020d050406 80
    0x203200c012500100d646845a40002403000e00f100c000c12104080c1004000c80204007a030f103e01021700d040d500705088030300003620300c1c2c042565100104982c1c501a000707164072052400c191403080e1142da452205a80000c10308452082e1104100300340c550f4014012940b008074091402200f820010002d4110707004941c0071000701e0b4841c005c0c40141401000c1400506402501c0782d0611042c1803402401031020042c00c901c80c1080e440841d40c4a0000401e0f1489040000d0400000342e44607804c110aa80440001100c119000e10824003044001704070040c007074400c00805a65942c1c41c8100070203e1301d46005c20008075030484018001c84980c3c112480e03111030000d50158482d140d884105207840398103003c1c281e106900040b1111a954150064401c0c1d02043c1c800b40402c810521440103980a03a00030504802da0901042c00802c0c802e018416000602600340280b031802c9403182c3d02911802c40d0040041042440e070b011407800c09032080b8801c1d6220344040c09087e1101200107156101c0c5100f008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 108159775 1250 108158525 108158527
    0x2031504050705040e1518060a0e01060203161515080607020604030c0809120319110a170708090a090615030b030d0e1c2a12030507140106060306170102041505 70
    0x400c4000b0061b40c01c1510000203000b100100345100d02d000300500101c03040c90140390f401c9800101d00c6020a41241600d403160080c5050840007030425942e20380003a0141c601d40514000360340800c40f0303480307100b600c00d45001400d1000350400070018941007024008204641c0071004004c0403e602000c042c0c43c0a900400446d51a104440002d42c96800c41820035554080091040c803d0350381d14009170b43e007a00d2500c0700c10300101540235458483c0c54409014003200307521040a0840301c0c0d10740c000e00110340b042c4951410f05120b50041010906c0301d4021002440e42c440f018031020b00380c40003425090445103010300031100103c02080e21443e6020a090500036100003000303269441901c0560744007003000c0f17060190040c0d801c00c1c0004280240d02a407200641c03080001545c247d121014007503903100c0c21002401e101031364040740c59a2000200b510310350200c5503500c101000030b00445000f00441c4d500030511034244494400c43c001c00641c4100141e00c1000304024008008134070303508500d9070342445 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 108161025 1250 108159775 108159781
    0x60103020f0303090a080f0d0c0f0f05120c010b0a05060a1e090803030f1e0405030a0806010306080313050306070c0c050f03010b030a05070e0709061d0102010605031002031504050705040e 82
    0x4203265001c4c20651aa00008007840860034540c0000d40314224984403084401a80c059402511256001140502102280690180030500404032442543d200710110b460f8090084004c1582d03030002e544203000b0343d444d0501c2048034640319100c900500800c0300c0c060324192048001619500b0314908040412406290501184d401242558010300e140c50669130340e40b50031020303901e050340c0c101c13607040541c04441480040340b80c04221003445554001e005501c1d001d440001912ba031200100f403181095107036007020420a0301400a004190004842c03410360601788400c00d070410000a00f42000c1128401e45500401ca40341000d40840300195507070070911080d5400300c0d000d040b0211119404ac03262449400030010000b804030300302c501c11211800c0035243c901e41200c5400b8548903c0f400101c01900244071441304810460110005000003d134465413400032034103180186661030a0340303601104214015148540010b0b145008603003c014178a00030708080c00f54056801140c55044000e400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 108162275 1250 108161025 108161029
    0x20c1902010212070303060f0f08060c031b0a02060f01080316060b06070602040b0706050a0b061912060602070f0b04030b0403080712050a02090315010311060c0115080f16030302060103020f 83
    0x660440c180f00100e041c0d03620b24480c20054082d0445129201c065400810006468100d45d899641543c1c012009002c1507103520380d04080755040601001c900f0f000480d102040d081c6120001d0800c0c0603103070080c140502e00b201d1010741040050388911504d800c10402d40c105a90301c10b0f6800520b40e84140c0000d115a480701c007090030740c050884000c040c5440050045601c2d810f4102500c1d18510a000c00d001541e6218003c405840c0c1d0304c801141c002d682070100100b031000d5540c406003040b0440c0340c5070f00d084400b69406016500f50f80c0c04140540c05c40f4a050000c20f0071600001e0252042060081c9800d24640d19440070150003480a8100041e50f000706030414461030748103002e84c0c0c1001d0309010714282104440000e40c017440c5a14400e20441e0689400400080d00f03881c12203402880d40000c60070b103d010300441d80e105203c001615541d4100d50028091008107180141c8903e800801101940e0b4245030b2608008150008450740c90070000c000290380001d056042d40d5054074044205000900 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 108163525 1250 108162275 108162283
    0x3060b0309030721050403020603060103020705060403180e0f0106140c0109050304050a170d1202090a0801050f06030616030c0311030f041b030f060b030a0b0c040302010201050a020c19020102 84
    0x44894082000010300001e9080000545250790040c0c54100d4611031a040c03001c112507041c1a0140482c40501c400c1026240c414051540001d0605015203801d68030f0362442d04020f801c46045000c162824411031180c00310412002c0540040100564141008030404248000510500040109074000d4030855403510040d0b405e81c403452402808800041d160041d02c0c2d804c83e00516008599136000051100c4c150b852a000220480700a0009100c0241045602c02d0850b00522150354003004950700c0c94540001c0e5000a01c0d444000203041e04000078902d805400140c0414840c0e4042c4040c4100b00d04403911506550b0700c1030500040815420f007007034018180c132652200a4130404000c021610100f820203c2c400ea225000006480c010003000740c0e44591180005450102c03500d0031400040c03515800100002801000c860180e4150b035108201d082d03044590329050070f00803e08004550f024015280c120340140f07015414100d140419139500e07500f40d041e1200c49401000a4002d69000340 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 108164775 1250 108163525 108163529
    0x80d020310050607030c0302011512060e0c1c0b070e010917070b04080c03070510050409110d0606050a08100e0609040f06050705070215090105161506140102150702030a0f0306 77
    0x40c042c680c4031084c41c24040c0500c1920002a405542440d40d50318030588866000400e8800d10614008003440d1516a40c00600003104810000d1042001c03a1400da03558070740901c6500d2410201900d260807518141d6121280909004d0a000d482c090200c800d070703049140070055415454003d1038039101c0310040d40c0340c0302c0035601c0090000000a0040740201c4040b8100209840507012255195580c105015202c0300b03e528510029030700344014081310074286c000400f29843c0f400281e00300a00c0c00300e0801110419801200800c0c80002c84240031600a900030394040115401000c590f441c00c6c840241c481c40062107544242202c000003800c0240172425140d1a03034009500b001940760450f00174046501500c8103904c9242110340130961612001e0407139181e01010b81d02c00781880707d001030945006541c03c10440d6440c4400841803141c404900c10a002400b1078072104031002e181000280c200106940d05d0300b4145107420401c00407a40000840f01941c08a1422250702c0204070700483c0202455 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 108166025 1250 108164775 108164779
    0xf121302190303030b010c0b010b09010c02060a0224060603071103160303060f080f0c0904020d08161505070c080901020312010f0603140106080106051806030f090f0307080d02031005 80
    0x805a441d50580007540510642c0d100361001c1142c900d40d6001500d4048129078001c207920240e1006200d003e00c044042c0a2452043c1003c3d128007030a540000c0d0a50070103840640140e100943c1e4123804c15135680100f1000f0a0046d5015075824008003048140c8002000c01c0b05010410380d5000c0c610008108981c06011040b03220100c1e2129454001c014000520848030303140018000400c490001085560140700c0100080c100e014145041c8407840100400c1030ba40280b880c2903510204203c9001454804828103030400c070003080340b920f5040c4840382c50f141141c00c1e103000c0c20071445c960003480b5644580d4028580c10b450b1015600103e1840c810754140044404e06a030000501440e050b440800350780080c0c5081c01003074060704203440303264024455200000d103050010040035004d500149440544500b190004038100404180301e640305891859030000c00740708015881809118202001a00720090340c03400f05240c80c2d80c0168042d40f020500016400070110700c0d810b240760f00d210300600c80 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 108167275 1250 108166025 108166039
    0x309090906061502031206120717010507022109090a0f0f0207061803080708040f171b03180405060a05040618060501030b060d2408011508030f121302 66
    0x800d241c400042d2005204454141004101d540035150003c8180c404800c0c85400c24034499403031030104048041a400360034514051880d01081001014108030103051462002182c541841e00000345000402003000407103480485246811800e00c0c0100c0d000244110303403809603070302d40b0285c100081c02c01c01500ea0000d49451901c000390310558000e4122940204d004010031403404402030008600700d24005d000481c2900029101405011010740060280d11043d010a105070354501152031001d07141310180e240070402848060381c0702c3c1e8101d80407091030041d50811fa82d00484062903607000218a200e139403218002921501c8044003c00100001170060081c0e80d030750ad4843c4901c031403600740c040354541001e2000c41c595010b0b024500540b0170103801245844440e942c031800818441c0170700341c8208241002c82c00040d004054240140c002c560002070859000760078070006c6081503000300071540040c401321441101c28030a81e16080840025552155150a01c1540000041e0340c02584002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 108168525 1250 108167275 108167291
    0x60b0f1207050102010b190302090703020c010923210a21140a020316031107020904080a0f030b13240e060f0d02090402100207080a0803040605070f05040302010804030909 75
    0x1034000750081c100c4000307800070461031a00d0790500014078007032840030039020401d4200304010308289a0341e80d8810020719005080603610800d0342c0c01d560400c0c400382c1d0036049044222101e0014030300850040c03001903001f003001d50445512203c0046103100d251401391000729055072681e00528000010040030380f4040103d0903281c030b00320020100002c4807080c0032030b04c80001c0e06002103407084be03024000000b207902c40300c052224124003074100c860b2400b4000f44240321990050b11442c80250056100d56805502c030100c10200420b0940302c60540d07002c05003458215400c60b11010440030013101d61501c0445c008003c1490a000d40d80500c030448600000c40c0030008811901311401401400c044880c100c0c2001d00808001c00d5004040c3d0295010001c2d0000c18010b01c0d0010082030340cac5070240142c81038159a02d09150414020101c20344000400000f0801004114456682d11a01c941042182449034800042150007580802414400a81e000c1010325014002460003080107101c10300c0414 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 108169775 1250 108168525 108168559
    0x3090306041e150203150a211109090606010e0103090b0f04080f22060807021f0e030a03050402040b010f02060c1305060304060207050601080c010507080706020f030405030414030d080103060b0f 85
    0x142c000c44078580c206e074550090075003528000c0d00c04802c81e66401d42c0313440414050340081d06c0140e40e01f80111400340c0b100d050000360b91681005107214000301c001a10681c03904400151850000b07905c0302c0c0c10189030240003000100e000b1021a0800c1c00c00070046896925440d14100134420104a415940d1021403540d10501c8801d001d4840d00e2070300a41031600c0c1d0354840d01501c000400740c1d0200c0168010700243c04901420346103505090860341e002281d840b04c17080100e400d5a12501c149400280c4940c05c02c004d608140c0035168a4260078070b0580d14101d5001c0009443d94006400c040c2a0000010340c1c6032403810316541003002c2e041c014109a940d0500d4580312009500455040b44c141c05100300008264401140040700c204068660902d040055640c1003015400603004442d030325800d20641008000002c06144101d2142e002180c0d55410711000c0d0034543c0900e0100e03442a40008290700c00c00341d102041d6070442c1d078008808a00ca61403100007a09101d01c041c00315800120400c0c20003500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 108171025 1250 108169775 108169777
    0x3040c0f090603080417150a27030807050715061212030b0a14040608010501121403090609091302090421050903190813140a0803090306041e1502 64
    0x11554500300d416100d544039288410303101c091101901420040c4010440e0b6540d1060042c1c40d071264070103964590700c4041e074000031040240c50418402d548c0d40d142c25000900680911644440b904055030100c01d540d03401014184001d00c0c1904209000c141007082004c07040d4500702070404405d0900100785c03a51001c40740302202c2c0400b92703042266444c0001e030382802441245c9403204007170b041981190034078694040e080480c1c4610360304580c0e0340c00c0008028a0030321030365000e02000c40b4014148215800e00a5031021070100b0500a50402c11100d00c45555a000300c84141c80d050390070101d1540c4d003641800081c0c0071048041c1d0490560410002040f0002a1903080c10710341b002d40f000700d1003004000b26894010411010382540c441119503900403400403101c60601e05c6500301c649000c0e007008076410300501750b40c414440d041c44019600d003107151030413601e40902181c0300214205149a0006503484002138806003207840e10744051000080c8508450000d190808503280084184c12404002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 108172275 1250 108171025 108171029
    0x170106020a02040b010804030e120321060f0319031202040b19080a0c0909051f0801020a080f04020d0f02061e0310080d0c06021c0903020a0c1a04060c051203040c 71
    0x402d44c58090ba010070b96010740e02150140c4c1d003541e1540340f032403001c5090018602082c660760000b4841807001840c2d1a001c2d205102040815424070211401c0031000c3c031031031402489005100b5005401c5024503211403101d58070f40c1c0c5801d46401e141000178070b61900c00031f1269801802e140d103400640c4441c548080c4801000744120742c3e44040b441da603000045001c541c80a40e042c80040c4000d6410400c08100b0f4015541081d0b10803c0340504402c011007960040c7e1440d4400641650085043c0b003146070001040c0e40e00c4080c007900520989400da0002c2d510001005000300b001a544260800f551103020030703100c10921003554604051140c0c1c4414025800403280c080402011600100324030f51301203000c4222102036251880200402d65170704019411006801243c0c03210704480c00c1c41380c840b600400310100e000b50007500101c0340ca4140b0303801c1400723107400c03442c0300350446020600e0400c0d4940c11a0201c444620313115400300c0303861a041d420020a880035000b410b402000b40000c1c00409003e02d03013 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 108173525 1250 108172275 108172279
    0x1401091704080c011223010911090d060c02010912030914031603260a090506060906100e0402040509090606120f0d030902030f010c0908190f03050703170106020a02 72
    0x1031244180c0e4411014070960040e100507802000d0710032203650040d0750b44034001c641d241020030b8141c210032007030304807100c134041903490a110040104a004598452807800e0310030b01c2c20482c6014041c07408104ca4a01d02000149407560300c3d280814154402c3d071005144036401301407110300d00c1007080010060714242500740ca5100c1c6080480d0504840042190700b041c800c01c1306103454007001c1d1400e03a410f010000b81c86040408040d40343c00f41c1c81c058050148103003031600d000100f0703407014103240b0f19040004041600403100c076002c2c841565a502491901d484803440d0100b00c007589603010501901695011903084248202400240b03980030418a2143c1c07025200a9444c54072074500d1a511181c3c10461682034008000e6540414801d81080142c107001070300300c0f0000d9805400c9107003100c0b08180e041d40001e11002051044840a0000c205030f8a2000000c43e040c80182d01c40740c2010300c10300c4004080c802c00050540c20140100344200081108503010704d02513a503080041c2d103603030408208034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 108174775 1250 108173525 108173543
    0x81602160b0a1b0c0603020c0304030b010806160f08010911041707081501030b01031e2909150c1602030a03030606030c03020f0d09140313031407061b030c140109 71
    0x7032001012024007400c221380007985541414038000040c2c000f9400036580380743d140030401010020882d20486036001f8078008005001c40c1ca40054040c5000900341046810040010b85280d0502e0780028260705603288110b000070300341c0004252442c9480f4a51001e800000903100c0007500c2c0b100401e00d030f01140c2034002a02d0340d5006010160444540901009181103200001030001c2000c03065002c440f5120080310200d40c9840d6141e0880454038071344010380e05000d48220204101c404614140c208400c01c008118002040011b403901a8008000c40f1603c100480c4a400c140c60000060611507000760560b102000a404c000380034007200d005401c08681003060900c1442e200e44207c910081c1015412030400c001030b803981e40940a200d400703a498010340e10b50245003000500c014441540341030070a000c100d1862030040c100c6428800e900c0240c1e00403020030095203070400300c0543c5265807103400e103001c403056180544609003166405084240b034080c40f030103c10015030200c2e40046c0203003103113 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 108176025 1250 108174775 108174797
    0xb03090601080303160311040e0109050a0c050a0c140c06030906010608010806040206070204020a020c0a0909030306080a03020304050904080403170a030513020f01031802040f0b120d081602160b0a 86
    0x1d2540c9200a80d40715100f0050508450f417132a119600010039200850717401440c180c1d43d000c4407040000203820407900180d07030f60180007004013144110803000d074803802e14138203041c2e615502614030184410054081081d15203103030f064200038400044190170040c9816200d0030441000e136070783c0409009840120b48080f002084102d07000039002e00c07644c2c4c01070020345080242d600744006500103805090551054068001c000d0342d416203080701616a046001030611900d05004059803166030000081d034000c985810080782d4003100310b070150388058903140c4c11501d40d450403948510442c0c1c00a03040b03180c1a4038806800700e1b90b40c010114400140d9061100b9120000c808443c1115560300a51204100000c80810350080d000ba880054150b0039610030282c803500458152003208003400703103095652080144602c0d000328504040c04e0f444005000c6051200c00160207980041c04426904952030000703001603208010314160071601c82004c0d1851607550b00315240c150000701c6501c0c04a860103041d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 108177275 1250 108176025 108176039
    0x506060a0f08030a11010b09042625080c010e0102040906061b06050603010209130c14160b0a0906020703020106030b18060115140315180405060a0506010909060b03090601 75
    0x440141d0b044800518a0011140c3c001c0d00c0d42c2c00c05a0100b111952074006110380d613a5409110361003540105082800d40c406102001181c5141c0403001c1c0c401b0006003c00d610051a4038a030300101c19021a01d41c26624003420a402a8080c00d0343d0b50303403a0f45c2003420f003100b0850306401030011208045001c0c02010307101e10050f60408480403120120a5074042c00e01c0c04070b03400b03800c9180c2040c4042d00061410070b800011524240d007012881d02415151b80112400e1359100d540c100705c4411041d030080c01c015110b552091442c4030304002030300040c180804a50440170642c881d40107a548598115925000b5280181c041d0030244801d4a054482c0000611030100795480254080442009480168248040c10030351541c0d101b0740200700640704544001500126004500a050003410307400f4105100b400c1206204554240c00d12018a860611000850028945401030b102c050042401c1d0390b03141c0121501841da901c16801a03003809400240b198101008600400a1a040c0d56082c0e0301c4000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 108178525 1250 108177275 108177299
    0x706020705011e020c1902030a0201200d1e11070303030509150112020f060f071719090e130c03080d110423030109020f1c080f0307030c08011412010e010501030506060a 74
    0x6c0c080d402d5080500e031040190300c1201c00c00812031040720191011784074441007602c0c0002d5034410b41d01248480c1008039402160740100150000c49180155070b040001268940f21280d501c0005c042c1900d600100d031000c1020700c03c1c42c40b199a542101340196075a02203411680d82c2800c02a401505c6a410503c45030130980e048072405115070740014505202643c40a11000214003080c2c1c81c2c1005100500b524407801420410300c0d42c403a501c0c11042d80c1408542481080040d2018404803848542030000807003800b05c0d881181e800102c1c0c0c42d1a9082011024060b2060070414002003a0028010540e044c0900895061b0390070150b0500002610b0300034103080301d01c8803001952100c44001c0e0900f96141c00301c59181000d03040c0381d01d0071103078081d0b0781c0f80e01c1d07180c002d600502c0d0008004000c000302d0961500c2210058051031901450b654900700c819055401188051030042d01c241004402e200000d402c0320b0442d010002c0200808d6a49080058440740c06407103c80c41031881c52800959100c0410b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 108179775 1250 108178525 108178573
    0xd09031109240a03050615090115020703060c030f06090c140c0a08031f060c02090a05240109030507080303040611041401081305061503010c03060b0706020705011e020c 74
    0x140b21240800480e401e0000301104070003115442505050040001807003405518082d840d10999040d041140e074040280ba414141c0154154104000c1e2139041c5903030002e10f0800300ca410a80015001440d0304044002d00501110300c00700c00d0401c4000601320360386502a002c000312942da00190806c1800800b2030070701c143c40c1000200d031f110404400104018000443d002400c401040c0b956840f0000401881000740d403010002c50101d880c0d8505500306083e80c9544030040e00780402281c036141b90181c18110b20340362003404040000b24001d0407a4058078002000e942c2000c200da802c103683d00e0480b65280c2c02200c0440d402c43c240380b00c1d95900605d840039181690860300000c83e0345041407004665440000380030000704019a15010041a010701c103450041816610013014003846009250a4482d480d03420b500301843c01c0c008000da04508000da4040591140c0096a81c116908100c1d02518505e02100102c414222641e00e24200c42e5000300034100402e01030ba1112000e03618202c86500c061 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 108181025 1250 108179775 108179791
    0x703081b0a02030405060d09020909030705060c0304030815010509060c0610050a1203180510030e0c0a150e03030d020c0f07060c1104181217010801051003030c030207080d09031109 79
    0x1d010a000c01d10700314000c0c1261000c1f000c0d00141c000b801d90000340800f401510340000c190400a0030805200c0c05000303250b44210307140522440d42c2055600103248890052407080f080c1095603203100745031f00c62300460307204000c0140742644450b20160a01d48443d000da80103c0181c004010028540c02c280017004102c6030f03401c40004410859403415540c8400303d44200049421510002c02c2c585d0b103100d0881340fa00ba156900148080030054000d2070044900e5101348103c1921008110300300000c4a004800203046c54040406000349000c00e00d14042c10f06588000390000c1404552038000003520000c2c004c802c0100c0340e50741c0e6076200076554223240070f2003d8072030502c003050140282030079046100107101c24009401245039945410882c0e080d80094130300021155500841c031520399202c028054807520000b0406410030b03901c1c08924040c2403000030244000c0c81e07400e006040c024002e90008104050950b05250f0300c42038000e00c0216a400308948003607402c1f0b03420019040c44940c4c2d40c0304a800d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 108182275 1250 108181025 108181027
    0xe030a020a1a0706020a0504090f0b06040501260106020c031009050304050d0201020c0405070806040b0f030a14070f0e01061e0806060c01090512120f040809040209150703081b0a0203 80
    0x2409003001e501082c0c140e00c510000010440c2100040e031920084c0304281c60303a07542c541ca5504016540c070070b403003603450f064000508014002d2420303654282200d046803424240b1054051600d0303400346500401d80400c22a0442180c00000e0b482d80200c0c843c141070b0421010382c5c0d20031309071041e0407044840801000d0003d62040c00140928180710005004103401401100d428048401c001010707110121540d40000b01c0704802d0103014213090090801c1f4070001c8541001e01000a070110b55203215080020b00844982c1258558910051100714064212400078a5000c1e440702c60144030b001007071103803200080205c001c0c200303034511000203441ca50308195505203054445c0010002d82d47c00c1405000307510755880755404d00080301004503000058000c00426250b1ba09100f40d00701070007000380501c200c91003800800c00060420004c81c3c201307580031030f030060b114a01000400e10084109204c15001c501c001980d000349900a010a40307d00f00004003848000f48004410510b402a01c01707290140e40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 108183525 1250 108182275 108182279
    0x60c030928140a080303040309050a0909020114070204110301030807150522060609020d0b040b0a030c0e04050a06061707050f01120207080c010908130f0605042c10060e030a020a 78
    0x21100c4948440e002000f481c248850b5191a125425980107850450100310300c200c1c01c00450034032054040041100c1e8100700b0403081e030764002a00c80085504403e100e00c00006800d021945d555103e41a01d0600c1401c0c90340340e62316846c018444d03500410742611085021018140b840149009961280d03000f40b1800070b005d1007108102103080d0b04030000301e078106d0311200007040441c0f0902c06090340424803040172600030355543c20300040b9040908242d005803512401070010881c0d030701041c0304545004c064060b80384e80780d0600358148448901d00400312410407400140b409000d4118000040c8a442642d66459490b02000310086040c4c0040c5d01242c0300c510141c50f15002580500910382c0280f9180303241100c064011800c640b0385002c00c403071648000c14030503003408402c0749510207008a100c1c8482d1082c00c2c440d001d0203138044ca218200301110600c0d00340d06418485812105280301c240784885943c100f5450b01c0c0d07040c2c0058003076400040c4800b03010711010f240c0060810411500500b24181e04d0f4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 108184775 1250 108183525 108183539
    0x9010b0f0a11010e0c0f0405010e0106080a0902040219120b010e0402070f050a122c040c030b180a1a091f0b07060f0509010221090c060c030928 63
    0x14101a100c1c6041c0410361074401c2c0c56403828010420401e826001500900454108103c034241941485170f020b603103028014440184100522415103e4a00f010b00c1c0e40d80c0e5984500c005803000f404000d4106001007548100d41c01102031a811842803900c40d0302c81003003030498800440300074544103400108000652015802c1607801070000034062806001c0551150b102c183c034048020108444542005004100003a480502081c10500707000c2d1a003030140e0813104081e201404c02455034801c50740ca4410a900303e00039030003c8100304025000f404420003402c1025001c40e0221115000241000040301c491640840114160b1400411803600c6440382103da40e1662080c0a0400c64114540000b00f0030f490b20002414203d4405d000225040e0040e00e03000094500c0505544000d03801801080c05400e820440f6440c00090203080c9001940d856451915000f070f02c044c91741d0000c8000803c004804400f06c000c04d045001629269056403240d001041c44071074031654041c0040b03072010123001d20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 108186025 1250 108184775 108184777
    0xa0c091d060921071205090402040e0f0108010e0a1502130b07051b01031406010807021608010221130b10050916140306010f05030a06030609080c01060509010b0f 71
    0x2a40d081010000555086811403038540180c1d000b941d29408201607540c6140011410502d000103070b076038582081ca440e51100e1441884540960038000d0200d092446611b0703a90685000703094020b409501030030a101510b100c40c03401e0142040a500b07114000d1a40b04d4001040c0ca00ac40c0d101030501035400d82d49902c90000e420006e00003010300c0c08000c0004030030100d02c010b03190050142029016460181552000284154503050706143c00d040034000d00c2084002c1c0103600943c00c1c2041003450380c481c5012800c199100d1040031201002e1040498a410154003800b140501521300180c02114500b42d8000003404030b8a0381280d0059444081c000348881d421150000b0900c0880001d03d0740300c0000800a080481d1070f402900803983c414000356500a410b98049490415031078914100500002c02c824809607103001401400030105e1a5500c030b40c1d0103400119004002000319011618002c0d00340d60190002030070350b6003400c0001c82e4a29107100304078101c96003401d49619009034440a1401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 108187275 1250 108186025 108186041
    0x10050108040f020910170622030c020306090703020405010b090a1206020d0c08091009150902011103070c080610050d1104020d05010306291e030a051605040506030a0c09 74
    0x40b480c4141504801612030700c032185c0c002c2c60640d00510010342414007030354203083c414000440702c0d44038000b40109100140c0c1d071060030000c040621503554840c0d040944050f241d814000350144207100c10802006400b08411054920813507013403003140d036944400812800b9540d013903030b8011486041080030350304101007400e4941c4214005170801d101c6000801c1101d6140c400c44000c00d040e40200b1511003001d00481e2910980003200704203040203038603030144201c03804000700203c903903444441d0b0642e8050f4002518500d134606c22265201d20394580784206007450310440c20740740704042c08558040c5000000d002900c2010701545402541a1120200e0440d03102a00707800950070000c0c0f020260480c02680e010310f002d198080f9a8000d000078581c4018070800c550340440d4010311800d00b2942e02e211101244188003100319148404081c0002d041ca901480020458400e20010f0000ca00d200030100d001c0314421141080300c0e503680350a00d070312441d104c20018103542c08400240310705a00d9a0011030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 108188525 1250 108187275 108187283
    0x1401050313080d020a09060305090a0b18120703030c0f0e1509030a030e150901120903030e19110904050307030f050f0c01050f0105040207050d0c05030d140f0703051005010804 77
    0x204101d11621100a03a6000d002c030310f507205800081c0141c80c2c941112041000b45198582001549085210152502646540280700c0e50b01d510101e4250341040300b80703e141014401c06e4880f141c02c181c1d00041c0c194030051040300481e05200011900074003500320a40700310759940765012180d0011080158219820040117a882010f01c84195151010000043e44601c00d49960341101d030718004001100c40d00c0070b0b07a90b1003550100000902a40e12000c610500000744c031010031348807401d10302035000d01440750000820707100b508500500c200145568052560003a50800c031111040000e00c004a0300448014001d584200200c0700000d200301c0d580666035034640b0306581000300b10748060044e5481004107403a241e4480050200031441422490b0050604640452801555642c0c2a071624405030100c030a22038010f0000381848014011a0049000036901700810031000d030170304004080c287c80e1889100c2d0b280740010400c40c0079101c0c207801030300d680e8140d1500528140c0110303003902008104507 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 108189775 1250 108188525 108188551
    0x30c0207031707020109090e0a0206180d03080406051b0a180b0c03071b0503070302010f142a010e03180a0e012904030c0902160f08030109140114010503 67
    0xc11024490b001221030719128440d9218543c0c00018201d00c000e42000c04004d10703051207502d05c0e000c0003c04042e440d5042c0e480e6901c540380d41941c1c84230040c44034442500003602c00380c0c1000f05a03000000501c038522520042010b1385411807201d5000100c0e4840408000042243d41e8506015903441c600803144004082032598646d4445260398101e121031160960003c1156400c106420f0b4101803007589076007140f04518a0480003a5490171039210181c18050b00c41e044240b21445060030744a400564a401551480e41d844c4641c07032a04001c0184087c0c58684020268148042c0a5861415002030003141003c241c0e00a43c204c100164091aa001003074400004498185403140ea0081c901c2c480c0c202066150307400c14900f030b0101c0d141500800c1100b00014800540600c80c400260741e215240161502e00d9500d9517400c0721418003000e032107410420755403010440864021810ba600821090010502e0b4181c8004001c0b401e0056001069036440b1800207944500051a41710140240d41 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 108191025 1250 108189775 108189779
    0x170c06071e021e0a0801150501030903020709050106120609020306130b03010e1b0f10080f060f0409060903090906121709090901060617091e010b1503180319030c0207 73
    0xc01401d00c2c099643e50b038404402c0030f1646494030031542402041600000c0c0a0a0540b42109505441501816041c90398524000703003454801c114800203003485890400007942c41e80380140c00d603900c02210000381390030850041000349840c000d0304e0003180042d000100940035005c00c1070140241000c0309401d5075030b8280010340801c2c00c0100701509410210842e03202c1c9c1d60841800101c051000c001070064026410b101d02d10b03907111250540c00000204400c10a0f141e140004030502441120b042d0301606004640081c400c1a034440601d05219031180e80c0d4242c0d443c881d403003da401078070550581110309603140000c10910050080601e002c4424035182c88041c0000424154007502d0003402c613036440b4802d010880d0030031800d290090f0312a03480000b600d00710250719510003006c00c0009441d04100c0201007020000d41050b10309140c02032000450040c1e040310300b00e481d04201e41504022042101140010704044100e44082c411980c3e00c04110500746010340144c100c0306540011880303a5940 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 108192275 1250 108191025 108191029
    0x2030f01020f0d0c030902031e0703020d06020309150112080f0409050f07090801050415150e0705090102010f020406081b0c030403060504030809010c0e010e0a03140106170c06071e02 80
    0x51201000c00d41000c3e854042d20b111900481e00100500c0e020705280070070f4000540d03000100c003601e01c59288980107000c044d051f5441c1c1490483d41c0000e4008641e40c44410812003550003442c801c3c034200f0100c80008034000030501c0f4008080c0b1480210705108204070011034085002005aa0b42c0c000310246801d43d1030210404a4100b11004c07000c1c150300106202c20681e000003860020403036500244a03900717141d00d5064901030501500b5071115901e00c5004039510b450850b0900500c002c0c12012102d03c1d10030405000c40d0b224080c42c1d40154030340354044d408660380e482900c051391402c0d51685490380d01c42500101c581c00c410401d801d558000c2c09100701c000c0c01040104040c40c450017000c250750806280203403203420b0180400381c0a0f4180b541c0460502c0e44058002c410010920300945206540804151000b260340c1000c3d01400711a14030407004c201c150044012240c010400d0b51100070350708907042e00c45050b0b10303082d9480042000b6180100e003ca030b240c1610f034034601c80f2141c18240c1e1540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 108193525 1250 108192275 108192277
    0xc120301060c020a08010c05030c0a0309020301090302030c070503030c030a031515030c030b0108060f13020d0501030b010e07050705071509080a05070611011a060313050a050c040f0b0d02010c02030f0102 89
    0x21215000440d0308849100311300f0f180341101c1c01445404000d00040b44443c5d0054603c0c00002c0940380340102c0400e19521162098022034171050700a4000c103e00786050800941b01d60100038210707030038410070700001885d00b0004100c6090002e46e81c00346007400c1e80000100e0140454550401203d003401e000031496020110805807410461b850006241108584c0541a90044d880e4141805501020031125844041030b030040c6410403240c0c0c0501214202164000b030140c0c1000341c800529110011042090f000f4000e0305075400ea20003040c0035522800c085070310788244440100190000e0b84c04000b0480e01425101c0d00c45000c3c00e000e240c0c161995050781c40c101c502d203426202644a40c104000d010b03003002c2840000c40c4094020700514803c00d03502d02100711420121401603d000000074401c10f60740215038a015445410b441d00d461080c02d00b290340381308900401e4800c514020120658060520030482600c6014240800710381e0190019902c0410354030050360140644180224160b20070300c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 108194775 1250 108193525 108193529
    0x52a030c07020f031504030f08040210030903050409020d0902090108030c0304330320040506180411030103120e04020a0c020904050a05160303030605040902150d020903030d020901030e15060103020c120301 90
    0x1498107101703454641401003018008440000511a05030705100240e1a480201d043d0358540d4100400c2107000703860100c0d0304d0300c1190b1104a1841c13000c0340725800781c103542d041010803a000316002905031f40c80303511175501c80c811010f03c042c07154010041001072806d40f031403043c09001c400c41c201124114254400f02107000121f24800000e99400302c1b030102c8240707070300490304107204540058189401d02c2e0110307010344903002c91420340810482c10400d607940c90360048540c0d6190303952503e489503560303d46a03000c014841c0c1410042a40b4010100720340c01c0600c01c3c1e5009290581c0ca02f064500550240130407030070068001c1d0390b140141b120301d101103881040720501a245d8a00b4008016195080c014112052900424440d40c10456200c01681d82c00600050340c4142421080e40c0d1158a070a08009100d4064088c1d0940804540300f11426110341c050041c00c1c1d03081c0c0b002c0c001c0c250038010f4140c595182107100c55102041101040e059403081c4d010305904411002212100320a42c046407502c0d410903 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 108196025 1250 108194775 108194803
    0x2031204080613050d0e060708121e040804035307050714011e08060109080604150c0302070b01080c01021c0806040b010e060d052a030c07020f03 64
    0x1410054100100903096100c03d000350080181c1c22243c0c3c1c0e06895003171020324103040000c144d010011503550b4404641895900c90340b010341da40380b1680c01404440040b550343d44140d08040800c1540c01e1483d6203144240e90043d20f5a14007070070340c2e03900204d0b40c2d0301d4054030300c000700c1722224603030b21081045445074070000d15080f01d0113811120003401262103000c00030064184040c804e4400040d000a40b8a0030743d807020b58076140400000c1d0048501505101d2031180d84c217200c08a0140d00780d001030001d070144100381d0b210034405854141c01c50f5202c0050710014000b558003c210120303940c440d800384038880000e240141c074103500c688034003588250a800404240d0480901180310b9a0100000300001001c80c40d40c03d00216504000340165900911050043c1d480d5808515a40c0c8502c2d10800261001008240c881c0c8140455000906046415001249007085015560240c0c0300100461500c1c0c144140d1542e03a49080c4800c0c5508401d4080360070440141000916a8041c0024500a038039 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 108197275 1250 108196025 108196027
    0xb0d06030c05060c0c04110909040c090513110d080418050a0b01080103050a0305071a0705181219050c040c05030405010525030c0908010614120d080f0a09020312 71
    0x441c244601411119800944140420061180d0300303100410f401203440340850700001e4400079509203022500ca0003c08a5011100b10100310401110141c1c60081d19690a020400da03610b10350202d200860a10005d080500c038014408203c4c40d2038018100c00b28030850a0700d0030603586698480141194142003411140c40e401001451140c07445103241000091800c107465524540b0f4154075513900b040050204580081d0301c40500030401e20340f2010940b142c0390f0018500d0283c400801d140c11200f0344546202d2400148103052404140c0410300718500805040c014521000c9101403040404040b202809228024405941da5100d00074030300e070301d035101c1e00d0f900c1c50513241c01421264014400e5400000380400e94614044c540c26901c100d031140e0130000340d8140d11020590390342d0340d10b900c0001c80c0c2d800c15001051b180c207541107203154907000307aa24203042600c030311030305444122041c46070001411020002c1c0880024841154205034140300008442c2d08a4020a02f401c400c0ba000540c2600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 108198525 1250 108197275 108197279
    0xc0303040b090112050f070c1103100c020c030706050412050a080304030203041802031306241511060f0406090804180501140306060d0b1f030b07110a0503040b070303060b0d06 77
    0x6003000d12030361080200c003805c102624020508040d100d6028100004000c0c1000030f410811410300440f810400009048507120091555018003401000c0d070960014000c0da100b4107120b007800105032040ea50790740c88060407e820102d00303903401c1d03031380d1072040e14907124600b08140400c031064025401240aa4051a0740310b060842d0344412088406026144c50302c10006c01c1045042c405480b010150701c150b010900807044100d2115641c200a06401c6902e0403200c0000c0b0b4151008501081344010348035030102c00545807071240c56100032503042c21401d125070300040c000394140d400200360503c40c45c98a4203242e00c13059040d00110b03441c0d0075600c072540e80300014051001300f003c04900301700741100145540d150030301c041401000c40c600001d01c0304002c44041110000741500b550f2166075010301d500803051780c070b08041c00e49120a88450020445c1c0382400032043c44045544545942c002005501e4249004200e10644c0d004640079020103079181c402050b40181580108074103c0e500383d0200b103840c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 108199775 1250 108198525 108198527
    0xf0f040e070c030801090513021002060f0c04081e15070906200316020418030c020405070e0307031b0504020705030901020c06180d0c032102010e12030a0c020c0303040b0901 76
    0x34064615414000e55440700800039600c010700c50705403441d9140100b402c1e00c4800c048420700b02001c500a511803500385680707035100d42c0050b19501c58020380e668801540c0b10311a2101261041e40103041c595003051498804140c0d81c0320b16000c940880800300d031820b0410031018144144103031a0500091000e1200700690f55102d14038241568085508284d202c1c04444d03419960312034031000c0c409540c0d03980b16a03015903465900c0019901440032090850141900c3e00238024010301d20304a00c100d15020100f60054803a0030407847d2020090005c00383d03182103450b050081410030034228402c100752000032400743c035503002620f42c00748254000d5403590040000a81000c1c20700c0c01603806100306102089040c43e031020969001d000c143c0300000030304154200300c0d00707154840d000034048968101010440e6201c410680419080c0c030f030b008000d50107081046940711100007024010818050000c2002400d03030354041c840a840600488a071600c0b210042400c1d500194410070b000d00020034400381035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 108201025 1250 108199775 108199799
    0x903110606150a030506030f0304080a03080f040f03050705030903070f08100b06040519080307080309070e011212021608030307030b0f030a06090c0f0806010f140102210f0f04 77
    0x1003902102c0c080519000d1040804480c003d0003103840400d80c65502066054070140140800c080c0b60909891759580c0320004c459450407203a00840010340e41c140086d06600f00d0000f42800345500c01c1070080c1030145610100c810750031100081e184d40c0003c102003141ca07501000011300420402201c11003071480c2640c6c007070402002a071207003d81821f0510b0b4a0f280da50f540210350035101c0c100e0b000089820070020001d02e064854204460501c0001903e100703021800300554441c50b0b01301d048840960726900b00f2425000280b180303000385944144080c000448001e0700707504a40303080c41210303158030a0340c030610403900103a071000c1c07aaa0000428001c0040d03150113903210001c0281c9000780c5018001000c02d40d140c0e50388001800c11942e0b1261302d0204444181c00c0c60041503a48510b5043c0e42c0c4603100c6c9922520700b0310617058500101c03480045c0d40f4519500205407540160040c082500b03188030b40006856a000c0a4a58550100b24500d000d14520024107074000d081e114180d169130502c0010012 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 108202275 1250 108201025 108201031
    0x91d010203090a14030313230f03041401020a0503030103060f0225060b0111100c0215090106050f1e1002011d01060509071701150201060506040e06100816050c0c0409031106 76
    0x45403c01c01c200203200203800200810700d50300140d0b800f241300c10765505101008c6c00302d0716603070340340119000c11400d210000090030540d50259102c403c482d8001005981d81c81d40050000d010340c10074001000401c0766907001d04201c3c051482c016140494046007035081c1445011884080d030345003d440020b004071407203541041c100070f0a0841e014400c20004036558203414000d80c016507110790740700102c14424000002c401740c5c002c1e161907040c14801c84081c0a00902e002d4540955040c3c1986031851a103003030b07104000810a41c5844401141d0000d004203d0300016a65095640f550740c50010b80b69000c562207031515004000140c070360700b0302080050038240035043c80100554803154541402c038500e5107504550075407610200d1901d003810141d0141a181c0d20090307000c200441e000981c5040010502e1240401701d82c400307510a01902d0549442c1001e4444401720501d2907910204d041c0514018038000c00c494044030314407a00000020140c0307203404000c80c0081c024400e00c8042403010081030360 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 108203525 1250 108202275 108202313
    0x2070606150c11031005010312110616050d15090204030c0b0406021203070c05100507021006060f0e01170124030513020907051306050301080c0301020c07091d010203090a 75
    0x8500e1003030300070502405644040d1215203058685070803031341c1c00c0145405043c5804414010f56a4904103c80701da00c00023110b13004511800102e02400f040443c085110381e403110307110501503182e80c60485407908180e80300700d906680d8485001003084000c11540091200ca5405a520b0b41149040c0148048903445119160310510060003040d0b00480d04000c262028040c5c0313030b2a0b5a4151044545801501f00038040303000d0360044120030540c6405c5a0f102d200079408944c8141441ca10810031180742c0d02c10a0300040004000c43c00080c801d402d0b0b680124014904407611510a042c5282a80e00070b0f404a4058001210303082022141202e007030707140c4c4116090821032890500e024903200c41811300d00a11403412080040e02880c004e8066902e40d2854012400111f1b03114000609260300070300440c41540308009a050052805008480c440c8104001910b0f40030301d03200d169405840040325000001c0c0304050000400042440030354491000d102c000d241481342410010845a81c4240c82e035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 108204775 1250 108203525 108203549
    0x307111005070f020a020a030204050c0d0504030c06060501081306020c10021b0c1905041d010507020d110705010903120e060c0309010807030e0d08150406060903020906010203120a0e0709020d02070606 88
    0x4000340c7d0340e09140c08200c0390150360125180c1d4500c00c04440503c035003000100030900d4103040c082410751094503c110030b4841c410400407941c9940040d030f00060101c905129000412203038900160082d0041c229507071800c01110140c6c010901000c090742c01c002e04080702c444490a4061b0030000400050ba03650106840c044031429441c10703541101189800341d540510b807511150640c1c210303004070715095020180000c01c01420204002512804000f80120001d845014955000600851708208588050b1113060a207460f6a03a040044410189940c040c440f811440880644074100200206112080556030ba060014009068181d019012004052414101d8030305614005400c013241d1210b03041a280b55074607a40e80c00c0c030310203c40c001941c010341040000902c2e0750b0410130319400d4074030840303200016981e4900126924001c19014601c0d900a1074085024100c83c0d40c480640020480d0645000c0740e2203401000607a400344182c5a90103500192050034484e49101b00302c040c1c54040500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 108206025 1250 108204775 108204793
    0x2030d060e01081218090c070c0b18040509150c0a03150b090d061d0a06140907030201260c041401030b0a0b0a0c06060f0e0a0605090403050307111005070f02 69
    0x10b40c0d59004003c0380120216400140174030000f000d450041700d001700040c15a400340c9401b403000401d64201c02d8045507860820030010400c02c0300076041e02da228001c20085901c0980c004100006090040c042d4413032030085a107c5a69161b44490301c40c0308281d48004207a9448075100d0050071180143c0020f0380740441e44806002d070081d00c104071041200e007194480c01e84d0b484c6081040003000740c0304c1e02030200d448a049040502c6030104002c1502c9018800810051640307948500344d4910840f180e0040c0e82004a0610056010b075954084805c03100078000e8045080a55800320518152604500c03200049000c1089008100b41221445001e00e0140142c002610102d028035410380900803540d04041807003550079100b884240c05903a00084140046583c0d41296440300701140211180080300c7c00000c1c1181c2414010102103843c041c00720780c019601c5d40c07001c0b41e02d5003002d08a04100507407030700790390440941040f9844884031181e10008072401c1c041400750280b0000c4034480c041d0740154000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 108207275 1250 108206025 108206039
    0x30f0c0209070302361c0c0b0c2104030c06021c140c1504060b06070f02040207021201051e0702070b030f090705060a02010c0806090903090d0212070602030d060e01 72
    0x245500700c1c000b4200540c0b100c0c44843e88a00c100740e000c01c025444a4100f15030704640030050003000d10303900c5c02c0e00c00c0e81e240c0c02c0e00e100c00701c0c0e9880b841d4009002d2490120040016045001c001c008208201d025180b584403000511134014242c010140c94504001c901030003800f00b01c00d01980200075900080c090084c0c440000c1000908907841101072118034102c190010f6070340401c5441c624441010380701c4400010740c1504008c4000d031410b0320854034101000c0c00e2418010119600907421140d9280c519180b17a0030403020354451032081360403603c01300750110300c10824000c00380120001c140c0507200750004103c100400800402c001d00319480b5000030041103107180101c0e03801030301d200e1080089642e1880b00071b14090349a4410f030307008000020819462603040d0311030f1110038002ea851400c0da4440c10108201e8507405c1c0d80781d460300d82040006030303041d142512601419a1014002e407028801107a103090404201c1e41c495009070b00002101080200d0b28800c0a010f0048180300350b95550615407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 108208525 1250 108207275 108207289
    0xb0f01080f0a1b020106080106050d030914030118150b010e010e12030f0f0d1a010801050603041b06090509060a06090e0c1c0902040b03150c07080405030d0507030f0c02 74
    0x490194400203000204640340b0742e039006202150140c10441d44400d00d2508001d008143c20710601c0d900313510b4440c0c00308062400b04000f41b40c0e00d400d0740d50740304400d04041c0100205502c41c890140c1c10340d619400c803401c0703000c0300e202c42c10102d004582c000491108214040c090703e0b207022880d0704105851211041703682e04610b1001d804c510985500c82e540100d10049440c0d44521200300301c0e220004211071443c001114006d0450700c2d04c9950500c030303040c207052696845c0c0f004507103007901248154006200c20705041c400340d0f9105018503240c68401c40604d0407003034942415000f860009408800c28070040c10842d0555411203400e076a0008114640000181401403078002c200707a499501000c04c3c0d0348094003080d2907080081400d8841740c0840700f50550000c08a8160403402a820041c02540c42c0c980454004800001400c0710105c0e60781b6130000c0b201640c0b1052013183c03181c1051101250544003080b0100301c401c1c80341c40d802d66820300c03410054421020ac0c1e0707491041004030011540181c403108 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 108209775 1250 108208525 108208531
    0x907030816022202070201350a09140708070f0803090607020102030c060901091a090718020d050a090b06150702041e090312050c12011511060c0403060b0f0108 70
    0x580c01d4914010944005203012142011940070310f142004842c84070081c076801082141d200741c80d0100740001d6001c505000c07030100100e82080200c4620910030030010054400d0f4800c510000005080100f6078603400e40100d1010601d14552041d1024000440204105406824600b9089490030714008000d50340b481440c3c002402000080350110071a4000c0080d5002c04652105443c1c00c5e1910030200c0380207202852082d00c48851031202c80034080740c1420400d000e001942c0c0600441800c2803400d03030000003510400380b03030981e00f04802851283c40e440340600449039034101040317121260401c41ca2000001e844d06100d00b85041c68807141050704011580c0b1290306581c041101030141100051a2901d50a407101403400c0040300d84c10103a02148840c2e10300385468040155403030b0702e1100111805400101c2c880c94401c00014800381c2110803240740400c090340343c0300c90490126100b5a0820b00c00359618184020086003d10412245006481d001071080d01d01c085460401e00008003025009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 108211025 1250 108209775 108209797
    0xa180503070813030c030f0611121503030d060303020c040f060b0a18031a180d0906080603010608010e0f0d0507030f030f0e010234020d030518030a030e030609070308 73
    0x3c19648005601e00321400841c1c100030301200e695601c0c10120721410400004442c1da519100c03240e040040b040d4150b801c101c611400003002c2da80c0d825229043c200880014560503c1705001d8106801c030140158400346100b40d014003502c3c402d8400303200030340e65900c1c4401d8059003020011f1280048050a8541112241c42d00840b035000d2a400c1201d0115681c1000d0204000c1c02c130129280c5070b50b090f8040c080d50a03560000e8499034080c2c680e03a15100c81c10710110018602c1401000307040d108a09094108900070000035900b5900d052036400c41e40f2902e100e0748241c20481e46451000010b102c00c00d458041800d120f45480e02030380e001402c940043c03250806041d9507140c00310940c6040e5004001104080000715980d0b48888035803d6181c4040c1002d82030554120b007040c0c40000407140c010050b0f540540303042c606040503a41903d580d0401152403c514048601c030900a0f034080000300060390190b21541800c0307842c84203041c00d003503004114155a80c0400c0003040081c00003400c581c814580 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 108212275 1250 108211025 108211027
    0xa03080f0a09080703141006050307090908090604090c2c0103050c070605010603020319060b041a2502010306140901050609011202211e04030507020103090203150a1805030708 77
    0x66803030a5640c00b1160b0400305a40c8280c11010082040704080315840e281c0b050202e8041d680d02c061400180d4030300d8040c0c50b401da08400e5041040140d1900404001440755110f103060a003240c2c040381c0c568006a00000e0a1522a403506d40e4a80d0400303004036464840e0280d1102402d16a0040030f034180c10080350030304165803400015012204581524a0194070102c244950b503983e50005000e90010f1307a25030300340c06a4202c60841e2511912406041b60303114080710f42854503260164900c414541c0c8040301c4c681080000000d05241400700c040140030b4411700c06d00540b000d00005080b210341d80c0268000803030f1032140007141d0391140000ca045401c1218295515165040102e80d5503c01d09844a0303103d0010410132080418a40042c400c46060301c6d02c0396160ba1074021801701540b0a000d09800700070b001004c50701007031152000b07180540c010b0401003032400d8113034042480c1c031206608192012190100707104035200180620701d80792446140d0030440a07103d4843c26142d1140a40040c41000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 108213525 1250 108212275 108212287
    0x804050303361f060602060c0d0603050709020d0b0a06021f0609020a0806030d0905060a1404030b01030605040303060501090b2d0a02030c07050103020f0d0504030c060f0b0f0a03080f 80
    0x800345000c1d41d420300d20300b68141d240c40036240240b580c51000440b005110340200b0712000243c040761040c04216190399000740142d84031503000002541c0050902144981c8605011000c940304024030310050114250059440181c1e0502d4022078100c80856442400000b508002a13a0b00007000e040c4055440c45030a441d0313a84000500046c2a1075008241107400414010300303558000300654482d51041c0c00b42c80c41e0800c4054121100880e40c0201540200c05000c400101441180001c2d03032200031481349440c080c0c076919a403c031420268030031102280c8410070002015418011280103000030308080211f00d047c01d40080d802c0c0110202d103040620b0001c1c80c1003048040c1030610404e02d82e004902d503034543c90100000d40300d41c0025a003c41e02d1007007030800292944a0b20031180c2c85101040c14500b403207500b80b9240c001d400003074801d40c2041401c0c0c004c1300110340d043c071810841c0c0b00310050000380321014105109038070150310b41491040c01e9250042000c10306410880e158443e80c000d48540e920 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 108214775 1250 108213525 108213571
    0x5070504090c0e090115080c0f0307031703070c0f0605061311030a09020604170d090b0406020a0210030219031a09010302031c180303080f0f06030d0806010c0227070804050303 77
    0x410929088210b0380b03001440007c5d44e003004101c0c0b80c03039080151000b990404070b90b01410303641da210307110003003464002c60650f419154498000c0c68000c0301e18a40102c2c140e14603121094441c0d201402500c042d691030b002d0044074a0710500c004d1a01b142c0c1d00c1c4c01c1c000c0d200601068035543c003006005400c460f486034059411175644804441c003901d28410388030314008000d1080c41e41e40810f030740b4071707070101d00c0048000c6000002c800640d4125800d9500903c4909015401c1c407042d407040038001b500703054003407060400032580310b510f5054030840d41c2d070001080011118000200b02c02004214000d116040051026884c003188c0169042406424207048014242c0308803941ca14a030b00003100087c240b41c000c0b041550200701503001e00c0c403150017000580c907040d92890043e0401d55015600d0f61214110380141ca010301c1d038940c0d01c42c0c414104001d0f81c0e89a80c0108413032110095001717803080c028200804680c0140240c0582100c0f13146040b50032482c0c940d8072155648009460000780003031a0b40c4c882901 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 108216025 1250 108214775 108214781
    0xf27010206241f02010b01050c1b060d020a0e010f051201030605040c050303030a0b2719060819020306070f0c060b0f0616020901080d020a061a0d050a05070504090c0e0901 75
    0x802d2024001500707030002240d4420100604100410040d401d000580042c4d6101d00140d400b5110780e480542082c03103800c2d800210003442c00440c150089428061198060040e10151042d00800d0b12048582008400010024070a004020742802414405d0078621602d001445041d04c0d80f2090002d402d890b142030180c046100c03135004c0c0d03038580f100008002685006810036400840c05944051100d00488003904942003400301c01d000c80e6400780000ba12815480341d00d10304403000d4000001d0a2030702c418a9600705800c0150412031520194901400c50800b000312036405070351490040310b07018094000510319003000101405017510780d0780030b40365690f41003221000064002c00c05596844200325260130201107540c2a0310495000300001107000002c20700000d85005070780a080840b009a48120080c008400300c1072a407002a50b020086031144031680b55028001d46c010140d0381d005140c21868510a9005140554100305224000440e01da400a041d9000c03c0c2c561190f43c0c3d1238113441c40c01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 108217275 1250 108216025 108216091
    0x20d0c0804080a0507300213090b07110f030406140a030612060e15040b070f141303050d020304120b04050c0d1209210f0f0501020f27010206 62
    0x19008060520081040008590040706c00708002540418403000008801116820000d0301c3d101c200301c082c400501c0c02d400e920003030f8080410001440b54043d1036202c08800304072211000b1070030750901841e4000c01005800c1d61058a900110700c2d145c01e04200601f08a00120101c9a2502c0850344200460017900b2140c050010030f0306c10344000d0395601744040900345030502c1040d03500444880e10400d9620104403442160000002c0e040341e25a051b0449842c0950190a820411103609004258020500410610010b0940e04038018190304102d800c1100144264041d580f04110030800c192400010b884000d80000b03100e00c1a0342c46050490401e0000481d02e0307808501d084030030f410400b02480e03980d11001a6a00e00340c515460741c9040400c0400c0f00c0d605070405607099801c0c8009042800c418030b00c00d00c03c0349141c0402c08981d43d910b01f0383e017018003440410040890416020445008403604546101480c1c940401800c0c0010b501c400003d00340d0038070302d5070030364401c078000c40e010b585408 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 108218525 1250 108217275 108217289
    0xe030f010509010b0111030702011709030c070902070302010501050306010f0e0c090d15050601020a021302030c0412060507031812030b03030c030a0804020a060309021509010224040203060a0606020d0c0804 90
    0x980d00c2c109034030368001e102101050380407441681350280c107a4800070540b4405a4103031101016441020117640325003c0007020800144020000c84c0a000c138103200d2a00148116000540c40f039145140213429140141c05c083d00950019004001a03003480840100701c1c0c143c50220782c2e0503120030488034814802e10801a030895900b04100c02003001100550400327407074900302004a40c1b264001280c4881c29660065404548500c0d0803d40c62402e038011030300f00889140441c03a180c0c0c1c0d11462642c0d40c03619241920f8090759002040b02c015010701601d0001c1030301f1000f08169603446d94030b071840000c03080304040805666140b6100240c40c200100c1c0c0f1280d441000b05d9444108000c0020660307413044034200e01584140798001503040c004d01580300d5055009007981c101050810608070b041e0003403035100d8114401e90100f04440703e2000b0b0313001c810842001446c02545840c0c010303d442d00f01d001d000300c400d05240c56010810107a004c0b41c201c0340607c407490301c0c66400225042c1000e40d03000d6038018070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 108219775 1250 108218525 108218531
    0x102150c030906070203040f06140702210c040b130f0e0f0d1409031c0513030c0602010c0c080a0c0201020a0515010501091205030d0902040e010903020c040e1603030e030f01 76
    0x400d412680e0302071881102082c0c00c842c80341d41d502d0340407601d82c0513510075800a6040d204080c00361074043c5c502c203419040c1440d501c1e0f041900c0c075000164156254200c8000110107030a40b030321b40790401d114814203080191814030903000c404021802da14001246152200e968807091030246449401c19241c0b000c0074012160681860b00086403603000003004400440c00032800440d07000459810f40d842c401c0d0080141244400d451404500030500d0703c071100030058200450286203540384184001740d805001c00d00e4409051140c042c0c2114000c00045051100002e444c03c0000c5103a002c640f000c501920b0300030b218401a20050303241583c0440000d00c1400b50710301c040b104a10030341e10603040750826600e4900d944d40d241040b50041003601009001d9400c200107a007070a0046820154526101800008102600041031400c6a0b0144c40403001038010340780d00031080c40c0c2402507001c4210b104020f024046100f403c103410540003444010184550020f9288141da803c1c404080a4039141000b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 108221025 1250 108219775 108219781
    0xb09120703060b0315040506010b0708130303050a090b030f0103022407050c0a0b0307020303010e06011209030305061e090a050405011805060105010f08010311090a0b0a0e010f052409010215 83
    0x240000c0c03c07031500b04038040c1c070850f0300400400c8011078045004903004000703000264201844411300d03621144064844480800070491101d54250403840118000e44d03480303407503956003603008000840342c4d481542e2400e4280280500700c00b12560075811280e0440d000d80c421036402c0700060343c010301440c0c0f0720401040800d0301c00910030082003e0703045100072140c0300e00705500c682520840f4001a0360a80050384244010f0014012680350a5000a014140018418520070944042c0c07020000120b0000303440d5020710803241400c0303000400050340d0701010074204401401160790100010880080c054680c03000c141403103000e5203c018040503800b1089180c030032a0401741c0ea44c4200f0710486002800d0403101c1d10400d440342e182141030b680d00040245d0380d6a05581002101c82c00070b80440740c190f944030142d45d07007079588100500c0104801014400c89615000000111040c01d80c07000d40682c07030004d203403c034440000c1540120781c244a6071721500c0c1c0055100403883d1094080ea0a03013007509500078 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 108222275 1250 108221025 108221033
    0x908040302040c020316030f140c100b0406061b060603080403082508030a0b01090e19051008030913060902030406020415020d0e0609010507080a08012303070b09120703 74
    0x20429a80242c2c0d0a03c000000b02408a9503403148000d96000450508943c03400203100d20020a40d0403560b16000030803200c09080c03804c86a0040e115000315500008440c22100d100c1d0040300b6102104480c2000801d15009014100e105100726502c0d100560f10004e804000469005202954100410036105ea88903e080d400c141c0c85540e5040e5100c1c5030358104044000070414002650354404980c90440d210489080c000e800407000880c10701c1910303000440c9d40351400c0002c40c8600b2500300003c0340190b40c00c0d584070403944054021301c0705002910081c4460b02000045401c071701c00c1038510000c02b0082841802c01040c00360000c03a0018000014801485426000780042d02c1e101e4588840310b0b6408202a6981c030081202c04003c6011040c071602c0500c2d01d200940b0030f0032410304105180c00c0c0301d980d440c059980112400b0f000b03e025140107201c1c20004035941011046104600e5400101c3e0000103507450340c140c4545031820f000003500b0041c5840311543c904004d00220111400c0c1e60700c070701d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 108223525 1250 108222275 108222277
    0xc12050c010801090b150c1c0810060c0206071e0f050109170c100e011508010e0c0307180f06170604021e011d040212010621050106050d0b130908 64
    0x540c2600203038a10001046400440c40740001d050001080c2d814520440200c3c0d180c2070700600c4004d5120b000700c0003503600500345101c102042444c15958010140341ca0036110302d0300e0742641c2008080103d804401d00040c0c0300c0305c0171500c1c1c42ea041283c4882400000c200482c103031481c810000d04080b1401d03000020414150000100c0700d10924070000da40d40c9019401006001d80c4442c00e4080e80721400078802d04e800c580c0149181465000041000302c1300d503d1052035a801342e40040403ea41d580070329070340044144041105200b04501800c60b0b40e01e001d0744924100044a442020190b41d002a507100380d003607a0186000300044c59041038002003041c101a2510400c840c1a8065984440714132240032802210a0040f02d058403207080d103c3c03800c001003502c40312915503241c02541c00c02c0400310805034442e11500030803840d60f510b201c50740007640945a03401c840d02070030021030030038005001c2160008160340130040903110005042d80c03009c0c0000c00022468070140001803030064510b0034030840358 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 108224775 1250 108223525 108223543
    0x1e1606080403020601140112050c04050a0e04051203060d11130c0314071407111206010b07060f050127110c100e03040515030c070206040b1c051605070c1205 69
    0x2e004d480d00303681c0c2c07602c03894241d00c00010040e000a01105000c1c6c0d8901241c1c0c00386030040b100444c490706107502c40000c681440d14581000405c1000b079410002048020002c1080006c0c6041d035250450030110003088500501001c01013101010008411240d21081d01c00c1c001c904140005004605d10711002900500c5000805c01c10040380c580040c0303545004d1441c80c1c80425514280c10314020701c48d207030070b40c011800760b15150344555041d00480604000308403075806031600f0f1454554510f024a0810300321303100000d0095169041c83c00400c0314000b45030041c003e03002241d03491310311142424900e100410004818600c12000841c048503030f0100003070308101c4000d4800c0d08100a4411518207562400340e4494150300c03031040001c80c0074044484010319040441c1401c21404d06a01c0d50000b45150400d40000415180c007184120581003120380d00410403041c40810881801d0102c29842d1004d0207052030402c1c4140000c00d8806c0100640069005140d507621540c0f00200e5460903c4d2541441 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 108226025 1250 108224775 108224777
    0x100806040e07050102033705130f0f210b1f0515030a090f06020a0305040b010518180a050703050a0515070c110d02090708060907030209031e1606080403 67
    0x7110040320300290028000007a204160000d5040000d0311a407440d0007030b4183c0701f000d00c84100483c1c0006160030419940041210b5881d240e865041d401065001019541c1c403055180401180c2000206510a140c0c0d05850b1000c01c100c0c2d8000c04c0351b2442c0f00c10780e00504000c1211448100700300306801c41e100c00b00c1c104004101d06040c0302e40c0d143d040024030310070860300000c6501c00300003046810440d0f03448500200c0c41740305c84500340900750311894100d030401305512000c03a031140d04201c02c1180c02c09180d03000d0401100c0c0c804440c00c41d50701d0011106401014100481d00b811350145441c5005c00001154943c4071046495250701c078a0501c2e00d410b640c400c219054480c0d084003201a00d0800c0c1d0a84c840d80b65a80d41075030b98402911414114411441d1098000e845c420b20321004d40ca49a01e10740c811143c81d12104c4407800c0580c14840c40386001003071f1004251061020510035a008901140013008034201102191602d011080c1000c640c41a1516111062500040c166402c00790f071034820fa0003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 108227275 1250 108226025 108226031
    0xb130303030606020114061c0b01090b1005070506070f27031202030702011b061d010506010225060804110307080d021005190203090f100617010207020d0f060b10080604 74
    0x59a0400d900786c0f4801400c440500174210700140301800d003401100c566044026201d1440d14054883c04400c031805c0e00320044c019240c0d548602f160a00040c40f610012062501910302080c41d1281511454054540e908010382c0040c072801a030711030003600b90380b56a485400c81150008910301a020f406030701c001c8446020b1904440c03490b0b030001c8103494441d5011784504000c020490542e0f00d40c0d20b481c2e4005ca07021a580c03c40f4902e184007680021100000d40000054035041034000686007403505c024a40004084604410000c59000c49450440700301e0300b000d10040d104c80c6807030b03584e00900d002d00c1a014881c0980010720401c0008035042c8045142d002e403541203060307400c0801694412185040e000110f00318000e8006601c2c1d0045503c9035186041c0c03102e2305100360102d410120041040200c5c030351120800d0210b00012040040e8080a500c021407400c0440d5020070104420000c019003130031030003583e2406000058100c40300783e640c01007444141111925010741440d44c1070301d41c680194a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 108228525 1250 108227275 108227279
    0x8010606020c15030429101d070203040b0a14030c071e0201020601120302010e0a0318080601120f02030f07030803160f12180c09020c0f030a050405040c03060b1303030306 75
    0x100180c801d40f9008150360b9031441d5688a4886c5544402803520354890b40c03040d403440c41224401e220615001e07940114002007028507048200840c602e801a0042c80090b40c042071004c01500001220704aa900015031511140c07034880c192200382e120050080d04800c000100048040b00c14000d1140c244030f4001c00e5a00c03000781180d50076a400c003c00090140c0d00c03880061091458504c6411491880b9100220703442e100f5062240c201001c990045020561004081100112101c082c05c0036000c200c008040940c9810500e041d000309140d00604040c1d241c3c0d081701c065441c00d000c0b404031080e4400440307a04075903074607002c04141e100f200c8550210142c0c000c0a8500f504c00c1d0604c400c2c0300303600d030381f82a4420a000e4003203004040000300035000030002010b810000348034450b210018100751100580350650065410f09203042070001700c2d01c58204012104040d50010184c4065032000d6034000341800349034034154001d180740d42001c0140003010490840705649080d020b400e0302d21903a01070000769 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 108229775 1250 108228525 108228529
    0x180e06010206091204091d011802030105090a02030a021002070f1707050105040303020a02091503010f0e0705091b030a0b0d0f21050d0509212709070e0f0a08010606020c 74
    0xc1855800e902d546804005c20040300078217800100320034400c0c240398250510700c12101ca003198400700031445103498841a15040d49030a100381a80201381e140075081c0c16000ba0b00094540b41d048200a210348009065880e2007882008964003401922010840c180e03110030141c00700b0743e0300143c2002c0c0c0c0d00c02d085c001b168039440f66040c1c83c1101c0d03058008010030380c0c2540c00c004041c0740040540400c0c0e400e038940343c070982c1d40c2401054404000403800052105107103140c18180001761704030902640705c41c804e02682101c0a070129504841c1c403248583c40ea103581202c0d40140c62703a20b00c42da5009140103a400140962000308a11041c071030031004400d010107052500c0c00c04c81d40e0780b10501040007070011403050762554010360b0f0b01c501d00340c06a5100c03030500b1840c10344048885403005089280400d010004070455006004040ca0070303d109465561000c2c00a012401c0c020f240c107003003000310401c0c1c404c107464111442c0500c190090840105036200c0103524000c05a5103d100d005128083c4c5440d094 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 108231025 1250 108229775 108229783
    0x2070311070b040b04090504050f030f0706060f1401080403030b03120a1d1e1206070503040b010806060603060d050114040510060f0f050114070803040602040302100215070f180e0601020609 83
    0xd41300144114102882c0802d004001d2100030416101d501035180340e0006400c05000411180c00b5080c42c164071050b040c00c0810844119411031580c1c035281000a000451840010f141e030040300746885402c0390f8a5240c00c0b0041d00009000c590544140b80800301030000c25006009052141d40e503810080d25203501c1002d100c80d5490a10360007804640c1c006645002a0012003d0040064402c1a8662051483c10314060048454078002840841401704211490b080700e80141004002050242802c0300011071b2440042c001a1003407c181451004107c420740024180402c0444031024510b0203090907030701e41032800d041500403441e0980c0420703403110f4641c80138103850508800b80021030503e001940d0741c200c101c8100c0300d1408140111400102800c7c0107511491040001680b65450741c03040c800300c00204800e950540d00004c40481c801a6034200e0907600c003905140990340010030300426100040001c0903804c4102d01010081034080078140504d001d094203908466042d9074554440d515 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 108232275 1250 108231025 108231029
    0x203060109080d05091309200607081b0106061403060f150a1d010c050a06050901020408070f030b0c090603130206041802120c04030201022e0c0e04140606070f080702030102070311070b04 82
    0x2305003003200c148416418070304451000d1441c0913100d04c2c58152507440e1000a608458122101008803d00551081c10280901e200901250501c10302140101d1080300490100503c0180281400185624103a071841c41c440c1c0c0901c4240795240d91041294002008404100c00b20b00582c80300c080900c08552180f1030002d0342a420001400d407486035680e0b050054a000fa00c0003500399000d00001c50140f90502a0030000c1641004001d4000d243d890605600c400003400032401e0384050200402e07d4071113504880e400b0031034110320841402c0910004006004035003082510b803500c0a40010f010001e0740c01040c1d0b560103d1800741042c0c1d90310300c050310715110703d01000b03005800900000070621001d481440c01c01d0300d0702200528110f02420344800322101d1094410000d034401c02402143e081900c500040301c1c104a40c0c08400749000700c0421418812088010a030000c2900c01409014030302e029264801d034003d009560b10a41814014100c29100e0209020342c0200310b40010a84006000c07242 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 108233525 1250 108232275 108232283
    0x2042c011505090d0c06020f060703021602010e010c0b010b040e0903040312110f060406060e090f071203030b0a0801020c060112023d0302030a110f0702040203060109080d05091309 79
    0x80c207019044126042e400400c00d560700540034465413070000f910010020040c110170b038000c06116800e00c0046207400c0020b008602410310411002415040f40703400d213400283c080c20070b500c5601d000b0380120b032180d00660b130184c100214100040f0b54060840024030440d81d00080e90788098a492000b95100e11803803000070115103861144086250042030441100c0d0216001c0c0d860140b03486400c035091840841e41100c0c031540d5000148240c040c46494281c0141c5140000d018848a548850742d444000b8012080c080700c41d24003071001c240c840d401c10507665502420a1203c0c9580e409140d010313410100c80c55000340122000450016203c10400300c509400800b103560040701110300c410104114012140c0641c0e1046c1c00f511a045511131550b4071040c40d0b40d00599902d000603045003120360106003128011001c0254519008a01e425a00d40340d804650050f6203850380e0740180c401c1c0718180d00c542c0440c0220020500344641000c06030110100560300f481c40c603104500c2070341c116032020740010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 108234775 1250 108233525 108233549
    0x3130504140f0c041a07030f020d0e0909030f04030c0501110607050d020f12040c05010f09031524080307030807080103020904140f030d1b080c0307030f09020402042c01 74
    0x252081c0c00b50a040340c1c2000381480a6880d16480398050b90b91200c400c44c40c80e030300d9440044c240c020558044114001e4071043e10261000042080004003080c040b20b489510071840c0700301040c8201024411038a50070348507024141ea582e56440e02c03600f02d410510511f4003050b800303a05a981c0c0d00300458000d00c5214650364592805070132444250094000b10304090410780300344068510208800081c500450117080c0c1000c056280400040c264480300004004210300a603041000542e902d111040c107400c18540400c8160700a03010300d4000400b016010f821440b440c8000641520100040400500035594050a40d0b2030306000c0d2030101c000e1000075006440140000c000c43e0200030854554503441d02070306c101c801035184035461070b001280c4143d2281d945071204000300d001c4410080f5203010506042d502450013a2000c144d07400700410000506803103503010320902c54140e20144200394010030864545840300c00315414104032800325810301482e1809401040388040c0e0f024101c4a03078030055 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 108236025 1250 108234775 108234781
    0x204060207120309090f021c020a020a030e0409020a03030903030905060405011d01020a06110c07050d0c0512030405060f0d18080a0509010311030901050718030221100501080313050414 81
    0x1d0000c034664148250100110060045201129400385044500321101e0151700d800300e1900d01d07880e10607550360700b08d004c52040211030606a004108c0b4082c990701400c058098108482c0031901030300315003400070740c00322000341c01104141d0410300800680e4020755401070456203c100b40a803600c00c60007114003040c207000b4803d25074078170b000080c4491501841a1460b51641703585000c10b850f140544401c07512804103108039045010010b2070000c280403211850740105ea41c4440000e200d0303501515004030318a4001c9120341c50100200c1e0020040a0300c40c0381d07500780d0300c803030390442d50031043d415044942400380d046401d04011045201190304802c41e00c4c900b130b00f2200182d5856024020103410300d84c80f1800120103030201d10286101d8000f04001140a103414080100300c26804162002924481082800962103540c6079861000900e80c2c3d82d2440081203106a18058064150710342403802c1c40008102d8042c003001500040b410303c0d20184083d80c440d400c00045c0d66008125102415002e000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 108237275 1250 108236025 108236039
    0x1103040b18010f0605131e05091504060c08060102031908060406050d1416080307030305071b03030c1e0e060d090f0506041b0b071104240503100204060207 68
    0x309078100c0c152405004507101d14040380303801e4444100c0760640503907507820308200c142010181003030601c41460741000f035240e507036100b80d6031080e80304000c94040d42e80740c000858116080200000d104051010b19410b0300e058a07100001e01103080d0544001a00440810095400001a80d250717502100498a114204200403594000000c01c25a44140c841a0001d026101c00030b139246418018041001040c0401a020340b6043c02546452182d03415605d007000482070210135945056858900410030b0740325040112800b0816070680b02901d000400307600c0800d038141d80808a518642d4840c004034144c14669030208607502d4160801044089410b01814500030b4010122030340c05410001c0d482603a6114510301d402e000008550540c0880203000520603817014108540c0d09000000c2c4041e414586070200c203002e0300000914040a4403495000350b91180c2086c00b442c1801c0c04441002490b2004e40303080003189102d641d000340204054040103140c3c3c2d00854050b500d50390014064a464018 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 108238525 1250 108237275 108237293
    0x160201080907051302031005010203040302131a090a09140609070608040512070510060b07081c0e030c030a1b0c150203040b030f041202010605090a150b03090a03090801110304 77
    0x21500c09240141080480d02d580c8aaa865043c16640d100058030391034140c4183d180d11181e0323013041c4e065600c02e010402c016034414089100043c2d122002240c0001e00802c60aa0740d000072a20640c41003204042081c3c03003104e58420405103000b44603194407a4500140c3c00c1e142e41c41514141e140390422a03080c0f01090142c907503203412611030780407549040400c4613520082c0e040300e041200d1541003130090f0070261b803444c0103000162089410031441c0081554617048688030f1008000b800d44d40c810380000001c40c450380091100e85032030f0103032607440c80011404d0b92254806401040410080e441084079501c944044441d103990200074a100141450080c00041000d5604202184810440811040c1101d0301841c011032001070f041c00c0b03034103207850842c0c03100c594600440304581c501101081180d03203201426801c981c000400145001d01c0d581091400c0382550800080640004280540402d0029020520b28080e81c6c03540036054607982c42d1820380300340c8424800440340600100300403440200b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 108239775 1250 108238525 108238531
    0xc261302010908030f0c060903030702030403060c020c040e01060518060604051522050f060a020601060e130504080403021f12020306010903051b0405100614070606080604210516020108 81
    0x41810302c5002c0c3e44122461a541c0084070550301201c000c60000d003440010003460380c2140c1d0300005903040d0b20341440c0080d900d02581c44040c1c00c0546030004600681d000b80501420400c02410a00c180140d02031b030240640041c0c42858010580c01c0041c58121641c200c000740103c5006088500e0302d03103007070300300685941d84080f0307011945020040800c00c0c40f80e80c810010040510300401034050f00e01801c03c0360b402e0040845500844d010030000c40b2459022421a040d0f4140341801300e0b9146c5201c0c042802c07900302180300050a8545402c0c40144580d00d005003045900c01c4401e04c2010303141c10204e45090143c0c807141c0010070484a88440303007a00340e401440d4071030018940b40e08002d6681c1c403802d10344950f90103400d480c1c903c3c1d001414910f0420b40541d66100300c2144000501c2c0d40361440c000c1842d03e46440004d00c0034804280d40c02000b0302c94106000030606401110a81c0c02c290400c1906136018103140ca00d5400059800f46000e17000b80b00381d8003218500b1049290a03981c2d60010b450b001801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 108241025 1250 108239775 108239777
    0x309060d050a110c01050a0507031b030c1b03090f1e030b0c13031101021c020c12010f05070513050f0d0303090507080304300b013003030c26130201 65
    0xea400b80c0f620610041c0902280d1010400204440c10064803000444030040c03d208201410320510000b4124900c1c07419644004a2a000906030001402100d090030710310907100031300059000507024590b02c0680c0070b0940d003615114804045c1c0d1030700d40c41c4803503a1120889609500d6a441000425210900c0e2580a11549549403405014034402d00004800d500111500f425411280341e80b540c0c10000440d40d606e02801c083d852007400c1d0390103036480141a19091240030358040110281e800bc0d00030b14100300102506003c00d00b0006001341154114900702c0c000d0250102c0c001400d42381a01135040d2048014089854003001d94404a01414140605407054450500c0001312800d08200900080c900c030180403188003c14060031151800c4d52050f400c114035601c1d1854046814030b1030050440d90880c001c144508207001081416200e555544058150340500e02030a1580540106090319800daa4412883c08035441d0982c0404c42d08000b0310045c1c1600c00001c02182000c60742d03041441c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 108242275 1250 108241025 108241031
    0xe031002180a1203052215080a090203070528060206071412130f0209010902090f0f0307061b060c020c0405071d01050d090605040813050105030112020f04060518041101020309060d050a 81
    0x1103510307446d140917a158041079641000390120010b2542c0101d0385500013a000d107003886074041c5038002940d0b40002e0f001c1c880c8170381c58007050800d080409042100301c0445004103103503159a40c0102035183c950488101d03011503400107080c014929640304075401c6003101c1410900e02d4850403004494402c00002c111f8150080201050141e506c0d00809802081c0d05d60025944410001c1440f010905a05415015a40c1600c0c0143c10390b80101d143c44c04c1d580706280407036183c1120407030805405240803016001c90316052680c16007a40c007050f0822288411348041c00240c48031b5100300e5030780c40b00e01c1080e0340c4140c1c9031031400200d41c403810080c40b0703c40c1f004001040c142c0c041c1d00e641c0c00302c42041d80d04442144000403908503840c2902d441c031000308401d0a0403800d640c03421408003500e48941e40028442c03060310b94601e01a507500d91290020b071001030843d8000f241c1029001100f03034010b40b415941100300c06007540703442d8400000c482c140180946410b0815204110513000f0f00303400b400400c1b050791 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 108243525 1250 108242275 108242317
    0x305071205040c06030b0a050d110609060406030b03011b080f0402060d06091b080c030a0509070e01080303060405180309060d0f05040320070308090d02010e031002180a120305 77
    0xd164000c10340900c0c00b690034040c4031407420380f0183c203c1d9111040030307010b02c41c180000c01039a940c0e0304400015a0b04104000a45405000090300d02c0c4503a0b04140c2d4011400310f00801d800c1c2c3d0540c003007a2000d03c282c00030810b203580701c11503041b0024000d03c0d000014583c000020030140740c4041040d00984060800380c00c040ea682004c4043d1515504250380450340d804500d4070244070011001c15080c00c90820f405e803414002d00d00d401510000b08068006a21040854070481c07040000038001c050f10782c1a290196100d20015445c0d03401900e801c4e103c2c034100000304236151103040c490700070300f885c91005610301103914041c03244c10380100c000c10a010b0307a10010159402c00b9805060f01c40d82c401d0b40c813180890903108125803000e810b2200800d0340d40c801e0a0500019150704102c4034440d508651201425174580300403504c0403070303582035290140104c0c480b0380802c840300d4010f070003040000000b00b2b2007846c1d00406c4c000001c64502ca240070024940b80403501181c0034070300610341205a01172240800f1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 108244775 1250 108243525 108243557
    0xc0f01050106020d080f040302060105010f090302040207082a03090d030e03010e07031703070503070c0f0c060e1005030c030402060310030c031a090f0a08030702070e010b030403020d020a0302060403030507 90
    0x19000b40d00482c00b581000c44d014280c140e0089480c2d43c44880c00c1d100c80e80300d04058038000d40c0c1e4441409050305008003001c2d000d6a1078000ca00c0d003802558010010341d590040c038608411107070001c88c190309042680d02d810164244603407040c500c181c58020021800d1280c0c0394200890240603540c16418843c0c000100b51064400b07004000010141038002c0100ea0326502c0d010b040700c8049040a5401e580074024800c1040d401001c40782c200da107500e4540c001100600b00125000f526120052440301801000030701203800800f40d046991007102c01c0401c60103c1802900c140c40100ca811104240401c00075005182550143da0485c140c1405211010f88a66900820030318a03001903600119003c00c88109901c0000e0b41e91b40400e0300c0d409041111340020320240d4503500386000402c601130200018080d14402c008660007080c00008800c00d5583d6005903606551090303030145d00501a4503e0a88094000680c21450795819801050641e4a94070203c0c010311000d4040000c11085170650800c113 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 108246025 1250 108244775 108244781
    0xe0405040b0105090f0f010506130e0f01050301060909110913021002010b0405130807120e130f0605060301030314070f0b09060a05010e0c0f1b010212012903010b0c0f01 74
    0x31880303107202441a50410b003c000c0f15081c0104901091184002080600741030040218111482550203075140c04100b21401c0092066030003812030144c10204000c140241e890029040303800035402001803a81325400c1d4025220341120141c19519410543e100a040a0203016880041e62400d484046220341c00144100b00c105032510050f074592040007203d1405101e000c0d003100b000c0210030300031f070500e81e11440203000c5e801010300024018a219580540100c4418482c58070041c107114100c4030080200c0010700e03009408088984c6001c40104e1242004801c40781660740544412200e4030810840820550000380201c0d800002040fa01c80010740c0e6890031400303946190f0250082d8031700010210101c9030142d02100d510045401445143c14500301103030000c2c44441c080550700c861520035252046810a1450020345c800901e2072000c0d518030305c081e4180c500e0128824040d0540d038850fa01009008031000001610800040000001e0040140041d00d28042a0703080d110151864a0031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 108247275 1250 108246025 108246031
    0x506180a0305072103080a050712050c0403050105010e010b03011701090f0b1603090b060103020702010905030601080604260d0e0c040e01020301050f06120f1306020705010605010f0e0907030c0e0405 87
    0x5a52000c0c000303200070408080b44000401c4c1d10781390010604901d4400811030f440141040041d0f135a02d20101c1c10b032a1043e02940700034500400140514100055000b481d580640b00590b195441d02001207001028030040f5412108100c80703c40c216400e2000200c00d160449207200015940d1351012070004141c1e17004061854000d04108000b841e08504084503d83d40f070381c00b18105403801e02c6040004910000d42138103c2028a80161a142c0070300c01a04c092400b508110b41c54418071000060412000038a00c0c4620321851461281c15110404000c1c003c05044911010520500c9210341e01c5500394000b46800d06103200f1107102000b0000448c00301c43d40c01ca418000b9940000040c010780c24514104452101c0980309079241000803003515414010180055201c400d0b4075020941a00c5070407542c01c440da4000390210b5942c16503103002c40c002e00c190b00c52240402c141001d80e0a00e540169920350320500050301c1d0400b5940c070924110014420060104140081000010540d4803540704580c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 108248525 1250 108247275 108247283
    0xf0708060a0f080a120e0a03031b0b19060e190903030f0c020a020f06071e03020109081b07060509010c030324060e090a0506030a030c03050d0c030911060406090506180a03 75
    0x110701850402d40501c5444903074450501074141115450b98032a4019001160340514001061045c7c8ad080c244020040501c0640301c1c4880c2070906c84401c4607400c0e1070885140c80303242003160700c1d038030300c00486041c100b143c81c41200d080c94581030414031403640011038014840d1a00250f5915217070000c0044802070b144160040c0d00010700d00045040c0038910320082d00003201d986040158595981d140b07800c0c3d00f520014550804070369042018000d41010420961001401c0c0d181c190403400c0d00a050300a41420b00584035240000032a94007a80c04c9495100c0d0680d146642c0824548081d400342c12411305601c40b0440d20780e1616011071104c1d1400010300f041c2d40d00c5189001c0305400304511601d002c0e240301940d91402d400c3c4a80d0781c3c0e000074105c800c1c59042c1810380d000401828240c0b028042c69003e159014189002000724541c19401940680c2c810591082c02e05920801d100040c000c2c0d0180b0000710307100c024280910701e8035002520200002484501c14203501d0b501042d8020a0b41d44121 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 108249775 1250 108248525 108248533
    0xb0906090601090b150c01020d02040e16030c050702010309170307030e0f010501080304051207030f0803190c05091e060403030e01140f0909041103061801140f0708060a0f08 76
    0x110808007070201d01c0c01000200414005001590f0000d104448841c16010070890001760240c100c0000b0740644180d9140b4003021515296180389500f42410221404201d15054140202606002c3d2040141d69031042e510030f42000782c1c036801540185000202610440081c2c3d03400d02c020740d5030310003c1d8841c0c10b89a4020520340340c030b0500f0500c3e0200e003401075a6564140710041c8040b01d0300009440031504200c40c19041d03060181e100c10f0400201d500040c0500301203840203000d00401c40021070281c0c03281000100b080b61082042c0c021500c01c4060000000c0d02000000958036224846001c1162501c510024000c0c40c040010081d5001e94400c078042100404001c0c440e40e00400310f4046845014111454200c0e0400380c000940b06400700c4511803000d18020400340300e124040d00f494540081c044500e0340c00e04201117020348407280100d110343c3d820f207040010240c6a109503107028281000005216032501c120589a000000b80b00640241000000040c071904000e552001001210302038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 108251025 1250 108249775 108249781
    0x30d03020c010e010513080a09080102030115081302130209010e0d050610050904030f050310030515040b010512071703090916020c150a11010b1302040f05040b030a03110106030b0906 80
    0x1207420740b80d802c9200ea4050b417501c02003203244000300c1a800b94107a03020004a41d9030100030003d4401c56042d0300310340040d610100c000724040841c000d010110390b41d01d0311031100a136100001c00f265046510030003074107c40d001607030041e440e4140d000380682c0300b0141000c005401c0d40d9408a0348014a50005a80a5000f202801801200003071440090042070701c1c1d20200c1d140c151000340c007a00e904d580100402c1800800620402000c84030707040a194050250360200150705842510088181c2d425240007500c24000911454441c0100040f0b0290002521101c0d107000c0c99041ea140700b48540600502080080048643d1803180c1d55220b180e103603428203040c040c003210092801640315469030150125010502040c050141660414215442c00c85c09000880c840c0300d0140185c50010380d040315040d41c80d912941950303005842603400c3c4d4510381a48580c0c510400c000d9810a91000740c06070010300e400d60101c1d10640c01e03104115114030020964a41c0c90340d545000185c210b8091549070010014 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 108252275 1250 108251025 108251047
    0xb070b06040c08060d0b04030201110415110304050a140a050a0b0c0606040c0e04050403020f03033c040b040305070b0406020c010b0f031b011e021606020109030f03020304020f030d0302 81
    0x2407a0018411482c1900c0f440c5405004140e10744883e01024080c40c11900015040510035040040e904542040460319507139030303251011800400c0c030040d0020079048164840c8030f44001064a081b03400c01041c211049142031040002140d01c0751080e07412000d401008129a2070f4543d1480c0201254800d840c0d503201e61001181c101403001e40319610440c07d090381504d80301d520413102c2c544034070100c8001505480f80c0ca0f06900d4400e40090812241c0404000c119a17a8440305110003040f81c1801c1450411081c0e0a0b9541c5850603034501301115440e401c003180120f001c1085a03607104d4800d040c41c074540410340d101c0c40118081110120b501503000184a010302400f0300507a01004801d0b24641c9174407040341c00180d1a10040900001e4a8030142200c8510703a101e403140d81c1e42021500101e01e01e84242000007910b40307205c660440082c50744503e001074454414820384501c01d416656441c541980d035941107000e58405001a80d2100211001c0c880a82d024446640e41030002d403070040c1e48103095a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 108253525 1250 108252275 108252281
    0x7020f060108010908030c09041404080310080712031404080102070c03120c020a030b0702010f0905070e09070f060c0204090624120f0206031f030b101a090103090302070b070b0604 79
    0x100b15903414107500200241c840d20649030044582c1610381e403182c482c4da02203401400d4415040d00305640000074003041c040b04000560203651400f07259034803540c54a040c2551040705100302c01c0c1140c0c0c2c400c48040424800c0404141d203100d01c02c00d4900e0310765910781460030380e0801c550a0320041c180003820010031401c86040841c070500c0303040000c0381c0c038899000248884082c1c40058010705425000072241c510070b40c880d4065500f400c0b410003084480c6c2c24030a644800501460341040180d10219090210001d0040c048030b103d0403036180070a007421001c54002000740422070304140c44a08081c0003400501401c007505101800e000031104480d4442c1c0001089603101801e40c0090030f07103203808107a20108a1076426010764030b0740c0e030b46e444040c0403005403018602c040586100e002000f000300300c10100454014400a04a4042d040d200e601c4032641c10107040501070380390410481d00340b055001e5040203000600a0042d2030801e59500c2111003d81d0120008407412940b450800402d80b41600c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 108254775 1250 108253525 108253529
    0x9040606061d011d19030f020406140a06180905090c03060c0c0c01030504020f03063408060f01020f010c0302070c1502070302090408090d0305090405070e0919020405060307020f0601 80
    0x10501c03014032180d000010700b120010b44d8414916200705440d90029484180c00c461151000c00801802d8540e207042a150380011054128400e900344200000c0020780c3c4035180d039007e14020690003005240402c1034421603241c2d403c1c44000002420005050f100318880c8900c80d00c810005848150041c2d030416040c510010030031000807005000081c0031b000000f5181c51105402c0c03d0000e8191520f00001d100d20094920072a454401d8808004c1d010f64168444014a110056443d414000d0519407282408403c86203000080e4001c000404502e0030401d03001050304180180c2d40c4000c14240c29034207544d200034446c1c0120707400040385030030031084100301c0780144800d282c0072407001c200c40002900c40c40a480043d02c14500440400d00348a1810103d5000c0c031130062040c1c1846074507280191141d000342e40442c1c415490900060480d500480c403200c2c00800060024105072b40300c8a074280409550b11498100c1c81d424040800c8070380341c010080d80203c0f0282c00418500385107241d034618043c070507 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 108256025 1250 108254775 108254807
    0xb04030f11120f0a091a25050c0d060216060501170102030c030a090309080102032406030f041704090e0a05251202010e1c0204050703020c030d0c020c0904060606 71
    0x126030280340109601042d15541e00c04558182c0d6600e44e030003422206101c2d1500300c6070800d100045030064140414004145000700c0a80b0340580c10320100542e880e400103564050030303640200b0f08030305842c5800502c00c1c1003203101d6440103092000c1c0f101d240060801d000421554150f4033740042c820241da02c007261004000d42c070020340ca949000b058240050001505407030116445200090825009450703900c09080800d00031034403031804080345540c1c406080c1201e04030f02ca0a040180003030418008492142d00103000103065600c89540c0e074029400300b038602c0194150180000716418a190240c1442038203c0300080c038042c0c10780d0a1236410007214010b15080c0c10050760034040a5512000d640c1d00307c816980d40204030068500041c3d03421680c0d10f4690741d01c542910340d040c0f0080d4440d25035202c076034002d8070100655a04e592082d02240b050003581c01d8190b00521841c101d071102c5410522030100e0920548041c81060004654180026241100c641d82c40c2c0c0000d20441c1c0d44070407016110029 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 108257275 1250 108256025 108256033
    0x507020a090f090b160507110a0e0708010f050604030305070b1008030403030801080c090106090e130602030705070c050109080c04090203010b0405090f010c09060503010308031e130b0606040e0606160b04030f11 92
    0x11000b400340287c4600c07040140b907244005c041003a560b8802400030001c10b820101e542061409007802000a1002d0144412804d03540d81d010915080c000265010303264140c441034503003c0c183d00d03a015804002450308881118500d40424100020b1010b0402148680c0300e01896505200f0312034285030905103614080d07a1980010000594002661000c88a840008043c140c50b690b1401c0044001c03010080c101c03500000c184a46540e00030300400c00b25000d144200404c1361100300458400c2498415101c480e4403000500d5583d150aa00c0040d041c0d10050000940b65045c0d008282518001c80780e404464201c4910401c0b10f60b02801400c038200010b181842c0c40c0750500d103000c1d00500041c040a8400400400014048100030b080c40d01a00c6252111941501d09240c41004403544440216000c0350902d011894030309050302903c0945814032412a020381e5100144602500300e030300e50600c0c07210064400404200c901e403065010794042d903115105180400c0014100b154400c0e000d003031941c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 108258525 1250 108257275 108257311
    0x150a18020702090c120403050307030e070f06020c10020304050f0a030501060902041d06130b03101104150816050a0519031d0303040f030e01030b03030c160e07020a030507020a090f090b 81
    0x4040308017550f11540c1344c00c10544039100c981d070480c0100207503004800644034026000c100000c0750302d044e0040b11b0190b8201c030900340346d05080c8101070304001c0703411000d84d005100611103440c1140076400b40510141040003403c0d40c80d2103450954059030700100409500203411b0140e40000c01c0ca6000e0041c19a0200a01e814034001003801441080f850781c580d20755440c8440443d607014403418481a03103000e801d0005041c0765801e24002e034454851098101c5806680c01c08031801444414480e18441c01d05030441540c210003515a5840003402d68108042000508682c84004991140740e41003541c00080c1c448092000c2160114001400100ca038000c0c000c10000420445601051541c18607080420f2544080181c0c040c10906c0c8880e98540030115108501c4200060000d01240004102502301652006840300c041400c2e031b003010068109484140100340144001c0c645144060044131446554141000464001041080343c140e12081c45070140205843c3c1940c100380c01da03c009071408 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 108259775 1250 108258525 108258547
    0x4030b0f07050405060a0801140d1a13080a0905010e090c07020d06060801021c060e09071518120314030105011b02040204081906060803040509150a18020702090c 71
    0x10020329001200059100140119100742d080e64020400500784603290050804060551282402060310765109107058194601d4290f4001c0c44041c2c201c019140942c1202c03801c81810350340105040303001040a1611000244003d0082582000a540d0101e0300b0307044c28001092a020f03190150b1041c10340c0c0d010700c031030409040b0440d041c056046031205680310f040d00d4080c018001960141d40c0b00d51001c9603201c8464464207507000c03405040207040091549032045204940010740700c032015540119028004130085550040c0d00c0750450921901e000012102081c100d15142c005104854202d8544800c240e006100c1910384040c0e00c84c2d540c2117604000009140f0281111441c06034540c0e411100c1c255120360f0b04070f50142124600340c42c01f21640c12083c0d003080c61110000c030f40e614a0b00c64000742e0044007000780d40903110000c2c5450380b140c4500c2d10010411100400c040d1344559800c00005e81054449582d55104503212009030721103406004024045400505142c1920001c00c8112044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 108261025 1250 108259775 108259793
    0x6320a0614010e030f060a09060f0e0a031202091504090c14030703200f0301170601050f040902040b090702070f06030e07171e0303061f020c09070e0d11090105060403 73
    0x1a02080c03801c0030100e044030f000241780c441024901300701e5015010030310400080c25081400c01e0b9000d01c20170311800c80a4130940c3d080780d0200510f41c80c20741040e4500300002c0e1080204401944107044094102060700340003070281c40c48400708180039800020200003052041c01218124080d42c1009103400d82021a501143e110080030102015074841080d030606440020000c4400c01e030403185626110030a101c16941c0d0b10a00803614403091006084201600000d8164103844000d40f05200070080710041c04003404900104907405a01c0354a0070009803981030ac0c0c54400d04550b402403241a01d4959100c028241e107070000382c200350402c2c1c2050007040c800950722007111008803801041c0039a4100090800031a281500b0390740302d02403413100403050004083c1d0b0080c041168000421513510b02214000c00c0c5207544d40c2c0158001040700c250741c1c5090060300b580030182c0e04207140b20059100c0019009201080c0440303440394080401e101e84e00b0000580c9014210607225540361a040d6165035400c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 108262275 1250 108261025 108261059
    0x203090703081b010e0a14030a0906080c0f0c010902010806030a080301050909070e07050a0e011b0219051008180706120507020a0c0b070203010f050c120406320a06 72
    0x100410001d9035000340d250740b40020b41c101040304000c008105c20311400c551a003441100540b10b0b00744001c0000100c1c2c1010084950160040c5c0307079044040c0c40e149041d900c00c032004000301c60307039803092003904000c0e100c9900400300006117100010b5002c03001d10024001d41005406a8026440381e6a040c0000302080100c0341074500450711800c40b5550400d009182c07100542004481e03605110a02480a070800c000e000c042c40d0701d442c4c106264603100c00449003400308001a40301c030302c400b04080c0050b0800f1449184d0054a0b0000151542c1e21800858603144403c409800000c3c1c241d010406502c004445410001c0340301000342007824038068004080c032403481e0f951200c0f15078840208507450b008224001483c0e50100301030400a9480780002600e4201003000d074065401d248044d030170580e03248a00e6108401091151742042c1d0720844190780c1060003001200e00f15900e1032100700e4a00c103014a441c0d124200c403c03000c007604403202408403460300503010074501d5080070000d10100e030401800e500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 108263525 1250 108262275 108262283
    0x9020a03050f0720071a03090609010b090112021f1206050303120712150303090e070e10030b0402070204050907050a0b070b07110307020a230a0311100909020d02090906040203090703 80
    0x1050303565650000d41800c24503448119486e03030991075400307951084005184101a03060542d50540e0b10941c2070ba00740e8210401c1e05600580d034400500110350345180c0d0ba41c105002920014400c0c02034000c8609803e503031600c40010511005003007808400c06d004101c09090150003960030701c0381e00b90009441d140003038820000d0041c00350702e140310304c0d136030b944080044954600440310850b43ca0a01512003041c900070343e00000d44481c0000c611a024803003105107100013601c2c00e03016480400e022002844180c032540c2d0b00c039400f0040b4034096a218060940240c02440281031241c0c5000b0801c030300d00171a94410b03c4181c005012580205503c55091580454a0309100c220340c2ea030b02003120306500c901d0000950044004c0808038000d0315905140880011031040b01d1120101c010810084208a100080001902070340741c0300582040750703d00d4003141d40750a02e0400301d81c484105400ba070300301e442d00d10300856001ca50b00744d00785801c0c07041907000101684c00310b246050000b186900c50007075010280c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 108264775 1250 108263525 108263567
    0x120307030b060f070f030905030604050601031b090906020d0b100504030809040915050a1d030403080c0304080a050a050705010306030807060903051b070810021c05070c060609020a03050f07 83
    0x40307454a510044a00740502d001c80c0641e41c18182c0750460384442d01308820707000615043c00100b0941000078030319000c0c0f50050004d05190f03207103980d1300020030800c61005215040f01c040003d074401440c06281031044c4254405a150041000d161085909038414688100c5ca8010003103601d5420a04450659401040c0c080d034403210a0007050180240c040020070388004d40b002d103204800e09510040c060461034409000c10040b00a1000304020001000700c2d01e5002004200001610800104114a043d9007a2030038166034214403400d090080400303442a40140c4281810484103200100c0540001d080401403282540c42e15081400340750340c000c156950b1905800c0c140350048003540d0908401c92984a92802d8440c0c1e80ca480701141e2080045500c41d81d05108201130507402030b2180480b13410100302d030040c00d00b010100604000362036174051020003c0980f02107007031409000054030841d400541d50340c80484c401011940300401ca8010508444184003031254061a400e4029011090701 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 108266025 1250 108264775 108264791
    0xc061b0c11011e12050c030610180308030405030c010f02041a030901090b011203031a0d02010c0f020a0e06010e0a03030219150204080106150903120f02010905160503010e12030703 79
    0x42c1c585198036458000d005001d250b04011040c0d021341800d04000c20320200344001c0d194008030150500058900f640c0c884051811074244034803c203003c0e001c081d121410451115601e403203242c9d09600940302960341d40c100050360781400200340140100e11500c0780e4110301d418944958101014803203030300703014441800800b14100318000d4009110395074203c281c05149594840c0b80c08503c070b00840007200480e0804190201c1404c8030040c943d0002405049a400c48081e60300448001090b90381c115040204a081d6a0140e244e0100040242c080c070206100d090815034005030100d6064070700c40744200240c034802c2c8002a80401e0040401c40c0309003e1048089603480d15481c0d60030050194907410303202050001e00d804c0150001070480780f00c0e00c10010b140d030340b01d40d088400d0481c40c04090b241181c03c84c0d8500e1a01d02c58112001741942a01c00000c080c1900d41c1c410b41488000003203500708150842d01406240380c01c2c03180d003800040050050180000746800000c041c00010b024105040e13546800f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 108267275 1250 108266025 108266027
    0x606071709120c01030c05160f0213020708030402121f0522060203011406180616050d0807020d0f080c090102010915020301260a1407080d0c061b0c1101 67
    0x64078100600244181d100e440c02c284516994250810340703e00082c00e0071072100c4190301500c203c036601240324a02d105260450340310540403000050301203030040e1500e0755040140d1b000340301905115214000007a500c1c140f50040141c241b00f103061400c56500107102c04602d501034040e400d500181e680001081e256035003007024103456a10710303554124422a07982102000765036401141643c04503501564419200f03002d101040c0a035080d40051011103109203c80c602e0507401500c85481d00c10400000c280c0d099441608200c0584055004111801e01b80310803590140150302c1e21079074502d020803051540000090018401504125280c800083c5002c03050f4030039084540d40503081500d0000301c3c502ca410341d500a41c401d100b04c0d943c40410310400401145440c040c05c855540210040c54040c14580360072038200d4039220448481e105021000a200380207000b0110050204c1d00c0d40011180a4280303d401e0729105200480b181000301e900480c000e0b000081980d06c01c1c0c118400d00410303084400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 108268525 1250 108267275 108267277
    0x81b090612160806010f08070b0d0216170c0c06030c041202060c060106080702060c070305030a1a102114070f140d021b012f040e040305120f06060717 66
    0x400200e10521480000c40c400b0f4002541d10304032850005003d46550703849548070b0300c03506035004640c1c44a004101d07055801149801824110400b43c51600019400703940c0e80c030049081c00801652030b4030100b10700044c1c104c10300c060485048103454091540c07808030121030301c1740700c2ca0061514024503d000c48081d925107505032103800c62000112030207942c580c1005004080202c03180d07801441007200044d000f800900c10341e00000d41c9515010300b15261850b0440180603403003500d00c6056440550005507030b40d410401a509405a21881e45064441c8400340303400c80054083c1403c1802c0113200c45c4048900c45c006e03039014103d85403030991301d03800c0302c2c040724144a180d01404440710041154441203203240c0c000c08a070030303a1030f280c400c00301141380c611030076034150206100107030300782d00d031401d0492058030705501500820445141c50240c0790b0541048180040d0b03025000a074010a0f07804d02010f040454907042a02c8250620f110b24001000a5891098107002010850400f17028039480704014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 108269775 1250 108268525 108268543
    0x906130e0915060d050f031308190803040b0c07021011010c0305010e0406051f090b01080a0507080f0603030f0408240c0a0f0c061a100504050105071403041806081b090612 75
    0x11b4281c0b6981c40000100900b5414140104400c1c0c1c0a0107444800150f03400346039141d82a480950a42103a50316203414581210080007151201c0040202070300680e80d24035005e100c0440c50322011b20751041a840366003181d403842902c4050500d0840144511800001c0990340300d036018030003040da60340c2c4a041e1028008048204030081080d00d1010900081c0c98100c0001001c00703903183d804940d920b041d01e0080e034a0641300c05010403d9040820466103200800ca907000303801408070303803800101c80221500d40e0722550044155404c0f54801a800800d2048450401c1d014141251014140086448503501c80c01d101d400a02c40c2400108920a000342820158103070000002c00900040010301518041500040740c0310f03400140303818480d68050400c0d103064a0060350381c18100703001136940c80742800c094052916140b000f40700000700c18262280d0801c3d0340814100124071103203400180780ca080d04d02001d0150514000e9240380c21a25441e0300c256110f402111100384903210418940d08010f211 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 108271025 1250 108269775 108269803
    0x11150909010311030613080703030b0609030a05030408100606080705090d12080601080f100b07020a0e070207030302070501020303040308070c0c0503240609070e010807050906130e0915060d05 84
    0x48030001041c070821003042030354030750180c00350740ca55910b550380301c40c400114000007003440034203001102c08681f0a41c04511440310140005190140341c2001a01d8503001c0602110250702c001001d114080c2e040c411140c050318150801d00010341001c0014100707540c014000820068049101b440790b580f108800060750b508002c10907405031401e00001c200d02c008807035060218504002068640700019841c034880e00550a4503c0403d04054081404c1d5000100980c1e01121400c0080385000803007401501805468000b0f1500c6031540c9006030504a40d0b030721841c10340d0400c0c400c20001c250405150b0380d000449182000540d042403500d0460b0301c1e455009190584070780c040ca07581c0c0d5100001001d02d41c0054030032071036441d950384080100a810440304140011032008101d20194041c1001580110503070400700e00b80301184001c503520350000c601107070199800403810072940f488092000c0e0084042005400c11040910190f030040341e0290059004902050300c0b4402d228003801103014484c02 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 108272275 1250 108271025 108271039
    0x9010c031d0402120609150a09021c02120402031027080c07260a0f0803060a030b070503010303030e010e12090604050405040809030105090307050606210a06060e090109111509 77
    0x81d4540c56505600100d540c2401441c0110200c1d81c00f0b6600711040c87d1002d00108544403607400c0c00e100070040d40120003d0400900005038400c00c204990000d00800003015542c104a407401e8010145001d504d00b0700c5a00306464007200c0000415030012414460300c13000307000030b2800c41a1074201045d00c5401940e104a01a404000c01c02500d00c007126159114403c0741c900540900c0c0303203095103c00700840007c160051148070400007503ca68081d43d4000b10052500240d282d03652104004030604888440006d40008014810140c00d4416482e0340c9609000070030580d05468000d40d564004a41005200f00340401c0f07000040d0b030780c0c0085030050714001d08240100d0516281c03140294010514803442542850001500c0c2140081a6084190408014051a102c0c2014009206c000d0310b8804034039030b400111805c503004c0400040f84081d00c1904001a002d16219800e0b004000240c000b0020381d05120030007020820f031200702400c40c882100d00c6503941c044240341c881140321340000039421241d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 108273381 1106 108272275 108272287
    0xa080714040b010e090f0405060708070e01110f15090106060206040213020915070f0201080901051303081509011e060203090112020d060503011506030e0309010c031d0402 75
    0x40c1030420f45000000040171a04001c41262202c0710400714030113110800004028071540144c82e4981151241000d80c0024160140e081085041005002c96441c1101d0240b1062103401d64440884005c011680c48546140c0802c42d61090175501c1d040001031600e0010a801d071003158002d000c200b0082c8181c00900081d007003420003035000303131404221800c012081c2c030003040303810300580141d9022401c43c4001009254018010301c500c0c0d04100a1091040e0100140402e45038141003c094540e594010240d13480d11806a46500500c52000001d000d0070580d42240c6000b113201e0202d490741c0e128841a603072846100039150004c1c103100c44c095000c2e1000d9010705409800b40c42d021960f02d40c1c0e00c0000b420b41e16a02e006008924000324100251038042c42000c11482941c0003850a0005100c000f0703102c28120600070381886485003101e860398a0707120b01600102ea0040c82192918 = true := by decide +kernel

theorem cover : BRFrame.Cov 108093525 108273381 := by
  have h0 := BRFrame.cov_init 108093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 108093525 ≤ n) (h2 : n < 108273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
