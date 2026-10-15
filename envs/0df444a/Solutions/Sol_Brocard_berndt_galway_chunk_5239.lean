-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5239
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:12:30.769636+00:00
-- url     : https://prove2.me/submissions/ac3672c4-cf42-46b8-8264-348821bc51ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 942086330 ≤ n < 942266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 942087580 1250 942086330 942086339
    0x12080a110f0301050111010515130b0d05060105030d08060307090f0b09180d09053d0302070c0b090f090c130b0307090602121917090622050a0f0c 64
    0x103250881c1410000c1904004010310030f80d030b040740418130002d10700b0300203100c0351070000e4601c3d00790180005c22038028a070a10301410501c02e5500464006400a004020100118149141d0b1000c081c4a0140a0702030b02c0c850000c1580314a0b060b6200d108040c00174003c031031928048000403c8ca0801c000321107580c44600e000940d0303426a07440d004000180c80701e81503640c480d03015410101c000c0005c100b4440e0302d03841045075480b841002000e100c0c40ca0108212800780d41041d403104800d50080e801000c2034444150ba501c1e400d0360241000358020090304118070344800b41030600b0303c0351490b030a5200740e01121003071080c44d148003020343c01b85030025880e06010448030300c409040c0c195006913004100100c10092a19072102c490401401140300400412001036038034402031140180c00a204150348800d44800c03409842008a5580c407401e40f04010b140c6144541d4a078801554510304a9007400c03c2085401205102c20300c4564010300a003101035080c0d541d500304040007190485400300303010380004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 942088830 1250 942087580 942087611
    0xb03030c121b06131202071a0c010b0d05011a09070e210f07030611070b1b1b0102180102160b0c0a1e03171603240611160312080a 57
    0x10b0241003400c440241c44030592620702c80b094401114a011903014107010003803412a690441300e4601050fa410362750301d4103085524058402d8103111500020001801410040e055025100701403002d0000a0a80d00f46020450b0b5400191101c000180d034003039005000e46411100c0c100034291103544c4405034460f640783ca600b0050f6500d910a11600812000c206000c4140100c501d100c00100c41d0901e0200180e441400c42d400142040140c609e40400d4a4520a4500f003210340e0300005503508243c40111400e01c9010354001944d0860602040004103019400001c4000d013444050b081010450b040000c598581c0d008903050b1541440780080c0356001c103910480640b00041c0b500601968004e0609029060407038070760703400c407103018654100401c2d20300c080c640300444982031602094180c0200c80720442800b0f0781e003c80c02d940a002400007100c5412841003200038030350205481507840400c81704030f40d010080c400504600290049050b106105200583c0d01500c10880000c0c0e0021500425 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 942090080 1250 942088830 942088843
    0xc0315030f070f080303060108040305311e051c02010e130507080c0301060e040b03100e010c020f0309060306220e0705040e0c030d030b010306120b06040b03030c121b 73
    0x1c0e01650020038050240d2041c414481c00940324220042d442d50400600080c405100280094200500841c1401d07010b15607404c0c8a80c100340700180101c0b5520520075010011003107201c0d01c082c140581c144025010381e00d8074903a0489000a0681c80321070382c090317010500008124400c0b810044514001c2d1910340e84d1500180008851401c0000c0a14009202038840714018020305900b5006000400400e6405a029881c0307000c00d640116400c3c0684001c20b2030010042c1d00f40700b02ca070a2030354071026820150700080c1610015803c40300c0341454100400c0e200d01c10f0540d003540005080000806a050080d10014030803130016110924910300c11080040351407007080000503030042401000585084d000b000c20312039846001e040450500000255100ca0141d40ca10605841c5d1f440d07080c0f541e000c0c0d071009006180707182c80320714903e0042c68007018801c400c48200740300780d103007803c880498280001a41c107400c1c0044c004154908640903a5401a002002c0d10a220110500281e403c01c0040c045d5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 942091330 1250 942090080 942090103
    0xf09030f0f0306040c1d19240f0c0c0e06062b1a0d060e03040503031305040f050108151902070f02031c12180f080307090f0e0c031503 59
    0x82c0c590070301804100c20782c0d107055107079810090301c0090002e481901001503032400e001120042e04400350400900a406036650040000a290341c00c8040c0d1148600c0d101d203a031620303e640f81e2900c3c40032801c080d191382401b03400141200c054400d00340200145a807400e40c0201c001041541403c26200344640c4400d608034600c1202590708c110948112a41e01903007000f002e02c0604130070403140043c0411904500400042c00a54030364074840502c4c075051003114064100581960ba17030399041c0503801540c42191089030300951804140600d20406485903074141d50031700000e003034000e0288180c0b0b690040b000c0e02c0b00000c10400070304840e1110081c402401300f00d00c01c200401c403a2449004150038110300f403d41c400d40d0a507021a01d508154404c04a1b4105403072a840000c00f81300041c0c40300300c03550718032070020701e60003043d10030b44140002c84000c1d5100388010743e00c000c00c182e141c0080401c0710025105007040d014109001c1090358107503a0141d54414640751410100681810002e860001d14504 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 942092580 1250 942091330 942091357
    0xf0601031a0c0a05161b0906030c0b03070903020d1a0412172511070b030609010902120402010302030a0e1608010c0903381006170f0f09030f 62
    0x828010201d121107880b603011902c2d41c09581841c00e20080986644519001070400104555004c0708100c1440550008a6000c000c0c00c0215901c44218a008240c9400155000761038100d000440c034030b04008a0b032185080e0360b0b0f5042101e14640c24040805940071b801c032001c0d40800001400000d00d040ba0521940c060080283c2807208140c0190194528024130403a541001c002c121940c2c022219401c4482280111808285410101114000c0200704010428000c002c0000340340d4036500040c5000340000c80c0c01c1d114903669608104120300c10100d64401307545012001801641c001e50107141e209001e404007040034240c01d26041e0400701a000845a5000344180074850200c00340324400f880d010904003041402c2c19a03d5510141000711100c8800f2203413040c0c41800b4100210780340d40b4403039145080c540d071418040102d503518a0640074000019001d05c1d081c1880e4901c0100c80e40c000c112007404120551508202000b12620040480090303210030042414138040341c03030041071641078080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 942093830 1250 942092580 942092603
    0x5030615121e011a1f110d03090309050402031e0c0904090b010609050d0b0712020405041e06120206030610030e030a1e050703051804021c06050a090605030d1803020a080a0506090d200f060103 84
    0x82c3c09802f22801e500705c540034500c1881000b80200c0e020600d081003980001341c2070b1481d9a400042070b42c0d44035484405030814246022141042032081c0164180c034641d8031845000c0e80c07103c0c144804200c00b840050002020700002c42d00160240d03d400308180e403107040c0175160030f0b11007010030151659040e0011070ba050446030506206064855600036010b064180e540c440b180e03800003489804080c01c511320546240985842d0f841c040d07800521040109010b40e501d074048044050443c00c80340c60718080849040213a404060303c144120b0720050744c192141070801151904500880034000320701900183e08102d01c44501e012152403081c0040070410100f140750030030003400b80c140c000d40d1222681600348002800180c0d000308004286005600d820700e0030b8041d52003003080802142d4406500500c6c0c0e40004110342101182411003a8040d40813101240ca0b4914002d03914861650034800050704224000d4000c150762100c4058684840125603236924010000381c10030710281c2c002c441205010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 942095080 1250 942093830 942093833
    0xa27120512040620210c1902010801031e0c08012a0e090a110a17070c020108421003020405030615121e011a1f110d0309 53
    0x1c00c1071184410507142502e040500d003810140c4138030784100000c18249014010040180c60402c003000b03a10880f4941324002100a0340e2000043c0e2188010751140c0c0a0a860317907082030f52030340c0c5817110b240c0d06a542260582c81d41e04e4159104418a1000b1403c010f031840c0712021503000070030b200140250100001c0ca18041d135610000c41c44c0d210104140241003005020500ca400c5a005804032200ba0b849414a5844514100040048041d01300c07424001159030b40c0055408410340f801e0400101d880320464656a90035101501e06450003400030341c42e0340001c1c500c1503018105031451545042280000449402410701412413051064204030012280382c1c0c0c0d51410f076100c0c0785800601c3c1021407070142080e001c2611028000d2009905544128001105469034200e00d1022100541513460541e000b001c00c40442d40c0418510840350300700300004c06816808207500320000c90090880810032180307071001c2c09040d000e240d69814400280480b071001c20040c8242500d51100d50360000741217166 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 942096330 1250 942095080 942095083
    0xd03021317031801020307050f1f0504170c030f0315030d0804050d08060a09020c01150f23030a02091305061006081801110d050906010909080a271205 66
    0x259408954224a901c0781c44480c16400300444920104200f40500b0081000303005134610310868500802c14442c070600c0c844088004515136000d2403884003801e0814041c1d8140c0740944a0944000e0042c0303a2a0182c1190780c02d612000700901c80c0c00381d00b43c906100c0c000080e0b03801500204d910b440070700324080191856150510240e07209030080c0c1002d10450416443c3d06e6600d650241c1035006009500011070002e039500d11796080113049011055540305082c8170030030b01074241d03000c0c842c80083c0c00c40d20100361103103051507a1040c0e801e510340a2800c150701100020981941048007900360060000080143c0c032407034845d91113040303402082040742481e841d2540c540319000b01982c90043d040321041c0b0516501540460708000700d440c4000c020561540d1250042111411541a0400c0080c408aa080140c0c2140b4840c0864006407032140c3c3c1c0e02ea500200b91200454010407400b402c10081c0801402101e1500246104480c040c220f64070706000800f20a0060300702d03c00c80d400d08040041040700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 942097580 1250 942096330 942096367
    0x40221150f07020a062408010f0605041e051009230c210702120d1508030f0a051303060c081909240b0d080a1d06070807080c0d0302 58
    0x100ca01c11841c2c210030094807152400c07401408a601da010040400e106000c13201a0100d0074046004016600e86002d8020100d580000074250305020b000a4145014440c010002c1c1c92070951550951120785908010107005100c03500c007030001b40c0e02059401461244000e17001024205481c120911602e038103042400510750714090000304032495940d0902c5182103200344015410382c0316074917007140907401c10124a502c0741e0508800306818901c1c2c412038101048110075000c00312200341c1c0742c03e626a184c1c86544a00c210f103910421140300c0710703481a002070611400a0f4180c00c80b0382d8881e42c138031080c0e8100081c1200000c0c0c180c800d00c8200700d110b0110115840010004020790ba51580e284041c100f42d5a210b5030040107200304100380703000c40e40c12251802c14020301c0b850a4100034a000c0b0050b03002001303240b001803d900e56a040340526002007416488005101600304403007aa100c00c0c169004204c119030300c100621070200d03189401c114280d44160340d606c0150300e600c03503a0308460020a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 942098830 1250 942097580 942097591
    0xf0d090e090d050901021903032c251a040905130f03050307050c060103080301080d02061521011e05101a13030803010f061b0302031204022115 63
    0x12a5034040c03003a200340019410309518000d05182e51603202c1900141d00300b04007400d40c00c00d005c0614040030201a85070b40030a140c1e1400d9941c3c948171a42108144c51300d00f00c1c5040341d16441d401506000010800c56001c0e4043c0c500c1901e1007540c007174898080804600200d803920840100214007400502034501460358011086940814152007a40380e95044809400000e01070203000004100a240b04004446003200da20040b0703905560340f440c202e09568400d20400718a4061140829040d91000c41d03c07500959407841d400780400f00000030081c44c41150b1249140c001e02c081c00c000c144030400e002d01c0f0180360541e1018241880d001000005443c80285101c1035811041d0301840500c0386090000c102070343d068660f948801c962a0310f43e01120442c1c2000d000c01c14040000a000e85442142c0816160690b0702c0107844000c010280100d807010080c0200035030014842e40340c0729901091419032180c001003c40307034600705078036100c05140b903010380d41c040361380140c7c0009650b0000d9018039601310 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 942100080 1250 942098830 942098849
    0x19030201020915210c090334080619060f140406050f060a030f02070b0f090f210307021204080f1203010f150210051008060f010e0106110106080f0d09 66
    0x200041e4000903142c4890900e074284c400ea041c0c08200c000342c28205890540354040c04232505418115081c2d403044058032022040c01c0740402e0040c03191030781d1f524071008a601d800c00030602a220f078a00020842410010100d00644d20180094001c1007507000c20300504c90441d20803138141190007032000755421074000500070804441e101c3c580d61a02000ca500056291500045010314203000c0c00107403042c1e05000c4c1c2107100001c10310585078641ca01c5076001e03180220855100c901212440e40d1540c641c00b0f11000344111504404003e008030200442e03000f103003441034803110000101d170321480e0740158200d41c0d0a0340c006c0c207805082c80400c1184001c0541003080850a40d8034294802c01c0c0c145c10760003a00d010203080c0c80c10050150003040022040d030032444052245180201909502604034070410b0020302c512000300f40c040924504141c1612130390340c2e58149503070808500344c0310181c404161517203d40d44c0312400540703c2014820500400885d1000d4406840d100c00001c2456aa903007010400c0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 942101330 1250 942100080 942100087
    0x2010908040612090c030318120b0f1504060e10060e13180b07050d061d0402190e0c030117030c0a060b0d1401090b07030902060d05060319030201020915 67
    0x41410101601d085400301c0c03802000b0124080c001401070040301c2001441803007404800b1080542142e40ca8224403194021a040503030b80d00180911020707104000307082100c3c581c011502d90041070390690707440a02140408a182034000100c0c04981695002d402d090120206000b440d5a03081d02074070080107549045610800c80f0000a07403218040f240c6812050b5940c80d0f00103920100c0c0b56020a0140c102d90110491f1800f51030180ca0740c0d1050100c40ba070f0b24608800802d14441c20b180808042160203c01c0280b69030309d5080c45100c41868807200d00e00044000d002484000012240f4801d4450809903500ca525101c01004641c0c166145900c82d500117016101d0003200005c2c400c04800d801c400c0c04a904401400851510743c2501d1001d4008021251038000e4007805422509009100303045080d03687d9a48031044044900200300250301440030000340002e603106422040d0082c800900b694a8440031b0b003c90040000c040b030003100946d402041c4080d092501ea020450300c210300d02c400918 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 942102580 1250 942101330 942101333
    0x402041103040f380601231306080c07020f0a090c050d0506040c021f0f23010f05011d04060b071b05090c04170709020f220b2a01090c05030607020109 66
    0x1c0d044130b05900b40705401503d00000700305038440d945211414805071400e86088641e0040e010090b448054045201c002076480080c080b4031480c88c081c46194440b07a01800c0081036400c03c00b401c000143c29030ba01040c80da002140b110410b10612604491545400303540301e40e861a10b105541000345107512980c80d0884010260340c001c0381c081c0701340301d182030a14401d490309460344000300507001c594240185041d541e444034034500402841000f40c07441034250a80e0b601d42030481d1801c41c0c0d0161a001404520440340e41d01c006440c0031680050080c00071441c07d03180c0c0d00581150f040101c080c3d51450344c03a042a0207019050603290082d010980e000a00c2c4d10303201844000500c224481c80c0c0d00107102d504a000c110000b40907480c0640b112003010b6503500150044800d207504482d01114124100c0b4030070710f1030301d410031240c00308907071010400238100340008280c441070300c1c540d181c0d4a4410207800ca50f81c0079030f8402c0c401c4209561107804052140f90414040c035281807401403008040da85405c01260 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 942103830 1250 942102580 942102653
    0x80d02010f05090a111909050c0d1a03030d020c0a0b04080403150501150503040516080105090f21030910090b0103030311161b0803030108012019080402041103040f 72
    0x244c2d004050395050b03c1c03c4800700b10100d46e0348840d0b12282c0d0491800c01400b513500040801060401007007030703090200c401092162141c0200c04c811155040e0300400c00001d000c840f07038010b001c10058a400391107084c42c0305c0e100e84a032080c04a030201c40c98180010280104203408118003c0b016802e0f000b0002903051010310b500580c030310788880301070100100004040100400220480b52005001208030660781d81156010300400d47d01c0110502501c1c1c03200c11405800122440f0908401d45401c0400d00950700c51341483c2d1000e400e0308146e000d0400c85c400c0303249aa00034004460311600980909601d035007002400c48111261005030032504200e07503c001d03510000079485481d0003045001002100721913103405a0a10341c821480f40c0800301c00000d00b0b82c010f600203e02440c9100301c0020001c542140020284a40c1c1002256030802d000301c0380b40248500b0945502030720103000007400745e498004580036a0000c48086407920403101404040110340414a00c40390101c1070080b44038001c584801 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 942105080 1250 942103830 942103853
    0x1a040f0801090512030411042007240b010e0603090f19031206060e041d0a03110c060408060a05130f0f030e150d050415180c29070309080d02010f05090a 67
    0x3807050351119042c100749c00c00c0580004401c1e01034a98030707641e44140d14040141b490081c00c40c800c541c1224880d0200391201c1d00400c0100c400595450080c10006c030200809500f0245c80f080c058403900c41e01c03042c1104204a404203d4040540300d40c01c0ca00c1614004140101241000039224180341080013520340045116150803070480300800c81e1244a00381225840741e0204043e0b142c8103050b103d405060f0440c0c0350048a100320000d17039542c03801510901146120380e1240001d60343c00380000070306007a0b19a024940040781145610941417032a1645040d80b801900d00341c0340d500c5102e210740c0800d50401c3c025143c21070f09072201c081209160040e08168081e18100aa12075141c5002400f0840101c10308690903c0c1c44c01c00300700c1c03805054040180103a10178030481c1c04074041080031545824840400b0250840340c100040020240e07061010240c10810381101405800c0101140800051200301a014619800058150344051000050301d00c05002080281c104108040109003048000f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 942106330 1250 942105080 942105113
    0x80715080402040e0a290a0606080402101b061e0c1202071e0602040501110606060a1b0204050a0c0210020c0d0f27060e0405101a040f08010905120304 66
    0x440d1310001d11198100f40c02d80b24024000c940c0d02e0b403d140c076400017001842500c85003480c1003103169560080e9000310344060007a080810440c00014005241240c446003c446c00307440c10760981190340c00130006200c18464200c0d12540c03224081552000b42d00781380800105109410f10004001003005080c00c52207807040b000c80f5400089074424440b090501d99010309108032484031442040c140034000b07400500990740090315040000e0343d40c10001402038007035140208158a403000007601a42d41d001d0039051080001c05042500d4056030b03507482154416a80c051002c108510100402400c02d240070002103102881031104d621800000102e2808007401c0f801e00380001200300780140d8040c22028425042c0c1c11440940300c00203c1080d01d004101c95482d158503581c0c616050402081c2e1705c0448942c440c00c031400000b049100c46a1401183e9900e00507407142c0380a03141d204850b03c03051603400130101a034441c4041c1040000c1042400e028400b404003090031804d081c1c1e0741608841d415400c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 942107580 1250 942106330 942106339
    0xc09020d0f140f16030b09091c020a03080f0a0f02070506090c030a0c0e060415060c060c0801050d0f140f060906060306090706030c0201380a0501050720030105040c080715080402 78
    0x20b201c203000b5404844a071b1402000301070f5500e00407800030b6888001e07410000b00d205810620110f90750002a83d80c007030039410348607080070f0369814804104607240140301e044000d03255010031320741b14243e02c014503080e80100060051482c24000304d030f10780016501c0c1c00e80603900c544620808110700d9019030003600c3c210100383d03d5907100c0500040c00b45c19203002800c0382c0c0d031289200149242d00f025110044034800c8d98203100170a0760f20000c9c0c031000000d12845400120304041140003c40764842d015090344117130208a040b000444400307140c0700c111003138107150740d000720240005050100550707680818110000c0c0800d1034030401d001e407520841d11a40c0141a100c00c0079682c854000c0d04202c0d01000201010003445c11000003010744d010108251005e0f03045086107201050420038103010540301c040c1c44e010b00e811240e59031000c801d40440408250082214040c0e00385550070301520f07004030b004421011b0110b04040469040c16070359400380100200c01010703400c0343c0340c003d8250355009070103d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 942108830 1250 942107580 942107611
    0x31009020a05100507060501140609010f02010603080f0406090905060a0e1b030a1e060b1c110a08011a09031e010e07060801060e0102150c070c09020d0f140f 69
    0x804500004401d0700000c2e44910543c01450841d98410042c01d41c2d540542000d00599a03034121041d0205c804000c00c54000400b0070a4218a50040d10140310303401d114400010070950340d843d07162080d008208850b50202c1300003030400c040b960146800c40607081401c1c1c1004a401d04100054407240d0905c42c00d000d030b1031101e0008490310100c030650284603440140050392894004800401410b0500107081e80070310b0032081410070a00c504c102e105946a110100d850701d03e541d40f802e20818504e426042015440302d040c0c00103201000080c02c810000fa446a140c5541400400d662100b01048541e10801d424840600c86680c006291166008406c01504400001f8070240d400740c0001c0d5101d1985200700d0740000b400a5200014034100c0d01c1a540758448414071100480e00e807420443c0300701d4112410030108111080400041c034400348100d03016a117040d586e40d0198241d0b0460403040051030303134411024590600c00d02440980c0075000241119924003222580300d040c4000c2c05074180c0b821440e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 942110080 1250 942108830 942108833
    0x6030c040905062124041203020913180308010e13030c02010c021804150204180e030c100504020103050a02030601050a0305100f26030903030724180b0105010905031009 74
    0x650115040d0060b0707140f240104244d10100b0369505024600c0d2103080d1203106401c4c0302c100c0342070346a5000e030fa8030200280f0312110029044019411800c04141d12201030126010030203038a00c9003481028904460b12808032103400c0240484505030b006100002c80e400c02c001c4410b10071115040b2240d410306007030340001c0c41400100d801e010011402900b0980c20f0010700030185052000c10b1069118199045010f22140c5240c803d900442c8030300001001140327034580740003880341c01c082e424011a2080707078200b10103007000b246840380040d6920200d554a178240000d550b0325008465000205080551940c1032101c0000d000e841000c002c03408142d41e038400300c0c5080c810880e10030014600101c140c0342503030315040c20001550440e1040b10907020b50a000c20b90004002c0b003038400d4114028061401c2140ca40c540075106400d0503070f4400b1481310000b1051000c2d0281c41a8507031040c8442d07480800d000585090890003130306030009814400e000c42c00300101e503000241c1c80c3c0c02a120007008071708501c05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 942111330 1250 942110080 942110089
    0xe0d11010609050408031602011b1409040c0809060717040b1305010c0f110a05120a0504081e010b0103060b0a03090c03203a031707050d060506030c04090506 69
    0x1a040b0b1a6603e04190070b0000b40901c010241d03014a00c103548010340c1b0000204140d0894030b0b02004440c40200c661405445140584819a050040040170324501402840001d0440348007101c00340115a14806021040c4070812510340e00181d03500f031100315102d090301850364580d0000d1000f041d040c0020009443e00c81d120000054040c0e000d8000d00c840c48404d034000e007188015801240000343c10040c40d440062002a101441533040006003102000c02e249039080795010345414014420100000100e01d002001550f140c102400c2c030003c411111140800d007910f80c01940d1504060030060280501000030044070006101070900045d040074524141e0b00d90310142e0b0000e00f0301d02c6c200f801044a5000407044240c800b800b100c03495400300081032540d603505c6a9040c0640203000c10811042522564070001510a000e400c200d4143c280c10342c0704200100c1c0031a007510003e1008101400c28001c01e0164402a05040381c2c650704519001d806204e03980514411095225158004516141c55 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 942112580 1250 942111330 942111341
    0x80c0a032414040b090f0c130f030b060619080712050c0301050a1205121b0a1203060f051507020a080d03051009050603061303090f060207090501090e0d1101 69
    0x406900014203034080c0c0520009841c451040d001e28920b030851002c07003441c003440b0307018001c078000302810404d8a0b2060300488044004101e884d9980741044924040c403d0f0f00c55840041644113459450107046280c205e04003807014141d64000c030400d201e103442d5000c841440c40d00e4411540b504000655a0348011500f1a000319440c0c0c0c2d00900c1d0005002c03040e0250001581a03c800782d40140080d580c0300300248100310304142c003420a400004074102c400340076038004e141100041b010301e82041030b80c035900d40c02e15848040440704190f1000840d20349541500500b07004010b003d050070b62440c503000118140c0b4038820031204800c0d50009506045641d9200d900b4081c156103401c40f9055400d1000c0900148826a8a2000d1003405500082d080002d07000d154071940003e0003518140d1521502c2c545400e00000c030444c14081c0d103502c0821030709c00a4049000404242c0e0091402c5440c000041045803410f0700030501050a190724108a11000111038446003100d01d4018040d0080102c079600400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 942113830 1250 942112580 942112601
    0x50109060f0c0201112a040c050c0d031a090c09090906010f050d05030f12040c08010219050d1e0c0818060106080711011e050a060e010b071a0a02030708090d080c0a03 73
    0x20041d00100d000441400104a91071b0002e60f0f040080d20301414043d100d90007440f00d0755146d5402116a032040324440d170070507041e01421032404074035002c1c5000050f602e4402204c14451607200860076803030754500312080c2500300074000302410465040c01e03441ca00c00d4404c0e00840e4041c003e2074448204100c1e04004884190030525004c58a03500e44100c1000142d00546040e074500440902c00314180c9810702c01c44800c21010b01d0f8003c050380542c502503604c1c0d002900c0c1130221030b6942110030700071381120410403001660100002400e007002ca002524152005d04052581c465018507150b039058002080d03415200a420816580e5a50102c1140d6504511581581780e509040700030901013404503543da50002c96100602c01a664800208221813440c03082e92228204000101b0490014800414116000d001c0c08a03410703840d420301e21682ca000391131a40001e5400404c0000c41c5a00010141e00032200c103003d04140c140e1403c000384040c002814003501c15100003281415031b4000da0112600d007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 942115080 1250 942113830 942113863
    0x1409011b05010c0807020d02030a0f0f03140408040609291b0706020610090b03060411030c030303040f26090402250309030c09020a09090b010306050a030606050109060f0c020111 78
    0x3c81c141e0000625111040c0c803041c0140c841c2c9007444007894004400e5410540c4940d6070040c03d5010f548088510030412000d4000f0715540303242c189000140031090510450103110011307901c900d801401410351045501c4495440e444002c904c5003120310401d01071030428140c81403501c40140160400304110b005410801a214010000960540100c0c0003849000c7d00c404000c00b0750b81e40e50024040d902c521422640c550018000100050b0711500e10324113605001d400c60b08800414004280341d03520a0f0380c00d4480080d070f008410201703d448003000c44089060a0003d4a07162907a403030544c0341c0181c0340060301c035036000304000ba074039603500c040c409481540018800e2290781c00e08015000540a01040d10341b02c81a50012401413000d0080f10055142130781e4804c8038500d03040d07201004203000240300c1c0c101615040700041c15500c80c1c0c105005540220030010b081c0b49014005400c11145600c04c0301400303900111046460380141a01c0d074050340a080004000408988181c201040703070b00442c081 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 942116330 1250 942115080 942115091
    0xf030703090506032707030203010510120201080a110c0307110d080d09050319030504020306010504050903160602040e072105130f0f1718060705061f090c0e030c011409011b0501 78
    0x6c114045900a0303000300140d8031783c140392000d41a0280141c8011900224881005504c62040c8543c40324100100040c0f403140b00f80100342551240f44d102d0901d520208600c000e2100c1c1c0407401082035400c45a041031005103581c3d46a01e401755030100e40105648044800601c2014000c4a13001485103440c0c0c14003c41e9048090010304054906a00a10500c0f00100741400c1c01c2c0700d40360048036602e0065041494401e148540d4006400302102c0352a02444005aaa0510345107039000321402d885000d49a403030312509002c02c8845c1d6500014107800e00c13060080b50310060b00c1800c01950004010b115884090070525882001c11800400b0000c5004006031080c80001c054803100c140c123403144103150f030900201321060041403806040303904040085007400d192418200f8005c0407140f000740d0b07055640e542d081f0441700070b148844080f850701c203c04195480c007440486988402401d19107410a07603001303080f4482c024107070028148041284090500c005008503242d055500c60000c0c4107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 942117580 1250 942116330 942116401
    0x2010e031b2e0c03050f1c23130201020c0907080105090708060604060c031b0b011a03010e0c0c160b03040b01081f0216060e0d080106020a080d0b270601020f03070309050603 76
    0x1e87e0280000403009403894410070421803003c00c204850107005040810111f074a4058a205c0b500c5183c403800c90662143c010444503940320f05070240d1085240b52502041d030740c500010700c02c0e16a0003d1071f043c10080d84404001055031840159000d644403842d0040304848a8601500d02306110484a010130490045603410400f240f41ca01e8142d460810450302120605c1c1d20041c003501082c050303c18005880e00020b01b80e400340a02900d0f003c01e2840803541c2241650254422281080d0410f05d800d500000401050124500340e203401008000024103c43e0501000001802e61190000d035026400060140c3c0d446640000c080b406504200c0400c030b600c95042030196103c0e40c0d000088081094a000003d0340c90010403414140e80e0000350291500020b00050401049a5034071154805081036913a000940103d034580045404800081c4c1c0c6030501c41d0001e45821104071904510f07074800c00680001982c030a030341030121942900d01d1612902c84034490b000c00c0700140300880707060005880048 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 942118830 1250 942117580 942117607
    0x309031e030323131703070e040c09080d110708010f1407030203101809170703020f1603060506060705030f190504050a05090402010e031b2e0c03050f 66
    0x3614588a601c0800022944500b580100f04101480983c40e0580c0d60000700004228030400c91120711400105d50200800d01014415130001e8920700b0002d21003014008003400d09120381b1500541c1d5040c401c10983c6881a0556030307041340c0020108120826507071041d4013800b082114090b181c880003e108410724001854028880d254518030b160b804400400c80d498082d00c2200d008200555400b08010300b81107408200c90f10040360010342135a280c800b0300215030740201700c500c0701074803002490340c515443c20003d02e4001c401060501e0b5404c2080070007110003030381060343d003141e034818800704030303507441e02d0006186010300c0c00080c2c440e01001401c003801030f0555004140040184211340208120000c0450781801180078260704580140e00621051501c46581580700e4414174207101c0c3c8100d0302002c80e0420148000e8030080c03021001c89800c903454402101c10031a04102c01c41c0c500f0484401328101a07001c0e40e0031000c1030041c41c828410502d032185040301d01d01c4450503d203d17982d00580c51001d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 942120080 1250 942118830 942118883
    0x1050114130209102604081903110a0e03011b090312020708101e1505210a0b04020d0615170c010c080307030e150618130807030903 58
    0x181c031600440510340c205101a00c2610b901e240c0c041d007030401d03007481d1640c180c440c59202c912024480558404d80789034006403a410768869481070710180e03203680310004071001034200744590b90300380743c1856036a0032203003450000e03a11030070814034140810610340f5000c2130041032010350303610325142413058004105410143c9602101d202d0348250503038441014080f43c854905018207441a0041400e80b2081015508115039501d2300e44450707001c01180001c0602190b50a0b005030380900c2c1070450401241c60207084501001030072009076000086940c0c0c070300d602c032005030340000c1c01203081401040941d1140d01004042c6680200d0400c0101542d641a100c8140ba520841d03400c0c440c141402c0c00c000c0c0001c60440c5420b04103849018103c0d2495aa0410541004080404165079603042d118614810800d9240d600201101e0000904000090145103110310020700c00c500c07804401d210b40d02c1308081e40c20000301d8000d501e0540710314883c81d044942103080c1d40040d0026080030ba110315042d446a644 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 942121330 1250 942120080 942120119
    0x1b0d06051e030d0206090a150608061501080a0c202e0c0903020120030c07030305130b091005030c070f0605100f18020309070807060c060e010203131112010501 70
    0x840c3c41441699008980e502401c80d021103844c0c124030106000217240703001001c150100c07040081042611460a9450301104883c6001c0315410300d400d510741035030080d501c65008050700ca0140b10720450f005014103481e40d12202c2c4203801c0300b180028180c21a06021001010319100c58041e418400b1803038100c0d002036920341c40140c96140103407008200c0d000b41042070450746d040c2c407941307055000503140d1a0311000044c03021038907001c20001603620000500580020b140309840e00d40c0c48040c840b241c20b0f400d1441d6080391800721000c20031300e001540c9000c0500040f0a1900d44141d072030b03a4080c40803543d4042c10900802c81c00766400d000c0c080001da03821092160740f8205031102443d583d40f8200b24031440718402c10214150505803103200103030303075001180e000c18020100c400699840c4140380c5443e0f0942d12807400034080c01030807003c1040718000c3c06d406503040f800a42c25404c12048a0560b0640d00400401100d030758403010711251290800311100a04c00030081240390394a40c0b841c030038000c00020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 942122580 1250 942121330 942121333
    0xc100c05010b0a060c0821070908120408191e0f030305090c061e0405060c150a090c140f150a030b01170106110708010c09140301051b0d06051e03 64
    0x30b5614542842d404280880c0d840e60b45a0710450404d031a008820b40c005803031400c44040b4041c84d5440c4030b43d0140d41340d021f00d94541d02d4103801490242c209042440120b041540074108000c200b00c03019000400300346c82d03c401081820003500b1450249005209610320000f5040703841520414032030380d9a165000640203850a0085a55680080307458411210a90340d2100e400d0024400c58110520340c61840540e11003c5844d040c0c031070713000034810340144504809903880104420710030510307268040e030001101c4006000c45060742d42d035907607451664001c2c41001d54482c100f03103413940c2c1d1360078150315002c40141c92082c850051441d04061540200100800310b130501e01101d8065203c0c0d0302c03642c44070f4641c5a0f0781d25035909282046584084903408600e55100d421808036144078284075501c090411341c1c0703d1200e07192605441c14418842a00054800c2c0d2620741044401d82001c06070080c40c610404071641c0c0e51030031110001c020700c829080b080d000040180042a1310040440700c0205076806c40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 942123830 1250 942122580 942122591
    0xf0308341b0803070b0a050601050c1507110706050a05090a09140402030712081b030715051501030606050a1103040b0a0c020f0409170c0c09040b1618050609030c100c0501 75
    0x1c26a596072140740c03c005d014080503000181d16421560203107400c110b05141030ba25020b011002c01d0b01c0d0011003208030349420900010b0056864008014106403008180a0b0610324070b020300c05401d50140441c81002c0c45800103485005a076008101e01c0a0210200c040101c09506081007001c1d071411502240a0722615101140e41c20750b010000d8030b001e40c441d0140d49440b1b8201c2d00e0380c0101640d01030104440c0700c14800d0b0b1001460300798420300702d00100000000c5514200c00c0c000212203034008000d05040c541002442035943c4070b011501003041e2401c0030040244001d040515502c929400110040300c085000495164495165031000b402110036010000c54241000115000160018080e12044a0340c2d0390701c210300805400d2182408041c1c0e001d410202c0041240700300c0c1268200c070301c4840322080007112180c4031095990b9030490f2402102c003540082c0d00300541e51941c010701348100e1020070180c1c40d540d4100101c002c40d10001c5c0601d501c540f14004064000c401c108021580d550030207 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 942125080 1250 942123830 942123839
    0x606030204120305070f06110a090506211e070e010206090309010c0308100305060c191e230f25230109060504080a090f0308341b 57
    0x340255015521a68110381d403000056600755141d030311110b821035208840076100350110b100b40c841c0d140801c48250005030f4a020b19407004140807080d4024a1150106200c01c0c0b4240780412002b20a07500c0110358100c0c6511189060031450541100c2ca40d040103144e800c002141d41d200c4141c4041d80c00a800319611601c450714a0307034880c011581003d00058140802c0008644121440e5800c00c01c200e10b40403c154903902d5080c00e00d0300c00c03140031410040020321030420610010b8000080581c900d09125041c01a021040090341800c02d01d0040200003558011031b29501030710b8102140c2c085c510b207560b440001d107031805c00f500182d00c604c1c210008090100174054010800e038206c0369120b00c4080e10134034801c042c0c00c2800d0f40b00314401c0c01c3c1e6680d4091440050300718030540c0d024038040c04010303803506079181000f4541c800036003242c074030b0f8050402d04100044010003035802241002041c3d101c400c8003c4400911900307c04400c450030a425041d01c006d11004a800040008546841c07629860704d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 942126330 1250 942125080 942125087
    0x1204050a12080a0f110109030503100b130315020c0304030c050a170c090711010c0905040614010212030c090a0f060305010e0105061911010f0f230f060a15080a0606 72
    0x11a900a800303103400b0003602858134441c1540302c210801500744004044181c800460031690f860104401144000040c00711107281030042c00f006041d480c04c07031480d01e0140391100300125180e220017000c0c68040a00d04841c1c1c2ca04c0d8040d6a692090303441102e0710f403a52400d264240214078445c03039007e0b000202000c2900352242d8074280c0800341b0000104091b040000600c1442e040091046080008400c00740780180001c1c01540340016881d0344001031582003030708010032102164000c812a001c440c0002c9960790700414003940914070340340116202d64854900440d0307403051802c0c0c568010305002c80461101180d001c00c0c4280c40c0300350b0781000241e88480340d81d036441c2000e000311940864244501290242051030004148a50f4503107820191100c041c000d007910043c490785000583c5903100280c4440031807150b6040e4140d09a8882000c000440310003404c240081d224800041815001030030b180c40e05c0815200401d0900c24000311904012001040e08100303031404100c441c207081d00060910320 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 942127580 1250 942126330 942126359
    0x10905040210080603070b0a020c03010608010c09050d021801080f1c090e130b01060e240403021311070326010803040522060605071a131101030b031204050a 69
    0x80c0608611046464490155070007000100358582c144200900807503507c0214010f0710009003a0b40041010381d0325a0201425030350a500044e6082c1c1c90661070881c07031540140304074201c0f50196440e4081c22000d0021450165050218104010700c840c000206421300040e030000b542004402c0d10749181614008410000540d188d010020741e06100601202054041c640d400400003280050782c2841039445202000003644800301049440c5d0340034100307040a920b070500c220480708150804260845401c800c1e405603002c007a01598903001c600a0000241c2d00503580c04031035000d441d4680d2a2894010010740d07007404c0e0304a804039003610072050030340081c84040c144c0307404102850400d410503043c01003c1c1920b040c0c4413000401e01c902240c0e29105407140001a1042d655800c1d960784550400d1814244602106207502d100f0808014980000f04849207540e5030140d6103010440c04140120060075104103804d61501641e005e6031031300003440c0c0c01042102c0064501c07880b0103581e2032940324401d5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 942128830 1250 942127580 942127583
    0x815071103030a0e1903321902070909060b120105060306010b0903011515080c031005010c080712030603020906120a0221061f0f1401080c0f0c0c0901090504 69
    0x900078000b2804503601030b08078400044448048170210f00050100002d505006041503010034005420007504508482203000322600310715041000030060080c0310154450040800010348025140c8460b5074404d00100c0002c0c80301c41405d00c86514517060850062a007015110310030142070700e4141504d42d0602643e44903900081c003a0072203a2a18940b40b4207a880360300c100303905558a001d1107202c598002d01c148042e01510400810101004001402e04103010b441c01c2a9151b0131700403c010705804d560319000ba80c10a2900040148451034483c849000350280100000f00b80b4410450150345540160216402101e0915454550000340301070a001084052410b0b002100340030b002d802c0450341843c080010340b011140100380710005c1818039100342c0d510341104450b030000c1100d03500c076000c3c1c07040504019090009050700e0003411104000054510701e051102000c002801400e00201381c81c0050f50f507076a82a62508a0000941c40f03003010a04c283c07180240078000302d0400204c1c4903051095 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 942130080 1250 942128830 942128833
    0xa0c1115060a0b07080c0d0201050907120501110a1107050103050c070f080d02030903030a06140604060c14250e0c0f13030501140a1b0822080408150711 67
    0x1004062100c55208000304180e4205a00180004443d001d00006025981c001c05030140c0342c1c100581d1141c10400c054031190116070420060180071100411140211003040140701c0580259140080c0500300400d00010312170008a18031007110b4001c404002025210003d5410042e1134000550498100b581c1a0f0040c904c180302c1c1c017000074100d142294080b400b40c0251400c2c8104080b075441a6402114a8040c5800120500192981c0c2d8003c05002d0842150620054640c070008503074140220b1040100700140c484480c8140304c0d400900300c110703200000640c0c1c1e41a11204a0044600740c0581c3c044a40c882000300107001e2030b035500c1117405803000d04602841c004580b00040000d812211108410180d10070340040001c1c0c003480754000304560441082e0046c80d1900c0c0d46001c032102c0301e40c1c01980d00c40c0f0705039440d1a0f541c0720f14090340c0405140303c115144401105102214202c41500420701c0304001004074100c45c0005a0300d0001010f40310480913640c422074212104085011b84603c3e5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 942131330 1250 942130080 942130093
    0x18140d0908060c07110307030804030b01080318150d2a05120a020c0f100615020a0203061801090c080106080c0123090d08031608061009121406040302060a0c11 70
    0x1c0d4500b101c003c00b461801504103030320689090f00020f04091f4107500c2103811040c000f40400400010702d440500510608000c4e50601484400c0e40b041442d1180005201e0b919401d0050324602c201d0041c0e48a010451a0070040382144818000c100040e10b40030321812154800110707480d031700c15422a14010012204282540c0717903c1d21140103900255620211401000f1101058034820441118038480b5120085580b5280003e980600c2a8514440003107410801e2a040561130001c0c20b1600200c0720503d03448400c48408040e401408401c800810038084480001503002301508144169141c1d40162078000040300d0040da1074504144559103908400e001d4425401300510242000f0600586036659603040d65540c400a58411030b150f50320b84500702d03080d0405a600101c240e80c452825901b0043c080450440500440010320940d02d5080d404807600c003c001c0c8a65a280e807d400d200c2c11603003a801c241c07501940703903030080b00e00f204003518180c9610302da40d100d122603104640d64900600b62 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 942132580 1250 942131330 942131341
    0x9060a050d080c03190513090203091504020a150512060f0a0e0403053109111b0c100f1704080a12061814060d1205030a18140d090806 59
    0x615000f80c40d000c01c09000910040c10400d0340c1e0070b48083c1d400004c3d940d0a945520625000400340704540204111740e106104201d00460005801252812140340035415551b41c0d1000441c1c5064039081440c0c1c0202c1c28015804180d008809460521044245003103607507100b00c180000315004c5401503901ca03c42da00e0401c415440400200e40060083c03501c54584080b901201100301140002c25518406001c00d50810650800e00000034000c400c0c1c1c2030044540c0c2d50306650050251342c98850042c44c0160340090624410031400c031300102c010f000900035403007046001d440c83c02102c10400c0401c0040e01044090075000000f648520390004401e0305040892030219018042030708654000c9035505e001140f10b0b40180e01400c01406d0384100480c250300c3c0d5205c0241090005041580204070108820300000c1c491084130120711010304d041e580b6551500d04c8000a0440c01e05104803c803110b11a1809000c0c0b00400c180d06012564200c8010342126034003180cdd0011136100d1003800f900003802044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 942133830 1250 942132580 942132593
    0x11d010c02210c011a030114060307090e0a06050a020c070b0c0d0e120a05030c07050103151e120f0201170708011517240a15050f0d050a050609060a050d 67
    0x40480b442540707401c20f001a5041c03421640448a5100e00410300c6907030101c11328090040e03c1081c403400d2890400390811001003035444c0114041c0c80c060544030742804900c44400c111803c0c20305c2e00f00b5024085401c148030054025805100c1c5500c00b801100300114450f400003084070070440640f401071090b41135801003140c1122045003541e600460800002e04240d0003005501d0245002d80081c540d40c4011382d0710300c2d00e840c506a020a05140c1082d40161003090f620a0000c109c42d1840100c503400b0060103182c803920360007908403003402c09040814a0a0019000007645154401c1e21a407180031030600400016074030444044000a658070300500c074491905c01701071201300e9541401303140d407d5100e8088a00c0c075400c0780c1070341035580b810f070390030380807100318800c10710b9101045d40c82e030890909212400040401600d543c4003885000640714441021000c2100e40740c43e1414001c011382c0c2440d85100018040903a8503a00c07071440030010492518208940d41c007191300c018080c00b1160a95611130 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 942135080 1250 942133830 942133873
    0x603120a02150604111207020f070302010c060c18060504290306040e0304120605090c060307080705180d0809010315140f030115030507083003090106080f011d010c02 73
    0x1d1304151074520100c0340c0204900604101d12038404aa00c841c0360195009240618004c980307280e40e44840d00c10030250760011052211503030400700200c1c1901d60b03c43c003601c15020000040e00044800e910000d0005c1c0d002c400752042c1c03161b0305000c0d0b00e0420b0200c003219a200f18000c0c01281d001040000c9050307803800c0c2d801300051032075401c10b613414a42e42d01000104540d115405071040d0b61500200702030000244090700c00400f0458043e42107090a40e001003510304010000014881e00145008640410019a40c50060000c0180c02000d580f450140303803903046540040d0110341000341a064103c0003840000c1600e01e8a200e803403000d0032010801145140383d0100b6a0155030322081030400d022040f0305240950300501c001c111191401d040703585060307040d0f51200d01400c0489024078080001292825080303481e607003001d0700c03510749244041c01407a1030b84c040f802d0ba01c01c203c0480800e0b2019004030364000c28812441a510241a14071400c5e607022041a03401a00f184600d030744419000404d9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 942136330 1250 942135080 942135091
    0xb1e090d080a02090f03101e1b0f0e090a02041e0308160305070b040615060e0d0b0415050901060603150515031b04030b150117060120070b030603120a0215 68
    0x8004500c2e840086801d0030307909003151354a40d44030411162380f02031141c18110030b11882e100c108135141d00c50103109008041c9941e00d50030080c08000c10036081d44150080c082d14140180005094103021441100030740c4075100c1e800039619504411390351180098400802ca9400805041c0303085003665403c1d4540706600c10480c203102c414407468011901d11101c50744030754400c14000403416840701880c0e0a80903a90711040800030300f1510100d40340c80d04040c80f6807c503401403c000082c0c8172464200300c0d1204120400604900d404108021400150004411604261402c001d11417601d0b407600030f851040c0c05a04e411060810710031181086100c02103030301202c03d40090790050f82d00d4092070a035920523071040d100c003c508000e02c601210342001101081d0300901f0300c082803054002020520361402440d50381441621600401c20a1148410001e1f144442003070300d548a0702c8114a402c4c039041614054028402e0016058101400c00102c5071200807640080546000d145289910a00000c21 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 942137580 1250 942136330 942136339
    0x8010303051b0303040503040501020c0d0f08130e040c091808031b0c0706030203070f0504080c0907020f0106031b05191e17061b0301050a0b030c070b1e090d080a0209 73
    0x140c010300c402d01840954044c42c82400959a964030b0800024039101580d01840c3c461040d1340000c1c000200e89040038010b03164803142c200d448850000600c03c2c00e034010b901556560301c1040410081050314800c0301e081e1803814408102c001a4411081c4c0203000b041402020b07844100302254528808500d5654a105030003103062810628858550074104194440b501083c0c0201c1480003594010151521180b42880d120382003918142d1399580d5610601102402200404085640710f8420300400460900500080c4002562490128103c140403030740031440c5801002e020401d443c0c9554000302c0b0340036020300c4440082c10903084070340005950442400c0e40000e8070000444d030142440d00b0004450010203030170306241c95040b4603881d0758070410003400990104018041991400080070586500aa0752038490f80c4494001c00b20b03214900015000c0f480407400c020324244c2d04c10010072200e809140e4408142c503903440242d603031049200071074041402c040c00211009044d42c058404a0790080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 942138830 1250 942137580 942137617
    0x1b030601200a1b091a01050d150506030907080106140102060136050f0a09120c03110102070506011a03010e0402150d1406030c0d17030402030715050d0c0f0801030305 73
    0x3a20400045081180c0180e50036030f0500402000e00148140410000c91114a4203942c4003400000d15a1051600d90081c440c1d40d0f05000c8141c40241c50504042c003005844141e890508000c556a16030440c0b190100d50340c2040c3d00400c8080030340348190700c491010303001803407940d00345140a0f041400408400ca0703191000040480301080c1f0aa0703000b00c1480c032000010305410211041d440304000181400d041500309404880051810220b0030416445882d00385040c038100d04d400c4030903883c02910000258008110328090182c0403031568100c4440c0020440074044280c4030043c640024400e101d600424280040d0140c2001d203080c1c010700084055082c0b130070710494401000c0700c4124141c82d401c200d2100030030500e41020440300344483c000310303110100c110241d0340c3c140d46000c2c00c000d110003601c8044082030440d24100440c0c0080c1c4240c60030514012040e140003405a000803c1c0c6a122908140b03068581902450101c40c44807601d5440c02c119a0954600b91400d5002620108180e2802c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 942140080 1250 942138830 942138833
    0x90e0a08030f010e0c03061311070f15060e0405030414040b06030915060114031f0506030708040b0a1a01080c0c0a1104051005130c030b06030403081b030601200a 71
    0x180d000307510441200b2035610b9103504094070110f5100004050b61070745441001480341750350f2207410004441140a001240c0401c1144084021740a00c00c0001d03d400540d042a10401035400c070810180c0d0b0700c0d0401080215079903800c20592400c103030f0b005405d0303800030007082c03200729090600c4c000b541a000d00089a14090741010030810343c42140e80f4580c503000345102440c081c06100c40c2c0e07a001002480c00783c0c001c41000404041912000e8920300424000d40b111000c0c170b03c0c00c40c071f5240c02000b004100f903480c1c0c81c020350007a02d070344001c03101121051850400200782c0151840b13100e401006080c1c0013500741c90008019103412030003400e500030107041800300610054040104140b042e2050300c48146091000d0f040c80306451004c0c00c202d20b0401e44000c14410307500c90407810810b000d10348501040200014800340d0003040c03140701c21768110364008100010326800500c02ca0040300180048103420803066420b210600050344c410780082c040038125000080d54071074104141007004199209030915 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 942141330 1250 942140080 942140093
    0x501170d0c110f1309030e0102010213050f0a0909080a0f020d0504090203040c081b030c04231323150106050306010e1f020d08070305060f060d0b04050403110c010216090e0a 76
    0xc0c031322040001d0740b54040e4008041d4001a00314004601380029410105e5010a070310034180d0030300849016600050f10b400d010b50310598140d00400b020390007001010041e041418187e4000103c184c0491113a8200794481840043c12181d030540c00d540c2c031070416042c1518000a944007820640e8501c0e0344103008165a9014040d06120f08074030f032010615801600107050a1600c0e40b514107108519140d00f403241c00035000c82c100303000b00d40346040505030b0b55a007101d4108484400c0010b00f44000c180a04524143c1e02030040e01665204c0b01120a288038001c240403031854240521000580244041201940100b484c40240c000050480080d01140c1c203900328103990307003020080180e004240364805290081c007255003005003460705210030f203421800f04d980d92061400050064400203802202c40300e003540680007039900104203116604042c00c0040500039240d4885446000b0008001490340c00010b0002034005600e10316030101c2d10b000e003203030020300e01d403a034014450013200c5014000402 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 942142580 1250 942141330 942141349
    0xb060702120106061205063010050709090903020c0603100b0319060510140325020705090108160b0906090604060c0506061203070605280501170d0c110f 67
    0x10448000580c452130325600800105121302c0c80e0110390b1038101406401d440e4135088002e13504401c0300040b01e401000206441c4c1c882c00510032202c074010910314090604003900200c2c06a20280d503520312680e2a10000360490740100030090250348088103101039410042c002d158080000d01c1020a030682e150382d0850f04e584211203000d030484003900f01088000c02481100003400c001d81d0a50000240d08078090017880c400c0300c07900c440240110009590028503102282c80f64211100c685c9103901d05600a5680d480c203001e8203200e0314641001084201c00011240c0b0607968074024500400d20300742e00074016900110040c0d8003e882085900d61a48454008000400396962408140f0780c0da810802d080030380c0544818801c59241c6042d259082e000010b5030022030300140006844e849458030000786c150f440a01c08910034004041811601c0f540d84a03c0c100d40d42007501125890717181034020380b01c40d4440c4a920100705000c0016001c209010702d0f49114281c003801d0350307201041c6100050101030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 942143830 1250 942142580 942142609
    0x1605070b071803051e01060806010e0a060f0e04060b010219150f060f031e0b041104092405010e01060f0807120203041101020c010206010311060d1e0c02061b0d0b060702 74
    0x14088407411017115504810141c00345982c40c02080014180466503032241410710445044401c803801142d0324440c3c681c00140103000014581911030ba94145182c00000200d0b02640c01c545443e40d0281c03075500108580e0110900780700c10f03840314865a80d460034022003003030f2400525a599100a216110b0610544018000d01da00d000f199524514106203454202d500c1c89405504ca030560b074000410318000c4a0308541e004030058181a100c901143c000c014085000e46250111004504201a9441021a40c4064107000d0203544e0300e40110148804d400c0c800c2c02d00003201c155886800510a040840d00680f003498030207c104020a002c6040e0380050704c041e03410300c000c440a4855036804026106082d0000e001514040d855516425150040c2040150103407600217a011078042042d4484098441d000880303008071005500200c00500700b6041c0f1030050710409000c5040042e074446091000214a151180b030020344480640c060044100d01c250000b405010101c0140c1c1d03181040b030f040c3c9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 942145080 1250 942143830 942143833
    0xe030d021809040632010905330418020f010e030a0f0302150a140105010f03090203030304061a060403080708071e05010f0c0c020f120c060d141605070b07180305 71
    0x200303102011142c4003d52141c0c5c0541c10309580402ca601ca0144100e4036044035500c800003e550755034070710391060030310a0346851f040800020b190848c4c0900b003070340f0391030307283c20242c0342000307511506e805100c2c03245140000a0b500210450416080d58881c0d801016180c1c009400d50713812020640d11840030004111048002d600a030754411702230410002107a5000217415000c0c450310014103107902030a50f060080c1c034100044110300d0051180a50001566580c1c054100c9640307141600305480102515201580c1491140b440d503081071800034140c40a8035003014241d0310b402c425540303a1206911113032040301c4d22486074508181e104040c10b03084130a1402100081240c0418040c4801228a041020410b0084081c1c04001580340c03500d080e4140c81c0f081e188955080c440450b0986840c00406d65a548603a0010b100107944000f500b000e10000d408610300d8100341c0b2010044015052361a40c1c10000900612408001c140b5405c54a038029089041003019052158078080b000a0f80d60401e0382d85 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 942146330 1250 942145080 942145091
    0x30306180212061813020a170c040605030f1e1603120207090626120307090f0503030304020934020304050306100e190605030d080103030f030e030d0218090406 70
    0x6900c1d005441507118108503021100109540c142121244c409400c454081c22924924011510380d20a00405407241b8001810040c004c6150361741d40741c0c0083c0c81140140c0c10060b00098505000035008a6010080041c0c501d800341d04084060b810311080f03d44503c0c1c811007040b210505440310402002c0c60003040c4081d0391a000d120040c0c078200361a8001c2070711034a0703e0002c11007030f10b802031447c0e8203e12049440980e10507040e01b8500d05003250501c1c5d0324602c000000e103c52290032211b100c085500300c95450240c15502c1c030406459000484010b5044091100010340f410780c0c02d01800d21302c40000011111002034101400d4042c121218040c0240e48001018071980c0303400c000da10350000c4c00c0c9002140ca24149144006002d4014044540010780c040312821080001d41008000d800f001e411640221019000184410028070058000c180a103241100c458460300071075400108400c019480d00310300c10341d450f000354041013424002101c403664410b401d5840410281c0150701032a0302041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 942147580 1250 942146330 942146347
    0x70507140a02011209060b1002030a140c0613080d0528050c120601020a1a04060c020d021b13020d0603050706051305190909030305011404060503190303061802 70
    0x80d403589020965049900000d00d260040c3c1c1d2100c0b50803005864100b021a007a42d05141c104082c0c07032011178190740100c1c0d085203590007507400800342c440181c1030303035540925a030600050328040c40b44560048050b00030030000b440c00070480540880f414461581d080c1f401d903d891031b90b81101e4003680c94003040c00c40040c05442c1c0204808580715407814414040103a4104461400e20a01c07440c581d00600600d20400030700c0580c028400c44480a401600c007406400940f603c01036105001c0724215601498081210062480041d6420f929201c0343c008201107002e004608503641c0300700111550089018a80c50f000341080e00252881560400d0045189810351800609105980c0c0000003082401c1c440340040f41018507508048850550701c1d0508a28104054000300449401001911341000c80141c00c066040c0c1c00304c5d04070340088846110111840d020001518a80d1290f030781d050b8441140740300461030307403034003005054401d00300014120350b00c4808500c5d20600303081e02814180c3c04200000b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 942148830 1250 942147580 942147593
    0x90e0c010e0102120d05040c080d05030a180209070c0503090a06030e0d17010b0c0a0602030403020c010207140d150b0d0c030b0a020702060403120c0c08010606090e040b01060c0c05040203070507 85
    0xa074203090020f030042c80c04c03440d1000c9042c050300c44040505a1110045814440700ca4501c4001c1d00c2071000765581400d0404001d4a940d100741e406004141c03520710825880030215440c0ca13901c1c1c0d0f00a11201b06511002000c071001607102c0820f4506000801003080c0b0b95441e141c0401c010b10942e2008a0002c01020b88542485071004c1c1180c00e12048002c0b880c4c0102c20345150506440e00602440d8a9002c640d280034540380c5030507802820188000144000c2c07540003d41d500c60704100341d00b1519503030f844546420301803440007001c1c0d400c4180308141400007603540c0d0003204c2800c0921400074030304840900081d20f4000400d016103680d030110000380140f004204005621100200e002c2d8039140980e070118004d0b204620001e0304403003e40b80b00c2c0035040d100791403009203e40c10105c00340c48a911032031070600803c8035204080120300d5448000407500030040b4100c1c46181c000030106256860030405940c1d6080c1180216410581e05401042c15500c44c0b010354080c400e1075a925444510301d18001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 942150080 1250 942148830 942148847
    0xc050601080102030c030610020304080d120c020c09240d030c0c12020a0303140d06090509010b030105040507121401020c030406030c052b0e060c0904150f0302060304020a090e0c01 79
    0x105202e9004000300402902d1220031640c0104003540c01080c40410040e00720b0460003950007800c0c00d4080c81821307101d80e642c040704c12041040c0c500b804001c1200060340c182d039140c5001c1c551075002a02100000c82c0703884910202e2001d4401809109240410b0f80c0004140c00b41d035002c120045804150f9510600c04c2c040c00e51406020022815064454950006404244507120003002c01c0f515542039828031505805513104098141c2c81031040d50b4540d01d40c040a0001214070340c15561030544c000d01e09140c1402080e024030f410101815015040c41e000700f130341d02c0044c4015107441d1302c04c0c0700ca00341c028024401400012803a101458680c2c0c14040020300341c82c043d141d40703020054207010f02030000d088030a10f26440c014803440600d14454850b050b03070241a0380401d0040341c0c0149410810141d054000500711302404941c100400a0070325803002c003245090142c0d00680500580910040c00c20100460b0081d00003890108556903520174501a50b4450f4402161508018a00703505942c01c003081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 942151330 1250 942150080 942150089
    0x1503050708010803030f10090903020f06090703030504031b0815041b030327050d0b09013606020904022d3402040212041e0209010501031d010c0c050601 67
    0x782015490f02a40039600d00018081c4030141a000020035848416078019000500b9010b0080c00140064100a501c0e07000c100e051400e24000c4900241c20700c10046415802e5030f5040d100c0320f0526003551510f10401700d40f5816950600d07200a00403503040004c102005118822040b040c40ba031406280007006035200d070041c4c083c001d0740d1007000d10010b500310760940001010088911500c40c1e88020380250448160720198004c00b1841c2c1c250240700f902e800e21441000c04000900860403410182c040f24194802001030303010120610445c050842140415820b0040c000542004000c50000e000c0364030084201b00c01c0e141e0005000d002116840d254040001003100d99404d191528092566010038110030740080e2009a441145d040b050300c0440d4107003034010340700315200c0c10b20134205a403006080d030b0240d8050307070300c0c0c84c0969501101003803041d0010b50140000716a80d10b803400540c094211009020004284800b15034460b1201b48203680c1000790b03640d140b407010b58150402d0b40c1052810b800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 942152580 1250 942151330 942151337
    0x141005040201050a1b14030a0207050904030c020909032701120b0a050123070809090a020408030409052503021809060d02210106091a0108040b0a020904020403020a15030507 76
    0xc000140c0e800005072840101c0c5030a0a074038124151000c01c8551a11844c0182a0100540c0080842030008040c1002d40c103250202c90740342c0d803510304101945000f2175004002411030340c20440142454400c035034100c401c0c02c04032406c01100410808100141698980d02258284194900796911854981000e014845c04012504c001c1e40850344840f014062030f41400f10400350082d40300c0d030b00da03100044500060040c5490b281c03180781001c001c2d03103c0307420107100b01040b00c04100c0b120091f00c200c41c100c07401c00300114581740c90841c00102500e00100071280000802c08a0740c05000744602c01c1d40e0001ca42da60060f03903201121085060f81881001039401348580c1410030109480e555013806400d501101d0b010190420340c540b891791003910f6040558117500f00000011500d1a0f40c1000360078085141d1840c04a01448004481d9208105e80c0607207910150300100d46003000690040901c0c040241c4054a400d86035004513075074907e00c0c1d2000440e8582007e8410490749e140c40b070243c0280b070a16 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 942153830 1250 942152580 942152591
    0x91e1b2301053406020d09020102060f240105040803071b090204120602180604031412120703050705040812041a04030309090f0f1a090903041a0708070507031410 71
    0x15069000420701c02d00f06a4142680000040806103411000030345950141d0207565683d94801114040d00d0865000c03230141c4503074008500a04034004840d440f4000e00d00c00742c105145840d03c009200316002c1c24140c140041000080f584500070f00082000a008600241200040c9034508140c00419442025114030501c0705103d1810380351801d004040d0098400350712030101d43d0b0307002c00d03c8000e030741600d1f44044001800000c2164000400c030508900100381c1d40316102900c082c090070f1040280c0c00708d02c2a46c0c0710000c2d507010702070b40c44190803181a03c4c24038100b82c0c591615500d405100108401050f00104040262111202031111982e02021855081a11399034010b00041c03100c0c010007100c6502c0d40041d4607094840c2e4804900c2007040b00d001c0c2301000040b5076103000b20401303c1620740903540c8000003c1c0c44590000848040380c10140410218143d803861f080c1d441d030001203003203032411000c000c0c2e540465003c101c510301a500a00101034046000c1e21050f140040000005080600b001c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 942155080 1250 942153830 942153847
    0x2011a010915030209030c090415050a180b040c03060501060210060f0302150f090603010902030711011a0111151f090606020a020f06073201091e1b230105 68
    0x1c00d5510340802c007504026072078003a0000061f007055a02d406041c1c02c5030001c0108420301c800ca92110000c2c4013410410001500c03060085c4040e541c04400300030301d803600c074071000c0002925110801e6100f8014020100c4603a180d50380e42050381c5080e840580181c0c0310704e5560000341c56520550000b80084031450202d1440c5601040703540c40851030358a510080454030340f94105c6244200c811514000b4a1300d9500c0d03844100000003034000f950000c0000e041c0c1440204244414818290011000f0040f10545808038004554100100c070b202c040e40e00400000041114000b90410701840007400c2c9142c2010241000400c20704140c0d03c00d540309400c3c00801c02c8440c0d000701d800400d0f65010358003000c4561002010074028440c43c200140001c0c07401200750340d422504111942e035031400414001107008603148081c240c962200d40504502200020070b4030310f4901c49400c501c528130a00031120440783c1c00700b030802141d0b4941c0c032202c0f007003d50300b80986d01ca0b8480c40b9501424842420b1242c1000e084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 942156330 1250 942155080 942155099
    0xd172110080309090c1c0603061a0f24130306090b070f080a0203041a090106061115011707030c0f08071a0a1809060b04030c080d0f081b0a02011a0109 66
    0x1508a07a440c030720011b4026000700e400e00703000c1c01c40c6403248403d01c41e06540385008002031000c044885101039003006072208a01d0411000420000018a400c00c01500750070300845906d14104011b0282004121214034080d00640500c0214012200011005900e007440c6402990050800007002403c02d90b650040750001d4480c1d0b0000350500c40161030350b4582c0b401c41020309401e800c28051509000c100000a0b105410400980b402c0c2d44d40d2258003212035904d40d66070410900400d5a5407030300c40041c1b08440700c0384a070110b2040c03000103e07007440e03940e41c50b0060517000b15003180030014428601840b00040801c6240020034000c40d00c02d0840801130f052015a0094402c400c00300826490001c041410b0b107040c2c840a0704a0000400030725954421402080e4403a107c1158520200c0c8000100c401c004600d101030308803580c90307000380c60041d040e00b141e28850081c0060030010760b0030001e1072040c850b113003d005150000e400002d65400864803e010500c00c2071101410010071030814081e07040c0c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 942157580 1250 942156330 942156349
    0xf0d020901090e030d06080d02100b0307030204201b011103041709010309140109050708010b010203070b0a0905101d010b031c0e091f0e0103020d172110080309 70
    0x9000b50001003010030405404d00b98031034942e00407031381400c0c1000421a45e1b800b00c2d940d04030640742d0702207a504841c03001d03c0400350b48201e0f11440e4180c20604d070800150a140e0010254103140141d0002c4840c5415200c3c44a60006100001002d84c0c0c2c3c0300c0c2ca0301043e401d10030745250102e400b8996013145490b40d01d000c104804880c1c04094000041034a14169001e90824600c090b407144c1c401c1030a00700c00003558020708005000346e400e44950701c0001503980041c458600310031410381c051850500c854640c1600b80d0809001d40104a030740b89190004207130301703001090a0402c1d410b0f0110354104941e40c0000342407800c0700c2400307040e490101090301c0f41e90300107950025010039140c00f4002d4029a40251400070700c4c1c2c0e03082900b00240c0d80400c03d080001c042c004003091545400280f00640341d00c0d901c495040d007400025000a50002e10201192081c031721611fa01e00b121900718641000584448008007400c294900100e41d448240b004440c2401c26070340140030001c0085041006d000c0000b100c0300c9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 942158830 1250 942157580 942157589
    0x11070303050f0702030f0123090c040b0102030705010c03020307120e0601350a03030c11031c0207231c080a0507020f0f0303010602100920010203160605060f0d020901 73
    0x1500b05810320040064641441d002016100812884043d41d4040c1c100c140142038400d81c041085403002807110b01550003200c0000040c814a4820700601005003140650681503200070f200240018100b40a0703540040c0241c3c1e00581c0720300f0302e240c020b81681c0e00d862880c1026801c1c4440500b0041d00061900c0c115056403059456544459250340d0114007908043c1809580c0f103178401a00c0f03600020b030401424441d0b64100406d001111080352408000001080540c00c10881c150064010b80c07031124241b828108018070f009255a240014014800e40c050840d41c1e001d40e001d000b0138000e00004012907082d03c82d440e9140d0180c04020801600104000d0351141e0350004251030b103208020403000b481d00041202c3d83d040c0702168150b83c0ea0424810400188120402c800b110100381c05203040d1198003e807204141e040070303288030644401400c600d604500c42444019402d0803001c5c070300400c960088200251a0814070305020704e9890800789503010b4102083d407c1e0058031055201c07811035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 942160080 1250 942158830 942158837
    0x150b0a03060f05010309020d0b150402070317070c0c06081b0307020f0f03090d0201080c09040c02030d06081209040e1f020c120307052709101707061d040e010e060601080711070303 79
    0x4ad522131498003580f1404044d50707500715102040c25010503811810b2007100340d510032400741c0296601882110f1450741c0f036000901d00301d8040410040a401100c607250860307511207244040058041d844140d0b80c0088a2020060340800380b684428841401101031100f0104051490010300b140071480c110342d8001300030304002c0a0000a4015000701082c0c410f0100d00901c2840202c3d40240000e64036048900402070762464410001070040001441c1204052075040040c18164000100002410100e541003030fa03010f4001301800b2003070090b04c018060b0000400058a030b10442c1200ca1601c0b6114400c01990b800c10414082000d40040503900803040d0340300c0622100d00085042001140780101d419001010340c024003040340c04540c0c6103000d9588104e5a14050419540d00580e110aa0311503070002c5821031800390592803518050920103240604042a885425007500307003168201c0529241c070703800c88024481103603403121030241c0105162520690b8040503201d00d54a4110500c401002d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 942161330 1250 942160080 942160103
    0xc160512072603130b04030308011401020703020f04091a090d0809031818100e09011e0e01060503060420090c040b03040606050924010c03020c04150b0a03060f05010309020d 76
    0x2000d10403c100d5580b80079602c0c2d864040c603038485411036180c2190200301d000c26544400414890b40c3d090f00340c012a02d0590050a182d131454081c0110b500c00e100c0c1241c2c0164803807400e800811440d601001e40d59642d044440f42d42d242c9641064201511842d181080104441c24481c2046000040c0c8804210004c01c2c0c502118803000080c82031642a000c42008200f544108a1640800c5c40c2d14400c4501c5070020070103e65031010345a007240e01a280d1150383c200000395400c40d0b040954070402c901ea808000000d01c4540345d2001900d091412a022104554103002c0034140e090202961246a042a07410751107a003894522813601d80503e0280c21007149011000505008032038120b00c000b03040180c0302c09420304180e0003030f10200c034030400c3d42d100710f072042008480345501c20312104107855010303809002400036080400000c0d007134070083c4c5100b03100e0640340030500c03201c0080141212900c1da200024540d203410320043d000e6105038082410f1611b00404d0b00050b8644299108055a0208a1050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 942162580 1250 942161330 942161399
    0x603030403031e0207080601080616080601050a081b0f0d0b04090201051e0d0e0312010f0b07110a05150d0501120309032604060e040b040603120c080c16051207 70
    0x3401081b90f002500038418071000182030b6a0105200d8000d500000038440030302107070002a9440002a90b415001440400100c40040d04c51601d15030045901c6652141c46050941c518a4540103e207195801413000505220600b1081c49850313102c540542c1e0502c1000200d0b000a001802000c8900e08904812001c02c040381404008444081550f210108001c00c40d1042c1165650013080307000b925811020000b00300c0c0c00070010542c0c00c846075030905900d843c14503038860600b0b486440340ea6800900108000c50b40350341da645001e07440500b6003020ba403500401c2000c81c0580f10180c0c060f00340e003e8210081c10200394442c00d5841640d403c0701c0b1801311a02070005002000f001100c180c9684140070030b0200d40b241c2e10807103100e402c01048805001d0fa0b00c54a08220854100d0700c0700510490164848040041c0504c0d907283d00e650180030558107000d0304030b04032420100e1420340c82c4030f80030a00805206c5441c01c40b01103204942005c00400140d81042950640802c81e13081a00c0d2035804042c40344e1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 942163830 1250 942162580 942162583
    0x140a0902060a112103061320090102010f050f04050706090303080f0601020a0f12020f06010f1401092d08030705100e160f0e090a05031c06030f030906080603030403031e02 75
    0x5034800a0b4040b541c042c0f0b200c0000044d03508140c1d04144a024540c07040701000c460383c06403018500000c29440312000481d042c0d030486900803101c0c141903540f104504009051507104061252004a030703240301c145040d2070443d051001c190815070030b2084150050000c00e9000c1d60660b886045501840129200e500c010707403074402c00e03d00040c00054011001c00822155001601c030540c085d400700c803032035409840000d40703440e42401649450301c0780e00c00c10000d00039422017400311003030103060880300b9a468038504520340c0c04031a03480ba0758040401041040052282c0311400420441c0c02450a003a4039070b5500b034903055110b5400724210340b039108180503040203010200d035178010300c1d81a402d121760703464403900d0030051803140041ca00c144200103081140046500440d86070712001075450603a4411481035070f84040700481003017640c0c600c004800a015402c00304a40d07400b88c1c4072182e10500d03003980240280300091406019410034442040080d0300082c490f011050b22010320042c0d11000e81d4100d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 942165080 1250 942163830 942163843
    0x3050f0f0d0504050d02010e19080a031107061a010903080d1a100804050708060708160203161a0c040f1a07052a01020303011d15030709140a0902060a11 67
    0x4a95107442c10b42031104100d0001131001e96a400c9030001c0c4a031004910010340c50390320010541685041c000555000501c2100013010301e94003e00b40065070040d849241c801b6a00302d01300807600d040ea68500701a4111078041e1041500409183c03039070740541036556010f00382c05195242c0368010389910310404003514250204030203280141005d0700452140c00d0040121101342c1b416a0320780602c0e003020801c2107000ca41117111b030106498101d120b88440b900c600341d000344409468110b01060005030f110301d45805001641c43c0c05050440b01e00540038449002040e4050250390303818a040208001d91880d070302c100d10440d044d404403000303100d24854804050380302c2c90100820500480840c1c103c0c8030450565100a0400542c000c0500b007801c80c01aa038038031080c01003050034448040d0f0440c0c20141040780c0e9900c00c0107091020000c0900720086840c0c0b0b00190485030303610303032142001c19842000e818000d0340150700c1c503414404200d140c1c01052140c0710300440201040418400480c40c40e5040108 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 942166330 1250 942165080 942165097
    0x30406050f0d061518090b01080606030901061d010303020607020606030705042d050f070e031005061333030b0f040c0b040608070e040b0a0521060a0510080a03050f0f 73
    0x12800d01041d010000703001e04c000d51860040810090001b045030fa00340e102d810700344001078441d900703152075000030401650002020480d0664950402141e09000005016010540c14800b075a9035411403401034142007000b40201c0031903106d40c0c01c00007070303507000280366040312825900007a40700d0018170401c034a000c40009000125005402410f0030440c5035100f9845050001c01000180d02d48402c11910314090219003a4150700040d07620310030001c0b541c4010303000314008201207911100f045403001640c4c2c07505c0341c0040d511100c80e40484006042004025070b41c510014840055003140c3e129110900c1c094211906c00ba5910002410028a0401c54000d01010720a085d1240e544e003000034040c50040f19002c0c001060580c903203000e41843d020702503045000030034000c074032410f0506002c0200003600e48001301020041519000840610000d0300800e80e4440c08641c078981090b042d071086000b540034119550010f0380e048082a80142500c620100840c0200d07034641100700e80e00b00c18040c0c4800c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 942167580 1250 942166330 942166349
    0x12190818090907060f020d12050a24141507080c030903151b04150e010509040207050c0f0a0f0605160204140703141605090d0f03020717030406050f0d06 67
    0x7404000800055075034110754131552641c08080141000301d8441e045145034001081d241c4110404c1c40303000782c0080f80d00c41004031000503480190b000040d00d40c03100d05103c1c8810400814148100c0b2050115500c403100305440001031035014401400e0300b44545d51015042d0a008030b14820303118410b00880f200c20000070110342c443d104103401030260680c04c0c0c0c0c115109481d003446001005140300f05070303801c4407007401c0070642c01a0050f10a0700c000c41c0782d00c5614100581004500c440b0b07038951001d030080741c2c083d20041017001e1680041c00b003242840040c161040c400801e0800c01d00c3c0f808620716056850034500f0507100c0c82c03061940340d5181805400250310034103000100041e43e00035991184640e019950612507000f5542209100f08002d0700c0046520030300b4400800050700a1000306009000a42049042c0c00c207511403e1510701001d40c02ca0040c1c11028080200c040f4203070303940d018020320102a501e03007440c02c90301038103d201781c01001c2e000348404180da0b800c8440e503900000041c0100035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 942168830 1250 942167580 942167599
    0x150e0609070f0501140d05130b1503070b19180801050a050601080a0b090a09080c01060b0703120c080609040f05100b04061d1b1303050c12190818 64
    0x8005034890207280240031001505a4000500758440d103040c03030010480b4003070a46006200349081e006884000e18001514500c5145007000400f042c04d581e00c260f02030442c0404401c01c0c0010582001c10310b6000c86a40901840404640d41c000521218400c040b03040a1080c0898642c841c0051005648419007951a2500704041c0d04415041a84581000d0b61801e180d6642e500030f034403c440c150098543c12280020010740340c400c0c682c0c4840301c3d8501941449040403c92440345094420603040b400507032102160b01c1d001c00da040f05c500c00c4001d0301820144035035850a000140301400091805129803004008101071000761144485a960840181d50000c0749000303102002e80360002e49140035506d44180000c288001c0103040708002c103034003000501a06c540010b1078907485100b141d18071051041014400d1801c1c82c4004400071807244c806449810401402c0140b180720348280c4882d140c00c10401a11118510384001311210750289419032501803030750b80c0085c81c0d40b41d030401d0f81d000500318 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 942170080 1250 942168830 942168841
    0x405090709090c090e0312041b050607080a02060c1e03061c0b160327081207230f0a0f031d070e01060e01020d05090415030b0609150d150e06 62
    0xd80d0b154050b980030302814000280c12030305c00340d036910880b1411644201e8001c04a0b00161405516100001e10020000c0700643c6a50000f0310031760044004035802580000c4164000340c0500819500441c9507042c2c1382851030708190229440d0b601c845080e0700744c10010024080342d85051134410b550341c41c1811403118501a190550b400201a900c030403048036041d40410b43c4920034000c81d509a0364800e40142401d00086010204000550080300c00250500c40741902c003e003443d0441c07003000c1695410120b9203203420412586951030360b4240300d44004100c01850140d0304011540b500708546443c60f5070104e0203c04800400c610900e240c030b01141e40110f40000200021480181d40340f455500e01c0326643c506050b240c1f901844070701405600100781004ca0580520b000c0c01859002038400301c0c10880c0350208040420706600122602ca81440900c417480c140001c520380d12600701c9411058855048002625095100000810000741c00c0e4120921030b885401008242c001c10f403c072051420311 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 942171330 1250 942170080 942170093
    0x40f090c030608280203030c030a08180c0a0501080a060b19030b04090f0b101e06110609100e2b11060c04090504210207050301110414040509070909 65
    0x80c419600c002030300300b0b0000301e840c45010503001001d0305101c07030803504d58a0316004000c4d1044000d800ba03078140014484c01600070020700080200000b195103202151800c8041803000708800b148092003a481150021425210f240218058540c00d09107008140d842d0081e84010700407980080c0d51200d00410441451000c101c8510401020b685040c00380504507800d000469150707081c068680c511507070702caa02007100d602d4103642143e0700f440d00001042d16800303910a4034001c8501b12600f981400410081c0c91340c408440240b030202480a0030f051300300003040039070f1580c400000f000d0040ea15007070204d081101700091000711007041c080b03503030080e03143e00c1c050b102e8482140c40f400403503c01100ea01c1c800740b020070200e105811203200395007060308106917075000704401071007255102409a08071901c400d00c0001d555540103aa4018064141040d09150948000d214541034424041c0014841054640703206240010262800203c690301d08021b68603020456000c0340300c1c82c1c03403d510b46e41481031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 942172580 1250 942171330 942171341
    0x1050406052d0a1b080403020d02010512010e190203040c0e0a0b1e090108030412200d050c0109170c100507080f0d1104080607080a0e0313090c022d03040f09 69
    0x4a44403112103d0307441e01c0304641d002e420313840248142c034200000c1c00180740443c00450350a00624100e82000300c01d92610310b40120030381080c00c00740c03245410003c43c242008c481800c4e1402601c015070860a280d62648060400e138041c00100303015180002d034069001c2d50102444010003070031102003c800c080c004080e04020117003580104000c40001c41c22400c00000c5804540041038000642c904a0b12146249603060007515410684c0040248440e41c52507120207441e406100900704031003100c40050010101940704004601c0b030781c511007041d0340700458070b02c02410301561000d109080000f4112403621540310020481c4c280401c01d80c40c0c001d545c50181c0a0309600c04010410b80c0319011949100340642e228900d0f06510520006445512800c0c0d09a040b035038611000c07e0852004011034107540015503440d501800c622001c100c200031383c0c01303030203489132550000c1c00052070031902040c4000c5080c00148400c40a03840c1190b4030520030401c550060001800c00308185d62980c8000c006001e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 942173830 1250 942172580 942172597
    0x201140d05090d03090c0b070309150509030d08060a0e190203090a11030114060f1813030207051503070804030e060a030921120b03070902131a0901050406052d 70
    0xc10303180103c1d440d9029216082c400e07500000b064001c81d140204441c420350000c0c07811801c100541100094000321a100c4190004480d191240c42e00212010300d07141031a02c0000c43c007004504000d110680e01c1e0190080d00342e98021032200010351324032441c030006448082d030a985407440007041102603a0b000c103250259030321500b120300c0088401000c15007610b61032404003400e1400b2402040a910b0202c808410b14200074040e000c6048042d0940d00100004580c0d4200003012040305008043d41400300d80040d110454120f1224119241180f1540c0402810481848204000300702814040e0915600c2000001c0c00b0543da1011000001c001e4803102d17804484108410705820030a0101034054280d40616035114611840070b0624640940101501950103026100001c500e00a1500042a07010402c100c0480b0051800c10a00d8481a0180040408502c00d120441042e0382c4201100d084503e0703441c156480d034010624440380c6840115200a141c04603030000c0039202100400341808070f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 942175080 1250 942173830 942173833
    0x3071b020607230304140108070e1e0f04060b040308091219120809062403010222051e010e1c030206040b060f03152e0812070803040b040201140d0509 66
    0x204070183c1a2542c0e4001c0f80940100c07210401d184903140c0d4403415903541c0c8404540741110750030090342e01103038502c650030600400c604044542d04d449400c01444100c2081c00a4800300320152600349450154011800000c207007000025006c6100d0b9a040035450b1410fa0280584801c0381e002004143c503c10194000c581c82c0143c5044024618041d4402911480e01c040c003500c40341d0380d590f001484401c100752102451010a2141d8184c0c0d880900c0905250004c05068074a20103000050702444800341c3e1156108401880000e224101710403000c100d400421308110381b21140e0b03640001e0324000e074002d503100001c0c4001a11401c1c10340c0014120f019600622040c030058568409100d203484400300201e801d58814412103484181d045809079200324100c6420580c52080e0500d1510b003042c681da10024410310035001c0c0580348003400000c1400b1101c18180b85403504a03954900940802003010b050141d410000400b5a4010500c51049004101c0010340d00c3d540b05058030b0081000b620020010b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 942176330 1250 942175080 942175133
    0x30c030909070e100e030709110d0608060613110702150d060806071b0501200406030b0405010e061009083406050f0a02010609060b040e0f040803071b020607 69
    0x1402005044400d43c0003408140510041070810b0b40d050400491081d00b5201d8840009a900118464a119507012811541c0d42e04108801441503c02c2c1b0341000c0b000c4c0c1c11042c1401816030343c0701400d00c82e41e001c80720040760094220300458501c2c05204000303908040313406410000c0090f16001040549981e0900300607054035070800c256101c00840301c400106400c4c2084110070200b044588010034814000461620166082840842c03074030f29882490703400100301805981e4040c01076442800701614200000d6142241c0420700a030050000c41c010141740c004000c3c031610811181d400303010000100c5192051071642c1d100d0b01c0c2d041c0c030003180032084c1d1306008403514071141d041344086542c95a141402e140c139912801e80d080d8070040a1206541d0b03074804c0058400c03001d0150200600021003499112480d00303000700e501d00300c010807071070051301610200000105007106907500043c43d807600c050b0701e000b2104802c00101c2000006540030502080040812000345541c800820f00a03140209 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 942177580 1250 942176330 942176341
    0x90406090506011b1e080d0c0804050f120d0209060d09081e03090a020108130b09011e09050d030e011e0203090c011805010c0305040314011a0a030308150f03030c030909 74
    0x18040c2c1d0054000300b5041040c030f071030f04017002002100d070386003409101c0c40b624110018200608640340c82d207000d40440ca2040421080c03200901c02c4090100802000e40760300e040701c0754450000d200d40d10b021003020341d000c1401308031900c605081c1e80415032610010040b00400341170600b0190001c941940b042508240500083d580319410f0764010f440080c020000080e0030b03401561302e02d000402c00340110f55040341d80004079500200e91802511542c0c00020722500c0188076450380d80c40c01c010b18220340e041421500004030006201d1000ca20186000201c030070185001a01404e0001c083c1d100b034038201015200c0445269002354040e43c001c104940c031941141c001998001005002200c0c9600380490800c942c0d40a580303091a030328481e140c402d24050300d84e50342031515410211260b503280c1d903440840500703034284040441510422212103c94a15564002b0203040f40103050a80550400d4605000b0b40c841468100e028403000b0141e940740c004a10059035290071814600c1e100d0890580400e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 942178830 1250 942177580 942177617
    0xb070914030c030c04200a1107060c08120a0204080313052404030f020d0b09010e301b070b03100b040308092107081b0612010e04030509040609050601 66
    0x4006480c080c000e4035141e42d0313400801008202800e00c4824032441080340c0d90740c8115000091031010b03034544130358180102c0c001d40f83e49001c0c1d46401a0052198400f40c00d00410405425070700c00d03800e5684c409106540d00f2614402a01455201c03010522010602c814103040d43ca48100035648191100751fa89604010141c0b401b6006c940c03021005d0104010600104040e104000c4a02d80050842d40090420750b580e1040b960301284c0591190f55550510400e248003403154541030980308030504502401c40504c03021802c0046084144000005541e002013054150700780c5203002c0400942d0304896644035071800311f0340111400f40c160000d0040c086640307109403058505070f98004205500340301500c1c040c002110203901c0d8055081005001c62161803408124031009044a040900f10b21462104103054079062211014407442061040c84401110340a00a0441d81845035190550719503040503a542d00c9003036402608107040c1000030501103141d40085004007400c0c0c1e07078601300400c1030344080b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 942180080 1250 942178830 942178843
    0xa120f1e021518100224010e0a050f0606130503060717071107031509060e0715021c03050c040f06051803030c210c0604060902120604030f05160b07091403 68
    0x18040301d010016410b441c0c01c01c1369a40d507101c80640111421000c000d10400710078100420248410700343c0f10014004100d50001c5240c104040000900c80c500303140c900c130703001c21030004d04185c00b076080440c51410341c100380050140107201c040e0036103039503060000000308204500c4006c648910400408249a03034416110705900781040301c0035006240c1580d5444152031031100c00040c1803034135030031321101080d000e00c00c0c0c81d03003001d41100a000715840c050b00e4004000040083c80250340002550070f1a40d01d00c0d10440c4815a801d14000602c1d036a001c840d09058001c07078100310001c0303140301d101207250341d0890010001c071603c840c2d182507038207d418201951386c80348058a140301c0d004901513090440440310b40d4101c85240140442c1004140070f0740e00d02c0e00313104441c2902d000740c0b607500382c0066040800c40c1200c520800d0b000b40520b0700d480c1e2400741c811079103d1303560b90030000005a000c041d2180c00712862100c0d41d100c000304045007000500240500d841740100300c582d41a82190000d50314000658 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 942181330 1250 942180080 942180097
    0x3070e0403030218100903030207120f0b04140307050d02060c21060121021c020702100503060f090406050708060105040f180f060f0f080c0a120f1e0215 67
    0x22801955560341e0100d019412001155004018130001401650350745003c059040140d995013440e80c0b851800e000b40b400754a54014544900804140b20110340c032811800d0046404c42d42c252b0a5450b2480e062a044d4800d000c803522901002c107211042110100711112419010b07401c0783c00503100c0b0010601640300341001c2c1d140001c40300e0502c80004503c2500264801c030141032440402402c16024103c3c1544409c0b0b00c081c20f0750000e511590104041540080060817040841c200b449507400b00780072400203403c24080c884c0110010748160740f420010b04003008064468101c6003441d2404902511080d07030008007003407c81c0009242c5510910683e0100c8100700303c03441c0700c18034201c211442c1b03035440f8510384a05616051440501412070007110010002001d022a40900e451000b034010070032600407621581000b01c010000740c1d103480c0c8020a6480f043e5005654218900e81201a035240483c004c003408810550031814900e050b02000c3c2c003900988806001c558440d240c115580b140040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 942182580 1250 942181330 942181349
    0xe0114010e0904140a0b0106030606030e030903030a120b2101050604050609070c150203071e0905131a180702010f02030906040b0601170c03220c0b0c100608100b0307 73
    0x8021400490103103001588031002d6400340222a00d1b9a10400c0c8240c0121022039143e010410100d03506100318100c5881c1d49e4083c60820b050140001d40300d22a14641c0403c0000c00001d494000c1d60741c2d40030310400000203240d24040358030103090800010b84810641043c1d4a008002a0a810b003402818401c000051190403950785200c41a00c0410b04160305541c5011010504000a51f29100450103000c180c0c45da0503894124401c600000064040c0790300401040000400040d01c8888040403260040b0001144054154030081110100341c03002c50384c44800b103403629100101303141045018154a50091108918620718402a1f22050725111641c0d40541c001070301281c1107002ca26003101c0e05150815502650240d40c034004401a5829141c580c0008140141007141c0009140c40c1061581c03c40f02a1820b61036070308503102c50340719045010100181c1c102c5010400d10000c1d8031844503640c02c016464403005050358802000c1c1100c40314a2814813200181c0c90700141d8031088032070409 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 942183830 1250 942182580 942182599
    0x2412020f1806040c17041505180a03050a0c06150501082a07031b03021605120c090604150b0403021c0507090c020106050a03050a1b08030901180f0e0114010e 69
    0x2c00340801020814840382c10032003c40b000e001c0c548110703480e1a01a0f4095001050102e15212650040720342c0502010100701c1313855240c0c4039100c00800c940407001d405040c1580c462100031410f07140c0b0790414200509035460714821081cac1d61040480c010a0702c40a0361826015502d43c602483c52031814881c50792300041251808000a584038010001c1f06d11901d000c001802400030702150319540c000003100907800c02c4602000c4c9841501a1000814045640d8164054007091007500d5503681c5181134010071440b80051030f251201c0e00018517135500c00c41c4d40d0705400d94030340e00340c1c21940050000300c0c855084420800032102c041d44400204c95003010150034481d1400c1c0a410080c040100e1100c155500d40000203080e540d44401c01e8001c40c043c0e00501111802c07403400d4030b1131081c44140116448160b03403090003143c2000083c4e42030240700b0708141c005010188004000c3c048180e03c0b001400c07074034407000324080c1c40d500b025604030380c4032070764010300034100400540720441e03107640c1d4540250000c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 942185080 1250 942183830 942183841
    0xb030c131a12060a0b0304080c1c0f0c020f03030c0c040b06090f01080a0b040c17070f1b0812011212030908070206163903020604092412020f18 63
    0x2e0060341d400180081c04803251aa0305c2889000a40003141e042c0c4244001003070400007000c081c007086030007800c1c0480000d01c541d50303088040d08000307200070800b08000348800002c045450b24600803448800040840e921404e42011030740d502ea60a06440d4052030621901403c14100501515a610382c018005913a0340c040100440d000440100003800082e01c9507416682500c0310310404032400025a282138681090f80461a00564082d010740c04120201038039405895100017041c2c0e4409070201c0c400c140c3c0700c050402005078050440c55014541c404000042d403a0306030744810551901c2140c621500141d80303002a41210400030000d0104032042001038014074080d80101042c88400741104228480c0d5101d10071954607200ea5401c0715001722004023100c610a080252440d20250200390800b411079000c285280504d11034a81469140d1400741101d211001d481c8011030415814003403844e50380c0c1e40032240c24000520a07401151403405031103c03400c11740e6441d0a0800301141d07052903515007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 942186330 1250 942185080 942185107
    0x1a040b01081b0922090204050106080f071103070501060e04050705030a0b010e040602041815121104090206161203050f091e072601060909030804080904060b030c131a 73
    0x500700c070680c01001d49080307035041411044260b1510036004d80014200c01c052061004442040e040b107404c0c400014204180d07120720080c19a406030b114a4100e00c2241d02d02d00d528518010b103607004045508010012440c481c10b0681c51b40f0a601079011141807954500c2490303122001c0c2138002e4426642c80700103116001c2100307000d5410a10031880145420360315000c44c05290b8080c0c509403900c546540440f20013030880038045015040518911403400d0040d074039050881c140c0f1801a0046480e40354113003d40d13a9980c141c034803501080054045182c894501110f1401030100e840300441c1c9480301240e1400040c601c03161041c684031740100700b15880400030015400b15840c1030b03c0e20340315640c00440c0e200f11100844114912101c1c101a03d040031b1400c0300c3c2515400d40000c8901850114000c02095001c1d40e8142c00540010b0203980d245100404103010301815008009131403000418040d104a0707400c01400e101d0710160040d01e040e901e8074100d902084903409442d11020040c40581204540c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 942187580 1250 942186330 942186337
    0x170c1804240f0c0815030a021302120408031e0720120a050903071514031302030615041407051909081615020d05030a1e1a040b01081b 59
    0xd100c0300c5618841e076100c204405840b600c1d541d42101c2500d49612090a542150751103404c0012525654225520000881d5887c400424042d106295046031a107a14405604541e0340304103019500105252500308110603500a41e940c1042c0ca004900d01403041e0948185140688110b54401652054540001002307420300c7c1054840ca001380c940a0504010110080c00c4101158451a49030301c80e400425040c0501903002c001340e041c0e40004105210351180110082c0010508080d4580d10b031036a000030440380407000250540304160a102c2c5048a1030b42c20000004200c50a10841d006180041034032002901e10401207602070011094001c40130820244640452a00440c031a648920f29840c010100c0b800d919150203680b02841290b00288444101100c07600091070605812007008280e48802003900d025155100604100700d400686003040004200d1004e0281175241d202c104110400924224402e621302060303001194011010076204a006030210303030f4480e081080380103403540b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 942188830 1250 942187580 942187613
    0x3006030a0605280b01090b040b0f0705100c0201150b13060819060f050108010e240607080703030b040506040c1e02160f06030b010305090a0624170c1804 67
    0x71190400f0901410041d650b52a14841044040348146a0390009850b042060300900c441903010003043c4a1643e003201141c508025055803241c2d15015401c007641003066903140b005250f401c0148030b8290741e070305401541c0240c10224078040116980d50380807115109420705002c03080180380040052502136140d1540c421244034403684800e43e400300400c100c45c0c040e001468640c407210f40a01180d41d010584074007610988602c4441030400007042010121181c650480140c3c13400e694182d2500c1c0d040c10749002c1f135488221581c075440c0c10320703010f4080c10701001801d000340d00d490005001c500d010b001e400c1c0c0450190300c66054402d010414504c039a210929690194465105503100c000c0c0407034048402402e01d031091440b540d080550081c1902d91198160b41014203000030310031082c0c0c0c0440c000001d40c6d4003100c00142d081003024030480c186403201c50903403112851440041d070100310011080c6214071880580300c015000804119400d88030115241c80e01d145003000a000613091105010401c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 942190080 1250 942188830 942188851
    0x5010905040b1f20150a0204030302061803040b0f030a0c020601060e0609151216030b300d02150a140c0c031603050c2b050a050702063006030a0605 65
    0x40c0304030408115440803d412110294025178058280090030900f698001c15103903019440e151950720000e550341e0004e018800002250510400405070404c1110010041c0c0065075440e50b9003940c1c500240d420441d440d0001d1414000c40300c401e10305c0404c3c4581078031116205d4286034840c910510071590800201356408c42180d1083d180d1110a000c046c0c441c2d0406000710700401d00e0004c02c0c4107201c0d042e8980c510141030410f20b00e24010b548150740729441041060b00d0b0080200b07080c0401881c94580b840154942c00b03882ea44a503125408140c10940380701072812160981c0340c0300b1040c2d08032040381500c0410034001d540404d07075000c545402400e01810103000c803810000e090a038000007841000301200420800550311039000001d220441d00b10b00418032000510b00c1e4602c20200f10ba1501184100304140000e00c00c1080c1d003d1015100041e4001e000b060720744504032101405034010340c02c800c0d09000b501d540b07032a100e92090810352080c1405000342c16020107540c0c031030010700f10150804046 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 942191330 1250 942190080 942190097
    0xd0e0f040504050313080109050615010201021e0c0d08010f0b0906040b13150c0b0a0507180e07030e0307050a0b070c02040f0b040c020c0303090d24050105010905040b1f 74
    0x200d40d124003505004078080da001d103541d00b000301000404441907a00411041e4141170420021480108405610124101e50819010b4030440100c0c0244603144c9864803c0030750324500c0c11b0070792412000d003002e42480c508550007102c51000a0b1041c013000d00c102d902c2014002414040d03072601c0030141402d003030302030480d03030030680c403884400415040760f030a440b40304280c8070007000300b1008440d400b4010000f0b418100d02c0e4100e0740d00c3e1581030b8440107088180668495000c2000c6512468140901c2525017100c660f5140d00c5400b01800b00c2016652040083d041c02400b00c0c0031003004c411901d415901800400c0c2001341c5a5030500c030361500400c51410700c4031a0005902686030fa00408000042c011000605040280100070403110311450100841d40320344020691074500200315001481d040750000101c01040c904500c021030340c240301314030082000c61142920303801d541029040e640244ca5510791aa141d0041c841100c6d080d00e840c69005031102c617002001e0582050402d20301c03030a880c14440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 942192580 1250 942191330 942191359
    0x40e0c070507031a06150a0c06091104020a0e0909061e0408090a0315050c130302220e0618030a09031e14030913060e01150e0a15110a050d0e 62
    0x5101c810b214130036010044010406140b41c054180c40420703075078000d100d0030700380e4801004000200030040101000e988152480601048040c941c007040030040c000e568841080b0f4005141b11020b441c414000c10f00b080101e121810042003080c460304500e41c500412000e203102400c2c4210000d442502c0342c01d030401a21180740c41d480b8005000d035025400760b1500915042440003256001010000080d4042c070009040506144d516811a03404480b082c021003200b10700340310000400c810000c501ba280c00e482c07450020012485034420840094900307026450040c0646d124030611710540c0c001104540180006521440c038900c992101404120042c000303581c2c0c1211322074025941c016154004105500c040c503104040310720b0a64040d006000c41450545140401041806081c00158001c0f0052140501c204074403010140014501e8188942d50759851201c020600030b51030000b9842c8040ea00c003008005203d1452940c4140240000440c0290880e0310402c81200d00740c1c0800308410310314 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 942193830 1250 942192580 942192593
    0x7050702041418061006180f0303080103050d030b130e0a0c030b1b09062b020d060e070516170409050c0301050a1d010b090f090a1b0302040e0c07050703 67
    0x2a2165180201c14014200516004101c00d0141084452070b4031180800c4140701c0c445c0840720440b03200d810284103091801c0718000010790203030040146000d0311000041816031040c1c1140c1224002e109441c42101040c0084003602e2555030040d8121051914114a040300d680c8141d0750040f090090300c54402082e0780301d444a41c4594002d40361a00c65400740180b10340303028ad01c440c1c000c60107007405281008450211f8140d026800d08203100c0103041c840340c60f91140d805183c440e00c05402c3c204548e02e40e10b0796100b2009101500484030f00c404258001950a40a00200c6001c02516031a8001d100525038400003c002c00340e40d007201526050100040b45002c50241a0103801000034060712581080d0510440060326400b070a000c1032112841da42e5804103040290644028403805955469603002203401009000c2000780c0001d0305d0001c01001d5034407075100d085c0c2c21880c0c8000c074040104200d02142680a50b0080d00071213002c10000c2303a40c4000c000c00070f240b43e9214105032102549c0c1d035220701 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 942195080 1250 942193830 942193841
    0x12080c0109032d02150915011d070903080d0f020c0d05070b0f01060503070807090b12060406061e0e03010906020a08011a12070e0102210a0905180f0705070204 70
    0x441c0443d042e076038103040c81c500c2c00c0b14882611008003410502c031009901c0007580c42100181c2201602800c8001c01c2c040c1c041401a80007105110792040c1555a59014003042480301c107001e403044d48400c0010904080c803c00000d811607822070001342c00d0040c0c03c4082801866900600001e8a0307080155150540007480445480c40440c5c46442e00c500d61400c100c140e0050040c603050351501c2c50300040c4401900182901c0c0c01c003215181100d000e56515905503010101da4001d1009901c01040712400c5000040300680700340740c2030340e0070302550369903c00a6070402c0c0015280808545801040c5d80318600c1056000e14041e4000c001103107400181d1640003c03a40541a00000100d0b00300c01803010759002004002200d0725620403515101e02c0402514a500e80984001c00300b1800031aa680c00703a108004020108142c2d696020140e4443c8000b024030b50f100519203004501030100008051800703003020300a01d43c10030780004081c0d495000e1303148d00d10801001070b018880c0a024007400b5880301c2c13041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 942196330 1250 942195080 942195083
    0x90a0303031a09101404020901020d051b0703240e1f020d060306050f1609050907023f090d060209010c05010c09061106070e19170606040e0304080712080c0109 70
    0x3480032130401c45e120841941c0caa41c5603020350300400404041c1e9034006914840701015280294880c06028901142c00001e4403403034a040c0f040c8000403042c01681660309070440d4a0740c94403c40120400012000c0c0e80b034101403e403698101620418170700080d130840c6031801d40b50840062a11175240306c0e0f08110340c0c49030800e135200d65440d010030843c1d00c2900003864008010b80d090618101c0a820b0003400910f1a000d254021090030000c0b03000c080c02000105107126240c1c03104928218440b011520074001718941c612192000d5454045003049801200c84d1540068410010095a80c481740b010703600600b00310b030400c96600041c4e004a0000e100f80c405c200d5007642c0c2d030350030140b5003600101240c1c040c01007560301d50000c0d01884181c1343c000404680a01080d506503020145104601c018200c00b68841c0348692401a91290100d0740803580500c14a07048508201a80a0440300e5550b80114000d0312070540c071081c003c0c0118901840c0c08002d40303104803031b010300c1c02d200c00198509640502c0c60 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 942197580 1250 942196330 942196351
    0x2701050c13080304180b010c05030c0c04110903030417120a02060702100e06040b0606090d05070326041a1b340e09030438090a0303031a09 61
    0x5010058400d400101c030001c107840c070000c41c02d060800d442e8140405242c810b048030641d54030f00851499001e03000d81d20029030084162078840a10616003034694043c0c02010b17110b64504017045407400e0b00031080c0e0b03220610240c000c50a0600786440500c0c134500003103222403e486020100c01e1814040310091003c1d0342181e014003010b041c181000391914030001c80300313441c0c1801c2021903d01c40d5800549194025041003068900d81c945001240e414824200070542040c0c42c3c0340d420f010300c107000500300c04813031045401180380c001c02d10304401241d80c0c0d501000e04100b0208803c000c0f09443c0080e450004000d06205072410320820010100c0e90041003c00c0096045112400e6800184801100444104902c49072000c035070322510740001006e60088040001481002c240c40c100d003041a5800f0341480c40c05661408070014401c402040150803026501d46140801c41d801d4207400261a00d40001514800520342141e505801800744000e40240e08a0802c0b1400700c241d0b40c508980340500c00c0c500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 942198830 1250 942197580 942197587
    0x60406020a030f0305130209060d0c09060e0906060d14070f03060e1605060d020d09080c03031f120308130b01270605130506060c03040303180603142701050c 69
    0x50081c041600c3e540030081450715140070007464004000080c480b140c1c3c1120308240656a000000700000858200036246420090020130b12908a0f40210142c030b6810403000c2c219030391115115500d05040710b416401500d50a18400040c0ca800c40300c1c0d5070703c4820029107810303d41b01c1d61040a26401d0b80d005407600394075003014035a6000d05001580b0071540760640c103090142014007207546407080c4810041e9080d0b00040d000c10f540319a902c500c842581c07000d0802c1d0f595081c800107690303a0b0802e5500401c040c3c010034160303003060380d0700b915003048034a00296a40d28507032a0300e05698400005120040c03081000c0c0c20400010f07414a5524080c00c51000c0410b5400c80d000032100903070041c14071403295645801c005100c43e6071500e82c181c0b0400070211022402e9a520310110b0031500810517103140c0e9200c082008020103800c1042840d06461540110402c03a40c0c500045051750000a48001130307450313510109070342044d0054549101c036080c2c0320004c03110703034103604c1c0a003121002c40d5916149940070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 942200080 1250 942198830 942198833
    0x3110f1518091e220f12030605011e030c2604140114060f030c0303130905130f02012d09080d0921030c0b0a0203310201110c060406020a 60
    0x121101900039a14000020801d0b146080100f40882d02030541c1500402c0322801c0e46200d040c0d04c00e0314150540c48191002100750a28000c100e0301c0d40c466080c4080ba0a00e0740214a6510070362224210015040c44101a2404003c040d401040d408800104000104441d4004240c1150244000c8010700c0218141c0740b0b028181684490a00f801040b42641003107407a0038545a487c01140d080041203500c0401c2000410001e0b2900209120b05901350002003141d0301041612101e6100322001ca800600242d40c40c410011066009950f0041240002140e80005544128000840c544001c0300c68803010486d602400700100039000c100300010a0440e080c4400c11050184000524490030300c0e0060070700700034280f40d08a51501c041782600949201803001e16100c0d85e5181403042d0843c1e0012340601340b000008000c0c0d44200c883c0c0c020302030684689200c401205801c21080354442507203c03480c0400350700456655000d80c1190295110700c0100c00000d03900c44005200608a54000b40360340e1905 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 942201330 1250 942200080 942200089
    0x6220b030c0901020f060c0a111c050a020c010c080f0a1106010807030317010f060c0606090203010b0d0e0d050306060c0a0b0c071505100b1c05270703110f1518 70
    0x21008031035504240c05010640020005a234007100d502c1c02e103d41d1508945582501e0210b002503c1c10b150141605908000ca03002001009400c00d2a401d40f1515801c160040d6179481d2141e06c0108036200070003544211076000805462541102e1a01494007182200a00e20b8000203070405a0b141d04191303c00c008054006103600281141d0580410840d0300d030807050319988546118030020301c500c0d201c9040801c90700d5404070020780306d030020854032541c403001042030503084400c0c0316200520b00500718204000000c0d100c22a001c00303649a0307280d41c0d215428400690080114000d407485440d160b00c0003d4141c2d60194410441c19403000c1d1120131504007099110010494190f409140c04140500207481c0c240b0841550341d11240d250399200c1000c2001e0038004d5250480f80294035100c00d02c1105054000c54803c10106018001484c4101c2d540091302c0d80c001d484024000c0c1c02d1760061b4130f0b10b414038281890410078000c10b4074520640e200b03d140825401408040b4410010000b440c0e1603150 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 942202580 1250 942201330 942201343
    0x60301180b01090b0f0a050d031101060905070909020c1c110114150d050304060c08210106110c091506042c010906050906041d0703030c0c09020906220b030c090102 72
    0x5046400c0b070f106071172078808190f8154031401210f004083d01d5075117a050602424404da004510100200416a0b0b41d0000c44e000b80001d5407902e000481c0b440c03000420810030f0003504d4403012000302500b507445581700380003103031500e00310b0020602c1410501a0103414080c440ca8040270003a032909042440c0c001d0000d08030345c03101800c141c82510b001e000e000c081400002039074140d40e660b051480e40031140d4100b840e15800703030300704071140e001031501d0f2000c000c1f1001c1100e40c12546542c46500f0990901089652202c0c0d0b00201e454001c08040d0008010b425044048004210098129071906032100c01d403030380c04020f0600e4600d003421300101d442d060f202c0d810400e5005140c180340821046007000c00140c0185005018540b1650b00d400700046003070029a900304903142c035001141c02d055542c1c603001d41030300000300c2d0a6520b103013240300014903051280219484e03840b00610462a100c10302c1c00c1c4100c209048030318204034843c00000032501010000c003c5000b80603402001d07881d200f40320002843d181 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 942203830 1250 942202580 942202601
    0x102030406080a09061b020f010e032506150f0305160e07030203041b06200d05120408040e0a0b12010603150c1e0801081207020108040b060301180b0109 67
    0x6104100030496281d1088500d6040b501800c0d01190003041802e141025052207400f1007145252a40072803840c07500021401c0180c680c2d00008d02002c00d20201d5a6224040c00822001420105002c0c0c090b0b005000c00c0f0f042018440c21001035800081d0700c0b80a45412190070040d1211030349a01481485410072044200d05104481d620703d19040001c5c1155440c03001c2c0c4440c06060f0080089400c01c0605880440b100991715080018690349440c0200300320041201c414818881c1c903007802043c1004162280e607444181c40300c9142060340d440011501c01d004206840110041c00041080840312600d0b0703000d55503481c008900f2511501c100005004003a61980040e8034060040000408205464032804c8601c1070000300e07140030384420f40303450041c4c0b1040c2c1640c04000c00444013140c1c00042e654181d58644040b200300d51400e1404125500c1003140103408078a03601e000070006100301883c2c962000700500007140150720383d2000e40180311021000c031030004200c001400045503522404c00f020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 942205080 1250 942203830 942203833
    0x807090915020307120c05042306070b04020d060e030a120e0c1c0b18210d020a112a04061a0915030a020901030c05071e05210d0b0102 59
    0x482495495852100025500d20015038001c80018a071600500341c0081c100c017044420702110100c80c600a00960240c0a00c501d00e8010110300304d900803119000044c40c4401904440c81c01c0c1240d1220304039610020b00480e0b01903200542c240014800380540c827104800b0100650b00c03102200750280c01c000c01014104101c40c50104002c81c0558001807090249000740c407440c100811050030440c0a41110718094129402d41043c0f05814481845424640c1511000c0c0c43c510104005814508850090441c491180900c06c0f0101c08409900a210b605002e04118528400074610f06060407041d1500640c4d1801d01c01024002c1c114140b881000c281003220300b0080541001c099998003440c2c4040c00545c841c0104202d50a915041483d009002c0403d142c544c6a1500340d140602a5000601c4140013038209441801524011001d640406a000d8800d414081105640200725181c4213420b81f680d11030030010300f602007000c080010008001010300396640084844503425a0032406016046 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 942206330 1250 942205080 942205091
    0x40807030528030c062301090605090c07030302030a151203030516140c03130807140f0108040b0a060504020f09041a0105030708070c061b0806041109060901020f1501080709 76
    0x4241844052010b12503140c1498110002c581c14120300901008041902c4116403a080706100c840400700503040ba6800790061000584803418017400010a031101c046070201404500c0c002070098000d50b071b100a0341e00b0000340420352644802d40c2e0200540c0040c000c0c10706c1004c0d640c1030641c980901e80d401014011100b408141400004000540c100321941504102240c440740e002800d0044407c140c20843d0308490190b2034076001d0391108844d22610403070850072040c801d01030400c00e40850f59600305840f40551a40e45846860507120001c00410100340d40c0d07000810b207a0b44510181030003140f0b40101584031403051080c4400c0300c00c2800060101d4000103820941aa880002c4940c0944a0302c1c000010341c4501505071403000880c1c500500460030b00c03d000501c0081840c0c09a00c0840540e01d11030319480b05403c4c0030840d40c151101030700400007000030080030b0801d0001080340c100c040c8125a0541394170b00321141440c8104001c0d801004e40d00e0010000000c3c10000380b0040d05444004001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 942207580 1250 942206330 942206383
    0x9091203071103070b160807030c0203070f03020a021305010f0e09030a0c05120307180b031306051005120606030c060a080a0b0f0402031608090c010c11040b060408070305 75
    0x4050000500701810420038068000c200d01c8107109607030510303900070700c0c0244c507082a005520b407400800e80084000f4005600050071035100f070060700b202c2c040d1500138629211140d04c035441200c2080790190705620610600000503203079846400b105816003e03001625504100903aa0342d240554030140a0250315000c2c0000220084221801e0040600f080005420680307401820709408030b00025210502004000d40c2a4004050441c3d52000d50310307001e159926a005290790380008da4000c00c1290748003101c1000103c10758801c0b0b401c45804d6460000d1155078000041c0c040d0f13506c0e040c03128241c0040701842002d0804101d00e40c10703414110740d0075082800a6000030003d41005040008041c0c80f40140c14954032406400d01c41ca180162080d0b40c1ca10f42030f01c03c0c00e6040ca58000c040000f83c900c600080b0040f5001c600004da08030140c0d1450003111b0640c0b9180d01200943c40c0d840d038804d517104021100c0b50746440c011700c010020701000e03003030031480c600b402410404070050301c0b01101d4907000e5582 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 942208830 1250 942207580 942207613
    0x20715020613020a03170309100615110102090d0615060207060507080904061d1602031e03060402090a030f0501060f051f0210180b060a03260c060f060909 68
    0x10307807054401c4458400b03074100d400001d00a000d103030310181143c1c25165003900345421701c1b0002c52103964542d040380d00071a02584428101d903440d208030350942c09038004100580344500800c5080006500015003419400310000c1c481d0500e03400119256a60f0711900e0200202c400005401001c250002d88600c41c94004060143e2107543d034014030b241d1b00005c420025a46541c00003000e000e003102880c4010075442c0c4200040300d800c0d50344100c02c0c00014400702e8507520000880c3d041e11410104001032404000e4100000d40014010660280d002e0000803103c0c0c5410300c00400560140a010821404c181826421628107802155114401050511540d15110200d40000404110301c0a81c140861401c81c1404c6821040c0c10341282084c006808104144427406140340c041c541403900c5484500400c9580c0e078031840014003052504e01803004200d40031060008034a10b41d26100c1c60701400c60400b600f8268204d5103805d0800010040c00070a04140d0000c60b403142495006044400040d40c40c0d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 942210080 1250 942208830 942208843
    0xa05100303122403050c101d030a02150a08160903020108040303020706111e1611030f060103030306060816080c1c090f110126071403090c0102071502 66
    0x341c203015070402c0c61000b00190740e000020791008803403a443c4903100d45298108070201ca100c10768040c0310321000c0991918001404001c1411181c940c2a02e80320340b5191003d100503900126176150140e01501c801585580300c500304041c9130540401c2d65000480c80c040c0200320094103510132030320100d1a0006041e08000d081040d41d0302401d252206542d186001c6000e4031030894000e00140c1400400000703444180007800140010101c0507600c0106006500e18a0041c1c400600c02c120001e43c050303020400309000d0302c1030064080c00f0784060b90310440c0b006240c102d003a401100000d540d91400c00520740d110304082e40008800c010101a0341403100018500c900c040c0940380000000290075a0072400241324101c3c0041c0c010045c03240e1006400d0010345204074480a440b450320080001c0b00d41d610860705580240c1d00340c0305440000006544031101100010300000c103000f50524805104000b110180d031003071040b04010590b0381c508000080c100100742d4851340246501c600750034132940e00480d05 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 942211330 1250 942210080 942210083
    0x60503071d060c070f061b11040b060c0a0b010509071d0f1c1101170f06041104120c08160b21041506150806060304020f1f02060a051003 60
    0x6658041d101260071109440e080c88041e038001d000003080c01800402040b42c0f0110f9100f00303528603660b07a890200742c91700c0419121030f138003091040c01071600190300c900c054000b07018054800078074440d04d2004181107a11015010340c40e5840707161480704000342c0c09440d601610f02500d00700c1d0113081564019200c2150710a100c00c2d95082d400b8908100d07210302d4100001d20900030202d120320707600003144a44064200700240c030401c150340d512030f2855002e109400c110054012401a01c1d0351800c5180002d5600a88150350090710b560841500c0e299203006030000c1c101c2040000060385e210300e0301d81860740d8164081e0308540c1004042c01e088020700c00c1034004a0b8089840703265126944002c84a081058000a94030030503048240014807415034404624012000700400000e80c40d0003031407070340c03a1540b200d4000041505000a01c0d5040c181d000c0d581052010740603c107107840400c00070f2211800c80c0040050190004048040e50b5030411006401410b204420031090504924062074020395000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 942212580 1250 942211330 942211337
    0x40e122d0a0806060a02011401231903170412080405090a0c0509010c1a0c0a1404030c0302100e0301050108010c03110c0c0607030504150c030f0e090708090a060509160f06050307 78
    0x45da071103114001c0d0090a040d02c0b810398000040d6842e010310130420210508100108505a03e0134103403410040e98804130103a000d081640003a15542d02c00c2800381c014420000c2c00300c400c1c00002900c8131004032640416215445030f030f8644d41040c040c080890030082c98802c0f87c9061440903070607550008210ba01650342803030034004503040c5007843c0e06071644005030100628a10003c10012160030005400c10f05c84036071311030030a2810440c001206009500000d40700199006c01000140b6014504030038481d40c07400d064224000301c1c4002402c403a426440718406035150f004a02002c0d525124161420b1603449042d81000d400803034031035940056804160043502c1c0040c03800145030244040d24000c2000f00100128128034070300003401a10301d60320442c00704031450448070391030740070323000001c49030b0f001400c01d5006684d02d1008440800e40035003846840d00a90440750041155401103600c2a05444c008080361101a21258004182c1c1c0d0300c5034964401c42d000501c1140da0040032039420940f0b510f03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 942213830 1250 942212580 942212587
    0x110a0f1505192706050601030e070812030612011a280312020316050d08100b030601030b010306180b0f12060a320402011106090705040e122d0a080606 66
    0x1241540020303054030f10603070b5240c400a40410400642c100506c60340082c2d0f0107010700018455240d0307071400107008030052030b0071000c4407520a4180c64061540060f005027111071480ca81e403007942c06c5039105041200d400918504a8149040000c030082c4c038110170003051584031b0f40d03810055003103200c035000c000c115440c2d12500320115442001a00e5010b03c5145910a81c0c0000b441c143d07558960303100812000c2041d176170009244e0043d01541e041110a2a401c040c55a510034004400521440710745506040ea10800410120689030304412480009007000842424031030400426081001e1141d03c2141c1c2d500050410f810041695a000101d0b03005c042803c1e03103810044401d024240c1d8001d070b5001011580c503103400c941140600e000368004c0e00c1d400e04101424403100e8981004882c07030740e0303241e02006081016051903800066611951000e580d40c084c40c4c18400c0242d940031030307101e0044140c0d4035150000108075103100d080c3c80d01ca00c105079240c02c0c5a00d070b0240c400280105440d101d0100070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 942215080 1250 942213830 942213851
    0xc050102040b0301120b09030f070321060801061a040b04050d060609020a1707020601050f0f041e0915020903070306020c0a060504030201020a0f08011a0a110a0f150519 74
    0x940555001c0d00c0c00d41000b6460b5a113842c0d04c100c1d40d4030780580603075090044a000c00c40b00c1c000070007191124100d0346580d034a040030949050301d0000000d02031300003041348040c0400181400e48102c5000c3e040150001c40e01500d42180007120070091a400d015448040008101081408007100c08890040d07800500034041c90508000070700250340000800c07400021503245483d0311103000c2e80b912084407205107054407007050807640e9420034040e440c1c000648101625081c07800c0b50303a010713030303008020300c081480d281c0c104120003244c4800700c040c1c80070342d118905681000011a219410b41c10340d40c1e8114103054003000080c1d901c0381c15101c0603059590004007130035944000c1c006290200d812000030302c854141450001c0c000e6014158940000d840c4820072010366210f49041c2c1d04890340c0c500e4841080c40b05090900300340e401800360b60240304460080e201001028400c5a14003800388100c82c15000b8142080c0c4a0703c3c0c10000c0d480d81580c500004c00c02050a048058109000c89903000524410035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 942216330 1250 942215080 942215083
    0x141b030d020414091e0703050c0d18020a0e07020c0d0f0f0b060406091505091807060809011109060304030e0103060b040e0a1d03030c07031b0605040309060203190c05 73
    0xc5000e005032650001401007202d001d0340388401030300c1205640c420b010360340301184802c1c08a081c06141c0e11200c100d4000c00c401034800e41015801500c80c84100e40340c0801140e0201c02c45080c031009005040c02c9000fa0000e6203045403040c0010071621039150741c1c5103801c0783e00a480307980c4d00b51014815001c00d49402c09000f0b6070880d540c2225440121510b4811442c10445202d90048071150712850820382c1c041502c40e120f00400a8894400c07486400c81d9080408112206000402e9150340b0305065000701c41003c002c001400061040c3d071034025141c00c0c80f454040c00d580d0810142040b0807010024030543d42ca80d0402c603503100e505440c241e0180e43d01c500048028112980c40041449008107001c6810000c01c0501d40c01104031711420800542403131140e000daa0750092050000c0e030400c0c00002c4100c10030800038448184a4034080d4102035514402d102d0301c1d242b00c40203032021540c500070002010b0300110044060803040c001141002c003802616a442900303500364504101d0051400002c0000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 942217580 1250 942216330 942216337
    0x20f130801110a17040512030403110d022116061b11010203060a0506090a0f080d110a050c060304081e0702011106040c0902130b1b190c0e07050702030d02100b01141b03 74
    0x340d47c009a582c103260038020400341c508881000c0e18044c041e4050683e900028191303c400d00d80302c8140078440c01c25a4440c54941203c1c18000100c51481501c40c00540c035449040310002030990544211815010000d0400709104c8032010940e1041080c4000e80e031703502c0c2803074007180c004413036a550f5800010041a41d0040a500c01c2140100502001c0b079604c101164014915807a40da8142c280c288101c2e142e903035050801d00250081d080101400c110781400300c01035238010300801c8020325100c02ca00307098501c0d2011020940186030b000c92028119039108070784420004800c0300409050a0a441c2ea05c2d10074101e10409203002c3c0c1c0054001304540f5640c1324030b4001e1080d44040c0d40c480512000c1c0412801d080090510300d4040c201d9802c0801e0000000c0c40c03181500402070316095800c0c0201c00500c40f201070800c0c0d0070320105100d01c0c00141d40c100580e0b1503a002c0c5a0180c00710144450740c1030b00341d442240c0c00c1c0b0705100e4000850880c04054005981b54803408004111801c48400c5c01a400c510 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 942218830 1250 942217580 942217603
    0x120727200d020d0603030806032104060f05040e0405030d0b10020d0e0a030b010f0f0b12040816081b06010906080a02040c0c17071704050d0b0a020f130801110a170405 73
    0x113040001c00014580c100c071246205a030306030180d403d03010b10709444010004a110300c500ca6504188001e0200c03e21400d0a148810304500b0514946521107000e403c8481084030226100c1e800040c1c0d0154031151400380416404003521545410f00e84250003039100c190042009080010101140700c059a54803c09401035030040c10042080d611100c1c1c00b00404e00c40c0c0146903440451100000e0a03880e01812100d07603120107802039245444955910005900c076142d81914802084020808130700c0200040145c0306449801404a1100c07000503814801c050307021104d81c1d4a4140104120000400c0c80800254112000115901041ea0640d1170300380999028086d0f86440c40e80ba0b1010014034020030201e4000c1052a21900444034011164441c50140d50340000d840d008d65000181020f2601e6000000183d025040c45403201150034250804182c1081c1ca80c410441046014001c1c03191010a00141c0b46152408205d180c0140c102a2012020440c900c00c21000406000040c010b030302550 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 942220080 1250 942218830 942218857
    0x603050c011805190302040b030f07030b0402060d0e1b04060b0901110a1e1509150c020f010507030204051e0607080f0906030a141023120727200d02 65
    0x4041c10130b4600c02240250104900803860103a260ba89450002500c000000c100300040c1f0441d803c0d942c410b00c8092000e80202d030020f1041c4080c4034404041d00400c1800c1c607a8500600401078000314150781004c2e071800300c0d800750303140003001d101104448044807005030003800c1401d64210701500d494640480031402801d948400310841d42040040c64060307070482d0140e20500742240e1900d0480c81283c62810780280030800782c00c01c2c03141c0d000003070b004444004004d0064a04502856101c1825140100c540e100000d50001e014004e620303002460801c8041a9a01400315034000000f080940c8140300d809814035a011039084c020705800b81c07c55035107040c007400841e141d041104002c00074020300f64089040007941d200003070443c6030301003a0000b19254402e014039000c0201d00c0111008003100150b54008540b0441100c140404004690082030b03200711240c0c0581600307000845607070395461150310f5541400320980c0e03098802c0d444032060310701c40b11041c1c1c0e4850018191030024420034440d61442c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 942221330 1250 942220080 942220099
    0xc08090405090106031703010e011503020c071404060803090f011404030c09060e0a0203130b100b1201030311030a12020a0c061806052d0924010609090603050c011805 73
    0xc01d4044d0480700449105176642d03145449540e0385a000c90000f4000c01821000301001080550300c2d02c0d820554460f82c50400600e403d80380b600b82814480d030350700f02903044285501d00e00c040d41007910406004042c0b5101950801130307075200141c003000081c1c01550400440c03144440c19003551034201c03030066074402c0318601050343d60003000740a080a0321521175030300158070001e0100c0e071880c02203910070f0a09090441c40d41502d1380d84c20200e02c1c00501001200c1b0f01c04500466261000802044440410103002200398503524000b4a41184002220410b8106010b60340741c03550418407520032014aa44050303164044180308a441800b0444040c0a40381061000d01442c9203805440e0700803402120140b046540d003d11800b107010171a00000480d4a50403141d031840da42806071560441140710503250407102030b00094000c004440c1081240008500042100c0c40c0c00c0380e00e001c0240441c540070721221b81b942d182c154070760041060203410b12125101c0d01e820400d18003241000b070200105110324 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 942222580 1250 942221330 942221341
    0x2070e0a05040507360e030a020606030106060207180507020c1c0510020a140d0906050f1f060518040e01020d0c0905090105031c0201020906070b070225060c08090405 73
    0x15090075034040e103042c001e04401052110b24015090030110b02c004104001005041c5582d0170a50851842001c45944103070300d282c0400c01784014154894543c1c020201e50a2402c101401c582d015444031080d0340c005c00d000c024094002610f400e103000e04410000d0540c0d43c4c038000742e0500e1090b4540690003802020f80102d8a1500307400015894004c50840d0391100d00914500120f1103680d40100106040d1b0b00303004201c0d042d09004081d00038082c03002154148680d5543c0302655029240c40100c0b4600c5000c102d940200c0c6030a0004804c0da0700145800c5500d04000500180314040d241d80b19080700d0340d1009000e440e40d0b00501480510322000315034421840301400000c01383c0f2240c01e000a84680c0d0001100e00d00501201e040c1d0708010003900031901c000d014405010b030004203200640d5024899889583d40702d0014001e401e0160076030b000340d4a408203000381080399602c0104c800c0500120325031002c41031400300344142c80190504554412060400c1d030700701c0c021000035580c4a0f05010030084e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 942223830 1250 942222580 942222601
    0x2210115061e110c04150305060109050f0a050f0a1a280906140909070b03011401090603180b0603120d0f1508120a210c110a0209010b0a02070e 63
    0xe400100d109801101d0294004044942c207040c3c0e042c60344507a00295460140b071920340c0c070001170042d8015007041201d5890350760504041d804d9010000e59951a400c01c191050407c3d0241d901c03a00f00b40c02040603291030380046c400440003406840d007032555458071541c4409601400003c080008000306582031030101c203c0c0f494243d1041040411401c100c0c0004d41070000c2c06901c05a503c0070040c2e0301035414075420721502e0030001380400780700d2185130b200088056100300258040d0225054811050190000160494401d0341c0007408052914049410000500c00e803150030552052000c6010788810000038039101488495002407200050600351340d00c030503448480480e0740404140a402084171150504583c00d1207441c070325801010b094000005480010b102e0030002d401d204a981d55841380706119143d0010b454402a5510102c0c440e1294002c440184040c1004004044e2003015602240c1c1e051418801c4940c1d600d404076203040454001e00c582006401e407046c0040b1145001c80c0d03000b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 942225080 1250 942223830 942223847
    0x40911011b110d030905090403030603120503060904171b0a020a05060c10110d0c05030a2708091512070e0109030b1503011d0d14070221011506 63
    0x49011031120101103154810506a984581d9000785241c01c0411486040c0071100c400c2031811010000051800300315591482c00c2a4000d90003a030b0000389982c29444c1c208e07001500d0013214030501c603060041110660724000309941c4907030312500d26040d64180b00351445180c0500d4000c511142c812010f411a51039001a035803680900844040413126996000d20149110b4038500104ca03402c50843c08030344c44100d41240c0751401c0440852450302502c04004030403503940744003003000588000180f003e4402d0038020854440c00c05c400812003600d05214502d440c0400b224024010040451007041c4d0740c1e103208162074000200c41025903191542c180c0c8136110031007203031084045072640203081c000f9441055140c003940d03440b400845494890220032500c5207402681c0d140d140d902d41042d15000d8082001c4688501d0202e0001c100e00780071124054002e14920001e03ca1000060041030050307078074824004d01406055100b40c107400305040801e40505604026050b5070f05002200048c02039000c17503071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 942226330 1250 942225080 942225113
    0x5010507141b03070902091c03091203030207111207050d02190e0601090905090705040e0f0a0309152102031008160509090a050706051308120703030b0603070503070c110409 76
    0x60300c0000d91141217803012405400341c215000300650711691502481070030440c10250103820034000c06c5642d0b040130b074075490018104034002a004601c083c10050040c1520709a0003044846142c0e0f541824545655030100c1d109503840b47d0740c030800c80000e54640f0401841010001c1c500d402c010b5446200c0302c0864007050358414002010080300080342c2040d44a60781c01901c45102814400b860b213010807019042d818100c18660081040c4512034541c1005503180f03082c400e441e10045e192038600c400b100c030014050040244007200c19005640086240c08103540e1407140c00040c0c8940355005200c0c980d903415080b85101d032040d400b80512380192600c203001194022500c11449581d1980e0203500c03200e80000045c495800040144072007402400504506030540010034803040c0c1c0c0b801014580305c1d5841d84080025000901c09085c0f40e414043c5441d01d00041e0f6503a840c46c02d100070300070582c0c40024000d40c02c20041e00043c1d030402c51295820f05803040003c1c4184000304c201d003001e04040609020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 942227580 1250 942226330 942226333
    0x1b030a02181e0618030114070201150b0d2706090605061f080c090d110f03010608030a210e0d170c07060b04021204051614060405010507141b03 63
    0x3030350200c1c0e280030140c550b2004850303031008950800c09024450a0307040283c05062584d0044c00c80308064800340b0810001840e500310700d04407401c00b110040d0840b0070180d8542e001000d0a0001c0c0403000c50102190a510405600001c2005201e07411000c2d980c0b42e000e9541c5103060f40391010081c0122900020501802580104011b40300c903410001c0102c0030038420605030700030090b4506018011820103510004d425481498450750364001080000340c010100c6021084504440982c201512603644112054000308841c0f810000030b9a079030300a480c00b803c1040520070310003485062042c1e90190042e08070f2400d1004d81c1902e01c22540300e82d90500c00a001030b01020485003441c1c02001c0d6103018911402d100380c80d110b201e03226030002d440c08580964001d9020071002d000141600c800500c43d5003e58041c1400302107454403014903a80c59442800c00382e140713004a20850340c6000403681203075424244541d40360102d203803800411181120b003a02c14018441c0e480303d803088980641c0c001400440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 942228830 1250 942227580 942227617
    0x30b0c04090e0303060a0509070c02040e1f111905120a0f1506141b03160b0a09380705040f06080c04092708070212060712051b030a02 59
    0x90b01035581c1d00003100d0880d400f0078043c0c41004107041c41450141c206220f80f518003a0b150141d0007140076074911060300392903503002c20400f480d0701020120304401602124030901800701c8800d4041003502911842d0340c1e0b408001080358206500038000c4031020b00070000d00804900c0c00c481c1140040c10104440d101d501d0800d800850b83c805203143d0481607c40d00d0701c0b404000b2003030b5054100c080d0403200c00211651815440520310603402c002502c1c2d641d03505001070345c00c0c000900d4203a5002001405940c08581091074000008800c01ca440707200e152449400318000f0160b4120941400030b0320350141c84403140ca8140031516601c400200240c0360b010a001c41c5143e07540f001100c003520215991014040f00380001c0c0040c070b401d81c010560743d001c0b02012444030710306802c0d0440403803201c1400700c41c0800001101c45c01c60070448050a06441d060340501482e01d00110b002c1c1041d01d52040191855503158000b844503007004800c1d6014a1100c4011a02c0b0b14114a1110095005030042e080010702c94 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 942230080 1250 942228830 942228851
    0xa03061505270c1e04030533130f2f030304140d061e0501031509020303191b0c08060c030108030706112b0506010e030a0f020a030b0c0409 61
    0x2202400070a00c102d5036104070650342d0300e01e0304016400c050203546061082d208030304c1c404031805010f0301c041d60066001e0000b80c0d07030b2070314021040d0000c40d541c8154031420b82c100d4821040e41096040d0300c5010300a24124101943ca403100651502c10001081c072030416001c03c5045400054541440380416002c0700e0708201d0760704040d964001c078450840c00001480044a8500380040c080c15881d1003500007081c08503903004000d1258009d05010303c28140d42d100104140085800e50000005500d001005446003680100e5200d20405d0002038161480110414a5510484007542d4019480d4428a40710071140307051400c02ca80c44c0300d00c4825104280104502c6010700003100e049424a00041d032500460b640e40c90f002c0c0080c02400254a503080c454941c905030b000d80c1c410102500b40002034040c00070442c1040850b10007502450400c070651181c19400c1c0c42c0003450204041d00b017608026810090703c009001d0507199040144800580c0091081c5503039404013034000d45803118000e02c00913108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 942231330 1250 942230080 942230119
    0xc0702040b1c03031a18150d08040b03040212070b04081203070905100903061503030314010821040902040b12011a070602030a1503051605010e0d060b0a03061505 71
    0x1c6040801c121203002c00801c0083d002e680144911041590300c504c640108000050101041c04103a40c00081d144e820400c168401d82c011003000402220764090800c40c03515502c1c080c0c0941e029001e1341c98030002c042404d640ea03a0b034283d130741540031408981c082d645039090181107420522881c402c03032046c0c90500c1d441c4003181041e24402c81d00e079616880d565240c8800c02c000c1c55080081182802400c0b10040041803590040716518250403828004591131840c0003002c84000c052101c481c0c0404400510201c200071030405100e03074407a4800c110360445105505214071855212800f03851002600203151380341c0c5006450360342c1c103413821401180c2c1c1c0c440081c503d800c0c80480030280755104001c0c11000600b00d40c00307160070181007400000e101d070741407040b0080d803030441d0010b407241d911510030b502540e526202d85401a200c2803810008506900003c80c1c290003880e03400904090721009012410349500d92200011600b05509000700704403004071081811440c064140107142c411004100401b8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 942232580 1250 942231330 942231349
    0x121605060405090a0b0d060f050f090604032f061e01170604020d060e0105040f05060106031e0e0307080d050a0f0218130b06070b09060906011206090204140c0702040b 73
    0x4026201c3c061a69031420381200030001c1c00d55107a44054010100c4d4041540c5200351404402d81e14800a09400c10074444000c7c1c002c01050701e1241d500002c10440082e9020460100312082441248510200140c1c25816444901400c800780d20130f4600300240a4500c441050030b403450304080b6810f50741c0398030004505c10008040c080072984007202090042c281424220407042c040d60000071039440c0e9088080c01d480d4191030a6a00b20a620300c20401d016080c010a4010b110300d080810807151004040042030003030300940001e13555502484010b290f400d0080b40c100c4c55114994a94525002100da401410217139001c080c0145404034104d00340881d03200711040050382a0359001c8000303003c003c00081944109000b080780d80c50ba140050651641341c05041100c0c85400c4080062801d094840d00c0e0180040c10641d05502420040001c0382d08011120b2846411041c041100f906500109024211100445503503501010030000c4105002c00542803481c82100c1c14040c40c048501003010382103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 942233830 1250 942232580 942232589
    0x7051f0801030b060616050309031c09140d05150a0e061b130b0c0a0516030305190516060605010215060f102307030212040305030d0506030a021216050604 68
    0x24800001400443d05030340415600c00030080c1030038a00044100e00e114203c030382d558101c80e60307400455514880e150030310000c03001040030a0107214103018034000904103545d42c40340407120008201751003001d8440700c2402c10029048012910690603000c425030181030100d40c0989654545114900702c1000807429600030f81c199580141381c040d04a40210381a44281c00a802d841d414900002c2c9110341c4002804c000c0c81d02401500c00b80c2e2403420464103150014003110002031030b0320310900000b0b400c40180c0ba40210700d0412600c1000355900103403001c2c400c07000007581b0342d61030055100400465400c00300549000780d0903110321041110800b003080405440a03640000d441000114074289514102c0b056102d80c6488010ac01503c48000324441d1030102011070282c00027044400e0640400481c00d400d01004040c910301840c40d100c003600c90242d54400c2110940700d10100701d140d901000b03036103c2c40d03070010400144010b400e038105a0711a98801c210b20103000c40e002c00107140c50440140d4040f01e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 942235080 1250 942233830 942233837
    0x2030705030a0f180e06041119050901171003170319150308040b250f02210d09080f01020a020307061523010801140303090906130e07051f 61
    0xc41c032402d090303030010010340c0c440b820440c1e42e09441803010764100c4c00c000240b03810240821617041c004140307c10b41d00c481c0d41e2044410b40030030140f81600c0c03074a04808020215840d00d40d88034141c6600488550313001ca0500414048400c0c18000c0c6080d0140400e811070388120b100c92082801d01c10344625500084595500e02410400002c0040040c0c3e0800005c103071035210441c0a02c1e403684d84000325500b00e500316492121010450b103000300c0e010754404071202c0c44044402484081030303469086001d91008001c1c06074810241002e07403421030f0008603900c070340b9040623512105200e00307004003182030a204414151050200c03074076902c6018400c036400001c1d07035800303540ba0076210f0300d550014001c0704d80405070304116003100188160005440784c44200b0601918486110401e00040960006070040b000c11000e500880e402d0707590000c00c580c01460140d401c08910307911400025092940541c03002225401c4c1524144117000c00314645099503421101c0c81301020f9441688800710180401d42c8010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 942236330 1250 942235080 942235087
    0x1406010f0e01050c01020d24030f0f15110a030c09060f0809030912070e010e011202041a060c0c0301051803071b05031f14160f050706020a08070206070203070503 71
    0x48901c40c04510000040c1814003a160040450005003282c0c0403001c5100707400d5071510203501d80c202c2408808540c0030021017510810b4110f441e01454a0007161004140440c6031854000308110000f54880c0400441030411521942c620709940551142c802c2c84006498082c0c00190300d0b01940140f029100e0a50701c2c415540c0e194681038401020281018445100c148004c524955901c20900400c02900021707042c0e092620b40620405003068008000303003030300180148005030507920010320642e012640452020154102d005c0d2154001e912030360030480000e1081000440016140c0c035002c070580c000c001c0c1e80e581041000030702e050b070303065441960410060700000c2446504051441080c04000c0c80101e41e43c0c0001900e0409900b219100054040da050400902540f02e0010251029040e5180511702001c000350b03109481c0c0c203501c0510000d8181000024400c505481039030340d2100e002c55550120a00c09010708800f1a81c0c180148035001c00520700034400b10580e808a43d1000040d0705 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 942237580 1250 942236330 942236357
    0xc0e012c0105040b01091a0403020907090e0c09121b130501080d0f0908030a02010c030c05070201021f0b1201150b160605060f09041101090906030206120c0c07060210140601 76
    0x381440e0440c190400640c4240840c0030582c10001f03e020b501c110051980e964558410b1240c003a40c01000c113801c0c002001420456803d010854943c40b0704e9850381c05941c0e004180004d400c101c80400400310500c18198400e00c001101540d02101460840d0124401402040864240c0354240030701c003c59003010742c940d5406070240c4aa4094404d03036090000b1051344a090607440c541244a21030010f070346617000703144a44d815200300c0c40c0b1420640f03403551414403aa00042d544a0f01001e40b101c000c4201120a10030501c80d40c440f804a00005000e41802c0d040d0b8030f10035020700b0140342c4490310f012100c54001408880e8004a50a40b00c44032207000315185681c4a1170b0003441c005045035042040c4042c0c0c1da000b540c8a4100c40d00c150300c0346103001c8000032160300040041c541900105442c40c80d0017010700150340c6000a60b0401c118100c0449140d9031042100e4450b400750031302040c454401d205010880d40c0e0040344540300ba540344081089241c0008150480d003c5007642e17403d0109542c3c2c0c03400c80e03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 942238830 1250 942237580 942237589
    0x10e100e0c04110c03030411010806040b1c0302030c01090305040e010b030f0103080f0f1207180b07080d09060c0c15051902030612070f052107210c0e012c0105 70
    0x2543d500e0700e0241402c1440149445003194011201103543c0394001002c55903540c0c200800e00d41160081e0f07000c100300c203801d0000c98680809440085402d110584404c01018800c00460705e001d042e1000074459a80c151030f01425a4003e4000c0004014001b000451201005016240f140d19000f00544803a461922040c009520520504418807420841c3c20342c2c40744244020105004082c0c40c01c2941c7c64840401400030080250844900507584001c004035050341d03050b1006a90801841c56035503102000700c0009110080c1d00034003a60400e03481d400265008500c08490724041d01d03200c00070a03d01d2515904a0f07508a0303000c2d41d00140780c1e652201d0b42c2c0307103940510b91100000e00203020000c80345205c6490714000340d10203181d02601a0f018080e03400c00a0056150440b111103680710031401604070303600d545080c000e00302d030aa000300c404204100708050380741e6040e4012420144242d242c0200f0502c10074240034600700301d1100d000d8600303c050f69002034082602d541033f820017180d00749002c20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 942240080 1250 942238830 942238841
    0x10e010518030a031d03070302030319110f011b030501260a210201060605180108040503041706060901122a24080601051e1e0a02010e100e0c04 63
    0x8081c24034250129103a1010800c140340725000f62243c800036801c840c041c41030301c0c0608642c5d034000d0f040134800308016200082940d001c00f9aa01030442c090301c0d0310801302d90b803541c42c401100d0755100d01d900c9100c0004040d4449808860365007244002500c03c01001d40584000380b141d002e0001c0350307030380b5250000c03032007000400854944801d9030381130400f42e1625000281c0c4890003100840e4446281c2800d10740910a105c02041682000c6041c203a1100d11100c40c81c40c4024418144115000080c0c01c02c202441200d0207040501420808a03c01c2071600e81d03900012034500d4066000d403000401c88110084481e215680d10100d40d94000780080c410b400741e50080c242c1800f030480803c1e0007050003503003181c2060107101d110721a05100c01400200500d40100a09164103101c1c00b0400449003080480c0c0085801c00c2c1030350002e80e506044031318143d2000c520300c1a8805004042411824158107400860800d4445402c41c0d482c400300c800e0010880d500b44c1e80f0401c0a1340701c0e00044150b401c01e074109 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 942241330 1250 942240080 942240097
    0x1090f110a21230f2103010b09032a091e1501030b031510090510210804080c030723090901140106020d030f06030f0b060a03050706111b010e0105 64
    0x65a154080c0c1945010b800300702c01001010b640c00155440d031364082c0401a401e0301031802c80080b02d0000400c07041c071283e4401070040003106000024a0f11190700e00300a03003100c6c08050820501c048485030400c100440c0004c500a104610100218a4180c000400300d50201c0b0314242852803911603e41070b030541d030641c011041c18142c4a6100303078031594050201c415142c070703104407800c0f1500d051400784006101d00d402818080e0715013001e000030000300da060201550403119600021150007008030407004090355004140520001d00411a480d0100c2c0710002d02805508640d800780e103610040384460352008081030503900030012261185000c3d03837066040f5210400000b80306128012505ca8550240c2001d009a800a1a104a41c80d4148a8034804101700e407401c100c82401c640e110644540c1d103800242080400001241180e51501c040b40001c3d070b0701008890003140e03176100141c00c0ca01854000012401602ea600b210042c21aa070075158202c144c3d540440014090f00640c0c96411080e42c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 942242580 1250 942241330 942241343
    0x10513050402030a05070f1409040f1509080310090c0f1b11040e0706090618120206120103030f020c09060d0f1401060806060a0b0c070b1b01090f110a21 67
    0x301031010617014446040a0503070704003035540081c03c00003100c2c5c03120802c05034140145aa0350401c8085246032426800450707100d08404401204d4510309005000400b0000e001c4180020920604000c00506041100e1b15603e0034040e40d045208140c2e840c4c81d0030303922540421074040301485e00428420300c3c41101032154001c41481c214010200e012103800005480e100c3c2d00509051204503003001c032040c000c00480c0b03070220440703085c03d2502400b07198a02c0754011154040c0924011582c1e071105841c400d2074002e4040b002981d42e820300420440100083c43c002d0701801222900604085850070b200302800b50600f0784010030780c0e6030289412003120060715410310360f400c03c481d51031007130260100910302e82006010a051450400c0182460fa6115180d18002044400c0000d0030101e1030404441c0c0354911561162188103450020401640054000d9403920517910304101400180a103528020808003600d03051202c00d0003c04c0c421401840d45214145000c84001e071015800009042e20844 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 942243830 1250 942242580 942242593
    0x307091401140705030301030c0e0c0a080a0e240106030e1209030a080d053310090b1606050c03041e0203010b2e1b020420070c0e07050301051305040203 67
    0x40720a81d40b504543c400311140d0700008010024081e01a01880c0a400801d51540d92800c00c501460b540c0d1083c8980c0506000c4070100003140410f1607405101e02d444c8142c2951022202c2c1c002000c28130107560003004100341c0d0003002103417842c4032b031040c1e0140156410007001400c0d10848180080d800034448590b1501c40c0758000000103407030801601586420100125160900e00c00300c9941802d0140090b031108480d12008040e4480c100c140ea40d44281039a0704600000d0841c002c4604100703c0d080040c00c10360000b440c00500b240300d03448181c1320380124000c2044d500c920360034858511064401506805404000352070340c07814218000d1400340b0042c0001740c0c40800a010030b0410004c200c00c0714055580a110700c0d464201c01c98000c0c190320852030040d150200c21120b0030015080e610010b4011a520312000030144441e914681034040140c2c02982c55000524104c019a19240102d840700300403140459009800307081900e05840c401815400342c400c001e101c1c807006150041c0f050383d0510601 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 942245080 1250 942243830 942243857
    0x807110a030f0302100504121b1202030c010f0c0804080a110109060608100b0307150c17091e0904060509011b020d11060f0708041703010b1902030307091401 69
    0xc840038402144039110807440a40325080181c204545843c4042005003400200f100050b0070510301e0f8a8906141801310009070620051400180e614400900303091100b0f60001354035800002800c40d02d98000020310802c038058000d08140ca0040f841c0394041032464001c500050080e41c0500ba0034a540d00d0f180c0d40c100741400f10542074480c500c0703042c0c031181da580b01c00784210803090200183e40d001c003007018061442800003003651510f1511800a4030214400046100ea100d03008c5401c1d000d402045c07080101049108140c415448034030b040d44191400840501e5002d1040e2242143c0a0000d0a401d010b59031b944034003001c1c00d0000c2990f4915541d810398504010300e000401aa550700300c1d402051507003d2004c01030444210711038031080a0b4022800c00084281c0500c9169022515185c10180d545440c07400d25207890546942c410205000302c000b20340c072200d00000d0a014810102000319402003281d059071a4030003a10b4a81c00241900c009000c1080c1803078444541e1700042c5890a0300e5180d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 942246330 1250 942245080 942245089
    0x130f1a03090319090f060809060c0a0311120105030c10050a050f0403060504110405060616060b1f0509011d10110c030a0c08060108190f03020712081222080711 70
    0xb83c00c40c41c0d0205910240c00d20649140c8245100948543e042c00071503420f01c808101d50300d040003806062407480008480c00c40718420741105403413185210318641c030340280e101417070b40f034200900906009106886407501d0616040350700b52400038550711114601101031030203c03401d9004010302003010364204000030005403a4481e180c030540c02451000204d092031010003085d600d000d426940b0444081c00b15a608800e803ca040c0e040700e502840c00103020b000d40d800f042224880691003217030800c0003441c00e1150b07070f0444c0c020076035042c003640c1d01c0340c00c0d0345030072124408000503114140d0081c480f16108070080340103200700e021383c049450450b0480a40100041e1070309001e40c404458100030003000300841c4204100710750141c4144030180005900d00e181c451f064201c01140941200020b0481d5000c1c140248003980c00b421003c00c041030750300210708203110755500c8150110070401025001030418900241c54488081d01e0203020802580310381c032180220b4120344015101d6081c1c030104110a50742c1d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 942247580 1250 942246330 942246367
    0xc030212030a0506030d140414040f0c0801141e12100c020c030708190b1503011a0907020708120a03020903010e01060e070c0803040f110904050102130f1a030903 71
    0x68850003203031510301a804e15040c103013001c46d10010b000006c2e18030110304000c0000d03642070f92110500045d010280e1307400240507200020119100710700e00440c880d0465031020f42c2c07505a54018540404024218043c400030a03545440b10141880f1200754030024541400c2d064881d0100408503989100189101000c48554500303007000360f8050f615001550409200780c000400154001e0310300c1140400924030041c0e804800100a19100c0c0300207600040110050320350400064020030406045c450b034041c000500c62040c078400c040c00400a042e05100150103000e6a6541c0d02501803880c0c513202c2040c0c1d07034100070150028540c023880716142e00d89003445640091891000003040b802d2a1440d40c41d0340f6840640b40d42c08100103400e040b40415002d0b41100c0d0000c1d400a034480540c58a0305000325404610985680c0c449440014041442015005480d5a22244014000703403640d0340603c01d9901d01c280309640e000054148014031307641043c400b956000391060141c80c5003002d0410110302c10f09 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 942248830 1250 942247580 942247591
    0x13030c083003150a061119050303060103110408060c03041e020a0501110118050a0204052419030b0f090601080703020d3302071704031a060102011509051e040f030c03021203 76
    0x903000b18141b080101c080041d0302c4104039a03a8082102c44803030315101c1d1030703100080c00e8034107158640c003d010b40166003500b194000c000d9141664118104800701903150742c0203403030550b42ca03c084601c00207410200d042c12468a9402480c00300c205107082c0040d1000280a1280300704e5550780c034691603100e0b0001445019152180001d0003101d400391040004480c0c01070000045809000070f030fa00d1a25505000705000c040443c6c000d5104010b0b034101c1400c0380c0c900c1c0c1006111207103041c10302920000b0705400c14054150b10050716038607a260a54035550389803c2c40080c3d4072043e40708400010400d1442e0b4941c2914030314840d00250307240a40c000100f10b0043d583d030303200c0641c0011080d090018010707030030603c482c80c000e4262425145890b035070b41d400450114102c04080071341c04034845130300135032041d5405842c00031f00a1400d42c1d9407908100030403003201c0011202d03a01d0090f000741d900488080340d11681e0302c0a80c82c007104120b5241103641040100013141944140c0d40c4403520500688090740c810f6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 942250080 1250 942248830 942248837
    0x90801140a050c040515030a1b210b0a030602030c040f031a01090504020a0314010b0a0909020406050402041a1309050406091103060f070e030313030c083003150a06 72
    0x9041c4012014101c1d1001422583c80001c2408240311355070b122050300c0104010703118070a840380c40c2e03240d03107070300610a400701f5050128a00e103096240c1a000303442c3c40c600340404403000d00300882419440c4190349240501d2031384064000030070b00000740302e5405180c110090b2442d035401c2c00c0d25541e41e074401c000310740c106275612480c070000700c0701d10a5051b0226000d05428241404507040a6020941103e00d0b80001806125440141071402000b54800f0b0500c400003800c42d035640c2d0f6a0390306400100120034040e03010340d040150110740c504050086404807456038208080c40c01e1003400d01d044070f4200c80c25128a9490300c0c040001c1c5410303240a1540124040c1c4800034504800e46001030b1011201101c176070098001e80c0c1084014492074039465404501401d0902c44201502d000030304612440a0040000380c16079404414491209440016583c0e06001c031070700e200d0151880c1d442c004482c0d420070b0941200d442001042d003080d4005d5a00003080c0c400400814500d0000203c18002940014000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 942251330 1250 942250080 942250121
    0x809071e0b0c151308071212111c0501140f01120c05091c022209020d230304081b0105070602072f030a23060106020706020705010908030d0507090801 66
    0x541c00f60119400080d08412801c00340c402d513541d00e1160192090140c41d40d21010000c040361401202100c15141181c1e00405c000c03400d00c6070421283e0405424828005024079074601c01011601c2040d0603150fa82914264005004e020429110903100010303040106045030700c11001d9060051080d04001c3e5140d440d250391621050151100b82c0f408940a5018010f01c490003580f610340c0d00d0a178086007000303005d06141c00340c00b840c0081c6c000408025004403900320210203001c01841c0340058400c00038000000c03c518054090381d0380c0514001c1d4001d94201c0c0000c80c00b440d8004054051140b81810b0150500041d1b0311010100d800c10002030303c0e40c840382c02010541c00c10041d041c056440c00500701481181c2e01c44c001c0b0b507403600e038404020100054000304400541d00c3d410f403492110701c108115652580c407248000d458510b01e124a9000d4805c4620100b901d40c06440c00500f5a4580b000070350804510441900244c0030182c80c0c1800c0c483d50910200d0a92000e000f2842d038144421103050f034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 942252580 1250 942251330 942251353
    0xc12020a0c140f150306040f06080d11010615080a09150513020f150f030a06050d2f011d13020a09181109091506070c050306070809071e0b0c 62
    0x10718111503424a1040005044544841301890140d0350090001e5a0010780c64401003007507402025640c01442540c46401e10b00410542d02c0308000c5802c0c142180217100d040c2e5258207235502011001c0299002c640004002000c8203025448000700900800300946103240508140b4121a02034a035800d5015108040c2c1742582445007114070200c03001c0c5c41c6042c400b00041e0f00030b8124080c080742402c907c42c000010079103042da10742011025000c0100307405c140c40042d1401c9035500a4403503060500c00c00d2401c01d031421901c400710070421941c0603120311040d941404140c000d0b804d0031410f0302e46d009e080040d00940d0030659101805000005484514960b4107018000000c240070119014040d03082800042c400c900708000d80b8058002a01d00784a651150b094617400c81c0083c1010b240c1060010642d0800e1110b64411402110301c25800d41d40e49403501242100c46031400c40d48500503600100040104003400c03030784083d08000081c00201c2040d200e03a100307d82688200e1311159613900044404a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 942253830 1250 942252580 942252589
    0x1014010305060f0f160203090315161e050d200a0e0a12060207020a0e040b0103020a0b030402011e0516200d0507030201050901090b0c0a03031503030c12020a0c14 71
    0x20341007803c50a038881586080b0b1401044064001c00c0f03c41c404107545140841c030340c003c0007910510301e0002c05641001201d01d020144a0704120340c082c00210030400d0814410b03002d4154813050300d1030582ca281d45e141400005503084d42c400c0e0940b0300a150340f00803045190b903040e0709a5581e107106010007540c900c41000010715600800c500c25100c0c10b90150208a100c02c100d0003920308640c40000561641102e00014542d10055800702c184003901c80100f1041000604a49040e24400c40740c614500351207188010250108039802404280d40e2500751001e01440034100710000a10310700079140880c00703440c441038a800031008440d541e42103aa0210540c1140391112442d41095408191040c41a02c6640e41d0795400d01c00a0705000002500c852240d1042e06800050510303001e045984498480e0a42d0340c0d070840420a9001901c0c01400c0040315a20003424011a0b4156899001c00700f002c2e11b61000842c9000100e00540c8602040c10380010000405200203024950816650400410902 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 942255080 1250 942253830 942253843
    0x9170d050f070f081b090306040c1e030f15060512011d0f10021315020f0d080c0f2a07060e0102011b0c030e0402030c210105060703111014010305 64
    0x2801d200d0500d2815041d2030f031004981d6405940003040c0f45c0e206105d01c410072118070540000e04c0c1c150058008000a0000a2855608840c90b11074290200407840401c90341036902400003d00c0344400958680108525074915004001c0c0c020703001443c0c5540b00c0016a10039201a00200341d651a145401d41407421442d588082c1c00c000c0c0040c1191109400741140c42c0c10b0501d0102034441d81c0883c5038041c00a01d058108098541040880c045180199001c0d44d240d010b02c00004951140d0021040854840d0f2916401401e1341001d4508040c400c1c0101c04041d0480b0005141d00d0501c2c650078603a00301d070504c40080e02601100503201042c10240014018102001c9c1913040d03a0514031032001d84041200d0450700c60600e441c01c0590024a850202c1c3d001c0e02c000103d540c014004030900a1440c010b000070440c00c03407080c80c1460504601c150b0f101110400f48501540407405008110104e4010130118036042140c00c26588060381860003401113071011075000490307007501401402001000c1244 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 942256330 1250 942255080 942255091
    0x40b06031302060a020a0506010b071e3c1a01090c080403030e031201080615040b060f0f040f06030507033903020c0f0c2b020409170d050f 61
    0x20600e1841d20700003030440101c10440c000c1c0500c0300040c20740b5006100740100480c1d198130070300b500c00c156541e41e540100c6802400040e81e40d40c81a40780b041d40514010280b101d00c039400341c84c10107500d0001451203940a2603440582c00728100074118501c200c2d515944100c071a210348030700c81022540702d1038a5070315003050700940c8506107400b20522400d0b4000540d141d01c641c0c14a00451401841041039046004000305036480800c008000303d101a00400d0302072041d4118120181c01c50010340c10881500c07d1200a1500840700b048503070320300c2c0e2509000b49061075034152818a01b070785e41c00c0401d40d452704e103511400009a80d1414032a40382d0341030041d20780500c0c001c0c0c400c0340d8084a19100160411500082c0420703008402c9100b15903074003a4042d21040c2907510107444206c131501d1207141d2900c000542d81c0d8803400c41804442e00440d10721180c0700408400305001103400d0b500c2e6003840020080340d50184c0f5201620400484001031040040040e680000c401258038144801025241078021b080d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 942257580 1250 942256330 942256339
    0x1e09031b07090e0d0e061e0307030e0c010216151b0503041806080309040b031009060e0c010320070206271806030c0d080c07030b18070b1903140a0b040b 67
    0x2041489a44c4c00117001503030a0f42110803595960000601c06903071b030705c148000d940c082008800c102200350107910403004925800251403a40985100480c1c480c83d140e01003100c55010083c01740b20326154802c00c80ca0403a540d00f40490040200d00c004608030031091000c80305503000040600009034442a028401a04101c0c04d0110600b44080c1d10f40b80d001b840d8040c1c3c040ca9507840b01000c59501001842c03404140c06604000144140c1090400f6003502a48607806100d40445203000e9403191042c0b1050a880308040c03100000040c441e04201d42c803d440c00c0c3da001d0000e10034480c805d1020940c442c048080013149014200c441411b0041c00c5101c0e04ea03502030310400c081001002e03103000c20721404240303003101c48682010146c5014030107402a0f040010091052180100401a45046e10f40c028840d081034210300c0c1d00c4018541d90703203514602440b180c03d0804c2c000380040d10403a130b0740e06c00c0e095910b08010038090003603610503a81070390403508018481e84843c4441030a0030184034400c50803100b40e6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 942258830 1250 942257580 942257593
    0x15270b04080f0f06190c02100e0f0c15030f04050a02090c0406080709050a0b070309080d02010b011106090a1101030e0111030709050a030503090d170f0711091e09031b07090e 76
    0x50172240602c44802c12050517141d84403605500d1090003040741940c104581045004000c1007510350700d01c14524560712a00c695a001a11442e00c840300100384c0c1c01e0808507500e10341d1fa000ca4141105000382041303881c0d22a0303207002d900503a51000e416204d01201f200443d22a85020b000070300400e80501080c06011440000380b100303072036a508070304c1560084d50409540f00111f14084075000c44c030ba4000f007030a000b990000d11059a064022440c138040980e81d038001800010b00ba20f440f210107480c2d808503030b8050b040c910001400188180e001ca201410001030400008010301d0945580f648241041000001040f000980022016000d031406442045010382103641c0c0c07039603d22501c0d2200348501401117841c0108403901451124051a62981c65100c2021440451203131b00070f11802c55003501d03d2001441c031402d16006042c4241d5640c0c050010306410050780c0300c1c2c0601c002d8040780180c0401c21080900d4007500300c0c920420182c803070040000f10b00d4100604111103145e0544e4005800c040b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 942260080 1250 942258830 942258841
    0x160615211a10093303060510080613020f060a0e150f1213051b040b040905030909070905120304030219180e070906090209040615270b04080f0f06 64
    0x80e03080500f03455a80e40005078450742442c940c050481001181e22103004040410300e41c4030124141c650440f40319180038030080d200c0c1e499030502000b290150040390b902c80000038889100760070b600c1661030b0024001882601e00d481c0401c00c90f034018016040400c0d109241c2c2280c03030a1034032448200b801581901380c02d0a120350340040c41c1c0c0c404c4150b983e443c0c50b080e1020400101001180c10719403035000c01200c41381c00786511880c5002d002d60010610407880c10000d052079083c54041c0d095107960082c0554981110001006026200603224000300f2205580100c0c040d00d03140e0400a00100c524000c60f00c1da451441000074403041c1c222110f032603400f04881000188d02c1d00c1c2e0640c01e0350003178010109888000103405440c3c070f641d07507001c03013841c3e418014000b03502041d0b035000700000a02a102402032948582107110442c814031030210000c4c203817104400058070545110300700c004c0102e8100040d550340f410481016005600449500d810070b00d0590845002040b81d4441041c230702c006000c0303a1826 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 942261330 1250 942260080 942260101
    0x21507050601321c1a010b040e010315060504050934060f0c06021c1808040519080703110a0f06050a08040602131e060302160615211a 59
    0x11608405150103c140a840c0e1035444a07640340d40004e00c0314600c0d01c1404103043c60b940101c50310025010803000d030310000c14044c0c901c2040340c003035881a2259404d241d2079130f981c8031034500c1c0940c1003507030320780d0340e004040b9041c3e549000d40390048204200400340f14406420110100c2040d070341102501003602d055008400440700b62104582e01c506080c0744000078034601380c40c1c0c1064180c0c01407101d4400104a40c101460b008040f1003907000301402c00000000700b01c0f2302e1002410030f030040c089800c00d1108100524040b219034000b034844280140300075984401c05858208943c100702c501c503010180ca25224100b82800c4802008490060703005545020b1015010784138081e580020020390740e000605001c5a6011580d01040c8030b4405400030350b94a015000f141cac2461160f50000741e8004000401521030f0080e200d583c842d103a0102c00c4001980da800c0010604120302c0c5080d14403001000860005415040c4e540c030790551503240c0341c6e4180d413425669001c40e0828006c8403845850620545010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 942262580 1250 942261330 942261389
    0x220e160311040e030d02032d190507030f02030f042a120201112b0306240c05062401050c03091306080708100606050a12050c0403021507050601 63
    0x500b51000034041840c100c005086224201d400d80c80d41d4000400d2003841074600301084107600320801201000c4166046602d2190350682c4c0404202d140c1004100000020760301064100361a418005058013070b4007281d106a810071586402034a5000c4200030501c40189050100001c100ba241a03e0b0b411800481005000500884440c8140104100c0c1103900a841c001085031a2000700c440144082c00a09406c01164103009003e141c2c240003101c500f8002d0054505031085543c01a0039544082a0040da20200e285207400708032841c8450760201d01c040c4134190040e44a19240000210003150340240d01c07091095180c1000350411510302481d030013100382e410340c02040710761051a03503440c24044054100d541207010305028661001039402d1f00002c00240c200c1124400f442a19541d8106036203500442401c4c02c081b414000d8140310341440e5910140d0300800d0891440d013003d0726500466a8600d13800300f1100700c1c3d240010081b092000800819004001940d200782020244d0807500140d41c0703 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 942263830 1250 942262580 942262613
    0x80a060f0b01050c1b130504150e030a090b0c011103090304090b3c1507020117130f0305190c0201020606040606201507030203010317070503070809220e1603 69
    0xc1e03400d0a10399142e9519102564040c14004080c001802c0c9270421042645500c1c80d8072516a2515014613013150001c42540c000341c0301ea444600e00207251044103a46a0f11665060380d955599200080804200901560059040c05c004540b80c81c1401d9441003101e8403002461311529015403118000800ba007491019280c44581c1c0352400450021074103621040e8039000e82d4132100110811103508417400140910750300036a606075007060015450300c12640c05440700c7c009000c8181030680400d900c2030304d00701818400c0c40c00c3c6203400010080c10116481d03410600c07000031051800d100556904010344c582100b82120100045407a02c50064000c0c103001e04e007604e070350140d410124803142043c80800240410b400740b00b2111300c2c1581e8020300035402404200d410502414041403108113000650b06280da0000081d8034050041e2100ca05c542c1041019640c081140078282d42d2003100000c054012040d201d0700400c800b40441d420703a0421070080c42006003512600d00c200046440c154000400c3c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 942265080 1250 942263830 942263863
    0x10090203162d0e0414060303030c0a0507061a0a090c08160e180906010b07050303071d0d05060403080c070c0b03040318140108070f02100e0304080a060f0b01050c 71
    0x45405400740140300b03000d20b5400c005804100c030840142c0e9004071116003100d004079010003060312822040c43c40480c080d2102e80e010ba1060002800c0b90f40c1c084000c2c50040b10301e00780b0301d052010f01d6440600707a0b00300084450700c00b0251240e0030640d0810210100151002201c00d11040e040c051005100e074200900c00c0c85c54074090314109101d076001d09402480080040c1944000c151904070b81005084140d900302500c1c420203000140c0742509005494801c0d0340400130b18070b1a120b20004580c0002480c130b02c03643e111804070300c86607580e6405009101c0e00b4400d50140c00c0519141c2006080b0301002007400703940620030803d0000090b45440c0040586d03009a81c10b50f11307601e81e4103040300c4610610000003041c100b0b4540210341c00030148480e4118a200366104061580c0d1100c0481d0300d1500b0f010306a004d81d1246003160b010600a40010044035410002c0342d04050742d55401c540340c410620415500355682c0c0071410a284414006c0116451003828228541040700002c90b564800814064605 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 942266187 1107 942265080 942265097
    0x705040605010c110307090e06040510150b1c02040f0f0501090501120509010b1e010315053012030702010b120304090902010c06141009020316 63
    0x2524410380d1841d080700041d0f51404c00c0340346810100340e45400f0304c100109211001d4401c0d85890f031181d100030082420b26042c000c1c201001d00000d01e10b040c1c20514001001411070012404540d0104606580c0d46484880b001c684d140d1803d06103c3c42d800080e0006034980c011400340c2c05d45040d0300d00112140d503100015242c8400e1845a2404503c8160096900c44c3c1540c4c40756910040c05000402c510903400c0014001001b040300b400b0162880b6902000c19503403601c6201c00318045080405109030400c400101d04904001c0c0482510954010f580c10a0246110205505031000e0445040b11040f18078060070340c10407141d460041d8603103150f2140e0340c602a0700d000800d101803030245250604040030300c00075040881c4180d0600803158402d20000d9124403520300e000c95501030f808150f04000840590340c481d29401040854014400d011008403041c000c07030034000150405069 = true := by decide +kernel

theorem cover : BRFrame.Cov 942086330 942266187 := by
  have h0 := BRFrame.cov_init 942086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 942086330 ≤ n) (h2 : n < 942266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
