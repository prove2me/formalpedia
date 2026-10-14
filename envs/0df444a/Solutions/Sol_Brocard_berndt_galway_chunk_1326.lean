-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1326
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:23:21.627639+00:00
-- url     : https://prove2.me/submissions/d59b773c-03dd-4286-b70d-fc0942030229

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 238309352 ≤ n < 238489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 238310602 1250 238309352 238309373
    0x1003060209150f0301030302070b1201182306041a0a03020d020409080301060c0c06260406020f04030303050a0b1f03021305040c0e1002010605060703051b250807180207 74
    0x1c0b00e40b000c2010807a580010039900041d070482e0711940132140c1c0300e03588003a0b007030f031031300440070500300499048004200c14100301c05c20f0342c00c0c0348503460002044040303500c0c0300310101c205000d50703540382482e4400c0004604051003500c90818201861291043d02040025540e130740c58000240221000202c200840d2035a8004a1286ea406609582c803907841e09001450324078240c0042e00c150b10322800029081c2d0240c03130324070000c100c02440100d00142c0007000891041c8090f1044410030780c200040220a941c500142024500c00d640209081c10114884000e6604d542d5403244510030302c0b010704000015801d079001b0b0030b01e02400d01503201c0c40b080200c01010140c03a40000c1d00305051010314149143c0c0111100381075041120081c4800c4821041242200e510b4018590401c400b0032040000c41d0180002c2c2402d0524650302d15801d105240c0d07442c0c242040c442d4035038040a0b0483d074114400c004440f0380c901070300e820340c020144180b422840300c0c4c03568860b4140101c0030703500161040c1809625440d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 238311852 1250 238310602 238310629
    0x303050c030702270105060304082506050a0c0207081b0108070e0402030f0403080a0606021906060f0e04120806010f03050c0702030a11030c0411070b220f060507081003060209 77
    0xb4a00080100103407900f01140d420002101e10314501300114040c07410605507400741d508044070b2401c00380410002c424540d41c80d51402216240050000001650341c00b4042c880e0310002400b080140503004080d181401a030421803907500580c2001d0044001942c83d156241024030b4a603805449101c005d4070140310504035280c00c240008100700e20003c04041083c0120b20a0750b5043c41503503192115011240103002d8840180c100d40c4a0424a500183c0c490f01e181d400341304005507035030380e80c101201caa100300c0d80130b00544506582008180480d41c02e2041d544815030070a12002c0c9410030008264458002281e41496502c0d0f000c501105ca2100640d508194094100c1340c0321319590424625421841c03600a200317204401500c005c030f0425000f40c04070020b68444460414415585070480302c04014555050380c6000c0120106c400c41000501080901490842d00c100c2910300708007055450082050042c003010000340a03150746500e810004407600301c1801030f11440c0f80360001e1070004802d00c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 238313102 1250 238311852 238311859
    0xb031605090111010905061b0309120901020102120405010c02060108070b0a0513080d0e0901080118021e03062806150e1513140301090f060e0a290604060f0303050c030702 75
    0xc00c617002c000d40002c440d03004940084070101d045000001a5115220403244d809254001d1000314440002107000b0b0716000c0c3c0140009802e0400302c8071018002c0b20304650554260f911001004000750301841003901501407500030300350721420440e100019105107120b078010441c0008104050b2200c0032081d01c040c040303940c195840a180d4040c0180304051858800b803150042900003e01018144207904043c0903540b450001901c040c5c08000a2404070078000800c0c1c4032101e040c5000f0fa4062020602c100b01080341c145d6000c2d0444109040d135042c0e00c034400e01c2186008028040c1c00350304080852501c5043c40c00d40d006500100204900715030b4a50701800420b0041800303080d09c01d0410900c0281c07101801d1444840c075500301014240d8615401c0541074001401d11180411444d4101c911140c8840040342e44400017540c800100010100000303038030081101c0002030201da007030074183e0090b000701c80900142c0e04203440581c121460703101c01014484001510702c2b1283d42271050781d90240e0000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 238314352 1250 238313102 238313111
    0xf02070b0c030a030b0f0a03030c0606030c060c06050907030218040203010905011b1202090907050c0309030303160315050310020c07050d030c0224070609060e01051f0b03160509011101 81
    0x403007085989410092540012a0810703d40c91020b00305200411862000244260f40d1145941c40946080305000000d4400903101c00c008004100c6045c03450f0010a21aa101c5858800600b050001c6820280550742c8541000f18208007599804501030025040144446413a4a03588000f900400560000404c15402c1c15003222121440051000c580442501c0c2c0e0203042907044e19103c100e10661514541c800041004150603074418005402c124000c07004803031a0854800010345150000c58044041801030401394102d0f035890302820006400c1c0e21304400e5005d08210010383c50310b10388003030300c1021540400c040c43c000c00204102d070010305020701101452140307030400400c01484404268024641c00c5c1e80340e8110440c1e030300801140c0d0484081c00e0704203516941c5000260101c01000d46007603440c3d00c072115001c1c01c28842c0600540381d10341c20341c160403960881140358188541c00450412001d004004541c4030b01840f04090300031514140c4c0e1b5410701517005031804c00805105494660ae003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 238315602 1250 238314352 238314367
    0x210209071e020d0e0409170a050d09050304240f05090406030b040c080105010806010b0a051602210105101a210a05010f050603060f0405090304050d240b01020604030f02070b 76
    0x11071400b200300055910104c0d0200c403c801e01054070101200104520a12002d5140101000c0b000c1d0900041c1c500d0070f01d143c0500c1c441d8071400d45940080075605074000080401405052100e98203c00160105540b005015200d0141c2501303250740650042c418006603d242075030300c940c00301003d942c0c000c907840c80074102410000404800c9004141d45980b800c030003c194107500180c417078109c0382c1318045245080c060000441d01c0303030007810800c1c02070016284074500603690302c102080d4813040403a241401c220fa079580a03003962800703000c400ca10b480c07204060000141c6008025203024858150665400724110380e40103104400320b05844c441c0c054018410351903110303046581240e81d03242003014015214410031280d0f208c142d400ca640b15441d900c00c2c9019040a801c01d5a018001c01c0c1500e080596510104800b00784d6110103c03040101d0124031302c904000f00d169245610703040b410406ca50600c810000c3d44d00d220160010303041c4440240d041d000903108201e0480a1700004220640345c009 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 238316852 1250 238315602 238315607
    0x9080d05060a08100e19050733030213061d0105070203030d06032a0b090d140d02030d0e0303040803011205030702040c05030f06030d080106120617070609210209071e 73
    0xc941c820b00996018a00d42c01d031351840003c80c1d403404641c01002904050340341c4030310500f10f012440503101c64444403000c4141004440c2c0d6042901c1b0000cad84015a452000051411420f09281c01c5242400440c0c08580d20000a680342e05001940c00c1c2041d41c0d07a100180006451409690406e1810508244000c806c100d00324200089401407080025012100d01a030801040454054140449401d0090400310b00d08855114266030003080140640b5984140781400e14103030010704005a44001448104402d0f070340328207030750103820758042c50460a05070b4605200784030620844160340c5043c8144024400180111000c5030b6004008004140c1c10020103041d541048564010140042d03001800e40c1c1808102001c100109607038440035a82406010395260308000030b1400c47c95903510010605084000d0310701d41d0000100c0003403880d20300e090801440b010594200c41089204907000040008803440d0b00c508440d4111074884407541c960104607007041c00d12a004000b01c031919510014140c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 238318102 1250 238316852 238316861
    0x11502031b070e13030806100302090a0311150306090106050702030312010914090a02030d031d0604050a110307150c060f0f061a0c0a23060a0506100309080d05060a0810 74
    0x81c2041e460325044c0d0344d09940380035580140070014001c108042c0c002000d41c0740412900d60700744402d05006042c100040c011600c0d20f41e254004842c417003411040c4051514140c0c0b0100c0a0108140d100c40c030714a04080401c3c040301c0c0c103210f81418060007003804403c40d54244103441c1820001d0400c81200d40c0d5a44e8004060b00040850005002036080131410001011410500c4544c002c0c00400d00c240185801310f0042030703c0e00c050321904036007000b03000807508140800341c061401580181960441410443d00b45c45010018a120740d1104004000002c0034001c0c20742c010396507040c54140481c0a003003140c007405041c4249982c003450000d01640105155008400340d44103490100001000345d80000c100d8458004494603640c4074604c500c0008403045078914880e2520b04011070201c4420030042e182070703c00c0c0c502811850700c0c1c0c002c0195a040c100344803034519500707282c1405002642c0d140d0107080c1c800c50b820314201d540c84000007604c03900d40d18000001809914200c4200302c0260003190f0040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 238319352 1250 238318102 238318109
    0x1d1503150f06160209100f0801020304050c0a0602120a02152d060609060304170705061e040803180f030c01150b091804060908030406050118050f011502031b07 70
    0x1402a01290003007420940203480f0890b0000c0301d6a4040310f034903020402085030050010440b451100c0300890030000024482c0000d100d03100001d61241842c0c9412824010072809050040c6440081000150703400036050005529080c401c0c0d507500f04444080381400c01d9030a02a040c0c00103181400044640b00803031403a403032210704041d070b04600c0210350b0180080b030581c2c00680c0a401440001c4cd9843d00c8001150054440c805049200c0116a40c1e04a21382003414183d5054002200f0084690765400882007030b03058807030b28140c2e00e19155a490320107020162080726245040806020498000c00948005010240450341c84170100403a0b2030280008028014601c8075500b0006002031000d0103445007040010711440f60517460491800721040b00900c20b48005494016200100e03008030003d5000380c4c014440820658113086003911140d11140408008030702d89010400481202c3c0441070556002d85200c1c0103010660b407080380f079400b40f074031103086504078030f09010492200084c070b48003113 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 238320602 1250 238319352 238319359
    0x130302010f0c091a040e0103030908150402060a1d090c040f080a05071202031905030304020a080a02010e0108070c05070b0301050109050a0807030f020d060c080103060b0a05011d150315 81
    0x5070800403080c0c0c05540c1d044028401041c2d0700d4074240845100104800f103100080da044909007540c4000410a0100030307070068020400010f4140701c2d088040c040180340c1140204000701604141c2e011a603688500c4e00d01c0002c0018a54083c4000e401c2c106034020010001406448507051840744d46009a1191048195240c0180c1c8005068040820242203154100000d80442403400d50303222080001104201c1e814001c445031280442e01e0b02d044043c1c0b0038080c000450f12482c0c90310510803034030595004800070342c4c0702c100700c140181e07841507185105810030b00e4000ca890300c400805440d240901c500041c424005c1100c045111140c6801550490742c0990b102c0c448a0790f80c10500c15818518080c1003000d8105480900104494103e1480050320181c1110002c0300d481d240c0d201280e1080140c2c0e0002011800100240700c50740c040c20746119070880724501150310301000039208d85000381c1c2c000a0b09003600c41c4088203981d0b041e40350106c04a80f80000c1e81c1ca01e04809140708001104200520 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 238321852 1250 238320602 238320611
    0x20301021b160305071217070309030203060106080c160302071205010504060b180406150906060c0c140604061b1a07110303010b0d0506040605121e030a05030c0705070e13030201 78
    0x40b014109503a5030403690040050711240e41480b2501480c2c80d004e040c147e0301c0c440304000b03145c120002c43c00244041801790340d96155050442c410503081940690024007003104400134880501810341c216800d040c03014482603009082c3d450180d04001c43c607440082c03131540c02c6041206001041d00071034402d074421002001002032031410001c2032102d051800ca540c842200c0044c000031080e13807020442c0c00e040e401070450665907200d0141a10441d4102c0c1002980380c45480c001c0051800c09500500070003408035000000e400081405400b443c400c810800c91020741040441e5945c2c42024031180d00012181c40b008422445000b031004152031090004880b03210b1905011b40200541c1c1c1a00c280790006840c28241c050190080e000140526500c00d64510001400e07580382c0c80a41080c1ca8040b0190603240c400c01054400d69560180c903402a8008010100b1816408000c1301c3c3c0c450300790305207942c440b0703a1802c2c01494003c003500800d0002c800b140a01818000f4009405c07040b030701c203900038030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 238323102 1250 238321852 238321873
    0xd0c0b06030706211509140a0b221e0606110604020109030204052206051506090603010306020a1110062310080702012c0d050307020c060313020301021b 67
    0x56442c08548921000180c51411405030b6089500a13452143d48003040451000811034220035020216400014803a6a41c1c414160b0551200c4945078040c250080810007458500d000c5144074112200203031020104100301103400b0020307880143c0102c0110a42400c00801208000050105000d0840031602c590041c8d8050751000802501c5164183e581000d19032070340c4c0c288400751501904521007d0b44103480761991a02285103400303418040c0d01c1c04191810714044850104c0480c00711140a23001c2001102c2d401d48030842220b0449601c032000503074490390407008940080e156840c440090290321250000c50083d03800440c00d03910b40f0b0482140c400614183d14080c29103e000481e08004011100c0340c03a43d002c0e13115194003082070b00000c02c1e0029050500052500c80244404009000701240740c5500c104200c800d03070040190411519506010001031b556185010042c1e11900002001031498015006c00c144c0240d409002503407596182701d4040b0307200c001c1d8103e241851180d801401c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 238324352 1250 238323102 238323109
    0x80703060c020705150f16050604030215090f070e0a090804060804150e150a0b0a0603060311010503010807090b0114030a05060427110402070c03050a120503010e18070302030d0c0b06 80
    0x80e2415141010303252601841c1b402075101034011210035101152002d95010103d5018800240f0a0303220364060b214400034491420110030000d040300f840c0364800e4008209007000020208152401ca2415004079565441070b01c0240c110250010b00e403a0000c10005a0302c1d820400030360140740310306034180a0590900c2d20200b211200545250154001030000c219080004c03206504420001000314441a200c00414002403466000c81d00103650383c03070304000f884084007000074808000d00e4024555450110660f40e201018042c42c1003003540c60310103000c2a0301842030a6003500c85406c002c0d07104e2822801c10401002c9c00c4820718001c2d420100701000004c80000002e0b040341e020141141e1401c040e46405603400da2880a85030042c0d0f00b005000b004c01c0210090b40300a522031001448a8042d5281220422100007504410b200d41800184010111069120340c440801c41001c0c1d0103001091100703181003480c2d80069014002c0c05a02400c807035000d403070f901045000300b54001c016100e02090 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 238325602 1250 238324352 238324369
    0x20a1d070914060d090c0e0c0a03061a09100207090c0f0f0309080a0509040603020a0905070f08010e0103030c0813080303270607110304090c120e2e06080703060c020705 74
    0x2e96000b4410020220000041e44c0413812690084014440315500c980c881078407000281e50081c01450301040304010980c1c140922009012103d910207003428080350b000d1041d00404032040e00c103101480711148102e208022500c0102800030301030040300c4042d000174000310011507100c4002220031508074045030180c0030351a08194000c401c2890212001000c542da070b0000400c00c0e5105407101000000350303032074810850107400107a50001c0d4078104a070028140150111848003408001c01c01004041450030603035044980500340301c0312680c82460071007507510400042e14121809048080340004001014500c00d11455052054000b00410035600f219a20f4074402d810381e1000c0001241288030340c903012207004000080381e0506440301101c1040c0c07401d2481304000103074031441c030503424461806211214000c0c5000b43c007130310112120300c88201c0c07a41203980b2109059452000d0b1104010740c4500c00621400d02554030350360303d900e09100580301d9800c66100500c1400c001041601d4000030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 238326852 1250 238325602 238325639
    0xb060f1603030b1f0807020304080f071d0f07050708090d0302011506050f0306040e010603080f120114031e16120215040503030d0b03100c05030603060c03060f0d020a1d0709 76
    0x1120700510752190b0f04440c02c00f001002e0501f140400e10001071034040800070b6650f540018000b81000345d0520400d0540c00384a100395403903180c0c180c0c0c107100c180307260001c245402410610300690b4401940c2000c9016105041803660014207225103681072590661103080e4480700c040d081c1c61704556410301103605010301d1810a003000002c2004c500c0914065001c0066881800c0010414a940352034000361600441c100003101d120000e00200145190200e050150803d00700034203d0000e44c00210380c1e551140100d41051010300880d44694120400035240161001c030000540c050712071545030310705042c03541c0490049402c441184036071000c9109030740c16200701600442c103000001e005040641035901540f5050700a810000031058541e00411504a00326219190f40303082c40300900d407408200600f18241c0c11401d00500000e0b55a00c140c0d2540344008941110701d071a0580005101d00c007503a4000113684208000749500e184e81c40300424441c1d56503840e41d018596448000d030050429400c03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 238328102 1250 238326852 238326889
    0x812090f070522020f040e070302040b0703050a0c21030b06070b0601121506030516030509100213090e010b0117010f0303050a02031b03090a080316060b060f1603030b 73
    0x88060102d0300705540b0b00c11a4400c1c1120450a04003401d0b040c204a910180c1c5200c1e00a00010741032010030341d44543c054022046140441c6040d00d0009a9542c50003950300003802c2120008075041800c0c8140381c48811580c00c0b00086407120100000010440d4410f0070074800700342402c81102003031600c0019a06255041640004556551030045034844101e1140040d0b080c1c0c1d4903020300148413507003050303406000c0c59140051207082c620312480c04010481240400c050801e8200250568081229a4014030311280075894a02040c000580002d45030002c414030380c0340880001c080841500000e01d019400e8a80d03820031101e1155010403d4000d000f44110b444013402c08200080c403075001070401c01020700c152820700b0386100e4014a494010481460150300c0841c400c02c135844c201241340e00820303065004500c1c100094104000303164800c40042d010550351003c06203251142011503650041410209039900001908040115800c110a400181c07402030460040d06090320300c208a0003c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 238329352 1250 238328102 238328113
    0x308030106110f010e06060f040c120507030e01020309060a061a0910090e040b0402040f0e0606040218030a06020d0c0503010620010608030d0203040b0709180e07030b040812090f 78
    0x180701036030703140d0940030a1040c501c254010441050420320480e40e0f02c00740b032000f800c00380c00c0180401980510100086100303900d0000d0103114540c01c01c00f98a00d0402501011070700342e031660380590081c50160001103043d4000010080a18000b1402c1440707410440d00400815444001641c440359100d50701c0c05010340100074002a620384101405001402844c11451070b81d166a00101e52990039030b0200c031400318070800c0c13004620b0705024980940e118081c0400240348c0d00601182d40d0307034000d06070790300079580007a580440c003e40c0c0c010f0380003c040c0682294015411464100000e6000204004000d854450301b80c070000e00c00d0044a0403905c180e512003600c81040c607012171184026040d0003415650710300c000126448248040c0c828071003010001078591401c1e007020b0501c128010031040070048401d1003845070682c032801804010030940740c002041c2c0c0c05442047d02d0911150030240079041d00c081000b0420075140b00130500d4444403607000000fa1610384005075102c4072002600e0b07080e00007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 238330602 1250 238329352 238329359
    0x9190308070c151803121a220e0601060e010c0c0b09031e0a020910121403040906150f020c1f05190503011d0402060a030b0607050d0905040609050103080301 69
    0x2079644074041400383c00007003c2e4100c100c03a01c0085501440100e40c51800440340c0070f05258101000c1d00c1800507250b0305210f2139600300424010303c280501e003248501d00316111460340b1b0020300100d0805064581040220fa0788510b1019600c14092040030009080341c0c110f5885940710310b041241c95640281d0124141c0e05003289428560428660b842c1c1501c542143d4070700b03800300520010300c4120072002900c0201341e80d0042c030081c000700070400079580300a41e90820003c02c5407042c0c0110315801c451440000c54203026400d0640c4950350004a00c1c43c20440c0100b070203032560040b06c80649841d1034001d45e040c03001304203a0303c071a0b006440c00d0340710081c8081207140348013003002c01c4481012490224644900e410b68008104101d018023000200c012005204808150003074800440500341aa8040c0c58164002400c620820703618900300760b111045204940c480c00e081d0340040d50b12809445000d68030311001003404800b80b15080c0b286040c01c1000400f14594415181030341d81018009141d68213 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 238331852 1250 238330602 238330607
    0x170a080901082e18060b1608071709010f230904060b12040203010e120906070c05030d0309050105012903060f090405070e06100c020d080c01020705060919030807 71
    0x900904450400502404001400201195800030244001c4061048504107a03418040080040907084c18600d44082030017008540c0064410050f01404070040c060002d14045240d8001e422008045025201c9425900c0300c000000d0703c8801c1c402c0e41c56800750304010785c0454481c25040b1400300d42602c0c1c3c040070131540030070300c0082c1103881000e0800304020341c1e100c500110b190712102003600d03e070050780180401c40c60203004103002554600c00820b080b03c0c0354901e28802c1d20440f040d01c0d115400c005441010800010101002401c0041c2620001501007102138050600d80340102c070350307510b02170000c0741140c0c0441500e441002c106130b50603841e03500e80c404001103910140186510010340d8240941a550f4550f001344500c0c4035001502003549410003030082000050003541c401c0f0700b05c150039000a9800b5000180490b01110744280312050b505004559100307144906040d540005038260034008001111401164460704440c2180c02d02c81b42c1d9034004c0300d00c81d80140003c010301c0118407441e1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 238333102 1250 238331852 238331867
    0x105130b06130e030d0204090608010e0316050c130e0106090e0c15040512030d0b030c151c0c0507020114030403020d080a0b0d111c120c03170907170a080901 69
    0x50002c0c10000d0b100c0300140032540b4540102408100f415000102881854254001c210081032040300a000d80750328008026183c1c0030f6101004210001c0e0300c087d4060241c2004050103640000d02862200c19a800c4030074050544003c08241c95070074004005510101c41c400c4161020503040a03240001c070060070490303040001403214400400034000810342d99502c000c05404030301e441c0000c6549030b00a603508001e503070484103414400e8028140b0704c06a6143d00c0107148813155003110301c550320f0402001d010500040da02810002d14505201102c100b41c01c60010080607000340c80d619100f541060310203240c0d100460700140141c00844135040c006010b4400c00380c1200b0700e0003020034100d1011010640089484005a0394450010020015404c3c061780030700880400c6948443d1b8084d06848814640d40113552510420070b004d58064141032244007941003484004800d6a01400c00c0c1c030016a94032040c0c09000ca00d81d0000d0711031003100070001281c0c170906034001ca500b420300c00480019100031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 238334352 1250 238333102 238333129
    0x901050a060e010309021008090715050306010c261806070f110d052a030604051209040b0913030806010c0b0a050601050c0109030f0206060d0c0306020a1407140105130b06 75
    0x245d194a144801031fa600410080c481c41c450703443c103040d86043e0340c85e20300e004503a0340010b03501c140030018007900c40d91240880e940f200702802d1403418030b0000d180c0040110303143d01400c803244c4c499900a249140821008102803030160300d4441c1d02220000401519100e141402018904240031140002c1c0d03d842e104030712039038021301c000d41c0398007940c4038142003800b0600c100c020380404480d5403602c0101d000d1814909881a0000c2105150076900e00399580d441014284100a0200302c8407110354561304020204200900f0315840c6090000c0c8001107440041022804241e611000604552107030700c4200e500b50304a100d034802d6441d510100b1000780806000c95040100400860041100074043c0c600414403994400c0c0c0c80300030004000b070030014041c101c41e11514688002d8000305e1020344841043c2c940100f801a9140000c52007642c40350052041c40801040100d203100c2482080751a10740c0c0c589959009008582e1090004e6150000341d40009000e0840c8501043d03090070302001d5640da0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 238335602 1250 238334352 238334357
    0x3060d0804030209161205040b0f090c1e09010b031b0304020f06031801140105100e03031b061b160f24061a030103050d0c0312020406080103110901050a060e01 70
    0x610703482e5004074101d541c044480582c00d04141c8207400c0c240d980100c0c046c8044611000801190a10740c2d215400018040e02e01410344001c200800c0b03003080c0a00020300302e054003c0129140c201042c0c11403240903c072035001c520030144400005601e001140490f4800c0301482060411075509084040da2500050000e80e000200c0144401c001e03114000198028480303100c00000c00b0100410071400d403103510b10102e81e030100c4900100701646841c00d4001d40d00b0103500b07041d00188005c0011926501035203019084800003c403e03040140c1c00403888074018502400608040081c80d102c103140c510070b5651104800c0f0b1030000800100e1842044100301034400c40001c049091840f0355034042e1740d13900d0000080e40e41c1d600c0c800c101030741c0c02240d80384582c5030000b01c032411580b6680b030b41900ca51004101c4024402611701240405226807010380744030b501d0078011501c43d41c6500004084003400d00045072503207140034442c1ca4900c5c0050b0b00f103049420061218003014200b041c01c8a4101802d81203606 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 238336852 1250 238335602 238335607
    0xa05090a020d050c030a11031c050a0c06090203070b19050f1b01090b0c0901020706030e07090902060c0304030c05152b020903031606050f1303050a090b0c010902010e01020102040b03060d08 83
    0xe54080c1b19a8011901400110107404034001c01c00d42802e02072030380c1d208000007c814160383d8581190a0f50320001c02401c1071605c12000d0306080e8043d051441000307506025203400454100100c802800d508504c4c0f0706110040f411049041c0c0d0300e03104020300c9840e0f6800074001c010b0400002201c840b508aa0b40e000802d80017410f68403081c210314103640304a0064004100700c400d55034100034210080c0b03010b1809000060916081d1520760049010380356940703854003c903e040d0f444960495030141c2909e41260354940c0c0d40c2c1409a0848541c1c01007502c619406a402d41c2d610740c0500580e11800111010b211403030200511a2086240842001440725000d001c52081d42d581030016001e8844d840f94481c8140e0ba0b24580b51080700c90040032030000c00281002d1250004404402e18115580f50620710f5030f80703000c1042500d000104e0790200846e0040001c80701040341d03042d04000440c510030780380d085c2e881e40250010f80c00e0340070714025410030359010b0002600c1ba02c6d000c00b207403d0080c0582501c61 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 238338102 1250 238336852 238336873
    0x1c090504051801020a091406090939030906010e06090a0b03100903030b03010c030509100209031e0d020f0106081908160b220c15030e0715080a05090a020d05 69
    0x1803d9802040c80900406d000300e90400c40c0b4508000754100455045070818600481c1e08000741459401800e041b401019041401c2910600880b94140c10085250f4003238208605203201581c075441160b10441500401d000002c076401244038103409010002c008400c550384804a00703000f403030341c94040c40c1e061188090004e031403081c1d48500c02c0d0241c000d903401314440c02a102450b00b0764030081c0051042615040400c640200c01107000030f0f80e82407009015959100c0c1000081c540062007083c000205c00300320090010b5440090160000b100315000e80da241d2380c4050b0308500303c50041c031500e11107420010805c85240c042004d0074072040e100b840164100b03604103204000018080008072502464103040c841006507040d4112400d000c0032200c2030078500d95683d081f01c4440b41c4d00c250900c1b04a402282d1002502a400003040c0d00d440f4421509010341d5444109422070610b180500420311160104441c8a060300800d0b00c6110a01c006240340c91290303082c06030003962003400b611075000f000046c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 238339352 1250 238338102 238338151
    0xb0315030a0c082104080715090911070614040c0501030b1804050d020615030307081614100c0e030712030504030b0a05010f0504022a1002030a0e1c09050405 69
    0x82010f80781c444002c1222040c0c030740c2010008501a025842c101070107002c2040f400100103034450684007145000841c5c40031600c01a111600300b50404e40d41d580c01c4c01d506d250303201d02d024068072030b9600683c0d05201c68100c0411010340500c1c10789002e8001187c0300001e0102c2d5010390131202100708041e280324044880e12110b034207000c0c004c0d50708a9564200502500e03d50380e040110035000701c008003040381103030801c4000a0303580c440e1007001000b5a6020030500080001e04095885e05504071800039500f2500511280c0c8924a240c0d0f08801c451608112000036841801c80b40ca1400e40600240155414403000045e9064140012003c00c541040b000c0000fa190b0b00380240039882c60340740482c82d541080f406000b8030455030490f81c000d510500881040c03400300311084012030400d4000c2c0741101080d4420901301000458400c160a0001046c44140d000030f6210384e0f02100e4400c00d55005100510904584140040c6210002070a0780c805001a2070f0a40c0129013212200c4805500703815082c010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 238340602 1250 238339352 238339373
    0x7020709110a170c04060e040209030d021c050c0601170109050d0906090b030f0708070201200d050c040303080417070209011701420504060b03040507050a0b0315030a 73
    0x400c030808404210b01040540100400f808031a010400070300ba480c02c803251a5044c000c6101e01d500300011a000c04801d42c03510b0b8100c91040700041c054a09503804844060343c4c80c43d00d022481490518500911003052240707081e94154800440a1303d05a440d026001016501d05134034180a5542da801c0f400c005041040b54150405907501c62140403407503c076000c1c007520b41e56031000b09400c60400070014000755000e48150f1141c0c1c40d040200305901e40040807030040c8202454101d014156002900840c403026010740456100e209090015503503421010140740200d1000401042500000c58001100c0c0d145181c241550104c0301400c040858000954040d02a406044d9144000140c01c1704900203009030700f5401c00798080440c0c01003169078480d6801c42d100700b00c403883d892031805041140180e00110002024000d0050141a0300c60701d51102e01d078000d41301103586208114002650f400d200040308200c035400c1103414117650380d04803690304d032601d44103526500d4001d10206000140e030360b8030b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 238341852 1250 238340602 238340621
    0xc040204031a010506162604090204140d121d1003020301080c0a030308011401120204090e1c02120708120f070f08060303070206130f090902330307020709 68
    0x14418400e100c9a40d042500d11410b820850045e40100001c2da80c42c001d01c46030483c001c0e03120702c40200314108500b40fa0980d00030310451031110900020000b4030007460ba00039100740c0b0011101c420510180d101041039511040a00a041c08004070308603083c180900b061440d0002c1c0120368003401c64201c80000c06003601c11360444080390380480184108142040031118490040e90380c5e1030340d81d0460708e01070302c080014401c4098034003118640d40c034664490390440407800d200741c6056448940302c40885001c0e0178001d00c20210392150b45034440b10640300080b04005001d2a802078440c503451800400140e40c001c41090314030b0300d01002510910105508841d1241e41c6a221203031840c02c196030000c0440868080042c1000305c21018401075a0b404170444a0281c0c1c101d07507031560b800f00c00030284031006c034581c0402e45440302e0364000980d095294100485c242e200325960041500501100400601042e0050f035028840c0c210241c1c01034500801590010f0309401219161a074980c180320941d0310502 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 238343102 1250 238341852 238341863
    0x80711030a09031502070f0204050c070219051002030f1903020c100507030636060509070905030706080f0a0f0e2416140703031503050d080109020a0e040203090c04020403 75
    0x410400502c0904c4444144001e490f5a083d031805081e525a80314505464070b011f4462541c45000c101c003038112804449607681d0142500c24411325030090003a940342d070351040d640641c40c14074203400081d00c0802150320b074410706200c01c2d0908034004c4400800300c9181300c0c101c0c103069007000840a484410050380d40e0000d4140d43c0412070b498500f1000702030b1146684000c0091501030007102101200c00101d16800c01c3c1e800585000c05c03400a81c0303030064805507104a40000f42502441001c0c0c0d400300110341520000d500316951036a030340364102c44c01501125a104041000000704015901a03040b41002c0c10610303201081c45030b24546998282100d110710312904942124030308142045c20030710294400c80f0f044060032014000400074100700380c0d009010568401c00505e480c2014082e500982c034040289003402620750301ca1501554500700310740d607100030848120001071041c2c1d07039000329950894240d5582c040c01440e4000d00010b03400260500d69180944044c040240d1100e2024000850081 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 238344352 1250 238343102 238343117
    0x240a0804050c0405280608030a03050a02040b0f0406020d021501030b040f0501020d0902041d0604020d05120307081807270608010218010f020105010b0909040305090415080f0a0c06080711030a 84
    0x100301481c45c0042820400d800c908044040000c0600030054070030781d0205041c003040310740d29104048000e10030303074011482140c404079541643d000d449001c0e02c04c1c1c44c0310b902110340d0107a80301c00682c0c1c0c904600002d002d071302c8403080050000640302480d45401c54030444843c110001c8e85d0b601e0609a070808160903411560310010242985001e0241200c25a42c0348100309440c0c4c0311820301a1202001040030740212103010070f220411004204101d01c1c103400c000a01d45900307080b6402444100705956104005e15500d00c030303888010b0301280080888007045d00c540040c03c3c1800300d9645006c000c02c9103500c580e98032500010700390000e0000704505140d0300c0511484a070201c0000d0300c503c200c4c03031044045a140400500c940421001190107203581241e090b04d01d0356480c9400c890612810208581190070700c900c03000745001072408101540e00398015074010201c03001d03205941d0f000300c4002402d034403403800041041500424402d5000b081380c1ca4034892414400006600c1c42d0300201c045000039011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 238345602 1250 238344352 238344391
    0xc060a0c033c1103011a04030602030103080a08160f030b031905062d0103170f0a0804021e0114031f08100b0103110901031e060311240a0804050c0405 66
    0x102c03480d4001d1214030b141c040182c2052156103540c140030501070052654010300340c0480b46001c1c030b003c0d80d008580c0f00d50255525a1680b911001d00d400500724800807074460300100b1001300ea0f0258548141c00c2d02e40e20444400c18555084018050090b0003540602a0b17210401c2980360300c0d40000181d5000340011b248a09260b0a82400040f0707501c0c8218843d441b48030312401450799440ea03581100e4003c201a1f1120f00c0311f04071850070388034844044e003800c0000901a11080d40200c0c0e0103128900840ba40d00125094011502c090005900500e00040c0020b00ca80444190b000c055034004e484c088414000d80c031203840702e20300800c040d0000d40c02640306410000601005000720000c80d41c7c01e2905100300c4801070701307000407405100075440c181070701d5021a000110b0b00c4d2507203070f840c698004020702c5140d0f40c909000c01c1049040314820f000310210100900c2c00341c2d80c03188012168083c0e0b6070b064074007901501e0131138140001030310856043c0130311106c240d039650b10760043c40e000c3c21a200940c0d860301340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 238346852 1250 238345602 238345691
    0x7023d030e0d0504050306010e0405011104060c0c0503070815040804030b0903181e060705150c120a060f031529030c09060310020c0106080d020304050907050c060a0c03 74
    0x1002d007852041000400c0284000e480109600d0f044958486010203141c07900e26119024111030200c900300c0100c0468005116903010f030540c49240c1c0904d6628183c2511101030507254070050090a035980c1c044481c46000905c2c43c500c1590240c041c034151400c113500e03aa03030040180400c1d2480245540003160b84010f4000b14140000c080344116044411000b8170340012840c1050000010b2080d6004902d070428806c082c0032000d82002443c496000764038001c0603a01480d000050401a610b411100041200f51a407180c04156142c10315008420381c41c56032000140a022040700c3e140c607455428441d443c540107814000c10142840c140d1400760320040600d807800320009601c520030002403050007920b03100440c0c1c042c01c503002610050390b102c940e990811702500099000081c20f1007803a441900e00340c0c5c0800a4000d407203040300d80840c5915014400c6925020304d13008403819820080214048555070790000648883c2401d0220350044241c940e11a803450100c0c94880749040010342509850 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 238348102 1250 238346852 238346863
    0xa03030f110c01020606040509010209090403080709330c0b0c091c110123040806090706090b0d0b0409021305010503070b0f03010312090e010b1c0207023d030e 70
    0x40000000b000900b41440000b5500c82d00500035501540c1d40302c0203d0201740c000e4044460f4544068003500310790a0510340103100c940e08440c0d40c4000750035090302068419080d400075440ba41000c07425080106195032400c111003184a0440501600090420004c0d1034030400c1c601c928602c8041365116891502030180d4407110700800c4442d00700358200381c00003071489179100c45803503002e00e049001e101201c0c8006450802e803d0001090380700204001480000002e50544036282803010f8bc0d48065641005698410440c02009000c00040c0054007268900d0781c130601d20000000c101081c070b00c0310303600410301c52481c1c0c1d920044020344a000502c040c3c1410020f2400400c00c810401d0b185c030240080200443c00180401008030000c80c007902416407241ca080001f9001c07000b400512540e503200e5845280d40559442c944081c46503031114103000c5240b095501e9160041c14039025907811039220f00e00508100020b094000d4685080c6652242c003614440b06540c4640f00000c900c1c1c0c00410702403030302e07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 238349352 1250 238348102 238348127
    0x612100b0a0e09030304060e03090d0f060f0b01090308070602040e070c02040c050405010e191d010303030c051309022209020904060504090f0f03050702041b0e09150613050a03030f 79
    0x102c10244850740100204032944540c22002c0010141c80c443d460504621600c02680d034048540740048040c407210007555078a5610900d4204200e54414100c8000d45032840c4505020400d000c2082000c92581002050030700d100744801840e0a03260301080d03006100941d48080082e24001d00c07101141014031807001402000c1c00c0142c142864800000c050086001001f8010310320010702d04a9000c0c22046c0401401e200c20100f0440030040e4002c3c0320300c01c424070003940028140250b0f41d84440c0a030b001c48072000410316043c10014180510711019510400305040300603160841a08622004842c9001130402000c000d03a03200801c0b006c100941b40c01d40c100c14031032854031760002c00182180400d40c89069000000380349441450030241e50702e01030120003a4005080032007898814214008034650803020b51644580d0034144000d02010400460345c2d0542c50f140e2208190062a050000d81640800081e10160707240d12000800e0b001c030b0265004138040740e210580081c04680020a101d404e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 238350602 1250 238349352 238349369
    0x1b130b0a03150c02150a020702040906050406020715020a02030306040504032007080c0108090309101824020a020306061909060e070201051f0509040809040203040f060b0301090f08030612100b0a 85
    0x1805020110b1411170a001d0500e032010740d400913240c0c00310344550b04007100766a0441c40410462500d03080143c00b035071058908403004102c03082c0a84c1d150840d0310a07a8104284d55000f14115600e1170706100042c41d0250081c0c09010300c00d40c03d0b1410304681400300200b101c03108050209545400109440c21900c120f5081c14001c0c42c10400c2905030001040c0d60301e401c0100e60301c003035010070400259514003946c022006046002c40001c101d402095500003499600d44146042c5690100412a151610300350002c4d81900810046509480c144401850318072080c070b8100e1246640d0b800301012915154810224010907100300080710380c0a1098641c415020028642e84403214298400000035034000c1c00d1040107100085800c2c4040c031380646d201c504c4064030071541d85c182414000e104441090302140c00070300b096100382160606005064986600c0406101021b100c0d0346c0302011034100611441e0060360211200e0502c0004100c0d801c252aa440340c0021040021024082e080c00c00703800c8441c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 238351852 1250 238350602 238350613
    0x6090c060c1502031f060320040b07150f0c020c03010501061b0627060e071a12060f0405010f031101050a050a050c0129121b130b0a03150c02 62
    0xc41c00900c482c0c0c40c00c024240d00141e8a6442d0040034444e10550074521100c0e05050101081664159010b40540c51440c03005000f480d81c0010700c07050310b20441c042c0301e00c511b1081c003405002032028503150540558040010419100390820f03030040b10b10111129006034003a90607441c481c14280714250260030700d40f810b000e510004a0030403641c0c01000d03a00a06150791819001010700801041400b07401c26451025210701c0c1609100703024089080078882140a01040003070410418100919043e444012490400000c00b420111140c00204215045807600d00c100c002540e85120700380c06800d680d015110390600310b04040c4603402c105080d85051101c2040145100344c0c00c441582d280c80c00754078200c1d82e914040205180500b0790240030b24001c420038040c1d10760001d00c0d82c0c1c8c0c1100c090000da030388031144c3d0901c1040d44c0e9070b640c001015955601030401d041025003171072100c0c100e00481c60b00000c101c203001c140c045119144070703900c150380104400c82d440020760441c4c001c0700300e41c603424030003002d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 238353102 1250 238351852 238351877
    0x30b060303120c0304060b060d02120907051f0c0209010e0403091409011202030a0c030b06040b030715030b010504080d0306030314030702060105090a0e07121b140d020f0d06090c06 79
    0x2c2031401c010700090041440840001c00304074441d044445104000340c98217072106807200c0050060b40091290002144c034410004003236810004076001110783c0140384e8240002018041134504000c40390a404124900301000f0140e110010503d008010301d074510078252916042c0107009030b8103a08180e2946241d00c030048040d0761400100d90540341c0c0440017641011480c40001d00d0545009070080850310704401c00014410a541d0b00c80c460402074070240304500401040540302e8585000380c82080002d0b808001c40a03109501000f0300d580103050951500d82c6581a10380780c00c2072040c2c1c000019484610a00030594412442c0f21682520038080c0c0c00e41c1030200c400b0752a5034050050900a43c0090005000072070030782c001040c181903180641301c80548515814514501281080c0d941c003640c0210182000a5280080c0440314800a5048040d03043c00403c26203560b03070002a03038400a4911500191341d03d100580c85824492000010003101501d03240e028980355600208c00d0181070355a10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 238354352 1250 238353102 238353127
    0x8031e0406050306060a170403030e0105060a0e0a151d01090606031109040e240114010203030106080a090303090b0a0c110d0504090b03160e09070e07120e0c04020f04030b060303 78
    0x4941100f004c40b101c5443e030000b640100c54105d280082c6411817047d81040c031042c1a0180d22031550188002c00a00a82e517076101070242da600c11303100304000700f00ca800c00100008980e070311140301c0c01c90105a00001560702e00c0080c101041151500402d10072442c01002008a03e2240d20001c0102d8201840710019504806005000d040300300d034040c5440303161200c000c180902c001d20034000c100712444540038040b0ba0503004043c09001780d1100d090103240c0f00e00d10b5030000064030304075003c41e56a0a03031503840d0a1500082d1010743d9085050545a00a020009070045402e41c0706524449000580071043c440041c401140c042000607150000c0d0200c88040764000110740603103100c180003142d10410600802e24001060340e40c030155104466001c121159110078250013204045c04640800741c83d0040b000280d402910b840002c80c0c030045800c1c651600940000409140020076540b28220325008a410390b409201c094840040c000780620410660104c3d003904540190001c2d42041d0010040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 238355602 1250 238354352 238354357
    0x70e180705100804020102070306063b072a030e010f09030803060114041a12070306080c010f03020c0106080d0f1d04020c120a0203180d02090406020f0c0708031e040605 74
    0x304200f5100005020740e40200b00002c015036000d10100506513031440b01202201c44a080e18518519903045407c00e001d8074107019140c0d0030000d1581040741c440700d4095800740c00300c0c04e80a00142c100205c4080c0c903600180d44054080c0031342c48000903840b0b44c60006004106290f610814840d03d03042c1070000c1800102520b500c4002030070525034103119055030807a2802164024a00480186050411040810041e11a00d19180d40050b29078a4031b510a90031b42d0364a0007403480980c031040810070158401d240808010b50a4100180361100500c5c01b43d0a40707a503a0403074140c45e03200141941c882d960000f0021000ca11618000500e2441c1c0441e0030f40000c1410041c610468002c03e80c242d0120f0140041303000e00002c9110b89941d80c41d9200080e490ba0001c0b182898503454900d1240c0103800c0000ca0788aa00d0b0380241000300c2d5540e1640e51000a420004ca9100120400d02407030aa40b881000050003601080c0010b43d150f88400b0750b0441c1c0c00d600c1d0302a07560b03829000c0c03008120840d0000203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 238356852 1250 238355602 238355629
    0x15020a05150c07060e010204030c0f1d06011b0f110121090804150c110405060d170d0617100608071818060506040c081509090f070e180705 61
    0x14a03081079142c800080b0864080c0781405082c0914203048070b112240158001c0040324490f8412000035540c0310009000c01e10140300c0c0c09210900300410701c1c88001301a0301c0a500060504041d00c40503410030006c9400682040c08884003018004110706003e40402410041c11091a085240c0b24600b480c4030322850b40e8607981181107445c0c880340d070300f0065120255009024025a14140c1d103449030b10041100c030308102d041d0340ca003142012022103410280103051050802500180400c059039442a032806040307032001075004018080e51100c03002d0b900826000702030342d110810b074464400310417500f444402520024400e141c08000c204004d03002c1048400c40d01000301d48460b01d17146010440140040b90f01c00001d103120000f03401c080210b82d80c00207001e10b6080d1070811080c0501142598004016034106510710030314581c8080c0d0785044030416610000c0300c401d860f00505014001481c02895420040c1a0004130040051901c083c045007034050061000034448a860030300828401d810944 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 238358102 1250 238356852 238356883
    0x30606220908070b0c1201060207050a030b10091a03010510030c2c07030f0b010305010303050318030708030c0c0f0105070503060d062a090b0708180d060c03020415020a05 75
    0x1030503242480b4072581965070180d086001e00c280b5140016005880e948400d21103040031000100115406100240c050252a0086e04041d68035045890300302e07441038001d0102440404221001c00d1442c02d50040010107043d64915050343c2d03488008050075501d00404440c1840d614907010404248105686411565070080700214035000c0412800c80b030806026000c80c160f902424050758603810b030b1100c0307261121075004000e0150754a0044007542c1c000e100c0a000100d0a01c0446d080414005c8040c00310100340088a20300356881d1f49002c8207400848403c401c620012502410501003800340998070000bc400800407441c10f030b4000340140c000606142d0041c16032003102002c020300350b4810f00003030300c1c1e00761141052080003804a03c800c0c0b6992907403000980007030002418000482c182c440250340030700a1400c4c01007001a03520ad840340100340c694004500a400c50100701c2c18450080018661b603800350f03070f4906105045051040b9040d039402103501621080000c148041245201c400001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 238359352 1250 238358102 238358111
    0xf08060d02040b060d0c080402010e030615130603020d060204050406080a050a0605100504090c05121b061e040308070b0c0406051206010306180e0c04050c0403080715050a0b03060622 80
    0x1240031070203d00540c40c0c05d10b90249000e400303045564100388018490f501c00d81c3d9040401282405064448109507140240188c0c3e250b85039220740f412400b6148241e844a0000455641d40d80021b18120b500318400d81d2050b9002801384540d0805000b1500600451001001413010540c0c0350390751604202c0c030250003959560045a82c0516150704400103205c001c0080c000c005590502c4105a2020700c96640b041d91311032000c40500f84042401603503c040d0344000b484503c2c0304814480139900c01600256020009841c00341581e044202400255000390034041d181c8401c1c0c0350218420320060005a110342c0144010011154445c0c21520034503000c1015180c1d075110400181c01808a80c1c12221510700c100c5400b00c2d010120354041c41070b43c00358104440660100b00107010031201e081d81d4120480d14104420308c04220920300602d4200d2080081d840d11450200c1c00104440d0141d0305142c4040e200d14200000745400c009060f042407048884c0700390075629191020600d80344929a0200d140c95 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 238360602 1250 238359352 238359371
    0x90308070507150608240123040207050102120709080304050a2601050c0a080a0c08041202031c0f0c1d100c020319030f050301030c03060e1006080106060f08060d0204 73
    0x149541c400c4240f0001d00900080d83c85580c3c07030307840300182a007600040310300c3d4156003c111081c0b0309460480d90034180500406070a01007014140c041c0460a41e0407503020010400061801d100070700448000d0384007461142031685008080103055400106039610610061240740d99120100c0c040b0f07107444410404a4086480e406407034050300c0c64180c600c0d445c00301007101c60510900100008100c55071481802c0d41c500c10f0001c100c43c01e040c4008000703002c2c007000070001801d29401c440005c0042c0101e90418004040e2040b100c0b00b25400c0d919803d450382d0b0021000c0200e40910b01c904190303801d03c4552042c00c0c02c2b04101414804910a2080d80b0000501c5001d901442400b0803058024081d10450f2840000c1c140741040c5107101200001c5850308501c000511803820350341a02da12024500020b440d6480d00d030094032a007031128006016506d00c0e44d603091a07511508005203010b0001040351843d02602a010240d0421000c0900c002141000220790f43c1e9090300101d1581294005441004c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 238361852 1250 238360602 238360613
    0x709050708150d050f0730060203130506150a0608131209050a1e08030a0203070f2102010516021612060b0a0e040210030b010503150114181201090308070507 69
    0x41c020f1015020b401600030642c105c031404950403007920503a07526502a41e00c001c5c2d1072080e101c02490304044e048680e04900c0d0003d41c15400a58101c2e01614400c20018000c3d1206401d0400545041c000b101641c15036503040e003082a0600014801c50502f180e00e4501440c5210140304009001002002d5000c01110804e000c0d00c0e600001d0100500241c40481c0c4035139200c00310050580807a0807442841400140a0700b001046841409a0303502540c20051740c0d66030380121400102d0100c4c1d03926034070303a103075510b0900c184460340045155500104407410036880d44d822071804211100b00310340000320040344800440c04004102c50142c2c200f907524546900f00800140502d00c01650310920310710300010075641c92254180554000c4800000882803220107804443e000d0500901141c0148002100c091404c0c988041c41e83c01070610041c8825407510750050340c4d000350317a4100e030301d00048181b1075035090420801d07068000c000300800c4100c040c0e0b240500002d800600901c10000001001c204011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 238363102 1250 238361852 238361869
    0x2d0201081009020f1e070203150a09060212070e0301050709030f08090d140c030d080f060f090702010e1c082413050114190b0c030c0f0a05070905070815 67
    0xb07550481151284902074501d07100e54000d1060542000140780c40b070000d081d01c0b600311601c0c0d0303600500429508030811140724503101c00a12140d00c4907512448800424000d0000341255501d6000481c2c6614180d08041e2540c00d400220a001e40e02d010200714103142c0190100003582d4010780c4641619640b03142c0482540700e9803c02c9a00200004031480c2084181d01c107480207800c0800a49030405410014582c0d5040c618014000245039000801c040b58006225240c012001400140c08402c1c00d0010502c0c0030f000303031120070041c3e42d240d00d868a420014403003481e0512101e0303070440101d1f141c99801880000058906000d2141d80c2051f28980010030b405005e1070b07100600000d141c0181d00140e480240b40034490034500c110f4100c50201e092504c50130f0154074030400c000002c486800d11500c400300b50801c104641240c40100318010b00020304000c1d0081c44508034000340070b020070304c1c6030079400d0014a0b402000c40303509083c1841502c1d900140240d603c10036111501c8a21001500040c1000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 238364352 1250 238363102 238363109
    0xc0d020c0a11090115020706050f190908010609180209180f0303040308151809210415080f0a05040201170702060601030614010c02060702040212010e042d02010810 72
    0x744110035654040290003206503954050840300e00d0030a0303176a015581500140904114010703008100240090b070700880180c015851032000d5541000a00400c0103a00b071802c003690740c081005d05c44200907040c0240aa507028108501060158030802d68403248540240306e00244120084000a401145901c2a2078000802c200484403105610f0307501c26101e0740240e40940000d9900000140307814910701002d040c2c10400b40c0081c2164003180c1000520900203407466025018103c2043e03800340b010f5522198900c3e644140541e100c1c80c102500d000381400c0548041803000380420046042d400a0103d5880b48600d031000c070312039a8510040300d08211445010103110000c90a010041c1e41c00203000380701e0142030705c0820442e07881c0e00401c0a641c0c030038401540021080c110302801803d103c8090701c2c029101610250034240c0312000010f004100341c009010312a049020041409200c81d0710501015100d01c1c1c50381e404a0400c0024180c0c125228003a050003200c10210f4043e1202e04120b1004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 238365602 1250 238364352 238364377
    0x30a0201080109050c12010b0304030f0305090d0f05040510031415310c12112b061a0703090b090f0609130f0603110604060915030e011b03180b0c0d02 66
    0x1a6840f1311516406e60000d66040d0700040400e01d503ccc0f0360901901c40e03e805010902d00a0180c3d40395004c0c100c4030503914110400030001c052000041c20f0b11f80744244221303640d242c1c41c0030501183e403030f555406a1400808078010f0009800c000c0150362505105203c11140f502c80307c0c0c840d1042d0841100c4011080311004a44910f0b2010100c86640c0c4400d600316220340e85081480101d8440c025000240106400803040201000103560081c0d0440d0880c40c0c0d21040078000300e030f225515009410100c441c1900e640d04145c0005034030b400c02d94405915006008944400c50400c106503000c210100c1c1c48202860003503900048820054ad07178030342c000360004003500e02400440040120b101c090091848110380201907400720400f10702d0110155010341d0b1041c2d440e04540380c80c0001c58103422031580d40340000c1c182d0b112001e0350a080c0a0154400440152117204034000312400001d003180c01e061b4103038004c007003003d004030f0004504a096540011040c0c43c0c080c4c8030f41950350144028401d07002d81c141c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 238366852 1250 238365602 238365637
    0x380306010303030b030613150207020a120c0e0c0403030c0303020f09090103120201290f01140a0201063b1f0312020609151b04150815030a0201080109050c 68
    0x201a49904058842c0b0744c154140c990a4503449150840c03068511401031000c0c40c1c400c861020054203a01404d54140010011420540c0d1b84000d2003950200c0b035000c1e90340d019141c00c01c0c041d801c030040d02c00390003204480c0010b00d081e24548005000a80c030b03040c0282010340000c0c0d221115071003241514230300342c1d005203240c4155a40e49804400035a0041c0c1c480050f5003403120f4541344403517001c200d0b06040040c1b25500d49444144040007281c0380307406451418011401c00c85807854840c0406000d09140b650000107140317080503107041440a50125000c4d41c0503d0408a0744204c40306041c944c0c0950107081107e14980750039008030720015100741e0007a904405804000203001001202c0070750722404c0c0c0c080d00c5031511000105030300e0b20001f80707402e41120341c41030125040b050782c1032076030440d60f04c0070f8280d03401e058450350721825580540d0042070000d1800c1d003d105800c030350b90201c0d45564404400414207842e0030740c00030708a800140700d240050b9540744000340c035403c1d41d48200c80c1c116940c41060700 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 238368102 1250 238366852 238366859
    0x1b0c060709090f0218040c021e0c01031104030819030b0316030c050109030b0f1e090a020a170c0f030703020901030c09110f030f07030b030f150a38030601 68
    0x41500d401e40c8100b40c1c0c8642071020001c10f4410390320031240003542030800c85680e099000300303010141507030390004000c601c00d420203200003d00070076410452007101c030080c0c14010f15940006054983e00101c1c468900c00801c000c00026001038211380031000b001107082000820036074280c00520651070415014007820039202ca00b0294800c1c8402600d1003500c0c0b51007150340345c0c0c0c01180c91841c14040101405c0340000402d0110b00c00c0080f41c1d500ca0020270640170091140110400540c01c10345e03100025501220380306e8114500044114090203282094040d115020070815030340d20b41c030391f0750070b40940e11000d000740241d1401d01450014503005050b020302540c0da454403903081c0f00903108045005140100c55038040d20f401003100c4005071030815460454503100081049804040d180000303043d5074210007015a02c080c003840c201d84951801422209104044140e0610001030807412181c0c0b9041c178803880c5003640da203070301c014052028465409044543c0802c01c000780342e010300c0f40d1611070b420000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 238369352 1250 238368102 238368107
    0x13020604090905120f0a1110060f150c0503030a18050601060216061404090203060d0204090503091302091005030601020a3203030f060603190614030f070b031b0c0607 73
    0x8010b1520901c110381a6141c4d801151a99010701c0004141280003006804a0ba9200f8000c0d4418003482c6000d44003111202d21003901150400d900180d035440400408001c82604000c0e0400f81b201607041909c00780550b41d4445072240710042c5100b82803956480f1702c0c00400c84080e0030000d1b00307610008540705541c540038081e5a070681356041000607040c4035004502d05104142070485891030340d0149003014140748010010b90002411250002c80d501080805070359a030049030170440c0170b540603640e140110070074014100c01c40c0c1c154500c3d00303004200703040254132051204031302c00703001d8039000e922911080c00407410100300800142c102c4545a410210034001114043c080791002800c000e40d0700301e82c42156440340400c560905560310040c000401c0350500c0e800443d0320400c0b510007412a4090481032004585491300304100005442455903014102080101c4140300744d40b00a0408901e0814402d03607078480105402d4000310b4014050101003900400e44503d41951010394074a4984030000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 238370602 1250 238369352 238369361
    0x41d040b010b0c030403030e0d061d1209210c03061501020601050904120c17040f03021504050a090c03090f051c030507020d031104080a0c03141c081302060409 70
    0x40d103050a09900002e0608401c9046403940e8039150065414a469a1016600b40c00e015038015045043e080700d42c40043c41c14400c030b49640071800d070f81440c1300c40f044140c40d240000c44030b02c04a81d4001040000c2071a41d440001402c0c1d0000c90500c0300000c40c400c8045070800d4044c42040383c040c41a4420701c02c11309009030803201e01201c00c0e804c0320500e03a80e6504001d0b901d40d00362009044d1440c4503010030b62043c402e40004003074500910500c440d681c400d564040d00d960066008071041d9161200030301c11441c3c581c20080124500100c80c90505003440000b03100b20500c0e02c2a03c0c6195a02c4a82c14512400390300714605407a0070000c3c00000d4496801c0c020340342c01a0400c0700c00a0302783c0c034403000c98450081c4a41070042c8179903801803001c042040401d070000d1400c21003030404100207001c0040c4070300c810406100d0140c0b144d515050004e1861a0203034108042c9003440343d19400120301420303041e00d03411300780b0401001445d05030110349568245c0d0084134120807010f0b400000019000c112501c86410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 238371852 1250 238370602 238370611
    0x6130207050d0e0306060f0d0c0b030903041a0702060a0c03090b0301120b0601030c1d032803021603200d02030d021b010801050303040306020a020f0102030106020106140303120c0d02041d 82
    0x50f40c4920354446001c2645508045440d59448254500259a542401241c041549104811340b02500307407203041c1d0801640084407101c426500c001000d0150342d42c1c810120300c29404d0440f1660404a20b40d0011b80d80b03024030031002d0300b00103070030803110700307040c4122280030042c026409865600d58649150708030703841400006440e15100715010859a521074820440d002c81d580d51480250005079041070020020741c0281907144c03141071900e03100c80e910014101003078511200d100ca0350084a18019081c14200c803880c016161034184100042507880449901035810b04030056074072464034001510410f18904003039014840e104090842ca40c000900401c4a40c80350007071010b44d16a0801100c01c100240a88c9425401c1400200001000d41d00a042d03500094019156804140c0d105242203803c26446940140e44540b0100014a0454295035140b1010f601644c0740c403994107504c4000c2e503000b610040200c1800034000c1c2848a070355055030050420001b49505808202c48140c80c3e021040d04c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 238373102 1250 238371852 238371857
    0x12051c050418020d0b060306030d0302090609060d0e060c0a0206010b0921060403090504090510230c030f0106030612110102031c0506090708060d0f020d080a0f0e01050a020a0b06130207050d 83
    0x5c0681d2000d207002010707030780300b503200030010010700e15101c2086010390806230146030850300c2409181056910705001e4044c84016900002d0000306801c041c40c540440508048501d1204100a01d09a039000c00d603a07054036051440141c0d0707996403c001c5026841d80010003407051481205d402c071850404038029001b18001e0759001d141c02d40700c13820001103800c400401455a4044018036404107541e4112110310080c0d00c2c2e40d400e40010110b12504801c00464040820110010400c0300404546034410b0150045103420000181405030101001152240140a016200b65001660ba1080044818480100c0d200b208610100f0900c007001e480c0c191070040c400c1419200042595202c0c8044510440b0010311403455801151180030741c0306c0c8040c2c81039030004031829030100410b180701c0003003404410513036a4443c40451102c004059000d14021141001010004030103519030005160b50001d402900e0450141c950300b001035080b82240b10302244060010a4500c24800f0100d00440d240c803064 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 238374352 1250 238373102 238373111
    0x31501110c010c0f061b080f0a150605070f0c060504061b05070b13080a0b2d010512031905120f060a0308032a040602010612051c050418020d 62
    0x40c1540740c08200324800d000950090f015804600c03400da0084486008040c00240016540151907401155811560203d80d640c418002c40300e100880b01d80d030059008204201254078254143c01c803021520541040100100f5042c091040f11141d103007041d0382c004481c2400c940d440f030000d0516006071007401c0119042d9403e04400c0480d07d61b02c400c0080c1d0010143c001b582c1000741090658010055116048101b6040480c0840c1c080000400c018088d1400541510b84108000c40710a40b020404030301058111f521074040c40074001190540c4c90455200b1a1403101425913407850103a83d030b44c0498a4941d440e00d8403200d40141c0180f10703240f5810301d807200541e116182d401d64800c05641442e0415951041080800c207910003840d04140384000d100707802d8400320070032407a0300c101503d4804c5400e0000b4041021a40900c9031400034010003c2ca1a0070aa05031500341c0c6540359040c10229541812aa0302181880340701103801070f00c0c0121f41c2180001005ca2883c0081d00281c00607101c80b840e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 238375602 1250 238374352 238374377
    0xf0c010f0903080405060f0c100b120d020c1302090a0b04030215030c07120309020603190501060f0e040e0703020a080a05060601091202190b0c0f0601060e0d030804080f031501 77
    0x295020605681c0c1200c84645400d1510f806d0011940c0002e40900800c2e405000781c0702850003d01030354030306281d01036002c11070000410420100c041803640e501050f50142d140240990303004600c000720071408440c4040ca200000d8084806486219589a8400b00c2c408010031031500101c05401036030300a0700e646482c81013076606991144025600100300c5a018000e02c1e0004100204012090f0304500d80407a0407a0a43d0216038160002d0b0b07291606004100c01030804a6603a102d03850042c4458a03145281d001c0e1080081c00e85a91a26550f00031134070340010b8011000c1c104884d0000316800b500c90000507a481e0342d5a511400c034030204480c00e028450100d0b10540c41200c1100a4542c004c0081c8860007442d401c2220181c0f2144d6101004201c9000010301111550040c162840765640503100030f80c0e001c0786250810905030492018443c03031207441d01081d15142541314030603a041c05c01608984884c14401d13000e0280d161420280c40d070000411a907070b02c490b100001d5110007070f01c0e03c208000c1e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 238376852 1250 238375602 238375607
    0xb04020906040e01022b0216080702030304030c080309030c01051815070f03270f05010305190e03040e0f0c031f030204110c01051303052a010c0905010906050301080c060307020f0f0c010f 82
    0x1b0303240301c5480c0004003842341004a5012001000828030081c100c900d4603681c1d40d03a080320311003194018601508040b410341c01078182030000301c0780c00109103051441c08503090700e5046c0000610800c0d600540e000c02101d00d10b080c4490481b540550400d12008101d0894503005256480705245850107000d200d4a5020070b40b241c001c1d403801c2d00c60021501c121141040011402028010020652400e40510003030800c0c010348503000d4161a8103019550340c40c00c001e02080b543c0b074054900911860840300300404000c40609880e0481c00c81141381c0b204200450042d4901e0600c1e40020b548546000004051092004014450003000c6030003840a41d80b25405504450501d40000e8082841001201241ea4a140030411a0325102520040c1c40600c1c01896007100c0321003030346101207480307800280004c3d0b8100c1c03100d600500051074120b1442d8105160302d07072214100b02455001c0c0f88003002040200f402480a80c005409032800c482c010650740e07202e40d0756201242c0b51300f80855091004c80c2081031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 238378102 1250 238376852 238376857
    0x70f020a0f050904030c150608240609011401020703080d050610050c1c030e06040b0103061103090a030c0c090207060506040501081534030b030111070b04020906040e01022b02 77
    0x704000c08a82e0f40703541300e0310305850800b4107903401c40e9903408411400c100010f481c401c40010340740301e200038125034100b455100412844191144907204500040190741c1d030310307044441c2c103603603050078623003516060400143c1c504805a0401440030b0b902003080e40e0040f0041d0301c40f03482400700715506000e100740c101c0c01740d83e00e104400b4841b403580c00800c6141d114882c0e0510700c1c054106240fa00048203284100002d06150007901d007102c40304080700c01001800074034081c1126107803038240c1031855406c10f04942542ea0382c140e41d0040c01c1c0041c50340e55a0a00c20000c40590042440d480d05565542070340c60850014441290b1003817050745880004244c0da00e000400440c0c001074820b6010850303e96400c1c00445810244030403142c2160300e141200301881c40f0640da4049100c944010400d01c554504050130f540382200c00060b60030062000c0f4000c22003410106400540603134140304291100b0b03004c034014002100303100089600028082028018180c02c0403d240c803002041031209554680a5050380b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 238379352 1250 238378102 238378109
    0x303090d0903030806010c0c2303060105010201050c0415050d1109030f210313050a0b0411180c030613111e090f0112020d0507030c020f0d050d0b0a0803070f020a0f 72
    0x968680009a02c1d54000c614a50940d40a46008c0d036101c2e6803111480c4a00c1880e00764030b4100d40700b8040102c05810200038250241c0824002800249019548411a4003413803084800c5003010304d0f5030000c903602035001c80f282d18241c41000c1c400502140800c000380c1e44442d060780e000c2e10401c44501492100410604a81148404145c0d0303041c541c0342d01100950070140c9114400d05060042d000001e8082000ea0310080c40340b00b0700005031905040c0025a210600304650040c49288400003112000e4540158040c2a40e45030a0f140c0d181d20001c1000c12030500c5842210501e02070310708a0094a5801401020810040d044090b03403004c109800c0c24003c5062581c2c01240300030a15000c1e6000b000034210542c1400801420326085c482007100792403040d1094070100356180300c1091a241e040c4415070b40c405158008004003150b1030402007072413260310751900104d656842c0c3d89401e907039072908060040c4404c030102ca40715540c80c1000280980300030300c224424514980002035150641c00490110b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 238380602 1250 238379352 238379357
    0x14060a060f0501030903020708011a0916080a0504051923010b0a09050603030d020304060f0e1b040b0117270d080601030f020909070c1101031a12030c0f0303090d090303 74
    0x1042c9408019805004105c05c110b09602802401007031280d4244180c120040710581600010a0101d051003035501c8043c180b14003254070085140e0006400902c2140c1004a5241c0017500740d80e00d00f000c40c1003191300e90484003001380444010043c030140c1581803600c201e600aa01c00b0704071201c0100303401c0700ca0b0940007580101030910208041801030f84039950201c00a015645000b200d0302c3c51104981c030482c1c00b10340c00c9640e0000e0130303200b2201b03111303015281001030010400d952400c0181c0441c4030544424500c1307070303483d1040500700e40d2065160b0000c0740490024200b035030901d6000d00d1030419010741c1c1d05c804107035025100744040354001a1080100c1c410b4803000e400d030321041d00440152080145001c81c4a408110906d4113449240350130384030707032407903a201e004448242c07400e0284120144104c43c101030030074800e81c0800e582841d4000380303040c00311807603040140044041821030058654100d59401540b4440400000c0480214800d00360325007540e41d103076444842074070b40d80f4550001800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 238381852 1250 238380602 238380629
    0x210e0d020f0118030c0609030203041205160906120b07090527070f17070203090a060c0510050c0d0e0f060f070e0103050c0a030f140a0b04061403060c031305070314060a06 75
    0x424443e502245820303002e8816a85003588030a07082c4502648078cc811a101d501c0030b8065041020718000d0356001d451820780c01c0c00320620300314040c485041003c00242100034100c0104030014004c0384107000900000d000c6480300c080e0541c49854104000400c5030300010000b0003c4c60031071007440c4003a0328210a4a07104c9240d114070240101c8810f0003408071040d84030400480840380c2d5280e96270001081d8a5492405904592600c2d50510181d600101a0541060b00384031000340141d0903100c9210141d01c00158250400055900c3c00e003000c1e010307041d00d0083e00c090020340601c0443c407510804264440c602000380510044040b54022140310029402c02d0004600c1c4c280b0035000850884030a103400b08020310072480c1c034155590240c0d80d0103200e036912a003030301c032504250180c14014240c1805120b080e0040101081d200e8200400710603038000c0c008002507030385034842016070117140c0290480c0c06541d105d18085001c0400896405168480c03040042c002c035030240200c41c240c0756010340024 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 238383102 1250 238381852 238381877
    0x2a21020307140f03030a0203160207140f0102070315050412020c18060d0203070b130609030b27060f34050318060901150f0303210e0d020f011803 64
    0x1802c040190030340c05050040441000d4202c00420146018001c00880103989007440c0840c800101084003a0201b55040540100601245070398005421003080d600b0650150308000101d04040d01500000c0906a1016020001a80640c00f00e481907115803030780c412040c640d0f0016a6a09400b03044254480b01200001c00000c85c2040c08540090000d0507100c220a81c0c1d5001a08044094014042101c0e0104c1c000400f4211003925030010b05242c00c114191500b15141c4c0440c2d01401444c5960600c5d80b0203d50100100c1e00d000b6486001203581038850300d05100b403005805101c16150030201d02e10000040441500701c0e14082002c0145030101004001c040d001034413a0741009010101d05c44480900b03860b060300901005108001d144000995840c0c4040c1000c001486a040440660030113141800080d03008400d403920440e0380c0300101001000b01d4519000b505000c05564064082c18a010625580028041c514001d840002303200e078201d042405070840035031340d070054009042c011703070032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 238384352 1250 238383102 238383113
    0x9150402070609080705011a1504090b06090d050703020108010b0f0306040c05090a0f0302180412080907050d0303050f2a0f071202030a11060c0703030b012a21020307 73
    0x141000c030b10507000800ca1030312036291039140c0d8020100545169446901c81398140815440749400341004840456816900740141c3d542030240740200700c04176540300c420007010340e141000c2e0781110340024444540d41443d0b103412074585001f031004038086003101002003800281070003070f0381d4030703494418500341503a46180c20003000c0c0c880120701c5000c0c081c04001c030114644800042e00f000e06072950800381c5451461051211489058549403084a500750a20000a181241c1f01c8045200f80c07804000c15219000d1440c00c2007001c2d40284d41c03000c11207000f10300705601500000c8c032071041c1c40da43c0d1415030348401a103901c0c5065420107401c1d0180100c14503003455001800380c072014110f980c0490800210341c0e1a0115030b0b0341a90010050380c408680709600301d900203651f01c0c81c0a81a00606410b0401105a800360700405000170b0a0649032020496039034802c0e403e201003407411440c00d000032001c660880c441604044400d581094203c0c68040685003810810080424294000c501d010303144d4658 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 238385602 1250 238384352 238384357
    0x6080906060d1115130e0906040206120403020c03030a030c031802060d020d0204080102071103100c0c030c03030e1507021e0c0103020702272401090603021c11130509150402 76
    0x919910403000074820071041c400760050b00201c01003590380e003110341c01c05600c0c3c507001100901f00d802d19480700781000010307280d600944e00b01c0c40b0710109400058a0360300c5c0503414a20080c1219416200c0803c02c040340700d5058000e0890312243d82c80030014440a400c00c0c0755030031b402c200041e4018808104030000e1000d0355004004500d51008014102030b1983ca6036070990f403120f0b60940d460103403400c0f40715441c501444400f50615203007104102a09240c14040c0c030b442c00c0e1010140034082c20502075800e15000c0d4015060f0080c40906a0b2200b0021102d414000701c82601d80100511070f2001c0c0c07a500404071a40076584a000600403c98080fa01d03004401a62028000300d030080c200c0d2080864a5002c801410f0407407800300c00d5081c003480c10314085044900140c0c9c1c01e54141280e000000450798000300c074442038907020b290150750f40920001c1c9424207942c1511704003880d031400d002e1010000c200c8002c1c00d5945000e821040c00c240c1c0c0c40d410011191001d075229449842c45440c40501403826500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 238386852 1250 238385602 238385633
    0x207062001020705010e011d12070201050d050a20041a03074109060315210715030501150513030c0b03060405090f1e071a0406080906060d 61
    0x1a500500304612400d9400ea03004003408035041d0f034541044c0f424248080c000c00c900c20609007403005244441c6644e042e545c050a88141d401510000340e0102907921540c11214041903195040c091400c284003500010980c2002003000303540c10314010030160b40442d04680407102c0a04c0054090540d10011520507031010344954140042a20114102e4000c0d20012040c851500f54500360000d1051031001003c002d4044042031800030010010039542d54019241c02c82c022902801d0b8240103100403c5240d40580d0400c40c0c1c402c0d0942c2c00c1038035460f00082071000c1e42c100e9440050b2f190202c00e4284c042d10420b005000329515000219850944150b024012100c030040500c0b05180d600d80311003c07501d45507084400f00d42000810001181054021940c1100c01800101542080044a680c4400403207001d5040c0210009006024007001c01c800d401610f00d0310721540314100c103a510302c007442e0f1140c413421000c15030b1480010300701070011908511808018007258804115562000340b00008441c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 238388102 1250 238386852 238386887
    0x801050316090b0a170706030e0304050a060c170d02070212061302010f1e030506040b010809070506210109091a04020f310c030e01090c05100c0b04110f030a0201020706 74
    0x50008420916a24a506961714180500811402e0100007019200503910544a5510401080180342c80c1c5100703480031144149450b042e10085032400a1000e034030361808550384280440c80d120340d031701c0960060400b548226040d0b0404003071100d000d07855510841d1080031707100315100b003040503501504185003520402d280c10a01440081100304401d0302d94505800000d54400400c842c80c1443e20640d40d4640003400d1442080c5010a50b041e0794400502a89020b62004540a000091840e20301c034410250051a2032540da12100d0395002001c6000c0291411000c520703840e05d80031481245903008a03005001c40388a55071040510041102e081703400c1c0030500e440951180c8021007030040b19500e20002c1300104005600000003410303200310214901d10740e454003240d68002504280d005040702c409540d00d40311440c0700301040c0c551442c19400a05101584810082001290121584602812201e0140c000b10b00414181d40c3d6481b03410090150344008418070800c0d01507441282d910f840030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 238389352 1250 238388102 238388119
    0x30506060703051b0f06060a080610150e03061e011502061f0302120d02121611060c030d0f0606030e030a080a061203030e0d0201020307050d09170f0a0801050316090b 73
    0x4100d0a2170010300e280c502d80c55030050010300a0500d84414004010a03803100101180d0030095403110104e0801c1c030421000d40090f4211134460341c09084044840d50004065403094600101190100003101c11000f00501006001003508803101c4070307a500000306640200429900e0500b0064800c10100c4407030b49140d015540000160303180c081780e1020003411006800590200310020b842c141c4104c42e03c01c1141d0b0280304000f44640307200308065071584c0141e601111313810518041410344c4030b241e1420416000001d0120720b8000140c000440c0d035070034203208100c095940c4204400f00d03075039a4403456407070300100142d100c098841c1d5001e94000401c180001642560b81c02d1400d21040c0c050000c40100380ca44240500405050108440600382c5000070751940c80c200700c004000e441042c0c50340800540d9601403405000c4000d801c210f00c0b40c1c090b9034407a80e4103c003110154107504840904c02c002100e900c00425181004103d41c088036002064a01d041d50a090000011b4442c101440e500003d04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 238390602 1250 238389352 238389397
    0x3030c11130905010207031806020a02060f0c0f03041e12061a04020c0c031501030f021017012d061409041b0e21070b0f07051203090d03050606070305 66
    0x40c0b06014800d07108000042e43c51419180182505810307000e02030b0402035a0700104843e9402250b07050b040ea40c1111f1255030b51f034503510445000d01480c9200b10306441042100494500b0000003002541c11200c80d00d403440e03000e00c9a000c0458594090605038280140b001c1c80055400d40bc54010b4120010030b0b41c060b8075100740410101d03082060b000e10554803c4002080030306040c4201002036004002400d525030450b1219281602107100080c084d03204110791822151090100300c081b0003d24241032007a5075503d48580d00c2d640c40d41c4e0050008208030346102c1c14001c03118a5601124050713100c41801001c0305002c0040c6802920110f0341050302e892407440114100d402007803100007a500d821b115214000d0502c41d00740000d07060720252420341d01c4200705ca404000764000840b41a43c100b643c1e5005c413540038000311302421100600c1c4d40f00b402c8410600d180c075400030754030500311070381100e0801d008480200c05995046d0342c002d4004008020400c00300c0d110b84020010b0a50044003006580b15 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 238391852 1250 238390602 238390639
    0x50403020a1208071215030201180e07050a03060b031b1b1f060e070c08160f0302010f0b1014030c071a060f120c01030b030c0a0305011d030403030c11 66
    0xc080b20072200240c240010806860341062400e10000c03080380e02040500002c201c3d00c81a8600c0d030002a062040340710f00901040400152200a40f2a20302c2010507400d0000c805025a00400241320100303003070080110342e0500d54010b07640b080c5501c0e02d48445143c60210465031a5002500d41d1111140b40184420005020802ca4907540c04800c89000c0c2809410108011205c1e240c12441c0c801d00410241300403d580311000048860b0444502c6580d440d94030741e00707100d040b00c0481c01002581d184e0320b0402856019403050002d540607450a01090a0711401c016000c40c000c4043c82c08100c0040d0000c0900407650040c543c041da1501c02e0341c2c83d180054850401c40c031208060b00104a12034030810000381807104002d0100c00d02920040c2c1c120400714000c64482104d80f602504040da56501e0100c6542c0400801c1c0c0709010103000b120b40240c0b607080c01800703000000450224085208490003442c14008201c81c2140e0300b5a0780c0c11a12000c0c1e03070b50707021b000e800b807020158050004c0366804403118 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 238393102 1250 238391852 238391873
    0x10c0507090e030304140a05061f0f090b0405070905030a06150519140402211e0a1508030412080a0306050301020f070209060109210218040c1d1603050403020a 70
    0x9024034011500ea241c0f51a2140340361b4400701300c68200d80c102101c0f100003d840004d00d90b070810050b42d403407542c0c81d20300c0c1d400c4401c0c41c3d2603a001269002e50003100040b4001190710400c5502d1041e20188403ea41c0d58005a4101a9600c9401d0305540800490b20100d080c41d8015049540480d0140c074003a6034483c0082c1503244603400b2080007011454080100d6810140310800201058400b5401d00381184407401c842044441252404183c050024542c40d0200505000036800011940c0280c2070500c1c01300010409081e203601109401540401d11036000000d550466102e803070289100d901340d0359240c41c03903008500c400061686417540032606030b8080c0007400008103100d52041c3c86950038010040038040c080e14040c10300c12034160600c00341180803042403506810a4621140351075a02c0400d48050131804017000c07900070141400100030b8227040030703400c64810405100e07000b40041002802030100b500c0e0244203030b002413036424100b4020781107550b100b4043e006803041800140c50b04841d58 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 238394352 1250 238393102 238393121
    0xa03061104180b0307060e0102100f240302060912070803030415060501030207030905090c040506040e1815060f010905100e0102070f030b0a0203040c031509030e040218010c050709 79
    0x1010082070902c2a030141c0c02c071081040d4901c0780c0c1072052601c4000407984030034140c040c0c00b0410000100350b0a41e41d000b00705c178103180c00807420100904001c5140c0c03500204044450304904c8414000c046030031441c51011281a01e400a044038640301c2070808210340900400f17603c40b4540100500002c0000041c40074511881c001c01c40448840107a0241104943c0c183d00000d041c184144605c5004c264494100010340c3c2003a5400358058560315010441c0b8003481c0c0c0119804040010040b444461004006004035444001c0600c96107425600686440b4040c1d551501000e07440005912464411310300542008107042507661903403141d010440039008900b03c01d011031403001d10044503580c1080404004d080e24500c0b07201c090300310b556031208000041c10403e80103130044081800c0c011805415001146e001440e0002c0c0104100d003600a040d0000054000c0b40e45a44c07203018904103802141c001d0703105075159076405501d035401900c41103469136058400f8410b206000c00c220f021071080e1900f5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 238395602 1250 238394352 238394381
    0x90102030d09230f0c090903090d0615060315050114070b04080d020c012004080d120e0f070315020f04090c030b030106080a150903020d050f070b01090f0e07080c0105090a0306 77
    0x3010000500f0711788000131400c64001c04d030100c00c010314001c0c080300703940c2005000c5501e032001d0002800d080010307004011411100c4292804000b46051b0181e124060903c486d89504041b81c0d0345034015556060001d0058009103410808040010b902d5007407564014403840206052814000d141c0c001c9070483c0101250b0341c4c2d03484a09280c50381e8511001c104079014040198070f00303414082e0140d2074903000d180344400d00604002c6000c40318001e4120824001291040380c03020030801da66159102c080c5d201c10b5400108401104501d040a4000c071495104520510f901e0280340400581c002c09001072a101010354407a0b03460340b199400c1c000d03440140300300c038005c100c45004d5081c181000c80c0900701030300c0502c0c40c10940b200003c0e0040340c612110642c6091031a00c59000c040104014880c6480c0148001018070001c120004140c4c031040051542c10010041e0401801c1c085985850b203005001d0107a003d070881c000d0540c8900000c2500c12409003090010035035030ba4500054960b41d80d1850719 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 238396852 1250 238395602 238395613
    0x2040e0415050c0913061e060f0c081207050904050903030a0c03090b01140d050d02031308150604051e090106090e1606080601360506090102030d0923 66
    0x14000c110140411940e600c00007007100c1e0a080902140354800c15110b1805112050b07076081568031700e90b100301d00034841021040f0f040c140c0c6540f01500d50002e4028a8040b618001c1100d00d21480740e040c2001042d40a1480c0f0f15000c00c598911664601c004c00300000c1142c100610740050320741d0700905004141c40e41c0115220f0800040d1007040c0c8102e40341e080308041ca080141000b01e114801071b1307411184c0300c1d0082070000482c2d2000c204a802c0901f400740042c0f140d038601605082e40003004040040c43c4a0014240c00e40300c0d0f040302d48441c1000d10840003400c281000c5034003441c0c281d120f650809014602a102c415044039505101241154500c403544d41d0f40900700142032903801611a043c2034075000e4100000744540c00f10304e8006500030748081003404070015405034081e004402c1d65140104c020308019100c5054620100c848402030701c04804103400000c0c69040600a444400710141c0245040014024500c1d004141001c1e0642c0c408001c207901c1c0c0040c803d140401481c90030618080c08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 238398102 1250 238396852 238396861
    0x411120703211403100e0c040e07050a020a060510090609021c05060901060c03020a060207061505060c10021e0703080a050c030402150702010207150c02010201050c030c07170d02040e 80
    0x8002400103400080155800264410495800032000c0c1ca28581d03103d0064490b10f80015a0f01000c4482d0400030164411000384001440000081c00c101c2d10081c034201010740d074001007202ca90041c08007840241c1c3c0910140c3c5c001803029000141e1116518003040001c5941b8107041080d111640d00940c021507002a17039818240c80882e0601d101a04c14a0500080c10b10708041070140320140302c1d07002042011006402014400d01601f0b40ba2908918250340f40c080e00c0c104100100226202e500500d0116140040d550420340203031110301c410103001c0c21810f0003c8204202031b61042d09010100409012482403104201010f440b006020340e44510461411340d1800040361009005a50544014030422005035146201e484008181555503602c6800b90f10050349002100d03005070054682c20a0102c070004d40c000380d8448664001d0703000307001540304c50b000c0d422180700c191544601c0031010050480030600012615007500030184000d0700c0c1414081c0150101d8026411040c0c00d04611004d01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 238399352 1250 238398102 238398113
    0x3010605070605060907020a031404232815090801020406050318030705030409110903010c121116080702060706020a03050411060909010302150d0207050d0f0206010609030b0411120703 81
    0x21603004c2000d661100b0f0b942070900c800703555103061080041c1000340c56030400020100e001d0a90713000300042d64082e039040450701400759601c40481019070160108075000740100413aa880070500d40801c41c3c4904400d41005510007502c1e4103880c0c0c107028031528000000305050300b440200020111961641c3d141d04221818100070201c501031180300380d0050140c040410030200403501140d06005000440f03000040d0032150034081c48604607459482c3c58a80c83c0b800760002d01d0b48440400e40541002540700a04007000740b401400d0310010950000c1d1019030004e102e50300106400c50009250314140702043d40c03150241d074440c900a40002c2d40b42c000780400c01002c000388006c003190403500c00f81000c1c2c05202040003000140b1005c0c6c4a00403402d000388403a0b0385031003113030398420380690155540c8200b410100d583e5140040380390001400f0040f18400b83c1d02c04186a81610041c0d540e0f40b05403031450b2100d1001c1d0901810644803021154180c0d451655002c968201049144025010042c44c60402 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 238400602 1250 238399352 238399361
    0x1109060303070b0f130f060504020a050a0b0f1803030307020d0f080f0a150506070507050a08010606050304060b182805070e150f0a050c01050109090b04140f03030106050706 76
    0x11402580180481c0c0b0004052100080d07008101006a82d5182d0b5903180880c039100c80300034007400c140c025100b00c83c02e00070190040703403007140241c80c4524040e41d0f440c188001194180305140d3304800178010400c280700d101c030082914640710600c40c09005034640029085034000d40745040503070b01c00040020400d8004c0f00c074003440c5145040caa030461070224007950318410024842921943d85040c24103141c0c4001c001400a4240030303280c2c4c4d803514514078055039107200c0350080520480d032141c4000340c481070502901c01599015070b075003402e58555640340009020811104ca5101c0008a2036200c00d0b2414621180b2400f4080d07203507198107081d0300400c40680f030010400c60445050a0070400d080d03801800030600030b50251001284c5000c442c4281035540105100d002c042c40b000540d908000d039120307000d0442007405000801c0266a240001c104440d074601004200714400c1000501155003030720541410210380c8217075511079101000403411540240c00220108101080304824000d05225 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 238401852 1250 238400602 238400611
    0x4030801150903020d020d060c0306060206060409030f052805090405100609141206010e010518070207050d050c0306072c0a0306020a1e02100e0303070801140d0f1109 73
    0x104040d950110740006119075400d01001c0d004154034004070f411034a070009441c403020341243c01002100c0c410b02c0c0060281403184030381c00040c421032003c110540b03401e100701003980b6416222510191860802070381c1c3d0341c0082c007082001c02d10409401c807a40001154040c3c0803985983e03030550303480c000d100708401c84002411040800b072440c4814010603800c0180041034805820050300100410710014000c614206981081c40c002e010000910207000e0f0466810707207a049480f103c1030b140349070034070b4440ba00444214005a02044c01004941400700548030700c18046c4050762000034220021131702e841c00a48a100c0001c056a8400b039114100c400c003c00d468290010111902c084000061040c2203940006021198002413403500b041c000c94185240c0114250792028403c141c2d00d02944071040d00d1100c80d001814007410305540383d804400c17244980035075141c0e05a1a420003c50a0301c03014842d2250350040d54642c0d1410100c3c0496008200061007180d100f0103201c0c8110a10500090180 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 238403102 1250 238401852 238401869
    0x90a02070b0c0919080a05070602160b0904060506030403120b0f03060c0c0f0703080301030b0117032b020f130b190f03090b04050f1c051b2404030801 66
    0x40040000e07452800c0d107401420400a8580342d000d10b4001480e2841041c0362030400c8100e12000094900d4041131810905c0c2c0904255a0300555401c810381e201c1e4071038030904040317907640700e01408501c4ac00d02c090041c1e240c000d8000034045131100302203543c80c1d100f81d50983c082100403c2e0860010828050100070b180b050320b004294404060210ba074507000500a0540d43c000400c03100100720b400c01070a54042070030742c111414182e40e07080514440c1d000b80400e6503900c00c210004203980c00381c6403200c0788440c0302c4c0004603d0503000c50703074140ca03207011903220240004144030005503256003030014006c610200361003140e031070754250110750450000c3d034800c042c00d110a100302d629090079850700d00d1100d90795080c4000800d40d170000443c02000d100400a103200040c00030710080c040c000a407108442c801b2003c946444c414901c45040034945c407030001c40015005c1101b151130a41c0c0c3e241d0384012000366400c942281402800741c5020004c040444000041000300704414182e11412940c010301006 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 238404352 1250 238403102 238403107
    0x10c0212070206070f020916120504020a030b0a060e1005120601060203090d1401050420010822031110200304080f070809031501090621030305061309080405090a02 72
    0x1031822805019904001e44540310218100b0184003401007002201c5034000e00c0c000244c0f51090162207503d1400c126040000d02d140540c0c007240c683c601c42d0354000c6400920010000b4519600d5000701000241803010103070321001c000079208074215941d4000e02103511000e2600e828201840300c5445501b803041111fa00601c0104503041d0044101c485204050700c01070000602400c01c0300c01064240440d20444d880e200c100024400c02e0310161003081076586128161003005801110401004d80341034040c080702811000e880c51900d004070080501c01c1c245441101e4041013200d00700015040b00b4204d9a4031000e000a042c400060f0440d0300f203907c04060760460901e9159410540a03522054a281030300280d5042400480b5054510b1110010304580d140c000b40d81268440704028454195818242140420b100702c044101020450800f0355031142840c4e02c1c4ca04070068480600900c0d080084030b210300d21440030074000c0c5482940680b10b02c6030340b14901018070404003001818940c405105 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 238405602 1250 238404352 238404373
    0x9291909052d0103020f190309110d031202030720060702010e1603031202040b070c03050105090102211305060a020c060112150509010213080a1130031201080609010c02 74
    0x980040c2c01002828a0b0050700c4801c058811320040c803c071038031240400303e010401100c403640364210444003417158000883c000e207504140318583c004d030000100420205024480d45100075809168000210314013540c140c4c040c11010702865003012501c1600e5040380d400c0118103078090082c803607840e1203035004203650302580302000e410703414502000741044030380300c100c014440703540d0141c6020300100740c89150340368100c0c0381090a035425840100e8441d400d15000510b140e1040c42500e0b10950081620704950510117a0a410040000d124002010100300310201098013004810304c15940000010b03034950700800400c0c5401d82c1607101d4400110201b44510004060744510214841c00c003102040703031b8459411072400790141d60581d1440880013000040d910800241c0d020703a030350040c503404410180004c24032a020f00c00c01c1c0c59a11948840100c0f034805088501446405114141528180b000484603c2c0c8065030a074802c1d10240e1018080c0304100e030080c1306450a4a1181c001441d03030108 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 238406852 1250 238405602 238405669
    0x309010c110402040314011b03150b0f130303020318030705010c030f0306080d030c110105100e040303060e04060207030f11120f0c0d0c030f0929190905 67
    0x2190000284295041e1503201d0351502e0380d8050b01c1c055540403100300c03c1c0e003941c8183c840c0284852a41102815400403400c55014007c0c4101481082d428070400941414035007400401e510030b9154960701c50082104090002c0c004c1c1124010b540b003580075641d6003000746040c1a40e0041d20500c10722980040350104840c0e07030844480c0d90036035071504100081c1440200254000d194070740c0625030300d000f09640e4401c3c0716419800042481515126424108942c810b0340f800c0750411903051452030003603501844000740074012240c2c414440c1c9400b0035a151a00d800d84003040e000c0d1004c5550383d8012070180d00300741c7c0003040701c07179007070501c0c900000c5020626410681c0c1d8601545112240c071000556461400400000c0341e011b65042d404650540d85610741c01010411b5896060b000185d90003030308554035225070245400c8580c08240380004a86074070034204445400703010300c100785904000c0400c100c01345881c00042210311b40c0398a114280780030103004060017030030f280f04050b44446216216001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 238408102 1250 238406852 238406867
    0x20f09090f1314010e0714120304080a0f140106031a010608040b0412090b030907080114010f0608310506061203120c120903030a060501110c130f060801060314030901 73
    0x6802070702050f040d6121000c0349004088503643c00c44240034003580030611880e001e0440400001c2a2500c401c0e04106080658403806580180f00b03450b0064260880801c1586050103c082e018140d80104113280b048a03908540c4990710485031070100304c2041309042c80071007800e4010840f030304201c2d89034a4541e0391b2032107034400240001d100e50b040076103440f0304034441c4000c5c0c3c0c00f40104000450b580c0c20000e14180d50707a0303030300d202d10701640d8200201c180712840c45003040781c1225512001c0300c9095080950654040c20f0060400450341c0450041251800c1030402c03102c3d640c58041c400104407911424202d007812402041c0900400c00e800c1c1c05c5075031a80c00021035030000c030300c0d03448000d2070b48552f2490328540c17194001c05d00c1030261150600069240c0800214000c01a69900300143e41d03030307500191940801d9840302c01080d006640a1070706802c0ca04841083c030104030200140020b03c000c401d01c22610290000096695940e0090003040350300c244032040000c90400a40c1840380d132a00007807404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 238409352 1250 238408102 238408141
    0xd0b0708090c060408100506040c12110d0903110609010c090902031008161d06132f09040f090c2106050f041101090f060c030c0501020f09090f 63
    0x542400041040038207112000c42c001000f05003030340c0d560b079030000a030780e40d55400400d0210510341008600c0b54038003031103070842d540c1040d215507a40c160240110303402030813100c0e8034410704482042074403c85280340c49600380b82031181c0c940c1450400e8080b022840c06400902c000b0440c0e00d0701c039840d03c0c0303141c00913111003c4401701d11015a59640e1421000703584100381d8041c4002d84201c0c0082c1c488082000081000d6900c8180000c100603004042080143d0041e40c040c1d8103d030100d0040c07508003a4940101c2e180902285800c0c0b103400d4421207005483d110045820314150000c0b8192105241c54000c0ca9100d151205041c0b24128294598800c003244600c01c03000080d002061030f02a0704c004405507106c1640180e4200039070b02c1c040c481110711003812142191020540c034001886c941c0142014004d4601c507424800f41d00f828410141d4034440b142d1000d4080c00b00d09812500081c2003400100010042810140d403070715140d030103212543d02e002c0e140c0307812198800c0401404020400c0040c020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 238410602 1250 238409352 238409357
    0x10f06080a0e1c170705071e020d02010e0f0904080a020705010206010b0d0b0a2c0708130308061503040507050102060106050a0509040b0d021f020d03020903070b0708040b04060804060b0d0b07 84
    0x5011a410f42035821041c001c003000e04408012040065080d0000c0280149a0292001ca2111146005c0b0744841c0c003c840002580001c9240822016501c103211502900802800503500307402c601001820303040f07007264110344c03040340000d5000d80c10b5810310000004207400e0005000700e50400e80002000c0c05111980c3c80c1c80d43d40c070300d184445681e8a15400e4010049124103403141840d10400848010700b40115900406072600410682c6226280140c8203405680e0784184264843d501190303910800b034562684803e1468004402c01c8042000f1801244607400a1440c0d030f1510b00068144a41644403034140001400800542c0e50440103c49842c0350803030700000c00b940c001c40022001c0304044030181d00101d842100f040f12480c0280d80c00802c080303d4085480200822204078241e1054500d980d8141d0003c07142040755480c84000350540a106102ca981441d4949d00d030425940c2180e404a0001000c0c002440144130320b034415281c101c04240c3d520220b50721721f5151610703c0030300549540304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 238411852 1250 238410602 238410643
    0xf0605040315150801060302100507020d14030415080f090c0604060e01020a06061d1503280204050708010312020a0b0c031305030a0909060509132405010f06080a0e 72
    0x2c8980964043d5800e04940c0c0303050782c03590383c0f141c80803402400b603400200d01440d2401ea070b20085500036802d490704030b54003c041d81407240743c2e6918003002c080a42182a02407005010104011003132030280c0242244da541e8058a52416030b8a2a6980101030302d41082904004640d09898440000700e80955170305040c050380480c240d50040389841040f21019000c3d5140100200714602c09042c640c3c4110001d4a0803812074480552a004810000340c030b45c2d9050b841b843c1d01c1550661004251801207002c0080c4a0007240e450b004281070b0f5104860ba240021051001442001100000d0141c1c2c0c9406200400e03400510b0f41d16a01d403010047c2c10100c80b044040001002ca000c0800941e424039800700c103a0b502da03d00800050700403202c50080c14106800c200002c2460b027460040c030740c441c8694055129403084030351100a2406540280c41624062042c0341400c8862140501402800c440c01403a0f007940c5800300051840700301510744400b46080c94041201080c00243c0c889120540156a45 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 238413102 1250 238411852 238411883
    0x10e01051809010b19020f0d0c03051308070503060108030703091211040603080301090e01020f041505070b0c0901110c010903080309010f1d070b0a080408030a020c060a0b03070f06050403 82
    0x59a004521050982c000500c1c8004036180c110080604050148a0400003c3d40b1142d9420f0b80c4410701140f20417000d40c408100d540c422803091105501c064060b0801c2850009460002d138008001070300400401c2e4800740041060307040410581c3d005142c240055402c0003110f5900620310420340c407c5c180b608907010010000d1000300808013041000040007004410f03500e150891058009120f03520290345050040c00b41c1c010103008079800c070707044184258a4581081c1c1901804c40048a8103070404c50305024800c0000d20903130403207002d012103415050b225426080010a074a091030507099607600010315406090360404082025258410425603c2e0303500c41d8840c0d40181428542480e556041c91941c0350711400845400002c103180030151140c080d07e8064140f107602c41d6820950001e001d000008020881001c041c40d0030282c1c084d409440c00c0c00e0249002c0ca0410140d50781422071b640e510b003a071151324041008500038003204500000503032401101906900542c480030b80361000040c03070352 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 238414352 1250 238413102 238413127
    0xb0a0e130e030711040c020c09160e031005010f060504032001030f022809180b01091a1803061e09010b1c06140c0403060207030207080607030e07090506010e0105 71
    0x807403400d190328040365101c2100d8100f4a0304c146208960900032407034a80c0d488040b03440410100c13400b200203018002c0c0d0380c4590b0503850450712207400c40703020442c0c5c11581e101c040d542804020800300140c1c20208095040070120440e07090540c0c0715074103000041004000045110540114408074400d0410040d440c8100685c049d0000110840b0100d20015101e0b5000016001d4401c00000908000340c0f20400720303809940d20300c0345000b4041d241046450380c000860507600500c11580381854528411555421034075801201d042c100003071103e012400030460b41c42c8030b40780818440c0071802010141803003000d04500400481085410324000d50001e100d2510035040b41c06448000380415510440c4000c80f1001001d81030f02c1103c0c050b0a0140051244070700403003142c0161184001c60b85040d245940e140025444070b4001c5040d4010070000141c1c0311410301410340f007011360751804a50030209410060501030150005000c5e1440c0906001e01a41e00c81010036148600b07080103070b80c03000940e0740e4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 238415602 1250 238414352 238414361
    0x160914011e1808031803010506030703120507060c08061c1205070303090c08070608090604050c0f030115090e1204031a130506150120060a150801060b0403030206010b0a0e13 76
    0x29442d56a9500c400540d9420020041c14a60b819400348100c4c031000c2c01c101400d8600c1500d03c04e42c103902c221001d20202d00c0740704d50801c3d1408141041803038039940d81d031071a003580c881c10704250110b0117070b82c100045c0c0c0c20700e00e0740060480040700d40703075424191700e644a0100c8408407000c8000c204001c00c642007018000d50040482c0707504801280411a541d050041da140c04a002e18400640d03241c0201d101c4800000d0b0a038051507105020b0107a68403c1c0050000c05156803444990542d00c80c070200380d0f5241510490800707010144008140c800c100c04580d072070038955030522020b00904010400224000c07034140c01c0042c03801d80041071180c8801610000c001d442010140981c0103d41c00e100c10b10405040e0f20100b00800c0c0c8500010840940071052401c541c030002c0da000d038108000090303544040c8d9212801e030b883c0001c01c208010b504ca4608900b1101540c200403c1003800240905c01d01da0104109130045c481c0c012103d2503c203103020002e22070061141303118040c02981c039044d500001d56420 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 238416852 1250 238415602 238415627
    0x10030605060a0b070c03020103150b070807080f070f110d05150406020910030f060e011203030b03031b0a1b08030a0c1104050403030207120306050609011b0803160914011e 75
    0xf1035a242d02090404480d009280d210490210b41f920400e043c2101c200340c0300c04100c90b24421510304041341500c03201d01c2c0e94408002202c20510030400306a400d14100c0190400c130380101140d0102c41001e2805502c0c951054052a204214040a5100041c0e0000c4d141e1070801d060301d04500d20743c81b1454070b400a03002d036140c0b09510403030f4400e40d20304030b55150b0b2100c12503e012840c180f01d4142d4860050940300707400c4c06908031043d00c1229460101e8025080030780c09010141c201c0740f4100c0d0480720300300e0080000c01c13614101d0f00080a507000740107031140d081880f482c03100701c01c140180c5800b40d0603039288034808161052080842001040c01010070115045000142017031203580740c1464014001d5001e004203d0300100407111200c2410302c03922441e4152000980036510b071140389001542c03040c200007030003800b90031405060800500260041e5001d42198582400110704880014105140d9900b000a5101c900c1001c010542c1c0d1000c0e11360410f201c0c140000301549019001107548503400c42 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 238418102 1250 238416852 238416869
    0x308040b13051f030606110706032019080c192303010b040303031a030c1c05070e01060f030e0c010c020d171b0114011205030c01091506050a0f0311031c030606080c0310030605060a 79
    0x1401380d030f1a112603340d0089080c0385541e100026981d01036400001d016030b100b400a50004110240c13262409000c07c400d1044804c81d1400c0071105451101e0400e5009030052012030001140800c10540c1602404102940310b1846950002c03c0c140400e550fa50600300c10ba100d4034604851a4400320080445090a500a400d440c2e1460322040c201c0c42e54542803150900064102d020703030400318032034410403002805600140400c00c130314600440b944440404240d903c02e09003c200400581070b02000511301600c04612500e405003901c0d0381141100d441c56190881c0d040070800403682d05502601e605403007c0b0100d54150503003905082c0d2a501079000d82400a619108030f00c002d014090440041c4400020030038043d458945061001c980e803e40714600e200710101030140005100c0c0702c040b41e0305103c05000c8880001905110b00c154861800c08100425511503083c08039503070014038180e0068080301410b240d0b007480c454440d030000692102a01c4269660080364080c2c0d61020101c0c010711030708 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 238419352 1250 238418102 238418107
    0x160803010806040308090a051203060102010f061508010e09030412032703120e0f04110702030703030819050906130203070b0d1506090308040b13051f0306061107060320 74
    0x401c1c100ea910001503600b83e0103d01100c0c0041c000ca80c1c0040c4103c030150303011000d4a03800101c1c0a600c0170a800c050000d50665407680c8100841c040320b03104000003400e00c40c2c1c400110404001010380700401c180c0102c91518140001c000702c0c00c50010484003100c03c0d86407849604203480c00c0807070301080306010760b1440e035035440030030424103440550400582e80201d800008841c200e10040d80c19110820580340c0000001c1c44140891616a20460208410140d20781c034201f00d540c000380c01e000720b0b90421404911001c00740100010380c610092000004c0e89000c2040c0c1c20401002035848000a25900c50036042148442c2103490501c11107008100440d285a201d002d0840c03140301410f80c0e40005804007134240300c0001e45e0751055441034210f0b504150824034042c20080001810b40c400f0b041d88040c14810480000c05840354180d044c090034051200a0941045403402400d40d121030307101100b0840300c0122043c81040c00b0407032200f111210f0400107400c0703d05003a445104034120103004101c0101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 238420602 1250 238419352 238419359
    0x1209030405011d0a0323060601050a14070609061b0212030103020117090c10111c0806090a020f040b09090901050705030a0b01260709080a030c06240602030903010c0c050604030516080301 82
    0x101580500c00e000311b041552032640d200c01c011a401d000740011000015a1078a10380d502e001d00344000d204a43c091100450803068a866440654141c40c000f034101c0d2100c10b00c1003000d2a03050000f00c021121011586241d5413650b0002003400d043d0004a0f079a0015510118001a40411400c00002d001074000804003881c210041d208017075a09070f2581a0056070144034200c241d1804404218056445501c041d8551909000031818002c100b6000350b5420000340d1606180000a40010028081c009944112032024014a5280034081c00940e80c141014000c105400ca8103890f445070004c200061507060000048034002802140111003096042228940391000c41040b44204880c1d00c0311100c0d2039580710519a2080319010207030004c4d0100345005c002521a400440d00c042c2c0e0000c0c1c48032078811a08803203828030015030000c0e000da0320000c0c80079041c2c18207000301c3d40e4894850400c0b402c0300080d41c81e03c82d04e40c035000b04028200f00c0c1c0007941c40358a25009040629107500000015141d40c0c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 238421852 1250 238420602 238420643
    0x18240b03060f0613210606030507150e0906040e0a060213030c15120c0e03060a2004050303191407060207022d150d0c051209030405011d0a03 62
    0x30a4030024010702c401c078075011a90402d0003c0310b01c41044c40101207003092421040b0340380402e099801c0140005092400c00102d5003502400c80a140120f000d89007840c60050b00c0c0020f504514a210f051007824819a40365668000340d80d9402207045c1c40100b6100d10f080302c01402c0c60001c24005110300d10110300800095a050000d00680e403044d1002e06042ea2206280342a200c5055801000034811069070712201003079802064010b540c41c2400010751102c000082d040c41c800325000b1803820340d101245a21100c1c02140000000503504016242c14100404a0740368400c44080e00115171903207903c0c284081c4207541c00b800b642d80e0000c4150312003102d8501500a540003d10907486003415054441010640b04011100c40c0d42071a1895280300c1c468017801981c022100e0110f40d0350405000c40c0b51a49268041c00c0009083c581c1d0f182d40d1400984005d407035011010b1f040700004c0d03200303000074091039030061415090481e50410580c41c000c1030b080012020355941d040141a2070031051520991107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 238423102 1250 238421852 238421857
    0x804150c050f0f06010b07020a0b16021306180522050d170105010c1506050306330307030b0a06050d03030605240a110f0109032718240b 60
    0x500c03400039903408a84450007a6654140031050002c0384e04000c00410002070000c000385003041c4050003218101d641d400c1c020855400c070411281403a10000307107100452922004032a1035010381e0f442006201d00b444000d40740800c001111143c650741e160040740d9140003000344500144a01410410800c83c1c0b480c0042d200e000c024105030108042c05201980c2d000c84d0088a4141d940c10394a500e4584115110900c3d616030992944441c01c1d42e8410118081d1018803146108004028096500390070058060713401c014800104d16442001c824096410364011615100312500903102c01c441c2c2c0c03240903104008000ca644006d1f80841000ca44404040e0141c02c01400c4400454030680400d01402e481c42c3d0404800350f20022103201005041c10041c001e0145c46802c5440700f084401024141103071b1421610921000d50200c7c0713250410716100b04c14540c4002a501c09104e000100e10326062290005c00760b45c07905000802e440b007000d0036081c1c24258090030702198102504494603503404410900c0d5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 238424352 1250 238423102 238423127
    0x203060c090112140403030b06160c15080903031305070b0d09030306050118170c0d1b080f070524070308090c04091e0309030203030a110606010309030e0d080415 71
    0x25000b0300340da00c0c507400340e118190340d1381407410401400343c1d01c541d4200c004003445407040398001c40602c80d401c01c00004120040c0703154410a0626215401c0c40440c0d098021002c003580c00700130002040218024000c01580e4101580021600d044107152a1090900165801c108808000820a0b1075121150303084160719a00036203082081e65210801140c001c6401030191032040188001008188500300061100c9080041550744106a090008106402d862000d0b20050104000050f0781201c505404000340079000083c0080c1d0722001629440341940e01c9180c1c0b069807a41c440e04450080c0000b2200071540e01092182d80712307428a00a000a0b50650702c1410324032030f40c1c409130b100d03003040e105040b0290b03003004099041c05a112090304000002e1003044080240100f030000041e10b0410217000f001603182c88894000607002001e0349800f0300100003d04040c28110301501007a0000c507440810312060314900024595400e00700094415613000e6450655081000103c1d25070100d81d00303024 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 238425602 1250 238424352 238424357
    0x70f03082718190e15040809060a0c11180a05040f020405040f03021209150d180503030415020f03040303090201110708010e060108161511060a06061101062103020a0203060c0901 78
    0x1620360f40b071107003180d201c400b60390016404070341803d9040501c003020b250b001d0b100d030038140d10307060021011581c550050440381d00030564060741c04007084442e0320720006050702a942910400200c40b2040300311403024182d00b4440d41c0d40d00114051029030107a04036415005802440307503082615101d02402411401680107000d07400d550406032519104482080d1001451411501030424100c025540b110b201d4014160740e40e000300b01071104d0f00c403141582c14050006941c9900c0c0608002202d4580d40c000c80d2130051040001d500407140e0842038035080b0b40c05d0310700001c861500c4d100680302d040103d1121090340c4582c0e04d00064403401508040c03421100041a00d0740781c5d90b28071103613990300000706820803011110322051014030248102c2a40f100c9141ca000d0000c5581c402e13403181000026a89144c03059215502403089540160180302a09021b0000304005803903e0350146030074805020094100000d00d56200c02d01d0710030072440e0401034006080d14903909056a81110550011742640d01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 238426852 1250 238425602 238425631
    0x1111506060f1e031905090c191212021506060a050c0a06050a0608010c02030702030d0e0312130f052e110f01090516060806090402012d02070f03082718 67
    0x342e00700c0c170707000b0940070304801c80050401c4840e1000b003020041000101107480500a94001240200c040b100d150060058980c114441c05515000b81001d580c05108240640103d00380581c9441c0c2d40115446600a4036005841d422440c40642c2030400c201d40c007424150610050180640442d80035004a840d030384001c20100704d200328140d80303e016480029615401031001c0044d01c1c0d005240030b50044100800b42c984074520400b5542140d0080c1814040b031a00b4013106000b10100c1400c1c40000e000d00b10745a1912000030120508901e24511458511004019a50700c4142c01041c007960260301c24010760f502c8040d151141802042841c0091750386200b801380c860303039840d03520361140c058404aa940902668a02090203440d26001c2c00c02c1713040169881e0318900340e10f11403180d49100c002964a02e601855401c000900d030400940112803416111902040081c1e0140122a203170f401d030501c040311101200c00220600300c004410103410502d181c0d0200d80c81c20a16a0080c0714140c412401d40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 238428102 1250 238426852 238426891
    0x2190807090b0301050904020303040503030c030408211c020c070303020604020a060509031203070c08030f04051005151908031210080c0d0201050d09060e0a0201111506060f1e03 78
    0x140c410201e80324400400074100014403050070010001039000e400641180c2c40c082d5a0b0020034134580c40300c0110303040da800108061001d56000d20020b044540840c074012400c044c0003504500702c0c031030030780a10a0b0ba0488089028007060030707016a40841c44207002c2e2140c040d9242000394840d641103408901c03413649810086000340c0100140c80480101900400c150079484480c6001c0c0e90028160300b060020150b601070004800e80021031182d070b003078000b80c0310301d00341490510700d0004210500b880b003d00308070820000b00201d03001c1000801c02102d44140700120710490a041c4401134211401034000010f2200c04424000c1049002e0640034403040405580d41c030f00c04d6190030701490010317480fa040d104c41c01c0143d8032a401410014030030301c45c001070401050b0340d21030841d540c10107481c100c0d0300095031460a568202c2d1a6009240049000d0103405032030045a5400801c01014240b01b0040464050264243c080035a10100711010856280040f44140701656030002c4a24440002e2400c0790b070b6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 238429352 1250 238428102 238428107
    0x2070b0a02070303080405070e010909030e090c0316090f08010203070207090c0519050c0f0f0d0c0218071107080307020f0118181509090b0601020601061b06020c0102190807 76
    0x19080e01005038050221141541e03400c5914000240044d10144120140443c1050304981103e008010340d0303000058006140c640a04041d4580d46258450aa40c4d0208407048610004036540504d04200c0361000503110301040e50202c0403504685910070403044040390164055006502840041e021203403c03a0b901c04182c001d1703e0583c50180005207041c004d00400202c500051424540a41000c03070414901e00d10651078503004040700702321b5500209250800d083c091103405204c0c406072410000c0227180307030080350900d20244071014180981000050400744034500d00c1164880c0c40082c1d5040741d68400c1201c1d41da41101400340d10402c0b2090700601c6d20b600030300100c40e440300020703010004907203800f5100703095207800c40b110140c4c4d03500ca00c4508110140035032000d021b0b00c030040340001c240f020f6052881d04400018913546c15507015000521400750030100100c690075080801e80d0040903107241034406030040554200466001003400f9101c1c00512501c08600140c0b907490140c1d965494908 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 238430602 1250 238429352 238429357
    0x110403030507080f0f0d050106030b0111060f040503120a0507021c020c0118120615120510052508041506060e0f240309010b0105070201120504020a1505040602070b 72
    0x103011400c108180c00c0001c0c002d1002e025500e44401101e4184150044410b40075030014218503045503865005210940c1c140c400c20b880c0040038641070400011a0980641d2800c000d00b07411044c05088000908001081080358021901f01c2d4601159040043c0084060b100c207464010150003071803003004c442021303901c140c4081c1395a0341c01070008803021801507508220850340034960034488113011a0003500070880c00380291040c180080c1202d034141c681c1e4060f000c1c2d90000f42940c3d101011420204100191010040d89201d8001505843d052101000d2591030310184d821200c1c0c440000c0c6d4070751f810150407481607004280c15180502042041c80840305107000321004140300035201e040508049524000340d4001505011400c1545c0751000c45000c038080c80c00c000703e1800010041004001e0154100c0c01400307080050801c6104d60028100a04820120104581d5440041c06540d5140c008030024603010444204203140080e0007010390340640184009131140140005290021408 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 238431852 1250 238430602 238430609
    0xc0c0607080301062f03040504110f0f03100f14010f030e1e0a050313150305060102060a020903010209100e24040e10170304050414070c060b01050705011508011104 72
    0x444500d584c2c04d0500950341000a01d0602800b40c00341e0b41703582c06203c040d1491903c90200c035801152107030b01d42420081521148052024016402c2c80741c00981031510042d21324002600c0100340d141d660b1448903200030821988505204800700100040e60788174414a91341c140c0c42a0385545010381003100030b40680344401101442035000110705c00d1201072454405224091000555401000c540c0b1a9482c40d003254440c007040c10010b070310800c190640d401820013028003d080511503807070f1820010f0340f00e190040401d492176400181d25011940c0079030480e4450032004183d00c02d900e5500d0130013080c040a0f21002401002c1445980d01112520f000c1502900c070f03201901c1d4940360a1007005540d01030090314901289081c0e65000c02c0c00c20400c050500c200c143d40000b151280c0c50502033000b611984409104001113040a000704c03c1e5008a0300c1803260f42220010584a003040012583c80c0324419011b0b0881d4a040100b540c8038400380810130460b05520024040c09a400110102500c00c520 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 238433102 1250 238431852 238431863
    0x37090e0c120c060301080114090a0503030118060e0702010504030824040b1c050607030c111905071d18010c0f080604060b040905040c08011b03021309020f0c0c0607 72
    0x4505040e5440c01c0d4a040606000c080242d41115909001241c0d954100703800817840d59441d40384080d1410740140c0c60640c80a6400010000b6000e43e48805880c0c0c40117004203000d07400303051741001300e007c5c20790000300c024914681990075500c2c00100c000d0003001c05490850015210801290b003042540c01e840c44841444000302d00040b8a000400008203020600a500500e50040b22400701400f0000042014001c401600c59803400078001800c55840c3d40d078400c03c3c0941040540c01424000809544202e000140080902800d040440c078055682e400040c981080e10400d501100b1820500360090210107008404943c10300010b600340c0e54a0214100002c02d0b000c00c40d5403061140e4400c94110307601810019903036445880d4001a980550000e102c05500d500c2800100321500704910001c03e4440000c000c88400e489030182e80f803141c21403503000c01d03130003058100680c8003a40c0501d000f0280282e08650307502032511140c40d140c1062202540d00d0040c0c0b40c2503040c03030800e9012a00f01c240e100703 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 238434352 1250 238433102 238433113
    0x20a030f1b0e15060903070608220305030414010c0806010509130e01020408120309120f0403050a0f0b0708150402130902040303020c0a090b0f040c020a0615140a0308030c0937090e 79
    0x1c5009c8644280c0101031400d0008d480e41c2e0b902a400d6010b100c02010340c005d9840726564a0309051115800003180e5102080f81c4c90491b8115100e980249a59000002464002d070303180403c0e00094900c48208001200c030601d04440c01d04601015401070084030842816542020907442a1074049d010840d5202c030a5086810405500c16140f00141084d4440314004c908064907a114a4035159044d1422650070f84802805420f2028140b18694421001d01d040038041c80c2800e100f0a20080c19110a8000c1c0e4010810a0084404142c00c40240103200411520340c1e540c0c5c2802556074400e500301134029040d800d004542d00e5124012541d00000203070034250170b44080000e102c020895007140108501865004000044a0f4000c10b0b03030b0b0010395500c1d1201f190908400000001256440922500c0303000760801c00a9811002d995110360074480701c645450390140468489406846182c0380c6083c1d5400b680300c0380c06001c402440701c1020040c1c0003080d0f6280c071081c0c0c0c04c035540e001c1011080e0703000c1c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 238435602 1250 238434352 238434359
    0x409110607030c05060106200a0f020f011112090423130206160309050405090f0a0b040302010603050a03091404020a020c22090f06050a0504020a030f1b0e1506090307 73
    0xc0001051100e01c40c1c0380140f040702c5a84c0321079081103000e0b04040d0000319482c4280c0c02140030080d413200310b40e003440050003010400f5501e8656036491050000d000c0c11082015506683c00342c030410701214044001d0f81d10400d40d03500e03240900d5003d02021481280f809802e1300605840d0b80b9100804d00c00c0411108691b00ca201c21000015602902264003072810402000c0303040f40b001400c1600b601c40e88074280c00d9424481040207a41d001803065915034011100d1000c031000000710004900c2e0400d2900e0741c29180d038203080303002d0480e582018102d44a408490020168850a80350440700320b400c80c5186180e81000b08001d9205065181d001030740041b80c020010f01d44803180c10341c00512039002414407854181e4040640d8940a000d07a0040652000d000902000c1e001c0e8561001200754108003a03d4240e0008003002d030b06000207040180c00114200801038402e00800000310007021502c481c981d11040d001e0316540403200207482810a40420700e40307040c4881915001c45005000c0c12280c0d04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 238436852 1250 238435602 238435609
    0x90f01140f0a060306020a110111130b093f010b0901050108071e020c01090806060d200607290609180304050d08040f060c0f02040b06270f040911 64
    0x78040c20032100d01d9910b950000c006025440203004007801501d540d9109960700d04074a084458005181c0a0080104850b00d82c0506000700e034025960400301e40790312441604007146004140b08480300d100c2035450740390440c00800840502e00c0c40040016154010300b020880350995517820040c54000b0488030041c0001d40c0152001a0310840915140c071185404602000b9824540f600e03030000740c2c00010440b000c0303581c007900364130161413594020080350a011300400c81000606002500345200501c280094ad40400c43c1040503c500620300c41c0c507182c0c1400d005000e56134000744c1d5498000c403900c0c0724048641c5100003511076040100004126911841114400c15108003d00100c2c0070070400411959103c4000c146030a028011054079541028030781c2c1076142c02038104500b404104400c0e940001d00c181d05260b240307a030585001c10200a81008503050380a500324034002d0b419000c200c4107504082c502000e04a81013112107611240c4080c05020403500c40382c03c00780c501c10300c041c98120700c0d04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 238438102 1250 238436852 238436881
    0x602030904021b011a0a0e090a060b060d05010b03100801051e060409050f07060306050102072916060c0f0c1a0907050d03030e1209030a060b0a0801020f03090f0114 72
    0x785072402801e0071212420501d0840e52808010030780000e40c1985c19205003003c00c00040948080b901034662420700121083d52062101d40003040c90740c583c201402e4640322401944d101c000c11180134000c03540c4810b98100c003904121001c0120b902d03143c3c030000d01004140074140c0aa41c0c00c00e0b154945071007000c0002d0080d40000c222310b0b04103032200c1c95880060410091030320389142d008090147c1030304110006040d151258007140c115488034400313120004e007110016041d0407035030108071100d030300a1880f01c9880c01484144800d081010700001c05102103a00b001003e03040136681c81342c4103200000b0980b03d0301c00040024001031034403081103030318122009401d6000300c606022904c00b160f807000001e070b00042c500700031000240c070b0b8105400044c40420031007a2944bc45000b0030b0401e540d94000c00c5d540d014042000c0c0400b6140d0410f0401520380301c04000203040003500a55030303464400340785022603009981c0c08011748180d501c0f102d0800c4040c418038202d40d055100303020954841005000152 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 238439352 1250 238438102 238438117
    0x1403041502040810050604050105031528050a020c010501050103110714010b1903053013032325060c08130603050403020c03060405030301090f0204050307030605060a0f060203090402 80
    0x580c00c102c041400042008030040c1e0310b41d500400318040c54040148800ea234010b0b072007980280d102034a640810342c80150ba450f840382480c0140c8100d086103000b0011011110b03200c1d8100d40d80b5060600c03107540c01030b40042001c0c815403c0240000d0b41e881004608a07098200104000e05041c01034000144101c0380c01f10542c0c049400126550b66200002162480c40741545a100340e41d0782c0b0b08008100d418401030309800b022031001c01c0784494101e0340402c0700c040450b562a8030310b4006058620b101c1c900020720040d50300800107010f0100b04041900107175000c040500042d100d164004080008039110075000020340c00d07203200c0d4143c40e217041504d2002480d0300482e1040e905000a110203904000c2100041800ba41e0100d01c0c2e0030181006800d01c4400d5502c80d0081d00100c0410012580c000226811140c550340e000611151509071200240507036003016900d070040c41030010901c04160440c5000e03440844d03452140503903e251000002c803261040e440540c00c01d1202c275525113800c1c0c1c041c10340c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 238440602 1250 238439352 238439393
    0xc0312031508071e03080409090b0907080316050f070602060a0f1a01030b0102070b030a0507171611120d0b0907090303090509060409051614040621051e071401140304 73
    0x5072500c5c0c0c2d460104940084d08004002540e800801c1c05005009460a4100211202514000d41000b00e91074617031168004218402c1e1000010904000301049a00c2c43c88540c0b006031891140c03150310007500c40300207881910b00d6900b0031b0f0380001c245006100d0580320300ea4001c2d40310783d480c08020040d0050010314054078194050807000040a0003010000e51040002a40024071450274a00c0507005d0034102605003280311001c1c2c20403a014601170301c401172484942c28000c0200030104003262804040e80080a03000002007588182c0c494a5084580f44200499070f1740040d80d1548030865120302948400350000712100310800107420103440d400c1d00502c0241003c03558428649500f840c003541544000c0c88160400020001d10059030a070155185040724103112070b13403070720152a4041c80e0408054005c0b690074207441e001c10804001203c00c407005586020084404e2030039540d00c039246441201403050f56008800000c0d03105030415201964a005001c1c00c540701c50719600c00d003401e192070900e903 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 238441852 1250 238440602 238440659
    0x50405030c0d120c05090d260a0207150f1d1c1a1005150f160b040c0806010f120507080f0106050f04110a14070c031203150807 56
    0x10504180b0a02c044003016448450704036011600040441310040c90b0081001801d2000c0c2d20030b43d0716a920705a1480d08030400f4408900c20400183d800280c110074503604940c001003a81029030081030280c120340c0c1e80896482c5210522006036010040c45c240e140019240260000326200c071040d055001420241013010799511141000181e04035020301610b40c4958101c0c4450440f040b2802e4650101c1600c906038030581c41c6c100847c0c008000c150040b121003101141c00c81003140302d203090f07504030040d0144a07520b80b0094103050900703000039a015035001100010120b04894001122412940c445100e0510769140400c00080080c1c218001c4815008141002130001c2d003c00840c0a09510140000380c0140380004000ea00c8420042d02405241042c1400701c070b01c018503040da89140094100020b04845401c0d050f034080c0b2490200800f000d03448075021042c004100348030380c020002030b01d04115081e82c000e003d20301a000e1384111116980f0428051000e581520079512200ca1449441d09 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 238443102 1250 238441852 238441867
    0x81609050a061706040c02030a05070f08040e010f170a140f0d02100b04090507090902010915030c1103031003141203010b0a02070509090a0f14060a0c080718050405040503 75
    0x46084519a12030350020341c3c0c01541c00303c070701c94000c2402e410140840d42040312081d8240c0181d01d134012820103905100c004250781060004a404000c082d80d88803803090f42d1192581d038030014001081c050b41c12000c00f0315001080042e400c01c050a205d010710b070300406500040756241000aa41c00800314000d000750740290b10720100c1005030300070440e15600a407450f54007a001080460380303091000b41c031803414510410040341000c1414000d840c085840415015030b1800140c94916241d4002e1444484c21540821080d5040d40051089140303552022404100c2003569030b660702043e240176565034021201007000906031003031660b16548030b1050714018010f0080081858100343d10501d40200c00180c10504560305000f000050901100d582c80c1d5030a02503805651100800001042c090083d40d24ad420f1040b5600740070007224001044407440c3c9064050389000d00261289e030404200e19101080007180249005d4009480c40c1041d0b10107103240504010191070041c04c02c5c1c965000400012 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 238444352 1250 238443102 238443109
    0x12050f0d1509141602070e0a05180f0102040509010e010506121906060c0210080415050a0213080309011409030c130902090702031914160204060905150307050a050108160905 76
    0x1e42e0410b0801c4103e0f0300c61405000340101400c0201680b01150414581031003d022020b20b0560082e02d01c0b803000405941e4080034222011020445180b80c0c41007600048401c101500140b003911015944510180d82c2d41000c500050820b00030700764005024000d1030a039040d10403200d64003601d00d2402c4940c41600100071021240a1781180c400511559110400d6042c1506400c0b40e4000c41e1612030010b00c2c0c00c0d10b40070b81d52104010610030090316400403070401ca95640640e4800f4541c5c02102c03200c2680c41550a82c4c0e6400b0340100b9002c41c0000031512150408030003942e51152024000d8241e9906600c204844484801c0d9800309159994000d0f01c0541c139229440c40c4214082c0c4c005580c0ca00412684201e4100c00801030000c02013641c00410790a00d01005803241031440b03080760140041184002001b40c15650403545601e403800c01000034204114085103001c03082503055a800d0340d2600c00344120106030707010752400b02d24070a010036088803090b2528070700b411142c900604071603180e5002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 238445602 1250 238444352 238444361
    0xc080307030b190e09030702030a0209070c0203010c0905040e0d0f0c08040f06020a1a04020f0d14100213080c0a030807020a1a030f07080f07050a02031c0912050f0d1509 74
    0x14103825220b0f0f007010302094151410494201200c031005500b45505030f4002642c80301e84a000a008003041030105070007074000c080d10500c1d140c0c010000d0003000c4d80544010301043c0e1610a4a12880c1400c0302c0341ca0144c0042604c602d0140e20742d884450601c00000240c8010191510440d000701c4100070005013440c07001505070282c60164042e100400c100d00b40b076911840c0780350354491003660307000a00006a40e111184903e0180c250b8030840c00344054105291310403013201010f01c2900581841d4850110340b42e00410101c0c240e00b076010009034942000c1a42ca0086030505504110042014004207071000003a000540c0300a01900b00719440340030318000380b100d4100c10941a10007106000b011040c420f40070360f100e182464420610301d030000c207680d03600e0000351103041440b00c0003403601d807400c1c400e00450305c400b9640004826241c0c82c21413039000800715044180c4402c1210048151500d200e0412140107052101c00642814004200d480c024210200c10074104801030340002100c0206014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 238446852 1250 238445602 238445629
    0xf060c010b04060e0108070e2706061c15020d11070501020a08060f0609150415080108010e030f0304060f0605090c0d050c03240406030506190f05070c080307030b 71
    0x801c0740740c0e503407050106032074140e042003030b245090070014804802c0c0000c500d400c50740d4209020003036454407200780c0204400c1469100340422050040b28a00d400011100d001d030600b560101c4140000e8021102031078403840c0005e160f45061b82042003166480d4000d0b005803c40508009020540110410b20b958401f4004072101c0c0d402041c04000c058000c118264001c0b030582c0c152420240c00c50000d001407144030f944d1882943c03651105c117140540041075034060035000b440d01a1000d20828068480c1100b44140941582800400b820700c0d80e020043e04c18440c44400c00074203580b200c2da28103000d04000700100c0c40740d650b00c580c000382039aa80031440340900b001e5540c01d983c4020070b8503c0c01c140d40008040c0300b40100100700b8001d84000e9512200010b10220303100601001e40480010044c0c040313035002402c18441c81d410700c40403141071030b00c41240398019039080000c0b800301851001501c00c02c458078000b158001e09254041401040110351000341880d00140d910b281000149154643c5071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 238448102 1250 238446852 238446877
    0x50a090c090801022d0d060f0e061807210204060c060506030a02010c0215130b07021c020a06110a080d2c030f211906082d190b160f020a110f06 63
    0x1002070000501825400c03500a54004100103030b040142c05030301d00081c04cc1010821160500b210002d0303a1b000b0061105035035070701950744655544d002403956100c0700098980c1440c1201007103440c030700051250080780c4e040c1c50b1440400341940030010180c4841903024908041040705411030480030036580e01400700c410031281c44455038014403001d0307142c80d418079008415248014015030b0300c035080542243c0b201e00d400007551003a01c01d01400d1241e00c01c0300500c00303031002c507000c1d04030078882d0043e0020303103c02d0056120300d00c0c3c000009140704c1c4501407511401e0300104960034001c139039203000705005030040d080d200c55202800d400032015a0300b12036690b1070f0f43c000c803078464214505000740c600612800008141000807103040b40e04064003c5040c88020300800c01c0303080100d1041c03125011140d104100601150f84504000c804030400f1207181111110190789089910f014403240650350302c0036401802c1103001c41d81d5200040e044065010b6206446200c100c8031a80d0358001800d00c120900c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 238449352 1250 238448102 238448129
    0xf070306060314030a080a0b2205060405090607090902090406080a0b09010608030a09140a0810060807120b1503010e07030c0812071a060a050a090c090801022d0d06 72
    0x141400d90f10065910030300941038100f044454103269000030410380190912400042c0d1150070710006070114044038824480300006000d1109000203648003070300c50b880941d401d102c140e480c0c41c0034072380790784d41115a000441e5502205004114a590203004000405000050401e840303899030f070b241186001c001c5412441c85070820003818070a01558005010303000c001c50408210760b070060000b41141c0200c54040300200f03803e503c6503807024813040c018a40c0030b0544120042416401c0c0251003580503c4009221700200041c2d01c205079406525030726041503600c002a291080c2c0b03444240f038208001c41e890340d2201d11041008809100c0d40006510030a0002c3c440d80c9002c0390582440003110b410080650b051042074081440309001c44d00c404040141d80030640c0c1c0307400c0020441e0b10349030002900464aa580030403401e400c1c0c2e0160301c003a211510768030100ea80e1f41495600782d10444036241208810746030068402030b14940340c17000d000c0340e81200b1410205880c0314103044800560040c15000c102 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 238450602 1250 238449352 238449359
    0x6120f05091c0509420408010b0d1101120e010606050903070e15010c0311031606050f07090b1303050d170f06010503010e0601030f150f05040501080703020d02030f07030606 76
    0x5070b8008540c0e00c103181490f034209105840000c0102c00c100040d1500782107114280c81e4201c0c40040c1c074000843d015180400745281074044449250441d00070040070350318059032082c1516000c0e503841001584604030104902100004660f03005031240075412040e110031140501900030f002c3e2401074040c43d44c0b45503c8250400400d440c00340e9692051005145a10a002c441c11050514180c0d600003801d0114080005160446401c030102881d80864040881d015103408203200f200c001450260703000b44100c2e11800141955101e05403020310100d0014041000350b5090200031b8149488402c0788181010f03aa6101d05080240861840c00024040d0f4a0500c204110b2041980c02c1021000c1d03000030741c603260002038400e100c1805080840040da00c000f80290388207801c1079480c0b200060042c0120035907404d103214814014000e1040f411110702d0003040ba41000d101d1103040f10303903034401080c5d00c0d403540c0c0038480300c0032084d8410ba0b014001c29002c004801d10030403800d0000c43c411440000c2c114036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 238451852 1250 238450602 238450633
    0x60b090f062a0a05010c020604031202130614070b0a050f0106020a0b3c0103030801140303090f040605091305060703050f1b1b0102030603011b0906120f0509 69
    0x151034080340705440c203014100b8145040d414540d0001e115904644110b03000070281403803e115528014038039801d18417602c1000d5400704c4c9a6004034070a07190207445114615400099005942e0390024150280354104400c07445080c10200700c5104268051510300e0756211100071350401c440080701c05482d5400e20030080c1e143d04010303005003500d1002c0c00044115603900c0302100c0018011107071052480c0383c41c1c200112000c000070283c0d42014103d0405269241212008000911042e00032032540000003811011035190000941c100401a61406080e1801c0181c40d1707074082102c58000d40d903200081960703103a104240c0d0040003c2d03165503143c10500d14182c2d10300345008125004148c00d010034008030b880c02250083e0840c4101c0c80700a080c10340b0400d05911400b484c00740700d09401e0103015031309002c0419801075000d19001c2c0d00a10210700b11080d03005080304407011420010329181c00405c04548190400308000c4104c03000400c40c103110010101c103550050350048050f4003c045c48190f91031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 238453102 1250 238451852 238451869
    0x5060f030703080f251101030c0e010c0b0a15030312052d041401020310030203010b030c0a0614041a0c15061c020d020303070f03021002040f0605090d06060b09 70
    0x144124010944030b41103959080c564010b1003112800503c02007100510038269040340c448086011003441c0c0001101d050003181c6201462045000c2480c00c2984543c4c03a101b10600403580f401a1a0900c00c610207686000e4020801001c9120a59850501170086580900080e00440c002d680d024102200780241c4030032160301900040101202040490700307001044d160f4207410740081c100705210741d61070501941c00d29419010700d00a51000040101c4d00140481c50010b036402030703001700140d4181000b495a0784000d401c042e9170004000d0400c114403481040c0020134007002c01110380c180782d6200e4120320540c6a003050080040307804244005080c1c000c0105a80c0800c4c0680416024101240426074883e0014007803006801c01c0001c2d00c0a540320300d8000c0040e6a805000c2b07a640e51820b0a001280c10060582200180240d8040c000fa01c0d00034002e0f00d054880040c0c01d2220302d86401c0c8203032503aa02c042a181d4001c0d0b0000d80035804038449100e00740c024450300ca59540d8a4011404014004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 238454352 1250 238453102 238453129
    0xf0d0e160609080705220c050c0c010206011202040b0a0b0c061902281701080304061103030903030f15041407080c0c1c090b0a051206060301060f0f050408010c030506 73
    0x102041c2d404200751440040c11108941042ea0b0030b442401411381221988a000c0303a02016903820700c2c0030740c00b600d90321000400103000307501d09585c0048a0301d0012a106e507828821240800c181080e9000980b03080c0d80034010804d07004028020141d5240220200c2e500610341103e1190410801c2104103000d440c13009202d0300d0b0300ca00031442d08050065070f2410b450708001414000e24042e1100380134501500c0e4034408902203c0b4400031540c0d48941c0d85540ea07205001d80302c0001d0920700307610014031001054074060a18540513500f140d80f03910f81e611381c40100030082c8016010080e0100d0040c0c6941c03003510a002c50a100c404101e01d03001001812240001c0c0c030312a00100100220000f103175001ca400d81c40c100c4a40869000f5a0100c00110b68a44031500242007420000504202241c6c000d402410140c0d5170390500c0c07480d9507659041054a0100340f00320000f0401c10a40c03034503098810203000000300042d040c00d40c00d1030340300d00f5140d08403110400c228000c07030b56841c02d014013440d00ca500510703907 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 238455602 1250 238454352 238454357
    0x702010f06050409030c03030509071a09131103011a071a0405300f0702060c150709031a0a0e01020a1d09041a0a060305150a1505030c060f0d0e1606 65
    0x4052a90006d2000c1010040a810580c0c0e4402043c00c01d0340502841004181d03030a03c030350b140c07007100c110000700b0b82c0310540d101e00c6010038056080f100c010501580801c050300d04c5900342960710708003101e49134240b100b41c01c1420542c1000100000350340720881b032400301603401402c03a061415142040c50302c0000081035044455500078400b007000d03880c0000c2c0e6003915000740180c442d20241c0c0310380c583d07001342003000354008070210300440d102030300007564401343c4802841911141c45a9406582020641c00003815490340d00c0c0a6103044800c24005681006010100103681040e80355a00d0880c1c0020001c02e002843c019020140c11000d86d040e4425018100c4000c21203003015910404603002c100528107940700d00780b00040107070841e03601c004004c640007000d0b90a124818109440c0c00c801c2110459840381c50700003d82e0800034482003480545001034000d015000c03550003001b00c0c1380c202001d409021002042601802e224a0156860480e4040010720039044100786590040085800281c04c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 238456852 1250 238455602 238455611
    0x3030a0504060e0a0b16170903190305150906031006081006140a060c1e05010518030901080c0904090c0b030103020f0d0507032405091c0e09190b090702010f060504 72
    0x4540c18003078840e000b500c914481503c0c0503680306c0c1542d0409110301d035918000710650030070042082c084010254249804071039851540300003015802c9980076603000840c4002c8814014103030600d149200e0f0008001400c50b4510681a24003200342d6100360000d14090300006100e2410b41d0b901d008010140044040e81100c07650300c0c0e00414501c0304548600010440e03100007150910116006000c0000784280d403002c07407040700341400380c082c250580d03821031030706084202c1999030b181c040150b402c5940143d4400d01035445000309010345030054451564415510030000300042e010765107440007003114402c000e44962450040164040d2085119805165070241100004001140c84003d07207074051224145840c0303020702a210440600401c601e241d1820092158214001401040b5460b201d56032080781041c01f07008035414007510140d240c000c03a41d4004503501c400c5070b075141503d1010b61400022503010070000030f40743d0801501c2c40300c09030355210301030724900815010f4000900b005580620 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 238458102 1250 238456852 238456873
    0x412030306091109181003020d080a080112020105070b10090903080f01060801030b0a0f0f0c03051b0a0e090a0f060f0303090e0609041202161e090c05030103140c0303030a0504060e 79
    0x521000c4c4071030200045809480010743c0721031b60071414401564016045101c0e10502e494a04815070040000401091004000003403481f11079800e8854a40d06965060404000e656446040e001c043c20441c2c42c050442d0000c02c14203081e12824101d6402030b52070884500300a1168101420113030011000c0041c0c030f45c01400801e021008054204101c020000741c94001d02c030117030004000c0200c01010450800c032540020540c950001c50060190750b007400740c84d13400201280164030640005e0b5021550081d082d60003031070440c5e04664003c48103d0f01182d0640044400303401c0f40e00c580c12041001c506180f01740180f40c0d00404a80180c8101c00c03080d0001d04004c0d00181200e0710082005100444410100aa0920030700804422003281c1c0c260864640e11018514070442100030201100b01d00c17024001503030b902d1307400703075201c403c040d07859091659003940c035440044907168801c0030351882660300030450f80c0c03002c1000303511038034071108001103504040ca0310800f622070001d2160016072014030b803d03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 238459352 1250 238458102 238458109
    0x30604030e040c110f030a3f0b190501030506040b13090c051f0206070f050909070c02030a0b160203040302150313080c01050403030e010e07051903050f030c070e1009110412030306091109 82
    0x102d03070340c14015000348c541510514440003c0d200328060207800c8040b80001d91804800c5c0c8000c1010798034243c80c00e01c203a5480d98280001c8400d1075821513800340c034104203074120400560100007000d01900c900e8240c40d80b900040395840000c06034078404403441d140648901036040c0310254010340c852914646400f04601d00401030f010b0400700c14412030307003000401d42041c020142c80c034602d1380c098181c1d07044140030304080c5c2d94008115240d158504c2c2500c1641144c17807021041304d040e070f42e008010b0fa400c0022800c0782e8103250130087c00120100c01400355280840d400381c2c090094601c11a00200701d602d003074580141982c03400851650168140001d80c1d03910300c07000c6502e1099803000d0380c44c101022492901c1480c0021030f44e001418074007480040d013100d000040010103a201c1030340c0484100d95582c2c5c6800722041c40c1110100d01c99080c04a00b440b80c0c03021500502190400548014201511007000440804c1080300440c0460b58a000400030f1819074040c0e0b58450941c1d011007400e103204400072 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 238460602 1250 238459352 238459427
    0x1506080303010b04031203090204150306151805040501141302030d080f060f030705151e0c030304080304020303190f140a05250b04150b030604030e040c110f030a 71
    0x404410300180d908000501c642e02050701260018014040403001620070081100c2f180002d0310792034100111496100018140d5500b19540c10303007111344d10040800c00b20010040075200f207030720b9501c4a014005522643c2903482c01100c0740e441c01c1d01c08491030320400d0318201c619460300c024401600d04000c03000da11601e0740e91f4810425202400380604500000741005e02c00d4004030742c0100b040c001202c510f241c00e406410480c900000381003000000c2c00c2c440c01240104044034081e9401040080e000900c0d820103150004e1000d8105e9042075062401c03042d1a40d40d5451100000b5611020b5071746441e07018007540240050120400c3c545000c0c160011310394451155104800303000f145405484a11414030819207980002c0c0079070960902c0e181444640c0c0703042042e401e6890800721004030760703c0c000c1b40c000d014550580710703007031050f00c9441444064030784540c142c0144120086d4022080c882071140b0440480400f010b190f442c0c409980240540381202d019003007000b181824024454041c512 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 238461852 1250 238460602 238460609
    0x11030124062714032e0501120503030103080d02130e0604150e010626070c0201020709020c0316021926010603080405120f0f1c0f0e100302090d1506080303010b04 71
    0x3d107500e6120520010030700c0c1911154500005e9095405020300301c0300301d884031030101c08480b03800340210f0340c0e1042000591103070308001603d660000c0004100091102c801070940080914016061011200c0c10382e5959082c5c0d07100040300c1424004001e5145084e104400c0001e20040c41c0200da10b00704032a05915079414024241800230300305035030088804a52801500041100c3da682944c41d04580c001c2000d250680d0490251140f008040356800550090310108035840c00207500f801540800c0c005901510070081e600408220328504440c003d56031f00704041c2001c03c00058040d00d841c404111200f100409180181e40744c107205200051590044404440c01161003901510046040d02d04101904600819904c00e481c120104102c6c04980d49540071034611007041030035070201703066602e4904000b500f80044c2850b0310041c25440d000c1d07100c0d411411149001402d102507000070984a450110090b91a601e00b86203c1030860742c140103403405030410101441c10355260410300d111034000c501 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 238463102 1250 238461852 238461869
    0x10804171c02071a09070e060f01050d0513020f03012a021c090503060a05090d11100606090e0c0408060c07022419020f030403110301240627 62
    0x9480201079015929030000c50841d03481103540d202c15140c6400d03207004294440300300c005040009180c2c2c2c100401c07064105d41c085422408a0780e965001c0004130040c0b54129414001c050000c000d503955240300d01032040f18084103801d4415054010000c852100c25100c51280e810301c00412013581c0402c0c5400c0100c040b8000040088160210a03030500c034280c100b0302440110740b84001c1c42d0707582c01000c28040701d82c00d60503a40740e9200c82a425080d100100c0d400b4009034080f4465402e80f91055000f501408001b1007903c46850546c02c0c14400d45415502040005803491014001213078081e20154004024924240c80c0c90300d0001d00548400b002080f80580d41c60104800055454142c0070094601c0c200c419034483c8810301c910800541c000c181489940c0c00c1d500340b103603102400080c001614000c010015400c0500e140d541c80000e1418011981d003554131841540c031850515803410741ca02110b00714800d045420424020520300307a0790040090382582007840786145010038501d400342c2d41c402 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 238464352 1250 238463102 238463107
    0x1109160e061308060c0a030c0813030509030a0c15022a190b0a03020c060907030b2d01090605100203091302030414060708010914040203030d151e060e01080417 70
    0x1182e2249449000da4400c81d0b160040808201007152030034001c040f100400d484c00c00c42c0000c011002c840c40b0394100d552000f5024401c0880d00400c0c05007018014020006045684400550391042c0034061240d10050140911200340d040c80c6030180804822000d2661441100500d032449030044d0700070104540b800b0b07003122103062099000940c1868081c10500c20031030707921a03805074010000e60044210310a07a00500b008076031581004035032403080f81d410194070354403500c84610170015140114103042d9061103201548a0600d1044007440c0204040103000400e10310303003000d00031040013440c2c558046400c1005031910503a6085101085107502980040e22580e40786403803264100080c1d0940d00501c1036108102d800e541c0071a9960503240313a04024062001441c50f2144a05d0003950001d515400c148080325864400707500c02c1201410842c24a101d407507689802e050070005414055070040b10202052003465004101e00701400e000303203405943c9282980301c42a100040e244d058507240e000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 238465602 1250 238464352 238464367
    0x90612140109200f0a08090c0306010501030b0303040305070b040305010c11100b0105070f0c051e060324060c0105160c051504022206030c0803091f05040306091109160e06 75
    0x420074840c0e08040c900300f59544501c425510140c607042054550000b5508000040b0311344000700711424a2040074005202c16401c000044d000b610420b502c0c213825100500000011500c00c00000c0003c05d81c001d9240d60b05c0b0f0950600d1402c0d602c488400d5800e101035070080010101d40001d14440c1c210b0500f100180384018030004030b50ba44500400a8880340d42e101c40407007808101c121030b0084640440b007194200d8401031540d91104040350b41c180c0d0003402480001c1d01c000c800f81410b04032210b0410030301c10305c940850004502e0f40103100c010440760340d180c1c200f0440e41054034912405070010305240000300d619955130350b511803006280b00c3c1c5150889000c80c08544550070401001101050031f0300050b0200041c500003080d9610090b154440b203040c3c0010008404401c8840b40c00d80500403a00e0500380140440704101032102c02d0003002410400000410b02c0c40c4103d003c4248a00780c00b60f203880400c0c0130032845840c050004032580c00c070801090300460300b09401c181401d10985100c0d454034074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 238466852 1250 238465602 238465631
    0x210903031413090b031006060c03050306030102041d0703050f1003060f0b04020c0a03140708030615070f060b0f03070609060e0a08150403020d0305040b0103030302070f0f03090612140109 82
    0x61101e851401d0081039400300f99450290043c2c0101c04064045036404240000c0710307001d5641c980b00303500124600350308000209208200455110b0b001400240c074007982d5520f0f180881804164034000d0000b18014000d4403945409155005248500c0c1c2281d50700340082040c0f04103031030784001086180e54080d081088860382d040300048030f2004100f10348414680c0d1049807600007115080b8006011640c00c0603640801d9019200200c3d001103100d030950343c6807824001c00700d9042945c8106141c05000b810006500c0c0050701850600c610341c0850b0507074600b003e104100c011125014400c1c1c0140074117129490f44489610101d810614040340541640b0012440c210b50b00d412840385401088114048440030009207806503100b0360071280c000d0041c000480c01c4400550740140b200750010010008240710303030050101d0fa405401d409501c00f5040e5103141850140c200100c01080c5040b20400119421048070300e04002c0081c0300b13110300e43d82941d8002a071541402518034490303481c00442021078 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 238468102 1250 238466852 238466857
    0x9060c050a021801061106090307030e060f0d020403110603130201030b0d02090901050f0709152a050a0209090a0f1709030d120b150a08060103020f070f2109030314 72
    0x907005014140319420743d118560501409010354008180004a8044480c0002a50504c1501810055070520345540e90890306114030a00e1660301030b00c00e000080b1780031903e00092400d148444030060f5140e00d0741ca804400c5200c0c43d502c15106003014800c11105011280407140410780c2440e000a0703040e512400100503038001d440207034111180b0801c104401105520003401440301ea0004030440da195007080b64481da05016100203420300000300003015010300d1802c8002c1166005d03144482c00d8480000d03200e4015a007058549600103030700c0c83d0030740c1452400150000b0801c0c0281c41400c41b01d0304d6203011240c0b5403000400342000c1040081070f13044220256140c0d08001000e48030100415980101580c400d504940007082c41c0181c038104901e0a581e0851021180d14001801c0401c0d02c40141c4107848001c101b00e0600d502013101358400d011001c000d15800744184250714201c42c6030304160541c40740b02c941106580840300c041043e8640c020005204403541890044242500c0740803009160 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 238469352 1250 238468102 238468123
    0x8040602040f170708010b0607080a09090e0a0b0901050606041701060503010e0a060b0d0c06030c0905031002040e0c03090309060307020c03030403121806051c0207140c13090309060c05 81
    0x2101401c40100d0f400410752404040c003000700c2c044500c100d45030103c840c201c94074403a40caa8058009c00019000078189400341025070f2050410712075050b6141540c0f0b0a0b10010404004503401182054003008184a41c03190020102c0000b0441481c0c42e802081880c4158026403105c203407110000c0e04000002d4002c6005001302070004d200000440c0e600d26615201e40360126425800c1081c0b000c00c5040402c01600b04641007040d000b429803805c4016030061000c03078842c101300708501401042945042103114404003090703030016501d0b0b213424020516420081c15150b40e00e1020400c1c480659400815200d4204080710901e607207840740c1c482649000017460045030940408a000424032082034146419202c0f286ca442c4012002000c4d01d24130685c10f80510004240309028400700c02c0f08506000c051840641e20040c54666240c58080c0c810602d0307c5440300a81c400401c014050401c1064040b070200d08107400d120101140d41c025000b51141d028a1007080442c2d1210018002c04000e0040e01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 238470602 1250 238469352 238469369
    0x906030e01090f0605040213020702031207030e10050a020d051608210903090f012c01020f160f1505040504021606020705060108280f0321050a0f06150804060204 71
    0x2400b41444d008000d0213003218164400c8a141c1a6907100c8a100e0084650181e4010081c00c094001181031b02e5440d04034050643c10401c188191103001d80300c1c030340c0718840c0a501c0e031101c603110211072000a103402565120a01080014401041d540072804505841c1d44e500ca1800d40e16100800c80799001c445001413509080021801401204030740400107140d0310400303840b0311400702c05480064bd606800e41404101c43c450402903000190210080702030500014416100140069180503280043e42211640044908070042244240e81c58510000b420916418003105d8139009002e02140107170f106144c004e60300040c5004c0000100d592407001c05c0d51026086440350a2810003541e0b92509000e40c03200381c071540116215608407500000e200c060b102201c40390f40145a40d0398400313141060000c6050188500044d071140010014200542500a0001400386000301c010000c0d5041000130885482c907000e414041e0200c041140201c000250810307554075120761621000901c0740d0341c0100d60 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 238471852 1250 238470602 238470623
    0x206070f110a1203030609020405010806042708040e090f03071502040b040803030f060a1401051c0204080a05070509040b150a0513060303030e03040803070f0602041a0702130506010906030e0109 85
    0x210b02d002c0345070401d0b145004e59030400806840b51801c07030883c45140076960100e40118001100c510340f50f0054005d0b80007007801000c041f4040c6c8250180c5a503884411140154003003024450240107603500c5500c0307102c480c010894140c00d105c80036124071401402034410240a1448503050b101901220014280001083c0d07440d0740d9000410348a820a0711221000300b904c1021034083e00d00204400d040d25400d620003c4a0742950005503540d40c00301140710b4170b942d115043c0079640c2c002c41c8007030030007400540b025002c503c416290030b0341400d07195000507114044040510010402c5509582d51290b0000903560300c107041d61002502c0d01e5016402a03a000025080709841032401303030001e4003241d229403070600076038142c40c5400b40c07240902d006144a03039005108040c041210015540b48180c01440e0051038940c540d1040d1005205004140600341d100041c221b00318207050140040d840700414040020382000303400280b50151522a0800301520398001210b180029480b0014032a4001454003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 238473102 1250 238471852 238471859
    0x705090a0f200d1e0906060513090b01061422180603080a05071e080405100e0315061207180e07060f050304060f05040f0b0a06030206070f110a 63
    0x8094085007400c1c0c07070305a081c8458200d00c20850210811481d103000000c90509401c2e40c1c041d80100701c80b01c80e03030705481031a118030541c0d014907105410b000760160202044070390618050001c10607500442c0c044007403500c406a404601c00310a0307207040d2042803030011086982c0b852512200c2c041e500c220f030440208100c2492a940d802c1241d20100d9032900c010a0010708a06d1a100481e01544805440c09004000301e44206100303000403c030617440b40c00c00b01c1a0581308580f4407402401c124003242d46560004052200e4a030424021f00c08480502c2c04040c0900005c020903224112120010041c04001000c107040d540c8a01c00310b003c0d011010101c0316040d0b52003004407002446804200d1040e4501242030550400100d6504150f40d10303912640b2891040b20700449841d4030080c81030b165a81d4440000080544500915005038003c1e01a80400034290a284a182c44060840c080d90303032910000b080180c03a4202603171091600810f050241c5d01c1c090810080c10300804504552200b1007601c080b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 238474352 1250 238473102 238473121
    0x40c020708060c0c0303041b1503050402010306090b0d02010c24090b0106111902061201080a02010905060307020c090a02070210090807080c0d08070201020c13021806070b040b09070509 81
    0x19045071811812140039031207500b00c03540e45200d0b0781e00584481d042000000d0101d00070074030109074541c88404080072103a5851029603015148204040041e0315001841300350740e4540a4103018024620f0100f01480084000580c40040420001c1c14403031100c10303400501c404d404050403004402001c84d80d0780350f07d800000c4020a0448011075100c142c000004c03d00314890f114010b600003501c0d0007404151000418003203c01032072141268449030410600c070808495012070360081070302d0801480b4401c80e510000d00640480d4124501810b0244100901d09500203142c0750140030540b0356100b40e40f1145000d0300644544072000c0c4d00500f00b100944002c5a2101d101d0b411030f80c135007003991415521000101d4540c0c915851480d4844134082030080800d01142c014100305205004440200b480390020683c0b070321008868464681e400f1a0340b0b01102002d058148810000b1240c2500d445084d0b5a4000031b8000a00090001000000040d1284004010040141a00818180141c50f0940f8030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 238475602 1250 238474352 238474363
    0x9060409140c120d05040e1003020a06050912161a071b08061003050c090703141510050c0a1b030c0801091a070c1415130203060f0408030103080315040c02 68
    0x210b42c015072003402c0c8000c80c140c0105031403242e0160360303541e45d00d040c1c44d007441d030340d1524405081003542e03078101d400000060b903520403a00c0c000c00982e2251902e4241031401c002509000000540298011900d2202c52503407001080c1d0648208c0355102d10902c29815500c0828080c6490040070100899040284061100600002c9030103a004640140c2d5072903d03003030750003501480001c040350b10007249001c1a1900018040d400b070380a00e000180c2140d00b044007036640c8002d442d5141c80c1314800b620070000d03040a802c0105849440e09005203000d0704141701c0c659421440c0300151010441c404940094450501c0c42c10040d50403840340103090307842d180303024002c245c845c404403003001e00d08101c6c0c000f50319042e50f5030744546602c1d100c1d5840b1031442c1e121600104100d0032003e42d140078000381c01d041c02c0c0ca00c2e00301d40d0240741012107001c7d0000742031040c9407400c0e001810700c1c6c100050200400000911450440e410b5a501812158990310b0300f2002906c18480e8074015076016003030170307900004150700080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 238476852 1250 238475602 238475623
    0x1806080f0a3c02060c010c03060510020307200d08030903032403060609060604090c110d030b061602010903021003050907060912060b0a0e070504090e010c05090906040914 75
    0x400b0142d24691003a00c0003100d081110075082c0d520b014003041603000b404041d0104060010f0016031500040e215600c0c2122507188100001c2551a0400e0003282440b41c051400442a4002903250000903201c00001c0407001c001d110070b141010046161b141c40b20741056045030f078400c8105443e410036443c1c1a45030b030400c58031000311114101c00a06146040d0108800c2c41030701a0240400e600c4003c1171080404000b8241d5410040401001401a45074886d151104d0400d5590078a0065544d00b1a13080415051a5004040c10800300803903591f6402d04984800e16124540301f0058924030050b2034440143d0310184d4031005240c01203000303e405801039485910018161001c1c59216001550070000502604a1007a107000e49080040c1e202e5000000c201c00041c600e0601a5490b0035044a24404580711744c00201c1c04a810050124180101c05108007002c000740003100d21000f00810034080c42201070310407645c10000c00c0f900d840b90f52001c184183c000c0a511561200b952090f65182d203140b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 238478102 1250 238476852 238476863
    0x3070b0f07020d0203120601030b01090305060a060905150102060c16080301060903030f0311041a090a032a03020f010302030c1309020a02190c170f03031515030708011806080f0a 78
    0x40003c240754808412950300f8032009281800c1d0b030729800c0045004020301800241840340f595000300100c0c108020291042168140214540b0b05002469007540c00180c02086120800c0c880da10740761b0380201c1c8031680980700742001901c8500c1c40d03041148860400030003620000d030010000c9010f952104000068900030744500d82541c881240440885004810000c02c01c2d0303080c04140500500c01640a0700700c00c00d15026810f04517544009850103a04c0d40c0212102c42c280715103500c84030b0304c6044c040c000c4001003034041c20580c55030300411105c040d015000c0e410103900100140b0100e0411040c0c808170b8203201e10440380252180080402075004002d080003620801c0841e0504081c042c00c03038880c881e4010000b0711280d00c0e1629a1920028500748000c59020f0301c0417003540403101f000507611035100d00d5081100e101c0c1c14000d21250035801d003074440b03040004004003c8402c0e040180a81181c4070b102d86540700344041d0b10100001c06c16034111404c24080c0200c108040b0030009003008800e402078 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 238479352 1250 238478102 238478113
    0x40f050a0b070e100c05062701022a280201030f1803021002041412031210140d02030309100306050d2108280204050a080102120c16020d0503070b0f0702 67
    0x100f41a60003917000c4800410951051001a00310580204440380c005015942d0300711142c40c1d948802d0990300a00300400403049500c0c20400003010754010b55401171011802707410811303d0359400355000c540d03a011a911048001e402e020445e4401c0d03001500616000c4c808000c114403424040c503040603455416801846402c0c584d20700d942c624070071070f02191140c800540050400b6000d011541c45c540290306080d010a0003c0103445c2d0701c0c0b04019120f08022a2600b80c400d0070a0b008081c4044810f10312401404070000394401628000110f0f01a4082110f40c43c04000201000320080c0080ea0003541d00320b0502e00440d4200030307003800b0304502c01400319840300b4010b0040c41c0c01c580c05101243c10ad1500070007890010b003054403140030414401c4200c0c0c000b514043c0ca500108000d100c4a9000e22031680d400a217280c0c4504030564120b400224000c0143c0c50304608401004003c510410007030311604842000c20100803041080f240300c1580314544c1c12903498102c040001c80c600840341c4801601a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 238480602 1250 238479352 238479379
    0xb090c0301050d030c140114041e0309050f0a030c0b0c060a140f0a0b040207081c0603110f03010e010e0307050d0f09031e02030703050c1c0506040f050a0b070e 70
    0x1490140c9059032000780c0054010f10710754600b11841d00400720151183c2c1903101d25140044030030b0041c48000e511050340e00c1000d0030f1034949100c0307603241e4510051050002007644400241d1103600700c01101c50454061500d80c070410000307000040c0700e0b070005007482a26440010840020b40140904030f800f24141d4806070f694203548426a8003200354407020039400070000d179184000b2940c080d0441c81d80500000c800d81004c010a049a102c01810740d000b000106284c01031480c21000050121750054040c025289580d554148c00d80003030814501c20f0b5161700c00009035450035030101c075004403e40020300c0440c1c1a550125140c4e8486807094545000340200c19982c64001c02d104000702a2694070035482c98510713152542c150781640410200009884082c002580d010010000510f0050010b4040070812104020840006000ca0006182c200d00140081600414950761007a04910382028811080c984103052036002240108860210b0091200581d40702d880c10760405410b0716520b0b440901c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 238481852 1250 238480602 238480621
    0x15040902030a0210020304030b13020a0603020c060415020d020f13050a060c06021303051516110a17040e04060501030b0f0919030203040f090b040b060901020703032607030b09 77
    0x100a0041d40562151a0740001414603250700c0030000543c0c1305680c18181c4a41d5a00c00c084002d0b2050404150581002c8056140c503208210041240d4141189000100200c0c070b510740c03000400c0070305005600551080e181055404807a0708d8480d004085540d0a0603485420325a0402c2c010040240101d600114042c141004140c3c00e668846c0ca9809101c001603950303c01279400009182c01850303100d0400000070b1010004580e07400340810b808002e910300a0035003415440340c0100e441c10043c1d1301d042c08065203008101214020f40140310081c0c0300700c0d45284c44d0310900c5140e10008109544404100a20010340d00590680c0d02c281d03102030761510344140341d15403000b00b59980d00194103c60006001c00d001f01d011051b03100e00c40d00640341095660642200030169a501c040d860640721035190946c0e00d01480b41152071002280c84504091000c00001d41d1a90300f0300009040c40200045078103124440000c100d49508048440c01c403a190494005014003103214482d8020104000428400d18 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 238483102 1250 238481852 238481861
    0xc0501090308030c0c1009060e061f12170a0c1403090114090109050405090a140f06010e0a0e070b12060a0305060606250b070f0504060504060f030b12061504 69
    0xb40c100280d81e00315150860306608075400101500359a10692018130441c1851307018400c50f56001d0400000c0007103810803001d040400c010810300320301e010214552000d259103003115064541131400c10500400710f180c40c0140600b00d806004014901041c40ca136660350003041015901e2080c611b11003210050713a03545640340a86149140030680c000150940e1a00c40c002800c04084141760880019940d500400d0840300190345000c034541281a510081c80305001c0c1044158091034000c10240b0306200600c2e0b1100418016800003d000d04045000c2038404d170488028a2050820740c0e130750950320116000aa804a40a034410b0b01450b0001043c51030400600000c50f134100015056a550f00700c20000198051011940c0c80b101e808150741100e8440c14410044034829440c201c0030741010300015050b4030b80c0b207448008000040000b8440c003075000d8203850071540d280c2803001d40b0400c210002c1e405000151781d9190041d90b0314204800890000a40c10301800d045110141c280d00048144002c0d103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 238484352 1250 238483102 238483109
    0x240c060c27091b0702100315051c060c020708070b0316020a050a0809031f02041d0c0a0305040807020d05010506040506030c030a02060d020408030c0303040302100902030a0308250504030c050109 85
    0x21181030000f11210840d119501100110110705403800388a9070000701d000328500748180c0026a64680306006210b400f0052000d428105c0788901b819040751500c060150a1003402401e00ba00c2d1025919a50300810694003c0e200b614180d0301d00d2601c81d0428529500f00b1101001003940300009101440c0c00420a01006030700400a0003c000c4152201e0340f0681c00120a0341e058480c00c50510600f101d03404000014103600380d0090381e600e10381035100344500001e404143c0b2240540d018088850720710000c0304c000c0c3c010b40c100450541d60318100014203000d6648040d4000100c040b4403c10844103620540c85140f0403642008151100d109241e40e8060105c042d41d016406014080d000d46041c41c0075000c80300824002500c1c00c0d0b03c611225045401614460505503c04400d1004054041c060f9105035500360204001c040d0b21394000983d81c500c1444050140405400820134201c1e0882c4a5100c018030100c2810501c900202d0007456940184030959455000c2e400c0401c15612448402c4204d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 238485602 1250 238484352 238484359
    0x103052a0102030304061a030709140a05071e1e0503060301110301050307091a210c0f09010605071106130305060105061806030c120708010302041a240c060c27 70
    0x3141d80d940d0781c0000407d56a5000665200300341e003011380d155020072900021b00a14000494181c5080300f200c0146400585101c1480381088104600c40f5030040f07030702040700890481c1130300c2d0310b000c46401e4641c4e841603082440090b1070f400409a429400c98002c50107010150000c100012440e004903070240028001c60742c0c560050303001040781c9142c40e000807924800040300072542400510009200030540840107005901451020f20040028400f12807103640581c0c1c5c80b114950f00c40c000036a10b0205018100034004081101411b100c040c40e015040344401078041035075992116840f251400740c0e44022034240c8130303400010440d41451015103220b50400040c030103204c3c5007401000559080180005103540e0107020101c4465000c156040c000d448035150383e0b507154118014001130300e9175400e91125250002c804a4180d48412014002060b02400d504820030700c81c004103000342c89540000c039000e110711418425404071001c001d1002000340003140c2c618525151010414100c030002c166031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 238486852 1250 238485602 238485607
    0x50402270601121104030302070e0c0c071a091905030f0f0c090612030f031005060703020c040b040906060801020c0d02160e1003060c0f0e0d0f060b040e03030103052a010203 76
    0xa5000f2800c4440018549601007040c142c440318800d0b0f1604560700070b400582c400c6108001d001d5400421a030001c2d900d00b4460302c0c10140c0200559140d0561091900c2d1352200c1c600711031500580c00c203844d500003008090f00b2240d9040748003110300b00c01901810344a4098045d108903420300000b1040b0001d44204040c0407850b03022010480e400390010f1086810501d04844c40e84914014001860250200450b290301c0e400c10b045150502c0000d1380015000303040800010011a800003039040100404440204515110202241c060800058014801418004003080c200c0d010740107025401c0081003290800884180103d0380c0d100c444000c0d13580040b140e02d00b0300c070003100381c0162035015190700c3c40d081c0c08540d20f5451104a03025003516800142c0380104880c1801c0c1d204150340008001105d02d54403246080d111040b22990301c0e00d0041000d644c4610f100340648940c1c00c5070b54400e100342c050360b0726980d480c14403644429030000010344d42c2840015001c0306a50b40c1101d007140c200b040c2c1c000d60 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 238488102 1250 238486852 238486861
    0x70906030c050f030f060702061510021506120f2109060a1103091f141309090c122315010302090a0b090702030a02070906060e1306090c0305040227 65
    0x401d0140b80343e04540500070825400c440d18010000300f4015540c80d4010030480c9441c1c0d0700e5448040c10f4040c1c0c60b224059040800355210f5000a01e030b1100c80c2c0045245045803100c00c001103031400280d0b00c070802c40c000e058030210300e04c02c04122040c0c0403010100c001c01400304401ca032210781c803920301519401003044c060b050030384d44a502e6101d48000c00408591405503944000781c4600c03880404407900303800d600c071035000055102d00300c0500d08a080c40032509010035850780000705002400341190b0f265541103980280400183c03200300900b014140411035010508102c0c054800d20031264141481880c12005914800542d10384c0c410081050748005034215820031841c540302030302c40c9101c0c07510380643c0c507919a00d0a0541e4003c9c0e8541c2c004640c0c4110b195806401c02e015540b11300350b540c0c0b034400c08214003130b0007003075007261940d04580c404990500c000740750707006020641240045c3c074900000c821403140c069100c81d00503070088580d0000c01c400440280d10340c40b01c1407200441c01d4100c00109 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 238489208 1106 238488102 238488109
    0xb0301031101030e03160f0c081e030c101a130209030c1804110d060203010b04030309090b01020a0305030a0920090105011805061b060406090302070906030c05 70
    0x600000701d0356a4520344900445070b06c0035000840084010802402ca1511003403a41d0050f0384c0383c40c550f101c40300039a40710300e0381c4010703188100e400804802c00803001040c0c2d42c0c6040114001e25041900e1050100a45a040385500c084502c1260f00302480e511141d06615000c0798400060300c6405130010903107840602c105403805811017048030f0702540704404566907c2038012074110190314604000c41d1400c0d200441c064510740c0301100204208640800410480e8044c0d51a080f00540329100b42d41118074401c00f10340580d011038403203400203001d403020316030021503070800241040d80c42d01d4190f00007600c40001c440c3c12980c020243c3d2a03241142115016203002c0c80c14405580316266084445006400390710320401000c50b16005200503070800003440310f2070000360b80c00c90409140c10000b801031803204501502400d9008503800255124140c201c2c0d0b000079600031000d1600050 = true := by decide +kernel

theorem cover : BRFrame.Cov 238309352 238489208 := by
  have h0 := BRFrame.cov_init 238309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 238309352 ≤ n) (h2 : n < 238489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
