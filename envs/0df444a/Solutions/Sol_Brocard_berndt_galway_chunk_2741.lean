-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2741
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:36:15.863023+00:00
-- url     : https://prove2.me/submissions/aa7c23ef-ce74-4f41-bc3d-8558d9992869

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 492805755 ≤ n < 492985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 492807005 1250 492805755 492805771
    0x103060c080601030c0f2f030c010c0c020f040e1002162109030b0c0403051f1404050c01210c08010509010909080901120e060c091201020915031305060f 67
    0x4070650b0381000440489245001e51070016515502c02151140a1030b0300a090761403162100ca804030b00c0001e80e509407001811221900d900c00102c0680c805000e10842072100464540000408050340020b03420020b000c16080c8a1590703421802e214080805c14008101700440d0306640740d501d8241545102941d070301c07054480c61503c00404603100c40c15480c44146a1444d190004458116140c410104400419005003200200070120120300104202c5420840d28140304048003100c0959200380d0f010546240103001c0c3c000203010014402251740b010300c0c002860b0070070644290034444010b0345904141841c9052400542002d1035034441d00b0207042c2c07441699008801d90b03030b0301000d00489042820203042000d043c8207541d407c3d0b206894a010312070b0082d5001c40c0c0c00d01c10700001030070300c181034034a000b5008000801c0c81d00b900b0401c6520080e00e442100071414515401d01140c008400c9005d055401e60b0f002000032022407410003a010420703000001c80d13106151000128002450030b4640c28 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 492808255 1250 492807005 492807017
    0x50403090f35070f0305011a04020a0207090f2009090609070215060f0603090105070305010f061b02150a120f09120e060c030f091513060c0206070b0103060c 69
    0x101e1003a11981e103016071522107030724619661104245116400d400d020114010340189080020792501c513020850185000344000030702084103e9520b805406003050081c000ca00600010b004542c0201e401e40c1100c0e600d0401048c40500403801c40010565022045900c09030b05441c01e0580b035545001e05002d400a07144113200b0f843d078008101e880d0300120b0782000103a000f0404c00d840c0504e191035042d002000a4140405106c0708070000341283c000f120300b0f1440b80c0d5a001040132003603250140074010540340f16401d95040c200040103007403441d04007080c030300c04110900d00c000719101d804024482440111402e5150403450900400e240d00054403204868200b14080315196414410790074070941c004e072000c0c0b0030414800143e03884610800c1003507000b0f2050100c02c5565600380001c200c090b207090101c40d56800600100310020080c0c3c6448400e85100344030102407400b0400544084e01d0143c01c0c840750407455480080c44030304c20078800038549000f4100000810140780c01020041c0700341e440300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 492809505 1250 492808255 492808259
    0x2301090c06020102031b0906040b16050d0e0a0905130501020c0d020d0306050603040f14191b0803091203070c0e071e08070f0c050105040b0403080a0b2b06050403090f 73
    0x200d082c1d01007034407111002c40400c4112401b802180000301650305014203030318107140d0350b40800d00c415080910f110100f00c01d510060030405c4030900c500c844d480501d08200407074220800104030303031011a00640221b2640c550100d5000d00010609a0b050790348003000703541d605c0c2c04004c419262540084c112001d8401c084184000724040c1c0504002d03100087c1c140380c11551a13448616114982c21b005561980721102111031504060040305140345140203044201030091428003000c6103301001e442d40070117204203005e40f240120450b00341150480d44c2c84200e5a8003e001c9013144a1620018440e0084500004e07100504100c82480743c1c1007030329001c40b000441c00394001c0300d0569492040020303000a000821050003003200c3c0b14103c807185010301c8039010350f95400b404c6407801d40c2c068502080c200c04100400d1352003030840f548140580401d2100901a201080340740340d916404075401c184469984900c810b00c0d011011200750001001e01c118209400c2c040c2070420240100e10074818503000c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 492810755 1250 492809505 492809507
    0x3020706090b0703030b0105070c150e041a040b06160318050d02090103060f0905030708070b0610020712032c04060909051b0d05030c0c030d110303132301090c06 71
    0x803090464082c0244a85001642d13682100244009030045060041c18050017002c140c211080c0c8020b442c0902d41d0160398116070b0700180c040f5100300b40c01c500c11410032800009001c4802c0d0603501c42002035038085200601440010310030b016643c3c15400107245901900103140d4414991001070004031f0400455a4550060202c0c600e07081c00081d400405010042002460f83d511260406158640008031400c00d56280c3e419540107400075a800700380443c0070350900c8400c00030030f84c000c0411a00400213007001c40001c3c0d21003100784103412075800c205e01d0b0b074030906026007840a03519800980c8442e80109824000d881010542c02680c02586482e0020400f0b00091040700902d5401c03034000c00b0381d2040d030341c517001402090400417a0042182c0802e000003600410281402c002e0070005002c1804071a01854540800600e0784807c004003410140306024020046980240c40031805568007281c42c20250070090b9507086808207090b41c03021207090602c041d40f05280d4640b00e100d8800c0b4040e51504 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 492812005 1250 492810755 492810767
    0x100b070f0b06040b0307030c1a04050d11010e0d051b061c020d2a14030411091008160603060f0501021c03090b04061a03010c0e120c030d0c03020706 65
    0x1001884841003618100104028440550b4044402440442c030003015402180c240300207a8000c44140c15061424040010300180000d080d02c1001d09a604041c43c3c4400071740044580c46001d440d100d00c0d00800324590340b1550320414030060151506100380d0b800c1ca400c075a5802060100a0700d41c0490020401c6484c1840450b005500010f4800c0014050510740b44025402a1117901b40650380300c0e8101044c000041003541c01c0c008160700141e0703a2024080282281c80c2040d010302c0d03081400c00030000010b02403a92041072840a45150701990b5800c5282d005c0c221050304011401d100780f075500061280008081d809940c3c190b902030000b070340e41d5906904c4000c2175000307840c0540c100d0209000345103c43c0050070240945460040b560042c03a843d00849134006507001d490260311030003c964803e00c415002681c0c0070042d4001c00c40900f440d030000700105140003400d446402c01c803140c1c440181d8104401c1c48407220003015688031220f0074001400e51446201c0890150150400c0010300b203000b08 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 492813255 1250 492812005 492812017
    0xf0b190b011d0d06050703050906130209011203121401060e0d05060711030f0408101407020c061e2212050604173a0b0a0e09031b06100b 60
    0x385440da40088403514801c0c046204841c19a04103c20035400d0010076403a00a19019030402d450004003801e1072002d83d03003071841c01408a44100d58161702da20060b110301c214903045801408442e0704031007440c03a00710b440c503036800030300002982454550a0000b04414a01e4103d60998036401d4036049410144410322280b40c10250058000700000b0f1941401940c514800203d2407040d01c0c50070826090140258201ea0881c04142d4401e00815036100b04621698600b00085d100048284c508404003d581d1200c01280328010180868400c4000030000000c4217085961001691034031310b204c0e980d1202c082041d0303c2130102c903048100000d2908000442c02452900038029041503a900d46821584940681200444400412403c0c00303088a0f0602140101c01d480c403e204100300e0f0b01c422081c0c0d6030035407030351030415031600036030135402d42d21241110120b620007621047c5a983c1e0040b41400d502030003031100c0583c0e0401081e00380044003c2507842c402c00782420340c054400c0c2c80d400e100c50f21780200c0e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 492814505 1250 492813255 492813257
    0x1e0f040911040905031c06050108010902040b032e0b03190207030f0c081204030c03020d1e0e030a05060c1c060b030705030406110408010603061d0312090a0f0b190b01 73
    0x7490340d0024101900310005032030044045a15050840e070f04820804804150f40ea00030340c6c2da010038883c035039111251a00602c8043c1d0301313504280c02c0c80c0d61445148405040450031400001340e41e1401c00c86030f0b2070000f000881c1e0740842d0005039640da180f4400c0d44100d4008100400183d03030b14070902018802d403902990190341c2c4203ea5039000340d064031a13004640742500c07600341c188030080340b80b19070014070b0f13115078401c0e074030401d16900d40c0c0340c040c4c80e15040e51220400c2c0b0411500040c1480b070046a45655000503240080d50044040d0220f8100322000b40040c2c00b038040c0c1c0c400c0007031070b6111000402c40c02102c10b1152208292013924001100c159000b19000c429080001c02e480b907100708007841d007260044c400001e400c0e2121070441501e900a07400340d41e559444030b90400c240481403007035010038404031060140440501d02101c0d241d1080142500d010b40d105400301c0d03031500c5c04101510341140c0c050401c007020180750070b03e00d084003401ca070110021600441c030110002c4c094001d0060513541 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 492815755 1250 492814505 492814523
    0x24011e0f0e181f05090a0e0f0703021005070303060b040f0302031e030f0d1506030b040f0b06040b03041e0615090b01120506060d1a0a06050403120f0e1e0f0409 70
    0x101d03c0d4520030025155245541440b00c01008036150399070090b15409100903107030000e401c101010b02141401c03001a4210a607401c035440c1000035072907000c940c110f00403580c684107640352060300e400e03001404543c01c010090710020402184503d810030032242a04d000300c00701c440c114048a405040300c20460310000c81c40d0428050800900c0d0407001501d14000d8682001c00c241045212280d40c0c080c00703501510000c1d850f01181265800c15102d0148900c0b1411f400f800062420008601d1781c5c45184141c03120210000001828002202101c80703400d05820409105501d69080950140640e60003c00420f4810440019082a5441050284035041c2c48d1001c02c003024181c264001d03c401401d05400000400141140040a114400c42c04039849000905150910148070804100d60020800d0001c01c00c81480482d91343c207005c0c1d1480c0b405181c403142880f082c1408440e19000e114619030040d8200c2130f03010841c09004089506141d050354140c1080000008010030b5541c061006004219 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 492817005 1250 492815755 492815761
    0xb090c0309070504020307110f060703050108030408070e07170403050d060605270a05030d182c1312080702011a150702060405060c070609060824011e0f0e18 69
    0x1030a4000c0d69204062341031010360b000c3c0007003003a4100142d181ea1440302e0f80010003048103d940500c900341c050080a0700450a0a00f01903400e41c0e6042c0c00d024589001042c0c10001e402c161180c044003120044003244102c1d503040a14003d041904194465240e060500c1c0c40807078264402c10961358071403811404003241440c14285a039145000903410b44e0008401480071859803010041301c2c2c101034903561414180381c540c1e070320340d1607065046d00031101c01d20040304c400080800440c80c00d030541c882e114000740c0300e80b5892580140d40400d80c030014808000c43c0040210160481c1d0030b2481900f19400030b1000c0c41c030250354003d1004101000c1c035031200542c11070303d054007000c0d000740c504103102900f560325040e100c1002880580000c0000307441d03079003c0d00c014000d451b07010b0704a000030155030a0100881c1042103504045c2da00b00f1201c040c11102445104410303a10408500c00180020590701c203003444e100d00000e0203803100d00042d002040b0b15144483c56030400703607a641000d075801d80b21809181c07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 492818255 1250 492817005 492817009
    0x604110111011b05040303110106030b0103080d02070c0b0c1509030301121113062108161119091107120e1504060215150a030201030b0d060e010b090c03090705 70
    0x4400c0301c81c0c25915981d810010000703110390901402e0300d90058a4040d140c1d840c0d0702e002400c42e0700140000300c2c40e90400c001000040d404010283c1582c0d40b040980d1b450300e4007904900000d000d080005007400704001c2c000104900040014031921100d1010380f800101404200441144161280c4000e54001c100401281c03482161602409201d800f1150f100300c070000015500014802c5446031081e1b4488040046040c04d500080e0100c110184c00c01c40d4010b40e8a501e06240a03c0d092000c02084044404080180440700000c0500c0020701419001c40303000d40d01e01c0c6046c010b024202405203040c2140c89030001441c02e40e1010755001d42041078500e80304404a6502130b00101940c2c211155403402e500ca89803003000340018103129402841e034074001180e03003000700b0005000d8201078005c103601d040258840c10014010380c1d4081c00c0c0071074050401408640e0b5a03030380c402e02914891914580140403141034020000600302150101c00c96101c41032640c180b8441541c2c011455484070100700014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 492819505 1250 492818255 492818267
    0xc0a020d030b0a05090f160f08131a070806090a061202040906110c030c010b01030b100e01090f080a060609022a070b030109020306150405060901080604020d021c050906041101 77
    0x8806008100f4203940e62000c90300048080d50750522010340c1c0707010003154140003801c11007011524600980c0709410a00c0103400c802d4041e040c4c21241d10a9808542400040480c0c034220319040300c00c051070f07840d10b6140241000b9040d25030314130503c26240401d402c120300e8041d030420340d0241000c1012480050f420000100002d1908480007500c41000b84034058a600250a00300c20950103580d84401c041703041402c44103050724003414075251100f000550b072187c0448401c00006418840354000e266401a1002240c41d4048284894001404141d00e0000306034545030038400c620034402d4a442d40200d40071ba02400b000c0c0f0943c01d80030018008a900b0b101180b2041032190000c3d03a10058039200b08040c83c2d8800d81064500396000401d1240600740b68243d4900c040c406902e2608150511002a440e071140f10307041d504020030380c4c01003601555194116680d1241c2000110740d60301d0040d01556100128240d9050003904e048001b40051501140d0300e0302c910340c4801e9140350204444015126 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 492820755 1250 492819505 492819521
    0x20d1e050304052415010305100e090708250f0b030f040c081203041406010302150d060807060201060f09050910180203060718050103140c0906131d0c0a020d03 70
    0xa2241c0c1944d900700d03880c0720fa1142c982d01040802d01c4154030700080042e035101e0b902c00c003190406140600b0011110203c0d92040d0503a00c900c04040e441c0d4459040040c500946508285514050b100a007007604d08501c482c00040d00c138104851a2890741c9000717000d003c0440380b042100c0001c1c01c10015114140a0f035840781d2140c820803000100c030b9254041c00703182c0300c0119900408007130008184401e0000040702090b81905800041c210f03581160b011841d1401c1d034159400d014040400e001112680302d40004019200709022604130700d540d22002806000e180c402c0341150000b641c0c010500391128098248145141c000408c0411040c2c60160300828601281503180d516007000d200c0141d03014450103004101c1c07079407480341e8410b1065003040c80c550107a2000341407501c3d00301900011071201e02510f034401a00c02c0c41e140c030342d00c946020401c04d2082c1309e04030740b64075a4075a0105100c02c40e00101ca40783c108010b80e82503141e5610071402c240d4841c191402000d41d000e500d040f80c8051107a080081 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 492822005 1250 492820755 492820763
    0x1208040b0a0804020406080a21030b0316140a0b07020105160f0c1814010312091e08100e030d1a0d11090703020a0f0e210d020d1e050304 60
    0x460a60340d5055160300ea00704168020014414074103020944c5094050b80300500152400380c407190b1160390b52921284440300140300c000040326002140c031802588000c41e03440011f8150b403523900000f0050f40010440c0d000d130b2400010747c0c0c0350000c043e081080656040d522019801c901d00344050f001503401d90099080300030400c001c80405800215500041400c540c865088d0040e07081c1004c10000d0180000d01d182c1c19803514101c040c540c541004880b40e8116034001603140c240c1d80d002c02040740c1c3e2008541140e481840003140f09002031681e403841c0c000700d8650380159074502241040690a6551040c20503519501c01d01c06001c061150f54019200d80441c044042d0100c17000c0300205107099640c032400c1e500d00884402144040c1451010b05a00180f185011894200035a4010b4001e0358040f010500f000a030b040101d556880b13110313240200d2100340070b441c0710100c040d2194a81d1403c21030040c0c4014002ca00c8002061402a020418450070303031800c1041800442004440310707040100b041d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 492823255 1250 492822005 492822007
    0x3090d1e14040902040306561f0801050607020603180a05010c020d0801050d08030f041a0a0c020f01060605032d01030515091515010e0306070503061e0303041208 71
    0xf50811540c07009200840c4034800210750308800001e0f00e000c0c040750446d550004580d190b01091560f030309804000715258031021541c8800001540f007078945000c5101243c106103444c4042c0c0451400d140d080300c640f6401d0b80c5143c0140e8850040c41031034042c8107402900440180702103100031411000c840140381300caa084460010345510380500b92440341e440000560090b421140b2190b40c40b03c010390242101b902c006034112450368401400d8840101a2000954400c01150030042d0040a92100c0441c0814030000c0d801d00326103620003055180d008402620030980f5a402e111f006009180480e192038481c2411030380d0742e20f0300213605d00045c0c402194000e225074004c0a00401e075203409010714080c500400413000f01618040c0e0a950150200105030301089200c003800d50401c00142e032044188003101e00c1c82502200607500e41c0041c06540798140100c3c03041000503035000c40a14031441d0111144030001c249015180180803100710840d415400400c0240300b1010350140302d142c0c151103440c000b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 492824505 1250 492823255 492823259
    0x3030a0e010c1205031f032102030706060b27011d061e2a06060d020427110604052404080f010e0c0906060318070b04030803090d1e1404 60
    0x30380c43c0c203000048180040b03100030040c001d9614094141c40b264001ca844802c03d281e0540d04c0d81300314012083e41c5c8029801c1d075003201c02d440700d10900a8803115036001c502800520b440d594040f0040d00050418401c2010b01407095400c46010020050207100c1a11860310aa521000b019006029104000d400200400140750480d8200301500440d51000994581740c22907512190010070402000c0c00043d00001200c0003010000b158035600140221818102c4490700e2000c2030181c248001c240c1c1002914040c5689171240001088942500c43d500d110800c1070700a08100d1a8029402a103401c584044003000c4200110b806e00841207000c8843d42d4141030769036012514084e082d801c003101c665100e04030440c06d0700c0c0801036402203050407210140a0318000e00031030201d01008140340d800d026100c00c8450840014443c20b4013034454600080d80e250f0301c1e402c0c15400c07503000340d408489900c516400703820214802c503000602c194018010060090106d00202c8040340a1581d01880e00c40400c80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 492825755 1250 492824505 492824513
    0x103141314010b13050103050c01080403120c03290102012414030a0206040f031b061d0a0f12031407031b03020c09040f05060702070e0703020c0a060906200903030a0e010c 75
    0x1200a81c103413009000701d80d540c110b242890070407441d803200d9418401640103000009800c200d02928504140c9400182d48840c030500b00c001d00700b81c030300720146400f04407038035070200c44c03d140008020802a0000d110760030b900c4c1d0100400c461940198082c0360043d40061101402580300210014030040407164960741503000110254051750044280720000401041003081c12810034140d41010b4600e21030161030550054264038007990310818681078040c0c030b524540e41d001036220140c0640c0b0764446a140d03d45e5040c550f128800d410640116120120100e0f800000000301c17501d0603415901d002c00c0580e03848410040c1007200318110706600812414541070b031a80303940203102c0d601401c3d01e14600d07803a9042c040c2c10103001404034400c40d0800c1a0500c024840c00401581001c150301d030040e80c50080902ca5400c1c444c186400418040c10800540c0501c03006801040072020f0380c42c22800d41003448407200e10170384219040076400da003082c04a2110503020701c51507180c860040c102900c94060743d80d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 492827005 1250 492825755 492825769
    0x192a05070314031c11030f18011103150a0f090c050c121902030a08071404080f030705010e1f0906110a120c020c0315041110020703020103141314010b 66
    0x102e030481c0e0000c1503240415130b0000244440c0250703003008008024034030761014007901c801071190031520b00d5400400c041c00241c0c00d180c0968114036000300015440740200e05100e80c02078034541ba410010484040b5903103092180041164141961080f800749403400034000361009036000c0050203401e12804a283d0403c0c00224601d41c0701000c182c0d07a481e500c04041000c4500100b0490440d8000e110311070a0320b403c4040550003d17850b0415030011503864003050070901c201d4001540030302400f2a00d04d40004008060400e40e80302d007000740024106a0003003541ca4240c07819941442d18600b85a10b02c07102144e01c103050003401480d011030034003040400005543d101c0011000015410640c509849000384250ba024810500c05071811100e1840040c0c2c0c1d940c1554890300361807202402107410005041c0038480701900140c03c00c0c0e4074084c10708d800303900c50310544401e0380424141940c1f294401c10b00711006206240c624500300120007607840321407030000031080781d10080d075880c0c01004655403014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 492828255 1250 492827005 492827033
    0xd0e191202011a031b0301021603090807050907090909020303040306020304031d120d08130605010b0c070902030c070312060e1302120102160210031808192a050703 72
    0x52910341014030200000342100e991000c1001c1c042c1035400441c500f541c020800b980f8500c2c2c14401e0511300c511240001380203105072200c0d45081e400c400408010184c0000001044868180540b01107580d00c00900c01268021101308000805002050150382015480b915800380068112400e2a4a0b0358803d03003280e1042e80c0544c04201e00c284070f08081e10b003c42400c00074070021f8800703d0700e04010040080d650503c0100300810302c42c12000052540f0318030300340e980a06030440c400340847c0d65915030914a1764481e91118a0324002c41402217a15483d034000ca0340a00d81e25810b5500c1c1c0044c03524102c0d02440003814010000340c07078601c0000c800f511603201c58060a1564070010801b41c0034410440e40006406414103540d00601650340d56407003540424010710b030191584040502a0074080700104100100b40010389040d5049005000503800a0503405403621000b41c803480010350151075114228400360760120001c440c0501485030f032800c02c0d6149100b03004440d50329442e55507070041e40280d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 492829505 1250 492828255 492828263
    0x203070b04031b060e0f0d141806070f0b0906011208220905070e013906060305032104151d010e01020a02070e0f060904030e190602010b12030d0e19 65
    0x1030091100a4042071020409604180c401040e540b41c80c10000b50503c60039407810401c0e00c40200382940455469115036921680043c034550742e0315035500c2d1507444a80201010b5480dc0103800026a801c080040d000e0305a401d0035902249021982d9030342a400c1e4402003c5400c207141544501080f07501c0d0301c0541003d844041c0300407a071890031040007032040c100f10b054181082400d88840704083c080c508410010a41031080b040380c8081c19010348402d00c50340c0001080e640c9042400001d100010000e469422032a00a800c60040101c8000103056825034000c4c0910a8605810001d1800781e444080d40a0191221800d22000c00c07000c582107540a018010302a500003400c603201c294107000342c50280c49949882c0016083c040040c0c1507130301c001046607000742000400f041c2410300405e0404100310004001c443c964407011003140d42c0d05100d00c14000550b0811909000500d00003000100c0c1c0c40c03480b0010f50800081d6011400039140c080394100e080c3c0110880c0e1901c00891848144406010f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 492830755 1250 492829505 492829511
    0x41503020c1b1f320309030702190302030615032107021203040b030417120a020d0e0705010f03091e050f1510050603070207050a0f0303020f0d0203070b04031b06 71
    0x2d0340b410312658110369869482071080c050003c544a64000f4010ba110020903d03440b443c080c44500d40640c41050503050b0302c00c40601004000c140f0310000010f2044900c01d45013041d07400c181e8500f010b00404503020080d4990402400202981d0b02c04844a060b10302c000d0446004151144034444900c00701c00c40e184094000040d0081941000b0820903200005040290301e004c0c82c1c0300310324049020192005144a176500340d40884000c6404c20360b0003030b445062205049040120921009500c800c201c00301407810420f125501308400b08111046400c103848515035000c01c56012401000110000c41d144c030000314184a00c046008428403400384607070003d092161340d114400d4075040560800410002000c4100440c0c0b0712040e6509044a10550311070b5160784405500b6401d0000b190801508801c46190029004002408074401c6a0198094601842d241c0c400542c4a2184482000c0564400c016400000d01351020040d071150017445c00102c01e80032000c0006a080000105599103030b1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 492832005 1250 492830755 492830803
    0xe1002070e090d020a03050c1c03050105031903080a020915030a092604051215190b1c0b0709120804050418030906050313020a0b1806040803041503020c 67
    0x109801d41280c0002c9400300400c0c40d40c1c1e0420000390343d600c001c24000c04121011030503600000d8100004c031403100d55503240b83d2009040e0b900c0100181024400c051180c0b098061500200c01003203072400d58107806a4030355000b80d41d00f9078000040d510040056401c8070000314020b174641c5542c006180070f0418450003180700440e50a0100d40e01850044000030342810305e5110400c40039803001c903001c5a02c1550101411204070018505180f0081c3c2a00c02e001d880e4810070642e402422a160000e528808041081003041001c4c45a510805d50300007013007464548110020420002c040d5038041003d03d40002a188c030b40385815140105004c01f19410781000c03609210600d000d0140103403194211540e8109101e0170f0710001c02e2810680310700014400c0c0000481c543c10045814070440e550003808001c3c5099544010a03039681c0000000e00041000200e07d00032468901d040390211800342c4021410681491400c8800140d058105c4042c1582007181108941c07051000454600d881d40034403140c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 492833255 1250 492832005 492832019
    0x90209041116061503050607020a02042003040813050d03030213050904020105090f04180b2e0b0924182d030316051c030603170a0e100207 61
    0x803000d0040c032046071814003240180d0000140504611600a200030881180030f10010079003c040d03820241c0540225010001d1098000400000c2184281c804005880d100d420710180608004c941680c010b5081021030042002000581070540040d00000c1075035940380000b5483c00c0d4402d404030040b0743c020030841c0e01c24403003241180c024001502c8400b00d03858990300081c4280719402c3e01500c07030300319203140340c010303440e254401140c0d038048842d0100c44a900d0309010512140031900e1400c0b0401c0c2d4044407001c1803d91516940e0300884a02c1d50384803d0030070281c01c03442d410046e031031504045100b20f001540001810800191800b0302c040580c5c5100104188041246086c030060040130403640018008043c0c8034640500a82540401c08a40340000024290301c0b5854054119406440da940213002002c00c5607141c6035480c5125a00b004d80f44142542a00d01c0c511010742846e02e0343c4640e8090024140003860054850b14000700c2140d00382c4001203040d07118243c20001a40108000d210f10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 492834505 1250 492833255 492833261
    0x130204060c0c052202030a060306051f050d02090f2a070201030b090f430809070f1401030b0a0915120f0f080f0d0902010906052107020c040609020904 66
    0x160106441c41d00e654070140c0d44d0b1209000d004d03e54500c440c0c1c0d00200140740c81c2850380c00744024542c0320710140803034103102040c034606d080620803074640440d44a400041c285010061807102c194058440c0009a5850800156081009250303040000382e042542c1c0800440b520640c0031030a02e40b91454a602c05400010b08071042090614014200b00041c01a100c0a000354070b54000002858407a05406000700c00044c0c584003a500c480140d00d10351030060480984014001010342135580c3c0ca101e070b94030390b485691813443d440350802d01d800402d001c1c0030180301d08401d0350000406040114000c0d64801c0850748251581d40600c11343c83d9503504000c440b40b044c4040900410720031a04050791a5580c48006208460920040074401078420b01c82c100000070090711b0f00e20551010b15074541e005990920007800454404a00107100502d0101e8035500076001c0d5260000800104188070b0681e03007080c2068040a04507009620943c1000800d40c0d946004190180031450307405a20f80b4242c03024001030b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 492835755 1250 492834505 492834509
    0x30a0608010e100c020708070f0302030c10050a05071a07030e0105010504110f1608161a09030318031608190c0831080105070215010f1202130204060c0c 67
    0x9540d0600300e041041840000c1c08440b43e83d0520400900f0801121041e4680020755000201600030032100007540b0407002113402c2260b0007a001c0d10400203c01e400c0203110380e0041c1071400803c0c8280020701c0507a200744003070103c8910504004035407007007181449044a8040752842c00280d01e800d104010003500380541401003005031010300c036581100c03080c07030140d01900706042d00d03040c800b150014540c02d181c0406450340d80c024504690359043c4551111241e24011420b40c0e080008050580000c540010414828071583d4044d5045407a840b82d442c6201100411301e44070b0344000d10140714007602010392800c1c5103114405480d59100500c0c180030040404032075a206001d2510031480111713804400301d9050b014040084003d10422060403d003c003004075428441d541c084001045a186c1544900e0040190360200e0780400c8525010410080090140c5441d42210000800c01110030aa107030316224402070202c0090401036010100300d810a0b484080000c20041281d4180f040341d00070000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 492837005 1250 492835755 492835769
    0x260f010515040e07050a06091e050607060b040e031b070b0a0504260d0504061704170a1205040b061c0b010b0304060209121f0b0a0314160b030a06 64
    0x2481c07801e60264107408035005203450082d501c401034000251814042c8002402e0006c001c0f111040c3c07200c81c010402c03400340c020f009100f00d15821403020701301c610108000321071009140314589903155407800007600b03034400915000b40e10b4100c070042c01c40c3d0a1000d40355262a0540d6241140f8440d44030b10300c0c02e801c1e507200c2e03180d0f603604010200000c1c1d0304c0021542603500070800030f9503a4901440366050840780540d224058019201e07184003403640300c40144202d80389992903001e004030703207800c8a40d11f00c0c040d140204441006009130003901d112401030440420381742415a550b59a44083c0740035540c042b1001c840244000d4101306961512003a80c3c5d0400300301442f02c00454640317558038500140103014040c04440044005800c1110540480b0100c000c06482040101448070a5039620008110750040f403e2009030819a440c0d0b4074800c0d4010741e0350003800407403010b14503251650700c00d41e02c0c2204c558501036503640c0c1d06030300f2415050000512428200c25924a04024002c0466440e130300400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 492838255 1250 492837005 492837011
    0x1407060309050330010603020a09050613050411090901030f030f0c0506011a0903010e06010e0703091e02010504030b0c03070e0a0806071817060415050c0d0b0a260f01 73
    0x401e400106403070409080c040b030200764031440000c0c541140c80c00300130240500c148070000314205a140c0c01601581d0003e03260f403442c0644038070030001c07180100c090368900010025001c203c58501600803982b20300d01c45420618058403c4040342101e4001d81040c1c0b1914020f02c005000c0651102108107100e00601c2c140f48900010fa488a40301d5034188542c0d1075001200080164004c4d0010440d41002c1c0002c00801c00342c40074110060312178009225202071181c0c8036002035a024040c0c05902201980010103c030740c0070200c0400401c44004030b0701681003041c1840080000784600f6070b050b0103450b134010313045e0f164605188000c2688450a508501641c00b0b00d0302040b0030400000c0b002c3c4c0101e614144000300c44031280c83c10310003400e2940300b1035041034443c1c040144c202c1d01080c0c1c1800f490245814003082c2242058510a403003040e910000110300070030555100e1002030344120a00c3d000109601040c0f230b0384030303004001030b240c0090742546000d5100703000780c00309030410100140c9607040b4024 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 492839505 1250 492838255 492838271
    0xa08011103040f061e090606080f0307081c06030503070611040b03040305070f0c140102060112050c27011401111605120102160803091e07030201120b0d14070603 71
    0x10000038040500000e15490354101100c0c2084845c1c1c00a105080c0200a00102d20480c00c04150140c0781760700040c0c40452900030003040345103011408251421242008500d403031300e5a501c030781d8180d101c0c8292151056001c02e444041e03504a000d9500114098001551956400d051900884084040f060011101004100445120740c425030380d010380c040c00c2040d100c3c8014180b1280c036008005006100790303014403000c030741d141d80300c046440a0070b03081e400c645050b80c90700c00480c1c44003030780c0b10040d00a5000e8100c10072645081c942030f00e540c2d10a1140c5419007044200603810201080c3c0100031206102d00504a8950f41b01c010308000783d188100620503058004104000e0810500405010360300140b280041a202501154001801d10390844135240460401da0341c00d070800d454070f1f8410f010341d160042c4d051055100546500c2c0004014040301d900c4d541c0150344812038195a101019111290010603685201606980c2070240c0104000c803100341d0301c0541807098035005071045c940b0341440c0b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 492840755 1250 492839505 492839531
    0x20060a0b0f04110f2d071a3705041b05030303061c02030f01020c011a04020909070f20060403030b19053c03250e060a0f1d0f01080a060c050c07090204050a0801 70
    0x40302c011240318480d5072048e40340d2124581c40c02e40740540c0c0003552414441440100711079140c00c15141c0004020708058185c64608058803448162161640300c0d82000b54400283e04003540d1554203480181141c1d034022001c0b003030a0980c0c12000c420001d91f503403111050b002d102890a41603001604442c110300d80140c800010b10320040140000d01003010010185104034003c0b10320301c0f025481d8030344080d4080c81004001b9500c400841c1d044000031708240441e5002d0500c0302d4451001510211624a118148011302c00424211030a83c00c0320919460107040401d41c0d60790ba2850320030303100805000006c0140501d031030188100c091018288101c0d08814003070003160501c90694074000641c20588d1200400500340c1500c80d0816415090f003074030009035601e81c0c11507175020403030320759092030059880e02107081c00503000f41309081141e00503450034400500540c0c447d284641003414400c1c01d06e0b4040886600d803070340c1a00000811940010140010716140701807200602c42d1800a100122184030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 492842005 1250 492840755 492840781
    0x1090606050f240405031005011a030c0f090f0a1202010801061112030c1318060e040b1305011d030702150a0c0320060a0b0f04110f2d071a 61
    0x1c3c401c40030510b11078000040301d265040314001c10000f41220300b00030b81c00d146c50300201401e100b48040c40044c0c00c00200504905402c0e248184500c429070350421a20708e5024070b00d54002e0701e074542c0c0000001c0303101d46680d031003c1d2510301a01d081c0b10141e62490061002500961040e0010800e0103a41e400d108900b14001500c0f00303070b1200e4009001d44a807560006d51115000366005514005820440032818800042841e40110103130107060001d40d903184182c0c40c01a0059a01500d0f0384000d000051805c00f0a1482c000c070f542c814030000800020600151085081070429683d140e0000a00d40c4254500f10b01071140e10135a200306607252015894026094140c4080020280031031030032a045081c1d41c1a1504207402800401c6e0b620303a1034400d986e85c0040c51840000341c4144090034483c0d0503424680f25132201c0d0007251180c40d01e03000120746049180c1e04800300c54070b044034264102e407112113201c1d420004c1d07000c0907045482e02d48000d4074011b544001150800c9220300c00e060104a800700d031042c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 492843255 1250 492842005 492842029
    0x2070c05040b0f030d200102040e09070b0901050306040b13060b1804022d04080732091503031b01090c06020d050d05190203130c120c05040509010b1201090606050f 72
    0x10a01b00a0407590712100001c4511501a0040652012400042c108401803034588502c1040c1c0c00da82c100f54a800c0300001a0268000c424005070043c0700048041c103181c1d01c0f00c07021400c000c20041d90300301d00280c541c0c01c0c2e40e1260403581d060000840c410400c2d840d051000d0300309007400c807815410100c81c503450402c41d0a9131183ca9440790f4160780f103601d50392500f2007120090400d810694407840d03290450102c0311032440102c02881145022142c01000d808000c2c0e845141001704090140d0b16106410b0b004c9071150010703a98140003c0025a01122040110000324070b040720005c42c40e10783c9801c0c2170110110743d5000c40300b5508100031080c000c59124040380d085d001c5c0400d001030503880d01e4811000d540808005039504038800001d00c0302a03039448181110703041c811010100d4054565003500701142103100006c0c45012403440501152130b00d900b0003584102214000185041400c0001e0307807001900460a020342d40d24003118052041c0c500502c40a401d050318411720b10070005001c10314200d481 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 492844505 1250 492843255 492843257
    0x606141e0607021f1110050106020d03090602040b0c1e0a020603010905090309222423031e060f040b0703020702030a02060f0a120629040902070c05040b0f030d 70
    0x1040011582e13107092010000f04c03120545000c01d2261a806030240c4000d01210207548100400103188046a020b114141c400c1f81e40038001201600005601800001e84126a0700c0d40178040030400501701c1c0090301c0c9000410004004030b40010340c807a007000b81c040000e14125082040e2110260301d8810032641143d8030f4103400600c0d039540224850650140c1400c1d41e6101086461540704188100c80f00006140c0e40c103820032040282c1c9003207598402d50040508034851059030100308050140140c2481041001c40340c0c2140d070310400000f41802451001c809100303407981202019414108441540402038600c0721409007001d8481d541101c400030003003020550005031880c2152000e1180703004051f07002e00082d4a40c0d1000030381c620a5049104890005079100d642000100202c6c0100000c4480d40071201400507560380001540004004a0b001c9240c0308001c0010a00741300e10052000c18000d4914134080b50508080009031101c1003866813040c41c003c1d2880e0100d54002c1210b00c940d22031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 492845755 1250 492844505 492844507
    0x9060409050303131a0c071e03021c05040e07020d180308180316060e12070308040312050f0304120e0402030708011809050f030409060f0b03041509020d0606141e06 72
    0x13117890821551602c8900039801c0349075102c18050000a440c004d481d005100d1886028440b421421300b440d4800d503044083c0050340700703108014003400030300d4018002d003000d8645071340760a448403094152460299614401030340000d07001411191b000c2100601c01614601e002a640d02d143c4404d181030262510404070205066144800382c1e40030800d60301c00c807420404100f40705984d424090400e0203503225550140d5841e15041d85070101c0071503038134156548101c0490401d82591a0200307804110000380d01404002c000e0703e01007200c021f000d18411440307400011214038003a4030090030061003005080c000c90041c41401601c80d00880090306480b101522030701138900704840f10b4050188481d000c5d09a001c0c4030000700c92a58044010802d440c50904c01341700c01507541c40000c5105c2958414640710290900200700041c010320100c140c140d500810204409075290006400ca0001d2081128210359414040003e81c51080180045844c04c8503170003400310b010044544051000700125108101c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 492847005 1250 492845755 492845791
    0x2d07050309060a1b050106090605100909020a03020c060c03060a09140a09021315050a0b0a0807050c0a1202031c05010f03060b060f070f03080108160509130b090c09060409050303 78
    0x4440c40107213003440c00c003507855511072901e400c0c001d000b030100c0d00a1841c1d20341061008501030405078541455481150345e185169498200390301c0007900702040c52400c040c0c08004804104d141000070034081d0314000c82c4640d0f20b042082c2007080b0034007e5400001c0c0c403400e110301008400b55840001b50b202c00d0f1200c0c049041b412b1741c4005041d503010031148a18a030315004c620b13101215001080010b6410a4641120441d04c5012000c140d0145185c01c07000140e11600240040d44100301921681d407445048501c40c038456903c0c03603501400c0fa652000140c0c0049281403942480362100c8a0a0749249170422055040000c0c2c00f070041075034000602902c0d1180d0800c49161140011902c802024102154869581d441c05100c110800b0905a0001e0320910000c6811400401e04100c0070340c11001121f0b0f21440c100a2000c0c4510080c0041c07500d52401c80517070080394090480d00e11a000074405030202280280800107035650280089014900c0c10590f480081c10000c11030303405c01c59205400180750 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 492848255 1250 492847005 492847007
    0xb0f25111e03070c0806040209061309060c08071e121a0d080405120303060d0f261317060109200a03060515090907080a0b062d07050309060a 62
    0x14101c081c5516808140e0421644030010200203090528418948403250701d40d0b50788a6030340c601050714080e50143c099030100b011450302c01030240248141c2d0304045102017403501c0d1701c0e00700d50074000000c0c042410700042103541681726000701c0f901661004150001100000002d05c0c00350200742d2406626a60002034280c3c24008200e04c100040040c2001920300c940d2500c465640c20910415004032503664441640350800b0050340d00c5454090515407441500e5294401d210102103030594107210b102c011306030500300081c0108041429000c4c60b40c1e40c0c09010300180e81810856202034014207084403030220503a408034600781100d1904801042000340030b1048500701800604040c200ba20000d509544940c2682083c02110b5040391007a00711031968080244bd44a00250294440d00c00c0c0c002801290040d0301035608404c0928001646e80c1c41c21002c01d00551048050002082c4503043c542c00428202e00b042c004c104094825a040440d01e46d580c40c0d5074050000070503c200b8010694104003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 492849505 1250 492848255 492848263
    0x9092001020307140a0308010e090c010c0206040e040308150109061205060f100207060201110306030d0c0c1d16050c2e11090a14100305130503070b0f2511 68
    0xc3c0d0444c0100c4c80620791181d003141d03950001c1108502107148080001003421b080418030344144441ca000d8580c1000f030714011030350f0340301402040364414014040499206c00302055148a540f0076280c1c040c40c0e081c5481401600706500000504000003a40c06214855018144c0000d0000c281408241a111500000c42d006c0040b42d445410907060211007202c1c41d400540c05003240d016030000c00c400700d0700304502c0c0a41c0c801260f01507010ba1154121071402485952240131150007152004801a1248842403510008070000c0701111800018048482c1000e03c01d410150541e0a0652074442e0642880d51207240e8a0002041c1c02080301c04950101c842454403420400509810001405031511000082e000707203864500400a051011590203d0000c95001000c0300829103840c20750010340450250400034000c50425003040300c15400039000700302400c01903114050500407031500141e03414001d203006200180030901480a020b0020400c090901d50040c0e91404030f6808600022a42c94 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 492850755 1250 492849505 492849517
    0xf040b0303091e0d080711030109020d030f022506092108070f150f0509150117010209030304030c061b0b16111006060212070c0519090e0307020a090920010203 70
    0x205078602c80c00300c108880140181041ba00c18008544110744501c00d0500b00c441e2600c0003500130a141c0f80040100c0c3c005c1c041c41801116900c129414201084040c801c810b64500d690701d000381c21440700348002504030601d80c001d0b002d4694441c0d400300001104810222180002400a460010380c020a100d58020a08a555048200501a52758003103004008081ca0299a02100e14041c082900102c0103c3c4c01c01001e410b060a9107590790070412034404488007009028203c0d0741c20400075065450500141004601030081035040b141b03000301c0548842d45081d000d20221582d500b2340400110070400d000e4100e031158a001801e401c100c0c00c1901c0404002c10041c10510404d11010000006608504180c030041d500381c4210040c1e05400f24254015980005d010301d40e0540f090005041c071030031445141c045000880c3e038207980c6504c990304507242c60000c00d2560700006072103029800c0508203c00148003180081090284649038844002c80554010000e00b50714001504141c3c420016140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 492852005 1250 492850755 492850759
    0x30d082a160b01180b0906040c0201090c030b43050918070909090b04021203090904030306092d11090a180507090807031515140f040b0303091e 63
    0x90007081c5400c001d80c616409204000f4070381c0392041c0f1400e4005180c01260b200b6034000d80214001d8079140104000b801c840b07001c1d01c086640e120619008104100340080045000b000f5001c45c80c100100c101010101006044e004000703070345a40f0b007210b0f5413298222640c69107000b80c070060481c1203000316468420f4902d004d90001c00004001301d5965200701c145d00a21460300c521a070203980705c080c542681d880d0303c4060000c801c0400000c000d070030702050300d200f030f06a00002d803072030320044000051008205075030650000e540c40034180201421485081c0620910554050303013908080c80e0340d002000807400c000e20540e10b6401d00c1003107405440c00d07034405202c001c003840c16030364a0f603018a23624074000d8a4550a40d00b05008110458011a014802d035405000508491030540c0c0320302200141d81d0309446c1500365907440403040071407101200130240081e50b00050b02c1120b4142005444030034105c4161149241074400d05c95039800200b221400d58050391401d0544c100c0014002e125000c05180704c0d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 492853255 1250 492852005 492852037
    0x10c08130503120705130501140d021308190b330409050f011401050a0302240903032a1518011803030203040314030603060c1b011406030d082a 63
    0x4400c4d95044800703880104c02d002c03040c1d80115954001140e28154002d134500eaa417204220485610f5003903001000710485425207101c800341d8034859030345000442c46104694100d10564881005110840c294000c131581034141050420070300042c2c0e0f1002c8041510502c8846440c40c80447d4580b034022090f41600701081c0c450b0038a0980306a40641443c1040b000650b090f03c00101e807901d44000400181ca8000e840da41e00e80000310880300c2d8004c0d0144c854072072044180080b541c01e540401c001d03e001d036000b450061541c00d03108240600d8424420050540e40c201c0c0c0c00700050304d01c2001c1d0656009070915402503040341110101401421541010000003801d0b1070303641c05250705500111f009920a546100b030743c50800c450f0380d00f540000d45120364150400c8001c515100d40d4880a80310807405100e000110740f0311050581e003152501f0400c8000f410022040050600d0140010304001f5040e081c400300c076140190390206100100c0007080505001c0c00350080c9010110000d13500c641d840340000c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 492854505 1250 492853255 492853261
    0x81c110d02070204090f060c17090c09102102090702011a091807030c0509011508010303050a030b060c0f0c0d0b06060d110a050304050106090c1b110418050d02010c0813050312 77
    0x749000d0a0703864030400c08524080c0444101c410906d0190b4030900e04d1070041c080143d2035004111803641c014242440c0d0374401400445c1e9184a03180304050300020a0322a880b540d1244107100b00400300508202c00c1d640b60940c251281c1220700c100d08000c0d80110392541099694201011191640c95201d0354107201700c01c00402004213071000780c015070b041141c000865070b84c0c44451381c0010751a1a0548001402c070001080000d00030009440c850320203003008a0820312540120340035401680408101d9801041c00505080c0d0600400007610f0f020f41d5010072189050f1182c0d040601e014210701c1c0035003800940c030065994154822442d4482d0030320320030f43d2130126000040c01b40c0c000f9201625603520344400041c2050b0307148201241a0340685030342010101c0d44800a200041c04402520041c007004c000500c00e544a10030081c0000081c0709018040c8440c4c14050724014216100b08150380c074061440000c55040445070307a00c4440d024404281c0801c0d031600b0340c254000c00702c8048141610b1018 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 492855755 1250 492854505 492854513
    0x603040f11041113090b030703021f120905060601080a0204080d0c060e010207051605010807080105011d09100609090506090f09010b0319050d030b060301120503040e0103081c110d02070204090f 85
    0x40102d400d02d110500c26060030328109511150031b0b09c00294006402c1c0d4820305407031800d00c590b0318551003d05103c5503200011030b01d60161010017204484c80d41001c02040429038000d04d010303800c281450800c43c02d09040050071592020f2400d4804140403c0000c2d0008000164000a070700d03e41c2d410080d03482c0d50a038a4510b95426a0745011011654030200202d1b0315440382180c42d101d050140e82c1c0c2c0f500380e442d02c1d005641861a540d140c00342d5401c031818410050303c070000340c140260303d0640d100c0001031400900034006601034110280490500f81800080d6a9901006400c60700d0041c3c21751054603956030060050000480301070b0580107200b103070003030400c1040d07540c0c2d10980a0300c161800400c2403103086044903002040160b201e84103000601801410a1941441501c038804032442c050721a101c1c00d90001c0241d100302c50380200050080018a41c0f9120b0045094102d40c05010400d00b904081c0a240114400c00c040c4c00e41c0410000250f680715001501050f8100d040b132480410b160030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 492857005 1250 492855755 492855787
    0xc093207080702010e07121109010b0a1d0310050c1902030a1d0307140424150c0309060e0604090203040506060108181515030f0114060603040f110411 66
    0x25503030007051031a00010078150042c01018130400c81c5902602006061010014403061051803d8440446003040c100e025166083c00c04e000c1c02000c40503030744405468038020141d80c074a00326001000040b400103884c64030002004c1180c241d00c44004210b40e80d40b0a00c02c2814058070903110300070824840c082c1e91964000c40205161007441e034031080500c401001c1700c52001d155102c7c850705070340300440800ca01c1d020000001d640c0c2c40c0081001c50000381e502c00c001d50719841d05080102500c100c90040020001c034400e5180350841500304855000c0d90785c0c8010b490040e1a10650092165a220f25400e950b90b400c00c95001d0052103604540b41e00b000d05000b99940d6045420902066449000c140280c102c90f54824080001d54001d0034842d0744044c2e900b240c906d018118101040e03607000e90607038503607007070110781e82c5001e00c440005499a025441144141c001403c01e131300801080043c0004211070154414060760044454a8100070300d8001c18028035011401208590700442c0e0f00c060200440 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 492858255 1250 492857005 492857011
    0x150e03040f0f05010e1f020c13051006081b0c0a080d0518060c1b1c081f06121a09011206051e040201081f17010c020a0c0932 55
    0x441c82072442d0707256801510000e5840c810641c1c00110a180d0702c00101c0c0c1032048407136200542c4103980d01d61480402089040b200c204041481c80e40b11700412010014100e040c000810300c528002d206c1e410508652007585c5514040c0034000c0200007175000ca200340401001142550068010b03955913250016400144010f070380c688100c109401c0440c042a000042c2c50340150100d00c040c1d8070f06100100d180b0040010b055101245000e83c04d0b404250350601107841700c100040b900c0720007080c640b085031120041083c0c22082150b500407071052209940c4200c4140692078816000603103a440c0074120180802d40313280740c0da4801d4418002260481c003a43d44e11032405d100743e0050056845241e14000c0502c1a50001144490740e5000180998451300c0d005800c00780c0105580d6202074007044204140d006504400e0a8030b440c0d2807014800c40007407282c504508481d201401c4001c0c1c440e40d4030b03d034940251190800305a203c0d401c81c0c4440e1055855030b0503501e0422147c003241c0400c00c00c4009000b80031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 492859505 1250 492858255 492858269
    0x6090105040816050c22050a06031e0215181807170c0c06011e120206090f1302040909140c0307060302130f17011401030308160504030204050f01030c050a12150e03040f 74
    0x1c140481c001c10b0880c0646026294803102e500cbc160400710400f00c130302c8814400240e038071210030039140c562211028000c18540c2054041c0d0844422003c00b031028824514641c3c0d00c1d40f02c031010401440691094690100300f100004a446c84c0d2180b0002c40a1405078100400c075601425000080003450004044502020b000441c100d1541d115410084140000c602a4111404000c000410300d005441c0c188041c030001c1c10100759440c18940704040380c1154001c4440155501518014041c015110064465415005006010001011070340324013040c0b04403000e150300444e07003480c0b001d0303010f440341c1c044c000c0c07100b100c1000340d030301c60303600d040307406032010320f0a155203009040925620401042416641c040d2644605912a104c0802a44404411000803c4018003000c00103903981e01032240280200305013000300c0d5055007403d800840442e484248a810402030030448601c48600c0d40041c150070a0b4031100001c0c0d1070468101918180008120390b0000007004180c42e500c01d0410b105450071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 492860755 1250 492859505 492859511
    0x15050108060108030a120c0c0506040506010617010b07020118120b01050a090e070312020a17030402090702010c2c060a0512060603041106030402011809060806090105040816050c22 79
    0x10b07600c400b0b600c920400039040c0016030b15042c0018900c400b40c10a952200613494218442d03038882e240e12b81092002d03101211560000c100400c58182c2c41603840000400640e01804154940411141c0b40e104504000b0306103c6848440d131081c0e64220110b80043c10607546401c642c0c1034903d05411121070034050b031803182410b508003207006000c52003a00400901000241803160075a103412400f510400580c40851003602105c100041d02845250701903040d60028603100d0804bc4104005488024000c0341103a01d4110342c1094103030301c166041140c3e043c50054003102006007843c005500001c80440307402c030100146400c2d115501c170300103007007101840000b502161602c20400603a0700c000d441c05440391100c5048520b0f54680b80c40155085881410080c1d1004000402c000180110394000d0b141c6540c0c9410800803640f05000960b800100500200101e1605940e05040780c01076a01e00030108102d030030f44008210307080081c003914000080c020403060001094250b5030b080140d520701c3d20b80d41 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 492862005 1250 492860755 492860759
    0x70605030601030f1b030f0e0f0a080d1e0c030b191202120303010e0f1b0d2406090f050108010b070b180105040f140a05120c0321072312040609150501080601 69
    0x401003502d5840030007581c02b4000c3c10407241c5400040d9004013a600f41c0142e60341021800702410b0502c003107200c0003d12004154051580e030041c0440d516404114000c0d42c603841d07203a202000042d05c4209550b000002454110294000314001424407180003800e44030000022a8061001422a1280b800c400890041c1c0c4c1e103400c1108011003400945684409042c0b04c0c00c103426490381c01890110310b45030040c901e0038441d100305107030300c01480d480600407812400d018000d69010022000c0900000c0c207201a85501d0200c0d00305c034174401d070790010b810103038420082040030807051140c1600c804a0002800f0b02e0819050511000100000454600c00d100305026079808011503c1c640e0160040050041c04585040c0a2000d92264060f2003150000f001000319850246140544000021094070040d1520349406032100314046440841ca800310b940d10800b8690081c21202c2003402d4020b800201e440d01e00d4010081c05c10186c0c0140740421112091221105e15440316048641600031110030307903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 492863255 1250 492862005 492862031
    0x10902031015090e04020d0b0411030d09050112090201030b03070e060f04090305120718120501060f030206160512031311150a0c080c0303010b0a030b03070605030601030f1b030f 78
    0x114116004808100c00c10300422002130003418a542c01400a046900d0300049903a805a03203100480303003200c85c09a072800319201d5060030811100b55580504200890600f41000680100c2d040b02085c1003040d01d4000c0c490459109400a8241410240864012640318611042ca00b401240c2e01030141c0c4840d0300d036000b00e24142c001d106102d90551200307840c204802d200701c3c80d0b00000034203002c24001e82d080841480c24009012034020b10303039a00c0f42c443c1d441840c50721a003551026480a416182c8005041c80540c0d61101115101001450310310040c1a140c0750032030070504c800c400c4107070b5108013008200c03420341c07045031050015202da02c9e5464a031682208001003107a000c0080041034409001003142c030f5001d2984042d001d40140d00450038104880500303441d56000341c202c208481808115107210039010300414a0340b207000c038048d1005505002000301217000c01000d41e410503032554412907412105502944440100101103015141a43d902401402c2284d450205040c0740074900d0300e00c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 492864505 1250 492863255 492863279
    0x192a091a09010905060d080a0e0301060e070203160317190b03070308030a0f06090f3c02160611090f01110d03020901050c100b0901271a090109020310 66
    0xe03100040094803540d0800710960700a110045c140c54010075802c1c0c00c44085820140a8050041075940702c0035481010414035094425030340c0501d10400920040c03100d8079030080141c86c1c4042c5203580788040300342d2034101150600c002c400180c4c4141091400d0111050101402040412005400b030000c01d4a81050540e00c071818407001c1c2003804140007040c080f00c2d05800c6044107400c4848041421502d401141040310445008001040c1c0e4a40c10168bc1d0300122180d44d01d1103c0800c80701e011040e0704071040d00000900c500c070001c0a9400038070207081810140e40383d815650022010000b0345001c2c501e8002130b42c8071500c224800c02c1800e91280f16984181d012500c171064403405481282c004a80507400782d00311640b4075040c440b06000e000c040182c100700303041032010000c2000c04c404149000780904c00d1030680200300a205042d070f040301400f030082c0191410006500000a40620b240d0403d582800d8460300180d0041c22a0b000050400c201e0b005103008118200101c103200c0d6407030b4810004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 492865755 1250 492864505 492864551
    0x15021005010e16030c03020403020325050d0b0c2a1b10050403120207170105040606090c0c0b0718030c0905130c090906020d060305030c1e192a09 64
    0x10f941941680c01034010702c01d8000705010031040c140503040035103e40c0001d0800c500341c030005584c071100490007046555079443e050020582550903121043c4283c4455018210040071903015000025861041e004400070204448924591040304c813005500e81a0300e40402402019841020400100b910310b8181e1301c800070b071240d070340fa1149031614641e01c0b03100f41e10302148400254014003030000b4410b8866a140f4404002c0e8400000355494140341600c00c90700076803c03010805150101c240140354000c4100b002c03490b00140c1741032807036403480812a0040f0100c401703181c540c0c0d0105000010820b400c0e031004196104140148256918a0544c40c071507440c280d0042d150254407801000507078030546c40311070424011354000d0700cad1140c403030300b1001030701c031a40c2c800c8400d9840003e1a00c56180b06021810303528a00c403158845102c4480c2c5219600c10802400600e81e004103440d0000304411051540c0a4902e00c00d4072081c4990200076510449130503114165481d4208500c01c0c51042c4030f180c0c800741d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 492867005 1250 492865755 492865771
    0x301060f0f060c06020d02040807061407020f120a150c02010e1204290703051c0501080c0103020d02160f1b0303021e0f010e010203100b030103020a03081315021005010e 74
    0x1468916102d82103c52602c11042982c00a50070060728507507030210b00080000d007540100800c1c0c8145000c000400f210000c119041f440d60b0f081c4802030050307442400300c81c0300d44800c94a01c2e940143c038100c81802c0842c0902c008002d4202c0204284030301d00d45800c00c06000d02c1c03a0700200035580c9501d0035503441d4014030401c01110030f0200801d1100c2240345007900240280e1881d00062400c1c0781c00a042ca60f401010309402080010071441c2c000602c60030441c10090344080c0c2441154944a0240d58559900c283c03d2306150b00812044041e081a6040c0e802445c00600522808086800c00419001c60b00600b52030389503803000302c0c10b804100c0203c1d105c1284d030f160740141304002480600305003030100c803481c01e5814020b542d403150801d1030901410140107410302c0010b80ea8140110b44c0090000180e11124002d501400100050780d113502c0250202c0380c000080c0c0340e4844403140715500c20f41e41500110441500c032849200c0203039000a03403001c142003a0b0b000300700c5641c8a032015140d001048507504 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 492868255 1250 492867005 492867029
    0x60521090a02060c10051f120b070507030215010f0f092c0c0604031a1e0f130b04120201150806040807110a060507200f10121107050c0f06030408090604120308060301060f 75
    0xad02043d108000802c0721078000d1040d9840030300580c181031200902a840040c21a00708002032000308800340142c002417a40b01400c0158280d00c8000300b0041d280c4910010100c2600002c09501120034040b0010403d801400c040d510b81d203a24003400900c0304500d55610a030101400240e0074040d83d039007035500c41e001034841e400d9503941402d00040b02d80300815010007040f5041c0b00000240800101d00c0c0210302c55002c2c0d00c40344889030b50082c210f584040c03001c0640111031104104241002c90019001600650690740d2825181049d01900e07448050142d00500c1c2064006546944480a400c4152040e403500d001010072900c8003030a50008000207520800801c5040c450780f81606078043d00c4603407420708030500354803031401c507007203407006460110762003c0000c1c11800c006040c0440301600004450503460034407400d020032164040104010241c42c8005444800c607030341c0304203403001072450102c11070058600d0324000700f14000c00d440460003582004c5020441c0007104448800784c0700c0b0002c0f00d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 492869505 1250 492868255 492868261
    0x9041b0807180c0f2a020418050c0a230a0b120a200901120906020a0207080c061e0c070806131a041106090409020a060521090a02060c10051f120b 64
    0x680300f400c3c17080d0311000e9200f5120610304010b8071071f8020003036800040068111428050b052440c00c29030400307030b280e00c96003404c902441920070742d01c494008000c211010300800400b44011440541c425040502406001b041000c04000d002c1213091041481401c00e100540008280002c02603040b03803e0111040c0c01d0144200b2944900c0340d160b80218044400b00d007100711915140200e0384101c843c070005030044a014451820100030100c01420f083e110103140401d10203000004c041d249001c1009000f00040c0d80d00e00303880c100403800c041c1c4004000e440f40c608004080c500782a50742c1c00100c0d17400012054a184041d50010103a126940003c0d00a07244404003081002a601c0003001686c0540da41207900c0260701d5800c2c01401600b056111030b50388140f04070094842e802e051901214020300d6508214100001103030800500d9816546103441d20350074086241006500d0000d4078074103282a040040c1c032031002004015244c0c20a0300c00701c2560700c49a0010200084031000703081e818484001c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 492870755 1250 492869505 492869537
    0x507050603040203100f05150f06070f15020a0e011202070b0606030a09080412030e0303250311010e07140604031e0c03080309060a050a060509041b0807180c0f 70
    0x35a0b001c1d200505444044028001810842e0f4180d41e15242055503502001409072050014401a80c2c0440b0f04c01403810390328001170b03140e200708100180103841d100725540c00c10101e110b101100070f100e040d0654862080540c020300c01c3d010020800d0019444a20345c0008281070b1088440c4603400041a4809960710030600c0756507070014008a05059403120008041212170000d0006841d00d800d030700d05495181d003401003c9030f582440c0c00c0d01c25001003008010151505940805512800120040c450b000b81015602d024442032840401c0d4200411005802030102c0d400d416a446200e808442c0d15030389091103001d01460000070301c81e610719654034031268000108903503814415102e03010302c2501c0390344100715600181c800944650051017413004a412601595502168400701042002e2074203000440d05880984054074807104000e10000f42d402e00b0441b04003806400301103c40c4590341c2e07030040030101000b4564602d0303a803030455810041c42c45140354a03200341282d5240e10454106e030031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 492872005 1250 492870755 492870757
    0x10509031c0905040c02070807050901080d03050c0f1206090f1605030c09040915110f070623090f010509030a0507021302090a030b010e280b01020f0303010807170a05070506 76
    0x4024050002c00000095aa92640100080d2a007154050110380d450001c0551500d50716400140c03103109064014410107800003451514a241860301040640355100d039001944540c116180003020001101080349405070303c0e5900520080d14508804d0352002201d0208007400d442900803240d00340106500b1600c070718080d580001c00342c007905290001042c002800c40b1042d103009c81c0c085c000301121a000c40540c1c807030a00014816050545041d062444450440c800e02d1402890702d035407100c0f400000349a13400c11400c10f0340e650140d091541404016a03903100720700074041199600f0234000076480e2001100340c8100c9280c3d91102030900103070707030300f0011a0512046107181d1250b0038820501c03280d55004400c001140140700c201a103504201040707040d51002411081c04104152011a070041c04649880100e16400d80002e403006000d40102c2c1008640000034405100120011400800c04600785007100c49504008001d5491840d6058940200e44001703442034220004c100b0031424240c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 492873255 1250 492872005 492872053
    0x80405030307111e01150803090307151e0915170402010e060f0d0504031704050c0103050a1409010e010606110601030b07031e06030506150a17071a090102060601050903 74
    0x210544000141061451394084075103034821041e691900b046880302040c00304c2e00300150511034042d41c03a0a1522010075500e09151142c5000084803074140303600d09200301044280400c0761484007190582c20180100307000b10b24010000050042442c03030003064020004c400c1c82980345501030b80b8903900e40d001034890307111460440d60003940401c150403484011800409481c000c80c81c00003210305290074001c000a19501c910351621380c01314180004200c0000380c580c03054a00b4a40440c244d039034200d480001c0c00d01040c4680990320031000340894080103402407001c9403d024001c10840d5968902111030354a142403000d40e5401080060012400c2d5030101c59100e00ca600b00469605a840450108280a001071501c40d5075200c005204104041c081540c00c200b0540e542c0345051180400152100740c103205d040040c0c001c03800b4001480000740004c0b402440c07805240e00550300556141011584614080340c0180200070004415600510a4410040d0301030028042c03119412514100e84990b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 492874505 1250 492873255 492873287
    0xe0103080c010e1005040b0604061d0c0c011107020405150a090b01030b0a06022505100507050f0d051c060b0d05071e0c0615031106030703110711010807080405030307 73
    0x902d8007048451001c04c403000b00c0e9010b2060003c0e41d85000d040210340d043c0040c21041c41542002400c02c100101940020300c00c0c007030340642c0585038540708801481445013010340301d501e50810321100304460f001406414010300a40c2c0500c0350b69500749280f104a0109008164061120801440784a1060b80003215001c01814001030440175013001a84068051703008100513800001840030000650f00d160703032002c1070342c01d541410314203004c0041c50304145880444104030f40403a200050201c10010020040c080c0010f803680984c403203000800740c1e40811960108540d01444d020034042c4035100380130848504618407410440c1c0071425802400015200c4c02c200301c0400c06000b0340d07034100000e01141451503202c0c44100c0ca03880ca0000c050303c460f9070302c203680588825010804510a200742004811041b103405940b985c6542c02039004090118020403000d5020414408018000c031a054807044240c881e07401d82e5842601c12188100700701e42c018080d4205202003a4003901803441c9401200351 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 492875755 1250 492874505 492874511
    0x20901030f030e0301050114010215010503070b070203100c03150f050d060921050a020c09130201030222090c2a110d020d05011409070b040b030c040314010c03060506040e0103080c01 80
    0x44400282564008c3c0c0241103909003203a003494240d81c041000404440c906601ca01082d0300d06000242c4a031814842c00808150008920b001c569003030000201222030b0301010007021683d20300081c002c14540000018440d8480c2d80401c803455022241811968000c1804a07040681d546600184c20130030f1080b5142c000601d61041c3c84070030b036448209402d03055034840782c881da081c880c020f203000203810b050340c01400380600748107818003604150f85003160203090241c3d440074003808080c2444c01c007209440709c0c0c2485450110322148560030001c0c0400081e684c0030508801641c2d00514616402ea20440024101000c0c400041e500d400001c08800d009040c60401c15940c0c010610020f156242110340365540c0913034840c44032042450301d80200000300144201350a1642407001c0e0310a60060042000010001440ea412000c084038007955103c00e04003d101d12500303403180a005032040280109061200101d2982006000d550485018a800103040d903e19283c6503540d03801166002c2c09552 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 492877005 1250 492875755 492875777
    0xd150503030a2304060203030408090a030f08030a29010f09080d0305190209030d08040507050d0501020c070509090d18030f20180a0b0f130f0e0a020901030f03 70
    0x203010700150880c04000d489034581028080c446414003c0312074205000200c00344028002243d00105580d0302541c0b000c0040d0b038940f004400240a41290340c00100b82e401c9000c060703000c000b10a0f01840c0502e028a00c00d022040040c54801c4600010b040c5803d006920020780225941c410600c16144085505019220640b5038100504010000585070007181c0c4620500a846113948168107071500f04020442c20b00001301c001945410409090700701700042c0341c1c0402e06100c0203102c001c00600703004008252009481c034145002c3c3d081010030301c106000303420303000945091180c241e0784200040c101422006c9103203482a41c0818050325849034003d14880080000b03008005a003290b240140e800061425109503010f1400400380240d902601c042a15196865400f1031415005840c0120201e16078803442c000c1040e030916030440f20381c09550101c10290442c0300b94410001c014640c0300501048a600e01010341d01c000344980290012490001000442ea100703205181c0c8510030318105400e41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 492878255 1250 492877005 492877009
    0x604150803040326070222050103030c0b070306030809120f032107051315020f160603060f0803030708090a061e060e040b010506030703020f03100f0b0f0d1505 70
    0x2492a4018003955840024103000380002c0001c455160746100c4580c00410101641d0308002d40201c1200038000c1e0510f01481c0018100040c00004030300449504000560750303401d0060150781840303c00d0707400c802e5030404a00e43c1c520a003d2002540d4100c004240740680c0071050110b51b1b007030300c01c1c411582e0165078901042030070280010520509150605100803401c03540150f2180c0c0e0242c442c1c0d00f88541009421054501901c4200c201e4007991952011071410000590130541030a61424540c0100181100006a0f041c1103409071070ba165401c01500e921200703181071600c054005c5502950050002681040c461000350340d100c0402000e0342c0c0c20722248e030b5481040d81e52003000201101d06100c224070861125109039001000c0010005107507081c99180e00700c0340310060060a0003203a00100148086010740c04846c111070381c880201d40d0320301d0240455440740500c1c0c0a50072007042c2082c00002c02996600942e0503c5240300e1780140382558241e1141c004000c0140300c0400c0f07403420b00c4002055 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 492879505 1250 492878255 492878291
    0xf0f0c0e0a1b0509060417160e15010302090f03060a091103010e0307060b1f09030512210601020c0a03050606030601120c090e0c040c0f0915090302040216020418050d0206041a0604 79
    0x1180d0500081c01891070b4100501c23850071158000c1e440e0000c20a007000008015800a00850042030a0041c0c0e01c1d007100d008520880d2451510a41602c00c8900f401316614031940200501802032014061144412041500341c0780900c0100302c0950040c80034402140f010f07400780c517044030001c0001c840c80382007046665805403005180700104070780744030400a00c181400b25540076003031094503518001c03d02d00080c45a080c5040b0b031205001c0b001c000102030364020003403588071310b07801031800e1038556032807401380d990351000c40b1040d00a01461000090810710f80901190300e590000b03000e00040e0408207a04010f01a0440000d442c1c03049802001243c0c8480c40307110b490650307036920604001d0b00018040c100705002c0e8403002000c0e0300c500c1e43c28100c42d0b21810510680c1c1d03044a000d82d58003a800c40799100300c5078211000e54003501c4d03c0c3c20300d0a00f680d10205041001d1049040c2e03040ca1039088810b076181c40c000c03900500150b00500000c3c8154055084480e4040b00080c40014610040c0c00c4050306 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 492880755 1250 492879505 492879539
    0xe0106050304120207060906120b0a0b090a05032b030902150703030b09091b040603060c080405060c030411040c0302190f02070b040f09090f0f0c0e0a1b05090604 71
    0x450303000000e20090010310740c002c01c118051130008000d414a000d80003408103809225100800c034012402424100d40303500005141c40e4020300f401241c98076805203580340d034882c1c0d0410744900d50300d40740065281004210040e086080d03550b4240c081d03080322044c41246200207550010107685d03400050051340e51903800203c5040e51440d280c0c64000500d005000c5175111a401441000c10404205480200055804411040800c194440c2320403a0109001d80015000180606d04022010080700c0c6e002c031500303100368010345c01c80344c45483e01403100c20644400d440242040b64500108103107030803e81c20141b080c100c5031030018039088492000140981036800040001040b400b1400c00c035a0f410450080903204281c032a83ca05480e0801007000090141300b83e0b640381c2c1e02d92010700140a202c441c00c1e4291604103406003c031244510709030400c603d0078051f04030f0349684080441d003c4a0b1a00c42c5082c407069040e001d2070406080391003503076150030230100d16070b00290820010940a030381c0b10201031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 492882005 1250 492880755 492880757
    0x1060e0a1107120513031505071803050c0f010c0b0a05010f1508130c0308070303050f101512020c07080102030915070212090307091404060e0c0f09100e0106 69
    0x2581445140c050548940072040070914100303201c2c5001003a06003042c5032240311181800e568841d50031480208080c1c1c00c0d40060407011403d00801c02c283e540c0d800c0356129144130381d20310002c8062284400600801e901018082d540b10300640308140c10180c40728075009005040010401340280c1c1c030000c41c40c60486020075940d444100410080380c0d00c1d0744080152142c4040d011141c5c16031a002040b01d5001042c01a500d000e170082181409000d20f5844040c43e0448050b958943c180e0401901400d4152591541d6021010021784d41c2d600480c043c0c0c0a030b42c2035800c0c908070030710082011544070001420402d000c40d400c102ca101200410407003400100503000000d41c6a142440c0c203a410041c114142030840350a4108104030264045071039048426042100358840d40c0440220b85070024940016011610f00513207040f00c014845c13281407185200341d07002d1010380f5848011940341e55948400d50b4000c9041e0a041c0f40034504407155581c414000c030062002c40d651040790540b5205c082e88a0301c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 492883255 1250 492882005 492882029
    0x3080609130b040f030e041109120105071211160c15020a0c092018010e1e0108040809030d1d03070f0506090301020d050703061e0b04050402160f050705040c021209010e120106 77
    0x5270a040c00c030081940c00b00f0f100c00802440c034000401030300c1000c4140c0e46c00c11540e5501c1d565205480900706440c03412980e1207144d1041181c52404000c0d150071405051060110300300110b9105c1d10000308100c02550000006184034540300b140fa0141405075554154a484807030140d111489810181210307504e020081c05040f41c200300094640d0014500c418000d8640c0340c2c0c036a000e02d40b03601103ea6480ca0a00c0e25544990b91400c1c4030b0f21500904140d00e038180a11000049850f501000810055103c51a40c120749038a95041595850085c03144115594400b0390401841c542200900002c0038090005880e19014205690840e401103e580000c00d40c1c1e002c007401400d28490b03d03440a812901c001700c84c10750501d01112414056441401d00c65600080c22a0007030248424402c0048d61020700700d100b130031280c034180752144050300a60340500d203028090345006200240e01e100e0354105903403d5140c144003e004490200700350f07007120340080c08402d072074000403030911800c40180402d43c018 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 492884505 1250 492883255 492883267
    0x6040e150a110405030714130e060105010e49081207091802030c0408030c010501230d080c01090506010b1806030103050322050d03080609130b040f030e0411 69
    0x62000c0701c0e8440d02400c036007031051100b071010b41c40000c6d040c41510410581c80c03600c41d440c400000d81c1000070b42c40d4072135900d08050380642610300c00104036050f1542621461001f00101080c44240410403c44282094203030050441d16002410380510b5000550b2859000c5040f050b0000300d030740d2682204494540d000550410201050f041e800d40005503450090b80c0c0514002c010071f000e1003048150130060358004003052075035048808071b400030040f10f01540e4035400c003a40707018003d190902c03419034030a400d03c0c0c44001c46608400000032200e0014008002e103415519150140d810030380d03071485035650351842040826410009280281501c0c0700940e5103851842c20000e082074100c4240f80907030414801400041e0010080e41c0c2d103500d0523611811075101c40010111404119489a030300a038044081c82d080c540d0142ea181d10a020070744070001242c0b1104110352011001c801c0107011210700101180c00181c00490546410f4024600710000010650000d8112401c20401001d51140000c003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 492885755 1250 492884505 492884521
    0x5070906050303040e0c1804060e04230d0804080702060c0d0f3f0509010207113007080115032102030301061416080301210807080306040e15 62
    0x202006440280c0245040905e000200c0343c9180001e00203040035400441d052911175140f186903034400c5401001400025582e83c40407041a20507076054680800b03e800101c00c0b01500071a2070100720b1440010140c80e2100b8504030303145a002342040b282d0160400850f00542d590801800d044203081d0064410001209005401e00390203c0c0c049003400390440017540401c03030703202d035007510f0344001014951241d1240841d0004000f01d00011062540380009002c5035100550290880601c54034107800290340f1202040706405004480c80700f41f4024040800e0710b0401d003d1985200c3c0082c00c2200c0b10107444540c2c650035500003010060903062618070400600003003a01249040e6140043e019604d481010002d449103c140580b0003032222100a12612485031811616850801015900c800c2140d2820781e0050b8401e2268080310a0b4451036541d03041310041a25408542c020102c0c3e150039003c1e039810b9460f4200420896210313a84500520822009001c010080c000d42c0401d07683d0340ca04415 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 492887005 1250 492885755 492885761
    0x9020d02040e011506020f0c01080c070f05010b0a06110706030b060c0a030309060f05041703090307080f031605160321050421020c0f040905030f070309030215090609190b07050709 79
    0x4005c0301154007010600350681404900303074181640a10f0201c010b50740f610601c81862007540c4009010001070b00c0e40005020301984080d9641d2422218000481d940e140e0481d0158510205c0c1400c5800600c420005540030750301525989034040e000030308146500d001c5c81c5c00c0100014068010035115583e503800c00440d40304071513550303069100070001c1c0e04041c0c86107514488a00c0d089948180000041002441c04000b0b0320302056000d140036079620411401081140c0040e030f6411003001c5064504580c803400b6806603a02c00d40e0010402e0401d01c0c080d00c04031820b004e160300d00c07244590100000c1214900500885100340e0055008424421084002a0514500c0200c00046400400801d141c43d960035001d11607100d0f0465010480d11814103000b41581b16104250516200000f012010107070442c40110889008555112410780361502c9110703c5e208000d0701c1070b80280201301c202800d10380381c28010300298000305002c81983d102c40b11500194800b500650301070b0721616041000c040540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 492888255 1250 492887005 492887009
    0x307080c01050f0405032a0106080c0f0103060b0d0b010903080d050711030c071715010608040507060203030613150308031911090619181805091f09020d02040e0115 72
    0x3a902407140c4c645038031402e07140e00030144150f0300c10141d4004107100c00042400c1e082d14500300402040b115a54400c900d64030841840c207075000300c0321006020b807103602a1046408903283d6400e46031a155001e5040c030020010f001c0d09905000280c040840030505410150a9010905e940041d40341000d200c06014646a0013421070254010010b0003038040c000b103007440440301e0400f81400072404030f4558034200007291082400c03802c1190000101c40c0d40c40508180614000c0701905d820b0364039694100e07244d1000311880c2cfe422480c1b50504400883d9140d001c000c0281000d0312404000b0340b40c1d551880b05502c10b440c04441c1c0819440c6a4903000400e106021300344682a40191800700e101022640901640c8084064502e10a1130903501601600d441c1106007105004194882e4607121103400014941d0003245000317142c1400542460400a9907101005a0748951340220b5050316018000e0718020320102e03007001d010070b070010050f280d80c000c2d1000c040b11640085001c036040402030421134210313 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 492889505 1250 492888255 492888271
    0xb0108100303050a03020f0706090b061504120b060d050f2103060f091e190b1806090702010f05090a050f0a030806060901140703020a060c0e06030f07020a02030307080c0105 76
    0x421801c20000b500074080b6071800d140307403c0160b281c80f850640807100d8013030746401408031414000000c0810034501c3c82c070751146004681c2c071807180400103010b0f11207010350700960070610780300300010001c21001070b0001d40c02030008000d42030742e0036245e5070a82043e511211410341603004c00c042c0301c070f029807500c1c1c55244545003802490441c07070041d0000e01c089030b102841502a81400020030846116510b40040e202c1d0300380b80041c041d0505507406140b60313106810759030305540b0b015284000c52074402644018145d602000c0c07501512541c0070451980c4024007840309644d17031164030010003501c0c2e02400d4400d4400801514441000382421403c001e2048035850490f0007070301c40d9100107500b005a168111405a805644800449006852065160200e069010004144c0310201030340051008031542c42020140306d400107800d001d440c60840c0c0e000440d80b010007400060222071880070041c2d4801c0c0684102c2d1701d540c0c07041d00424155840075400365403140e4001030555080800340517003a00704101e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 492890755 1250 492889505 492889531
    0x9060b0301022a1b04050a2306092d090f0f0a0203070b03010612020c070e150f01020d0c1103010b0901060c030306060e01171515090103180c0314030706050a0b0108 72
    0x20819010410b4000180203034405e55a9102080da0184590702c013031126031a0800d40b0104040c800d00040006c001210218411004440041d031102d680205d6032810300800503810342141010b1000741d914400003402c0d0200c1b88181096042c480c1d4081103203a540c0000b0310041c0c200d9003100c3c01418140200798003c0d1101d0344082004000c080d1f071140040c1c4503680041c00040c0c84a140000041c01d0500c9944102043c013002401c0c0710840f0202c9660402c2000221880000036000400580e05c6142000005020440e49005070b804034011a004201c0d01c07100500006048403080c000414103902078004000140c036481c800800c0540500c9160040d100b41e0415241c02c0c540710000030090091124120b226081c06808114220800615410001303001131151900c10040d10040c2000c0c0c11008107a070001e418002d4228185c0138400b1904502c0341c100300c40f02540d60440c0c13200a8146044145401544030410411020980782c2c455503000c0c958901021802070408030004005c884050521501d02e80b07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 492892005 1250 492890755 492890773
    0x10b090402150a0201020c0715020d0e011d0d08031e07030902060d0c110604080a090e010302060d091406090a113703020301061d070504080703020409060b0301022a 72
    0x390b2101c0c900c1224070350281040d55010500400ca0281c010804020b820348a8041c022540c4034004002075000280d540c00c56007c0043d1000403145101900743d1580890111070003041c10b034040025a8949000107003440305499015501d0151a510032034900d1003000c600401010b11448401071140c01c0380c000e10302440a0519030700010600c2c4200700c079602449585107209810300c3c1c041c44003840752409003c296949071601e418140220b60016880e080001c51004000c02c50350342d6020200c0c162a0080c2c1b0f21400c290504103828020030440030240c403000c203540e0800d00c05041c1002410320070000c400140480500b581b03001d420000c580c2c80c01c64410740040790b9600ca25890178100412181c090000000c50130144007080d1645c0500e40c101035019400c0c0349012502030164000d0440494001181c10f50175a10f403842224107000e107003d0f0360b04681180d20108050f02d025000791000c00e000d010300058000070900000d01320b13072081034207024249001c070364013160061007c10980341c024040c3c050032500e5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 492893255 1250 492892005 492892009
    0x1030e0601140f01030e060f01030c09181506030c1d060604080303040201032c0325031b050712050c100f0c1b0905070206010f0603060f0b0306040e061503010b090402 73
    0x60b80212400e0049050001001a5030301c65040076181a0b540410380d00325051192102c06200310900085e510842c041100007030442c460710444414215041200f20800c9280d51900710a502e50200f0980741c9440e100d000c004201c440c44c036500200310034440b05030540c8100700c0a459000c4020049031207101d00348002c022800000c01100e83c855424070b400101d55100d021b4490b42040c4100201d0f062083c01c085c41189a8000130040017000080c01401c001900303880040f150420708000010700040508002200c80c594500c0b500e000c441c80340341a20180c6403201d01c003034401010814241d4035544485034040d000d092042280c0f90111443c54443c410700745031500501700d100c43d03038001003c0905461040c014140480d4006014096409051099007411240250354440178000c50b8080c3e200c400300007035a24081e200f040101d45140f0504010706280450144180d04000c10158016403900341004002805201441c480c1c0900841e103c12000340000b410700f142c44480815008074100320030302004d6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 492894505 1250 492893255 492893279
    0x30a0c02150c0d0f180c080105070507030804111309140a1e030e03030f070c0605130303080c0702101110051306020c0f1c0e0102010515011101060b040801020901030e0601 75
    0x1042c1d5502219036100c030031000f480c0052074111450041d40740b400c030034040c9902040728102e00180c0140b546040041c0c50b03140841c01c07904281c0301c4402244040040d480003074050703507029900c107025a8002404903111380c0030809100e00c4000c803844881c0d54039841d0003000b80310310f2022000000000240540099541c0f12016022507510244129021170098003c0510a4150540950005d4240ca444610381d40c2e65450540118004580424a41e00041403052140042d144032443d01d52a010780d00e46180c1381503800000140c0b0051642c64100700c0000581c4610300d0b000f20002c600e07038486031400741e07981e0207a0628200c28002c42c1d404c0c2c1000c042c403c040300c205207034a585e01d8000d030005a80d906000f00b22450550945803010303080c065404000d02c0040003680c1100018025100c500d004076180004908031030b07007144d03551860f6802290fa00c0c0e03254450f110b0204504074004c0001140c5490b00b400030000d800952207d20260f4000501c1030483d41c0c1401189021039112005085a5060045402d46 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 492895755 1250 492894505 492894511
    0x81e07200703060501030506010510020a030e181f09020705030f0904061d070206010608040206160201051b0105091b03071e0e0f040203120a0f12061a030a0c0215 71
    0x1001005035a5010546420303401140c099219030854840555a1610a0184c80700f4481520580078060001030b281c1004894556244010f901070106101259030999800b40d1102400350003040180c0d101d0542242000c1c4c8500403614802c8020300450102d42c14603030600d840d0409400e40380180720881c000384002040e15035100111020356210032020f000308008084950002c0c20b000038440d4060469081c1810340f030b0140c0029401c0c0c941584e201d0b14165900c00c001d40c1c00a41040041081d5030900100002d904507030303481413401900e0306100e2590108107a052006400345a550780003440b48601040000880364009400b0f00c0611464040020ba2624202d208640321200500e6803610051240100c0740081c00000100000c14203088840821120049030704900034840d40f81d1420940d0074060684446070f0007075131448a1301103040400c6030080c0d40317048041c164584032140820500303000343c80740b100c4c1c1c0f0140c13243c29200e00e091b001c400c0560718040030348030941d000038401e8110800e103400c032154 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 492897005 1250 492895755 492895757
    0x32a0807091d0105040309030b0f070c0209040501111306030510121e1a010603240b0901111005041a0c09010819050106020303010f090b030c1c21081e07 67
    0x2032200d100d8014528401410b0300c407489552819080008050b0000c92000642c0e004624540b85e686d01d102030509055425151840400c0540c104ca800503c0d111001c298080d1040c40085080c03030800ca058441c641005440c00005e12500710188103042e454403c040d803001180c00320115a51a0030b101e259000c44000020f080320300980850703504040300105062400d41e200a400f066000c000310941c240f40d90070700403c400030742090340c5038a101030707070300901c1072604000f400d01a401480d0040d40403496100601060502c8580500c101200c00184400c04080c60300d6240803940d407030300345050a00404044c4107180c10322403503424800b0130110803055a400741021700b04000d054035090f00d90070344c0700303000c40041c08200d041c1800030800c103a0110285040301d1100c0406000c40d901d070001d1030b003500c1d144095240c040e40440351b040b20074940158a11300c05100c04060070007080b500c0d210107001140541f1a040d92a01d0010000718540d84042d48540c00b41490712800301900708041071122603000030f08108 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 492898255 1250 492897005 492897011
    0x50708060f0109210519080d0501120201020c100e0a0b0a0905030a151503050d020705030106050102030f0702090601030605030d02030c0c0109053f010515030d0507080c030d06032a080709 82
    0x40c20007208222811000f054400c1b890717842000e41ca0900016032000e40034102440c1000000147c1c82c4020340900346c40c03079058000d001d00207140350520000a030861005010003511034040035460729580f4400019140140d807c80d500d000300500900800031950050340298010440800442e003018010440c3d0503017000c000c01d038144500708040c0082c0d0180c0000d03045011b0b6011a2007902d800003421012a5010350092141691318001644c980c0181c641d10240042c080181c1001417802030358040c0e03c180141400100b464403000440d280c580342d800c0e0140945d00019000d00d181d0020400c02100e5102407808600c1d01e824100411f01e1000b151074045187c81c01900d1400c01c6410707400301c04032005100007130100c20106000701c442c0a00015a07210341089c5102070120310364140420140001540c94480904d000c00d0b50746c90803007580c047e40f40754400340424007880c144040c881c00340500560240c61004d4400c001c4c802d90b84804554510032201205114030304001c103600106042c0e00b1600c0c00c1c9000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 492899505 1250 492898255 492898319
    0x90705090f07090b1b0f1606031508010908071a0c0a0f030b060c1e0109030905090a0609020414010806030106031509020406050a12170f1b10050708060f0109 69
    0x15a1241c81a821210709610f011980041d1115440d4864030700c1060317070049a002c50b40710341529450b880200c0d00260508481076040c4103c50007a08601501c254a07549000c01560302c514a5085034414041104d280c60000f81c150140705a80d5103034400c2c0c841c200c4210020b81000d4045180ea84203103000c45080c41041c00000103281d00070f81c0f0102400300b001d054a070351161410541078071400d00c1c078410204c01901c00f521508030354051155a48032035041e2600d120290511080000c075803001081000c070240c075400c0c08502d440403070002d000108281030b030f01b00019200e00e0000d84042e03801031034103020344e140c00c0c42000401c0c81c00c1203184d0848900ca0000a107440c0b10300106008c0e10607604025001101200001003c0c0c0e1100c1c0c090f0b685600800d940c00300080d03845480c5249104460810903040e00506c854800c041c07080f9030041c041c02c45a411200308110842d0701405803541203030503502203030700352003009064102811000920b040910780725500500f8a0800407061707401c40340d1418070219031103003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 492900755 1250 492899505 492899507
    0xa02090a02120c0a1b02031518120310080c0f0105090d060e03090108060a030b061302072001030b0105071a06121b011218022e0903050105090705090f07 67
    0x403200d40d0341200b01601124608080c07807201d69480103180b07000003608007009884e0b55a507840861441c40d8024080c2c4500d4002c4901c0805915002d044500702c014128400c24100d0002c0040703e09421560401c2030300e91070038407500c58180d40e4aa1000540b5002850148078913598815408040c0c50b003401d0a03074a840000c004214241403404000309010b203055001200810000302620800300240c1e03d071170305982e40100340401a030091000401c1480000081055489e200c002c00c4580500e807000103040950b6503ca41c10000e10107110200850030707822000b101542e25000300c8200100031f007401842c110a42d41c0d210499480d842c0b540b82010303294408158103503211015a20034413101800c03540d22158208140d5540b0f80031600d2140468100201c060a801c024000c20720078040c3c1e80c125082c00c15094080c88000c140d04001c0b010700745160300b06407200e107110202e03480340a0500d566218925056261031421904058031a10442d841180304028030b0f528103a1a41d8001c0769800c4030082a01c83c040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 492902005 1250 492900755 492900757
    0x6090e0601120e1908070210050702090c07030302090a270219050912010c092306030a09030c1b1d010806010b07080d0c0521062b0209090f060a0e0a02090a02 69
    0x94000030407880c001c14117029540d000b4100b594000c072500040603800e00c405031040d10581d00020f4215800200141d045403401d005016003c0c080d00f800b5140046410000d000700050303403c880413030702903480014104016004c02608448071800f04510300b5041107158411000b900c400f210070402c0c0010700031115107811040c0c0300d255900c0300c0280504003030b400019041e003e05005991201201d5120f8007505403a0b10348440001d000503014500d103494408020001d084ca0b03003000d83c18000c0d52620800010703c103890140010080c401a0401e0a0420000758000c030a5010440300c1041d0000050200701c501260b5035045548000c0d41659070421131825440d41d00600c030030b2178002031420900c07218094100e8020076044c51040c1c000c81c00320001d4403030400308903429a20035800c61241141c4901c060f0924a540070006520322800b418054560f0003c1c401020417103141c503c1e90000d04000741052002c100f03440d080919224188410481d614901d503483c0104034000c1d10410010002c42c3c804841e0b54 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 492903255 1250 492902005 492902023
    0x50d0203100e010501060f023c06070e1216060c020d0501110316170126060c0c0607080412050d1103040f020307050109060e0d060b091006090e0601120e 67
    0x540c0612082c81d91203800303802060248908408a0342e5001144600da20200d03200144102031003459440400e0b086100707044034460942e00c18403240091800c1200c072410041d983c03080d0030965404a5414441040c0b0405031075202041c000380e0f0003440943c08200e1000180401c1c2c40c000d19142544100500004050040300c00015026528013020100c0c20000200118816086181001803d2014cc68229503050401e42540720015070703800103102ea00e0805807643c0300c0000800000701c442c0e4440b000e850404c1d90a40f20126098000200d080110760180a640c0d400242c07820718128524251320703400010f0410304045000c01c0300008200220380c0c1e4660202591069001c04540c41e4509171508401d071046001050781702c0d100707074140010b031588107544d1042510034650390031648138011010301c980d542400301d04881642e19038400c1865a201d407070103148959000d0f60f1008460385414405840308200d6000610400e290900700714003030340c0241200d02c2075000242c0002c0d020074440e9007141050405 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 492904505 1250 492903255 492903283
    0x1602060918010501020c10121d0102121509010b071205160807030908030a210b04090b10050d030f050901030908130e09010608150717040b042109050d0203 68
    0x28210007144108604009040c2d4000381c00300d0b801e9111500c10070881020320048040010006004061954141d821504501120483d080d0016440001050a90304104a80880203111a0800140004040381402c0300384050320404000d50600d01000745c1c601c6084806000c00014006003a1614032550490701c0e68441122004001440f900e440c0d01ca035070101001f0360000300c40000c0810307584000304c21110078180701c1e15505201820b000109500e20080504110303d203585880848481c0c80728001e802e1407620800b52200e0b28135080303607001c40204040d0412800751030400c1580c40007030f8200c2c040c003540c51880d080c129220858000100d01a15514030010200d4a000c10004800200c8084002c00d88903505071506941e03481424490803a40d0030300c03400382d2a500107000403c1c488000c00c56550421441d15200e03e044c005070b03660044101c001d460842d010030f000410003040c40380700301066100c0448001640c54154039048014980c43c0d003401907038410000b00e4040e00c21940d04005600540003a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 492905755 1250 492904505 492904519
    0x6041b0806010609170f070512070902031303020d0e0f0d0203011503150b0111030742060b16021c06090507030317090303010902130314010c020d1416020609 69
    0x540000030940c2c1c40c4e500ca15841200807032844124144042400900310b01d516004011a502d0131007005001d540380c00d0305003118043c40c040070801c41e110b40000c504c07070440c0050a101d8030a407403070020f10f0407241100d108200220718030142020f90703800c0e415400d1000e00702c07824039400c980b07400004e00400c1e510280d0308404800d41e10000c10070000385401035070001c61000c100701c0043c00400540311800c0d89170942c05580c0041003554002505031249401e500608452800113000d40001c040c0c0308500a164008541d620f034405800d1555035005840142412620840c01c1003000c1c103a8581103140716900a1144401903da024912001900d05460076049002440084d0050034103640303c600c00d02007603001441010a50001e5250303160110b01425980b001545142c1c03900c02110001e411164000c00c3d110b22405e40040400c004040104541e0700c128000039140803a41c40c045d20300200254a0403d2010492b104140c1419404c203407180c0081030300501824040c2c41c400201d0b203104075800035900840e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 492907005 1250 492905755 492905759
    0xa0323090706030f090c17150405060402030706110d27030305180108010308030a02070c0e01031a0105010f02030403080904060506030426030606090d4e0206041b080601 74
    0x400141c0e180449455480800141d080140d03901c0c251420614050250a01000104244e1244074940d503010301c0d50500b0b61f405803001c18542201d24005413000e0b14980c1c4000180001e5141c00d00c5080000c3c04e00b404d0003013030042c40020440e02d07000c08030180b40c20700803003081e0007100608000181c1d140441609a40a84070380341d14016055030050302c500701100f5158120106103501400d69181660707089090311703095a40f4005150042c1d40901021144062029400103841700f0340042940a0344c403e00500d1214951a81002e001c0d200590055040100c500f050322031881e0048102e80c2a00d400822840c6c0ea40c0036800403401801850707010b05c0d0008400010403042c0018140142f6200c20f154030300407000d09030707200000d11902050743c040d03a0061041204552902d00408901c1e280d40c4142000e000781e9040280280380146003c4000e2091010030305404115411500d0125280000d1500304c09203101c2c00000031741d05e101c020402002020403a0320541d40304100e090759401800b941049802d107607 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 492908255 1250 492907005 492907021
    0x110a06020c0102041a0c03120a0207051e0f010504080301090c02190809030d09030c121109040305040f0b03010312051624060b1c020d23180a0302030a0323 68
    0x584944a0b45100740b1305e40c8440d88401c00301d0380840d0f03410140c1200075400c011540f8507081c25100e016010700040d9038200034000000d40207002c14601d1901d5028025071084242d070540341010f1101c00d403d84c440c0d01d428200800501c07100144d80c150f9100980006d401c0b10041026032800012002c01180f65104003e40e108014851008002102c012f8056505a0a040c03405403160341d600e003c01440704540c81000d100c0811030b00205071034180189054001400c1c1d050100b5107140342580c0540006800080c2404800e400f800302500078203542c0c298034a10361650715005400b41c1d441545100700440040c015044c0100c01c40d1121640d07401103e007001494100c100c100746072409101c0490344070b050000010390194914280c0d0990b920241003041032040c0c146249009500c0758203a1009580c0c0ca0030f10003004c07135850380b039411718211111540f22142000808260315044540241e10749600000f030841c000b80e808000d41e0402070f038030304010640c042c10111044041c101101d040f0400d21150701082499 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 492909505 1250 492908255 492908257
    0x3150f1407021c050d090f021306051203040305030910030b09010e09010b01030902061b03040b300601050a0c2103020a110f2a0301140103050c1801030201110a06020c0102 75
    0x1c0703106400b11026440030300d840c5081e00d902501c1000114006100b0f60918880603084a51024070403c5001718085240e03000035042644860700d0f869190360764000340700c01c2c10301588402c10315804d01c0086041900d10703030383c0c5ca60fa0711451070000c1c0102213034144020501c6c040d4124400c4403c0c0240100001d603120005400c07206011a901c080c80e40c202000c80d00740394040d202e078005094003c2c00312480c295450140350414540700c211030903548810080001d9044452024102d00e040b6005640d084900b80c000c4d00f61a1500e80c1812440070790000e05001ca00c1c1e81000884140900608140381d24a8250034000b10b00b08080c400810141e580410365441c8a038160300820003080c0e42d8440b0b501b010307080d41907141c1e1011800d110200ca0b03800285001011102c03645c034400c48424480440905010007400319082d85e83c60164900541c2c87d240043c02000014030081c0541c0c00c05440000511105201c08000d90a041c400a810f021010b8240c00301d100045c807140030201c0c1c00c10780541d51070101032022030007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 492910755 1250 492909505 492909511
    0x708070e1005180105040207030905041a090f10050d08040519150f05180d1403040f06080906010608070e09040c15080405031209070305150f090a02090103150f14 71
    0x160041c1c0d10204240c640060100c240c2e0a42181c03144090303091405000080d84204026000d001000c000020701e5a202c2c0a194020580b8020f1010204034007400d000b002d14014090b01c0e0303104980010020100002c0c07101c02c0885500321806280f184082c10204854400c6401c11a000900f04188101030043d070310110f4101e4121400c9145a0941000110343c1d5100c641c9005000030b800700441d60103150300c040ca007555404001c11a07403190b540c0380d076102c6035500c51501c034071010740000c50108040451001c07260001e02c42410204010701c1e003100c0164aa2105000b0703035041c03100820125011910490200c64140006009040941003604200e050301b2507500c01c4404221103000700500291144050900503030380003008500b031040c1100b02c1044904010503012040c800c030b15000000c02c20411290802065682a010f080c1c00c000c90b01c190000801410011141d1014000000603140c40400604503034011140c04110800001c40d02c01402510000c0e44030981400c0321542000a45d14032180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 492912005 1250 492910755 492910771
    0x40902130e0f0f0402060307020f0f10060609060c1e08030406090501050a0b06120408160c0806010f0312030902041506021c0807020a030c02180106020307020310060f0b0c0708070e 79
    0x569982d07101006407465400b119040031441c0c40e0b4010900508000c4003441c1c101c8441d005454206034003407038031072400c610444804095070050800001065461050f1400751115280c04400075040000203030031404040b1009100c031110700340c29141e42c0b01114121081c00e9024019650300e00742420190003a21500c6070070355003540781102181d4244010311400c580c441c0d010b042213003004041b08148a4403d03005009850202c0108202421303141c0200c160300c0c2441c03094081442aa06100754589801016048407118005282040c808524405e1a0f40740040052030081803003140c901c04a4040c14883c030102041101000700803d0090f000305615240e01a0040c00c2155004032041c101d40c0c88c20305460b203001603080803000d800402d01c910241d008050014000440c07041e504401c200000c6006d90186005030000f0610718110b24060101c0ea81c40031040801b030000d10300f401c00c0d03989c5144041c81040b41d812000200280304840c2400b01c00014840042610f00b0b803507580701c0c501c64561007210303104 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 492913255 1250 492912005 492912029
    0x24030c020105151c02040e0a05070503071a094209060a0f031503030801080f070602101517010510091b031802040e0d0f090e04061104090213 62
    0x200a944144541842111030290425415080c0b4007400740031401007003480448405801a82c000d610389014080c400c030381e1038000b010a00c5250038001d04201c4507402051003070700705400401031040e00f0300914107540100c401007a82d031348803400010440e01036100700b5144440511070303480e201444540125401406200070707400c1c0040b81600d0f03c02d00e1059030603c550000c420302c10080c49a11803407440d0681049400c000901d10320214140b4040c04c1d056008400041c158070041c041c4110500c402420540d028004041d00760500c080a511541c0e220a0001c4066585180c018004640c070890002020540e060154100c140d04a6034064041143c446034a803408502c0001c80c60714a02c107100a50a0311803000090103104542100685040e40c048a0400080410030001d46c3e03035442850303d040951001410311b4035483c040544110700e5a03040030140240d00300104014507105c2e0361a03602030f170f021000007804410155a00d1a600440e000302c028070740301087d40c1042140c0040d0340700c00c0e204144000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 492914505 1250 492913255 492913271
    0x90c080102031801290a0f091a120d030b0609040906020c0c030304060516020609040e10240312030905030d05010302181e0c040b0a05180103090f0308040c2403 70
    0x800c4c261800b0100c100d14040c01520981090079409034040c2120800030000d124080e41c80d04400e86a0b521504806c0310951354010003160070441e80400d80d42600140d0ba00e2444550000850b034880c0d40c100480002e0640f202000540d0340d80701800c544126800a05c00c0000088a041901c000c4d08407080010b130902c9040b124070802e18000007510210380907035480d2403900b03407100303240c041d00e800720101243c001a0601000046982e14024161220700b504010b00300d440c22608000b0988240355180c884244840188480344081694000140c0b0380120504540a6102100710b0060000c0b5001502a0001050303c00c40907405401250480340221403c40e1801c1c001d40449150b075400b9203046505240c1c000c1d44201c0388415842071a4401c9484101505055a8807101c111990100c4100710009100283c820601d01b00307804070300481c00003881e00300514407403642c03100b418050800340a02441034941c0001c00308020100100003401d16000c80c108400030210390039001c410325050341400320b4104080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 492915755 1250 492914505 492914551
    0x3b0d08010e090f0604032d03020a12021905031504050412020601091b030902031e010b0117060d0b130f030e131a2701030c03020307060203040302030c13090c08010203 73
    0x43d05400b425a24041c1545448075a402c0e5071381d03521001d80900101c00440c10042c984030210301d20025280c44d45025980d544207110051040040f4030a0020f1b941c414810320f203042c041d0080d500014540d40c02c14580e42d0b02c40f544c3c11321040780600641075005042c4400c000800c400050084903902e0136800301c4880e031340c903203144405035103c22211022642000b600101c0da640300b50450345490340040d003038500c1000b04450f404459840605115416911040b040041d568410039420040d4200d51b011411810504001103800c00c1d8000060280c1c002000414941c0c04c0200d0784041c0294804a5004181400d290140203c43d010300310130f1003034500b0030300b28110342024000d00130030360100e01c01640320321044000c104201c03c10590b0354092400450301243d64880014095010354021080c8614907480c0d03104040c501002500104c045400520003040140c80004041202c40c508640d110b51075081c04011074000e016601025101c00e000c4100041c80c1c02043d8000c500604902c00c00d0400d212003184 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 492917005 1250 492915755 492915763
    0x1240f120f051f09050606192d0f0201021602240403030c060e0a05070e0a020720031e121810080406180201020a020603070201180c0e0a3b0d08010e09 66
    0x1880f64000100300141c16510b0300c490203042078108c0900700315103075800d4003407210041d140c0395a03946000d20300842d11651b0307141c00100802c0d0740c944031b01c000c0d4a480c54050690103240350516000703000d07012502c0c403d954100d40032060f2a202585800c20f0351180d50344d0074010720300007429900b075401a140c803a0001c0308a50102d03140751800c0d0044001c2c0b50013440d01115400500c1d0080c4907145150b400d205982c000386080d48210700741d00011290308070b00161b0f80b08242c100034003180403401f100380340010008911004254210704940301c4816546400030003611030f42c0341000013941540b2074000074107003400f1500b19101d03e0095000e20700400032120740540b24614021558030107405031380f024040c2001440e00b48021940f120b4144004030784032005449140115002c081c2c12512041800b41c1441812618042550f03c0301010700240a01c060142007101c034154210607441207109820900401e595145005aa2148081c42111545090100000c280d401d0038040d8071018500c401c0840c2104000203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 492918255 1250 492917005 492917011
    0xe0d051c090806070c050f031813051014041508010510050909190807050613030f02010510030f02150a050408061303050f030a0615030501240f120f051f0905 69
    0xc001000542c892840942c2d00c0e44120030211480d110b087c10441c0381907400d00240a4038450b40900340c01c07a100080030004d00300d0364010068490b074640782c00c0009440b41501c0b0003040303800346400928100f0341d0b00041406045000c3c2e90384155200c82c078001454400544c03003940302c1c02414406403100b03520307502005005041030320181840d030b100403040b000035514039a610121900c180d481520b0204550740781800c2c10400c40b4800c40c2201d400c6681000e1580160890b002e1000c01d01c003c11203454502514507000c00340f80006000001819122011500c0c0c15060844128451913255110504410010720b0b0358014010601c29025901c0803031000d00c0a480b8481050750b064031100d05000c1c03211140301c0940c10040040e048140c9a003000101d284d01e04a8542074031542d0390780811158140611f0300910841010306291014005020090b1554000094440f070301c01403403c10551010842100003414003c00046422440d100620191003c0100c1c4114a4040d0007191210309644180c1c6000700e500031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 492919505 1250 492918255 492918269
    0x312070e030706120b22050103031d03190201020f010f200c070308072d0b07020c0a15170907030302060c0f030610030906050f060f030304060903060506010e0d051c09 73
    0x2c4940c02c0e40082203402c0000d00250285c580c45501049003860961002c206c0c0c516050290ba440051041c1944242c0d00c46005810100c2d00c00c107003080001003580d40d4500c0403064401100c040072a41168400d02a04c10380344480340c024410103080703c031642d000b800510200c2c0c0b40f04141395074081c0d1000c040710a031052007404c44040c0403418510b8540300d10360b03413002008440c1206804c110009400c24030030355000201994800001c180c00c140382c803800b181e40107410101558003010010101e9914000709000303071800754942035000768000b542692018a802201342407000c02408220269500090410881e80643d0889155071a9015514001d10600c0384070040f0740000c00000d80141410301e403504242c0240d02c0c1c001040d40f4562241400c654095030070b490b07040c0d40038007840014502074140150341c820440113540b40c01e14040c40070b440f08041e484001d042030380310400503185a0141604012055014140b8402004140390664494040d800c0d05811191215108000c0034420745003a01074070b001d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 492920755 1250 492919505 492919517
    0x60509070c030e1918050a060509130f050705150910080106020304120312020a0e0907030b132309060a0f0b01090b03130206130801050f04020102210403050312070e030706 75
    0x1591080c094a04550844540d48201e0130070001480381c007803041120302105282d400107080c1400071140e801e640c10342d44a103100300020000c0c8140b0446000d43c2d802c202da44400702d00d0702c555a515100c0c3c20600241c0c0413541c4442d03001c0c2c04400890b1420002c00c05060304441d001c02e2100381c0c1d02c003951366080a000320001644240410300c52402816002e04959010f030804444c0500290340d40c4042e030348040f0b844400903c001003007507442d085c950103041d0400001d00f4107028502c404c80104145c40d4480b00705546064554035615089400511f81c86103011884002101c54903020030305595030302c03054800302c90b024585001e00b18441541d10810f4005a4140c1d02d82e40940d1420020305243e80000d0311010f80c0d142482404001640d60100030804c80e20903645c000c1d1140e03d08940c55084880003030180d40d844104030304000045c0c0c0e003c100300004c42e004c0100d0f0310072007400c0311509549000e183c00042c4035100000e02804400c00b00307000e25100d9505a5205180301480d4001d054503030400744076040110300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 492922005 1250 492920755 492920777
    0x9030a020c0904060f1506170919170c031b15040311010b030f011509090b0604020a0203041802090405130308010e06040908040e090c01140706021c02030a060509070c03 74
    0x601106040c0d0024041d80021451800c01d211a00031152030340c00d8201c0c07160003802d0070052280c1003400d504000591241043d003902e0030b5580c0b0352b1606030402443c02142032204140b0204050840040030700f501c60341e681a11191816001c91740c0e030b8401d01090400107400408103800800008101c2141c000000d800c82160f1900d90b030640308074075085041c1c0029503c0c0c821101c500c0c2c50411100621039038000001c11050500062804410040d41040b40024105064200884c20f20b540d030741e0b0050300c161001a621300543ca8101c1c00d41c043d50300182c4114034090341180c00d090054028118a80c2c2c103c40800254a4011310751880c200c80c04002004200303181e0041000001c20f8100b640d03c100043c0c408038807040b480d81c2d407116582c0580c100c542050741d10010b000d00b42c0820001d00700200c0c4203003001c50800080b4983e18840e030048820003460103800007942c2c03c0c0801c0c1c402c19045401e4004d0710554480c100303600780201802d44c502595008140d1507001a4031580b0500300a868290140c8507584410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 492923255 1250 492922005 492922009
    0x1a0106020c06071104090c0f060212040b0d021e0c0706030e0a060e070810091202160b0903010204030b04050a050607030c0906080c09030703030206090d0512150411030709080609030a020c 82
    0x500f0107403050300d100410354441c0d6950303212401100002807041955040b11810030211b16104411030f00120115440050208a811403082c203c2c0c081d203079031460f00c549034181012400301a00c5003201c008401801b0819444581d13203840044d20400081c24152460947c40c0e035011070840b00344110181d0b0344d5000a08074800300302a03611001000700c0d240c0540365802e0308c582804c2d01c1c00c0000e0070041d00980ea00c0c8214024040c0705000d54030440d440784060032001d01e6844d268040702d550b5001b101841c10380090030201c1c07942c003541103c0003158028000382c003514044c01d016884118142040d2070b00d028010001d03201c203209104032001c0001c180c941c444e551341414411900e000d00202407c01c0510b04124507003841c0d90401082008500c65030040400b45400501e4500302000e4404800600405010340a1214204815a640241d0410900420425810005000e411040c0c108035060400000344281e130741d80604180140d07546103086910b50b4441034003130b59881c4142c0d102c5000581000c0284602e038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 492924505 1250 492923255 492923257
    0x7030c0b0604060801020412050c030f030f0a170c04090c0e0901150c14061e0609010b0c0109150e25141305010f170a03020d0807091a04031a0106020c06 67
    0x500d010707100148450f00d4051203401c80c0c7c4244c100440390b041001d803507010014100030b140f03c5144154041d1250307200c0700107444e90b80e001f4121005d0070544040b80e0000341c14070440c07601141102241d00e4100c1c90901d4242d150255105000e61884141001400b002d55030140f00b03800b10b0401d028040e0a2568a000c04000401030081c1058007005070b031150980102d003070b10040c2c40d42c0041c0a0302a002900340019010b25000c0c0201280994204100411601e6501c00c1402c030f0459030140b03099691003002e051030705d004080c0a0001800024201e003a450b18510303035800444080e032104101e030002303030a5900024840c0102c042d0008141e40500d003c2c4150b0382e0f0811803841e446805400b00e10760310b800b4484401a10026048641c4801145a0801951413443e0340710b00355442003c09400c01c1c0c003403920000d4584603490401802d218070400400c0c401841001d00750002d01c001030007644018422100356040c1d40c4984800d860711070448001031201c031503220600d4100c8003036400402e0720b103603000188602c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 492925755 1250 492924505 492924511
    0x10915110a0602030108010b120a30020f1605030a02060901021501030b0603190803060f030c0d030302030a0507142227050718050f0303070804080d1407030c0b 70
    0x30003103410601a10410100312816a5510072400503031258100881c031403c503001056072034422599604071002604021821a101580280f0100d0001042d030315401f5a6100341c24064801c4220745038040d04040c0d0124407465524044401d90b40311a800c6150f20007001d140c0d0041c1640b42d08040100c4c17005241100c0180718140060040e501d03028402c81c071481ea440d200b6401a9401000300040048500c1c051103041c2c0010129102400c400d001902ca00b0b00901005120703901440b822040984a55010030051882c0003000340b50100803a00ca01d00200039400555814610b86d05041c0442e00390750240032005080459081070134186500c50307892410351590841b80c010300100440d408500a9030568a4403a0200c0d407403c860403040110140ea0200c41008103540f04000c11003010000c1d9012410420040300c0c000c07503041003150641c41c0002d00303502c11214001c10850707000800003000303030004c01c0c070041010164440d044004003d03051400a40316090009002414030749940000901038024650 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 492927005 1250 492925755 492925757
    0x14030d051305030604080a030c080c0f03060a0e0c0d05160f1206051005030405060609160e12010c02250f06030504080705060403051806040e0a09081210050405090309010915 76
    0x2070265500e5001c070341002001c1d84c0030340784004001546100f4a405000d40510f1110520388882685031030414207001e030140317816004031075200002007140e60780c1d904c00c084060310b15042908501c1c101001180340541c0301c401076080c40b504050028049003030a45041d5030480654480d110750300c40022040312030000701400d200c24540e441401044a8031001101ea180b2003240c5c60b4999a4140760408500d0118002d10581c420700400080080c01107e08030451010b2005082008040c860301300041c9031070481900c008419880c120b000f01e4501d900003100545607510f000e0345194518240302d2614041d100c1d0140d40380040000302e003040301d18800c1d48004d034064007500070141440c2950b40c0300c50030100256000e40000c0d00119058540782ca18504035510014100e6485240c249003400080c60400c00510001007503540e0007074141403060b40c104950500300b21480f619070341e10f4151204240000a402040c8c0560f2500001032503800001007101c2c10404141c40e2004060b00d0404030806070040724003040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 492928255 1250 492927005 492927037
    0x2030c1210030f05010515060c100e010f110301060915020703020d0f020d03020c0a091a06090105070807060e0123040f1b0924231c0b0402010914030d05 67
    0x80030450f1031410180c01c2d44079200110301804c09004044050007141c01031031003a0400c10680c041000c1c001402080e14000003004078585880444e2140109071408006115504041e0300204002d02c140096042e034140342c60310100d41d500c800c0c000201c500705401000151348a081c00f0f00c0075150400c0c0701c2c854203208100903d100e0446038007050f50030080401c00c07005680894003102003403074100d0600c0b0180040401c2000403101c07601403581c0425040d006540652800208256680d01c140201c0b8900784d0080c6513107039500860b252030001000d02d88030380c500551a0180070407494410b9006146103410309299003105072100d884100a156058108891010108071000300381000507602000400060800040c00718403255246201c0ca605490006890304551007400f00c650000400a58600750300c002c2c00d600310525021500d1620100d40c228201c2082e1070140f010040d030a402e05215501c01e130b071900300c0e80307070340d502e044c3c0d444251078403407941c550400ea94100119100c0c4000d0036400c40b030318030b000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 492929505 1250 492928255 492928259
    0x140114040b1002060609070807051806090d0804060306050a1401050315030f0703020307080a051c030b0402040e0601031a010e0f010504050a0305070608070801080a0807050f120d0f02030c1210 84
    0x7804101486118005608400201720440c039100c411260b10846500b0001403a2500d1540181284641445413418400040c01800c07181c988c03600b030343d080c4100501314203100c84180c03d001d0900d0f00907114a2000074104007000c1241e0030f010102c8000c6412000c1d4401d2240c101d0740c010b5410741c20040c100b014400d40340e030f800c0c0c00c10395040080c4158207801201a11300e01d81580103160404403660066409507100396281c0b4001140002ca2541040404801c2440340b0801e0780202d01410064071041c0d0301a00104000c24aa812107217601e0041409880800c18000075501980705030044482207404100001207100280c1011500b1480b0144145400c034a090745440014480121581058400303502104080c4110b80e0072000031600080141071000f050b45c54805283d9950f240808014107040004c22504100b007801c1204440c113182d404181c03070141c42120040070003604510341440400d81044501403461003944200c070b010707103620284549000703100020b6980b1041d01070100204e0051403280 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 492930755 1250 492929505 492929509
    0xc050711040b090a0f0c03090809040914011e0614090c0a0c0c0914100806190e010c1d0f010509040e0a02090405100f1b030903050f0708040513140114040b 68
    0x8620130443c00707400003280035091110b18211014802d40e0000d251030311070f4180c003241002c01039600f044400c84001c00d0744a204e280c004452009948200d20b04d60074203070b00c0040c40d4030384410503004182e0141d0804c0120369902c00203241c01c240c407440c15002605100440c01204990005003e0340d10300742080b8000b10320b159215603041145a008010f0155204503468a000c81394000c00d030804403204a002c0802c0c10301000a8503a1005084400110031100000b814202c40e60418890482420000c22110b150003502921841e007590300005400030f0392604008c00d29145101c50b1a4a07410303582c050600702c0300000c0c4002441d03400002c000900c201c403441c01c0140d48111405200714465400b1b00500002049110152912016649682424240b5441c903408409601d401804140d140200343c40e0032504068a203480303600038200360102c0c00100042030000d0300c0011b100b2900240c1700d0b0b2403c540c000b40082d0880709141041a1485500c800401510146050790130003038000a10000d500c401c8100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 492932005 1250 492930755 492930769
    0x6060a230604170a02090609090312060d0f060b01020601060302040f0b0c0f01050408070339140d090503070b0406050a120b06070b01090f091e06060510050c100c050711040b 76
    0x4110f1481e9104800400850034020400b60300446c05541e14040d5060600c2e080c0c1d224005c030032814000c1c0a41400194141e41c1e805402c0541c150815080740c1800050705040e0f0160009240ca980907105200002074824805c0c401c45048401c0507681c80315150401168000c10741c4141c041071818410780002502c03c4c41c00703204d0140200d00c202c03080f44d9140591701e0060103035074070140c1c03051240c100100c0f6004552880d400b26541410783c2c07098203460158500e070261000c251820b1601c541e00c50709400d1042c090b000381c6004281e5808900300c482c000d0382c4002d4500144980d0081f0307000074105200b0502c60500416000d001c00418801c045101d051010100399190481d01003696445040401040040b0142c401da600700b0020302d40a05c0303010783e82c2d01c60f081c01d0350078035000c25240801445902c0030b2060f1035002c030010f000020542c001d969119803004125412501c220340b014024219200030090142c4103102c101c034802e8a42074105075041e140c0584c1c01011602880d000354413031852100c40d5595803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 492933255 1250 492932005 492932039
    0x70c0603020405090702070e13031b060e0f0a1101050c0f011e14041709030f010204150315140105031b0a020a151116030905030a0b060306060a230604 66
    0x1a80050b1114609410403058000240400080d900220000e04c4100842c41455078000c88480114030074440d50710f001c403080c810440c04074024106400c485020030060340c100300880c80c000f400711590f9000c801505500d0307041c240c00040c0003055644503c03d542d4010070107403803841c0c03800090352052070303014035801c1c00e55508100140d412800c0c01c004071300b091294403a8016074449a0120882da20701540c60515202c0040b002106001020070f81c9070003036400700031000c2c1c8200128025516141e6910300a401b001d420101c1102003420320355110f05910b2004110300c2150040303080381402c7c1c0b2000e8010b4407030b5071002d4101c00c0700c21410185441c0042440303009100c0420700b680140201103550030079130b0001d2841301d854102c3c5410201c003000000566400d5411072000c608031840700c00300038034040d10f20711a07517408a82c242c0542441e54080c4000f81c14140d100c0c510aa00b5030b0784554441003001845406401500408200c9246440701ca40c1e84042150f2041e41c080c0146180c07540b0745d030403111100056 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 492934505 1250 492933255 492933257
    0x6010e090f16030218130e0708070f270e010b04050106020f060a020c1b06070c0e10050312250507090f1d030703080c300f060906040b010203070c06 65
    0x540900c540041c1080c0d000310030302d86500e000c50620700410f90f000c450884410850707104855980b13480c01801c1c0603034001c111007030702642200e240d02e50341c007101c0d5281c17100b6128149036103c0843c00062040303010f00b020140c601005c0f1101446110b102c680000600035100325a030559039603400382c4a10b0711a4810f090103446190000c1c05d442c00861142ca241c50030007030070341f50002d005003c0300d01c0c1024002001d0700749601c0c45640c10f032080d81355808507016026008000d0301072011003600003607185403404454000c0f504541000c00c0f0703d071902c090554680c0001c02d10b1b20f1844c01006104480713140180d00c0d8145102900b0100070b212581d840d924641496600001c42c1281e0b511003041c40c4507900c0c0b02d004e80075107441504584582d4011f81c05901d0340907559025040c0714090001404da0103040c8112072000360071100d070b040c65013200026000201900c81d40651042c02040c0800c840c4540442c03030030310809000f00405640c1d075800c01403101402e4a42105415440305000d01c10009041c094030300050951 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 492935755 1250 492934505 492934531
    0x207060204090c09062f15041221020903030d060303020c03100b030c0402130b030a020a1710090c030207020315090d0503070903030509150c061009061d06010e09 71
    0x1000031100840d11401d1800041c07144920b0704000c895040b444c0000b146000003495206001c005000c2c0468151000c40b488035402440301c7d00c007003070a521880c0780c0654018022100c00ba038800c00c09848803803c403100c400207070000f2a00b0240c00182038004202d4940b015060301c1c10912540e00748420b44541c2c0d04107c01503004415229414203007040240172402c11040c091084041e03042c0441e40740e419405000340284c2c0c00107641d64050140520480043c070882d03e0302540c134504001c28000070740020300305000190341c10750030078920711111000c1d42c001c0783d1301c6019001440c0b42c089031000501c24100c142051603000c2c44900003682d010702461520311480940c000a40c9071803d105400d001e0030196043c00c2c01000d0042c040070300d600410362030035642c0c941000c5680e815040001a00c0c641080c0103007c440b400024a100c80f650045070407405194944000d1a07c561a0f115040540c3c4190127090b020f42c031030108ea10f851a408040054201506041100b00c402c40ca40101d00c0c04034041320380c040304000e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 492937005 1250 492935755 492935759
    0x140102070506040209060406050604030213140103030c05060a0c021009030915080a05220303150b0a0309030207060302030c0f031b0f190806370807061e0c020d03090305010207060204 80
    0x2400d100c50341c6d2200003160100141c42c02c04000441038084e42c00043d00802e0340d605100d5040c8a1944125a003c4210b94000010340c1c4d0303490001c1040a902a088800780035070130119526400030b001c0e10145c4441900940300d95110340950300d00a00c194032080c0c0801040610000b050380040c0440c810200c3e950b40c8081a600c0c2020200c02515009865407260348031098641501c010010017100003a03626107004604880300d81030741ca486403060703000b100013000009815900b86405901041c1e90a111740c003900c2c15140c0d211425412070008590819210608018042c4440b400c1d5008543c82f1b0380500144c4166402815814443d0708040791078502c49000055402524a084014a29170000c4d80307054110ba240c10400300b040500304040c01c0c49550182000c0307406071220400f402c0580b6003120f0a4518070350303403124955916111231140c0000320700486410552a4814440141007002940341c05d10040035560074004400c0580406030100809e6a00101c0050000e00003013006038050f00c009603c40b4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 492938255 1250 492937005 492937009
    0x13050a020903070b0a0804020637020c121903110a060204061101021309090f12050a030b06070203060f060114130302010912111c1415060108040b0f041401020705060402 74
    0x1054000c4c101d82202449510605548400d0705544507078181d41175074441c01c0c101c0031648854201c3c081c0480e500c118680e900726520001c200d82d400c0c150703d43e08448a041c1420144074200201c0314414031a80c112032082030003540c0040351201e0640c4203252241c01c0248050000d4200101c0e400e003160742a40008080040c01d0788a00b1180708200044001c51505581041e124504403503442400c48480c8c0f5000c00c0301c00d100c1e01a206036035254100c49070740e82410340c407440100242e0000c0310080c0840d10300361030185c03182054019902202d9024000300f00c281c40315441a004000014615410002d200c00340807802c08150010b401526440903400b01014298800581124045d402459005905039220400308013200403121036080281e40da0704241c04841075070201c0c8400c0b4400034007584442d0300840c003030040006094903010105104843d00381c551500440300318400381c80281282da0404081883c051000c18101c1d005480349100d02008108410300d84d007a82c001c107000f42c4881e08030100700021342c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 492939505 1250 492938255 492938263
    0x50c0325030305010e07051e04080d0e0a090c02032205030d02100b0d0809010c0602250b010803120403032f0c0705030705060a0c060212091c03020a08010501080613050a020903 77
    0x2412000701c080d241172811210040c07560182c040800c040c40c445c01d072302d200c40c00030340c00c2210090050309003030305c111820045000d402c0c1c000c0000010701442042c0f40c0040c4c11001031040d443c46035000d40c0035503e41200402120501403400c280300c0354468041000180c0341d5405c102041d018007440c3c02400100c40003810410464260082150082c0e9003048000c000400390000c480204e0303001d080a052208942c10300d84020f008114102a0058607080c84c50142c00c090541021803030300c504844240c580c1c0765400a520307030092400f0303410190603403c0406c001900a8104240c0c0c6101000401c042c00102a002d012043c05014104d1078150000341c1c1e498a9901845200c02411081d001022841c0c03401010076128810440d510042090409404042003055012034030a0790740041c00300002d05003540d46ea900c2c6d0100380c40d0700c01c0c01c4032030700400203150f80030b4020343d8000d12840d19482c0f110381c6000b0064070541c1c00140321607400342c0b5940402840c05007500c90f150281402100041c1c5503a50902070500e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 492940755 1250 492939505 492939509
    0x2a011d1b0901030c060c1103060a060306050603150c0309030c100e01140118020c07121220060402040b0112050f07021015051203040f0e220b07050c032503030501 71
    0x600c1e0704401800490482c1d0380315002c64650b07240a80c0491450700f01252039002106d00b140e854082c903030a001c03114585810100c192802900c08002c0c40c0c0300c60041580d03d03e540381301c0014007a4190700040c003006c01d20001c0c6500c120442c00380d0389800c1491907910308203904803845c0c3c1c86141d558040e500100f00c09221b9440c543c01400c000c44040c0d41046802c2200d601c40302c1e401c4810075000503030300261000602113040140740100c07400024030020f01c1e15400065090440000144034a40c074040b140c00d100c1095068070307400714080d00070760311070342c0910010700f4076061940d06000c1844110001904103120380780c805c51450a41005500340800300a041c4403051401055442c2072004550a6115001c000c0e0100c5204070303000e001d25144c0d10070302402d42c0506e9001103078003c1203040c00a000c4448403045032040c42d00303101408400c1c4032142c40c0b441d840f80ca004d0190114080c00d00242d211806040205a81ca0f80d450071241401c00781000390061403420030403a102420311589034401c05415001c0d00740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 492942005 1250 492940755 492940759
    0x9091109090a020f040b150a0f020703420b010905011d09041a0109020c0c01030c020c04090303110708040806090109030813020a091a10052a011d1b 65
    0x1400e0a003030781000c0e610912088043c0c42030009001c8221280d40c1d661012a001c2c00c00b5003100300e241c1681e802203199800141601000c50313894034206070028404101d40055941c401c10340c61034030140041150039118034211042c00b00c4003400307210f980c000160302e0303101220304000c0000c0741d003a1111000501010786544010305100442d84400705100f8042030100542030140d42c02c04055132142481c021088a01c10f43d11070203a402c130004601c0306580d4004011150348141141c2540031003200460480d0444032205e40103820400c11000d29150682200c41181e00034907001c10010300030812000303035500064040b00d0040c0001800c00c000341003440710950202c0e4a0000f003203040d50549002d440418028020f101043c0c00d90210821907607000f00520103001303246020042440c104c5101004640180420752041180d00310f444903c602c20412101c1140c4c02d081003103030700411401545407203089400d1002442d52500001060721400022203500f03402c207407000b03140c64110310750312150408103a07140c68 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 492943255 1250 492942005 492942019
    0x40e0d081905070c0b1e042f0d081e0f03010806010506030c0d051302040204090e280308041b1202010e030703050c12030405041112010b07170903010e0d05030717100303110a05010501090911 83
    0x4190b99181610280f490304040a02da45581322142d091080c10300c0a0002f1807104042420881005e802020314107031000300c012110280d88a8080000e43d0004552903800030608100380414120950030040e005407650300310712078075605940081c0030390300b040d04251003140d40e4001c4803900100030800020201411074000d42c90003482d481c041046103500c540034080c817240c6000709081010b407200400c02800e40b8604c68416580b10502490350030200c007001e0740003880c46561450300785004101c0314204c0e540a002400540c4005050240c0c41c034442280c04150301052000080350780b60303805190301d1103d000d10301c10b40d60b841c482c80001103110103810140c04c91000f40104800500700c5141c11002d0001100c106032079030f01070b5001a001d0040c0d50144200d500948820071040d42c0c0000c00345006a2242d1600781045120b0b504401c24820112407800b01480794120400100b0301507000c2c0540380c50000c00b030362075000c40f41d02c480e82503075002c1c0d102c0c419907583e0310301003818041076842c4a02c0d0040111111 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 492944505 1250 492943255 492943343
    0x1b060903020a090b010918060609060201021204060515060309030a200a111203070c05040b03210c012d1d1b040e0d081905070c0b1e04 59
    0x70a00e02042ca0082d82d000740c2d956081205641c0c016032040300285107140c10342084988140e000d4010b051f0710301c03030500403456145002c14030700c1c0180251542c80d0755440e4416116622500c407003029200241400102200030080000151aa000110f01c90304031a4019a41e03400400e10040100d071552404c0c503041c40e0748408500c2c5103500810016411078001c4204000d00c103003403000a003c072039420300e41003561100003003d0301040058001002111003c48081040c50f050b00141501d507182d9203540c0a0740ba00c14039400d401411a0406071580012260001802d120118814807048803280b0140f01c0c1403150000c0401c10351ba140c020b1ba104903801c0340120b008603c90f5114141d49001c10000c085d92402c440880300c01944407680903122030142d0008845a00d05800b1014083c072200780c500014401800b628817100e8802405001d008050725500c1c6014003480f601e84103d040005410903c0a060b900d24041060741d10a03170613801940204608411104030054080140c1d03d07440f1728903040ca48420103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 492945755 1250 492944505 492944509
    0x1b06090812130b041205010c110c0603090a0507260714090601021203130c0e040302060408160c0e19060b1902010605040c0c050f060c1602030f06041b06090302 70
    0xe000c01000100710003684516025034460701c0c0d500180c220610100b0041030000724914540e4102d400c05000380001c201268600500301d03406801900e07110f2540d0702c085406001ca040c800c00071071703000000720192500c500c0e9a556040c14403070160301045181c580ca1aa9100c8048004102e481045001c401021302ca450001103490811415810b0352141080d1000540203074024172010310180103620320a603403454682c140103040c1c804000309940c1c01c04002800300780c402c142c084042c000e0b90907400030b04450791036070345201d1581d004510000c00f2815403c441000160507030911005003403070940c40243d0345410b10000074003a003071052043c45c25040440400420081f00200d4501c80011400c000b01d511000074240e02516280c0c2c000d6800030718040240c1015503000800b501444d00ca14140e032080d4486020003641d80d0010380750402807400410004502501031001409000d1000e000d1360401c0790320050050801d00201e0701983c114003c44d0045802e01d80f021071002c05002d031030400070141342c25600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 492947005 1250 492945755 492945763
    0x1c06081209030c010309080c010903121112060402031f090c0e030c010e10030608150601090b12060f2707020c040c050318031204120216060815120a1b060908 69
    0x10144e040c03695503000c200500042800b2a1003800c2508000e02034241c5901d801803007001c00d10102c140b95494500d0546d444042c0004440c0404ca10100c0210a40c030340c00204402580058807420f1940400d0310300301e21101120010310010f2040000002c0e0255802c0c2c005000c0941e400f40c1d4601c660800d24024185a8000c0303110790403a80107641d4091900e40c02c06040d8000c0101342c0018036203108081c0a1003141118010700c5118040a03655006141d0307441358098402c3c050f0b08103101c400620100007480d1402c0511802c21490070003401c04040b04144883d200e81c5400301d0300031f6004203100b4020400d00d5901041425840601a9170810081000110060080c0000340100380c2032a40c00072280c20111080046ea8040c086004506513a0700b403070300c0c0039483c00904d41e80100140c0680841500a0f07080000300004461054440485544e80d11151130600b80000d00b480d80e1000e000b008d82030b810041009002c01c058807400d00d0400c0820365041d112185442030780700d881000b0550009004441000c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 492948255 1250 492947005 492947023
    0x102120310241205165408031e04030602030c07110907020304030b060406051909060602211606060906030b010b090127080a060501060e0f0a0b090103021c0608120903 73
    0x4603240c0c007008940b191500d2401028004420300a9070040c2c84055010983e4070b81401e4103042c00c145500c6c411215070000682d2540c801c49100d50818090b5a400c9480103128004464101e25014503203030b2a5600d0304202d0f04103550740700c50880017041100030421400d1110301e1220048404000618205c00c000323507039100c0c9000007404110b2000c0031070301c1d5849640002c000703004010300c00707004000300c0b04180c0c002d1804c0f07200d101c4d01c2c1c40c01c00800040c81d43c00801c83c0038400306c0f4641182201c800c070250f030200b00e5000c2a508403844100e2142c2d00c01080301032003507401810318000041031300d500c4c50500c0e1007102c006801c41400d0fa04100f005000300d81c0c00a075071145402007000a80c185003803030032840e03813110101e5100302418004d44141400700840c035408641626500d881c1c0d55005400340c1d0521080300301100c4140d030080352100d018081c140c9903001402890344145009494850b01c0c4c1400c800307146c1003c409201e00303030300d0b40030911240c1c40900a98290001c00142c49082524042c0020741d11640380d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 492949505 1250 492948255 492948257
    0x206070201110418060b0c06040203061008120a05070b010f09060603020c2e111c0c021f0b0307030609060b090f0c0a0c0204020a0804050f0c010212031024120516 71
    0x18000403115400c4d15004800106002100d403500c6a14501a0a4036540c1c1100c04034440c1c0161000511400880c070107280079141510024100d440700c54611a580c3d034000d8882200f4040b080c04140002048041c3e03d6003e8420407503034585081c90500308106548a94000360107042c01813140b510700710300c006659280012202c14481d045a4076500300b644042c40240840b04842c2400030501c0d0150030b40c00140400c040d05094a400071140780440400c582d8030700121401600701c50341815181d6140f0b806280f00313010100000030118002e2000030b00d00f001d590309c00c0f28025100c401c41424000d562023014914030b01610303045420b103080000312504007402859154001e00100b010b0030f0311446924042c50003a03000d0011556030004800240c1010012103045a80784a81840480091004540b4240311181a0024a85801408070508190300300401742401c10244c0040000d1081e04011400c10a00d550032404144901c101c0d0010901d03a420b60a4036412401c16003404003504150140300d42001036 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 492950755 1250 492949505 492949529
    0xb01020d0c03020c150f031003020a09060b0909190608060402180115030f15090905072903180a03050414010305040c03060504050a060e03091314071407020a030b060102060702011104 80
    0x40411701120501580d42d12020180c4c000c000c0041d11865003656505403402102c0d0845642c2c0c2e56403011382900c03c10b0040c2c0c0c2c9414000c2c40b442d803da040480c29070b50070800c0300e0000c5201c2d0343d940381108201e46442d03000c8001035129100780415814040c44885911103044007200d0a98140b10500c002d502e6405440c0c03003010795600300b5060000407170344291880d501d8032000c4002c03581d5031070101d4060050355106660f0742c0560315000600c4005d4010031034008004164084170b5003007804407426550130041c24840303810210041c00c015485c007030110000591007a21855265814411401d105404150085050500e86018000821048245082142d501910210302680c4038074006040c0140010000c01d0941800782c46401c041c000700c090400501c05031640b1540c1c034040741400741910080c0040812442001011618031849a0958505c241010b1707640c515040056000c101004132541c42542e4041c0b802d01400313007a603030500186400400501c028003102044c000443e04078400c80c0b2400409202c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 492952005 1250 492950755 492950779
    0xf010f02010207050102040b040603150806060607060f240e04020904082b02181503040f050a1506030201112a03011d0c09060111060712110d0b01020d0c03020c 70
    0xc400d40407603601c00e40c000d00940d02c5aa482442200c4e540150240c840400e0901181e52800700ca046ca80c007084884840042801e80c4a40c02070241c40c0c1d005102c140d400986900710403940317601d40c3c002c0b90720b883e80e110410030450a010743c0b00c5000d02c01c02d820404111a694040c000076a0754000e80d01d42103600041d80d90b5559070329000100c08064040da8034054010700301d000244030451350b03001d012410158500444003400c00b0003041071a00f46c295626200c1ca40500104002c5a200c240d9050040c0c0305000b1650b89c2003194540b07140d200e10a00f0340042035600e54005000319644040080400b0001200900500020007806104801c2119900004070f50088001c54140da00350400400700540b901841820141100269103540e001d490b281e000d45280004100d065110300c031030994030030051020b401c4540700c0d6170040764021000c40040003199150300b80103c40300003810080454070010200000d203450f42000290a104000152205100c584007551002c61307000b0841400007081104c006040e40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 492953255 1250 492952005 492952007
    0x90c030105040b1c291005010f03020a02071505310603060b07030810051306030516050a061209080c06090f030306010c03110f0a0311070812040e040c090203090a200f010f 75
    0x12031600e1800c1603000a506100501044006c410262242aaa681a500342c011019000c1e80719003410704006030300520042001260410480705102502e2414500d0107800c40b2007442540d0b11001c0c103a1291151156601d074651034641880000c1c00720742070a01038246001441401401640009818003000600050000500118203009003100602c1d10f420010041d00c4000109070314041112a0711451100c0c0103c144480b0000742103c4004141d41c52890600380b0841c0e4aa405000084002d80c9034a90900000c010401505403050201e006010b00d14002408038640100c4010f4034441d0380040050065a9134000200721103d505810aa40c890000b85541c034905006201105c22794000d60300128200356000885590040e008001c444015440380080c0c3c3d00d41052441400d030a280c200020081c20000c0170086a105004140790301c1d886550740e01c103c050380c2c01150011002e401200889040042d22030500c503038044110807004d10a02c41c00c000c10a0b071500c0c89840750601071345104e400421 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 492954505 1250 492953255 492953303
    0x26011509020304050f100e06090c09130303060b0406110c01030b1302090307050916180f0303030e03090d0b0a110f2505030c0115080f070603051302090c030105040b1c 73
    0x5c1c0c800380080b5508050f040c44614020641d041c0104c0f0580112000b11742040800100920980c40080440c01d40f6180c07442d2983c7c0c118440e0340300324141070321118000381c051043c101030700042445460310150040c1825050b800d01841e0344041d414545030a1120016444501a007202c0303000e910070050707844500d03400007481c0075070542c442c5600520b000c04001c03400613074404600000080d5119298089109818003440003c0c81c054503714420310082003010910070b8200c150031100c9042aa881c002548000c03904a40041e13005550207442c042c180040d4400b40d100d081000c0b01c000514506202e415010000f0510420341501070802d038204520420400c0d44580202969004c421240d0b18500006501c0c06414022101d101c01220b10000003000341001c2201d564803089903014010b441d0800c00160000c1c200030700301001e41526010000300680b60320ba900b43c003c450144505803258542010403003602c0c2848a81c600030017040d040c0085145000c0804a481030703105081c4401d542e00c400b404008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 492955755 1250 492954505 492954523
    0x20624190906090c021b091003122c13020705030f040909060b101e121d010501090b060403030c020d020d0b06040e01060521030d02042601150902030405 67
    0x3000e41000006201c60099014804940c003680741071210072601c0d5000d9032102804aa140491880481d070b0001602d0b04c050a140c0c45860400c142c603220380c40380c46000311713054218031501c0824600e0003001c000301030010f115540d40d0741d00300c182580918003030040380740b4010307412440942d0364020440c0d070300700305090040e0b50540710014407458481eaa510705100250045a002761802c0789000001021410002c500780d19880d00758442e0f03000c4801c003000003045d9090070b000140821075503031000060000f140c0501d249401442c0c0c6008101044507800c02d003111410703071214803818038000c0f120010f0749492059030112a01420203010012141c004550b08058881000354000c6c5403040c510204034403046034030b00804c026682003014118111500c0d0803920140500c42e4000318030702411f80c10813841321103041c080b82203100b66420318009082043c241e13040354010865000c0d046510010440c11034400002d07040c102e90083c0050078407814500c40b09034181c090f00e4141c0750000006014000108411302c6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 492957005 1250 492955755 492955789
    0x51b070809030d0215060303040323100c030c0e0d0c0b0f040f030c030b07080408030c07021c050c03150708070507030e0d030819020708030601110f0a03050910020624 73
    0x10109400e0000170b407030308400032a1142001a5101003081410000306840582e5480340040d5401c0c3e02255070544210b8500340d2800d03052084e030344040503029441c001d107100005251004242101c0042000e8000c001086070240144c0702c000380381010840200c103803c03c5403a00150596642034007814550184259000109004031481d03000040105039100041264000d4004900c95100d0301000c48041c2001d88000d000c00405102081c9160311180060010030b10080018003050012111044501c035a0750341914203420030030f580300050800380b061941450000524804074070b049d4501504082c0d01409001c1000804030b81c2c24105401502c510001e810000c103000c2250202d40b4009040680c21152016200d40081e51198280e6560082d980d0355a400142d032810b540e43c0400460303840b0750101c5822403d21a0400c1011200b4003441078620041c066990682da82c000c103018801803840307885040301154015020004001d54486038004203225070b11700b0f20780500442d0001f40950b001028000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 492958255 1250 492957005 492957013
    0xf0318030503040e0a1503030302030c251a0403080f062805120703030c0f060b150301080c0d0b0402010809100e0c042f070230070504051b07080903 65
    0x100c1071000001c003410031034107582a00d41565441c1c1c4e80c400142d41044001010141c0351040c20b10000c3d000360080e55111800c010041d082c00200c5226083e0071460048003000d9580d00b0b91101c091045841d003182c540e84998049005a0805030f400410b00720008100060407200d1201040c13241d5104200140204401c02c1c02c4131480c0402c215243c41c0c20420300c0340511a00e8000881ca940480c0460f5020807250942c9409030242550745402c500003044a03403c658007a0740340c0303111031140d692003404404000484026503d03903040c501c88a01d080e200040d82c500c10002944010001509000b10a50080d0f0a203018500c0746c81d810355003460521000c00c0d01400909250344200711280004465080500481e014007800710411a00c0349941014940028040d2941070a003170050400801802d80d40e10207000b100090080d442506180b01e002c41021200c20703009000380c030802504201000c060070007220300b003207070741040103c01c0800b40000300c40e401c0d61040422610140040141a9540c03c000541030f2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 492959505 1250 492958255 492958259
    0xa0905040207030305072307061e0204060504031703100b3603060a05040b060d0c08031c0f050601091502030c01050f01030c0f150e0f28050f09040f0318 67
    0x34000e01000c1b00d00c07100041d220f21002005400304016500358044041d4158982607460700e9030800740c84120400510f910a581c25a641000c10380300600003410540e84d401c0c0ca0718190b14042441c841d081c2078640004001344280a2a03150710500031041b41c1c4154140b550702c01c05a01e40c0962100c0d48022250306144442402d00b01000c0c101c90400190f400301d082d5880c039651282d2484c101c8000360b4014000c3c8800340300040341070820b4103850318503a000c0c007a04425a55126032451650380805845c062050505a0794295100b4038006c82078085606c141c28440f0346020b1000801c0f01c101441041e5207401017510210b00c0900030710032542246c407498000d00c41480d0035003910840060a1100300c0c0e409041d900d0002d400e900440889007a0f0b94051011726070860792031401c940c0c0c0c800403850b444d0b2055001e0951102681d48440c000d082c2501b100e0511820108020041c22921555000c680034248030090304d480c0d40d648481c0e40d94060b600014a07140070455003400c660b942c0c1c1c910300c241070103030311843c1c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 492960755 1250 492959505 492959507
    0x1508130f0c080c01182c100905090f0a030302031306060906170319052808090706090b0702040e01020c03043b0a050c0903100615020d090b0a090504020703 68
    0x100340c0945140d40100c6450b040220300460b01080b42000d81d40583c4810700b811b111983c128038035441002c801143c2402c0d5008125002d620300c580981d11150000f100d01d5042003140500e00813140d00000d410003800c40f0340a4914500e48443e42203200a0416500200203148001840c0940c802107801040c10001641c841850340000d19580c01040700801001404104072100041200c200850100000e0038501e007081050b81d40c2e40285200050104500f40b0f60446201d980308649c0d4544000e90369234840342070000c00300707080c0403c40e0403071420080d609400703102c0b03040248200c3d900aa030507600051068001c650302c0c2c2c0240524201070310301d80400a000594200f410000064a05060f581260b61604e5040040103075200c6000511155000e03030b0005400300b21580c00b4540c412840c0060710700c0c25040c200001e040c10701c40812030390015a500010b10052001c80064200000703680010000b00c9503c0301c02420000d050701c200015564006507886d04c1612030030004000708006881951541141d1034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 492962005 1250 492960755 492960773
    0x61803040b07060e161212030b0607230102040b0f0d090f03170108030315010c03030608120d0518120c10021216021c050a020a1403040e09071508130f 66
    0x2e0218124481e1030010001240304003046000c91b5880005110301504079503480c0344907a564000002410341d100404101d54a07001d0080030120300c90800e9a44c0e4616104600d01c0c9031000355100900b40e0300c103210134060781c0210402c41d007500c03c56005a5031142c3c0301e46240d00103400411401480c8802d031800e5401003541205040c0005041d2210a0b44542e0b00c680003150b803408112604d2071f1020440400c05201d50040d6010084c460082c80e001ca551a2034941107031901130340000030500390350002594005107459115868102c0c070003e038810f09040046952940d00c0403c04501c102c408800140442c298a0801060040018120041d07458010080c60806120801c0b03c0c91210701c40b1001010300240e2000c0b50402d050003507244954040d0b160004c08480c0d58020a100c0c400303510441610300d007c9402c0200300181c0c02d2040c4025640d650501d28903462180020705200003943c80800c1c1444600d035000c040c0c0252800354070380346105a40c3d945a1f04804403880c14050003403003401324840300b0310075815 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 492963255 1250 492962005 492962021
    0x130f0c0b0915070b0705220b0c0111090a0510050d0c0309150207022d09090c0102240609100513090b0105061303060c020f03030901020a0f0c05061803040b0706 70
    0x350344448011500842c50a588220b41004081642c0400007808803030049015048079100154800e144002c8100c034403200b00890b4000320a44c09021030303c0302007003000740070700e0651035900305400c0d0505d00c4010210f4040c40c5c09000c3c0911404072000b10100040c4140f0075a032072041070714003d00007104201303400780003801030b01c5017039811048241c0b030820481024001ca50686901130040030760303040040e51024008441140010120316821610302c115600c41d00e0490060001d08040c020683c80301c000a451310042d01c94a1508040703240b926109070186020b81d03035010030191600d8606544211054207402c482d0340140b9070141255103510400e01d4154014503241d8800d0281c0841642c840741001018080d01c1d0a800309150100e030180000342d40e50300b2451401c2e0f428011105480c00740d00d92641540c00032528481141c0d404a041e4039203543c0f02144540b00c41d180e0802c480108007545420780c03142c1d401415561802d82481c00300400394810000c4400424030101c0094a505143c948a000340c550f070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 492964505 1250 492963255 492963259
    0x10e040c0e04110d02031c081801060f06030b0f120606031605060a0309020a09060b03041101030c0c11030f0706050a1d0a1e090908040806160206130f0c0b09 69
    0x300404140c11262609240c0200d0b00a00b00b44840200801003090300c0409443c100c3c1c040c01240161011032800c41e40d42c60303c2507021b445860251230144c041c0445108100881c42076681429400c00c04054954848415070f035047c900400d8244628000c1802c503840324120b140c05c2007415403125491400030808038010501102074807840d00608240c0c4041402c02c0c01680d85c0303d0400c010003901240130380e002d0600390b44003410b85621144d58103840740807203804d07074411500340342c0000030801086400c0c0c07c400d1103c2800d00f803c001c050302c0104000c081000c1c60320003d00c2117a40365020040d81d5400c110b0602d00b444290100c3c5c05043d2200c100401c0c0c1c4c1c20006034100400e002c0e403e0186410b89a03101c020260300058100f0764841d107008141800f002d01806510201403000c04d021a0002441c0203810010f40500c8405135117519001086181c00c030002c001144e101a160411040d090780810055000b0103003800308004914141049880300d483e000d0010183c044144000071b00410b44005491140b2003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 492965755 1250 492964505 492964523
    0x609280e16020601030b070c0c031205040f08060f06012f01020c010c0e0d1b0b0406020c18070c080318010212100e01062c03010c080a0b0f030a06090f0803010e04 71
    0x1110400ba82e480400b03000080000c492400002e80070b91080b03a40d401300c1402000007852480e640d444c0c90910744980700c6d5260010350002824440842d403110725a0050034413000034440e07071900004200040c800502082d0420000300c0c000d240d0500344c510384065800850369010804151041100e00035805070f0000c04142d4204400303c08241d0080d00380074207a04010b82a5450701c25255607441c68a03002003c01d00c0e00c4107c03c080800c0c058800c03409000900b6041e0014075210f83c001040100402c6481081c0200304182c40805c0340340c1c0e6000312425000c950211440b038070380d29810104603403041c4015a0841641c408241d503140c03110201c5050740144003401c003001025441d0304150b05007400901842d008603802c510b8003403c414041100a26031010601c5800a503c22200000d095075240c1c8415800288070005100400740d6600c04d40210000c2120800420403030803002c07070b846c0c0c0d0081d64090806540c403041001803010a9541d5071101e68070100c403550b40e603154107001c0a040010707202686c203885 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 492967005 1250 492965755 492965791
    0x6160306170105041e080405040902010c2001080a050702031c0f022724090a05090a020307020c01020715052d030114010813110f0916080c090609280e 66
    0x1c4002901151b421101043c075160030107003030002030240c1d888201e0420800b0029180403d00481c60048841500d201d03d69104005800051105a014190110312440c140134821003c0e00002116a4415a030a03054007460100541000500c411000100d40a000148040c2c45012190b00300700009050b100c0c07260304141000500a0007501c04880100d45048002050380b41d41388840a42016607004141850041c0c860020418440301903509406240d008001c0c006142d4041c4202c0d0407001d003c0c4001c02c91146040100c406c110590301e05003041c0500018a8800040001034004071440d03885050312880707a900c0c0c2d00700c000764801d01c02d041820440501d04449584074044007801240040441c0c030b820401f544400541c0260407110381d43c4940c0c42e000901e1591a40364000e4440c0204124000703550303a10a00192091200604010442c0b00801002d1442d40da590300340c0f208030311705980e040560030b00201c6c1059051100c0d000b00032000c11802000600c1025035034968410001e1401b241c011903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 492968255 1250 492967005 492967043
    0x306090e010b180106020a020915100c020315060907050a02030408010c02070510080103170a05090409050706030b03060910051b04030b0615070b0106053006010905030703050616030617010504 84
    0x43c8080c0681c2e001038002c40b50080c0945003040c80c40703030411198904030740c968408000041c00e000584403400301084002100c0300940c078040c8180349044080c00002403051401100140c03201500600c6501401400304001c101d85100b00155406003041c00000c110740501d0b0040650342c4c002e02d10507140311b50641d141800d00107110781050b0b030499a000f984102c070111054000b0980790000280081001030070721004910f5510340c000c105086018201038800103081000050940b215990301320b0183c2d0110003480744200000960900f0011100340005541e03c0d82030420300b15019000415169442c049004001e000000c90498042c0c0001c0320600103620410701005114005c0a07400707001100b124004000070350254000744621065286000740b10000400c040e4510903c2105000c45110070f981040702a5800400c0c1002901d0118000c21445296a41d4242d903a08024640c405142150b8200c0070b906009400200281c1000003c050f50048010b074501e0080c80c0c215000d440e010310000c0d042d1004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 492969505 1250 492968255 492968299
    0x40905090f0a08070602070b0f150301060810090f0b090601080709110a080408090d0c15020c0a03030323070206060112020a0207090b0a0503060c0a0206090c0a12030306090e010b 78
    0x81c0c01c0240646550b41c070940300d242c826000380c001550086d400b00903210000b00b4801081d1b1080d0ba42d220b0803041804d001380e8030f4040c8503010700c83c280207a1408806000203c80019504801110076a01003a40700b000d01d8042116101018018900810345050101d254030204526040c0c0302241c017101d4110303a64859010a0790700402c1c10070141c0c4020442207080b20310a808440e40710b40600042d624090350200440c52040c0201d01c1030f0b82203075001030180021410b580e1644a20100da200500846400c1800505100c440744801010306075604180b00b080d024600071b0082031194030031146000e280c445c1e000b031b40350318007111018001181d9980700540401140301741e0701030780c0c0320360300500301181400c600400520030744908035071285e400c0c90b0005036a90100401c0c2c1c414a041c0d001103486010445e40070f40b4101000e0105115504000141d0900d500ca0810840484000110705644583c603424240c0041c11103401010107031303091100307209465005410034550008283c0c1d00b0704084515111030303886 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 492970755 1250 492969505 492969523
    0x8010302060901050d0e100905160e060d030e0d0809010807021515030c0a0305011e0203150603060f1003060f090e15071107060905010e060703140307020a0b090304090509 75
    0x200c9002440300b0100d55114402400007406560300010f01403150130081031810a08046010a442d03c82c0f2034007080040c140041c0741400b140c86c0e010502c41d4204900c0d051700560082c18075000b11034082250007410702c0b49404940e42c40b009064500707003082070f0030f1040d1035030b0050348414081801f04001c1400d507440050102810031180403442080d4448100d4080c0c4094840d65941d450b01c0b40f0740400c2d078030755900c0d20721400440c80b03840002443e1050712a9807036400a1001c101269610510402c42c1480c030043c0782042c0c0c4501203541c280d80f5035846000450311819000c099400400c1c80b403001200540507800b0500f581c201d200c490515a541d8044501920380402c0304140381d4103c04400c01025203000101d03074100600f810704070000e07440000c00710320380301c0c03160b1040e0001500c00c402046656000701e04442c00800546034280707000807540b005000440c0130644100842e40010001da64076100740146100950b0012120981d41080c2c4406556a00a80100c9880500d4400410180351000814403e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 492972005 1250 492970755 492970759
    0x21070503101211040e150f04030809070f0509040f06091b14010e0d03020703050d090906090e060f040c05031e0111040e13061103090604050705010302131e0305010606050307020d08010302 82
    0x1c1d101c1014007000c1d06001c600d8128900ca00d00d85903803a030020701c401c0c07441f0b801c400d0905d81203131401d428010f200040185c02c8807000d401c070100c18400321015007082d10071344e0000e40741d05a0301d46079890304c00d1f9102540303800034003054035200b18a000c000c204d440005100c2190361940c0d4406488196000d074186814441038003042039040c0b004081c0c14160b412524580c064011380d4007055894541a0401c0258244000003d0000c1400d01000303020344141da0180c50b035904100000c46074460350365078074400038104103441503501c00002d081046d4041c00c41e000d0107024050300c4210440500c0d40c41503213143c4400328401d50a054071004140b130f01000b514101c0c0d00c0607081c04582d482e200301440300c0410b94042a0703180d40e203801c00c54000d441103400550003604100b00034451803a05041044c11300080d5003080d0304050040050010320492540c00105903900304070a000780035009840d049409100d0760000f429542040b400040c10750b0400055880f52800d0307001c0e14030b100507181007201c0c1c40100b408025 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 492973255 1250 492972005 492972023
    0x40b061b03090405092401030803071b1704090612050c13020c0604140c01021204140301090b131403040501050a030506190e0106030609140c210705031012 68
    0x3069881521980040020100980b0b00e00030811000c64203891040300d034441c4650180218041489411100c0185004003c41e4950194150390b10240d09100240445007040201003c100a034188250240c1c14160300920810b42410610a2100361f50007a2082d003484030314216002075400004000481d08550160241c100001030306c0400000016400800400590034000d105520318100041c0c0e004d02c0c01929040b2441d204040703040c1ca000b428540d02030442d000341d074407500c0011407070381540d083e01c480c014000d00f10701180011034010410a18003501d0904508240305102580803450140d882c001e600079110000f0880c1d00a50302d1149105841c006141002182c0f4514800d0f48201c0d00504014034410030303c1960b06061001081c82d81250010000c5540100806a098030030440205002c103014040c240e183e541101711000d004025181500c000a0340c0402c00f818010f45d0301c00001403110003030325030800710030081054204403802400c8409440300890b02c2c4034800c1035281503d42c048010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 492974505 1250 492973255 492973267
    0xf080709020f0a030510035c03030702060f0c0c0a080a0b040c090504050706030515011d030a140604060b0103090519060b0607050105061c02060f0304030e060c0f010506040b06 77
    0x440060400411b060084000c010000c0001195825034036031100720701c6c17101c2032560b207170714002c81d00d500c000c16100c0110581250311155100b8640300c0130141e20b840303540b441c0c618110140032070f0552040c54002940124002911500f0522a42c040c1c0580b4010504480189080100703100504550f03005103070541e8052182c0e800040e00c1b00c503401e41e101c0e100701c000d900483d030b4500d150803d4401c151400c0b0b4540e0030805c03050020f154076100300c0f41d2100d04c800c28440c0111030400003900c0c1c20300600c246c094054024100c00360b151000c200d51454643d000305c0850f60b00c900383c10015158030041d01c048540b01e0170007120f1030082d0302c640101210180c10030082d080340000c041c0400f60641740b2880454640b5250581c0c00c549640314005800250b011300d0001c9050316140d41007001504802c0f0311600b480408004100c096103881d8240d94007801d800030415a6a03c99041c2502c4003031405600315845140090814110780022450501c800e011070002e105944a110400055130030030540303560400401e000f4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 492975755 1250 492974505 492974507
    0x1208030c03100b040308030a15180e030c070608011403281103030a020a02010806030102040b0f0a1101090309150809030d09080c0106030b160c020d0204240f080709020f0a 75
    0x40d6040a01e5551507102d050b503907500584190400ea01c01c1e244c000011007003180c500014041c0c418881c040e21036245403542481d0f03914160100ca5400c3d02e6003981d80311500400040104100d03003420403480111a901940d4000040080c202409840c0c48011414120300d942e003030000d0307460030741d00f49450754005003880c0c01c02614110030171010a40d50024521000340b6151024001040c07910b143d94041c00100034540005001b0302c47c003502c0140240e20410042200790010019682e078461a400016a90a400300085031010581044c0da501c4d94030b000090402c154000c1881750881d20180c0c9a0000c154201313005a03140241141c0d5100e0a4004101c01c909062559100080a900c100076450411a05071003040c03c5130840d40080700d0910340744044c0071f035100083c02e4021500d0a1460005d000340314680c0412408142c0d050001d018030344400c42c2200307a0304045c6901c0981c080c5a20882c40b465a034184110059040e407185c041c4c0340c041c103031000ca0082c04030b0080710056823064003a20324201141e00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 492977005 1250 492975755 492975757
    0x50306010f021024050105070f1704030606080705091e041407090204081b0d0c03030e0a05040207061d0c09060d17070309080c04140f0c0f130801061208030c 69
    0x48490443c0982e0122004072410391148000e00000100c051804501d0090718007030000041d001241402010300102002503c0c810301c020119900ca680011034807040e0b408465a405181c0000304524240800460210400a2035500701d40c41240c03030001c0d0703899500803040042c80003803015009141c241d000501080300b42c0c031811208941141180d00995680c0c1407e8100e03046500f103140680c00007804c0c3c811a651103080e0400c1030301c044071151070040c5035031f481c204440e01900c00101401a543c61800da07030303940c2504a00003044d01030700c00d55030f500131482c140700241610b81c60840480114100c01180440020740d0401103c005420340c08152190020480c141d280c4030001c45581c0044042000d4a601c07280c003500205100e5240c8a04a5007005512810101e18031101070080c0e15041140c01c1c0d4515941e00ca94000c440002007424540328400c82024a105082c18100300150000d0840714020690415070304898041000b04851919070301c0b000b25681030800301600d8140c0600c08182e40302c503000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 492978255 1250 492977005 492977027
    0x90506180114010e061b01091104020a020d0e0402040f1508010e1e0604020c1f0f15030204020705012c07080f150a0b090c0304050105060901051e0609150301080d03090305030601 78
    0x901752070034002481403081c0b815401481c515000e94440800c04c08000880b0107015000000301c03010341c140700d07189034003d40e21104000c1210400c11444007854842c0c5640d03044802428407020042515516010105641110700e06c440380010003100c00000d46608208034039000e000b401041611030000c1d81109040c003480681201c1d4010703402c0041c1481c601081100c4e1113007090003400f10001403856803408048030484915001c0c0c050900320008440590b203c10b0740c0540303a04a50050301c500890900900421074000100841c8607510440e881c020013188850f2034100c20340c400c807820251500e00150301c0d440403142580d0558089424410380303160103500d4030f5201001036400681401c8280000c1d1840d8425120b1074410b40c000400c0c401804800e010b01ca500c620140e07207079002545003402003200c030741202c0090b560300d09144c4465201640c480c0115801010000c00319010700380e2180a00c946648280302d50019071050304454110180a8000e00c070070160075880c0d26045543d002c00548541000c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 492979505 1250 492978255 492978259
    0xf07060311040e07080402091806010b070311010501180b03010204033306060309031e081617150a080d08011202040b04090501050402040b240a18090506180114010e 72
    0x1400041803804043c4005480383c0d406540b0085c441c103290040c0062200d01506a0100e0007401d120b9426800780010680d0444410210190740ca00700c83c101211040c080c600000c03155400e000000402c400d01e6030342004200758a10f420443e0011034400c01d0300300d10a91000400d000e00304030899003844404400d490340f020f40c0200111654082c600b1481c11142181c2145000c42c3d682c281c01410b156114919104117031905000d510340d8804c03900c01500c442401494142160500000b12601510800f21440c0c500000700d582403031410102c110084d544030345144580030b01700c00400001d91200019000d04483c1c048c1d2a00402642410998101c28440290598006442c0c0b407240550380c81d184501103550b8081d500010309401d044c8100400d45810115aa1246486460b600944806042507038070314101d03001c2940d50f4280c40c10094660160000018900c04014040064103202a80001b40325140c200c4565010340c610000540682c0000c0c0900039041d8a6000300b24910b5008020641800c540 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 492980755 1250 492979505 492979507
    0xc060c210c0905041a19060e040902060d0c03060503070803031e070507030311070206030a1d0105150d020a1d04150204060c0f0606031e031b0b270d0519020f07060311 73
    0x81d40010407004c2c1c0820f05105032211b10340004004161b0700099004402c40f0890b4144640c0605400003246070141030b0b2404240d907990503d40090b20701079030000004000c0541581c08036070340c07403074891703141d0300704840914a40c4036545504d00403000b0000c134540b18207165124141801d515803000c8004040714007001c03880050400140c405680c444010314030440c0d201d580030503030f003000003500280d140c0d56510018041e07040c0701c1072007074109604174410100b410640d907017140312865000140340c00c94160702000503c03800c0b60f4185441d20851603424403850040c403c1c2c0c1e043c9048005d02c80128030940c4a200c001032094070b61b540c00100c42c034207a201c0d814029400405c8580c0c5030303160040702c80448920010802c071341c40100320030160402c181503000c08402505404841680d00c2e030711b130031560060046510342e00d400c4000e060808421031424505854a00b180c0d1162100380c00a0041d5001c84201140f1200320358140281600c0001c481c40254000000f50a5840c507140050700508000d034454064008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 492982005 1250 492980755 492980801
    0x1e050a02060a14012d270501051309170703020109020a080a03080402040f02130602011b0206040822080d0305040b13121b1b1a04030f030e010c060c210c090504 70
    0x11961800060001b03510821544200d001d0202041e654042040700341c80d080000410007540c511482c0070100302c4985c000f1079000c1091a001135102842c0d44107080e00031000c03070b083d01495815480401c2282c03003901c0c01d4158030380740c1983c075980d2035551f54014006007400c0c002070b0040c21300d60440110f1b00002d00c0c1c00740c1000301889145c180d20909400000040c0e40da20302d00083ca4810103a1503152868a002401c2c250400b43c4800340148030b4002c1c603018001d100000180d14503402201070008000d008103803042d045520b08021701828041d038082d0380000b925030114000c04041501030310182d0f4400c41c802c4200300d04a41c150740030b803006482148400f440301c1000d40030501607100f654641c509810596030581c24151a1850340d2141032074046450b400340310500002d20103201010160f609410507140c507000307540040742e0407480301d040109680e00b00181c0d2075481c1d4125205c443c00c411903000c2c40e420007049168010803078111081841c00584c1e159002c100701d0820707034000c4100b1800025085240a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 492983255 1250 492982005 492982079
    0xb060405100c030909060b07081b06070908010501060302090303030628060507150e1005220501052517060d1713091e0209011e050a02060a1401 63
    0xc540e080541c4081459001224101940600180003900b03004074200302c5c00d800c002600100740594000180300312400120720440c00311501c5403440141050085034002d240009004041c2d03100392003445629030a1400220f025400780c001d503503406201a004600b507039281ca040000e43d14180491051074040c01d055411610480c41010000c0c0100d91603880c0d03580560720704455441d443c525911015031400000c2000784a0124501300030422109002c52103071903a81070b0302c81440403442c100300384047e1002c900c010000190017180c81040e20620300b03240315003988180e400a85081000000003160b070302101d1054441400780710780184004e0300b4080158080d43e140411880400200110b060b00858054040070100710b680018240c3c4540501148440a028041c1c08481040c1d01c00e04030380108900e080350b481031544c000440d0745904500480744400202810700e5001125107401401903a00081140381c2602499910404500110302c040e80380045a0000d83d44007142650840b0f40400561075030303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 492984505 1250 492983255 492983269
    0x171b010203011203170c030103080d060b180f030c09130f02060313020306070c1205160606150e0909030405060a0c320a0b070f0207080114060f120a060b060405 70
    0x60b2943c904488400040c500700501400075201404c641d04904004200800015000303480c11241e0010209407102c206d0704882000e0412130700b100400c01d402003482580f110b940c41020f00300d490203554110558921700e051585508500b5601c98009503000007080400d200c6d00d084590007070007644002c0c0760a83da035001900681c0281d0381300608a0040141d002586070500800350040e6041c01d018001c800c150f40da004141c03070030b48100c10a0100109010000d0040210312240700c1e40e00040400143d62180c9491100310704803a45440024544c0440300ba1505040c01464003e00300c2c84c0040d800c00f4688401c001190380100c00d95820020b95010000c0000c00000f02c100e4114600c40707050015070188800f41441030705240703041b00c1c0780c1e101c5d00c50200030802d001c04041d00641a1b2821680c0143e0501c02a494050268445281980b0749680280e500d4001800680180c408813109200040c07400d0410003140412540080180c10510ba0300b80081c20b1a07110040d0150043d10b21410a41e844001540b5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 492985611 1106 492984505 492984509
    0xc030c02010f110613170702030c060918010f0e15012016090608070503121602011403040602030a050709080c12160f080118171b01020301 61
    0x82c880c0306541e0f0a00c00b018000c2151030f2410000059041c10603800415140c11503035501c0d114000f00702c1d1085407081078000b4010444079440404110032580812131041c2e2107110846801403481c1c3c219012030080017951003158a003483c01c3e0110f05940c2c0001c01c0e200c04680528126441070780c01c403101d11551b920300001040000d0240d9400c61034280559407981e59400d20386400a400700007600084243c845110540b51001e994405140e600d08c410b2140200c09801485103a0010350880351070605180145852000d2103400401058198401d42d401d9881d07a40001c100840303485680985a00407015182000c907981c03400140d2501c0714070f02c401c4140310340540055805618010406290783c00000c034081c44030715587c0e844901e440700350784c480c200540d4286a10f11001032030312074080c0041c0d500700d22201035400d01000004901c0d40034035002000c0f5600300c104030089850900c06140 = true := by decide +kernel

theorem cover : BRFrame.Cov 492805755 492985611 := by
  have h0 := BRFrame.cov_init 492805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 492805755 ≤ n) (h2 : n < 492985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
