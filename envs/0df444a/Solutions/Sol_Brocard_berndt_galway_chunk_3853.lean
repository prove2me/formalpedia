-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3853
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:52:29.500983+00:00
-- url     : https://prove2.me/submissions/9ef8d3d6-e6aa-4a7e-a9c5-e232178a78a7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 692805755 ≤ n < 692985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 692807005 1250 692805755 692805767
    0x190806031023040203010f06061701050102060709093b01050705071509170d0b09090d020a170c0d0309060b0904020a091a0301240801090b01050409060b04110406 71
    0x103003004900d0501030710070b01c0280110358800c00650300300c0c9034400766507031400024050103400c0c0044186519141000c10499402800030031440c1034829402a2a641c0c0c5004aa80e00802c07518100002d040000900c118211904501c07012988040300166400c01210541c80c801c80c20082c09000065030b41180c104900b080c007038981c0c0100e09040c42401c01e00c06880e40490000071182000700103a4410b20b8008022041d5008898101202e60103900c0d00490728030300c03005025400c0300030700c1030040100140c0001e0002660ec40748045950180500101c1503540341c200901c500d907140d15411b8207200e800c070b440301e080100000500d010b41d40828209034900340031301103880d0812118002d1000c42c04100260300e482c80ba507800c442801c14000b0707800e5140c0d1000c0c142140420502c035450350a0a1882c1c2e00150702d11000440300d0b44000c1d40c0307014a40e4806089080b9a1642c000600c6116100c004000a2800394403890742d260042c000496400300c0c0c030001a0072240d803c82c00750011000401d05122580e4031007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 692808255 1250 692807005 692807023
    0x3090606030c0f151e0f11120d180f230313060e1002071e0506070f0302061311011d03010504050105101a0301030f021f0306090b0f21010219080603 65
    0x2040150035480440c134050040c0502603145c0c0180a0000014080c144c881c0700714400c0803200c0c5d8103980c10041d05008000803603000000d42c810441c104058290b441c2d4040318111200c0e940103400442801d2036030b071085800e20040f00c01c03081611406e80b501c8a103480030301c01800d000100c905071035074043c18102c024003100d4182e22110300900710000041c100340d80004600302580c0b028900f1803000c50302140c5000311351815822040d0403d60201b4010304000a603019540c15510230740a03110a075460805107010203032110320282c559042080c58050a5010b1160501c0c00421041d0300c10f0300c0d018220109007901d000795811655a9580e8041101c441c00c02c804600c0901034032030508880b0f02c1003440c00040d6000600000d00100713119111042103560f00d0084904c0c040745005c0c040110f80400d40c000c0d00030040391050b03a0542e404c140000d0b95900e030840304003252001c0145080e1080c035000c00c0701d040d40c00280110300344940d420840b00701c80704074084500d0410742c00c039500e442c084c0c9442e1042c181080201 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 692809505 1250 692808255 692808257
    0x216030206090714061e0f0403110907031e02090a0302042a050405030d0311130b07121b08210a090c05030f061612051e1005010f03090606030c0f15 65
    0x1884031142c50b99103400440301901008203003040d286d034801080344001d1181d81003a400501d000540001080606440d68010240840c1d00300c03510b0760b40400035410b0320040c1a03141c0389080c1e258203900e90031610340d000c2c010b590805005100101d032a980820708440c1c0e03405044880490040a01d01c52542034030001000c15000d16000f814949070401003642c91070b150110b00103040c0c42d0000b400d1005291016190380f000c03111800c40c005603076003030841c100307920246090700c500300345146240d0003600409501c0380c0d03214000581640b006103500c401500c0d8010789240b034801c41c00b4006411448a81c0141c4502800358a00009155025494079540c03c41486d805203000340c02080710a48444000b252090740a1090049440800b070390712001c03102c0450110208084900d000144201c980c4204608103000c00e1039079494503107849042d10558a4a0203101d13103400280b6880e196087c5502c01c2e0004055248140d4020910a8407070350303124024149508440608080c1003010003c1e04548001c8103088851 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 692810755 1250 692809505 692809529
    0xf150201060608180a02090c0c0d03060315050402060904060311041d0a060b06040f0f060e180114011b060c080f13030c03050f0c1e071809050102160302060907 70
    0x280000107060b00030300500c20340a0104c601d0440c44003250030f01101c100c00e82d004000b0a032910313040c07031040c1181d00030314070310601071080d0444440018024401d90382a603411444c80311040080c0c0c0d801c030010f040014800ca801820500c15881d1030340f5940903850140d442000a0115981942c0030301049035859110b01341d01a540d80450039030305401243c1d20100940101001c2501680f00010808900c0396a02ca04610018644005880074460151009403003c0e03540e19921510b4480c1040800c0f4107175541c010128035082e00401c12600030259491925406042582c80403401c40f000003000d40d4a07010544102d615540710303517013060b131102e4415030203201650481c11904000540038003121036180000e06200241c40c0450034180104240d808101e4120102caa4868854a0f9940c4070f000d034842c69681c003409110b404c0c15500d0082448402c0d030742c0800445004c210100c01c80009041c4465040c1c030f055508102e8081c068808600c1c0110503400794004003550704054184628220701580042c0d40e1804c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 692812005 1250 692810755 692810759
    0x1003060b0f0d0603140106060201050f090303160306080f0322290912010c021c050d0203040f14071e031106030601090e160914060301030210020a020a0f15020106 71
    0xc100c80075540c020707220121540c0c07a40c50344850240288010b070000b51507004015842050708030305400c41d5040d0303551503000784240c0e103400512000c84c070016030340d031802900305200181010300407843c00740c540122403501080c85a941d048485c1010b800034009070b116000014a04c0040c0408040b0481c60f0b02c4032445604454038105100728a01d8a03901e18450007511401504140049501034071180307980180421503d60803401102c2c0240124000840940282d2030740b0080307042001d411901d401c0c46615940c4c03402c10380b40017003402544020002c8a002581806150208070090000402c1702c10100062041d907052115500340c00066030107400440100c042e040c00014841c10a03041c080c60f00b5030f0320f030b0b4903038660200580300b00c0a248c00c001214041c140c2001404207845024a100c05642d8450302045510781e031407800300c2016404400d401c50400c00c01000103040c038650007585070798641706444050140c0d0f400510800560350000442105141007072203a001036070424590303120640020130000d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 692813255 1250 692812005 692812019
    0x30b011509210c0f06030b0306150d051c020105070810241e051b06010e0f1f080102040611010c0c080c12030c070b071407080325030b100306 62
    0x404640200780c45548180a40a9060105a00003000c0d80d0300642d110b01051312440c0d400b144440d6880b890000034104030800e4201d0901142460059250130301403240101d4070014031141d940e102100301c44034400d0310032040c82e02220000440d08008a075001190070f080c5090700074005140508a00d440c900c041908000b8211a1440c06103030401120403083c4002841d00152014200c80340b00c2d03034140b02100c040e0703801c095120004118508400060000b00d41d10b0b0000940d41d02000d000304400c040e4010045641c81d6050040d0f039501407000c025070f1110310301001e82c1001810356075100e41480c1e034020800713101e0309801c0010040040185030080001e00001b1b40001c0a040366228043d1145400050004410500f441034611201ca41c01180e41d076402c201c6203207020342d4040b1105039150340800340800c4d1850300c5454140d001c030040d00e41103030414a103520360f0300b81540b015005c9a140c02102594400000d00b640b01c40c4424425500c00140b00f01c108024801c07510038102c8548101441c041c8203000c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 692814505 1250 692813255 692813267
    0x1a0705030906281803080a0e07170c0d260f090d03030e032b050106091e170c0307060201020a050d090f0c260303070507030503090715020106030b0115 66
    0x80481d800000700c0f000d0084066010380e000c0c0b20325118660800c440019a4044940d9104016110740e58400903540c0b0b00f510841140c00c00c1e072109805802450040100b00c1c552040404400d03006802e6401400c3c0c2c030700c0007965441d190441250440600d5480d0004a100c8000c01710300800b00c0d586280c94102c2c0080b0401003840745240183c8204054103181052500c6603101100541190f0104c2c1c0d501c028207034040c840c0b281c400a65084075020721100745102036250140c03904841d070fa511564406800c01505110303105640b04014075090380511b000480031401c55100c0e13441c0080d10007412131120008189420403001d40c20613001e5a00400c42c005016602000b20f46001c039000380001040f0185240a0201c00084080a84460307010480480c07120070480b00380ea04920ba08041c070001c25845010140c032400115081c0c00851800d100002c0441d0007400259805641c0d034007920089600c890801243c079814001e0040142e545120900c100081035641030b0140c081341d05250100c050018006000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 692815755 1250 692814505 692814511
    0xd0311071b0e100f05120a0210030b0307030305091906140c070905160210060503210d05091b040e030301170712080a0e1c02040e191a0705030906 64
    0x42650240346454050100c40700001d004000c0300000c0794108214a00070401d080d014424869002110018407468894107000c00442c0e51030144c501f20056808100000c14640f80030401d061711b0b800c03c0c52850b9070a20ae05406184039454140d19040a50240074036045110148801203242c00c1e0706000690700400da00c4011420100060784c0c0c0d24904e4811800c0044940c029080181440309200702403050140c64129018140c0c00c90310f100210341403803400c0d02d0040c0f040b45c1d0160400d0540c80c0d20014002c11104489140d0300c2810310780071000410b1004c484003120608115000241305480c1018100754046140200700c90900081109074805522448184290103946244140d02c0c0090403040c4030b014018900808007000009240c10304006540c0000703a10000120310094188103464031444101500305d038100719000001781c640c203000040c64414000007592040c040c01d030010f0741040080c0c0715060310814452004000803603480001e0310003e824201403207024000c1260240000595680c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 692817005 1250 692815755 692815763
    0x50d050f190c02010f151509030308010e0c19021608120d02030702010603050d020c04051b1905040504060f03110303040b1206040917031005010e010e01080903130312020d031107 78
    0x152002280106a004048401030743c5011800e016600d4160f46c00c0c3d02c8110704031786841c40c0070f426410011000303ca004440d0301006011421140c01401400c0103030b18595803103601522407904c0d0040b28480f04032582d4203000d4402c016441062480c6680c9496002280100165001801000420b4001000c2800b4102d903485101e40d0200008113124800d42100c030056820400703544000801d040003d481c0c1c030a41703010301d00603230400010805103901400c21500c07054424030700c00d0800300700c1c0002e03044080c0d0a00341c0808000043c00003055a130b03180d01c40c84004200140c4254107103860351030526050404200540c2c4203400a00c0b08006140ca80c204440319030509968400d155920400001c00402071880302030015925010323a0091317400032800940c015492440d11034001e03503440c801124190f9101c103c0500180d0b0100342440107500a2079000c0c2c1007030300803003940d00b0852500003141e20f01d00c485e4000d80f100030f40c5030f03602a14260140000d80e03484042d03290911100c60801c66841051182c460028 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 692818255 1250 692817005 692817011
    0x80d020c04020405010c060b04021308030a03050601081003020607060608060c22060906080901020c060f0730090c091802010f0201021e0304020609190f0512060c130b0a050d050f19 79
    0x39881b03543e184d04441039404907009122226840c1d030a33640d62a00054091030110f85803001249031580074050840c4211a4541c010a4103411542880780036044020110f4a4940302c80e00450861024002244503440c200b03411a2210700d00c0c03d03218000c0d00d40501c40740c00c84111110070312025074007904000584030305003003400343c80e280e20001d14028851403427115554050031091050610001d041c060150000345e4400d01c01c0344120340420040040c4003e4003592070640c8203100e00f02080e9403c0855118007030910014a20350b503480e40019903039aa0481c4180141040c90081150f800c444a101c14411510086041028214101032002d440c242c001114a00100c000340c21540c0300d20844500c118054a036422070385c4c0c80c450100c0c010704035024248104030350305404100c0307080006542d4280c03400300b40107200d580c8460700017011f554048c1c4190402e9207806240410300500d800c1c010515a0620380e215640c82038a46000c170100c51014011101c541503a10038095005540c0b148004840000d642c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 692819505 1250 692818255 692818271
    0x3090103110c01020307030504020a0e070f120e01110403051c02030d1503081305030105010b160809010e1215070801081c2708070614040608070c020406080d020c04020405010c06 78
    0x4014002c91088503541e40c000000c0101d01c07981078024900032403003501c004622540303480244904c03880403507603040041d40d0b003400c0b0070b206e0f440b9140d03c0d030000100002c00500302d84070700d43c2d03a400c2d07614440004003200c030006010000c00404110b00d0003a0200d401c003085004d0082d40303000352a4420b01038207600301503c4900c2180700c0d000c0340040d840103551140314541e8843c3c15042002182e036851241611a500e86800090101c404c2d10132038500032689810315a80200c9556114820f420130480a41008200080c000890700d480e0040100e4841e940024428402078190842d80744000400407020405000d0040010141c00078001e503002084c00280e1484202d501c000300e0743c0501d01800091850a2412522a8805c426450405888409060303440c0c190305c49009840050201400f078646984c1000100301c1d551040e5803950b0007e2480c980f51040e01910340004081e03030801d410152032070300600d1004034500c1d010421103084c01c0d8183c40541c100381c40c0c180040c0921208540252003c1d03161521 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 692820755 1250 692819505 692819531
    0xf0106050c011b08060f241c051e130308040201270605131d060618130b030d0c150b030715091802030c0a120902280f0803090103 57
    0x1c141449624000340310320401c40b00f040185441d50036140c0e03a010341540710b0a40c1541c10407070000159690341c45546040d200710180d4041580d072001c0d84004041401c0899225200901c0c081c65009040b00c3d10700008104151140d900004009880d11003080c61480c1090006500001d01300d603c00d409003080d042e0191a580c5642c250031521051030171301d00020b0404a6100e400c840585045e4481d0391840700c216031030b030041200209940c50001185541507000943d039181c100c6c000c2c0722043c13000034844070610070500424a00c2a81c05c030003011198581c3c0307000141d420f040080c0280c0c0e0702145042400e80840307440d01d14061602c00075079124145ca03080c18011a4404122980c018400c84010360000900b9600c010086040c50045890001c5d1080e030301c1039032140034001e4030302466102003035910b0905842010b4034502071400440d03807140e4aa21321440541c2e1001d8000000101c90fa003d902c4901d801e10440045031065006030556040540f0f003401b04000c00010748102071000c0c00c001500b01d06040c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 692822005 1250 692820755 692820761
    0x130903050c0a03080a0f06051e0604030c090b120c13151a18060304030905040b040f021902120f2a0d0e03011116060f0b030d090515030f0106050c01 65
    0x300280c9640b0940060408165018521502c650000704c010021103c2144c000c1007520603038414598030070303401e40e0440300004011040b403041c0c50340100001d1030076540e5611000036108a0380a8141555208200199400c100e11810f1040c0e000d44050307c0d40c0081100010708007548114100304150b903800806e01b43c50035030f4129401925100786500d40090f4034180c140103640c80103c08552100f01d1001c4030500d4141101030340d0003107915499a40030780d42031406000042c50107000f200c0d406a111300b07076610030f20158401080230740802c0a126a0110702140c0191a20410032010a400082000007031b0320504094213860049142c3c01c42004601c54205008c00030300901c40340c1008034000c01c0c00e038020040d0050f02c0c03a010301009a00a00144407040070388519801a00b805665045418010200040325940000c002241e0074100003503102085e0082842e0040304000c21000c82c0b134041042c41a460600c111072011003070401c0301461071919201c903040c0c060061040105110011990482695081d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 692823255 1250 692822005 692822017
    0x31211060f190e0c04150f061103040b040305030702030c0a0506040b130503031b070b0406091412100f24060518090f07201c0306120308100e0613090305 67
    0x444140f03c40e540550310b440d00c8118112415101c3e1303182544003480b0903191545c460072038250703216a00741c580c45e03c001620024200c45180800d408100000b00345010603002401c0a14080d800941e00c50032188141403800302c80c0084d051044030600420412079541400301d0b402c1c0c0e81c126221355121202c40c103060303080580c03039000154107000200f030a2406400c1401d042d1680710a074811241641d81d140b0101a003846035000c0c40c0000360030200c0903c44c03800d004010511200001d45080aa0508065002e0401038170300c40c07010f00c590302c50b621200148114020007012240700ca047c29031550000d03030040c05441c81c41c4920f000b4050003085441520341700e802114006031024241c5a21480e0a0400f000320a5040742c106000c1500030065800407080c0d482e0110b002e891250040002540311011071105200c9103000c001095110100802c03400101920320404903c291122401401d0412084104580507081989120f4101c0b040003119541c1c1146011004510440000d104c5014201250103101e54 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 692824505 1250 692823255 692823301
    0xa0906090b13020a170a0b130b01030813060306290f0c01020304170702011706030c041a040b1e040203070c141e030705060402060a1116031211060f 65
    0x3104100e48111031142400c40c0a00c200c854034000780c5c40e0a07080140800030007800441d50f12003e420400514481c56450f042009104c484801080503500c02c1e00d0054241c108840d88140840c2000b6160702008500018052506040c00b400d41003014054a0800c1c02080d0b12076141c03840c80000201e081c000444100042c050003070ba030303903130020712446000c0d61042c1d4003185c52560b110a00c46122104d0015140101c0c0d05030745240b03402c0d4181d101d19500b000090300b03a075454018040c0d0031015940d6072160074081000f41d0701440d0000441007c000071507181c042d4060081011130380001071860400c82d24480464200c40050f1a1389800c0c00031105104074a4004105020300ca15142c1408000104880d541640001860091540d424550b07183c3c0184c1100501990148011500500e4514060500100d0300d140200703801050545251501041e00302602107a00d440030f040c02440810031030002da081c000d04125140c5c1c0547e29129540b094011700010840c070074100860400c405a6181001d02031314 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 692825755 1250 692824505 692824523
    0x90c090a03080703140a051210090c020c040606050304030503041209031403270609010507020f091006020f0a11100e1002030d0b03060c07080307020a050717010c02060f0a090609 78
    0x281e180c0b0000c10351007841c0030740204d0024485001416441c0c801c40c1c0030643c840d558503080240c019001c6407a00c0c006000e80006140610012805180e9403141549101c410b41c004c00c204001801804100d0b4116000842004010400c000200303809c0230441e0341040e803100f00342000c8604003c0449040e0741540006003200c590b00d80304000e0307500001c041c0511900302e1460b60b0710804d40140007450f425640581940101c418880c2001035030040e406000c4090020700f072221500122030000720001d608480218811041c4402400f8441c0d04000442c2034048050040413241e40540340c1d11803801c2c55910f440e03c030b198412a020713082c51280341903032502ca60141c2000d00d5a402c081d406501d90308045070b40c0c0c1d40c061070b1988080c00d511700001c08500a482100d280f0745410080d1300c0d0f50500e948010a170740c0c00d61160000443c0040c0041055400401c1c10019140c407401c5044d6041f400e482c80142120b007190b004009210070b000c4a550310302d810076000c51700003654102c1440d020300503020581d1701900c0064 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 692827005 1250 692825755 692825759
    0x30c0b1303110604030e1201110403080408060a0b0306010e130b012d0312030c0504150207030605060d12051b03030c03090f03030411011b080a0f120614090c090a 71
    0x140c40448520041c840d4892050050140d92031650b500740403900500040d01c00e030145040e030f0501c0903e40d03c440b00148004a01e801c60f800d004102a0300c5a071040791f079000001410440d0310b409114071504a000340342d0038003100c0502000244c2d2080b060061840300c4109030046010564120600c07510198000e000f8481d643e580c500c91101c0103010201100128925021010904e44103106902500da104400308440c0d11000811401050302d400468140701c3d0401000c50401e06003101055030340c072642d000b00011411442d101c02641c00141c6428003513840c292007000015000c1c181d0f0b4010300150724141e074607980d032502c032040000d0413010301611601000050120105407080114410a40b00044031100c0c80f040a40f02c1e03480c401201c001d024014140c8581d1103941c81030030011001d048455601d41c0104540d1074419141d8004006580400c41c2d41d40403060942e0031019121110010b580300b0000545032203d10b5603034031010081c03188150191400100b41558a40545044003405851541595 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 692828255 1250 692827005 692827021
    0x30a0b0a1502070603150b040e070201060f122609040c020115090501030b0601020a051903021e06040b010f061b14060c0703090933081212011d040f030c0b 68
    0x14100d0080c0130000e801c3c44440a0300200b0141004111800c0e4900d807854145400720649102502810783e10443d526100300040c0680e10715003c4014003c0ca4860f80c8010700d05103485085094190b01006003070780d0240d4030100301c2c010390040d07070581503041e0b601013614181c2104c02c80c01040082d1180c1900c1a0844000c58101c1d015403108e8140da104207640b00b065180e120042e40e46a44040c3d008203144c0c0000b501031024000003e08004d040e100340100c9a008141c00d14015240141c40c032035003441d901c605c00b00420b00a01d10f8456005011140c042524582800401400c043e104012005420f0309801040304000312603c090308025001341c103441e190304050340d10f000c0071b60141750154001403a900300403498080c90b2007a114018100c1101403905213200202001655010320054020254035030006040701052040002c402c6403100c5055903240008040401d4000c1038009040400c1c5d030304d416041c0071500c0030a02d9001900050001d190b8002c2d45000c545d050050080240251070702003e02c1000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 692829505 1250 692828255 692828263
    0x1a090a020306011a0316050d2d0b090c160f11090a020a0e100c050f0c04060909080f07170a08180a11120c030115031a010b030a0b0a1502 60
    0x5a8400c5090328010307680ca14100250f80560751000550110800101e89999a86c81d43e4901c00c210ba4240117040c1080c2c182420116042184803902503100340d00d5030710942d80c941440f007800540d03400c02040305411450205404c5600180080a00c510000302c00c0c2c81c481000d0401100258406001c031741b140501c0c98104504c8030380002c100d000d40d510102094041c01d140c000e0b115078a9013652052040e4001e00100a40c0c0110300b000c2d002441104038440000ca00240042c084030a004401419810041418042294807550181008915003144a00002d408004442c040d40b105401281c81d0459400d2011008882100882c920000000d2a0b1209a0007220b1540b1a0381902e806135281c403107620f040c1da114104030350001d00c0e102e01d90f007024040b0702d4021003a03401080b03080c040390360341d11010f0042401c40b00080084071582900f20804c004205044403082a00c020070b00342c2103a235500d07000091059000260010150b036440d0404172055481d000d140c40c0c000c10806136400780e41c00603500c0c00307074031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 692830755 1250 692829505 692829523
    0x90605030d050c0a03050313051e0c0402040305060f040804050d03080406050a0b090601210c0908210a0311070609080918190b04060518010906060207050f06071a09 72
    0xa4012011a5001c2600030401d4916034000480a40001e090b9a41c04499681c00146182c440552080700c1001040040107042421144018807000102d02880c900e4030304a500b44902c1d1040e8010001480040c001041407900464501c8071503a0b00d48503403508002074050303900119001804c03407071020b0505521004040c00355008000400c02c613111f0701c0465064400404645401100c0040400c0e01c80d407007889401d4000083c016155001d1083c45100300030355400c07040010015a50482c00c0c03124031003d00404480e96030002044141c0c10700b45e10b00307440c14040e0828880030716585d90381142d2242d800c07008690000d5445603007084118003a26118486811024000e4001c200304180821507004810109001e003a40b80442202111049030040c00b511200060641040c4c0301c0100241d0380d05d0b5001c0d0091003211010b044585c5d0342c104006c4900312010b0b035001c5021580400001c004503101d2aa895415040589210b036a4012a044c131661844131501d0403140c020100081200c000c00200301048 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 692832005 1250 692830755 692830759
    0xa0e01080c090909060f09120f032e060314010f03080a05040e25020a0507050d0219170d180b030403020f06040804060f0e3102070c170312010e0a0207020307090605 72
    0x4191f40350103248a580380c0644500d10f511032404c000024a50080b8000365920100e000700328062a000da00d400c682e000c0e084081d54000740302d140010702100c2c1d0940a6010300030410070300d0004544c5492038959442086201c068594680015041040c07845002103c0141030314211000a03800c2500e81e01014140100702070701c41b00c00c880580390040d48042104c0020503000001000000d040104008030050580340c02c0741e0203542c0344400100240d07031410301300041000ba140001d1800c0c10650850500e0174250240c0100040d000c0100152a52581000152030b01030a24a44a543e507243c240d11b0200c803800004900d204003400c200402c0000307001081921411307500c0900034000100140e4202624650079070740046840c00344041d01c10403201810b1a12a007018064070540c0740b4810004a9200307001c161011789d20000140254a10040c0d80074030100d1030802949070035160070034071000ba5018040d055921182e4030205154000b2501070300c450301d8005054400d042c1d5100500c800900c65413062038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 692833255 1250 692832005 692832031
    0xf22090206160c0501140a020d11070f0801020d1506020615040f2d02090604120f1e050c0108010b0d05060103150e04140c030a06090f080c0102031b0a0e01080c09090906 74
    0x1d8186c01c0c402055074040c5825070020404901e03500d109a60f0f07011442101e411500c5280f000140e00034144800310b000b04101000143e55a050000b0070080c0c41800c0150340d190904500308002e5240d0001c1d59070780c01084585002c156500300c03000100941042e04044c01054141001c804410007419000c00c51203030311401102011541903ca907003617000325034100e507100e5001e0108010034044402242500340c072541d042c0402c5555541d40044094000c2c03110329030380c0c0130300404601701f200070403c4142d16842400c10105541c501041905640b04c0c0401031896181c617840440c0c031990094110030300c0c28070b40c99880c110145d225210004070081c120703020303a41d40134041011503420070003084003280e07128050041c10804100d41c0364403000d044402011120b006a031a495404100e507500507003a125811300000d6541d017003842000407074441209148440003410481c13890f00070740203501680302e075100b8248000381e90f82e00340c071340b6025000d80491981c0000d0fa4008000a080e000b00d079151045031020b80300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 692834505 1250 692833255 692833277
    0x150a05090d06020307120b0d08070203070b0415030f050c2a0105090a0b1302031515060712030c18091107084b16200f22090206160c0501 60
    0x20000c0e00c4910350141d8208e0503002900c3c011584490007070566034005170803180b0480e03640242c4a0941e0140d4441503004070b00350b44146040368503002d440307120007840c1030602c841c0c2042c000d00c508501c1000401e03d5007110f110030b00b801104100b600d0010012400c0000c120a01e0725041d450344500003e101100c00500e01c2d4005100c0c20b6030307903d070440220740160041003072600e965000301100300050115800e018181d003800c2920341d1460010720100380304244000001c00c6261001c1c050f901480702107024002c1c04211008001940803101048460f01c001c08100030018000015061140ca00c01403d1513000090f550164200036075881598004c1d02805040d51586884544a584141001a1b280b030f505400c50300c84000700030041c1c65040106100004414100e80e203000442004050703440c802d142800c2d50505501d48011071001d140d41c00c0c0c81501d0160180c450410520041160120581d555a2600c1c2c00f50f444200a4601c0e102d07001c0c3c42c00c211003c403400d09042d000014401c041c005030984620b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 692835755 1250 692834505 692834537
    0x61403010803070f08070f0c0f1409040305090a051c110111120a030b060307080405010c110a0210090e01030b151516050f0a030305180a02150a05090d06020307 70
    0x11203040322806805035040c50710655555803100390410742690030940602203038010440969002d200c40d0310030200220704074508640c0038034003080c5a000d500d140d0301c80e417810711031a200e04210326070196051038029a2000040001008000141c22950f0404400c0c180c841004c404602c001c003409019110246403c40c4039001100c0e21244450502242e400c010460518440090003410301d4181c03505011481d000b6203004200344d50403c54000300001d09a4041c4400c0c02028441c0100302c402515000c115440405841695403000e803070000d001783c0c420702c56505024425686000509a0100000c01c01e581d28101132070001400d403420b40e01c0c0041511207860503e85008010084003400e503005040c03500e9412017055400300242c0c00e03141c5000b103910070948078400744003509045220b0340b0006001c1c14280644020005003c040b101c896009504032409652007600440c81a8007002c08142d0320308035018111018015460000d401103496280c000c104420313600518071a4546540c2c0303144c11449a44 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 692837005 1250 692835755 692835757
    0x2040225052b030f11180108180d0c11100c030305090109020f101e1232102102091e0c07020102120c1f0204030309140f040c090614 58
    0x2448860107003007040301c0b03003100d402038201c98842c414a07100014000d114812000c140c2e80240c54100c5c1018001038000c580c0d68004150540144801704400e01407451420340981d02c520f07c5980c03400703006180f041c840802c901c01485103143c41018040c0011304015007000340061000724411070110b401e000025840741414811a80c0c074036001000ea542d080c0f0901e0030b1101101d06a40e030f050030051034100c6401c10700b14858014000810390382d03e030140c2c092810301030f43c1259031003081840c40c180807070702e442404403101a26903094445800a80106c1c0c9400680c1d000104540c2e000504610700300c0f113099044044104145241c40c0255008001765403200500c650040c114500152515111000304901d8074034180642701051060045500c418407111091001390400c42e204191580001c1e014090354210b0f07080c20141640701e00d425824982507a40103060140d5a000e150400600c0c000c00040070307500e2407603448080d0b4000e807080000013030340f1a008007090070500070a804030313148154801ca8460054 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 692838255 1250 692837005 692837053
    0x30106140901240309080903072304020f070605220b041208070c0803060109090905010614011707031505131a0d08030115030e1005070f170f040204022505 68
    0x2510780c043d107002c00c10150700030484560140c0720410300b8050311b0340b5074500b003000001801c02c201c42c0e0a01940180c810611105803007103a0b90089005112a1541c1034200c810386200b5940075201107038039502c002032140007540ca40101c40e00702c5041080300e41400300c52010280510f0182c144011083d004500c01c0d668810242c500c0c00004818445180100d90950051034112170145045e8141554030b100500c01c0c4c03401e180e8280ca059542c0c9a041101c1050416281d6940000b07080c40758160410f02e401c120301c46402024001455140c1100c0a0030310440b0b84008054000180003190200340b0043e800020715480002d0581b10f801c00381641124508420b200c142d4984c000c00d43e40c55a82440c040c0700502e400708045005160711181102a105414840c000fa402e090b410002828a419640201480400c0e4040420f0150280380d480589084610050340102d11003403200c2d2680725880890001c0c40748200c0b4040050750307400c00f0400c0e21007100c0c0e00803445010380100c27428403116201d151b05480d810 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 692839505 1250 692838255 692838299
    0x10308030f151c0501111b0f0c010c0f020414160e06030105100e1c05100606030501050d0605070e12010608070504020a1e02030c100b12060402031911030106140901 72
    0x18081e840f10401d044994041c8101c3c008580200d04540d58101600201d2020310f0305100c150402c40c10b4441001b070050074400200c0102042c05000c0000382c20106080030152491400307011071030030740d1981d400c030040d0100c0300100102c01e403600c2202e51074003c6034151030000182500c00200c046141140580381a40e200030002e8400400c07050007500e822082405254010b2000b04500c005102c250000070001409a17010301540c0e01c3c042049000c8400344d070000da05061501c1c0044c0125100d895080545691180740042c4586428406641300c565105002d41d0040030303a0340717546c0c0450f01904401c00725400c91301250340b00b81c0c8450811059003d0441d40000090f0328811204540888800445043e102801034038602007500001074240313aa150b1074580516280c031400c40a82c00d08040e02034a094115014015909044e40007079100d0f505e18090f000614520112241030040307400b00401070620003802000020741c0c1d8040107807040014103074548561551000081c407201c0344404041e0700011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 692840755 1250 692839505 692839519
    0x1602102a14040e060f01110303071b0b040317010e010308042c0a0b0103270228030303200c070b0306060d0e010504021f02070519331719020c06010308030f15 69
    0x410310114bd0000c0d050750f80009c01c0039016580b401040c02c412201c0d009a001c2e583d450614060b01c1c01c0d02d1030030401a8000114403030007800400100e03e1141c240c400740c404070700502d0901c4240c26101601c005155041075005803c840c14010040b003190702281c0c6103202a00c0c107001d0000180ca010504e1100c60203180d04003008604600c00601c2c0041d41c441741d0200c0a50948112007419070601842c02c0160011070100365950311303c00010b01c2000b40076081580da15501c038607042c8461140c58442d1b48a21074080741a0011020800559500069031950310041c0b03010080030001c00d44850180c1001c2e201a40901c0300280d0442c40008120840703000f009054000f01000e528020601c1408914084104010506c003440850440701c072800203c034410040188264a181032901041d0884582210030284240da40860340e01c00720031100f496000e1103a80700c852000616101c414003034821094aa40c4500441c00040100030350700000e140140c4403030201c1e61060b516616000886656048000d5000c1c43d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 692842005 1250 692840755 692840761
    0xe01050108121e0f07060902031b010f0f020f0a0506010f050d0206031302010203090409030305040b0702240c0d0e03270109091a04051602102a14040e060f01110303 72
    0x202c00078010304032616982c810b49030000c0800308a013540c00c01001107035281d49844a85066180c100b04141e11698103001f420a1030b02e280300041c1140c14040901420702407840407295489000b4000d04000b024040c00782c41100c05949807880c0c540341c00b402103210311902408042011300309045004d004a5014050510b151907505000c0310012581208034110300c0200001c00f4151554003c00c40441d20a44000c1024200f606d4140c9d2070250061000046501100c20141056000700c69145055940c0c41284542d444140c035540642c4990303540305c6040d40c1403807002030b6030410000050081b203800590154407450340c40300caa50754001036102240041d201c64824820040c180d800007403100d076440801104003040002150a444040300c2007142c0b8690400100c0b8026014803003030842442032101003012500c030281d02040c10215400c0841480651440a42d10341d0040802600091111080b641c8450361001d1381e4007640f5049070114001c10320840c0c007840365402051212440a03c80d0051800e5039 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 692843255 1250 692842005 692842027
    0x2d1810140f0a02070b18090a090602270414010501210203011e060c0222091203061a04030218040212011109011d0a140d0b01080606041b050403030c1401050a0e0105010812 75
    0x25003d403110300d23030903a00d17501c507c001112480103000d0710130705203a9a5a10241801c4075000f442362400f5060046007044540d0b160540c032441706170306584d02400c006001760b8150b255141c9001000d80900c3c00b85100000100c0c0242c201c40130108400201e60140b1103c030b4a500040301d81160ba108000e401c0343e1543d0312488a4004c60041c40c0407817140c04000101c80700c158407032913100c034070600240020940d5003c3c240401d2404840c400e03850f400414183c0d28062455020900d0085031b1440580b070203140c1c03004501107541d4143c0740740c9440b092100910481d5110440310384168412883d2138003181c2925015095201100d621100040000b441c116050346082c2100340040038003016243d00203201003120000400714409d4231701a00c40d030802030085140c000240701c100d13102031008001c4514000b0000c1d546661000c21034003540e5240c0b4084501c45440d281c01c1032015030002554103654200000c225204016601c40e0f0720b0001c140300240107a0341c0c0c803007881e91500c83c1e0391030784818110104170000c402 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 692844505 1250 692843255 692843269
    0x50f030c120a032406080604091a04110607031115010e0f040606090e0105060a1212050d15060c030f051e130b2d1810140f0a02070b18 59
    0x102c403800c01003100d00d00910550f54070302c06441e034000700072114403051049a1340310310055440542a030f000c2180c1c0d84030b0344850003180203101100c03042020400010701001a03d083d88900c00102034100c94036242c103850040d101d4143c40b04000310340e1144440840c502601c590a890403508152a45103203902c0da04141110424010010703290b154640c840016012780c540b0590302264940c0c000000c0c03a007000000c01c0081c3c01903a02000c0381203e000c40d0000030480d80b4101d08400403843c184513030344160300e030025000b84c80d03880352801d000d8800490000b200d9401001c95034030103109039030315141026801c4003a64180a1681c03111100f03500420301419281c00e4a00070324942c900030f011444825600c0452400035808010039628510200e15000441c8840002a10350460002116801c4c41c0711180001d44504040703860038440d80c0001c52505032030b4011104805c05030001d5100350780c5d40d20008101c4031154420341081b001441840400035403540140e0550744e120f003808583d4404800100104140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 692845755 1250 692844505 692844517
    0x11070803041b081b01020f0d02030a0807110601260d0f0e011205090c030f01020a0f050306191401180f0510110105070f03050609060d081312050604050f030c12 70
    0x2d1101c00003400b0661500c200132642840c0454260520442000400241400d4040340422925400114036012280e004402e50b030310703213900703140084507136035a00002ca420504e00c08260606006000010681191208100c0403400080d1b034081c0000101e02003441e5541c051030f250200259098400096440c4201d4450003400f50524041440c181c03401da1a800b2691309403602c25065005080d1400b05050a004c101c9582c0b60f041d0003141403445a95021f803111281c0e4840d00c08110002000481036643d401d90342c88142c4c07010710b0040d0800e0300d44100049610800a60502003039401c2101c04610f5a181809400d036050101007883e0706140c01c083c0b1a680e1000c00045052040b01044114555024412584185000c1eaa0043d940e41041c0c4040c4c1222409402c950040d0001710800120f0b0311808694221668801003aa0f030f1045010042c14070740c1015000580380004800c2d07001d0a0240005415004601450139034148e1108041207564a225075801e011144d003044032600035a5000c2000b41c40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 692847005 1250 692845755 692845793
    0x10f0c0b1603110c07060206010f0305060609040c080102190e060a09120503190c12110d0f02100c0903020f092e05090c210903040b090a0b0403151107080304 69
    0x500c0800001d40000c076601300d20310154090703001120801c522030741007024900402d00b182410300a9402c644a41da19040c009150312b00680c6c0c8000801c00700f0004031011001012128005c40d160306180c2031500c406240148001c002440b003540f450f080d8500b150807140b110400b500d60a0409103440340044190b1140c0c0800e0300e4a000c10f0010019403640480c1120f000003440c0c0c1c40b40d04a1030145030400030100f43d40b500c1002c2000314058440e00c0f510005039000500c1c55410070720f6264480340d40484c5400d00401000e55075509003012011441d400a451a09592003114500d1406c00f0728030611071300010403039202400c0014070644405100751b244100d100b458800c1c1250b415962504082031a8400990300941450030020b5103504c0c0030004044c17400900c0c0142c05074507803400c2204a5640e40e00890040440c202740c0095001c14640d00c0c4400b1000a040f540c842c592180d80c1c80c05c1a03910800750342c44812900782401f803c845807101d03110844402d203922480c034a0070343e145ca44408000d81c8070642c1081c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 692848255 1250 692847005 692847011
    0x17101b12090c0f032102150f13060c020a2003070b0d02042102190602030406260702010617030405090c0313060509031306110703060b0a090c0e010f0c0b1603 69
    0x85185041c00d54030f440a54020a1044920485400d4490808840c82459011904625020602803020503402c58000b181000a514242c84160b4640c5203070b601000c00401c51881d144546192b50380100f900c119450042110640004411205882c0e070345480d10003035856000000144403a4076084003404019181110060401e52107942e9101c82240f08034075503092040c0000c0000442c9882d0140c0b050544058050304010341ca0084007a5590150340205800d0200c0750074900c0703c0160f070011506110030070204102c141d00f4a004081d000b04454002c05031503c014401c540e890f2100001158100d80d00070700b20342250390311421800c007182c001a0208928218051380310340441e01c0e0340105406625441e01450381d411504d06a0369025002c0e5010109105074000b502104820218040d8100c1c0d03080040480c4500c000d03030001c1c2404c80b507500640820340c588016161060740c01040c011003188280ca500d2075a0031140d5007540c0d0303840c841c500140b00601200000e000c52084111200110140c0c0c01c002c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 692849505 1250 692848255 692848259
    0x211e01111209070f060315081506090603030c0106170715050405010c060b130b0f01021f0b1f02010c080a0203060d0f0602042309010504110307080c0417101b12090c 72
    0x200c1c05090f070b9603000c100003c0d1647c0c0d13003154488070000c8400081681c840101118402c580c0080d51380c6c4c0c40100710030300c1041c1910001d0038641b828800c40d6261091031000700602600ca00d8a0051398004001342603040c0f01c0c258011410380d9400400d045980c84503140d86007020b00c0c01004440b003e118144c1101d1507074a402d054501c903110b00d811500d144228080200c1c08007184002d004540e411910b015045501a4800f4105003038021140807900e540c10101180055902c40440c0715410724090000543c91030004944403c4c0d4103620000c0e00f0a81d503a500c60481e01c61018800682c0019035a042d03011484440240010388942c0307405d81080d100310009800d00d0f0f900e03c0144030320003240c24501d200726048070300b80e0010300d014402d050140100300d13020049907110180100150000503c0c6206102d01d0a02080700c1544403001d80b001018025014100301c0c51003800b494503100c0302040b40e003807241040300855038100382000c603820b841015560b80e94040005603941020380109034045e16803610207200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 692850755 1250 692849505 692849519
    0x506010504121203110a0e030c030309011b050a021f03050108070605030703050711100207021306030b060d140316060e0c2d03030c1c0801030809010e211e0111120907 73
    0xc1d12004a0702e84441f403401c003221051606060f01090618071942013003040f031300c4580c0c00045400d001000320b118196070400a01d03240e40b40c91003070716019500c49a228118105000c0200401090000d580d50901103641d03a0742c0320176030300c00f03450040c0404a1020710000c1d00952203030380000d51164076841d01002048442040d45e0602d81001c86134004550002100c8055003004204005004035004d03040100074959114a00031f00c0000d026140301d03190006080042c041d86042c00e011418403441a00c0e601d041486050000002c8101b04694040c185a1000042a40800c51a4441d00c014010071003000013408180410000200b00b404075043d284075000301d9860410180056600c0d1100400c2407007c0c8042041e075150742e000710700040140c100e00510000b07071031500361900e45100f0308041030241110000951b403d00310b0020b41c440003140300d804032212200041c800203251004560b400c00401d40340882c2d03003a520001803150200f80100300e19580c210b48501190741c0010303010309550f141034039a01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 692852005 1250 692850755 692850757
    0xe03150403021e06090706030b060708031314030903121e031003051e0c060f070206070c03150e0601210803090c030106060905093610050601050412120311 68
    0x40d00350010fa0242ca60b518004401c0e8600386504100e24008043c14030304242c2c803950b2803c940c05208200b43c0c0b03170301680c007094540c0801e98840d150302c8100c50381c807440c0542441403c4000040d09840c0301000b40e0240700403501c04800c4984012019000d8651100c801c49a5851940010188001c018407101044021a003600c06140140c1c51181c00141417403450400310b10344000c42e6a1907140680d10205000714100002c4c45801c0818195081c98581e8980c00440000d4001c0140c0030f504101d0000380241041400c0d103040e820b03284150b0015902602c00d0000b6802c4a2903461202016440320005214924406d0708040741303125031002c1c007940200d036a5101030143d001a10728126960080200d00032a00e0280524070240c9420302c0e200c145a403800740021201c0002030403220b840d8001132103601440f42910f03551148100501c0c0c0002106010100090b618498440c44030b920758600004200c0b1036205101700e0381203550081000301c8034a600d840b018203004040c80c80700107055036201c2c422641c0d00444 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 692853255 1250 692852005 692852011
    0x405030307050f25031401181b080c0604091109031f060b1c021b030f040303031103010515160b0f181c030c03152601090b070e0315 58
    0x44080d01e0000b10690140d49400c0e91349941e507000040070704070b40c90b03107040b84414901101d0b00a00841c41402c01000990b0041010001c2450707208511112142884090010300f10070700000f140c1500d001e540d42c1025a1950320401465038009010082004036a8498101d00e0308500543c0761645006200c0c00000d01c1c050b074188808404102c040da040c418101c139031044034000d11006421a241c443e420005c10509501c1200d0300c14080d41c0403403242901e0758840c50000001c1c046000312543d509190106154540103480708400103403c00f144448055881026a4100d50b0301070148100c40001400700c0b44140c0085202120100c0c2c80015000030818100c8540d0283c4002ea040c80321500f498001100c56680e41082080d90354042c51003c06024642c000004070714050340b90000c0d131440242c100714043c00e07002e16204050204404046107403150b128003200084902510f0810104400c4a070a0a03a10104405000c881b070103070009801070b005030714566003800000c00350b41c046003e00502d051095815 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 692854505 1250 692853255 692853263
    0x8220309080d0314090601050d060207111810090207080409270b10120201020616090302030307060606030c1706060918130b07020102040521010219050307030f02030f041103030405030307 82
    0x204c1d010110741e800003c41c0e80d0007040e0440a0285581014080740a200c1d1820004100135400581c00c014070041c1c8201501004000340350011610402404846000c802d4480c6032803420080030024414240e413080300e0f00561f0013209181071a140180500040080c044070140400055046102c1e49400e090080e4150344154011201e50402e01d0305e050f0703001e100360070501954030f511a2160150703800090b69584951051a01da11004440f031049644481d280d1000350148000f06600c020807006401203402c1d2003555504100d420883c0d0700884000c3d19800703401c10394203c0e410101e000e0b8200320008180090f4090900d0a041c0030070881c08a25174411101040d0b03890180d255482045526040e181d04949244000d6040c03505000000d03824400c00300d180105c40013000d21000300c600b000e4041c0c0e80c7d000111032841c070510707950303050182060303108440b13440c00a4604184000d004c0400e20a90b40031b5000748140300801c0d43d44e6a2a400c44445041c1d03207a80c10305c818400001c2c140d50800c001d159051003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 692855755 1250 692854505 692854511
    0x4210501050604020703080a090309080d0804051513080c0a021005090307061404140315090a030e0901030305030106030b15040b040504051630060b04060f08220309080d03 75
    0x54100a421100003802c200d201d01d00402900001c41d81c000c1e03229400282e18000001c1d01011842c0580d100c111643c006803260040d02c50700503529401682e00ba200720301070f005a07521030090119079051640100c4070105102d00403104000400d5021002d0419458207900b15800c1000303580005181c02c1e000841b00b000244002400c4d6180e00342440480020003071410202010454100c1403900c5020718002c03400d50040070703181c2811540d41041540c400c00314000481c90035003042c40ba8039456010902c0c0644c00b141d120540c504140c105412980d040329090341e140d03800c40c3d003001c200300c0c041c1c1034000f0f602d0782c030100300c4070140c2c03628400d4001000102003040c84190780d60b252206200c02e41d10018070141c0c4040c07080046680380c83e0000802402e8040085801c0440045c020b8080010b070115015810321619040010902420070002001503c4c1c00340c8840c000050507510071140700380f003100d2900512440485102c0d0201c00700040c161000e2003420882440e40d160b0719550310340b1002d840440b001a403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 692857005 1250 692855755 692855819
    0x1317030a02042d05010e01170a02040302100e0d23060702060106020706030908070f080c0102040e01051e10052a0a2d0f02041413060b102304 62
    0x804402d21015282d265002111a0500783d00c1100300308600703102e00b5040c80101030583c0f03040d81c8102207215079100c043e00700703003a141404054200250498001280a00f560ac501a0241c0c0c1c0039466070b8214240c01040c21143d0500d55603819600100207983e4404401c3d4101907449001d014000d4500c0f81c040b0354024031183d894481300924102041d803000c028145410b13400c0011614030707411900d1207501300d407030203412100902c0c003001244105010000607502c0828081241c80c00c1c01249030480b001240c4607409840311291581400b61020031090348802e48a2001000c54050300c0900104140c2d0450307800300031225031074518244100e1404240381d820030050107040104160600c80142c84601c2d980d0009029400c00500104032080c016046180c0590004215902c5400003400204140c464048a042c000410001c05074050011510542400b043c4502801c1142e400c991050030740e500d01c0200c0315190340000c0070b21440090b8440303054007040086410080c4e03e040020025480e04012407400b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 692858255 1250 692857005 692857019
    0x60c08070305013c120b1b09061602040f090521031006030e0309120d0e03010e030f0c0102070c031a22021207050a061106010f0308031317030a0204 65
    0x30310141c04c50100529041804400d08039101a04150540d40d03401c6070718426005401c07040c500810381c3c40700410504100c501d02c100001e01d00c0b850f0003a008815100041408254240307001e0145a01154001d0320600c48401003d03849146801400d0000c1c00005082144c0400d000944102ca10103585a81c410015001a0340100055000c010007a410490447c02c281003195216016403254a04154658110400ca044240120303010660000e1403904000c0c100006151100c14884039070011440038001d13180d69003010301031303200741a0203c000b031450901c14922502058000d03202d00441590301307000c5031000420110043d40590f00070351522041ea2940f240c3c0864901d0001d02e080c000706e65508200403c2031280c10380403802e07981180c882c54030b110007000680c81c02201d6400550320005110001440300e82015240c1148450603046d6880f684e21101010205141132100078a50344080002032031040f0300842a481c42c40c4650701c04000e9140580421036a50400e803080c0c2001540042c04000034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 692859505 1250 692858255 692858261
    0x110a0207050f0a1e051e032109010315050d0f051207020d1106070c060905040c030b03060408090604030503180f011b030809010b130204090b06031306020a0c060c080703 74
    0x5100c01c859800c6000044004140054114030610b0707010018000c0c424455264011004c0c003a000c00703081d032180c0710900c2d0050225a4000c50f115070003400307000201807488c140d40d00004602010118100c0c9001d42c040c004400810307420324882c0289601180106060351905050300407a40105100030b50100c850030a0b5080001503156111828020010600140ca0340c18801c01c4030360b000865505440120004074181d84183e076001007d00d00d00d00804515a034005c14007070180c0c0c800f035404000e03a1001034415000c40d10b07a40131441e416485500000d0000d407032007000303013915000034101500703040e50b0303640b454030750781081111106091110900ca10b081c14991880040b0200c2460100041100c13142c101000b6512030801a00f0840300c540060003000094001018800010303004020328546003100360020740150180a80890820015001e1071800340b0030380b4050080e20a030f03414031428598810703000f503000c2075841080c0300840800801042151040b01c094820343d40f260105840c00080003022 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 692860755 1250 692859505 692859509
    0x311030d062903090619022503080618010b09040605120106051801230402090d050606031203070816030f0f090c05040c0509010806211506010801210f06110a0207 71
    0x4007110500070014013250005041c0c0d00500c1084100041143d07150801010b0300c5030344904100c52030300d00d00c1d140f401c001c40101c0480850195882d04040d071a1401008201e0711212148400c88007108018071601d20703858000c0840150081c00010081c4c3c0c1c48010a01c0100c1400851060ba527541c8020041d0381804174003000b403003000e040400200e40c101100100080b484601c080d46124034041d6001640d21664120380c11240300411950705101c1600d03003a5a41c43d8212402030207402105841c00b2429001e9060b20b000762400d4440c205695512030228030b02015400c0c0d841c04040e103a03030402d90004114070520035502c2d41a8000303d140c0000c1c1c03d00715a00030b0640c1c0240d01803480e1880042c0079aa0043c16280c5001c42403810101030340b150300001c0d00158100d402c4130300f419074008036121001b0000a0b94034428070b4a044030741d01682c0301401990f005e0000d100e110075072000f252010400d2080414003d40135407003100d80c1c90514509072600303000c48066000420b014940020381a0401c3e8041040c200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 692862005 1250 692860755 692860829
    0x30f070302091c02010c050f0304080f0304030201021207060609050a0b040b0d0b01120812011e0821030910050702070f05091e0603030720120312040311030d06 70
    0x80b030a000342d404500094014101d02d80f40c040e84008001c110ba203c0c1019840c1b040c3c000301151150031110f800642c90b50302c18440d00304103228440130908001d070040107403000c6940580103848484200140c0740c0311b135070201d0130450344a943c3d030030041100300040c8242d5019582595000602d40503d60601c8104c2d610412a180300705480031404d00050790300c0c0c1d40107041d68003402415003035110510700500207001c1c800200c03541040c00c84c004505104003070701404d0004000070302c80500642e0394200e1703a12909030400084905c0356031403c2d000303944902401107810010388006c0380d900d5202030342c4910031550141c440c0b40058208003010008500e50311a103038040c1c401260710030320b80d007444070382c02c00101c0c030310110f9110744480000022204c0d40c2c140199030006400211b40421401001c4032420b501d9000180180705060000742401c0d01140041a96811400c01c030b583c1c00c041e15107440c2901ea1a00c00542c80000d84010843c942880b0540d00402c0000d06200d0b0745003a0341e440b030803030351003503283c1d07070344d4680 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 692863255 1250 692862005 692862007
    0x20f16030c0617060616020d06050a06121a220c05010906050f03130503070512040e0711060a051032030319080601180e040311010c0905041104090e03030f070302 71
    0x55006803140c28151300704500301c0d50b40f0f07a0380040e000001c0100e0450030000e54801d032825a59018881c00f41c110b0b13840750780602c00400c440c0e80c407a8042e10712190b04140c040c02d61182c10b00e8680341c1210b4003002c5d40d0400c4501e4054080c1000303501070418055607410040300c8811f80075504202550300a048000640b02e40d081032410100320307040003240c40c0002040341030724652540d000d40a001c010300450b000d80d500a41500d25401012003c01065802407160301c00e00802d110028461600c501c0c403138465031415501401d80f5885100035034020301005040081c1d0011021700c00514115401c031883c0e241c44070000302d02c004035010311340320032900e003038070f029034040d40003040740c03581900007030010303010000507800d01c0d48040d103500c1e0040301c8604540003198080d4554000210300c1c0d6201e040c01ca44202e00c40e46e100080e1848507003500d070a913511241040d01056142c00280302524042d0056140d03070524aa480e428a41d41d00710940c140d0712071442e000015080001441280c42a18892942c030403c242019 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 692864505 1250 692863255 692863277
    0x4050a1502043b0907060f02010506011d03120c1f0510062106030309080606102307080a080f220314090301090c21120305040201020f16030c06 63
    0x5070f1031504085000d81051070746500328000441240c0d0a4030104002c03c603101440c9080c07040141d4405040c0240c0c004114031169100e0590320500903180314060694070460364518885680e601683d556207000d5242c065806440b00c0100c3d01000f802025001c400242810842582000704000c1d1464024140604280c1005000103600c01c80100b01c800c50f02e85030409001c010000350301e100c8055100031590742011800010300d944100040f058505840a444480d1506402c010799024158601d43c085010121100780b01d41601d001d12200c9240310101614001141e0344480c002d5103e00c60202c00304209005026803080c46182c4954000c020b00c0d0804620030714100c0350b8850143c5898020704009101400c400030b800500b050b100900c201600a10a020551a01032044001c030b025842c80e103008100c2070300401d4401c6032007000380d0340c00100c034141311000d4041c118083c01004000b6030640c070503072044510a01081004030351a41520150032038144c10742c501422800b8641e0b201c2c404200da20500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 692865755 1250 692864505 692864519
    0x10504020f060703050408070803030604060b191404030605040602031812030402090604060506160308070e0d0b0c041a040501020c040903170414010e1b03031e2104050a150204 77
    0x4581800c0000b00d50b1140c480303d03d0302c0d084900c0e119070742081c429402090700008801c140000a9402443c0c11a020710000d500e8240513102400f404e241710148064200e40d1007400341c01450302c1c0114035070307001c00c55180c1030310f030b480d1071069440c00c2d101158125800010002c00380320803590241100014006482e4000c9200c0c1584420701002e031002c6d20030b134071540110b074003551254041d5001b41030141c1400d884082d01944040c50708803846054020651300c0d000914540e214810403204141c004018207020105502d403512502c1c001800321041c01401c000c0891001d6070103150300a18030103014501c0c1c3d00c0303061000082c140a10103e42c64000ca00b07004180000075040004e1014180d0b45c07241400d800d655609284130151a000d5614159500c0c0100c0b1608008004c0b8085090340d1544413410f0b00e4040c80f5040c15528460000980b0f0165450741da020a0601c41c20010f185c1c4110701e4000e04001d2104040c3d00d100814281c034110365a84c0040a40b0041081c820b258580c01000703000d04500b840e10b0002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 692867005 1250 692865755 692865769
    0x213050f1903080c101404030206093c0a0c08070503030a120905010605042903060c0307050f070204181a01030809300703021201020703021209130504030207051201050402 75
    0x10b007221408075141d800d04e41e003000a02400c5c0020501488604132003041205207440c00d88050b00140100c2002440e074140010f00c129081e82940310769884000e08600c0c40e0100540f6039540780340030300940300b07400e002e41c0108003c00c1c01c640611480360296203030440341464170005d94049130103034000f4030081c0e5031250450203a07658117003078240c0801c1000291502e01e00400340340c0c0140350700900d000c0305038110f00c4513007075510442c8000201c0000042c80480c10180e84640459040d080d0581c20000244a01c1c8100058417005581803010750814019500180640742c1e02e0115a004e10a100141c0c400d00000000700303044d107e200c1000d180e03994115112140a4805c2c0c1e0401c501440040c90f10a500030680540c05010306400090388440070807503c050340e100c210300e12040c1d2140890b949884510801842114a065850b4004081d0401c018001042c10380108207400ea201c000407850402c215924050944140e120742c0c081c04055090204000302c100c02101c08034900da140204020040e181c0704 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 692868255 1250 692867005 692867009
    0x303070c030210140a0f06031e1b081614010210051b03042001080f0f040f0516090606020706080f060402040503030a0c290f0603100213050f19 63
    0x40340081480c081810142d1410b01c80d402500c944500d81154034420421303c00e803507402001030b5075060010441515482096622a02018240191074100a007216480c08045224184075042c015100300345070614516565455100d603000760003000400d02c00e101c0e0901403102400c07d1101280d961a100301c0001d59030031317400c2004021281c2e00c4000c2112040b4404004280415500c0781981c1d03858140346c20540354074662260652290030079452005507028009240c880c1d088400283c072959500700c030202d00c01201034020f6444800300794244e801303d142400f0300c0c0c800400034011030078140d10300708d8680100c031042d80c421400c64100c0c00e000d2100550041400f41c200521032020401d50715000c0c0060001c0c81117500540c2c0c94480040c0d0450900c2d005a05411490300940d4084514868a42920802c0760380c076480d0500c58091000044014404d40c040e5030304114003030111849020344e019210100c6c0e010080564002d41c0d01c40e0100114a0200c070a405d052006561074000c0c0c410b070568a0540c1100c81c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 692869505 1250 692868255 692868257
    0x6030905150a06080106080c0a12080d0207060615180b0c07061409030102071a1e13030e0a091a03010204062f0601060305061305010b091c1a0702160503030307 70
    0x941c0110303512407101e0304504050405030b0002c101403a622030340642d0360801518224019042c802c8009a07500c1a0b902040c01241c0241c1d260b072409001001500080d400000c0448030381c0c1d59000080341c9408820086c5140720896140c1a44160501168550055081d0b0000b00500010000300e00704040106221003204c2d6981008800c1c034106152012450161000c00b81e010343c0701181400501c101881030031100e052043e0800f00d42d0300c071158914030384016442e080c0011541d100c0810003450b201c402816016009250103104010314000050109005910801410303883c5c64681400d0b210200f0400f02c0400d00700c008620b4107250010280898880c45104900e400542c51002c1042034108481e02c140c0e8070840c00e0320a1584c42d000f01600400041d603909015042d0110014004141481380c94140c4400d100345d1070800c2c00c61805c01585500c03801d80b41c800e002819000c0b40005400d010141903900031368007103070120301d405800245041c01d41c1a81c0844288804010011900c011044039000016 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 692870755 1250 692869505 692869543
    0x1a0a0306030c06120b03012c010603020303070c0e101a07020f040603080406020c0906090f0c070f030518030307020a03170f0712031b090b09010522090c0c0b060409051203130c06030905 81
    0x10142340500400c0903610103501804009440ba0411410004140036941c180400a03601c2d1210000380c401e03031030a4042c0102c000b940c0c4681c0031510320154050500148010400c010035400d10002c1025104194001c0700c2620001c01e05109240c5c05000118a902058400e843c0c070f4502280002c000c0d0700058401d60290206001003510300d080380c42280c024070b4004d03000358055140c2d440d0040180c0d00807002c6003c40c0f50100001c0700b8a190200445c0d11194000345004c154a0030f5171600f091013000c681402034642d8042080c41c81240c1100c000c2c1c681c40340208481c114034540b009024060720040103095903020701c081d41002005400412083c1580e04220605c0d407140c00140060f00c2a10500c0100c040400b6108102c901072030610001c181a00e01145d0240500696180191040421164000c24080c0b010000070036074101075204140141c007880448141c411498091000c6600607a4282e01140c160602c00052003410b410420003400240390400c8002c1c55502c0d480d89030100c402c114008001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 692872005 1250 692870755 692870831
    0x90e0a06061a1b150f040501050705030415110919091a09071b0204060915052d030109020607050a0c0b030c07020103050907150e13061a0a0306030c06120b0301 70
    0x1504000c1c501d54810000d00d06001340c1041410416554000c03107003120150300f400e0018040078401d0701541d00550707209061030b0000b00c41e002804040d1101d05003034a26504240042c480503625001e000042c21002c0e660080010706002c07404041c1c1710804d03140c1e00e03494010007008440e922240c80c80c030760040da00c2c90b050724040300d194922003004d1411140a5442401d14034046110702d00365100d5101524203803240c07500c944d0b0b07560078845103c09903a000e0640801d01d94507020200c041e110b80040080004000152904069000500e00d420460040d152544a00f0301803040090340c228001c043d1007100c00442c218a42490000e030940b1a401d002030401d502c4a011820842c000c01204014188072541002407558440b0020803d0303001404140c40f0326000744101c038007150381e0320421095900e2030380c040d01c08000101c1407080e80d90042c3d03004002c26545a40c00004215000e0188010b0400b0360b03a140340030344c8080c42070700681c5c00076800c041c800c2e45050030103143e403c026031060f0303040c4845c0281002c1e544 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 692873255 1250 692872005 692872057
    0x11202011b021e131406120304080f0309030712050d0e130c02030d0b0d0b010303080405031201080304050109060809070e0a090b190c210f0204090e0a06061a 69
    0xc0e01e0107200940000c010320700900e400441c0c1440e040c43d500103981034030280c0304142405007039400b800040c000026107000414a2810b1800b102d40c0c1424142044030724050303461500070f2902840030501d88564001251111148c5003e0003000c000301402120030000c0316160b25200e44480441220000f800f040d01c00046040e2a004207403500c540804100b0407001d08400301c0030351282c1c0071506682e5818540501441249042541c845005820281100040c4c1c00c5a509860048003c0c10940e400d10050103080140485032034154040c100100256444614207400989107001030341146007440690b10030400d07500f5002500c0b40490303011703030342a002039168200040014907800001031b1015030400c003041234020401c5e03a02c621806003500c0c200001c0148580442d50303440a10082804210720101d00b280e0580360360091740e40f00844900040c0b4080e40c5d140f16004850140c0384880854000c0f00c4c40030107120492180c1001004400d840305142c0801098078180e61080c103c907030705880c2c1925943d000007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 692874505 1250 692873255 692873297
    0x6120705130b070c0e1e0c03041e0303060311060c1b06040b0f03102103080718080606150313140102090627040603110418020a06032301120201 63
    0x10b2240c282455520303481414400060907941c0184c81e890260070000c42c140001c00c46c103c52042030111003ea405441d01e01c03402c1115170003c2c005407200c0900708143c4e038801b1091920512014881e40f00010443c0c594688074040d82c000c540e42c64441e5005200c2a6131032031010030210880114804100c440040f040e001070030314020f94200500c03000740841d01b07000c41240c07003006600520070920ae440341c0381d135102104141003081100620100c01041c01c40c0d00000d009014407900010380e82001d001000700d02d01c1c1c1d202c0c540180d60240d07a55a200380288522810310b508203005104460310002d26611f0b1032101e12400d2100f1800050608180900c1556409800c1d41036132621074008101958540e40e54081d044010402e60607090744201c14003011080b460144035000c1200e0b885100f400e10f0700e100408210081540400300709011031640c040a0041c0d031500c140101a148649000840d00100c010075001000d80c0c000b0b501807000d626006000c00402c80b4002e40207c0d509180c444200c0c00140941d0b200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 692875755 1250 692874505 692874509
    0xc090c121e0b0604050a1503020f0307050304061b022814011b020c010e01110a0501050a020a020d0905061210090c0504050108092b030603200f0612070513 68
    0x14a51a081e1070000d08240703441d26040c01a034849052102c05681420001248203500c5260740c055108102001643d07100d480501c0701e21000c0c1801030900158024882c100d0344101d90314000140300108101c02c110985c8119420700c400120b441460b8152100040d55070148040e000207030b01c3c210040d40c81e2a50140e0b0b807004031380e5403203020b01001d440f400e404035021b46659152070102009003980040d150348000303040078075075005035620242540342c80019918842c1c03004644005004545100001c51024000c682c013902d84c5180c0166240d001e044001e082140c200c030b9170020030a10140822865444d20140c13079000180500c129156224043c0301d5040380c1d100d50058001d203080c080e074100341c190040050801c9400c280c842c0c90f0150b440e1b581860312205180680408200094204104000050384a0b030300300d0098100021544d481e501d8642d4668169401d1200740400c40029100b241004258055225001d413011814010a2810080036810040101e400c01c030300810100b814281d26401c586c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 692877005 1250 692875755 692875787
    0x15041107060f090b06150d05062d01030f090503040b0d02041d0f22060b280f050d050d050c1c080f010812090112060506160501050906040c090c 63
    0x1080c45040b0365020050605842c0035500d111000000800b80e0814076120b0240c0d0440803800c51070000c60700440c034018040603000581081e40003584000751031045e031040007070444610000880e54a074000050650f0b10026200c164141070000340d1b400220000140c805a0306040f40064982c040703218030f00000e016542c86420385105000150148100501151b8020445841c51110316034442644507050400c4401f26084a05001e2040012030210381c4400c04107075008216a002c05040742c4488025082e240a2050ba02c1c9420801c1002002100307511006000031340d00c0006031a401c1e2a4652180b100804040a11200203070200c4207503000d016030030545104000c1e852000e50411401400c43c241102d28011820064001041d600400100c0c160341c01c074140705862418582c0001110484100602121500d8440c200410f0b10b50b20355024040120310356481449890b100e08200b801e450003c1c0543d501a00b006080c0b1011446002020f01034400c0b607100400c0c0d41582e0781045400d030b070800560392 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 692878255 1250 692877005 692877011
    0x60708070f031202090901060e22060501020714030307030c211707020106180c0302040509040501020a1412010b030603030c060403020607111203011a07060f05040b07081504110706 79
    0x1420001015101e2002034000e5407009194021144010124800e040070700d94000460401005054850f55010031003a0000d4054061b0303090176000c0301241c0100d801052101911064140695641000b40c04002c0c2100c0c100c1c10a03100300312020a80742d110301d01001c2d0030050707407590b11003d1000c94a841c07851007415034188011222100002400c01641c0382d85516204804404030380110b05c1402070340b007075500c40d280c50040700c180ca06d5080b0013010864000c0081c07540a100000f11a92401c0c9004d10031405140050703540c2100c0d00c001071110604500d59130380c2ca0014044001501e105942d503d043d03034074155030503543e900d070100064a1400760f40240f01c40c3d845024100400c0582c04504207029840c1915003071800c032001c142e13003074840d004508a074800d83c00c24401000000302d51b10425074441e1014861624201d42d42d00c3d031505035003030001c0d8800302a44135400e0008011126520039805545854000901d00381084020001810260260310840e101c003500c1805809080440780c0780c6a11103810 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 692879505 1250 692878255 692878267
    0x50f03160b030403031107050c30030a030c090b0a0f0e030d1809142205030f041a0703021b0a1e140904030807030c02030d380604030809060708 63
    0x100c0760307038011242100000e0500c56845001c11843c000d075624958024041d2100407080402c1c06a900305090360b039420030781c80d10614003041000410010440c40b0318400f556883e002c1500280503620308820440c100081160100140081304084e41c500030601d00c0c0058900f0320700031048442d0404102d04030b0381400342e010404c0c80ca84d00070140410007190703500229000c540d01c00860040b1400000c81410603030007032000a007044540310b031400e81c1c20804119080d1100e86511810f00d15000620b20381d20310480060309101d0244950b0700e09104144a411861400d51240e400035102e102c01c0c5591014201d841010040b00d135101511700c0080c2100d14030780c004401440001c0850f07404140b00f14500c8481d810000407003410074000c140c1c4100c3d016101d502c282e0311848000c070000c001242100702140428841e094440700c2c0e074011078030701148580388071100b42e140014402c602c40c0d04100c000380704691020088070740e4845900707a80c104d98100c20b480746c440d2122000f05d503852180c02d0008040590025407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 692880755 1250 692879505 692879519
    0x2070606060e010e0321070f0506090303181c050c120a1215260a0f030801050f0d03020d121b0201091703190c0309050d0e15030f01050f0316 62
    0x200c0001d5100907030307490200110490925803031ba0607000e00c00d071144c0051032800c891a2140402402990b00c17600348a182c52a180c2c0740c003410f0510940b00028541c10001c14482018905560800b05000c0d0700c0c0504420005810704907803040c500d00d000b81c24814086404088800140400e86500e003030096859920100c00c0c400401403980b04074590300442c0f0303000c0301c0c24140410f61303510003e481d0213551000c80350401c2c1d00028030007a404a60b03445e240c4100440e08000401c40e00d009038200b4400d803902c0f0819418202000341d202404550360380103084a0380408042540004c2e00c806070039640c1071268a019070411000b0140050180321034032122194440e10f14217605510120b60140600c1102d1400d80320482c0b03585d4030b88801d9400328000a51038800d510544665404078480320b486080c0080c12810035907a103401e0400c00100a404940703420303c0e03141d107818039520902c0f241300d44c100c01c1c5185107441e5801c0003200030103001e80340c01103201c2c0b0604c28040c0c60070062841c80a04c4402c4010b15250384620f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 692882005 1250 692880755 692880767
    0x903160602090d140d081b2508130602010b01080703150b1903110712050a03020d0f09050c01140423090405060105010233060f060403080d0b03070e0f09010207060606 73
    0x54044c8621580260040052160504034041e007108038005980703040320000c10509420403140201042c900c1402c819040c101c107490152401d110341501c0d41c4425094180e20804032169101c541964106804018540c0e4410b010660104642c100041c5282c4405082d482d44402d135001481c14040001d05961403034070070804806070b00500d590030b219480c006580c0e0711143c02000b0b8010031102d40002a6020a80074401400c4100360a00e4018140458a200e28007600c61381c00e0351098140da2001c402c010b011050020303640c05c61003801c00e854000c840c20b40e42c1c28540725901c20902da214038006116005140d0070701e40204820010041c0304035007000c0c18143d850f18028030070103007d48a41d4140115000004140d0203071505004901c0d21201350140481604280091903030b64440c0c00c0d104c10442566a00c07000d80b02840c06036129a40390402807000000310b996840c2040e1003580001020011038040b920441e500c24901c003241c400580ba01041d40c2d0180c05000c3c0c004120605100c00841e405034040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 692883255 1250 692882005 692882033
    0x50702012d0824030307080c01181101030605040506010905060304230d1106040c150917030a08100e0c07061118011e02121303020a080d12050903160602090d 69
    0x40c03a103008007103e55195101e8500c2e0400e40c1501a0014000c020224a10b03a01418a001e2107400208540303446200e469411207410008550300902c00a03c11246c1d6032600c00c01018203000c2d41c0c00c002d142444000079004c82858811280b0034540040000c0810031900b036402c0d809040e5412203040194030000c40b0ba00c64408106031800107001e402e4054010f400005c0b0036001e250040c07142410309040900d80b811314803001c05800709001440c040000c800c42c0c0c03c04d2840410f154030016540302c000e4414024030700e40002e440c00e9400c80501c8401e04c0407420303c02d4181d4020760709440035a62010140340c401701030680104450041c200c042802d084440d5031404803089118240c0e940d203c204c01c40c50542c150700c8104984440141e005128030806046844000d040c0b400f248143c00d161640d480e40001c0c100c3c0e0346900300c00d08940255202d01c202e140c002c8070b8444000302e80007043c0070a03e4050140d6a40f4005c00301018000e1169000704010f2008544c115405100c000c1c2243c213002d0914100030600284c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 692884505 1250 692883255 692883271
    0x3030703080921090603090f100c02010b010c1101050306240307030c030905070e090312010305011406030a03121d0102070b040516050d080703180806011a070201050702012d08 77
    0xc40c00410001c15400c88241e460030704002c60508000a13201440586e820080504003d4400d6000c0c0d0103460f0010400d15038003082c801408641c1c01c001d010024291403140d03050b50706004103210700200080c2c81031a07000800e207080c80c015803684c0d10034000a6101c4120200381003130710104510003150b0345000004500c2a08030740c80605c00c1c8100200c0480468503881c60180c000d40040030140414030041d001d00307030880c1c01c0c2401c0702c1c2020340d2055450306888080c2d2003150260f54458100100403c1d0031200c6034060002c03009045140d402c0d840143c800040103c914a1040d52041c0d48100b02220702ca1324a82c5c00d862034021900c0f901c882c58280c080e10340644c0e00340c800e449004504820700c602612407109580e4060b2840307520400703c0d914450030ba080707030b041101840b4504c01c2c040c140c603112640f46001030a00c00010318495240090f40c0d0913034080d202c80c030a0042d42c00c0160f4400341c9d07044800c55006980c28a0000c1603200300784210301404151204815032450585001c4070f00302d510a070428010442 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 692885755 1250 692884505 692884513
    0xa2604081014010b03061002010605130603060b0f03060c030619080f07050f130908120403181a0a05090409050601180f020301030c030f031223070216051509030307030809 75
    0xb00101980a607400b407052094150041002580e28213081d4013103210304003240004264261590000342060040300d01d03240000d5919003040040c01a0740c06012110301c0700341c070100000446240400e80f9076400800d40b072030300e0100001285950302e41710f801003003450000000c60000c54540320b040b0307103070040406554a07074481c000c1c001c03076240303030080208156000041905000d0241101910090f00d25591705a800360300521820390b10f900c0c0c5154240c850b0740300b0b0380d1741c241040300005240f83e1001c807030700011100607003004000404200340d021640c200905050154946a2900028024002c0d0020003407841c0a101e00002e494214405521070300203c80300148290104010040200d0000b407002030b0424420030020004a450340610003517060003071522018560500d041202602c15040c85000c120301d01802403900061514086504420140b02802c059070180d040c2c00e460780a01d01a15120711180d69581288000e45d8089510548000d415240c80b407903a414003501000080f1001c0c542401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 692887005 1250 692885755 692885771
    0x603070c1a01060f0c0201030603080c030c1209010801030b040f0606320307030602070c0e040c05130902101107031704030c0e07051c110304110406170a26040810 71
    0x525001201d042e0365041d500c004c42c1056480044400f0700782a00240d0503d5582d5002001103503488009081400d13080004550b541058480369241554120040080314003d02c50640b07240c2e841010380381100d03041402d02e1400e0b2101c3c1000d007003510000e0307401000d40d03103054000107104601d40e140c641e1020090010001510040c2c010b5184000011203282e459000444180300042403a4041c0c15640e0140071510680c2d526039007000c8400308192000d441c0341007440001c00403440d2500151803000c180390820f0018a640b070380802c00356002d1141d00700c14043c040c0c405501800042103400003c541040d4418800104008140129803081c00700341c0d01080700c0000400c9600c140f00000340999061381c5c555181001581d942403003102105107201b52740303444020b68080000014003841c000c0307019140b4140c41c2c1e01140100000c40d842c076441050901c2618400b40400700303002c560030744e100f42c00c441403400443e42e40d41024030501c0c40c1d01c0c4440c4803040104000c15070520009445085002400003040615 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 692888255 1250 692887005 692887043
    0x50106020703150f020f0403030804050c060f07140f01151805011a0f04030609051b0901050105040504050921070b1f051c05030a0c0507050405071713020603070c 71
    0x201da42e00002c0c0c014180b600c21441080c01da54031003c5002903458006042c003148044181d260750003076100303800080411080c4010b029040c0300071050160100e54180c5001400440c01c03041d0301070f03400082c0440d988030104641500c4c052008620030000f8030002c01080c201082064003c00c07141c051600c1c985e005c004800c00c110014414076058803408900b45808500b016034143c20390f0301c02d400010551500b44000800141d45010b9903002510842c040d156904511044406036511850103620554102004011591f04141250140c800940e030100d61076503003a0009260a60001030121181286c0d0074802250403610003034800203114604260b104d80b41c5c00030007070080302080a01070100d442c01400700070078a05a0201030010103410300c9406a0001616203500395007001c1d00032000f10301150b5103903041200c1413003110040c0c007048800300302600789040018034946464904070301008418000c10010303000b5658204800c0d50040ca6541d6034502460700130306807140102c1c00c407944188454070030090 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 692889505 1250 692888255 692888263
    0x50a020d0513021c0f020a09021206010309020919090f050105190b030c0d060e0f010f0e01150e0903162003010b180c120408090a061407021e1008040605010602 70
    0x180c000307118407288600050034002c01d0b0110031041700c0d20303a00c0b0841000161604020000100300040340182c4440300ba09600e61f032000001c040710304040c03808000000690b108180aa08182c18400300d80d00c1c2450700c0b04803001040368140c0602240311800102c0d080010540104d0302c68003a003550304826040704c1242c9000e6035000038003503a05400a42c6000114103200190040c0303039018400c0459414288081181800d0050214501a03511161707080000c51650191700d12120201008100c0301c418100c0c00c0300a41c0040c0101c00c11000c0400115080b00c8041040d03d52240e4640c0c000000240f003450400300f01940f09a100e41d183d072050a4000395845c043c407800b85800009410100c1c107504002e0102c41304e503401031025450000a00140001e84078980c115849075106804560340d903d8107908100c8400950340c030160400010000c05460900040203890129078183c0c0c002c201b4024403488003040100b0b088841e070f084000302452680d050340c0f01c0324060055010740c100700282d0b625010101d8607 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 692890755 1250 692889505 692889541
    0x9061a0102190503030105060901120c081609030b130602120109060e16020303040318121b08010b130f27170f090d0f080406180609060c0b0a0609050a020d05 69
    0x3d83c1003400100b01c0c0d806c180c130083c09060414545401200c0c031580010303049844414007800000c8502040141c550703482d26a100028010b4100700149502d182d030b40c042c0504005001140c010b5444000004011468054a900c45501c51500f6072941c5c42c0d918100090007175220b481c43c0303941e0440214110200642c8003012114059010f075155039507503242500c5200c04503103040c5006003141c0300028a00d160104890b1458465076200d49504480c0c0c41c2c442140d502c2d80c01071211641f41c50b00c0030360950b454620000c50101c6440000c1144001800d0441c01805024800e55040062001c65030203600300b1300d075112101d4895152841e4442080c1e03e022040d009072011801125400c201c584a1840e04190f03c0e400113125001c40c40454071640d40e0242ca603009035200700003244030380c00c1d002e84400702d6504800182c5820b140036200701d40340c100014000a10343c0c02c06400840e80c1c0020956400d01078200c00003419007600d040c01a4100404180700950080c80400c60040c03802c40071543d40c40d1810200783c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 692892005 1250 692890755 692890763
    0x12080a03180c0b03190213140603090a030f020f03120103020102011a0a0501200d021c0c0b01090207080d052d0628090c08060f0f1f0309061a010219 65
    0x10b161803e01260f209582e00182c01010200d030038110083d0014a280010010400718000a4111a15000c50341e01001e42550609206403414420811581000109400038581510300042080e41c026400ea080560048501c03250740400a07501460f25418a82241201c3c400e0303000b00b00c2c403041408003d103c1d00300144620790100c00054104421341c401d8041c0c4031181d0503002030a542011021402d4a000d84060140000d0380014400a030030061000d441240c45405007091001510320380e9540010380b00c1400303101d52140c0c2c04184035061100c40e006443c44100107900400407410280c03191000d028070104030580303500c149480b8581c203401c0b00c0342c0c503405407001801250a010386010400d0710329a802da8074002e021a03011002412410358007601c00000e01e2601c40d05080c0c10132030140240c4100c90798495020380c041e0001d401013038540d1141c011a2902c0c00e404d1841074140c010040f03024210104013700031904100001440780400c503c500e812240907001c9800c80340041a070900203190800d8054 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 692893255 1250 692892005 692892023
    0xb0f070909090b161206121403030103030504091e0c0c050d02280f02090f06310c1823031207080f09180601030b1c02011812080a0318 59
    0x203500b040c8201c1c4400fa00303982c1030400b800b200c2e106001c07104c01c03103449912824010300e81c2007c001c1440b8040c01e034032035805000d1010f140f03598150b850280c4140308a00c00e10350419a140c10000d40740c502040b452501016080c014002d100d414a0003c02044100000b41c9890064a10708032a250000881c1284008400d0341300143c2c4c594420b568070340703001140060760003407644101306005903034901d8800c4c41054035503500740003410a0707802d00400c01041c001c1d41e0007811007048030750441ca4070a1480c0c030074500c90070b1001c518840b8480301150000e1501008200907103104502055001a42016281c0081c07011a880b0a9500e00c3c82050b80d9101885034941084c241040050049a4014001c10b5440008411240742a8001d004124006586600c0c03010114602040c00815a030501480d440c03000203c54011402c0340003c150840380b11000b00082c10700008800440c01c03800c045d42c6840040810510710f51405601c0d003004c0080d5440000390300c00080c54400104041841e030700c00b103030200d604040301c5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 692894505 1250 692893255 692893261
    0x2603040807030b090109080313120807120902120d0e0f0409030504150e19170a0c0b0d09020303070803061507150b010302090d080a030f0218010503130b0f070909090b 73
    0x4a805100600420350310754072084030102064150f1f0055002c2c0720140d24444040c0c02d1740c10704030f950f006024a0f40041021031000c1c488000d80c409078181c200106180d0000e4054194070004880c0da60421181916000e00d614001c1059007000c85940d640d4025100ba02030029860108030882c0c200c0311005000c100e041c0814000c65261480001501646062a4525201600002c4c880300220300140342503039180b4500b4040b05102d00000c4401860900003008141259500c500030441e05001d001c10703587d03010a07078401e0b24409800c1801e9854000d81a80d0341e507400c034240202c91744d20841d0424051034a254848102241c0c1c00c00301d0b42c4680c4c01265401d408690403060034080c20701ca52490b41003640034805080290358000c800c601203485100103640d41ca10317902000d415258088003601c0d00501c103203c20000301c3d6150742040c0e11310900340780c181c1d82c03640d401c0481106800000d10180c581090141000320620b4034403001801241542c440440e11903880094006949008200802049040c004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 692895755 1250 692894505 692894513
    0xb1207020c030a2f180709030f122a03031104120807050106060203251a0f09010b06090d06150b070803011a0c0d140c0109050c04180519060b0a260304080703 69
    0x3c07860b000446c1c4d00d81900c0351a5262030b10141d10002c1181640c01c900031242001006030046181e030714485880300004600d41a5513080300c0030f00d80380c0002505058075060341d00701001400781110060f05542070500919040ca08203c4c5103500b040d00101c409610303081021900314000015103841040401320765801c503d0f6010024440d8981c42e80858a104840790601090404881300350701c104400010603801d46088201242076940404080380158010020a1703040c0e11035408800c80c04d6000500030490809161502d5181c0328035500c401e94408001c11040c0410068000450407600205c0c071a02c90000c0c070f5000740d40c6601c9140e4a4031100e501401c4948045405803480c5408100100c0c030042c1424088903800c0d007034034443e00381103816420590301c102d0685850b1103502d038004214408080c6c0c0c40d80d199074a665803c0d10a4074045200b090407070700800c001e101d400500d050170000c4c1401443c2c0d9603c103a07000d0200c5211103050108400032011207802721001003038404940501d0003e0039081e180d915 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 692897005 1250 692895755 692895799
    0x51308150c1c0204080309100e010c020409050f0102070507030312050c09103005150a180603081803010b04090203101109060705070e07020105010b1207020c030a2f 72
    0x50030503501c00b100000384604201e91014000510590340555542d40c0803008000003030307001c04261003c1c40a80b0880030400d1b6801043c201000c2d90564001450214900349145800204c405008141d80005200d4003004008611f403011a0710030307140c80c0c1d100e9100015003010342d0700496807100800014085d080c40c80c6049070041201c40600d051480680141c84910301c140804034031145041a580e02c1c2e60b00f0039202c1c6105866201c070980e503031100600300a2001402e2240d00b44100084803070180581d03102e448559103c00001d5a000018960b10003a40509035520051800514801c0d4070f801061403140c00d02d8020f400160360300a024002d442003c0300728400501801d0030407416402c003806003518076219600207040682c0510000c01c0340500d00700020001c181300401040c00c6904140041042c841c0c0c070000d0392001200041c807640c140d52058800c901d490b0340004415414812040d10000b40310760221307a80d02c60900b000018048800c4c01d105440144000905150840707619041c41d0740000d02d0407 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 692898255 1250 692897005 692897017
    0x305090307030516020901090e0c0d0203062a040e0f0a05070c0b0a060306020315040516091224060501080703060503031206040902090f0601020105060a030b040b06150406051308150c 80
    0x20b059101c03104c0440d00821a41725091700920340c4617648807145138054008101c181c90082d0120307040d03a4482415804a030b11020b01070f10403a98410307081600c2c2644481048100c29030300011041341d444e03070b40d0741154800821040e01c010036051821404507074411418000c4511030307041500c07a0000c4000c241ea400e0340c48600100b41c048070030f41ea01c03000b10004880b400214000e40c81c0d08591501e89130780e1b43c00c01c000c40d6400b503c1c2c218504200c41010030f015400c4800341c422907061650721841009541019401600310440d900708051040a80c5002d010b02940300340140d85080c0c0e10f0013400d03501c801c0f0950407105103000d403540c554001d000040400303480d40d03140fa502107000b510200c2c1002940c0d005c26880302d000d80703a20a003842030302c0030044556824030a155200d5021039485d094a8656140e00c0b1028001802c050113100ca0000000ea1580340c000800980b008006025944c4941d140700041068000c01d00310030307098800210001d6000300000d404030f03a0030b011340701c0c5c3c03109610b91026450142e8091 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 692899505 1250 692898255 692898277
    0x1d01110d0f0e060c01060305060603030307080a0b150708070512030105301603050d08010e0109020309010e0321010e0126010b0604060504180504031b050325021003050903070305 78
    0x10100342d081a840ea035000d400461020000031620500310710b0b069044c008000c2a80b40aa0700a01c01c011690740e0180302117801401000002841c085480d011400005898245003d01c807800030b0000100015800101805406003040e143d644044130b00d414028402841182d80c485440c8500d10030940d1001d0010081001d60007891003040c210000050030820184841c0703c80c2e9207442c4041041c00018020f01060443c0c2d1311740f04240f90305020824044c800c040c010010603e5022002400d420760942c0a48030403001081140d444120611151082c00c00003e81101282118000087e0324420f00320780a042e00c0110a814201c02c1800c08401007003c3e0549071b038a540d64aa500c40d90141c0c5541c40207001500341e07a17603100d0342d07141800f0140d1030800314540981c2c4250719101c10000429031180034040d44116114840490307040c0d0303003031480c03960148940702c02e510540f005001d400c9a030031100502c8868401d4072001841a2503d10a13011280116031030310003604100401b0000901c42c02c020302d429041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 692900755 1250 692899505 692899517
    0x41403060f0c270a090203040c060f0504172104150c0b130206040b03150a051c15060b0d020c010c110a02090a0906154419031d01110d0f 60
    0x301e0b0f0001145400d0075400900041c0d070000910092040000e42840034000d6804e00c80b20016a2960007044c600c1148640c0301414015003038168038003418030242c0726140d10002d41411942c5058500d5080d94858031902c3d0440d65180010140180030710b140f040d8a580103000d030440c560f02d903252201c40b8070401004a030700410400002c11440c515001550180100c0c11401803541140c1e0140600c0c90950342000784540b181c1d83c0f00101c42200031449a070700a50041c4030684201d21000c12401900da5030f00306050710300d0b021136030915242c1290701802d00d142d5104001d21003c1654941600c90a034900c0b4a05201c0d0000d07958800541003410b005a00961000400105002c0d0303501c800e0126241d01500311400c064080c1d00b00304221100030384a0000c4800e034084a42200d210088910040089400100040184480c0c003150701041c008802c0403180044c603046048958a402056544503504602c0c525a15551040082d489102c050802c039442c5070007411103000c0341d03a05560014640d003c1c1410864 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 692902005 1250 692900755 692900827
    0x703150c1b050616300209210607050f040b0307120f0911030f0709050603030d182009070503060f03010c11100b010c0305070f08041403060f0c 63
    0x70146241c0100c290207036000d030031282000260300c05400c00c800e84183c02c00c5009807140c0c03007842455070880b4504a2010382c036140030112a100c08082e024507807101d5400025010b624140501d441800030b485000b810660b01075640e42c01c01901c05009040c900034261000b0b110500840148100451b04443c03242412034a038000c03440c0d140700b5503211030742d0074a074103860382e0058040140303041d4880e142840071000360601c80240b000080d6507040d00e200b5072407187c1c0c450b00401d1454034148100c4030103400800080c401344040c0e081c074508240b8100411200b07005189103001c0e11204800c402e00c0e002e1700042100243d80c40d0144211742541028125640c0900c2c5405644a6a5401d204400c4410683d449121170072503141c0046e41030144d030f041004041c5040185910f8a60380c0b191041c000c03554035003071068884105052102e42c5c8288001d00800c8840c5c0003c0116600e801071a106000c020118216030055035050342000413a6000d0340c00c4503c8080c00d00080c186441d03180c0b1000b40b500014505504615 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 692903255 1250 692902005 692902037
    0x7170f040504050103200f06031f0302060a021c0f05030f060126011e1409040c0b0c06160507030c0b06030a0807060506030f16030609080c030705010605040e0703150c 73
    0x10f0007079008403140000e449110030481c55040145180340e804444c0030508100880205401e840700511020364507a44042d05001c80411102c008061034001d03240d1904d610344100003135594820503824461590600791103407440c0d4411140c100689205544040c11926040c0d4007460030007014040605000d50703008018070780a03013030149042d009020110070b6500e515100721110f00512100009032084a034034030521101d007240342e50303000110b8180c40040d141d42d0303079041100e8145c0c400d4103c441c00940c001520360b2030100004226029070070030a040348030000d2174641903801e4410f00200802081c0c0e8802948007060004d064181d0022014095038019091917036000d0301c90303102120171101c055441080c81030b641030400c41060094582c40082c035103080c42d10016030401681d8800100304c9502c0d0003000c1e00b0050f520b000c3d2116403c02000301d0391148094a0254040c0c02c05005140c0a2803400218400b0354000007410300c22250000032103081c1050a100306c4021741440ca400c10244404810081070382 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 692904505 1250 692903255 692903261
    0x3080313080c0105042904021c0c080a031b03360e0a06080303040314090315090a120e010c030e030127060c050324040603020907020109031407170f040504 68
    0x104010000050525040c40c04201141821a00c80f203125551200b06c0318005004612680054048070ba031403801c02c1294203161804140240141b00910b034040000d46540002240e1544a01c01e40b1059032400001440b45103c451080002e00002e400c0244000200c000913403d000340700c000e0b01106501a045842da061500071640480c40e01248481040482c03d91072060710b0280034100d020f1450343c209910000c0000b802120325461400001804014543d010821a6661600f25003000c805141400c403441e00c44182c480140c41e1041a80c415005103845050410a40340c4142c5503400741ca581038130102c41100c07902006a4046d07603100062244400c89261000400003910240a18801c16207004019150043c44407410b200c4188184071001035800780711288080d129802118010b51a00054040d10559001941044a031024080c2030f1340e06400403c0356034020340325807200c680045100b180e60b128403000680355000742030a0032180c900100050440c000a684d0f42814a0388840c009021 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 692905755 1250 692904505 692904517
    0x120207030f18031209080105011a09150903070e06040f1b050702030a06051303020d050a05030114040f0c0e0a0806010e070c261c020909040b0601050c010e1011130308031308 76
    0x4a0200001001900306c01d0091a0141018000525406610224591a500444417441d00c501015580901680c900c0d405a03240d40c00002d08480b146aa16510f041402c84160f072054000d0b03041c2401103184d08010302402c00340307003c010849445100c5175002201c0710b4000800803a4503000782e000310404140c0c5805401c0c002c82d40b190042a01031054580a442c1825052003070084c0f010911204181c0e40c0c100c410759044034280209a520120b510000400525800c228803c0c100e00d8680b040000c5a80180c0da0418001c095454010b1940c48040301c0d542c4100c00d1140c1150385540710001098a4420200884868030070304a0241a041c0703555003001a15903201240a4170f40c0c003241307132180c031480c06840000d0364011034000c6280100782008180ca00f64001d01c00307420b42c0d01000103c2c616034810001c0351403c1c010640200a5448444189a210b4080c40310b4044101d0030304180380503010b031080455107001d0000c2c2090041c01e10390f03903881e10344ea080208404802036112407140c000c0750b40701c030003000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 692907005 1250 692905755 692905757
    0x5060f06070c0509060a030503030604090807050307050d0e0f032a03152409060d030e040606091701050702100b0a0f03080a02061006020a0212120c0706120207030f180312 75
    0x2e990341c2030030140190320304010411840b600020104002080000c012603401140030b0b100070800312054284501d07a44613004005003688000038020341030107408034880c1c907013090541e26071840c90101030807c5052002d0b1070800c4d40c507410002401c10000089400040d07100e0b01c0c040060b42c0300b20040006410260304d5641c43c010310b150f910400c410001790030302c1314417025550317100c03152550b1000c40032a841c540014000360007218901000403d0500542c0305140d00200108144092030f144d100c001c0040f5440c2c45029003010040f5003c1d043c40b141070040601c01c1006a00420745003844c003441c00040c1c10610f1256800009807640418900c0d0702c3c4440380701650040105170760301c42203401d0091508200509495002d404168280b1803160702142d076815294040310320300ca0b4042c03100c1515003051035840c1c22085a0900049a140c070f8200490080111582901c80c03100034440a00d00340164490014000c0000c0c07100c050000c00e190282c40d0383d12140410b04a4910319a8581d9a0545406c140060000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 692908255 1250 692907005 692907023
    0x3061504080c012d11060f01120b060102010609020406050d060f1a070c030b010e06031615050c0309091501020d0302070201080604020d021210090b0a050307090222090c03290405060f0607 82
    0x1d202904100a0b0301c0d0442030104c040355080d8544075541e027450741981002442c00710444045a0b4681c400d412150240000d02400c43d03859070794005c060f0003903000e40c43c0420306500700040014040a00c0c1e02030022a80b9041c804040fa02c1030000d100d0440c2d005060442d40c10b07801d4030011003c25408404140070344118480c030000c80c185002090300d40b49000c87c6080d440390948000b80070304080381c903501610380210709002d512900b03411550740c00c5004da40c2040350005000020000400c14040c2c004481030301c20307000d81d030700a140c001d0100c040e0b108076071000c3d0201c4d80180205515040c07580c0201205000c07084014100141e029010300481c0d000d5400101d0441c0b07900080c0144a00d0b0711030074100c0e180841c0e2243c00c0301e203014041380e1201a01e04c501d13005a580414201d0320440b00c42e6100c0e5003543c3d9080c1c0c20310b911362103040410040c29288000700c00a45021041c1c06588215000303040011000004484a000c04ea420800034101c0206102d420005540410655840700005441c009101c0c407140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 692909505 1250 692908255 692908277
    0x30304030318030f1209061e050108031e07080d29010203160602090a0510020106090b01111506060d0207050a14010902010912030507021503061504080c012d 69
    0x3000d035030035440c418404001c0100c2c0600000d40060268440d1000c40c03c0507541030210784600c00051600002c058602c0b4280080102914407034000c0c2441010304040c2000356036211042595240a20304c2d007076002c0032650040009030042c1d40054070001f842080564500584d03000004152007441d804005034900f1603060600342c0c1d84044040358864420f01c000c5041841c0810b80407090070204101916440d400901522142c4604130907101502c8040d019440c00481d00381d000340200318034410061800c0c901403000600d50300c1030780800d149410b804001c26a150000c3c20340d0001070009080307194030080401080984032154009460344900500241440c0519410048002c104541003200e80744d07d001100e00060703070050200780035103402d000d41c03081030550b5250a0b80c5521460001035406070568841c1000000010019449000700340c8800b0b422000030b0ad0b01c041346004070b015000c03140e007140070008819417040d555400007a180740d08208415003d25114400150704040f40c0c03001694020359 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 692910755 1250 692909505 692909507
    0x16140d14100509090c0d0609080703080933070315180b060906030c0307020f03122508010b09010210020a09050108220809130f060503070605040305060106050901021e03030403 77
    0x140400810b015200f070716440c6007104c8001d0703c414030000d440784035600a07000681440f0302603003c0030000307030710080059036040d1a08014148801c202c1c0c4100c02442084032302410080b03079840640c68808480000c0c0785803500c0c4000a010210b00a148108156403255034070119102001c01400800e008080394102d02c0b0184030300301c00e498205075907d0040c002000a0700894941c0811258000e01c04d0340c0103602d94890410803030900c40c13406120915440040b41c41403503400064820390003030b0b20301c080c10400030345690079840340140099401c0e8086035245004000d0304840034002c0032400b605105480c1c1c000d507102480c900b01e1308000795143c0001c0d5004028445940c1240181e90800301c080c0076a0a8103950381e07040f01602c040c026009002280110342e0282c1c6499112842c440f109850344107000400b0403446983c020080f500c10b051007803140341c07000200c10b4081c00032201a01c0d04440a04400e0707003890002c0c1c078035621011005046210305000703c800e0aa4807416026501d040b00080c65427030400f820 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 692912005 1250 692910755 692910781
    0x114010f09140c04050f0a0e04061b0c0f020910030803270316060b0d140a0507120c05040c050906040608160f05071b08100906110316140d14 62
    0x4051a034020b01c0c0001d00c540841e05a0941c0d045410485081c082c0442e1000403803030700e04550b0b0103040501d81c0d4800b4041004003907080a042c090f042116404215107450301150403100407400030340103883e0b03a0f44040c00750810801c1194480800c89034004c05641d60364a040f9258821216038202e10014144010308990025030f03c030011017040b00440c04e082c9003140a24941c091828020100ea41c4d8103560001ca0311203c1314004111b42003800c0c0714000141d148081d0301e4007001c0d8030488032406100310100f144080414440105e0390003c00c01103800e41000240700003844440750640c2808401d120303044a60b912200144080d241550780c20184d400d0560300714072454020340030401401520805146e07000c0d13110007a1102140c02c4404020380910f10718080648420076001600180500c6081c1141500c0e65000200501c2c480e8004005491054800c0741d4036002c00d4400f1482d21841a110300420b134403074000607030a4210711103114075160700d01084030200e070048000000d02004180821030f11ba05044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 692913255 1250 692912005 692912021
    0x302060414060415091703010303030e0c04051302040f020906070f0b0609011d150a0803180a1a0d0b0a0312020f011509020a0908010f020301030b011202030a020d02030114010f09 78
    0x44000d0185081030740c2d90441c080300303500404142945c2c0301602e0f01406400c01110002e4020f0070010340d0f5030750312420020040c3c200c840c100e140c0c5100e240040c0b942d9081c83d2241500c580070f0390380c10303d8142c0c2d055030800024285031252a02c40c00e03001d00a540603540d4000c0140110340c1f041162903105007003403400c181503503c024240c51162a100004005842d4a0381d40300e802c0e035034400d00950456403030907482d4180452507403070f00c0c2e002003071010040742003800007006000035400c4200c0a13042909241c01c0017032010141c02111240141d80e448034035418858409440d1904140300041409a02600800c2455205038403c4e1241d00c00c400211908079010b000d0b403070340404a41c000b4400c46009281e176054801da20b00ca08078580e5400900d0200c0707103204420b120007400c80c100092080d1900d03080c41402070740003800103417103080c00354000042026074103004481e00c65000c0c0180c582d074446502000054400b17131400366015500d42001419401c000c200d042d000c1c0002c101d5801c841401e0481400c00c5481ea5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 692914505 1250 692913255 692913293
    0x6091b152d040311011b05060106030c02010f05101205121c0501050303070b1611030c070824011a07021306060f02010c0905060304030c05070b04180c051209010204050d03020604 78
    0x420041c4007242d810000841031384c90030b0030401d400c031526402d0300d00c1402c0084006085401210b0001c12a207a264108011045195000740809110614079004442c4103940800440c90f200c4001c0104903c1030811000e0035004a040d140380341c88030303070308801c45900081303580640441a030042440c448461164a016000940c029400d000c1c069850702880b00c4040c04458004032803290500c822071040c0001080528a5000d407034a510040c10501d0382c8450a0040407110302508800c9010032060b1405e450045650341003039080c50346441071101e01009000b4030171203480c0c010001e0501507122141150031403040702d80e000482e5854100002d003260384256402e0116414030140700c0c20290f03c40700700c009803132044035840d80c3c03500c0328502514040c02c10076005165008002c0005440e55072a00680308032003a594010700707105840b40e464412140c0c0b031440070b808101c040c8801e17018809203134134160b40040c042d000186459100c000203a00c520000d1012401644008104000c1142801e800c1c000701d805 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 692915755 1250 692914505 692914507
    0x803121303051c0204050d111804030207030803060418260c0a20030f0d0e01020d12021b0303090a03031a24190c120206091b152d 57
    0x80c035a00240b4070f204403001021801c9050070003e1404034a0743c1140d0040c48002c02c42c0225206900e010500803280c01e141c84d204100800c01544c195a50b00b001e40d00c80ea030326034050b04026045a0340c0700900e4001519850b006640c43d04108a0a91203241d410480c501404418200e1038031141c0652905601c130f94052521300c800d0244d21624100090360400e116800070784441c0c0140804050200c800714141c5c100d9142c441c070386800800c0100801d0036139000c0036076652f1460310b80003d401642d4410309000c0784400118100d10b51580034109a010308001101c6003005135034030f0341c1c5a42243c59908251031003c6160400290f88040640512800c02c1003942c4010820440c1e40c0c400c00200d03081d40c0292840b824180c414030640c04540202c003280c00514030485078400b245410a001410018001c4c801c9440072135200340c9544050000034a54802d00c40c4400400100e00c04031102518101e1800c15140c01040c461000307060026042d000c3c0c085034000b4041031358004404210800744a400390711084080710 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 692917005 1250 692915755 692915791
    0x80301180b060a051e0f0a0801140a140121062d05040207170a020c010f0c0b0c0f2704140403020303150d06020c010911120c210601080312 61
    0x100c4106031002031680f81011a00d036900030b04e200940f10080000700b401d00100244000030f501b0000050002450780340e48002950783c89030740b405084c0c0f80403107136584e00808900c03042000d607003411840c06180ca0103251400028020720002c21b160710140f081c0e1182951900c009015691107400070244015241401c2c0c080d108200703803a41c1e50b4060318040c20303000300d40000703400040c01104640c0a000d140c4111a840d511208404025114240d15901600180c030301045081518031030400c14401c01d402464610341505d07884141e01044e4400100c582070712005200d040481c403041400300500c840000024400340415400304422900c0c0c0b8085200f0541c2060b05100110b68004203882d44110204401c81e620820300e40001c90415603808002c0a56000240300254210107401c00424184916512040150740f0810400f80301109090b0380d41a6005405000300c610b0081e81581010300012540320504c03100c0c40e04241400026084081140d0001469031070314032a00014603400750500039a802122 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 692918255 1250 692917005 692917009
    0x709031106072f1e0a0506070b0601200102160b1303050409180f060c08151005030a060330030c0f0c110a141f08061309050703080301180b 61
    0x140080c1008922900c2003c403400491140d48003075010024a901e11000d01c146201000301e405501c401c2c06484082000200b500300751068414142d84480c0c0d95400b640c41c031004440c0c807004064000c1942c90702c4400a0030643c1c0a10007090300d4400502943c84004603410b00c02480840645138428280d001803114001c6030703001090b101999000380d40031031600e02e966141c10001c00b8034800070b040000e82d0300c00c9804010031503000c65040c1c0500c0e1501c500b5590360b0792031000f41554000300c0e507800100c0403208507101c5100300300541d1300000d40000000c0c0241c49441c3e41221966240038030031850400c03003040c020341d82d03640120802514a0b240a2001c0c144c4000014542a020500302042c04070b0801c0100802c200385501341c1859002a110404103507031524050345040c000c240070390250701c4100240001d00d140c080c0e180a035603165107640c680b98541e4070078005512460001c0e9503403140d44d41d1038400001c0c0c0c103002c000021401030501c0b0740c41c1c0d410407001032200b0720050107441070326241c00000c000c0c42d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 692919505 1250 692918255 692918273
    0x14220513021509010206070f050715022706041202040f0c091e060c02090601020f16060f0311030c1e0c060a0605030a0b06041104080102040902040602010606020a1502070c0e070903110607 82
    0x40041c2390001d00300c410744000303561b2406030310707002000207001906000c48140c095024281201040e0160500c2c03046203206450440f080c800c08a400020402060103464800001d000b401480544001081030580003d54103d4407010003440000b88181804c0003602031003a243d40d1400981242d100c481e034504017016117208030700140240a00315590000f50184c7c0244032480807005400300742d42c03a00b081038000440000c0d0b0790007a03102141d01200e03550324840c07107845507010030740306031000902e1512011480030302504510a4102c4500c0c507034210100c4145e074100034102c01d1256400030100350a00201a0040d00c40981046000b90720118030800814080d101c001e811a400340c80010b611481003050322140d100d80d030400001503000140014403909a07074018001c5400e16402005800c0d122441280c4032402000c0c0a8201191907003408100c00c2c8685c01020402d118444441e00c40355111031404d02b18004840c0030011a19034041001802000208022640811190145440d240344d40d15102c07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 692920755 1250 692919505 692919511
    0x10c08090d1407061a090703090c0b030903090a06230922150b09042003150307030204090605090706080108030a1d18090c0103050114220513021509010206 68
    0x100140c0281909050001c10103d03048941c000c4024003044c081c0254000c2c080d00070050403806690307080700141e416031191140d07002496106a54181081ca8000c0b544002d400140c540141030004221641e801d94841c0f007420700510a036111003c140f119110001050114800288828281004284034540c0c030b011a201460000a206a1000f00060200302c000d0000c4140061110004840416048914005032040f140111024020b61107280c01e000a120f000c0640c1528650317003480450940d91048410081100b00035046446c940e40e01d40008040d03400c51401500c0311607a40c818010700480612085005d003d0a0900c4120703540740c0340c5d1311552441a5101c04041007001009400b0f0050800e14403809410700602010000c40c0180d81070501440644103031031a4412081095010750181c05218100c2d00710300d011008006c10725060092620f108904c1918130714090300c020108041c0c0b441460700a140c0c6608103036044c00039105003d0f441c0c0681e4400b07850781c83c0c00c3c05a20056a030016500754 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 692922005 1250 692920755 692920757
    0x15030112060b0a14090a0207032f2b0f02030a0e0d082b0b0306181c02010213120c0b0f041a2106210313120203010c08090d 54
    0x14040c214184200145000209260b100030404000a00c0b0b81d40d4051400d122074048401507600d840346007a40d0100d120f8990b0003000b0560f1079004040215180a0404055100d98120646511750581304c80c00d28010072000009010305080c2603211000390440d8007400c40b001e0402d0580040c8462000e5942e0180706100020842c058015020a40b035645d020f4400726807090310365440b04001c0c00c81402090b29200844145005040640605501405513448102000d80039284c1c64030382e0700c4050702d12201100c00f01603500c070350391620b041940c1e00003420100d95801d90005840302e903070010100150314640d01c02000c2c96038000c917034404295400704140441341e103407080b980d07681c00f80c030354150482c0581d03840b55400030000c03000040c012200000034000200ca1149603200b50010302d442c1c041d07404084e600340f50000b2401640301d111a1004802c4034884103910122420003038000e00106150200d504071104140c0c8501d462011030070240155881c00c03440d420700d02220702e0460460313030b60380764100c007040c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 692923255 1250 692922005 692922029
    0x11b1d060d020d110406111902040f0608150f0114030714010201060807060c0c061b02040506030715021011160f0f0b011409160c0f080c0601081b150301 67
    0x80c01c95006604840b041840c00d0814010030b0244400c404041e00184034560102c0c42c012018482810081800d044442501c2d100c0c03104240e068003031100a04840d0355034544103542c2d00c03001c0b0301100100881144080c0c0320b284a01075280c00f895a40c4142410380c00750310358003406413080d201540d012408000340c1e901e0f0301c000031f0801c1c0700e032004074007501c1d03260301a403000e0213240300c0407548590100f04558524020b07455070800c240d45a004a0b02d042210074200341d0032014100040c01481d040d003115400400c01001c0301e10040d119164644251203003544e130350160307208218040c0035480c0fa0140d1000c42d90b10307041c401c1c1801040100320040d03090740407000f4600704200b01100200030a620705e6805d40c54002c12550302d6036844444540c00000c00494003840303a84007200041031415080c1c81c03a000c040241c0c0d03034051004c0756a600c2080c8240803402c00c030b030740f844240f10002111000300300703850003403c030040202000210f110015100d081c01d04400d5004800540408009050b803401301c904440b4152030309 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 692924505 1250 692923255 692923267
    0x1152a14012a0207080309180612190302211c14010902183a060c0203070c0b03070c030f030b0a0303030b0f0d1a04050a060608011b1d06 60
    0x24010504015804603a0b040300040518806030b012040004001d290203c1d80c5858445c62425901c1c01a0882d15502401d90480031503902c000e1540e807074211801900c000c1111040300806030500f100c0444d15442c034031240203030700107059040006500107007210380c480310080c503180e0582c103241c40341e4911910700c008a0035a92034040242d40c4613840c004c4817402610003e503111184000a50320940fa40c0c024811500159095450880b42082e900c180d079414583d1000100038081c00c4c00c195542c1c10900c134140884408000c9402e50041c800c0216075036000d941e030f403140d85c64944282c03242504090f00d001d10900401c40796580040086100d550181010f03007525540c07003000c4000e00f0041074900d40200301124000201a016080a11102c804a410807211080304081c0310030001c5449000c1c01609158488220508801e501d42d07030064041d0701030302d44142841c2c480e503003682e065a0000620760364942c10390303030b00321100403902c84a000d41d403030050841094460780c0402c080d039043e0980e01c90140007882e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 692925755 1250 692924505 692924543
    0x703020405040305070c0b03010f0902092803050a0b01050306070207060203272706010f091206110f18010f020303060f03100f060f091104150c020901152a 68
    0x5556105c0d90201c1d42800083d290008100aa00284581491401c003003e000c60038000318020781e00c4060001e40140f4a88130000c00705140c41d26281c105400d107210703590006c0080380c01485424807050090b2003001041d49000f06261400034014035820442d0400c0c0c90901105a02008440005010a04440c003580e41104104040316981580950088000d00c1401100fa001d9100a42c00c111464007000140d0b01d08005640104005501d400015001c803418022006414103064406014210010301d0714207641c0400341603030181e0904141c4ca0800b15880780d000107221180d03a001d00d82860302c0384041c0c1e450000a9501c0c04040c0880744074407654503c120641c0c50803c052132810840c688103025601d002c00c2e60703000416240c00b0b05079482841c0800440e006441e4010411040f49080d041441d0070b1070401000002c206504140c0301b0400d6400da55809656885036440c00ba0000308400800701c401090080e00ca15a0700c84402ca000c0728038603030b80e49103202144010700c1c1d650f00034002c1c1c044550800c0e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 692927005 1250 692925755 692925757
    0x20a0f061d13050708150418260c03120603070308040b0a02100c0e01020f06090a03111f0209130b03101d0115081e0c210715200703020405040305 64
    0x24003159080c1c5410104407420354403000305401131385202c04246c0052010018402501c01c0d9100b100a0841c280c0071500015070100f041000d007002d80c08041e410f00c4e02e0401050b41d55403003000d605420782d1001c20003056030034452240e160400b03011002403010307610755134030103281e40103911a44c09074070008a007003039409009008066840c07021003404c00c0043e076508000351603100b0111030309005100c1c1010140346140d00050081c0a60701e040000c0c00ca40ca01540c04540103000e4051643d05030040030300c2c55500c0070b41c1070024020f0a04005002d611602c6c9201803010402802030b4070303032a060405c201080c40e0b131070100d020340b2843e215600108202d101155940807507110f101c80381e0312640ca0402e0700301d02440148003010030303140b01d001aa010130f0703103a2050146001004074420740f0342e0850002e03030149203000a8203c4c000d48203c90402c5044005007159030400f13000e40d10010005000f048000f5060740e10000a00c0350004194000000c108250803040d6205034900000f8001e90382c82d0081000d15010300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 692928255 1250 692927005 692927029
    0x4090201030f050a021308010b0616031803050703030f02210c01061a0705060916060f14030709091508060103060f0b09070203041a030402090411010504090216020a0f061d 75
    0x850140f120341040305401c8000d611102004003000d8406030089021401802402c5660b00d004008074104403142c8004003180c1c50400d0100d003030101164095213090708000300480214060400313004003502e1800e0203090b180c0482c0c404421900003400060303143c12880445452101c20310843c68072510070802490042115800c2212004c000c010300d1422403008000404d511403045003502c0540e03c58002040e9901c0e400090364400c40c1c502310701032000c1403150850300b03810300782031412500781c2c900d8140324072141d4420740301310001606c4c1e0750081c00303080c00c2401801c0420031f0800b03015070039a10340300b00701c2c0e16104180170044c24691500d241c2e4036944410380001c0b422000c000d024420768140f0f9040a950f903842032040c1840034100c0c4035904c0c0c00402000641c1d02c81c54016140e0f44161703549a4550011901004009050050511011520400a01c0500140b0800c10003ca148000303a00400824070b00d039601c903d540e501c0c0c007070050120a0303021178441151082501421244089900040c10b1040b0507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 692929505 1250 692928255 692928281
    0x2030313031209200a0e0a02030a0209090405010b012d080901020c030f12060a050f0105030901110d0c120c09181e0f1a0306070c1e050c031203090703020409020103 72
    0x1942c01c0180600b41d2451001e68a134035a002c0642c1c5041014008021440d1086d408201c3c0d03110005011143d641c1c00642d840a804080117203080320b0817001981c8440b090380e0a40f12690f440d0300d0488156040f0010031070102c008a411503030b0364a0b0503080060510b0040e0b80b00204400b800c045020340009405076001030720701d0002e50341c546c02c1900c061031103908507042c0200b05580050100b10b5509020f0300c0c0100b030307550190807104d40c8100880152016070014008d11055987d030a2310000f00c112250181c240d9001506011400f1489040020301c1c0c118180301c018000d620300544641125008148c01080314421082410a05034000105000380080135491280418454214504c0c001c1903101441c92094881c080007000c120a1680ca81600000701c92038155200d42c003c0348406001e01c049801c068491400d6071141d407841c0001c0144102801ca00f11010361003030000551528051040f0991090074023401415860b045202560341d00b002d1001034003c1e83d03a40500e50540e44250003070500c003004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 692930755 1250 692929505 692929511
    0x40b12070605070309061d100c150e0c0102010209331c1109030d0e060d0603121707090501050d020d24050103020702030a06051e0109020306041407020303130312 71
    0x81c030280a81a54031141086001600781c640200d441400b0f201455007a910542d05450780364803181c240980e03403050020220610580b450204001100c5a0040d10b030b0110503c800f198a010040f1034074503144c2c03449011070569005000042c09501c41c0307507292800c405107020007003050900c51103034100d062080d00f20040c01400004d05c0c940891203aa51305502c060400010041015400c2c041c1080c0d005d4a90740e00e9240d00000100d0710824880c200340340c1030302001006145000540d99500c012900715a01c2110a0200103000c05c0600390020740611125010210980807840c020100505a003981d0049506120000c135195201c0129941560803000d0590420413110100104150201d81484160070310b0000d40500030030303e07520074000d80303011607030140084c07501040c19900c12015050081c020341a5460b801d01400c040c404c507103e107500800345039400599a0800e0800c0c0300a4800010400310946504028070001c95400401c03aa4000100b6503a1480015240380c12103450b5034100c00d420307540d42 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 692932005 1250 692930755 692930759
    0x9032007173f1803071d18030c010903020c0f010905030703032f1f1b0e060702040227101b060e0d0509011e09060c050c150d050a1a040b1207 62
    0x10090020f010b00c0d020403803c840c00e05030303942140c1204204085844250114504c04182c0c2440a48207008142c1254016a404d02803c151440e003159100c00051340141d01044540b0114209410160708201080c40c00c0e07941c0038140f1000c2541d0f6146403100400300308541500da1208040441c84800d524841001d00c40209201344029568460360440c11694603910300150507264158410101040c40011100020550210042e52281c900e4240d41c0d0300910104050310050340d6902c0200f4000d80b40190f00f800d607060320614501800440160030b4060203a075000700428a404c8070090302004e010603850042c2404510f0003a01a1082e0310903a41507110341040a541d403070b006001b0380070b4144207070b07a01820080348083c000490340d0404112008600c500da0140a050b02c40c129041c400742c06001100d028081500101e2210060245001c500b52004110903000030858011540c0011052406200c551150244084c90903130f115843d9214554031505250789232130380c12400c29010f42c04029a00007035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 692933255 1250 692932005 692932027
    0x41a0412080901030e28050a0b070807120b01141809190c080124050705030f07060605010503090d0809070f14040605030a0c060309032007173f 63
    0x5040aa02c060201c1d08007070400032010000501d81ca1116421001800000d200141d00482c0644005c802d41d0103002d00181304002c982400030b150700903021a543c0c107800c3c0c90600b80050010345400341c00492a400c0018902c4c1d5030b03910400c01c0d071a0402200d40319544680240f030001c1310030074508500d90000d0781d103c00c1110510180005c0750242402407010700030a501d102007211103d8013401a0f0341d1259500991082500b04407540008040040c2002ca01d0305a464858501d560082c010864540b1400140141040020b00071180145003e090035800d600f4000100798031810441e9642c0d04001240c40098031140d001c1000b0002080e00c10400c0380c209854410140d82418612441400f03281003410009071400e00103102c0c0d80c4a40c0021440b0101414202d04401070450f6080a0b010440800c18148448080f00582d20494140000800d0b066180075002c10300040034040040043d00141e00e103c044548201c0c079210000c4140c6d840d000c5541070022240b01550300828148014000850952040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 692934505 1250 692933255 692933257
    0x1b060c0a050c1c150504060e1c020c01080405060a0509100c0c1b0b04090f0204050a06020d0306060216050f0a09060b1b01050402130c11100225020105041a041208 71
    0x1000e845541040c0c000c40c082d03c001c05a0400014a82560604c802d4802005a404150003c1c40b40300045081c03e014604c03140b41c10200984032201c844c0a607440300a5a0b010000b502a41e03000f800d00b401d00e40b80c1511281d482d071400400d12651192140700088443d80c4c20310110004010b032520800c201d50b44098024410b04286100b208c54943c0342111000c0d68049201d401e08072611048454503180c01c02c458200a000042e080702c1d801070f004d10005c10540d503803150120151003983e0041c0205414080c3c01000e462305940200290342180c0b01680c0418485c02d020003d50300b05071080c80640009101107610340d240c55001e402094a03003180400c03124400001403601b607a507040400100300d031800310282214015503009502400003034070104050896080030007000c4150410150076040c04510a080000038030442030009d034000741080c003031507610744441281030440c1c0c0001c00b03555140e030000e840362040f401035000e00305000b1021002390020b10b0484001e0a20203c038030709029110704d010446 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 692935755 1250 692934505 692934523
    0x1513050709080c032e02211603060302210f010203100f0f06020604032a1514100504020705070b1c0501150e120111071515081b060c0a05 60
    0x90350060f07201518032450000341c41400741c0c15441031080140c9040e500c40101e1101d403e03403051459002d02c00c0403480408403601f403018400107403841803070307160000000c20501c442d641070206140c81e200301880562282155150f41d0b0032000c80030310120348040c40480c80c010862581202960000080050360b8039601b45101c2111101201300c82c240b912800e60380c50b21030141c02401d0050340800c0c00100400d100e404000c19102c203610740c42c0117040030459110f00c0d03940c4000065403000c4594110020b0100e40b440b500d004450b810494078054100448202010721141c070506108507004208403081c4882403100c14000c1c15501c1070203907650603080f2071034100b0480c4403c1c03440321840c3c00000110541048210181000140d49090b0040d60640800540f8100000c510b0820765a410503611f41d0000c1800030420b580c0aa40e42201d5211640b0310601510210300c410382000b010a001000300c0100019400005030448128030000f4004c100031510718015012464103a124110380c1d0f0741440307c041000300c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 692937005 1250 692935755 692935769
    0x11e051c1d0c010c080f07060b10090609090e1902011b0302060f0a06140d0611070311010f020405060d020d20030406050907050d0204020904020d05101d07081513050709 74
    0x38100003101e0042d91142004400506449020480080f50214100c014031015122301d80015903440000041007029110381e0120010600d030020520042c0c1e000000ba0b001020a400309000041001091588500c5c01a8112002041c050020811680540b41840c200403500030707100540c41007414020b50381d07030041d2440c036251090390b004909508054080c1070151188144194400004607040c0701d01e038059a001a100140d0b50164040c080c4880f00040601500035610301134031804800c026400c4800d5110802c882d50b104000030485511200143c2d80d04185191380180c9600341e10a4000180500c2d000c652061528881100d02400561010b140074074042d80e810041c582da040003140c1e4403e203c0c000c15a02a4142c078001c40145841e0700100420500507101504200307081842c1307400d1f03580c140c51076815000041c00902108800360203421410085c00018407407424020381c040c0100d8405054605d0400c0321042020f2140c454505da828941c0c1a075004000625050078002d01003221401040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 692938255 1250 692937005 692937013
    0xf030414030306011d1201020a03020c1006032a09020d0e0c040507050f0a0509090c121005010903060504050a0b0411040c110d0503090723010e011e051c1d 68
    0xc0c2214001007074900c144010b0711a004041d4141c1c451134011014008001d0f0711001c10b444001c81c90750280068114442c076502e006d61143c5400e803806050070585260868000c1c900705040010444c105800c8110082002421004582c412040c0c0356040280d08140e201a00000303506000003241ea015000e024444810b40e1400441401004245c503402d545240001e00b05020140c100e410110060003030250600300140303131a00c0040450015002200e0782d072a080c80c0400e03c2c01000f4600120568005a00081042d04a08100020f446031086010180485d9595000241041410030002c80c0064000c022003d542c5801e01c0c1200c1c0d05200c10351414092400d005403012042d008910b0090b4180c0e65002034125502501004c98444d040200030003598031800c08001f582c010210b908071002c1001400900014a10b5000904100e040b251003d0420034a0402c07102e005c3c8000c0003d4807030000601e0403d84d10a07081200803042c98207030850f040000c1c507040400750101007414240000f8032202040e5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 692939505 1250 692938255 692938283
    0xc19170f0a050a0e0601051005040e160f111c0c02040203180c0406050d0f020d020904080c1203160f0530060103050907031103240a050105040e0a0204021305060f0304 73
    0x60700642c0c40d035900000c01940300ca00140803506d1320040003400300e4a05d191a9060558a035425550300034140c414420843c903203140d16500d070f58028a410310302e5066092810641030584030300b40c5d503107200841d03f4031500210b900940300c03135201c0d800f030100c0f440e00188255104c0c10f081c05911040c4c6130b00c003488900c80c880c040885820341014014002183c81c0100714865601c02d0740c503410a0000304220032070707001405404100c0141e541000c22800355006045075919420245125031078903a000e6040e01c0700d25028000c2010364810080c69174105840c4d840e020024003000c813000d840d1401175199032507060030304a030031004008120111100009040781d010744a515071a00540c2203d0041e00d11014540105105101080c035094030385240000103403c492002c01082c3e4600c1c3c1c8451840d50b6046800406400e000f00d45055000d5240585805c4038204104407401c116650f6541143d403009000d0341c1c0100703281084114a030002801050081c20b01c9944200ea920540810740c011901110700c0841041d507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 692940755 1250 692939505 692939521
    0xc271908010c090812040905090a0606030f0c0501090e0a0f0608100e060a090b0402090403020a171207020f030d1503060c050703090605030c0406200a0b011d0c19170f0a05 75
    0x800c50110381800203207447e04020742800642401402000b0b1846103031030400c0091201e00c201c400030341c00351102d1403c200d01c0d0f18284201d10000e81c0304030704120b03254406200440c000041183c00880c0814001003c2d03804000e5a0f01030406a4840c0da0a8024050b41014a408680046840320001400e070340103030343c4103000217080f55a980406000ba01405000500501389000c41d29040345c083e0049a80c0c451103595007050552060a10754081403000c1042020188842c95050304894130303001401d01604414000f95490083d0910000100d4883d11007803a925100d8015030091500a0414011040c100002404076480780c0d000710f000461541c1c001030a41d02c118242c038041c0c40284405480d09103485400c44104440000d1000083c10703807022184402410020b1070285442600300e1200341d17140912141940c8a1051081d4403187c0007000c002918046000700e451452070800502d8441c40d40c0c440866081c001d1214401d0440c05850074450480302d9044c0c0544035100405050141f5070b11108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 692942005 1250 692940755 692940763
    0xf0402031c121406010215090309010f050d02031906050102150406050a09050304120b0c04030f06050a06120f0201030501060315150e150903061005060a08190c03140c271908010c0908 80
    0x1000e0300e01d07800c0ae014610440d0300c01c440c5210300782082c5c5429410101031788007160481e0310070707030310b030300710303403440107294908440d043c003480001740000d001504900100250305454444001c01c02851540d882000983c01241c980c02200c40d01d07041011641c840c0d440d0340c90108411800202941c440c9114030000d049200000b04070f0f41902c0d4420003401c3c904089079103c101410003d0101800c05490300c0c0041042d00390350803005189400f5880a4039aa5140e0001504850f018cc2180e0100f6040030005009000503c5801d0111062400c85119920901608680341078070001d007654407400c2e103c40584000d184101403e880b400031030540d4415280d540b84403100c02c00c0f43c0305d42ca400c0b1209100454400b4010700e2960350000d080c2004c0480d40c1d030103242c920100c494894a4201017aa903c94010001d4980301d10302e0b90080581846502c3d0100d0f08100008481c010781068130099002180c0c1210340d15151490344070844003850302d0300c180c0c5c0c60b40c505034003901d420411500050003042002507100700000b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 692943255 1250 692942005 692942011
    0x80307150e061e0a1e021803060c091c08030c0a0905010503060901150207090c0203070b0c12040b07020102070503270a0f090b04090506040c030b0f0402031c121406010215 75
    0x4040c1c14078491814014210f00001000040719540d0ba03e01c8450801d00d20a0f011603c0c10b174600c006903034401d0200c1c241900441200b107240039503c18020040c1c0ea5a60904640c58407030100c819605004c041400c00c4401c00391500d00500004c40442408861115040900750302c0c84d268a80307000c51078980004440501007125410750084c400d4004000c0314024214005610003640f050b00d88082d140e50f0346000b40d41c4914080c50040e0303c00101721b01403003e820002500715a010203c20314040f81010044520b041c0a00050050049c1c1c0000c100c0e118000d604407400e85a101080d00d072a044c82c042282c0500c00180603a40b150800000601000d1a00e0241c1406550701c2401650580e81024420030090200401082e00b1a0f40d0f00050340c04102c003044404d100350302c03c0099030101421441d28803110200601344487c07405114050100507900030598204103a141d400b0f0921491141408507a00012201116029460310380d45030f803a02d003100140303445a1002e0b02181c01200d240a0020001e560032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 692944505 1250 692943255 692943271
    0x7140f0d0b131a04180c0e10060908030a081306060f0e180637150618030b040303060302040e01200403021e0103110406020106050f04060e06040510080307150e06 71
    0x11121810f140b4040d4040c210250294445502103000c03541c442c0700c510040c0d0440d102c00c1c4024403c200032000d88802901c003404481c0303400301e0b072686040b0515a50f8082c98000e0024007002da0001012035200c1c0c1200f54016811007418000c3e650b0b2180054000406406428808043c1100044800944070f2040090b001004000c0606540720f00044419145215544008845401c0ea9441900700e0f80402907030700d0041d000004103150310f09000c07903e00c0c165611034824821201000c0c1c045610340410f00c0300b01c031b801840310120380d56180b60480080505400080d4400c2c41c00e160b24141c4501503101001090381d210783d44416102c1074803002c459000302d101c001c1d449000381d02c0b2107030044241c40c0c80d2100c014041c100440c0290344100e41901c2c41d0015001400142c0d500c1808220ba882c00078040d41c41050142c80c10495075003040e03032030382c1108001815a40616140c10210307800036600341d080300060041074140c03920b50103203161020a040b5411102c54000381011410004400089291400b076525 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 692945755 1250 692944505 692944541
    0xc0912031e1101020706020903061005030706030c051b1b0a050310022a061506040b0901050703020a0602041202012705010c05030919051e010807140f0d0b13 69
    0x880300050307115041400210400042e00700c0d52110030000d001400395180b04907000b58030303102900245868000c008003810390700444d020f410441130b00c01151203415201e540c40d0206220351160002c3c1c543c0c3c4a40d1030245044401440103a1034100c000c5030b4035030b0b403064010031208000c0701740040001a0a00b0b0250070b0b4160403804d9405004a01c550050264001e0150300f01c00700101d08440c16403500c03140e66000c4040d0405010490b041c004400c0e40610818100e03001400d00381003015480c801e00541d00b4030350500c1700c002030f107005150080204c4c41029911003800c1d075645803a4102c810807140c0b803103c22804540343d20190f100c0c9400244402a030005a401c540d44054a8080110707091040d00c407040d5224003081048010544440911041c0b5400354240d24003001d04c0c0400b0322003200146c20700c06000101d070755180d6100d40e900040a40d0802c3c070603e450708030030007003014142140c802c107008051005c01c006102602c0b030b40303030350000e100155088a020281c00851540c400c1903644542402e0110380d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 692947005 1250 692945755 692945777
    0xb0d0629030c0d05010f090503131205060721060803091002033408040605192c04110313060b06070b011a1603021605151603050f0703030c091203 64
    0x2014070750103d800340108000f2400003100750150040b03038010b07d015240c81d040012150410305152070345400810a20b0702c040110320076522160740398030dc087e140b141001700e907040070104484038403a841e40076000ba6a0400902ea510018a542c0341d01c090036180c0202c15020030b070550b050000c0151401d42180c609451844200001064079101e130702000c0f03a40c004a5140c074403005c268504040d001801f41c544410380e40380140544440000399071200c0d041002031030100c00f04c0840d1901415890307800700b00110480c041d4400001405405004000c1403001004000c001055603001c450030301640c05510b0070490103243e2424000c130380c42251406040036500f00c00403ca181c051050f042c8240d039442101c0c60800e1300d42d1242c0d0945e19224002a40168400d031100341d10218241c03031020062904444401030120580e92007501030240d950743c2164403407443c0880c014140140111440402c2b19040c0e503554001919010380100010000040010a0540e02047c1240707400b00c058401070309601c074410210 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 692948255 1250 692947005 692947009
    0x30705030301090e120f070221031c1e0b0a30080f0d0504110a060c08031009150e0703051b0d06050a121a06090c0a030b0d0629030c 58
    0x41405580c554080c17143d0a880c03859406180c024086580c60100c80c942e9070b84550040000c0800a22450101c42003c200e80001004000013100e0840301288415020f00c0340304d90072107001b0101c29440c0c1d08110020320702d035040410316a00100c24040c1c1110350100d00c6482d5017011080d0b40b040c07100d1400e074040c45c4a189040900306a084600103105240032480c01c0840c40c032410b1560890028096800e4940b41804100b01c44101144540c0700152010304600d454200c00070883c9d500c0e540c02805905001011031151248800d002c40545980c01080c4002e000c41039001502c010030f403017020b0303102e0200004140b040d803290048a0242d504960038101d01c001250415003681d0010782080c40070307646d420f0000b0701a1a004084001084040345902c0110000c0c10310500141c1e00e10111080d00640c1410451540d660f0f00c2031940100d5600000307501c8210b0f4040c00c2d001040d081e944203500040c0d2111070020000580c01000b075401400028014034907601e89400b00c1c100104d40803030381c140c01c00f0389160207038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 692949505 1250 692948255 692948261
    0x140a14061218030430030e01050d090c03080901110102070c170114011e08060f01030f0203030c06130606080a02090103060e2e0b01050a0e06030c0405030d0f020f03070503030109 78
    0x8007195042000040ca000314002e840c542c1301e40d00c242c22558294100861505203000182408000d4401400c4058402d6500a1402522940142c180100811700310f0525495500426100760700411101c840c0c0d0300c0e81441c85007900400c5004c1c1c00282d01014401a00f81306000b50340c0e0440e40080303803050241c06c004000707445e54411100c0004a40d6520607000402c004020441e00800005802c0c2e00e0041900c0710001c0302c45159080700026900120611000880e0b4144540c1105e80100d0280b8900c0d605100003815071050555585d0103200f420301f8804103d03003034102c1c1026288a01001c02510b03a951a4403500d980c0c2d41c0b240070f0351040e10000100045145608032800041c1668246c40c50503143c00d0b110007505e15018200c207a049100d020700d500b000a1031046891a103400d0030810f09000031014010034805001c400d040c0103030404004101c10b40c2c0d1171415540640b00040c26940f614001d504010310a0002041c42c2c80181714134004a00008004001c51740000e8100000d585180e00b010044009 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 692950755 1250 692949505 692949511
    0xf050106171b190e030c0d050c04050c0c0307030509181302040903020f0a080301090c0201053c01120b01052209020a0803070302070303030e0c0607031b0606140a140612 74
    0x70680030480da000c0c443c070002c040407100b1266140c0d607a1104100061628000107045201c2c02582041804008240700041501007042c04840100d050390f60f11050600134040c083c0c14942600c8085035a40c200341d04035014145800040c1c641c0c0e194140724945d84541c02d40705445804400528180034409030805421403c1850301a0044405040c0c108090038641950700c0c0302a550b0007030200060000203001e005100d504a003d200900207414190f051750040c490041e4940c558010158040d0b98080c03c41c94680341c4901c00c500080950b40e51030380d4642d44a150707a00308403441100240042414079001460300848801030f482034040032043d8800c0b070700608907650140e80c0860340403000038000d04200000c0041c90302c2903025050140c0741d0301e03001d01a200744000c00c5032140c20042c250411525964282c9044a40601d0320508684001d8400e441803000f001000d4806800d0400c0803409211a0b01881d00c003040589400000c5a0341c1da1f1a00d5107030441b002480d034050740400180c180c04480000280d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 692952005 1250 692950755 692950801
    0x612021018090911030d090b30160906050d0b0d050109060b120606030319030b0d29130b0702031606050a2403031209080705010f05010617 61
    0x8224210201c20500d035203691100d10216180d8081c40204010140c41d00c04020b0300398001d2802e44040c0402503c0c070381c050b003c0c1981c2c680010035840802c5014840110440481001c5031145440c2041800c20940c01101c1d8101880b03e20014110410301c500036520840d05250b6800b4140041030011501400d080d82945500904030940f10700418401e2041c0e4030310b03a204103000243c3c1100f0308148600038920443c181c01300e400080410050b51808004c6a2140311000f10560491601000076002407810400064000c01d89001400410070301525058002e20000402000d06810301c0f007505800d00f040360140c2c0d8100e4544c403480c0000341440001c90300840540107481c1010001001016407500305441038840903110014014040218840d200314960424420601490403c10480104c0200c0c80300134100441c61880c56040025980302e03503d02a40241515074600c1c150410314084c140700701d4803020185c0b401d000041c489000d00109200d1450320b032401c603803aa4400300e00c0300d0b4401d5031110880d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 692953255 1250 692952005 692952017
    0x5060901080f060a0f0f1b03060803160b0414150105120c01120e01020c1605130203070c12021606020703140a0c171e030a0e060f180604050a1706090106120210 70
    0x7031000381c414040e00002c841e400c01800b8004207007c00050a4034520b0344070029a80003048180c1c0f0051182c5955440d0640100310b02d000c2c0e850b6440c0c40c220141503110f1415041c0a23582003c554001e0f102c00d03240c101c4100311419400d080003007104e02d85034600e14107014082178500458000c0305130301c2c0d0001c2c40300044890005080c800c002007000e0902d0855031022501c9254500184201c0c41c000650020300c0c80600310440c04c41c07502c0308024110342401d04000d001d0200210f18020020300c200178044a40300f442c00ba03100300d03030f030349007006517035540396010444880e503115603920303400e88002400d00c0b02990030020001401e4504820207d07448417107034402c0c15038042c03131156507941100f248a0014403581080116601c619802d0f00510b4103078140e082c0c512030f0000300a4002e2820800c1c0c10b480c9800c0b86617200c4242d00c0e0f00d00c00011201e01c2968022034200384107850004604078400600080180f2110a462003544c4805006080300d10a01031900100c441c10281c5016060004c040444034100c1e041070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 692954505 1250 692953255 692953271
    0x15010903020d0c1d07020f010603031418030709021305041b0507031407111207060e10020f0f0115120c140d15230405030702040c02190605060901080f060a0f 69
    0x10342e141801044204c407400038100306100313001e40c1c1001003100c00044800200002d9045940052100110010480402d0301c04915121410306c90f000e01400380c08000c04503801240e0f01c0340c80c0d0002c0c1d0040840031f2441065058000741d80c5c00c15004502c02121040d0180540401c100b40503280c94020741800d608116034600202140302c0084001e08a01c0c1c000e050b00d0300c141c038001040145003512000206040c0d0071a08040240383e8205102a10075481100d030b145031b080514204038503040d00090001d121348100c1c44a80811036043d40481019200c01d0102e030011a1185803611000705400c00050404190f210208440a20300c0308403201540c0c020b1248840d00c1c5982c868000b540300403a0031f8503c6a41c0c54030b1000c81075440030030319105004124004803d030324041d10368980368014404007034016500c40c1890280c5038804c1c170407108480d8140e442c0e0f10100d92281040d80050104031865070180803c1c400100710040006200a13140001a00400d0640e0b10040000b006d452a0000114203075103c00310 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 692955755 1250 692954505 692954519
    0x3141506130f061e0329010c020316030620030705130e100f050f0f060d06030c08060105030c01080c09011d03011409010f0612032319030515010903020d0c 68
    0x1150b004059035500c01640e02c01c019080340891070700010340c02c24103103003028406c0c0a00c3c4601c0c200c08080400102e05541351318840050340d40c0c1d46440c41c02545802007129170aa100c0074521900e0a0f1f9005203000c0200da9034000d40c0a40b891140300c9040d81c000750900006141501c114001c100c00d026040010072016514806a80004c4013036400065501000070144240d070003803042d00c40203101c03c0324900004070101e4081a0b0740c1d04c6608210b0702465001401843d020042d0f0803070b400855000100c088003a50714100161201403c0c06294401c0c0504001c1d081c081d03200d034440b14000c524038048245403205440041d1600d04140076a0700c0111181001c1030000d640a103d448202c818650100005d0b1030510401400c407031020b440e0691080c80e124003440141c0415440780e40080e4503080c0031f2101d008040400441101c082d2000700d0044c400a80b500400140c0039250040d0600b60301c091100e504e9846040c15035554003003000d80002e0301804100054030300340c081021030600810342d03015030700d0312040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 692957005 1250 692955755 692955779
    0x70b0c09040e030711030c0f1201022505061e18010e03031e09030307050f250c05010f1d041e0204080106030b250c1b06030605010314150613 62
    0x74000e070b543c0c102103940300078410304005400b400541207010b0b0200c0301100300020048901c8441150103203500e2403010000507400d6044450580c3d1100c10442c406008908410400f00c2d00d0004481901070b050205460754500f05150031a126481c01c800c50301d41e01d83d00e82e8840e002100c8000000c541d2184035421201105000560066800540c24100c03280c40010866200c80c5c0038118000e43d03482041005141907104041e030307407000b04202200395a02c000e80603c141c100b07034101049005110020360142040090108802250004e807075042800e458100c0507210441031084640324100746010701c0e0881d1078268403508050740d950006542040f44040700208a800a41020364540c2d5214428400d02c42c004103010b60010b13804000244000082030401542d5600718102d00030702541890000c05c0106140003900034001d203540d050041592420010003400c4144200e0f80440c2c50807091038600c01031034502070b10449540244920444031131003403003840e40c070112920300000c0c3c07070b0400410414a000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 692958255 1250 692957005 692957021
    0x1801050109051c2a0b0304080a0c03140d020319090c1505160501050105030712080a030504080906030403020d03060b0c150c040305060f010302010f05070b070f0933090b070b0c0904 79
    0x401d000b01d0a5000c8844911381d1600e0f600305844005e0148204800984c00f50116940c1041914010000707a4151809440c00c4c03020342501d030305400010940a5035142c45502451059411900342c141000070440f8000445095103c05017030500c0c040030a1214805040c4403044071256440d01d20301e00703030101c6100c10114580e00402c442e81e0351075600400c85440e0422503e03000e085850225000683c15907204046845000c2c80d0720103140e100c00007d818042d1190a803000d00a000e000c840e80c1e85454607000307441e02c080f003001b000400e05c0c101f8089458403440d0141e0705034600ca00000c007400c84201c01884644180200300003483d100c2013001100148050103441d02840f0090020041541144000f400c401c120406541c01c0110074050f1102040340040c00075000030050415000140c5054402c55122078650445801c1012102c0040008104507000c0a03459100c41c4206d110961a040111590f80c2d8a120741c0e900d1100610404021400c814400c42e042002a138225180105440c0820103481020b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 692959505 1250 692958255 692958293
    0x30f2618212a060c0c030f070b0711030c0d060f05090616030b0a120c14090f0c03090a0b10050310020a0e010f02010e1204141504090b030c0d050c1801050109051c 71
    0xc503072171984a0808214075924007980c100034040c3c0c3d9081504c03080042c090300c2006801d0080403004030203940c60512040707213012000b411000e40c64a044c14000f003c0c0060146402002d0300d0a000034000d0300c000304043d405006004c030600b0810320514412030151140b00c0100f80c0c068103d24000854404031640b91001c14400d2007201c410030301d000d07003165402501c0c3d200b640c001c0c00e2000c104084a0020102c140c0c0c01031180d07c42603166164421518908008602d00500741c81821083c0b003003490f0444134240417108201c085400a80d06182d80c101640513444a01e000311780304800403140c80d070084c4004c8422076803600c000203a0200c07580b007552070058031107400d20032214005000c2c001d1001c0e5810300b4062250a846040c402c02c6496a200f000d0b200d14403810b104280d455034203d035a40d070203000390078196074028006199842d03142041e54036440e1350400280320b40f0b0214800c2144495141025048440585078050032902c1d12040c8850034000b21007801e8101c01000303190300002c0886203042030404030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 692960755 1250 692959505 692959513
    0xb19082206063f03050a0f020309090901051909021023030c0a140910050306040e03180f030a051c0c060f0603020118030f2618212a060c 60
    0x10720003250b0f21640d11910001c01c01c6a0712180b1008690007030121031031800a441c0c520510121044220f042d401440d07400c0d0b83c09151031080c81184001500428040c14020b80346010141c002d41d815011100002c10007904030600e0341301c140a481c002d01041c0620341e0314100348880540c1202c0d4420307607036008580c00d6642d800007244000440b81d2001800030341c03241003040d01d458141b02000040b010030030161002d080100010002d041e0703840d5030300300c80413459210040303d4844011031080c50011502001d41c034080d41006500102c83d2900040000b801c98002025180400c080c60b520481010130000030014058840540c3c4005511413023452940b171000c0500007201403d62000400b00140391101c0704034285801800e201240c165103410000030780c800102c10003406040f90141d6492103102c5400c85d00c11000c618250b01480f40b80c83c0c80a88403044441da02100000321402490642c00b01c900c610590054013058000250800254005404441740c00001031695000581a40c020860b200c042d0304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 692962005 1250 692960755 692960819
    0x1140c0c030403020907230403031e021c030501090c0e09041101031d0109021327060608120301090e0706090b070609050f0a0203151b07110306010b1908220606 70
    0x18905148147c00421100c45d2030140356132801000c4024528030018484c0380c10620751200c0d80208010151560f59056281481500c2d8201a006140900c100c0382e0090620003c541501c2c400c0e18140100007008091400c07644554882030605031400741250f061682d140220200500c0c11230a092492030160000701724042544140b00c0420841404460b00e6800e20030000300c500800000c00e40c4c041910036041c0015030080c100500908129400300320140184402c88069021050065040c1c600041c4140031401012003481d03a2100d840c40b9920014140b01b03c2803185100c44401003c08501860010446c0b10503616101c1c2025046050744641e5840394105e142181820300004100300c03e01d4059640a1802d0380c00c00c200083d0700d0202c001103c1e000101c100401c00c081100303600910014044500c5c4c0d6854180d0350b00107502010030402d400e100f071074412808a1003030508900c50201c01e52105501c1d036814110245410b43c0510031a08661147c0e0302150740c44804c40d241555003402d0f0003000c82c1d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 692963255 1250 692962005 692962037
    0x9172817040906090b0d0b060d030c0b0a05010f15050d090f0515064e06070e01030b0603130b060609041a0405011205060105060f04121b060201140c0c030403020907 72
    0x1481003440d213010700a40d0003206c0c041100d04010340e03070003001625a0500d40e20700d0b180440d07144070242d80081c001c0714040188901078082c3d41c091410f07507250300ca10703a2095444080780c2040d01c1c1202d1800340010420082c507a086046504988045485090f40380400b585c59078070503061190544c4843d00300242c04003080000d18041100ca00d102c41c07400ca802c488410182400c15444050129800749050624403028030081c04071400300042501c10159240c5060080f0010080b0503802d54060020b820b2458100003850082c00b03e80c02001d50501e020800c60030795a4410900c803004060641c0309800b0321028a09484030300441c2040d80030802c2c0c1124000801c5c0c10030040b1403042c2c0020a0301045200d4200c0090f200044250544004549071912002c01101442081c400c80d04100790b4284901c1c0001c003040075000c00c00182e03004c982040e140c03154480d10700324222140300304034510076614034012070300740d004640003004460324003010b4a150503100c1e00405c1d8595020f1b41c0010008622070700c0c0c0b640c05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 692964505 1250 692963255 692963261
    0x705010f0501060e03070302041d101a0604210602041703040905010905010b0f09031006031a07110d1101060b0a11010b03010504030c1407030c060917281704090609 72
    0x241446003012002c0c2044400400d581b1503c2e400002d005a68a210b80150701141800710801d048540701142c440c0072044c1da808001d485600c4819602401c0a40d01c83c04c0fa1420000343d8095030800c0c144401844401d03140d017220105600c0b401d070303140c0d80c0c00c000118130580082d0342da813038465400008640daa45050b064008075001603110700c00d805d1805006111000004c4212000041c4005102d5143c621000000381801a0000802e14092819000004010581c00c1c0c1d80300d40741e60f01c0e109040f29540c19809035803800704081110b817141c0100128442680c003c004581400c14686c00018110b512042c583e05c881d0f00c034540302c4000c244058680048110240140509564140c0007413019003010b41d00900003050562000f4031a640c214128015118100503290003503402001c00301025a403004080c219042600507082c0c1d01c403504560020240f0005514040200035034035402c6c0071040030000001201c9000c07000c881c08000c1c4001c0b56982940074011b00090070307101e00c1c0003130444d183c4100c400c12 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 692965755 1250 692964505 692964509
    0x11070b04080613080708031b1b152a0403150617071d090c09150307060e0a0302101112090f040c080f10030b130b06010c200f03030705010f0501 63
    0x1d4054010f03445400180703c0c400303940300d65a0054005803242c48505806100d0101480c10008002c1d0100d0710400d080350741d52031040102c1c0d8400039621403d207030444040a0303a4044414203220700c110301c40d910500b515003a80d40405050407680c9800c0c591030303a030b0324035012040080d1010142d841d08010b01c048500480e502480c141054010a0700c01e14010111180440720980b11441d09920703000180004400c1c00005064000206484070900d480742800c507190700c03d4032a40c3e00034894803001280580c09520301034980e6000519409030b00d4a994200304403400003510340c004000142c155100495010004642c210064070349aa0703d82d044207080c00f90201c20b0711032891203181000015034078113801c901c0068000389166000e100654070001034144403003030341d8402805280b903c001c1001151040da404a500c0d480388040400c0c0d42c4800300110b8003a140e00300054200c2c003202d0403446803540800388414841801600c1a450504d0b0f00b070007c0d0031a08513400c1500c03540d4490340f1501c2262110310030280 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 692967005 1250 692965755 692965771
    0x90d08030124111203061c1b0518040f0201030e070608010e0c0f18030304150819090b0a0209030a0b041202011b020a17070b0c1c02070807030e0111070b040806 70
    0x80003041d210500d9a881440c0d04c03038641c1160020200b00e05454920420312001c1c00c0348a1060740d824507150041e0001c004910811507002c08910110b120300d44003208400948400c0212030341e41c1c84a0b1140340720903144203412410f2580c3c8007c00820044140003c40c02043c0544503000a98500305046050b0200104051013692040069014003442d401c156075140300020b41115480d800b8001107461441660044031030080d5860110201030b40c005820340c401c10403e003c50060240112840e0190780c18402d0051060190b81f0004158041c29030280ac0b000ea0001c1c22542c2d2a68181c92f0b2608800c1c080e241650194411040d40701c01c250240525040a0519006030f0302c4002032400c002c3d118411048000c104c004203480c00c0712015070340020340b03450070f030841d01c51030745400d0992030070400d070340044106010402180c000035015480307482607903241c1e40c1148030985060410750b4211581c403400d10040d03050141101466200801c100440c001134055a40000e0f1360301d003001607440c42c0c8100206905 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 692968255 1250 692967005 692967017
    0x50604110a0e13020103150b04170a08090d081c02030718080705011101110309010b0a06022a120f0c01020f0304230a0b0a08010603060b0c070506090d08030124 70
    0x300d4025280440c0c3c4480000040041410703e407004070060704013840c03144440101c049010440000050090044130411006240e801d00d1810721680c503000c800c40c01404c100700c14081c48595040800304040020300c140401c515003449009910754001c2c0c060100c20f1425400310401c42c0d440d403c0b0000a00b4448491441c19545103000010750380c03a0100d002d800d040081c1f0030070002900c8025000320590851b0141321a4980c682801010b00030200030b40703400d2090011210010b50140003003030a081902410003035010700348240c43c00c4a1450207000c41d640d0080c204000b10030710700c001400101d0781004c008e8043c1191403041e000080c0760200d055040c0c00942c1082000b00990b4108070100700b914040382c2c0c480d600c000c180c940045c4015030b06911210750100c0020300b000e02c40398401c000d54143c81036a101005505e07200e4001c0c1259004190f807540907079004030803d011a00d4070901900115900a1400c82d8050055680401e95003003a404100311f0f80c54030681900c3c0042700070480d20fa060b0145420 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 692969505 1250 692968255 692968259
    0x6060f17071e030b0f07080711030421050615090a020406051c141f090c05090108091009110916080112150204030b060a1e0b0d0e0a050604110a 63
    0x254860085100b06604680c0203051501e02c5118000c03020002d603008100407260345016078001004003c12580d090001d100000000c0603180a00303242c0d415186a14025400c2a0030b03c2d440003100b0648a42500204403011205000034004001d0325100342e0300b001c150240043c07501e0034091503460180410400c0da006000900c40c00c0d82c0309043d113009410010700c642c0039800c0d18a000700140460401c0718040400f4204002e402c4001c0e140010039803041e14035604503155903410310011544e0344044400060001c01403440c06621484c0c200d6008a4803030152a20300090003011740444050310f07011100030640780e1000c041c505d884182140d11030300f12075007101c03007880c1144000d1188905000306060104000112024012038122140d503c10b1588411555242c490500d0400c000040f509640300f20071110f00401c0c00000701382000e49a42c4d4900010020320b05041401c60b00ea000042082c00380c0380d5032a040700e41203a080000c0c081c103078091030142000f414181004003011a031024000d018590003401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 692970755 1250 692969505 692969549
    0x106170c010905060901140f0c0d050a09081b0d140f0d1403010f03080f190c0b130209010b0c190c0e01090509060a091509030807020c031c2303010306060f 68
    0x52030301c0c400001c00015618070503480900c00c8d42c003584191019902c104507000b01c80682103002480301c4460303038540480c0d45595a1100b690f881020710130101e06104030000407440c0c00c0c65070702000114030416078010009080040103250900c80010a80e05600001c54070a0f070070341002e880c8858250300c010040c55581408912120000d09200060484c00002500310418100d0f0042d03d01c1b061214160480301301192400400000380e1001c2560140340000200f240b2665602c0b0021602e540600650502d030f00e8400c0070300b0241c01040d82d020550040710030b8500d1002d00000404c18540c41515141640f0303040220b0307400070940580008010501d08414480514000100554050030785da0020810301154600007900700f0003a10200980c608224219003010f402002c100e00c03a040503400c40c0c404410388410142e4503d280d01000d00003000f030307001c1e106109108c5d040140c80381032001c2400c509014407003801e004a500036030090340c5040e0750b0803091188200380c08616009060700750340c03040c0028440f48 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 692972005 1250 692970755 692970767
    0x240d0533010510050a1205040b06040609090b042003030c010501240c080a03090615060201050c0f04051207030807200604050915010306050303041710020307020a0f03020106170c010905060901 84
    0x140f51007803110126820140c1446585408441d9105200a009034100f46c6003c201150040e580c140c480c07410010041a40f40075445000382c99500118414030319150b40d110046c03030103034003010020010b0120f00300e8115510700308000c00c5d0340e2302c14400000301c6600d0b040450201d10038648880c2c084040d009051004d03150304c81c2802e00b410350021401c60351040300c107070260014080c0050003403080e400c0030107960051003600840001c4903003540080c030043e500ca10b0761444a220381c40c04107e21450620003800309081840d1405180c0c0851011a8809501d035240d980d0300340c0103c2030031035031400c2c242e4028590145c100c0c80d0400000003078400c2410281003900141d4042e000500c0405032808800c4814180ea20980090004000160a40743d6a03a21401c0b104034120800070741c0e043c42e22a0300c07010f800250492085a11603641d5038041c00040609588000390110f4400003501150741300c420106209411020343c0c030458002800415510440b00700140c034904103503001501c01c5e0070600c81521a42d82100b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 692973255 1250 692972005 692972029
    0x30c060612072c0103030c0201030501050105160b0a0e0f0d0924030b0307170f0c09060607021c0206121807031218030503030405060402090f240d05330105 68
    0x108201c0c0b00801a44031042c1003040b88100300c040f20704075000000900d1f801c9290b900100e4000c0c0c0e41803105a07201d50054a9a110300100d002200304419215404a60003d1401c4c0d0000e41c012800b00c2c88c0d2190404241c58800420404045508408170440c40355412140a00c02007500e480d00703060401c5600e03ca46a0064144500024143c403920948050b41c1c1c00e00607075001e040c07061610210201189049640e422100700d091405201c0c500810f01c06151500300e480c855a8014142440d0122541c28041c1076100c1c0020f0700d400c02c2400b629680169141c201520901855000c0c2e10340910b031140a00a800c20809807040058008002c14004106c1c11140200015164200f4080141e213191840d0a40b5100e03520107400307030201106010806c4400704a01d0f0040d4022507040d611501e8000244070001c00980d004400702c0b00340032012100700c0701700400c21744541c0c00501c0802454100c0e11183d007414800360f1040c10100350f0892004d441442014480081080d140d02044190304007800b280440183c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 692974505 1250 692973255 692973269
    0x2060705031305011b020f1015030303020a0203070602070605151009061808070801050a0b0a081c20010b040f02090904080f0c030d0203100e0405031602031608030c06061207 76
    0x310503030b80900c8001d41026000c80c8054003032518449000314004c1d12001c1030401881c0d18002d0180c0b40484404c10301078500c80c0c568440c0300c045518919a0150000d5101400420540c0400c1c05140c000c50003520291040d14054080402c0ca442c102154a02e0401c092507040e109901d07100303e0141d0280d00c10b4003441502c03510300f0b001c20100c03e00304003414540003991107519241300d484d40210f807912064210b68080c00401809000300c2110f0700c10805443c88500406003103a1240c015078065441819480c000c04107a0300b45810f1429510f250855643c081d01d5007044140c0d1034003003010841c106441003191140d001c01c0114100b002660006005a0740940702605814021501e545108209000c69074a6803182045a507100703a40e400200c042c0d082101e40364800e144201000540c00304600c01c0e05c0c8190383c00406035140080c0c5941814080c1980d9034240d806104060059400420803480c42000e041600021034a5101c1c0c00d90191030004000c11583c02003a0240f211080030704000341134400e640302 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 692975755 1250 692974505 692974531
    0xd14040b0f040303020d0c03060911030603030f0a0309020406030b15240c0c03070815070f1e030e03040b070c09060605030105013506040f0b03030306010507020604080d1e0206070503 80
    0x2690500b10080d000d1701e01b5103076545160860364078100d03805900c91011202d2101045c4000032001030340600340d000444840d905600100494000400008010883c079501d82c1000102d89203e60040381c100c0b610743e0411100e070611601402045030341d408030020140c4d0101c400d102c40e41c00e012004500751076426003842c1c1d22400410416030903e400c0c00400c0c00800c0203812110b660381d44001039555074131800c0301c105454001c0d50115407007034030442c010100415940c5840a00d0319903100f4052501e28811090720400d55140401241900c081c0300400c01041d44201a0740c8a50080c00c0a41d03484180d0351003c40740a241070404c0002c16040026203046070300c01d007003041440e55901c07450528118900080d02111345c1d03100345c400003c011512414060403050703404000820800310702d43c0c111111011030301e915500c14800514151b01c514010080684058419410941e944001d07600c1c11200340210000300384400049090300c801d9003411102c01d0780a1004021900b040400a0814030000c0c0000c3c1c09406 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 692977005 1250 692975755 692975761
    0x110406050c0309040f0603020112050c04050d08120c040501030e03091f0c050a030c030e091e100b0c010b031207080307051303080d05090610080c09040c0e04080d14040b0f 75
    0x403092042e5143c141001c0c005000b59440225814001c1c0020b002c102d010504443c14800107003094840c0324468000342e0001454103041008111040602460441d401501085040d404400e0014040e02801c40b0500e07458440c3e05080c000740903614421002c0d0515441802018038650f034003000c0d030501c442c3c18040659203c00b51041110320030441e160103070051082250010402d42d1083c03203042101e010755207178031950b881e0000b0014032850a582c4460b80c0070301e00d928400341c18900b074031040e00500b10310302040400c0d41d40d05500081d90800050070807030b42d542d13105004107410148242018455500c615a291142d2613a642c80b0b640000b070000c6c0208a404940d0300303265200000c00b4006981c1002a4546959010502e8405050100c40611701800703604d01040300d44210025000583e2019409030a254441c0c80c1400b42003180140b0a91311b07010802000100f01d203004425038000c40c06420819511940300c808903080e10020035900100121485c2088003007003d4040c015003002c144405081d05071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 692978255 1250 692977005 692977027
    0x1e030c060f0c04030c06050a0e0108160807050919030c080313120203070509010312121e1e06080a0507080c010e010f02012004080601082e1b051c11040605 68
    0x1008540004169030f04040d0045407840c7c000700a0034074810990303248000e40c0e14001c01180d903010255005865410304140254003180a0b484699112015141140c200392081e000100a400f1000c001102402c001c0000d005000e4094a400007412004004514112021100908401c941c1c81001d80541183d0142021540c05200c40320050500410031205c6584034104052000100404080442d038407061303001003018980540c50344200407c80705801e0b103000d2413100d0041e00c0481c401020850205190101890080c41900301401d030150090039660151f00d08540ba08205030400302c0c480d8010320124860f0303a8040d400c03007003c200070b107050034050356040c0c4264050029a0355a0b1040c045002c9607040300848600900300300d031001c20480b00103990340d02005403a020800ca006105508041c550121000109010381e80300f070324640300040c22044800020310502855084200080001030150200d04140800e0030361864030000400000b424124212010710072807242d40144000410b05000e80b03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 692979505 1250 692978255 692978257
    0x9010e010f02070f06030515030d020613170403140f060f01060c06090b0903091509060d0203040203070305150f150f011110020309030c070f0b18040b121e030c060f0c 73
    0x3060b0f606201311010b519100c5c0900908412140101210500c194105540c40c00280c0d501040e0541e40281800d40c441390151a0041000351381950702402e12400320200d0580c1c540140021400b80710052220142c90300101d00f0070903c4c2c054035886a02940501041c0380b00e04011604460041c144140c1012481c581030014240c507080103407c8200c1c0804101c500440440109580301c81100c0282140100707210b03c0200c0d020ba403d07400d4000b0382c00c5c00760300010981c540c01990005d00060484104c550389550300c6103400381d600c2100c54070700180c5062100c210100c980301c40c0c000b2002d000f95034840d050200450701858031091904c0c104480e41c43c0c200301c1d01c0b00601c006010302140801c190342d00d203000b6000c540e40b44c1c07040c250100c25120300b110000308061017620a8054604e17040c412850040407545000d200c0c400382e1a4194407a40d03514415060340d8584a06440f203902c0840500441098052070325498006c4541e244050740080000c01d01d40c01c40822810317441402008002c0f10307512141000c804e2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 692980755 1250 692979505 692979509
    0x506040f0630060806090d0504050d03050c121c05010608041709100c051b100f03020f030a1506020c010f0c0609080c0601090f090f081615060503010e0309010e010f0207 74
    0x2c1e98011860800b541d1103150080002d50b0312403001c07580c45440f0040c3c2c6030b80c0d07540c05641100010300144018410382c03a06420452619000f40b80103420004005880ca0605d920801d02c0c2d9503040c00002e02d02d46140070442414128980f6805c10030503980f42c1132014010a01c010002401921541e80400394000307403205440c120400a410704a0018910704090a01a8458030a5a580c4a00d0f0749507141001144a80301c0241c80142c9180c1c80c40d510382c0c106950b10440040c0706402c1c1502400700000700074031440514400c0070200d80114405086403030b012014401d5030040307000c640107200c00c1e90301a42c1185184d441c1d41280d2400c00c4c0340d080c05003030a8004000503a2f00824914001400032000007000600b141615480130301008050035032901c0500f11110490000e007926a800002c42c04075110344041c001c1140d19504040d030107402c65031030544240c6000c01a884041e0345100511032030900340f0610907079001a20042d46440d0041c00060040b41004007284c0c1009098469003041c0c0f8400e00603d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 692982005 1250 692980755 692980817
    0x160f031e0507030f0f05090c0111030c011a1003140c250b071d09010603021803010f06090b04090809060c0f0a03020c04051e0a050702030f12010503070506040f06 71
    0x5241844000200a80410340c00152034a085c240d199032003440b68450310b4000d86550f4018166a40c503200150788900301c0e42c1018515000c01c0c858410f801c01c083c000c00002c4600e030b00e81d01e807000341108200a030b03900c10420b10000f007500d40400407808503041150581c0181801c080d8546070302c00402c60070144200c0c000000d280d0011715940400300212100154024401c81d1034180110307044111400300903820300641903011040700010083e441c003c2d0700820b05032152030f41d0840003840348070203c0d00703480307031180c2a45107207943e408200300c20b036070034401d980e110a42250207104030719880e2500302c003c1c0038109200f44104800103006ca0110400c00c90000610091416a000240e0604001e516100b040003200d014504220000c0c2207904070380c0142e48044082c42c11003801b0344540c0d07a6240108002048181544410041540f1041854000e45920510600341c28503d40c101001e02d403d1014070f901c082d0181c00288803c0c020611000303941340c00c0d07440e246060000c051402c0082e002083c0c86410400b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 692983255 1250 692982005 692982011
    0x30708070b030f0132010306091803090602030a120b0d1203020c19031b0309080f030423130203150d050c010908161a09041112160f031e 60
    0x480340c40110107184543e5901400101c070760380e1000154030b41500d600c58280c0e045508141910007044080d4241c0c1d0340c500c1890000b440d03c0c0c81e0f40680d400c4403104042d1400d0071080c80e00050805a000d0182400380c0080c0c8055420013012090103071030151150b4240281a49076411040151110101140c486130007052140d81401e03048009030082d442803001440c41d01580514104074041a9a52583e40d0b07410396540c80c0390031240c165401d44038200c01044040103034250b070000d41180700700718040e40340a00c40099036489103084884d40d041440c0d0880000d485500f00c6d642e81c0f503a640c0740f10141290604d080003503902d54410b0802c8c014500880095035111203485c030700030180a40098903d010b404281c0b2a45955612010000e80d180a0b5330f00b2100c0304d451074003051010581a001080c44003025448480c184404000000e0549a8110480045850110741145070002c40c45125800100c0d0719250210400800ea00502e010b10300d0200b107080c507440d8001c01c0e200841303e030340d40328042054207010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 692984505 1250 692983255 692983259
    0x16020c0d062403030311040b09010c0f12030b1207031a041a0c0901110a08030a0b040b04090305280207060f021603291e09241b1e0903070807 62
    0x8000e0100b203000a0740001d107003811500034081240100c40664901d00340d40b5080410300d200445828103030360700440f48418401d1040c8006a69000c000001042c240c601041c0104200140701d24100810408200c41d401041c0800100e5419003624011040500500715507035914182080031880b0454040b661428030000c00c801640c54101805c4140fa091380c0d6800c04444400750310703546030140c403c040c16041c1c0c10400303e03805905a611484039600040d00100342040000b00041c1100c1c401003054000c07400000d0844004ad038022107117011000c68100d513080c10b18200c20004c1d0b84141074040c03001840f40300e00d40d2124960080010000c45040e00103c40d03002500d038a49142c00c100c041000d05001c0d8440c942420340241500006c0f4440c0940d00e82ca0300061064842c2c00d611803201400b000e001d80521041c500840030900e07600c5401b002c1032210400d03142001d18080a440002d600d503941c100d2420300030b0b022000d55038120001d10644034859940c8450810300041c0c01c02007940c0c0810380f03510400c800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 692985611 1106 692984505 692984561
    0x60a15051905090c030c0313021513030507090c1d012604050601050d210203092d0a1203031509050c0c010516020c0d06 53
    0x1090016600c00c04a03141d507915200100748010040e105025504100040c144c101d9071514042e41745140c0307410400c3c4640006040303a000e00d1500c441403800e40d0b440c0c4074261a0b1181c84a00300faa60401914020074010127844119810f0184c0700c80069007905920441c40f00d1903140c0c950501e40d0324409007142d50300103802c14140c180f0045401c801c1c10045501c5038000355030251141402ca0381040d0615a00d01241641309502c9141c1030398404c00002c80510b901321031070300201d0f048031110020840903400d50040f038002e560426172542840c800c002c8024440e00c07019082c09030002d0000c007a00180040014107000f00404d01d10051401c1300001d00c070798820900c03061704a590b020001d44a807102001d03168280d42c096800880070a00ca19104030030b02c103a0785c000121039100d40d140b0307240c00c1002c1d440c0d5640c5102503101e5501e0070220814000d65400010014a10340303240308505c011428 = true := by decide +kernel

theorem cover : BRFrame.Cov 692805755 692985611 := by
  have h0 := BRFrame.cov_init 692805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 692805755 ≤ n) (h2 : n < 692985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
