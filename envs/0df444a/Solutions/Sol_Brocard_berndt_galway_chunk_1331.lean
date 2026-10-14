-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1331
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:25:03.204981+00:00
-- url     : https://prove2.me/submissions/e798d55c-ae0a-4818-adc7-ccb4a93eb9e8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 239208633 ≤ n < 239388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 239209883 1250 239208633 239208643
    0xc060301090b0f091005010906050a080106080c070c0303080618040b0c03041a0c030703060e06010e0423010320010903030f0f050d0905010e0106050f0604141c0b07030c05040305 78
    0x103280441e40c0c460140000319200c100000b852608050103010091410801c2408440c0c0c05104150001c2c0d500600000c2183c4158207550740c1c88645c0c1d440704d10036440d00e00c048800f950054040c5124580821007000040d540c4004100118425218a106483c1ca0400c12030201102c404200c900c241e0b4a007000001018004600d174414200100103880b43c907079041170340e00b807030141c03500347c503078142e6070003400440a42c15024610409130b5907401d2025685858861240500c16103686003c0b0b414082d01c04401e01c0c00b608418036240380c036000b0340c440c042c542c208101a88405e9100b5034200118010718149049281113806907510203007021401e031480d680d8001d180f05402c1c05a002004924061070000c0f40c4984112a0304240144c03050042c10700314201f05000344030400000f01190b103420000903845c2031082c03203078100100c020840c1d0f00b024501000d00c480c04002e10b14403503001d80c2d0700001082d11807049030300b210814010b602403401d51030000f10142c00c59420014443c180202440104000303180000c0d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 239211133 1250 239209883 239209889
    0x20d0e1002070803181f0e0607030905030d09020f0d0606090f05010501300501080d090614090607020604030c0b120c0f03130314030c0a02160f050108040503091e01110c060301 77
    0x80051881071201100d00303211508071b00c1e0010080070b01c80315081150940241d4111400181a100c0907240e01c103040c0e040340d2201c400203040f5002448000c00e0b0400c6580a0080b95001a00c00714207007100400247c100c0709505400c4924544c0c48000348074500c0280300320850b4a190a20401c450750524002070321840341040e50f00b240310651400b84004440c0c6500d0b00002c0b5110300c0f000c0c0071030b584510805031a20f010101c4400000c2c0a6000081c02e548110280002c1c4408a5443c81c40c0130300c07400c140401a0700c510003c1c3d800680400c1b001001440604000005003503490700350380c0710740021142403143e02015120440c6808203008010001441c40d0840f608020010082c09070116646019a90b11600c16000d88415101004003d204c0e50514000e00b03101070b403607090b11071052450007070080e4031103203004800d98501c03200710070b111650244503c1da030014010b0301128203004040c800a456050f002403443d008c03d80904510b9800d50b0842d0b5000c100303410000261843c001107802048941c00144 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 239212383 1250 239211133 239211151
    0x1151b0321090507090902030c030106062a2003101104060809011b0e030d0903080702040510080d0203091807080406050703090203010504060905160608011a0409020d0e1002070803 79
    0x81500000071005900088101e94400c007542d034a15910191a001081105000c2e4020702501c40340101c90714041c840c42c001e5880c03a031a041010045094056055010320f064901c0054102c10920003107917511801e20603020083c172021007500c1400c0309140c10180002000142c55003082c01140e030315059030050f2410f0321403519002e07449540b00452107024080919500607524515035070484032a601c29462200fa000030f5080340d200206080c01220469164800a004210240035200051030590403141e0000440311200d0010382c3c607840e9503818400c0b00b0240a015074000030300c40c011400c007520442d0181c00e09103024102c500d00000050241e01d070050000b403c0e5130f0750b10000b60407a8065800b244020360054020041860f0070700c0d24000802a003d01902c05115140141071500805002c6106071452a5030310b42d040e928043c1c2018400c001881841c00140c002e200100ea05400d0380302408170b080300d030b10011030181c0340c90840b5030a1442c013030b0381394424a00401828000c2100241200e41001d040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 239213633 1250 239212383 239212427
    0x3120c04030b04050706030b06180d0201050915130f2102152101050607170a020a0209070302180102010506210309210c01020604120c1a01151b03 64
    0x4490150218411900010508030085043c4014000c00044070010b88003261000c0000b03048000c1044201c0c0242003130b4043e00d400007884d200340c904105a040710301e1032043c103000303080001c6d010000e4681c1c149288180610030012907200300e44200c40301194010498201d64441d014101001c0c40d025468013408811880701c3c040d624001c41d00c80d1070a03001c40100069070345440300e5a01c104901306091000800b210021003034008101c515114003101c141d41c0c4e02c02d80d001c1781030404d001a43e513240c020103001010b50140040c03100c0580c4441031218840c030100d681c0180d82e10404690006154270301d407a02811a0b15003410010b090710703503080c2d510312501000c12001c00b82c0c46182143d841d51068200b507035001400045552030a000411002620075820820741e607420152100481c0e4800c0110f0b8090308a00303840000d052201d000c3e10303124049034010a9001160700181d00f000c1008102a4044910112000c40c8546102d070f01c10f9140700340c1000140015010f80391900d00810041003042d0384030405021b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 239214883 1250 239213633 239213641
    0x6090606090d05030d0b040f02030105061605070f0e04060f0b0f042c01021e070309120303022a0d14030403031d0708030405040b011b031101020708031015110312 71
    0x11180b4800005500004136941c4000181c64007002d040d10a14031806203041c0300084203010850700075241030780c402518180c20550340d111000c1d04032035810415580c0b3301510345c011481080f0b4010040140c030310000c02103041d080616252040b900d0701100300c42524030f00085a0001da07140b814080301c030780d0f04440100b16040030303440c0c803110007a80e20301c40300c0070800e01e00b0703110344c20003041d0094000c44110940940c50092000b444a01134862a00014000b440882c001e10161031060f1840e80007901a02d00141003280d654030307a8840d800c00074003049803d0070920b20030480100800014102601e03034a440c0301c0d6900740d1110714240d070001420080074192500d0b88881401103001c511034461490500b203541d029541c4074a10745960080c003a00780910f0078012001003e5000f403a03094510901d10904640d40714103034400f01c80303210803440c44001c995000c1001102243c00140903500805044072040b00c1645080700e0034406080c00590f41d41400081c4130800100003012041da0000c180060100e000c45e91 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 239216133 1250 239214883 239214889
    0x80610080f1c1b1103150f0106030903030e16080f0102040b18030c0a0303050c060606041503050408090406170c040903020601171e012c070306090c0b040623030609060609 75
    0x1a0403c200211080c40e03991150602c040c1c81c038007180344007060f820303a0403000340011141194a000c45081010700f005800405c1254829402000224001e103000102860503010850a04841d051b00a0364a04290000d0024110500250201c140108000c628051425841c0f5206000b0f01204c0403961032079403040c40507520240049040414010301a50340c241d01c87c0b070060030a8105180c0e00305280301e11400508581011030849068454410400c0e8205002503c214003030301009004880d610f07410300140311541c445000d08000b0304041c40000d038412418001444c034081c0d011108500c00d42c101120300c00032a40101e04c40e810340c0c4400300b11086148208110713605d0190000c0b80300101c450400d14064005106600100241ca100d0307104820101528a04a860f1014031040c0501c5406c1040c0400001d001e5500c0444028131030802e1142a40e90307220405010b8000740e0000c004a004114174015400c2200020009094804081420750804030080b884141000300480d0050300c4c0080c407100940c0e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 239217383 1250 239216133 239216147
    0xb04080a030c020f03060702031902010c12090309170a0203010b06070b01050d051c1101050f0903190309050a06050702060a050907060f0c0b04060606020c030307080a0c031404080610080f1c 83
    0x5030007500b102c54174140071f03100a640303a1010310814490800c00703850315480740c07046c001c10902c10b08540d980d000d000601da040400038004074000300e041c010454400035280c1030380401c0c054080a804080c00e11090540103050035600c2c244101c501c188400c1005200081d440c03c402410344e90140c0701d0781c0004246c2d141ca03d1034030310407981c1544800c0c152088074402c140d02142d0040280784d000c5c02400302c0d888d08550112201001e44901d1a95002030011188400a0342c0080080240502e0045030b04000e5440b41402c102800205661881c2c44004001c0030680401c1001c0e0003600c0f1600800c9140f03040000691510218002c840400c0492901546c1c3c0c1c0b88139501000400d0b0704103414000030b04040c03806000a201c10312540c00540240300c501103807440e020040e01e189030381007403503589441030405040b6071501d14150101d0038004541499090010000041e1018128200080c002ea0130000c8040880d5210b075070200b000ca80c4100b601400c590400b0480c0d5105018070848070103080c0e0903000030b440314 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 239218633 1250 239217383 239217409
    0x10f140307050c031204151a01080601080901150b03090d05180904030903021305040c0b0f121b04060906030609020702060a03051b07050a0b060105041d0406090b0f0403090b04080a030c02 82
    0x2014145d424082445460600b2540d6034031100d10800541c0d010001c950422102a207007180401c482c080001e915500814403154017540440001400d208440030611040c2c1c61900481102c00008c0104002070034104000c190300009030030040d040640c2a0396180081412521050185442c080172408040c0100d0030a800b0b15401041d0030b600c92948030426004050072101540c1ca402070b00000070307001c0c450341c0840d5803060310207107110b03d000c60402856001001c050140d40702001d410b40d500e131035540e41c0005007000d05065a00c42c0c1a56160101c0101516000d402004945204001c9000140d56981c110389000f807180c00e00ac2070703e903600c8550000c902001c0d1805032601c0c000240d0341080140c0800c52114640c41111010880e03100d48004444601507400327040d9048006070f61001035000e15085095100b84211004a4440382c03554504020000903070300c4015002d00f05051004040d0080f126001500040c49054146031070800d44559404802c0400340c1031010614005081d500c07009141c20318 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 239219883 1250 239218633 239218657
    0x3121107090203131106090f0402030421200c091602070302041a040f0e0601030f110406030f1e03050301140301110406090609090b0d0303050a020c0109080405010f140307050c03 78
    0x1d91505040c042000200c4e110102d0301d0f0691105101c5291600d902500c01c942400f501e11451840b00310f0a1100951018000b0b5448d81c030f840e81113190030390f403000000c003100c0e13519511246501180d03404891020641c006d08206034000080340c6049854006802e5032100500082142c3c1c2e802c0010260309000d203a420280d000350500011540751684d9891284d003214007518100314256541480d04200c801c119200c100640000c001000400c2188644200f9103005a902d541500c00980014040744c60075481110a00143c180740010b0180c04c404001c2031f0602c00f070398070100d1030303282c0c0c6d004181307100c140221014591140740010960b10254021341e01ca8004c00700b041e5456448140140841c0c62620030400000d01000020810244c1e600030021003081c0130f4101c1d00014a155400c0d0040e2a0040130316800603400e222002002400340503c410381d9020312031450381d0340d0420000400c4480e603030380400305101da49003584500748000d40c2101d030b2290340e6142c1a921106038807001c0b400c51050b060290b030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 239221133 1250 239219883 239219887
    0x3170a030b1f0f0305010b0a0c020102101e05390c0a0501060504111309050705070b07170601050a0c23030301140109061403040b1b120402090f01031211070902 70
    0xe10100d031070200510502c10707500c07944001c03140c5100450070349409000702143d00c1c60a00568040c24040c921402c0170030310500680700b040f03a40020940c116600200d89070020100d0081040406e003040c403902d42c0100c45441c0f0385422081c003550b95a1461803680c80c0140005800f803030004001b448406540c0300e5480e078400d640880800303080c0540a8161800340501c100e2400d40f52140040c0ca40302181c40d000101c8030811071f101d191100d248000c0c4002007414003885820040b01d000151243c5241d48111219141c001c1101c51442d0b0080c0351900c024622418030400b04172501560740c0144071b440c49654440c0744031249403010503e05a404080e18000d40c40c0303210101c0080b4455040755918540c00c007080e40d0b1800c9050340c62804031000801468100d01c8050304101280100381c01c001c801c2d81c8400741500b80030109440c402e84c810117031b025880c11021700c0400001e0004501e407603d1070b1500107402215551885d415521054a40c0e003241d802842404a40000c0c045d5124090200d03600528861400319 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 239222383 1250 239221133 239221159
    0x209100e1504020d0905061e160e1f030510050402030903040302060c010e0d2006070504060f0c02060c0102070b01120b0f07030e0627070b030a0c05040302040204060e12010603170a030b 81
    0x25544e65023030360382c4000d12841c0c941807010310032040c05a038819000704a00c14000b50b9284400c0d50314403114000703d50880f08044203084c3d140000d02c84090745031040c0c0d42c0040c0502d010381c824400115a40c01440c480c40c010001d10400701000010b90301520b804580704c950303880c0b0040300b050041409010a401d54001c410b107801c2560317000155003006030780000345e2105441101c60368503220501200d207603001c500e0a01c418406240701c0c0410002e503180c0c03402c0150341c41c0003e400003079980c0c01078591005180c1d0002003020401014540d0b5900500f00000009860b1101d0355030719510340300042c00c005445420400060f665071203a0001d202d954400000d58006092400081c0e40003540f400301c0c16814000c2c01071812400400154100490b00300d54491401e40e242c510b00c040141002c400d840c030030090140f00100259540784024030042c030381529202d10416482c4203200607030a40e48084485070f490100204045035012005906c440340b9200c900c0d40c5d030042d1074000e41c000c001d807441103900030a080e12342c6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 239223633 1250 239222383 239222393
    0x4050309191e052107090e0c0904080301080c0a0f060e130606020106091b08010312030f020f0408070b0c03030a0b06121302040e07080307080d021210030209100e1504020d09 76
    0x1c40b054800980f4000050035150f16204850320215141544503070010b0800c00004200e40e0101c82059400010743e9540c40b080b1000449400b0196001d4034401800001080700e0340d02008000c000503c19503105000a180405150005629215002c01d105101487c0451940c5826164410384200e4904010710368803044001d0080505002c3d0812052a101d001484a44c030312810070080c5a481e5210640c2d41c3c216604c03c0d13000f05180900c0c89c14103499031800074400c00c0c54006030010b880200380032625245004103251410302640d01016a8000400440c14161004001c03254011105d00740403c40102010100c2c50382d01c82e00d030540e0b000f02c0703500c0103000102d04804600100c40c1d0085a00703000900049207000c3d1118510b206040c003e605c20810b00c0c0024501d40050030080c450a1001418068403954000380100d0032101c41042051504e8244214940190041d810011070b012001401c3c2c1011801450b800d03018291682d11038120344404820741d0307a501190303102082810140854003061500c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 239224883 1250 239223633 239223689
    0x30f0c100c0c0f110102240f07140d0c0e060a05120603120702041a0409081c0212060103020c100c0306050906060306030307140a1a01060206060102060405030919 71
    0x306841e06140218500c80d2207481100076460704034588400c141440e0755040101d41018603000e0550241d5150341d2051140d1010710f030040000303403101007142d1170084100409100024a0700041c4405c9003102045583c20710148d51080741c5150f800900b001e1800f0741990404400e61000740c0c00000000c4276441c003270788203000d807500604001e10200c1640f100380400d91076072000c80e12091020028804900589020f4000261848070311104800c510300980204095881215064890940025085540c8501e602c2000382200f00950110b0801c0007481c44031203000c1024215504041c3c0101c0d0803c0d07854400d1010221104040c43c0400c140340d0382d40341c05006000d840c440e90b4481c0b43c80e0000500d041c1840760403640704980081c00b441c5440844c6d0741e0000d02e0001643c5441300c610034150070070001420350410804002003005c010207907615101000b4542032000f040c90b41150080c40c103000004400100392610110100c507400d619400c40404603000c084142c0c40305403150002034881c4180c0080342c60f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 239226133 1250 239224883 239224903
    0x130c030803070e1c0302101e05010909021e0901050907031b02010506210706180305031c0507020c0d152009091b091509060304050105010801061203081602030f0c 71
    0x348070140900d80d0791084400d5000c1413400760158228041c40d80741c40c101d0b980708400d8a070340c1e04014910310050501c802c0c12154241c1141d035070300e60754900032402e5243c2550ac00007001c4580b064a10412000d03000304c0c0070280180300e000d000d11025004106083d000342c00c050355034018601ea2203a50158514001d02a05080d50401e0003000c0a81c0103000345403250142629410000005161182c07030448203e0b211100346030340300d44450011002000290080c0020220200c5e4160300e0f000244803400000210f0710094103040a641c00700c00103041d04d45844403034924887c0c00110850004c032141c440343d0098901e040c199001280980d4400203410101400b9207043e40003502c4400d401e9a40181e2a00d0710b00b84a135042d80c1d040b4090040d60018a85042c011802d60894030f130381c0d814039000da0b001c200141c00c160ba0450301c1d40d4441006112840c002d210704c070000e0a1908440102d2449903c0181040c807024000c02c1110141c8e41c1d038002107900810883d89141d41c15954181d43d0808141c1007611041024 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 239227383 1250 239226133 239226139
    0x220609120e0a06050f0f0a020c0a030609060f0605210f0a1401060803091e060f0403260a05091207030807050a050c040204140904021813110d0b130c030803070e 70
    0xa0b004182c40f80b10340300350344500d114241841e11b8644070030703203400c05900b03d060748501b18821540c04e00030984400c4045002540f240307201050482c1c0b10314007002950300824040ca4028a403810402407551a100314044480344059003580c00d00c400d00c00181405c0800d104128244140030001081180b00c1000d40f440e00103800c020811640c031400b0407603c0384610305800742e004408610f074070764030742c011011542c4040d0700901c5913251a40d2503a8208030754001d0760040e00d002c0300b40d100c0740307540d50080005c02c51540710030200945084a4840050594001d103101c042c010004440e000c007081e00b042042401460708064501e85a00d010f152095880311204821100c5018800f1180707543e01740740c000e032026122403030413078800005501c041c400c0042c8000c0090341d028140301c0c40b98040100304a8014099004882441c11032201410241c4459070030444072070103070f8002ca00000208800c1204180c12060074440d10b000d584c12400e0542c1c42c3c201d241c1028110b640000301703125250b0b0300640d00000c401016 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 239228633 1250 239227383 239227399
    0x703060807081b030607170901020d05010e150f03030307120e2b030c0e04020d2a090506030408071e0803070c020901080a05070b2d120c03220609120e 66
    0x1503400d0544030345e025984280403401e604032030318041264901040d48420b08000040c1000d000ca504c40782075600aa10404580d1524800c1c4107044007041c1036418101016541c11520068038030200740d40c1c1c40018150310400007a896505a508100e4100030325051804046030303480c020200340c01c4403403100c034103a0240050314151000c1055020b1f01800703c100946460b240c0360740002105120295000d1021a81c01a03600c541d61000318201081110320f5004255954910300c0445101803c0b198040d00042c0c401d031800c0c03042200103403e5804031101250700400c509444c44001c0d0301c0703044000b4240c10040038002e0200c20030a410b0344c030000c039115480c000c50703518289907620580a51100400e80d80900301e0382124205200714112603006004502e940c14260300b09a003620304000000c601e025805860280009007400070140c1300b4003454000e54207035030703040c61400d000003502c41c40c00710400e01c590614a25240c00c81401401d920075a20690020100c2003060740410006095551549425100b0019 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 239229883 1250 239228633 239228683
    0x30709060f060e15161a090d0f020c030c060c2a03210d0527010603050c0f060714122208010c0c0308060f21010509010c0c0b070306080708 61
    0x14021010400e11102081031800c4080705000142441602c806e40710350400609018408600102c060301c6170b10030f84d0284c0044400404014940c80e1122100c008660ac200d0b055002e50707902048110740d80d40100e0309955900c1d0100c44c4141050301101c4008081201000c407140541c003010714020210404400303565180c60801c41090300c1d401d034900d8000c10350030300303005000c01d1000781d920154010f03c2d42c1401c3c0103007000b44086040003140355600040e250f5101c0138100200201086a85040d04046450a040d43c1c00040460790502a090f0050003075075181250040300c5500b8011a801c0c00300c801c02c0a81c0c7c42d88041904011011180e400342c441040b542c0380090503150610514040c0010b6a1310304600c059252000c4400c40805002540d020740d4121b5041d04559444082d581140325074011520220b455647d41800c580e401005948a641421984001c181d8002e44003031580c0d6218607108070a0311411400c600908c07098024410900ca503e00115008034002004050340440110749900a01d07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 239231133 1250 239229883 239229889
    0x15070c1e06110105073f0b01020c030109020303030403050a090b13150c0305160218040b0103020a0b09310f050a1518020a0212130e07021c030506030709060f060e 71
    0x20048a1500000d0500501000c400c0c8603200109500c2d5514298031140700038407800300c0006e0902d0f40a100701c49541c0c040e05001c550b014440002c00440071002003000156036004130b2784a120040c4001c0400c840000c507407034154001c198140190405414a81d2108084580c80072214981c0c0030b40c02062455150081166224140c802c5855230b0595034070f802c1954803041985100c40004080340d20914070044e240700e21607200c0003284501d0003002d0541c02940746005100340d148554100d010007035010040c0b00500d448007000c90070085070b8041010140c4800701500085402018450050b032030800b44011503801c542e410880c040c1a84840803c070b80301c5608040d1b462200c41384a0031104030319000388440165946d9014204048050042e03030020002c86c2880c90066000d0150480156140c2005005a50b0b50742c2e447c50380003826000514140580d40d00318000b4031846030003e000c1644500024405031800c2c0f0411004103003150040c0035494030b40301007840c011003034000d540008444c801002130a103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 239232383 1250 239231133 239231141
    0x60507211d01050705060a05150909120d090b16090902040303021f020f03010b041a090607060e1608070816030209070e01030204050907050711010e15070c1e061101 72
    0x402038840c003200041000c0c494034080840c1c007900c0c1c1401001c1c40608003283c820f010302031040500310b82c0010703145440411400b448248121943c01070b0244800c1040d040800520f58950614050016031240789500540014100c1400024170301104c1c402408201106003114400000090301c44e52a1591142d2080b4228003503840060300580c0402c48840100111103031b001c0000d88582d20140c035040e030246c0000d500354400c0c0c2c041100e103180014104412a04200b40110300038803011007a01d00151480051024001c8660180241d0f6072541175035600395040121060582d40d0307000728008103076a140380c03a85400e0035200c0ca01403405065103d81d0034800394140f400540c0da0081001200d5101d56600300d400da49002411418142c0c20400414581d407a03009040c4035074260f80ea207564442d00c80c0761003401c00c80310704c2c1e14034141301d02d100c4c40360055a110000c0c0000000c051320000d80b244501d0420b903a031550303164013515080050700101724440e08081e0155017030328241c0e100c00c25040d12401c029400c0f5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 239233633 1250 239232383 239232443
    0xa0b0a080703110906031e01030f06050c04050d080c2802030105160507170403061104060210060b1c140f0915090c060a02010b1e12070b040509040309030b01060507 72
    0x83c40100103407800c0c1d150050245400051100b08030600950896010001c0c16003070f00155961011059618208030382402410b0744440340140c01800c0c145480c0c00f04440745540c1c00d0042400d43e01103903d88448404009085084e44180940c0a1030780f12400803507648a40c0c00c206a020b9403c29002980c48240d5400c1e001a00509582d03140c9050903d13110407255013070307410785255040790400c800070205505004038004240c010b90099603413441c0017230107450804040c44560301942802e504022801080c0b080da10b60082c00304c2ca0700c1403082d8809404004010300a119082d4174925414407000303601c044002031040142c02c084902450107404254092a42260340c1034aa0740407003120b28443c21711802524441c0d08030300020441014100028444400903280030900c0d0152412180041c41c1c02c1e09409104500e503006842c0c16410003007140114451400f41a014120403404075040500c240b81181c002c5070020805040d0756155800105158403114058458901e20544909000102c04000c195 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 239234883 1250 239233633 239233661
    0x180a050c01030506010c0c0303051201170a0803130c090506090106020a0b13020d02031b0a050d02060409020f0405030f0a030f0e030a1103010f06080c19030c06080c07020a0b0a080703 80
    0x15044030900110003400c3c0040034981000100c5080500203000480d411010390700c2070b15450f840300c403088404454060160300070300100c0500d00941000003030103e962003070103800030102566540d0b11496003c110001d50303001400d55004200003c1e2074032960340701a004480c12940071801d81d980342d008907640c070000c48001d84084030f928041240b2100d24001039414620180641101c604c2d04d8001034203250306414510314a010b44403400a00345072800705003002c1c1c90119440c0799000b886401040c180d004600880401c5540003e42d10b16800134141a6002032400404554a07a0341e020b4095803601140c2c20200c021610740710801042c02e002c1c8001d0cc0c0c500c040a4020498000d094483c1c42e03180041d442c040ea00344d50b0381d0010050688190260f0805408600000d0900c10201014400b1810000072240c20300214040c05000280310085d908007190325600d80030810b61113541030480386119501d4029840398540d54001241d04810024042040081e21850480d549480d0298290b4441c40c5c0d02d992 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 239236133 1250 239234883 239234893
    0xc0d03060f12050a060c0c03030b06130b03190207051c14030f070c050102270301060e07050d0605030334031e020a12091a0c0307020f0105090405040605180a05 70
    0xc8180b03409101d92804500603000ca07950302400342c590b01c0c01c40c0d60010000b000500d40c1e0355008289a0075006611524006940881c07800e01010303070558180c001c5000d81c04900c0e400001190b20900003400040007034402d5542155215014074095607160343c0600ba201030f110301e1900d4019181c1c054500281c02031109406180765a4070881d210086e020020004400e001e0803e642e600442c2d02440500b40d894044040103019410030084000a45004103646210f13030f050200c2400507030009400c003600070996050a036126108405c0c448081c1c0425040039406100228414600d0031402c90703445050003560300345c0310501e43d24460005000c04500c0f00680801c40c0a0004540c0f861116400c04040c4943e02c19102c02d1000c41c0c0d12104170f804650070040020b0b42d030360b81c00d00c411244169086e0840f000044818640782c8502d1026449004070700000e8800c1c030403409100c6a5902803411184656802482007085181500d040c40c01460103585508890b0640110751a44640000b070340540c0e070341c004c40101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 239237383 1250 239236133 239236139
    0x515010612110409020a050d110310050d110f011b0302011b03180206130b070501050f06031605240a020f100903170c07020a0801020304051507171503070602030c0d03060f 75
    0x802940c40780b0880e80405c0800c01c41023110103080d00c40c1460301600310765645d40c3d03030402040c00d80c280c0301c0a4210511400c0801010300005000091800c8920015940555112000c1005841c0300c4040341c4807221400880d002d190030560306601800c548446100003a010b9004100c0071801c48042080707290108a00b40300240241c64064041d09030281c410034880d00d055200c0e80030b02480d070040d4a04540c00e0b0344840074049809240100319501140c10740003004001401c1a5034448080d1038170030035000b101028655000840b000c06002c05000382400595964000041d000b5511b82000f90080751500070b1101d40c0e075550006006501d446a007542d240e00032070707003c80345440801310043d26010903100708220b01c10050b00e80c0369285000f4840c150006840f80780a041c401c0c10004c0200c84036060071210f50400550a40150302c8000b8811719814242035a0f8a604010303103901c0a0021071a0300d0300c42c62600142c19a400001004920244000c1c0d6a158015600650079645c6030b000306d51007600c05840034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 239238633 1250 239237383 239237399
    0x702031e010209040f06090605040e0d030203070c0c031209090c050a03020315100c1401091a0612011a010314160f14030a0911030c1c050a05150106121104 68
    0x108280306094000524114901002904603281a610076080b1603c5080c1041501458440c000007000143c0f000d00810608a107596160301510015070b05141c1e0200100c1c0009110b101a007a038580e1001c2c3c0d246a5903183d003003041c4800c00c040c0c01c0f000040c203111004503a040603805109001051912444c0c02c0102e5290140d019420040c0b03210001807200e5542011583c4264201c00344503071076200c0c681c2ea0150b508124004000c52146a81d0582c1080354000c00200b14244403c1d180f02900080081602c0c1d09000594480408030081c4107982000070040804102e008081c400300f1090b2401c200c0f00c07807408004030080340308a4030881e800382410342c2c0e125034500410851192413690319140365101066006550107802c01d031445400030390360300881c00c1003100c480990003030140214010328001000740001107601844640404054007030080140070000b00700702e8643c121b41d0003030959001401d4540b00c020105c40c2403251000044048503d907810355054840c00b40d140030030007281840c007824900e031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 239239883 1250 239238633 239238673
    0x111030c09042415020a06020f04060206010602160b070609020a08010b012c06030612060a05070905010e030601091a03060112050c0a0b07060c17040f060b03030a0c06090305041d0714070203 83
    0x1607041d1b01865140e00300040c10b602c0200000c0340c1c1e10017129210b1341451002440c00034140c200c2002e541c0015a8040d5144074944130030101c9205007045aa15034051409002600c510a0001e40040d80c250002c035014006402c003004007403080e0307201c80910202a640c080d07101c0d0300f10300d0310070305200035040c8240d507090610056a01100141030258964580d440a5140820440f100700e00240d459043c4002c03654030240c2c9600900e000d00c0d002c28100c601400081d1901300601c103030038845554459404444060400580e07800c000141a030b0029a5141c1d0b50111000880d03104640e14020f0a901052a1500c803114000340c4244c28102400e00da881d54a4800804c2810301210030701806c5018a043c200030605a28840e41c0310b4000303003921404500e020819103d60b02e19880c4660420700245000c56400540401c1142d08103d01150008942c1015121403095030481d07031300800c2c000c1c0404000c0c0728000c20765000c1e4005a54020300740a580101890320700070410020740c9a007260440b4420603000c510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 239241133 1250 239239883 239239919
    0x510140d0305070c060e0901050a14011d03012c01020f040603050705270111030c100f0f0c050301080c030304030f0204051b0c071409070905010807020111030c090424 73
    0x2842c901e0f050054481c21641001644010001104d0054104990900e000d5560061000343c90010b40031b804d2103148035202c3e000084160400c1103124880b41e10884010b000c0c44022800740080107108080d40e00c1101c0404024103046108058200e001004481407007100c6110740868401800c00c0e080c068120003921010741200208070f000e0102c01d0403a41060320007803000c20821518003020340407600141c1038064010800600ba08180403640140074081801c12200c06944000a00d943d844a00800280245e000464209107000e600b40c80c041c0d00036000314180c4080302d00316a04855000201556481507004c002c060248800c054001410560403003034100b90101201d01d1180406100d90b10507400c4200f0383c903902c0e48400c0041244061011503100b84410a030f50030829441c0042c80070341001e9403032049030f0411250303130002450139100303511069400804018182d900e00346508284c01e1a00024250381c407451800010b09070200c0020401300c0c10358245050300b0417091812002c005200d09083e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 239242383 1250 239241133 239241137
    0x1703041e0f0e0403030507080f1902040312020a140604080403030507061b120605013e03041d060405040c0509090307080d0203040501201c110d06030203010510140d03 73
    0x100c0041806807002421001402a51210780310324641420014203691001e0031040c00d00000c0c1c41806888a0880b07074441e40118800b005421000d05d025100380240300e01d50024124000d42042c0d010502c0e0701213400e03003406000c1d00203140d81d15560b64400d0381b606416a0300401e002c40c10802000000d005601070100c02d40110400101c0030003610b1030078219403034100c580c0c1c005090300e6000040c5180c80e00c12781e4050842840c0c1482c06204c0d15802c0d03840080c000c41c058407a02d001d5107084040040507480e440801c1c04550540e911180d40e50003c22404040c580d1100b600303841940051601d0a180c804c44e840f403030f007004290708004d00d0329003840880072000d0b00180d903078041040100c0205914000030b003030049001b07a00603582c3c90f00f400e00c00d0840304c00c02000030708210406850814040d4039804d40703900200300820103800b070020071a808001d10500400b038050340c801040c90071002d1502e9001c0804c83e03001b60000c2c0102d0740c40102e100a511240e0044080c0a6541c4940c880705d42070114800c10a10b11134 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 239243633 1250 239242383 239242439
    0x10609060801061b0c08030c070e010b04050d080706061221030c02032a07030803040204060b0705061f0f0b070317060303040621090f0c081212150a0801020a0306170304 74
    0x2921b90141183d00031042444035600c100c10402485c6e2004030050b0041c0b0f24240000e0030181001c00252140713800c101c01519050303012a8000c24041c0d65400f040c0202000348102501a10340d1805005100c0c409030000407203040318142d44101c501038000e0001c818550380c00344d880e21321000d0180e24040b03c209051140d04021001d08000b103242008107501950007003162a0f00c0389450720400054030050f0700440c6084e001070101d00005031b80094241c1e00290320f40781d0181c012101c4e183d00d5281994503400041c03580e90130b2700000340001100e00100b0790240a0b0383c43d808010410012a41d40744400c1c0d0301c1a0701644104010040c0b94403450044046046151140c900c2d000801030480903280103000581c5c4c440b0b42001d9040401c50151040c10042100b0f0303010345449142c000d0344c8261406582c1c68544101c1030300c4002000b258100d02800c0201d00c00400c0d4400715503c1c1d80401c1c0c004e40101003100e010a140800225241a1b07007240301c046070018800443c5058201b460405040c0c00e032900043d0030001c9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 239244883 1250 239243633 239243639
    0xb100c030818070605071b050109030314070206030f0a14010501090b1b0703060c0f020d1d0f030f0d110705031b1c060c030f0e06150d060e06010609060801061b0c 71
    0x1083c0120401080b141e0394007920740485061040404006d94013580b9603446114040110381d030000312032030440e82c05003040c0d400e019005c400b515a0b8402c0100007075003c9000030400030a0f03548100a81c0c0140400c4c2e0081181d0419041c18513496002070181501040703240e5420032810702044024200c00c00c20f880c3e42c00001a0340d021107490400d0981044a01c00d441c0c1c60880180c0f5806404020740c040c151005254081d00c5c000060001e111131103041c0c107213502000c10b801c1162500002c10043d82c2d030240484d04030440c4c0c0412640c480420035030031000940c0710b048500c00d079400015004e080c0c441c0100640518424040107203014042e40421541000094103d54241f48031841d4440b08070780207180200e100b072040c4400604551390384001e003d142d460140030180c0048002111940200c4450801900e103980c0d400140c960300140c07100402d25406e012601c500d01300e0100d03a03181200d00300c0c0c40b403a948a803104000c0d24150824080c42c00000c0c0240600346501e5203c0020b078401c02c1c00b8a080090711a1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 239246133 1250 239244883 239244931
    0x3103020406030506011a030c030106050d020712180605040806180c10080403140c0a02040f0617010f0c020f03032208191d010e0f040f0c0f030b100c0308 67
    0x101580c825038281e00311324010402c1d2421a14084503240d00c2d40c101c03528502c5c00b5411003503503000c180149000c010021416001106503076048984440c0c002c01000881c03110480000c1901140342121440b00004410001c2c42c103001d20140c030203840718980a0283d503607421b44100d1109000628034000c078460460052801d446803000d0801030700595031440250700c0d133420003070400c040d07902e580030044404001c5c0301211100828000c5d2000d604480229080f990003501c04094211500801407840100808601101d0158006c0c2d030303418910b10040c4043c3c40c1030071007030381c40f1044583c50300f40030340003040041c881302e02c0c0c08001854582082c2c4d03040c0141c3c029482d03c0500e80c20045c82080c0440d107115642d04000d07000450400c0404007000c0303a044018043e00000c10032103412403118003460b0502c0e5000300356030361608030580a82d20044204018001581300810741d0502c0c644800200e40342c2000000345040a004001d8030b00c1407525501842c016a42d8120768841d001403101400440940101c00c03811 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 239247383 1250 239246133 239246141
    0x1936060321140304030c051c090503100204050121020c010c032f0a050d0f11031b0301080703120e030f0705030708070e01050603100801050108060a0605040231030204 73
    0x60044010403401c4103000c0c0d180040390340c5035044030144070b6445480080101120112a07005a251420717051040c05c500c0c003d4074140c0e4052070b180d0642c00509004051075070021105046420890454041d2004149841e00b24400c1d80039050000b084010000c01d0083c40000e21201403003410703001440c020303100303982d42e0031610b00c2101c2000107500c5041c0400c61031141d0600101403a01803501154012542d44440080d10400f0a601c0501c8004500341d020004180d21212060070808024082580d40c5c4810103259402118000e10360608855200100102c08080d130341616074120003045a542142c6030070f60080800c144840822140c01141042d40e2020310548001c0402680104138840c145420542080945d0f00100d4640d44189810401405e152903014110b4070243c1c0c500e81c0d2901c070034028560201442e0003415840d8241000098010000211b951040d03044000420080780c98108105c140d1292088a0301c0344210001c0000c2d140e0700300030b06180d41180445d82c00c6607103984d80d4041400e803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 239248633 1250 239247383 239247389
    0x110a1407060f0504020405090316230601030b010305060709030510050c09040e070303140f18030f03070b0a051e040b180a1103010c05070b15030a060f0209193606 71
    0x10507100d00504c011030510b03000341500810110302850030078004581c1111010046100030b03007807085c040d2685101035143e941040d248072404044d200c9560310b0741000c0030345035420300c01240c481c860a000550101e108003901c40a803a0302c000600214848851104040d040103400d841050301c0c104030340c008030f03551032045080c42c1c0418800341559910f54200608048400350980200078400c006a1840d549624201c400a0035213480342012080c0520100e0700c0c1000744072124185200028159040c41410051540710300d1100783c0078011a904c1c054010a150340f9a1661b030362515080d1b000c540024484061a9481801c810003e40310300305d0703000c80c1071502c450708005854561404c0071b00300d11402c0030300410b080c00200b406e0151800215070b0360302909050040080400706214401ca03291390350240a50300c07019030488424001c04003150b4061000394849100240304100403440501c40c00c00250343d00e4102d03009614041c01000c800d5001e0089250b010701000c2d45036010401c00030004030f00d0300c546009 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 239249883 1250 239248633 239248661
    0x3090402160c06091214030c030f0304060501050d0305070303020d09080406030204230907120b1908060f040503090d110a0602160b12010611240613110a140706 70
    0xe03080c042c14540d04003441034010324104500400b06001c4191a0301c01d0100d81580a22a20b5001c088026814154090800d1420142c080050020034403503e0070301440c051806880704003c944da07182c00700b0069603070145000340844d00034895080420301a41c0a033011801404001c00e50400030b071740c0c50100e980190018800700b0341c045001d000982100361207070044a41c0300842941c2c1020074000030002140248032208105080010752045c04154110341c0200307501510b20454400100e108044128050151500305d101c0c24000881c02180200050301903a00132015614240102c0184460100168403d41d520980d40c4c28030300b050389501c80208c0007003032560b02522501d80600e203000d900c04030070741c442019018240054880c0049042c00320741180d4070741c201012403100d80000c0a0401103009440114110b41c400074454281c4403c060900c41c1c90115024410f414002503980e00700c0d0140c0c1440d026001003442020b650702d010721070380908490403101d82030418405075910001d4450005080035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 239251133 1250 239249883 239249917
    0x31505062103030a0f063605090303191a0906010c0b0a0b0424050d020f091504051602120c01060e010b0c1c0e0d060618020310080c01051b03090402 65
    0x915a6040c8100785d40c182c0c00190520045180045180164000445007541c1c503840c100611401200480341140280c1680b00030b014500d402d004550b26500304946a080e83d81814a01040c0324201d40315003080d8800015070311000c0940750060069002008025905211342d101440c0d011401202190f0310981c0b1448001c100c0ba1008000e00c02a1082c0e0096003415010803080b0340b8210b50701c038045a00b43c4406540c103101c54401800001c1d240c1403a03140c5150010350a00501c600c80301118440081d504003514107110b80d489085d0070f00c01c01c0c2e44010418005810610516070300c6081d070380003803034010100d2002086c1a40c44d45546042c00d6000ea110b90482d500000d60103254003414000800d810510b03035185401c4220301200038040d5018101383c40e2103540c030003103502c2c100b101c07940c40000504038240c0410b201c1000070796a6002548141d402d8100c0348100b0200064072400021980340c03090060392041d00780b8140c402c06140c103401428041d001e900040c0301c20112929a8070107404280900c801d0b0308 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 239252383 1250 239251133 239251141
    0x60a0506070b04140c090705032203030203040309060e0a060302071406070c030215040b07051c020315120102160b0702010204052e020114130c0801060b03040212010603150506210303 80
    0x74101340091440ba002038000b0041013089a0315000c02c40c0d4003603803500f042e41d96940c95005c0c1c0c80c00d003c1d480c0c4801c0e8054012000c0c001c18554540c0c042c61003103200361149550030b9260903040e036101e00c0c1c00c03044550140e02c02c0c07400d0100503c20f03000751400622130150680400780c00c81c0c0142c204001100c08130700084180c3c242d1000d26504004010940c142482038078000d0410362a20034810754020701c400c2c20b06c40001000503262040741103121b8100d00703421046459081032020111894550702d15548142481ca0303440c00c14002c107108981d03589041e2409900761a00665555031800c400800c0941595800e220002d01c0317456000c0070651340c01c0c3c40030140454034582d9007880e007140041980d00c800c5a1409180c0c3c2007480181140c5500722000d481001b10828903803400809038080c9400000940d42046d81c00941c4049401c05140200c1c42159520581c010700c008007403c0316030318480030305428248589114a40322550185400c004060090074810f0300000250b02e11440410300b00710716a10003c104 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 239253633 1250 239252383 239252393
    0x3040909020f18161707030c0e0901270e0309010305130606080705130b1e191205120a171005040c080604050129130e070c110103061805060a0506070b04 67
    0x214451341c4843c03c0c003072648485141d12648004000380880c042c140d0320540361020ba40642c20001500780001e090780907940c7c60780030164488207070400c04242207035800a4500707407041c0c1c0d0040362030364400d20005504100040004401610000e4130200c8503801d41c802d29004607200303019503030241400c10002e080309898481848055210142080c3c0c1e0f5514258500400b55605111120b100202440d0b10b00703840d00e168000380e05c01809499408000005910006c3d025808800710b2030701502a00c155000400420384140c9035101d1500041d0015506220007445450383c08403158101080c0080e001c80c13152203038080b800715003c2d0040080400c00c42c5080040ca46401d000d09400760004118001c00c0d0b007901c04000c1042641030034020703030001010862007401303076500c0280401008540003401282c100104081c0115070b44207010364022042c8600500254002e0080c502120103d4121140c1c00c510f00f00d100e0300801001d00010341c0132044a00000d0075654401c0945000760290708401c40a090610307107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 239254883 1250 239253633 239253661
    0x90102120f030a1e091a01080102040303020706050307180905060f030c060405010e0303130e100e0622090203010c030621030509060c160603090b0f0903040909020f18 73
    0x40c004a41089226240001c8a003034940003002d810300860445541c085420715002c400360b002c00060300d08544442404007545411788800c02d114030a90b150f0362580c140d00d090b4411404083c0c05a8428201082070500c41c030700940e03002c0c1c0315141428800044400581e90501b080d4000064551900d007481158a07005034a6040814128005c206280070103002ca001d6004900c20705050051400b41e000c0140c5003481241c5254440602c6d81029035295922031600d0001a51003c608218280b404603e4100d8410000c0c00784400421801060f83c665410030f14150348210140c030b650f80c542200c1c0380141c4090103a43c5035860381b5203000c18158186007172810030240c580b0b601c21884038140c0c41c41001c0782d0068100c1e80070307450642e0380b13994030800c50309002d207030a400d20f4030856041104c1e01e002400036499480410300703603c28000078080c4e865401c1201d0181006447e218401e40040004014210f29641300e4000c0c0351001d0250f000c410a0000024056607107002165003144c45c1c5010088140383c0c0e040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 239256133 1250 239254883 239254903
    0xf090209030d030e0d0c110607051c030b0a0b03040204150608060112050103020604090207301d0102060a020a021603080903010612030c0813090e0705190308072d030203090102 77
    0x5020061349011881c201d9079444954000c2c41480580c3d440141401041707417003610350120140c012981c403089031525130b070781e19084920494062008240d010405119000310710200c040201201c5817175081032112606944054400c0b6071003562001491004120440c1440043c902030300c03410200e00c1c156002610f0041d203c04c00b00c1c806072600e001400180d031094191026110040d40c01a01d48180d49480c2030503c07940211071100b1020740124003070150785252840c0004030585e80762a26004100c0294519160341203c950143e0810b80000c1da00c50300726130103030180391141d204540e61251f101100070703940680c40c4c100788c07a04400011b4104450030240030f1007000748442240b002008015032402403101c0c1966100500e40800002d10070070800d01002000042c0c04111010000110303001c0b6a0760f6240d045100301405a942c43d101190700b12034903814101100c0d0003511403440c192855035a241c42c4030760403440303007d0500509a048440d01407014200c1e1418800c1d00156510002d2000192410001030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 239257383 1250 239256133 239256137
    0x120e090a0510060c080f0918010b0a170609060103050c16030801082b050c010917070b0a0b2101110a090608060d020105040603152d0506070506011e0f090209030d 71
    0x907484d0340090140c00c101e840d080b54089215407182e92480c001030074075055105d01c1e04c6441c10403002084120a45000f04118840d40d2110400d0311100b401e0350441c3c8204a50030b9078000b28010000380554000d030042a40004480811803520001d04501c0a6207518003800790009481000140030a1a0400c040d25a419101504c903103d2110640030088000b078040502040040202d50104040c40035000b60310031a60000c4480706800e144203203003046402c0000199010086800800c001724042d10440302003040140c107140444001c003030082804840c8011030460703590303290500503110042e8005028945002e0340c502c08030740d00d0204001c04001010381401d2003002c00100500041c2c0c2c0120881d004c560003403d0104003804603801c0101c0942a580c0445915030f968500c02c2c45959018203a04403281c8101080c051039a110700c1802224090610010050382c08280144154490781c07103185480b402261013009200d1305c800002034220a0350380b00d5500f0580101e442c441900c0c0501a500b000b0700b0b14 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 239258633 1250 239257383 239257397
    0x709031b1d010f05270a0c0f030605010206070c050726071a0405150d05070306080d090302060711032a0405010b0a0804061a030115060305011e03120e090a051006 71
    0x25241201d4083c2520450380b180c8009aa00c0502d0540304803a44a01c0032000400c044c2441c0c6818540042c00813803000000250074003212034a00d5002e4454001520b8040c2d0040025175a410403c0c1c500c01407100003030710144510680003958a5142c0d22200f070525103008203080d518900d80b9007070310b05401c5030419900100300344411580c01d45c110381a00c0c112402222840314691000e41e80c008280f00d4120304221842c148020003c0c4150540c0128081701e25079030440304000b4900c0001c864002075400004d621507806c0048201240b4103011803d801c0d0801800c0e01c1c2040c2c0500c0c100c00100659482500421203071000c1c50b0602d2429100e05801001c3c44603140b41780c9010403600401c0c031a002000241401e54400c10783d60440c143c1c0c280e103a10107001500801945860302c4614103580c04503c1396000003800c080c00842c510803007140f01001900c1b5420120911800c6036590040c500c00c00c0d091104110300c90381030784100c0d518441407500032041c03e0380009203810f00c1b122130000c03004507802c004180440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 239259883 1250 239258633 239258639
    0x6090103050309040f02220e0106020f0615150409060815090a060903030e0d03060e010f050a03060209011407080901020714100c020f030303040305030f0901090215030709031b1d01 79
    0x100443d10041011603000071031086142c074650080c00386441000c28442c4040003d405561608284420b80720009942c0040c0d030380e607080484ea14002400005495001807010512401044007683c140c103000034801c08400d080140440c60030b40080e8801c4044a40300d44041007561000c0c0700300c1e4601007480c9400246468002e24040d0b450040c600700409082c1d40d01c042e80180b5110380d000d2210100c07050203036079a200c01c4060040240c50b03107008298a1140e003400029441e2105c000700400c58401604130f000003072654503604003d41001c81c609042c0001010b100c04894441740040922030301c507907082915078a40e080024034061941c0c01410544201000511141e507039400300426004040c500919030340d403184042030a0f04240e6035441d405d84400300500c0b08158000c1c000e103101d40c41901d1241d03160b40e14040e0751426074011782c0e0701075003080080800211000081d00196400181c0d8185605031aa413940d0301120a450039107904582900c16000b07020110328035400594840f5908ac040e855541 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 239261133 1250 239259883 239259893
    0xd0207061e0c0b0a1d0a03020c03011802090c0c07090207050114281b08220210030c050702030a0b16050306030606101413060e100905010f12150e06090103 68
    0xb03280c41010b0188001c02000038035100007070b0002e01041402d0f0303042c2a5502c0b0700e4413001c0d65909203404210050301400403214207a0a05200c0d0008001c07140141802c0e00c10a0303000d00031841405404005584000c104140c00e02ca000c01c041d00040c107908800694612050900500311680b04044600d500803d406201090070b1941c0401050b0b842d031003282c6034492203250524003c12000080da01001491509011107075040040e03988500109510881c01c1170001c800e03601c0d076400044000b980f02c00d0b07040302c10141d40e00c40c2e842000b000040e414020320301005034000a1403c480e01e8404c5803141000d401300b22181c020303d00030304488465810881d05504100b00040c1d141d003002803101d070062080c60654601a41700b41e01002e40005180003480c0d0341c10045c2c1808010032098054840440c01c00c0e00b501e07030541050b82c0d500a205a16545000b4440d052000444185003d9110a41080740f081e060032107e807a0b81c420700454003149074161b42110301d00030003c0c807425801070020b480b0b034202600400c0410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 239262383 1250 239261133 239261147
    0x70c03050703350f04090f0b04050c030714090d02030a050a031e020a11040b060304080703020c0d0f03030c02030c0102120f070e0a030620070809040b06090319060207050d0207061e 79
    0x303e5207010441c0c9034036a0200c5464107000d503034085c0340c615041600c110182c6005a10070180040260b40078850f540c0c8440d54094a4801901e814000910320000c20005d0844107015150010000380a08215021500001d181c500401d42c19030b061b80013a00039004150300000d0740c3c0141142080354181c0e044c80c040c0043d40314040504094a40c0740e2250f8400403da40ba039000c031640c0703800180101e490307040074102801d068011540440141c818160441c01902d00511852441d0364000b41c1e4035200750095604901600090f00c00009520080c0810461032200b0700143c151640c858210ba0071f0341c80c000300d800040c20400b814520501101d0f03450000941c44000c400c100703403500110041200307922008501d42e00c0f12602d050203c05c0c0c001003282c1d000c1141c12401060f01a01c1143d06000013981c6800b004968442c4900c0c0643c1a48011590010700112142801609024500c010704011058468608142d62280714000507040b0324418410103410001550040201e06191030b40c2c402c0651002c1d00740 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 239263633 1250 239262383 239262473
    0x5100b040615110f07050105040302041505030a0c0614070b010909020d120f0806090c2a19060b1203090d03050f030f010501080f091002071e050115120b060103020f070c03050703 78
    0x7440c1c40e0300c520944c4980780032041d4001d0ec005801c60301d0320809030038441801c0d4494003a0700006032030356810b4511802820103035181141c02050120460b40707801c484500815264504980002d01250a080804c0390040e800401294030303244c100c1c1424142800400161000742410b10441c0304605002c60103240354103131144007129201070032602c03110906590464a4400e230a00a512803641200d21444d10180c0200712184030b4201480144070b43c2042114152152901d044035510074801103030f091420f410140145030203424020300c0d003160696002070607402107402048550382800104420b50780241c9441e0f0014566880e200203041480d02c17151200c0707482d04860400758020030f009041c8081000039159a010f09250b81d29480d803240740a03800b03001805810f001e4440c100b80d00040c1038640300c088143c103981c800c240b1131380ea43c1d6140c0103400030341008025800140060101400250b030310090580503500400080440d00d10f14900004500e00d0855900c0a00c0003050b00c024800408800f00030207 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 239264883 1250 239263633 239263639
    0x50c0906010207080604051c0e010e0f0d020603090c0906090708011520010f060501020c09130812010b09040b04060617060112180c05010c05100b040615110f07050105040302 76
    0x49455250040f881c0034643e1304030903000e020b04428402080000100d200d0800754121000881852200007643c1002046000b103020607481044001c15107418144215944002441e4200101180c0c02054082c1c00445010406902950480ca1140340c180c0c0c4569000380100d031412401d22381000028080300041c0b00d0440440399010a0003984c03070041f03019030410101c0c02c1e10385401400c2c00c009503001c0c105003412500664076240000c9819440801c40e1090001c000d0508211074450f00700701f16482d01c01d038a0903150300c441401180070048413154198000c0091520301500c400e210300804c001c540004c2e100703610031450000c080101542101200c2c96000000d5802d010326900d0030010703a0f4480d1002c4a054050b481c0c0f01081501004030541d0401881c00b83d800001e02640b0fa070019641030380410380142c69580304c0031070b450f06183c46ea0842c070800e0b80050000700f00c0d6540c40c100d11484100040e60714003c6446030800140007141000840d00021000000f02441454000060400c0c0326901010f40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 239266133 1250 239264883 239264899
    0x50a030609050c0d0f0c0b030106140306150a020f070f0e06100c0c1203171012081201030305071515050105091207060801170c03191a040c0504140103050c 68
    0x1c107001050015444007000900754001460301854036100d11001104200c40000b00140d010070340b0810320b829030b81a0348450315181d0520010954451440e04010b10640e842800f81c9040c00d40c04180002810030600b058006103406103200a0807410101c5a4011269a6406000400500e054415a0390300a8001d41700e281051602c0c2d181203602c0d0260740d030042c260450b0950001a034010065840741540e0007a038442c0d00801c02c15640664014060307901c0c000c0c19411442c24410750300002120030400d072040801c18600240109030843c11b1009910a0b0046600412040c051250600003046600d0020108206140d12180001244201805128100708010035614215243c031082d2100024504048810840c1d0b10b900c01030820509000707408001180c03817000000c40400090341515050020090503440c01d0501902d50310384205841651618541c0895240d1340001c003420900440c041e00f60208101d0501c03050000362030303529095480c40d90724480100041140811082514007040b40c4d108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 239267383 1250 239266133 239266151
    0x1203020c012406020714060417030d0e03180409020904080d020c0106151106070c080702150a030c030c0509010e040207060905120306040506040c0203090d0311010f0e010e07050a0306 80
    0x80c1c0101450480800d6120900d040ca200004002000c01d00701e403120b5080f02c41135074903001805510000b03825410f4000c80140801c1c410107241c2000249101202e000f242e0501c45000d4403041a10190601d40840c1d400025896182c107124440320154028240d030309200600c240c1d80803803840302c4001c0006c0c02036100803855200d44001c980403103a400b00c40000074843c2a4071103c140034141c0c201c02c5082e000c14a804c05031901e2540c046a400e1055a0130340303515045030216212031204e5880901c0481c6c1c04140c040b10f4038001c00b5040c000d060724244a540c0000c0d090180003026080302d00007a02703101407040600202007a6a400001c141084000707550150300c9164030310300032000c1c011100008145000e240380c400d084400c050055445104102c4050000d80c40700b10900040303d1180d8424001604104101102750416614010b6901d1003883d102195a203a191103a08480441c50807214140c0c9510130f0000082c02402803d42c920300d900d0150400b60325010003c0c0119101d8032004081640381c10a40e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 239268633 1250 239267383 239267407
    0x9021c0312110c0318040c170a050901021b1501170d0e04060e0f1506090d020402090111010c05220b03060d030c3c11060c010b03070b0322120302 64
    0x10b40c030000420702c200c81d02d07860300e600c2082c01160712170b0003a070260b0303d04164000500d1090301d14028100b480c003001c040d5600c07050240c80141c00001c004007110f40d002c101c865503040c0c402d084000e000c5c814030094980002c524050714a14641a8000130720282c4400da500030111000c903120007801c000b42092211b00c0e1004003c60040c0c090380c3e125440e00903002e0b041000003c1c0d42c0722103610599003640c50a03c555003407010410325000d030030724031600100180c40010041c20182c0c028020044c050520321074501c40b40049501f52941d104440340090008588103410134040c102081505990000203110241031000485c03031404000e080704d109521005044041c54000c2c0240e00c442904103008020940f0300c03034850a002c984800403242c1c07600408541078a200f1f00f00980c0d6005c1ea1748801c0100803039411201300000c1e038120107034140f61035588811114840c0c0d03007088a18018002e5996003501e030702d00203101102600317000540007000e020503001c038800503101c10b0000041c45054100140c54807424000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 239269883 1250 239268633 239268637
    0x31050d0c0504020403030201060602070f0303020a200d030306140303090d1e080a090311030f070603022101080609060f010315020711090a09020f10140a02030c03030a09021c031211 79
    0x725035003091000402000303266045d0400020364000d41c007225841a9215540035489074240300150040c3c000b402130500186510081842c0d00c83c0e2408066401c00920001600841104004902003542d8442c1002020b10200b03000c0f04000d006c0300654180a8580045a144010b025004143d0702c10340f010354075001281c01101d00c1d1142c110402c50f454901269014002e0303502c500042c0d8107078080e14025609480d0024841702e0000164020f4404585001300c10b80280d0411318070181e5a42440801c403800007050060b40d0f000709101350007400f050802c049401d007400005001000d2400e000e100620220790a1031301c0c80d0a01c644614010f0303849200d403c1a1131200d0043d014a0f900c10030030000d00940311410303080341c03802b98000ca038412401c002c4601002040e082c0d000852000c503568400e00c0a0183c0100064400c2d80303568010b6030700c0d04180b800c0041c203562046500d0025980d0303074581c50b8194240001e80e014002c000790340d082031b1046142c5018081a04003075515a80549960407080c0808407002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 239271133 1250 239269883 239269889
    0xf04020105070510060e0a060b0d0e010b130906060b130e070516030809010e0c2209020a0f1503020f0d020a11060711100b0105072d0831050d0c 63
    0x1515445820181c0c4803000d480785110380025482c6c800040703a4625041d101d01402c60786040303642858100c40350300751405802400749000c001e543c1d556005460340c031030300e004492404a1000006144c401c80c80d0407001c441c0503030021005003005008050021254002e001c060707a5515112855540d00c441040350710f0301c0b80c00700c40c5c19a4000d24038400d0405402680c041d0080e10014001c0c40380c1880c40119540d00c0010090459124601c0044800c0e680005202020340c803400d8403010403103000c0c5401042c0c00188a90004060000c600c00400c4001c00b200600051040d042c0b81c15031600800c40060b462501800401e040250380c0000c40110704c40c02005031150304091001602e02614040324040c1c103803101c55031141500d01490078110442001846010f0722210141c5515040400c50b03107038498080790314031403900414050031091001a0700301320100318072841811290740d2031001c9041d254842c40900142115031039140e10700d92046c44d0440c041002c2e20b030251003000ca068918202564a40041d038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 239272383 1250 239271133 239271143
    0x61b010207060c0f0c0506061002030c010231060504090f0b181608090a030503070210051504390509040911010e060a1202030709080d080402040f020f030f0402010507 73
    0x4041041084940062260203c20b4950101c5194115010780300f00b82d443c44014071540250002414a242004401000c0c4503a8811241005504541c0c24226800b00031140401c0780400c0c4030f81c0c8841000071005041c80c018640d03c204c40343c942070700034000e030003a40100107243d81c9844128110140b01c0c0d1114004403002007040704000e84030300b0040750f4542c06071f440a0194075a030303803c1d42e01d880c0034800e414010311010340103213828440364800701ca480d00042d1000d03046010b003003aa1800b40d000c60182502582c21803c030b03449a038203100e0800c0304130707075100d008e092047e50b0401207604070385514140903080e070241c17100b000b265103030181c02140c05204042400360300c40d01e0302c00c910082c850000d4050524003001e03229030b403404041d441002014000c004c2954000384d0809085200c1940303d40246822071583d0400650240d01c40d02268180825100c00100144d0203038104410761500d4004c116a41100c3e040451919280d0180300281c1d2000418101e01080301d0700c041011640304500303c96030700c1d401c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 239273633 1250 239272383 239272387
    0x21218040e16051e030c040906061d01051e0d030c0201020f0304120203160302060a0302070615080d03150f1a091518011d040b030703020a06030608061003030905061b0102 75
    0xa01444195407050083c1c0e4010000218071a40c081d108407481c42440da8010000c0c19032405400802c0058400d400d02111029103950b00015002d51180342c400b21244000d00c012425810310083c089044146002006505441800481e00f510380944c44d0320502d4140c40c00200c1c8031603500060b40b400d41c40012814445c440054009034200b60050a20b450501c00c4094460b81112060120396a00f22400041e501c40820000d00c2e800c40d0203a401003061611030600480d00903912008c94410003c070740d01003901c50700a500505242c03070b414403421004660985c00c0000f40740c04c20074520900d404600805001280c50660291424041d000b0345010740340050552a4142c400400d440203074018943c501503e24000c01c48455540c007441c140715801c00804046803041d082041000050690b040c0115010b0284400206c0585c495100b100302900903a200820f0a600d0550b00601c0d011008200c400080c040180c2400000e40c46203800c802c80c0c108550345510780c4040002161140300031189a0340641c40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 239274883 1250 239273633 239273653
    0x1170c0f0a35070302010905060a020606012a080910080702100903030b030f150115050d0f1803050912060115030203061507050d081e070302030a0b0307031a07021218040e 75
    0x3e03030801602e101307a940090290f580c9003403141c540210f018078405604190009015544a55480c0f0007100f2103001b2000c502080c8400c00f101d200d540c010a0707408102c0022103041c6402c01b00305800742c10b40c803482c1840302841d20070002034450000340d1260700e4440c2c66941c0e900c24580309402c04499200c0c020151182e10308901c0950380e42d0a004003001f035494409070b0000940c071550407404000034500d919072615103a42820488005e00150b40b0031050b8681d070b0141d0f8046070a000c1c4406010a10075181d01d9a14010b580400180c841e24074070b91510381c1c2c070040050200d0803034400003540c1240141400740e00e07600c0f42400a648240c400c0c00c1011003043c00700c0d005045c080002941c1003110340980343d09425031078030f0000a4010003807142c2d2121100d0104081030055200e54021907019540c03500010302d640d11540003a00380325140c0d005845140e0a00345084040c0c10034140190402c20900003031000c07803080b50102c151809034007050000c1c1100038101400c0c50300c0d80e420400c0030660300d5040d5107207180 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 239276133 1250 239274883 239274989
    0x50606011b1a09010c0219021011030a03090b0105040603020114090315070518040908070f170c030c07090e0a0f17040303050a020d030204062307080301170c0f0a 71
    0x1000f01c500021a40c24644030200081c004101504114602c1d07500020364840c540038001b00301d258001c281708201d0317494000c115504051000d0461011a0ba8010650300c440b82060b15440c8010380195108501c1c04908100503a002aa6140d407040000071aa80703c0c0d41c442c00203403c001140c5942c05800e143c2c0300c2003103a5503034000014403181c03c01e21080c0c0120810a000e10080703406011000b000000104110400b01e15074543c00c1807002d1040d0300645180c02c440d60f48809641152001c02440e0340040b030500d8201c903040c03002c0409010424003c005d2a088103041c19900d00d15844003500072105544400d0a00c041e030100004030480027100d055a4a9807494002c1c81e55000300c0544006029844441c2d42080c840e0089804448859a810981000700e81005410380700c0c00211911404080042100080c84280554020442da03031080b0801c0c681d09d02c03150300340316070030751901d104c3c00e0300302c2680e6900d690f1f0b001031105488945659031803800001018405400745400d481403115080500c1c040051 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 239277383 1250 239276133 239276183
    0xc0f0f0b0108100f0504080403060213050604090b0901140607020d111e0f0d05060c0a05070507090501030213420306061805010f0909030c140604030813050606011b 72
    0x3400c456420000854520404c00c11180240c1d8010004481084104003140310394003e01642142c1c00500082c1710350b544000b40096026a106803205034035094802120b2800b960260300500d10000c884000912440005180e40300c0c100b030080c41840076034544024001900c001840510020f0580138000d40580300044142c090390310f02c6403248110f560030131418103103240303c0c800d042d502c08018511900c0700154546550060011002000014131400020030400c21038200148140310300000c180d4110f0041c8002200e05000c80304825052140d1100702420790352080c9030700e82c0d03c82841d240942a46c034840010ba20640614075001c0004200413080c8192a400741007201c008403111044100e41e44c5c800020307540c0034415040d4071002001d041024040d5034000c40c40c50b07403107481e00038507811450740da100b40d84512084403009980000100b10405810000c8079410803180290321135914039503a00d031a039800c1c0041506040110f00c1d200714a0094000007911a400c0c0c2c00740812417107084110700c0407003031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 239278633 1250 239277383 239277403
    0x1a190b040321032c01090503040e09070506040b27090a050a0e0a08090d03110d0306080606010903050a030e060d0c02010e011821020a060c210c0c0f0f0b0108 69
    0x550364285000140c00d00134495030030740c0e8412650860035515035880060f240e40350304103504e05a540b5801e103030b000190240001c00c00384c0355200701000d00d414030380d4115182c00000e411180c0100006c0100344100c018440c180d410b419400800b06d04040000706014242c0140003a11079002407261003405101603050304654130541140f84104026428501e01c59581c0003a9900074011100401861701d40d8140030b044002510300a081c40345c40500340e00c4805240212100210001031f5031000244413240b07042c401540c000f1070918080c0001419501d41c42c0d110020040000c091041042c0004d429840c1c4a0558421b45406030080190b0031a02d0006800fa04880903110523a501e0120a8004e407422401c24404681c0c100120520071703400e40303005130f23281003849602c0010340c401e007004140090018014460310b00aa6501e80c49024144111070342d010420f6103944441c1401c050140b10050344c08288041000c0d00101c107400103014904154410000d06800901b0200c2d071907001180350440001c500c20a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 239279883 1250 239278633 239278673
    0x1f09050a0c0212040b040b09150f040306050601021f0f0908130f09060f0509090111210a050403080c0f0f03090304061107120f0203010f0c080601020f011a190b0403 72
    0x4440300322205040f62080703000d8441c800d041403005000900e00240a080040409000446007801202c604002c581009030081a01e00000030140708120880c000c4541005081c001041c900c21111214000d0400c2c075661082101d50b07405491002490b2904900072040c3c0000c4000e40d1036412611070f6403103401c203004403240c40c81381000000304204144a00340856224000b00340010303090004005080d0800361800420350340300d04044168007000d4005151210300d0b48100511a1840140480341480040c42400b8180c644020000440c3e00b1512861340070050b95086503550b24101000629400b070b4603812210032401008003c2c45c0c910000041003950b05646400c034441c2d01d544031003644c2d14240d0003604401495803050f0800115484142d6001620040c000705003102900b509034115102d02c5101d0002607240030501406580501c4060a24000d0f0303c003d10112052004024491201c0041e1600880420119020304000c130a1050080c08209050350340c0d841c0d890070103030502c501ca00c1042c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 239281133 1250 239279883 239279893
    0x114010b04080706020c1005160b0108070306060617010e0618010b13080714011d100c0204050c0a1409040e0303010f06031b08060f120d05030a0c11061f09050a0c02 72
    0x200d040c0000b070101b00c1582c0080030041c940341d500313500716020340003a03078004441c80f54801c6030340001c0d424240f401d002c0c081e01001410044d2650a01806a8000340e11090510884081c1c401f60f040c0c103440064151660b406405586403604004100387e0b18043d098000c40071002e40c001700303a074041e480040110144010070001b109864589140d207404041c401d00da8800220115500302c1e5000c0e2078040e0146051001050640c0d002e500802c40707000d00804044009150b00591208510b0144282a0001d4020800c1803d0030743c0c2182c007400c800540d6241440c0858045500700c40c2c1d07620f6801040f0704203e8141030301d4480d607442c0c4110300e80c81006e003e07034004a030a0a6000d401d0040400703044184400356074a04e0380507101e1310148844140350501d42e80e0481140c440c00640380b8010401c580b06070340309a554965928105081c502180c0c41840c10070304000800e8208050a800000c9c56900704041c9054038144a188507100e400314411a4132440c2000d003030800304203200b011035005582c909a00d8080c0c0b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 239282383 1250 239281133 239281139
    0xa0f060c05040602060115030605100c02030111040b0405011d030a0b040b0606070b0f04051612020108060a0b19050d06060c0605090f030301090f0603080f07050d050708090603090114010b040807 85
    0x25401d80a180114001a0b203c40d00402035101a01070886580c1d0580c00c000442d03580715000316034206540e40c00140403a044803070200450900348101c0150481c4040301c1410b00e820807200c440103104600c40c2074100300050307840f00d4150ba003002c8201182039000307089500c0d10f0075910f802894000c1c100c4040d40c40b082e51600066081c201601120003240c0c0c03101030740d04655186450203180100181c804d80c0d46100300c03940c080c142140040d10341d020305412045541d28102d02e09c001421300b840101024081c108403841000101d512100b50b405001d0b80079540d201b20f000540b0126414056854095481400c01900040321350b0004180079080d0b015800c1881190b03a00405155511407440480189902c10801042030406643c081000c0d060304003808560320780c0d40c3d201c3c0d1040c4d80207813514514402c40012002d081200c104010b070390000c2e060402c582003800903110352803280500c42206004080001c00181c90328000c0d8008401c0c484906001c48903561264480c44803608540a101e4443c8039a007804 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 239283633 1250 239282383 239282387
    0x140601080a03080a090305091003050a111222080403060b100509100e0303040902030a050108070509010608040303090c090203071e0c02030a020d03200309040c03060b031f05030a0f060c 81
    0xa010300d20b4040e250a4116250303022100000c10080c04181c1c1085014043da4005507101d5a601400300c1d070581d80842c883c00c2c04445141103410b8121002d40500c400c00c54080c101905100307269000c80e03202125850414107483c0c00a45140d020f400410203031002a02204006040e0702c004078180d029101d18243d5003100301c00341e8003849150401644100860025024940b280c0340100c584007025007900e00f0300e50303a007811005a070801d494580c1c003180c132100180986001045040300a08003240d011180754906103015150300c20140000c2c0c10075843c1c107506010b0014002a072030050007000d0701190b5074948120000c003047c2406d0600c010340d1070f0400d9101d82582c0f1403c0c5070340b01560000c02070701d02400b1581c00c0143e04444603404600b0300145419084a41c2e041c00d880301c004c942c100c0040e56584210300c0c00c1000f01c0d241a07c0c1c40e014103142c4403080c0501d20720802542d03030240380b4012401103a040f895191101c59195032005038941710fa50000030410001d05100c1486a109040030301c07600209142c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 239284883 1250 239283633 239283643
    0x5010608010504060b03040b040501021606140603071a18090f0402120c0114031509040f0c0b0f1803010e070f050a0e060102060403050a0c33150b0f1614060108 70
    0x1038175120b510600205012602d0907a41d40d4110303100d03100043c035009510040c41c8040900c1c03403040da1030940e1140c03a000040036000c140340e48480110040d01a0313a0031300c88400ca4062140c01641703e0250040b604850202e40c078840c044282000038a8045103182c01c00c00704c000100c003150101e0003800d103106000318000300000d4030305005805850f10744039041c2941c0300c00d01640005129041000008114040540f030703442013140298010300c200c0303d11400605040e6440c207040d6200c01c40742d2400b0440404081da4440664542c40d0020007040c2c2c180c152240081c0c0500b001c40c88010060080c03040c0081c0b80e00321030040104403103058802d150a25521940488070003021a02e03940540c11150000380041e20580c010441c01d1080d041000d41e264a58a815680c4588071200d4540080d000003007400040081902c1e01010305001d0301408403d4206802904803803c41c4641c0c005543c000c41c025550303030007080540d0018203004000c4200c000003400d0450b40711010700d1030b001c91401180000f295680012034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 239286133 1250 239284883 239284889
    0x60b0d1a09060613030803070f08070c0c03021507140d020d091805130b09030703030f0b0f010f030209120a0c050a0b03010b0f0705031222032003040b0a030501060801050406 76
    0x160348640d0307803600f0300591303901801881229610656020000a0011010303501030401a660b840c10310b009884040e14940c80640b281342802106001c10000030004c2c030070300e0207413030303040d0f0384090f0303c40c0e401c1c10282190041000c021700021194940b000c03141c4000900312440c1c1110f078222903104503404030131f942020160188080c40f4030060072103514803a01c3e4114603048070745184468a00000e41c0c0769010083c0050380c404415400004600d4141540340c002d064581104031010042244044001801d80c10f44008841c140004012a170159a0103681500c1c51100c01400600340710b940c503c3ca40752a2104008115201e503000440440ea03410042e0b5410309451446c00079a1840c4d0900c240e130a610b800c640d02c0248100d008000204c00568248041e021101080320340781c0300da0820180001e820316a09032407103440c000e000c15941c04294001540074010407071103c1e4180403410544814110b01c1580c02228140000084c900c51465050384414100d800c196540011039803140100000d80e00584 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 239287383 1250 239286133 239286139
    0x703080619060e0409020105040f0603060f170a06052205030403140d021015050d0305030f01060e06120612030a080f221b170705030615030607140d060b0d1a 69
    0x24841c8401e003005d0340320b2107405005041c9031381019580c10810020740300e0354001000080c0c50fa0790402080280702c2d45000a44000b0000f45045561070403000e5840101c040d001c0c00c020b881d5004125214100318280d0052402071042c07070401c11041c20328540e01e034860710040703400100b00960000300780404a44520b4186031035021b880b480450754059005000b410381074038210003e116000441c0d035180001d40f04128407d40312191680f0301440f04280000050340306200f03001d05044c0180e50340e6103c1044510002400c440c1c0001501c586d000300d81440780780034a0003200c8c8400205116469001808548241c0c010704007051180e0b0380d080b051010401c1c44022a082840101c000d200058080388001000010104d081d0a56a42c40f804018410700942c071624990300708640074001402c0c24041e07a54000c0c00c81042081030540c24000c0707940c9840042c1703050704000185070b00d100403407500021070f1000d084250003030000343d0300c42c01202001c0e4819142c3e041424645000090b104401d80d01c2006a0a0b0007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 239288633 1250 239287383 239287397
    0x3180607050a0219090c0804050c01030e0d18080708030720060307031a0907030f1406060f090d080703090501030c21020904020c01060305030d0c051602040f090206070308061906 78
    0xd40c01d00a102c1090500403120500e03046002c40d045c2d61034400c1100034005560350140303a042c241002030510640366005810182444009420b6210021700c040e00e485003480e1603050750382c080303001026014180d00001014003e8032000035001c00004090400c85001c0c4180e08202e51080402c0340c01602c01c0e4010300d070050700500000b045140280d001c5410074541520b1038449a0700038000a000e54400c0303c4034000b10307655985202a9500502c40c580a10400350a1010740b0b0814100199880c007402042509540300095401b4098642c2e180340c013141a4040748040c0c50302c0f11032074017400003201c03809000d0000345440c269520f0241f281d41540074011210b14060603d415088030240650701810100b90096020014020809070034800e46006501450203903440380d140c42c0821090340c03c15820f160410800703105804d100c0c0c0e84440720f11941b550440f00050714030390b80000680584031040000c1c0d40a007000c1040800c2c5034014410328800c0e03108403001010004105150a0740098500a9100144070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 239289883 1250 239288633 239288653
    0x150b040608040f110d1b09020f181504030807020f06030c0d050406060512011a0d02060a030f1103090604050f0d202e2009060901030b060c0318060705 66
    0x2800c0724611640b03002d07015001c05604d6800c0414000840e848040b01c400c0020708040e601c01994036a12000350901d000c080d49403907104041c0e21000e00508025407042d803000b01c07107503000313940d10a88a504015699692512550340e4180001980c01032003069015515120200009260840480f403117132480110b50350900410408034030007001300405c226030407036682c0c5021070141e0b0780702052103004e2182000880c04190004402e01d0001141c03a000740200c0060b4114801030351000700303441241c02c85240001d070503103441d10800080c000c0064405180b403000002d0042a040114020741718074041d00c21103203016081048242d03a0404042401c00048440303440426041c1d0340d41d41203200000150484048003000030007020140440610260f1078407401b02e051036905214000c115005400e46003450440c41c00440314107951041c68003480c4900c0303000801e84a05ea0007a4010a81c1d4880502110303210901c2c80010b03962940824840071071411451142103051422604032088142c1c010060000409 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 239291133 1250 239289883 239289893
    0x10080601030b27061602010b030601121719050d0c02150c07020d050f070305061501020601030b0c22080c0406030c0b0309030d05070c0b13030e0906060c030d150b04060804 75
    0x4283c600f144012038810072100940d501000301c1401558400310360860640840006800c584c61a0407640c020b41100004100307000e01c51270716038034490300241080800070354030503440d03540d10407a6880b1110981c01e01060b04400d510201130080c0900e005004c03c0040c4043c1d80580ea105040200c200c018aa03620010300c43e8296000a0302c0c004e44050000320019805d951198103203901400c044c0301b140d01407141003041c42005c00030981c21007018045607a040110f200001d40b00d08050001805052044021400d1014004222142800303100d4029000c1c801c0e9001500d4407200074814141d0510a1a581d526280381078800c407002c581d4801c44400301d5900e01110600c0f030342c2000708294803d010510104843c0c80003402198815019941c50740340490440ca04083d800501401c003803054508020740f0000a90001500381c640c0c0c50440301c030b90f47e99487e600020001e200d4a11140c3e460b00020aa94100c191241c00100d201040d10b540c100402d07440311000b0b0f403a8043d900c103040001d00000b010a01050b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 239292383 1250 239291133 239291161
    0x203090a03140f120406050c040303050a0c030c0210020610060e0f040e0a0f0501022a0a0605041e0b0a05070f05030109110405060a110d031b05090a09060e10080601030b 74
    0x89200d50083c1090010b054546280d040b00c0b0300c568040300c4020810040018600c6140d500201516a81d1304150464400030468020b0317403140c200b4414040030302000d140c0a00c1201d0740d29540102244850310405034000c0d11288240c4080060701e00903400840c2030b5000b5540680d0082000d05920f80396001d180401003e0410142d070300206008018482001c10b525a00720301000e4042e40015940d4600f03162446100154691100182200c0702800020301c0d50105201c00742a80000c004141c41d2510b0074404a5146041d40307040c1d40c40000b440f010f04102c0360032111072040030403503070401c10f0b0b603101c1c002540d825040303108030800110100010b22032140d444e4461408080210012402e154540e404503185912840a4a01140102c0c0c2d400031249020449000d5a45580c0fa00340101ca640800e0414044401d03202d09090100100340003072544c4070060244020300c20a841400710740e90761891084414000c0c1e4071075442c1105440049015140000d8039412a0340c8600943c8850342d8908845482c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 239293633 1250 239292383 239292407
    0x204050a0209040c02031c150504200a0207090e0703021815030706210905100b040f06060801080706050a0503061c0f03020c0414090307110d2001080a0203090a03 71
    0x369003031014086a8565105518a10039290015582c030701c0b00811420000b41c0d138140329034030142080d68500d0303115801d6401c0021507100790380c082200c040141d641c01f03240c40300c802c81d0007003e80d001c030b000010141e00050800894801035001c0102802c0c11070800d444c1c1e13105000103500840303805440c850034032007584480da1154003134203103524201c246000070741002ca5961101000903c4501080032046500030316100c64140901c0412115141d9034490f5215110b41040d01405a92051103560030344480c0c2013903203440e0114804100e41900c031200981515820f0244510b54402ea180229041d4000d000300e40c5811000c0d12520309582d5908100070744400c500c00102c00d0301e036407072050b0380006070001a404070944c482c0e009064403121590612088548007003c900c0752060030402e024503000044101c03a40c00f9004111450b080454201141c54441c107401300501440c078032114440c400304c4130600128080d01c06d81c1d0300351041d04d422451b0f5091b0f02003555603428540023810f141c00001c0c0180d00c90000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 239294883 1250 239293633 239293651
    0x1406130207020f011815030c08071803060203130b0405070303031103073905010516050f0f070305070506040503030613020403112e05130603060608010e06040f0203070e1002010606020307020405 85
    0x17556813251070361100c448841005801281d15240c0e013849240e040300f0019400040e034517049201c0c229100c400e000f505040d1102800306980003000c181251440003c0180040d0404010320543c2010310700b895413184144800c1d40040d180c030a800e00449003100c12030b4010786144d82e4045441c0c0065211a02400344c00c04045552020b01300807800b90381401ca002d01c0740318010000080c95140c0003c211135980807144486080020030411182c40f40c41c1d4100b5105201080080d0985402c19460140c880e403140010103040c2d8814502084104a0b0000003940700301002d41c0c07502204041030300d024041e8080c03408000c00496101c1d92101041c00c1c4804480d40008548001c42c0a1054803900900c00712415690500001d500158040c00d80708042080f000070103840c6810422640f400000415440041c0100700405c0b8081340030070b00660381c2d81c0000810503008041190740e810f00840140c00c0c1d1220448481c060000c03900817511150040c0300c0c900031074031a900070314034242496003044000c040050030240 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 239296133 1250 239294883 239294927
    0xc030a0c050715021b060126070306110a020c09160c020d08220f030c1a09040219030e07053610080f06070207030816061406130207020f01 61
    0x8900801c070300050403c07401d000160b90701c1071015104410012801d1101069000714010080c40c401c1c2142d0072940c04094100d400c8044102000f203040c9425503201a0416042910030704014056200411282040f40c08944185c244034082c441900d2081342c01e039003e4021410b402861900501005440610051604141c04001d50b10100e4a8010884512025040c0380d54825091014682d020140c09030840d40c0e40700a1541d581d41c0c3d10301005005420b0305c0c0744842021100040d502066070b260400084c019034aa02003200181d020f2410035003440002400c00d001040324101c04100b100c141d40c0d014158540302e46840e03c410103984126000f400c0244107140350040c8802040f00b42c10b008003100454071400520300f2145030f00d0040c00e04282e0704150020810b001c140e035000110403080b25800300c91a9100c1c0817090781803005503074500000d030131142080e81e00c41d026810342500034440d07070044684c0342c481c01103107004000300e004440000303400c4280341c025240c03903600810f44440d0404c0440c10b03600d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 239297383 1250 239296133 239296147
    0x1e0a12050a02010212010e10080a0f060902130507031406120d1b1505010608240d0212150a27060b040605030d030b1815040c030f1107050c06030c030a0c05 68
    0x200488017680685981c41200c0242314030340b02e03d41c83d00c1000303203007040003081c0440300f5803100c0c1d944032071032a80181030f2903480c9041030442d250a104a204031083c8036080201d03250505020f0003602d1800740c0c000340c030041d4400107403031843c000580c034122010000042880003920320055510040f6016000351a0030a06003040000703a9000d04282e01035688c00000c1215407400c200074043d14000340401600c0c94403203950380b1440c040d03460b0f4a20071182c200c3e0b802c4800b10241c0041581c01225211002c0e403405280c0000b9000104111694092002c800d410001140c2c808040021003440000000c0550761900040f00407030b6983d0040f130400e10f002000052403550f81d90000385031180c1c2e83d1162020a03151281304903940703001d0f04449021000702d46044001e1414802540d106140c482c2e1580c4155500c004a000e22403281e0300103006105078160070000c3d04440a03d0040c9900101000c440b05d102d5201260714070f0034501d040d1303405013001d1a1000d082d500c1e4500b01002501d807080141080140910610b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 239298633 1250 239297383 239297407
    0xe07050703120608071410080103020d120e0901080f0c060a0e01030b03010f06120308090105070e011107050a08070e0109060b0f1c05180f0f06062b051e0a12050a020102 74
    0x10020011159086810b00651b8144002000c05045243c1072201e1803004002588038800400f4106a0104102c001c100410005039a0140c2d921661a0050004c2c8000b00340d0860015070f045001841a048a2548168401f0408140704d07218241000801103511141554000c0d0000c00c21804014004581000c2d459180c00841740c540e80404848203402c01000d00b4542c201041d1a0406506030007884140350440000d04001040d841150420440300e416103040e071801c0c04182e024041c0180704621513550341136965a910307124050340d45000300c20400083c8030045442603400306c410490a060402e107204007000c561342c000000100c005218004061400401441510310030f680044241891407070442103e440e00d0000c1c0c11800041d0300c4180395182d03c80001034000c2d4040b13000c903000290351048a0b0715844048503015401c0030300d59141404000c104002c900715030a00f00d6003000041e1140390031081750754ec42c010440540710044164010900c148654001c080d249210f000261904c1321410b90 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 239299883 1250 239298633 239298643
    0xb130e12120615160816060e07091104030203071e08100f061d0f0901060b160201030b0a0b0a030203150303030a0c02160b0319140906040203070e07050703120608 71
    0x78200151184204100399442e0580011444541840c000340c1440c0d1901000448011003460140c00810049440c11010f01103a40d00e02400394850700c20301030145900c2d40705a441c0c0107405090030130f078105022030300a407000d441540c00b00c0340c000f0000c2004500c0c00111441c601000445016202c1052a01007103240003040f81251965141e080020546800c40c0540202e5215400c02102041c0e080900c1039420721481f58150010340340c0084814540300c8103007190046c002d9a00854860306c0120741e4070303010303610900704125060007030b01d0500c401e401140030007499141c140540009480c0601150f00301078401d5000c2c1d9400300a12200c4041031028800082c07540d00101d40036000305403201c0b05215015814001006a4125403200e001d031b40781420f03400280c3d804005d01e2034400e1412480441c0c00d20078503802503030140030856505001d600b0412002611407804403000c1c0c4c001c1c0b241400c0015144036040c840c40c401d996540d034281c1813240301d5a044829003181c106d00c50032551221400b00f140707541400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 239301133 1250 239299883 239299897
    0x402060708031008190302150a18030302040f0815130503040e0f090d030c0207030303020d0204050405040b091204060c02100e030706020a140d0e100c0f0c0303030f0b130e12 76
    0x120500c0f10a10f8822824a00f540b003005020711988403002510010b500042c00791100341e800f10b400e118070340d106080400240a5514500030548191203100c0500da01640200103603811043d8000d403082d01d4804141d9280007550019070300d03001280004140b074035000b00740d4201d14801c0098920307003a42c2d110174501b6040190b6400c81110b02160034810145410454040001780740d06007402425031600002e5254401480040d052540006a40c807840d08140e040750054078000700b040006041c0380c28416040074044a111115100d03481400b4411000c8400383c4040320381a654210300780e40164241302c240c1001c88212002c1c01400710008042d035505100a402414043d401403084601314203000301c020020400c1150550044812003080650050107070300c99100c02d81e2200c8580348025011102c400d00e00502404d4000da0380c103180100315041c1c08040450340659024483c00f80c0c00c000c000d040715154940c0d0360b0b10482c0c980d0b1a000008003074118401c43c1001900340c07007845004200d22400399011503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 239302383 1250 239301133 239301151
    0xc0209010f0e0601030b0108061c061a010f0201050c04090e1014060f0901030c1214010203091b04020a08040b0a0b03030c010b091e0103170421020102120c0a0209040206070803 77
    0x3038024442c40b5480c03a0b00680c082c2c0c1c24030b0240050100c050020f419180090031b680c0c050b1241003049490100c81e1003076640d10a0b4000410001c0c002100c000b041070509420820340000c00c004c80304503100d072050145c0f500a04407684110300d050300c1c00044070011b10f082c018045040c0900307140c80c002c0280d5486040030660310814141ca043c600741c0c040180c0c1d44407808070581309600b68070040c008501201e0100064409211241d40d0300000360901c0c1c001c001c4040741d4010f02d58000003c010069402142c60010b80c5140400341d4282c0c089001000306070300a0048400c0050805030011700459041c3c05d2103a0443c0c0503c1c00040c0c00c00000002c00c0c21688924a03244c5540c0d143d100201c400e05001c001c490b8056215080f074040d0b102022030349110448103201c084c045044110300007046040d428122001441d910003441c0030089000300101c4445529001a030141c080c2981e09407a00251008076070148940c940a00406841c0ea4204195044042c20983c0c00540070302c00701001411420007540522507030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 239303633 1250 239302383 239302409
    0x10021518030a020c0a050406031e0501020702030a050c04060f0e1315020d02031f03050d050c0c062a01020412061a150301090b010516120e09010b0d050108030a08010b03070c020901 79
    0x11024003400d40125484036007d1450000c042020446540c100c0008280c50300724110f2040c51410554060f020348140a94180910801c45040107800a180d89000704150ec0130b11206607076803a08040490140700d42100c2d00d6408001a61410220719410030289c0b04010381c01d044030707a40340d0940482c0c20031340d00300b03004503400014050350450b4020041151410004042c04240c115911152125075036540070041c0180411074120501c01400100045c540c0a0b01054603081c0304103142900020034074414100764121000681e444c0c2040c002c0f5001e0342d0000040c82010b00041d9184801800d000c100c190081504240000503a0395545080e103201d004103950ba0b0b129410507801c0b000b25152112214103000c010000010b01a800e62102090590410090b42d8074951207102590440382d02c5401d40e500514000000c2084a402c6000d0f00d840241c1d01804c01c8960303240c100c41035413407091503080e034045214803004011000c008402190302405034a410b0320544080c1e404510081400e0b00300c01041091 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 239304883 1250 239303633 239303653
    0x9030a0c080c041b05070201050711090708060405100510110102040806071e1b110f04110408070b03010e0a0e030705151b090906100c08070501090b0610021518030a02 73
    0x20702030368203402c0840c800484202d613460805011413142e50f00090502001041c41014005040448201200c0c0540311242c207140186004042020884207103215070718100120340d10401c10b80004040c3d400c05440d01400303100302c82058441c100680100c902c2b5640810010800c100b06101d00c3c2e0103034041b5251403084507241c11000d4a42191400c14101304100344400d001c1400c0c200c00c6003035001c0c0e003180c4a00d034100117410100e081c01840540d642d401c5410401034000180d40080100203c9100c03109640510b900c1c0c800f219a288000e108200c95400080302140d2400c1c000c0e80154a58247d0380308581c900440740c7d8500b8248a5058502c00101031544104041c855059001210b051805100c440c641085940020102e01e4003501c41401829030203104503109004040080245400440c080d8641890b441c00030302030b0441603400c403540d0040c540464203d0800703c107a40c00d2100c4640241400c81401040e04540c800028501c40030308000c64000c1a072050244002c0c0b0301d8205a602400704004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 239306133 1250 239304883 239304889
    0x111090103050c030f130303090b0708010305060601112505030703030f021b01052d040e0a0e0a0f320312010803180105030417160b0f01060f0509030a0c080c 69
    0x1004010001c3c40b1001c100b0043e10803429080c182d07204210440800384115182130440040404010061507803000c281402203287e005800541200e100d00211400c40d6680401159100c04820b544005070b405440d807084a0b03900c0c0c0d048440d11518115a140880c0c2d91040082e103400355940c8103501151a42032107180c2240d0500c1b202c520741907513113030380b010141384000003c06034801d00001c0c61003038010506402c461340d500000e04c0c1541186506081e1510b44918481000400546001c0100303845d040b104140c002c1d02040142c03044bd004209640a4100c94645c2c0d4580740d00075002100b99582e25200a0101f103803080c0c0d4512252451005544504050b6244811014180c01040040d4400e0002950214000286100004081c038245844c0d4480b0720781161207000f00442d02c898610085544440211104d0070072040c0750140c5405000c50302d80c0082c0f4030310300c01e080c054500003034021202c08000c42d0081000b0456490013401301c451000b01500c9008040c0c140c0e800009050300301c00d0490f50103203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 239307383 1250 239306133 239306141
    0x10914070608130b0a0608031c0e3409150e060904210e030f0a1707020f010e0d05010c180b0408030910050c03070b01050135060a03050111090103 64
    0x90642019941400e00c2041e18800d41442030f8003c20316900c074000600c070ba040542041004115050840751620a40c01c22200d84a1442a51b40700d018a801a50080d80000107000010f08248440c3e60300c94801441c910707848000c40e241c030b0305880c07141400c0014050300e0394410f0300703030704440d040c03003032801070700301542071f900c441026110500c00e410341010b10000c01d45070180c1c00402282412441c1c4021420801915401060300b01c0c50381c180103c0d01c0e4a240e2040104090103500d10807544485407240a9034000006d005034040a9041342051210248650040860664070071004002d44950f14087ea0b406080d41d06000c01c01000580c0440082494842203550002411803400703064106410513a0959a03070007040641791281c0760f40100440000d0054045464920741e24040c0c2e9504c59023400c201807101420710819000440c01c1c00308000207180fa4200c2d00d0600300c403c15042000c10b2840480801c1c03c40645049c0e800000e4070030001c0000c00c02d101701c5401c1494209044d46a40c41500050116 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 239308633 1250 239307383 239307389
    0x160626100308161a0114031f0c091706040b0702031804020711090415060b0a0203090405060604080a0b06131109010c0c050418020f041b0f02070e090309100201110f090d020301091407 80
    0xb94841d08030103410100c2d846039441c0238888418001030303450b0071410840e40c1410a03400b040d058550302c200c118650070003284140c480c0e40078610211182c1c448100480c0c0e6132013600b0380362504a110701201442850f264000f8096103000e84646220741d00381200003034185005940c1250f030540310b0180700300e9180c01380c01000004d00c0c4150b602c900f40419804069128410110024071959a43c0001103043d81c50a050390050086001102e0b028000e5281000c49420107490403880794503109900010505c490040b50090440c210200e8140381d040001511260b106400490301316403181004200e9468a100303800ea80210b2065a080408072401445007034401c260b2118051410040004102c4c03c0c1c10311100201c0416280044001528400881c1043c0d42a0024a1080c4a5500b44800e0351400009402d407007504035120a008400710406900304c9a9540050300c07104010701c0040800c0c0c0c0381002070120403c0c064070940a0138803e9000030308403100440c0445000c0e00780c001d521a003500400241c406 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 239309883 1250 239308633 239308639
    0x3090114010501090f050d0804081c090e16110c030f0c15090607150e070f0608060103150501050703030605060c1e0c03061305160626100308161a0114 66
    0x145090658178050a184d500070140280b000803000b00800010314201c0e002024444c050350141340e80c44092000c80182d4507103030000240c031030401142c01180825010b004807407451b510141d00250320000daa602e941c00e40000c060303010b10b00c120041a2000c0c0044c0004071030520150060082c000c040204810341111038102da103c09001e920840c0c2c40355011612419040100c40c4c00034501030502c81c000d000545e00110040c0940031001400c101b1202c0e00b2070655031152a21045603452900440c12946d06440c800000c0a2000c010006540142e0081013000d0091030007003000d9403140d0104e0307402e52102130b5400780b5500082c541c0c164101054a025400c00041c00540510964200003a41d2014040c040300e10040710a1401010841d0401883c550881200d00c2c1d080c0300740d91035401424240c0801c032045c1d40340c0d1403540055400862031509500ca00c0840301035196440c11134490383c241707400001c03010071391a0025994102145080da58200e000d549030b0049461507051114207c2d0700e4140d4031200340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 239311133 1250 239309883 239309897
    0x1207032607020315090709020c1501050409050601031b08010504110a15020d0f0e030f100f022106060c030301080a060b040b06030a0f02041706040b0105090402060a0c05010f0203090114010501 84
    0x6030b0300401c440c0802d641d8054601c00d00e8817903040880c1450b41c654000c9407100d10009684d0300c295008564100c030704044000805003682d0326070038171054884413640140780d0340005006000151118948404414000c08030030250b0341c48128032400c481040d01c0540d0f4111070218640000e01e040e40a19002d400c0106810516a0407108060355511100429000b4001e2003c8501c101500c034000f800512940142200ca201d51403040756a00c0c0d49032046414041810038040d460400741381e00840d625100700800c060300c3c234510341050b42c05861014040310343c0b0400404c5054086101040079501230705001001d80540780907403500f4011100d00d4914640900e0502c08112031036581c103420341e9400051700c000410700700e0820407410000c4c865a040741c5102501c41c030034004c1c100d10010b105c80c401c0b40704481151450340c07074404000501b4802c8900079440701d41000006840c6125240000e2402e100384004161400742c00510016600202caa083c01603545000991040d010240441c6c0100001c0c20301d44 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 239312383 1250 239311133 239311147
    0x31403070803010603050c07060603030f030c110c0603040816291501030e07030204020c070918021f110a03050304021017010504020a0e030709050105130b18040212070326 75
    0x1403641e002c144105004e0664480c0015816101d000071950669449442000340546030b1a02824100700c25580f10300092a003461141003034010b81e5114101c120480c01412151244001c10059600080c1700b103403128400d00c81e201e401daa68403510000b940c8a82d81440814100c1248051810380c0c0c004003140e01a16001448402404136003500c41f2100c082c81c011603000058200c1034640301c00c40d1b200a42262000844c0d400c0d00342c5c0401c0c04415520152411b106c9101c6c511811801d0311140c030400f80d40007801c84410741c003458032508455122052418009101440829040c0c1422038180040d004030b4000010041140b426100001c0c080744c280c2080d15071080390284081d01c42d00c05000d01ba0245500085040c1014000c14162a05100c01400c9948241d15115070101606082c0701d41800f071509401c5030401c2d000a80070f01d42c40404042c103168409800d0300c00031042d220b1302800980e00b0200811010f944108107200000c082c6008100c16500d40c030159041c0c4100c20010b200283c801b0320184901 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 239313633 1250 239312383 239312393
    0x406031533150507021e060712090f0501020c060301050d0c031e150e070312170a06031a090c061c05070807091e050d0c05030613060b0604050d0b280603140307 70
    0x2407035103442c1c401030400741b208081c800b2030164807805601404006955100941643c3c0c003105000c10358041086000d04a5030710300059903650711125056902c420144014011410108581043c181c01050004c21f0a03981c1d40341c861200d800c4510312802461611107102c00c5c0305a24100c1c0c00021400002080481c0280d0181e6407282200e0000802e28404500000803040c85104c0c400e40b82c01c0e480000010714208482804002d0201d4030044600007400bd0890746140302510701f061184110001800761500600e04102d00c41e804100a61005400c420240410b190148a00c52040b58683c83d200d1755400c051501804004080e070100e209041540e2400d424402c0c021014400c0721016241350034035400340d2070100b14a446c0743d044640c0501c901400c01441400e902c01601b00d89004082c10172041031004207005941c40345000f0f0b02d4200074030143c860b00098181804c6580703e9540c038000149115055680206454184441c0004540342d00060041c400115102403002200b840214948440b075911 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 239314883 1250 239313633 239313649
    0x9010b0a0e0303270a06050c12070f08030a0c030f151202130e03070606080705060405010c060e011a04060b032211031009030806040603153315050702 66
    0x668400c2050240015001e600d04100740c4010740010740340d20980d444111100e11450781520504c0e442907802d9440011168040c400b1141c2404407000a0240780401c0da21541c2d0380d0b406180116000170880340e040c000300b84074402840c007403210001c01086030340b003608004060700d0710364411900301458241c0d003004102003c000e0303804031180d40c11003851103c07460001484400c0c0f41c610b440c0c117082c101000a10075040200080280ca44900410024a9160440c85541d00c10728028180c000740300308020321103580030306c41e1460719a01c12580880c9034140300a42c2d0782580e0102840302c8400e071380c0207245070192910703011710300103086a1003c007400c500d0540740401040038003900c1d032802004121940024840408031140080d54060126040c40c03159480100092a940c3e2040d800a804030010a4561a00380158000c072078111030030980340394600f1000c0b4020074a07100b03208003441e0542d42ca00b00051580121003004180968038113031441c60464011080c0440340080800c0101c20011080181c5d10060 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 239316133 1250 239314883 239314897
    0x90f0d0e0103020c03070c03050f010605011d040f1d07050103110a050304020a0e040b04062d020c0c0406081e03070c0b0307210b1e030604140715050c01060509010b 72
    0x15114420312000001038000384a08070101000b40000520882408144d91030071048070312402c00c07a000c01ea01c0c00a80d0f03007214045d004540c0060078500410300e000790034081c0840700c060300030300006090a02240407001c851140c04d4101c44000540201b031542070043c0300301c00041c030080c01c0a02104014180064142c420300700d82c08180100030005c01c0640d203d00080e54040c260007101550142051304106000d008111801c680407030400c10140f480c0c407082c0703c07081d90380d880c28401609244025640c2001075044017a440996104035040c02549a6032400703103c0003001c420018182540c1d044d94841d401c16808000000c2a5000700070000002c0c60303a40810381190a003041f055143c0d00ca421080b00c062040900061000040c81400c80b6522016405040000c40c01c0710320300510300ea200c01000d405541c641d91268150018400200412120115101164003d1080e00d81240d121030003c078039140d95940b40030002d030000c6400c48092809120741409460211581c0800f50314000e910035452003030039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 239317383 1250 239316133 239316137
    0x9070e06060c070302091003060b060414010806040b041d010501060e0319030c02040504060b0307080105223e01050720031618050f040f021009090c03060608090f0d 72
    0x2e0209841d4010303c01e000103168020300c0d440241c00c15072104664194540400d036080c52911040118525100c0111402c0f42e1540310510034a444980040d10300c0c4500a04880e0001c2d00e80f000b03070702030f65118440d030551102e48101c400391040700b07034074601c0c01c4541c1600b141c0148800d03002c045190b50b41c000303000300d4040002281074000c0080d501d400c81d103010001d00d009411604000511042006030703001400c900da003d0701160002d80c2d49203116400c2c3d440c01da4182c5203141c42602400e820310076040070355980174001c0c00c40c18507900012040303501e0f40301c1d011a040c11a85010070210700c2d11200c1c8180140d076074801d2824030306004003529650201c414000c401b100d00071322905081c13402d4800703112901c040ba1190050316402c0d566684074216aa40405501580500d4440060b00994800662500443c1c0013442c511032000e0b581d00348001107a4010121040c0b06110200043c848050f000c0c5000380d0300b80341d8001c1091494110301601650010b0301102031504058800e109941000038a40c014030458 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 239318633 1250 239317383 239317387
    0x1802070b18060f040602070b07050d0c090b0906071a0412020d0306050a0b030a0e0703060209031612020405060a03080d02090f03030702551a03070c08090303070f030809070e0606 78
    0xa171034460000d00c00c101008110340c10b24010410295001405040e0f1000c2d610f100380803030040e540c0b088a01002a024560f4244030910050129081c650301406000d0700c00c0b000822141d89000403400801000c0381c0c110b07401800c025100300c646038140203030440c1351300b603080500c155070400000a5051000d802082072103178001c40016a14a0f858100c45002420070040d00d081507100d040100195100c1e00400303001e40b0074400e69001c4000c4880290040310160340003080704021039403c20016100181c800c1e80e00c030503c000c1c00310104000e04000c128100301000e0040c0c0e2862680c050080000044041a109400c184201405a00e980a61300400702d2068401c000803001c1c3e200c40f000511003e9110702c0100c2c59066400502e1001180250143d04402010420302d50b0315500e0940c511201800035081107018408100309034020070311100c080d40324060650421071204042481c42d0030081c41a146520f69090000505400501c0950407405000245c4031483c1801040f1903400b41c0500740500510b40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 239319883 1250 239318633 239318641
    0xf0c0201030b0904050d030c050903070311040e1906060509060f092701060f090606140702010504051e01080609090325060203010312090f050a05060a091802070b18060f 74
    0x21030b03489525100c40042c1101c1140c1014140290f80d034400c1000030011a16290a059202c0e010340240d40000000600401c2d41e107080d0382e030b0020485024055260069102d80d0040390424040c044184060500c3c0304540c480c00082c1000e01c184c40d80d0740e01240c05a82c0200601c00191680c01d2030000840c401e507145040ca4070ba014540d1841200000c24440f6107088014181500c00c040d000802100e09000c00a040c1e0343d101d126007000c55005100b80000b04841140d00c002d8003c0d0742000d4800707180141000da041a9a41c5c0108404010340300140070300c9060300c075002c16a5038001000a4000d001501d014a072488c000b10f136182d9034810340c080c01e0344d4400242140c00903c1400c070b10388650294425015501c0c2c0d65a0724090381da030380c1c0c0c214460010074000b07580032400c405030020030406c40f640100800c22003460a030501007a0340c4501d50000401003148004900301c0c0c0340c0c24028800491901006a554420341803924040c00c014024001c0128841090200900c00150b020340054840b4410049915 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 239321133 1250 239319883 239319887
    0x30406181a0702062b23010b030403210f0204091503110f03010603060f140711120c010b030f0706030f0605060316020a0c030309030b0601020a05100203070302160f02011106070f0c0201 81
    0x1084602003038807880101d07140700c0403080a80010200074850f08006d08104150b840911810800340261041d2480c10300008012a1198402503400070380c0314441c80c0152000b8204109072080d50740c42001680c0c001030108090001449420450016813985400300c40c01c6981d00d24203000c800d22580c0c45110b09641c80b2a0681e029030014000f0340c0c1c048410000281d01c543c100000d000841400c003004014000000c070b000e4001c1c103c2100417101c89015080d07440d08080040c40c141c00030b00c03903400e03559a141301e40380e0307192420040300f544203070300200034035030940341c40801829240c44981e2526107600b0400308121a0310303510181c83d00003a4001079100020003d540c124607000c02c030200608280301c1540f000050581000201040d68059041412039640c1c038801a60b40320002c890081c201d900c580400c1d1002899a409160028036619015103000001c84680e250008200025a07407031803095040401c542c1c000c034046401101c0000030300550f14015101520301141c5011450500034004161402c580c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 239322383 1250 239321133 239321167
    0x30b0a0b04030b01080d090b121509040308090c040204030c0302040e0a23060a09080313050f100b04050109140114010509060c0606040b0402041a0705030c030406181a070206 76
    0x400d1211646071202d40d03d0030700711101107082c42900d1690141c10031000c2c0940c4950250000d50b102a5042480c266142c0c0c00c4c001030f24401050200d00d042d21f00c441098035600d01ca4214001c0780699100d60f6542003140d001030404944084440c031540c410041040005e8a401a542c00c9a8045400180c43d010001d10242410f0142d0305c010042e103485411001d40701d8102c2c407503d411800050807180341c0ea42340c2c811042254403550010305028414400640c2084148ac0c1c2e1030980703132003002a98540b0050061051818a101160341c0300551a00c180c0e4510f4145440790500610490f1070a00c00034000f03041c00440100180a0500b1003034012032078100076405803044410466024004654856401001a80780c017415035000340710324140a07042c00c0310f14040c001e8070180c1d00c415021603102074420124002541c01541300f01c0d0940401d11007803c0f0030360144060002030025441c0e40e1041d40c203001900c1e480c00001c0d001011003d00000c0e180c0a060011411340b0384440d41580e099988a00041d0400400c07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 239323633 1250 239322383 239322389
    0x30e030c06010303120612030c02130b1210110a1e030e0d05091c1e050c0319020a0e15060a020c100207181107060b1906050703110312040201030b0a 65
    0xd4410440000201940016904111540300c003080020649408105100a1310440013500143c0e024928001500c0c0c100f0603070745200789030400044c8098124001c1581c20800d942100119008804c8800c4105590f00507844480c003040c0d0294504841c0d80c001a15a000031407100410040c500c90604045000b80d100401113418034044444ca43c1c400c4038002c02c15400b2115041c0604882c0c5844a9071203440568100e40d50b0f0b014210042903504420744051411440005a46610680031072240c0c944050040745004e103d914020042c94407035006010078080c80b43c2c0a101e0380301c40c81e003c2010b1140001f024221a010440e00c00307075100c009800803440d240442c9031480e17000a083e0000c2d0b600540029040049036400300b12003248203042c400d40030032074a88015501c184641004035000081c2503a01007190290000d080202e038200e031160540c01c0c00d406803c0703079000c2800040c0d85018140c2151355051181c07a0340c4002e620b8500d01c03581c000d84044000e4002414140c0b12007500b20559140000762002d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 239324883 1250 239323633 239323657
    0xd02030709030b091e031612090f0308030105120a050703030e060702090708090f01020901020307060903051c0204140901080d0f02030d0c0203181c140c0603070e041b02070501030e03 80
    0x2030341c10207410f45921581929802044481760300504404a035000c81590300744006000e03005103982594640d40d000c42c9919400d034081004000c8045040341a80c042d0401030b6000e80d201c0f42d07e940c1030200380039040603c40b0342007941c0c0e4449501040001d0b030006190080c1d039498504044820020340c04940306014584000394001c4074141004007036a40440250310681040301183c0d0040c0c0442c50050803480f804407007600503041000b10002084240d001107000c00e202c0d1514a02e406030b0341c1c1049004400881d01803500c9a0002010069000002a041c90f010000c0707800c00303d03552510036150307900c00c40e0524071018010a01000b0525500034001d0710a420203500e0305000074503804d08000d440f03501c000400714080c0f00d040c0560807241003101c44080780b0305400341e83c110200219140c0b40e04001c40c0012502085c4a041c0e481565622144040c50040300e81d6142c05120f50144401c01c001c0e90003c41d001800c40a018880344d0365940d0002d50007040b40d00070300f40000c01e10941d6141f01d0452149500070750f5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 239326133 1250 239324883 239324903
    0x5040f36020d1101080105060a12050c1e0a02100b06030609091507031e0c0801060813060207030306051201050402030706050703020c330c071a09030601090e0106050102060402060d0203070903 84
    0x4140501c20f1100280d418007681d130000540e0b20707101044042e0180c10607000008819501c12208407039181d00064014159941050400c2c0b000708805c0c2d01c5410440d540c2c8052030010860079502601008002e20041c00300205201e5081c0c1c1c04049022400010b111034032500010002c540c011000f070001c4402d001181224503402d1a040c50050081c3c508014048078103880130342c012040070320911030040c05050640e5a41c0380da034602041150906000762100340c02125542c01480010520710050405520a4901140061400d000c00c1901420480124080c1c0d0400d0308002c01a80d01207100d1064500c503007807040e155130040c00c049180c04034503c0001d4100d2121900103020024801e01150f04131070036800f404880070f006006118a00402d84030110580c815035042c042640d203406040707111000308a041d82480c10000000b860808280d10216a0030350321541550007820a0080202800d803c4c00101620f08255011414a02c03c000b10002c2059000c804696842c0c49440647e00a40d08100c03042 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 239327383 1250 239326133 239326159
    0xf071406070906182403152303031611011101020712080105030c13050c0c0613050c030a0b0c0703031b090305071202150306042a02010f1e05040c0f0f05040f3602 71
    0x107050740623580d044102003440c03000480c1c06454000110f526468414202c0f1400c2d41c425500e08594854100c100c0b0305101c03114046109554092000d40911070160078101c00300088180701401d0318106820141c025000341090542685401c603100001a000300400982a52900303440d031410302811142100c80d0091006014480046003000f41a4900640a5540c005030a000301541c1b4600304600a0003000c4460020b000006188003502c9543d00a007400701d601010300180d04482c00c5058001d40114540300006c1c800d00c4010051a80074220714540c01c00490b4054000a011624a40c02c02d0041e0304c00000141403612950425051045604081010040031805001c5004401068240158030340290710040d4844e0b8014202003021541d0054034651040780e4840c09400d00900980d80103048020000b0109803650746840244117215440815034107080800041e10743c0811a580d502d07041144803115414041103200003a5000d1240300704044030b8050a489802d00340c0300c040d600c800b2004500c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 239328633 1250 239327383 239327399
    0xe03040603060f0f03121211040e041109070e04020d060305060408070b09120702010c1103190302070f0b03071d1908010f110f07140607090618240315 66
    0x38005072103e40c0441241141c84c0c2215041c49655403101401e40c580038410164014090100d811a0001080e0301181d040e5500700380360026881a8020840302a5400403c0306102c00518007502c0c000c0103c1e8071030080d0030f10b00001042083c1c06250700f44100da00150021511a41794051030040d94040d00f6a1300314605810030020a4215103000c0e01d12411000005e00042c10104101009000c2c1c0c501403400c004850b00111140c1903100404c5403510002402d40c078459404004001c2c7d008a00c0c007082529031b0051034002e08042c180c0e841401c89211440b0705200f1100c996040ea0b61049151603d83c5002c00d4001c2c80b194415896288a5001021910105404100c5101007405e403440c1343d00a01c00b003101800b000040300c4c84584000381c819420721070702042140c0c0100810000c0e0207540f4210b4078810000c4c02e9070400c0c100b696020041f80280804010b4580c00401c2034000c290f4a0701c0e61003036540f0341001c40603520400e48054524608003103401c402a03000758402e09280c040f607a2050390050301d442c02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 239329883 1250 239328633 239328641
    0x120403050a0f03090816020607020a0f151701031103150916120209010512070f0b03061822060e01052e03200a0e0c0a1403091f0e03040603 61
    0x1e030010b1100c1894000060280c060403071526130201d841071802038000001c00713580000b4581285d0190f01044402c01594480700610301815141115000c164075120054464611034100032081c807010303284089604178410001c904690f0400c01c0801c10054403c0041d0810402d15100c11890505106004003458002802031408038000b03c0010515103800c1075450380500030000a44c080c2120300140070724204000c02d01411420b00040301d140c2a11481100020801d03074011121440c000300401c03c0f640341071102e03040701500c5039010010908103024850b03900c00c16041d03034a115844e10310390401040042c0c1e12054030041d51000820a81c200104c01449442c0c3e02c000c80b6a02c0c628110381100242043d100700011290300c0b266a040d411280d0003448003100c068010b2071313805650b413000080d406a1200c94907104045006100d541e4151202001d0400c2c885d8034083c500c01c079410b00c00c000d0030200c001032400c030006084c0c000c43c08220500c155036001d01350030a1080e50502001c10002689030305904 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 239331133 1250 239329883 239329897
    0x12040603090201170121020120010519140c07020117070f0f0305070e0d02060906040b0417190b0a09080d060602010b0f010e10020c0409140f011a041112040305 70
    0x280e40c90303180c0058005031543c2134080c040c03000c2c443d25100300d101c480c02c050002e01041c0751041c1061544203000030300301d0325003800c041541003050351a40304000d640e6a029034503590b81c01c4000d204106110110184080b6200e00901c50300c00070000045000a40e80100d0620b8001c02c201605600d80340f0b4449801402503085038036503c0801c1051074174032040760080c0500d501c41d07882d603500c9072180b401483c2004413800405809a03009030042102c0442602d8441c0100060000d0b1380000355940d103419440d4445586211640e0361942100310403040f0919a0b19806009a400c0f2603416410340b1000c0e0700b40010044018014000c5034000b401e081700e880b5540010046400c0707500202701d9401100e05100403ca00c01a00e5400140c040306002d8080c0341c030500b001160a01c1f0310403603010100d01d001260071905801e0064411884511510000100030880c900c03042c68284000d0020108414040c040b86801e01d200ba03106a48455440c8162039040041e03074030086141d40900524102420013402942c0419 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 239332383 1250 239331133 239331137
    0x1d130c12050103020102061303170c03011d07080a02030a15140a0e3715090c0c031e0201111c06080d080118021c0506040609180204050912040603090201 67
    0x6032400c80168420399040344e030103130041c1615944050b503e00c001026840201d080c02a09140d07400240c10368807199124410721101c9503a00d504004c01e40d0f00c28084911124592450442046492075102c02203c0d0808420b800141e22038070b0b41210000606644400408440c4c0403140000b00c071840340820101140080c1d901d0080e07240c445141a0314460111880c1104401001d4500407040f441242d40c90030341c03410007200100014180d4020f081c0d510040180c00d01c49280001804a5100b0b841144000040b41c00c015032102c0103954040e101c0100402210301c070309801c1d1180c100450003034010903200340020040960303624070300c250350700d07108508001501c4040c94000d010502d91400030b0444c115444507110170000e40c1c80d00017030404040b1034600c50000344e5000d110361410404640d14880081d0601c7c2c0c004907a500c0c18505000c01c4411a40c41900f8036410310840c12020340e40d00d001c80d04c181e901a240460035940e82d111992414070300e4980c04000362800180001e04d281c1c154441d4901501c00d07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 239333633 1250 239332383 239332397
    0xf15101211062d0a09050904030c02030a030206011a16060f060b1303050111070b19060f080f0d0305010605070f050c0a0806040506010e0c090f010c0501020f04050a0807060509011d130c 81
    0x1010f00901107000b064030780c2000c6612000180070b0b51074032210440d8042d1180c60400803213110340e4042070030000080012800f5901030001130140380b410300f40c4024040a00042d02d030620042e44004242081c4058020b0440d60f510031305c4a01d080c0307242d0007001c042d140301d58001e41d441100c1c55020120000601c019500ca510308031080c22400660300c01c65070102c1d0480140c40480d01e410007150b074400f000342003c0e15a41d648540004011450304803610041800d40c0c0a09121621049102e0402b01d03a690388204051800c001405050342100c10b0340d401030780000e282030402400f0b1520354900044845800ea1004140d07134001001f01c40060540e100ba07124034151807880e641da10700c502e0f480f60244d46d903081b07803642070002110500340a45181c050482c149020f1002c0c1d00c2c5a00c03207500b240d0084c414445140c0c4000303400e12190030300361440001040d40384000c0140900c3d00300300514901590058038108940000b0f18a08089071424100c1d0100004210040b2004101000801005101202ca020900b4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 239334883 1250 239333633 239333707
    0x10c06020f07051207052505040603080a031a01080c0a03021605012304110907020c041401090c020307080a0806060c07060305161d060a031d0f1510121106 68
    0x102c1c80070f0350f4200d54080001c10b03003081c0075010100380e0040d1501f0045041e82031540081c2c030365541d001c0d9270010750007000019604e02c04418010103581049000311400d80d03c00303490064503603009950560001407014415120040138dc0100d000e84a018814a0f9040343c0d0402141031060641c0960007220500140c50a07007489031141c51000ca0040360b024000c034905400100840c24079651a69100b41948151000e01640000103402c0b240b950b08920750300001e680040c000e01050703100e0403044070407900045041803690360340d0000314032a040c031500401ca510070101d4103d0708c480c010340303002003000030075039200c141c603528000d00400b800c882c0c400c13a2032f003902007008500d03001c1c540f008105904140030340c62003220002800340d00da0104000c141016030362aa2140c1001c5408140a490201c2d0005000080c5581c491b00c0d1905400022048100204d00240811420300e0840c1c1400c41d01d0102041f460060303103080c10050400c01ca18010b8010f01f0000d41000036008000350030001c05030710705810107060341c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 239336133 1250 239334883 239334913
    0x70806100e0906070c0f020a080a060906061413021b12031e0601020c0409080f04170c010305061f14040311101b08070804031a07140a0c11010c06020f0705 68
    0x1c00f80c030b80310b021850304017030140030500a50342d00c0f5190303001401c00210a503030780404030310b80444a842a1140d80d036500c00d810030800d540c0605030003001e01143c1d5040c0d05003868009501080c101c1c0350706002c41c1d4005101500403254000808448800310305481038081001000104e541c003c4a0070f00202440c0024031501c46074840295000b40d4060340101101c03100281070000406003640c0555864405002071080106480001d00c060065080c3e03034800c5844840c041403030601320b095600c1c107050802c002c0111a4944038031070030041061114038040504000340c00c0d2000d402c2c0c00c2e00e8030f034402000140030040c080d0300c0d5030344c10006909580b000340e020318645040f503921800540d20851000000060070100d038030074029000710b6000305166880c166a9544080038002c803203100d25002d414031020064aa80c001c00e05c240800a500b04044c500101a040200100d036012402031903540f400c51030b103c00e80d11400d0a0075950341d221904542e101038203408488203401c4010304403035910070389688040b08030f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 239337383 1250 239336133 239336143
    0x304030809150c0309010e0d050406080108070e06100e04110307020c0f060f0f0409140402010917060105091909060e190c0b0306031606081902090d14070806100e09 72
    0x1821203410b0a01a2a482e580718001d80c8090041070b2250b4840c90103071440c9000340034800d00701a00351920f42d955858100c0240074184140c0c420300c0c440e0486402002021a41090150b0154088602040030021001c0a032488111b528103180c0062a000056141c41e41040c0110b004254503001c44d0703a000c4440f800c100d00e44000c909190b4120200344103e2003442c2c02d000183c240c06004444082c245a103c12030241140c64040c40d82c0d1a05815600b80320640d60401c2695010300321194030b41c01002c49001c4115503e013810f1203024040c481e03240c0003500300c85032060400340c141c803154011b0040b401c10741003c0010304480b1000c4281c0d40150b0984048611890740c039030900c00da116000380907992800d400702000381c00083c020b58240c05102e01d4000d1078070f002d06c0840c02070489900e4804240c100039081e18600d00d80601e00043d0140704000c090102d83d50040929611940120203011900010560900340011684030380060f108200034091084103c0491600f900c0104850322000e42c1c99100f40f907a11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 239338633 1250 239337383 239337403
    0x9090f050411040f0b090a05010f0f0807030209060105090402070f051c08150109030b01080607020606040207030509150c2a09010302010c0f02031e012025021302040305030304030809 80
    0x40c581010042c035504064000700090060349a0004800003a030010901d5202c00b141c03d0100d9541d9580148036601000d6a0030f0007521035400301e41003290529400750350b01c01e098040a403060185100080c8541e208404540074154050f00541d00c4074001d10b0700310707494620801c04889034050b19689141001380d001424641c48040c1d40c80c2403582d1101c0340e410301800c502ca44200c0c1046a80940800801c1d040c0e5402070003046102c0040240e80f4205400904001e0064501e40c400c2d401041070b000400c0d4400b0540c2c2e4a008100c601000000d00c0301108441441024400b0704240a182054200d034465480304480c085010b42c0011f010100a008005c3d13000024000203000c150f02040150206101400206c1103920250454403900d081a42c40e0508041140c155142a034498521807108100441c0c164040111800314900b030101c624140d880c1c40355a0010012203146c10408002599140220105640b1080d0350456644c5c1d22804c106031070794000c85080c1c010a0441c0f000c03452010000400c9050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 239339883 1250 239338633 239338643
    0x7080c010f18020d051c02032106090114010c12020a051207050a1e1b0501020c0922030201090c0f030218040f03030506010c05010e03040611121602150a09090f0504 72
    0x4408803950070840c2ea0007414400b079819210300561485400d10390840c401d1b0000c156001107403115034180d0104041200c01041039100f80784031040c040240c848100702e905413001c00802141e4000c40000488962682300c201520406410802507070306600407541140d07660160060755840380b003980522180d0312039280000c0203030b8010a201d102190f949136454a1a503000c140f0642444569101c1c100d19032000c0f140060b01c5911810104010f42c0c0401176290102d200380d840007000d14000c4445420001258130b00b4a105600501c1e400405100303601500940c1e034843c100c8106151180311100b42402c80780030072809118034283d1052146040141c8612856122462040c801c00540c1e045000d010041c0985040c0041020004000703402802003480800c03100c0011600d441c035004000708000e1151030400c1c140d800003a800055030720044121180c25001f5107004142050318801300d03040540318402e1444504002c01c00c0d00340c03181d0003908182100c14203070080c008801506048400c550302950018a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 239341133 1250 239339883 239339921
    0xd0605060913020901170c1201090b01120e030409060f1e030507031b0503060a050603060a0204080c09060a030812150402090f010e030106090903051b0a020a0915090207080c010f 78
    0x36150350307001001d44d41018500246e20407604500d0649105054907190351002000c2082810341c541040703d9801052901824468900c018001900c04480d1000003128a80c40709802c106d9400b04100711360042c01c007071004106031503540d541007203240000d0044d481ca40704034200c1c1c0044c5403501d507a0f00040c1e94001c1c1c09004041c0c503580d540c7d00611080021400c03115680709001505603424031940e8410849410042050326204c000c250400c00001e00031418a40b0612051009201c0054028560107043d290b01c1655150440060f200d0700d11584020450003000500c4150103116140990013084c071000420305511840c010402a4001c82c404507800c1941c009000a0641c07055000040d03010001c0d00008003651aa2940f9003628205c2c80160082900080c020030f49901c1800031f079030f4042001001c0d040400036940060402c0c03d00784210010a0307128200e00507141007022007280141301c0200115960340192030f04a03150b41000b00a0101d0b54a408501c429508090055860140c42480710303071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 239342383 1250 239341133 239341159
    0x12060c0a180b0f03070210060b1803010f0e160504090b0c030a241814011208040e07090303031406010f030e010b1c02120d0509060c160b0d06050609 65
    0x4415810740035004101104085000641c001c0380c000900c014512060101d503285000b0001915081b200c000c5020090b00c0c0c85400c020050074501510b5205a00c0701e8510754156028000901600341c1198240e40513281107107030030101c80001028944071100c1c01d40610301c50390321f10800c000c46024090180a03a1601c2c4001400c80710a01c00031030b40902040400509030001820411102c0780c3d44107401094200c2c094180504514955a0103040101400502406001c80c0610b024101c0c107106850104030543e030350104024a10050790040d04043c0060f0142c0c0c41e02c04c10080452405102c02c4d00032a240002c55604180d12200c0c1a1196806840e445142d140d07120040f4010040c50300319034555540c8000743c50403076a034002100d940c0344502400101c030381118010003a09810000c00707111150300110024800640100903109418000c84d240e80c5c4420302c040010b41480884c201000c00300400d0740000c42c1001c3d100c8003070070280751440410011207031580f09000d03442c8102441a944031090740e1100c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 239343633 1250 239342383 239342387
    0x21e0601051c0606080615060408100c0507062a050901021f0905060114040b030a20060d0e060a06090b09010b070309050603011403240a0c03020c0a050102070212060c0a 74
    0x7048540080071030060302c20040b07072500c2048400c55005641590040020702c0441c00c5440700724900c0400803210285801c4c9802c0a040c1d0350100c880c500389903162100c400019031402001034032001604400d0030700c482c04070301c801c04605d816500302c0440b0001d205101002c0641c0300b4810346000030070680041c1204014407001941548034070f0120085c840d103921402c1e00081d0140015402002800012142c0844000410095414455400780070b6806441c00c1c2001c9000082c1d00c0310440140480c9003280c244040c04074900e0310490391680300a50030902e620013000000100d03144503070301284007000923540324a0000d00713840544d900c407580208102d005110b02d1074048004c1c02000e11070300b400c2c503a450741e80010a0b1503400c264020240c3d0038000c6555201d500b418402e0482c804501c5002c41c000b600516040840e0450240805049541e14800003190703a0095040303903280c42c2e812080b1849411f95141c405e010b036015203400c0f80280c85401d07000702c0704000020320728020340c20a4176147400e004041c441 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 239344883 1250 239343633 239343649
    0x90b090d080910030e060c03041a0402061308031b03041815080a0b0718060f050a02160902180901030b07121103040f03030c1103040b0901021e0d021e060105 69
    0x1090701d000804010b16400c982d154541c0404210450b00e020698104003400c26051000051945000d09410810040010f540084010181150041100f15519180089051800b80b400c001600d10169400481e4000300080030380300b0860311106610700c0107421041c0540f05e0003039210785007400e215503004d01ca640d016504a000720300c0413020000515030762016024a4075084a03426207000300e1540c180070101d903111401c0700e280801c44100d4461f20749006002012000302c4202d050401101056160807031340309010602c5140042036011001e103495a000c3d1000b90f006946070128107040a2412a0b07030b00306210020704803604038109a03003ea0320480203441d0303000c00c1901408400da46515062584901002031400f890041c2c2401950040a141c041d088580e05c50700401808140103030b80f110588000121020760350030254642c5c880000200503480e04204c84003060000001c0414046101760000c1ca5111421142d403c07214550030300e0752980c00400c42100c440000d6081100180250700b0082c81e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 239346133 1250 239344883 239344909
    0x30f0a020f060d0f090b0f100e010302010e010201021201240201050c040e04020607150c030608060f01050111010f110703141606051e040b010510140324130b10090b09 73
    0x10b40410028501e0400030100c5d55a9001202c40450140038018840c4010441c1c95100c421090030403811428420300798140390f4140710080c1007006511070308400e64400c2d0155117240011800344200d07541c449507052039441c1c581c04119108000351b82440203561050182c0c0e800364002e420f403249464200f454200300420020070076600100e003045480000362020b1652851244429400100c807048200020150b0b1f24507809080c0c50342c407820a10003000d00302c003176a6045500909050540a11120f0341d039014007403211500e003a0702e140026000c0b2805031100105070180c441c1d503461501800c144d1041c5d04034003c007542e403140e44114425070320000d400d40c0d00054006405030100c042d0103100d001301c018440002c8800301d44a140030001000b9a05200c3c1059568903454145a4000c02403045480020f00000b0700c05440103440d007160307000e0781c641d5044d00f21201c10090490400340002403045009000c1cbd04c103910b40984001c109010034148a00d1000c4142c3d688113921078608120b280c100080560428 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 239347383 1250 239346133 239346157
    0x1a0f01020106120b1906140919140109060f06020303160905060a030f060e010b0f0d060515070b010506090f13110301090902150a091e03051605030f0a020f06 69
    0x142c404500111550f98400701d0510484280d1030501d0b11204500c034640701041c4031003182d820080240b1440720890303d103c02809054600100c203581d01e80b028046410041250b141d00e901d030200d8510010480e44609043c0c0e0117030102440039641d6a442164205403d11480d001600244040303804c4005200c0807840a1980340382c403080842d1990b00050b1503a00808000f07001c0707980c1d038008030003e8003103000740001410001341d100c10750361400f58001807a101c0e07400c1452600c43d0024030080c0e800c1c02544140b000d48006800400f2105403114140303525030201005a4401c6100c0000081ca403030301c038046500c1148083c26040c071003c07404091100800c00300c0610041c9640743c13140e205038111954003031030003401001c00119420000c1d005000d003210030646101d03000c0c44100030440d40c16800189003400c4422640842d480c10340100408000c40741503410040850040c50a0203020700f8011012405440d000c406440e240d4940d001e0040d514058440021341141480c42050f80d28030703181020b4501404a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 239348633 1250 239347383 239347391
    0x15020102040305070f0503010e0c03031b1507020d170702071203021e03130e0c030408070c031401050402010e030d17060a0909060e120c1902150705070503060a1a0f010201 75
    0x25900c25003001302580040d0300d22200350104105614007400741c99014043c0c00094038926001d880402e44910039410b14102c1d518071181d40710b43e1281c040002c1d80e88941e601a610000e42030051009483d040c0c40120203000841500c440a10560202c41c424001c24031500142601498000d0041c0785440c424070036070541c0212050200100302445084002460900c09160703900c405c100f0703a00401e8004d0700030303041460f005420846800c0040044941068005021517284d41c158544112266001e4000520343c2c004041030211000301500a0b40c05103100362100343c00074124005050362045940340b0000003c111300f10448213800c2003007100e500030001615541d801d64940b8502000c1e9100b4401c121041039441164814002040c0580c2544540400700c10780790802c1888070980c0c0e5920355001990324080882c4401c115940d04880070302d04041046001c3d2140000e041031500c540603807140c1c0b40a405680c00240302e40700b0500ca802c0901480303412001701c0500c10401d00000c0c51010b00038905540da2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 239349883 1250 239348633 239348639
    0xc05090405040318080d051c1e090c120803181c020a0c06050403030c0615210506090102090604060305090703140d1d010518010e060d0902011707091502010204 70
    0x14a000380d070311a038080c2d240c900134401400304500241c1c407140e2001020f500302e1000c2114981d400b00c01c940700407001446610800e0003682c443c0c002080c10140c1c45038240080d5460504c0340d800c1e50810b28026000341c1482e51035540d84c01441d100014008002007915808000080d224a50203981c00680035400040b12428a0003403e030300c2140c0100384440d80580d1020b01c1c80e504014491200a0280500f460038601b0146540d8024112401480000f04456280c01062a080b0348002d2144000e01c10200e2183c2d0700390707a01303104060301c42c0880416101c0340075410005001c0007050003141c60440c0e015001074642890044100c0040c2000341c081689d900400c540040480e8041d8800c514554041010b010031400e100c501402030803840c1c1c601c10f111100203c130140c080c0c1c3c00c54241c40b41090005121103030702e0610340048603050f50300405654003034408140c032182c42019a015443c424800c0e2107009100001450084810380304907940d10003c2e10030b460a001c80110000c07400c2c08010140005030602d92 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 239351133 1250 239349883 239349889
    0xb03090c060307110c0d0c03030f050c03030c0a081e06120c09090f06150312030a0f060b0a0201060902090306010b070212030d05100902070512090111060c0a0e0a0f090c0509 76
    0x8019a010b81c001802d004130301603000002d00021101d50012210200101d209980c0c6241b038040c644000b600b801070003000c00031560702400c120399010141905403592440d011051401d0354015444900008080703400182c038511382d60300c082c0e0b83e5a02190034940c03150f075000c1c1080413008803400080d0880c02045065031543d10f4440c11f86001e80c110310058907204404888240c81e02c28005d05070720702503003402e400c003481c0c2d200410345000b40300041c101d2595a50320b25414030090401d507803069484a2810000090080400010307101c003007015070003070114550714180c5201380e008048100d0b41c1070700210010001400341c90010500c603803000d402c003101e903c05440180d0039908080c034200e0980c1e03159801c0148860b114100080944045d0390114103080103030312015640c5015800c08614070300f0020320004283c0c0039052a20b50306003034408031040c3d0300d0702c010448c91581181e02e100c0c0102e0000340713900c04c0c00c2c80c04404070020345000c09804c17154946400c111101405400c0002d1091000400036900d16803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 239352383 1250 239351133 239351137
    0x1120e030f160b090d050d05060f1809120702010e040203090115030609050d0503070e24070c0f05151602040f0e1516020c0d020a090c09090e07030b010b03090c06 71
    0xc1d4420421020681d4900307003d401c2181c000c00d2401075070892881c009060390800c0540c6e1102c180c4a20000349030703480740049800c031485203070180e500c00100604000010040803c1c1ea104003154419a000500074480c001058020034800030302181080000540508055001c1d607404032960002052010359200d45004426254200f500c03000d4599040105029041190600403400780c5065803a5180010005045c6011000d030140b040030003081c0500200000078042140c00c1c0c5150040ea9201007074a00358203a01400c1c4554410f070890950700241b03c5c5050740c60030003025295043d8518001954100722010102d0071001ca038807135a6492140c001550612400c00740d480020002c080c03139803100e0003100d00010300924440d0691010326800d900705030702082d050300400c0117442c0072412240500c0001c55200aa0304031445140c81c01d03420040c3d4036441041e0004441c0e07030328420400b840180320099101d8001c0c0c000903141c980700c80010080c4090100046600080d8541581c41040c0b40f24000b814130707 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 239353633 1250 239352383 239352397
    0x50d05030a0207050108042111061003030801151e02030708132d0909060906020d06031509201c0c05040e0105010311270118060b030601120e030f 64
    0x1544041400740c1c00030740401428001e803000742003036841850b1036501d08156800e08000d45a0015240c8800619680102e507042120090101950854540f290b100e15080000744003e4000803070050002070941e164001c0c28a9140880c0d41e60020401915040c00c407400018850504500c030410078040421070f0000500500700c0070a8940c1c282a00c0c0180e0000452a40401040940e6107141c3d00c10708140c0c0700880504903860035002040404250801200928245901070704082c000500140590401c0e40f0a02c01d4034031603100e030a0001c0180304500c1c12200301c4c180040145511b4051010b001040311440100f00e08000d00a5104034002c443c0740c5080c8114003000c0720461800c0a0a0003545001c0c0160510b00c1c5101e00200502d40c55031b21103901400c1c4041409000340e040780240400c803001035440340121003403030500710070340d50b91241240d0f080b81001401d60b502d18035256001c2403030200401100e014110503901c4a0130f44031540406002081c0700d116800183c402003101241046076440a8a10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 239354883 1250 239353633 239353643
    0xb061c1e0c2c06030d0c060e030d020f030a060803160201081306020703030506011b0206070b04021203030c04051903110f01051b06060a0b030c03040b06040609050906100e1e10050d 79
    0x81142030100c0c41030b0000e805405903102c1d030061000c0c1645258001d00c51a0300540000002c10030214145c2d606040d4071483c01c0400066000269845122154000442c000d5400b00000c000380b69541c001580c86e80100f042e0642c00302c148001c440e01561180d054035030031071240702254030030030815542c0341704a034002001200402c0c0c40300c00f044071071b60300805c5c02d5020307894060920350000c02507400680c291142d103200802c04406d20010030250344a4006c001c404048400480359a0300b014240005560494883c2c03d100b03075101100795083d58684110031048070391150f60b200381c00040d1420000203482d548001410000240070060340d4041d801003d420030b0019070302070841c6c0d0070301c442444101c0140343c01180c80002c082044c0141030580508803070380103401c00146c840a455076400180038158542c4084140b030f0400702030140113072012811038003c01c01c01a9241d049981c45034100319100341180c0401011741001549200304800300318055012502c891b80a008a0f2a8000915403e054441c1640c07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 239356133 1250 239354883 239354939
    0x702011b02010f0b150d18050d1805041103040b04030c0b07090f0f0f120c0b0f0a03050f0601080a0b0d061b022a06070318030b061c1e0c 60
    0x8803004451251455011068455003a00d11172882400701c54880c40034203840c2d1580d940e50900c00710013600d43c0b462040781c3c00001d0381e410f81001c66001303215290220384100c140c1080f1100068515003446020341d001d00e081241c070305607611500c402030151030041c402c0d014054510311240c00103400c4003825200344180d072244040517091081c52000c0714050340000340800d09010062160260b07002241003141c00180141c2c0d409095461700c21043e000a0740001100036021482d000c250000c840507000110702c80d034040100e5a01c5240002c02a82d05413000340c0441d0600c0c02103010031155800170b50300e5240c041c008000c0a4081c0d501d00045030500050a903c410380d140f02039041990620200b81c00f4030b141c400b04151045100c0380c074481c0010166015224a0001030003904150040c1c009820a200041510703290307950342e08012818401c200e800c1c40c1728401c1030b0901e0700034030481c81c2040d0b04507411200a550b504020200d03005d601d0403509040d210040d40043c0001c518800315080e140d040303002001d800b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 239357383 1250 239356133 239356151
    0xf020a090213050105030c03270714010e04140703230112020907020d020615040603240c0201021813020f0c0a050724140f18120c180702011b0201 64
    0xc0000d02d054108504000082051050903000002a02d03000400842043c9442c500345840b25402d80d000f000b20292800341400004400b074440c0c0d843c500044003030300d802d01081c0f049002c000849882e00c0f00c041c5904c0c2c14601040d48644130368401c1d4000103504190895000003c4118100c00b04240d011034406690395660034114200707540d8a540085140c0010702c4100043d46010751100780040c02c0c00c400c4000210450080c2e0741d15000f102c021600a4150311001e244c0c405003284144c200541c401c00d00341030400d940c1419105200704d610719611030803950380c800342718820012044560745a08440903000c0c01180401d400f00d00040406170000e4000700b00340415440c001c0c1c10f24130198001100700314140301c0004050020600c442000d60240741c152048400a64514011702412240302c40030304000c2800e0440210302c52540440741011103800d6841540c1b502c0b4950350300344034406680c109035280e5080480c4808064056001402e40c00003007650303000a41300240d001291100140140c2d11910301c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 239358633 1250 239357383 239357407
    0x90a080c030c0105130e270a0302060c040605120402060706110703080109020f03010608061f11060f13080a030b060d0501030209070f02060c07020406123002190f020a0902 75
    0x2c41404a00307090890601070460440302800da900c0c81000c0800d40c0340070001d03840070002c5a008410554082c40c2a4210541240050352075102c4c400c1200540308a9020990807910300c0c060b03400301d0700240c4d2440d00c0d0044103400c16507a020701034012600000e091000c440011050301540c101094084002c81d101e142c541001040f200042e03002c149220320410001c0c00005625084038151482414049902d403660070100380b0440101c5041c0000f00c80d600310b0188031585c0440d02181d6845c0300707000c0714102e403941c0c0c00c0c0840320b90056801d2051491030000382c02c002401d9002a000d40d4180b410001886420b24000c1030340ca81c041c032188201650750b84014000c44c90005417054105555140004204031218006036075698060f1030045461408a8200301311341c0c1e190008005490602a4103028101a00d88410b0942e10030789102c0c0c900f02c60016401a20005064025840303417154010b00780444c0c503c0c054007140301c2e205820703542c5c11403c0c4903040158564a60290007004043c00041c2d80e240c0407089 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 239359883 1250 239358633 239358643
    0xc0109090209060412021807030e2401170a2112020304020315090102072901171c1403040f0303050115090e13051902010801050f060a030c05090a080c03 67
    0x40d5010901c14454440e00d9240d40050b40c0941d240711000549084203400003030351621901c0c000c540356183d400c00300200703194150080350280c02b45004032030801410304079401c1c044840701142c0e59080481e000405c0703400d60707407820101c1031100c84096500c82c04407502c1d02140c2c0d2003081c02125402600e050301850075540001c400742e881046c84821411400d180c0d002903154002005038540c040c3c80640460b28110080d07041f2054540d00c880b010400c0704c02c1c010002d4091450800d502e404040c01780001484110b82d8001c0d00c0c00c1000359000d090b03a184030344002003c40c400c01d141c00d4100304084038019145800d8600850045c0d00981c444441c0356064500242555016088000441e08200d0603807651504a1240303c244d42503040c1c02809a52501d040e1020008185006000c9115845203910103146001c030303030081c2134001c2c0e841c40c0d1181e03210000d002c1305c0388556400580200b020018420241d119034082ea0341d0f270080c0c2c078040b0700d4803102c40c0020300f200d002500000c0f11600104802c80c441c0c542001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 239361133 1250 239359883 239359889
    0x501080109050103110f01360801060503191a13050715020d0c05030c03070804090c0c08071407050a080709050f0403020327091009200301060e0616050c0109 69
    0x428003030b80d81980e442142c110508800c190041c444901070001682c007842c94000d0078401181a000c3c03200600700000c07200c00c0020381403400400c4200000c00c0049040c01080e080e140094002c1c60948140402108003c8411200b038402d201040121801944052107560198010070b03599040340c503c42c2086414000c3e607911105190181807800c00755580c000c01c5ca88203c0090342440403035800c0c281059410745c070a544081c0e407940400624182080301540182c0f09540346a00d08108144000300182c1c0c8040d0b1050015200180c240300c48000102d0701040010382d40d420750142c0310320a41c1c2d8000301d05001d5071608410415081080c050000035010701c140c903886010002001c4c51814180c030044d45030710402c810b0301c01055200140d601d401d502204032529880c0058402c041c14540003044d403101c0c1056004907216581040c503854207002004003031080c500042d4031780d1859640b03042015905142400d000540240052282504081101411200300d03070242000e41648418000010105505a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 239362383 1250 239361133 239361149
    0x30b090907061b0501020d110a090b0403150b120106080d0e0a05090c07080f030709060f02160b0313080304050109050c09070c0605060d02030a06090c0605040b2a0604060605010801 79
    0x1c02c80d07150b01070200120001106020000450356040c420302910074580409103650030440c0703080c0d50008110040581d6800e1395102d003251503d0740760300701045c46144005441d2580e10516400011407942c00409030f104000d010014040381c9040d141d095034140c1d400414139030842c00301d49004035000001425990390490701003403c0c40c103200014140d41000f81040100c0c810100d01481007040c0e4030b04a51180c2e8000c42040c0e101c0ca80064000c2c4400c01764011000001c17444400102082d0001450071510803000c00c100303404c9810600c0380c00e01a00001c10380174000201403240350200e88408010b50065001e24004100e0700c405052042ca0b1484040d812800ba1802c0c81c2005982a48101e0041c110390b0301c40000f10f440c2e100d0f24005070010744038035000703513040c000c0555010400503c0e81c0700340308180c0302e9002100003075074a40064405000d144204811080104819440c05e608458071504100c04ac0c0e075090021041d0b00c1c016032400340210f4040354840e58511082c1f1507581c100d82c0041c01000e00c0b07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 239363633 1250 239362383 239362393
    0x5100c1d03060a05070201020403050a0f12050f1801030f0609020c010b090108060a0b0103110a11010f0203091203040f0609080703021b060403120e040c020d030605100813080904050403030b0909 85
    0x2000101e961a0001862981103540c1d600100703200034801c0d011140155000011580b40305102c0c10040200080c60a00b2201e2841c20000542c0b03e80c0144c064401c240320030100142006c4003804074000d1050440c00b418101950f0303651480a1a0721803107000c01510701158010307120b10b81d19410a0071a0074503890380340724540644c0100a075003800183c00c3da00079034460700400c0d1040000011b801401e14004201d11180002c43d42c43d00f415482214105540e02c40c2d03000380071402404411104a02c001d80300e5001070b030403440344542034200500003503420a11031280c2c018181c1c102c2d250102200d0100a00f11542d1200241c01380c2032503410007492b2401c66940e50004031070b600c0200050030505c503601c001414049030010000b07601d40680b241c4130101801600134003259622b078000a4591040d403489502291500c7c0001c82c960800050f0f102018480d40c650340003035100c4208884072040300310300c100c0b14600301704180c3d650b070f03229409228020740c82038401103610a0850100401008000c0080c0e0560b408 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 239364883 1250 239363633 239363687
    0x10603060503100b1c06110d050604050f01060206370b100302040f050405070c061409120f0a030e1615090b071211011d0d0e0a060801091805100c 64
    0x207001c00300c0d40c0d104d41c80380b054002a030949801c4025203824200987c8042000c1031b105040d008079006184a40030444d010401a03a4101080c00482030a010f11030041c2e001000284a40141c42c80c01d04500064082c0882c00800c54072448000300803408008a01c0368440016200d103040070042900194504d0030298181030406454911800f150311a16100da031b19600400d080318001c0e160008480d801110500540b40d4010810a009005543d030103141e2050040314000200350200342c85010090f810954030300311000c030303003140500340c0340c1091082401000d01800101e004030310301900030058601c260006014846000c3c0c0072885130343c4078070f800081c00c22032000010441c09440f03100811600308064480749503201d480c01801c1c00c440c0326285103188040100c6d14a0005200c818070880f603622459192241018000c0840b446d03c0b4030808a841000103005950080e0084031108010103002000864541c48003407074480c281c3c0c0082d085694804600d180c00d070b44680351502452040c64070b4080080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 239366133 1250 239364883 239364889
    0x40f06020d0e130b09040f020906040b150702040e03040303090e13050a0f1b080a0501050601030902010210111e030a061401090306020313080a0504060206060301090b151305010603060503100b 84
    0x28440c54a0b51040f0604050682458180d40c400601018042c02a800601e07061070101c03001c2c04071140c240c1c498a00c00002036414a0300340180b02c10740b8805020130b07000e007030404030002d26a000030800f2684261a0b41c1301c81c051280030000b0344000c600a580305c010240c80c000140c0900c640281075408460340784900364010400005243c2000c0d40d00240c44c2806405a0800c03030750381651540c00b03180350f00e40500001180e082c009401c408941c022402000241c444000540031030b4524070000340960400e214075611060b8641c8281100848d4141051030310740c001c2101d40c003608411008010301c00c008004e0000c2040c5a100d4a0081c0c0303164002c1d64044c2c0d0303c08001030007d09451000908158000000400000c40c01c0910f003405030780400c00948030000d03124082d0094105000e00001803203013034001040c500c0c0500034081e03140e0700880c00114949403c594250f980d40c80c401c41c0d5400084008060a00c0781c8903124440c002c0556a80c0094040c0c209802c05003030032840046680f0f842e08040d10b11105507 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 239367383 1250 239366133 239366147
    0x603030c080a09180e060a05010e0615040905130302060615030114030313030804030b0f01270b0307151202070c052209110109090e0705040e0c0a0b040f06020d 70
    0x2508600402d8881061400443d01c00c8402c2c1c10544074410740301000c81c1c082c9480d0f000100052440c00981c1c15a070707510500c45d03040f92001d00c40c01400e00c107080301244403400d00002003c44e9044d8480e009140544805024064410503600311840d00326600c070720000e160f4103004e160340004d41105d409140b142e181350b0841582c0011f000708002462604001152668100100d030b90b03482009402c5404550741c1e040c0155950051311041d00c2e40819030740040c203907150006066059407143e0001e0070b40c180c211824043c2c0e0b40305000020381c4aa644000f03909880d502000303400001d20b000310301c0c2245504000c03c020512003c2c101c550840c64018031031075002500180c0c040702540c03400d0f03130848580c0503145e61020b072030505080740065251130266220203200c4e034848818407440f001c1c0ca03000e04881d51516080308503141120071000f070b600042024050f80c5460340101101106010440e00c151021100240c0b40c5082d681c44044c0240c0001070400180707500101c558020412400074054009616001811031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 239368633 1250 239367383 239367407
    0x2105010b1308370209010314150408040b0a090902070507061b02010206040227010e2d0f10090e07031101020303010509010e13060e030306031203010b0d1e141005010201060303 77
    0xb0b44806a00f0046110380005507010254000340040b84a503502d0034040004244070a400b5800d001d42031a0850041740100c0f264080e65010a50600e0300b840c1141c0380e03566400480390343c000c202e2101303000681c81c40a0300103041131500890203850000d00d081c0b4060500300d800100c0340b0728100b9034081000541c2c0c01041603035002d601510070070419250301094040304148000150355986820001180112450400c2e078482d420000998203140c0c2c0758404032100d080c1d455002c0540713128540004206a001886813134005840000003448243c5a030360290990744026584461580541000c00030310400a00350780c2c05074000c0c0065451941801c012074042d40050143c04841c01100340404d8110b6800f41c00d400510350880d004200c3d04078800c0d20f072a101d0380117540399440f030710400c12040e403001e6441c0c0459040300d00d000151403800c0c4520480002410340c0c3c02c03114035200704101d4080200136a0b8029401a48544141a1f013246004074009242d858035411460440e8904601400000e070030282c400c0e02c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 239369883 1250 239368633 239368693
    0x12090c01120902120a080301080f07180f0f0c1101180b010302010c080f121806070503060120060406061a04030b06010c081b0f011a060702012105010b1308 68
    0x2e94034500225182200e4404203e909202c2e40c0c1c002418040303004040c5050f92121020780300410b54a6260a81d034400c036001c2c0203280302d5001c4078500c0540c01a80410000000841d0111707038120301140f01e038101c0b011400d104020441100081942840a214059450f8018400044402550346814244101c1408000e0600c132108602c40107106225050f00c1305a110040025580d440740e008100d11480d090b100d03044008407003040740c89041b60102d05944542c07520303a601420b55941000440e1444044c110048542618003007001d00032009000d420f01c40d0703018401c00302d01c0b140342c5a035000c44d2400d01c2c20480114078041c041400005c4440a080da00070000346040e412408041c10310840610900c1400045c603401401d00481c40341b40410088450a0800002c00c0071341840b50381184010003100070f180d4024410040d200041d03000b0380840b01440c3c11501c0c10500001d00210107000c80d442a00720f48074000d0b01080b110b54501003051100040c01c0d06001400b84000307000301c00c8200049408a00700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 239371133 1250 239369883 239369891
    0x4030f080901020a150603020108060102010c270503010f0501060206100303051c0e0f010606260609040606030b15040c051207030f020f16120f090b070c12060212090c0112 75
    0x1c81a0b208005500d0000e030814194038011410000308030080066200880c0498a00d10003d40c0c81d60040c455100a0b42d4035803200081e841182d280410021083c480c400c0740300514010204098400b441040090300840d040000d9a504040c006440c0c408001e00c1000c0d0740c40e40742c50900020ba401026101d500036454049001c3e080c0304030414028241a00001546201c0c14030f8540e01c0f10303815001642114901d4071140300404000e205080404a10600c4125006ca00e401080e030300d0814034140782d8090300403400003481d15203d036100a00300a00303840381d86240440840e0361503185801c0c4115002910030382403091070f0100030803580303120304401412402815030320403404400700107c1e01101e03109841080f0841c3c0e5181e0011030251620241e000070780d140200588404660307402141c3e6040c200481ea150b521f041458030f40e40c80f9099002660449143d0002c0c0740014040e4000c04c00b4106d0140f1540c4003580f1804000e031100003a00c80100201c8080d4041c0b1400300c8103076081000f50b8540040304034042 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 239372383 1250 239371133 239371147
    0x190c0e101d07091206140a05100b090d08030f10060507110d05010b131d12070f03020c030604080a0324180905070b130609050102031b190b07090602010204030f08 71
    0xf9881d0b282075440b00004c2c04081c4290020003d00340d010b1007406051007000d6200c2e8440c03150180858404642c0700c808402003a005101d1102070201804403440024203540b038800ca183d5860f038041c4c0060b82c0849a00f02940148010810415034620140c4600d1030042d0030140161500c1092000310818240100b903074112a0f010300400707401c50800d03510003428030054201410305090007001800c07a211601c1003842540c00c0100c0e0007150400040e80c0c0d4001003820030b021500c0b001c4002c50000000c03401d51040741e4400e01c0544090081c14421801150403985030340302c80e040613050781d8201c17200001c40b10170603040d20468802800c81805031041c1d8648820000c8061060300c008104c106000740c068450070340001240c1a134100140560580800182d643c16601c010948840020380034550161b0801c1c015098400410505100d0041e004421182c2c6203000b0b44c0310644d42c480796081074035089071140c104075040f5004191b0000a1075640700851605145841d444210070441000074241a8001165 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 239373633 1250 239372383 239372387
    0x301120809031e0c030304050a030201081e040302060105090c03163b0f15090f0a090e011b020f19030504170f0d1d12190c0e101d07 58
    0xc0c4406030720180c101d41c0d038195149401c03000380540b1984908248510481c00440e800d012083e40d0807500050b00c1c0c00c8189066500542e60454000c4c6a41803002d0071010000f0200d0300a41d22601660094010304005d5051006101240d0350007003451a0311081042441072100c24080c4e00d80181e101da141115000101c00c1002c000580361107003c40c41c2046544122444003040c803284249a5001c0718250784c035034000001c0c06400141401107540b903607001c0c007202400741024084550420700c02480380c60724079101d6652600315401081c1d0f1401c01d0390350b2041300f1b014200d42c10781e04691004038001410801c0c1c4442049658141c1014401c1c043c03c034030802c6104040c060800d4501620803240b00d8450343c030503140b007140e031500c0e00340b18060b00744965610400314070302416003159034505601c0702401c0c007800c48040c4902085c40001c0350f0348900c90f0704040d041240e0300070040d10000e4480c84a0244042c07400720001030105000d00414181a500e5004015144400c003407001c80d458292950140c0d41d50302401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 239374883 1250 239373633 239373637
    0xf08040302010e0a181a031614031c0309170715060e090d0c0804030210050a1202030f01060e150d060311120c010f02011401090c2d030905070b1308120f03011208 71
    0x1c0250144103405001c41207900c2255188c0c1a1001504a0040d030145442010b80e583c000600030010003642d4a110102070303220307801c9a03031000d00403036080c103032400c20f507440300100c4d408400280d6940b4201202038803071204a0003004010550501e0010040c01c1c00b0a00c5901d0b101580e940301c0500050004160800c110901940c005640081c503c1301e034030684501c0a851640f00781d03494400600c194003016410300c110b1003964042c803d00e0340007140c0f584c01c000003a1915000f540e0030b036034465405000e6004a030000001001e00050503a008501189180b60442c2003d0701101d28511404a070000407a0361400010000e44007582468006090381000324141c2c01080500b81e104044000c510020500781c82d1a0000c5800f44a90f646261403042c5111505080c0c032460b000311203045000302c03d520116031280c0c101a41484c000d600351403e481e614413400c406580303c5041c607005ca070340d4403c0070814240240071510b000580d000303020789407250080440c0070341d100500545100803698405a4180010501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 239376133 1250 239374883 239374931
    0x140406053703060204080d020a0b060108090a0b0106030b0102072102040b0d050604081207030e0a0605070504090204180c020d171b180906010f020601030b0a02070f08040302010e0a18 80
    0x400788020340c072410150003030340c414001c0701e60910814144240301e41c4002002840d141e04210700f29a60b8a07010011680004090540302e103510aa40d001000300d00324030100d074000c1050341c50001d81c1500502c0007909104031a031100c10b20030011040702c104001c2c0c01c03910340400f03581214005040c180c1040094100b801201016216205020070002000f0081c1c0081c0000ca4103a054070b0101d0b40c802c20308400380d03211010125203035001404404000f0382c15801540d04101581081801d01d0b0f1a2004030f000c0741c116a10401040504400c0000c2c030302440d1181130000c1a151024094044081e0b00c00380c1f03440408a501c1d00e0501c045d40004040000540700c041004002c004113940d101c001c00107101c04440c5c0001582e1040c5140c4000c40c8096009a844144807882c03900540003a80ca1a201d14686840042001a01a4080000d00002514240880c0d03003588101c24041d101ca0440c0001400c00d501105500d009046020007031294042403080444810503000340800d00c80d040804141c0d151940d82 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 239377383 1250 239376133 239376229
    0xf0406090c060207210302030901030e07120b0a0f1b050a090b040905060a05010e0d060e0a0b10061403011a09010311040f080f0d050a1d03070f14040605 67
    0x180c00440c00b0b541c0800d082c0212068034100c04c0c0c0075450b01e001c40000c5944400014050b91040044c80c1c3d07554040d070080d024a110301d0b41a14015507840d0100c020407802500121240491038040003a074810a100c4c0002100c2850070411800981d603280c1c105826030494843d040c0180421100c0c5c01d24410404c21020300340148069032129a1548801d02400041e114280f003a02c81910114065100d6000207415440c000c0a00c22180081d4807400b0060800450003152805500c0442003c1060301c05002d0081a85000e08034640740b40085c018182e6107100070498840100b00010004040071442d00001d004412410540e10070910005030020302c0c086ca0784030007001d804600000c0d485e011202c413404640c030314030590310000300c804000c94036101e07981e1b06000810010b0221024151040000c0000b41c214980c2c850507101503080000c0c94080c00b0f62040880b584502020700204156040511000728160b030f00303000f03050402c000100991605110400c40c8003004280031a420342010300480805042 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 239378633 1250 239377383 239377403
    0x901020903210f18041a0337050303180a02060702060f090301061e0801141b12090a1e0308042004090c050a050901030f02040203040f02060307090311060406080f040609 74
    0x4c1000c4c61543c22208114520480c40c1c80340c032688403085040c4141311110000d001d4441d588903c50002c18042d500140c0e5030303400039120036202e44d0480880b2809507040c0a0001142c480c40d18a441d9030350a401150b011400d03400820183e4016100ca1003911450b90341228202e846181802480c0854003c07140b41552540c203141d8002031000968044000e815401901505915258060345081c1c4500c400d205d8600d4003c0000210369001c40517a034207014201c5280ca500d00394203034001d91308141080c1c40103410368016480040c2041541e14210307110600d00c812070300d031010217610301a020420052001d0443c056034a480b010042036103265246040d8010710400003a1142d090041c510100da00887d40201b81014010840d49054040d19040313030307030000d22200310810390782c2440080d401c003030f104882c6401c524032442e00580d14080038501c0b813a842c6da40d07a04442d01e942401b500122a852000d40115010402486102d5115002683c80a00f5101075415a00e0320325142c07000b4200d1080c06804240b030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 239379883 1250 239378633 239378647
    0xc0303040611070f080307050c01050f0103031202040f05040b0d020904060b03060604060e07080901060f0e0f07110304031209121a181902030a050106062012120709170c0301050901020903210f 84
    0x50102c2c034ce03051303a01030781c2c0304a40c0001c0000740d10224403a9025000400352222010803580c41c054006401101e03000d41352012102140c3e01140281c80180c4003298580e4403500c411101d4282000000d521070340850b0b082c003100c3d240c50b4105018860140401c802c10003a100010307402002500161b00030589140c190500c0b95880c90b4440c028001601c001c009100148082400c02d032207181c1000e45504141c002e1480d0a1941c1d8841b89035112040c206818064000d10008400c01031900b4070a265004541c041890b0310014901852030100808402d80040191952518160300107511403200c200c0d654509004115030000901e00094000014100e40c00c219000c00d0043e40000144801c020700004070001d405414001e82d09d5680008100c01c01070020322914841000040d40c50b60007a1441c00c2440d1a5500c138010340e010928200384001d0598045510001182001d10817a03a00c240494000c40c03c01580c400002d07210808a020100c030302e002c0c201c250031000512005c680400b8407100030300340d031a0a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 239381133 1250 239379883 239379901
    0x1b02091303090905010e070f030b1e0f101b020303160804081903050a0e2106100f1401050306011e020106050934030b060c0303040611070f080307050c0105 68
    0x3044010440000c0d40c8440000341d9251640180e5058a6241b105d800c00c96440b40c508440e41201c0219020405888060490650700c4021038449541c0f0720300d601071504190380041c015102d030003040030740c041e8001d50b02100d4016400050f07406008040e0301c07120600011800000e1540c0141c09050112103c0801d0300020011241c004200300c0d54200c090310000d010140c205404c400510b00058082a010400d411800d481012001302c041001859442e41280783d1510384e0901d0341a01f84070045901202c144680c8440804420340104005200002071508008100d070396000480789070f9040c488080b0200d00d85030300172458a04001c08016000c06029000ea00c020b019011921604d8000c2d000c440200f031a2111458081818180b0f4130449002c41485000488030408040b940504240d43c5044508a0703039074440c014100c0709041c000841d10390509052042c2182c0380c101c0da80d8804001040707a000040d2400c90802d8049030400d02c42d54403565440c0e400d0b40c1c24402c800f2802802d510388010041e45803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 239382383 1250 239381133 239381161
    0x20f0706050a2c1008071205063f0a15051012110907141603021029060403150917030a020d050603010204140d0f081c0b090402090103031b0209 63
    0x15408807684c000140140d801034502c01d80555102e0000740740000704030024484c941104d504900087e00f100020110400c503601c0c40d265015520b100015009800c5202038299140b8265003514a03000c0c0c03a030382c0300c645e5031468003200780c403100c038402a01c0d080011921000240c1c0c500050400d6624644101c00914201080c44107110b402031080034580702041c80039101c0c0f4209030802c03034030f114003510b0a002c2c0e010401034014000310032030841c41604188800f1016501034140c0c0c0c01c41c4c882154601129018140b850001c0d441c9806008540511041011600841c01c421010010100016080c1c2150a011284211504080c002c03143c0000502040c811300d580104443e803408441002903441f007000b00340c00d070704c81c52085e019104040c0292143e28986005030a15545c41000691818181a40d440781150420300c0480848410414041810345280c001c25910400440742d102e09450258001940c41e181030002a08000042c0c075001000d44002e048040000c1d0010020b410034903007605005491 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 239383633 1250 239382383 239382467
    0x90c03030c03040801050c04030f0f0f06110406110d020312130c03030e01020d031a010f21060e090706080703051f0806150d02150906130807060807020f0706050a 71
    0x340d1b280000180b20720283c60190b609036940502c5044210440e6101d00303084554015007940c2440640e40e091002501c2442560741c400c0c0020055a103c0d80303001c0010b081405850b1003d0180c7c0c0150b00c002e0921a8080b003214101a000c820680e81384c0c0762094440050903070258010104207010902005042d0041d41c2c084040c8070036400c45164101043c003c40554001c8c19080c500742d0f83c1d20020741060b40c0110340e040c450141d0f0307140101032410340c41f044070301d0245410a0b902002e96103460606c60820207000995200c0204401401e141c0d16181d8010301402000f481c007002c02d582c5001089964400305400c03640d54500c102c20f0030341207807500c4085d0385646003034907688024012f001202120b42042680c0080320780e0020241010360b80300042003d000e5106556483d808441003041000d1044411140c90180a014004001c500d04040014094034805001441075500c152003505003042c0004819042d03440c1c2d4a003064a46a0549082e6143d220358090074418020090100c50031440c460685152 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 239384883 1250 239383633 239383649
    0x1e092a0905070c021e0d02090411010806091608071b0302060a1802180a09020a030312140105030c0f0324160e01080408070203120f0c010b0415030209090c03030c0304 73
    0x756190400b05641050031004002d400041d84480c80401c0020880150f40c1030034050a0050b81300c1c0698001040054110350460360350703010791030824040d644400b00a602c010244c07a11f85443c140000030602c1c84202c10455010012150300180c070700c610901354607010b9100041e43d5030100310b01d4a0082d460382000c032039031070301180ba002c0c0c0040000d02c6090203001094006e842c2119000c1e00c2c04000c1040c0c0c40060092a40b142c48500d041e0050301c030311400000071806179407442c003c00c0419a070002595980c006a001c10250701d00184150b9401103050800c00008079442833200901101203070074560031450710300e039000b02c0b0343d1902110310b00380440600c103010701502e034540d036858100190340040c1c04840860000b030784200085d000070001d000900e06079000504680f5903514a8489603140c0e4007110407000c00b2000442c400b801c42c90240510003596400b12070a00c903a4000d60140d00d40102c185c0300181c030030b06c0c1400100c0c80404060051741c0000780d001e0140e84d6a0700601805503540e03071083c410088 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 239386133 1250 239384883 239384891
    0x6020c0303060306150a06050c1c020607030b01180b0a0e03010507020c01020c100f05030408040e010f14041b030b01050c15060a09020301350d110f011e092a09 70
    0x220269110303040e00d03070001d042500e0a0304042c070803510341e000004210118420710030202c42c403401d100c200c2c07614010f481c0d004080394034020dc0010150b55134030481d00d061200018801413500301d0030340c1d0401501c0c0c034002c059371941d21541d0300310340d040c0f0400002e0350103501e84818058810340c0840c500d2000d0308281c0031100c200320360700d00f44205442404c0b4608001040c028101d0a07403031080000710340150184041500340782d02c0d82059561203d0a07400840f44c4c65110f54100a20030f81032404905042080b903081013100c1d039074040e413110b04200c111840105070f07a80312002c0143e030080301540d4034110114121805e245464500750450701d0180c1c3c2c4c0d14030680300ca010004030141d650003141d060b00c00c56070002e00324045134814001015842c25049030f00503240c10b245010300c2c104010407644082c2c940d403241c00c180684450903041808011003c0707820f905010182c044a45420311904d502020700c440000c500f091410b161001030784281004035406005589450480c6060b0f200e8001d403266840100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 239387383 1250 239386133 239386141
    0x9030a030b0303030f0f0907080d0e0103051609030b06191712130b071502030a0b010e0402070b04082b09021e01020a0b1b041206060b070b04080d060306020c0303060306 74
    0x2d43d80b4081180c0304160b056803000080e09803891030007080d4119005100301c0d01c545807210400d0b82014105034841000642c0070320400f0440d0307818094550050018a6210380c0f4000c2c0d146d005211600c08d0001800e034840000c081443c541f28000110141791145140c080403d465015680040302c0007240c0108d14800c0d5030004882400701411a04803c241c0020183d00e02d1411850b44903942000c0020380c0d0b0000284c11415444c10140000e500c60540100c000520868075000508241c5180311154081e52050100710300290302d4620f584d401c01c0d044100c00d62165030f80b40003210014041026200d03444a40c1035aa891515150043c1315168800c0322016a01c070042140d441242242c451800e005901551411011844210b40355800002c40e80700b00c01c84008030070f441440f0f5402503106507000c40408003940240700c0944101000b60416000013071511040c1d440700c1a15050140000c1c00144001402c120303c114a98030840086900c1007003503449040010180d03490703800841d4030a0190180c0c500103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 239388489 1106 239387383 239387389
    0xb04110904030305040c1a0d020904060314100506030d090303200d1205010b131a0c0d09080c22020c010e061303021504030c03030e1509030a030b 64
    0x800d075030800d403034924006e030304540c0880c01521502c11422040181c0f00120b5070300054014001d80c0311000040003030014a540d41c40146220051540d090b0340020105084055540350441085580d44510506840d240742c0f008000000c0c000c2802030001a00a00c10b04080c003004402c00040c40f410b41007030501d4520130085003030100300c0444054807803808038042e0034050801c01c0f0b12503081440200713072001c01d84024042c504400c00703418a0b984c5030480c820250380205d0038003800c0303801e5a41c003030501610002044c01100c01c1402081a10b4a482c180000650725044082985c84900d07091351002c840250400304940b11750395200c4042d41d10a40040052500560700d0000d0b6400603401e915010b4544000803800740780d0a00001c00b0840803c1d041030710684d00303c1d010b01b80442d00c0a4a24189030074100500d01907281c0c82440c0c801d1140c00e940000142c6100303401c9440400402c2142010 = true := by decide +kernel

theorem cover : BRFrame.Cov 239208633 239388489 := by
  have h0 := BRFrame.cov_init 239208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 239208633 ≤ n) (h2 : n < 239388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
