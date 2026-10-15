-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5174
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:59:20.01498+00:00
-- url     : https://prove2.me/submissions/9beb1a21-16b9-4126-a8dd-1aa2c1c064d5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 930395683 ≤ n < 930575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 930396933 1250 930395683 930395689
    0x50a030506151c150b09030606060307080721110c1903140a0e0303040801050601110a05060408070f060c0906110f120c10020a0c061b20010e0a0503091c030905 70
    0x3412002801845903107000c4a10304004134591000a4002e03840c95581741d040f020101071030002c2c01008180122414410b000045400040381034014200382400b21907020074014603111030303100b0400c003402542000b101444d106006030040c040c0401003c103481901c0d200c415400660080711000400040340156100140d249840c003415219206262007003050184100103461f640060300241400c1c5d5544080c01155030700800e002c09280d400401901d002029515016146d440050010f801940005900400c01803100310b10041290301031410000200c0340302d00106400300e6070003203601245154242d84011200000c01518220501000340815921031900c50801d0b001840b14440910501d681011469143d00103031100c040c086c1e0392100400114100141a51041c2c894516800c10b40205628201d43c810546d1100c01005280c1c0350002140e116070b04e006100c02450386801e401005a81c00821101000411030500c08403070200d18001c00c102c880094001c0d80303500801003504400708102500f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 930398183 1250 930396933 930396967
    0xd05090307050d082d030402010309080f130f06030608070911070210020a0b0c04232815050f0d0e070e040b090d080c0901030e01060305030a050a03050615 68
    0x98060241d406199607000400e000b40668841100c04100c00304a26641c101c0160408030a0740c0d40c80025130941070001e00c076000511014102038100b50b10752206609100210013210040480350080c50740e1400028004008240b4600440e1000d0024450000e0484d100c0c0c02034409603200480078001461800b00020014828140ea200c5030080c02d120764405aa940e4800440007032044c0c020308070100140c40c100c41941c41c000c0404540003409d0005221907c11080f508056229280c1501415401c100029130910b807054109030107855412200c030f042406403e0380c6011201c1c5c10141800c0300c03401d02419512805081c051040580d024022848041c049800c84912050610b0039103c4454541c0c0302c501240c0c008441c140d4003841c00505008190b5002c0202c90900e00c101d20b0040110b0602c070003003440c07601c1402e1103581010344401e01c41c40b0555003984944001c1d84d00a040ba42c3e502c0404802030100d07040000c1800100f0302d0300c1c001882506182a0888084010b4051140780c561415010f103182 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 930399433 1250 930398183 930398197
    0xb1306110903032d1b0706020a17031f0603020904142e03082a060408040b0702180108010e061302032a120705040f02040b161505040b04031b0201020d05 67
    0xe02c6118656134401c4420700208107281c41c1d10550b460141d4030980491908810b030b4050000c5503c4440d190300070030180007507a8900c440158015980e41c0719069400075034544e103403400520a04082c4005421070309035005050702d00c001e50301030100e01405000a104008221403100303840790482c4180c10b01e40842100882c038030703000c010b602071100d4607500d1b4100c04e50044410b84411000030b40360700c80e00c0300c80901d4a2131354480700300040c43c1c54034281d600c00c0c600d4000c07427040030680003001c503e1008543d81c0880d044807205084030006195a582c2c2c04181c0a405888040842070080c4000309035a0f0142c2050201c1094010b80140a00c0304110201940383d1109010340c00c0700422084448900ea403a00c10a40d10854500020001142080304001c1100c00289000116900c1080100260184601a2100c40042d54a4000500c05a00342400036403140c180b0f10764680e2400d0b041000304084030401c1030250b4042d580b1180d0440e0046440745003000b10700d2010380540d002c8916075807640c0c420b00062410b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 930400683 1250 930399433 930399487
    0x100e09030c37030e040f0204080102070b0601110f0c0114120f010e01212a06050304050c01050408030712020c1002150601030213210b130611090303 65
    0x3410303500358501418405002c0d03219150240c2d900004032404a0000e50074000151800c401c81c0e0112656409400e80c04c5a4003031034041d0340c541d41c0d642c0004009070b055600401e10b203002907684918078940610800002c82341103000c81d01074a140d06860f50300155041e0802c550700c004007429030f1001e0040d6404042c0c44044038200b0010044a8186c1c14400c45441c00703400d00450f82c25042d4140038103520750781d10503008007400089501181228440c203021248047e03030081000781d1451000d41d9521031030140c110300305d034581c2c690394000a003c590107002148558005c1041d100a12410001110984034034401ca0080303900078004e420100307166482081e0301c1141030048134441620f84c1d000c07601c0004206140030160304000e203140486403d0311a88c5501402c2464114600840464210300d602035a02034807902030420480301ca0b00310103401c100a502504801e01140070300d00300020007051403800c4800c889032400c0480c0c8882c0303c4d40c407400380d49404030014095410000301c0092203682451404000700 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 930401933 1250 930400683 930400687
    0xa0201051e09060708120a021608030612070b041403030f04140f040c020109061404050319030e060c0702040b03070302130b0105090402030a0b210d141b1014100e0903 73
    0x141da41d500d000500300d191040045c152284040304900b1040d040090480e548140100300050202111407040c010455004014940343d450300310110704030318464840f02403c0e100d03101000c110030f420309020b081118052a0650090200401070540301d0003100206c0b0b519010a01c02400189540c40d100d450201d0080e101c03101011074440018140c460341031400c800750355220035203800d001c1d490044500001c1d618442d00ca4034141651041d0340c80c0724064048a503070381c4002002480364401e400c8200300450341c50071900d882c00d00402c645000d500c43c5000f01c0c402c0d4945082c40304203040100e2914201d9070000c08151915000c4a10700d0301901c4000203d0741005001c1002c0345a554561001c0c6010750b0907182c00180300c507104404e0000c10388002d290301c852a140d050803892880e02c000741000c12460903250000078040100c103074440a005500103000060303100720403440d0b03041000540d5040090001000c0c80b0350040c08000380c0725410300f500c1e001703a480100a000d200c2000748203449c41d005104002164 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 930403183 1250 930401933 930401947
    0x4140105032206050712060509040b060a0905071709061312050409050109020d06170a030320120a0c030c0512091e0a0c091e150f0b13080a0201051e 65
    0xd001884000200c0f19996601306200715203a104050100305401030380c0c2000b03000d080c400001c45007000100014110307071250001401945807134407982d000f0301992000303003c079042070900901034006104080409540d89030000c0c002c1c441c00281c1038020288280c25200c004407a4440c1e005003041e4000c2c0f0b0007030240400c0001184900741c483c1c1802042c1490b001030b21140d40040036026244a40d000f014214101da0018050500109510a03140c1d0305003000112039411850300f0703c8034010600803101070a00882c8403041e842114804e5403186450b80704c1000400c0381b13800250225040c030065840050750610400d040243c441c409103400102403000c0316141c104210100f0919603c8401005d010341201441c00300304040420440c010b841403000074005250100710800890101030002c0c1089a103c4012100c2d0030306d00c5000708054940800c1c403403442e689860098016500401a10310404001140004c0941002c50892185d642c1607654a00d0b0a51180b50034896128000a6002909040103a4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 930404433 1250 930403183 930403231
    0x2c010e07060908010f140a09050c090c0307020606101b1713030309140d2603090c030c0d0201050f0d0e01090f03031d030d240e010810020414010503 65
    0x800001d00036030782d5444030360f418060a40e003507440c2c8036a02c030401400d0604029001580c24040ca41c003441c6814006004201341c10000d152042000d0030a401ca414802030040e14842d5000862040401e50201e44482d19841c1c01d1029010090308002d0010380792030180040c044e41d03101981080c0e802400c9180044884110003a0039501142c0200000c09002d80200205500030140c00c00410160100c00d00c1580d140380491f100c8545000700602c021481440c41c56180c022030905440f010108607000e44911308804a01d9450300607a190f240b10784a04004044540390849083c40c0720b50307042c0d440c5410044861214a15130700000180c100a50b1115030f01c40780e8050910582400a0080c0c9500c819241541809001c1b2400d100103070310040038014076500210800400c03079030a0998007900081c00c000b900036062070f00d007000180c1d074480380c1d02413400600601c1207101c043c1a500c01006075180140d01500b0300d4100e00ca031340304840e005082d40c1404501580182c001d1030f07100700740d40d00e400118800d100715 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 930405683 1250 930404433 930404443
    0x504020913051303020708031201060c03020312010b1305040501030f080a17090706090b03090d0e03030f1308010b101e05070602130906121110090803040f03060f2c010e 74
    0x2a086150002c03030b000c1411741c100200700c000d19104024518007074101c829640d0307020050281c0d4041c0040b540403042014400c008440940e100c00d113640c91156150500c51445a12090b4124881e446044000c100752802c0e204a074100c0781e009030003415842d80d5540d0340115402100da00c04c04e10000842101081001f118540e10601491001d13041d100d090407030140080c1c859030404003d23a01c060007004224180010705400b164860f04200c80d200c6081c50020b49144109884038035500004600c035180e0b080414004c10a46080b00d0080c0101da040000b480400d220b51030301c01c400200c040c40220f0b04680d0300d070568642046180b0b0614a050440c0c1c039a0b40c143c6e80010200d8401301c10284c0c04000307040040c40f840001c0c020041d04840c080b041611854000704c10007101754400d500503003000c60800d000340500c02c020210041600d4a9907500c0a00d60152201844191801810b18160524106861154800c010441c6c000e4000a0b001801c02d84402e81c41c1d0510f81400c1e650f00c8111400588041103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 930406933 1250 930405683 930405691
    0x13050309090c0903011515321b01091502031e13050601060908030f0f2109060109020421060b030616140f121003021003090311070e01050402091305 65
    0x7100c2552221003c00707140c00c42d801c0442c49414003034210b6050102c01c1600310201c582d00e58500e008450f009064000d5112900e07200340428050324070005a00f030b80a400c40280550309502c040b4880c4254141c1d601c01d003030b5816020002c1858484c00003102c0c51286036400b4541000c402034501c840c0c1c030198506444101c0040c3e900121000b207100c908420003000300710032405044a450007032460b0b860f094000b40e4a000d5119004240305000c214829800000c400303440d03141d400c42807410101c000071110201900c030140c0e003501c00b0b0302130600046a191a01c0c003c4500304c900304c22029510700d0440d41902080505003c08550f03054986407004510758003006180e000e61901c528014015004010240024402e01003641c0c2614050002800408580d426070704242207080f003899113a690003207800a682c019400003540402414002d030b54055040c0e10402d40203112351141c4401d002d0001a040c0d80f50100e10a0107c92146000140543e040070307000b5081942024111801620303401c00340a00361b40f0304603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 930408183 1250 930406933 930406951
    0xf0d09060f0f0e0d020325020612090f030a02070306022d21090309120f0604030f110a110609060702120c0f0a150813120f0201060515031305030909 65
    0x32440b16508100e1059146940a44000384036030625a140a51207028000c03500110716080006600c4003851407010601c07013a03009120030303591080002c1031040c2407000d4910610b2131240c01010401050000200d0346c0740111600104006440c40c3d5628029611402009040680010a0a1288a00e03010455a99282071007458032201c0c4280d08580c541407202c08201c22503c01e41c20300075800000702c100c8030075030425900c01c0484880c0c14040d514204e9900049401440b80504010905501609200d004042540c4040200c2c0d0382c0e8981c00e90764080381801801d4000121183c6640e4030b091401045000d00c090700081c00c00c0c1051300001c1f00005459281c0380720b50480307034041d402890241500c00342c41d5000c0f103072121072034102001070840f414444840c405104400300481d01c0c10660140703205210358852400d0340d40740c0589400502c1c45203c0c16407900590308100003c00d45182070226008240740785003c0341d05542d00c170b10b184410142c05480c10f44003030200b00002242c0351940d00c1c4d998800d00ca94 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 930409433 1250 930408183 930408191
    0x82109070509190905010b090a02180607110d1209241101060918050c0a15030b010203070b09150a06150c0c15170a05060f3705090901110f0d09060f 65
    0x801c140808d440004002c140b0741441003140d50319007007500c3c0c01300c00c15010079109651201780c40d2802e9850620b20b40c5c2d10951050321264034000700440400013030601c0320103941b050f040a40d2100c4040c00ea400e40c140c0084c3c41502028514001e520070b4900400c00d40e03d61002003038090356503001ea030403101e40b07580b001c42030f88190780d44009028040003e0b6101e082d050383d590f403900e072914000c4042d00081400d60400c15441f2007010340168030030021340b000d42d50065045081410039040301c1c0c1d034952481c00600c0c0c2c5290444c000030f2032180203200c4d80c07044a070031004500034411844021520601c400e2000c4600e070400c1d000105083c1800717400c88070a40fa060300d07071065003020351840b8050f8800c018058034410b800c3c07000304006905d400c0c903041c2842c481a10032401002151201900c99225941c48210744104a079401404012031454181207402c2034403240903640360003105a003030307920036442e00d80701d03900405c1085000d0840c0c034014004000c40610005071400c0a69a035801e9400c1034801c07200060316 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 930410683 1250 930409433 930409451
    0x702010207171005090303040c120c09050a02040e070e0907030b130608010204061b02030c0f04020c062d0f18030f0f090f010f0207060e03070305010908210907050919090501 76
    0x15100351307034000c96004c00560031464656103640030141d10713003d816a003c00c010750032010810005102005403c03800024416407030300156100c003d411a10524004007044004a2007290148005500a00d0064100301a0350346168050700502189141150440c9960341c44031035030107691090030041c180c03070800581e0b903516205e0018254a00710f224001c1c083d00d0001c3d1480160340c0000c0f50061448146c64880e085880707040003030024050811984001c0c0645010420302440d0600088141d403400403400060380ea268240c080c2106c0e00702c0d0310000c019004801308441c05000340455072050442c0313003200d141c8440096540038641080e60144d068400128420107189441107007513110700b10030f05c0c102203d6151034000070750b6030074a0721076042400070804030012903860600589014640100092009803402e1038002c00307591059050b144c80b00000540c00048451000345140190b0400e0010540c0601703143c108030500c180584a4952450b001004181c881103034003a070014207000d003000042e10b8103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 930411933 1250 930410683 930410713
    0x60408090f01050c07031203060305030c0a0203070f050a03142a03211801020319090906080115090f021303030e1e03100209030a050703150f0b010806010302070201020717 75
    0x1c00901040e05210060011001e000390009040088a030044000290700b0308a1100394020034440d00050142c1c0800039814050178070000394401071603c01e50490706040d81d101520300c9103c88600901d54003003407480082000c20841d401014028600005840d0102503500003054003c0c8284012810220200b00741c0000e072a0601007440358403035402035102d042c58202d44a40f120b2145001e01c1908494510401d02d10340d2080042e1101070310503c0040548042d16038001c0d1501d407a0b442824180d9080c41f00210341c0c0b20703043c00b54902103d0750001041c501810110300d03c0140c40c091a071600303e01d0f402d000f0244203180590344030300110302a441d03220f080f142c04011300095001a01e04007541d0070400c030403000c003a100015011b0489180e00d20058680c2d500340c0010307080a10020000c0d00510801c5000300c1481180c0d0901051100c08000411865034a203c44400341d421601c6a103020509102c000350381035000e07400404490340b05106a58034a43caa07482d0311442c2c048001030302c1c1998804000d203800e0070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 930413183 1250 930411933 930411949
    0x3270f0603230106080403120c0201020c0f010b01080f0430030c090602071809050d091d0402031b030a0218062706060f0c060a09030e01050901120c0e0306040809 71
    0x22010036102c200503010004800341018884c44c1d04002012002500f810b00c5921203c2c0da80520410600803c0b9800303500034082e405c5051001c0840c0200d000c5441403101c140300303e200841040c2c45020290b91810305011089c800100305585040c030034840c20503406400b800031041c40c0300c3d0442403014421405801011100200b050340140302488900740320250300082d25000302c604400080803455002c4800740040d0004550062a620038841740b03103413023508103c5400a4400c09a2103c8501c070301c041820804010598000e5095041070104c1d1007190007041810541801c00340c1250b22051259010032011103111481d5602c10007402d00780602890008007854889850011034007040350440b5200140300d0f405859148500800204000744600481c143c2ea503103400c100569006260085600018060480e01240004d201d07882460f80c640c00ba201390307040c2070740607035402d50030b8030400c00a58010700561200000f4440f0040e001c400c141e900f001340901c2984210103258507012070b0303030a10241c0303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 930414433 1250 930413183 930413201
    0xf1306180b0313081e07120f051c09020109080d17061503060d020d0c060c02010f03110d0b060c010204090204080601050301061503051f1d010e09030703270f0603 71
    0x3980030001c0c04401c4a115070904401d40d00610050742c0e4030380c015071804025100c41103d480d03000000c101c08050000c0010380011f89003880c2c031140d1401141343e108507030318813405200400002c24102d4103c01d0140a611003102148181007035031b40706481790201d925280205210300300003084c404e0355001600200702840e41280003a05e10b030300b0403c107410040c2c845020080c20240200c4141503280290742e00c050012200c40c2c0c00c0901181000e464800003080006e4201080e0701041056845040091080c070600c4a64a41560f07424205039030029040042c0001500256004c4418017503004460401e200900c000c115803003006035503d21b0860460304001059014900c203901d4000c08024001044020804c0c0885c0351030300003180e40d00e0b56006156000d528940030015040544c001c01c0000074a403842ca1800d00f40c4140706541c0c1e0b44c2c4d040e14104040111032076a455001840944000b070b01030281a50141c0099035110007003400810b05031440540c9500c2410f2214070484100b0040d90548141d5000b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 930415683 1250 930414433 930414449
    0xc020307030822061404060819140a1404020d0803040609151e021306080a090f0b040228090e030408030f0703141602150903010504030f09290f130618 66
    0x1803801d4041c45e071940a0351046d0014803004100083c8150420148035040c090748003020490048002c03800e08961a0072200e0028030392801401100c00d0305070f0321060f0f12582d40240041082c0126503141c046982024000316901901c8428103400103110202880544050700c40000c1d0755046401003080b0b2160440b141181070348104090a08144507031080000e4690354201809940c903a1000d000c003c041d031141c003904501d0034542c003400700030204d0101402203008441d10391101403114200c9600c5410030401e070303215484100d02000f0500460b08805c002c2102d207000d5030304040d80e40c0c1c0198251383c0400c0038100445c0c400503644d010507400036100300c0404400702c0610b00b4480c0c00809501c06400b40c0ea4040d10456070109e4116881c0207460403a60b07021000ba00130b10035401c0611700540808540d044050202d804843c0c0404c040301c42c9503141c13003001c0c00441569407840f8404441446940b00c2c041d5140037500070803680b640001c3e4011a10014401a5a184100c2040564111440440c3d800000c1c6c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 930416933 1250 930415683 930415697
    0x605070815121b01091d0106032307180302030f0c120d0203180604150905030f0a0503030c0705010b0a0807140d050a020915040608030d060608090a030c02030703082206 74
    0x200540c00080d21a030f10ba100040003020044103200142c03020f2200741c0c808031080380d0984082e86208001750030141200d51a850502800c00005c1d002d1082e03071242000501059100c1c80018807003480786561601980100c0000000c5a8494010a08007102440180071036841000c0d400c0150400a0500c28110f8000380540001d10302901c000303460307100c1c200e009110b0313038a00c031403000003a5109012078008248140c04001c180e030202170054100100b40c42030b18407a009403402320080c2503011640e08003840e44180a03500d15030b6421030740700e0f103500803900c140d40320365940c1c0c18442e0584038064040c000d0203e0100a1030194541100d0f00c440310b00d90540ba50051400c2c442041c0060b600203411824a54100c6040d0080c0d0345d003980712116800460714542c1c0c002d04002c000251903034044000c0c21284040001404800c0d02d80360290760b4280240c0f1804030a922000251001c01d01c2070084a40c0c481c80103090f201c00310364035181c00c54a80c00420705d1103c890600c003402c0c001e007002e902048000300540d0600c10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 930418183 1250 930416933 930416959
    0x5040f1415012003120f06040e1b190b04030b09160f060305190c050403110d030c140a0602030f0a050601141e070807060605130b100f03090605070815 66
    0x2040c032807a20740007000c48008500f1240a8060900540b44d1a8001481d00407081c43c10820500c3c1850b8280c50a078021031502c1c941c03040ca00800303e1240fa042d070701d07807070b0101891300110140201e001d0100c007012584658410b01081c0210214010401140940030342d040314200141c5540c1400020120300703d403140883ca0820000102260b205c089521070705001503665104088480c2a250803064824141d28101c1510002c50b0020050810b80b4000c80f011007641010005200008160340006404141036400c05000503403001c0713080141c001d881003600c080342210740d64841030340c0081e602040e0803039040041105c000118803070760b51301c07420034a8010320300004001000030510031041e0b038400100c00890617001040e494011104c5041e8001c074070f1a518145424240c00801a40c001d81c0e125040e4000360b48030f811158041e01c140104010035001446082c0501601c04c18807460b581010305807500900404a28580705c0e01d480740c40d26846640841c54820703a041c000300348000c1d00610581c3c40c01400e0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 930419433 1250 930418183 930418187
    0xb04081201151d010c1202030301231c050f030d0519052e0e0c0d0e030408120904230612010e1908040e04030e041107121805040f141501 60
    0x40c4452900c0c00903200d1403144840102c45c41c91103074501030712500d40300c200d043e4110341c000300450403101c01440000c61205a01201a4001221000150f101c0d07001c05500101050340302e80502c00603c10821513680c0061349240904540241005440c41d0790b480081114007501c425100c2c8160ba00b51104015a1600e15040b140b25420824001c40c2c00001d488003068100340c00c98148040c0690340410809454140910b13900750344003682c440021800e01802240030200042a10140c52028000d48070f40303010117112a4040e0040700750103500c1905d0342c0c150780c40c14120742c2240e9100800500e11a02900c3d2441c140000e00d01c107089404000c2c1e2511940f9142c00c500881c00682042c84c0d40035003c000c4001e030511321168000e6411580030800c1038001d0004240c0c00442401030318500b0b403014010307905078007032440c42d034000c0d80c801926141c8104484488130340318401170010a511010001031a0752a4004079040304c2082821100c900c0d640e16003c0c40710901101d10780c0d07101005810001e80348101c0341c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 930420683 1250 930419433 930419447
    0x512130312141504060b040305010e07050405010612020309010b060d0c02060f0106052505030c030c06010608040c0e0709090e011a0604051c060e060709050913120e06070b0408120115 80
    0x600d0110076400c965940c80c2e84c0d07600140014200214007a84071512400c0190080200741002c0103503204d2160b00045a04290103032034101c91580d2034004424505407a42e070061760005040c54070955036840c00d030245a4402028001c80d031042d0600007810b4440721070103032030280302500c045414103031140100a803da01000300c035001141000b5100d42e0301e03042c045130101c08030402c00042480c00003003410410b40d84000302030104900c0d850200c1c4d03030381e07641c5082c15203a0440a40b00a442580426414442c20790b0b9082565044040f528000c40e4450392034a01078111070b9200c07450403443c0d458000c20b49841c1507508480c0c000c0c8200315221441c044ca070100092082c50203030b082d01e0070f030a542d40050090001580c8601010300030001039407014500b0280091100400c0d0044a124298070b40100d0322036803203c000601d40303590040d400340387c110500310140c94103404e07510990f0b400700c020041a0002a07a098029025620502526850311021b03624048417401c140c100240740382e140c20402080640c0310315 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 930421933 1250 930420683 930420691
    0x10c0311180111011d0d0806010f0e1f020304090609020f120c070c03050c1201020c1e030c0a05010605030f150105011b0209151e0f0f01051213031214 66
    0x1c01e56604414100041e555040c0080941e1919460034521600c0003282c034a4000c210300010095645000c010002500c0e191000c4d14003e000418841140c0d01c42400386a0141e20010000c10090365240c0c407400300585401c0d0340a401005802c0810200701e03001c080e001d40ca000e00404c1000b07600b4012000d80e2147c1c0341c013a107104400d040000c1000303d40d141180030102d0300741030b4101041240745030b101d0901c82d82d60b6146c070241500920101400284061061003a101c0300c0d410240640200e5981c4014100306501c52045901c2c036000810540c600d545003080800d81c1c1ca4130610022030700e00e25100070141002c0451441e42d1060304150440343c00408078a1445064640908101801c61541a41c680d542c1111200c020b4100103950140800901c0c141a45020034104545000320281103406402440700d5801c00140c2045260b0813103221403510320359040c100c0606241c080c0c02c24401c203190704114003007a60404e0b805010841d0322028180d010004654860200704144001d401c00089a1341070a0014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 930423183 1250 930421933 930421957
    0x1020a060213080a0c030312050103030c060b0102030f0c0a0b1803041e05061206040b04020c0d050f0705061305070602060c0301150324061d010e0d032303060102010c0311 75
    0x10341d8800021502c520500903001d01e01c112102039600b8038200c0c030f50741c0641c007003500840c03006501802801c00704d001c0c0505070380c1e2683c0c41c090f1118456440402900507a850b0074154003090012203480c02d108400742203820494001022170640600b803203074500c10050000b50034a4280020701640705000001c840171034120785407504960440f0107080b81c0c000c095401c920ba0101000403016140003403040220b000f02d80442d000c01c00560910100000c13446003150500305600100d0083d82d41c0d41c01f80d0b020b824100c1c6070200d41403508405d17942d51030030540d04458015040c2c004000301c0040c45405c0207c400604500c0c0001c0c00d0700d06202b0a040800e00052003600d210881008024813442d11a400040c141140c16000c210082e170340802a8030198554010500040c816241030320b9048407840d0321402d100010384a003040d104e04c21041c003102c2301308020f00350140044161522410003000c20b400124070540b105090f22420311100090035101908100001c01d0305110b0081c8413940224100c03002d00d032041c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 930424433 1250 930423183 930423187
    0x1e09100513080307030f020c0a031509020303041820070f060c05070b0412181203230a210902010206162a02030d09060207050910030609140606010e01020a0602 70
    0x401040381d1911203800c00d010601000c940441059040010300400389031540a4901c40c2c4030030340038040360700000e220207041c00c05503071202d0340d840416500800c50140003809a03440e164a880045070040001058a1240d50396000d80841c050741074100c803000030202c010401d14200d441d0f11100e01000070044060450703a40c50881401207401038003200c414541c008441401e902d81030416102c4c0102001900001c100c0b42803954810448889015040d500344054401b882c07a4151411102c40c00c04c00f00c2e100240702052002d000d50b820690142c4910107050703a42d2070000240100c502c0d10f900c0e0705212200a40c0c20014004010b0381c0200301c7d550300042d5084845038119042c1002c89503042d0000c1d8480e105a810b40c1ea200c4032a11594008050314000c2d011240c0d10121800200ca0440c5188600310050300803582c140851300e071069030350b5001075017004150301c215160b4680204aa50601c030845010410444242e0303a40024009158420401d0030a4803500042100203919017048c00d100070145640 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 930425683 1250 930424433 930424447
    0xc080405060913050403030c091208181504092c100c020c0a0806150303120a0903020715021e1207021203120910050a0c271a1e091005 59
    0x2d0f03c42104100070032840203100c2c2e4141418050000c14201c048080002c070541030103d0074508480391807052a03401003405281004108890760040300901c03800368010458142000c50740341d810041c0c4080c040c6e4130b50006031000a4000c5000c461402600e4030800c040a032066003204801041610005030100310104400c640d5040c22070a1203516009a0b900994181011450701c01c000b501612800c1c001c42c00b03419140c640380400d5642d009140030325404480d4071000a00204040d00030741f0100b40309004440d07149403501c40c00080030040c4040c16006901206111401603a16041400c8109854020700929000c00c0c0d00242039102c3d43e00c01034084d146103408011300c403008004550505040d41030090081c104020811b0302d801005a60030b000900b03103400f2030260601841403055036605070321510503102500322030308203842203942c811000d41c04030308000581100307000901d401e104010604942d207619001582c01c294a0b1a2042c0349030301414820303d0f80790340380c403040440841ca403403c000e030311010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 930426933 1250 930425683 930425689
    0x406051e0c030d0e01090b04172b0f0c090b07030e04020d050123010905010c0201052208010608011a09060d1e020108010603140a110906041e05010c0804050609 70
    0x806440a6034015000074601e00040c90200107003402c0d404402007404040c0300c641c03001e8261000e404024180f0076030780c8049000138501300d20b02144842000c05440c10981c400815084644d40c003030040c86480b08100400e0300e041d820380310759414080080000c210b030485110005010700740b14050b524054030009280700c103140c00390744401d07034420000340255038070f41c1c0b62100d0310040c120070311544e070002d556201291540410203810a0802d0b5042c0c0d113400003217240c040110307012042c407a030907030601c141008612020340c1c81c04c4010042902220a51151a19200351740e03007160500e5220400c240d1428030b000000134151404141c03885800c503103190464540340002115543c0070310004100c80c50100c4107580994a440c55050014000d0f2124212a80d072800181c00303440414074806086ca00302400100c3d408a80d0f0b0000540c5007100d0751241c10002c60001141c000d034000d4000d40025810307154011a032041801001c07000e0728003840c100ca5009a25521100c9500890091520030340d004543c02c00300e03032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 930428183 1250 930426933 930426967
    0x1180e130206070807050705010903150b0d081303050d030e03191103030406061a0712200706021005340201180b0613180b060a0b031015020c06040605 66
    0x198005102c00d950781260b01c2c00b40121360020004803128001c3c154001040e42c0206009412079800c040000998510744852100402e4415a42503220020340b5111012818941c0640440d485021148442504500300a0b103040e103c80c10010805081404006802102005440c4548440f03a4032075000c0801010988010310144145042c0d488040704120900015800420840c1c400b8100340484000301001d8030076a01c0b441e030f0003800e200591110300021600c68071008241100f851100d80c0c100744803c007020b06080f420f03803024006a1140d01111010306251145540000c3d1075035104c040342111005c0100c0006200050074182001386204d0842e5900030b422209003417030715220228178802c483ca8159000601982d003140145840302d5056602e440078800c9441c03000588003d01004803640c0d4801c1c070b125500a140a800c920380342800205481064003035401071010102c113546860400c2001e10b012003c402401d801c540c00307507400c03074901c3d142e440071181070303800320715040f607031440c868919000d80 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 930429433 1250 930428183 930428221
    0x20a0c0b180f060703180f0f060e03030106030b01021b0f13020c030d0515010903050c130209130c020f24090c030d110709051519030f0302010b090601180e 68
    0xd03004031000c419480c2c0c0702292040c40381805032170410400c2020080303820100c442400050121404002c26004500c000c40070390b50291061401040c0440ea2440d95070942c2c00c05e070702580c040383e00d80000e2101c0350b805004401d00d5100e0301d00b401c030300c40701c10000003200c1c1018603c03050702541c0504028021114150100e40c1c68540c65400c032a07a9034130100e500e80040c0760880c1d41e030300b503440c890204000d03641c450050402140d410400408000780d4080422405031141c070b44011085030708105403001d13911080322134403941200740b2000079400c03003034600a8101114020520040c1c0c120410f0a4003030294201210180d10626004082e5544c50078582450000c007481076a501d449101c0c0340d402c034958018402c01c0499140e405032007655544503542d0007551015182c070108944482c004c00103d00340001c5c81a404060300c08680b40361680c03901d4280da041d4ac0d128094006175142d40180c005402c1c801c0007280c00510072b00e800c1800c2c0d5813141640b0540880c0b070248801100a200c017040856000c40c10107000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 930430683 1250 930429433 930429481
    0x705150f04030302061b0c060c16020d0c030204050912180a121211070b090402160209010e041a010e0609070908120c060a020c10020c0712050109060f020a0c0b 70
    0x51191a418080d40c0c4a5089400e0408441c06d41ca150b20908a5031040d6044240c034580240160340f0b03228000346545d0011ba210190b464421a0800c0150b0394003044800201d001c1e103a140ca459003113005020030b960006000380a9544031120010989416800701c80c941c20070711b000c0320704507010340001a00c941501d0b40203941c1004808001801d21190000000c8070040c1e58940b00640000c80e9603e58030f03400c280c45240c02c140001d202000d460300381a0001d03c280301071045c82d8003082d40642c0c000b0301406802e80006441240301300c104070400c4111007034980070320191220700303e0540c5049005000c050004040f07031700503c00c09000c5090907001d00403d101600d0840c1c1a603803590301b4140c1e01f000642002401e51000d10410300401c2000407036108031015642000080c4c214000f0043c1c030400607521203081080d15124180d03001a0740c81303c0071524180c1d04c2c400c4001154a198038200441903450420407072001d507104014030328585800401d00c594142d4030150b0f600300c9940710305200303c00f0400c00c169010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 930431933 1250 930430683 930430687
    0x105120703020d0c08070c110406030b0c0307020c0109030b010b09120f0d020c0f0303070f0c1a04080124090b0d0b1006020d020303070f08090f0109050f19050705150f 73
    0x109058241d0040c0005503283d0304100700d00d42629000f03c03082c0e0800e88180c004100b08611080114965071010482c44e180600045070380c0340da90341d5800c040482105c581c1c802c00804010300040590502025900407424606001c00c4c07401d41c0c45543e0151010300c600c40b1901c80c00500d800c1c40340c440e040c070602aa0002c20945800c078107942010368546880e4071044005024005050250340b40010307035101c40c035201070021400c140182d40c032692076501002060318101045440001c81015981055200b00c040b001e0160322589895000c0d82900c502d00c2d140504144004044a402c5003503805007000c0310f10390318001c41c140da242804100c81d5500080003400c001280000c0050390000402c10740119942c40e8201e0b00c0d4180c00c0c5e0412603c070f02098400b0800503030081c10300410345114001e41900100d004056407240c5400215003400c69401c1c880032034503500152100101c000c4140407600c40c0342c400c0900039942e04103039981d060f11000c5030b018041c4245200d013074000700711030002c3c160340c00d050341e105c0255 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 930433183 1250 930431933 930431941
    0x80a05030a0b0a1e2408100e10090c0201330513020403050c010504060f05031b0c100b06070302070902031e01080c13020f16151e0b180403030902010512 67
    0x800842480450312013004002d0000283c0b503904001c40041c0410301d0b9198000d085003e00040369086d40160081c40107070030140011801c240103540c5c403401420141e03030b1046041e180001c00d00581c1d804090110a5903d03204022004895a400f0803010340503196188050400f2200c14080340c1c00c10350030450300002a0155403905541a500a1050303074060300031500c250712020f00448072881a4003a460001d90f0801d041d01e0b6140c094809542c22000d01d50318648001440c54016101d80c00000c0300088a51116003102000d803c14070418051131381c11b9480c1c0e0320300402d9440182d07035103006125829110364000b0029409030300030700d18003003084400e1405450550351510080e80d244003842000f4031074000745180007a0b44987d4400c440d01c3c065020380c502c0c00c007051008154051100d680050303500880c45440b078000c0325400c5c441e85c0c54608990461240610449200100321820f80c130307005005028003146d502440b1034841d801540a1b0f0f00d8500407510b40e02910048900340903440c03280c100004000140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 930434433 1250 930433183 930433199
    0x61e091c090b040e0a110915030a02091807031d1e03040806010b13150e06091201050901061d01080a080c010608010204090f0c0e2d030d020d0807020604080a05030a0b0a 74
    0x350f010311105e036001c1c80201e000050002041c4a8088036a502401011800031a590604007440e4400621800142004075600102c2c0c5004007100146c2d1078404154208184036405210348400d4000b21400c1328001450180b000740d0720040700008080c0d84044071000824820100126406000d40405550881d41e440e10340003201e81003840c1c00451800c07803910100f01c11411504c01c0f150309150780d6600c0f1642c80c022044c80803d900624116400c618400680b000b044000d00485004040c14000082c025107400035041d040b100c554105d81d288840040100f010250000b00d45c00102d8102e04215921050006024010000c95105e00c0d41d42d400810f00240c0400d003a0b00c449504400da2409002e00c1c0c5c20b0050407a41c0d2681108825030003810311644490302400301140c01c0314003040d075071080b001108040000f490655219030a000583c13000c4d5103054805d03404034a081d080102400240440d0074250b442c0e01250040380400c6042100200010302c000609402c001c00502000e0000b203e0b0a03211034603 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 930435683 1250 930434433 930434459
    0x90216060e031207080c030106050a111506040b040504080f0310120503040e01090b0d1124070c1e0608220507140604080705060a110f061e091c090b04 66
    0x460f420500c2000e0010f044140a0144548103030724808a1030324684c24160305840c660040d6492000304001641c400e03032010001c1003859104410031060b1030b098034010042100387c9010030080360046041c0400d00c03000628040a42e54424411200700e40c4130b40e1208170a005202c60740c3d00c000350b0700c802141c0c100180040440203100f0764000c01001c0e40940c0c1ca6001c0030080c4c41a0050a1390410020017071000030a109408048030200e0090a00074100c884820901000303442003d4503d205d080003409404100c09510740d0801402000c40440380e15000c90090302c01180c1600c1050301303001075140061a208003428100d1601b50314203a040c082c0b2025820001d545502c41c1c09894028442042000d1f110f203003a1044d141221111001000028200002d1003688e800c040346180034031886501c1b213a80318506000c00b01e80014190000c102c20700d072200340700d40c0101480004190028009044c051400c802103145100382c5814031a442d41c5060b600c4046404010aa0000c1c00c070f0321021901286049070744035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 930436933 1250 930435683 930435697
    0x60d0f0816050105060f09040b0406021e1209060f01030b0903040e0403030b310b0a121a0a1803030b0111060702011406092211030d0f11120301090216060e03 69
    0x2000b01301d00c4d0303144002d001c4040703000030b11145d0001502c1e0020b00041c1e88902c5581d40144107a401500300090715280c03201c24202100c002d85940d801045000d0310b081300381100b9602c011600010042418100700003200758806000282410007010001007071030000b0812540280f005040c0341107107240500f4014000c0c4800d641030385c410164207810120441d004c140415107035800801c20940d90000d84403110087c40350420f040d412800d0004001004c03194200c3c070110560250780050f00150300681745490300c42c80148214803541c681803110f150564060038400b107081d070509000919940010044c3d42009030310701844043c0c0318079801c001490740c2c10340056100d81628108181d85031280e4080001000b8110341440e8040e047c904080f02c548860110a05a580904060000c3c61510300100e420300600c2c8088801260030003c502d400d031a40880c0c0f0610f20300194001c3c00040e40309107840c07660307440184240c01040b9004100307441419030082e150180c1c55400401004602002611940c407034100c40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 930438183 1250 930436933 930436943
    0x150105030d020d05090f030a1202010e060903160b041a270f03161401290301020a081512060103050106060e0d0309060f110d09030c09090506060d0f0816 67
    0x800010401c1c0c0001a100c0e294142c030340360203080070700000c140078004c92094009603041c410340fa0b02c0d10100d00300414454074102190300108910503c0600c030340c90000c000d024885254000c028101040e911507654444040c3d210360076074031a840c0c43c200b002c0141600c07020045844040f07000d0201042c41341c0c690140800b01c15001081020b0004c64071500c03101d200c80c07031103c1500100442480d248103c1c03800c840061003043d400386041d0201304e400d821180c01090010700364210b100c5070b45042e0541d00300d480f0f802e88220025482c05103200c900420510b80541189940351901e0a81842d965914102c0811500a070382100c12560f52402c0c01400380c545071159001107500301041490038188024025102a015200c03c04a1850310340211000c109a803002c030304119081d1801074203100c00b4000030346050225614054402d081d410403281c040104d5122310340b140d01d00300b00c0307100103140420032035071281040721b04240c7c0010382e060000318441c1c01300c00241515070008100400d444582c0c0da0500d4a0301031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 930439433 1250 930438183 930438193
    0xe010e0703050c0a061d010c1a090105160c140705040906021c142a0414010207050a060914040f09230c0a03060209040b1e041506080415090515010503 66
    0x450034044501050b01544000524a507a4406c3d120040f1a801246140600d40295040020340b1004410051081c00c0d5030001040b1007400018031007400f40940081c1106120052019603c030040e04281d5450301c000e14260389462905804071043c0101030062130040c0c002c1c02180350030314069000358440440719101030254201300490310b00c284544003030b0a8103585051050303118144200350750500b03403c0100c039042c80c80d004003d08940c82c5010304010302c0001041505501d8040019041c0f40060700021300801034104100b101d0782d880300d040812280c4e0013140422200f90100460040c3c400d14000c2c9201c5400d00240344100000c00500260322040812941d1450341075440071601d800708804001e9000615000038000315100780d00400c0c010310000c10000f000700d4440042440e007242c00082080d40b00000c4411100c604150103105140c40381d101c8103201150901001800c00400584040d101042c41460310340d1a22203680003018440d004001c0f6102c5900880c403540b5500000d0141c14068052 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 930440683 1250 930439433 930439453
    0x1031401081e0109030e011b0f0b0103061427030d060609150e01020703080a1106011814040b0106080c040f0b090f0103020a0e040e070b0c0f06070f020a06050a0e010e070305 76
    0x4180f01d1554131950594514004001e0312004650004941d40405c0d502c4c1c003422904c1000400040580d03820612406418003d980765082140803621030701c1904045840c02e20802580804080e81c1000c1c4110640310001c011140036025031844c0245225022100c0ca40040455002d401000e46411940a4401100c0c01900036608440f88120700c2c04c1c40b809603104540500000703042401500d50001d10b850080b040d0200010000e207015420303404803a130300c04c0d2400c14040640d428041c001c00085024580c901d031b800d00380c3d00d035940050140324a40800403030002181d0b000e14074600b110000d140b5a40442c40842d00c0e14150356240d071040c07131140e109600084002070b06d0350085c000d071070452089440c4c8005404040041c48040c200440c5100c40c0c6004405c004640107404101501c0e61035010300041c0441c030380b108403641c98a0406450041840303049441951a41c0d800038040448a03440790b80031a9a4071000081c0014005420004940394204440d04000c2c980c00139540701282d0181d8116407103950 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 930441933 1250 930440683 930440743
    0x50a050601140706020a0309151e02120c09030c060a021c090b0d0504060f110301140d0b0a090609020d0503070b070503010b0904111e040f0501080705180103140108 72
    0x114008800b0410010b000b01000310b030081c3d000d0a010348150034081948815981d541854480740070040d584a0f80d190074118181030b002840d17078907409000800318540b400b92503401c2900341d0005e0a92890303050000f140d10140d10203104442d20420090141a290340d6140030180d03c40204250300c0140f88040c000c00000d491003500720741b08440c040025145440c10381d43c4400c02603c401403056071042e490b141d154800d04414410445100b10400d030031a10b82d41855111241c294600030442d01c10402d0140910100da50007481d25001009460005401300441c9801c8000e8032404070040d41c0030400c042e1610074084040000c0c02c91912503030415205580310b9401b81c507070740020b008200700384409002141540c01d182e0312048411001c8080705041c400d010444604244410081302d500c5100428200210303002d4520340000b401c400d003044405450964001040ca01548141c88510001c01503200b40c0c40c0d002ea07009110302600407241440b590b03140e04803555282141340400040300741d40610440489 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 930443183 1250 930441933 930441947
    0x70b0915060d02091e1509090c100c030c060903030605010210090506130327062d0c020415060809160f03081c021629010e0702070315050a050601 64
    0x80402010380e4181d4101d07809114180d40024049080000381c403217541480c0da0f0140b5428415244240b05441c00844c2c01c0030b003c0c00c06c8014000c482d4580c001000401c03076541d001160400d0313405625054114105074201100e0158043c48003403c850318018150080c180e054202070251f800a8088030182c868040c40d030401c4802c091405805604500b0100b004801f0715000c0c3d90565000380307820f20900031113003103811b592100d40c0e2a15401c100d06800400c5000d41241c6485050386054480e00780c000e102c24040b01090303035540c404904002076413a2603000c5513269808503040c1010f610f00c008000c0c0c1c0f5008081c0540d80c1c15607c045440c420905804540e0050038001d006883c0204c0c1007248640c550750380d01303107a504016074100c0a003100c00001c840b4444284090401202e40552003101402541006070807500b007507e60000075800980c44610a24441d1b1000b41168410b09090100d95142d01049080c0b42681d007000300003003c094a14540c02c403151300090b01035030901d9030030803140e110540191401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 930444433 1250 930443183 930443191
    0xb090405070302040c05120a05010e090307031b0201030e03070525031502030603190305090a060e100c02041e05010305240a020c01090c0b13050a08030405090417070b0915 75
    0x3951081d0703018001402c054210b08140c0e407640c2805404d24161417070b800303461380341180d460951030340d2200100628841030321059009122039000c2c51504c0720680740100400d10500720111942400c40d01402164403c0d4004500b0303c5080090703d44401c801d2501c5503c0c1d14a520844010300170240400041d0f9295405240c100c03940841c01ca0000c0c08007000c01d00207900002c0890303901d80140080244080c404031a8820054420f9407910b0f50350180340c2c200400c000d42900032004011103000045d40946032400007002c820824200101c0b240e115100060113040341400540281000294105080c480750f000741e8140da00c00c0003507402142c0c00018202400c04c014107001c1069440401207003403525154010140403a640001241e00520b549491981100550111078141d000241400102c918200100b0240104854000b007480c64203241583d01c1c01140245031060a210000c40d00704143c1c4407020443c910404029034581c1e030182043c540803002124121038a00030415080c03e69800340034601c0c42 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 930445683 1250 930444433 930444443
    0x901150303080402180117061608060906040f1a01090b090a0b0c01060b0313060e0f030910030b040f0b010f0c021530093906040b0c0604060b0904 64
    0x2585146440c01c03102e819000e8026a00076000c4580e640e102203d402105019181001e148200000d6110560f85410002050901138089603c40904401d501c0210036401c4042124401010b4440c3c0000a00400042c8a071110051809a448801396a2080a0642880c1c2604c420710700c143d84140326440d81c4103044802d980540550801e1258807030b518003802d02c40c503024000041b09912140b00042a900c141e07052000040040249810000d003405084a60002c1070301804400c00200d840b0359a07406041170003841500412030b82098207229a000c19071135140100b09004002e94001e41d00010b00110701c44a00050780e03020009209800740040e88010740d80504032843c1e02486040d107040b16000104021460f8202c0e201c1c4c041103400d00072101400e200080c83c03002e41d0f0b051000c90540b515043c0001082c52190030384205810b12030302680503c4064809540031080c51000c00066654401d540100b07150040204500002240005078544990700c201d404000c896003040030003288160171640200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 930446933 1250 930445683 930445721
    0x180f030f0a090801090b040204050108150406020a03020c1e061609151b030908061006140310031401020c060612100e010f06140a0504020703050a0e0a030b0106170901 73
    0x511900d044010025038146181010910780c42e00740d00c900b55918890150f0b0000c001005000135880e1621035035004000030401040d2119a0040100908c80d00a0020b00081e50103c8c2a0064a000790101c69403488104107803840701d80050010a41709191a04200e80d904c903c0c800039018814900386141d042d562038a0310000d2902c1c2c1a0b42c0518201400c40010400207001e2a6911308101901014800c1d40302e6110510351301e0070510010328210005092120004a9281c100031140d0403d90341088051200241aa82c3d9954007951211416030f6000a20510f10a003c3e0404500c1c1076010701860304494003510400d0f103401041011400d6003c0940c1d249421296041c0b030b046009034028104c081440c00007080d8480c091000001b100c049030300c00b04181900c0303042c800c01850020465805004100e40460074419281c1f0010181d0280c02500400c0c050b06541a02103039881c0c8074803100469001d006202c80350307110380b4001c01c440b40ca907049401502003803011411400c018005c06015510400080c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 930448183 1250 930446933 930446947
    0x70215041e08030a230601051c0204030c12060f0b010503010e07030e060709081228050403081903051005060d270507050a0605070b0103061d060a05180f03 68
    0xc00514114a40c00a0510040d0210800900c2c1d10303010710f20400800b140011400c02c0d02820a10500801691100f0844260f007044100d0780c022003600d495a8005803034001d4101c3c1145030030028400d517000500b000014881c0002c119000613000c11006210305404e1200c14240c0c40214180c9203061110790215070184018004c010b039100390139030b100c00d083ca000b01e400000007268505020040d1400000200c0d0342c4c00900c483d50080221035103003e10404a01d01d05040c552690140440d256009018050111780103601c8030702c0382007982c2c09150002c0189907034840b00c011907510407014002050100c2c1c14000001c20050b02020324104580003e4909481d010342c50032203070024043c600e8414a0840800c015480c401861481c0b40c42e4148550000c1c90300508020170001c444036258000d40422070101319041c0011040030000f41101e07840075010501d0340644c6407500b11032043c40d000c00594446c8104010130041550000e5015000d1071050160708503007607143c180c55040c018807641895104000c04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 930449433 1250 930448183 930448193
    0x1309020904060e210306010917032512120b04020c1b0102070f080d08100803091c0b041101091203020303310302030904060603020a02370c080607021504 67
    0x9044650400f0095408501840c0940d400c400d0305400c000e080407030084100011540c0100d42c00e40a802a004200010440940c2c0107540780310f10f0a111440144203c0d01448004580c681216003a038405100c0720f000c0f40c00c0c0c00040116011008051005040020031019420030740b0840d41510340800240002c4002d4802444042e0100c100355811445540000514603030318012400c09041c10030701a0042351445da000611801d405001340807030069000c070801c0302c03403c00400c075404050165080c0c0705030f18580d5031175030300b8006507207010f405081ca10b0708002c200883c0340d404228a007401d032140c800850712a034000542e00c40f0207800a015038020800300701c4042d0680e140c103c0980750744035140c02d81e10440d00c112154480202d0101c01691000c03464401e24a081c0c0188806080c40d03203400c5042c02030550700256201801d100031307200e4803540c05410405404000c140a22948038005010040a6525040202c0c45062280c13001a02925011880f924808100d40240b40101024080709880d00d840d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 930450683 1250 930449433 930449441
    0x1b09041b05030307030302071101021204060f0e060a0f0807020c0f040b06160c21171308010608030706060e010b0f160605040c08060901050702030a0309020409020a080705130902090406 81
    0x880029a000350000040c0e9640800c0209213191080d43e015844174464607040f41d04c1c414560711039040d500038942d0055500d50071025101260450302d050b03500e44900a1003031b1103859040c2080e41e0040c80c00107955880301d401c1101d89041410595842a855a41c80e804076101c29003042c100d9407114258001c980301d8a80b43e0410907001c6002481107103031100e10f800e4005503401c05c0034101c03a0017003036650070480d08480c00ea84503400300343c02c002c050350f440203551004074181400c143c2408000e40811240c8592440340c0c81c1c9805003030240000c0141c3c1361241346280c4c2d242c2040303600312500d6060840c0071400401e02d80c2100d049405061581c1c0c10016500210f403070382d40000d1912001581c64190348804180a4043c0717a0159000382c80c0c09043c00e00342030304c103420044000c1c113041e1503038185414001c0c116800402c072014442e0503d40014018031900c0000d024014441c07010f9488012018046141c0001060040c2140e80454520890039a07542611041d118400c070044c0d807041c190b000140200301280c00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 930451933 1250 930450683 930450713
    0x3052a0d05070b03070903050d08060112051e0a1b03060b0904091502121006080402011d061c060e090703150c0c061805010b03010e06011203021501171b0904 69
    0xe0700c0b40320b5211080c11810340c00894000000a07040002041032140a0000840311102454842d1580c6804070001e00070302d00240101903a039a0740c80010342003015000e50180303c2001000c0c07071101800e00e4070b9894045d1923020300341121a0800d4842c440441d000f8420300b01140d0700d4604160800440c141040001d1407006801d4400c0c1d540d12614104021441c80100403244000419100a041c14a6004800e8800f50045010b1205040501006d030707800520700b03442c01000d03c82603100400c14601040d00c0d40100c00940240b181664020300008085801c00020348180d419030491999840310b0701130782c3d8429440007074214910003030790502d8503c154200d20100f2100342800e22500d529a9142001ca4512000340640194042207440400c4000e0088a0715418114024022000c0c110340040c2c03200418070801030405241146502014002d02003d440c3760644056040603607551950104440c940c440d031a0f896000b1225100114034400500c40c0310b20381d01811407295070380c49584001c03640074420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 930453183 1250 930451933 930451943
    0xc030f0c0509010602070f05061810022112150607110d120302092107171204030b1f03030504140307030206030702010f1401240c0209010f03052a0d 65
    0x401d59450b140c482900810140d4001d0401c586010480180c07044c3c55003280303114050400c00c01d02c0d28081d00c3c001241038841183d0780135031818480b006078513200304903e0303d000c0400b50070140300d00b104050001c3c010722004c010046889643c1e10f07100017458030512681335480181405160040780560f010200c0d40c05002e0200302c810962a210041002ca2000d941700c0041e0700011004504c0c1848400354106a591164403868800d5014002d501c0312858041e81c504090031440e43c880408003007244261460381101c0003aa0350345c0b41d00380012003140032100000c2c010a40c0804840b4005240c2c042d408903034040e0747d03440c145410b02c94000380c8000420724440d414895000007001581e81c0000850050035907400000e0139100f08801c91042e5031521001c03d0241515500420601140d85100e4030070021255500d01503011402c0c0c1910f40000d81000039406c21442400854000c86806580041d64003400485001030380b100302c141008076044503e120440b40c040000c00045c1030089844000600c51 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 930454433 1250 930453183 930453203
    0x90d0b070903150905190312020a05040e13120f050414031614043204020619081909030e010e030106030501020d1d061e130f150c09030c030f 62
    0x394031036840c0024444400e00319282c4d80d9582c401040030810602482c0303000303004261b100ca4075070344002e07160140408400075041c0d000a049602944144101c40144c5145a0f105940d0304005045003100f150340d10040303910140c03ca4242d00418003500b541562455660b80c0c1e246800d0030b00320149503024141903034a80600c207035640c2004528030f4020300e00103032070121081403400d00ea1008210644a01c40c07000103481c1c0000505001d005138107045140390f50762440010301d00380c440d0710218071580719a150650042059008091a4541c450107103409030030346418201801001014042c122000c3d004c0040205403004003034600395000e1000503110560090000a00b5a6261122800d9130320540b821040c09684e154610007510b04a400da4242da10200700a007403901c0c201165201248200300f880f40c131610540006010008400c2c00c020105500180103070000c0c5644c0b0704003442c002c6008040800e5800c000d403404006214690072801c80b03400071040201c2d0b80ca140c80b4041000c402a800760f50403858 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 930455683 1250 930454433 930454439
    0xb0d0903030617161505040b25080702010e0a0b0d09060e011a090703050f070c020310140703050a050606040603090c0530010b06030402060c07080714090c090d0b0709 73
    0x660300380140e02046070150030403544098813981d8400c03050304102e00c0b00c0340003410700c0e61440d4031005075005c3e40c2801104030b50701d45800c10214811660f08048100c0540304070104010840a1806009185d10270380390480c0c1c451a020401105105500035100b40840500c0500e18001d00c0d9004003d0160184100260b07c0f00c040104500351840c000041e5841402d0100c0c0e40f41034240010101e078041132030f260030010380c2851401036180401c05064641004000c0000c40250350b4180b040e810b40c54000202000007480f907441c0307912618011940c000229107024000342180010740103d07841200c00800b50352605041c10800d0b001481d40b0503055039980d0340c840c03000c28203484000308407130702641c8070629491021f10300c40c4003444001c5001074503401d40d0520300303540099205d540641350026811500191644010800d4030300d0141a503003c8002403150390703000502258116005036020300241c41c15401540d604401c1030127841100134103600605e02c0003903900469110444644c0216840c9450b80841d86c2d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 930456933 1250 930455683 930455699
    0x2071e030e04110403210813081c0e2a011209080309030301051002012c0129041113050d02131b0f1704150f050a0b0406080303010b0d09030306 63
    0xd1002000940001000e006110b0174408011a040340c401c185121640006c20003080c0c5000945940d2600320f940341540c0401582005454030b4100c00d142c011648800700d484480505040041d0384a54020b03509010300c1c0710b040308810020092011042d00d01c50038040011943d640f0744410080c0d0701d90342d443d003220000e048400198012503409004540f41e506010401c80190720880340c0340190b82c0350005a2240d00116884800301054015000308109080c0c00300c035024000180799140c59423380e070400300b0340d00031115403003c4442d0199410840005a03408130b58462190141c480881315004000f040546060010382031403920180c0113055200315442260151010241800c0e8412007030381322045444c2e400a44110905401c1c900b40340200b4007403c07540d00c544009071010300200043d035920151298142c00cc031000700c48280301005a840c0030032000c0014208954110b1096023890000130f000b080020a8a050b202c220510510b070406c1001c1d40d0f801049014011003e164656100040d452 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 930458183 1250 930456933 930456941
    0x1c0807021e0102071b15030902010302091c0b062209080c1002180402070f0f2d06050c0306130c0e04020d02070c0503030a0c06090f021f0e030102071e030e04 69
    0xc1c40800143c0c0b16511450114000b4001002c01d030307101c2c010310a081005151018983c81c140306a814001610181400101c0280c41140c26a42c2c00c401d4007003001400c20516459038007840d0090f180f911130394a6500400c140c80209814400403003500c500b4458021a140d0b004000f800d100d6044540381003591501d46007010ba501510100041c0d02166055070f0201c00d640c410305d500030445046190a91a5980d046624018400502801c840201304410000369000607a0300b10081e0040c0e211056400c0f54102503501800002c44925041c40c0210f45c00402a01c141c03801103600610240704803107402e40e410001d0542ca103100d410010812604c0302039444a05c005d00e981717505100b0150f034a91460600700a1680b255204c180294410010100d4040d030241c04074a101740e2200020860981500f00040e85010104010358001107850680072001d11200c40f01110100035140c1e2044885c2c1602014200d02501e00e001e800d0280307840a40c00c00590100440c4055481303402c0850f005490040420106c0b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 930459433 1250 930458183 930458233
    0x7030803070806010203070812040c0305010213050102010e010b0901050111030d060b03010306140603100213080303131b030f0221070f0807090b0a120c030b0c1306021c080702 77
    0x42900000744045298080010741d0f1244003030004601e891000d0391000c11170300c03030b1360340d2900e2914003170001c01c0810100508080045d41c00500075034880522403090b803070a48181c40346501540c80e05940302c0c1c1d000018010b401c0304c264010603110050b860800195140190241d4400282c00108a5807607054414440c1e4405040d005105170b440758190714144c4220b03241110200c0c0e11140c101d0402225a40c00200d081340e50104810141e101c0d03240c0681403c1c480300540041940740000b1080128804481003151046030040030b0054000c0c004c0030345024036841c2e6000141c10010340d61920005401d140b003c008051051002d507050803007030904a5814034100d5002a01d00c0210310408101c081005c014150141482d5401000564080c2e400a0228176151081d8444035140786200018405110090001560080c4c0700c80ca4515003030704592400c1d4401e8142040700d003180035011400702c0c40000d5400c40c50301c45000c0340c4016017142e80150760508004281e04210f10907104e840011403a280541020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 930460683 1250 930459433 930459443
    0x3020306150c0606010806010c050d0e030f060c1806030403020c1c0b040b0702060a0213030224121e0f0f0604240306110c1c090e18061807061107080703 67
    0xf0301d06040d000144200409031040341002028494a00860350114508904c3e1000f420421402c140d450042070a00f01c10250000302400343da8204984c0410940041050013900e0f0103000404d21a00208220b900054038050010f90181800e40801d0521045c840304124050502d1140d190103692650f0003000211412500a2305500074024031036010403540760040c08448080d801e05402990000b140c2d24184806480b074161700c002842c0f5980080d081200300444489550741d83e00e04c0800032040b000003a541c01228040e600d1000014800b9100561300422131045002c03403030344481c0754040a42001901940e4003070b94401003000306e41a040079003504503650101d00f900c17075440c50030300390f084513040011800788000c2005101d1142c02c1c0401c089a102c0200401d0042c01016510211480c4503113801c08106895074900788141842c00c425404944a400801c82d1929a5110580541005001147c4032158414142072118034060050040c860b0300207412121010b0755074602d0343c6441400d41c81562 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 930461933 1250 930460683 930460693
    0x1202010519050c0f061b09060d050106050414060f070305180603070c0311010911120c091e15150d110a09060206150a0306020c0f010f020306130501031203020306150c 73
    0x803e0b100b44070b5400f080301054050310091800b0031030b02c0c210001790242c0c0344c800d80c4c001980700c0242d91400152400300c10b403503e0420141d03841c0c040181c042c0c1e00a01403031444440082c20b414103031404e08112081480c5038281e083c04c1015079039060f2695004648502c000401da21001801500c0d84009184103410b1681c61280840182c100940146000000300169034107203049203000c5105d028015080d8501501c5a58104141c45c0000c0d080491203280f266005c15900144927000381045100b0986280b001041000382d2181c0a82c02c10070858402c2040d0450100c3c20490400b0710400098860798808000111b00030b420080502699800794010801140c480d4605010940c5e04021459012000c80300c5040003a15401c000785032465180300080c00c103500054045040310f8107104070242104000c0003800342d14802c04103900a0340080350418000d0510524041d8041c9150103014101c83e00060341c110301c2000fa01048010390300060800f60010508031211100e42039140081c0401c40c040710140c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 930463183 1250 930461933 930461947
    0x7050f060601030e030702100e030f01060608070305011401141b06011811030c0d0f060b0a020604031e1b0f080708040312030902030d0c020a081f061d01120201051905 73
    0x9011030310000480304e010b81c414482000140c981d0003a00d11007112a05004501040f40e4000a00c1d2506801304901d5075400c20320000346254111004900500d5140c5041c031a0740c0e201d004001c5140c08034088139001502144201d8101c150340030050201280003c1050303011541d5a01c49881c1c28400e80c04150511050703c03006141d00b68611414140c1c0721440117452460900d1103885800b400788007014900700d540c5401c0580d000000ea807000009100c9042c0040d101d00d44e45101a440f560101e070260081500c50b41140c003a5011032a02e41c0c9a5a8580c481c6a04000b151000900500508008440c5500989040d50200c3d5100014040700c80c0710340740881d078441c00c5103444400810a8480c9405047c1499903110040e940425007140040301468031001d2403150323000180360321280b5409010306003d8140084000240d10340e13040802c0300221b0051205554495001c03580450030010154482c6280d001849501e0311000c010340882e00500d012303410303da003105915080c28040d10010300031400000d208 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 930464433 1250 930463183 930463187
    0x60219050706150f180b120a05010e120d110405030a0f03020c010801050108180a0204050c0403211e03111305011d0a06031112040524070917010207050f060601 70
    0x40710300c040001c2010141d02d14003140c1c100391307400c1d50050307604115050204440030000c0f540101c2c40020014042e0f40700000010a1540b1240081c00a451650030b01d05409031031880000e0b501421b03c0d41000407407600d007180003207000a0400724100154801e0421000070306030340c200030303440c3c04a01481a03002c1c82200c9140c00703880c002c40074003002c3c184080400104a030340e070490927403540b03c1100300c9158000700c245c401090400d80e40e4400258001c3c5400c0a1040d05500c0c50b028102360ba10a50300100711601c0705510440950b0340e945110001500d40d03001c004004084a44c0d07802003c0e40d800c02007540004a040920150041013070f4031280090f60400300182d41e030110901c541c0070b00d0340401d612000e11141c0402d4907000c1034040d002c28591102c817601007206c058400c03a08021071440362403440341018601207440d031075006032808600308840f41c4031902481880896005060781c0e00c1d0b40c10114586050201d0405151040c40440c1d5824803d04010410621864800305a810081c1030285000400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 930465683 1250 930464433 930464441
    0x905040606050a120c09051e03121b010207080702010e1c03021c081e07090b030a0b0307230409110405100905010f050f0d060209060705030c0d0c1e060219050706 71
    0x402041c5d0400c06a00d031182d4006200505460044d200c0c0d448000400c03080d80c0340d5072147c8114582512480740c00b0402044940080c00342d04603040c520258020780c000b000b9080c1d004441c80504048000c0241d44015030180e8206640342c2d0b000b17064450881200340c501c0c184400c807104240c000d6044900c203e0032601030360200f82d8a50050303080810300350518030007080d030421184102c2000c6009000c04a00000d00031410304000b402c03844000d507039a00d4000c1c0a03101804040103071034002e1085280114050342141148940c007500250022600c1c0e28040420015006414041d6020344031815040b20380d07245c500803d0310402d0100101c415035864a18128210b0314141d00040d03ca4000c65028005a905d211115010800480d2252201002ca0070242c00a2044c592591750004001468100300311012001c1e00d07550131301c2c030300340e80c2412205041507a0407040c43c50010300150040b440c0d031072031941c1e20019011180c01140014103115040000070054030903007205401107a004520030341040200e001e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 930466933 1250 930465683 930465707
    0x6060a060219230f070b0a0c15110307030b090f19021c021306030f0212180a1e0219080319051c02092d040b010905040606050a 56
    0x59850215241a000030740342c050109400b114030301d04200304024040b080e4440280b980e06040d061141e1101e05090f00c2da243e91211184203103004640000440110071000d0b1030461000c4d80b202c00a80c030032a500c00c52a1403a80602882c201e6840000001035218600554821140d5840001c0d142c40c030b140c20405210001000c001003500c1941c200880a8031300c10324803640715440303540561103602d052a01c1401c42c072048000100641f0224101400c04e180490b20301c215076842e1410028001111207a130203910a0100320070190b032941022400c1045c42c0765000414001c0b0740c00381da02c00c0850743d44404010310b0030b103060090001081401001d5150440d000140582c2d80d460440103c1d1420070500d0f12402001000740d0342603a680e0070301c0a01401041280c0090034000003060300340c044060031000940010000314082c29401c4003d4540a000c7c01e8903214910511034140e42c900c40120420000c0c0c4060114035041184400f8005402c1d00c0f6801108083c00094903140d403a002c05d20002454042525 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 930468183 1250 930466933 930466939
    0xa0504180609331410030e031303031d150c0109140f0d0206090c0d0f0f030203180409020904020f04060f030b0a050709030309050628020d180518040f020618030606 72
    0x28401c00c6114240000703100044c03800e60f40d80b00da4525065058000f4000c3d5200c0f030581d0f0000080c500b003800c5180304c2580a0782d10940f40d440b003922a07084106c0c9100e86064145400c103001c80b90031070071140d0910143c440800104004642015560740ea0501c0c00c100740c031015aa075000710b120740344011003400001d101940920007010b191511103c200e0740c0d1190070910340e0049082d0074080e02440880e04030002c107950071619030700d03040b00b030b6250095403a405220140c1d01500300c0d0169107094501801800c0616400038000905610d6913002c0042c004030301a4029801992000005460b4003e00644001580203520b40845032400074039035410344000404240801c038a4410a20029401c116503206030348082e1200b645841240e821400c2d104070b201d06005500e80c14500c00c41c0a03036400649800034040a5a505080d81400c02c1d000c45c08010500950340c1c45251682c81c081d0502c6d0700c4103100d0340540690044c00b1801c0550b000701e0101e0380001419990707042c1c5029440f00606041100303a41000e029 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 930469433 1250 930468183 930468281
    0xd08220614120103110607080a08041a04080307030c0201061a07051e030307050904330509160c050a02060a0c0308011208270907051e0a0504180609 65
    0x2100210b21003014040101040d07589203411201c1d84402c01a01c148a902135681c079541c507018a005405100101e400712140c0ca41940308240d5554003098541c000c603400300000e030650311641c1098000c2e00e0f01034060800c542d44d5000006004004403420340600c02240441a901d074a00d06100e42800c2803142034660a40da002500307400814000112903226109281c40c0d03407140080f2000074040d200501c1105904c0e0714883c09802981c04c12144030071000d0624000021003644c1c1e405100c900030301219040c41c207904c00c84940c00c12500403242840550301c507000ba103001207019030001e265030300454040340000d405040501c5c10980c1003440103024102d11001110b2086030382c0c3c1c40c0c04107403107880705000074522401c0740f0114003111a10700030700050f00145510402c0c640520000c2c0030342c02070b680103420855030400424003040c001046428032002030b1703211031030305003814088084160080007495516940d041c0008200025110700d0340022140c0d901c4100c040f80e01011041560741c13440d034184c1d601184c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 930470683 1250 930469433 930469447
    0x2070509090c06070302010f11031510050a1d03030307020c1507080304030509010c0f0b16030603200d050f0102071109101e090501081c090b090d08220614 68
    0x40060002e010b00c608503101a9111510715041b03000d1300b03410074034085450800245080003520301c0003840c030546121841890011212003000442c080f6019850301050080040c10758581c89540200c1d00060041e0030a2841c3c220350002c240b0350b5100301c480302c00582012000911038940011301d0803404154000d41401c000b42911041c1c881c1c031000e00000d0510200244080c01c5901862200d015242c10903030008000035242094209500d04869182c21140900b101401680c000c0c8141c005407034002800c0c02c0c0c1c052030b0b015604003500202010302e0340f050044513504006141001483e4072003001000160300c8203498a428016440600b4116101d40d07841c00420001246500c0c0d800300b01c0740500603d043e080d20301c00c1880140c40341600401d45240c145000494520b2000450b44858130004558071000d4001c120115500071941c055940d5030b2008009616251030001c8400c201a401900242c0c5456941038280400303140030000304111807201681080280e41003000c590600707400b18005407802c02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 930471933 1250 930470683 930470701
    0x1b0915033209071805061c050606030c012307051f14011a09090c0f04030c03020f0a06093b0702010e0f0d030e12030709080601080c0d2a0b0a02070509 66
    0x2004500d04e281e49507120700040306541c070865444407441c802200d14400480905000307840b0320040b240c10380a482000c0c09045954844d500300c2e4036000d562040c42c0300e006201c0c8034420307159100d050140d909200342c0c3c480c44c1c1c004400311400c501248920030001943c44030005d850074103c0c8164801607141055014240010640b071b000c07100e02c60021a050781f45070703844204120341c50141d8090b110b00014080360100810200318115001d6034001c80c0c410180440490810401178002d0013550b001075000c62003000310b600308000040402c8a00003102850b82c129041160300c0b40f8007244403210380074510044c03007000c503028800e40c101c0d42e003048060701c1c0c41a41d0412090741e80310482c601204140d640c5103402c1840301c050158090403010b45044039500c0c100724034001e041b44182e00580308a4010800000b420080000d600070354400b02501c1e540c0000c3e11034854810007890f0001851200710301c5c5440c03c104080000c03428025000000000382c0302e25006070020b250044c950001030041c00400f00f4482150 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 930473183 1250 930471933 930471959
    0x90606070b090f1006050a09062403090206030705030f10060219031403131202060f0402010c150609021b01060b07060c170108010606031b091503320907 67
    0x150003034000c0c801030302d4840c0e2a6260403c0c4450024141c0a140d511444070210741d0000c1040b582c00b101e20607042038441c041d280485002d48030f00e84c1c00068040c1c003203415004991081111050340c0c01d00007030740c0c040c5402042041d4000c07910900090000410481000c1d089005190845009000075005170b00341701c0060364944000b2a44e6840410410340309040500c941c103010100240070b00700c9900c07030622140407503c400c1d04e1402260700070b062142c6010300d41d10010b501c620500c15111070700c41d151070381d40054408100b180000d0b5544103a031a0010041300300e40c000c1e0380080c010301c04010381d61940240100201c1c1903504134024940d041900030841203501e0b805a4050341d400c2400080d02c09600e007816614150040300543d1582c40b02c0300000b0b070103001940800100d800c20345042c06075100c01c002080b610001c0508240c0418410321003406503140c2c41c81940c02d0101141400502441c8405001402d0744da088e0a542d01800016147d41d0b06403010000280c02c0101b41c0e0080165500380b407140b0082d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 930474433 1250 930473183 930473197
    0xd080a02120402090c0c0a140d0f0e010302030411032a04150e0a020705121e04050616170f0304110609090f04020d0c080d02012a23040e01090605090606 67
    0x401d00301c0082081241e07120219400c50341e05001b25a44078407a840d10b4201e23210082c030303550007074007030160892110b40c0100c0f03400000050696070300314916112401500250005030042e101d8021030b1407210000c1e1410068200508043c20302c01101c1c2d0b1103d645502507809484401d40241d051010013039800000096182c2903404002c6405150307a91859504000e000b0000c010341544941410b0390803071494074005222403a50300d0500c641c0303001c03684844002c3d4482c1e4801c031500054100601861000301e03c2036040c4107803140042d8081c0381b1000c0080ea80c140c00c501442140200c1c008144010070a040c042d035024220165502e80c10302ca84003001400d032110040c901002100c10000080031075403001e122407081a400202d03141c0c02e9440341c420596403030b24600c5940c090340ca003030740717801c20700700f0074041064a03241c084030b00e140c12031681c0c034200c03800e4441d116010a00c118152541d903039854050041c0c0098402c1c007580075000e40c5000891005c0d00c11b554072042c001d4400c82c00340b00e05900d80c0d20441e400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 930475683 1250 930474433 930474439
    0xa03091502030c07120302160305070203010e0d05041d090a080c100f0209010e030c0a09021e1602181e060d0219080c06030906011716080d080a02120402 67
    0x15400040c100a8060810000922403140c030000800c0902c80144018010990107100080f07891106020240d04901c42c201c000d2140b5015408030000180c131a03401041100d10190002c1064450303484414604810b0542103401b0500104084c4403402001d00d001103540014110310100741003410915450b0110200040c0411400107008040d1000c204201c1e10308203800b80d010170a91081c178100340005e4000840050004141402c500301b2031800144a00c00c2c1080104094202490000c1041c000e500591184001c0c882140d040803424244038007800c6080940101c0381c218001c1d0b481040040c004a4003203066031105001071280010011a00851000310130030038582c1c3e42c03101000078040c140c4444000394041081650350042071045640c0104690000084814420744c00d0308028250004550541c030b035a002c0001000343d4607850b042e84411f0001032040e07070700440031507000804401e55a0000c240560050a82c006801d034860401a4007038641407085061038091082c4043c032000240020388 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 930476933 1250 930475683 930475691
    0x209071d19051207171005060f21101407030c0503010605071e02041e0e0c060937030515010302060a12060902070501060f0b0a080703050c040506070501050a110c030a03 74
    0x1c80f490070000e0030302070f0100c0c82101240518034a41d050303490005c150540c008505000215200d4100007140c11081140205011602a1445d180c01025103004052680d248070302c05903c0d040403040e2240f84680c0c00b042c0c0c5203503c1460005405010b540201e9410010007208000411446901074240d031364969212035685500400142d80428408071380030701950141c9000d0301c60803201c0c00c1000480441d451030000344120714030340c60026120481708c3d14158001070104542c00e0340b442c0c091010046181060188202142c00b0110704061a01600301000020741c2210b0510a009040001160f11400c0040c02c0f4855030666004c600e032405000150428003e01e4090050b02050942140010b080407010840d11a402814054003814485c810f918803001810300c00306580101030129607120400da21000c505449042c4c1c11801800b004000340c0400c0c2046c000441e699031040001c0021500407000031405003050103400c4115149822154200795080081810074000442a20044022810001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 930478183 1250 930476933 930476959
    0x1a04081906020409050a021b010e0d050d1b08090606042706060b0a05070b100b040b0310030204091a070e031b03011803080f010b03040506010b0d02070209071d1905 72
    0x4000c3c2c000c44d00310619031800c0c074003000080f44282c2d0141c10005140d5029003598441d03d0f861600700d54141c0300400c03d82c4c0003035030f82c050958000c00040c00d00c0328024200159504021041383d814500900d44500000e80341c909104451004000460300802d00311420410f8101540c074603001c040c1c0da07031940e86180b00401d14890034800e03160f200000030000d0b28032031951030040e440e00400580c010713a01155503050340c802161074031251003e004141c803d1001e40a1600c0c0c00e10705c2c1c4860b81e41000344010030340790a0607004001070700d6901131040054411040381462804c9161098445900288150200540d0b8681c1d80f00329580040d08960000784080c4143c4c1100740c00c80442c0c00743c511150143c6031043c004a1840c100755000301c00b07521402084c009112281d0b26500800d0a03448281c401901c1a4480c4006014902c00400140917440038a030340107240018070f9021900c1180103d4040c0040b591a030b41c100c80c00f111340500c48200b140c04960545140b40001c4041c1c0e11a90036016a602804501d1008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 930479433 1250 930478183 930478193
    0xf090c170613020d0f0b06010f02012c031c06050405060102011a01110f031c0b0604030c091a120c01081308031303021f0b010e040e0307060b190f1a040819 68
    0x11002c803070307003042880c0b4422811b4100ba10a11b031040c3c5540d80081e050626000e046403040c4121054500350854081c85401c070b03446003c013170315000b2a60710130600003000031111741d5000410200c08419a140302044032403a00040004030303107005005606590401070038001c1d18400340e48003442e044090901c0071602070f45011075450942d804404100174400044c40c840303a0b040d4802d00140561091a0078008110f810050104038041d034400200f1f1200400300500186019400c000c00c09401c513140e0f8090140c1c1940011100c108440340005142c0007031006020039607000c9040c951282c85d06c42d40d401c0c450100d42e520001480018208006140d104204004043c824002c020890810041200c000079144000c44d0042210a011a0203d000c115920550307082c2401a0380e011981d08001d0360502004d0384900c0003074168007611560000d0400131010843c0d001504020151000301100c0c0546800d100321861107005c0d200d0a4038140005000c100100440041c01c110101d0a02c25041c20071911882e10b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 930480683 1250 930479433 930479449
    0x1b010c060f02130303020a290c0a050d0603030509090a2f09041e1404151d0d11060c031312020a02031507020c0916051c0f090c17061302 60
    0x140d240c0c254480f1000200b170550019034406407074040d080041e25080ea14002400c03004c0b400d041045100030100008a4070003d440292001c03462906102c0e00d4480d20b003003a50300b11560b80d08201c003c20f4020440c0100350030032622040c1d10058080c0c08002c010002c00d10903104c1c2c3d0010a40d030044105003403011014100030310507030301d4400b800341003801419121000c000520b4000e26038071140b54a0500c61107582018802c0450043e40c1020045e10210035000c41c09015045600698403135000c1086d0000902d0743c00c2101035503003403166892541c80d00d8402109810100d0207005000c10303900c05e00034010340c1c1c1c28079844400200c1c1d04c07103400c41c2c035900d10240c241c0c10a204104040c0d89401400144a00b464018486510800340c69003586c03000070b6a0410400c080d0815100c040c10242c00b07580e04609940540300a004010b80300140c400046841041c800540c0c1c2180c0a01c0e01c0a81c8512106040115062880e005000010b041540100402c5041c942d20300d030007010070722014a040c0012044d500c40c04a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 930481933 1250 930480683 930480697
    0x203070906090e0f010203040308040201050c19050601060924180f0b09010f0206040309060e030a0609083c1e130806090106080714040608030408010b031b010c060f02 73
    0x40c0500c260703507030740001000900a165000c0a03d010300380d051040014180300b201c0c4525850f07142e0310322685440d0011949900440d80e03514041c0304040c04a286e40202036450548203100340000d04480d810180018401c0c41d0340c3e4001c25094565000f806040700203550001491046440d00117241c1e1619240006084880d6000349604040303024049140c00c80030300203000524086c0c860786a00324980d04126a0f440c400c60b001380000394501c206100b4140b0400304002c1c108401412030f01c030b07400e07940c884000322100203104039003407103000480703610385240d084580725130000b503040f0400320a0704242c6006101801d0750746503c20b00303000200005090000c0c1c00100808903048103032130700c0701c3c0c201521510314443c41c002d03040c40780b04810000d4030301001405404169290030010300403c9240c51144007462852502650b07100c2d071103010200e6681410000b5000804252001007410792410043c5801d1426010f005444001240030301f071816600718840304425a803107800040c03c1500000000e00a0241403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 930483183 1250 930481933 930481949
    0x180103080c19031101060f0e040b0c0c150103060c0c02010203040b0310030c030b0403031508120d0e06040c030309080312060d06110d0f050f04020108040f05070302040603080304031e1b020307 84
    0x5411428158054114614803500d10b0003080a1512030040101800d928841c6a003070188c80c900043c0080c0040403c150040300030345440d030411616081040c145054401d89201c04200305004109000550041824524440c24100c40d000c2d40ea80000b926071207180201c00d101c0b41d0010104075001001d1940000175500b15600315a00fa071240b03884040043e0036a030a50000e8181030741c0b6511603008590420440c0e44950061078440c84509400003643c101050240300580d4612503146000301c1442000c0c456031065911082580c02c2d45006001c9070760039000000950310034860680d0006144042e60f42052089030303034126090043c6408000340c40e580045840411021450440030342950f0005e00aa00c041c0e101805282d0710078046004142c41200d000e400219020041000b0603116421000b40c1802003080d2045c20b500c1c0d40101d02a0340300ca034011550180004200030616901070310b02c144c0f480060a00c0e940341103c04000504a1088105030503540c500641d40501f10f540420075000104190 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 930484433 1250 930483183 930483223
    0x70b041406042019050f0a03020a170d02030906040621110406020706020c0306071803051f0c030213050121050f09010c0507030807081e13050c180103080c 68
    0x2d01e40242c40b00e20300440c280b148229146600c995203840413000c2512114100481600c80c80c00b030400c060b1803900388629403c00458980803000d0303150b0b01354500182800013040c250182c510884a481c01c001041618115041440388803096500c410440741141c0030f84c603011162228148003c1c039420700f520300b032668086c0b0b800404d070032550b0002d0280c41202c81c82d03020380b40d40366610b8005a8031020a80300450341134200320700150007140680c81f050198441030701800d02d22a240d0b034406152245914080c81803500c80c2c038407000c5060660181000c0e43c8240e103019414030303a00e42680075610302c2c613003d82c07810710101140c00714522800c001c3c24405070b00d84075418005030400d0190540b59004c161080c1e5495420040c0d0f44001074001c800f03c50141e641551450051340d43c41c0d00c01c40390900c6c0542003565250002a90800d00940802c0341c42c026444500101c1407400c082c03821034a051740e000051809041c040c031502c104240118881411290002d60403681c2d548510307203c2c0c2c200414600482a18840 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 930485683 1250 930484433 930484441
    0xf0e010c0e0307120305040e1f0305030702030c0402090303031305100f05010e0603070810020d02070b010320032103040f020a06050403050d0e0f04091b06170a02040308070b041406 79
    0x110540c500d4201c5800d800341e8204507141d003041104d992800d48080c0100b103040004118080742410386603440080c0e05a504070346010300c400b000104115a0050fa110303880440c0c5c8105626050081c400c1d001c00c102d4045162551003c040781e22400001c0000305101020890070307040c000240400703410542081340410801452144c1c0000918082c06018003000414000940c14100040c1c03035016a2400380080c42000c50340d0a40301c0295011801c01c0b480c45409104000006411a0b03050307020b0b611410100007280c091024100200700c84030f1703080d807080d401005100d140341d00c0c0601d44108401030500d8269266603a09042008008180000350480318806001801d0b960000140050303034440d81c161204042404001c031050940c1c820555401105c10b80b00b030b16540b501d540200d100c036202e0803540759002040d88110310702008030790150000c039207900c013411401c1e1070280381a41c0c807004460046081c035045071203088103409122001030041c0d20b443c000c1014800100300003420720001604640d21490 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 930486933 1250 930485683 930485687
    0xf12032808070e0d0f2f03030c15040f05030712020c0415150512010906081005061c031206060f0201110f0703110f030319050112051f0b03010e1b0a180f0e010c 70
    0x41e017210f1b00014005000741c020346004022200100001c0b001440703003608160340704a07040b41c00f030011121300d1400021040021410301c041c9c05a20b000e003214824084690b80064102281c203a5024403941c6031016442009148168113429100341c62400e2014040460086e503080c0700c0c1c2d905d03106134940348400000d0807000c80d81006064609200a80d900c6840ca401040159842030341c1965004084050111014030f4001110083d28001c0c9450011056080c16402c12980e06401400c0098280244000d40d16024010740d060f030420f8a412034a0801845100d10480c003594a00400300030701c81c600840c2c20801080764050444e80d00003925035900b40041e40c00141041d0078508540745080400004000143c510b0744c2802a40180107014000c00c2d5500300070342807000d81041041584c1d1480c2008854070244150540011400c005040015000c042d4100d03d10580480500c1205030314001c1c0304201c840c24500010f807102074004100c011061035200060103031640152225847c000240d01043e03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 930488183 1250 930486933 930486983
    0xe01090f0c1e0b0f2a0a050706050403080f0306060408030f0a031505060306090a0e0d0806031501060f0e040f02160b01060503150f12032808070e0d0f 66
    0x6140707048280b0220100c42102c000228031449440e40b110320074460401d130201d0501c000e0009041d00c03c2003800c26141c030102c2d11281215884200b080d580708103254000c106c0200001d0700500344608050b410b181c919541c403489441003101f487d5800c076012021411076100d00007941d010340081025242c5405101000005a41146840c0d400003420101d80d1303001d205912001d80d0a80302d0180545186990311070070f10038200000341c207176660b4607070300c0003042c40001c07085c4082c1d100e21030207540e2440b080c2880c404040c50201e405d40030744020505980100a01904660800c0d08171350035042079501c084542e8009001822819150310f80b060002908651a0500c42d0750140014403e03404030440e039880d0f00c022101400121030440c00d10950425400031450080d20f0140341c4a0018136a00070034034905001c81c1180c0142600f030741e4401d1850703400d941d1005a007210f450440c25030314182e055460030b03850040a184a40ca0058010703c2944411401d101e14514144c2c00c8a42084130190003044d80c00440c2008 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 930489433 1250 930488183 930488189
    0x111120f0a120c0c110f060a0e0f031b12071508060415080c010309021504060c0b01080c01050a03020c162304051302190e0f0a06050f030a060e01090f0c 67
    0x11010304001860142900c1041035040d40d5903200040201207584c0c40310000c0079543c8041d81b100001e006040300703a80d9000207081e141903980d50401c4080301c2c4414070509081f00d0b5100303803003904884000d50b04007603402011489030800315040301d110000800a107080050300cbc0c0080705000140380440b4022030700690201d0040d40e06070713410405103030744600700e0071209100d000740c003281e4100b0050412150303c00c5d04090036450005103108003080300b140f0004c00a50241c1c0c401008112a400017038144815401d01d54010148800a0041d04100c040000c205e84510b80040040c0f5602240700b400c05e070380070802101c00302d850b01070303e602e100d84034020205851002540d141e01044201c000c01090708040c0100d90048007a41c4200c520090240e08100c2e00310369100705541c0107020341400060042c900c6282a0042c00e000c10042e81e6400c00c04115000e0351100d802050040114200c0c01c12039440018200c4e14031a00003000140c1c003031264190a015104101000d41003603020140001842071070f01000f012 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 930490683 1250 930489433 930489437
    0xc0b0c0a140d0c0e0603150f01091d010306050c0309121b0f150a0606090b09060c030403060b0301050a0911010f03150b0d0606030501030f060e010b13020a020d0503060f0111120f0a 79
    0x13109a5108004d1544401c69441c1401300c10913000841600744010a030050300c105050800819490f042c4503401507d40010b070209003207001d0b004001b1f1040902c602da4002001180c03051544c030f404c40c2e03000e641d075414070400c04041e940004d07001c02c03c002e540302c0c00100d4420102a200d00300e001c6c00c0e040399541e000e541c4101003060748a000c940711042c83d10681048507000d80b1603203030b82403620960500f01e0300701130308003508002c04000da041d44070001d10080020b0b52199000040e9030300700030107050031901c0007002103030007926244003000441c4981e090380d05070550918101c042c03401d01800450150034058500310a0821111380429200c1c0300c0303406809400d801e07403010003009965100c11015218280310140013000149213000200e94a604094641c559010002c200c1140312130100350514100090114440d9001c29102142541032010701c61000c0399103000e40c1141030a50000302c0d200c180548039418000b034429103100d5824240201c0d50507489101101e070300c4130b0400f82a00250382c0000104d1340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 930491933 1250 930490683 930490697
    0x13020c0d080115080606191806080106050306120a020402161e11090a140403120b030a0b060d11060f030702070b0a0c0816051b01030c0c0b0c0a140d0c 66
    0x40c4580300d0041d05040ba44405100080501041c3c03007a03441010207495030382c1000c01000205908072408408130300c03010355036480704480081d100c46030b98001980c1d0814400c0103000001000100e50040a40e50000b0040311003240d080c000c028004c3c40c00d11001802500980046800740e07840c0c4600a1002a440c0281080d00c2900018038880d00c86040c1c5d50b100425030070b90794813121541d00300f1038940399000c043c801c40000c600b0b0308003a004803005000c4400714006014040000d40c000603d00852101c200c0c1034009119840340e0303603130703542c1e181500800c45405080038281040c1840141c1c1c4820204000c0540201c3c0c0e100c0700c404860f100e43d401280c1c80300140c03180720380005440880000b1110b20301c40540d01d00040800320382d1140a20fa10250b5040d15052001b440b0802250042c0700799018110f0034010000c125407908005801d643c1c00c2c5554500b806030441d0b903040842c18907c0d207940d004641c0030540b56244110681918640f5255215400300c040c00700700100d01c05007517800074400742669107640d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 930493183 1250 930491933 930491953
    0x26010e061017060f1806010b03060406090b0f01030e0c1504030210020f0604030503070905090a0504120f1b060216110906060c3a021506040c0f05031513020c 69
    0x2840c42c2c2845482d415a502c40030001c1e00410b0850703d126003108412521512100311a041c552501600ba044031f014060000140316240c509882114018444171809125000e41140021074110010500314140740e01c81c680454614001d02509800280c0202282d81d180814801c4c0702c10f54006000c101e0241681a146908c214000940415030840c5480100116036130396600310b650750400b801110500c4200c40000c90f40e40c0c0c52800403440b40c14901000502071a15040641c1c03080d0501d0003090500000c000040180c0d5400700900315000d0030840d4070315044100d86003580003031003858890721401e0104108007003009010845500c0d0b00400301c86820040d180c1da0200503480c8506c250b0085164001c05a031510107803540c9041c060523030304000042800c032035440e10846000098800c0401600002c40e0f600e82e1311281402c45402c240700751340401c046840c0e02c0000e08444211040c680c1130210101c0000e03810340c81d03808000340120340901400511150591040d020303400c91801948036000b003034102 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 930494433 1250 930493183 930493199
    0x11a041404050615060d1b1d01230909090312011a091905030d0210061505030103230d0c0308070c02100309060f022809060926010e0610 60
    0xa14001c54106015040c01e44510000710301c10901c141c00103030030280500400003001c42520500030b078040b40d0404c40f507503083d80680041603503a020401c4601c13442592404d00c1da9990000d00058901c1002441803143d10207556010032501491031842e622940d0720b8100002008080050150800c6103174a080c1d0503621000c64020940041980030880b51003807240c50140d1825480c0e10059100c150040c3c0320491700d60707021a0410b0010404840943e00c003440f0f6161500d11442500000c0a5641c0984614078450400400c188010b1002030061600181d4a212100c5540d090500d10701a070402c03100c920b00c800c1405004060310180940c042a1a64006640c3c00e00410090403450380c010900044441562016401005800b0050381e13815a9600e50040d41d0f01d443c8001e10002c1140c04143c2603081e0300d59000300010044004c04000c201ca005410005c60340c101901405841c028040c10640500c04101075082c031548080c2240158204010000444d4000ca03000340241d07940601c0061aa443d0082 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 930495683 1250 930494433 930494471
    0x7090314010507080c1b01090305090315060f06130b0415030e0f1f061703031506250314070c060e01020a0c09180210050d0f0b0d120201020c011a04 65
    0x41c400100303410000107071540c1791540017800310704484102c0880746c4460031003107030840c0c207010011000f15100281e00f0a403454100401e03181c2a4100303084060702d1030010045110300e120017180d01e000341c00109042c084205c2012404014101c0f0404540c2c841e40d5407544d59580000d4150f000c0c01080ca8041c02076400400030404c2c0c8234048090300148500ca921158542105c05102c0c5d5800519a4130307040415000510005802c042c8500c03001035444c2e0800d40c4c0d9000c1051111204c1900ca00400c2001445d001e42e00184003910100e90340d91170f1540203440c01d0a5401150410020b8000030001414200300014500b40074141c41c000d6942e840c01c015110010ba0741c1c0c0e400004094203d0f05015410000814560400400e030240900d0429840c002d81d030110380e850043c90003076004200041020700100f400c1b44030b00021012080814811024100d001c504510b802a101030048174000b05603518081c002d40407a2120b01c0c90340d00070000c4110040d0002c0c04031101e19803480c031a0703041c4481c20a001d200402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 930496933 1250 930495683 930495691
    0xc0403151a0a030f0b0403021606050d05060d170c0a080f07050f162105030412050d050f190c020a0602010e06160504050d0c1206060314070305100e15070903140105 72
    0x80040300c2410a07100d170b4030b5400009008404500c1000184451b80c00d004203050300a240315210103440d404540d4004003074030001040305001da070071603942e10082010f1010344400703070101c000c6640d0788202a14003581000d004000142850b400051480801d00c1c50a0080012601620179102c4040d1074803a1161200580d81b01a4080f00042d50b040c03203000c0d044411500320b03030711020000d185180030b80e5615095400c2640609202c0760020781c1401408024048a690200c40e480d10300c4c40e000781c03c01aa1003500a2800618035941480d80122401d0f0141c0040700101c3c0e0010f201204039503403000c00038064543ca40c0d407400c99025a0340400c0200304641502c2c1c05d4010b0984a403030078982064107100c440d0702c4450701035601042264000a88826504d43e24000320700625000c03078141d00758140507034a2801d196007000c3e541d0151400304042480400e10005000f082c0c84085141078044141e03a1902c0018036208104040c150140a62a0f80040b0a04211307440740807001c1180f0b0711540324a00704d8908403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 930498183 1250 930496933 930496943
    0x10e0603011d0303160912050106030c062a0302032116030b1c05030708070302060f1807090222080d021e06070e27071d06120c0403151a0a03 62
    0x100100f0301d20006940c440200c0715076894070800341640c1d90003403000c141d40d40340123031600c2e5956441442407064003e02c41c03014200c1c40c181154070004218007080c110a1a590304261407040b060040708051090040328204080740c80552643c00c00501034404241058841000705c81c8030300e0300100e44602a000f0719000100c001c01d4954031828000b01010130780e00b56031044490f03000c05c004040005100c80080c095160003640104890b16000f4940d4220a00142103103d02c1c1c000141840c03003000c000503511060340c0e14140050b07119841114143c0e10281519004130742c0d00b403440c00100b07080400047c0008011003031b500f2034682c010305840081001494100f2640146c0201c4001091603008107a210590400500104007086040d46030700f0070342c035280314a001001c01480c14000060340c0711100d100b0751090300e10304010701400c41e0b0009000b8400d51a02e074a030181040000303500d103100030060302c006540128041001901c01800c5000030700322a100200491110640d507411130030312500f1802901c1d841 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 930499433 1250 930498183 930498187
    0x302070504240e1e0405030306030d090305210f0c15070302040302090a050402060f07060b0a0b032e05030601181103150d061d030c1002030606040b070614010e0603011d03 75
    0x3c4000000c070340d4001030a1100310805800c00071106100305072854400c80c004e06c06182c690411204040c00d014130400c1800402c03040042c2440811000703c0c880c00c06541c80506408030401c0400320368104c0c01071141428000f04e020a04506504011850f035440b5844042e88207010341e2001340a030200d0043e07020280d00018200002540304405612050300a4001003000781808451262800c45034004107040341e5031911401c80030020b0034000e2402024019031090b9a08501e041003104008040d2089600650f50788901041010b8580b20180c03001b605000d415960701c0e68403038002c2814518542c4884201a181060300c191001000042e2405600035045540110f24036004005d00e0300401c800c1070301c142d995004005040310b0394041d0145504108400703507480d015070740e04140c00c182c081500030305007500400c2041003a60340c03107085406030b03a40101143c0e00d401103400c20400611140060040d400c034004000b042041d0800d50716841010301324000e0254004444240c5003408003405800b00c07503402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 930500683 1250 930499433 930499439
    0xc090c0f0d06050a0906080606010c080a0f0512041103190312020a030f1d190c0611070803040b0d180b06090c090d0b060102010e12160c12030207050424 67
    0x280c4001d2032405840ca001298072501e03540028060200399106980c52661106c081040c48402d100d0b9079442002403c1403900d540c0c00313844004141c8511410b4500b00403002c1c480c5041b0b10701440a4500c402d030102c281c02418507051402e01460b13010019640e101e4810605a104120101d10440f01c01c03503415039408400955203070240010350820314070501071640b82c00b1204905044c510628a40444003200d100103400d13a1200309091100715140040ca00c0b21901c1c081e40426801d01c000000c4030b01c2850406019500310120a003046000c0c0c0001e5000d000000300002d8900700800588000001020100b06c2041c1c0b8801c008050807145030003c4c001001240081d004d4a0846c800380d91080c1d54070101c61401c1081300000d400395400a000311441190740c2d05011b0035590901c200c46103000468010140751031030200765809030107650441d43c00d80c10101e10b490708225444502100270404100c195000044615010b9110070705070103100d01591a00804a00802640c0881d0603181500d1110f442c00500f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 930501933 1250 930500683 930500707
    0x3072304091109180403090b070b06100e180709050904030806130609020d1401050405251b2402040b041802040806101401080c0a12090b090d020c090c 66
    0x4040707000c16603110b01842901144e031950542e0024041c1c0d0204010f90384c0c502441c000d08015102c0d0400c21035102c041c8000d40005a1092510f50489402c5800c1c10300049036032401c4905203200169036030408800d0240c0c2d10301400800007540910500d4403050007440d1500148208100200c8004d00029a980d01240c406d041c851581d0010200795800030412680343d0205030140da100000031880655200d802c030700c1042c0842112405018111814002410314090031501e01000c00c030400f012400344e2007901c481900408000c2600481418102100040e6060803801800846d0112241404401d241c0220440c584203c0b01078811074030005042c282030404800c1486101e000b10428035500704000301d03070390300108006449428800046036000b400c140050b0130f507180000249043c80658428032035120104400c0e1251143c0614000c00b070641d80c9003a40f005417040312406819510000c1c02d100d0981030100c2c2c43c0741800d5803a000c40700d40c50074134804d100d1001012564043c64580034000058114 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 930503183 1250 930501933 930501941
    0x7030f0c0c0f05100c170108010b0102070522060e090c012c0a0b0c010b0a0918021203120702010e151e04140d02010912020c010c15110f0307230409 65
    0xa4001d00896090a040144c2042100c00d001600c1c0007144895810700a6007030304551460240102800a01020100000107943c800c86400784e94030812104094400144400440c0b039064100c07500b040c050950345014405c00740205440a8645016041e4000e920354000c850406034214400b00403107400340042500c4404100044e40c96030702480100c000128200a000680340b481010000040d100708013000304030b08800340ea40215961401d0a10581c007c50075984c030180c1403901aa802b415920700e514209096204052142c0760001d40c280c1800310b0355605610030703400120544101d030007000320415000c099060407164241101d0440404460608185011a0b0047e100b00c5040c0d545001c604a02d500b00700c1c00381003482c0140e5494500d40e0900c40070100001d090b030818000341031040655800203000d170121b0003000d01090080f80c901401e2082d01d034440c2512200380c6c0707070442c0c8910200800c3d81e003550041e0b4000740041c0e0340b12003040b03442c42d94503408620030b0282d107401d6240c50b1401d241d10000d8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 930504433 1250 930503183 930503213
    0x22140117090703390e010608040c0b0912011406130204050d170c25140108070c03021908071103120a0f090b07030503040c0b1602090603032107030f0c0c 67
    0x1510020041da50940401421303d6410410104003100e00f400c003445c040c0c0b03d500503403100c410081e8a01c18000414001d100d01006d85070036000c025030390404500400c0240442c200c00d00f40070741c6031481e10b24440024040d05130103840c0c1140c031080e007407807402c6003181030380294000c1581c019007031401100010700000d102140401054034190034010824442800c03e4485100c58101c000714112841810a4051002014002c811242040c0d0082d0b040000c00611006100d102801010031080c42854002c00a1241d00c18040c44242c820b006a172a2008458020f10011613900000310107410707036850007183e18120080210a0b160902004100488001d021950b030340040c04042d0802040c031909400c020520349009454840d900c1c10b084c030380780c2074070b20007a400150301150a2146404400f07401c0403081800f6011205c426107911100700180c00d5200b0340c020780700024545c0400895400d03440c1803003840303901c09072010803034441c00e945450160351440004000083d12810f8041c0002c0c034040c159205 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 930505683 1250 930504433 930504473
    0x20a0915091815172a09190c0504090b03060108030a0c060e010204091e050421030b130903110325051510081603020904030522140117090703 62
    0x10301e0060010102d94490581210b10703c850f00d031502c0040550104031855002188007220b01403100c1560a22040001442c03034035224150a20200c0c050003001001e4441c400c11611f001c210070308184030301422550040c820002c0843c05c00505800342d250100e00e0718101c819003801b0358a0030f142c0b50300440e042150074400302d400686da508164142e6009102610280140c45400140340c031070500304407030035800e50b44015021800d0070204000100c61034030f208011003846483c25541d02542c401580a007040401c800c2e04a83d0700182a80c0d4a00d00da0455100300713000c0c0d02d5a0005800340d00701d2039228400c40c44001e074400c58400580540d6514104040c0520f030040040e9070801d842d80c440b407a101c2d00150740001e55003010070800c0c000600184001002d4040761983c49c100249143c0c0880d01220b00104040c0c1406408600c071080102c40e40c12a0031f8200c4031901140741952074848808464400032140c0d03001500840725011400c50081c40b180c051040340004040080c40d599814460f000c19540e8005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 930506933 1250 930505683 930505691
    0xb0109080607030917070312050c040306090507030320070302101b0606030b0604090b040210090e2e0b160c051206010e0702030f040e040f120201020a09150918 70
    0x103210030140915400342d4001d64003ca0b201c40302e801c2a14508507040c00004021600704000d1000903040201c4080c15804c0240101e096512440c5041c440d0043c0da0001d1701180c10301902c0420041c0114407101540e00c40e8545030040342156080800103131694034403c1040d400040d0034009440d10100043c40381d00c0307900d001a20540c2ca000a83e103022240d0380d00305ca03110b8945034140700b0802c54841c200c0d0702c0101540d0030015101c00d1307110900c0c0c103000604040e001d403002d02e5919400a108079508030291064000204040c2404034002030b203003088081c8951490700e0b168611000c0181d40000d80700b103450800c00d141c1014015403001004403850082161a106180e100050b5a10342003c0c482c0003219980c007030f1505614001100e000030100074050021504204422510b540008090b039040e11110322414100d0380c1e952508004540002d0009030215032589052510312f9815001440001c029580e10031005a80d4001100019500e06401000c150710980a103c1d411800301500442903101c50049 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 930508183 1250 930506933 930506939
    0x9060c252904380307020a060b0d0c06021005091b060a02070801150906080c06040b070c1e1e080706050c0307080406020a0201080f0f0f0901021b010e070509040b0a0b0109 75
    0x901c00504410032403000b2802c5054083c0381030a40c0c00c1040c00a10b030402152035460003080c0251181c20300c480080289a0f1507010110946954007600c035031581c4800c080080b59100c4002959611001c00c61414507802c000004d5401e820112302550844c1c240d00f0f60041c40481101005032941044111408600c5800f50000e10351100f40070b040401500900070150f62405c080460094a80d16001403e07182c2c0505914422a01c4110446003199003002215840e003806151408800c1c90f264450884100071441c0310703041001090310070f0102c4280702d00001409026109544c54070444e8800c9071881e0700301440400259004800810180300000700b0780349000c91960720007072950480d80045005030b000586801c21560080d0300a508401e80c40410035040c0341003040080038000080c041ca000c01110700c045981100250103584060a407280740713803145500c00310840d00074810321244282030300c20100e0028403402e1443d2542c0c080da130040c09400c0e5a607986209007016102c400500d90400c03055030400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 930509433 1250 930508183 930508199
    0x603130203010614010f02010e0a060b120601030b0a0c0201050f060103020307090b070c08150405191a0f0a0b15091203191e051809060609060c252904 66
    0x109004c2e0504a440110300242103000406201e0b00c0d40c03c140c10342e0300d400c1c031000c0d50140015040004036881240440c0e2111a180496401064005c40f000c252194030004010030503030050207032080310103040400446030b011000300d013640c3d42522417580b041d00100204030f855200340c000310790251003800c2007000d0075a01d43c292026644007140a03070f44c444020300d050040100520041300645001d41807414141019152a40c5078403500c070224020006038501c880030404505070003418401c0500014049281002c0e000342c0a0340c0880b42c85c0110341c0341217031078802d515250b1390840d004c0841b03900550a151489060041c40d1003d4900000d06100034403414150b007581d07000303416100101d030742e844480108030b14040042106592016003441400d1011100b031010030074800b48181d0f421035440c41d40707841d000301003000c1e44102300480d5004100001c0c01c1c4c1c0c7c81003000404005555149412440403407260402c0b40c80020180078a012251001c0007041d41120012450350f0040c071010340d06850b080e595000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 930510683 1250 930509433 930509441
    0xf0305060a05060d0f050109060b030a020c0c0a1d090111090d080904110a090812070b3409050a030b070f1206030b04050c09010e180a02030f011d0a05030702060313020301 75
    0x400590981c80d45c8041201300003d00416006113800700c42030180509002940f0400d02009101e41c0c8040da01180045898204010f01c0c904c005001d004081e255440e01c6245000016458141100101c002c01098403080140f1070341d03c030100d003040694200720f800c45c10806800101e03202030b100104107002404442d03480d03200e441d013030f80300441c0c0b4155100c1007103e000d028180c3e254400b449503000180030301d5002e001c0100712410b05900444101ca1650f5007018103802c10568403489012406054551b0700c98071509a5a1200101c1da45502c0c1d400c5948408100f0100118000103100020030340204d0b039910f001e20324141040000d410b0542007040580c62501c1210000d034801d9502000500c140000c0c02824821501f08400035285503440350704100d070030030711058050441341c044140d2018a0070722100071b01c00070084640c000d0596489490200b8003a0180c0324261460070103a030440d00b00180d031300000800860455002d009581404e425400304040c03600001e080d00724082018483c2c0005a6080c42 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 930511933 1250 930510683 930510697
    0xc0405040c02030d02131e0b070f021807020708120313030c0c2102040b06070f020f120102180a0506071104050703020f07140f0f0c060c0a0519020102010f0605010f0305060a0506 78
    0x1115001140c9407000d160301203000349403059490320760700400384143c000740d10445049e250040e8100c00090740c039201068040555200751303800c642a0205005207903034045072840480702100300322941ea00300001c66181c1c9110940d001d4820030000a01c00000a01848404005c140200300e20750400380d8400140840b5600003c40010006602540d1411890035100e204814102594098109116969804079100c120301c0041d100b040200d410303000c2d0390b0b40c07001d019030f00c400344000035500c440300300c10a00d603995038002c4494440c03000020003262034108101581c01c0d450b04602c100740360652003810301c0300611010305450105074080192843d40c0614400500b0380900c21803d00101c8181c3c03410706070038000e5442c21254280c0000e507a10840c801e000444d00120700c821242655a1030040070350b1450400d24280040140c02000c080b0706040c20789006081460707000f038000780440d82c4e40d80340402c1103075813601807117011404044440b902240700360700c520303400440640081241900c510004040c0d07000350b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 930513183 1250 930511933 930511957
    0x11701020909090d0f090e06131d0312090f0a110415140a060e220f060e07080a02031b030901090818130902030a080c010f150305060f0c0405040c02030d02 68
    0x80013103144141c0c0031810840e50b44091078400c0b04581460b00d41c400420000c5c00c41e07817081e0007054408030b812039240d001c8903e0f045554080c3d9090980b00000b0350b00c94026203208411131400800181c00e0340000310b004441c1d01000c101071300c03250600fa0f40c0c401e0300349640348906800a6a828503001c0000c50840c0700c4015156200140c16411901c1040004086282e0490f1041002e0181180140d031920040704445503074000b102000c03080030785e0580d4020010701c40d1110342d19050540005050700280441c6000b502660f0b94650141c1d0340300c07524400d0f0304c001d440506c0d03841504a4400e441a900001075078205940d5400400d0114490300e400349281c20880000c0c2c209038244003440c0a070725080d14016204c03840048240301003011900043e403120752040d00035094090000751078850715000c0d0f0207403181c824014001c11160300b00c00c2c1c85240e1a81203000407a505e10a09010034881400081000d110b5125030590750310389420101070001600d103001e041810761000b4032040640e10700500150401011380c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 930514433 1250 930513183 930513193
    0x711030d09092406120b06070f0b0906100303030924020a020c03070f090908070b0c0304020f0103150b0c01020705031b0d080405071a0904090f06050114010801170102090909 76
    0x8020000c441c0b200300c0740c1261000448020fa00300c00c440005400320b604a0038119022030251004070301800510650b0b540c400b00000b07038502040321681c10310721018040c4100700140d0741c865404d0f99803080c0030b465840350360002c05001c10000b84a600a4455030380305e00d01c0d1402d645142c0d1090703141c0c40500c0d12203c5900d07401103500b00090340e0411450b42849011030061081a28101c5d000d1207180581c0550b400d0541c44901d040e050100f2442207880461f0301c407003044107500d440410002c464005490880c89100c0c000301080007588079001e00d01c40603200d01201a5141c0c6440242c03c0f0070b6000700c10001142d5022300294020410900182204007218404501190210300000703040c03d980c00c040905015402d0306000206400141c0c107000d44500b5000d01030f2107002102c0e005201c2c05a2080154854201206602005901c5c03451024042c1301e403400b8006a40c850081a40c0c07041d003c15020b0004000900402249034213034105044800c45070001071804840300080313007144000700d0391a5501c1e440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 930515683 1250 930514433 930514439
    0x50907030903030b0f06030f070c080d0c02191227170c0907051204030c0804031209210803040204240e0a15091509020d090506100305120711030d09 65
    0x602501a407990200c5d0600705e008001c800180c450701010b09020201d82c035a900040001d405803c2c1c8401c10b58000200c1900d503001041080040c0c08103041c1c000c0180528450b81c3d402c4c54820901c840940c1d4403415141c12955244d40840d00e098040c070102440840008000c22010410b089490240810f070302c251400c452482111440c1c18001c03140940079507148020803101d1343d480015144110f11007810b0341825100d6003000c880c240fa120b42d020f070420780000b900204006100d0f24046d0700e50125154000c5d0f050703440c080b005170a5100200e014295280c1410f030390010746400021940144018400503446010704da4001024012101d0f0103075070b1004c504180304c0b82622250059019000081c21300c0b144540d0390881e02400840c0c82010150ba07200c810460303101c0b1030a039000c0080c3c04004802c43d101c405020b190000f410702a20151803500590020500012180c410f00c3c0c20740b50040002d00b82341c2e14034150400d40c0c0e8080c420a41d00712040c40b12885480d03600348201c0420421980c0d8082075142 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 930516933 1250 930515683 930515687
    0x1603030605090c0c06011e051504030501050705030a050a0e061603060b07080a35040201030e010c020105150d17031803120a0c081b0a0e0a24021204030615050907030903 74
    0x47e00600d6060707180c2421900c010030440315034402d88105031040d480400040200e98003600941d0001405542004104940380b070f4040091480340403a11070500040c9c851a032101d0454856000c1208103410034000554000c520120360310b4130208519000902c0c03541c1d00100006504000c1d01120b10b880002607065145030b0165245208c615840e60000ac50807080c1080d41110104112007a035181c0181e000505581c0280e0101c070840c0c4401c0c009001c00040781000030f000b0041201c0403c0c03020070840100c111070918010211110784c1c0b0171101c2012690090152121f80c000420385a031529402d140c045943c10300f440034060611440c00c0e80c2c201e50809401390015a211201c0e90400c1100401c200810071081c0a000000d106076a41c0f003565a0150810880c0c1c1844087d11081e040400d4100019101c607181c2c0407840b1000f0b042c6034903007601c42d4407034040380c40d100d00e003030181c08000b000c0c007080c03000c5542d95000c2c2c920306966500c03030401315a840000c290011011120b10780445d69038000401415 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 930518183 1250 930516933 930516943
    0xf0f04090b03071d0126030c0a15021c09020406081b090115080f07020309031b03100623030129040c030612030e0d0503030412120606051603030605090c0c 68
    0x2c14841c00c41000071344610304080814420351960030070035000d801032206003c0032404880b618005580e51101c5082044d603450f028424100c131180d1210134005450701203071081d6558a040100300d100c0a0f0904401038002d030a40c02407e99000ea5140350001d10b00804000b0020343e00094840010300c1c0349075804001000da0705a200c0e108561401c5036805000e50307c10b502a0b13115214018140c103070745843c4070481c6140100c1522a0b014800c26504050402d01055690102d0350120220340000a5282c10642600c100307104a4036801140c0120a4511b1010780300304030b041001500003d501100395501c0410003200d0140003c0800d0340c2a031015640c1018011468001000d09080c08194074210450800c00345030400a01080001500100f80340d544880c00c1c080c2c560000c0c101ea44900b4a810b1803440c0c4981c0102c41700200d280341d0003a040c1250240a500102c40311500e42c50304140d80100b22074407990001c1800c03810581e0342c000214035680d4068005002c2d0914216290b12501c518120074904 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 930519433 1250 930518183 930518189
    0x9050a0204030c0605070309030c080a1403041212020f1c1706031b1c03030c021c050316050c07080c0319170a050c0114041e15020f0f04090b0307 64
    0x116004100034030103d040c169121040740c071540b40840d80ca4405013002c03a134030f0300907400007000b58502100000d0b000e800020b40007189405083c5211a004106014565903c80d03441140c051050280d004070200c2c07111410064200c10b54010b86801c6200000210704040003a0081e441916454280740c840940c0b02414480d03400200c1003007482800c203d40001d54400d1001032940811a480c080581c00d625038449407800c240b0f007501c5014494181c1d02c0c0103001303031030a641d45030300502c60031000c4001c801e003107a040398041030701d46c0302d031451078a41229034603407074a222001005100c0108124681460308004140080ca40c0201078503807014000105820000180031f0501c40080b16056100400c40000c2a41d44c00741008444991b20307008810709a600c0d01421002285551810f00300c01c07281c2c0303000c6421620440c13003510000c12007683e001301c81c21210107181d0050056080c60b40d158030007603c04e80c010143c04400c044950b04000701c40640700b0041e4419040f6040740c1d525005450151700b020000c1c1009 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 930520683 1250 930519433 930519451
    0x10051909031e0203211f0e01030f1e031e1107140301090c090f050604020c2d0a0c0f05031216081b0609070b0a17040510150905 56
    0x4188a4a0062264101e492008680c03042c08030b191034110300810032118036008400039019080f10600c005807500e0000c8640248843c210304900340d140203c5481d407816903905e41c0b000c802903429a10340050030300e01e104c81114250034001602c4c1c1401b4135880c41c0398001380302c1c2e81c1c1d44460034144d88400800203c0c0700388520a000c50089440443c19000c00e1020948128a580d1a03080d040d400020b40540501c180103052816140400f0034010b40c1b0350000384804000c1401845a42c450740140070403441021050070b2140c00c000c4040701d0b0701d0305100760149480624124030013605844161a4103264680e0001c661102c0740c4041085201d42240c00d805c010305080b00a8004248415101d0344140300307908100c081c080e40c403443c1070100044030381071f81c5a4201e00100481842a4440074076070703c1c178003912080340d54862860001b034060b040c0c004860300001241d50300b030f61104598410600e107180c064402c940901603e541840b410215110308021840f0900f0749401c1c041c50141240c003220006414040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 930521933 1250 930520683 930520691
    0xa090c0e19180f05070507030306060503040b070305060f060a050901020f01110301050d15020d0c02060901060b180303091c03080c0c1f1b08010602010c09050901170f100519 76
    0x20300000000304980c21a42c0254540d600c0c40014540d00b402084025015040180f03400d00340030141e5404000303000b00c80d03c00c3d20208407030381c1c454000781c4441c0021500100300380a00350000d5199480303034008940180f00681550103980240002035181c2d04609401c1c0d0001d100072075031100c40c0d0b0307042010640301100c0000800c80340310203541c2c2e140c40c0c2c0700502455002d903400744003080800209005850069038803a60441d1121031500d0031340c01a00340f01640000500c20703a00480d890300b0040c8568400c0303422411f0307000d2400d02d190140c82d003a078510034152903141c0020b0101440d103443e0701000850341024005407a80400d240d18014240c16409020307007507003a50600100c4080400040c0e424501c01005110f40003202d2454284009046250540c03003402d5241c03070341c452002d50442c51090582c0e400e42c009204074080004201d800c1c0d413a51080703a601c6860400100039900030240c034242c085c500c0c1401d48a0700303580c2c146982e00d00303450130305410010350f03481c0c0c208008100182d42c02040c45010740740900c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 930523183 1250 930521933 930521959
    0x4230c13170a06051306060b03270705040b0402070203070e0f1303020a0b13150c0206060d0f0f060b06130302100e061218070311090109020703051204020a050a090c0e 73
    0x660b9200c22040c0100b03055600e00c0450105004175032800c4c0d0b1140e005400b070061790f854072940001a0020f4440382c10314080c01c28800140081542a94550784100c0c0c010840715180c9002c120203480c00320b0782c00da00250708001d4000035850074401513015011001e5004443c2c00c040b0012020140000d02d5500003045104440300000d40c0030a00000060300101500c106494611350701070403901490004001002c88204c1600400103a0462a0504159025244142c1d04e00042c040416604840180a80050312114000030b405840d010300c0503000b03407000280d6629020214160350700050004058a291070010421454900605d00c203620141c17820702e100c0c80d51200411150b010304070300c54510682c072130001244150312221011b000004d01301101c1e0141c1e5281030003000f296411003030740d0161900c94008154410705008580b0105d51540e40c80d45808098088a4a00341024004a80c840203550300000c40b075441c506110042c002000c0c000a8000c18440040d00040116010354054100742c0846 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 930524433 1250 930523183 930523229
    0xb0712051204080c011b0305090708010605181512070e06010e012111030c0406110c150c0709020d020d0b040e0714010e030d09050a0603020f040504230c13 68
    0x40c0c2050b441110b1688480554010314050305000803220302902c2a0f001111b462907151f00b10324000c0000500b42c8440e030b5240d00c035840c2600d95a0040d90b1f00400010318a02c0c50040000d003042c0d2000d410380c0e10f05003010080b0b0000305074103140411460070741d000400600c4461001a080768202c00f003403c01100d80209080081c0160a409107030003160440130358030b0001101244c014030b110400d88501c095403441e00800c030040641190154200040010740f020351035000001c2c1004089030000c03c00d5155020040e1501c840394040d00d00000310b80a466800a22000c10f07001a200c0d0481c600000350700c0f110040c101c0d404540402c043c90344201d0030030f0751100c0081400300d98001550f045481c9100300110680c01601c4400d105041182c02d03220351403200b000d0a900841c400c0a80e1011200100f42c0c0e0381c1d0700405c03400e03406140e10200140d48200b1040007103103420f030310600c446901445900390800c032590300340034501001c80f02100185000100c161009080c284500080c2403114030410110502500c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 930525683 1250 930524433 930524467
    0x1407061d0f030f06101a0306031209180106090e0906191a130203060103060b070b16091716060207030503030a15050901060309020f0913020f06130b071205 68
    0x225400740850701d80506075614280440c4200350003038002c070b4825041070150103c1c81c261503c40c0d44600041e0300243c000c9184c075901200c0c02580010020032034501d601554992542c0320040706540280070462003820b0b100014240da00a000380d88130480704902d0110007045a184c0240040440d80003041000a002d505000003200807440c850300081a1210104001a014101c04090f074001503d80950300107013101d400842c8203940030390b010b000305940c0d0745d0300c8201400350701001000c034a4000000b800110080358114895151450580016070742c4154607269008800d000707000540001e10302000c510074a04480004200a200800700780f851078945980fa8000904110091500c8401701c02c001c14241c0355140141100800f210440c2d6541c42024008001042d0128043c0030301c00508090b51070445c1d40103202d103000800b0001d410221303508201c4007000b00442a948a00b0a0205400344041d04080320080d205c214031203a501c00303190400310402d0805403082c0d03041200c200000c00d00c0181450b5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 930526933 1250 930525683 930525737
    0x919080d031a0405220c081621081204170f070204050f01050607080c0f0f070608010603090213050604090501020d0608160b12040c030503030406060504051b0f07060216140706 77
    0x90031043d55161450116546103040d400090b091091803801e80042d110040c03c1011580c06d003040c800581c02104c00490b00a40c27015020b429074506000c03060982000b482aa030b4000d2141c01156103d40815010300556006907842046401011828400710b0030039104a94102c0a4612180300d00d614000005a0520400a00404c4400003280102c5a1041000305a18420b44a820703140c002400d001d8003a80c4250034403c3c10b000607449000020380c58060312400070400e8002e0b01320041421445056806403401520698000d5907070790f00c01010400a1024104031801003502082040c5802c0d0803916080b69026001003a11145c1410040d00300d2200403262092144510172560f95182c1c2010702550496074005081800000f0402c008c100340e9512072000d880b02140e0421290301c070324202c4e030304580c41a1035003101300c1010020001e40026440103044400c0c1301d00030140ca0b1801e841403811081e00c120b44100e4003c2b0f0010b070801e003030400c01e100280180c04c151138111a0750884800c50401046841 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 930528183 1250 930526933 930526981
    0x91211030f0c1906051b0c100e031b070f050306060a09090f060c02061009020903060106031a0301090b0601140a080705090109030503030f09010614060919080d031a0405 74
    0x6054403200c00c01e1080c2d800c0d002e5003c1503107030125040e05095001c0c01084600141032096081d9240d00340b105001a45e002e208424001c20412a100c14180020320303142003ca852031000f8081140000c11903051a241525040050a02c0d90714100110030003030301c3c9803c4648290803000030040039456814030402100c05246010400b90a5410320407541b503121070b0042c1c0764900b4111040c00941d0006280340c0249200a4510000c0b40c0d50f4010700c040380540c28015034150403d100401c200d51207a08100701a0040030421100705102e200064216610441c0c1215055034000802240350307001400840e840e10307401d8900d4600b00790390000400c00b2800401d41c1d028003801090604090348a00112005150f00c0340491390359003080d03c0c0f00c8003070080480e6401c020758240a008105078802031013008060741c01500f40c50a181d507a00410001c0264501406441d041b141c0c00010410401c0100d50781c81611a2400584c0c0700c1004459140c01e80307120400341c0180d05241c203004c03a4600c507440c0510220001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 930529433 1250 930528183 930528187
    0x1005030a0209040e0d03090203150405030a080c0c01180615080a1203023c1c05131703011e0302010507031b02040c050903010f06080d0507050c0d06091211030f 70
    0x4100050010804c140d6004c000d4420400d9064025805500c04a40f541c002c078111402013440c54142d07a000d5400b220000c103c1d4000744032054041e80a181055001090361305282c0c14103403a48002401c55407400d124140da420041040c0090050030301c81d4400510024105880f190b06008078280d8480400c1307401420031012002d081b040e02d01c05e03410740c0e4002c0b076100b20031a940040c0341200e84160440311340485000d080ba4082c0075501da4101c04071a90040c1002c884c580360b001c0e944a041c001c0600520030200c0c2280c5000713803c001000f0404086c1c03d0102e81c0040b030303101e5041c102c40030540d5801d1250030700f500040507800e10260781c000f0b06583c01d40ba45444c1c43d101704000d08540c8044419510310003500b080c100610204450340040140155847c1600200300d03104100d001401504c02a100c0c40c201500303d5041100e0b21031241c4020883d280c09401103800c652a01d50200f4480c52242c030064924a03601d208520400103090103050740c5a2151610b00c0c00c10111210041e1a48660a05080700c0100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 930530683 1250 930529433 930529447
    0xf1205040c150c0b04080318010c0f0c1b1e090b03060a0902010507480302060c150906010f06211a030f010f0506180a020f09090709080c1005030a02 65
    0x100d09103100983d5440001102117050603d41038200e500180d608400029124041c8a410b030014490300d41d40c40181c2e0b4a0301c1d0b04400c268400e480e0b45640384d109486c41c0064540c900003201d0b034104918000c0018903d9503844c000021615400240c8903000120024180400441240e5000905c190400f41d00c000008140210f0b200503101d5106100c4020b00301c204171402c007802c10499910101904400700014818040050384806499048000c80440403040e03038814805400e1160140984000c80700440300c04c0019003c0311044010308882900c016881800188030080b41c0c101e85800900c0703103041402c651001c40e0440510062224841040b141c3d0390415000ea0048103041921030060140c2034907104101d00460a02900e41e04607200300c0c481c01d000106420382804404c42c0c00110001000350250345034140d1003400380d404000c40d50501282442005081d5466545c8640510255100e45d080c25250100460801c1c00810102d445004141c480e144102d41200840e6130000c00c1c03c000582d6520 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 930531933 1250 930530683 930530687
    0x306130816021801061805221d06090d170612100207201909020306030a0c0602160b1c0e030409060303080f090721060b09070f1205040c15 61
    0x1c5201010394044030b00503407103082c0742e0822001030503038501e5582c4030400d2070710310f81d640c5015100d032090540000110035420322248091051070541d94002c83c000c504844221150281c06480700c5214105800001c10300151034002c2165048541079400c00110340c840c1400c5000310500001c140c02e00426407444d04204030703036084c040d0320700490f0120001c5460305101c1c24204100400c50b0480c881c0d101c540e245da02010700d000540948200e115560450400703040003040d40107134102400458040c82003246c1c10002a40c4250110702920150b4000c00250300b400603520f40c2406030307a002c88424001045030070315451094441401c8041441408605da042690f032062440c0708a6001d2040c46240c103001000701350307005541900036103d158010702141c6400017060745910543c443c10400c0076141d602410742c00d46211f403480c030150140c0030000f11640c0400110318002802c0b14040005050300d080d042c0e21503007181d880310307c4814045040181e481e140d034401d041c44005e0b02801c1d0010004003900c01d9614 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 930533183 1250 930531933 930531967
    0xf09020a0e13050706211401031e05060112021305100b0702010903080f03061e011d190311040e07080d211109040e0c010e0405070507050102070c0e0603061308 70
    0x9500c1811030b901c403a03580741c00400c020519031142c00c451429101d6080070301503a024042c14442d00c600107c074243d1841c1d564a0b409444036004003007a07481e0001c1c110200d6024080380303009009140c0c0345110394910f84100100031100d0016148403d20302010710210258114040c0c0c00c2d244c144200d07564488090006944c0405183e10080c031030200010011329480c640d101550007400107694420441520040e02c00845c0c440b00c0c0424009031844140c0d545414103000b402d54280005080d04154215891002076590b4464005a40c040001c840e5040c2e203003068400c1c03810400800001d04016408c1028040c0c88160548030380f0104010721444080d00c0445550544101c0428142001020750b003128103911604981041072250340fa200703401c00d00303820105801003032006c140e4580b82c140c6c3c0b4000c1040014400904000100842402000d00240f070900c0100700040c010340300e0b0585146081e0f040b2010745001454280070b40c10110034072441f5055610045a2594490034a2740c5501175036010310805 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 930534433 1250 930533183 930533221
    0x723030601030f030908030a1b02040b040207050105010513150b0a030b0306090a060615121a0d060504021f080a0207030221031501050316110304050904080c010f09020a0e 75
    0x18003a12000004102c0f0110481c4280e9109444191110f551020b0545d01c0f400758292138004112004008849240258100c0d0105840200002400000140804c0c02c80c0c00903442115685e40d92030050203a86016072140724550000f60051141c20076001c07205602e607040d0310a1a40e509408981c240c4958042d0300304070400035001d0211202807405d1035407640c0e6600d8190082c1c407281e10784080071440b503226402d40401d90015483e04c4a03c08955128940100f40810406d0300000700910740c0c214694400c14010300d081c2c0243c9022409060500410140c541747d14600c1040318150720810314420740107a0300f40e91001c0720680050302d90015050682c2041da1810b6103508805801504002c85603160010318001c03501c145c0d000c148440e03590015501b80c44107403141c120721504101c603100c280d849a007800900540c0d07102500d003441d035214041407030042d00b41d9044803000343c04140c61001600c2441000711b9002c0c5180d0512484040d60007003511412903000c1c206045282000081c4400401d100d911b40d2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 930535683 1250 930534433 930534439
    0x30f09060714010c2105010e04030e13050c180a060921061b030e0d0519051b0c030f0d0c080a0201090b070e27070509130213050406170723 61
    0xa01136480e2002008641d100d00c1e5002c600506100040400b0800d00c6441c1c146d03103142810740002d031038580f01520100c041d9145039600442c0d81011060401480c080c06024642548025488261402030242651040c0c4000360040c01c01d080708004d15a400380c41c110840340c52404401d4580701418907054071b0449248003510380790528001c01380480c0a126a404001074550b020060380069088080d1501c0b104115240000c006002c102c0003003400140300440c0c0380003800e000386001d142c4a40c007280503c000c0b500403c10f80100030000401c2c1010700001d0b0342542c4500103007030740181c580c002805549000300c002d410f407400865425a254001d6100701480e0b40c02c00c040003130314680200000c048603510241c00780207186801c3c504110080c880540d907520445211044440d03070314050304481d03a0300034200300c0754000c2e445458031102e0030840c4002c0c20420288454080d42c24107000501050300c403c2c2e44041c5501c100405055900314010840d0f80a441c80e0f1020840c0c2030b0141c0e41c1ca10350400c00313944c16641c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 930536933 1250 930535683 930535691
    0x30306120304152303040c051c0c0b0702040c02150a020f041d04020406170c090402010201180b0108070f080c010e150d060510110d0f020a060e060f09030f0906071401 73
    0xf00c03a0b4000044601d440d030130b2024203040851910164516000a8070700420100310f1040900291030003410350081005986031405000c60a61150107075100c640d80052182c500008117801541481d009038205a0b0f9903000412581046900290300210001c0c0102e80782540800c0c8030203407211460443d00100031181e08410860b0b015181d0342c41c200300965080340b05528003240040d04090300c43c0040304803407032100540a41c61064051000c1e00c0c00040089046541c3c4543c07a80c4014024a5004101c0d80a40c80d030013220340c10a0074240ca05182c0750801000d11030103034000c02c403020300069800e100350b4083c600309800c2d8507d100418120024441201c207144404030f400920115168441002c6840446602842c00122001600c1c1c806a40d2440c1140e80c028405400449010350380ea1104407d580c4100d0305403203119100c0604860040d170006149401240910244c045500901034001c20300360051403030484403a000a60034801c42800701c0c00740b20049085814082c1d000201031101c0c0002c0000c1c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 930538183 1250 930536933 930536969
    0x12030601050d06060f09060807091202030115081015030b2806060e031002030c040b0a0210110301082427030c030a080a0207050307063210050d05030306120304 70
    0x1405229500c3e0030117000a01e24507002840714858101c1c20b000e260507440e09140e07581080c0540409030302c640b8060b81c00d5901d8042420820342e40c00d149100900030f00000c1c1c5100030140c040502070b6a00d280c07011080c0c00b480c41080c4085501c3c2c0940680080980c59602000750100c2441c000202e40200e544080390325000d00020555084640e480b07801c181102500c912521060100381240800c0e0360284540e80240001c1c812507540c0e8000b428030850324011541000100810f01d020340b40c4c1485400c2e140d084c04001008891010040c0305e98840d0035850406580c2c1203807007101d0996000800c46000880c00d011a035102c051020689000c42d40c024013940d90740c2e00041c54141c2e40354498040e0f0740c0040d9014001503040704041c4265008158400d004d1442e001507038031001d000d00340c110300c101c2d80070462403503c0c00c4940468100a03039041011040e80b480e850900c0c44004403000d29404580610000007e0200080020045a61141048801c2c00e0740f500d00c09091851400345030080348480c112107a5030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 930539433 1250 930538183 930538187
    0x6010e101d06090601020f0d18320a0305010c090f06020312040602031810021809150409060b09100609060c0f1e0503031014041b0c11032a09060312030601050d0606 72
    0x28807840e05050503034040c0591740f40420000f80c95130019044900164ac1c50841c030114940101d882c151500030b040310b0810303481c3c1d11002c1c03c4465440d0050b000c02e4200e0b00402640c0e0800c4411802440e09001440c24007000a860b6240064001c0c001080305500000244001618211104010701c1010849801944003510603009611200d12100c1c43d81c50700782481d100c0d151216166214081510b030a0560190403424800030b41462a02203800c251100320459180e101c01010078801c41c40009051115494400301814045580c2c0008042010781031400002c100c1c44802d844282c1c1d40010a021001020451500100c00c0100010441d0200000340000030502c00d10900549030071291040f8001c04403400c00c0126802c105190880c141020341040c40a0f001c3c4d5480007110707010700c1844a030703443c030507001908040380461054030b1619562901d6201045070070740d40c02c0c9040282c46080060400800107035860941016849004c4c82c004001070702640b080341070f960840080e900c1446056224800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 930540683 1250 930539433 930539447
    0x2031302131b181202030a1b170d09060518191a0d0506061c0203071e02011e05041716050106030b040b070c030e1201020c06010e101d06090601020f0d 66
    0x1c10306200d02c0c100401305a45102c8001e0003441c0d640103000b041a02159510100341c0c04040740058003514403c800020028003075001c0c0001c41c00b109001d040c400d004001d01400d0950030707400c00d070108403042c464210f4201c51214030401000301181c0c0c03401492080241040003117050b8000390704420501d4034140c65010710601804500ca01c6144c284103599070202403000030b00804a0800700741000580d0a07924800307542c0150782003030703152a042d100f0304a4072504e48090082c40c001180140c0d942c050000d990204200d40c0e0a80d52900c88041c0000c1c02c4c252528012002114804d011011001503a070800b080442010001d40364032a0003400702641e00d04000b00d500a04a03000c3ea140542c00c00016250f520601551a40036410340300c2900c00b2111a044c000030307500e040b40c07003840d81d0f50070030149649800c1000007600a20a0143d98140d030b1801e0401e0742c2492601c1e501091140e95101e1441007150400c1e10b0b280c0c0d00c06c43c2502c006402e643d580004030700e05104c56860034030a00a40b40d11500c5140c2c030030741c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 930541933 1250 930540683 930540707
    0x310050f0a0e0d05030a09020307061e0915260a140708040b1b13090b010e1e1e0405040f0b06030309090f040c080709050105040f02031302131b 63
    0x103400e14850307907250095001c0d244800840c01c01c5030805044034281c607014402540c0c100c1c0368804001110348080c1d0109241170714541218010407010460150b5010887c4004a1100c01a191101c0f031240b80203c0e490b00d042031400f0388010701200c010490304070350311f0404408401c416440030103260b080c06072000000301000d030888c00b15030343c10310001144a1f01408406008650104569201d5a03030100e80160841c061401c4040d43c1340100324075036026400402c90f40190a99071b43c00110800c0007400940307024134100159000d00e800040c10f0381c59443c112491500b40c002a240001c00d4000c07504005404841c1d286900e0b4402d00c4c2505000c1801190301d2404211403203081798560680350402055500e00900c0304990b800f03a944000204521b0705081c840750000e00c100c64200580e51103070b207082e08007803043c1c00141d5110f503150010032151805007e10b03038403149030400441c031b142442c40340d1130005e1082c8130000e40100642e10b070901c04595241d0001c0c1c0c00071001e45c01c2c0307211401c1c00f445c003d1081c49448 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 930543183 1250 930541933 930541951
    0x303021b0904020f03030d1434050c030904061d1018091506060c03080f16030209130f02040303110f030301051909090b1807080d1409031005 62
    0xa05045a94101054030401001022031190355540d030300300b1100c0d4580000c0690503000078401d00d403890282d40280754049080b44040b0000b40340c40030349440511a01000c00d482400ca034021200e40032002c4078620b02c01c0341d451800710703554020012054950321480d80e10941040c0351820018030300c030400301003c0c1307800031161200406807186065011240c0e1180106107a10803110501c801004890780181c104900c902e1501052050845146088070415403029001c40c0d0500003540425600050700d42d440035401105a4003405d1210510a10782c1c00e0005803000c0c15030000c2c0c1e940d8582e448950443d501d5032107180034410685490007800294020340300840206102c8a690a481880440c441c1a0380070080021411686090308001d010301c2d04440ca02269444140041110201d40c01429015030141e10022618100000103404540c91070480841d46d8001200912198001285a0920786241d261240060003810102e07002480789000c1ea5915120310360110340c0e0041d181d001036118070035403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 930544433 1250 930543183 930543193
    0xb0d09060b030714130f020c060108070e04080a03181b170f0a0b18030403080a0e09060904292409070f120905101406040603051f020f070804030302 65
    0x1c10038955948500d00440540015800c0381110a00b401c0004040800700e10b0404110950403624034012070340841140d06041d0040d00c018854132030108060f40041c80303042642030300e40c680790301c550032240903031107600c41015140c001d101d148241c40f12a085070207410189061400d840040c00141804e4140319489509900018074481c21401084c1960141c1164028125a040e44d690300c5841c0310009140200c0000129807200038014204041c1018510807a409a40c81c3c50b101406401000c0c90445140300703120318400c104c07594441c0010146c00540c05410403041405c0d140c3e060559041c803010240c09040124200700c07180c414080100e54100800c14450f0608540a0610008940c1280c447d00030541b00400340301c0c454421030840c005c0700241c1d8800285c66441d90b0f11b403410301d10042d0140c7c071625290703414400289107819003681c100c10100ca08104051455035156119248c0305182c146144907800d1101401d90b40d81c04403520041400102eaa4541052130500150341050000703500510034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 930545683 1250 930544433 930544451
    0x7110621070305160f0903080310030c0608011a030108101e090c0f0803041d07030b100c0308090102031b031e010e0415110d020a1e05220501080402190b0d0906 70
    0x44017002c0d00324081c2c0d40c602099500315100d01c00c141d840541500104e552030000040403400c1008014060b1002e55513805165240010340311044000060500ba10030341000100810301000496086c000c0014501003055806040444400c41400c031800c580c942c01c103000c01d0308001d2440340395426212245c82c1e00c0c2000d07441d0090700341c0e80d025502a000c0300208850510541e001440c41c3e0070345c40086880c2c04500d078003040c0080396040c1500e0b4468004680c0d54a092410560000f210951202042008600707520b0040010321a8810760b4040c40803900380000410f0b000002800303100030004000390365601a59481c601c00d402d4200c02c560036107581c100251210703d03000c43e80c010340b80745005800710181030041c498080c000075480101c0140500207442411002c5034101d030500218140c0306c0c1c440a480c2d00c042c0b00c03140c440f0b0390420f4544100800f911010301c42682c108501a8010b50140c2e022212007011649951041d15030780c000b9a07154101080011000545802803001e0358403400c014800d04034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 930546933 1250 930545683 930545687
    0x9052101180228090c03020c0d0c0b010b09011704140f0d0c0212160e0702010b040203100b030423010207140d17090c0a0b07060c050711062107030516 66
    0x4036000000e502c03a10080042c050415000c06071111030710b81d140d14560300c44d41d0b5038140046401c03070031082022980100e242c64020006002015101e012402c00025446003503a03402c03070700401402586914003010800542c580d00c5a030310000600d40b01d000304803403403c26080054541c045034072640c030507208010305a0102d00c0c000c80c1c1d41420258a0700c501511030034583c20040d0003030b225404e26038184141c1c1e4030a4101c4442c044544028a10301c1d29501d001c0c10718100080c29555801c1070640554010014081121050300405085800e480030b880d4498880d85400042981c1895814030f4181c1c040c500422182e030194020308490303200d443d00c20501d408840c0407607120690180307291302140c03902d25a0011007100c0c504466000140b14180d81503071138a00d0000740d520b101d80d08482d800c01c01c0820007104000e0103100300100c030451030030142d0030180196035000200d141c225202e0701414000c907030140d042d812100c035107500b034498501040442ca0007400080082000b11195400040c20f1414402418 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 930548183 1250 930546933 930546971
    0x5010c2f03031803070506070818010e090a0b0f04060305120903010209100504240507020112020d0e0c04060b0c0303010b07030e1c0b0a0606270b1317030f12060109052101 75
    0x281e01241c0181440002b02200c940d000c256003015040c030030100e44480f0035940708006588206d094240024901c0d00b61010300244503600d240503030040345050024130100d0b80008420100402c41f41007507645003000400f00303003e07004002949400100300d000c107202580e00301024100307503a0700c1401203488840c903110030070f0506141559000890000c01440d0059407040c81c3c442c1ca00c0d59910300240c40d0902c0910f06000701d59000c04581610b402860001d185440c2900441004010892042d4100003001101544070720040c851700700c44042c006420410103005502c1054424001010111001440c44400d160a040c03441c0c200c0b403c5c45008009000c07042d441c07140304165001346d92102c6c82c40f109420000c0f0b6071000046561000c6034040000280359010800401004c105444208811854040200d00c4105801e5450300e0ba50420321100814052080540354800c440300d00501117030701d4040061315407c2031038000303603005046d0700c2d0315103400400c4070065042680c004c0d000300509044101040007071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 930549433 1250 930548183 930548197
    0x3170f0c1513080d05130c0f230a12140d032a0f03020f0c0f0c0a0f0b07230f031908130609020a0b0d1505010c2f03031803070506 57
    0xc902880b4100d2040701c194082988085e03030070303009086c0000a448004400300103901c8441140306c1c0b50000e100000c2c41001c80381b003580450342504482c0404400164550701c41d80180c001400409a03844d080c0300881c02c100190f0090b4909503064001c844200a0240803100302c0401004007840400c003944440400e5004404d420351380e980600c108445048001c2d610078101041c000c4000c0c031070f018007000140181e0901c603000e18000d00b44100c03820244180d0701440c0c2e000f0340c50a07890307031010003034421400201e800b01513200d1405040c0441e40015800d20142070700520429110b1f0218040e801880003000701400261640702c2c1565607030310802224a1403040710342004c1c0414248800c0c00203110394001155082c40205100041921a000c2c6003540d001322030f031409400c0d1100307269910050b03100b207880b0140000307280915945200e034403440488402a00d000703503190704200480c400310412000301c0742c80e104002e0a8907940c2203056a51845c1183e941100d0f0b10901500200040304d144c0341040f1000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 930550683 1250 930549433 930549443
    0x403030e0f180c0c0709060927080405040b04021b06060a0b09031009080f030a20030420040b06040f090c0906090e0403021504080315100903170f0c1513 67
    0x12a9964034040f040c84c0c0195841e4502c074480d508000c50f03680c0b000e00540011300100d0700005092106520720094440d4202540e1080c5a050641034001c2003d100c02c503010303194196008680e40e500440410002e22400c03241030000b04040c5251402034201080342405820115240350840d42c58600c02507151160448041c0d155100b548a40c5c1c118040da04104100d41c01610390a08208180d240304c40254011520000210380e0f650b48803034000801e00042549a81e0180028107506c1e03d90341d00f041e490000e171110310a0480b0a9a10925540c482c1c016008413080a4042130710759688010b4200d8140040c020901001e05184000c07038403501c1004280704446890355054409403a1039141d442103c005031013036003103004425820390391203a0008000d002d5841051155540d203004000c4030801c82c10401e14901c83c0d83e100042660507603101031400107030707500200780307800c80040006002071600c22288200409400072500f941d0521000c0b800342c0d4100c0600f88150b200b0b90710300054108818105d00c00801c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 930551933 1250 930550683 930550729
    0x7092313021f172527060e09060a030624050907021f1b111b09011401090305120702120307020604092c1006060e031002090102120403030e0f 62
    0xa40402504416a00100c5100c2035420342103a031510000e204c10103800e428007240d0f4920840b2a6203204418001000e80728100c1c04d0001e908140b0024081188403c4003407107070b5078880115034255104066a002107034840810000520002c46080ca000c154040d40c0c2458036506100003001c2c10000c81c514800c80c80d550103001c540200142d02c8400c590880614101960b03501d07441c4031a454006110a00c498403078950440c1c40c01d86011075441d080c1e9814182c003900103580d4441b03569440d0b20311070606465540329400c2e180942c903030040320350718071507400540740740300c0c2c607594083c034203c0c480040210358006d070345840300303070045010451352441080700080d00400100410080d001e140d034000d480c40c00c1e07003c0304038040706148041103c0c40b0300c0f00011032541d9003010f11403154a991034480d01e4001e21743c60500d5000700342c1d504002074070340e00b40c1580e03511102e4001070f41441c107078428441c01941301420341d000780d2500c0e01c9060040055403c00c81d500d000700f41c0361920701504d10744032424801300600290848 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 930553183 1250 930551933 930551957
    0x11104060c080d0905100e030a0905060f0f070b010f0e0c0720210d030603020d02090403090b0d0c020105070804050c10090906081c05090307092313021f 67
    0x350180725420098880d0744080c803841010700301500565140e1400303600207003941000021000110342000b4003954095000f0000306001c42d030046200002c64600301d46a075120004c0303521052062144030803215880030001448003c100281681d40d059806240c1103083c29078813411400d143c2d04081c4c03904c09880c0d800340a0080084d004406200c4403000d603242c1c00008598403404510082c0c9900400f059404400d41d900002d2a41089080401d080034682404000e2030354011030310030682101c000e405036060707070700180a050040d4151401400c0c1d015000750344004000c00800107001458099005500b400089201c507031042403c0d40c000c0740c20001030f02d45200c035081041081d40e4448000828494883c0000841c1101407162000515640380070744202002d05041280c421a501c001c032050290521001500313460016904040c1d45401c040014010380b500e5020300381d14105083c0460700700d486000c0044511a52882e0708105100340c0e056088044045c04100061008c0545c510000300d41e41c4442c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 930554433 1250 930553183 930553187
    0xd2001060b1b070f08061501080c1c060e01030c081507050906030702100509010f0501080a0b1603020702040c0f080a14060f040b03070f0f0f030c0b0708120709090b0301110406 77
    0x2070341028102c01200d48180ea98201d03010010000d03401400c440d008001001030144540e26001c00406007407038040319603d032808401c1410301501402c40d88100019010705100502030b40140064461041600280d680d0382c0b030f141445c1c0b4002d000b490428011500070581107030f40b14040c40d014031303034a898403800e000e1504140040c9400040140c0d0440c4a01c8142c244c2807050341c840c01c0e0280c9815000407602541d2050306409a03041a480002d40b544855050f10204500e10210f80e00300100690b05122146001c508034064020000f0203940545004146619641c20524121005400703881d40c074415510800e00c502100c0e8000b400d0002d090510740004d100d0f1806001c2c1d041100401000040e905010102080ca440019017111940030b403402c005104200b45682c1103030041541c102103003566400c540d11500b400301540304003a40541c010507150100000401a150b004840d0032109031180303000c1b1402404110940326541c10940f6001012130700d404e040c040c3d2005615904600e6141500d0a081 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 930555683 1250 930554433 930554467
    0x100e13021512070905030106080601081e07080607080406050604020a0c03030510030605040f0b010e10090b060403080d050a0e032104030e03060406140c270307080d2001060b 76
    0x22100d0484001c10100141a0420341c1c030300e00950060340c4011301a0b04203000e1508440c0e00750030600c00e550151f0010800d4000000d02003403450415103250b11030312000d014040c44d0007190382100c00d16000b080c00f00071240c1d90000140707110354055081400182c8401e410f00c0100d1040c41c040b5800a0708031500003000c640280c003ea6040386241a0062010359261030b440100d41003542c007200d1051450098505002c50304192501421126900b49001e041c008595200e0560b54480e902d121500d80c00300700c1e403075076070311007520002c2da04588801d070341c6e0480c58800c1c0300626088940d941300d0b601d40040580d10700f2000090b81c00410800e8000c07001004007046003480114020011001c1003611801415207480034016036002c0c1e88240004103c00f01085050000307014004c1c020600401c0610100b9004a075048004015020b8220280c4c483c000f0032010034203003541504071000030302c034407440d1602d4940c0c45030401860040764040780c11400c0d80408103500303072042131103910040c00c0d0034010f0034480201c03044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 930556933 1250 930555683 930555709
    0x1030f02040921020c041a1311090616021e01051b190c0e132102010b0402031302131a0907021014010501031805070605090d0f0803100e1302 62
    0x180c6a003d41c03041084070002c0b6207482940010781003e00040d04a0801e4010303150848412a07000b9030406240380401c520400b4002050380792511a1291f0b61441044030072034a84000c0074000e19515010f00700c201c00c0c802e220060480c012201c903209819410140c6a8001d2300ba14140c3d2050300e024a5000001d411000401d6a03844038003400c0c82030b000c0204261001d4600c00c3c0f00d081030b018113a00c0c004d40c006140400401400c1148410710b18100007807040da10510040346800c6182c1d140282480b02240144000c546c1e01d50400c0c0b0020612101c40b258080d1141c4461013120040c01140c600c50170181a150307101c0e00f0342100100c08044000b10324202d0f42c03c590083c45881243c29103801c5080f00f90940d040c400703100b80320071030000051126581c5400f91640111406e06110200c0865951b15940c0d84024490b0a003007100105034100a5602c60000300c0084c4d400625403014201141096541070303100355110050502c4083c030000c0d071800c0c0001110300c520904400c1040741e0240b0703000d03c64480c0c0941 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 930558183 1250 930556933 930556943
    0x1203110d0c0e0a0602150912070602030408130e1504020c0c0f010c300e010c08030c0d1401140901060c302a0c05120a02060d0212060901030f020409 65
    0x10b00311882680301d0001080081810358018030550724460034035055004090180c4002e0740040c0e0300c14410f9542541120380169202c4001a80d0343c0d0350b8182a01103020b02c000d2104061f11a20000a41c0300d01760518500429901d00203a0010a510b02040300300c1c800d6014003115508040c001c041c1c5450140e001210030701040c184205096800c0d92080c09115078005150360a0440d9440c49038000d44844d2461042d000600302a07114642410000c3c00320f40c4048070040c0754400c0003000507503440300714007520018440c6131428407030f044100c02c0001c0d10340000d000d958030030501910414050b280131040903048411903120244104041d46500210300d2210b00b016aa00f21500b890741951070b4000c030140d880c4642a521001002c40310400c1d60081e02c0d036107007540c08441c840076802c0c02007080704111b102204e00407650320350540b0364030070f0711030070300c4400c140180d13103c01e01040e1108483c09680040c0150a0340e0149460940c4e2100f04000c4450000c3c00043e103541d07400481d202c01801e25500c0345551501070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 930559433 1250 930558183 930558197
    0x9150b0304060b03100e1203040302030715110708180121090305090d0311070e1501050c0703051507090902030f01060c4d032a0301020a09031203110d0c 67
    0x2150100c0d241c00000c1180303d00c20780d511803509807004828403d442c00a1f4802c0c01451650500f17490003941e0f4000c5c1c1c00c1c054485000b05e4801100c07904640e101119842401051507200d5849040007501030300220411105074160401e014010743c4516540c42c9071440c03981c1c1c4040b014000c464064010700025130200c040c80401c020340d985550b00c007800e60f01d289200b55541040c02749080601401c04000c2ea000280482c99001400f00d01c0c0c1490a0740c0d03075619020703e4100e07111021441ca40f4980ba800d5480a801c40c05803900f81c614400c006058140b0035202500c03171460807541d54018400700d100840e40403800d4040100144802c40c40b40703a501d54001e016040700c03104400040a43c041e01d10021405d00244d6400b900010301501c0d541c544210482804000501200c80080109481e0b40810020802152010b4016500c409503001c05085000e8064000c40d165000c5840182c40ea501ea404190f4402c2060600b850009200f03004074030304d4034215203000307007070200300c160031806024080c176404144015 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 930560683 1250 930559433 930559451
    0xc060712051305760303052703030402010c020f041401050f0102070f0611100e0d0e0f01021f0905011112070f0806060a090504090c05030709150b030406 67
    0x202d000304991481c114003100000d80c0c0111a844c600c0c5561103901c6000c901034107074038881d6101084c1c1040406000c0d8640c400700380451001448000c282120b4005940032140719800703050f81940b02610070700c004104007a40c5488030030040104035030300c3d0922159502c20000034006501c21187d02840c94400b88c1002a205804e10000b000c1ea5148441c0311414001302d0010891032526041100302c0417030a001400384c1c0c074140306071004d04e0106401403405104001541034070401040040d441c01d00c0c4150b0041100452007024070b5207801195242c0c1002a039850714a1483d0710309841310741d104500c140c0040c20701c90901c80c24010310100624070381e12510307134400c40003012460038056003042c11080309400342e80780d04a04505885010140c4000100b1400c4a2004885a0460103254000b8000c4444c3c2c1d8407003180110031100d03283ca83c1c1010b50010300344001c3d00b040081d1900400240e6500310107440e40c02e6214a45d1700300303c03040e103610f60001c083c2d10442080360f100401b0040da0010300a110100c5c407006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 930561933 1250 930560683 930560689
    0x4020405040905010516030e0705100e0a141f051b010209030d08041a0c030a050a0621020307240c1104020301030822030f200a1203020c060712051305 66
    0x149040381a103030ba0751a0750810900c00c690356102c9004000c02d0504000480c41031445943e2009c1c1805098000c408076010000a00d000d81c90b240c10091002303001e441d040b9206c0d04880d101c1c050011000e401801c600200f01418405514002034401c2541e41706804c001c0306659030030a0802280240246550800c00400c80e03403414810300001c071495403200c50060900745000440c0c520b0440034441c0701040d010a0020340a103403000c03a500f128202e40080f0b259102c015440c0010b2086d079000f5a41c3c0000e085840a0321004052068240e034000c50540d4080740d51200d048401e8400f0708640e00e182400741101080d0700c1c3c06100076806a40c0101c6105480d400c40030040b508a0b4420b03041603410420124540c824000c1054846840400ca036500710b0605155030b40c0d513103440c2c15004000b00b07000c031002041d2000348084003850400300b00040040c03d010b551002c1410842e802010181e00500400010400604044084503825640100103031803a05491400f19480d80040a0700d6060b81060400040c01b55 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 930563183 1250 930561933 930561941
    0x70f0309030c140316080705210718150501080126060a09051b06030106050c0307020a0320091603090c0902030405070603050601030b0d1e061e050f090303010303030b0402040504 78
    0x400c04860741481410000f01301460030040360084007804942d800d0900294001107090811aa000e03101031140d8a079002c0143c070711202c103882da01c019100d0003100041000007103410b00d224081c0d194007088044001d4841110313500c101d0255230701003030041c00104020703641c1130800180c40588110040c28164400303030003130130447d059078000c01840c3c442e10440107010702400403070225000b001d0300ca2107402400c0f022600364007051040da001d008002c600790b0940f88061040b0b51100f41e00a1180805a840c1e1524081d08001419907980d40110b6000700b8a641c2030641da50740c003034440050b071091888194101200a00b0500800f02d9440340c0c025000102a092400a0740c0245d01c1100940265800c0c084001c0445800070f1015040500704500c003441a218890200b8246401502107924143e110740f452a03002d281040c018102072609910b00d00d044c1c0328001032180907000b044103102e1904c401d11010114401540c8800d0f0302d41040004000080c0260b1184000a0018102505040d69400014121 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 930564433 1250 930563183 930563189
    0x120c0206071406090307031d3f030a0903060b0303070507060206070f0806060d0e12070309030b09070b0d0c140d0c0f02010e030f0306030a0f080c01050606030408070f0309030c 77
    0xc2c0154140302850390248681540b01424000460070180c05840c0240203d2451100302d10b004250782d90343e64641c54078039290720302d4500000c1c035109489600b0720016484107401013140c06581030000f03824900c1c0c0080100d44010b00a0790740c00c2d4079141140c4401d0010600007413a15030500c010008130001030414480000101407075009000a460100c0004d0840300c1c1d02c50604040164040400c4080e03540c00d0280c03201080c010900003200c0840b070072901c2c07a0548038603265111003008030b030310810550322104001c12759104807003200c510740741c031039401d50780c1c0d0018025408415011300002e60303038110340c1e400403082d22071528000c181404401e00b9046954000511403c00b0341c0c541c0702c0460a941c0065656000c00702c2440200302198900022503202c1c040d03801c580a400200001203042940c04004c000c2015400c685036407d5103026190043d1990301c4100386042550921000540c1303442c1c89410b0300c1c4126004814a8a49100b0b40d65040b241d0307100d01d1080b0107003c11018048003083c4501f40140107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 930565683 1250 930564433 930564443
    0xc02030304060c050405310e0106030302070b07050d081306020301090e0105090c031c0215072303100e0403050705060708011703031303082d0f060d0f120c020607 71
    0x140307041c0780c10074109a6499000071400e20000b00303c00c00058030780c0f0f544035900420050006400d8422a0200400e00d818503180c3e9024604008180840e54019032010003102e200c0e40840f20603950b03500310000c8a0250944c0640190080e582c0e0070a09405801d09940c0a02a103081018050450382e40f00e007203802c280c0212551540d03d00e40d1410b0307000d091148a4022491100030101c80c203e50f0300007951a108503d80c0c1c402107004000c9851442d00030000c1c1e14000c2c02e9103510001c41c0c41e0802005020b041760150203006100105207844440780e00408480c0983e91003001001c1c1141806120390a8080280c002c0702001000c0049401044003400003038003a41440c0d5400095500d84502d05160051100303240c510b0360020002e0208000708180e03807050581e07040c1802142c3d43d44810352980e88046d92070380f44915200c2c4c2c04203890501c3c05602c0c4039102e166070801c40d0358251a103074148807120050f400b00800310400e8180580100c1c101075040940030403103140a50000c405580405c2c001e030001c03030007110303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 930566933 1250 930565683 930565687
    0xd150207081c02090a090c0201230915010b030c0a0908030d0b030c030d0c060902150706093c08040902040b04080105181b15071a152b0203010c0203 65
    0x500e190310b4074128504011031000650034486600300107070541090744100565151744001c0c4400b0302e4004e401c9441000b4280c02406601c0811035000c1000c1ca2046455034080c0c0145440340e412800040c840368183e401022078541190744030481d4800b154081c400f04014025401e60014110b03200b000103003508030aa0354042103007408102031514100c0015002032082d0007148001c040107601c42034000c4025040000442d070a10540081442404800c28003043c2c45000142c06050003015000031020718400da54150400403500c500c0003001800c0b40c50302500b04400d1080e112203030380c0030110401d214044d41d20b041c506030399008a1030480e8459448070340c2c0d50a000c1000c101d02c204c2803260350f0740005003107205007040c10050f0030349840e48209207014640902c101e20340007858403120880c0601c050a11944ea5036100c0313138105241400fa616400d00d0b03100340740f10b0001e0300c003041414440190000140c00748106000e13000100c1060742c60603081041440c04414500096a0240200004080715401440d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 930568183 1250 930566933 930566947
    0x50a091511070f060e041107050d020a03020f01050105151c06091a0303031302191208040323100e10020f0306010914091506071a1618050d15020708 65
    0x18200025a030201d405111010401c0041385e8002d00c1034a900e483c00c840010395050103410761000c900070701e10b01400b144100640083c3d940c1d000030b08104624000d400f01e42d001c030724040030b26080c2c030401d00030b950300050300d180d5401089507030f42c0c094010312101d039404c0203400681c0050f24003260200c0c2d00445145854018280d6100401951a0700094050b4051f6207146020f08800c03042c0c003255603009000340080b05101c0d00f104201009000035184500307003001c2e80480341c1007100b4070390085e0009599400000005500304090b00f54a81c004208200242603d181c8450500c4021300050104e81d455000301c40102c10100001d100402d60f0039270248070f098880c03c290000400c0706a40b50006480c0c0956000c4246855840001c5540d0020010080310f82916500d0b0109206d4010f0f000018070107400340701c880010b41e401481c61480b42c11441c0c10307001c10011a84003229900e50342c0c042007201c419100424081400d001d03e405103d6800b510200e8040b80810050b1012a4401501605e03511004141c4c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 930569433 1250 930568183 930568217
    0x1110f061f080a02120f07060c15090b0a0515060d1413080919211214190504150306090b0f030d0c030e04060b030103060c0503040f03050a0915 63
    0x40d691000600016001c41c034102280e81e6500c455488010303108403118020000d03141020410f501c420718104083d07036150b42e03072000003400c0c40c0794525045420610a02580840c1c0c41288188000141c0000c202070341030310368034a0000248009496000000c2d0490885420354440100400340404d040c000091034800d10005400c9945c0e0142c181c22a1841381c440200214101d4800d8880c6014110b40b100e595810704000c0c1d080d080199440701080700d00c004803164503c0e95480d90031291a00803680040928038461084a8445000b28401024141449003103241d041c00c07074219440003500d0034003500d800d86820108402d200d51034251070010b521007100b403048c5c0000380107581a4510075100001c020030560000790312400c5090340103080049041c0c1c00c109052140310690340100d8054002c100305a144d000c182e500d0341c42400141e4000e82003840200303c0030b100b03004491081d40c01816582c0090b5556400301d0b0194005005641001881c2101203085640c100c80006000034644926445544072510 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 930570683 1250 930569433 930569461
    0x310090b06090a271e17030c0d0501090b1513141305041401060602030a050304032d020d021207020901120305070602030f071824030f230109050606090402030601110f06 74
    0x1500b00c209020170303442800510300d11801a0001180340040d9141d545a6910f1440c80c0680103810500d03605000002030000b0740390303200c4180068251507420f18102404102c0c01184600710320040c902c58a51420801c0c100c084405682c540d0000700341109440c4180c4500c0c00b070f50b01c01c1d48c060f0741c0d42c44400106421800244903500041006001843c180011070b007000c0e006010040000d024442c2040e06411032044d07103001180d000100f03903000000300241101c02569400700d10b0859001d403041c600d034800c1c003100000907a2901680140403c0940e03080c50302030b070001a80c8003030440c1449001c1c0110340c00249140055441030b00341e1402d0900c18500f00000510a40114122090300a80d01d0400d21911107005611009a01841c4440852200e4010110002c00b03000f05420307955443c0050040301d952016040d60a8001e42e06020600381c0d072100b039144100c40381a5650b540c424010486600f503418160040d50303000c0414104110902d280c6003003c2e040900700d101d5a08560002c40421007500f0001034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 930571933 1250 930570683 930570713
    0x905090a050919110907020105010906120c0b0918011211060a171504020f0c010c09120308130b090616030603110f1f09050310090b06090a27 62
    0x20040c03015042640e030498a82c0b5004042c00c80001c18041c0300014084c201012a0949401401982c5185007401c0b009000380390a00a640e4078504040c000540d0002340070880c048181c0100394a0480b40c908112001e20764091003030240c020241c0c4410a640782c0740c6114450090564602d44000000145404004541d40c10043c0e48560310501c02e2030149940003203101000e58481c0c51840c0142c03180760389951035440e51203001d41d101d400064910f002c0c240c0c2801070700482c02000e000303005c035419000040d01d10026502035840c44003c40c01030b400c00f00e4445d00e1981e800582c160316414003510280c54409805608542c46403050740280240000d07040805402c01a00200d8503041040c1030440e81c030800d00b040100c82a5208900c0c60f900502d141da5021690f1041c02034091040c01d40000d5950050100f650030b02c2810f110340151141d200741c20301c0078081d65035050f910030b812840c0c2d55a20801c02045d080050259075016a8071555100c265030b005130070101468800900c1c1b0796400300752502108885c4042 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 930573183 1250 930571933 930571951
    0x904050a020108102303120c150106080421350a020f04050f2701170a080904090614100302090109020a090303080703090203070f0e070f020318040902040606090509 72
    0x80304201da40810082c1e0000722543c5c0509000840009001902d441c10701c2c1c1d0344406580000610682c0d0190024802c40c000750202120304260b1303070702c4105880c002001c407009001003002c0d105500395940490b0744051000220b040103c441210059200d071000b005154200301c01c0e405032290218841101d28050340301380003460a42c9410a02503016125010700d10410b0b0090900000d06161035507055500002c407218200c81c0e2081810401d18021110028410f48000724071300b07044808000c80c003003003020301c480d0002c1d140c614080c104014400282400502501d03030036502c45030b4841020302c0c000c0403801540024901043c650644c0104140002c060344140301311743c4104585420160002200f10480381c050528590396690b100094019228080f002541130060140c04541921104104415145152003e08030303a610714800303842d0070000d00901005a031003403220016a1581c145030301c184510160000c201101c3c540d0108094544641101003c540044414031176800c03d805250385c030514403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 930574433 1250 930573183 930573211
    0xe1e033c0c06161e020114040503210c041a09090f0108010c18030209100801020403050325020108150d05062a27040204030503070b04260f0c0c0904050a020108 70
    0x390f080503010710032800c40702604100118019507000c1c000e500c5011007071080034625406207441d00c0d240d9200e078480e003c83c0c0031040c41149050815030079505410b00c500c0c01c2d07040a42c0741ca41000341c1131014511000340d0107a60a01080840c030a03440303226040e0300444c040f03072050700c09504044030a1300f501e180f449440c08019841c5209400f145072200c403c02101e40640751906180c030750f100c07407554440446e0400d221542c00081c00004001c0d0010052054030901c40810080000074040114241d40704800680050408004900542d0005030800c05040000f0400d4000300d40079601c9508040c0201c1350024080e80d003203444505020180c071250030400329060150314008181c800c55950300c401940d80d1440d100d1101c40c484080c0c84070b07812207014540103012680c0741c041c0303441e0007414583c0417075003100d00d2482d0040522015400c61840100006041c41c2c881c14401c1a550005080e0080d41410f229407092032185402070306c9640c142030086001cac10107801c4071201c60002412082c000744c0b500852a0913 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 930575539 1106 930574433 930574471
    0x1b0f0304030c0503010f050603030d0e010e0a03030608070501090e012d290901090b090d06090305030714030f060607020a180e1e033c0c06 61
    0x104a0086c0080d601c2c0c589100306898007640da4a806034400c0c07211007916a07460300481c0441121000028060111000c0706103010403544017a00030030ba80e502e041c001802c091041202801d07003801c200d918035140141a858051741481400c0c00f0900604580c45030b0017088950381ca00790030810a01885588611802c0400c01c00c019059030421440e22170419a0f00e590816078100010503180c030000c591500d104840194480c80085038400648484800090310900c40e400140e4080d55450f03440c0c1c6814030b8050b048022980002007162000d1040141c10035410041d16800101500d2158450340303284003103448402140c200444031001d000500f0071100265101c0d5410005050803206003001007450211035401802d40620b0581041080840c807078107400f27414410401c00005065028102c1e00000022441003003010f61501000a0114810304204036803500400d240c1c444030807100d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 930395683 930575539 := by
  have h0 := BRFrame.cov_init 930395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 930395683 ≤ n) (h2 : n < 930575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
