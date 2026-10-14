-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2655
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:21:27.742385+00:00
-- url     : https://prove2.me/submissions/50c2716d-aa2c-4fd0-81d8-c56c81a0dcba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 477338129 ≤ n < 477517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 477339379 1250 477338129 477338131
    0xc080c0d031a01140a030207020a12031d010f020c0f0307031a04030e1c02060d0f060b090301140103020907230301170c1005040909050f01111209030a0c03050c031b07060f1403 77
    0x280ca00588d50310369610100300700315407590051040e050200200c400b0190003000c18a01c01c250908102000004e0078011a00c100c610310090000d40c002e64240306040c00c0009110320680f40c0901161851a901e03070f41c41c40e02d500c1c02d070040f00b4107150003c28003082650002c051000b08004540d60140c0c682362492801260f01c50050003446180d000038205102c641c5504902556060240f0400402d80e4a14609070b003544241034151095207441100080b100100a0322030507640c0152008446a41e001010344072400a07542c440b031120201d1404040500c103010095019207141b032140070800881d1402a0700e0021055420351191080850a82100303500905440440f80ca194010a480f90b00e400d05e51b06000080f06039500315402c0c0010207071a030313482000038121640780c0b003404640c0da07440100c00c945030f008035840b9800040300c031440c0c071002c644200e0181c50040c402c1c2054a00c0c10104501c0c8451600d42c0d11310084403500450010024a074200c00d04110f00c0c072690405003061000c0414490240c48 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 477340629 1250 477339379 477339397
    0xb09010509060901050f06220501090b01110105160503040c030b090c100f0c121101050f01050f03030414040c0e0913060b010201060f030212030f071b0b0c06070c080c0d031a0114 78
    0x3019288c600f00150011296025081c09240c00c101c1e9503112041c03040641a040001404100d40c0003031a041035070148150380c811001d401d002035500340c0b000300844050740040c2040c1d0703408100780b40202c01b060361080c0c018000e4241c1001001e07e44280b105000704900c60041b007509002d2681801c005207a04440072510242d03204000c609680c4466109a45103014903c0701d09071586801d04014007a900512114160780040355021507803800c40d8205643da110303d01075103800401c9203042d1402c0e82025000150501c4941c01c00c54001910480856088081100e0840d2441001d00c0c0200070b0011910030707100c3c941c17020701c001e01410b4203055211080654500c002401031140ca69120207814003441a6964030301020443c0d03a07111140d0401a2a1400f264100d1050344a400710004000c03400a08a9190b400414081c201694a101f0140d641d0341502409035815442003006000645090041c0a0058a1901e0018135030355010b03a480801c60070640040d05001490429400c001080000e94481c15 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 477341879 1250 477340629 477340639
    0x2040921021005040302061f09140114060a0f03090602070f050a060b0307062f0303010b040e010603061220060c07032d120c02102601050603010506160b09010509060901050f06 77
    0x4110000d200c3d0500310389c0d8840740b40c031494825820307550f00101220f541203449215442c01c2e07003c150010130110348901101100850140070b03088105900907080503070024014100141045402d468064a20528010407521034200501e200300304001482550300c0d68000713400800845040440c0a8400d8040c04403281400c20102030303444402408d1010f0f010042070150640703440c1c0d6034861050181e5082030180765406a103603c00840d0b40c038840e2003100112024004c9094403803419840341d007941c0388501c0704025641c42c44141d52000351145001800b2003203010b001040c00728030f50300b011220b142240d10f00c414010544130511146050368100c0880c015080200701440314040b0800303a45901060000a42008112040a500640028250284007680c03030058148080c410690065004240506903014000b440140a40e0409202400f00b4058440c00c4062641c260344905064010440e00c1c16000d80d156410841070303d4007800b0054000025500a00040c00c0603821104000320003407041e270141c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 477343129 1250 477341879 477341911
    0x130608100e01060f0803040608010611030414030a021e030d031b0e030a0c091401080613081e03010e010f121101031a040509070603061505030a05040204092102100504030206 76
    0x2083d80224010b0001c000d22100081c3c2d5000519280e0b00b251041c03802003983c00c4000034200d0300030080c40100040c000c000e185400e080c1503083c0b80742245000850f030180310b603400c41001070b1914070000d64880b65500107a0805628007042628041c06020020101414411602915000702c0348114660b0031904200300104060400f00b46084034a14000e400d68002d03990021740c03c042580141da5541894035001c505030b895641d0540c1d6601c0654000200c140c200401801081181e000f900006100c2c0075605100b40704003050402540081e04118812040280100b00c8100b4a64503413000f0a21030505081d0401aa2601c9201481c170f2501a410305031a01c0124240594003901203180e40c00060041059082c10318007141e80c1c0219006030f40129181134008106501c240452038407442d05990750b24030b16030310000034a01401001c5c20880e04191111251b90001d80c065501e5440e400c00700481002281c02240c3c02490702c8100d250104c1054502820300000c0303540400d4465101c030805c0035141035 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 477344379 1250 477343129 477343151
    0x10606030b15071b06210608150403050408101d0c18072a140c030a060f02040506040b030703050f250e03010510030c0f14010f02190b0613060810 64
    0xc040445166130700004502404034150350401c802c0c101013081c1240600c404103940d02d03e00200c0b5902c2c0030703140b00f9521200c65141100910f40340039900500c40d2500341d0806540700c008174501008005420f86198a61744500858a40340c40346001c06848000206083d11800b400315180040b50344002248509100024010501640314590a8425041502c895075800300d030780f6080c034039048002c8444507100511194080c0b03000804041040000b070181554044507610540242013540b51140380a40034440080d40b40e40d03090280004200c0d0040c42503032443d00c414000c045540007004429a00006010310030704100d41c2642c0000080c81c2d07110140e000d8001401a41d100307061402150f85517082808114440c15050003540449104695003040152110840c00c0b12402d28080d116422090000381d0482c0d61080240d01c04002440c0107a414184101c94032074001001140c0030340b49144403a050042d1402d25010842018203581c00800695050801031510340b445881c040b0510764440c83c47c900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 477345629 1250 477344379 477344393
    0x30f0f0d021c09020907030606050f070302070807030609051603031d0402090a031101091d0403140d060303022d0c06030a0b0904060501030501050717280203090f010606030b1507 78
    0x2216000607014030460302c0c010400714000d002c201030f040780141112804914814064051b203000c0c0c42481d00c0b881d0604070031003490042604039072415400c500c603046000543c800e040c0928806117005031000302c0c0c035000505000d490200003114403404148121010000f1a61282004440c6105540801070124050300000c1c06405507620103503104500f00400002c0200c8000501c0302c031102070701e0b00081c1d66900c0403030035161800200d501c500d02d5660000038000034402c0d50f1600e0b40307150301d020301c601305085203003400201d80e401d810890140e031218101c2090702c01818520041c06404a80c082c102c00b0b00500c0460b102c01c1103074131160003204044040342c2c111485d60091a084540036105903210314003030800601802c42840161015440c2c1008100610702c503071055200321800101421071034a0380701603000e2080759026180d004014246444010103c00e0004500406001008062001c0400041ca085901d00c1d072100c02418688141079120751109105d41100c5140c05000c40d07212091810054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 477346879 1250 477345629 477345637
    0x62d041b090c0909060f051f020f0d0c020406052205070908030c010b0a0b1306051e0414090601030507090b031819031805090114030a0b0112050609030f0f0d02 70
    0x240c991818079100400c0710f544a5889003c4880454007070004507a611038800c1070356058090f081e0814000c800c6554a288a003104048001c803a20440d411481d90384492801d284020162000213510b000c2210250301d02030040002034041160540c0808040c000d00d40c84071324a0102c2211d06545800010340180d000340c1d40c00c001010000e0680f6619805501801d00030000c19680c1031280c00f08020100f60300380b000741504d120201814061251030308240e81990b0700c1e000300945111102159a071810403502000250000302603500c034428080a00a04101c0d254000411b1141050324100400400f161702000c0c0310f0807104007506050b980c2d20b030081e4009248540c8442e102007846600740d400300c80144850f402003154001d0ba6807050b510151032004030a80305a1269a0384a4051030060001810b14640c4002968004003120815280d039510b0040810099000c1100c0d0a0350005041c10700c1828804c0301c1e132104101c000b0b14a49003a986081909015080e02c12402d1000800c94201c141c0c100c0d0704907 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 477348129 1250 477346879 477346889
    0x70201110a020f070b090d03180914180d05030a0c05070c0803030108122b0f06180f05010806160c0b0906071209020f01230c062d041b 59
    0x3641e66180312200c06903032a0a5070a0550891060700f000007000b02200c3c09554040c500100265405803240d101211320010b800e40380904412020000202d0300824464001c00040440e2540018680507250030f100e150080d121095541000342c6844100f0b520000f03d95000302d9100740040c56007445407040352180222040249070b0601110b000c01c6200d0000003a504031002a421640200c20100182045001c0d088109c0100b12484428400e4800302409405880c4002d0340c0c0010340b25420a40300c0c0c25903c81c0e600203035440030046001c444d804401d01a810502109000030301142d4585007407603546500003400f010391030380300708c0b60b00001c10302c50411004450b8000c0f01600349810f01d81c03c0d0503101c85003039646101003071000401580e03000c1c0c2070144051260300106041c2020701d070000152805016140744141482420b4410305160f0504000760a030100020000e14003441d00d004001441c040f2a0956018505a485184482042540a90f520541c03009030300910045620303000291360700507005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 477349379 1250 477348129 477348161
    0x30303040c1a120a050c0d091b0f0e040f020105160c1e0303050307030f0b0a030510110c0601090c02071a120f01060c080c0a0803012d060512070201 65
    0x18401805401008107050707074142c41c03516011814800b400340d20381c0320b608449241042c400c0005a41900164030541c2d01100d401166031602c80014000c80403500e155008644c82c2a6042d0f44032480c2d400215418042c000d0b00c00510005802d08503213a41403c0001c00c0100102d5207842ca080031039104400391145c4840840300c1d14058842c501d8407007000c070b0650280c40d44000d007195601c0d2120440c00c549408991301074417040e01d9a25001c00490182040d000e005580c181c84002c4502c094891b81c0c4104004c40c01000030b401800c03111308802007903c05145d116041e601040c07001140d102c0d4081889411103c00113000a0051481034042e403d02c03145600c0100d88420500355404030f96100c0c0010501600e140801c04042e60315071510400715a028050304e400aa1940748040001d03260381c000b0000319055004484610603181d540b46881e9000360403d01258100c490490b55401c210412030690910682d941041542401e500070280d0040a20100c1165240004a050203000703600003070b044041046 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 477350629 1250 477349379 477349381
    0x70212071a180c030105060a0905070e031b1306080c0d060b03010c0f020c010f020d180b030a0617011803050d0b09040615050d120c140f0a020a050609130f0209030303 73
    0x29012041c00c240039070b403a01806044040c0400e0328061041da4441c810051101c18254144035000008040c024100d04c1804a107501d0041d250b0303000c02481c14003161a20601032a101e42c141400740d1303062043d038048421410040c0a1100c0720020408010600060f20400010401c9040c090040c196080300140c15507c0c0001400c06164007039608480300f0f1a980844230a40f81c0c0d4401107440001a0a181006030000001101d07810b1040d0060f554007041008007103960360321230b44070548030b07441540c0104506580c1c0504101412080a100074140d90b00743c003c102446200310351817820098114001c3c2001300014418000314803d41c40700ca0300c0d03500a0644c5159140c18a0301d10020701d40500381c203002c074480c0740d000074041c54a003007020025a4000032244600c840388400361840001414111404091180c0012003c00c080103035443c094140703401440705000c1381c01886503401c3c050700181c0c080d0004204401894413222b031042070120050760000744401242c2441d81c001c0c09a0000c00f90b242c00000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 477351879 1250 477350629 477350641
    0x30c04030c03150b010e0904170d050f011d0903090d060e032a0d0c0609140d020c130c0e1908011d060109050613020306030a0f0501140105040203070212071a 69
    0x103402002d241240300c0f00700084d020010054840260308136400c4c1e84140e00c100054009689101403080c4040d002a8440c03e10111301c0c10b65044c1d410489501403c5140e42004200f2000030100051400c041c0c800c00342d0983c10f0196000e40c036840f54000c03250241c5904020401002400da0105481d20700c00b000380c9445205035108000000e961101900e003681c40041c05420154011480c191904055200c07803d00701d119646410207050142d00584070302d01103a100000800050105036000e0b070007580942020300c420410098031044002804605a241507480555250800b5a50318919012a045070306034210004c28040c50701d95810542c107950800540d6a1070240080005902103092002c0d40e1140c0c0c0c07150a413508444088501da544940107040408039510268000d54104101900b550307900786040d200c80d04090401c8508843d0785e07640741c3e40c040901072516821400740030121030075440e60800c0351000350386800000c10381010307450000f01c040801104001e030a040d102400c80d03150700c40c5400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 477353129 1250 477351879 477351893
    0xa20070510030e07050109141302091008010603150e07081003140307030e04150e0414010507050304050d02010606120e160b1207020312010b0f0d0f0203180a0f08030c04030c03 77
    0x20460306005110f6039001107011b40c0140d8114064890004040741c518405d40d040003c2810209042d8a07a15800c21424849458002c0d80c40c0d401000c40e101c1c6d00345545094802012140301c0440103000c0940e8900c2441080f4902c140a074000f541d51034004801e44580341004001d0181c0d5000615501f4460044030f00303041c0100240044c10700079180c0000b890310b04000d01090307450340d0500143d0701695410a0114001d4407090139007090040c0e220000074041c06410b2421140c0031345043c1c0110f20040b003000b0800100f00007200c3e43c40b6203132000b440110300d45603029000b0041001380c400c000c0d444410402203142c0400c40d4034004075014043c008210780c2c90745104a50341c0110700c034031120b0a00800240d13007240004126820310802140d1003485a01e80013070781545800545102807000400c000e10240349500b0301602c49041c0e800c80d8010f0341d0f1f040c003c0f030943c04510b410440e4526500070641c1400414090902ea1083c60303002241e4658075a15221440c24900c85e540006000710f486880100030720030380b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 477354379 1250 477353129 477353141
    0x9090f230609011d070e0105100216062d23090916020607050c03070201030b061204060605041a090f1e0703051501080c0712092102030705060a2007051003 68
    0x60304d0448100d00000b0751103032a1410303409007104080541004204c142010224180b503082107105883c10070241d02c5207000b600c08103601803000100d003881d04142507042803150042c0c5c95a24019506803e9807a18003400034400101c04105003032001d8001652042c04008460803801c000f41055421316101c8000103000313800b9423480c0300601c2070400003080d42d0701070800c6940b00c100c50f40044d400c0a4566004502410400a40079001902801001300c040c05200c20540910300c6141d001c250076041000b84002c80c0d201c840c284201384040c00b003840c8544c0b590350300c2c2500841604d40b0402295100c64140c000f00f4480403043d0b0075010380300d00300a4090b616500150003503420001155515041800454912038140c1c1d61201d180c2041000800040d203483e0607645070080350a200c0140c9a82e50810600d1015081c101c03200d0511280380d10302140740078080d03080a40b40031941c06081410102c0c0c01010301c1050340c810400107400e1441101c0c5040100061030040c08006c00c000200340404200401a0074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 477355629 1250 477354379 477354401
    0x305061c080c190c030b0406060b040902030405160b09010305040c080607120c03090206120a112a070605040e0a0b131a241b0d09030b0109090f23060901 67
    0x348a503906000e4510382010318200d8009082000b41c42c05d540710000703840030203001110460350380d9174006000200740000e00020a4000c500585a207002d040281c02c12840501201101c0360202c030601c030841091082d108044020710b0009502d90300c52070100c2c5059010340080101d407158404000039107031f118010581041c05048103000030700258405034183e965141009500000034007401c4e84105038101c0750b55009460007004165084040c1001c0c80136440080031400c208400a003440c2d00c410352988031203424602d00001e01e0b40514120b0001d04034000d500442d039101380b00c3d001181522a454007c1c038031050006100c4000a011141110010400c0312500f83d080000303000d40c0790040c6003d500740083c069051000c0d600c018000500e2500b2507024440b51611313102404124910480d04000e04043c802c00c548803018080c2c01c60409440359034050344419045400d014501c80021040f5800e842e09546c000b40141f24154213030b840329820301d0389002ea058075114034403c00845400540000c46014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 477356879 1250 477355629 477355633
    0x10f0603062a050d09060209090103080a26010501030c141222020f01030213210b0105100e0603070c140114070c111c0206030a061809030f0305061c080c 67
    0x56203500d044880460500c2d4500003003002880b001404400325000040c2081c0b0910b00149030450f03103400100c210790281c2069a9000003c40c1070b1090070f81001001e602d4145503620120000303e81c00802e26201014010281019150300521070f006010709800881c0d80c000c40c074890b448045203004078070665021119115a004540003280401000140340135800d900900402000111400154040c0d0302200e6240c2201c03a00910009000540c802c03124910440c0e800f41c0c11000ca054144642c0f90641a0046072117101a00402c02d400e0307400800705c0300402801d580d895201e948080c3d044c0d8520003215000b070207102c0c0362003030803c0c20901940049156509200802d0054540c580708445107000c0c0c001c01016002400e1051101c1d10704480313100e0311001488602e0b800e0381083c0c1c0c0490120b070002d40c0c00d0310304161500d03018030801d04004104202c6200c0440e00f080005d44030b88009214031b440029400a00d5500d40100d42c280d291456010f500100f0003009030340c04401454000400c3c0c0c0700d042240494 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 477358129 1250 477356879 477356921
    0xc08071202150304030806041d190204050a0605030703030f2f06090c0f090c090315040308070806090a0c09080d050a090e090d1101090c121e0302060a0e010f060306 72
    0xc0e100303002c03d0b41d00a68042c0c1d11040259a814107000050a10810f401a0441da27280d194000d500c0800c8104030b10444403400a00c401c1891050000350303100a0300502d07596003004010312407518005910011aa014502260b84030b401c2a02a2404600c0c01113a0f804002880701c81c2c542c0b28003610199015001280442e9003590300d000e1559202c41a0b000307510381c040c030807524a017840c1c42c01c1c44215400c401c0031001c45140c803400d04000b91500c0d942407000d14946440904100c00d068000c401c1551141050400c003000d4601440099000c1800a1031900425624084140c01520401d10407000d04000c0d022102c44000708203029108c3d0300017101808c009001e58034082145107101806030301455050b07004200a600100d01a076000030728034501841c035135850710703002d01240c910100c0c88000e02500b801002c45008a06040211246c00140560380c4005081e82c1e20010b540041c1d019030110940e5000070f8411600300040b8050078076000c6075050340c2d0918101100740040c031750004034a903400581031158 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 477359379 1250 477358129 477358159
    0x25120906020c0f0301060902030a0b0a060e030a080703031410090f3c060f06080109050609220209010e060f0a0b04120f140a050c0f1c0c08071202 64
    0x2400025006590040c2c01c04180702c0982e0074642e10945254000400220b0000d44503013541c02281c000300c0b4a804c000e80c8880784030300541401201d03240074080303610302820102900000b0036503ea140b024014027085002078140141442540105200d90f80d6050807805428203904001e07540401d4003801218a140c2440c1180e10307041845084100e20b00000d2502029940b00c0c00340d00d144425085000c0c1500700340b02541c0300c0c0c684512940d00600b1548160109013410310034001c284032416080a00305910342418131106554504426900c82c84403003e00c003102580020042c400136900000a410415070400403448081100d00d80b80b08840c01e1340c406501d24201400c010359030b22a449013100c0a4000c01c414400401252000da0425001c0d40c0800d22120b003940d244170300401c0d0060300f442c0c25049003851a0401c00180000c1b000400d08803103000d05540b5006c0054134513009040b14940d190b040005003010800c034071882c04001d207004004d4802c0700b9540da80d050781906802008074442d80440386c02c020 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 477360629 1250 477359379 477359387
    0xe07060f090803160c0312030519180210020715050a0e10050d27050a1103060f010612021908040506060405100b1b07080d020f031306030e0a02190e10080a02090c2512 73
    0x100a0380619400f0824000330340031300012004400b00c0c0f5046010b20400482c1c1c2c010303122052005d000e4586d079030315500c042e603540051400100070001442400740103240c240081d03114007070303820b11003140300c000035a08540d20004035a41886030940800c7c80090302c1c8071080c0034000c00c01504250007011032005d00c1c94a1420517032a000c08481c080c1d50203402c040107020b2107220310340014500d01c2c1d00c18010700e441c84000806500ca83e20301c2c250700016000c001000304000f001c0c070143d034000300c0a42e8103010f1070034110440f040c0da150340d000380424080e011442110f14200e80104d403d49a03000026507451607107039a4a507441d107440308840400743c803d05028045a0500100720b0b03600b54171101413020071604000d002c0f40038003002c0c021422940300300381c3c1920240e0343d50b0024122210208280f0f201442c030341410002048001040b8286a101c480c104115044005c41c0c0c946125504560090851f030725041000010300541c2d440525100101ca01014401207010595507800d001d6034034911607544a00f0121 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 477361879 1250 477360629 477360641
    0x708130504320103050d0f090509010308071101031a0609030a060e0307021e090103030f020f07060201051008070e0109200a0e09090136060e07060f090803160c0312030519 75
    0x10100d46c02500446006403242c1c070300502c1c0c1001450801d40c0c141c1e8440002d0242c080a8100362115180042d4500c1001000701e5080c0c00c1007070a081c02c1c441014101c000340d501c040d04001c2c1500600d000200d90300c0c907035418040b0703500c43c0e0b070310003400c1003412030707a201d8142e40e0f400054040b80100c401254087e100110120321029005008100000c41d82c00c69a0884400851a81080640c030a0b4581180051020302c06400504801ea00025051820103007610f10680c2c2a88407207000d810118080c001c115042281038107668074803101103101034040029445a00810501003050b46020031030881442e48032007003c00c020001c9440d44002c1c0c03034400c0ba9608881c50038051024100342800e0310740301e00d401e010078483c003e0b142c14038100f040f00312901d9003000c0d115401250419508200030603c00660070845584c2c4051080c40d0442900f0305012a0702e0782e81c400e0f080011185903404002d00f003048034448104002d590301031103180c041409840040d029020544103c00c0310903824454108150f8984940 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 477363129 1250 477361879 477361883
    0xc2205060d0b2d040b06031c050304110a030510050601080a140a0c0e06040f0e070302250c0b0408060a0f051611010605040504050307060c0e060708130504320103 71
    0x418161200c4003160400b603c0034592075585030203240e50182c0e00550340380041c45503008403a0b94402c0d00c0c000701007605045030703030401e0420400c1d48001c070a0741c3c0340d000050341e6011364000c594084400c100c00001c2d11104259000034114801d800307508203562130310b811441c0a224280c8606400da20750780a1882039444030701640c082c00282c800014180a641d801110130040340c3d0610030840c201000201d0440d42c401d4000691004100d0b01c100141e103000381b150740d403200721454118185060b00c0c03641d10800120040113103c100540e240d032010301480c7c0c80118001c0c110b041a245c0d9440d80c94900781d4854004032541c1e00d080349422407080a00c001c600070280700305940c02060040701c0d0994010b685246046c01070341d80ca50368408003c00c0c641c4480c444c2c90700031030182d00216101d28091400c030098a078400e0715002001250034540300a5181d10050310b01c016030141d940e54886c04086440e002d01450390b4031941d400f500f4271680350040b00702c61400341d140124480002540d048031100a8843e64001c0c400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 477364379 1250 477363129 477363143
    0x171e01050601050a0302032e0305060105090403050909071707120e0d0e060d0b060d06330503040515240d0206040b0c070f08010c1e021e0c2205060d 65
    0x119002d010f00c46c0e0300441d4441690958000303280c3c02e407a035094185c1c90000c0f2000c040000e0000c18014003000300802401004200e80520007850140d500400500449203024003c0354080041546540180401c41b031040015101c41c1c0d00c0d1400f01030007030422022540a421191400c0041034121001180d01c1c00c1301003603511114009400e10050001c2944000c400004880e81d441da404156074a48000f000c0001000d2008100b403410400f0b40d003805c0b01d034001000e0109408011034120a120b02c0f90b0001d41050030f0814039240e035a40d08015080903d0102111144c040480804c0311000500b5802406d944403004181400000d07407050040710000a03802039486030084c00100101000350b0000c00568225031b0a9508090b03803103007000b0996180740c0003901180d440341076055100d68490441340e4030112600c0842980c4c4103a400213525151081c50101e0950000e2280c480d480f50b0030032203940150b001801d080b05400140e90110205070480307603413003810342c01c0a0204205281c903d00c4810b60f2900000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 477365629 1250 477364379 477364387
    0x610080118060306141e010e0112030c020d0309030302070902250804120507300210180e0a0e070605190c02061602040c02010614010c0606171e0105060105 68
    0x2280780703045980000030000c110703121140840012643e0141c0c2240c0d82d91554222000d040400c641a55080c0070603a1610000c418401085810a1488034504460030140080c0000703985050480f4852490f25000e034100f403a0204030410140c0c01581601200c2c001c2c2d00755007020344c503007902d58242c3c0720707180300c40806081c500403150711151010f200383c1c03c003449100c299140c903a4400c5020b1f2804d40380302d41038034290080c80007000a9109900c66114070f030030050140c41c08072008911290485440300010b80240054000104518080d081b40c0b50035680e12400111000d0384e07510281d8203410115400c02423141440440e0b1084e8100003016415100309840342400c1080100110240d2001c40c4000002c000b203e07003607500035845040082c0507074051491540b45140140c014071040d190341c140d0074411603140c0401045404501c0400181810007480d002e40c0302d01d594100040941060b40142607540500ba07400d0380340c8000000d40b440e8441d0510090224007080980c540c0c00c989007141c42c030780403403402c00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 477366879 1250 477365629 477365639
    0x70f08062e3005100b0d0b0103031b02190501020c0d03020d0f0c080a030204081b0f0402070c15020606031e0303010905041412090301060e0c04171f0c0806100801 71
    0x4404640d5500c1071600d010b4505282003400c1c404201d040252030581008641c4a0000310314081d1900511094410320041e04056403410360303910051101904001e40000c0341150003003208800b45200360006d00c10180010050001c04440d00188603035409449055410038150510030790244051b50103030050052a85510b60959581140c01e50360010059221040000141407201801c3e12400c0707a6030040c4c50343d062171149071522006840d06c08010440708404d9040d03640f401c4224406080582d00543c69144900c3d01d0010040c5540142a00d100f200011b00510f940c001200d41c410b2404904513142164800501c0e0415030126174103d215400410040c09404180d40041ea002442100d03403501c030351040c00505080440d41500120b10810000d041311983c41d003401140050105d81c0e003603100078145245022591702c290700c10745580d01742140400740c00c6070040c007414990010385209807101050b0019140010070006078040040f030000d1012030035900301514240ca1050450b280d84125234203103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 477368129 1250 477366879 477366899
    0xa0906080d08090a0506040302011505031f0b0102070f080a0b1608040602030402062a011b1b030e13020903070e01060f0815130e120901050703030b0102070f08062e 72
    0x600014039440f600c1003110005d80c00700b141c2c0b071066010f40d0000840070311a0082c010660b80603481644a42d0040e06500c481a91151450403456498613000071041c10000c0140e0801905600c03090058804c2040001d02e00390110b000c400303051081640c001e160381c401140d24074a1516131003c40000d8130a10010b8002000ca0b0300440d08140000d180034106103281c62a140c2c50303003240c80c111940c44540440140d010b8800d000740450a25020a4110300700342c91a030041003006200341840707003485403a4030346040c075002c0c1c00341d04020031000d01028490314002d14408042d50100100c1e0b806885a5500050413001007008241691101d42d07521202d1880400201c600b1803001c0c0a2510520700011010015900c48180d10b448034150f01000c1498106849150709101d256809403a24400c10880c1c80c616030703808400c0722146541400c00098207000c03e80106c0c502191070700051244050888042440c94000541c00d201d20321081c4030032400525025128995214080300302c4070340c000300ca410320001c059 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 477369379 1250 477368129 477368131
    0x70c0b031b0f07030f08090c09040606092d0903052a060106121401080c010c031b0c0306180c0b0903030c03030a05011e030807030806060d0c05090a0906080d08 70
    0x1030718440c00740142146051030002e41c0030540280580364000303128410160041031000d503002190510740110b10f08944c0d807a40f103001002c8468424104036000404004d4039074040c1018210000c010005c0c480c0311585c2e00da0000d640c20800c2c40e007240c42065040e02d1078460060340e00d800d41c196a11070070316800b1070102680d02607a50001c0c45083c03840c00b80c0aa044e41c00c200941c006d00c826603d0b46d42091350308030400110f4441c010707858400e000d00c0005011070500058012001d007002e02c1d0a01003180701e410300300c501d070f11f000300e100702805590050b91060120031600306081c1ca0241c0c20401000c3d600b08422440c420080b00000c00d18180b0303550804c13641d4080b501a143c40340c000f90550785448800d000060542c0e20484854001940e6000180b080103c00c0c244000c1c18408204042c0382d00b415074468442902800e40001c08100464002406680720303002519000c10b0f4003c0c05000ba060040c0c0c2c040c0140d00306400303e5000348091080000c006000e409600d0442d540703030002d4182d88050850071600c50744 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 477370629 1250 477369379 477369391
    0x6010b0a230c0a030f09080601080a0b06010c0b01060917010c08010b0c03040b030103060615050a050904052d09060a0b180702011e02190c05191b09050a11070c0b03 72
    0x20700340701c0503906990034003009080910a5503070b00d503080541c541c090142401500031038400d40c0002c0c010b0008500000d05240c03059000400d03d0700a0f942d15004903501200302a004080c1c820789000080c185070001e40380c07800d844418110080c40700c1804442070880c0c041188690008000780c004100040c100780082500c94810b40581e450691a41c1114602e0780c420b900c21128150b80704030402150402144502d0249020714187e444e00a11a100034118092080c040c6d100c0c0350781d440868485508880309034141c08800e40b07015032401441c220f80540d940221820a114011117000030201c032198410b00200d8800107100c21038200d28540307a801955001000c00041d990b88040128001300740c007540320755440b40b540004d0b039240040000e07030002d500344a8800080c00001c4240000250000c90f05003841100700c500141d43c0c0009003446060701c00e0320304900c100040e240c0b40c003003080c030300c650489880341d0030385501030010800705d81034112940b05960300600395400f03607035091002040101c000d6030025 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 477371879 1250 477370629 477370697
    0x1504030b060f034b011a0607060216021f0306140307030303020c010e0f070f06020111030c030406090602030c0d0b0607020d0b0a0f141f0f05100c0807030206060306010b0a 75
    0xf13035092454039a01c04030b0010b00304a80011103e200b4803c4090154540c4030340c1c40189409401c0c01c01001c2404c6004440c03008201e1900030801c201a16185050076081640003480c0580880003440b0308964411040f10020000741014400f2070701c040719500318064020040c00801410b45540c8040f0000d40141c1c0c2c0a000954840b030923407011003010441c0c500d8003118180035000151804e45c1203140e400a070380c480029a410003004514001c403d00075603a1100f00183c01035901c1c0d5903481d15400620f0503044c0140458400300078866070249020151030740700304030714040001068050800441d8011800029800034036505074800085c22005a9504228803120104004000c1c0480034107494034420101d4686038148100040100d00c00c02d901a08503c1680d030003e41400c00384041c151200710f000d0940541c21081d0710700c441a11440c0b003c0462a0880e880036203590300380c50000e440d9182030f90414400c1c42040c2c0042482105030303048811012254079003030145c60400c0702c598815a0684107600d021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 477373129 1250 477371879 477371953
    0x827040507090b090415080309100e03070303110c0d11040e0102030f1317030703020a0905043c06080a02010906021504060b0f04050a050106090f0602061909021504030b060f03 77
    0x1004916686c00151400344041d5494506800520540d484000e244400300a4540c0021885860200320401625014030304a84504c6d101c030102468160445809034012045500804c2031210040c80b1a000e440201e600b80310660011000d28240d00066480203422300c0715074080b8034000e408016840109100311b0300450000d00346500a810b51304116004404650009031700c407000c5621900d02d101502c01268104207403194006208900b490107005029065030805500580f050259404200105850320600041e0b445242d030346d0300c419419504038042814480080f030702c0350000c203004003000c07003d122020040c0e44540fa11400b500905405941004d03420541000320345860141a20500e03509070040350759490034a000702805299402400381400850301403060b40e41c0802c0c0944c008906500190399501d20303603500b0300100903900c03000350b108002440e9a2810821400a032044a00441540d00d0a94614040c40900c20071109880d5154005240c1410703105a80f100680400c103464500d0004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 477374379 1250 477373129 477373151
    0x207260609060f010e010b07030c0804080a0f0b01090504030c1113090501050601020f070506040b0d0204170607091a030604051f08160801061a160827040507090b0904 73
    0x2001810303601410590408420000e0307414071100f0f20f038010039500c0c61102a40d1324044070380d072507402054001403c10040f4002c00b818020000c00341c1300a41142c0301583e0321b2001500d810b040c40c103242c1404071805940c280c0001003c1f0202d2041a102d00d42503180c000000303801355210100b88844848450740024403421f80072035003440d48501040c2758840c000014460400c03000192506010341640d00c41c41d40403040501103520b03200261f804a4540d80a03140c0c84041440da000041d002c3c9070001692401e101143e0130080c140052058091312558451003000da072100404405080070899840c2c08540400c0440c540342482d5001c03035400300348060400400d450030780301c0c0403100100b507014401c07030750100003004451707503858050100504c1c40c40008c22025261140c0100c00071301c1c8451480350b10b0804291501c45410104000c1840c5038090011a901c0d0401e0700041008400e03100418100680d03280c0400081c01c0c18410140070b113480d900e800c80f0051030030f2080e408950004911030341007500e031084815 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 477375629 1250 477374379 477374383
    0x604030f020a1707110a06020d030e070e16110606061b150a0f06090b0d17040b22080307020108011824080105070503150d030306181a010c0201020726 66
    0x1002c06041606913a0000c40c102042d414000d0292548904002d040c1004102d8001400002d0540300c1d0030040740e00056a100181011900e038481104115050f0801a10856420410b031031000c0c5511000d103e14a4225629649c910450300307590013440410141103152401e55000d50502003440c1214000e82c00d80c1d4002c6c8102c081950040318080d2100c007484a905164090500608210f0004110030044c0c0000100c540e0104240504030041d8110090280e50100003202d0250070324941072651101507030b92402d0a0604640245e841c85101d40c000324000c41f0110486e404590169a20607a80e400c02d40074010403c2c0f250000d0700410ba0b565025405007506020040c00601c0d80c00c103000c0c0e11460603440710f003542d0000304079404100c0304008208001c481c03010010700d196010348520b000c80402c0d1078203400511194104240c05000140342c40690280b0790400b085204081c2d505049440f007500042d912407110903002030140c2c00200c0c06104020481603d4503240e511480c070a804420301c240054 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 477376879 1250 477375629 477375653
    0x1206050a1b0215060409030c060207080c0f1005070503010b0a0e0a081002030a0c0e0d0f021305040b06030c010305010614031e091005060307030201050a110a02030601120b180604030f020a 82
    0x90158000d58224210710b83c241d00c0782e40e4405026101842111500d82d00280781d03200d102c1001300200d030302045171400e100740f2000741e500405445049035406000d9410666940b448035040404882c141000540e1081c1304006680c1201c02580d151824a007a185040d10b403081d951340c820340c00034034207030001841c03041c1081202e9808041c54401a901d00b0806a000c099854540c2d4070010300c80300d120918000e49a1105103a0303029008640a004000e0074400602800c1e80303001800f10a42c200003d101c14024800c8025016041c214125000188044010750948109114501c04034103141c0310200454050001568000d041300c05140868189400d05041500c00707841114183d0b10586501007070012501c2899003002048005003d01440c0d50300003881485281518030030050780240091203030a042008a078915401415240c0c1c03503031143c5075040c0442ca185800c0e15091845030101d00d40c85032902d5080e16451811002c0e10460351070742c4054480c3c0600c550104210302c90a4000c0000c40d240324190 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 477378129 1250 477376879 477376931
    0x60b0303030c070b0c03090a0f03034104081608070609081903020f0a0c03050c010c020d030c0e0f010e060706110723072601020304060b0306010e011206050a 69
    0x60701d454032400c2c01c0080c00300061402c42031703450400c2480f580180001d60180d80c19072001c520000d43c1490b14048001d089490400d881c03181154060780202e051300c3c0e004000300500c40e181c0030b50364120f2104041c0003480550300608500401c200b0468464411940340c0e04c541d0140305141e1400032700c2d503542400c903505940107a131200c40104070900e88150403404102c0c410301500d415030500ccd01c02c0921000500c1819000030910108081100426004000b41c0d84605032080c0208214800c5c1c0380c02a403100034404524001a2510248000d10341c06107034802100b000c090424861038074a03100540300c4918480103107500100c00e00200b8000b680602601c0704210000c1c83c031507165503043c0380c00c20f05010014900712003414110702984500b00001303071180490306903401084241d81c900131800440801024030134079175400041040b00307100054000701c403440310030f800329846a030303a0705e0311003505500a010b81c0e8040c50000c111540800d035590030980c0c00485070139002031a907020070240c08c0104048420 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 477379379 1250 477378129 477378151
    0x9080f070201030606110325050d081611190203120a021501050d052d070605090f09060108012c010312141603031a030a0311011b0e0409060b030303 65
    0x40c0d421542d25020759001409942003400040d01d40742980e41e220b000b0a00c2d0b503c0142c62035010f41503515012000144003a4001055800707240c2d43d554010103000040360030003d0700d0080f0700c0b01096a845024801038003400d000281a4681000040c03848000124500f40d90500c5104180d203014050100145601181900100b120680030b1660003000c031016848144038641e001c0300f81d808294081544c503007810300c1d20200510480000d179043c0c2421050030079140075200301200420340320381140041000110032030f22101c03420020002c000c1600c504a603071303600080c2c145004100c0300c0005c03a8021070688444206891190f0380b0042c01c018014264825242c0610343c04080a07110b4201004250410480000070300d008000c070b6003030180d110f41c040010205a9a0b40306000000710340c8400009411004042c0c8600c160107090041c40c0c1c030f423100e100c20099441c02c3d00302c0d1100012008080b0500b07080d903c80c06100c22161042100400701c050040e40c40b9038440150b48000d54007840154468890013507 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 477380629 1250 477379379 477379387
    0xf0f04121e082506050c04081e03070210140d0b01030f0504030806012102040b03041202060615090409020d060e0f07030b0f070203040b03040302030a0f080f0c0306010309080f 77
    0x8280c0a15002000c541d5405000c0510000118400c40121001e000035251050110001e25681400f46020300d07501904152900c411312a82c26010380040c130898071701100312002d040307412404034405e6104019a4885038410041840141840e9003800203400c42400e068541d030200484210f0035a1000500340c4205644448404642da01031154003c0600c030080200598a8542d80140207840082c20041c1803041c0c3c040002c2100d9092207440c1a04004030905544466032260420316540007658115104030b02c5241025000d413000903ca44140c900070b151a451601d03049071810560702000500380c00030b848000102c0940c0390001810401d80c030078200011000d403401410350030310601c5105250f0540104408102159003545243d8100218a1024000342c58014003a03240d88110b50040c01c00310004401c00c0145a000300103890441041c0d107900c00d15402c5540700701c1d400f07842100c002004907140804100d0f241407400155034001810304000480300e01c035880d15602c5d6040f62502c0c0804200001d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 477381879 1250 477380629 477380633
    0xc050111040e0a0510061101021b07030b06120607030b040f09030f080c0406080a020306010e120609070e0903070f02060d0603060902040b0f091302030a0b010b0d150501090b0f0f0412 80
    0x9107079521040c040f80400207400c00706031401c901d0010b48a039504000b07107403482d0600a171b003c0d411603042e4101491800408c1d02d100d4210b903200c2900e4401950501d0204000a4803801c054401c01e03082c10101014041c107a0b44e281054000307083c06200c95821594440104424510070320510180c3d602136200d4000400308000001c280d202c009055210005003400700b0091503800142c0f69030003a20401000da01c0b0366403280101d89414540003003642c8031030341e03032200c03100340001260340ca01404168040d146d0180e29550030071000281550300c1c42082d40300f00f24400110360000305d40d9203c240300030816480c1440c2044103c0554070250405d466450387c454050f400c6103030078418401e9803a001c0e1054601f403100c1c08001500a0300091100e5600300d611000c60046540c2405015084e96026407180283c0d40c54500340c00c031581040c5034409046181860b13160102c200c85681d5802c69070141d4500390a0b60505007107200c180c10142110401d40400e0000d04102420b150140000d000d80c8007410050801c54 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 477383129 1250 477381879 477381899
    0x91a04050f160306080c0f04091e0b0601020d0c121e0216090606080417091819060315090305040b030903120c0a080a23040b0106030e190b06010c05011104 68
    0x280c603400b82070514106081003c0d000c0820050013001c4125603d07500103800038040b0700500341e001c000410b414461340e0702d01208a44170626405050040c080d02066036218801aa40d464070105401c01294004580d00700060312084072842c11482880c105022020010800407050420480080980c005600c80048061190300c40c07002041300c0c8109000c0945001c9010b040310002030400f804002407034a9102c070408404c4111600c806000c1c0260b24562f0010401200080040e10f807030761028014001d250007024503002d00001d40b900700c0700103080101041c401800034202c0c200224244001407000203888414003001d1071041001001450340e820741070442c41d44105000b0202a00d8200c188800c03030040e544483c5c05a030245640400040fa9200f480100c030710004000b40b01c0703010100d40401c100401c4054500380f1304803045600c0034030140055080c0c0c4e036100ca140c1d00c3c81501d80007018481234041050360103041d820480604000300c81c107100c0e440b010f0a640c1a403a50051a4200080030000341c0c0301 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 477384379 1250 477383129 477383161
    0x4050c0d05180c0406151b140a0b0a0e060106110a1407050907050408070302010f030f02032802070305031515030108010507020607050309190305040f030f0204110310091a04050f 78
    0x8100c40400500d400d00040030360b1422009010007c000041ca10094222070000e01c0e20f100c2038108034006140505500c003a540c0d03a040100869000c038080000c2500502c090003081003010020014040507820b03c101201c4d0115917044042461062180103070214052141d500c2030000307100042e008090810060045622002d051081000f200300700070040030300d01081240c1629424070b08040058607001d0120f0143c103101c040a103680d8030000c180038a0400c0305a280d06401b0405000c010312007294031105080b80a070500180c0814020800558514120030380103010b401c00400c441c030340b20803070650000d032a0400d030008491a0f40da1028049442d4041144940c002d24a01d40946103280551006840e42e500d4000c00d004911692502402c250280c0c09036000b8044942101c180190780303060207034650500700c80503070080f80752590244001c0c004000302c9100d1076030921812212845c0c0b0b24080d0003064100c3c0889c0d021038a00c0075021850b1358030b000307190294448544448c00c600f010b02c821690411 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 477385629 1250 477384379 477384403
    0x18030c010e0312090118060309030e1909020903100e030a0e10320a05040e0603061005090c07020621060d12030e1903020721020307030204050c0d0518 66
    0x458008490720301d50340042c1d80b003030200c21410715540b5000c190f00145c0d144480140d6206200007003400100f00c1035030680c09074008900031341c1c6000ca448400001c1c0841901d200d03044c0d1107032106c038150034004186160005c001448024044842d805000c0109504891000f00034003400c0c1c100081100322264010441a43c5402c11518585800030b429000b528001040c02c5d00c0c220a0804c143c6080c58034119240c0e6044003814082c0182c1d9000070390740040490f4807a01642d2120b00840010580314200002c3d014400e0a09032040c0d4003003824041080124031004180d4001c00e0405c215120050700e42101600f0b44001c480034000510141c404100c090810007000c1c1c50099000184c510045480d0f581c581ba50340305a810001a400310645115052032204242401f03101d03160b0303800b07008041e80003070713407400b00c0f5a146030142c0342c5503004030040d0b040003d00b200030350f042d400340406002514080c0c0c0036075000000c1c0300c41c56140903860f01001d0103807401211058160880708a03d071400c2542071105c08208a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 477386879 1250 477385629 477385637
    0x15080303010b04050a0e010503031b0a061b02010f0b030a0204150911070c1706150d0209010e040515040c05011409091f080c1f091206020418060503060a0b1518030c01 73
    0x141c148000f10f4ad40b0300900420b00c5080c1405e4404d40c0412030140510010700741c011009024692003003006c0440980e01070801001586400c407603091403086880f421a00100090250842940c03507005c10000d42000c3e85520401807400e1400103448140303111300d114002c082c99034a925a006814504118451030f405466010000c20314100d07814400f044142e031003401444c1d140d02140c0c3c00808540c8541a2500081d0401c90744000407400712084d401d024840c0d4858011210b0804410302d4403d00c044003541d0003444254590001e200d0303580640410700b00e00c2100c42041742050f41c550002050000d055030381c8a20104030110284442e000c1c50580d0003e00511002445041400400f280c40c48402d1203025030913015103803261661504c1640301000910650f406a80912442c0c1020070095100c0d01c1f812649405444140801400501505c0102d40005000e40160742e140702c040f0020701400398805901052400d01d0b849961010703405000100e00360f003070b000e01030200f820a240c5070064946945041c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 477388129 1250 477386879 477386881
    0x6081305031306020f010b040632060409020306040c020703030c0611160f030e010207050109030611040b0a11010c080402010504090b01140c070603061a0a0c06090515090610031515080303010b04050a0e 88
    0x104039a0070a180685c0040740b00401c2b081110030a604101c442401643c0c04034000034001000280c40e009540141c1003200c00700910500500181d030b80300c0070340c0300003004621840d080b400030904aa000c01007503001030304842d142420701c00708903031005078035030702120380c01030461200c0189075004185006140742800140401814100060a0704445100081c08103846c1c0b400c40d000c2e0400003054900902c01071007440d407038400120000d000c0b03000158410314290302c0c04401ca07800510581d1294056601078480c07074506414411113070050880b40303d1907818841805042d04044a00c90b0003881d10200356170140c00d0fa50305007400242602c174250b002d0b1850201e81160a1200c0c04010202c54a000b00c1d030500c600904d02d5450700201a102c099000380550045c1d0041c00317040003840e084103104030b201e1000e950781c3e5540c11000318180c80d910300025000c4c520701880c90602d51815072043e00d125441141c0d902582da5524178007491544240c2122a41c0f060105007004541041c40f6901e018080d046c68015203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 477389379 1250 477388129 477388139
    0x30415110c0607080c1b070b0d050f09030715051e010b0a090506040803040909021c0b060109060516170702030a0c0816030f060902062206110706081305031306020f010b0406 76
    0xa170780a010200140316199034071010f03040c41304001c404024441c501141c5d4581000c04000d50061000322098800080b0740700001e0742c4080003104a441d060b40c01101407400385850156980200b5004003a41d5010381103018403500950980541350085c00c86046031591803007120b02c02007003140395510035801030702c00748400d220034003001c019242500c18100000414a440c0c1c0001000e10f0740740b010340c4c400303882d21916040c02d0042c2000304511425081e02d40098955458070b0485152249188001600158040b120005034229000e81158170008003190300341840c4d60002800c0034911a41211950001070f0700704800071040c0110307011030000c40010601646180c58407171100c3c00d100c0c0e00404180d9034032800002c65488805403050054044c024441a80d608c18500c000340705580030360700c080b83d100c0401040721840001d4160035920a0f988908050300d42c042d45100c00008000100d036140030900408034060781088000005107407c2d4002d040c8410364140c01804c45d00c0308407185004074200141401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 477390629 1250 477389379 477389401
    0x12030614030604290a0609112508091c060605060901050d0e03131805220204020711030313152a020d02041811030102120c030415110c060708 62
    0x241c000d03003103581050a402c07020109155424051320909140e00b42000380000301c8050f80c41340081c1c8a018501b000301104007024038140e4003a44820f07601d1101101c0200790300d02041c68003024418400d2001c2410101c0600c00100e461150891484000030748800c1e1a0174000e040c000c26008000581d042442c000e80040000c1c0f045c403035400c112441300d07119003110020480400445c0c05010030f070203826020030780300e28010900300410900310700740300d0034600480c070130404007142003507848603001e0020941c42566080c407001e500852000c0e603840c0c40c2900503030355688045c070013001c2c035017000d5407458403250801d0301e0900380d12401c11050081020b9064400d2542205290704250008150030401200310f15100007220b0481e41c0d40000e410a050070707100e000403584070f001300c10010f20900710070006009160a2500700e0140000340101c4407922408129404060310007140c21a0081d0003980b4040c0d040c580301ca060340c2d0859034a488486001400005020050200306d42000e0180b400b60402d040c2001011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 477391879 1250 477390629 477390631
    0xd0e01110a0527030703030804030f030c0f1b06090507080706020a020603040b090a2001091d010b0915070506060906090403080106140d050c04150801030302030f0306120a120306140306 81
    0x31440600c3d00058402c0d2030710300d42c0380300004070040c00c4620396600c03454000c20307501c0207440481c04184140c1354084c56500a002d001d4030130f540d03030365141254000071008595404100701c0c602001c000545106001c04d581e0b000303a5001d43c0c0500c0050080902d0403082510748a1264010411034024040c1000182d441404403600700b90010302c5d03641d0070b40b200c1a04d2070601140e85070040240c45808880c6d5200298081c80403400d0000341c9410b45000d0340c40d00000414458003282c030400f08214001440901002009450303801c0d806008844840030303890b08010150b00c04002078a03960b2048080014500c0e14245c0e042d881103099800b10a6030405039405800340c5818040e41c81844491840b20052805480948909043d0b0003c144030700d042c1400481c015601c18021500480c04c520607203111315000da44098100ca51540c011468916401381103001c0713410140c17155a125a8200e09145410700801407240c03454040d0603540b429036a200c6021f0200e8415511041c2c240707101d08640f0b010f558010501d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 477393129 1250 477391879 477391897
    0xf061204020d14010e0714060a0203030118020906130e010506161202120729041505040302010b040e010f050117100b0301140c071703010f0512010b04020d0e01110a05 73
    0xa0548500e10310f0418808058a01c0c00000e543c640b01c001c0c00c020000041c0b080c2258018001c44800120450502031700e480381012000c09a8804c000401041403120414074102172108401402c041c240d00014529a114040891403811680c0060040d0ba6112084900400c03080700c21b1450000d0189000c00701140100d0701910880c0c045405100840c024042c0440312040c800342c150703540c0b09628010401011111941440600e00b5441500e04c8a200356240d010f19040981d181d501c0c0f2403012141c1c040c020081c0100e0440d5260740350319a00da101c9000d10100303c80c10000110311031071500d03401811034030140d1003400c18007a0382441c020314510101c0e2244814124002c04100380902c2004240502401402004440d000350200050f55207541c011304a894401d04030041d43c5154140c4401980c0002e0003a44051030400c401007105140c20707403001c40c2103a050800482c41d80c0c84003000500304d0b04201402e00015403120071480100e002071090820355914403103158140702003450000c00a008007102 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 477394379 1250 477393129 477393139
    0x100801060f06090329190e01090c0510050903060403080601030b030c100f03060e090c010809010203011d0613060b040504060b070b1f09110703030b040902010e131805010b0f06120402 80
    0x56210302503140548400b08442c00d031401c0031070305114142c041d08040c06105980320914014004840d0387c01030041ca1406500704800d4400c041c00c000030060345041081842d41840010007410f002c1c1e031410320000744150b000e0f8980168616212001400307540c00b400300d2511941181a00303510507540c2c5820403c00c40300381e2a21030341c0c0d0042c4c0c0c0002d5004044540000e125142d11004001300600c0c0000c1c000f504500a99400105840d603131705090a0340828040c0f041c3c810701c00400181440c0c003c89034664065030041050311807180c041050b10031201e42d600321640340903002074144103d0425000700e900502c42c8106181c0703001805e0300d5076a003c90002c0e01020508641c400e81c41040410640c0031805868080c004005648050300e481d1010b03405210100d000ca0b05015400308070b0f28103881000441178040c0c41d010b24402c004000c005d48034000410121009581d001140ba520106600780b09010384124000210403c609040152028444082500c0391200300308500c80c03101002c05543d003180c0d040d24 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 477395629 1250 477394379 477394403
    0x52103060d140102070c030501020406020106050a0b03010b0f070b0403020f0c031b06130510020a0303060b04470403140c150901050403080a1e03061d040515100801060f060903 77
    0x82e00ba01a1003000c3d005460011410f50110512006500078001c6826540080040c50782e200c081c0301c001d8406109081c100101400100a000c1e40d00c0010901e80c11030010940ca00700c02d0343d4803412094000c1d102503005a2002d003c180f00c21034100b064071071044040700100358000c01007095026102150851600410000c0355046481c842c0a0000003e4080208003c06090711054025a10801600d0507000a03040210000d5032020500490701600c003000c10b6201c0c0d1000b440b50394034090301d51581d031066100110302e4401c2c000d1140c80c1201c040c4444000c94035625851800c4c1002d0038540d0080340c5a454001201c500d01c1030b07862030001102c2e108904c4000d61941050030050300e01d0301a50388054180710300085d4808d04941e010050421010000c0d0044141e40801c480403000c892640c010382070f02c030f0300080300304e0500d02d459141079911034421811600d40480c0d4140d0000e0084050f034400560210b003440a2000c04803e00545010380030400b41840d140346001801001c0c1c080900c000340180c09002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 477396879 1250 477395629 477395663
    0x60905030d1e0f020f0f16020901121704080a2a060903060f0506240d09030807110a080a211d0c221d0a052103060d 51
    0x44203440c15401d650108124400314080a444490480355180426a140c1940c2c88540106442550310000d210205107040c1800030007194000e903c03455610039085440d1072a0340040c0d542041a42c00380c40800440c2c11500003d1409180080c5031104440b0355040a010601c0b07201d100080c0a0750301600560f580542d41c6c18072529100f1910000807200d04455440004a9090303000b51000080340c0c8640b000f0851320000940c06400c956007075030020b90111502079041000c43c818414450b0030344000c040c00c0c1c540700d090420039040701c1e240103044000c40d00340010002600c0e00880000b99469480e0702925000d5996500c111030342c45070260100034049986a01d48601c6411280c641d8001004201048003a003003c1500700d40c1445000751140794890500350341598182044c1d51484004500340701d10405164084104c040c20318a02c7c5213549000200040102c0c0c0c10070050200c82c1c0e406100900324010442206010310b0300c85c2c2d0716110320940f0400c140403882c0c90b02640500c007603810843d40a400c403485 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 477398129 1250 477396879 477396883
    0xd080715050a060e090a0c0605180d0f0b010803030403050304080d0603050f0f0d0201020c07210c030311070e07050702090406110c1e070b04180207080c01020a080c0306030a060905 79
    0x525006040c140341c041000b03010369842e840841a00ca010450b5126580d4011901d0f54400c01400c0040c01c40d0b051020070056a402000a054480150f000c200b80c00740c2550041450b86001e035000395162101d0010110900018094483c05000e070140514954501918094194440034100078010480080d14422000360356220700b029580c44001d075545003403034500c244e6492801c0071844209002c0c00380e141e40340d00d0051089a90300d100d810040c0c0021880c281d085254000c20f82c01460454403002400f0000945202d00003001d94425129110065001d859952901c04190401c00301064002c061101c41a0400190358106074110b504840382d40c0c0c1d928000c00074104e45044c1000103c80030420b41e01d94800400d00141000385500400d214801c03800400d40d60341820710404903605000c21051200c01e0220314103002e40790070b201025242c0701c5280d8500d0714070340c0301c4213412600e6580411906251030b8400c4616420400f6501c4090440c28030500107134480f500020018009503803041000200f16007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 477399379 1250 477398129 477398153
    0x120302070f0305070212190201050309010f021b0c0103021e030612120c100b0d1403162a180c020123010303020706140d11090d05010204050f06090d0807 67
    0x100160440307075500c1614018180340c201c18400c9118004603078914606010000300d1500210351b064045110f98025001525558005400c01c1555521541007090400c4103000801038101381181050341c13060814461410104081425410180100b00c4c980b40180841c03085030b120042c82c00e0951340e07070302d80f200050f580d400314031a40602401280c44503842c4000b943d003d4881c41b200c503c203031a0318101d500072100c102d07040b040700300384c0c030100044120000c03074508507d011304080d090017102d20301b2007a040c104142809514080710810704118091210907190500400001c46041c070b200d11841c14552440c2d07140800290030141d0503628464528090302c01d4000703680d0101c3c5941d008240f0240b10410806000d42404280c008d4415400c0004440d480341d9140f05044a5100c0c244d428040700c10b800001030038110002018020060003000701c07590b228400c0381e902c207204000041e40ca03494030091004d4403d5034140720344125010300200340c1c82d0b101c0b02d10700c10a40703a0051a903a910081460200c1403101c0d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 477400629 1250 477399379 477399383
    0x90f06080621060a150b090303040e060a0801050c09010f020136020a0b0403060507081605090d05030a090e06040908181c0f170901050a0e0a09020c03120106170412030207 75
    0x100304400d00003d601030703a010804a0b0303070003178404c80300c540c1320703c01034409100c2c01c040e60f50542d008110800003c030a071b40c032403074004100414101c10a90746101e000d003901d20640e0b040c1c00802000969000308d40e04408a040440205c0c0001d01a40400030380f12071214101c1080240c441c031480c51103100314880c03000301038545075000b04403a40454540700100d4082e0450300040f55054a803001103407845001d0702816100741c1080c070802e900040703445d10032a0150410342c03c0f95000340c0390000e07440019005101130f01c03c07032000e42e840125261800140d0004004050a068040c40c902181607011400c0203046403c1441d2000414400441c00400318568991040523090a0fa00c0500b100e41000641200d20110901400014610070301d075000880300f600c00c41705a00c6c04100100054005a130080481c1090402d004090200056580c40b402c4180e0307100d00e4001e2001e800001d0b41b0038540d1000001703940500110f207030142c60300c3c00e1036420f0340c1090300c05440a00105d00140106110600c01e4040b1001d0b00e03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 477401879 1250 477400629 477400633
    0x90b06010c0201051317100b030604031d0405010801020d050a110405060319050405100606050913150b0c0a17071a0a0e07060504050907080903090d030203220501090f06080621 77
    0x590f10665102e000031500181c1d811b40c05850b048400700e2005011346404404024054a441e803100d507030a840502c0090009500301c40301110071700070341c0d456224135802440e2407000960307a480404000c9085410090103000362510344071800c654603001c28141d409075101030780da803a600d45070102c0407001c43c004003011216076410f010800c4100300020a0520300308031007083c14821982c032120203543c00d001c1c0c60316080c0c110500100a07190120107400c17400e00035030440f256483c00c94850300b40404591100c4e82e0050254041c0c0c010307104009900d640720101071824202c0302c0c1001e400d1390701c2c0310849000c83c4400302403890a00107e0304110055200039080e08100b0101d5011555509d0044e0058015202c0c25108510303000003c2d1605005182d40361040000b078010310b103405841000c20207001c096140a40841c4401d102c404200600c6203448202d01c0441440c003a0f007545007400061070502d03207402c42c030b01011148000304202c540080c491500004200c9001c01901ea1504070f20200e400017082030718442c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 477403129 1250 477401879 477401917
    0x6020403150624020c040c0c020a150804020402090105270a050a231f020114091603120e04180519080307140f180901050a06020601030210050c03031612090b06010c020105 75
    0x100e23009000a1013207071083d556165001c0d0b49050070800c0303191416100300451020b400060040c070b0154014211150141803007400c00149120005070b948120441302d8542d030305d84159204900e01040441c00070182200d5080780c2c2810001c60000405120700201c0c1c0c0f1148103031401c0043c0d0740b4030a0f00c0d1041052950500c041fa0b1110000034007a1080384107240c42800d50502007501103101040366440d500140905040341441c50b42c3c2d5000c04105204c0c1c40b4108440a1503400342961076014401c01101070503500c030301409581c02e10900381204444040c0d007441141a041c0c0000b090102925406400c500f402c204a00381d0611003040d030b101e843d501d140d007500c1c0010484501c00041c0200074000c0303402c1e52032140710380c0c80ea011b10079a11031030700403240964041c10041006261042019140306090b04d0031600781147d2240c40d40c61a08180d54000303c104940d405211a5544449100c1210707608100501100820b512413001182010b0034050402c4600b800f80015039004204075503031200400d001402c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 477404379 1250 477403129 477403151
    0x10050411091609050117040212030d020d09060e0a0f0f020a15020109112202160203010e0714091e04050a02100c030207080a08040e0406090203030706020403150624020c04 75
    0x502c0c50300010110108008210104a07944110b00007051404020354203001078036143c00300840f402c100502c0b40388070b00c420821151805542c1c005041e44515406d03012444100a181c00c0081c1c3c0c17038050807030240b940450303582000300c1d0040e400000c2e040c0d00841c109800b401c00e80089051041c00303404c610803041880c4051149140e0540c00484114080e00240000000c0c5c1420003003079042107006d5030030707071101e600501c0302c00c0000350300030101921400caa258051416902103420b540c21368076007000f643c1214500300881c401c01c03111000800421904201540303021444c06a403115800307030300002103507001c00007000c00108008248010790020060f00e242ca001c81c4c401132414800550890040c003d00b1400100202d0005101c640c1c554880659814141401c404059000e0000c9c41611515121111200540c500b0310091082c01e000300c0c0d01581d101e0860900420341518000f29a003110719040b800c05c071001c01c490740d40300c160004501e50050210042e03c100d191540600c001d55200d450030180f560 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 477405629 1250 477404379 477404401
    0x10b0a050d0504080414010f05090f01110f03190305070f1409040e07050310020304020a0302190e0406020a030c050a0c02041109131a120c0108071103030f0403021902031005041109 79
    0x108841401720481310031002c8000440d0000311801040009c610244030303c020386d2420002c6007181e0710040c0341c02000368061000092a00381c18544000d403a4100013181c4200003c4440300c409450034508007030069040100c8010100364000400030200300051052a9030039024408803272101c00b00910034020f40200841b56900da40152040c6840b034030070b114540350319000600a91707200c0c2da0010680e4941d10300c0e68081c420484c481901c400c2115030425004981c0c0020748107298021802070a0058461205043c0582125140306010781809001d12440403442e41c0101d03040e240386d60540300407484488001a004807401032900d1311354050381407a01e4912400c3c0562088058032040d4022020105509092002c542c81886200c041e0b50007000d01d042c034a5002c0c025003a00030b003092904610804071816050b08580040d45d01005191141090100303259040081d10410032546006480002c51940040da0b50350322141c04846540d190030005050103401d00c80e2201c0e104028089d44e0981c075000800780703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 477406879 1250 477405629 477405637
    0x15091508060109090c12030207080a030f030c1e0320160b0f04020a0b3019062904170a060e031c020913060b0403020a1d010b0a050d050408 61
    0x30880388a16000011148214000c1109a6800041c1015081e0500d900e103071800002070743c1501540b05124002480c504108000e88500f4083d56404980e8001d07400020300380c0d00d000c050003081114004039000002011403046c1040c010f03e0400095848410074003080c00c0c40e41015040701c02c60003192515204011030031030807005215022040b626960a070036000d25a800380e9010350041c05100c001d100740c0c43c0c45d400034a1225021040d8078501e101a000f418100201040102404440103040c007484a04a00c2da000c040c0c0704810050040728280144100c0303540003581c6a5800301d07803103400c0303501c3e02c444401102c0280c06010a06010b06400701c1001e9501d0b03440d00021200c2901c1d11480c0e00141d03001009840c40c844040740d48003e0000c041c1d00b50b07030182d008140300c29071003d40100c5240307400e12140f00d070000401c504106a83c840d0320714010015001c91030360010780145000341800b101018240000e9042d180f03552441502c0e0340d528002202c0c91f000b030450300780c5414580310900041c0729880b0060 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 477408129 1250 477406879 477406889
    0x3081311100f111209060f12010906090f0b1f050405060d2004150807050c101b090305060402060304050a0c08030913021303030338030607110a0303150915 68
    0x20082804007604003540e030039142900700c032402d13014041014545010700043c40560000c03006c0a0801601012500b4074103030a03801480031584c1e40d0401c00403000c15002d201142d00701c8540412a065021010078000701850508190b140c1060900300402800703981036902810000c2d00554880c26580d160000411740340001850f26545414089020034403841124280c42c0d0300b14400b10340c030040120580301e000c0054a00340a01000b40a0291611020410300c2c50030210792a01180d4400300032111003e40e10284000300400002810600208400040050b00154195600c0d560703590b480c108a410030600c4500108152403010000030a031000001411025108440141040d000c5000010491040702002005482d80350307020000b0a010394030a1101144600b030a50350340211400b00e10b0042404500d0060800108050101500b001c001140e4084aa0b0a01d0352103d100d11540c90b1f650780019000500b09a00c803282c1082c8060a903802c00005c0c095450284401c0a03864040300b1640240d002c1c0e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 477409379 1250 477408129 477408137
    0x503030604110a0f12061d06100c0c050904170c0705030c040c0e010807030e0703050105100801150b070f0f111216090207020d080a080108010b04050403081311100f 72
    0x4080907411070011203514903c0750b10ba14400c420881400d4810105007200801007540e25000050740082418645001c81d4403201c480d80503292400402ca2a291800400130400c002c0b00801b000007106042c0e5201521001c8503684141e80d110b2400c5c0c00c12070001800d0603880107001c518030201c07100004012041d11070440a803503501200005000c1221805d100f030b100014103040e88034003a0350080b83c03001d030050140d03c0c0c007180010300c1280135854500305600888150f0354035410000310403000079040d406002c0210003400142c0c4096290410316095000701c9140b041300198800402072122102c03001c5c0c0d5801141080c10500307900b0721a0040048805640c002c21300010042042440032800c6900002000a25a4400d0500c00000b00039009481c040741c0050102c602113000c510f07010081d00c040720656988044940c140340c949403c0d52203c8440e41d0155042c10148000641c2003091140d01446403014113034071403110701703200074000404840c1c0d075000102e0b003454405030fa6001e480d5810882080c3c903 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 477410629 1250 477409379 477409391
    0x6040f06080c03100e04020d05010501260a0c0605030c130e01090e070f1401200109020a08030901050901080a1d030c0f0609070b0a2307140d1205060402040306090503030604 76
    0xb036154621040300c0b610148025a5014040c0c001d03d2080c2d25041400070f8800d50000c941c0365500c40c01c540007a0840d0f840c01144548054802c0c503091407401c04907550340068203c1c0c1243d03075107103100c1071141e0140c0da05100003c000642c190080100395070f0b58191700340091405130380d20700061541c45d0007805580040c900705050340f000c1040005031101200c9407070741c100b10382902d00401c0d0100c0d240701001443c10000768400d000300d446240300031081c24010350000004c984030301380704105051449520400864005000c2012030303a8010098078002182801d107450190380e40204000241030807061001000c081c010400903034503000000d40602e5000f2001ca42c0d106002260507591000103c400801507070045c0c5040c02022120303400342c2141d54407820414990f0f0408452408081802c0604134060400403030710400340030428051122151080d03019108151010800902075040688203121581d240d40c0401c00350f40b156411a00210f41007030307081111070064030342180c50ba84107603280c1c1d100c0c40c02c00c6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 477411879 1250 477410629 477410641
    0x180605091005060c0c040e0601060806010f0807030b01120e0d0905032a06040e070804060f0b030c0d05100212010806011d040b0709030807050a060c0206310206040f0608 74
    0x2640c80d5006891071044200154944002c002c0c996100e469040d2250007442070f0540e13907496a003d52643c03a6400c0000d4482507051840c0281014001045071381084840d01000f400540c001c0c0d000c0750041000d01c0c011414460030801070391980201c002440b9270b10702d80580070000480105110b05060025603684c580c055403401010703a6010611500d051740d00e0f121425a401e030501404d1038000e9000a00010b080c15a1415500d210110032200c00020030740304c0f001c120400200d0700c126a01d00c440040100700c404404004290b0382c00b142210346000f22901c0311030f68103002041106c4044003002074010340d540c011188040344205804c0c441c48606116900011611441805984201070350b48034042030079944580716914214009003400c000e102c04520007201094a800c01820000d00880040c00c0d004618604003003143d803051000b40441d0000c4081c4002c49012112210683c81419036050042001c844510600c2c010854002d62003c000100000c03401308429811040f10403e49500169503242 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 477413129 1250 477411879 477411889
    0x12030e10030b0f06070219060f110a03080411030a060203070306170f030306011b0f0303020c1b0604050d0302070b0a090611070b070210021c0305160908072607180605 73
    0x240e6015a445402401d1441d100e04250005d02002800144a0400c1d411041ea04a11450468100305c00007102948203010f259084643d56000d0f110b0040144101e1a00341c44c0101007503405040108a0740658100300f40b41d65040000701c400c2a08a10b003150f0300d0400d01e0001d401044c042c403550042d15600e0520121342a00424648159450000a10705e1581c5807001121541e407410301640071940c4045007280810300759078440a03c18829180141d6030302c2c1e1480c00600c0c00200c460342000202803680000d1950302e8190036181181c400761105101100706103020303424200c85070071190aa6401096020303102d5849000c4100300c132460344510040b10f9810500700e80350000d0b030041040030001007182c240141000b035040d9548441c81d2050b07030352181c0791440b10b4110b96010803a04001a4444c1d0a104500d00c2e441030814008500c2d04111011a20784010191601518441c8440f985808214001c280c40c550b1400d0000000301003e42d4261030305c4510700d400700078070080710b40101032400710f012030f45040c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 477414379 1250 477413129 477413141
    0x31c0b0f061306030b030f1c110105150111030c0a2618060d0204090c090f0b0c0a020d03170901020d050a1e0e0705041e051605030a09020a12030e1003 66
    0xc1010b000c0704034103008050740a403403c04030141c0c252148884507105a43d007400032901900644440030440c4c0b408010060417680f10312920803d45c1d14000600c140e034900444440742d035260a003008001451b40066050075805290349505c16406081d0f240c00400040d42554551015013000c01c6100c07500c42da100d001329014a032203d061845160340d5401c102d01d050409001c40740000310000d450580c4403001c150070380e015400c80c41c000c40ca40e60014482c030418100c02c00c0141a211b89180d080c003025040040c4c0e00c0c0e07603e0102074040d240d41d034404014548204680401400c00e15880b29880c14550b2019000354840141030344424540804540e032010756001d8100f260600760341d101d6141d941d59001030001c1c020f03403038640c00314864180300151513180c038095410b00440700100041c0403150040001e0542e00c00520000140b0f00e4012005407e43c0c100082d40e40281c070f10180010b00881a02c04911700320940d4202d480c3c00007000e4140010075512451102c580407055803807604802d80b002c401c0d02a140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 477415629 1250 477414379 477414397
    0x1b1a37030f11030106320a050d0b03030c03090d051203011707080d0503070809012a080a0501060c0f06060e190b0a0305100b0f10080f100f03030c05031c0b0f06 70
    0x20003007501c01c00340000c6e0f02c602d0005200d08820680e0035100440c0c400c43d5070000c0074807c0402c0000c528010054050b12591a0045042d4055454065814802912032181c190702e02cac42417846101c01018413038100030707412641444401d03840c2e032542c5643c01041080910b101c1e10815200d28030307010482c20303000b240d100050649a1503a90071502c50b40000d0303030100802040004103660b901c0c0d00082e2450350072080c030a245035000400220a004c202c00415140008048a1200342400010045258006e990517162030300040b040d16408100c0c41c1060251020342c0c84000b4404501c0144094a40d00c8440c03404810400c402c00c0101030209014002040700e1440003034a0f9070400459001910220340100d0700f4800010000038840740240300140d40c812280180704000303000501000200d200d00c605d41600303c03040b204800c84262801440e964040c20398040203081051100144041100800030b503258051382224814600040184040040c0345100c11544141072030a00a502d03030034600b04442c2500c1c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 477416879 1250 477415629 477415637
    0x90c0503040201200133050d031103041a1312020d08090111070b120106080c070201030c031404140601060507050c0d110a031b1a37030f11030106 64
    0x541c0d5900107503400d906242424076260720700c5040091400302032085078038003561003182400f5007907440d80b04102402400f840c54451480c0035800c0c84280e403503004044400c0d87c18580481c42400a520f40ba0071401950700c6107045007206501480d2044001019000c0341c0b41c10074042e0b00c0582e0b620944800e11400020203504204c103c21a44082120708004040d40d00044c180112180d81c00001107203000420b50011951040c003003500f00c0d01c80074800f42e0500505a03071500c42030a0034604845e400a10071150001c2c18540d43c0c681c4100d50034020780085041904d000d55848091409041c1240c003a0a80e02c129202401207000100d80310303000d00c0955030590b82140c024000c01c4144410b1044d80401c4c0b81007640e4181a0603d9213540d503440c02e4121020350302c1f42006072110300d50341c0380e0300801000039001400600004a1030350746114450003a6007000181003083e9507449600e0242a07441403040580c2d04c001c04005040f03040042c3c050b000914000c0036100c041001002c001400705e80742c0400c1c01500005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 477418129 1250 477416879 477416881
    0x603140402221503030201140105031227060403030c0c061b15020903250f15030209210c010801050f0f011d0a06030507080f070807050c0304081006030b01090c0503 72
    0xd49610b90b22012014400320001840014008144080b0446600860041c0e443e0500d011102000c4490f6900410080d0020001810000000300c803d00039204c20020481e20090401000f00b604040402a00006070040e5a00c5489040c01441c80780c034101c0a07100c8100000300082c0c500d105a80001d88880b010b04130140c411000c0c0c0d900840c0b002e0f130701840184540c090081070050b560a010303500a0070007808940003281201250003010750302a5000b1499a03514070341c10440c0208041e009104803125203001030350342e5002000940c4001000b9000c850404100103010b510507400110b049260078240c80c0d032403c681c0e8030000c2115012807400241d40162042e41d5881d02ea5004848201030107480040440c403001100c7c2c04164403174903d0b031141c00041e4489040c001019041080b030345c0c002020502c0b802503032411510242000c40702802c01000c1040025480201e8603040c8207030390250805005841800c4401c01680000d0070080c08150340701c0750118000a9140e40b98400c2480705035054940c0c80c29 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 477419379 1250 477418129 477418159
    0xe0a0e0c10050d0902030d0c05120408060c0a1b0606061d030c060708040e0c070201120b01020a0b0601050706060306020414030714270708070e0d0f1214130603140402 73
    0x45500035680e0520390f0b68684000b6401680d0070700c006021301400c0e9580c00340c00000d40c20a1032070000c1101d4280560001040103000859001c1182ca50259852010903038612151a040f00c4205010001940e030a040503150781c100109034000700100c400ca943c810580c00441c200f0300f8124030b00d1079000ca0303269001e01c59884050a020b009004945c0c01545110704056680768180000351044520503c25030000403240c085603004a02440c0340a0303110300400c01002c1c4440041c2d900c842e0b00300080c20034100e0000062041e03100704212080180c2c0f102043c84600da807403611002a40003802100d510740700c0d20b0b04c045000c1c02e00040038000c44d402c5103451003803522003070144103100c90003080301081003035201c41c6d000c44094482c00940c09640203645090491030414001800400c0741880980700f12114107400020a50340d030b081503201e9410039130314110300030011020784d4511044100d042b2501c030f01081c80302a62103c40141ca0880d5100d44050100039140f0307140104c0c2c031108440003035000078485c401d111 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 477420629 1250 477419379 477419387
    0x10e0f0706441e011a0d0c0306050a030303060911070b060909030903120315030a05030a05030a02040504020a021c031b120f060815010801061d1305100911040605060901050a12060e0a0e0c10 83
    0xc001f41103030900180340c40c0c0354004181491019002a4042515075400b00860314261040003618141d00c000d05007000c010f640d5030095910085c01091040311000046620108280204c680f281b400400f206c00429444c00003458581040b50501a80c03060344200400700c0c200400e44207822503104001e50700c0d05210400503108d0350000703414485201c0d07007807102258540b00c0d40300400700d0805c00d40041c00540e00f10102c4900d07041223811802d08040c2030a501c000307030898850800208414504014286800181d038100007007001d010003510103410305100203103041020880f000c0403440e180c02055140c0c0c17680a518241c500381d206403401c41720118813078400c5500000d4941d07009617400c81d40103903a5519494051501101080c50072516549802580800020481031071080c5c0303003901c082c0481880e081c001001c901031550107605000e00015081c146500c110340c01100742c0c41c01641045400e84032420b804801c902155001003040c940900d40a4050002540101e480303402042501c160079903403400c407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 477421879 1250 477420629 477420641
    0x30e0606090402181806040606150905100c030201020d0f15061713020d0c090f06050d020f1507050102130e06010320090a08010e0f0706441e011a0d 65
    0x1117145224a5069481c513070003803245501860007004041401801d20303003081150031040050070140070f4110703800c100c984c139418510300e0014140d0400b1502d100f001d04080e80a40700348126a041146070005107500e02001d03601003b4028440e030300c5011a0381c0c0701c1d0015605064030110284583d4100c40014580c10219103049550510103804540b5480c101e07505c0703443c80f000fa5004031040035151049020380c00d815208080003000b0413a81d20301040c0c41c0c1c0c0c020400c1102c6003a1014051102840c0c1401012091012030b480d25900000031990384a1070061a101c20070b850054107403522040000c1340340b0358800e00414040819030111801c41116403404421560700940c10306801a00400300040d40c40402c1c400c0a50840c0350f032015003202e04000c0710b0f0350b003003402680000701071101d8014001a907206241212140c400500e1416840c1e11008d402d224a01d45c0c5445000d400f5a4490100458070f601c910f007164107414140c01c02c0c00c803641c03100300d9491b06a01c220b400410004050080d4a443d41440d0010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 477423129 1250 477421879 477421891
    0x3010e070c061505040507050a0c0803060409140309040b060306180601110312010503070b0a090b0f07020a181d0a060207020a170d270b28030e060609040218 69
    0x10746a084040d91860203036004a410600640c0081c8030070000e9040c2401a19400f400c0742c074000346003225640003d00302c01c00c1c44034050268080400011440d40310390744289915034101b40c0140f812905036014507569403010301054042ea08000082c3c00c1c2d41030407802c1c3c03802018010b102c80002c02146080c03c140c4070000b010541041504070b1540326038801400100540d005441c0c1c10708556042074241441c00745141c1c080103500100704101740c000c03644040c0360380c02d030b4001c0400c3e0b40c1e0f60018020309003054001c001d006907001800060021b401c45c40c600c03c00001c284014014803940002c00c0745114424241130307008a242d080304048800081603035004001462004044080441e19050045a0990307180d02e07a1082e54080c40413081080d81004d81c900d5134003403550040140324148101100801203d129103003442002041011031f007020080f0b1800e40d50030101070308100c107981400c02000382010600c194010300603100414403500b0f001c0a0544171301c5c0c024291800c131814a1302c107445a61001402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 477424379 1250 477423129 477423137
    0x30b010c0c0501032c03040906050d0b06190b0f0d18030801060516050109030306030209090a03021b0d150c0e040b03060402091308030f0f131203050c0c06010b041d01060503010e07 79
    0x70f0918000340c81c817610310b2209080d10040d51079609091450007250103640000d482120310903103201c000ba030001c050f50b40c03080c0c0a0b20840c850101c118a00d54003282a500b007003007100404209a202000e0380310103015101c010020900000410703a03040180900030050207000119514010300c00b00707010704028401d5010b00002c5a00c40f208a8550500315191401c2c02c80c0004c2e1281010419881c207034002c182c0081d59600a40154803140e50080e565901145140c21041100010703454581d0700d40b0341030702110790003000302d04003040341c0c0383c50300d00800100d00204080340d060208081682003621503050780c031102600030300b89074646400700013400c05d00918040c84210600340319000103e00e20095801801d0006040c049420040f98400088100401491044e058803142c9008074000a51400c000b000c0c42c02c0004040d211100d10019a20612028110b24851a000007504040220041040300c05520742e44404a80710120999511001e108100000f0420b000501151034903144164100c01c1a0030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 477425629 1250 477424379 477424421
    0xa120509060d0207030206011d0610030902131e1e1a0a0b0702010917030d15080f0a020301050702191712040605042001020a06050a0e060408040303030b010c0c050103 73
    0x4002612980808580b2824035008500c00040603010400710b40074088826004032810369481c203600d69044010000d621801660590140c428080d5000362990340c0c010b00794111081801c206400601196035484a088091000c5444800e40c10700c00d910780d00b081c800c0d020403100c42c4042248050700c00c052154041020190520344150343d41d0149000074440020029120b018500001d00071a905603c06000049180340c0b9100c1a40040304907034a0820102c0000b41c0074450100c454000138060700081c10901c50040324250004e270000300f207a0450b00c21002445155a03401d000c0303032140803000d800c0c9a0243c500d900300c40000c4810302182892218900d049081100c1c04074171440f0303107606580c142d41803541e079030601c000d001000e0f050440b24144d508a2500324224000000e40c0d035402064007600341c0d562100821000341c040c0c1c000700c0c502d800f204102c40560600742481c08051f8030a02c803c4000c03a151041c0c00496502484108054941007104150600e280ca0b00641c040d1018210051101d4110700c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 477426879 1250 477425629 477425647
    0x14040515120906010801180201080a02070f12050c0f1629030f18010603170f040905010608090f071505180405010305030c0c0427031709160605030403020a1205 70
    0x1001d0030307114010420060800d540342500329030031503007100b840c0c0e07200c0045603160f0000f42c0d80014a8035009074901c000180e480c0c8150600d000003000c4220000c1c500c00504d500c4039522039114010740340100c080030507101040c8000102c92307a07801c622154101756100b0810100211801ca240c0c2d00e0402c0e2904035956264400c40170100c800798011600440104410018003415511100c1001d002d1045100200980d03411030b20b41c1040411003050701c4c0346c20000081c0b0006110a01d00c00e031001401d0a07e414085961501e1024010784803c417200c401d28031508402c2c010b09080010041c049600701c0c40c080c0007016042c0380440303072a40003d51410740b495881e00400e10a4541d0701c1010f00842c040c2c409103403200c021414803803c00400c6900c0074443d6003000240c6403102d1341e50004c1a124401640320711030610030b501d02030b074100c58032100040e80b403aa00f1040050108002c2419003c910780c1000200c003a603210340d02541c3c02d000517203001c0c0050b80070082c00c4001402001728060108001d081241c14400c0c61 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 477428129 1250 477426879 477426907
    0xf090215030903160507031e0302070512010902090c09090603070f0902030606071a0a050709080303010909020a080706050d0507110c0d110a0303030f0e010608030a1218080a020c0114040515 83
    0x14607007105d1aa000c100c08109101848801510440d449000c0100700c0c41940c400940d29002802654491080030000c600074410075440b08003c6c580c060911800b52070600c4504440e908409a118024203a80000446601d004a90355007592a000440c03e0841c0c20030300c205000790001481581c2080e800c03c00200883c008a0182c0d82940304401c40c2d81d03840c9400c5404d003090307c8001e0812000d2007100320052240303000100a0320f054a0b20090005809a09800054031220700c547c4041200e0003100070100d500b992000050010b140090014002a110302d0340485e002c10580c981117040d9084954100d0081c60105082c01d107050151080806000203400000c11002d0943c2c400c601103592104007100140547c012040864030410081055620f800c259940b24818440c403c8200413003602c4000101c0595448104041381054031100001070f5443c0142c00b81d4411510403000d4801c4c05600440b646c0b04e4210346090007070002d290350900d0724180a00218180d0410303803048000e41031200e40e86035041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 477429379 1250 477428129 477428167
    0x609040509030d0c09050a05120102040b0c060714030106121d01110720030715021603030e0f0a240207030219051206040b011406130b09040f090215030903 68
    0x20744000c0e60741c4240701c81440088038600d0b0106424029030383c90030400c650f141c1740c0020480b001070300e5218400d10320340070b0140280700c1c5030081d100c8800d01148803d2000b80008283d4418181601c079404012104825440c03103000912400c1c4c00224640b403440d5a642840e0040c1000c009032001c42200d06406484440c2503540c45214913271102008550782041c4802800ca501e64824030207100c0008448050220361500000d0040f290b1003580712196000c818400c2068554080182003090b490310745920303000300700c02c1240504a104140603840c02146c0c1ca0802c030900c5c12140030f0b403021006d0583e0388244d911441000075900c03007940104c1c040007015884031101c24a40c0003d09803000244d60403d0200200115185552003460340100d0401002640941030310f81568100c031201c0000d04007520016110307114001e021044039101000000383c8044030000385c0800c20f402c81c0c00b807102c0081e0705503c03411240b80000180d0b008400d080401480e401c00002907422414190680e0f181644030514660031710b03d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 477430629 1250 477429379 477429391
    0xf0109030201020a0905040506090103030302070819170c130314030c070b09041b0e0d0204060815040510020c070506070804120b0105010201061d06010f090f0807090c090303050a08040206090405 85
    0x500010b103602c605520a000502501003250200074074241903000c2b406103001404010281503000500009004001082d41d41c100c02800d00340004d9880c5280003064112a1348011009000303c0005ca8003040d80e00c07040e11840ba5203918010402880e54071041da0701461030014041d180810010000c005070140104006041000f900a65484100d800e00003181d2220403030801411880c500e2420095004840c0b2034802d0341103070707010801212800020014070013a4045102e40c030a14500030f80000403204510b102c0c40c0290107032034820014a00d03d8040c2c0c803800340f00d00c5261300450340a221a2401c02c010301203460003401611705041e252410f200b0420180c00c41910050074800040007150b038240550406003080c0603c190840400c042403880360340024260302e0500814030659030007148110f0000c40200b84c01110000e41560b030745490350321501980543c1c14110f08140c0788904070382c098030864089a51580c0c03001d140181280080f604408080d1040303901c00d208000018440d61035006a81c0658 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 477431879 1250 477430629 477430631
    0xf060c0e092a1e130e1003150204050901030b0601020606100e0405180712170702130b010e03011104080705190b0307021903090e06040e060117100203090c0102120c0705120f0109030201 81
    0x38040740034040c14a105e5110108080d0200b003040311071400080c804088a602440c106e14030004007654102038051504000e070064820740000051101d40c481c00c5020310001c0e000d44110342c407090103010b0b4a030701004040c00400c1010190801604055000603802603601e1001109001c2418400f41020344540c0b0986240b07a0002c0d0140601400304001c10810b103003840c1c0c0614004d07403513001c5250500401e18810131035581f4540040564002c03401d1483c511401002000324828a81c00c1020f660400d029081480c4070740714001c1154108084081d81a941512032a400c052400364940250b510041100703085005505504025920207009a0115803090716505100c90074554200822240101000d01c07403424000501c80155012580506454468000100460340d816003585080001e006103403916100000b0400101c1001c1142088081e00341c1c01d448440304400300011040c0159032003410940c0101c1000c00c03407450a0705450f19400c208005039205100b090070781a0840d420300009a02503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 477433129 1250 477431879 477431887
    0x503060306090118080d021210090e06131e1202031206010201020a0e09070c15050103020f0306090d08040311250f060c1104090f060c0e092a1e 63
    0xe140c28818a90b205084100030041c00b440300380b07800c40604025074040e1243da000540c0b400704a505070101d0384e5000350482d0114941c101500b044540c15018458100082e1400c207d5695690001c03c48030300a140d58500c22034040c039540c441200003400030076400d0700c01400c59085000100c8503401030024400e42d4004e140c0b00c21145100e15002000180f555045901c104400c451040c3c0064a4903c500425076020400c1e42d134402d003e5525400c0008040c0c215000d92001ca07014030768036005141030f01c0c42038451400c0c0d0300101d4285507131034406880c0241c0582104042400d024801c0040650150180c64800c902008842c0d40341d0a0040850810300d80307040a40d6011440d102102c1d00310014011440307a0440580703440300040950500c8400100380b42e04407900c8250340d84c0e8070f0f08034401d01c03900b100e040000704509140540061074404c2d08e040100703000b4140380340e0f18900918501e1107107100c00a2410281c10540080d0038618224600c15a078810070701080c40360f00b8810100a10b50310303415880c10f40e1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 477434379 1250 477433129 477433141
    0x1b0420030609010f03031e050d0f0902030f150115091715010501080601140f090414010801060e1506090d0b01120c0b070816030507050a030e1201060302011e110d0503 73
    0x1a141c2c140c014200d1558041d10400001e5404200f104c010350b080341007207a554140c0c500c2106c1c035118051180381002d0400c0180100d0440d164480c500c580d1007103003142c03000c00072070b403013241c6800c0301000c41c029017002c0000400100c511003140080b03030720700c4c0c0c54485c01250f100c81c0c0a40c80220519403a048540c0181e04031140440000c110b14090402420107100900e0039000003440e507031160f91b00d000000703004190a6441e54244d826240a014020b109000300810f0030340d00400001d091040f01c9256080c40d900142d08800494400d00544051100c202e0004040081c0f180c254021444c6981000ba00e051382004501d034141c907280039000c0444440c0d060aa0303428230a8020040707400c4100e614400300000400511034004903504815003940c441003803600f5040a88071070103200030140c07090081c4c04007442015848889804454070840700000e0440d0882c10041c00ca03040c034000280070070344447c1507200030000340042181082032407519000380030a601e44141807900c562490000b0440110034888 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 477435629 1250 477434379 477434389
    0xd11011d070b0d0b090124080c090d030309020a15272c01030c0503010b011e08040f0f0506191a010305061507080307020f06101a2701021209031b04200306 68
    0x185811f8145444089810581c5d1500344074441c2c00d00f2503201d54156400081010b0003504941c0803903030002d0000c2e05203642e5210391400b9980811182000440808001c09030043c0c100111494030b208001c1d0902d8075040c84410322100c0da126410800255200d05145010503540000c180618030400180d040c5910f400c05150a4440382d80a82d4184050708a41c5180880340242d00700c3c50002c2c51411401c03036203550034100103003a400100a40030101030388140084c0f200004115000d00d07691142c4460030100c1c4105401200c01480c803001480e40c0c402803e1440398400d0308401d030004001441a81c0018040b0307603204407680000b800301d0b06000302004024865406004e001d016049600150400d45002c1800c14001200d901420260b01c40c0340d0b10540c01100c040c0252900034031868803190b20b43d070304107c0360161344042c80051801403081c4801e580011000a0581c1c040b140c1c0030f402024002034034241803180c00c01d4010466006070340c0340301c01418030b0140e12800d01114048c80c034080d942e0802d1320a0007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 477436879 1250 477435629 477435689
    0x20f0c100e010c030c050d0917070302150f0915180a0c0e011406030103060f0207060513050c101d030c10090303080c07110d060e0d11011d070b0d0b0901 67
    0x40034185000500c89170190021300b16000e50814140018241c0d100e4a13088001c003090103841c5440d1040070410f2010540c000945c0420405504105600d59540059034454181d086820344166000369505010082e8000c085a07041110303000000340e0086031026840c03521068840649d2102c18813a010001c01c008200003601400104000c80641e5901d034010460900c07040c44001c195030f60710305c0c607060307070540780c3c0d054403680d6a01c000700703115600b810f035104407241c1c4600406903040e011b056034021b0540f0788000450080e10046c7c640c820454411501d050030a04000c880c9601402030790030200203662040000e114040240c5c0b42d03403c45e1811030500070291100140351117043c40f410050003002c00c1200d001502030038000c45407440c4440e910b1400358090200c4244d400c10b00e1041070388000e80d2540251600c03c452070004000c1000072280d031300403044102480042c112603040700500b030000d1222100142400503202c00302140d03408020021640d8404241c0c006001024800c01d100401842501d41c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 477438129 1250 477436879 477436901
    0xc05070b21420a120305070c09150303081e01090c0c21080702162309040b06030c0a0e060909070312080604060b130b03060a0801110702012709020f0c100e01 69
    0xf0407051810814103100e42c2404820140500201051003070800c0303058028a0003404059405008808a840301c0c0c0e00d00d031116000440124503010001009070000d0031640705204c0c000030307803c400c40c0d203010803140c000c142044042c000c10140b0220302010901d8800c20005614005040040e4020188002031144c2400b52611085412804038004407150800120094444103445803160317100341450541c24400c4505085d0300000302070100000c6c00800b15485204960039425a003041104c3c20401031001d16a0066400c0c10101101240b80ca0800011460340040c0000c1110036054032030719406c84010303441d0041c0c00000c0201c010890f10f4200b60040788002c00300c00c04040d00301001080e41a0741c0803030358011002e070448080000394844d5140c842d40d00090145100800801c40a00300c2054075612032001a4080b40070b01c50407001010003002e240c1400e10031004003004960518500401941c040181d08094007024040c2150300304c018880300b50f0303980b07940d100010100580803a10f1f0039a4074212030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 477439379 1250 477438129 477438139
    0x160b07080c0409050c07150c1d0d0602031509040615050a03081206030715180b03010e130819180801020306010e13020c07060c05070b2142 61
    0x103118850074004240e4042d01c0009001040558907404c42000b14010004003404201844902901c5411180d0120b011f1010558440f900c0940c40904960b032030000c250031540002d000041e5401058880d0b000c3c4d50020484003010300c0c41030642c000a608120107a41c1541d80d03646e5905d10300820050300d41018000d11096440280c0b291954440e044d16009401d82c42240003115000240180e505005d00d102900d80e8040044440c2010f540c0105950404d800b1040f204600c0800424030049070b6040e00d04803031405144d100f00d079542046150b03400d10142c8084039407135000e103c0542100400ca030208004141c5075079065404900121502050500360b01c14007103a4810010f101c00f60740c2c002e1030a4036119098680b500300b00c02100c1c1c107034000d106003840c1400500076501d01040007035122040c48003007401203041700c540e692112404003d91060303402080b901c5003401004442c8414181c000c80c0d2142401c070280c071100c0b40440803d1110700b4803504018445c03500c585200ca0010036081c9031842c0d0101035032 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 477440629 1250 477439379 477439381
    0x402181e160c0609110a1511010e060601181a0c06070926071d1e01080703141e030c0708060c04031b150201290904080306060c03160b0708 61
    0x41e015041d0101c060000d0507183d115140b010038400d050000b05988040602041c2156a943d0a40b10281001070740800004000c0c2c100e5907113103241401070b1080002124041c01154885d48011b40350003111041d120400c41d0388000026071410b081080d00d05039510300422655840405141d14101100103080340b09120500c1c8007480381d1392604000c09660b85080d00c0602c10b9103d4106101d09d40b5041e030303024480901d030b5203001c0111105510344141c06484003e202c0e41c0c0443e0000c40d80c1d1000d090034000c02219a02c00141000458880340e01442c0115001c02920040100c0c01809401c00000c1030032201e440d131001442c2000041e0803c00400200128070140c40d250500050794595032089110162103c00f6030004021011500106240202250300c0b00c1044bc0c0940f0301c019019040c2015403103c0050300502d50580d40d14100c0b6002e0101c04018035102040d502c6d41e070394040c1034002510300e0b60408000e122031000c1c50300800007402e000c101c00151502501c0d441c03500d8091001d00030001c1c0c0c100120a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 477441879 1250 477440629 477440671
    0xb0304050a020f06070b01080c01081b03130f020d0f03140a20010e0604030f0f0e100c0302010e1203090607030903080708060d020a0b0c1203130b0402181e 68
    0x41600030300303158115444003146003ea40013030150300400340050008440c1d2000084d4031840019400d504040c00e890f2800d4641e1510500f1020380660651000400401c00026008102507401480c80c1c44c0b041c0c4025a9031600ca8001c107482c118101c104440c2100d001c80b44500745a04070800b490300f468080c07a0700c1d02c1c01024090042c00d090880032ba0f100c03400d0b07240e040301041207020342041206411000480768249801c0c00d000341841034690a04011a440120103801a4851491781000c004007a04a4142e500d810300c0c1280c0030350301100e05070215541c079401d6271101c1c03809005141e0081030151640752641030203805142020310241c00001030500d08407804001a030002d040e20750180715414512515550100031401c2c0542001d0029407203034490001198006281001e480041204401c840b1000380b101040000c034401070310401e00210041110302e00045184048a61003480a0212101c10203200002c001c00b9038156030a2440c4001c02c108200011034504c0103a9005882514102c1906407079 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 477443129 1250 477441879 477441883
    0x1103010e0f0c010302090d05010203240a0501140901090806070903020a080109021c0c0f0303030c11010501050f150904152c0f0601051e0a0306120206030a0209030f01020d0603020103060b030405 85
    0x1c2c0344030906040d00460041040e5070750700c0056140d290000002d56681c60444841448054000000142c100b007a0801b500c25041c11042403003070302c00c10384410319026084018542e0702e400509040d410004281008160300a0510038203001d11203540314041a5070071441040703407244140e089481141e14010604015075904e113035034041c600c201610b01005440720308095034050402c0d0090303400c540365400300004056240e0f020306155a1071307035a4660409151602d8500b6160300380f06a603840072580a00401704e02e480c0007070407070164a800c5024500220302001c141030b2040741781581a5005115020800e0111011040c1109480903048041c2041166450a02e039907026000c1e01886807500000f80c0c45034040c808541c0384584000c00c000242158250f1046540e01400c4a100024181a00080c0f02e0200300c1102e0030640c0d0041c915825951455100380003904040c0700c195041c0300340c0c55050000074003840104640540f983d00801c0d840e04500000d402e40ba100c0e0b11140d500041001000041180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 477444379 1250 477443129 477443143
    0xf0f03031015091518050d020d02130b04110403020102070816120c030206070b061003090317070311340201020a02120c04020d0906140f0109051e041103010e0f 70
    0x208000038440c103940d0022103007000c0f284c01c003c604c0c8680309100c14180d0b4010f20341001c0d40360500d07400c03e8090b480d08140041450042c20003900300860700d80d41030041c9421708140d20728074400c5c1c90004040814070002810b40d4500648003050007400542401556810321852018050060040c0303117058803c00a0324401110b44204c21400f10ba0459090410508004000095400812058a0706018180550340c082c01f52101c9106150030040580740302c1c001e00032116155003648490b00c9a00da0380b084209401d2006103030400b0980d0b10380002981c1001800540501c1c084500302086005040c80308180070482c0189103031418080414040045c0c3c3d0001c0d200105550648100c00000d14680880340740c41ca0b12481d2030f61040c0003180b0075040c44050340c00030001a0042c40c00340710400406004201c1403600340c64107684d01405400500c4448000c2e00640d03004070001d0301103000c0e03000d4000e4019840e24141c404550300e0b85800d5294110307217024024100c2c0c0d810150090700318900b03101149550b80107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 477445629 1250 477444379 477444389
    0x60a0909050a05270a08040b0a030b01033b0a03021b0103050114060d200901080a02040609032907030204050118080618010b1201051f0b16050a0f050f0f030310 70
    0x1884074134000c4000d4052006034180c40d840021a0303211502c401144d08941c001c211081d0001c1d2424012040940c0b10f4050080300d00c00103148a4803258058101000450822241070300e95042c02c07080c040900720800142d6441800395024029422103d041140707410320314140241014242070060003032200d11500646448400ca901642d07618000800d14050a001406010b6540740200d106c4049144500240741018090341e070281a60381d40781441781240541d02442000851502090000400324010040c81a078030001e031080c1103060001800d4042c008071340c80300000e600860108030035600080c6036141070700c0304101c40364030a0a2900c059568400285501240e0070344150b04540c000c0c080d8030920850b840607112400305d90b00d000044d400307004107807081420f0802100d082e0242070940340e81c0100b0350343d003180402d01e400081c0045031071010240a090340d0034002e800090002410400458134428401d0000e003040e03200070007030b82c0d0034000203510a80040c1c00030010014030200410640381907072 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 477446879 1250 477445629 477445681
    0x40b0f04020103200c0d02060f060d0203160f05040606050c060a0b0d0f06050417030903070b100509391b0705060301060806090c07050d080a0b060a0909050a05 70
    0x6515030004030044c240c4030342d9022009507419040000b40d4146070050042c808002d00300d80e28800761400c120380d01c1d401240c0081c020050b020204440e4607107080031032410f40c0002c00f1244041b1905600294200e0180d20403078450340308220401c1181014007600c801480c00d4100350782011200d660042d00c1d400d00810b0684c0090740c0705028149aa1400d88500bd407542100818584104a01d001d000910041d6002d45492030395030010a5400500822684120240d030007a50411010b40d8505034110b1000d1300f82c003c0403414203400b08584e1100d2420a120318100c10900c141d0034a00005040c02610207601015024400720001006242440c200d59002c0c4114040c44240b40c09058402d080141640220340c1c020f1000000061042c1c1c0b10800b140111421035031083c4a884044201500d03108480c1c000b0025084248180d00942c001c1465a510896129000c1403a201c050000350b1194000510000440c1401c00b050000008e10321a095014589403420031842c1001c402d607000f1a00b165201406c20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 477448129 1250 477446879 477446881
    0x5031b0f04030302010b031c201e0312010b0a05070206030c04080f0601090c09030210050c0f0d0f09050f1f02010905030706091119090b04060b0c01061d040b0f 70
    0x60a02402210208003120000380e0301e5a88078a0001d001e0905048814801c0c4289802e405240300e86c01041c1c400c41c241a00c0d507440003c4c0c2681ca120481040b80d1100f005070042000c4141c0500003c80f89040b0b6905203c00307180da0f101030384101450410107800a0701c0079102440480700603a0020300300c40c602c940440300513441c0e40d200390b8040310520a9130040d0a490050500040d1014000030307180741a2140a1001e21403c055514111040e85045c84041e5008150300d159010142c050402016a104e00308107482d100c801110000c0c0c40c0c01c1d440114100011440d00104544c554800000006440215910103114840d07000150340c507480200e0480444000c03e81049503e8002d600c0401c0300381e0300000340c07a210212424200c0040140900680b5580000b000e94101840c1c604031415130140d0b40500c2641560038141200b004195a080154005683d50404034142200c0c4d00909400103c0c100045225400d01c150300c0020340103c0030040c100042e800621000600c4008100d5110809000000389 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 477449379 1250 477448129 477448171
    0xb09030f150c09041808370c031808030408100608102403080910081303030506060702060c01052707090f060b0703020a0b0916120c03080307020a0204060905070503 72
    0x8004103c0c104c00345c03500f51340040e0100071300c2c5005000c0d00940316901a03243c200f2024200c000041d1906a20201c4104101090885000f08040d0700924020700e010f10200da088002012180e4031600800360075400400c00700012601045558800050307004240002482c1c0401c8640d69095280f5003031002e6182d4005100c4450b1500c0503001e9103000a0b0031001e500d681c3d0410407516803090702124051400d641d0404600b0780188145030291103a81202c060a10a0383c900b18001c201c050169544044200f2040700035950b1000a028407040c2800001010b040c8010b0081401c1c4441c07600441c0b0070f915480c502e1100102203150811980d03020000704402802100110081c116a040110350a401080c03540038035900240255805215983d06c400319122806a0340d619101c202c0c3c40c8880d510450b0301800310307080c0d1946800c3c11a108143c141c0d0080e40740d641d1074205420460700c49006134004400c09065107418082c6000130031088030200f015050842c002045403000403c3e5098103403001d403000c04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 477450629 1250 477449379 477449381
    0x21090503120f0f2709130b060303090607030e101112130308040312090e012612030103050a121e0813020a1d010902091c050f01060b09030f150c0904 65
    0xc0b655844109640c641c40080201e144d5800342c1c070304200c10800e42002c80d6550410760207490161200010303403803403075289503580e41600c800145490b03014001440b0044854403a04003030684076101c0d40ba8420300403011800d01043c5940c6034407100c10481c01d40151400390002180081c0ca03008024042965801d1104249040f29642c1c0d02c02000607000080010074444921201801e09105641c1c1d200c2c0c03282d8034400400310000a001d000a02a02111200030b0718844451103a010303542c4506907414208864070a075030b0741e0401d038025103042d00841403031020000ca1a81d0785600c1c10301400c10781e00c00e038034001c40100340c03105014011041c40140400b20301c02581d200e442e000c005500910313008195032210541400b1101408109003100d00f4100082109002802a1b03404014081c11039246082e4404914840580d0b02502741c2d032074080d0304650f0041e04000c3c018075000d05400010319a03076001c3c180078945040c812054801e12500300f0840b64500c50292592660800b50700842d0030f0300d8001c031100180c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 477451879 1250 477450629 477450637
    0x31513030207050307170c010e030d032408151f12030e130c0e1806060f0f07030206041104020903060708091e0c0a06140702040f0f050421090503120f 66
    0x5030b041c400c60b0800035603046c12042e110740c10091030081d600c040103210010348502201c6808a94560000e66480400c03621039440300701000505288a052002040300000c1002c480d030304101e01c00c2d04120203030310700d00000145c041c0c0c0020072a000700085180006000c07056000358080c0006100024010b0707801d02d07229040c1000400e00c000e10b0410600301c050301c0e4a004020941c1d445002c29a84410140a843c0542e85111700080c0982c80215980c0e482d07082081c0d0354490440c11841f40e5007071000b01812030b034040140440324800d40080c4400d003010300300800c03151080e02d24184a01c0c01001103144585010420903080302441c10a0b2200d500c03031915490409040e210300440e1002e40e0802c117442d4441c005116001d6080c260340c6207d285440304022500c02d90302c4103140c400f40004004610042c2442c2d4007801141c40542c0c03000500c58046050342d41603940c155000d80b4250280c001300c858010062481440c0141c0904140c0c00c241c0c40c0ca404291501005004e800920b60007144081200c0f960004032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 477453129 1250 477451879 477451889
    0x90618050903250804051908070f03170f1303050304030201080f190504030e12060609010602030301060504170c0a08031206040509070b03090a060c0f0f021906020c070f140f031513030207 82
    0x47d800321000c00d26080300120703e485801e5542c440c04400042d80600500144c0540c3d42280f0856591503070f10004032420740c801c100300c80552100b00040781d1a00d40d101402d1015511032b0001d15038452460000401c925400742908010f10252070078046800d114031105842d0a0070030388049880c4d905d50409540c2c09101c485041e801116400700c41040d641c0100d81eaa2084034200d4041c05240d0f29204101d0340d9010074010100441d104110034464a1414148c4120b0103001c0c07011103004080035008120144680da0220035540c4c40443c40055450f0341c0020142e000b40d040d94100400c1c54840c40d00c9560706260720529460101c0040440d120402c10721001c284240c000c003080c8002d0303503108001483e00c1d12452251002680348000003610074130200d081d81e001d030460343d141602010076440b220002e500160072034640e8800c41c132000074500c502d4a23a0384020079514002154140600301400001c00703035451100d201f03802c40c40280000009120409401140c1c0d031002032101c0300146421b03803603e0780355000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 477454379 1250 477453129 477453139
    0x5090c0a09020418052a0705030f0309010b030a0507060c032a03120e0d1202120711070803040b0703081e01031b12170a0909061805090325080405 64
    0x10201e011982a0010012580400c0300c0401c02243d0540c42c004031441581c4500e03141035203164200403030a503803c0300701d0358405c050402403605d1034580e0740303520b190302117181c1480200d4040700b0084041c600b80714102a20704142e000c2d0031012131a40c0c030640c555415004402c244107140c2c0132881414810400f0794400d4480031000640090403001311001103540800450000300030000800d8042c0c0d580c0180540810140300402c00c44174141c5c0191001e80c07241080d4028160300f80051001c4003a8464158020101074541040745200121000d0520b410381c1c0011256a01c20401081180b040d402101d00807a01031905c1c1e0100d44440025003180071105070760305c2900034440004000c1c084542c1c00b24030f00007030b20a406030900e5510001580c90080052010b05070300140160049040c00003802080b145142c0e2030a880d05070345603420041190410303005503828803c04019105801141d1081c990442c82282c0198145484803d03041000c58481e400340d506580d8802c00c031400c001c545003c1d2000f50030000e003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 477455629 1250 477454379 477454399
    0x18350706060e180c0405130501090605011a12060f01050c03030103050d1824020106050d0807021014030406020a0c1e060f06080c120a0c030308011d06010f0305090c 72
    0x180240602103501410142a540740080380c582030303007095103414100f0f42c4005480d034520038a08000051000034803180041c2101d2061000060f800e02c10494038038400d41c0c0008a41d410020401c44480e4030741c031fa8100c02041041000800903400e42840d0f840541110f0000c400e07005480100e07000c0c0502c0c407900340640310100c004800c221b404529095080441d54500541d4008400d401c1100500d500c10265104102c039a186500488054103026062403070001040072036550000c07580365040030302c0c265000f4001060706800c518090b003d04481c80000e03e0103220407a45441409080e11024100810540e40012030301802809280000056600240d000200000050050450400c1c03684100c407060700d480034641c418003880c41894280c461400013082c0d008100d00900c0080d00c20b034a04100345106182002c00001c0400401d074000e03503c207903a1101254900035040303800c10442c202c2c4006d036903289405c008690345e000030514000b03130301841c0101c0d068070b64220050070454031580040d04958012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 477456879 1250 477455629 477455633
    0x409050711120a1707030b060406030c0e0303040509010e2e0303020f0111030c0708071205070201090e070e090403231b01090b15061b0709183507 64
    0x940c50882080c035000b9911841c2000c0000e100307512540a450012074402000307000c2250000005640c800322604002171050780c6d0341c0000b011500541c0c09500001d0b01c1e180680f100b40e5000001c280586c1c0164010741c2803074181000030f940038805010b14002000b000001030080185191804400ca40410140748240e41c2d03030208240100301c1e800305801620981d01440302c041014450b8120349100558464103507225613805000d03a52007418280d41d28102802068007042e186003500400c80b1494a07420395a000360300c0050100d01040c2d00c480d141030340000400580301d030861340604070a4400c9a03803180d241d03600c0c03a040c0d42204d40301003252401080d034108c0e4031201b0074060040c40c002441d206800707490341c00f20105d5400d0702c07007600340240601141004180d54138403d5403d020100c2c401001c4600f00f121100380c01c1588220080440b50a81c010034040080741c01d41d100e00c42402007800070408240c14145c846401c0582e0005404919a00e600d10009010346005000b206e81c0740701d8811241d440a0b01c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 477458129 1250 477456879 477456887
    0x302070f1b050f0306280b0301020408011416050415051b0a030908010605010509040b120a0605040c0501090e07200d0c1401022d1308060f09030c190804090507 70
    0xd0b01405018032110003166405140000380342d84603070702c4140010908003004450408140310080100390082d01c40d1810940d03075070280003a0000d0101ca400000d610052035400e1030f040303003000d0207010760504540d00004c040d9a108040710152400c038449d40800412822044517980b095000b9071710915045250440d2690000c6600c241040c040d681d001e80c0e454480117031500702e405511809000c81c2e004c000004950800e600306100c82da8004086801000b5a100080c0c00d01d011105d0031601e050780e500402c01041248001d0502070f02080c0707860441c050520020143c0e20340e01414070020300c005902441aa181c2031101042c2510003030040d202040c154604c09444130705041000c6400320740c1e2a01c3e0b42c1c101c200520079035019100c2c0da100202c0d84440c1005400709402400103414550724100145400c9100c0c04284600a103442c0000340128640010b0b0114800005814000700d50010040c0c180b40400015107080e8185038105540c0c40d5074002d183c8003440b0f03c1a41d000250041c142420403141c00d0300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 477459379 1250 477458129 477458183
    0xd05100302150c122106030a0503121806060105120637090c02030a08040804090c0e010815060315030f0a0b0f130213020901120906060915080d0302070f 67
    0x1600b41191a0140a00d1054a00d800340d00007011717851810003054040c1c00c3c03404540c207411640c040e06494180100b601c0700d07401d503445180c0441b613460422040c0481a0b80c08042c416461010780c0150601d414450700007446071080341c42e0b00e042001c1f01c00c0031407620307500c21010b1140613480d001c0b4050808030032150030084180c1c03003150740701340c035029030780002c40c2202809603841000c90b9602842c90480c0103102910300102c050700943d15514248004a0105800d108080051a031500e4100c40e5600500c0010f04020000302210300c0143c0b0800716100030303115070042d2500600400140300c081c07404071021a02c3c00d01210100c071040d100e00b4260a0520020f80f90040c000e00300609105402e40e03441d250203403014251100290016414806030320950040c0e805010804030505d0702c0a41c8444e90350680701a204204010b44840750780d00810000349900b84250b000c100844203240c1d00d0540b820403041e865108092a103800d0640014402c001c1140e290302c00e00300c0c103a1081003841d9010441e0080208420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 477460629 1250 477459379 477459397
    0x12d0315060504020f031f0e0c0310061809110d0f052205060f0714071b0504060b12040c0f03152702040b0118091a01050406050d0510030215 62
    0x715201e008561030a0034001c5402c0c00d64055500340c0f540d1a81c0103c1c9014044c442c80340500080003840104640d240b800c1203a0260304410038498a03800c01074502600030020746e002e101442038003910000071205091080e01241c0d216840002e0818402d11101102d214020003024428500110700f030840d016a444980111781e21410b0f20100c407501c0030420080f064005028125a000000040211100903030340c030341c02052480d20303160050b41211001c03240d82041d582120500b0080c041d000943c10701b60302c0040181411102400264034011024034039108500b00411940e40d070380006014402c000c158100241104001201641c0c1d40c2c0c04c1c0702d5040c0100c503503416143c6003000c40041d22000100800314400b01a030502903904101e9500b004010f10510103903506100035910001d0581e200b540d1414020304c082c0341c0116285a98090f507008031069918140d040c0326003404240b0040c0d41c00015154155419500001c1980320801d10b010144915807000354440455a03050385162840d0000d042c1c403034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 477461879 1250 477460629 477460631
    0x9061e100513080304030507080d02121305040203070c1a070507020402130b041217040501050d020d0b043210060f030204090f020a0206100302031f110301031a070206010e012d0315 79
    0x43d140d40078140c64a040360f04480050748001280c10400c0d33001c00080012601c030300658000f09550384017260582e04200c9207074000c01d01403051202071061104850300728074038400003c8020724007140041c1850042500190003203502142600002c14004816809440b4041c5030680300d55880740e0092064000c0071040b0b502980802c210306015214501b03440503160140c4489080012090028000f90090f800055038241c4528103102d040c0c43d217124064003506820242541e28010b80c0350b000450b0101e030700481442103c0c50402c08620100c10056045d25014549822440302248084019010f02d8004125681c0303440d0f00010340100d00c1c0d00401c0c1e810555005c1d640d19540320748059002000a10010750550010301c4035580403030b0082d1000c051a42d94041c00508c8000e1b030480940990404d801c2150b1441c031540d5503990707040322440c00320703400340c0f092000307008541c14015810351546048c840c640d1048481c40ca460b0041c84002d6107000810759480301c41316800d03031341c4c03d0882d600900c11701140502 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 477463129 1250 477461879 477461893
    0x60601020d030612031d0d0c0807170604140a08031f050409020a1505040314010605030105130c03031b02060a0915020c010c0f0f02060a02010b09061e1005130803040305 74
    0xc90180c01820300701e03007416400b0001c0d01d00c1e5407025503102d00200086c034280301e9882c1174050984d5a020034000d03028098003460762a1420504054079001d01500189801e400d002c0c4001e001d68000078180740d01c25481014a0441055829800e10704000f880c4000c2407204084100803260041025020714440c190f008410031f181d54105000c1150004507020f504031440140500207903603860f03500300004419260292400303a0325125000c1400302c1028050340c5944404007048145007d000305034204000c2c000400605041d59204030810761140310043c10f100c2420000040311003084800e01240d60040c2600383d0380d050f98000241041078500a0030200302401400850305840003c001241d00410384940400c1100c6403120140b058540d0b4046881c008841c00c20070060b00c0b94000b07440320440503000440e5a1035030404110b040000208030314002c1840c41980002c025140d5070b400202c001c1074518410070300303c0450840340782c0b2030080c900f040d407050b0300d00004410000000800440b4000c509840017 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 477464379 1250 477463129 477463153
    0x30c03021506241306090302030c041806050601030b0612060a06050307021b040e011d0127020f1216140301020a0807050d020c010908030f0f010b0307050705070e0906060102 76
    0xc1c1c4000b95021600a004030707150708082d02c8072aa420b0304490403810903034100409842d11681242c0c00703070010000149030f0303070301042142400c00c8810a41e01c0c00722820305c2103179602402138003100700310307035018000f2904d400104549034003a42c40742120410282015a84041c225080120700c08155040c0380600c12407207000444d14826010381e07028001684c00342c8000b545400f40e008003100e928131240d034401e559000c030780160300302407046400d1132000441d4034a60380c06108005084820101c00c2c0d500194405844d40d00f20401c2c540392030701e10b076030480700201c1c414484404200004410343c100342c1e00b84038000503000d00404c01c03a9903004554110311444440788409090500743e00648043c04081554080800e10184c001c4000c1e0208841c10b8070010308044003141c403103003552400c1c002607600e807070000f00344410b1058100d4865840601d041207100c2c1940340c411441840c0c400103045400b0400081485820000103020715030081240001074009070406800c1c1c80c0e20741806070350990251040403030f0480 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 477465629 1250 477464379 477464413
    0x908060f250806310e0714061b0a020a03050c1002011a040e0a08030c04172109040e011506030b0d03020a030c0f050312070f0e0901030813050303030103030c0302 71
    0x95107080c16910607a00791280000e00c51882d0000030540c802411100070240d11a02c48022030903441d9541201140c4101c80070946030808803290000c000740706d82007401c4ca4041e1038104c1140c00e0707000002c0706100c8800070695001d062000c0000003d40c00350314640004140180090401e0752100104c030043c1c860291403500b6400c0711078070400c20078180203100d03118034185419400f0342607040d40001512528240f540d9103400300c5c1d10450303080100e440089000e021000421a44142c560010402041609400001d05910207654050100e110310001008281d0fa203490700318402c144902c400900c4455001e0b003038001202440d004c0d10f40024a032111241051405041165038280c140d00508a1000c40392000c848a054010701910100185903144000581c00c0008014501c0e140c49012005e050840f0300900e500f02080354181088006424040c10b070f5240c0014504486d8485510307565001004c1c0e0301c1c3c029144950219a00d4000840000300b0305820011407050300d440f81d426100203071044040c1078 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 477466879 1250 477465629 477465691
    0x20106090609021e0304020a3206090102030d0f0f090b0a0c031b0f02160312020d020105010f14030c09040305032505030402011d041b1d1f0908060f 65
    0x85114240d040d41e03100e040852000454019001410742d105649c0c503204000a070b4030b0003010403980311556400a407141c84100000c22050300c0b0840c1c00a1424483c540000d6a0340500f0406558084c2c0e03800d03ca0072040c140790300004a002082c54203002d100d0450514440282c2c003262410180c4d401c0600003001640709101d4803c10104403a0741e00d41c4030360380102c204c13001890740c684101980700303c4c030039411034004400382c0301c0c002c6100d084955040c4114800080c2003a4111180390b095a042c14010b000e007050154008041d41d400c2c086120001c280300e0006450005034060144c0c000386800240401e040d0302a0046100745035849564811003070700c0f051146d0220780b0700840b2001800610100703006610810b108500c00e04501b4a12942d00c0844001078200c40c510440c8018842580300b0004003a50010044030400c010144201d01c0c2418010100310050b2035103c02107090781c909541c1e10544e034041c001c0c2c10050201001110118600204042044d61040e1070070800075281b0360140b4210907c1d11180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 477468129 1250 477466879 477466897
    0x1a0705060a111b0102040509040f0201030c02010c050a0c030c020d03090f140307032a060801060237020303190f11030304031403151c290610110d02010609060902 71
    0x1e034900b1005a00c540707200f491041c103000440d50200000503c40d1b64140100340100d009180809038030300144005011100c44404590a590400a400c640250000140c590b41380c51410700139000e1503240b400311040034034080000c1d07110b070510100d0003e040e44040540c0a681480d8031652542d519810f00e000c582c140c0251041d0b2560000e03034140000380c41c81000d107170f90903080303e01c4510811208221172040600c9401c0071000544850041148550410489280b851241c005801c18a00b501140c412090801c8440143d00c0003402c4443c00c64034100100c1e11800003504c10185283c45401c4014400c0b40440764240018951042070740c002c20000c800c0b41d000e1603042d01c0381c031411801c003071951803035400091011607008a18491400152071f1601034843c2441a0a891500030b802407401d1a400458154650110000c031207031030f0a40980021100d800c40011182080c20742c803071900468031034100320803494050184031900390140d6015003012007514084242842025154910002240141254 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 477469379 1250 477468129 477468161
    0x3090c042406051c0905010e0c180408071403030901050402101103092206060207030c08010204080a11060d0e0a0201080705030903090d0609050d080405010501051e0112061a0705060a 80
    0x1081481e000f50000c21003030840060400c040107205040000311450304400307480903512111000c61107881440454604041200c104841e5042221000ca00c180010300c01400c00070001174030000d000544520f11110740c8043d080f69070703a2802d07206940c080c183c2a54200d0140030450308000200d80500081e40d0751882d018000c5090856030800c001d2040340c120b41c840710944403440c01c1e2040900d42d000301c001034050354004060661640c58030170300b84c1b10194000f489130307481440300307212250010805100c02601314841a142c040f003240003514034412101402c81991909002d4004044003280d001d035014000d03200c01103c0e64903d08155164030080700c001030550400c1054000358a80810b0300d00303146001c1d050000343c0c0d24031990b60b00d1030003c10004000200e0a0388082000f0410309002c1c03280034140c190f40c0c084801d90f616101c80d50000c0506920380c10b000200c0013402601c00300382e00180040c05414813a0040c1100010742d800b860780b0000c025682030240c880090001c2c0410300800340d03840e80200b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 477470629 1250 477469379 477469451
    0x3071e051216020f13020a090f1508070507030504080a030918050f010b0c0312010902040305070b0c1e0f0105070f020d0c0b0105091f03050304090501060804030c0b07120203090c04 79
    0x1c200100700410f11342540d8800d05544012035901164805480049a1074507002e10541c02e0480301e14070b030801e076400705902542c0001c141070303160b82c80000c0640100141c00e02039242c030b501d843c00b5241c600503a080303e02c652087e000e00000307160b409405074046460444c4004900d100c0c844458080d51070449000108086840040003000340f0350b002444041e83c0360742500e0500695402032041c4450a034054000250045814002d0000a001d0b0700001c0c00c10f544610702d8040c0e054510303a160505c0c081c12607001301e41c0350840350300440b05010a07455251000c000300098904450b0280400c00c1c0e070a036901c01803162405030704586004814140c100c0e500b0034a0402c42d40c0c6802c041050000c4001c010814203000140781120015070340031010042c510035000355845e9410002500e0441e101684000d0170411490203120110350402561390815400c080c002c0d4250762100c02c140c612440100c200035400c1d2000081090f1000b001c6180042080c007100c080c0001034101d008039800c01804880162044c0080e8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 477471879 1250 477470629 477470633
    0x51003030f020c03010e150f1b03100302100c11120601031502040e0124050f09010c0c08070b040302031605130b0f0d0609030315120b0903071e051216 66
    0x30518004021451040f00d51864420010900b520010103251030240c3c41000d82c1e801581c01101d040d43c4c80500051050b200d0f10300041d2198414449a0700400e139440c0000114405d4030001c1103081c041c54000d0070480b419030350350400034940c0030324460950f0149889101d1100a207841c084d680c0041030050010000c0317900b1529614030b1030064511039000301e2f03400c00c0001543c910b240a018001e15008800d09648400c1032807040144404066100401004000720100b00b440d40c4280c40c500c42c420302c0c0520021050b890700342c40080090704180701e14410400001158030404000b84182c0f03109a0030380301103403241da04030404814a4011681d004010390034003070320310b2081d52007000c160000400e1702824050410105007003030701000d000d440643e26043e5040030705416014000c100c1e60101030900420746031003d000c101904071440104171500307450121708051010000d640c000c940100400d00607040440e031750b15421150001c221a1809050b2558141c420902d05551040e20300c400301d54400515a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 477473129 1250 477471879 477471887
    0x13050f0a05010e0a050d050d12090209150a0b0c031e0301030206030f1e0a0903391b1202030f0a0b0f0601050d11090a0e040f060b01021c03090c0905100303 68
    0x4651035040040600001403030f580d01191b0303405203401407000e000d078244038a0000340b00a000649144015080c5255000180c5500800300c3e4007151030a00b41716411a20300026010405a40c0400c01c140e0020a0001c240f040220080411504800ca65451182103a042070341340c0c0800d01c0003a5104078207000041100f4180401180d22200c0300050b404519825440980702d84403c0d607909a034141c0d201d84000c101034100c04034450150880c489407005140c80005070304042c200000010000c0790f0007102d801000894480341c3e000302d0030403040050b4107842c0d58810841c280c40980586c0f092040e00142ca820329808a91000001d0f080040c400241e030300c1480840c0d91000140103103040080810501c0030704401c5100b9000303401412030720140c0d92401a810411003074441d421100e00d04640c40e0074400040c80b500d501e0005c03141c2c40600800c0d03492940740140d0500f801403181d183e030304011102c03070340800d41e050f030044a45070300c503540b400281e9446610301d101703d901c01c540d0290440d443d001c040c400303e030003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 477474379 1250 477473129 477473147
    0x170a0c0203070b01031101080c120c090d2301140108070306270309050f060a020303040b041b030609051204140f032805100c09090e0304030b01080313050f0a0501 71
    0x450040780d160681036954040c0c802d10981c829911403807402000000e940c1e1049080b078010101624807030a00081c0081c0300ca541202600c0810b041400084115a07912a0065010144d40100c03071803c004102240c00381210b28140100c0000d0f5280c081c194119410300c0081c035042e00c603800c0084c0301d25400c0d41c2d110001400c01c03414200b6070700d03400c0c002850349c030030706410034440c41d1b1003a070310110300c00c1c41c0c41e0034040080c1c1c40449492184200b4010103107901c2d40042529071060308a01200d40e261518180b608030360080400d14090202481e801100b48841a00014001e6205804642e12012000d4500c1181d01890080740040f02d0600c26205a51910300460001814014103440818041030180a206040002581c0f9a000811408030a0000501c504998203140c0b11041c0240501c020005144560714001d10350306c1c6580e40c0c119582d19100b081664003443d4001460065541c40d0240300365203030030010681840d05840e2a0104590829031000050000d008e0914620325082c980103440c1c0d508 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 477475629 1250 477474379 477474401
    0x2010c020a080a17091e03040510030b0d02030102070b070f080c0706051008010c020a030909020906040b2104030809190302060c0a02012004180b130e0319030c0e01170a 74
    0x59840c1203480344c00501c40e04103005188543c01440200f18254a21044564111000480f41c00074070040085032500f080d00c5d48014490f140002d00784030f200000400e00a00440065010b61000c202ca80c10040c003650901e001d0011502c5569200f01d8142c01111003540c22101000080800d20258000400315044503400000c03c0d50400c442c980c071000502c0c2100c0e05100c4003001a80000390140c01e05070860b00041c0603100f400703000d41c81c1480d0400451214855480340c000311940005404901e076852003500000c0c0e01d0091052081e90506090007400c0184c251f5042c1681c1c09000d044541000ba4010042c7e10795516401a004540d120a042c14132600000d082c3d0081d5506da800c0d400145048280c40e503d01c1440103013040d2940e00b001c4e44411000c0001824211140c5000030310020355440300c450406c400c41c2c840300070507000c00713900050303046000720010040c048005411006410380c141d000004103407200d540e086500710a4100444100140702048400b00c01c2440100e01c4004098100310070b060 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 477476879 1250 477475629 477475637
    0x3031b050a0609030509041103092e1112010e040b0c0d06120b040501060605040f050d020a051804030f021522170415141c06050301060308030a0b0102010c020a080a 72
    0x551662a510190f40c0300c0d180840c0004e1000a8240c254981885480e4592100400540c214030b0600c218036500d901201c841c41103280485841003018002031074625900c090940f0a1041d4401800003180507040f11550801e5030842d4070002c00c1500104903c10700c1030741c00c40600070ba1030300d0b0703080025151b40c03082d0440481d0584501c80403e4140c0c024a10300d1a191107201120303694030346800e00500f1102280c00210412200300401c0058000e8000c0500645804485a0304490843c0c80091141c12980d4000c940080091408020100301107001c80c0c0704601a4851001100010404980f140490702000030300506100101307400008580480034160b9009520400d9420780783c0355100c207141ca034040b11600030700000c2d05000340c414031607001040b41c000782040b45110011401c516070f079000d00792100d1400c0c3d041d00c00c0d04002c1c20203500228010500907000f04151512402c0098103a0300803076120049608200506905501c1442407841c884080c1c0e000d01550100b07a44da60070a40d03c10b0322440104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 477478129 1250 477476879 477476893
    0x160c050c0a030f060b030c030604141c050a031a1509040e1c0906050406091401090504151e21050109061815060f050609012c01080108010603031b05 65
    0xd032a80c152000c00385000f60701c1d100a09010b4640341096882c0c500708580030390480c1d00f45140d551400590b02d40c1003a407007105402000d18a003c0c480ca001100000c40c1110800328900b451921303000741c003c0c84040050b60f81442002c903100008a08600d00101c1c86820a200c00f10825074040e401c0090014070400810106c0d510004491043ca842c1c2107120300d42805044103601100310790000002070040c00181481d40c1010702c0c0040140c4900711611030300c500d90401c40505100b90b84030349a42c0b03005d0040100208192621a00074100103841c174003942400ba800d4801d103401c02c250300c0032420100d40100d580688860014000c4002e01030300060125510740d22008407100203400c07805800d044a4050301101861201410202103401d040340825050900c0d000c000d00020b861100030800341c50302074a604d03903601e603000c0040301c0c000070050072032903000800c2108a00c0a049007160120301d0398240c6c3d42a00c66620350f0650381c220780c13081c0300c000e01082000b140718606601e201c0401020f20701480036982c00e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 477479379 1250 477478129 477478153
    0x10030c050d02070602190219060b0d0b010e011e080c2704050105060901050405060a05010311040807140109150c061505100e0111030702010c0807061b0f0e040203160c05 74
    0x42e40c0002104070307081600441c40d841800c0440c0300500e507400c1c3c140b008003840c0e50496440c2417202c1c80140003070980ca031204004600f5071250707840140310603881030402c81703e0b40e582c07219151110310038081c520109203440540c07103501107401182e0007601d441601410040f403030385040100c6240f0b400c2c20a840025040300e0700d801d48140c25285440703240600f0002c14145049810052842c50503048a4410341c944814041280c03038820040040d11020b090016882030b031140003200c0350059038401000c0d0700c00c60801065020740c046882024010a232201c00300c1644501c00c0700140c140c81c40401d00001c0d50b03507985a01042c0315820a00101c140000d44901c041d4445002c01c01c2003100c02e00c0c0502140c5189018041542d10100826403992400080d40c03d010b02580020080d07000400090900071010602d14144650390b40403660700d940d01000d0504030000e4090150004044140042c0814a041c5a640305c6081c41d0080320b2040544c4c0242e01c61007504220b044e10781064000c01034030148550040100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 477480629 1250 477479379 477479381
    0xb0604090525020706172a09030d050c0601060c0203030a031505060c060603070f080d0c1b06080702060105060a1b0303060801050901021305040e07060516061401030308090c10030c050d 81
    0x1242d5010303603010b00b07042400d00c07070098140c10103240d007050040342e80d100300291b48294000341a907400d412042c480c1d0755049003011210724041c461040380c0c1409070603003020308503400c02e004004024044040d105143c3c0e0b500300c292050a008840a03415420401054580c0c501c40e0384580d942d140c81d040304009094882d404100d480c0c00840c039501140e03210700d050000c2460100884001045000e10040c4424100058581c03035041020074441449600d100502c100440958400c001410040c034256201e903031000c0082103070b001940c1c410054004c00d800440c60341000000c507030203c5020740320041d584d0001000300b440307082c0341002030f01015560100130900c900b082c00f400f03000d8401d401c005612804005907400300b8007c03c0d07108501c2589425401480032401288407422689181855030319130703030340145000030b001c55000000c0c509440c2c1a540040c00440403a4241603a0096507000c4050360341003050399451001ca14119407082d6150b5000e80218440d8110620a038a60300d042400d00e401c3e03c808034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 477481879 1250 477480629 477480691
    0xe010f090f06210c021b010e130c08010e0405190f14060709120c05190801091211010507081611060906010617010b09060f09090718090b06040905 64
    0xd8001002000c980060010054103a0052003c8020070002600002c07800303503503450f50314824014400da40b40ca03405903a000d110180d010b21000307082d0300b40c08402e51803013000510000d000c440c041009040080741003448200c0f81841242c0c000000c04140843c4c442d4031003864000072044031a010941d41d164001807600240c5200508200001c0104d414140700140540a540c1c01209034921500c8940000c43c5a220340b950031103030103940d0603441c030440b050103c6600505800030b200b99803c003a072100070040c1085e012840c2e03820a5840e22150100e11002c1c60a0324810f440190000303031020007081922030350005024410416041c8040c001c41804400760030048120b81e030142540102c401000640c0c1c0112000020b03109243c4540260347c1000022020380c0104889c0318022400811500d601c2c0c600c0a003126038070306000f05034011900e013400c4000d001c00b09041e8076103d40e1020303903c000340007030030f60007401802900202082d04190030441030100030030004004403000b95004403100c0724980d00d02000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 477483129 1250 477481879 477481889
    0x411180105040c052a0c1804150203010509060f031c09080c0105040605030a050403140c010209210d032a050d0e03040f0b071a1f150e010f090f 63
    0x85815031400c4104401c5940d004988070038044104014a4100348481303265040a5401c0801249080e840c42014a410240441140c2028046601c55040800a001540f240b40700e0000c00401132901032204003079000c00c0c0704854100e1044000f02d025803410754002805400c014044030214030000000c403807074001c00c3d5101e0b0301282441c1c009100b07030704080c4022164582c003824203a1074039140101c010030900c4001c3c5002d292558500210742098070401c140c981401460540c0d5481d1803034410381500035449030761036a00c140b208640f040007071070034803510200c120003450207412030a000c550b054001c0c0408010f0240e204e560207416114441e508130312242000c80a9480c2900c43c400c442a40c002c50368000c0801d0352a81c82800f04202540150821000361000482032944034043c614056016194a5980096075101c0c9420400340500c4030030060280d2032640346a1915558a091501c2c40100e86200900085c407107425801882d4010221150000d60798030307010901943c1c070801c440f000c00b100d0f006 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 477484379 1250 477483129 477483169
    0xf021c020a0f030203010b040e06280f0509100c05030712060f090204030b0c04082e0c08160504080717070b03091f0c0c06110d020708071a0103080409050411 69
    0x814004c3d8142403294040d4241705070f50402a8181d03113480d450703480c6d2001f40603da8084170443c03100003c03001d400302072030b1070300c0c11500c14001c054081d405140034141c100c810403038601c190060b800c4231144a01034040410503a17154949540c8801da4102e0b004d640d4072a1003800c4c1c5441c3c4c107000074a48c04141c4440d0080c0415400103803218218a000001910094801500100f00384014800c0c40e9000c15240c403400000500d616588202c481c1400b884901d00d42c1415400d4542441610342d283c1000708280310700309150b441d000d070400341001542c0f60f000318090390046074040001444611184d1460b61703207803e034000844402c20f41c1c521003404554400c556001f080d8009840341d0b81115240703402040c11490f90142400f00c00c0b00705100505e4803014000c003600141d10f61000031400c21290b0200d80e04002a41019540da61290810100603484010201c9040042e928068006481550242e06807030340201107510f064602600c20001e400003500a550402c0707a525103501070303545c1402c074090f0300001e000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 477485629 1250 477484379 477484409
    0x513050a060f050c07050c04050a0e15012d1401090f0b070317010e04030c080d1d0615010807030f060504180203010c02120d0911090903120703090f021c020a 69
    0x40b0031800e03100c0103041102900c1045c001c002c0010380108500c0300c6e200381900c0000701c5980301044c08001d00600a48000c1602804034080c00104103800140d060351078422002002c220800c0001d903000c4801c1540001c62521a841804000801d40084052203414034010301c05079290344800011081561041d40701003c0003403900d08064116400f95000d00e502c0c5402c090640c1340400f6403511110042008080003036600c4141c1c100709000003951250143c4e4072080150018901014203106211010400d941c4941400508880491483e0030b941c0700042c0d54403402a2204d82d0150041c0c2142e500700340c80142c454070b010600b904c451080c1c0c2c161180d440c4500403030703e100d40140340c01c48408005071000c540126a12266082182d0101c801541000c00000390460070b0b801d04241e002c01e180845039011046078140120900004080c0c10000c42c01c240849560300c2c1d9400c190301310350022500800c4440500c2070800903180240800d2407201145030001000600d80d4000f0750060b1164101c2540c6880030783d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 477486879 1250 477485629 477485651
    0x61f02030c0c060913020d0f0204080a0516051c0305041d0a1802010e1201061802030403020610030201020703030f1b080a17041502070312022706130303030513050a06 73
    0x10580c0c00c01d0094a20618018032000407800c0305405c08038441070305030009504060140140c7c00b41c40c074045000411901c454481c11010b8694507800c03403e840c1842034400c0d00b1030706461924020700300d980041c2000b613111000751804d48098800101a0184041804005104080150b10030148454040d4411092800000203412242c070400d610030f15a40c10813910700181d03081403020748010021500940307030210600c402409042a9048010a940d10799a8500407104540142d4090b0303110ba009d035402695a0780c09050041041d20010740140c0c09840104040b0707009070760228450019180c82142c0c20b4541040103401e524001084541c1d440010b02000411b078001100020500da00f81505003504003521210108404a842d01c4021540010f000c3e04160003400058a82c0e01c0802d41551500b454010415090000440031034140b4244500003100d071801d41d0032141d00780545c503040c111301b90458400720700810006103107104200c1848000070214a0401040c2000c1f0310038070f80800c1040001f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 477488129 1250 477486879 477486883
    0x1051005120619021804060b04140607050601060503060402070515012301021f06050306010f0e0709080a0605222603010803070b040c05130b0f010206090304030b061f02030c 76
    0x40900032119800c140e05000c04140e03022881c1490281e4140d0151700e078800c00f049604003211001106a21503d041d00000d03028540f8000391003281d581da002848451081c405111080c440e10000a00c0b5810510050000c1809803002d035030000e60180c070050030009140e40d46071130801d20044410310359001c0c00c01000401603411080e00281001c80300500c020100e600081e40c3e401c121380803a400c08050311048000d8482e660304c40b2004240040c01c840081d40d44680901c0c00780518003580184040003000034071810300031580101250b90b40300080c400e440c8581c40750002400003038908007800c11414043c01d180500320000d120442e0281d5140c964011120860440720084070008020520041c0010080a000841602e44a036086904c2500955036450808503020540e0001b1758010800340c002004100543c0c00480c44100544560002c01e0543c4c005aa0301d2000b00d0340480c1c01d5204210038800540810b40b039580000700a0034003100c100088003001c01000c22403500c44016400400c90714180041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 477489379 1250 477488129 477488149
    0x204090b1f021e150708070f14090f0a0302060a03020c10050702030427050a090b060307030b1b07060c0314010e04170f07050714040f050f040b0c0c01051005 69
    0x700c0d41000309004040700010b9164048410150681c0e01000362914000c002480405a000c0b804244d800c001c0c42e1010018000303090549446e000101205030031000980a90321000b000d8940340d10702c1342010545020416400c2ca94420039030401c00c28400040142c4810001e00007414054a02507100c0a00c0c10381c4520344144081c50413052400c00042c0141341e42c020044906507080042244c20402264030a041504c07142c06e40c41051902d4042001404041a84040c1034140705032a070003a81c0e11583c08240c1d43c0d5140c0c0c000070b0700c14000f24004c203060105140c0740f03903084405210201d0901c80541c450708101d03101c0c0916940401d4541003101035074000404807501401040c1c0320b42070709041a0f00c988a0385c0c000f103444824495000500303200d80242c00d0060341d1000c1d81c000704941000d0344900d031031800001c0180310035011701d040040403c10502a1300949200b041a003140c61210f0340ca40d211250030600c040c1803807410950070042c11000307a00a0003034902c1307000c0b280f0480c1e5103545040300f40b25081e00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 477490629 1250 477489379 477489409
    0x306010e0613050402032508061815130b060f0705070f030503030705090f120a1b0810020901030b120d022a0f010e13050603240f0a020405040204090b 66
    0x240c2005040100b600310060b081c19150700b078500507200c1d40d41250394181c00300d401608801c0080400c410b40703030765680068058407400c010780e408901d04100400c00111141e00703403851000402810b45688540c1800d9540180c440c800c00e06c0800c12491210200d80e403507001070b10b00e01010f1000030750300b000e0060821919000300580da00c82240780d80b564507041d4a03800041e04403402c001002841c1c1409030382e09402a09844001001c2c05c004081ca00c0805613580d00300c900c122180f03041c81544120380100030810f40115104000645420469504440c00941c4000d485030b0500d643c8403444030283d220360f0500032114240b076000300848400c10501a14110100c00213418940802c2c2c81110081d9003024490000003003921200020500e40f40141c03500900039032155040740c0040e092003460b4400c1e0b005140200c8083d0151780c00310803030003150460082c0702e41080c50100c0c140d42c00b14800c03245502840f603101c0c100c00b10040c141903d80000409903440342c2d00c03000324580c0b03d4050742c8052030000719205d0000c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 477491879 1250 477490629 477490639
    0x102220503150f18071706040b060102060709030303050c0417070602010e0c1302090103060e13030e0901050105040e090c0d080403290114010c08030906090d0c0b06060a020f010507050306010e 84
    0x4030f0100e006103c460001403400c0602081c41800c15900082005604054000d075450404052013001d5406d5954a0131141a1005001e41002c940d140d40081a002d020b00030a90304c80f01c44c281161402e0300685805002c0342c10042040100055150744480c10f00395020b10b18000e80385503403400c0710084c20360300c082c501c01242e84c01910500e40c046c1d985c041d0944c501800b0800140c1c90314448801a001450254054907141d0711001c100720381c2c2d0310f01203403030040705d44280c4a00020807501001d000310300708240903c4e03020860400c000d0140c00d070500d072140da000401d01d04403170648450001255541c0220081201c0400c2c01140500400072074011007100040d268001e40c03d60700041689541030030040c070548045c1152904c1000259114840714001d05400c49540d40da64203141c140c0c0c40d502c1070704503100c1c5180c0c0a0251041c04151003456800d02c1507070041c0802081ea00d03500c1c00c214240d80002d828106510600e15501d201b000207000d282c0c03140c03030b141e210240c42c0e2030310b800050315841d500310149201c0e13 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 477493129 1250 477491879 477491881
    0x70801020306090106111504030504080d0503310804030302010c031812030c0203090616030f02032d04051206010e060303130308070305070c1401031b08041103010222050315 76
    0x180c0c40d8a07240f181100e40e146890030801c1c0c1500c000a0a01d0883d4030000f0f17144104404010034150410000c00890704032408071040001c44080450b11400140c3e01c0054804003902c04900411840b1503680c0412081c441211102a03556079000950344180d000300c0250751140c0b518801c42d501846044009005000c04800d6600030740c0d15001e48a2244040c03400340340d902c0711b000c480d180c400c0041d510310140180406948800314031284801500e403420840009414410380a9094804030981d0350f000c0c0034a41d00d1050800c5000300049451120050078403002003070000103129503611400e148000164800782c0340d10b50401c10441d8100f50001c000701e009034410442030004105180c4c1e1034013100d411810450700c035126441d0858042c81480b4020f07101c0701d0b4548000c62410031480b454440c03c4000d0300c08100301040c810b0910011078014500344040381c46040080c01080d68000b28801c0c40c00c000b0b00040c6442c15090401c4d0703111141403c0350070307660110f03541030015007030812503280100a9541c0c24005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 477494379 1250 477493129 477493141
    0xc31060c020d03081510030b0306090d2a1205091509012309030706090f140d0807060b03011a120109170706090501050f07030b0a030302030a0c0c03050f0607020708010203 75
    0x400400b104010108010400020107020a10354010b0b840302005212140b14480038000070058801104894402c3c01800c0c0803c809040c0010180c207111000e48800c0400700135103006400300c60104411035449a4880e400c1d1000030743c5001080c4d81c0d9000c03900c840351181072100a201100f100d2440c2c81425038001c000040440ea04090b4040c954403503207500c0f08412035049040041340c0102d005068042c843c031b1303e002ca140c41c1c2111070202581d250380b001c035184e40da495221f8003480c4070785a1b00c0ea4003d81600780480100360801c1c01002c555000781000304410000c0301c042421a10050364907490300c813051515440c9464014600200d590094009100008598032004005c1400f030010f903d01040004410080040c07513041281d600d50024003c0056140003403d580c04c0c001c085804000003803500c1c2c80e400040c038140c4148004d0341e030150b00840c1084040071069401400343c1d0780a0340c0c1c044102d80d0000000740d04100034540701c1003102c0500014200084040d140c191180c1100c01164010f04c20881 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 477495629 1250 477494379 477494389
    0x30f060a03150b01031d07030506070804080a141b0d02190206030a270309090b100806101101052418150429030d030204030c0b030c31060c02 62
    0xc404200c0900012010310f0100180c005080c050100390100342018104600d4202c0444e00700708886c0920705443d101e0b0381c1c0340c17411501071008890040803204140041201c0320311a404071985039100c00402854512103549030950512a400c61202c0c543c8150310b4584000e0303050103042d968400111110702d0250840d80016054007004000a0845a039a0644d102040035400c0004412080d00e2020144100d00d00f03004105c601c0347e00840f1481e50801100d1075031410b10414071003082c0180e035106603035038075060200310460041406076001c00107240c0101c9800b04082c401d1a00881d1f0b00449038081c840f168040c03000c0b4402c54000d4510841c030070901c1310810000e0f02d6000e580041d1010301c0759480d210314400a001441c11240069207010b03483c080000e01281d00d80c000703a1a10088049440000a00d00214203038456030000501c5040111400c0019074400c00145130000c500742003403810304030b14418003c4110078480c03103502300e101520603040d11109561143c1019149500e032080c142c07070303058003c66 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 477496879 1250 477495629 477495653
    0xe0a0903110115090b031203040f03080c09030607030509010e0f0705040b0108060303041703071406040c1e1e1505030a06050d08070b09011401170105010b2a1002030a02030f060a03 79
    0x80e01c4d85d2180260805554148030300034a41e142d4092040c4ca81c142410310184a0072800b03001c030086441040801e085140f110142c82c0e409100034000d244c0c9549416044002d00009854401c080d0340320038103c203441c14144640280c0d01d07206402000c240349008104410f035a1810115410f0041120a02090740c4000c001c0310300740ca5107418505940d10160034120f1840c890280c024000c0d01031581064003036000032443c14003560040b0101c1a80a854100341130070320070340742c2002803013034209072040020b500700190303c980c0201289002c6098503510f120008442c0580c080c54130008800204200640754030b40725080c00380c00c0c2602c60507882c0781c0b60f030f9030441d1a1040c500041c2c041c001610000b40182030035040b14200302607030020024a03594400c1c2c600d00c00d0b00002c00d0351140d5428040041000c0030700c0070a9480c140010784800700200c2190b8404107217a000c480c10215580550454590680305a00040d400307a101d4020060f07581c540003660301205203015003968440c1450780010404943c9010302c0b4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 477498129 1250 477496879 477496889
    0x1b0e0c07051908040b0307050d060e07081803030112031e050912120d05060d050115080f0606030c06030408040b0f03060406090915150801050411010905180c0d02040e0a0903110115 79
    0x40d6601d0b103400c1f2080d210750240d583c2c90081241020720101782c6000d2130305c10f607000380e01e0740d10b6010041c0c0b681c0c461100046103198411010b03501c00e01c01040310112501840a04034020704118090031004205c0c0c421040188038240081540003800d648a0306264040d000704c2c000b52005010600701414200c980c0d4400c81d9140600c007034403000407502c60707500e82c550014641c1c3d1200003041110b8080e408014105000d1213610800d01406106a485003c0825003511418005001c0e00a1020132800c0103016000908286d504400038007021401d501c0c1c5400500400921480390754692400c2005c0205843e015003080b000282001c1c06440003640d40303103408000407500311000c034803511030303803101e201480752a8400b4025600307000c01e00042c040c4030042c40c541042c003039035100c01b00341c0c840c814010800400d1b0149142048400006040300120401030010b446061001618003580da410b0124400000c0e0313030310441036503540412070801d900881d802d506892684d0090013a00c0c03206207411004041480b0b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 477499379 1250 477498129 477498149
    0xc03182315070f110d12110c010501030b1e04121b050109050d030e0c0d050c1003240803030a020c0a0b19060807080c19030501090308090c0406030f1b0e0c0705190804 73
    0x160b481d84403203420020b62000ca8500092326012002615800303040c080c88241c030042850400314180c202e00300e158007000d12032000386402c01d81301c42d6502d4104111394030305001000241e07100300c2c035804010614110303c45e01600c00824001c4075030600a0906000b86051070502d882e00721001115800401d004c951a40b0440720344610071014240142018002d90301d0660000d815018141001c0e0103a00c2150104100d000c0e802002c0000c5c101c6201c40a00c6000c0c01056038024000510310b05459001080c03543c12440c280c80c0307a10810b40d20920550002c0d196101004014254148180c0b202c1c1b00e464000c01c5188020b1006e140741040d402d41341c124096055010740c4038250301403402e1030000f080400965001e00200006a02420010300c2c00000342c1d6840305501a0714116001d601e8103000d400c0c01e4a03000109200c05204c00e40d910100301040031440e28080d4200031340000c031390844a03000c5109900f00340070140e40c5d500c20720f070980c1801c000504200300302c100040300c8130220b01040c0544040e03400d451f00d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 477500629 1250 477499379 477499397
    0x5270702010203040c15020c3a0b010e180307060606020c0103060f26120406020f060c0a0806040b09042315040b0405030c06040809040c03182315070f110d 68
    0x18100c0c00c1c210a11400d9803c158201c040b10603c411b036403d44144402800c807100d0009d5101d10302c410350480b01c01c501605d020404070045c041d00c1003252015030894100701c80d0342d43c0da10358a6141800d50b08000415901d00e80d41e01400c000301c0e80c0600c6a280340500901e001c000702400c0107400d04003000342e4041c1c502c42440540c1c648030501c0a81c01220a118880c0c811100303410b0761032440b54116402405402d0042c09114403214200400040c424003a0000558260500c5421070044a14000083c4000d61042c0c844002c080d80740ca42150b030034022402003401658201d190b40e28a401c4140c001034980f0294440c80b1014990040842c03100e80050b80254603448949035410242d03d94000c802e425051030242100b40001c101c150303001071142d4101510103101c580d0404c2c030191b08a41d81c0038400910341a0400a4200041c014074280c00f48a40d81400010181040d244503440c000b0b50011a402c0768404a080c010b4954104e4003001c00400d051501c18480c00113610195210101211074005104d1412 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 477501879 1250 477500629 477500669
    0x30a2715050f0c1b0d030e010c0303020f1201050a0b0c070302060901030b1c020108280b01031e0e0f030328090f08031602030307050a05030c0405270702010203040c 72
    0x94102d40c11400e41d80c0e9900d449200b442030f0951160790700380000c0040c45480d5800380142c2488500c3c00500c1d50540c90704c0c1d081030300c02c038010f45501c60501011420181c0c20003d12415100c03640140c001c952004046154540c1844280308070020303c0e8100700c9075148240244144244009841d809803036040c0c1e1a0303501c9902c1c2c0381c0103902405d0071700c0303026501c800c041c3c10600101040c0d07040c804045000741c0c1c540b03545d91160048082c0c05402149130040400c1c4422410017501110b800420100358103240002da0145104100384103041005030320301003d07071600000510140304100340c003009581346001e5851401d000c004c0040c0d040f2101204c0c0140c51080c04403d603154050fa0101344200d0300710313024580c030500300e01c2c01d080d00740e00468010040404071781800d5001840082a01d11422a80e10340760701e03010b503c0c0d000350344503000100f1524450318100000300301d80c0c07550b207941540442c0b20303000200b0030301d441001c80c2114000140003504680c41070041201142c41daa040c00101d4101d40258a107140e188 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 477503129 1250 477501879 477501887
    0x5030304062001060e16050a141608030702030408012901080a0f09030c0201081006051e040915080607180302090c161b1703070b0711010608030a2715 66
    0x542400307800c43d4a01200002c0e01c401480601d0310450085000a99103c0e20784800d5036039000302003c0200152103c0325004446100780020701c00d100f00d082c520400e2180a40d103041a9a004585400040e00301280421040d06c0c2400740c0402c0b010010840c80460111000c4103040b1034018550b5030400ca0950b0224078a50115032001101c8071000d00c00340140b0990f42030107045203100000803070000d912440022003021140c00d0300015a06c45940e06480c0031220203059881d40704440856103803981c1040300190b01c000520808407a820640032a12a142c80d2990560401c03c0040c880014043c03a0030f200314016070751038030090989904031000011921810400c444c1c502640862503040d00660f48980c080c0300a0612035441500d001500400b00f9480d030101c160b000c007191f01c0d0121720358001d104560024541d2280c0030742c4041035140c0040e140f9089903c60342550800c1d40300a6039600001011070b1001e90080003600c64074102001c1580070f105104480071120164414944c034880d44a00144296200d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 477504379 1250 477503129 477503177
    0xf07030507050304090507110a020a031103031b0706020f060f130c03020612040203010b0607170d110d0905011b120b0f060d06050f040506090a0b180a02030f010f0503030406 76
    0x380490b80c072107417039888100003000180c4410012420b13125542d1191400044d40c00c42095000e0a440311503451640c82444001e10800d0480d4140401d000504a00305410356040e1103019070f00041140318a0610003a08000b110070b02da000d903400c5407007049000d5102c03030703a101c1e08031480c0010f05402500c6404d1001074880326400080d030107071000aa4600080d4140c2030140918000c030000c02c400003000c81040401d101e00600141401c04c11250a00300302400303002b0740303040c40c650302011511080c140400c0c5070301c2d882641c810003010769800003981484801d10a00c1d0bd168115448044501c003400c5010b019406940c0c0703069121901c90744041926128841110f20030030014101c1511013640d110f00001400702806150f00914500792459024035050042500801c0042c11410480e11241c031844058080701c1070107034000494080003c440071f290001c00d8810300e00d0750401a00c2e42040200d0a20780101a4071010801c120b41a00b84402ea50100460f8111109402d044040c00d01c441d000c8060340c40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 477505629 1250 477504379 477504383
    0x230c030a09080c0c010f02060115080903070c120b0627040312050106051b060609010b071a070c0210111f0905010f020715060e060d3014030108030f07030507 69
    0x16010560140e81100082c40e0034640134262540103503001e085008030b90b282400d120b05103403038100c040a062010702900030030360040c2d1071a00ba40d14140071902c40300c5034581a6071003203010740d11b1500c0610a008843c8140c0750009030848000b0400389011881148000c3c0c0311414403614403941e00441e0405d406005121004044440288020340c1c3d5060060301c1c9400070440c0744040e0b0902d0814081504c0c001c50b20921400c0000c00e642810703400c1030700350501a000f181c0c04444521801600560f8100ca040005101780e40303071303070301c07107100c8042481031140c010400300380b203014040c901d16400c41844010504608904503403c0c0d0103d1103d00001150151145d00d20103445035281403100d00c0b894070581c004006450090350351851007c0d500703040c0801c89040307202e540b00d071104000110b00d5518040528002c1c2601801480f1144800d00441090400aa0300240ca03c0048a80712100c4c280c0c10114038085141e41d142c80d1420340d85000d1019499200300e1800e0509581d000072000c0030580102c042d42c031296 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 477506879 1250 477505629 477505643
    0x1d0c1803150108010c030e0703030c03110312010302040e06060d020f030a080d2301030c030303020d06091a0a0501050a05120709120c060e060a0210090c1203080604230c030a09 77
    0x20304641c403401080c5420300402c0700e25420b02d00702c0315a4038028001c20544d84035980051410510f9a01d0888040c2d008120880401c00000000c0641001c00c0010700321401018047c44e40c59451841007208680c198251030b40c441c1c10002c1004410758030440c9640c1c1c6a90152030701c0c0c40856580300041d0400195a03401084c000000c40c4801c0250b03c40d61007004880110303604c900e910140d0003481300d070700740003440014514003048800f0300020b440b9801031b242d444054034020483e1601e4006041c252900489901020b40c2c40032102d00c2d052500d070000d00c00409007800c14034500a0070303050007000c80c40b0710181d06c02d2500c1010702142110384143c81c1c00d0000c24000f035007035601040d9441e003503840403211b109850008921841050301450001d0031501c01c85a6600100018889440c8020140c80030000c00d640d4400740c91000030720800b8006540525500c01c2e503515207185014030411003203921003d02c110399100c001c84002014198a614580c0224a0011140c0c60b40d80ea480070b10040c2134112001000d003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 477508129 1250 477506879 477506893
    0xa0207051e0d23030d1503020904030c060609060b09090105060310031e1403130e0105010f110c130c0210060503120c0a080a09060206330d02030307030903020a1d0c1803 74
    0x40f402c00b2000d4128040702880901201c0d1800c8500302106602c1c1c000654040d4020001c034000a00804107a11441d20812002c42d52076610143c070000c480050380004941140014405583c1c41d00404050140804860160450802c400390050b10895400700030b00302c0e2620701c400d5010a05200d04014540c4d4010041c031100c9513200740d085d490303030040b503102358216030180000b01d00550010581810388006a41d601d00d80410103800b103032206d001180f038520a0040400c1c0003466141e003500e0401c5001200404510070020900c024a440484001001d42c60b182071006d1240c0e650120380c1c0260340d407040c40e40b180c64582d171803007050074013601c0c500041c02c410340000e00782941600004090220785c82a001d540980d51a02070101008000440320034511100e01c004084a210081c0d003075990040291012800d00d40540c0403904e150300c41d40055000c40c00c0700000f0011881d11240501c0940800b044a5500d21244140b0980894010f06100d800c2030b4042070711285501c8001d403030300c00098020116020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 477509379 1250 477508129 477508193
    0x3040b0304060e0d0c1109180a2415090902130e1506010c260f1b1c050a0c0201030f0f0903030b04020c07030b0c070b09030a0207051e0d 60
    0x207140300f1020041034080c48101e0403100340641850000e4540144002c40c0c21200b80c0108041058000c000d010201d107030600da481540020816000214440d452441c0002c0d88030300710b140d65030856404a0b8510b420030703003100e00010f6052920360032103506403000b0800364914400100080020102d040b11f003850405800e0103582c00050004400251412004030303030b21007100441e5040e02d20140500345a2110040c1098072150404042070402c0c0d002c0664240b4101d10603298907580180d41078020703a080f03202a0841c122080c095084419200801603403100d1808402070007500500d60350714203000e030741030000301564020b03002440580036160301048a41c00010040008040101c0d05a001a181c04041c0d0004d0620b032080f90340700682e500051500c50f10b560b481002c41c1c50010140c0f0102d00080c05108d00280404020301d01808905003d561a6091600000d00d0544503501c55486402001021602c1c50318229110014003010b486540f051091814060010100c41030404089040006422a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 477510629 1250 477509379 477509381
    0x50417070906061d0f060409020a2007060c080f0f07080304060606080907091d01050f010611060705310f0e0609041e0c05090f040209090d021b0303040b030406 70
    0x4191001c03400200800394940808498044200705000080003c1818480891070511004090140010561440d2588514500059800c1281c00b00003040341d2504015400303030101c8003242d1003a03da0005200c0f55203400d000412746080604040c1402c0340018058416185001c11a03502d0901a200c40d5680d803010b141c021b6080d40111b4040d034500d841c01001140c0c140c0314801c154010294000203003041c1e41820400d600608501d00c008232002c400403036000343d00c0e400b8010340d40b080c0003c0d55007036110345c9007060151401039424484403040d04107904004015400c4002c0d115007035400051010500c01d0f45d00400a5030700050400a02c50442103000510203002c0c0c0b0707989040d150025484c000948601e000d1016440094400624440c2020360b12154000e45c180e10010090003824000809562400030a402882c203646420318041c0c10700070441541006003640c0c1e0003500703410042030841c0e920b8078000c3d12040240600c2085095041d0500042c0d6020015100036051b000083c5030703241458074040c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 477511879 1250 477510629 477510643
    0x1a0c073f0c0314160b04170c1c141f050612010614100306031e080d0e030703030c180303080703060306050901020405010932130c020a030206061915050417 68
    0x2480d14896100b5401c2409584c032040e03821100003000c21801d203824440e5200c503102031800c2031100d501c00d60410343e00079610303031100d000444450004c03e00c080c40c50342840800e014205502c41d042354060402c0180080a900c10030160200c1510300144a4650304001100341c0f0650085110540c21700c1404900032901900c2d0700c030010400c0b07401000492490f9815000d031040c511010300315a010400c641105e022a00f030000c03406119007101803400749052007120032200c88204406042d071003c28494205070709446079010510060030030032b16001141a6001d00e00405020003000c004404010650140c000e4002c50003455101c0d5084c0120300d001c20441c0d000f50010303c1a5400500f0340350000070244841c0001554001030725082d092464009402200c1a41000300102e812800743d0264600c0441d10f481070001c2c800c620b0740a00189002401d00900c0d00c40c01820880c41408483ca180500d45650b400c100d0840e0300d440030402b080f000c0c1d00740980e83c41c0541d81c401c0d2007110102d004000d48541c045401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 477513129 1250 477511879 477511913
    0x60313120e030d140304140106052106060406080606220e0127081b030f0703020c0a09050613050901140705300103030c0204061a0c073f0c03 62
    0x58a0304840307031804588208010039004e810300e0042020501150f8600c012031301d1040c030100080f840a546a000c41c402c2280c0702d07141d280107803c0c10580d00440700b081c840680c00080440c2c00744000760500c00d21945611000d4100c5200d806c1c1d0008084012110901611000814600410005015516041c00b0304480d03680b04031004903144001c40f030052040a101201380d0846d112038105007100e03041488074913010314000807521092140d81c544140480003000524820f81c0600b41d40100d0b081480401982500100d0805040208015503078607450b61482c8682c9010002007010380700c1041d0300d4018500702e001c0d048500212020003034031907080310042c6032000c8120b821480c5c1050741c000188628101613140b480805941e0300400100344914009050319000510003d10240d50384161110154110390340640d0100128200c0c803100c0d02805164000c080707041043c0400b17600c2031103809880391a02134814101540009803100012191070900782994004c031000c80941c2c44e41031129416940302e1310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 477514379 1250 477513129 477513133
    0x8030903010b1008220c030348080c0607030603031b0c1802120a05010602010c0804020a38070c09090312050703020c010216020306100b09060313120e03 67
    0x12540c5062242e540d1104503030581e07072031403580c07209090701781d620200c0070b9061025490f40e0b00b90b4022400702c0599200441c03081c3c44903000e002285180c1840e4041000383e050500b40c1c425810304600d01d28400404881004a980c501c107050280f4080005000b121040f002c9403084408002c0500e8059105806490094549102650860341a00102d034120306004040d4040f400041040c030400300c121590301c0003035600160500201e405140e0f002c2e8821100c0c481c1803030b2240010400c0380d4080c440d242c4902110300d00004540780a8000c20a41d40c2c5c140b00d984000c40d072240d01b00d6030170744d1030a5541241044604145c0c0c04005180301d00d03003841d0000300c8103a84190085400103001500d900c20040e0b16070f41500c450400b04100383c00300008110003801d60060603001c11611000071802c0c8010074480207180300c20380341d04a042c010b051800f0f80040c080b004c2e1042800b4240001d500f0703e0705a4481920031a010356517503031140655030846d19280001068103070350f000e402058a80004881044032000d400f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 477515629 1250 477514379 477514391
    0x41104030f0204061a0702091905070c1e11090403020f0d0801030b010506031302011101180507030c140108010306020702030a241a0609011206080f0f160f090213030c0803090301 78
    0x31041c030f4900c014540703a0170210030000c81005081006000b035101141c0b501c158070000248190700c0603a0007c1364000005020b41300132100700f09800b5540f1400280c0150348510390075590ba0b4981d1031100a81c4081e204020f00b00000702014400c02111400d600140181c3e010b41020441c040d228200c00c1c0412600d009130800049030504007030040d80d2140018010101000d5920340042d00e9104e540c0304045181e5481e0303d0301e0017140c2c604500c80e100345072113980140a41032550500c00e80d000f89076042285003815050b50124146c1c0d201c0c40c03860540740c0001c401682c49840d8400030b841c1c5156840c000305024030016480305040380c005905051070283d0601403019850000203161016080d070350300c80d40081c051000c0303046540324061000503060a00000a0391075280c85c505860b1031036483c403007d41a400306048a013201802e200c0700c4c58140d50250304d804814100446901906240c0c0a500041a0f0100e0368072201021140ca0200070764015410381a03980c4ca03a002c481d00c03039003d070301c0e4903000e582481 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 477516879 1250 477515629 477515639
    0x3030f0f020a0f02011d1504090f060f0314030706060f050f04060b0f130b0f03060a080c030c010c151109030c01080c070807030519030204060f020a0b15041104030f020406 75
    0xb044080640c2d9120075036074660610396006580e0700308925400c58110f00e42840c2c8990304c1e11040201aa200038403901c9a03100c6240540c40c1d801e4807040000b0b4040c150510320108504182844a41e094a6002803980300c514244241030b49903003d02d03072020f40b001d0b0070000c0002d02100c40400c00c806071501615201501011041070200b550824407d40d03868040811a042e50350741c0120190071500500394800c40784c2c80d80c80c00b441080f900700d80c20829503040c0000c20300c80c4600d45443c3c0035008001d450041c04103100c0d0b0b00000b031b4442103000c0c40705060000600b4404100010502c114050824103581040301a07016004490036400462880d8040d00c0b40894040066008070b10301c40c4200310742240c846c605061a40c84642c1d0743c001003011000c0c000141b0403448409644401c00005503100e9070010b8440340b40c10402044207018010442c2507411120480001c60121071103554808240c1d41440b22200340b0703002040080030721604400120001040210410080040320392085000711400d20002e600e80f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 477517985 1106 477516879 477516883
    0x70e010c0b01031505090601080307030507031704150c020316020415030c1d0a09051902221d07150c110411030f010905070912020f0a03030f0f02 64
    0x800060741c0d4130342c0d80f403054680c030001c554001c040c00d51404011036102d20038200c02038100800080c2000c14503021700c080f0b0110303802c2c003a000f40e01d40c9070038240b17900d110b08100703201c0740200c0c1041041c0482d0351000081d28401d1300c48040e000d45000d45039023048002c0411141c0240001e40c420400000304454415190040c8946243d900c1e134210041000b180b0020010300e090080c52a149044d00460700014150408050241a8501000140c0000b42d02d80918070b6001c0340f0311244000c1070415240c40c7d00082c1d84030503030310410010301c2e94089913140c03035040a0042008481c5940142a4500c0c807504154011900552041144680a02c00700e4140d44040c01061310842c4000203220034481c0460700c0c580101003c000411150405844c01000b94100b44907403d610189884c0b00b00542d92800704e081d82d5500300522284c000c40d41c2c1d18014200322070f24500390b00070a00f402c9200b0b84080c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 477338129 477517985 := by
  have h0 := BRFrame.cov_init 477338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 477338129 ≤ n) (h2 : n < 477517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
