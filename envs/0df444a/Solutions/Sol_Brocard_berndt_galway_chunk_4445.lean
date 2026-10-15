-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4445
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:38:04.20266+00:00
-- url     : https://prove2.me/submissions/c22a906b-e495-493f-bffd-d676a716f62f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 799280575 ≤ n < 799460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 799281825 1250 799280575 799280591
    0x71e03060b010216060f05070c0b030901060504051515130f1724190501080a0611130b250b07030e06190207030203120c030412050910030906090b01061101 68
    0x5a03104d49142d080b07001d00302d07180307a01481040e019544a0f542d803c414908a410000981e41d03d600030b0034207030044103600a0100800058890134020500600400c3d1000e106504015614440c203482014407a4032400640c0c1705c1d0b0141c604554159144030b13030b552010100056403244a441c880105005028036035401030483c280381d0b2000034a420002580c040c485c06080181c40c60360005400c05480400d1540250035901144515030141d64003900040015011280b060320b0300750f0449060720820034440c8800d00600100c010414015401c882c0840f400594401d8070400c812550780319980000c511848248025007401400d00c012803098045450800c45210303da910159204030460301d0300480480398503907003100705480e00130f040c40b10b01c280100e80c1009106030f05041090011202200d400001104000602094411150130189030303013003851601a040000c1241340c00000882c400345500c2d2407078041000f4555008460b02a001a00da90b0780d940c540360000c2030314a103151305011a608040d50f0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 799283075 1250 799281825 799281827
    0x60b0307060c0803060103090f0614061221160c030b060414061023040803070309050121090f05251403151806070314010906050105030f09071e03060b01 67
    0x294012030b81d0030411075410760751074100440c054400c0c4513046407a2248000400c0010310a40a20440c1c0b404e40c4031301800500e80b072028020f900c40146070b4181c2c0d560007901406220206085003861414031180c0707140e62103201e121640c0e00111030807002008500461000000d0103c00009240191001c80c2d0038402201b110711700100f06503003910a1940b04a10010005032a40180351869080c810010103812180c0c25400c441800d402580c031105158000160b100b0030154004444409891f00f401d100746094440089004a648410700d4010442c2e03071414110103201400100052007035110003107458847d0388007200340921201e060480c001b11460b0a0100d0050552829002411006002001098040c1c4204075038004094851083c103c603440b10a02c01e4030041c030072580308400540303003c294200d40414000140405034031040019280000030b120700d0b031740705046982200d00b103616218952520603050b82442e4113584901d40e8410110034403544114000300210850340940c40c2000040c010f070700 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 799284325 1250 799283075 799283087
    0x150603020f120c01080406180309080c01111506040906020c24150402030c091903150b061b1501060e09090105070e1003140c030a050604090c09021c0504060b030706 72
    0x40242031940110b40456041c4d403155403069401400303840c02154085008080700c103800884181034002440320001403040e81030401030009002000c3ca815200005e440540701e44400ba42c4d80854099044440403402550300d40c0c200b070091076000041103680b0300b0390070a0a6990708503020300000c1c0300b0003410b140c0801e84030289500d01c98007034844540c100d003a8030000c000003076000406d07800f00b0740001e010307100c0b640c0c17221031314807a820302400542280e040c15400d06800e1030280c1c0c042004010309061a00d03109482e6030003624082c8590343c5603101c0000740803006500b80b1541ea405252810380410000861903440140488040401e5465407116140c000e5514240c581c215000400f00e901d1314028151810181c1410118601030710300003c090004040c500d032000c1d0150744440100c00e0110a200d803018103403161540108003203a0422600c881d664401c20340a445124640700710364089611b0400141c9481d0010050403811340800051805240407401401034040701802445103040103d0b80d640209 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 799285575 1250 799284325 799284349
    0x61f090e16110c01211409010507120903020a020f2d0a050402041a0906040b070614090f06010303030c05160c03031e08040803130503120a0c0203120103110d150603020f 74
    0x381d45c00f410841e4511018259044081c003449442c0d03561b1600404a40b05105598090904c020000c12181001c5a00401e000f03070031003500000070b01e025018000660001400790180e075044c1c0307504543c0340388035001071521503032180903543e4401048400340c0c0001c28603212241c0020205c55040c0302c2e589580610080307002d240500f4442002d15881d00b00c09201040250a0402c002003503945040d856480da90001d4201150442e07005840d0004d8419603850000780c40d030b014242500602c0502e110541d460741d01e01c13040c400613003490f513206502c0940038428004c407020521900c4440809100602d41000340e0121407009800207055524040815951b01e801c0c81040c03001c0b1380d0386051640b203540300c111160340b001d003155199681c0e070480070001500c10303c06020481124045405946040312a0740141c803500d1a8440c1150003c1168480c1c0b012061092415660480b0807210b030b1081c028080303040040c5901c40a0007840d0078046400030158560080000d580c409d8a001102c214590244040000c0d10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 799286825 1250 799285575 799285577
    0x60a060f0206130f050d05131512050a0b0a0605090a0803120712020403020d06091505190b03011409060417040b0a0f031d0d080f061f090e16110c01 65
    0x51804503000c00103011855603d103010b2a00400e4610881d43d60500d0041d1415040011070404100d40f0b00c1c113004540e0203001450b10901209142003003420060902181c0d5826072146551800400d030301c2801c580c4043c43d2800064034510410ba1156000f514030740010b80245d2080c140c0039008648031201205888500c0785034030001c905511040303c103448440c0c0186076481031660901c400009a912201010041e0340266400580c200ea43d04021030176140c04020f02e01070745d042c00140284400341c0c0c400c20084980039480003035148080c400113030140c01c003140d0312143c0644c55414001c1100c800b0591034021486180b41642c000038141d180350b04c60080744600d2017031032028400300d04010302401d0035030815032300c07450001103401c0d852014000100c1641c5a40042d644102d000404040d003004503181c200e00c3c00305010546107401c0b0002030b0f4180b00c403540101703410b140d1211461030324003a1035240301914036502546254500211401c0046981028110003d10241c10341e04003c1000f1480760603403141 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 799288075 1250 799286825 799286833
    0xf1d150a02070c0314240115080919022202030709060f020709020a1106090309190b041202011403070c17030402030a0303050709080a050303010503060714160227060a060f02 76
    0x24503103400e03030310500c01c0f80d4031507050203041c412072586d8800488080c0070032a03041c141c8034076504244c2c0d03030301c0d50f00c1d81c9032500c1b400c0c04074172030900a12000c00520082d4005010392b070003e4400303082c8041500704d00e903203003031800f4050450b243d0b5450003082d4001c0c5110350f000381d50351001a0f69402c8100c03160443e845034500583c105000500c01909a0b800a10b03510705641050808080c94101e240c0c40d04204684c884090340022804aa0614160346140a400c0d210320001801e80d050442c00f402c0c61140384100c500c24040c4c1c1c0e0040c81107900078091900f20700e02d03814405441e441e0040028105004400044500300f4840c540d010204800310141d902964003d00105102e01d101d81c2c003a0010040030303000300300b40203081c4070002c3c00b07007401c2052860341440b51010b580c803545408281850480080c0012080c8209020300020360701c0d000c0e042d5000c00751043d82c0310310a8030180c00481d504202408003410510401e401016404003503000150150a040d5002402e2565070f880803542011142c40750401a04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 799289325 1250 799288075 799288079
    0x30204090e0a1106070807110604080a051e070620010908120604180807030309031e0306031b030f1104020d05040b240a050121051006081311040f1d150a02070c 70
    0x40345200d0748d04203014021500e025162102d49240640c7d804084800e40e22901c01c502c2e5000165002010b048210f000030400300741007078000703026103003002e4114484d14016a483c01071041c0075000141510f4200001035a105042000310b5540c1804640250255040000c1c440c015011210003e15040c0c1001000341800600d84d801c6001d0415110b0580c200315001000070ba0701e843c50800004000e144c1d44001488501e1032502c01c0b8600011080d845a40a00d44820000b0800548a103034030907a104180c05101151440040d000b401804108140f05180604100070003a020141600410307039104c41200d10f5608460300030401101514035904042185004c01c140d50107070100841c45000e42010142c1e082003034401c0340c12a101283c1e0b020701001251010001c20b5000b000064100b1002c208030000e141581e250b071240d804aa03144107000e0b40d954102c810084060354000039030b500400c5070113480c8401103202c05503107010000901c580f242291001c103540c5001c0f4401c44521a52140d50280054 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 799290575 1250 799289325 799289333
    0x30c0b04060f05130b090601050d171204080c01150f09180203150f01060206041a090c0a181a03060106140706230106030e06060907030204090e0a1106070807 69
    0x14805041100e003a41c44090740446102c0c90300840d03205810440700c100c3d80319003e050100c040107002e405014150001d034014485500c800503445109508528100022242c1c014548018420507890b20915918503092104101d1400300034040c00f0a40c0c4001d00846003410a001d042418500c24412110002c0c2004c0000c00d5003a04822036098040340d40c0134940096402107401c118400c0100403e2030b00580803c00f00a0000890501601c0617100800f902d24050303a405195980028125012502c0d6070300040607007200b0030514180000241c4001541540c6010103400d80301c43d0510031890a092854095182e087d00c1ca41031070b42b0310014010103540e441d000040d90040000c10781950008401c102d00785c041007841c05260030001c4011401008026181c103035052066040c0c119004041c241890716001c2c880000720190000e000f103a0b181754036203e14105400a110b40c0c2d0241480d5402c0c100a000c0c50000491000d2200d80140711070060398001c041000317814450100010003843e41070201c14085 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 799291825 1250 799290575 799290593
    0x1507030e010603080d050a050c030f070e0a051008090f0d0e0f030327100f1d12010906020405030f0f0a0303020d060e0c0d110405031504020619020609010c020a030c 72
    0x1032150a400014641d44036207802c0c0c41a40b02003401c000c025124002e002c0064800d1041641c030a400c01302182c21410b0003114000c0b103140103442c9000700301804210348201e50344c54908174024900104450f120b05084140603010420440c1c03464403500030a100c11706083c1010680a0303041410f640ca038a43c2812441c10054840c0d80d0400554141c40300f408400f0704100c3e01d103c4400811110007403900d11080d01e208004e101118906843d04021140e070140440d56041200301b242007441c9040d8030500c00400780818802048190010038070340c2412800c20900800380e0061065500950030b40743c1036014140010707690800140001d0050344562411004203200c0d501034903031040e410201081c910303940d203000207043d0415079103102202c0d000515042c031900d41e03100c0d2040510382101d5207814035241c100020b07190415107045003800281100020210341d999000c0300d2140c00051845800101e40c0302c0029916a41140c180784c2541c45e10500e000d0031400000c0d01c0b00e5940c0e0641da60420801030b96911007030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 799293075 1250 799291825 799291841
    0x120d150e09010606020d0c061512031706030c0f0f030c1507030201110a141e04141e030616020a020904060905060705072003010e010911040b0612041721010f08150703 73
    0x42c09c0d025100482d4032402e0102c081550750083e5200f0300c06000d40d01d01760382801f8014000e98400d500c0041e24100c543c40d52180540c00070003c8425611008004020900f01150040000c0d80b10301c82040c00308003010742202601500d40241e0007045040841082440c0e1345c441d44000348d0100b185903820b0f002d04901c02c0f005002c140112644244604885e14108481303400c42c1e00f08104140b601c003c0f80095090401024031950000b82c2120019400400400d40b01c03103000d0400d00715103400fa1203212181d802009050b04613540544202c03454906410080020030b00ca0504560038010350020514041c8141d040e28486504415440e8025145c80c0c20b60a4902c1492401d0b41c15540312980d50030340100a204844110740514034a00c209030840e4104000c48080d140b0b00e900c40d02d02404402590101d03140c64550141c0d02210140c040161841e0484450280c1c1680d80e000c071192140c43e11014080c503c20a04a070469000c0d151350700d0700d1707005207501d80d42c0a40c6191540780f404400660308074425003060803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 799294325 1250 799293075 799293101
    0x28082d0402090402031531030e0906030c180609090607050d090c05060a120f020403150f020705030c0304030201020d1d01180f0b0712020d02120d150e09010606020d0c06 74
    0x6c645900103109000b014040304e21400c0c0f07488581d0784804c201041084a01c10301d04d0303072000107003600f00e56030094240c0c00c0307170785500303015201a03030001d515500c04100c0a2003c040090107003030342900c45a81c9051034003085a200b40103191100118100c0140050028090000b0741c80c1c246c103118014040c0f03c020441401c051750f0b81c0180c80e4000030262078a100500301a226556181e210309940284002900c1481c003001c40100c2c8100f0003003000c109030f1542e081c0c03400e42071000030a1001d502030ba1200a4010750f030000e081d41c08000340307100c481c1c0c00000c010002c4901c01e03000c0d1100d08441500665500715424001c40303035083e450821980b158807031840350b0041200890b03e60345181e1280400140c840d1a40c22080900100190080c00d02a40036406001000c1e148010440001d0381d060007500c03405141d00b41e0500c2d903800719003891031042e641c0180d0544201400d405040300e0303695601d1134912001f030310000f050354130303103c1c003c074404d840030a440c201d580c1c140c0c44591807075071643d071000d000b841c00741c0000f0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 799295575 1250 799294325 799294333
    0xc0b040f0209040807060e03040501053c0a260c07140d030605011419110a0204020d090b10030302120903032116021504030528082d040209040203 64
    0x8401680d030154002c3c01a4050421a500c6842c079150142c00c941240010302c1c0ca80d4400d00040001e40c1e0b11204544140fa07100c00c2031542003034441340300501c20700d0203607600c01130a80c0146100d01011662000d085005002d945075103488027140c2c11080d0f0240500802c43c052600b0800150780300601c1c0000b484114420042603401c8544001068100a03c4003074403030000e51565810442503038000904040580c1008a1300c1c0741c01d0300017602d06a00c031f017004449000e001c20704041c180c1c03441d010300265807610740182c0b040d95100010300a02005100340c000450361803903004081609012208240816a0381c0361300100740c4040c02f4143d80c0c0280d000b02510640c18401003080000c0e0001034461000b50009500c408070150401043c003000306d442051a0404542c410490402c0381c14a070748206403c2a018200340d6030b9080540b420480340d20b4801c103a08140686164130251700c5500c4404a84035840c1c40c0c0440300b66405002c01801d07803904080280070584d100b44080b03000351801e44501500036200070111 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 799296825 1250 799295575 799295603
    0xf020c0a321309150e1e0c0f1c0501051f170a02040209040612060b0f0105133b04020102070b09031005091615020c0a12230a06020d0b0d02010c0b04 65
    0x4e03605075811418403800382d4000500103500200d80d4813901c108000084081c0c00076a010134003180a50390240e040343d115254180c034201d01424980e01e036001ca980c0040080c803c80c034210343c0c21100c17040001c2d184c0c14425455800050280d01d0016080201c2c500003002d030554107059000c02019410074482c050340180d80b5000060043c481c40055500c15216240c00310340a6001010404814400001c4a06004040101c01c1c03048820030f021b14141d40300a0081c54500d000c8950a1034110f5040f008654084038010704c08808500000e04a03100c1c40c403da007200c03581502c1e10094010340c010b500c000d82e0941d0001d4101c03041c1c40426005503071312180300317400c888541b005849500080d07035140d0300c1103038030004400001c180c203a41407124203001241980c1694802e85042e104040d18000100c0141c100005070359148019611281412241c0500741e00701c0b540008941400030083d440525541e00d203d01e49008845541085c851194009405844400c3e140d016034075040e0640b10010030171140c0400c0c0750380f2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 799298075 1250 799296825 799296863
    0x313050f06070b06010e100c0c0501110d1101021c1b021b09060d02180a27110a090509070f0e010e060d06060f03080912070b0a0f020c0a321309 63
    0x1f449240119640380b05111a290030040d0045030960040703070411090481c004404c1000060140c50340e596442c0c41913681c0c2d4012070707050080c01107540d00205400b5041c2ca07040300041d44c7d0440e000351502d4031402140750440307480076a600d00c2c41c403e0b00501808411900051440c1004031141d1201028000c4ca0b00c00b4126030000d00c400a003141342c5040da41a00e803c0c03040700c442d1403145d8007189461221580414a803002c032004101d51000d03004020030321110841c1660b881c1d1580c44001010310311018082c50510b00b036459107910441c0600d010450a0381000a80414400d0402d0704a40700c0301c588420035150101440320b08042030740252134058840d60002500c131100d291400055004001032516007070302008008845013a2040c4e4101d80d40f080d08184a907680710001c580c103a12690500000703403095500706a00307180c6240411030384800030110001d03040060f90303c1440c20044000106410b58110005404500305003040a90010b0aa602e03a6500c541d5581c00454103038029071840381490841d20b8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 799299325 1250 799298075 799298089
    0x90d030903120e1e0c010e0904030c0f0623100e09070f08010c030c030e100e19110301140411041a040903111002070312050606070503030403020313050f06070b06010e 73
    0x9402c02c09a100c06240407150a000c4146807112059601030702c5e00c00405c400090860710002a0244206407a001040425009199259441c0e0748070100550380c014030305080300105131510309054403101080c1c0c0200d041c116907441d41c2c81002110800c0c6555030401d400c02c1403144004200b12614031071a800400c508405490120051070408008100704144100080a5800c8485030409141c00c00c0070500c4980e01c08290100001c0070f4900018410190295891600c0c84800106400f034040e070741c0500900002035041081d030071301034009000814a0485214000c60f04980242044403440d07140d280303d2420341c0146445901c0a03c00004000d031100009040b510546011000b11b0017078000460452000c0c0501040103642080850801d0400c0d100a0084103101030a0716030b0b980d81e000011181c2d920981512040340c2c001d4212500d9160600c0e0196036a840780c2281d00c1001c1d030b00d000010342880e00d00661000300350090550340c10485103590701c0120020140086042c818154101d45080d00d4643c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 799300575 1250 799299325 799299341
    0x10b131a0a06020319020c120102030406061a071e0b070c0302010e340312110106090b01120203061203160312050c0f030c0702090a0221090d03090312 66
    0x2490000d054414020240060a604805907020340c00702070040008035004410f8926002d07030034100040d5840800c008030b04002e02c1a01d9164800c0c0141c2c19005844015409180308600c02c480c10404203885480d0000c0c5180940c0c3e54487c16401000a10000b640020080804100306403e075248a0740650300c01c000303c14100d41060008101c82004401e050f424010744142e00000d0024007899503960100c2c248200c000200d016074403803100b07400541078041540c802e0056800c00c0d401c19280e0003803000101900c605c511000040c1d0300b80040800c03034031498030518066003070503100c0203d0490712403840f2002c0d406c000c20003980804801c900902d614010300c01402e5112403035000030380c00d50541c940070305a41003c0311784102c071034a81410010000d10801c00c48407141c03441c2c40075a071039541e03020000744d89100d140d40c02500711084106100d00c40e0f40c50f40250100845020300d030350910b40030840108405d4805c03242e00e51b5a41c024404070304024082e0b070140e03452501a1503d800d0403c2d4032500b4200341d442c0d20f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 799301825 1250 799300575 799300609
    0x4121e05030402010f08060a060e0a09020a03020705280311010906050906060109090504230f0111130e04020a14010e03061503010c0203040e0f22030206040c05180408030405010b 78
    0x200b00002c540c1e01000c0d4203501451400c0c40c0d0190308001d0040798108089028950600c00d11780b400c15615556101500002c10581c41c0640d0b485001120003800b9400c00103040700c1610484d6540c902d5a5063740200900880d61850f0400c1c140041e18211110366291280c00302c0c5560b21400040850b00300c2c0201d5201d61036003001040d20303050080c001049440b4941c0715001d00d030301d000d05002c006909403102048481040c0070084060012010751b40c202920034560300419842c0101060f10740208001802d865072440e0100c0503003a41e00c803a8010b0780d00c811500254012080001840719801740d4480d02042ea4047c50200d5000c082c14001c24548042994890701d03054110113000a980703001d0007503010a2041d4805107003010315000383c16640e1701d4042e0603031004009100020b03601050a105055030300f4000303104d8855940301c50a001c1d403108000e81c4e041c1d5010501e800081481d041c40040c0200d42003484005003035a03940c90f01c80c0501500050700881c0d4030754840034124920342c0c40c0082d0314552031003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 799303075 1250 799301825 799301827
    0x604030e010f0509060a201902060d1d070312050c1009030e04060e09070f0b0f0306031c050c0c040203070e0f060702090108070e060103140402220509031b0a0b04121e05 74
    0xb02c1d22150047d400385099071185a030010444940000030050502d040c20341c1030701e045464600c543c41542c05040f00b044610808418070068000c3d03001d000175007100301c0340240d06994500c103002000f200d06100b41c90025059500c0220b41c100400d01c15402000c649009140c20307600d03944110001001e4401d07685c03154182050400c140b040da0407081c0042e000400c2600d04204110785032240803481070051a405010114010000441c1c640742480040e4154218100c4140003191503880a04250810220202c042c450000c8004140c2400d1080700c0c0550125181c90703211903104010041541c40d0300d260140c00c030303c09000440050303c80078070786806810b10001501102e42080003040d00081d00800080c109070402107480708544400c03c25581158040d01e01081c8922131a000c05040d907610042611003070311b49410803184036804001f0700140d009030070b001d8040c003064400c815550944030b800036007869051008240000c00b85606108400210b0421a4140c09001c58100f11420f11200c06004910 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 799304325 1250 799303075 799303097
    0xe091005070f02010605040b030a081b06011508060a03020603180111130e070e090a0b0105070b0c0a02010b0f03070608070c060e03070c0504021306030218061b0f0604030e010f0509060a 81
    0x1c0c081c0102d170b0284c801a01e08119083c2d194000958520401902811501c40080c1c46c040300042000740b4049048480100c842d04d582d6040301240402030032a14100107014040401c0c1c15180854168045079002400d690540d200c50780d000450000140c03030325282c3d650740e0060760300d0030705200013901e20312491081d590707401880c0c007100c1549161700501500400c15510342160132581c2e0820556040440314800241c44440000103841e1032040d4800580329410303d2040115082d20080104582c00c0198001d21616241106003c5082002988698150400350302406140e10444c50316601c1151490541c07000542521000c3c00c90300c100c20558023540001445100b4002da000034000204030a882c1145014103220001e04e00008a00405003010340001d00302425142042014078503d600a0a49075504441d1248442a000c1100e02070b019009112180c1540c65000c0780d017522550705500c5c1c911300007403150011a002005548035005104c03050100d0303815600c030301c1d019001034012501c410320014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 799305575 1250 799304325 799304327
    0x6040b180f180a12140310051903110d1106070503031e0114132c010c020a0305120603150405060907051507230f0703030e0a050a0e091005070f 63
    0x624010000e2014402200224848490025031003a8032900014103a20041000da0708171400c03403820382c1211a0000c0841480030703191446a600040b80c00840d6142d024820030b5094010020f0a8400900402110040e080d118200007410f03801492080000044110547c40001c5d51500000320607505640003008004c0d03805001280c4880040402d804143c0f82d41c5081e070000e52603a080c00581d03000d5500005a040004582d0304245171503415480c8400d5032602c1020403072511551641a01d89541c2005206000d09001080c05441d0b540c00d99245403500f40f090880d58a042c44c0548010740521808030210740c1da80f0717000000d500aa1282c0301400c1c49080c00e10340b442ca04003664200c2485044100701c01c00034a00d400040340c400c0c507405031001100048400c015000600c807400c6c03a601c0b502803082d802594900100303800081e20f2007515100101d100302c000b48880d004250198542001c06040c05204c6803242003502c40d408034682c0100e590000c0d070000c02d001500c0c030a50344003020035919000c8100103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 799306825 1250 799305575 799305601
    0x3150405120415020d0e060307110114130203070e070504030b091f09020f010e010f141b0f16030b2809030e131509020304050319020606040e03130b0306040b18 70
    0xd00d14581840c80c05901300014030a2303c0b0282c1030205002210114107003407482900280e031440f445000d140b05d10b1800600c100c1601b08000812442409255000301d04441014006030161703c1030b07a210360400e800e50b40ca41071402e0028125490f107102c3e4412040d046c0d480400300e0b9001c10100140800c10004a1061044603038a281d201810310407180f1031040300340da0100345c007041c0415910f800c4140500c16041d0a13880d106a03240c21030219030030200010b00c66000104101000410f40407101c880d51032540721600440035000040c284c1c82100049248030748a0350b0728807400180746424101046040809204585c40310504601048034406000c006140c0400740d190981e45d0004248500760145034000318001050240d032801ca64040302203000e02208109461500505041076009020000c2e000b1f5a1102d046420a12840c101800e80350204030110964145c07015000618428908203141c5855a40000f0000340d00300b56182c26054080e138551444812002d0700e84640e43d03450501c081e040240c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 799308075 1250 799306825 799306843
    0x2071e0f060e0318130b0315011703030118021c0f140612210f1309060f050108060f01030e0a03031b08090613030c0b160f02010b0315040512041502 65
    0x10750b0024030040e039601e03201381c4121440050850305025126007403112a4000c164569000f6094070038080f48203c0140c4a107000f03810ba40da60000c441030548206406a56072009000b0f1100c8001c449030104591b180f10f0f00642500110800011079a1f01c036070741002c040302e1022a120550302d880741000d40c0c40c000340003805078108106441040c164400c01004550300d5140301e0a83c0900d4200c003108048580040701900d01e81c4191490542c2d64210a0300d00001e480c3d00b0740651209180703401800140c20502c4100d1404075641a118131469076200320400c091003408100042c18140c4034600810080800e101000e5458440d032000200f0141e8820321340038900d000d03045101403025a40c14401107036030008016038041c0800009042540031460100c07481083c0c60801055a0010418010b803010003580780c8404a449650308869008217600403400d82c2c4501004c0390f0190881c444804800710740c00d0700a98003900410464618440c00744040ca80d0f54450750103140201c103040d1280446581c144030341c1031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 799309325 1250 799308075 799308101
    0x9080706050c0d051302190b07140309120a0b011203090b0a0c060c021b120303010302130e062d0106080a020a0504050312041a030c09060c2103061305010f0902071e0f06 74
    0x1542a090648e2100c10b8401c003500942600100e071228001c0c100c040086880c0548047c0441c83c203818108100b541e20891280102c90408420001007149800c210405c41e456405589100d00f40f8904107101840d43e00c512206420008184200b5021500c18080c2100c44101039000b41a0481d003c414400d8040c0c3e0350700c41d64070907244109105d195010000035641505e0301240da9004800310018000c0050031282c1c545141c0b40500402c004400050200c046000d03020015045c0c240c91070305034030b00b0f2911424001c03840454007010200d0012a13135a13024010614403820100c1c42c00c1d8850000914200800808a40c0d0060015040c405101c41e00120313000603805903135140c01e600f041c0241d0f10302d90241c40003060042d80c001c44c183d812403000700408400ba10140c040c0c1504000f01c82c01d2040290700803512340b0700400c84803a408440c0071603071107514101e4480c0a901c103091410a101000a5403101600b076540f100381404900b0109205100c2c100820300c01c804812141105260181c140c07100804142 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 799310575 1250 799309325 799309369
    0xe090a231c0f1706101b0c030506041502070c09110f03182107030e01031803031406030a02180702150108010b0406050f090601110115080c120109080706050c0d051302 73
    0x42d848605c00c66131030311040d083c02c613001d40d0803150304440300446a40180084d20101030001c140107011801d28010740c09000c3c1455a14100403802e0180d108131070000b0030341d080d075820402810507940c0c000002900c01c185100d04d481c1c0940100b6951f07810544860b90b025848002c0c10342000c60422902c40142d00040300203641c810345107010301150240c03a501806210714002014007a0707101794007219403a006100f20110700d0265003002002010341070015504402c18202048480c9000181010095401001042c010843e490903510700c00c0050f1007031040d480b4094020005204440c17115002c0e121401c0000380c0c0c00200010001511210f80c081ca02a20303058004c510251600044d0603841103007820501c000e66080c400a07401080218a0352500354010301e07001c1002500411030780c800d11000c440322440400a031003e58229004054000c08210701040004006010b5400040d841400000711a04081c11101036000381c03801158820040040c0c281000214a80b1610750010242004164 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 799311825 1250 799310575 799310581
    0x1803080f01062313031205070204140603030a2613030e0405011a07020a08061f05100f120e0706093303150302030111040e090a231c0f17 60
    0x10b5034180ea0b100083c500415000511450900150700c030400003942d10030405228076180b8000240190002c004c101d2046040220180c3d1000030300d0505801400018051031500d07090150a0f694102a4518004a065054006140015403900244c0f15003006002d5004070015850b00600561180c1a01c0307100f1072611005102800200507040e2840c0c600881da0780e0380701c03000d0000407031710007040d802860640b0401040040310030074000c160f6580e40401c524806610b07100c0041107859600041d100f000514006400942c041c460208262a0301d021240003551050059409081c070040303800c000301189480703400300f00038045000b007400e1700400f40b0360f82e03080c4030f806041036203107008008924010952914040c008140384071aa070401185c2c0100200030564091003681d54a030428400c0d10781c11000a80050440c0c100802d00704e80c1e450303120416030b419410404114807418402c080180032407140159140c4e6038400c02050704c000100e5078881011445c102d8070001e0510307043d402c020031246000018 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 799313075 1250 799311825 799311857
    0x2d0212010603050d05070c0e06010c14100b04140705031315050411030a02010c0209180f010504020307050114070201051c140f010510020303010e092d190201081305011803080f0106 79
    0x200b41580c8082950b10425118a40101c0e00cbd1584c141d00502240d40007090030704031110004010054110140050011412142c10841202c119201c181517481060001031a583e21800017940c0c0a03480d4400c1e500310070070a440e03294221100c540301d0f03000e6a58400511080c000c406480c3d00000c4011801402c405616a000034202c2020840003801004e224001c96a681900c1090841510518007100c3d080d000c002441800303400196001e90190280d48004607480d4880d00300b202054400d002e403a440d040b01c5a00449146e40041856801c510244003141032034000f0740a1701d05100121281d042c000d041c044101400f100061f8440ca00c41c0c0c0005c0d8a0350601600441903034111382080404510741d95a6100090400c0062102d15444140c2d06414080020084200d10750000050044a01e9942c1c0015191042460814083d001c503000c2c070002481005400c1c1c100d500c5030b02c100c0010072020085981c0104010350008100c000c00d24045c10880e0540d002c02c8003078010b0200e0b203461580c100090748 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 799314325 1250 799313075 799313093
    0x3120b101103090d2312040608130f0b0a06050f0a0e0c0c0a0305040306050a271a07030b18011a030406140f041506032d0212010603050d0507 62
    0x3004424401c09149900201c8418000d5a0b00c0d40780181605040e8406880d280d0034580480145444c0780c1320240b00b402d0103880004110580801415809207070509041090b282c400700241030310303840c98615082d03100051f00341c02d04c01c0c038052092180c2c020340c0c203040b01c141b130541d01e4076006240600a0300b03c20280969a5010b140200c070681445020719840348203e000152143c2035840070188a5500c410f0304041d0300100410480f03001e90320421140c0c8586060400359a1545030040601c030f041404d4101e003000c40014019001e2060244032001c2054880c01d0444c00c2d02100c600010a941d4034800c42c4500300340111102504a1054503011076040203c0f03500f1501250240c40c3c403030240407000404001440d488908085c0c0c1280c942659032034207a60f000c1b8058012034088401d0034035128802c68007a650301032a0f060782d502a021000000d0000d40f440b4581880b0600c1c500400300116802000d0b0b128000c49403200150100086605821070a00d18a032080181c0302d2003c01100300240c0c004104042 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 799315575 1250 799314325 799314349
    0x7080a03090512150c0901140712110606010801050f011e0f170402100c0c0801060e061008060102060c130b0d0c1103120a02160204050a0e060108070e040b060324010303120b 76
    0x105c082500d40703203403000480300318001000c1500c4c0b41c1000500c01040c007030703100410004155607903109441e08074085142508c815041e80c405d4003140d10700c8014040381c60101040c04840b10103142c4054010080e00800403c11100d419810200d0749803030800d10084d0f404904101341103108002d80d61a4146030f404500d480d590601c007401005000a207402c1000140708101e4001d0801400a004050f01c901140c0b1803140c040e5003580c807600300d029000d00810300400c8000c0c0b2500c016006171a803a6034030320022540d58044a140d80344410b1355400450014001c0b0090550728554810018480360741d403c01034042120030040f240b47e0303402400b180202200c1542d4030f540c0001c0d0101e0150300e03003400000d00401d9516411000703600a042108000f002c01d103a40c04809004103e500322007142e43ea0301386142e160724a9000d8082c0d05c40b040c0c800076011801c088942a00a6009001c48158401d07440f0900018022842d921420b140144010028158040c08200481c00400c2003001108020000219540742203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 799316825 1250 799315575 799315591
    0x307030909090303150b280f0f021011030901110f0f09030a06093c0b06031203070206011503060b09040b0d02040f061d0609061207080a0309051215 65
    0x442c180c500f058400d4220610800c8512070000788036484440d40c6081e5088010010601c0e26125262400360b0104400c0c8560010b0546403090100d84000045542868007401542544901c5024981c2d0070360303901c600714891a164120503120f0401d180c1c01ca09403810418880148a03040c0030300d504a120240442d140317400042c0351a0740c3c0c1c0c410000403d050000305600940424a88420202440025050140b08030341c0d03141140401c4005038140120482c02030315091100710714007200070010341004006500080000d08a0b03403405064020341c80c143d4022124a40160801001003081124015030100700e40c400742010b0100c981000310788403c60040007032481c0305503201c0c07214030319580340c2004c2c58010340e8015200b07014000804030000e000e032000748160390354410b0030a0301d170b401d211124408502411004100000b00c4d10781c0802c10181d0400d04406802e00d0054400026540c0001c1101d0003074140300740c4450302c08a1510701000350642801507142c48a8000034031012002e00c03c200ea00d80c0c00901d0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 799318075 1250 799316825 799316831
    0xc0c010e070303024204110301050c09010309060e070602010902032b0f211e051506130b0a030b010305070c030207060513050303221211151213140307030909 69
    0x40c4480e00e0198004017464600b00c1729543e844010b07002080c4004da44030760f000e40e100d46000500c00d8141800c0b20402c03a8044059001800020385640c444d0304104080d034020300010030680708803070b038035800e2086550244000d40e41d43c0300c0340e20460806000c400e1801084480095080c25003602c5111b454048a0075070041041940c140d541e510300800608c0d00c080c500758403410595030040c01d1130700107051180009010182140300700c8200e0340e0307500604c0d120304941d4071081d50154002041c000f158001c4031000311020480480850742502040141080d10303110381d404608455800000740c215100039042804210b414222000440d4000800b54100c50a030304d080fa60b5408071058491100195401042e410b010001e841809c0200070b12018010002c1c0050040b030540e0f40d62042d11101c0c0c00860300030103101d444601241140303030074004503044a1100070060314084078003135040901e032801c540c00d5040d801e43c6041c00d424071030110050010f6103203c1004504e410b0007501c025110380d00c80d101703462203a91 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 799319325 1250 799318075 799318123
    0x6010c0204020c160f0819080702040605090408031f0503250b0403140c0a0503120c0a06060b190e013015180c05030705071a0c0c010e07030302 63
    0x7602d030b040f2214824000b044c0c4035158080c048400014525105800c2d10398000d40707000c1404440456080c00c41504120f80c00891001541c07803880c00e80040300b041e64000e0340d5443c00070b1a511080d8100b4400c520a0000b0fa0f501e191800824102c03000d100854002c0b0010182e0501030f0703880010b40ca17210250040c06800390350b1031140700e00c82407c01d1504100710800780450004100303d1018070100303035482500152640041802c2c00c0c849506030b2032003016495031203985513908040300350b0300600c50000780030240d440315205503c1d031380241d51b4280d0004605c06d100040c443c80700c07003e164118014002518000c2c2e58441501c0000f00302c0020364402003100451a0070101c1d80d0031088000014810000405204001200380542007054040c412442d1071494181c5003601d14010744034070740c080a904c4e181e03142191210142118117800022044402e1030500c2400c0e0304000541c0c00182c80351780c400c00e800c0d40d626485141ca0b825284900c2000056038480d61003400000e401055410040b960b520345409490 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 799320575 1250 799319325 799319329
    0x13020f0d02040f090317060a03020105180d0c15081b091c08190207060c060f090606080708120c10020906120f1806071e020c040f02030411090f06010c02 67
    0xe0300c080c800a60040c079201d030500b50114113804ca500180c0c00398482010411504c4160354040e0021144113503c038029034070a000641c0142c0250a40020240400340e1744045040442c04040054405407840c03010030904020119802c00505d010600c5132410b40308034140b18000350481d00103000790100c2d0950101e0700c0036858403840c0905c0b11914a50480400003042801d01c81e049a11801c810110780070350b501c00c0302c10140001105012101c1e00d5944c150090741d50703182e5000920344100c00d4510300f078888913220302042c1d60740180c030041c058800c00303061040e20700600e8516100c00105404207003542030081c11841c01c3c0200f8448503400840b8000b59039248047c0001d11903120304031042000c1810b080c1032040c0c0b008150400c510400c551047e03407403510303442048140c0c0c42d0022148240000c05403041c403404150081c2412a00c041e00740100d40640041030002410f03120f10012811010341e0201c100018840d0081e1010707120441506c00c40c0081c14581c0000c001961300400d041c0c1400310b0b9908440c215 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 799321825 1250 799320575 799320589
    0x105120a05100608060108030403081204170d0c03050a090203030702040b22020408070504141317120603011d0703110109030210030c1d0a05012007170708030313020f 73
    0xe03550001c161107801e062100407400812250142c81c6452248800128141e100001210305507500700c080a1705181030242d8419681000400440b0026041284102e40c081d000000c0d017200390060001060b04091800020205c2da0014000f8010707904044010001d6180881121103142d0162000301d0a02d50140100d11101c11110b40c038084d1040d410050028049140d0262060f145160262501d50b1358800c00c000507660801641c1110030141400b240080900c40c00c0070856078850310004920000c1141d203100c045d000a07203400f805484003020000149021300c1036000a841141d00003040307041d0205440c0d03503542940401044c8001c610075103013403680101187c500544d802800d1701d100c6e480340b4000030003a28552080c0d40c013083c200d0b29500c030a0400f24281ca95008405004190501d1820004544c210f41d0102c2c4081c550005100e0b11040d02002d02c92600036008000d100b45003000500c504600e064860380c03003140e10340c00900520180d449505021540b0940443d0b000498020b454001801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 799323075 1250 799321825 799321843
    0x721050c040807030305070606060f05090d0609080f041e150503181b040c08041e030e0607030804120305090309041d01050103230601031101030e0a17121e010512 71
    0xb6201c1c0c07203800410540d1000003070024502c1030314103120041d500e5009071840d0b405480264045841407004102c6410400c110002c028010100420f41d807030103840b58142c17540030031f084501050300040c05010403d0a413084920180c04a600101040d25140c0d5908240a2844100b0308008000010450443d20144c1030700d0000034100558009040c940d2960102c0e41c035204c0c3c44c501480c1080c00d03544166005030f40d040c0c4107030b401c42c0645041c0d1482e100345000d80594000100d09000320b1079204000360b140c03078001e440d84520a031600d4096060904010700f9249074082e4640815003444c0401000300b00c00f00c195a480c072016200851107162000f090783c2c0c1100c2d00c02520002d5841d040001080c048807024260003162581b2404680801c1d040303c583e00c0d041c00b4040900050721079039090007030394401e5204241d03241061003525070240040e42d41c400c080c10340221300c0302da41d8004140c3e81e80c0411400b201c03c0c2c1103c420f4000b60408102000803880305441449528420342d0780800001c4000400c0c850361070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 799324325 1250 799323075 799323089
    0x2705041403130608010b07050a02151308060708010b0a0507300201140a18020d0809030a060f1508060f1f0902031008010209090a0b0604091b080721050c04 68
    0x52280c82c040312076032100600388102c5000600401c0001882c070f070f50310211904a07402001508071440e0300d40a0154040384580303035444806042281e0314074105000d01c000080c1c4428000b80849040c9044000e1480406030449005100308000e01c3c0e0f9801c4e0030100301d500359903005000b018a1a119662021080344100b82c8001074a280f80300552602c5c0c5c1940400c054480790b00785580c03640c6990105e841100c003550240781800442c0f59101026203041001e8000452003541101d2500f100a03000ca414800989003c840b00398031580d0002042c011402014441100c202032540201d1400000341e940d58405000c400c8076429079800305108880101c0c4441071044680c3c0c000742d60f295562600d00c025030003101c410b90240e02c401d038003040391b05c01070081f14040d8070010111103040d1203085240005181d0303e140164003400410000804110901622000c03450440c0c40e5042042060409050260001c199000300500000b142c0c4012a0300085100c060010701c0b00003031259500c00a1100620a41c0c00c0700c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 799325575 1250 799324325 799324327
    0x120a0f0b060c0102030402010f0e03210f0a171f2112020a111f1d100c02040506030d020714010c1a04030f0f020601050d05031207030501050301062705041403 69
    0x60035400b05400850080703200303a841c000300c0040358008840c4c89040c4246907601d50810402e0741c50061883c001920318001015126140405e030310091401c6030300502c0007102150108214a88901c005410b0943c440c80b01c000440d103c07541c01c2c3c1c85250416135809802c3e0f41c86d5920504002d40740c1c1043d05c40740340e90341c054903040c110084800c0203075580800000465414400010205550502c804031500c10140d250700c031070300005100d405a41c00d224204640c4680c4418503500c401a42c1c40b20140301154826441c0c00100764142e0050205503000140118081c0d40440d02000340981d0024001703044a01c0e0b48440c084211410700102c4005144400141c055051144080c00d08880040481d014034840c1e01c070350502c11500d080945e40b007100c1e0410000582c01c0100100003030300304000c800003c03511030f6040d286080c1c507001502580000039140200040c0e41d880061001c0c0c2400d10415020f080c1851040b00344042c82914800c5070303003608801c6841c42d621003011a0404c007100c400350608081c1c441c162 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 799326825 1250 799325575 799325587
    0x2070b09010e07061409012d170601031b140903010204080309120609060112060e06090a050106141309021c0b15041b0309080f04060e0301060506120a0f0b06 69
    0xc60103048607480351010343c01400d500240307440c05203080c00b10401580b10304c1420219950300642e804501030310a10220411500f840320000754001c8610138a580f181c0740c02000080c1a018511116401014541130510701030010140f0040b0844060201515240c124910724014102d850300d8000c000d91107426600204000c0303400329010000d80039040003070311001e060f0524001c0b41a599201511202c00d00c0d04400d0050100c560390a0794441540e0181102003500702c03080940500c2c200c42210840e903c0d070002640c01081103028040c180013094080d410703100700b029000000da120045a8100440c540c0e0707890f140340840d110450602c1c1c601002c40c2c0070000c07038621760030080004c4404032005180030600c21221450381c5014410740860305499a0090101d107071100040d80108000741c0c0079112104103110362a04c02c2c050314020000b5000543c0c07441500b007040c8e000c0c03500703680f000e400a9100e22400e1054004001c62001a164840a40b8801103404142081300d100180b110700c0706950803081c00115 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 799328075 1250 799326825 799326841
    0x9110405031207020d06050402011b05010e0708071d0a18080310120305070605070e041109042f1305030a060e0c03010504050d031a090a0e1b0a06050c0102070b 70
    0x50021100103506a801c031040c42031082c0c5143c820920020360200804803840c011030810f0b032180381c2c81441814124285030103100d103500020079500c4120f420340e4403800860140710040c03120000810185005203001c601702503048005603400300c682038000705c00b800000d4ad941140c1d004600b024000391041c1c03403d082c20382025510745c0d1040701c144209068000c80098080c0411800c1c0c2c510350780655505003070440c0380d0742d1a006082c01621800400568001c590410740d0740d0710458407410030200340b41d66a915820184415220300d15083c604454a40c242035011042c1309144040e4901d506618942d180142007804801030019081683c01d032290815a4040000c90b074420b13030449030b81314120ba001c0c00b01c0303034101802d0340c3d0100c8008201d80c014600d0506428042d401c0441e900c2b07518034000340b442901402191a500301244c0c0c0d00206034482d903035400900000d205420324451a480741d1054032510b5404240000018031440303041040010301c0000390380080d03041e42c00c8583e1100d1003807010304140813 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 799329325 1250 799328075 799328077
    0xd050a06060e09120a02030f0a0302070b091e030310031e06050f0106270501030f061706070e09090705060304060b0301020a1d101d011b03120605121c02070911 70
    0x40c3d0700342039220791840326000200380340c1942c2440d00668011440c1104050022082c0c1c0c101c60008001c0c1502403050400054002d44024481e038000e4008102d40940b009e108103a49242100f0140690010000d2013001c00c0803100781030603680c12009030036012660604130904e124440703401910507032901080c4005c0c01a40c19400c0d04941503a03488804c06920340b6a03e004001d455180307910124504481040554001d0300040c115512034071000a5481c1d0781c0d0501070b4180b6500d41d01e0011604180104101190041d07111103d4a4050319084aa032401c909065a00d003001e002c3e09100b050f02000040401449030403130f480404010707009548503140c808003d400e500000140c10070220b058080340c40d4600303280300c950380c1c0d400450f03a900705100c50860202c480c1d00c2a0b0164181003001d000b42d5174594034554140349890a100e69607500304002114913032811100c4640003507109501244881d94500d400050030300c070303540880e818240b0114890905a140c10459030001140e02d062251a180c0402c7d810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 799330575 1250 799329325 799329331
    0x110901030b0f01050a0e151903062901140d090609030c150506010504031e0605010e010e0f06010c0209070c0506192403120504030218010501030b0d030e0d050a06060e 73
    0x10b41815541c3d0b00e038400c100c0c1481c807600460016030050400503800d007400700b00360b104428000d03202102c02e00c04045d40e241d115070380344c0081c0c0e401a11280110341504c540030a0700c6541680713140c40c0d68408031210000341031030120288a0344c048400700310350802d4030159201854032540840108a1800180340240c62140080002d031800c07007119802801c0541079014040c401e0318142d481e545464199030700c904260451a82c032507030321211301605200082d4a4070502d8040c3c5034901d030aa016601d050206440b42200411019180240c01c1c2400100d9800c29421059264116400c80440e0384008040319804000240600107225000c140301c5181c68045060030b066818079420300005029240020802140701220500031410000c1000840c449440c000614460380c80c2403440c03e9540d0b00022040d800b07400301184143c1c00791004001e10740c0c0500c100700f2038800688101c20304000903140503040c0c0c0317030b541c0130b85000d0402d0707140800401070248202080aa0310980420078243c4403041042421012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 799331825 1250 799330575 799330591
    0x12030b031509150f010b070f151b0906050a05180409061505030a02030a0212100f021305180a1d010212010312020619021308011d100e0316110901030b 66
    0x200890040800042085100b41c000040541c8241d286c0f03940b8030001c0d800042c055801801ea9440c0340f00144002e035824a03244000d01022074910340303034003420100d20003108039441841000384040118507042001d41d5101d5506003050768032004282c400d44400c061602d0811f41c0303d8542503c4c2c1c02084403a80c0b0484068407440d1807941c1140d2210241603030b03010b1229019502d5440150850300500e0110051543c100c00341c0196403c40001050b210141c540c1c1c000c0c01103010345c01050700c6060703040840729480240400c03107400c25000c01c1c1030504d00780103501405442c1080c3e02c84040302441c3d881c401d1a8000e00700030b48000c44d911046000ba0401c621000c1c04110f510961091004051900c0011903030b0040508604c070204c2c1001c0c11440c240258080d5404014640032901c1c009002c5c2000c1c443c82c5007101749035001c44d03502050f4000c2c46003018280e0402c0701e03100d803508410b280c0b4200c00200740e40764043c0d031070425400005d1a0a00f10141c07209001d03659070100302207001108000c2c83c010702c0360266041c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 799333075 1250 799331825 799331833
    0x905100c110d02010228050d0e100311160804051801030b0705040e070e0d0c1205070f12030810240314190510030501241a0712030b031509 61
    0x41c15007040525281c540001e401640b2134040c0c0700305140d101c501600c034100103c12883c881400355450a040103e2110100b001c42d2040c507901c4001e081c4850100c6113800c062504200000c20b00e1154201406003c29a1840000040010082200100448000e4900148a01449800e0480d401380d548000d000c01c42300c00b04944c01042205000340c080d6829180080c00c40c038590380c0e40040c01c86d411724000c061103a201044e1101d0301c0110303401c070b00d02101400c072014603181162100d0034214a0720886034045640c02944040c01c00c00e481a408102c0442d0768140b0f04400703a6250070388401d00400ca5a00986c081c1940301c001c601c81141c018080f1011640181c6084c4444021242f4280c9207c408859891055100000b14600c030b11540d0300c52a8410428102011666100e880307950849220244095026624480c0080e810b640581c80c20010030760f58401d00c0780380e4401021a0410b0107104402800c07a114a006017a41a010341c110200c0703400050103c0b0704000e0204520f80c0c031181b0079a001074041c02 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 799334325 1250 799333075 799333103
    0x207171e0d02150406091509020306090a05031b031207030606080f0402010801182408070b09060d1e0c050301051c120e010c1e030e03031305060306010905100c 70
    0x1000700e01e0352000d00c1141c000e811900c005078200c1d034402400510854526580f14000780008101c02031800300d40c010750030001784590079441454070b841c20240410040c0d60100f20601c0015100004580c15402d0310743c210b4004481c41403090745103000315082c5108144240041000703003075059218078100c408685d55142c4c181c8810340562818002520060300090a000c0140812040700c800041c52400300d902c000b45082d1744100041c1401c41e220580c017919000340004011400d030800441015102c5913124924200c45400062201c0c402d14400518003521035513030b0000561448103142400496060a000441c100303440105107610901410707100d284030881c0d2001c1a2601c440d0081d0343ca40c49203812000301d0f80c100040d00d0000c208034159042040204140f0b00089002c0d40c40ba00f15a141c070001007424910386009494103412001d498000d80c024440b060f400000010140220f5074107950040c1d0f40e0700e41400403035644805030445500100440540190240d0096500301411700075000705040701 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 799335575 1250 799334325 799334383
    0x903030c07030f260414060903061f0503010b0f0d0201031104060903030f111f021c02090405090a0317090a06111305190b03100302032a090f07080601020717 69
    0x13078101400032820b44002e00051040606a10140d1040c0d14010001c80c01c20b1860800280740c0705c0e049403c081481008005465a81021412480980740403130090101440031400309030310404103080a403103a410420610250390095000c0e120440d0131804d080e40d00ca44800020300317035032501c0c8421000505040c0090014a114448940344014020090b00c181264203106002c171842d080e11003200c1d59070030004031071484049046001450099040540c6843c9040c04200460fa00104414400e402900303943d030001e40d100e251200205d011111140d4030f61200c15156150064250004210620308016404003441a03030141840315034104100c1040780d16001844143c41744602001d00c4076000300c00a01c00c10b84800040e5501c0361940c1c01d030440c490b0b034a800191821045491020221100d01c001c1c0700100768241101c103407410140d035007170382a040c1a0018400584014020410409008081501a84281f01030001008000d4288055005185603152180441c040d4211030040d0615014152 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 799336825 1250 799335575 799335623
    0x9283f02060409020703030e010501090e15070806090c04150503090c0a0b180d0f080918010e131a070f023702130f02120105040b0904080903030c07030f 67
    0x4640c0c0948a1424240740c4441035000e0b4000003170840515440b80313031442000600340300720303402060000b0010407500c60117131200341001682a81420000307050010005107d812170411030f0840c405643c1500d040e41c6088d0300b042d13070f4007490300040038403980a1164181c0c276070300101071070043d02c034401541c403034400e000700300940390750b1501c5450524502440404010700c3c0081c55080142005060b202111806a0703550750041407000e003c07070343d00b00045200b145500382411031000007510f41140b102154141654580c020310020000d42d4651060a8484108500b00302c20802500340d6401c0c013031250078051805850000100c050600510034041214601c500d40340410303010420f01d00c528030102903c950103503601604580c0a98101c620040c0c00e1800007582d100e282011400c00e60016224940e005603a81301d0081a0700c00d901c218140343d5000c03550343e50104804c0d0020b921131008c99844140001107411030040d1146205240645030300001880080c1072054a5644950000307050f00c2c0a1031000140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 799338075 1250 799336825 799336949
    0xa03060f0b12040b0601020f060103150e0d0504031518050f0d02120702150f0d0605090a09050d0e0f0a030b040203160f06051e1c060b0928 61
    0x10b1902030780b001c80c0100302c20390300280d00403d040c41901c5010005004541c42d102080e441164a07582100d2211031014461090a0700007205401030101c40d103031040c0041080c011401f011b8486501c80d01030000e0a090356111a14100f84803005a031421000d00304a62180001440c9420a004181c0d45104043c8003062000300400000c1000d800d1164075002d000c0441040034429015600400c000f60b20041c4075409400d001c00b6408011030402c0c00c000500446520140410044508141103140058000301d544010030726181f504401070703440e10001070741c10445441c410b6001120440044103000b10240745620980c000e604490643d116501c1601141d00700303104400343c41d8150b5105021241c844c000030200d01c280028a0310500680224a080135400f0403601c0052201e00b9000d0b070000300441c0240c000606140318903070b08003800940880e080701d400f0400001c1120055115544060402643c0f1001c1d00c9001c2900e509242d10315152104582c640d00540b0700c4c03500c20444000114103013810451 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 799339325 1250 799338075 799338097
    0xf0b0d0807060b0607080717030f0114010c02060a0e0301051b03040b040807150605100908030921060403051b1c1d03060c04050114042102060d020a03060f0b 69
    0x104181a00c0d908910382150304100c40d055190b290482d016501c21014040080c0a00b075155500e420501d02141d035450000701c043c441c03060034800c00800e082001c0600d41103841c103007200e40f0382d1041c110048070440074001c4000c0d03201c0c4001c03036611a003a40c4100c03c59054203041e4001c210a0315400e180ca0601100a000000074010801c0014000b8080d048601e41191045c1400750406003075903916005680e60a160200b003d0740d454042040340303407280b5540300d00f13209402d1040301a030401d000e117503c912603507414078041c0b048040c54110051034050f1404003e86620141c2d003c41c202494014250b0b8450f99800c94040c24546420750141000300d104018003198081858240720190025500c191603001450040c08142443c40c03a1928240130403840784040d000819955410140058132040c42d00201c1040c0c000f0901052000450044400c1d58081500164404d42e00b454030015806d07126001d941901940089002421140c244e003090003910600c4082c001c00c0f586540e80050107014103d4050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 799340575 1250 799339325 799339339
    0x2030c030405011b06020d09030917250302030f010222080c01080a2712090324060f0906180b0904030e1302160b01090b030a060c09090f020d0f0b 64
    0x2c555030140c03501e42520500144885a48035040e25030500700e0b000910589075042d2101c103542d04040c1d0241c04139024141c0e0306480d075075050344812410350f50010880300c07002c409003425440203124081901c900046078014110780d0f4042c2703101380940c041d400c0800003807048140e1940404100141c00425425942048010b050410201004540340701015121074200b076515810710241b0411565036220701c165003850001407548610304410080c080300c90725010080843c01c180b000405400741107020324644011104290f802d06084c50040c1641d0340151100821010000359261840d00808101c42c8070355448100340c104540e02c101600c9040f0340c01c9901500ca0800200000c0c0618145004400d0190410700321003502c098030000ca03400203400d100c030410a1000c2c1c400b0854010407003400340c40c0c8040140951000719011a69640d201c0c0001800c0940f50640307030610510a20940bc01801c440400340030352403222441c0707002036000c00c12000342c050403d03544003040100341c0100c021a5901034202 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 799341825 1250 799340575 799340579
    0xb06030705010f050f0918040c06050310030f1401060807140409080a110a062904020c072c040b01031506050f01030c02070b032d060f0103051509040302010509010c02030c0304 77
    0xc9404d41d200c044076115008051140f8851a22100b2104030022022016141a41043c0c00c0500c0000041d9000e981005020020094820040703109003048a900040d40c8440c0c050074076000c4006402c010706040691b207003003400905c02c2d000040d8170003200d417052140c00c1c81e1a241c0003030205903041c115000d080a44104039081c80d042c403d102c499070060310354096a0072604283d4460f01960102c00104a071154040483c140d002c401081111403500116011454120484021500d8141c02c0c850b070050321000910b150301c03000342502020790b05105124803041d103180c245800400e080302030200b620050154414609400e0340f511414051b12402003000c02c08402c2080110b010303000d0f44145004601442c4c0c00050f0760610800618041c42d81108900d52514040076582d1345210041c444034809156001031101585034207950a003c10750038a40468107039070718a05540150114441160000045c2c2c04100525030b041d400300303010342c0c0c546009002c00903880c681265240038040407002c01350020001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 799343075 1250 799341825 799341827
    0x80d08060906120a0521070b0f0402061303120806030334200301240b030c0c0d0f0914010e040e071206020a02060705071109040206091306030b06030705010f 69
    0x1529a0000d0000c00c100120a0802ca5480c1803550000084610f80c2c80042d001d036904403144403030b1b610316041da9105030410b51141c40b003120800c4007038000c0e503012440700d02250664070360504072907400780000c0030f202c40940d503442c2007130188103a86081c200042260700407a22502d0044119960340d4114001160f480c6905800090050003c080359007068440001040001e00b500351999101d000005801c60841c240744141400c3d201c0130b0b074000031440c0000c44104c0c1511b402a0541046e2050120b0791345d166540c4052818240c40384825091040c07284002079440c8940c4400c04104243e60341e81c0f40e43c0001d82d111300b503540f0114111006404140080841034090416500000f140780303030300f400c854519a0301c50b040c2c12015440003096411980004022602135010000150042d02a00d48a8a040c1a030348803501c0d200107150074240b00703001d090046000c1d55246000d5989400004060310910045948083d00034038851104980000004001408514001c40d4000843d4010b03114001c1d08040382c0c1c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 799344325 1250 799343075 799343089
    0x10050306180c0732150a0c08010b0904060f0b1c1e020d090f03021c0512130510020a0e040b04180f1a0a02121305030d0207060b040f090c080d0806 64
    0x1102c0000c041d00c0d0400000c0b132089294264040455260103003030304003048410b001c0c07140c800a10864007203060102181d4030035400100749044031071403500503440d14a81c00000f0060031407070b4040503030030190781c0d004075280130380c00001d226106074108050b18202406003080c040d0350100800400012013809105030407201c1d0b4000704401450340400160040480d59841c542c0c2c080780c030b0150016449003a882d154240f980c401d00076100c2003400c00b00d0804031017281300d010150340100001c158050001c899401c2210070000004038103240b0390255100c00d01040001c20b80b942d036080051045003000d05039101d80c2014400c6007416080541c40d5118250706407200080e240d6524403c44010008403909004040d96000107401907620380005aa101d14100003ca0140c402600d5004500c140013402c0740022000011114142c00415003d6154002ca040a5004111030454584c1044c01c0441c00e03001a40c05d076010318441c80c450751908240646884410755104180d01d030300c60210b44400042005450041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 799345575 1250 799344325 799344353
    0x3060504290103110f0c1e070311060901120e03030907050a0b0a08090a120206041a1303210501080705090916050405060d21020601270c0306030210050306180c07 71
    0x50017460050745601d503803c3c0d0707404106c034243d4981001410b002440044112a0120b07208040188046030460b1202c11500220b86101403040100280d5035145034000c1e08420309504a2000c200028000d000e00c054a075802161034070003034014500c01059a28040c034591003510443d229071400c0100350340c0252a18407026008124610074003440c07000248101c0c0e03243e030340b0703c020f80d0141c5000d0800c0c0c9000c8800b0b101c81802200a800407500b04240f60b07000200c1d8508943d01031078000305569006480c40e82100040245220090400c4004111b0324000203842080b503200b95141200c6643c0e01920300e1315100d40d03208420032032031011000c000c00e06d087e400907a0001c0c8010586600c80040303030344602da4598142c800b0b40c0c00304040240b5015243e018003a050041001622603040e205151042007c0961082d1400c1d0303403299918418208544207a1203072000e0359000e80094201c94200c0d01c00362940c0c00848072103102e100c842071840c115512a150041c001c0400c0740340181002e6407607036030101620b00b034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 799346825 1250 799345575 799345601
    0x90a090b012c0108070303080109090b06010e01050d0c0804171603030c021f09110105190c060b030a030c1103011112040303110f0706060902030601022a09010603060504290103 77
    0x6403907000c148107501d00443e00a00c41c040043c851149103140c00380030030805030700450a191415402c400415a49840c1581c00402464008411816040142c400313000e03484101458030300d011791039040c040e00005c0d080d01a034050700000180b00901c0d55000407030f12a840384009940d41c030240f1500000d000e50803060b20700d4414010389502000b05428045280c45020129601e40e45074a0b108082c0400611500c210141c00e10b4020314001095240e460240304104110040000040d0060203001050b4401201c02200030f0030317180203c0395404c0060201d000d0040580d0b4003000141600580e1405100b40d042c29541c00905a0600106601041480798010002d8003455203c5a020907500d131042e0041200301100d05032a83c40b40e4203402d200e0100c40c001e404c94118503104005010590780c0004243c510b810b0b01d1000540309501c80c00a00d00d1007004601b10a03080800742e0000303da0705070150081c2c01500c0042d1001c0000d41c541642c0122071404240400252403031625040c42c01d5442034101403c0c03040c1c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 799348075 1250 799346825 799346879
    0xf020106082a0a0b040513060302150306090a0905070b1c09060e010c02060613050402120604030206011409071e2a0209071706010e0d051b090a090b01 66
    0xd1a107450382010072088400c2407040c04104800b00e054458074401c450702400b0384070382c401281000d291035298410360013068464008180c007500c060109810400103998003502011901052041c19074960700700b51842d6210310789450000d802c0401d58820503044603000740040c800c01d486e0410518142d804203941200414910585000b03ca00c2c0340110418284215800110400e000c500f0508607880e060500b01150410000c1c41981c2d1381760000a42e444408074000a032544842c0300045c480500d0f0340c890011405140c0070481855000704020b8101c0d541c0007210f822195041c0b04001c40c14800726001004550a1440f1800340074468440d078030242c43e0303811310810058814a0828040f000144001c40c1003022030461002c500301108580d400500c5820001c07150700d94000d8411a944c4000c02c1b950401c4000c00c0141c040c1c0e40c403015000b00745a040000d99007101c688598a511012280311007600404520300410601741403442404020350b04550031440c00d90074040343d000003450744280d045c05801 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 799349325 1250 799348075 799348079
    0x110f071a160c03051908040201020111040f1a1603030e160b12070e060d0e01111e03072f0d02060c16051501180c0212030721021b060a060609060f020106 67
    0x40d03003000020100c010368036122147c2c40d0a1000a080d1240320b501c83c1d203855014002000014800c40d1500c05465603031038030399250511030302248070900840c07001040f001c4d071102a5405040d050b0b448420546490425104400e000307103165401d9001c41e21070000080010032040e1511283c040d522900f103d0145414561400407800040b250307040011491101581e480d080603c044091007611076040c00100501e003003030608100c010488046036850300c2281d60000024031054400c00c40c003603622100c2d403a00181d2401c2c80c002108035a1a0f600014583d101c1c8020101c0d6072070000a01714495800700c2401842e183c4c1e044807410381010308600896091040d1801d021090501402d024081c010142280a070383c0402c00f01d00b01528168000320055412440044241c030703008904481e0311604c64200f19204048002d1201d120480824a680203240b02088071183c3d54075105455002c0304c090411a0740c1d5031145041c1d001191250302c00c12012408241003007102d0390140b107240b05c4802481c000019515 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 799350575 1250 799349325 799349347
    0x1b0c06040302090a05061207091d192301020f220f1811030c1e03090a11010c14100c050f04060c03021903020610090e15060301110f071a160c0305 64
    0x24080e82010040b03e884140c54400c00082b18818583c50080f40000e04441c01c10840c07429010342d4042000d0305010205501d0596881c004882c46110203200c1c000b10340d1106480c0c0c031400385820514034446040c1b52249815032202400038005c06030395502413009504c615108000800c103551004103240a619900700e020907a1525001e5032289841d0700c2665a1404919003d03411010f5804c58006404014410b1280640d4001002d1400503802100000490640300c0162554241010b00400e40c0b04070442255120718041034041d031602840505001010058000742c0700e038000c1c03002c1407200480c103002c2003210324030071040040141d0003801a81d408032641e650080e0011040d103400c0e40540c5c000340c288005080d40c020503400600c140070381048800780c00030041d80c482a02800582c0140da18602080d40c6541c01e521032103002c401c0c0c2c0c00f0385a0796221840300e4200b5811046050703411940d407034084802c407801c1d40201445524420040d16182a18400940e404240401c054007086800d125240c2c0312 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 799351825 1250 799350575 799350583
    0x1209150a270c0f1203080604050709120614012702160c03050c090c0c0d0c02031606031512080720100c1202160b071401021b0c06040302090a050612 65
    0x101d028103a4039400a0815070a2484002d0381c4e88001582004508940f011030380c040d2080b5001481110041041d8a40e240c0842c0e401a4640200c06c481d1480e00c4040c0821031654000f9a210f51121481800d6a0380c64000001c20801d04a610403a101880d00c417100c0006550300820481881c0c0003444810b402c02d41355243c07042c5a0f90400c5541e1303480b41c504601c091030b1101c001d5902280e00c0b003041e0b18040818080c1c41c0c5039184501e04c2d4083c016459203800840d601071061074900034181e41e0044240f580c2d030350014042c01403144800c81031402000f0100f00d20190354503002d001508491114a060481d80d240c1c84c90504901060f11446002e20031a05595241c2c0c9a100c0419420b641d1400f1b04a16030400520110354841082d0a40d030010b16039688002e0400304100440b041d4411f2591111091f0500304c40c02c20201100130701c0e5502c0002e02c20850241030050f0b41040c040c038411203850488071401c2c401d19104500010b54440300d100001280c00809800c002d501040240c40c00f62030f000f03c41c21703041c60 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 799353075 1250 799351825 799351901
    0x30a060e070c0506010e0c0403021905042c1501150513031202150610030b01020a120801060f181202010e040f0203011d1003060504020d0b010b1209150a 67
    0xd2960a9402e0a00a00300a03c6025144c83c0301c5140392400e085405418520440c48024040c000396108965410400300c0260b004200c094400e1120000e85c0c1c449841040c02c0040a500b603042442d801000003100040400e040c144204907141c1903420220315003100003060b5513000c2045000c002420001000c12081001507104040c2c010040c0d122070740c06814000002496050654503030b0801000303595100781d4140400c12414001503003104200107e040501262014000065503400f1002040d40940501d040301d80c56030fa4030341d1020b8000400c4131101c2c05001c02040d480c00251080c82a00481041000c00d00c0c03050402c5000c441c0c000000c00c040e030300c9641654000d580c1c084010003124203060b091409a92411002000c0c40c504051040703860b03003807400040c003801e540d00005000c5459024850321200e4006a0100c0d09681d502c11114807a44146a00d501418a1f032020612411002500310311035004141d04805c9951160054001402240011484000d14606400e0324850413190951 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 799354325 1250 799353075 799353077
    0xc060f03180724051608030a0609020f0d061d150d0b0a060603050903090306130f0b180d2c01031506020708010606020c0102031c02070b190606110d05030a060e07 71
    0x103a00742d0482c0c02074248000340188009200c4c1c20040d17111003054140207044c21941c003080d01501c0f5220001711500811894101188542c0b00103844100070209501074101107040d11030a00c0555113452041d44a4a60500350340328ad04200000f0461407141914101c00d8118048c00d512201c582a854101b11a034003a143c17042000e40d507a900f80701c0181e160040300e5021420304019031400000a000c030785d542500a00d02c440810441e00b408040101002c000c3c00c041c0e800100c2c01d101401c0442040c140e500207d00f07840558814036818820a50140c003808180040e20405541143c041c0300480103a005505100c80c10107a42e804c1c2e90b40110b4400440d1009071416600420391541002c2c01c290840302d65422580c2598044c080310b8206a13800412a092003001c1b0703424180460341c2c40d4004c8007a00425500074a8800d50000f04480e00040c0b591444a086a4003010310096030b4800042d02c04100c51010018607401c90244964954018001036400211505000544a903102c0740141d0340441590100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 799355575 1250 799354325 799354349
    0x1e0206030c0d050c0f040303200d0807081e0105010e03010e0709090b0117060615040f09141b0a110a05011406010206090304081b0415060816020c060f031807 69
    0xa040b941c11445400c1e0300901819180c0e1610304940800100740c09184401001c000d000f2500c0c403403174001890854007007240001103507030b00c2501c140054090303d01125078400103007113100041c0c4089020030084081d800214003441f010703400c25004583c05d43d103034002a5019034980000ea252898100b140030000d150120700010303402d049142240b11080113a02004480341502c0061043d81c40c04503c0c0f030b4015108441c201032091400c0d50b482c50700d00a692000d21502199000085d0900e09a0400d20960009142002d03940d0340e0300123594010300e0405000c5040c6403090150a550902486500c2d803d41500d000b1035040d540e0683c2c9180c00e59046480000750782582405120803544c041000c150490201d40165040c42d05040401ea078600c00c100c402050003100f4110240a9200c6601905040030000e0305001850345891014198603015114110040341c0700c03c0c2c0300701030361011411300300560008060340d1030008a52130f140d460f03800107030101a00c2015101c400030030440411006004003441c814403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 799356825 1250 799355575 799355587
    0x207020d111003050903092806030507080106181814090304063506010309080a0905030c060403031d060c0312150904111912210c020d1e0206030c 64
    0x200820751030350030b4804280b5040c2420700c80c10002c048180c0d442c5c00c10685441d140c0c40314410311109298081c401c0004008140d00d004140309500d40c10803441040940c680540c2666502070440e6202c0c003200805022030203a00c010b00c50103000d20101000d17581c9086010821003040ca404440c154001e44d04440240d00004040185941028005036044818102d594040d021000c4c2c034640c0103614095500349540d2030f000240507a020b0751000b075115400c08983c0340c8600060078060159000c07030140500c20f1182c2420103401d403916204580689a0607a2065150b14081300d01400c42041d203126903501c050141705c01e5009400800252850700041010740c3c116051525140c40c40b150b044040502a108610070440440c0703038001e406808003429a50501130400309401d8403000b074215006015120002520f8105000003840c1043c0351000c0183c10b44070080d581c2e06c1c1504d0418482c0320084d004000f0303c40b214003003040b44004804286403d185d4444040f01c95001400d07550080b40c107481c01400101d21 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 799358075 1250 799356825 799356829
    0x15061b1f0203190e1501120314180607060204120b040b01050301090b06060d1d0a05070f0608130512030406050f070801140d020a050a0f1502010c0c080903010207020d11 74
    0x114002401454011441e60600e030030f0032000e07aa404544584030940380e00c0d1001e01d0440030170072003030310b6002c000d44880075507180d004000d21260030360010380000340303200441d0124900d481d0417180e00f0a01c0d580b0803001e0b4640c0d042403182c681c001c400c5c00d0b40c04039070034800090200707940039403000c1692045108200d00e240c149450288510183c205d42d00980c507007400c00000407080615250800001c9071510340301c80c0c1d280000c801805600490f58400307246119061506607001910101c400c1c840d03000d0395180fa80310b1a00b0042e20346544030301030001d003428001c1503035510401c1008003154090380030f481c0500304e044400001544182c40494001c0d40d6034040060001e019440e42d508800d403890040319035403402c1d1030b1807c818540201c40d4030400350550b8000841d0b484580e200010040541006540c030fa5035424210090003920500604050414946920500c10300c10400b050032242c6440e41d01c0300c40e40d21400250b03001040350759095942080b0745c101580e10030104020f024070071408d00c210004c0344e2007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 799359325 1250 799358075 799358113
    0x150a110c1c0810080c0d1e08032715060a03050105070f0906080415020306061e03060307290a1709010c0318020913020109030f060902100807050315061b 67
    0x1141d101c0d201c544014410050081741030f0b000103004460340140c040c0d180c00d00004a42d00407106880020407019007504100c040b04c0610310608266041101d00c40c0440002611a800440300c50001d03080742120051180344842c03c0c50304150090320003105241c50382c0d03403036084400039038508000ca03091300c0d50071908030750201e07464018006a207052405030505942d406e03d50700d5040c5000c40c800760040001401512060180ca4911181d02c2d0810909034040000040b96071060704e5240c0240215640450100419000c03000e45507030b14018000030381c40d03034014026030740c02c910b03010420014000d07044c00b004160007503854050320403480000382421103a0130150482c1c80f4106603c51a01d640c40d000000f583e2080c81c1e60381c8c4120007510710f940d1900c00c0e20040301c102005400041071048150a80c07014403000340d220049452090314a032400040c144002e45041104a6005000603c04c20001e0441d807510403a41008080107441c40e4206409107007881410780c0c80c0c80000945038400c05601540d40c900c21 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 799360575 1250 799359325 799359331
    0x3070813080601050619030c0318060f1103070f0c05010b1e0103051005030d11160e0115050301051309060b12030d060f030c0506070507030c230102150a110c1c08 71
    0x180c01501d001400d000306d103500c0e078090700128180b5030f0381c0d600d84403800e001e81c1041c01760f950044560490110303245850303c001c02e44d26002c0d58080307280820403201281c44030101d9024030643d889140d0b410305841e00c11103241c101030604070792654031120142a41d40701c5901d8500c1d690321103001000d40da850b0000050803070304002e1008020f440450420030091b180820b211034410010b1816603081070408943e6071138087c480d003120401400e450390000c1c1121503111000d040c3c43d802a00901c0000e42507000312454002070140a6100d81c40501140800308a0742c0601c0c51240b04510200d2580350110028141c0c154003000100a40c00001703c4150a040314469040600f039060580c07510b66040d07407203802c0700110600455002d05000190103040c08801c0081800869210584030200c0c0d4a4070581e003171010031030f000a5081d041172180401250300120b186d0020b07100341d89a0b15003d0391442010805000d8208020341c80403810400c440d0821824004042e080780100329076002400c90850040c02e1800007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 799361825 1250 799360575 799360579
    0x224040e190902150a09031208041208010b0d0e010e070b0901090e0417070314041806080307030c150b04110301171204030b070e03010c0906140f030609090307081308060105 76
    0x80350040e07006a0360100c0c50300000e810000c42d592241100d81c806c1d40c1804032900003514854a04000402c456400712038980f20790b20a84440300c0039113811000b41d903034841c20b00820a46860a01019005042c1035010012018402c8001700301d20040e821250306106407900440e069a6000841e0121941c0143c4510010011601c588500b441d054035091103c91010b10b004092a9001590000380b40c4030300c10310b0066141c0e034503c0355921941c0301801d91840610b580704400302030400c10001510740f008000d45140a0b01901d8034000400540da46d480e00304044480c51201603956400c061407500c451060282c856500401e043c2e880d41050a490b020b5107030584004030b11350101011074200c03049001510101c990180740c0130707030940382e581e0300f036560000c040143d0b9015071a02c0c1c8200501648280940308844c2e03903440d4805d013031030758074074140ea030f8847c0c0c2c0c1d00c81c1060541007010031140d05142e110181d12414180c1503a060000e19611501c0340c0e0300c41001e40c84010307614202032080760420b12200e03006101c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 799363075 1250 799361825 799361831
    0x212010e0c0c06010302210d0e03150606030601141c052a0d02130314011401050a0f0e100f0f180213060e180702012013030224040e19 59
    0x420007071190f6803001400001e001e41c00039131291041102200002c3d850f11017540a440c1c40030b1505400920745540000c2e007074420701c1042c00b1034074100c002c242814020b0790040d00075881d40c1da5030001501c1802e00044200917008040104008101c3c081e03468190302c20701047c011030181800f03144035228201c1074507203202d184283c0c40e0701085c4651040031181081601c100158581000c403c412200022a9001038440c048650316413080c1c440651010005d0302c0d59085003660745c3d032580c051098211440c019090600154030051001d82400c10105600049880c1c40305055074072044240d8001000b64488505c400140c1e0040c450884180007003130612003019030441c21700c2c19044060085100707070f110b07890600c0f0b0a0408080c2503100d000d501004030380194818486400e01e040028001c10986403003046604202c0c845410f206005d4084802d03500c00d618544080c41d055400f044009400d00c000615180c6c1e00e807603610101000c80300a00010035020312040401d02e0140f0001001590135180c181069103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 799364325 1250 799363075 799363087
    0x20f040506090402220f0e060f09101515020c030f010c0804060b01020a05011104141c1211100c0306050d050d11031b0c0307050607030504150e040212010e0c 69
    0x5560607000e0380660100c1c0c0d8002003511000791085407400d200c1e1039410660030192001101c0c6d166401055440e01c2c07041c11100076a58509044507044000d440681076130b00000d02d9000b020b080d0350070002070324508500c0c0304101da03a03841c2d6088a45010005d0900541c10040704981c4619013801130407070b00c01c4410028400300c007000038003c1c0b62003802880200059500d41058220364801c00400304003d0340103008200740c03941c0c041c0c464044d4000d8450042d184540c441c42c610141010306100c0d09100c2c024201b0600c00c0e45558aa14443e080d55211504002c205159285e41000c1000555400721306c00d90001070030540020003c05070380107a00b107680034802d81d0500c100010b4000450307007910960340c50812501c011400001e4150f00c81c0c02d1882501d140100441d0304140400310380b40300c002c08100c1c1194a0503580e801400001e0280c00b00c003502181c8148010481c17180e602502c003004090904d014058080b0800000381240c0101a1150b005a954401480100c1d11110f0507500080510030040c1804 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 799365575 1250 799364325 799364329
    0x9060503090703080a110318030706090608160309230c040603080a0c17040305060f01050d030c0b0907050d0605070f021c050f12161e090303080601020f030d09020f040506 75
    0x582d888000c00c4240001041d801c04d5210b0010341000d0200e002c1641d50f0790340603507501648041a402140d20034000c0d0100007a055002d2203440701200c030715803200d031a50340d14800401c3c0c040a89104160600d9294600c86000a00c049112035035002400c030f034034010184084400349041c16020003140110b19000e010b0003c9240001910550a154604036448042e249012180c0e5190307c50741d1a03c1a0b00450040b082010128038944100b8040703401180b184c3c0c1e91410000710005442c009004900c0700d403000742c040748400d01c6d00da03030000c00407040740c0c1c030309642d6408100c02e401504001c2e520f4039540c10900000c541e01c0f034904200c009541c8028040ca218100c1502e08220030208000103200000500300703001d49225050320f140c4050010340d11610325000403581d4210700b01211010005111292001421403504240218480c4540d0307980c11850445d5829200120003034a0641580708006036a80a081c04100a100b120119240070076060520f106100940c007407261603512983c200000c200c0c203a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 799366825 1250 799365575 799365583
    0x615090a051b0415030509030a090e090c0306040b060907020705220b060c0106031e1101080603010e0a11120a12080c0c0d0e0a09020c0607050d14040506070906050309 73
    0x805810304000426498406075119860720070401c4220480000c9400104480885003400400f4241c0e2011311182e41c64402032501c910030150f00d20081180a082407160400f4010240d60000800044038805940100007038600842203a0442e44400d0b483c0c200181070420140c4d03540c21001500092403c1400c240004103555400d286001c0c0c11907542002d880c00d00e20325002454090707000b501a42d5250380b4116400d000c0c180758007080c0d61084101042c2103a0740003030280c099031a0b8001c80d0004172078006400465040c00081c1c40a9419900e800b92049001d805100301c11901d44242450f0041e00e040f0400e024000d40950301b2010190031000d400000f081c080319480c4075200a91034190f800d9a61111140258042c0307003002d01007446208c0030030f00d107960002d98070f101940d400c98211144a0f92a40a0010380c4140c5180e41200e41010010842440c0513201911074400d610b4004101420b1b8201c40c880d030319104071001d603900d80c0800c043c45002c6030041c0c4058080c02c01460458614a000c014190752 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 799368075 1250 799366825 799366831
    0x15010c06050c130e0717130b0f0708060307032a051215060f09011509030c14030c0402090105541c0f1703090102070c0e070f0c0f02030d050309061509 66
    0x5601101c2c000450a46022082031605075210440c282300d814808600980c581003166078001040c044008101c09180014980c01100c0c4e00c40b416090b218100560400d0403150407004000c810250750003c100c41e03442e00f00301881280544000d00400102414007045400d016003418001c0700c40f240c5144840c0c070780e21170450550380341d8002407a11581c507000848804555a00142802103400000701d107c220068099442920490032610911803a00421007248580100e250115004000c1c543c0a94203016079002401c4158400b90089000030900110b162900040e60092401c080c0c070781504240d00032401c04002809650100c80c1140488c01610071000001010300150302c40a2007100704048041344a0307100541e007100c1e130303120300f4440b0b001030103500300d410122040c0062003408140d906d0449002da114010b2651681141e90041100b668511000e41d020f944002100d000e41025880c20004070300c80000302d5030389540c2e03803034401c0002c0e080c00c1018140d840340b14014400102a80e6580c0d100c150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 799369325 1250 799368075 799368107
    0x501030c0c1b0306110d140f010323010e0a05070b031513020d1406210322050303041d010b0c030a052d04180b060315010c06050c130e07 60
    0xb00428000b2110038406101d035000505803402d011030304051011200140c0b204082044003444180918007000d5540032017100c5280c000c202c500010404200070310300c40084507007051108098207407900b41305402c0d109007003008012640a8402002000410041030004040700d500b103505600304206908040c41c0d02c3c0d00c802e0711540400b04040349502c0f01d81d045070170060300403100300f00d18402102c2d00e000807072040340c40e24840c440c0e50081d10345081c2480c85e01031401e5060805189007240303510a10000c4248112070000d00d07820807034003040300c0d1010030060001e01290344000015400042e0300f2410305005822001389958107000640d000c540000580740040024203201d0340382e45c0703003038041031452044504000062a25000030341cec14105020080040c0d5140440c240e850040408001003554503070081c0a820000c20000118004414251500500c0b0145450310842c0e4042d2034103000d0f99001d484142002000041c2d036000710001091071001030003900604d000500d01260081e020038010f0f10010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 799370575 1250 799369325 799369343
    0x3041a0c0c1012052a03040b061504030512041a070809040209060909070905210601050d0203011d0706090f051008360708120a0302130b0d02130501030c0c 68
    0x19101e0203800c050700c43d001c444208200302d2400325031064a420f0419004007080f008864031198101d0004201c911507074021340e4200c0c080d02e4207070900071903000141288000380802e01001c070014406000582207040130303c80164071181070414602428140402144840404002c4600064192401c5d2040c2600455005840f1402030010616134414180c44640c40f0040c4000c100c100307a000064a0300b5a803003503420a04007100c6a0f407201b1022446442e00540e58440401041145404100b803d14103101a00108200c0080003400000c1001424a1882c60304018410300542f0340c03021118000740401d80092070410316142c0400c1c00740c0303002c0301c6000c104002940040c83d52100da002040d4a14040e042d540c8072902c0702c052048000080f000a000355025102000505003800141101070001102d4811314007654002d06400951003900031850000000b5000a1300c40054000761401c0414044c0c0940d403001c640c6649403803407219070041030505141910085202d60f00441030440389902c41c3c050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 799371825 1250 799370575 799370599
    0x8011419060f02010f0b0f0f0d0b0709080c0a0f060c0201021204080304052e0c030314100303020f3f070602040518010501020d27030503041a0c0c 64
    0x10500d00052a40c00c44111801084001016a801500d0446140071030380200030389958000750200795000c40e040039911080204441000e49403840d5001c421100041000125120503942ca1082d00011075030344004c50660002000300e9802409030032818141202c41d000034074144100c0c610f210140c0c1c00b0340b2007048410810030007164001c03c000021000e0920010351219594a0407607500c2d403003401224000d12945400c0c3c0440a4a00c142081d01c100e880c141540e0801c40300030449103100212800d034100b58844451105907010f8030007441c040c0b40d04100070044503085050207407070075400410200f00c582c443d40b2441c40150342a011980f51004150009030034205218214840d440f40d006401e83e40d100006004007003001e294010003c83d0b406441f07e030301d0000040c050509000c0c00f4489c035030150700214030464280344102000b56181d486844090002540584580082d2110360000c4030950b000150901942664501500c507915038041950310384000280200c0d10b480300e092246005403004250 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 799373075 1250 799371825 799371829
    0xc030816050d09141b03072c07080f0c0c0c010f090e0f07030b01090b0f03042d050c030115180e030a020c0108010e040308040f05100212060a0b030106080114 69
    0x12a1000420060b0a101d000d0a41c18503e41c2c84001180c400d16522810f40040c051710011032049548110080203841e000d0716250310344890360300e1045042d070300780c0d01d22042480c84440424124010f070419910b0200915104604e60000c0101070a18014070b00e040c04a400d200e480092102c82c03008003841c040159081e5240f0a44070035489811a0604011013002c01450045a00d071700380c0700d07262607601840303440d5a9074015219001c6a0045804c1d1130810008616081001401141c01c64854002c01c00004444004200303131088000b03d81003d02c41481348402031103020080f00070388a100b10003c002c3d040c002607401e50200a036124089848592044135000401c0543c01410b4100d850740607240d441c00900d40080d19005119001c0d404100424004203000d074030848030602c40d951584030052191969111007840840c14081120640f0850481c40840030840c0050101d403c505040f010560401108000ca0a040c1c2d800941c1d400c40300b07000402c009603026010f1411190984480c051f0907000c100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 799374325 1250 799373075 799373077
    0x19030204051e010e1008100605030403082406160605091209010e030c04061e06021204031e05071202091b03040b04110a0b030403121b05090109030b0412020d0c03081605 74
    0x800746030700407105811400c15940101c011761041c03122030003051500c0d0311410300b40d80c3c032b000a40e40900020b1b04400005c0462003412503804581742c52802d02c3c1640f250740c1000414036807100103d203e4900008136071104201c014022581c00c000c014001e071031030030700114206d0143e0040314211410860002014681614140508007030160007030014403000d03484034400b100c1030030009025940e2602086d80081c0541c40170404010300f801c0c069a4618061a41d1101007a6182c0c82000e00c9501c8503002d80540080e008006000003040302c0500a85111054010444590300003012030000b94092a40034295401d1101140d902ca903100064110a840b80c1c206100c4017065078400ba80c01003484e0b8804540e14181902562041d8841e0f82c42c0130400d2110286e44090b52900c2e890002d45929409824551a000d0409030408900600d4501145662600c42440c0040e090b1010f03540000c1c1842074000f100c1c0d0602c042c80c54906181010811607156540080c14008010192480c441d865102d640d0000d100d10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 799375575 1250 799374325 799374347
    0x81b060706090b011e03031b150e06090f0a020a060c080d0203090c0a0602010e0d03020d2a030c05130b0a09050303070b0a061202061206040e100219030204051e01 71
    0x28810492410b8500d042c800c4100280680c007a50503034052081d0444420003402d03020380340d15a88029251408442c600303e4504003407011188140041155900c00300e01d4410b00c609441c0c1c80740104658184006941d0918800c90031350507032031f0040507200000d6210b810b000d408407805490000907500850508c0c0750365000b804a034684c01c1d070002092190100c4005019603842030201d0390507000340c1e41c03210242e080342e000d200c2001460300010310b04c580050003a0b024241e200660240810b00307084000b4580c0e0070510500300c0704820094414070181041d81840383c41c405003103d0800360318007552020480261400b911a03501441000030750300a00300d00c5182d10000424014085a8442102e071514041e082c07411a81450711601d803100006400d410f004e940d4142c150054121498044603080e44042820020106a0440d840d002d018003003110802c9000d0400040c20382c01a12228580f401b1102e042d404081001090300502c414445035440038400c02e00f0224036040e05112141c1301005881d045425 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 799376825 1250 799375575 799375583
    0x110f0d09050607031e0b0d0210020708010603030c1a0c031503100501090b1e01320c0a05100504020618010c0606080a11040207030e0d03020f0a080d0c09081b0607 71
    0x45050281d0710360150008860045074106880940124440305c004a036484500c260b4000c034445807590160030802d8061540748c0080c81900c424a0721441e942d400c1d202607a0003180082c40c2100c401061203403151140e00211515083c0c103200d41003103140d076030250001806d07508107200b6400d14014150b1302002006000c00740c2800601403507940b808840014240540c105024101420b04101c0000c03540a04e030320009416100ca4035440580b9004103000140041149106162100151440e8100c40301804140b407a9400504000305545050340c10400c031149042950390512081c4001650356030141d031a00742c4801000b40d011321a83c00120b410410261000c0c1042e841c2c03480228510038049040360207140200d04c540600310840084c00101d00c185240176000410000b05a4400c0c41c2c601c890b50842802841100d0282e00703580809414024450805c5a12140028440c00c00802034040c2d945600e4103410510519031070a10300d0790329884c00e14203004081041074840742c0140d070f070b402c10b450000d500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 799378075 1250 799376825 799376833
    0x3161b061802010216030503160203030f07121b03020a1401140414121e030402030a120206040201172a2503170c0703080a14042301110f0d0905 63
    0x229088610001c0c00072a060340180034a07852a04242c00c55a942012682c0c083c000314a090440744c041c0c0e2a901c99020f041340d160108000e40000034403000c2c0a04080c42c0105c8002c3d0a0030710062004d45251800803c00c0408103848001d140441e4010400352043e9030800e90002001e4010b140c102d00410385140f4400404e0070080030300c42800030111000122014400c12a10920181d001840090003800b110030100d080401100007000b5094020f140c0003480a0100e0310000819541d040030440041d5403100164403070800c02c0300307541e4400d802104140054026503402d040c507100c000c140182c104041146807081640318401e260f410030441e105003400c035030458500202c0240901241090200540005108050015540146214060243c0f50000905150804a54068a0924008281c1001990380b850054500001d910704203105a200d000102c440c61b698407030080b440c01440c0c41146040e031512403401030310500e000803901c00d50340450000b6255030760308140202400d8a19001025800303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 799379325 1250 799378075 799378091
    0x1802040507020d03050108010b06090f120a0b0402100e0d02040c0917101d150702010f0e010c03050c191409150c060615071118150108060603161b06 65
    0x350200e40c1200c0728007a59003d000c1d036661000e01c0c7d42a1a40011444c0d801a004c10000c84c2030303c0d1000031500d0004001e06001f800d690a10b140340c0c20002c400106a84000d0144108411032810a1842c0922805030802800b8803080c1004034030314220541c402800341e980c44842c000740c0e030700903840300d0014102c66680d00f00d40520080000c1c2c6608403005803408050a005000c0ba5111007080181c0d0100c0081c00148116840c081d51400700f041d002c0c000340155541c0d103003003401000a5000c0c28100120010010a40301c81c0c00d50000c08413003008100000401c000d0107800d109802c42a280783d5940716a1502480d03103070440f105515a4480e041070b1992141c11040280012605007018094030904c100030b4640310340c0c803030040c131030001319007850405524020040703c40081ca00d02061040340c000504a000c41c542112a0340d0210b10003074070301d490f854003e180000140d680c845c1540358400401e448181c210309200940c07850810085001d8804c0c0881403842949242c14288070711325498208100707001d012 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 799380575 1250 799379325 799379327
    0xe073309210c061209020406231503160302160309140109180207170c0105040203060708070f0f260a0c09050d081c230903070b0a0c0e1f090f06050d1802040507 70
    0x841d0327600400e0304542005034809507454816030a291392a0380c06000e41c51907481c8041c10400f4010320141506265091081009004818102100441c03003611230402d83d0381041c03200740441c2c0c50704003224104902c01409000c0818070030031041001d40101009a140d9426161145201200b800403164450010a04400701a0150050b6020f1030090f010b03900192100c20301201c580d4011900034010070740c14580710044520401c2e0027220001a85428038210003420844046d11404040000603c1040024040c414007240f180e0b29620480e42030400c0894541004608c5846c9100d40150180c0e030041662247c4d085541ca00b0013590304581410014500003c01003a8406540719104000f800703540001401208000101c0d204181c02c55040b0903a075458009850150132039105500403c4a282a0a60180c450f41100031640d040f520200c5614008600c0003080241d00c2e030300112441102040401c02960840100c6000da070304001c010030f056210421411142080c8180290020b04c5d00081103402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 799381825 1250 799380575 799380599
    0x30f2a0209060607080304030c03030608030d051909170c0c060309010c03051e040b1b04090e0f2b090f0605090f0102010e073309210c061209020406 65
    0x2440c82290030108544a50051207001d000340301004101d11000c001040102e03001c0c02500100e03501c60703d00811825181c00800d41560000100d009100d501e078000e006070000503000000c45400703036610820081e603103a1600341d000486100c90709040900065a502e0b600c8042c080d1403855980030b081d0360b9407410b12010a60082050f26820340c001303031601001c03d129640b0446082c8100d586c649802d1401e48654840940300d00018049200080e40c1022459440000c40d015000910711040c00160075403900c0035040c10300850202051094010940300c514160100c0c4a0001404403010014807a40120704103031440306c1d20350890040f2100341400090610340c00b400822000f4400d0710300100c00c441500059080c2c0c0c10340741d01e40384541c11440d003e0207104040f039661620440c0551358800c2c522507a200441c0e000764120042c03400106040340901400500003d0284600c40c0200c6031080303d07466444000d00540300d07002c1e41040103110b042a090800f0b00e500300421060f0020020002250b43c0d000ca0501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 799383075 1250 799381825 799381907
    0x13030302070b03151905041803090e0103020603160e0303121f141509040608010e0601080615040b040f0e0c0a0b03090c060f0d0e0a02131503030f 64
    0x51040c1000403070b0040d11203083e07030f020303001512021450b0000681040084c50084108400300414400002440d41c3d03039000703108010030207041c01400c690440c20010708007d010381003110f214091030300410040c1c8440c02100e0307010303103180c2c003c0301030702c036107203000c8500c007020b0300d81203506110102e514a40c0d20201400c2501a85400301034207040c00c81c06488501414092140082c0403c620480206900b07000e114014041b01c80040c1900d480f21b9000020121a003580000e410b607991031244500c1060104407441c00340654000808007460a049a611035891002019001da525081064010f4860b40c0054550203151a000d01036074032122005c643d00c03503d000b1001e00c1040e007094005208280c810850340100e917800040c002c0500000140900c0d5803200000c980e0340c501c200b0030600502e07103d100b007011601403030024090300c003240d0040011703a100000f540d901c090321f428500d580c1c41d00001c41c2e40c1d08030b03075050030040380703d981801007540c080e0b80a001e000072114040030102d56401440001240c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 799384325 1250 799383075 799383077
    0x3060203070f0e030a11130e0c0406171c050d0507080603100b09160c080a02150c0c0d0f120c0503100b04030209041b090c050c07080c010c2006130303 66
    0x8558140b904100e611403651000d0941607042215400c1c0031910f503406281a00d40094042603408005401c21012a85030719085032003500816210b0801f8a4203010703c1c00101a02110040c20501d040e0145031201c1c0300e107400500c41000f510307583c0b58480c0a10141d40008144090800091a02d42d0014201c08421114240310b401140084a5440c4a6210359040703814090510416641e80c0040c100001850804032001d105039120030200254014000f4200070003183d02400325405098119a880007003c1c0084060140600c06002e1038072001820303c140b0641c40c50f048141522981d402d440188034044050740c0075003010303a00703e056500040218000c403903450070f0130348069a55512701505d02550000039407241d00c500208001c100d1a5400140010040007060840b40d9076460740401c0300e407c0302c2c0c864003080010600c5460b2403020320440c4001d2028402414000c180340b00001d2002c105048000d011303c0b202d840341200004080d010035201c40000e0071407540c92284034801400f41060744002c81c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 799385575 1250 799384325 799384337
    0x40b031303171e091c030b030102040f170c0f0603040803130c170f010204350303270d020d050a020102130e0108100209130207020303070c0b190206090d0f090e010306020307 76
    0x64441d0100042ca00349941601c64170304402d07a000d14040340900380401ca0158103640030f10010075003804003040b11001700814601030f4810ac0110104600f070108140b14244500d030349042094068454404a03640036500c507070b8480c1d03255a0b41d0b105000c02004050003074952880d1000c0810a43c1180c0412000c454048045a0b24600c41d542402d0a0f03228a010f032210080c000301070031000d04860300e40e407a281030070b9440045840c1d085815071869034008580e020510404d000080031104074140c40050700d16a01d01c05001400d42d00400030755100c1a02c211207041040000310049170038802e40c151100e14885040145000307541d100703080c1c0000020300804469000d1500440ea8203003040c401c131a20808060668022002d060102c00b000b90000700302030307070940020401c25000503901d03400300d405030070a20b400c5600d074a4040f44040c09107100c1a440411f541c840c0b0180802e01400107110400c40c8030318a001301c2c02c19120901154404c10369440a110600480c0c00807081000c50340140d1b10600650f6100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 799386825 1250 799385575 799385581
    0x50c030a0e16030b04030c0510020a0f0302120c032212021212060d060e030c0105040c151b08071e1a16120209130609060506040b031303171e 62
    0x60394403400e88807491441c0d06280b460400004051000b0613520a000f0b0a06400340c41c510303140c290400c94400d0000429940c0040c5400c04107800c4120142808070030700c2c0460601405680c40060554084c08424110f0030200000b4200401c100035082e00002000003101c0466180c034020740e081c205001e24102501883d503488903000352000a403411049196040c0d000e6861711014011211100d06050342c4030340d101c201007014200100024a001e9241e0301c0001554600303402e00e40d030042d0b640e0b0010654100ea030404030800315844081c1d0001d44c5803c1920951800c07144c40e2900d12440f849800810240358052601443d001708425a81264000c0070740c03000342c00d1240141140014212803003103003440110740e050481c43c860894080098161036005190030402800180d4103015158082c0501c6d458510500188a5038041c14005000590b1900d0400d0f007014803030882c81c040204941403412030f0300c45410030b00d4403480d1401c9822011000941540c00d0054418800f201034050341d600b4078401c5004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 799388075 1250 799386825 799386851
    0x190e01020c0d1107120f0c1202030c06030c120c04120302070f091808030a2a09090e061b07020a090f05100503030a0c02040b100f020d020d02030a1b06050c030a 70
    0x1c8042d9101d46400076041d402d04080c031817a840071760b00c00280d48a440c101000e40020740c1002140d00500254400e20040e107401d441014136114074a10114004c2c1c030140b003400401c0b52f0b0340c002d480d4030701a401c0c88035083e542d83c0034000b1003c0c00341d030740842c40605201c2c49040616401082c100300795142181201c00c0c20751a000d6440a9030b80401840c031090201e0f804110215075000041c640203004400040391269040c00030152000c09440d000c5160010b032490404801e402c415100010552200240076200301c1c410f44036102c0e80018000b144030b1003a03641c1c050b2050068021203040c60341c001c1046203900d0b00c03007039540003d00b5403050780350031286004085891038500c13519810446400900031031030500d061a003250a40d011000807030300a902c40780400c1c1c03103070707105003078071b4102801c55840c1e4580100d44107000b4038000f4130300820b9056400491001a425a0200c01c450303101459080842c90341c01c00d42c0344104c000900100c054070541c40c107030500001c11042e100450043c03120100034810342c040121 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 799389325 1250 799388075 799388087
    0x2041103010807170a0b2701020415030e3a03060f0b1303030e0a0302041d0d08041101081b0c1c17130311030304120320070605190e01020c0d 62
    0x501030181c1d40019005000141802c0b000360744024050f0301d40b04c100c021622800e1f5001001d110554803030750045030900c40003070040c001c0510903005e03103414080400c2030b82000e501c030081d440c41c0660f240c50220304280340400485c00d0072641015540040858050310100070700410884c0600000c4460828001502007102d4040c0c402218500042c0020b5501d03660b400c2c0c038140d05060206401416000c80000980ea0b10f08c1800081001a00c00f0031401102c40d440714104000c84284906011864041c03001142c40c003c0400c2d07000c030b001c0c05c1c034140c69100c015910a4960f801d03460a01e0715000000c04850054006c642c50108441c41d0800c022402c0304424203031400b0703a0488080c18a039a117540040c2d10b01d000700e0b100250150080c1080d01764881540c80207415680b04450a0321002030302503030030041f141d05114511151040086246045014842e020414460728034040d00c01d60320350b40429066412211407000300d985110041041400d1403d4060203504042c5407845036001e41c080312810705005803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 799390575 1250 799389325 799389359
    0x20906012c091b221a031008010203012306071709100f020d0507140303070507050601230d03030e060a060906050a0302030c1201060b030f04061820030a02041103010807 74
    0x100d031032401c105030000090441240305203d00304969210700c0000f401503a03031034000314040300050035698900e409021f01d40e611815520070702a580c410401001003400400a0b035840007500c01c0c44040481d6160002a11800b40000c00b5115418550106d0703e01045003009010142e42983d0050405100391030985414000384030313070400360700318444181c0e541d845100180080e0f4171801440d5503052105a80503c2d680085501c68080303040081c0381d80600404001d0780d03005003c4003100a04400d800d44a146d0502041c41c9254010081c6814040802d030098101c20b030074613401400c07144141b814101d5031740645414841e074950246000004112410220754074010749801400800d50b008900c024003544d00910307503d00c02e1035581e40c4004650117a01710001c1d030150354501044602d40c2040d0404100b10f4042070020200b80c401c400f21100010954144402d1240b44c3c1c0eaa01c290508044c00440d0070500e240030000c1d4064170781121560211049000395041e40d030984100c5010542b104a01c021907003901d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 799391825 1250 799390575 799390621
    0x2190504050319110f030a050f0102030730050405150a0203070e0306101e09020310030b010510080406020c1509010e070515180607050f0f190f020906012c09 69
    0x101030413081400c040602d640880c03005000c5401c0041c19072102e03401c001e4800c400c851540d40010034800207580c0841a4480306441a5104070110b068007141c2c426020304207400220542c58400203010b002c070070f0042007211100019450031614005c45900c1c001e41c0101c0d21100802d1411a161040341400260a8441c124501308070408030300b00107076a0b00300740826000c0b2405080c0740342d0205401c0b059001450003400c03115584c070b40e0300d415445e12a40900701608018054070500108880303566001075035a4006c0e400c0840141d652030304848003824801005480c3c00741c804418140034680005601900b2000c11607415182c0702520fa40800124030590819541c0364002400b04089141e200d1070618404600103003e11301e0300507e5a03c3c20b00f8040020048000b03a042521034540300c10085c007440519914042410110403c0390340c4102d81000551006400340183d41d00282103079003d85d81c0c210b034420000c0c3c0300300c0d0034620310181c4101c1096031114050258a405010455810040041241484203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 799393075 1250 799391825 799391843
    0x50301031b051903170c1e0304081f05060a0605070809310b12100f0b0402040e041529220204080615090105011202190504050319 57
    0xa55100c20038a078203400100c0c50403105580340000c4a955a250040b40c034103010b00b40608030b51560401030980071034850004c00e021020041810b640300c02096402100750341948000e543c13140d080340031345140100c0c0c120750441c3c0b1402d0102c440078802c5c0246a0380c103050b40c900c140a0365891030240701c0e0700c0803188034450101c0d0303040c40030800281490303000d882402030260480343d501da6040185d65101140848038490b01c9668042c2c4c0390080c825024840c00309400381c80c8514201d818480550341e83c4e0803c0010703200b244c2e136080e007d0080b41d0182c00070320070954001c00c10b41d1101c1e07c41403000422030080e1021900a40c0d0091660407c100600a40756070010110150a801d0710311181c5600d40c4040808031580180e54855100b001c9801a201c51501042d4450060f29142007106007442c2030000f6102c3d0040c0c2d5031071452190b00742d46850406040d12421b2070102c1e00d412001c0c28400103402000c1d2803510750220208400816903000c00036004442d0101e046500c1500021094600200f00c2e210151907401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 799394325 1250 799393075 799393079
    0x4050f120c1612081b030a08071e1418030109082205010504050d020103092015040b0307180b12040b15030c060c0a060213050906030d0819140a090303050a0c050301 72
    0x30000190070250760017510701002181401c24617045a10402110012410090901960640c004058540301240d003411000d01c40c0199000361154002002301d500440b0300151144c658410b40307029003294140a0000d0051001524003188a60800007800012501c01e810649110984146c4081200e0041c0c464924040c108000d108514080a4007030781499200c280303c10000c1c81c50710004c52401040c01c1000300c5001003100700b0140460300d00c0340b081c0100c1b061205010041c001c5c000c07640c10100c4c40c100070030100400701c0c51500d40200b0f42d0164188130b1012500442600f69a1031443c880c900ca02071650f8150307030f2031098100e0300007040c1e29940c169010140c06001c0d0b0810000601000380c1d00f404491140c07a0681e2040306907031007030f002843c030f4056803807081065082c0306150b1070304808110701074240c0d03042c4150001c0904d0302c02840c5140c1e52030700200c0800c00704102d5200b0707a0049441441725032030303103882d44c0117078042c10000c40100c002918100008006501a100d00040a00280d60705d6240d64 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 799395575 1250 799394325 799394333
    0x1a030601183b2422020307090f0e01080106050603090d11030412050a050c01081909020a0306020703051324200106080a03122304050f120c1612 63
    0x21002c0400c1c1e05030881080081003000d4195070510841c1c00d02c0c180603030b4014046441e03408111194016000724855a0708807034191030821800200b102d004001a282d6807080001c640d000d5484d8003082040d44010808528120020741d1141a104460020320400c0e0340c0d203062014070710040b101c6540765000940910b540d80c0c0319185980801e03980d07808403800c10303803a140d0001d04051000030850f401c0d8843d01c0c0e20781c208803042c49a120502c0c2c003401c01075420310f8900e102d610a80140c4084c00c0c2c14681e190382810441d44c07074070003500265412000031500c0f21201e181c0500f15522290b07038030610030f1b01d4010000d407090200024007040c06990352807580508058609a40301c0c0c41c5103100c05810100c3c6904800040424480c4400a0441c14024401e101041c1006401041c4240e068000241010002d050004c1c040d4010300094802003144131132035845082c06c90402e0714040080100c0c0c0a40494280c4003c02e540c064100380016805441021074540394044c1880714902c640e00c0900c10603030010000c0303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 799396825 1250 799395575 799395629
    0x201050d060b0a0201091a0f010e07020a0506040c03060e060105060406050d110706061e1508091f150b030f01050120030f04030b1f031103071a03060118 67
    0x34090400001c900940ca0b405000181c2c0c011010520050f0341d80c50858080c022901c2c480704100401e02c1c2e0a00b001d0420400343c0b2040c0005000d0b00ca15070fa480800f00303034218420401c4c40b00654100b800d0b101c550403e803070024594110b40c802551320b94103140d04140c011502103030540c12201c004082526091415105907041c0c3c210b549400c01c680e030f0341c01c50b103544101c9450041100610030700000603501d0a01100c8810fa0651792007509001045490500890000c04032010061586040c126400c0d51039144091400030000e111004c1e0b80700e50f0311303521100c4800750000c10000e08003100c91a8080d4452a8020007404200d642007551140103004000c2035000324807444e62545c4200351003801c103031010342d9a451030384070714420b200c0d100303002608009001c182c03040183c001d00400200705109075080b8401c04020064080a080c0e0050b2487d200c1c070300d0340d08111000c0140540e01004804545910f41e07007225420494016000c039505440d01d403000e03000301e442c41007900d8003081c0b1740e80b2084840aa400700 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 799398075 1250 799396825 799396837
    0x71b0803040803040c082427160f030312090f08180a0b09010504030f0c03020a080d0e040902030604060c0905040c030b1c05120c2e1413020f0609040504051b090103080403020105 78
    0x10420007040e000d48110342180001c400c0d0141d00914003d13003010b5251800d003105904c010442c0ad00050103000080c4c1c003210780c06546d22580c40100b0000c6590400082d240002000202286030014601102c2283e5142e8801d9648007110b00013040e40d6102c82c031040030701c40c2c00c1e0708030b0000d00104018800a9605d5206402d094040c0c06003500342c94a03540801c00300040da400192942e40441003a055403540821071100b410010b0b107041c00301000c0c540c046a50f80b00c01030700c020031650f03d681003079444a200d2000030004110040051001000c4510043d000300881000d6034012103078041d442013500080000080001e50000c02001c4001e8202c60365040307604664030030302140c01001001550290740354800c915181c1044030050081001d04001c0b011202c20506103e80d18402c030082080d0b10501e00351100e001078041c0c0e400300e20a004400001c204c3d100e541c8101d0f03805403030b00c000d01c4144000080c400d220200f080d420b10020b02410010400303141c07003d100081908000300f00501c019441403029142c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 799399325 1250 799398075 799398091
    0x18010f171e03130b1624060603020901270b030403050d0912110f0d030c020f01330e010501030f020904050f0603071d071b0803040803040c0824 63
    0x1a40c1180d01e08020740e4048848a4425440400e56028120881c5240c0c070042010b039000c18a03007101d041207020220220440585101402980304104414031044520708405501c410031820391210400340080d0070904000b40001d08560b0305210310341d05121542c0460171042100841c03d8a01021480140d20040080f4204402805508517501050048481a603c6050311308080c2940d104020401408210081d10036840b03840450745015021400c0381d0400114580030584100c440003d910b04540c0c11a00c00c40b541c6080000b41c42d21200282d4040c5040c0041b00150001c40c2481480210190b40e000c0c0d51419281c040040106601950016017520010b090150400c420302c2e000504a03102101c2000030f400a0380208030103480d040c00b02a001e00f0001d542c0b16286aa00b84195085480c000e0cc1035051080a5801420031503962140c0000c050740803503015500c1c07404e450440860382094508462041d0400d4000c82c00203004640c2d24501112650241d0030b110304044420318034600a41460 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 799400575 1250 799399325 799399333
    0x180f0312051e0c161e020a1701110a02030315040605180105011b05060105060921030903011b0503040605100506040e06030c010c03020d0804210c0218010f17 69
    0xe004251809940d00c980c42c2d041507070031900c08481d14603514140080104140c1c0b00d0800080355207400c5405004d1304150810910300041103500c0c5540003441c80904080d61003002080c0004051010482d0030a4800d980310003808900e00c040f0600319107015680404016801c18400541000746003800407440290080c0080350072695100400d030015003e42042c4489804e040043c04103580004039014010200305403056080000e0300c4190710b50106000b00b40c821900000c0280042d911450140d501111100c0d050140c035008140b190341c2c5c0ea124030740c0725009500348500744510850710b9084030700c1d001c03098848914558840e5900c800525004000219600c3c588202240c41c0d02c40c603000c2c02c05040d40c801c010301c00341803d004161500d10420b00240c10001585139140c000b0342c2c0421a6051102e030b80c1888851500c5601e46000ca409003010341c4040c680d42402d1640a544c0e001e142541840c1c002d0318054910560306407840503841c000d00404018070b0a0b4034040000d0032444ca0401c0075400c514003a9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 799401825 1250 799400575 799400597
    0x9010e09120c03031f0b0d021e12150a0b03070318050d052205010c020d030201140708160201050907050d030c080d0501150207060e010f020a0209090706020f01180f03 73
    0x2a00e5000480e02c11a1644044108048000c500740243c0544c0b0368101400d80091400910362000d20070b01c80c1c44c440389900440d000380400704007a04444000790714081030307840d40d09000340303000e49003401c0341d00c0355071606000105c0b08903003006d03008481074403004100c030307407550381d62003c280c003d80040300010016403030041514010480500c41d8103003800c00350340c441da03036a20007400315141c981000100d2607000d1a906001c014a84e0001e4601041640c1501c00c0d03541c6084a04041c0c0c0103244100b90034448210240820003010b60021034144690f01043e4080704010300c402d0121300302d6030201c9905040f0b03800740400744594030b40f41c0804074886201786000003c02c1215900d840303880d00003100c080722280d1150014480e0454610b02c0c0107004101c1e2004040891500100500b034800350074a0b541800080c0b0806c10005109000041061b5006003004203c0d0901d600302c0303995284140300b0580107014401040a1148060041a14800c042014070320380c02d41d00d8a070110750034a010400ca041c401c2000038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 799403075 1250 799401825 799401853
    0x1060324090c030e010b1c03090b030702010f0507081303080a020c190618030914040f140708100f1a121003020f01050909040f150f0e070b070209010e09 67
    0x1060041d20a02402203504000d80c64060103440d40c29000101c02d0341410325100107500d402e000d9180c40c24074040e458030402118141035691480ca50002d0b0300100f8000201322040b6015003001c41d100140c8030041255589901c02211030342015106e44a060366500308240100b441144d50b40e42100c1c118130010310340b000c0c000e080380c43d04440165080c0d2101e8081e0140b02445014411103411002160b03142031040324a40e00180b00005a0144010320502210b8880c03442d21964007144008130091020402c5081c290462002c0b03201c202c03000e100040b40e80d800a02c0040320074200f82c0c00c0303460f4810010509030800f8042c07021482c10840c5418882e20038010304a04034000081035000708600c0d441643d01c1c0342140144143c40c42c02e0400385042c80303010002c105c00703900d0b006201d03030f8070940100e42a421013256180466072050a13040305003035141414035209031090194000320401100d07904403400d2940c0d442c488840e078021480065846900400100040c5104001d10707540603044400382c07400f031122401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 799404325 1250 799403075 799403141
    0x150703020f0a0e030c03060c03070c050a0204050411040506150a2618010f02040501080a0e0a05031b0c03010e060c03181204030b280b031e0109050601090c08010603 72
    0x7403500000f41442048100d907084c140040d82c14264150081c0205107049001c200081c800644810204a034030600582800018014000b100368020421b02541c1054105094082d0544c02c4040c8a54039104c00b150403440c000420741c080d0b4465000c0e050804000744401d951031407160b86850242e071107040d05000300b00d40328410381e88101c031420317081e10840440050084c2182c1103a1107030010b8038410401405a0381e004400540d2040c04c0f030300301146911078051001c1c180303500a6002025480082200d08c1c842101404031a20103020138101c41c41800340d001054281d0701d424412101c40e0304201d010031030384090540255032290303100e00d00e101c11100d00c0317800300d2901d240c403c000c50740b0075404541802048001c908a03500714070009684006141500021590203009682c0240c20550311600030003076460900820350080040a03040c4036800782031011a0190948035021212070040000109100080744104030303200c1c1c0c44ce62404c03030507801c0c580180e004001c42c50b1182038000c402e01c1e0a00c44410101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 799405575 1250 799404325 799404337
    0x10924090b04060606120e0606090903221d041208100308030f1e090d050a0e0301050a0209040501231903020301050a0e0f0708030316030608030c0a110a08150703020f 73
    0x18200003402c0e480d0100050094200103d411904d5041c07c00302401140c00240c1c5640115045a50440315207582c59101e15502c00c05182d0500384603280e4001c01e0380242c0d50040c0085801050110301552543c0901400485080300c4c003d00100601085401052282d102254042c2d5001d840748003045e2261a160260313001114041d0300303031985a042110340c40300400641824040301111041c0f0741030031001141c0380c074283c0c03020808100d00030071000001d500c034141300304008070064007c10660400a0a400280d809000c2503030080e8103200000a014201100004401c0041d45402400000a0f010003052501441114600580c000c0d40400560703421310580d80034a0b4403210000d00617100312441410410210301c2945560443c0c0000c10030740c0404030031240d101c1075880d4850361030000e82a094000b805c0c9a001443c1922000c1030b032510030b400014407940601d0089000c4070780d03a4088410070643d0780e540d020b07140603504185080c842400d2552000d5800039900e04001d41880c1c0200c0c0130711025001a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 799406825 1250 799405575 799405583
    0x160b090d020a080a0614130f0c1d0420060d1e1103060f010815060c121201060206060904020d030804020f1c140f19031205010906051002010924090b04 66
    0x2501c040003004060f01c036582d41c4070f001b0140f064541c60110f1824407222980d1001a1180c904001c00000304807003071000d81c01600c2090501c0d400c08113100c6540030107043c2110100c500303420001499103101140700e58410320500c010019407404030b0101541002c1c1ca4412041000d03023403040409000c001d0075000b1a20009041a00c240c4c603840d00c49d040056001010142a040c08039040c103004041440710080700f031101042c0c034841d55a052402c92030389040b41100e1003d044800c003160b0501441d00d401200350480f00d0700d50031144144c50349020808504000d441c025031200034194a14002405829566842800101010b64a003100808a489107112481c00103400c04000900c004021480c0c00b000d0b1003641102c000c103000004014900d5841c10420f0903080c000c0355082d402020144140807820006c035a0031007c1c0b0540d60746002c06009060980145031003400c000c4400703000c8070710503c00d020400b90883c242984214905201040ca9a08582246089511900007001003000c100d00c1c50300482c81 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 799408075 1250 799406825 799406833
    0x1b03061e1518091502030c030717010b0306040f021c02040f0f050d0215072906010206090d140c03070c050103051012150e01230702160b090d020a08 65
    0x34103100d000c22209018a000001c940070103041c03010408160003007a207120460070018501c101410121098a01c2c0410402128000010040700c2507509001d5809054151906041c098043d02158900d920034000c03c0440542400069010b1509401400100c80e50342401860101001d902d1400010806560901190002010001a03c0b6004000010001107100040b1241018002844080001000b074801e01b060082e81036043d240c40100c0325600da101507850610a181241012080d1b0a030018a40d0042036100043d501d500110b445403040b09018050320341c000031403200f81c5950f4040c021300006440140182d5404450410050010b140212002c01010b4500320004059803401010b076840d05207240700c1040800c005a03541014581e00006150381d0315441030702080109445030304c2000a40c217051100500800341c0054260455085411800c56070340c01000b032380d482d0b2a684101d1902c108044040100420b400c01418801c0c070021f03c622045411030300000c10b0241150441d90b07147d08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 799409325 1250 799408075 799408121
    0x922020a1509030b090c063a061a070f0b25030203010f09060501140f0f031315050606090d020a050405090709060602150705070c150509011409030a1b0306 68
    0x840b410781c1c00c2d480031710f01000707190044100000c117400740034216810320302c00b1310290400e5080684c200c134a05410900014510011009001c41c00a0902441510101c980584911042c444144210b40c2c403150000140d820303001e00d507651fa014002e0300034100f003050006d083e1903048810b02d0091109090341a944c0c090786a50408c4a49090441c00d43e1003a90420700c2c1003010402070743c0140d182d016503404812907070b071190f60400502c0c945110b22148488021400010080c00c0b160300403000c20030900403110000c81c0098a85124100da2042d109250704c1001442114818500b50806a0069202800e6100e0705540e030030202d4103403071044c1c405080d40d40040c801844454140e110310750040409100030000c0c1c4542160202c0481e801405210421500040d03140c240710b0001030510040c441c3c0070709422200c194140c000c107250080240640020000401c1540318100402514102e0100901500905c405540d40d2944907060a401441c0200c01c4000003002c2550351081019000f0391940740d060000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 799410575 1250 799409325 799409333
    0x80d08100602070b07210c11030606091b0c0316120e0612150d030f031a0901050f0d080a03150e04030801061107080709020403030e0922020a150903 65
    0x16001030024100080d0954100800360340000c0c007400300c8180c2d0340125a40c1c140b60409020701c210018112200c40f55041c501c026899101088000c40d50041c00c420700c41c0120081010749800c0d0654015501c010343c03a000c5084807100c00000f40c02a082e40301c0701e5280c00213000d8041d0840e0804040030701901003580c1c00c00140324004010394800440c07031a01c000003001f28800a91907008942d41c420032612141c1c00508480703040b0480da003420000504044088000d0b2900900f101d02c024030000000303041a0342e10724050741d05458458111002030000d0100d17070800c0240302c074a41c442848564070010044d09140030403e4400108000440c9503000300313500360600101107103030f42a54804240e80c42e0080030400460350010b483d6044d101a8076080d4100881c02d24a00c0c40c009082d0130103880f80c064404001201c0e1240e03401001200d200707031030301c100741352580c800c11540b038204071283c000d0003403890000945042d181d00c10401e41803000302401c035600c1c0c036410806810900382a081021410f0701a0510500c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 799411825 1250 799410575 799410587
    0x180b0c0c0108041e11031c0315210507050a0308070302011a0904030e120102041d0108030703080103030e15040b0a080c0a23041a03100605040f0b090f060301080d 71
    0x1440c00703080107440741c2441d03551022191007018a904514014500307410030040118025006031500404980b0b81d0410700f05141e0a00810051010120346881d84845c6148002c00c0d054003200c099840d101c0342801c0c807190800c07000c0003000003181e840c05501c1c0081025690203410340090b5006151140d100c007a0303444c000c0e08503601c288442c1c8040080d083d42c0703c01940c0e0310b054035500581c986403040c42c646640001c60044940340c0c11641d0306500210b80450440311031030f2450b0030a4003450600e4080d9903a044903030388a100fa00340c0a0f0004447d1801800442d026600c1a180400050540449a0600104164142c1207034002e80c8000500103207512589902500564100e003401c1041840c02110443c00ba094030343d00703545000580076940002000e034100c101a20020100c2000036a010301c201c0b40c105030030744d004841c6a081e10600c50780c0851514030500a4030241c941600f10070300490f080c800500e1150300030742d00099200c00c1d00600e40c80c85440d1540594000c04210008180d80c2c88198005090707 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 799413075 1250 799411825 799411843
    0xc06030e1b211c051908010b0912070e15150304021008092805010b011722050a120906090e0f04061d072315210c0415110d0e01180b0c 59
    0x3001b80010051051426580071620f0103081120308801100110b045641000e50562048196400d03603000c10407150003a071464003c2c800d00302d540401c5001c2d100e07200c511a02050700c000c0d401c2040281515205070180f541da541050249085900c2003510b0b080b484446900d082c50078844004110041c000c00100340194290142c090030400c0f890210400c00900c1240700070030340d0141044a00407040ca814644201e24216600301d020f580454034182440c0a120000c03c1c040d800041a4076070000c1c6143c0314071102406d460040301042d02607180c105143c10b4910340504290b44040d65000c0203407884010075200da08018000014184982ca4924110241805403400c001100062485104c1a5441c62808240610807400803a214501c1e000300c682030340f0348003649503c80741c0810180510f011030200608100d5020780c0f1607503100c0810010480314245000d50f403424961244181c40180d40c010081c1212811044c0b40030b0f2030010240b0303540c040c080b11540c84222a00c3c000104060803040034843d15034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 799414325 1250 799413075 799413077
    0x6070f1b0818040b0d0201030f02040e0a0e060105030d091a090603070e01021c0c0b180a0308040b1006021507031b030b0a0e1b090d0c06030e1b211c0519 67
    0x21344544021030005461110001c3c1003607500c0f9604203215805034162000313066074010380e0000c0c2c58041c1000004250001030620b50784074001c000509880d001400c1100c840c030702c1ea1108992071401c443c054182c007580c1030301c03a1994014800704080380c4440e40903610840aa5494505150b10356002904106a50034444540340d1405c041e4422070742c100d440300c105594003003c0e0507944e9541204100000300c0050314080d01e805180150014507601002042c000c0d400350701000c0c03654540c1c206118412503a48036110141c0c10040e02d0740e0041c4560541c0540c40f400c80d09001c2440d004001f012404001144545001301c1c2d13aa04a403000c03405c191902e20f016040401028055007070018424004ea42140070025074180002060b80103031b21240040360100703078014049446140c85d2103000c2c014000c50049130440e480b400c160000c1c1c0001c18000f001a428002c0d03c90b4203c0c1c10400422103942c2071920381b0000c5e40c803a441000d460301c10031821b000c03c5c060312540c1300e546640c0b4086504a521f24801080c034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 799415575 1250 799414325 799414331
    0x50d1b092f2109010f0c17010603061223010e070305120301060504051504091104140f0f01030b010302070f21050405011b0525080c030f06070f1b081804 67
    0x403207221580c8550a08200301040301d0b18079500c0150b035030b0150038616504130145082003040d40c00d01d500808a1101140c90b11031003149a80c85d144200d0440b42c4a21442d2586112810703007101044031903200b200304500c004058100060b03424000341c00d43c0c440d100d55074142d5000240810900409015840c0384180740e10080389903514280c4001c0c21790081d0302600340700b04400600110002955001c0b41d0042a1800c018000035502d4400b01046410602c01c24003d00f050b101d2040741480c00c00d010800d02c21004000410040711040110000c0010b06840f030705250f403c0001401044040702e515a10070701c00c0043d90b45240040c81c4450341e1b01c44400d020414400c06002c103102c507030780010044040000e070a580444101c86c81c01e24170714010441481800c600c5c45000c05a04070f0a4040072207069030b000800311809814001d040c599695207640b01c2606031f801c0003022400b090700c1816244000c04961804410003004030a0f200d261900c440c00c00c40d26550006003a050703203400803070f8825811750700300c1d010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 799416825 1250 799415575 799415587
    0x109020d020108091905073b100e190e03130501080a02070b09010e07060203040b030103021201110d0b0a1508191b090801060f050d1b092f 61
    0x3103003000340340120080c1401000c0c070020304280030410410100344552500d0344101c4111342865515101e00d0700640c8000503203c803040c02c581c001946038072213540c4600c2458280403030f074101d69281080003414041000c43d00355800a0b803003a845074518025820100600c000349a4040c4060880d8100756048a258109010103400035011044400072140d0a0820a10315642c1464104c003d20600c50020210320110062001c081015030280020351810800c9403241c0c1c0e119a410380e40c80c0074a100d100a4050204014001030900404124400c140c0c500007041c0c0c2c44050030040e4083e0006111017003078550360300014a44d490140004070003056004004820b402e07540c43c006213040d0340100b007030b42d03003078443c0e040151508020340c04091805005001e015004c0014000181022154031403421b01d58240035000c14800f0219200d01c0407030310700801c0c0c01c000d01d500c3da9846903601c0c030f0301c40740b03403000a940200080e2641e1180210195180c00b120760352002c5088a41c0e203001a4640510800a412b0030701030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 799418075 1250 799416825 799416829
    0xd15050904050a03140904051f05120c1507020d0f30180510020d1d0319110402030c040513090201052d0a02030a0f1128020d0c08010608010902 63
    0x1018403020341505d0550702c01030385450402c41e280304132003456401a1a00080198840200300310003254041c0840311410303a5581e00c06c01240c442e01a07441d0880390800c5559100920b041000404d81d681003130040c0341061410f40019071a0508500306594140b4028094400c11000c201001040403441c04060300294142a551160101c1c541040c0180070142700b10b02e038440341191629000740310003003040c03000d003c03e03400080d1180300050601010616400840d8403000d113000c00c507480c45102400614100c0400d40c40c94a0340900101c0a45500103a80046a660380b25400118071a0004410f11940c442c50a814030154030100001e4040c02d40c540103050b80180c3e4007100301e0f03c3c44401c0504035a90380c208031500e6102e40001d20180d4004460018422145a03004006001d000e40980c075002010201490181c4c5c0d4106100c0d2441d00c2a04800340d1020420500d0902c41c902c10003d5400302c02c40d55003580810500c004030740c0251546544a2010451080709001d0840a0a80395001340911402030340 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 799419325 1250 799418075 799418083
    0x3010908120a0c08130f05010504060605130b0d020d020a08121908070207031106130e04030306080f0709020a09170c09010b120a0914120703030c090302090711120d1505090405 77
    0x4100701034260040c0c54242400b00c40030f1b641c1001e0381c0210081045043c40e2410100805451055602031100d210548044110510802500b204060211140170a10313508202c10300f01c0e01c3c4001c0764042c0c000413001c0341101082041d140c03445903901406641d0306802c0c4e89415071000000c1120100800320003001042a4003141e448100c80e84050b403211100340d00c0d00001c101c0d00504204800e410001e11000803070011841410703002d24001d403010003141e0303181e00c4565152f88041c600802e0ba43d014000400c1400d0a6500038002d506043c60007105040d110501e22034204401074002d2036650041110071038a16100021074010018840343d07034905180980c05402c6040000c081d43c400c41d582d480c0105c10304c5000300b0811741c66411401900e803140c012160010342600504030641c0000d10380029102c0481c0036040400903240c009101e82030980d6011801c60348081e40031a071441600552001c0c2c1d01e5081003001922a82010100201d20300c03020180d120599080da03401144204492018440030900c04a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 799420575 1250 799419325 799419331
    0x150a0902151815091804170304032c0d050c2b02191d0a3c060f08070311060405010e090c0708070b01051003050601020606011d03010908120a0c08 64
    0x5030f000c1805a200300e4028903607001c2c0300412600b041c06200c2c00d492059121044da88258410202138200402c040c4000d0514042124014045051030465006403101e5480904c000003074142c00d012070014160104041c001c07500c400301c40c40e80c0700019400913480c24007003892584403549440700d10881504410030705000326004c00384c0207007030342c106a400e1103414003007030710103413008402c0f8842840b00e1140c0d055403010221994049a0700e00000c4c403013410140f2022200c0800c03a01c4031034040c001e011956800090400250b200703120341c0c40d50300068080461600c1c8000f00b8135000074140c010310f9814002c1c0035400ca100b01030321445003000240a40d07a0442c110f03242c1c050b010364415401c1c0e50f8030002001944640c80c1d0160401c030000c40d501c4200010910710905840b020344d0f2103040190f200c0010b0341554011f880c3e85d80540c01020000b21907500ca0340420201120081d180001c01c07505001007400c42d04420821750391203000041d201c10584c803185100d500b0401121381042200c3c640500102081805 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 799421825 1250 799420575 799420579
    0x4230105010e01050d05250905060405090a0920010906021203040609080d11041706071d150309012703020303150105074409040e150a09021518 63
    0x302c100070a090b4422420345103000c400c050100000c0c10000c100c50118031101c0c084400314485440c0540700c00c1c0c418910324045401c0540344900f414140b800b0010300010007810110466a01e0071141c0202c1c81c0008034071840c008100700d0b000320351000310004204007800e8200c8420747d404181c1080700c880d2500d089a40c081c2d085880007502038464030b0b11010f14482c0c445007801c002d04003016020301344c5207100108112540d007034001007821800d40d4140c0d21080121444400300c0c41c1c950003081840e6503081d060170b020b44020400d00c0c0300d410503141918580c100359042c003c2a035440152007440d0a55882040307a05080d18180342c0700c203170b45a50003552807000500e11240d06403050301c0700185902a0040d600b0041d0301c941100b083e03034403081400042e900310b071151100c0b85400b03180703500301060b01100d4014610b40040807146003403041e2040c000a840c035038030307140c0d00c0744a2600c00307030000c1014105c2c4a0050788680004190010580100104d41d148101030840d07a0004010070a01c948101120ba40a180c0c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 799423075 1250 799421825 799421837
    0x120d09090b03010b03060c041805070e010c1e0c080f0303010320010318060504034524030c02013c0203090c01140f091306081006050423010501 63
    0x1070310002c00c0c09031519414243c1c051007a94180510f00d504100035009440303909040c0300c0351400b007151010a580301070304c04402054100800b07168551207404030b01d01c100d0003180c000050f44030540780b1b8810300f00c01d00d80541e90030760745500074010f0003c03d000d002c100400d004003d40c203550442d2284050065200300c4508036800ba50b01712005c59000360400d501741c41150f00c01c14005080c0b410310001074041141e003203000601e03400c03000c8202644003011034180c45200f401c0d800001c00d0364900d10400b00f406d400b015480c0310000400110a208001c0a55040d00b160f0912880c02c0304080b07010381a10031a14040e400c1d64104042c0c0071717101400d0030b210342c0802c0360b80702d114a50507808800c05100d0440340c20415800c5000004000c81403000042201103882c0aa8400300c1540c644601c12007035018041030820307031043c20043e440e001d260441c14810a07010303e400024a00d59100c0d0140d14018810400214060312041c0402140c0b800d4403408502c4600d40e40603e0244030001e2042d07000110501032103043c010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 799424325 1250 799423075 799423091
    0x3030603120315040c03051f08060a09030e03120903190818060c0a030e0f09040b0c0f0d1a010e041536060503070f030312050c0d02070b06120d0909 65
    0xf2400d07841c98145000a0000c0201051525009004d010304403400c080540c101c0d0004003030304030081c00030030072610320318081c10840d25041d21401c040c02541e00b0950402081442c011a640c3d002e1020040028000c4406035680714210241810120b81c01048041d2002140742ca6000c50012000c50782d00b0f0300c0d42c03445d14908500010008105001d008240700c8a0702c10800c1020405402140c081050103007114050401c424240070001c1598003210014021940540070800488042d0b016141880a00070360508122080d2800310488810810380c600345004030300d6800c40ba503003006c0d5080781610203075000d03c40c0c80c4000c2240c03010031001344140c043d82c003240d4910300b09564507101e080c2c0c030b06168546001c043c2d06044c51800007130401401041e209009025002401c018181c941d13804580c6d164480152403551020303a400105001031103032804100421000d600407001e480104481761081001c411142411030510400c9025400303040f04a0740310610030180c650300540e42e6401c40d203000300c02043c411 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 799425575 1250 799424325 799424341
    0xe1024210f03142106030c13090303090206030f0106090515070b0c16050105011a430302011a01030605180c090a0608151e061612030e010e030306031203 67
    0x4200c0c12002c1c03011030101c2c0c0004254514883d61803110701c0e0340004c40d41c0d0b4581c42c003015240e2070000d034100e40c000310202d502006600d058024000d040c0c041c0c00d0004c1c40e55410340128038254806c45002231426075120040c00029003082d4803502800040c0c3d10310700d0540c861155440a8440c01002a00390343c544030009822141d04800c036154604482d904142c0802c03a8030f4024041d280c00e024041d941d07030007030601420801c0c0302c0c5d041c0c0304030901000910781401b101c100040102c910702614443e400740c02d8500181e9000040d509148103c0c0300340c2c00001c2e1440c0070202108070103141150181010b0800b03901f081256142003440504a203105510541c035210100d49000390702c1150305403034100749222000540943c00901c00c6103e0b190100b0702450483c100b40c10000c0d1110a0401c22102c1280006a40c2c510306000303024040c80301060039a480f841700103440b204e60086000103040002500c80d05a60140d410a0103800c0240148600860640c100040002c0d200c600f002902170f0140c00c0400003a10300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 799426825 1250 799425575 799425587
    0x308070c11090a290310050403050f0a02030903031204021c0506011e05030d0e10030504020907050a0c20030d0c0803010b13030f0c061b02030606040e1024210f03 71
    0x4a00384c0d0703110080100c0700d842603500302c42c0242101480303805640088514a103060107818401c5a0640d601c0b450001643c61500760f94024280100c1140300030f200700f808544080000b450b05941d00703800d02d503080c9080d2040041d04d090008187c900a0044416200040d00025005040da22140119107104c003e20050803e1110158440d943c51b1044d0003428902d21381115068000c580706071407801120b004a0001c2d415144d0a0b10f000750000c0e0b2034800100f04910500c0584001222031401000b02040c50720740b0700d07980c00510071035209051582d88100a81c641001454103410480c20401613084450b113806000b40014451000c4251001400002c031003613000401c005907501c440802712486181c1490701c191491805000d01045154503005440c043c1844180c00c4603900400034469a600ea0042c1700c090100100c40b16110f104890304d98601110340d01540c49580c050030054580c040038500c0403001c04d209a1310407410b4448038070641000700201c10b807001ca03098008040380700f010014030341110381e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 799428075 1250 799426825 799426841
    0x61d040b032d1905061b0702010503040312090c0801050718141507060204090b040b1c0201050903120c0d030204081c050706140a14010503070303030b0303090904030c0308070c11090a 80
    0x1c240150001c2000032890514415140760041c01100c05c0c95407029038040c170340301e50340180d040303030050034041800198444c000860b03100c1e1080c80c0c95104081c3c0b111201d000d5803d20b010480344645801801c0c40220030074407031154010300d2460004903103072841d410340c070b01804980030b1500c820704035800d80071842e00c4101144800c0000b40001540d1551181007840082d0014010039012505181b0300300340074074050050980c0c00200034944017809054038905100713180b00755012410b0000600074020301e507070140f180c3d00440c4076041c0d03007a03610030b61a403986080213818142e00d01803501c1840280b1080c000050054901c00095480f00c0d8111541d440a982c680a0400000c1c512410082c4000c0c051010030002e0340690080d410602c285a9a126080420002401003076016072100100304003003842500030064145026007074a1401c0310b05004291240004c8030240c1c04640e030606814105039008010682c481911f1504e18800703146950740e940c85074411201148950b801c0000b2404810059001400b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 799429325 1250 799428075 799428163
    0x20913180b070f080105030703021302130b131e0803030601110a06230a05010303020319030204050d0b010314011109092e151b120c0c061d040b03 64
    0x20a8a811000184a8103c2c0c266000004990704000221070030005000c50a43e03900401215440707110744503050013034204400303640e00c030f040400000030032900b114000c003501c00c42040500146818050754019a007c80b11340301f080c41707020100800440c8804070541e03801c01000d01c1c0c01d81d08040054981c41c41c100407480064119864807420191502c000030f14003820008031b00012200d0b55501081500b100c500b4813025003d80c004106400708850100b0b1070740800101400c005080c6034130f44000c030b80c4001c05404102d95581a100050062006100c480d00d0160b8000303009100d0340c00008002141c50058040250052039400046100f90490940001d4002010ba03c00f407448070210714299060f401c107101c1d04205034807402e80c00403030511820600d850004510304504003403542e030b078a0000c3c0a80340034000e4108089061118001003004081100a01c7d1a59409403048203c0011002c031102c54103490380b0441c41e14403030a140b51004628144142d020b207003500d5084103449000641024089000c3c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 799430575 1250 799429325 799429343
    0x1603090f0c0e01030209070f080114061201031a0603070f05011409040e01141f1a07080c0d020d0c0b0601110f0f03190207080a060c0905090c09031002091318 69
    0x2c2803116010710403504036802112642c2a5403a08607041c0c590032080031807400003d080c034006010200382c61810018018018010501d8202041c0301004140002c0c1c0049544461002100c0b8040340a050040d410081c1100a80030942c606965510740f01c88510441d418003100c1c16007245001000c00035200284400352062044d45000c10380ba500030500b040340380d80e40b07010040c04685d020950727498030300383c800042c503442c44031905240c10503214084618401c00c0409003046618005071245016062401d8014001d11402c4131800300a418040341074128001c100000e41c0d6180803401d0740006d690050000c0c01c144103a8414411610304014044c200a0790510a83c55401216140040103003050061580c01110303d40000c42c040b40c9800040c800c8a0403644900701020200b0340581c80b000a2242c0d50401c101466a20380224410b800304662180303283c4c0c004a2100858201030200666103440041d08528041c1c9240029082120a83c26811119502d6128200d89100480480111a080300da00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 799431825 1250 799430575 799430579
    0x61209120804030807050c0316020f030703030f0e010f0e010c03030609060f0f210b090a0605130506100609141309080309070e0c03071b020a06021e061603090f0c 71
    0xd0007a10060354124005103101000540785886242910410340c000c2025514003c01401d084541c07034050b000036039000714003904d50810351f1f404100d190b00440c0300351034038004400058005482d580480c0a00c0307050004142208042c0e03036201d0b45201034060242042581c0d80c003507042c00c800524541d00300c0c075119850000081196504124420102e4034405014010541c907030203034403000600d800600d100059504000c0001555040c42258000380c40030031a400d0a01c4c507121901902c0d030070b5404007051409044100117224060082603401026100d1509070589400da00428503540c034411029001d56141503070540d6031300c840e00c41203c91800c4009100d802d4807401c09100c1e544c0141c406120318402d4840004000400c05140c82c46406401e01041c11a82c400e03c043d070300c003840000149400e40c0c0c5a2207100046c3c0d01e04c117070342c2c0c0a847d03a40e00501c1e4542e212903244a1421807852000b6480e4800000c00a07490720170181022846001d14000c00e09a03800e142c406844400440c00401004940c040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 799433075 1250 799431825 799431827
    0x1e0907020601140d0506012601021314030c010e060f07060e010b120d02030f090d150e160e0109150e0405030c0c040203150904020319031101110405030706120912 71
    0x324180e03403012000340307803d681203c2002600030000c840284507401190042004008061028113600d0030041c0101d200c1801a01260890748110100040f2500341c01341400031004025400385c107010181e009148c7c206540c0000381407030360443d440c1845184000303400726007002e050007642d1400394054018072a20145140b60381c080c0c821070090303601414680b00c10303541b43c0700c2c00200f030b001240480c1c001c3c51400c0292a07100f00d0581c030184c41030342c105400614480008900000b41070550060140000f03009100e4544a401d0690a0500384403006610406021f101da100f420071b81114840480054410f02c2d951020031000007550060fa13104420508010500c038020004020810f0700c582030b9802d4040502c10402240426102e4010000c0105c3c0c0c403803030508140310741540146c002800c40e00305d04020200320030100640c10003240064444e16102009000900a000d160b0114500c0e9a04003410800440e41c0c1d06e6031032062004001c003003840481c19030142d510107941c0c00c0e085005400c01d0044080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 799434325 1250 799433075 799433083
    0xa4a100809060702150c071b09140604060b0906130317040f0806010b04050d03020a150f050a0203090307080d09080729091e100218010207090b06091e090702 69
    0x30082454042c01c000a80303618800700c4c0c3c51054100101850f50940c8442485103100d400484e0b049407440320035142401000710307404038000203002c001c801003a4100c00100302c80310f1001c0074015030701407410004c040c0000a080381c25251030b000151105a10303039060511403040c2946543c005000380c012140d003588189000c034001d101703642d20349840940315940e80700c070203a40d52170910598070306460502c41030249142041d10785103051300910484a06003a40e45403040e0004c0144400a4000d903a408030700d90304000c0d07004466101101000442c01d6150200725a40c80c1d00c201035004080314400164661740701c041360300003050940c2001c04207464050398039080b00c81c0c888515100e91040b101100013941e081c40326041d548244182000f420310800e16110089129040181c1404540100300b0078040c2c2c0351440c0b0140040d40c1c01d00422500301c440da003002a0405c50550040407019003803109015040d1910012242c182501340c40721004c17111002c0c07128030351100b14035041d540100300304113122801740d0000b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 799435575 1250 799434325 799434331
    0x120e0303160e0409230303160c03020319080105130e07090924051005031b060d020c16050a06180506071505090109170403021503150a0b0a4a1008 64
    0x403105c81440c07802142c402e0380d42d0004a6440300d0342440d0058074126030307204481852025120b40100c0c3d04080c8107209940d00c0300000760603a03000a5641004001905d0301050b000152103005100304600e501000c8995217030071003405410601921b48260004000f02ca4540d1100392114040703490080504a4400000c1c2c0019030301e01d03041c0440d008000c2110314000c00c3d61034001c2c00040c9021101c9146070300340403054210000c0c60503a540c0c00d001d4140b007420f00b4421134206140c1e40c4014035034507061a00300840d03410250000c0c010414801050320202110407010802d5990407509035450300001c0c54a283c01c1c40d80404040002400c010502a400d28150005c41c003142c42009051102490380e01031030210300071440042d60140e4060444600c07945444001c5802c0844070806500c078807013035000310341125800c0c0c1c07000080d00c4d40000c040358015802010182800041d024031000c2d1164030b1120052000b0030b20b0038101d00000a01180005c40c01100e80016450020b07020342000b1f451020301802d020030031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 799436825 1250 799435575 799435613
    0x5060c01140f070507110a35070608012d0303110c2b020409173a0c020a240f0209180403020316080406120e0303160e0409 54
    0x200002c01c9400100940c0584218402c4e03495600b40043e0703442d400280d0f200706040b960022085c070f0020558031714072382604100300c080c2c0c054100e030400d0005410b005039a03141c140c1034154001840a20103030b43d00440e007504640e00081c210326001c820f40804400d05000c0400301d94049100d0800008140c3c0010742c684000c0190700a641720083e802c030138000b11340a5000388015545035181018400d443e107404034500d55001410000703c51000d075407000d01800e41142024070741d0202248504050072017100103c0c1c101e2448058241c45146414984049086425921105625210380b01d164920800200c0c250f00d8000c2201400604e5000751002d14170040740b5481641414500c60f240310614500031182c04030009895a803649180b0002d40c50b82080140045003180020032191310051300e00c00314401028002c580c09030341c1e18540800034195043c24005d03415102e0074001e4042005030f0200941758490b00c6541c400e92041c65058046036000352a0300c14907070244c50458030b5005e0000e0562103e2403d001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 799438075 1250 799436825 799436861
    0x82503062904060513080706030e19151a1003061401020c0a03020411071b0509360f120309070e04050a03030903050d0c1806140f031005060c01 63
    0x1018080703000d9080786084244407140200800c0125610440c001d10010324452200244661170701c044a08291043c7d0101001989070602031910f0f40701070000ca0007914015102580100e03055850000300e540e900304020175259034009010300b8522905103821000e00c0104071ba0301c2030b030304d00b0400b80041c60240940991032119500b840300d5035000061882d29040011310320f4041c0343c070b59400c00c00a40302c440840380401e80140901000540c010000d050740c0e80300c41c203818080a00780424401d004034010510b100009031a003c2108500a900415100b0345100100410a000c038550a80c90800c0070b041c0000785100d00b540c0d40c0c08198100d070146014400c0c1c0f000380c5400e640c0d90f552031004400701383e80280144c2c0280d542140001e029600a0064501c2410160708105000712603908403201040400007042c00d0b64078070341c1c0c003284040e850300c081c0403241032100b8600d0300c10740b18941070b0043d10310845403c100040811042c2090600c1ca00c0184001803030380365034020340614640640900e1030f24404e1456 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 799439325 1250 799438075 799438109
    0x2040903092306030c0a0c020a12062304150e0a06060e090607051c060308071118070c02011404050a17010e150703022101060f08060402070309030308250306 69
    0x110034494040b501800415050035a00c2d80c040002486e030250201506110380b4070034140c0181c48201c01d4600070003044100c41e031000d020f0f041000c292101114804000c826a41c20001d01100c10000c0640080c0c00500e000e50759009010710700b0090208040f06505482200220410030102c0d0704201c0c150341d040146400c080e00c40e03283d0281d641340d06640b504003182080c0a01c44207000c4c01400e00051070440480411825540c5d00c400016034000101500d42c90310501c2c00034034500b411042001c00500f000c42214091070002c600030000c10780c4040c02810010602200c0d44c0c403055400545010340303802018031000554a1400c103850014801284c6210750a0192042155002042030b02880c0ca04014000d03242d41c503090224001e501c04481c00c0400d215800321080007404014809010782a207890380c03582e01d6218000035001c0c840003010303c0e1249004000302000254031000480c2140e5150526211580301c00058a83c00f000c07440c5000d20b40e03080b800c5008032807545031b000501210316030311090300d20300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 799440575 1250 799439325 799439369
    0xf060f1e05150d540305070614040f03020c0312180604180203010f0e0c04060318050a0b1f03021503060114070b04140303100b0c03040504060e1b04030302070905060402070204090309 80
    0x140c0b50b00550746501c00003500c00f10211b03024500a1406a00c01c1c900022003882d10f94419107407040544080e1003103103090b14518100740c1c0400c40760a0340e0030f0850040110000b864941d480b00d01c03079039420b030482100c1c130032140c12035459000555002d064180c0b01e090344071040f444150000d42091290b160400081c04001070142c2c05410024011009407008924040c148ae03015009041003c6000d0081c201c4c0700c82000c0405e505100035640d10b0b01c1409400e4080c00c100c0c8950034242c4440ca41b15440c02c015400c00c10050345c3e007054a080b90614000056165134580005031825506070000c03084e0b0f8440001c0403810007082280c1580b2451007005c1007810000b001c00f0882d80d0340000c840c4058802d012103020710007262124060b00703401902c681102e2a007a25400818259541640034003882e1100c00c05204802c20095000001115912030380783c1000e1864500943c1c880c0248100202113540b0008a4030a4030307150100d412a54000e4020f001c180000d00d001132031290244982c0c8011110320030020002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 799441825 1250 799440575 799440701
    0xf020d110301120f110d031805040e03040e0408040e09010f051503060403111212010807060c030c03030f110304110906010216030206030a0f060f1e05150d 68
    0x40c80d4100341d40341c0c04003159560312074101d21030081618501e0b0305c041e5503400c40d60b0303900300211028482d030340314002000e806102c0b0607103000541200e0b01c5030342021010919000300006403030454503c00c07400c0015032a1801e00099034441c0703402203a0100c06140c1040416441504440d484440f22041002540d45141c82d1816440202c1041c942c942c00020104010078860340c00c400c0303140201d00c151151868004410141540546001c0b10302800040c0104104a0300740b040000401c01c40c20a05021152076030000d01c13a590380e110090906030b0320741000c00c040e0b449520800740f01c950100032644c1c9060a04006103000c0608075154483c81070000080d240303500c04034030140307551014405500118295802c000582c0c00c01411082020741d03a200c900d000e5505802102d0041c0843c1c2d5240e40480d051244014840100506104507134001c0c403c20030444c0c4a15480903071502d0182c04181d100c22544840101405000b0b26003280e0030039800842001aa04071010190840b070f240300e4208460714011484a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 799443075 1250 799441825 799441829
    0x40504020a090b03010605040c09030c12121812060212070e1c0311100b030712080a082508060f030a080405040e0f0f0307230705010509040f0f020d110301 68
    0x48903441c04005462254008940d8400020000b21301c0c0e40e218000f050440782a1010300000641008080040c410940184130140012191200c0074612036110601540e00703121010003089064010441100c140000300000b81c90b51a068440221080c00e1800203074002c80d2800b0130a440103800b0440c82805210a42124031015000b80d140150341241d030081c401000c0c100380c0500c00c0359001030310a907805218218590350210740014821400105141c078ac030845810a601910b0804c1200d40800c01700c20954000b1045450405145e9a1300d51020024080380400c00d480720141c50845120142c000310901e1160100b039680034a80741120041695505210720050018141040180558140b64200d06002c440f40001c450210034980e8403103103089a80d4800590750382010810401b000240414034058002c2940c480c01c440d0000c2c030755641c07100c40c144a45414010f00050307c41840d2036681001c0041d01d8410005c0000b06081e40c10b00300a0340c0540c000d0310354140303040901d1200403429070a40381 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 799444325 1250 799443075 799443079
    0x70e0f0402030a03110a0b0c130b0a02060f060a1d07030c0e06030a0b04020412030819140f040501390203030420030a0b0103120f0921080405032a04050402 68
    0x103c04002034606803400080d80425800a000d0200c10001168821415500a00641d07600503600e5100c0e00da868048440c6400681000104201990141d41e0001300550004400040d4401d6074890b2000910040b0507076001e242540c1084141417500b40c1c500c03017228840c508070344041c85003502d440d01c11030b1800f0000703002d43c3e80081300744049482d09a551f17104884802000d4001032406403206160880e00c069100b0440000d40399004000380c58038070310329200020081c004180140e958a2640d0700742100700528003c1c100b40d4800c0000c00703115094004c098981942035250030340d00b030409140014070214541c0242c83c000c081038100b0026200004580c40b4640005a402031451072a0050b45004940d00742183d0511500c0a03103c0440c1000c0d4543c6e000310311642441c1c40c5110b03801405420600d06500c075405206503c00d00f0401ca000503c240041030300341ca80810f09103800c510b040f00160086801140e0076200718845414071480060701a084200758900300b803e4142603a003000165442220300175 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 799445575 1250 799444325 799444333
    0x3030e0705011211090d0503270a0905090c12010b1f0e0d050325060b03071406090d0b0106020f0609010e0a02040209030f0a0b011401030b15030601021509070e0f040203 74
    0xf0003224590360011460098401da114608010305c1c00040e80d18403c1e4006603055040018181c0901440601c000800100c1d81c0c0600c2c120a0200000307000580240f15400d405600c400001e1180074007484402c0385803c0052015500d9040c60210500800e4442c8016000340c605d4130745034401c200402c0302c00c64008141e945030b620481070002030010343c40c00504100c85500c000e000d102c40d400b10039003030000da185420910b168244001d0400000792031000c10024000d4001450500c0070302d80585603042c1888094420b01d03543d00070000800c205004024014014405100010522036030204000031507024050448103291140d201e19422520700a44e80001a44819040300050070541c01402c2c24041c02019a4111031039041c41300d080900404040b01d0309500e080042c416811004400343c2004000e107002c01c803280d400004540c0c0300360703183c440100380e020202c000f402503031007000380e2090f00a9074144078480d410016044e03591f4000c00d000700031b19040e07a040068116980c1090340c9100e150014028 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 799446825 1250 799445575 799445597
    0x3106030b060c032208010509010516030e0705040b012a110a14090c0c0d020a0c06020316060207021930030e0d1704031103010c0206012303030d0f0903030e070501 71
    0x341d1090f003413074141e561000042440008407904288907288c843d147c090008206840c004896194661030684100309051070000b0381c1d112110000394040c15100140c900013104010b02c4010780341032400c100444031851032202001c4001c00300b204c0c0070039024801d010320140f02e036200c010400082600d019010f140030406100c441c0d9458540b102c203030441c424010040c54030501140d8903091080308235119015902141241c400c000ca0030000c07000802c85032010390b003020b2074800038280110650704041c2c42c013074020517030106650341d0450101441a6961071841031a50761007200d070621000f4088250303400b011500943c542c0c4180107602c1d40c41c1e0341c5562191101a051010011880c1c283e90080d59041e0303d66010741040c1d03408a0091020318041c50320022001081002c00d42075800c1069403a04540018004004803010340c5003d0f685500b40c5045200c000c40000040303859401442d4205d0741440c2892010700c210781907039102c0712142d4040e95050018810760300d6071540d221018440c41703001503420703000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 799448075 1250 799446825 799446847
    0xd030e120304020d15090215030c09090a0609060e07080f0106090e07030605032e0b030c061608030a060510361508270d053106030b060c03 61
    0x31944244003c00741d18400900c1d41700c510700086000202100c0d240c1d9404003405500d00303500e90740d8526500c05000d5195103001d0650314001d015525541c1d01818614002c0b81c10115160009409000c003090308000c229580d01584401000554145011801070000b01741928030030b440d400c3c10b813022502c444682d54586240e444d181c0380c0061500042503941d00010400b59401d000c1c80030f6104944a07695a00b160820059040071780c14406150b0071840c00c0006030841e10041018001418219140b07512040040c500c0f071240d00c102e9400500c01c031000410000d0000b09540010259081a15003001c40301d0110820355240c062841e0101c0310518603843c03a00d14000242905203003004030810007298550340c0000e440e40b41640b0450b10701142010f01005614018101d1003514422070811900070790901007130203070725010710798082010800300140c01540701003405c0110200c0c4103040d4201d8444800002c0003420a0310900610b0300181c10300034001110b20302442600c2c0f11051843c0074514101036819 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 799449325 1250 799448075 799448077
    0x1103030c0a0f11330a3806070305071401061418010302121608010506100207060c02100918060503060903040f0504090c0312030c0906090608070e060f07080c0d030e12 73
    0x284c203401c00350300f03c1011000007004800c01c0303009041c1140003141843d500054803007120480c6200c0048044021007900501d044000d10041030f080c280d036102e0b60392055040403200d510601e20b0180814a40302c200d02a61841540410221190094001c8000c0210300400070150240032342e4100034080c1034018000341c5082417041102c141010f00f100d0107402014021000107240c1c0e4060005655140d0807c641d0b4140740c8108101417040707201a280c502d0910038040c060144100010b40640c00f51140c0c46006405186203030040c00035407000980180c40c4000c0b03000a044075001d034034064003941008c65558100082a181519141090341107043c0c18001404014103044d08242c60251a00703c00101240402d0529a9481204d640200e10340300c1401010748121140e40c005400c001c1c80c0c5004028280d4085642078004110745810313030340100301600245440c06031080800e04003c3c0056000e04204000000300344601150f01913941401c0e498405a044800744903500c12103400c0140d100084a000074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 799450575 1250 799449325 799449373
    0xf0b0c1218010609060e0604050c070305040605071505090307031d0a0303030e01060506030c03041202070b03040b04020f030304090204030507090216030f021203041a09160909031103030c0a0f11 85
    0x43e0300795031241c03258151006503204188540d102d005020681c2054012150300c1215802d8040c030b02141e0ba2740c020480c1c032491107140c08008001c5000c80400100f0403546445000c4041d0a02003800c00c1000151294020b09007100411154985014106030040d001c107441540200b40108251550303c1c02d80c0a0501080c80c488155a105c1c4085015590500614018400d42540540b280790514216454108100300b85056510200080003401510002c5a0b4055403096084415032618800300c2c540c00c000c04401941400b020401090f044869805001182e018004480c0c0d8103640b02107982c12846018446032100244a0070000424004d0002c0f070f0304428030307104441c504d2260903c0d0b804950420b45040b603401300907949441040d201d0318803054010030403c010f8034811840d107605000c0416a48100c1a400361a0a81c010525010712000b600c004210030580f43d0340c1c80c240351214056030040340c0b001f02181901e0070700d040c1c0360b106049840041c10890001c1c00d001c01c05003040c0d60010002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 799451825 1250 799450575 799450621
    0x907030b1f0302040905090a020120070902070816060213050d0c05090c0f03040c0501030c1b140a050303090a0516030b0114040f090c03030e0d0c290301030f0b0c12 72
    0x2000009840328807807286c648140290380103884440154800102a40210055113955000130118100800c10108941c02218800900103035075500a14050a6034090380300b805501d200c4001c1e508090040ca03800070400e10541002c460310f044d80320000c020125229260142c0450708444060110341071003240302e50000d8209030010304100b0403d08010850b4001c80e02182c4000c0e203800200f02950700350055112000719801d200300d003100c8030304800c0d41f40083d04601030003d500d80c00b4003400348030042c0240070a050b086415660b13603140440b0313580d5444a030760304120f407180710365060041c0c0701c040d0310300700c070b00366076020408500a0746804d08211074011846c2c055a400f541c0c07880741318142100c40c80341c0c0541c1ea10400c2d04480341b0b850f5003000b81100d05400341003402860038408010028080f0303c100f105a81404030050100e0b21402e0301d0f50022030741c0d90544070303441c0e0700000040284031007503540c46a007500c1058070100a5940b80c00645141c025000000d06004c082c40100d034120110384a031058403952 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 799453075 1250 799451825 799451827
    0x801090f0b06060702100c120504080a02010f050c070b0309060709081b0f060703020105150a05010c0807060204030f0f0506010602120403020d030c05070906050f040b03070513180b01050907030b1f0302 88
    0x841d0001030800790000181070111f142030200c2c10400c80e281c00011216489403c000d0700302490010401e407103030701c0050000e04014204078000f44090103481a1203400700c0c00b00c201c0b0991034442356032071031941c0203941c840d0442c0b00301c600081d6190302c10f00114066030720b00c07030252400c10650500403c130440c0c400c1e8050740c020100700340319100341c69a00250041f28083c1d40049602d00307100701c8039114949196082e9000701c013684014405640c00505a150085d0300031502907440d2801d0034580c00078080d03500000c20710b10b1988002005e0084503100503140d00e000701c098420990741c9810980c2d48a81401111a05101c02c1c40104054500301c191008598000e0511040c0e0f4400d0b17030385260600e005600002e103840d17034a0030148000d04122880e100d0320b1806035420422444042c0000c2d55032249031050034800c901c195454003918405400a82c1346046140c1e80782e010f0704c0103182c2040540e000740078190180c10490009465648207024441c1030640140620411508002c032690195011020300414560 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 799454325 1250 799453075 799453087
    0x3070b07110d150b0901050609010f03020909010b07020909030304260c0f030406180513181203020d0f050402130507050903030313021503010e0f060d08120a060801090f0b0606 77
    0x2c841940c0042144600a0045007151451402084074900280d0a00a4a80303200520194440c1c1b0120b0300c0c000d509080032100340001d0801100a40b00d00200d04d80c00c50034503000020070070743c00f1001c1e20003d80300b1142090f59903030f0703c001560760f800100c1d4082c2c100000c50144003901c505d9900c2c0b003c2070301a940c651600d00004000d81d9490501e080c0d9070950b0070340c0700240404c402c9500424800c08e0145c0400121800b519000020314040c00c40e04014010300d5650f065080903a20101d40c0c030344801d6000d010440500410b0402600a40008030144101428003000c0c005103113940c0701d814412640180808190314004d0a91001440001d06820900400f003007130702516038042020b140720300303100c070700003d1080010f106010f03501d0b203140c410580b030700360500c01400480303000724040c0d903c0f106501c00080180e494000003001c0a6128031701074484900010303400c0c481d01603407100340e106442481052101640d070b044018200c1c0e80359080a040441e640407114009420104440e0f00700d40002c1c4001e0801c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 799455575 1250 799454325 799454329
    0xf040204031b0f090b0d0213060f0906080607030c0519121401030203070b070b01060c0224030610021c051308010507272304060e1503160503070b0711 66
    0x48051030902d206092500300070030500e000c00781928050700d481c83e02403000445500c007007200c0000d0b00600038401c29850710150840a401d511010003170441e040710700c4645a40700704000040800b13009050f070745c2c02903d00041d240c50290003984a14452030782c2c2d0501c0c1c80b2080b0107090300700702c4076040002004842c0b03229030213040c001d014140d054030411002813a554518030416180c06c2d0154444081003074140700d43c0010403400083c0d141150980d0900f803030384c08041d00c00100f0041114000d0444030310714040344e10000b0041e00c0075601c101415945414030f244412802c0e42e445000490883e81c0c010201d1002c901e1030b224201809010400074a01300106403074500c0e06081d01c800702e407284000f42080055458002041e4200010000c00b818144922810069030400074006030484026141e04525054020b4443d41d03c90401083e80c0100700d00c050034110404129031031a100801e1180c03190304440e5002090701c500d20021034200500609800c0d02d8841314029a40007503c040e0380621409020022135 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 799456825 1250 799455575 799455593
    0x70801060c030207260609010b01090e0c0708030708010501031812031a04060801050f0f0f0601050c0a0203010f0b120111190c080f030a0f1803030b060403170a022401050f04020403 79
    0x1145101d84c405000e00400f50714185051b10051541960368100200d0050070307600700c4010b0b0169403040540724241d40e5404a80042c2e0300c5070700c8005000003000010030400680c40100306059600c00d80e800e111407d407642c013880410030350920141851054000101b03d041c0203a0210307412015000e9040c0d1443e240400080856401d5481042541d4540d0104044c610344c0920030b0340d200b880c0e403403000c045042180c5050b241c490002c15030ba06029002a60303135800c0c2d070b0401030000c007154000d0090005072480c3d003602000d418000c7e1b61500030040b0500900c9001c4041c0030704d42c802c0e032505801a0402c1c61040d000301c8541407103941c0e201403049140c1ca07900072404c400300030300269408048203956418107080704011501440c450790307a19840c2c0040c403070310a032141406950721b0f034240ca4046100c50040001419a12031548024480b000c86501ca031104005180581241003ca0f0296031000c51140c1c00444580000b0003002c5411003450010310103840c001040c01401c0d0707000340c001800d1980b40d590300b11013 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 799458075 1250 799456825 799456859
    0x60405270304030c05011e032c0d030c1128050a0501051609141905030f1c05040509130501091a090d0e06090d080d05130309050405070801060c030207 66
    0x181c00016080c018000c0602d80032006160a10381201803c400d501c14a201c00482c00e00c8404154480b1903403d120007107c10307140c80484100e52540b01c0409080b00d02c5641d01c2c441425440441d04103010005494000c036500105241280c015054074010091988980a10741c0390000c114103a451003440424010400001e0b02031252000040e141412000071003542910940e6404002c04ac19007440204846480c0d0200310b0f406880010219500380c090266950f42500038941511910344900c1e040c4030005000518081c0340d2200d51015880c0700d004403001e10450043c2a00240d0300c800bc601c440c00340030f0b0408102406140001604102c6070b440b16100407902380490f494201c0181402402601449408040405410720703407152030000e4081255409807480300da1044040300d6000d01405803601c01c6500d02e20032454100800c0c58501c401c6c1192440c5c0240540001d10212004241814544203040c060602511051941e0f0318080040f103036018140c02c12030450060400008000e2003000402d12 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 799459325 1250 799458075 799458151
    0x2010c0815042a0f02060c0915130320010909090203060118140f0f07020d0e01120207080c1f020406020304090e10090b01051e300601090911010512060405 68
    0x940b0704d10795000f03142000240803400c003101d00300855496a0740d00c40103061072244540b100340d00c80c54054032448610355240e001610600012141c012841400c00562043e090700740c0b1051501512031441008442102c2e00094065100700010310440c3d00010084641c4000400c0101d070300103400190200408040d40c081c0300301e510000602925104822126a105000d4401040b018404540080030940c010002d1410701065214004011406404883c070064200d040299141090004182c0d2801c2c111a580110400c080e0325641c0c0c0200d074000c680485d01c469006505041c24440b80350014440d1504851462042590791035004000c1c0c01a001c3c00303401150b1401082d0700d08002e010010704203d003800c030040c070340f10940c030203640d01d04c1003840040080a1030040484818009030030071004007000000107108030760000980000a810030b20307034140b15202185080002c8001501e590252640300c03010f99090a002598506050380000d9001e2030400c421480e558603401c0c45411200c3d030300681c0d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 799460431 1106 799459325 799459337
    0x71406160303051503430905060406080105100302040c02010606350c21040515040501150305150105030d050d020a0201020d110a02010c0815042a 64
    0x101c252180901294001e03040d103030340071007514104100c188582046580400012506c00c21004d000e031004c060b00003044d0b0503c4105070151034014030300c5420990f0b401001032065400d020305801501245c000200007400c5006104c1a1042c0340c1d011400d583c1001001c1006541c80028500d00008074204401d0104005500c0890b803050341e4003080007040c071b9009000303140c1c56240041c180d4104040308101803081c40404840b422004440180060700f2502d004c2081c5c1c407005250580c0300c2d01c0388000080701d800e19510311005003180d070030a031034507070040f4840704200301c0341861280540340440041c0340102e04401c00030024401c422004d00311580119400c50824002d405590f00200c4003c0144811065041c0540040e001501000c00540c2000500003901d401881030318013521800300d0150140ca00c0c0d6003440040c0800355100c1540140f41091070024400a1301441201e251654501d = true := by decide +kernel

theorem cover : BRFrame.Cov 799280575 799460431 := by
  have h0 := BRFrame.cov_init 799280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 799280575 ≤ n) (h2 : n < 799460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
