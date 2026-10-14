-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1110
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:17:00.63635+00:00
-- url     : https://prove2.me/submissions/a21c0ed7-ec45-4cb1-b80e-a4f82f097322

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 199460431 ≤ n < 199640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 199461681 1250 199460431 199460441
    0x4080d08090d140403081b06010605030906130501091203021c0b1c05160e0f0a0e101505030102030f07030e07060c031206091e0b0d0302060c03071e03050105130207080706 75
    0x43d10707030315100300000700101d00c01c10010880d41511441100301d44812940c0c19040020680111041241c204184102c032500025110703001049640c00305441080ba240c02801047c41d150014090041500c1c9c0011494060b409024208880745a09501c45040d1500400325010300c05201d40c007080414100c00000d2012000c0e103079076807040084403c03202100e10440c01c06900b5900c901c107038840c90b00400c0b16070356101240702c0e04400440414003030f44055020b441d450314003c00c41840ea4540d00c1c044943d0f94590250128000e00c400b80c0219030300e0406c41c0700c142d40708400302c8614000c80d0038415500300401d4005440b0701269038a0b903520000c41c1042d98203c840c05904054204802d80360000450703140824403940c012a13814002c040d40200030000c903401a40d100b002200d03c642481918080030a40200740150f0244000036841c0e540c1d078807030f40151400e1142030380506101c096181c81300170041d0543d0119050f01d00c01c44030000c540c0e0080010343c00381e1152010003024140141700400c0014900c1e000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 199462931 1250 199461681 199461707
    0x106050f0303040e1f0308090117040305070f020406121104050702060c040902090609040212040c060306050a090203190608070e0105030703030e040b0136212004050c04080d08090d 79
    0x2c01d04100c40d400b05c20386805c20300b079001950302c0f5070002a0340380da568108414250442c00d03a00f101c8824a410b0301d0203022402440800f810090300304501d0011903582c0d40c850b001500c139400366072200c0805814104d121011200c4101d0041e0303d46404a0aa5400003450368403036080c0f2180680f07084d08021420004c0c0d009001e0898005106100307030b0b40c2c10341d164009010320801c0f81c84055502d10700341c00d00e80780f006c0d40c0d40c2c8000b06051504a0034402912021411001c3d54107151015a89468091a00030803990380c580c2c0510750740c134155010803484808201c000403540c1010764079140e66260410191191250721000b404944002d81c1f015441c02d040c0c006007520074050600000110401d03c252014001c00c003407511842c19240300e20b0700e105c9070524148019148541c1e1f5059001040031502c01005140400038081c1d5041c50304003800311110305101c00750028007501c1840b07141040c2483c0c9000f83c000d80180c24060290179910311441d8462060f0b80d05c100d4100b00200510b00321040117440e40c19000d81 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 199464181 1250 199462931 199462951
    0x30d1b0510020d0506090402150708040f0f151809181a0105010f14040302010c080f0c0303070806010203070327171b0d0b0601050313050a060902030106050f0303040e 73
    0x20910000c00d009000301d40c49001d6507071016030b503460300c070840d102101c43c010001845041e4040900016031610039803581220480c8a50039076480b80c50801c0013072802154481354041c5074603040402d00040d204040400c90703107405200a001c0a440c0c1c01550040505140780c00176085100040241c6102904648205840d11200b0304403d003050b2241c0300c4000c10005042228a0b8078001027040d568400100007100950349400c03006428501540d0285100f20b1001a04221884850505005840c803c0f280300050f18000590b40740b02c42801251240c20440310240442d140400048055002200b16646103502d560340000d040800c001139050403071001c11a9401c080181400b1442a500502111603240e1000c018001c100d2891400b441004c40c108a16008519000c1414002284001c0007a041402420030f5500c030b50381c1c0c815002052400300c601074910b00c00d0220100501120740e000100040c02500288082c98860041c4100070311590b4580c0e426502c100401c001c058540000150002044a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 199465431 1250 199464181 199464227
    0xb010e030105070c14032a0304081504061d06040b040501150909110328030201110a1d100e01050702040912090e150d060b0a0506041814010302030d 65
    0x40042030842e001281d5002c00700d01940c2c100028030840c007003002036110001c80258501001d0800641c04641c41c1e28800c41c034001e07000154100c580f814816140503002200c1180c0001034bc0e0120341d070043d0b006840655809162400104101441c031120804ca43d03034003c020800f54440740e4402003100340090003a40c0079582d0725200c0c481300c501c40c04030740000c0c01d80c9580031480e1b503403d00303010f1118911356010360300c80e0b4002203145844c02d030089014091606414620b43d5014442d090680c00352452304002054001c1c000351982d0020b400c46890007103031103500250290540c40b4001d1001c104080700f00e10b0081050f00f400d8925a40c420002400154070152000c21403d680303030307100e1b248820700102d6a00030401711042488503000d101011640440b60303c0c0c0e51000054004080350350b170b101e5042d0103481e0640b40d00b0814043e86801260701c0043c00050480da5071144e17181103055a07608812003011a40f41001021300c1058400085641641d030000d0160440041e0030030306036070741c0440c50000e240000c208 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 199466681 1250 199465431 199465457
    0xa06060c02101709031c1b080c07080310230a0b160c0e060909011a09070302070c0824061005031902040b1209010c020a0b1506070804030c0503031c0b01 67
    0x300240c0c014880c1c00020b50321481071280a000321071b481420240b1040c603200030210034500000f21601300c0b91450504070150345990284002c5031113440c00241c031103030002090112007003014407500212001e540d5444c031801c1080310030402039010200c6155100c0d109440500602110200410280202c12230356281640103640d0201c0d850074a9000301d0600381c05c6d404101031420025501680f05021000800883c41148940b040130502489512f001340042c07000105034a000750704403041070b0782000c4a5a2403580d030b8859156130f01c0c02d20148240c84141520900c0328640f00319040c0b0300591004116080300054400c04a03000c0d017000705021248c00041003499001c489510041c805410080482980d602d40d9407a1030340300d14409024074401d41c0c5008a88100039034007180140707407181d1084440b82603844003c0074403d110800320860b580300900081c010200401000104200da10600078004400c0e0350703d08058407805001070a00f4480030031030300084584a550b210410303907201418000040c0350340c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 199467931 1250 199466681 199466717
    0x6030607140924070606170d03020901170f010302012c0906030a200f1804060b010e03010e06011a0c0d0509040204120605091606020312060a080616080a06060c0210 72
    0x307011103d0714260300080c10703400e01403d4041c007000303410600c010000118200001685d0340d003078000e82204142d0b01145441850303115018895130480c801074050f01130b00708580f02c03101c02402031004a001c100d010581407606041380319011000d000c03030300b00801d8400a150603c0744e441c0004090b154140221000c0c4400a0704e02d401070000c1038400032022040b4000d42c0c05200c03001c0c1020842d00d10a11a0103450b144050b108400d85520540c0400d02092035016400141e4a52406d180c4041c0e06500300001341c1400c400c0015030a040720324108681001c0380040c43d1900d103610603810319107800e401103100c80c2500360240700108800c017800b40006180595030b41003994546841c44044420913121024442c500c075042000d000f1b1001041c198284d07039450040c002c1d69a11800c00c2602c0300600c2d40000400a81d144a000d9000380030180c255074080c41c2079000643c1040c6652404030120742c0040200c1c418562910814050300d5140e15481c950610305c1d020456100c00c146188001c204000d4905c2e060524 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 199469181 1250 199467931 199467979
    0xc01050d232403010207021f030605030d0c03020606040606080f0c120c030601021005240f0405040302010b0a0602070501120509030c0d031a01050702130e0a061112060306071409 78
    0x414995002c0400791003403954031041100345481d5120fa0b0050010714056981c0c0a0210301c0340352010704034190502e0141080d800340007607511055150044460804609070810118804a0301c29800c4c2da50550300e0300c0030881190038074000c080004080b000000d07007403405900d8040c3c02165a1240c0c07800d02a140b101c130700d091201100c2000002c10701005101580d41c04111030070b0703c0c001d4075000380680e140510000380da90031407843d00040701005110411300d41d110102c03800005400500700b0b129901d000e0401034064070740014650301410064600060140c404501c2c9010340d08140c0d68240d1903058045504007a00020b040740042e404104172008040d0010803903800741c0c050302d84000c54401071144861000b00769a1030340074188201080306200580e10101100800210280005028404072044601e0803042031001002c1c1e070718004028040d0b400d11000b4190700c43c254400d400f9181d588509040d2250810784a41c4042480481b00b40103401c80c2c0009440d48070f002600200058030124001c8076404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 199470431 1250 199469181 199469191
    0x60d0506070c0201092301052101031b170316020609040c080a110909010b0a03180308090709090f02040902040e0703060e0f160e090a0b01030b0f07020c01050d23 71
    0x38405040039403c550700061240d00804240a0b1180b4840c090b2250111740390749013000b14100f010001c0d109480f0116605503c50044182c96428919a104c0ca03003050b4501800550a61180791020b000451103280302a181e044a401c002441c00c10068050a00c0c2c3c03a00500401ca078400800d100c900450340340ca2144205034112076895056508141040c0400c441140f945000403400401c48224141c860b051098112081464440c1c2c0c0c4a051810072401800718421000302c007440c00040c0018590300008660203882d0a00139501010307510000c460483e0f00d0400010002807003600014007618083e03001001d001e0001d80085501001c902070f090030a6056081240da881d40d450601c80140d004018a403c0c2030107400c01440c4003035408403907110010062280340c11b410031441c009100740754180b055154a0740e000c0000003ca584030315040c3c0c423140701140c4034980c254500d070000fa2194070024001486080607100c142ca0400006004005030500c48040c0342035901e0418130341030008840004178494 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 199471681 1250 199470431 199470437
    0x61d04090812070302091509060c070608010f0510080402090a0e031c0608060714030408130b07020f01030533090c0c240a0f180516062303060d050607 66
    0x18036498503103955120b80203001c41e001c061050010308265110b070343e00c6940c00d040010820b902daa003458000f8419100c0c4041c0340030707140107a02d4001100ca0b049800e0382d05a801d950301c05c40c580c0e074580c0c05100c0c0c6880d84043c0c40001850000204016040c485c1c40307035802c0341d0150f201141031000049032030b18581c041c4c2c85a1030100d01011300c1c2030b0001400e00c00c600c080c00281000d0840c034100003d005290700068032840e40740c000c0c0040800c1c01c0008e072004030b41d08d0360b098601100c5841c0d95604540380d542c000382000c1e80a0780c1181107400c0190300c28802c0c940704105072030402c0c1c07901c00f140c403c0d013400342c0030013070f003040c01400442a0506658031400700c035214504140520b607445041c10242418101011603440c88111042050600c0424510b0016480200c001d00081d44c00d0841b42c0da4070140584d1442030201c0c5503e80c4407007081c058045401207803200d1164480d40150754450302214021414018020f52200403942080340f102080011038000100801c00315801c10070707441e407a00f40401aa008004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 199472931 1250 199471681 199471687
    0xc150512090c040608010504080306060a02071208040f08210901030f29010c031e090e07090602250302120115080318060a0519140a021f02090a061d040908 68
    0x50380b51a01421000e442c00c00024055400c00d6552704001e4040a02070350700c5000d020074159405442040380600400e040314808030009654102a2060343c011300070792103203a200ca079020455140004001c0510080c8002150b0310074034144001040750001e0550504041e182e0000d01046282e42c082c256421005103005c9101100c41c1603000c2c41d81c0d03200041141440101e0442401080d08029101a80e52a100002c800483ca2081c11550010b96070050303a0010341e1041404101c0c3e90051440b000e8441d6a003c9401d000e0b40403040707030f03580701c4469044844c449104009000606000e00740c040e494150b9000428079001c003010404103186560411800e03607001090642c251081040e140c8001c0d4302c02d60300702c0e1900c1c080c450018010300c1481d42e6002075402101c2603030038031071098180c1d4444101120409480301081d00c402515505140c001c510144040c0441c110302c0c5d03170640308503180100c0060400d5882d9180a1050350400c02440303036190049400081c1104680b280d02030307034003010702c0b03008100c3d5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 199474181 1250 199472931 199472953
    0x1d03070b18031902060301140a09240e011215020909070c050d0c0209060603090c060a020f01050f0708040b280902011d0a0b0d110a020703050f0a0c15051209 69
    0x1240035003014042807140303d02c4898201580350142207a0660f102007170520038404100011a61009241c1c0c480259986030141c1010421190300d03038000804541e410900e015070f1744580702d1a8044083c042c080304588030360151130003d0400810001342070740e295005401c02d050b8100040022000311040300208044815840402c4024881c1440e080c0040c103211044084603004250f850100030080c0f070141d40c00202060110900704075143c0305c10310041c64555164a0080c000b5111003d1802540940d82080046101d92a95402140c030032140b9a03619031140e552515100c010020140601014103030000004403144603215520b401858a41c5000c249290385100040098650642c1c003401a19504110300050340c0d1403402c41c080700c0c1e4038600a6100d0381c82c0701080000b031150410789030140c80d00107001d04445401158980460340200140c030021404c208070507465040010b001040003840c80d00a00c03843d0a03071160b190302e4501c0303032419500f400d025190481c1c440c0e00603546105242c0c00585014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 199475431 1250 199474181 199474183
    0x6010e040b0c0a050d0902010509150d0c02030711090709080709060e01120f1214040806040311060c03060d0c081501050a0503030f0909070e0d080a0201050a0204061d03070b1803 78
    0x25410510180b5000d103881d9600c60010064021a205e8036002e0303440302400d80941e88a03d003a0f64041800800148404401e140914801d03070003e6030b03610019041a00701c0c45954000700545445a0b08090100d1646021108100011400074180410710020240103d00d4980c01c100d00c8000c0c104007040014442e0a1194051062034161300600c000c0c0813110b010000105c1d01e20085000ea5400f041c01c1090420321003040e1380c499150145070141c03c0001c5400600d803100000c0c160b0041c1d019445030280c1e40828100d850712801e044a00c1e0035540310402c081039442c01c01c20784101d0090b0007102c0c00041583c41c3d8001c6030900ca103a039a11903405040030018031992808030495001004101c0095140c400140310284140c001e0003a40c03441071603e0f40010308450f002d05130000c40000001e121042212682c036102581d5001240c80c00015807030800003a110241a10848054a1054031401c102c800c000460040c0e0350300d100056505030280080c0028405a004090303c0f4a45107090608203580c1da0500749 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 199476681 1250 199475431 199475453
    0x7030807090909050c2101180204151d060f040f231003110312120a05010e0f0f0402010c02041b02100203011a0c0a020d080a08060f03070b0c01090506010e04 69
    0x18641c0b8600d0070b1100c000081000401a182d62401c0d03c13200580305c0c0544100c0324a0401c400c102005500f488025100043c119401d184458070845007000300d0f2410880f01185105a4006c0c1c0111000144040020180403c0c01a0344a94014030507104101c041c0041814bd480c0560b03181d81c202e885208004022484810144a8100c3c00a90150a00d0003480c40c451152851101811030180b0f103000c41c40d192020700010345c8952003203440359503a070140c03040008206821115001564607250002c14103c5440724a14083e00700c0c010030300c0041c0c9562504c407240150141040f41800082000c1100584850240c182030404070881500d9011001c54080d05109940184000c06441040180049101c40803c01c14481100300311545910f90300c074031340386401040400a54041c0d00c42c0412801c104590004151a429a0b0303500d41c0d03181c48003000e10a5030030104010961640041c03c0520020001c0fa003d40420100c000001c0342440c003035140c07241480001e812030528001c2c110200b1042c42451102 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 199477931 1250 199476681 199476689
    0x60b0702130b1003020c12070b01080609010b0d0611070c0306021803010e0a0b060d050708060610050928030c0306060e0c030411100903050d0309051b0f09060a03080703080709 77
    0x818010300345020001030040144030f04035070a1541c0460803107500e200400c007103100748010f280c031503030390b06481e041250b640351092265480b81c0c0718260000780d0383d0106025400400c003000d06454030701d0b00c1e50755444001e000c400c90884015203060000c1d40200c0d410220392001140140c50041e56004c4a01444480408001c3c00c0e90290f81404030100d0041c4002506400450700705d518080d8070b444100c00602d1410720501301901500c507004000c60341c00d001180d81e500910302140c4078000324075400d4003507419000e0b13581c0307680c0d20220740c01410030750281c0320101c0799a07100300210400c0c0240d169030b90241116821303041914600e66030342003444400400c1030704680204800359400e007140740a03035840c1001e903204031406000704070000941d560540108000805150f11100386c0340c140200302d00040041c0f5030301c502074400e480382c000e5118103203100074202c1107130000141200c074021500c1010301070f4010707001d80b102c0d800040618000004c1a5803030007401c41c03c0c0c0300e80e840840d1820030100040007850b481e00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 199479181 1250 199477931 199477969
    0x30115050901090b120307060f1406030a030f050405030a030504090605040912112802030c0108070e15070c030b1b040509010303182301020106091103011a0409060b0702 74
    0x2828822540c81407803060440700c0000300418445895804a00707070221020501c00188004181380080000f540c01c104400d00200c0010000380c0c4640ca040c544940080d41d5050305900541603a40c0864400c2c1800c0300c00800a080807450542e641000c00e00d42003000d8000d4000540c04942840262900d0158100600c8125018001c0400d140c403401c0711065010310020602c0b442c0c0c01c0703c80f00c0c110148011889202803c00a040e21502c907050743c0c8501c0c0340801c00328803a001c6d40324590050740c001d400560283c0007680e0364551803c032031b40610040d070390030962094901078103000702400141150400c0001d94483c01d0355059900f00710900300110540b40c1c00009000320240001d2000e900c03180605811240c06240452220149107001040718180381c003c0c040c02503071245400480c0810314844090030f0001c0e4000c0041d40e5a030f030314810840b12450f040d413900000070801001104e01241d01c1015a00318036140d240b85c0317641c03041e0784ca00b03c035003a074850710b407012000c0f03440c07000d46c0303090500441e0701c1454007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 199480431 1250 199479181 199479221
    0x30f091503150e01082a060d0e010b120606150c0d02031312030c0215120c031b030f04020d02310b090403080a0e0709050c1305030f0303010e0a02270301 67
    0x8a0700b01d41b140410060001420070950003100080703c07020010305640300c050283c0f96504c500302401c0d00640600c02d170780b1419600302080c05841d8200b000c40e5108214500e0090305d09900d0782c8040090040680c03004c002c4840c024001e50501080c103002281005d0a60b40045070f030b0343d010412070b81c04a80968080c2c401450f4002d0340e500401e4021440100c2c40d58100d60462a069007218090713070f1402190358000c0d403c103030841040750182c400001180500900004c0c005000c10840c1e4540b02031008440408c1c00380c0d104c50104005003016010070140510082480300b4290a0002e03182c002c510700c00c41c050008121000940040c40907100d1190314050545402c0000e02c0d10761806450524090200c0d4082691821054031255052005e000076041c0c0b00c8091210341885000011b190700b1101d4682080200300400042c9440e00081c04800640c2e400301450541c2c0c0380c24031050341040c00500300c0900d08e4007003140103801002242d030a0030100c0c601054510400b60001454210744010760610301d140c000c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 199481681 1250 199480431 199480439
    0x3020c0603011d0c0c0a05010608061311090405010b1002010506011e0e011202040f0902090f04060f030f0302010605220609050c0d020c0106121a0c0301060c030f091503150e01 77
    0x15086030075a0082e0388508461502ea0b90640440c5100300d090a030305c5400394800071010048190010401c6482e654203c460b107882e001501100440b203801d0051a0800044c80c070040d900b0308500c515800740c01307100002002900c140c0425001c000315100e120040c1d556008100c50b075a04a1a180171030104020654001001081c001e0043d0000512071414030032028540d07000c0841907011038016008040d4000609503460391580060b40042c03030841c1c400e15007089490800d0070144034490403283d4100340f40d58440e146031034034144100c1c20f00082d02103540303800b0042080e03102c1b4441d01c00c0051560000c44401c0d09c080000d44125400303071b0403104e2441d00b0300c01031221102e010402d4841d02c40c40e111005944d1040c80800b01e0043c08182e00402c1c00101d80d014410505c0b2030003c0400c40641480301c144e80654404198641034402402000081540c0c3c00c41c0101180c410720b013040440c0640c1c2060100640c0302c07540002e0001480e104c1c0030010340c490000e45040c0d001445180d00a001c020380000303280d410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 199482931 1250 199481681 199481699
    0x507050402030c040e0f1909140d05041a0c03030403051e03040b0f06010c0b01050616060501091e09050a11030309030f0d021b0f151905070b1302010917010b03160303020c060301 78
    0x100000b07c0d1145600c03818240e051010013280c100d00c1406c0d0004032250075000c540b0140264010303100e000711070075200c01210001c840120480306000c8016020b0351075582c0320b030380c00d49140c0c0041042240943d414600d40100304900d0380110f01a41c010050035001d85000f100e003100300c1c01d00500300f03810048409400c000160f00708020b503043d03030f0084650a848811150f00c4000d14040074002802650414000007180341c5181d0010600721344114011001c0070f210118807066451b42c0c0001805a0310020204021411698495410400080c10b0f80c0c500004040001c2ca0880c44801448003a000951410700940d01080b615001c0303012000180c8141810b40c1c0055001a41c8440681c01000ca20821500c41040300c42103c66001c41000c0011900e4002c2000802d950800307082224039403000c00200b224035400c0c0544080f400d905941d0002c1c0e15040802205940c0c1d081d014144496480e907884050990302400422005118205540c900a2450030005d190070f081c0c030409070148200300014041c85038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 199484181 1250 199482931 199482961
    0xc1107050913020d060e06092109120d03060f092a0c21090603050f04023312060604061d03070308041d15030c0405040507050402030c040e0f 62
    0x40e0441d603140d540e41e1100e10307103107a50484540c000d51040308004040100b0126600401e10b120641084440b035a5440c519a13545168000700d202022820700480b00d0801a50002045c0300d8001a0594515903059419149044000b40e41c10010a0f02c0e24800c1c0064881c00ea6030038000d025989050000701845100c401052082401e00c041d40e0404003a4200c0043c0200d0201418603071111781e4542215441141d64840750ad04480d15001072040380740001c51912a019550181d248100c0c18216922164200441070350078009d14207000250400740781003450500141214948521307001c0b030780c50140050703e0071810745c01032030f4034404c040903c414032045500c000c0030203404a00070a820f0310480e850340060302d8125184d100402d922400a0049002c554101420403140c820345d12030136641d03c070310040300b10b40855026481e416a1040303148000e10b03d880c0d04190b4005d4060f00070b075252203885130041400e0364411118402c00392400030781000b00f42d000c0d0003501d500a05441c00c40b182c0381030040716600224 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 199485431 1250 199484181 199484189
    0x60403021c05030a0c1401020703090608041b0f06031808040303140f0a050a02010f060503060a0c050f0c07080706230c0c181005090405030a300b040c1107 68
    0x107196a070200e404040da100d0001c0c1d10707000000c40340c80310031601000b020070203040c1d8120380c001c0482c48020301050f41402941e070301640c951200503c150501c88202c40034000140280d81c10282101103510030f43c00c03401e1850250841c101076400d02401c081c405000e40d01d5164094080c3c503002d4500f080852140401e60702902c0e07151402800c0d04030b401307003003000c14042d448000542040c0050f0703621207246c010009240e80c841c0754009004000000e010304049818920030035815401c4400041d0113022140d0280c10840c815082440c1481020900080d10b0741001c4034402c07071540994014850780408200001c000c1415180c1000b8000c11454644017150148003031111090001c11a45017103201070040d00c002a9010340007082c3d0301e02140e40040c4c024404c0c0c030440d0071000c080340c0c08640703030901c60300a07445960440011894540441022201d4442140311399076511242e0005440454410180068054015502080407141c1d03a04000843c0c4503a4001c070705105851140000d08100450800119 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 199486681 1250 199485431 199485439
    0x3021f05150d230f010f0b0405090a0b1f1a04030c0b0a021c05041806180c0212030604140c07030905010c030f0e19031a060117011a070b181002040506040302 69
    0x1000740794103114603120100e0181d40c07072175003005002e03c03004c1050340c050f0406c01400c4030709001035212030b2030403502c42410900280a6203d10f400080d9492034071480360300c0c40c85500500c801c00c3c0c1d03603030340e0071400c0241c0c1040440d00d01c0d032000504000348906008480c02909400f11218076094400001075541c0340d800550000c003880005002c4c110303c0c050003d45000700480072a080302c40300051307480e00061405002c4c607808414204ca5000140d1214494001c405060390001d21403482c030341c401c1002030340000703140304e41c0540c49012807203088002e00e00c290300901c00f140c0c20548560051402038a5980c958109034104980c1d000c10387c0c0403c1d03115034035040424060402400052248010410303400f0004105c1c0c4002c1c0c2c98600010801c409440240300415420741c0d02c5210303480d0000111203c1e42c05501344030707440482c00018045981941511491040a000c1c00c0e86010f40a0b40c429041c42c208070780b1403e030200d02c200150310124081c40300844040382484114686401c0600040d102e024900010f806 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 199487931 1250 199486681 199486733
    0x1104090b010f08132910061b0305030a0605150304050d0f08040204020d06090c021f0515090903070615140904150b040608030d0615090b03040f03021f05150d 69
    0xb4001c4440d00710b81c0305088a11003010103881030316500b60170002641d65041c440d11b0300c1000600b0900c107030001d5000510207581da42d980140d0361000c032040e0f0006411240116035542001406c0da075218481428021915982600d03454981000c40c14075440103944814440c8252200701c04039481080140d00c140c1c100c800617100c004410414000307150a0300035409035803a000c00c00e00420b800156030000080d4a086401d003414032a5459416500c05035030012400c1d9105005038030626000824039406610041100d090070410b4884400303881000660400e01c810056051044140001c506c050a1106903042680380c1003c0d030390301184a03845040941c480d41e40340c194507415900ca4112800400001d011070351204a02c40030500105110f104804070104440c8000b0450340c01050712204440c0028112410b42c2e07113540b00e441c0d0080c2c556034124218001c0041821420210b020207481007a07208a00003194506a400c41031000c9201a50900c11800b030301004000800058041703038a80d14100c0700d088 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 199489181 1250 199487931 199487933
    0x170606030703060f0b1005030a1512030318120801050901050909060c0c1905030a0201180c05010c0f06051005030105070e0303041a0c0706080910060e070c0c0503011104090b010f0813 80
    0x2000308203043c10164041c2d0720340d01b0303400c801d1791000141d8080c1080c00020003d032900201140c680d00480c0c0700724020104002180804a40070b98845213584074110420080b41c070031b030303a6442020341003070701e00d2408159004014012030034104512400350400340e070b01707c2c024104041f04c01d030740e00d000400101e1f24a40010342941c0c0300c0414070200050504a81182030340c001580b811617126013220100c5d400641c43e01041c078074116054060030b5150b42d004408036941e207040c20700446000c4c40c60081600c5444ca040d00a00010743c1c580f0030a03100d00d2201c282d0031400c0d4104000c2509650340640b80d0000c11403590145002c550700803040341c0031501340810441d100e4544005004042c06100700c80000344c02415400150b868004440900c00e49042c0b040c0e598000c0d840002d141100d41e00e00903030200143d414001070f10580209004c41040f40515504650030381d070350300040d0941d4a883c1e14043e104074007040400c202000b900602d80e075201c090070040c0e125180c602c001001b80d0f000818001500c405445080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 199490431 1250 199489181 199489211
    0x806041739030d02030f25030e0304051302070507050102070b0f0c0a050604030f0816091401090302030304060c0b1803031b0d02160212062811120117060603070306 72
    0x1000d410036200582e6100c400c0e00f00c1c0900290011120104050900000a0300e4264540e401301070f0102003500b1030f02c218000c2e003c100d001340300d03441c1c419021340720402010400f540c0d0200c5070105002e080b04056600c01031403400781c3c204102603004038199484894203000c00100001500d00c0710084074001c0d41c4a4000d4061107203060295003019119008440911040c160f00c50b0050b040c00d03d940e01d41030f07426120a150400b54903509201440000e00f880030600600d03200c406000c0cbc040c6014901100b41c2038894002074215030040e03115202080c0c04415100801c03240401c01648076100f400c41e068150b158180c065101c3c0b00c010041d0809031030413a00c4070310707402d5418103680c12005610011521016101d1111805a115403001c1e4400c14074110f13101c801000000b6a503108401c1040110109030140c80800b03102d20017080e0030558141c5450300c40d0743c502c203202c01400c080a40c0d001c00140e25454119803502040380c21562400540103001089484c3d1000103074030003160750041000480302c032152080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 199491681 1250 199490431 199490527
    0x14130201020a061a03060127020a20100f0e030f03130c0e07030501080a0201090e0606070204050c040510050a09060804030e0603041202060c0403200102011508060417 73
    0x18100f40c5440301d0300040740300c419610344840000790111200b07039888581c1c0c440b400c00c00040c03c222a08501200c985030b101c19801400ca120722a04282c1344000c0e0340200700c05007a0701e217100d103d0b441e440480b0002c1c0200c800d005a01c84200101d03400c01042468690090b120700c20070a12400d10540080854460840d11a0310548075402100500c1190341300c01d09807010800c240d07400d000003414803002049010000c01e08001050703058403141241407038a182d01128520040919500c03440a100600150300c0d58041d2a108070200359003076a41b50708200400c0344038505d1148150030000c1c14400d03080343e2a04207901c4419034145041c110280d94651408075a0121190000d50304000040144010010783d1000c050980f02d01c1c2d000c2d070f4982c2d901d00c4050071070340c0107510010b492a0340510a9000079185076802070300da940184008115801444a036403601401c0742e114180c0d60b800700c01004140600c0e041d034103896900761130b84640b5020390440802400c0050700b00b004503050001c56407414511540103c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 199492931 1250 199491681 199491683
    0x4090203040c0f080f0105070f08040b04061b0305060901081c18050604090f0c08100302120c03070e01030b06010801060512060a0e012909030601031217010f080d0314130201020a 78
    0x90506940d1301c0388441900c8408005004c0c400d90700786004280d03201d000320b61501c60300441d60b81390b4801e0b940c2d41d21000e4040d40e01500c03d0b640c041d503440d56292100300254103884404d0319a18081141c0c1400414800b403000d050780081c1c9150040c80c611114008520410300d224a0749d460320860030038045000b80311036203840c0e03c0150b001c9400280041c08140355000b07003d070324001d181e0800100c1200303e0291381c0120101d840c031000008030f10f024401032404102c40c3c0d4801801804843d51107820030302280c5440d160760004800b4090b100010005c104081850341e902001c28038020380707194941030000c0d000c0e010314403902c0c00700e0103002e0002c2d485450b101c91802c0141503110b12180c66581d2030303455940340c201049448400e0064803007e0401c801d520720840d1500c2030701034010500350b882e58880ea0304103031116040104000441c0040307880040c0201829010704990190400d1030303441c045030b180c94450102304000c1030500b0007080d034071003940c3e00060681c029181e001414107030030240700403800e020007800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 199494181 1250 199492931 199492949
    0x909070b1303060f0b0109180204090f05040506011a09040c0e10080709081b010818010905070603050603011b141b0a17070816140307060e0105070c0804090203040c 72
    0x41c0407604a0a0039504108803070190304200060b48802e50308a05940c0c0555900b404580d076450204100e81802c1c030850b1a110a060006042640705c80d4540250340c020200710a00648940901061101c148580d900601c5039605440c1060700000c4030b5070b0302c0d00842612502ca035076101d40340e03c142c030f00882010343c0389807000305003070f01c001450300c3c026051070000e42d101e1000030341540f8081541180007808072442c0c80840c1c1d4085082c1a5080111610000100b4043c00960b6200f00c161111009004da2100588946c018103001420031500a00b1544002d00076407103031307041028801c0b00400700c400342c80f80c140d03d41c80d101c902d00c0440e035400100e40c441c01c442142c00d44804c00340d21129110100d44404072601c16140b84400c145150310985041c02402c101500c1d11030204039001055502c03e02ea5001c141c0f14405075001c9e0607000702a9815900800020788040b500c034000c410b581402880b413294040d19034100080302030b00700e480b10702160107240240d450040d40013003c1010310458079004002000a21 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 199495431 1250 199494181 199494187
    0x9060c0d142a16080f16050a140d210608070b0309010f05010e15040b1008100801060323070902120f0f0c2a061609060e060901180819140106050d020909070b 69
    0x207d4025a610f44060b003c1e174806000d101d1407004501c0106e14403280f4404c030341c0c1e103103410440103204c441512401c5c1031a80c030507582c41600098501d0103104601c01000401c0e401070b240e140803e902801e54000c00006a06686840d005100c8040c83e0060300d070700462000b03c0144000b40c2c0c000450020160016040c0d800080c0101f6805843c0c0d200304614440c1c10b55940d180003403503440e26480e00703a42090000611034205001410b46a0000c21040d40d1242100800c540982e555290900300b207900c460810003210180300c080007507480000503210f0b041038080140708840e10300283c0d180181d014074580d881c0402070045418005544890340d403611115440165142d038200011b81d90350a070034410090000c00e482410006005000303010a540040001d029107150002840c01140c0451036011050808a040400840d600c6000c0011140b1140f00c05021100c1422508040c4050240100115801c0c0c0c1847c0081c03041d620740640d210380c016815902c0341ea0a440c0c01e0f1005042215503001155903034004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 199496681 1250 199495431 199495433
    0x705090c0c0c04020c071205190c090506010e0109181409010e0f0309010905010c05240a11030103080901030b0a0e0a0507031409060c0d142a16080f16 66
    0x3400041031401032160440b01007030700361420f1200343c0c0142200803d041d0003541041012851202d4a0700795284a4810307134044030542c2c8091000c0044105060b80d0040c0d940900340148402c900c01c40da00b003002402c0540010b40300b500001e100c0d44c06c901850040c0c405115018500550720340003405000304150a00c080351500c0c1c925507000340506408440c2510508090700110f410100032141c40450680d10704005030309040044d9401c0c917000d90219598801e0824954041d4154040303c01c075503280321400480e03814921603420176510240031302500d0940400c0108009010f01044038217a40080c00c001c0307801c40d89440040d01082c4664040f0020400a008004001540390f000510620898078100490075418400c1c1901280494203000c09501c5080402d0b8208000700107868080304400001c50340608041c105d00503c90180c5140c3c105502844441022624500d1001c40e44014600e0b1316060001b0041d0384c42387d1099010007e0200d100005008854840c01c20480c2d903001aa5050588448030b1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 199497931 1250 199496681 199496701
    0x1a040603080c150112080a051b1617031602120d050a090902040303050313021c0c0e010911040303030f110a0c11030705030a300809010c020a0f03050309070509 70
    0x7000101c14450f008981d56030600c1e0004003801c42c1a141c2904803008030600960701c026860380240000014800180300c40b01080700b09160f8084c050940354050301042d451802001201411504078030380000300380c1000c104070a07000042d1102c50192480c158400c60117800426550088041441150302404941c01c40503a085001001c25000641e00e03441455501c4215004038020303400018006141000410110407413160281e041c58001032130382e030001004d0022280d0baa2408402202c00e14201d0900704014115441d8543c0185440481840300428100d5403516511890000a060550717884e002004600554008907012008110346075480d4040c6101610b10b450300c200c21120000c0c0048945414280451840202d900140080130340c4c24031503850300300b9241041d09a4124002d107105c0d04030700840a000712200c0c80229100c141c47c034100540750a09540000c42190300350350080c281a400608480003e0301403541519005807a034680341025030030039040d541f00c16800041d81c3d0901040c410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 199499181 1250 199497931 199497937
    0x20609120319021507030c03110a0e01020606030f060f1315050402031c0203030105061b0d0509180402032e06030503251104110706050a05010f05030a02131a04060308 73
    0x201c0c42c2c010344811107400002c80e0740c0c0c4100c0c209101e4501da504c01041010b40241c0140011b2074075414003165040d4101400e584540081000c2c000013403114000d2a180c0d601070240c0c5810440c00c0e0060804001021b00c02030740d442c00a00002c92104148000592500c0c07202c0400b211076502c210602400c44c116905000903240540d0103912038041e051000c1c040040e40e4820302e018189940196080d40e00e04000c02103660809141044803100781e5000380c0401d0000e100c01ca15004003a10303166214041d80090080340001c0d07001030484401c04a041c031026943c001490008814a4900000b60207403c1850707045001038000c030b0b20341c0d06003819004000c200c030202c00362038041c50206086101200800005034a000380d848050815030303401c0200c1c00ca44c01d0541010940451003005a0303e001c0340d5135138140803100111050711540d60380d60010301c001301d041501c20000b01411002003003146941d8001031724031012044003606d01a91100d18618582412004001c3c0b810014030070440c49540b41000d00c4294 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 199500431 1250 199499181 199499197
    0x1060305040c0801020c0d030f0f05010e010317040b0909070e09040c170d080105041107050a0f06060902030115030c0e030a050f100204120609020a0e090309010806040b0d0209040206091203 83
    0x20169070b2020404000500c2a151110020340040040b40021042500240241c1c511080966100c000c0400340d40700a005e514000e1418088252f61341d172440c1821400001011400c070310b1890700700000c01c1061100020303517851100480e02425280c40f0a1400d8501035040da0706181c000c0c456100300018010f0340102c80e411154506595450040c030fa014054940c0031900c04900401d2106005010030305050b4041c03481014104480ba01d01001e039164180780140c0e241c022070721803010300310000400682c5e003d0316004096240040d400c550600114816141964070701108040e030742c0324034112041c460b006283c0316800240640d4260001c0d800e11a844400f0301d4001000742c0301c0c4191070240440e851003200c040311824211352030b1071100e603600cbd58068401c180090741d2001069201044083c1c10b40c220034003480d00d01c5c0c0110381d40c0e000d0b00005003400500605c0c1034411403030542140141c0d2100084022a107604880407074690341c840c03001991318002e804400d508050805884200c0f150000010f21a01e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 199501681 1250 199500431 199500443
    0x305031902030a3006080703120801180e0c040203010801020d141003080a090b031e09120405040b0301200702011106010b0a050a0201201c0509071401170106030504 72
    0xe0142000160b03568801d02ea10180051078140000c800801ca0480c19100c0c941c0c03c0c440c54400460482c40001034030b4080d0044007a035000280100b00308009103504098900703040c00c0c0007103192315100c030b0152110103600703441c001e44d5100d1a403600510340911111401c242c006000315140d507110810107000350010303c5130300240c07460704071044091801000d0441c442c0c8418000c41522318207643d00c00d00380f42c205088807410300007a0600414403c12070000b46105075180e150180300b211315103800040403080905401c035590040b0000c00900291141143d040d80c0701528003191283c80c002c082801080c09041d24004400c254200e460740201c941c00400109001366200b078412400008504e40b111070a104640000404100c02a20240120080c00c05840240000160b03240c407004e01d0b850514184020001340e45000030000340b8400919039045d010a14040100001e00c0e015440541d60041d900074482d9411081ca00d40311240e10800404484040d4810395280c59695200068003a0030180c60460341 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 199502931 1250 199501681 199501717
    0x6080c032203031d070515130e010305030d050a0e120a0908030d06030b0618060108060409140a06060b070f020603041e080a0f0e0609010e01020f0a0803060a080307020105030c13030b01030503 84
    0x103c280009540c000b46e90000700800140d042491281c2510b44c080413807203000024403c00000c840c05130031030460085001e41d014654540c80881c0380d03011640c004144c0d00c0c00794900f1140b110b0300b17800082c05442040681c80410381e50040c83c181564014980d81c4104298800011007030341091664000744100d13849072441d25190b44507101000540311429100a110812800000e9895882a107115400842c00f900001c3c800c0e29544505510f00e202200301407860388039521200c01c11201744034440003040141fa91504042580c0e8a08000100048010740300701000300c042414440300f000f01c4465090f211500c0215499070703180210302500405840c5010420800102c140309008210381141e0003801400603207002001001541d00f160304103821411489400801d10006030100a1545a41d000c2c0341c4443e1280740010411410360559041004c1640007406088010307600802540e400070780241c0119111420f1401d000407129880d4405001d820b5000e000005010022000380000d010103544104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 199504181 1250 199502931 199502981
    0xe010e01020406080a200c2b020a060e070915030302010e0102030105010504051e060c0c090c0901020d140d0627140a020a141206010f0906080c03220303 67
    0x401c07030155201c2c200c0400c801100066030b01007580d212140c8051b07280c034006661002c070350041d03030241c00c450a917080070307400f00b0714030300980901c14015130000840c030303020404034003182d18001d4a03072408000043c01c2a44900060403804414046800a480403207070400411410a51400d4080710324842034000d940b034500d00c2d41040c401030003141c1c16a801a100e052a080c0f80c1418801d150510b115400c1b01c405030402c1150080e540e80005214028a4000401d07006480c001000711500020b094829040c0c3d040118511591700030924069005580c280030140d405941042c086074419035440c0101d040c0b5181d0041299044103412440c0f00981008404d41300c00d845800b02c0c2111400401500592050310010300501000d07002810030810a250480d80c1008040c0136659a400150b02a92480d00b41400c005640d6444655800342449610b001540c0c1031400c60064241240a01880185100000000c2c02d4580c0c5d40045a2071280d0102e0a407403403c0d03d400c0040080c1040c54840c92040038400d4480c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 199505431 1250 199504181 199504183
    0x9060903050a0f0f051c02070501060e06120102090f0607050f030a05190318060b0a03020a080a02041b0e010c032006070206060d08040509070e090a0621051c02010608100e010e 77
    0x40f25401135510380500d03141c021280c2e280b100043c00c0010703c41940030032442d00040d5089c028034005010401d421621030030b000003045042d00c02103840b00030503031051010311603617078600d4214030003407505030394550f55084541407080c107100035a914121184000144500445e6221005000450b064001404821f40641048040e5020b03400d00714081400720303010b28007040040d4040f08031000020708409442d90790342d003c601921699440003c084d00a100d002042d0306082c020b0720150400c586091981030003072007018210410071a0b209040108040d042010180202c0c4c01e90809004c100b58265941c60500b402c1d561a4800c032001e10050040310049521400c1c52181d1840c500d620841c19400e160070305051041d014401001141040158059200d040c1c891180e44c0d03019081620022517101d00309010070145004614045407070041948100f030101b9008225030801c40100d0048042c1c0c918005001c0780504074903001052030b800384a100300401c2007242e20044a00c08040020701446489403001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 199506681 1250 199505431 199505447
    0xf060904050d030c09050a0306020c0c01030203040c1a12090a051b0d0602250b0106020610030b01050f04140702160b07080306090403110304030602120a05040201050a1209060903050a0f 81
    0x40c0503900c030486000c40c032802a08440c104d90f0192602d1040e45039030740e0008190b0700040d401907410030b90009050360280c400f440304007804082828150301e1828230365902d080d0190580b24058600c0c0f072918120001c802041c00301c4a89403c010300c98041030810380c0e9003640321800040300300e50700e20a12004032030118066501400418000b0040c02c0215500e48800d806580310320301c440a2a07080054820b40300400c04002082c10f406000110215810030a0107890b00e03101800610302d03841c1e600c9080000801880815064035401e44800701400340d060080707400b52800d00c600200340385491082203a035136800144039041c3c80c0c9038010100c0c0143d5808401169100301e94002e046c0050820001d03416080c80c034502038016200703141c00740e4090030200015003942c20640088443d2500011005900122450380e2900440500070070030080c1031660018207288280d04010081c4801c05040032400915507110450141e0020008d20020120b40790080c81a07001443c11b0700803031000404000c40700e21401038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 199507931 1250 199506681 199506683
    0x20c060702280302072d0f12030f0c140d0e09060303041403031303150e19110613091b020601060801061b0614010f05030c06120405240f060904 63
    0x8500603500700d803410b411048041c19401d6042d842840b6002074581c0b0352184035041e05030003940c10303041c4d5030348080081042000f940c000310502c40c0120040c05120707580640c1100c0503916040461000105217800c0d210a00c28a070058496845c80f02440210080404c10411404103540c1c0c01f4003074002401040041c0343e0685441d0780582c0140014000c0a6600d00086103510000b0112030826105c200100c000c0c01e007541003190342c84007024046003c54a1801124001c0200c0005050707502041c0c415103840b01d000e0380d0080c000b034100d1980c40c5a01d4a072401203c0e0510a20040850100d0311080400094a10594205411245c00351913414151000c620705041c2c0c0c20036502c1c4e1000c1d9107000c0d005c8590040020204950580d400000d5000504600c20400b0110520036118030a40c9004940d5403000040d90006010340c00c504c0300803410355142412100858901c0c0c601d20a81c1c0c480d42081450100f0081444660b0030889050030781c071001d034400c4244600600045045a0750781d8009225042c40300f41c030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 199509181 1250 199507931 199507963
    0x1009060801031202150412030605060c060f060604050627010c080f03040816030e010206010605030c1b030909010305031305031906020d0b0307120501050a05090a17040315020c060702 80
    0x1005100064503d0f4241100445030301c112400415800044441c0b002d064400b03c1c0c4005410b501c190205400d401000001c0400321013841c10310700d092641039156840142102c08900c20000001c245030b41e810181c80117401c02401041c1c5801d50341841401c008000c840b20342d6148601104480d003984241d00a61080342c1c0007000c14104425070181091640000d442100c2c0039405100b40c0c0d08810383c40003202842800f81e5500c1c101484000006810a801a007000302003103410000c02c1078041e9800c080711000e59100c5000c010712042c45c6420740c1103000b600341245c2d1240001000000340079001001c0c01144a40b104c43d9802103603110308061740e03070504c9205031011103000d10b211030214039191701520031b26101c0b407804940400860300290410b25a90080b120404401444200303015007403140301e5210342044001c10030341c10034003061175840f04007410003800c04407000d0341900048410419180150b9100080040c1c1d02181d81140c4043e411001c0f01c0c2c45944148800540000d100107000da0001080306 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 199510431 1250 199509181 199509197
    0x14060303070f1e061b120c0203030105010c03021009050309011206050901142106070e040b0f09180f010c170f04060e030403080408010f14040b0a09030e060a030605100906 75
    0x35482d41c410725289460070015010200441c0c0c0400c541e4080c0c0e10b214100315105c000c6121600c14060f01030403164012065051a0420302c0c3c82480c0c0010480c2e0540b134003400e180346504061b1504900e400c2e20004a581c0e9903086c28680810400004054032012400740c83d04100070300044181d5048810a01c5040c3c1c1c0442030000401008000d0003050f454040f000d45038004a5840d80154907005c0030403407040c0060342c820001c10040036400074941021781412503050100503000c0c1e00040d0544104130b5264419240600400e00340030524200c1200f503006141a20300300d00c40710030741500802180c2c1d40003001c51428201c0503006120507203064032a0080e03804014154803140c407084010154604074102d144410800400459a02e50107000100160000800e40d0100f420387d107000c4d903805900d1100c4d44002002400000f5a45030a10342d80701d2060080003444481a04040316150282a00250088000078281112941c590091000d031a019141c2d01c50001082c00c0440300001e0380c1c4680c10002e240c2d5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 199511681 1250 199510431 199510433
    0x60515070303050709080d17010b040b04090b1801080f06390f0706150b160b0c0702040603030807020d0207062007080d090e0f040b0a23010914060303070f 68
    0x80d40f00e40d4010280740b52139443c054440918030701e4100c0130b400d21404070310640d0044000c00701101c102405000010b40c041d050600c0d00100f42403d00960003032070022919a02d80f505107407030703410456580242d0801c8031012940c0d1501d030140c4480088010f101140a01d500040d501040001d2686c0e0f0301c01c03007000ba90f0094804048400c0381c4045170126882d00782040011503456460140540841c50213408001014410784800800c0a04140d00a00c0a450240720600003100c6019031192031a40005060f1819a503080b00c01c0e07114170800b04000e500910340701d00030041c168001200761154006800320b44c1c1c00c90908a0a0387d40351010302c200030000701d02c103070b084940c0800d883c00182d5809049085070203140d1114000b03424202c0f0010607070002000c803c4104202501c00042e6a0043c41e04107080141d802c20351600031003194002c010030800d40c0c0301da4a0038920708100c6c030f41015103030050480707100558640d140540501394410140003401c0d440c001240c450714021088480a0b5448a2000442d00c11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 199512931 1250 199511681 199511687
    0x2070b011e0506030717090d02030a0f12090803090f0703051f06080609061f0302010e011b0218150a0b072619080f06091f0503030d020307030605150703 67
    0x140504207400c1c485094000450f6140c1c10091401100039403a0802c0000c11040b400000c0200104151619448603281e081040e03004012100002d50300c0c5031008040c80404000c4c1e8644840b07005018820b0301c1e00d8011820b01c0701e0400911f01078922541940c4a050101080a56031102400f010b0404c4c0c03c00c1c0280c03651301d0b4042103008903250b0a4100481c003540d44480c0d09060520482d108682504414200200c0030001426135078910196840303240300c0e909540000b0041404c2c0d1010605100074008041001d041c0300341d0f038001076980240360500301c81080911200206082e00c140f00803826000c07410185180c41c140d403030f00b9642508106424200e042d10b96500c2507031162100c50380d155110064205984000000303020401008040e070000020300c0c3c6008000e441c1c01010800d514030b0134800d00c6915903a031200d01c0e8001e56441100040d80642d40c8100c001c4921a0780459418400043c4011040116030055403182915807001c020342d641d070b101070100501c8566a01000c0c000300b000482c0000740 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 199514181 1250 199512931 199512959
    0x307090f060e100e0a0506030711030315030610030c1404020c0d03091106040e1501050909090f060c090102190c050a060c0606050d0803040b090109080a03021206010f02031617040e0f0a02070b01 85
    0x527061402c1844900c20344030040c110b91044d2100d035280090103121314103d00317081042542205d0002001140c0320b185464101c1604c1c5140501e803140c2c4104d0b000099142d449030143c3e9010b000040c00c6c2c40c40c1000310301001c2e00034044c225080712a040038900050380c80c90316609075030440d00160040100c5584d0030000c40e001202c0c1c01380c0e55040c040c060064120580350514024030803c41302004003000c8039541601c514003480109030561b5410300b0040c0100d00d99021070380c9407148403500001504c9010740d10300707500343e460640c020039000242d0f81000a1101d030711184079050140074030420042c0d140c07a80d0030b001d0052182034016180c00005c00c08140003a4103445003076441160b21000291158059442820315800b010303003440020780108410f040050003121190b0080001d080504001c44000740c065168020f0240481c007070009040701c4400d11014142e0300c2c682850045205036519180c4804c10950032080d25402c000c0441c480010b121141b0358402c030f03000c103502b008441545070b10308a85000118 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 199515431 1250 199514181 199514191
    0x108010f052211030c03090c0409021804020406080313050a050d051203100909060902010206090f0607030e070e01060c140c010c0f1a0a0209010e01051603050307090f060e100e0a050603 81
    0x1c3d038451400c0301050524020b18001e8451140c426501c0c1000000c0c18034101781225418802c0340340404040059440c42809802d841c1d44003624441c0d0707641c50000400522940e40b05031001c0c040081e80580387c00814144200b80d0b44121940750b1603036103410910400c20300c0c0314401046a4051403003079070350090100141d50f2006c0d844082001c11615071141c0390517034100c084120381d000d485610042c210344c1c040c402a0b502202040c0100310018a102149030307140800313000300c4d0600d0b5890071046c80d4414240052006080781000b820115651020020f01076526150300b0340321303500a009206440345002c2880301425405079a61510b03c14240c44100d25450340c0f207411640701140f41c91319919400c200e081144643c01c11200107032107008240000d000d03600e01120090400204028070051141d061034800141601460311a85030b80e5810400e036421119030300958000e80294000103041984600f81451507070003514a0170940115420944241ca018407025501214421007888241000e101450b1f01c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 199516681 1250 199515431 199515499
    0xa090c090906020304060b060a0c080306060c070b04050301060e01080d0f120f09020306090a020d0f0309030c0b03091209031504170f04081c0c1b0b180108010f05 71
    0x1003a40c40012004807501c0110480303590ba00030042101b48640d5106202c800306080c0d510624150304500c0040c03c41c010381c240101900c1c004004039903180c0301e01c811384040500c0c403c200d41d01d01b900c0d50b50800c07564100c0c0c82018400d6080220201320030f8504c010340b6049030948030080c0070900190400b52058645012140100011203c22007800702c01c50094040c0000c0c0303100001a83c4140b401850708103480180380791442d5005020100050710b880303202040d107a812100c1d50416540313078542110f245c04582c2c07016009000034000481c00d1030340f4030025401807640b1001ca9103110400d441e00e01c40c0303006003101654140c200c822518411040780f4001a07000d8803c010070b15107194488201d5500e82c000302c58461288030082000c1c840400102705042d904940369140d40304007c08014014001c02072039000610348540a500d00144003d0100e400000c0c0480d0309209445030070103411318180050a0a0356800903201b00000905c40e10101d038204107031500a080c89682e54000d0301c8100710046500204446 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 199517931 1250 199516681 199516703
    0x51507080d05010b09040b09060a06080405010209060f0310081f0f0b03030c070302010909141b0903100207061503020105030a0213120605070f1706042d23010e0a09 72
    0x50100038440e2034040c01d074208000d919030155005000880f40d000e20041c2c0259030300004d12005549690035001100c4c070624144070704dd565807038800d01a0051000d0542c006801207014150114140e018522800c40078000080d65070703580440a690314102182001d9500e00308641c43c101c180d2030380101d00c400c0014600410303910b40c038201192030b640c00041803060540045c1028070442d80d011181e240244000a420320006034a00d80000050802503c81a04000c003495411f410041000583e005010000d00303a03254075a220000f200650701c0418221031300e42c907085030750300120031454040c415a90103a5400e421560784a0806000354042803e40701fa03100348a5000407180c1c244105002c0c3d091245001191900303281c1009413131901f07903040e04418000100c814906004c3c503826900d038011f03c01c4030082400c507541c03002003811011085044100d01441c441c038180c48440e6400c0301f4022861107811000b0002d03c1220009001c6007030241c24000ea0302100030034231040a94005450080c0142c2920320 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 199519181 1250 199517931 199517947
    0x61b0304022706040f020c06010603091502040b070c0501030e0d1803080d060801050f130f1104180c05060901020601031704151101110f1e1309050402090603010605150708 75
    0xc015000c8560300c0500701e84034003c1020b14149405800381d9240c6180c0c0950506184907016038407420140901010540d44a20400900942c441400041d4820b00000c644c0c5d1501c60000da840f40d07021a40641d101908180b002409510a10989032585101006410303404d0906404446d030302103c01041d007440030400000f102044900c001401401000711002409616080e4403c1c00e40c1c40050401c1c0e00c80d0800000c002c0d8001b040500b0740c60441e880404075445c402d243c80e01050006494228640092600260001080000310b140451a004d10f13581c0c1940c0d684c030b07402c10581c0d02c03811020305d0048e0440001007000610031240c109200c01119006428a030301e85040e8036550362000b044c1000031f00c0120240540400a106032048240007c80e0580303400508815a03400b8810310035400e440254880f24070003940c14000640d01c40e10b000c000c00a840c580e4544982d03000d42801d48099101d012041c0c00305669240503c200001c80d040549501081100e50901d0f1025402c4400282d40503035003003113901 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 199520431 1250 199519181 199519219
    0x15030305030601210c0e0a090b030a0605091009061a040213030b0c070f1214090a0e07020a080d020903280f060b030114092a04021605030723061b030402 67
    0x901701499980b103640a000c2003003000480001a071080c003040349001300003441e0340c4002c00c213850f585400141c01310b16500c84085162030955003c100e001141d00e420080c104201c0584c02c0300c161794400002c18019030032400d04100482c4520600c0050380c0e03071800410030002d800d140d13556a0200030b05841c0d6040400d03545070b0146410b4904d104941594500351440313981d90300300c428188111450048030b030130880c00350701080c040f4010303000f03401d00e121030000003c086603c2000281e0751079031701503043ea8130781c6045869000a50070080c0c1041c03080c06410014169482c8881a000c54214100d59603a81d00728680c45004481001e114291030140c1c4440c0014240d880901500040c1521551031094610705440002c0c1007403030560000950136a941c85402d119104602600c0c04100102c03401661011082c04141040c0c0002d0340c02402400085000401d01201c0444002054040e2801403070359030f0704019040d11048115012444c0103094011060309084c40e1000e1580944080d00030003041c0c0720f01c1542 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 199521681 1250 199520431 199520441
    0x1909050402030a05010e09030703050d0522050d021b100804020102031215010306150801060f021e01020c0118080301060f0903021801080d0207050132030a020304061503030503060121 80
    0x10040e40d1321940104020440303d4042d0b03902c40e0360780015504110f05a07070018814407c1e02400d200e00c944507004105c0049500d501c0038111070182031401c551641c50300e0031a0301d4904807000c01c005409007807940c1000c1c915030110250a0030008140d003200d80d0005400b520705150240c4140e0440c442480342d0b4813910b1481a9081c025069003050180001c2c990740010151682c2e60410200c030010010200185908a408181035a1160401428cc0d0300f40314802ca10b003410700701012010303411200440d5220441036009129242c0410020b029260500281c3c02e04006280d0005090200410040041c1441541c1004242c070451400d005487e661b0340010714800c0340c03c001500c0d0385100320b0042107608030800103000307400302600150005d5480c100003c2c10902c0c0c0b00324039502c142d111030303030030903154200a4042d006500c00801c215102c0c140302d0401d1000350000c95003242c8092812040f4514014121b101c882207940c503503500d514554460004403940d0394400614a80b1008015000c0400e520a01803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 199522931 1250 199521681 199521691
    0xe190201092918040c051c1e090b04140f0a032d020d09210605040809030a1a090a0b07110709060909210503010b0a092c09010b06190905040203 63
    0x81802000003c0800080b5a44481540701b801000c20484c80c1207508200d080014540a130342c0000d821000c0d03541c1c1340600440c21514884507240c54242400c2141c12010280198044e10068042c0c0941241043c0d5980214000b021035a208030003001c0000d21444804606020802c981003564280d80003156901c8030040d603050268001c0500f10406a60069204004000c1c00300d0441e441401c5000080000c1c003402000740c12107841300d0020301800031081c1102c41c9203038050101c0c2e41d18802400e180c29264000d1126030200d000003400320300d81020000b21641015000580c20000c0d480c4d007401598481c480ca54420800d006240001410140a20070100208081d50000c01e02420a02c2c1c421001c1400b0313101d403103800c00076a801c0f014a581c42170a807030546d03001041e003580c0e918291134290342c04000c41c0c0c4650700307600e0380a03901402000c40d42070034160300c070f400d92045806440d450209400e9440701541d1343d0f0005001d1045101d111012100d011001440341080ca4640b515000410241d03881190 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 199524181 1250 199522931 199522957
    0x22701030b16020714060901020a14070609060f0203030106030506010c02030607030618110d0b2d0117090c0603270606010f081306020d020f0703030e1902010929 71
    0x4100201084007842c90b003a0006101800c0d041d42060700085030071713507408401d50103040e01040c030070b2071a4002c100200b000383c1c000d101007003000700415442d03a907626a4056200050401680011504c0c0500c0c04e042c00c16003550055170a40c6c0c00c0c144114000d08005010320704011088001201603217003800402d020f004a0b07500803807150b08010604159410048000c0300003071900b00c6c1082541c18480998660329800080420759000c1600000c009118090b406001c52005600301c0a01090a00025022400070713258400d91010321564524020011603002e180e079086030140071107a1401d40d00944e4440380706006070107907210744a800c007a00041103012000551101040c40304a41c0c21140e1201c01c0340740c2c0d240840c01c0386811500c034800b50740491002403403d074011481c0d00c0c0003641a01030310b8541c00303107026030340d00c0b03034040d040040207080e0010780641c8a00440c44164000c82031000c00c0140d107078043e10b40d00061884e1104448031440c0c1c0c51401d1a4901600c4000d03186c0901e40c0c0003c18035484031807 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 199525431 1250 199524181 199524203
    0x80f0408160836010215060301021903020702041d100c02010e03040303020f06090a051c140f0d0b0a140f0415062304060e010f09030501052a0403030c02270103 70
    0x981c89004150300101900c881c441c0c3d581c81e00362580e900043e000300005c2207000b140900d45550021a001e4010024803043c0000754800e5501840c0d4585d0142492500807142409006034aa40450b034181c10080c454800c0d03000111103000318403850f080f1507000c0d04a4400002c00c0380104c50b415007990020342084006030410181d01c0e1a14000300031043c0c00030052409031416844980c1c40f0796480c03001c0e503d14080380c0010503231308036080d0013540305505112100801654460090b00c0d0708196a011812010b0100d1610814180b1801d0164011060320310002c0c2c000300110040d0204440d41d540035054962040d1100200002000503400000042855860b02d14210310ba13000128502e400c00701d460080301c2e006100030800d66601080d044aa03060a0070f048084013a500030441ea12105500060129800c0c00d040c05039054400240740c20b005c00b01120716070040c001005d140b10b01d2140d0b110140005400c0082280503207802034480904620101000c4030b031032580303000301440c004c090340140c40f0360040c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 199526681 1250 199525431 199525477
    0xa0801090311010b0f0d03020304050607080901030515030d180b0f0307080f06030604020d050a060518010c0e090a110c0f0604020f01082502070e010801020a0906080f04081608 77
    0x70841c1880b9030500407000344040c2e0501e8000c18100034641517a58170501a00d116a01803500034400ca9001d801c1c00740035596550100d003001100f982c4407498007400203160500241221501d400c1e041c1201c0001000ba040c4008401005c4402c002a0002c585100311000d0700002c501c20307440000c044051040030466180c2c40d0052000d005802c0040121b002038410201300710850b0b4011412690056048030000d036050201c0c01c2007407612620200013801c075841c180500c024070043c2c62002604650480080c0405459104115610403818034181d1700b080a80012458045094200204034140304030260b0400c28017000c414a013561102d070603c95a0032110500084d81405d02038800b20100c203007010025030404200b95980501c42c0b0070480a05008480c0f0050500c1c424024280148049100c000752940c6030241c4078003d500842d00703200410441c100000311503004562041c495101e500344000b80360754a4450054591100a404144245c04544c03100010a00009410100b1b1080c5000303841c2800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 199527931 1250 199526681 199526687
    0xd0e10140405060705182d040e0304090203131502090109120302060711030408010e070f0e060a0314030d06060e0406090e19060b030a14070603020304150c0e0a08010903 74
    0x820604451400150400010070b0b4000342403500080c1030b00d010307a6111103c01405100e004100425503202404074060040f11b2920302c0c0d580c070b80d0604901c40000414800080004960302000100404d0b0000d0208001c00c03801e550145a0005c260200000d207042c490780c4456105201c003410082041d40403610350301c0380d40d011400b0b201816001005400c01003c94501039510701d00204090304120f81070a4001c0180c01c10300a403401000c1d0f8000038480b00aa00100c261601e01501814000c8040301d00e00107220140210034034020017026201c00c80c03007410340c2c030340103041c1520340b224411602c000c10030103002da040c502c1800b00412155460781c031000c61200410082d25042c2d40194207040c200460f080c0c400700007003208046d200f6040d43c040a00021031138100007501000743c0c0a94103003c1c903080708040c03090a45188204800650668642d645c4a8809130100d02058078040d00d21040c5250a4503400065401407221284905042090989420004242d00c0d1aa0031182c01c5035140e004039130401d90 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 199529181 1250 199527931 199527941
    0x4090c03110d020310030c08070306050f060904020d0303060305060c180a06120b030705100f0807020f1e03130618080a080904020f07120804020f06070b010603050601050d0e10 77
    0x6418501804004018100080d090082c800541c0b01690300001107080c400c1c2515118000307580c004a54003c0b141d9a025039034540a40d44006d907034003820007001446101414100c14413480006019000b01e84594090024500d4082c2c2d08605040e961140031000ca481000614071400e461100c1560360190700c13140030804d01603a8800d500683c0c040c48203110b03041c0c0103c4861070a80d031200300040c00c1020100001d11785501944542e81000145010003e066400746030142070700e03616210301031503840d110300880c4c2d1584001c410341050307005035200310041e01c00c0802184100c0440d100310f03800c1c48503114020285101c40d0740410003017138040c0c0c600c001e50641c4108940c01000880040c145280d00c0383c81b50195841011400c0d40304550029414102c030300ca5000781e501458000740030264940300311b07201416002e4290340c140e2146a2419500880e46032450864041c00c0d80404007915a0f403814000380c001d00340c003130403440c14040f09004541c9441e405110314840320821500509511140070b4022044034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 199530431 1250 199529181 199529201
    0x8011a01051c0b0103020d0603060b120304140904030507050114040b01080d0815040608060a051902180415180204030b0f010506041a12041406151311090a03080409 72
    0x41484001d04a8080010b50b01ca4201c04203004200010b00c0401200280718400103040b046250080200a202d220744c05140744a205680c40c00841050031459a5240954421400010142c40d640815030801003442c0303400600ca410243d0074101c1030f5980300d082d40e4003045040070350101c4ca8100000d010404801600510b540805000c0810b00900c004058074402060440d642224480c0c6110603100d80e4000d40c0200182d109451540c00d0030a52400908001d54020440d03046070155800014414400c440140d10034102004610b40c016062001824000c4940c40302c6d4002010001074040b0704e80c001d103000041e20380c00180d072b8900b185010401018041c0000d581c1d4040c000042c07145840740000c450a41e030a002c2991060f040310083c6400e140300b500c904004003100b9100381f104001000010031150882c10003942d407990b8902d03c00f0f141600310b2801660b072201d0420b80e14107400301c00e503110068080d1882344140c0303080010300200e6805407040d03004840c1902d001904000c0b82c40c0b00c0c41403200329 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 199531681 1250 199530431 199530437
    0x190206072015090703050d120b010512011701110415091502032a01150e090a0213020703030603050109030503040506010b030412080621060105181611100608011a01 72
    0x161003850402950b514110084810410002e0b010504101c010000340c40255440030403510f8280407241d00405400b8005050b100b651f0030300091100540c0100c2c00c6d41d041c81c660081c400c0a0381c0c43c02080d0b4922842c0b22080922039513851a031b407006049684000d0028200b05942d021046400c600300400c00708443d0f02030b0300510040202c2c0818a6030200071070303040003a0100c3d1700140080b080c90710194040c0f098231244d02503107400f41d541c1d40005154622404c03070705034107880300040d9a03156603140c80380180c910003980019041c840152001890b40a0000305000707150004105031070f0f40d5440d0844451020a50128a011080004000040000134090a103440c1c2260450905c1d0b65148400b0701100f9040c8c2c148801c5400180306a141c844084003000c0e0009080601c1054061a80707460718828060140260b00d444840c01c0342940700b031006401501c40c8142d14a0312920f81100321811511441c4420b03150080b1074080310000600d0192501601000c000003511804801d0b8503849070341320326643d42c14 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 199532931 1250 199531681 199531727
    0x2090411011205060a050910090507020c131b1d09040f060605030f0a03230d051005010203040f0504051f03050d0806100c0f0809030102040902030901051003021c030519020607 77
    0x131034540c01303c10070480d841501c103000613490b40d40d1501d03059589030308003042a03480d10080100481d030004140701a124103540c4035641100c2c5400d044140d070300d416441c0c0c0380244100300041580c0e100c0c1d030451600d00074078504071004240203c0042e800300001d450968400103501742071030074020184262001417034201d004008440214070324a8850150f4a005000e008100480504240e0004612029040e90704910380d50b90741e205400c071004110a0340e103840d0143d1a654003207400e5000004580944004c0103540320f00b14900800c100c003802000f48045080380c00e00c07882c04042104091903d014500c0b1f03801420140b51444c42c004c0c600d41d4010300240c80b443c120642c0b0740d820380c1c00c003001e030844907081400030104070300781d04200b005031154000190f0550b00c005000a00500180c1c0a9030051940c10000c0c001034503112950b030188581801702a50041c15102010746150300100041d0000d407090500504045000f02c0c1c107038007070081700361860168001c030301007200d07030b640c0003600c00d00d0740340c6119060b50 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 199534181 1250 199532931 199532941
    0x6020303090d0c1e0f140a03020c040b0a18060f180b03010603150203130803180c03070e190902031902180c0315040902041b0f05040b090d03050702090411011205 71
    0x404660002190300303c000c802026806102c0090305d43c109a9401550f80d09048141000a80c0d40d81100c85040d0b00600800024100300d29003030041c072140362001402043d103035092800101801c00e04083c12650655039420025400d5810030b01540109411110000610b0700340310544142c985981c0c0840c801d0340f405209200003030107040c21815208034045c0c010b84941d189000702c03409001040018084841c044100120300820921180c40e510010096a10380c08041e428103550360400d0040039880d0741e807003001a840d40d0180c218440e0500b08030001060080040e000f0a040840304a02c3c624030f0b080003510340080d41418070540070904840d01c01034050380b42002260405000242c8a480318202c2c0b9200d80005903569000070300550b07001030003000800e10041c10006007514000c079980108018460340a10280207400b96401c96060154070361500c8070300401c1100840070704070210709100c000e10900000d81c8888c100b41f0b2086110700c0d68910385114074000501400d901140c0b1030411814001042 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 199535431 1250 199534181 199534193
    0x6050a1401020109170903070603060315020a0c0c2c040201021509070504020409050a0c11030d0b0d0b070905211b0103020c16030b06040207120e01120606020303090d0c 74
    0x1004031035640d004206800c8410340100e0140840e048080c2c88810158110f005090190006040c030000880864049070b542d40380580680b181844080d0808281e4416000f60b550f00e90000c0c08014801c0c07400c00200c000d40e44d41c080c54840d55801c0640c44041c0c008030043e003809008040b00003400c080e00300c2051841c01d640000d654030840b8812041040c05440419100364081101c040582001041035440340c0c2c486501ca002020101c405600e05801c000e408010b075800b500c8400042c20440340914a4500f241e40ca820140c100c1034146c6030094921500c140104000c241910f001d4041039603154042c501e00000c00030001540410b4100c1c1040100c50740040e4040010400c007811510303440310003600012001640240980c00200c0315901610032001140f4a03204c0f51102075a02c1001c004000c1d498140c04c1c00104d008201004181040c400c80c00d00c0c6582c0130b42c0313811000820501d00200c524035034101000c207880c0035500507409680f012052158550f0309001e1449550301070700d408000e08819488079 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 199536681 1250 199535431 199535449
    0x10e0c03041709060703020a0c0e1b0901020715020109020a06020f03121305070e040308070503100603050a09020a0609140d1101051c0911041d0706030f0e06040302060f0a0605 77
    0x1032401c840d21000039015003014041e0f4400c80801400162220340ca0b040194079a146804121840f0a6244002c15000722442c01a8028280000b401d2601c1e400410011450f5002e4210203040d0f21441c00006050b03000d402010b03505994940c008184d11440e0b1044c0981c04459070841c00c15504601455040e0140010940300007283c886075070722090310f81c040048508419040050301c140101d140c081401c850403400c041c00303a48280d40d10311041e5104a4201c07000d001c160780c3d064840c0410b00040000612a8006a8100044c5000058000010340c0050281c4a09500010104072a4003007080211502e60841c039000c00c0075140240441c25540e03800d601c0c407100801c580c0c140712010407102141c04c018803059042c0590043d04120001140c1001c0c41040700c032410051040e070924081801412980c0c1d079241c0354a142c00020407031181801e00c1035000d081421542a01e003036440c90695441c060400c21140074030b0094018110070304015003030541c03429004180d21442420524104019103a035112 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 199537931 1250 199536681 199536683
    0x90a09030f0c02040b090a05070801060c030516021c0615050337060c05090f010c0203100f18150506243006040e010902130f02040503060f0906010e0c0304 68
    0x40c0301120b064400a00244031842016070001c000c2c01c100005450107503c554015420340c0ca501e4116a61000106c5001c45410030040001d030f0144500d11030248450380071740f01c2a05c010802404400d0304a910040180250402d459050700c0b0050410706149038031130803002c0c0038194090f08900d800b00e4104101003510b909101c0d01482490701d030b1b90001814003110404254400002e221603090810700034100d800ca1400c0b00d00c540350b0001c400185600a628000340c0d04d81c098007401c0038010741c400072002004140c8103032940c2500c944011440071014036005000c944038031000c000503c440001c800884500034001b50042071b019609568603c0d0b12580d8411b8030700d01484190385c03001844409441414071070040078038074504180c10300003010040c0310203100f404169010006056025104c900380d5088820103500408800c40b4070260a10541103806c0c600c020f00405848d0a40c1c400203c1c0c584401210105280c00900007031203076401050103081d0061981f00c00ca0318460616440b141500c0c40b0180c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 199539181 1250 199537931 199537937
    0xc020c0f011b1e080a05090103140105100e0303040b0f030406060b130306050c12070206060114042108040e0403080109060b09060f0d06080111040609170303010302010c0303020c0604080702090a09030f 88
    0x303950989035070400320404444d80001d5560701d9040b210005803c42c0c01241d13034540400d00b070038981e25518404080c10f074100c640050610359480240d20003514400042d0f155241c02d4003080001180442c0c2003002410610700046030b00ea038a1030242004002c590303590300301e140c281c0c10400681e40074030106211001502d81050000609460f4000217140307a01c584804803184140100800000e290081202c40c459903080e2211100749510300c03000c101c988541e00034807815038045c0390045c01030280c00e118003442c103101d4101c0c24949602d405c02e07400201c10454048001400120051040181c6802180c0080c40040da419040150201c00200e1500074440300084614011415020a041a412181c01000c01d81c0003080410000e5180200540c85409000040b81c00308400041519400c103010080c40e580e10080c2d811642164011510f030600500d064040607001d0011500d602000c3c0300d0070f0300491241080a9544220744140610800700801c0300510501c0c0600315000700790003544189420410340307 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 199540431 1250 199539181 199539203
    0x90307230709050a020d050906070518060d090605010519030510020304020d020a0f06030b030316030c020105070b0f160216060e0d0f0605090625050703050d0c020c0f011b 75
    0x4003440c504201507220100c0c80c0e0601042c82142e8545178020300041e110f81000344159a914410560707507034000d4810f071000810800400741050341150121500c000e00510706031510600029000a8482c0c27840c080d1072159a03000100f1803031511240321200941c420102200d22417440c0c0304c0c0b980f00c2003120984203045800000040456a40c1040d051034668001c0c8507480064072811a483c2803081c60059901103032405101b0005460000113880c4400040202032008441daa80e080301c814000010407410702c14144440c000103101e00141a02c0384c1c542c011200c8040c030b059598100d100d00d40c0f4080380103542000c0c0c1e211000800c2c4011a4041d0f41da14200241c074000d91341d000c02c0003500b500001903c0d02900c40305e4401000003542006001e820420210341c820740f69143c2204005508980d5848400c2031006100a407171b0140000d054468001c2c2801c1d404c02440310340c00c106031965800748600503040110704801c0361901c1c3d90411400c2a0038640010f043c810341609840b10003041401034034030742010b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 199541681 1250 199540431 199540493
    0x30b07110102070f0c0906050303030a09050f0715140c0c0f010e04020a0309140d08040b070e15030631020c0102040906120c050414060402090d1407030308090307 71
    0x800641008211440c000c5543d0091400e10f6074010112010803101c0c0a00000b0003d450340c4d15010380000c0c0c40c8014051441c0d5102c00300450000c24042c0c1d0120b96500800003106016601480080000c0084824144c014a948100104183c0841c46103003140c190034003404101c0399000030b515104030400c1d204110400c1a410042e240107180b8404c6c6039000d400001c200c250203a141e0424488240318558000090b201c00c0d02c0703151034880c8070046000003030f500c40c00200414888185c268000504e418150b842c03c0f00c00300803031403003500304d0a52049080008148070302030410980060140c485800e84003401c600003280341c044803004220003103540740c003c9601411728900794101c60003070481c0041004110307501d1440a054140250341550642044035002a00e410107008040e54580702a18013881b03659200200402900490b141076080000c0141d5200050450321304500060207a0008003251071031440c00500b402070007024456030b0b0308180b003e2000242011800d111240e80c3c2d071541308000c0d0709 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 199542931 1250 199541681 199541687
    0x12030c030e011106010f0e1812030c07020a1502060f070e01110f0102190207230103020304140604060203090d0c020603130503120c04030b06030c09010509072d022401030b07 76
    0x2c501d560800c80c4c001c0f040005a07400c1c001c4a0b005c11100e1010007134981c0c0c4d40c1c9680b0480e2604485003400425081014280220315840d4011a03100e242d05041a04140c09500401c41c103a0346a0066080d000c0e070601c514800580401507154404142c451204c602d10300a500102203014451001e814030a068224529a0074248001400c401c507050003152105070b60120085032818a58510001d80100213001c180c18000e011800341810075000b1421311070082d040118002c1d8401002912919001450f00034800b000b0710000d409680076520158503410841c000c2820301e0840c019810910184c01b0303401c4d00503280c11081d01d07031083e444540e0403800619420a14118454801d002030940007481c10840030f05201c1028000b41d0b030042840c6983c40e43c4210506542d40c41c2c05100f10751000c000001008030f45461154240c0c03044035498280030b4014130f030040000000424400a441140c44180050040e41c108204008100d403000305140510041c0003880c20340c1c0701804054000220032002030300da030b80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 199544181 1250 199542931 199542947
    0xd0e040b1c02090c0c161e060207061d060a08010306150608060f010504080a030801090c0302090f12010b10050c060a0c0f05030901090804030f05100e0304090902270109050112030c030e01 82
    0x10440317054520500004101213080c1d5014080c1031309000c40d0007a001d60000c6400c003440f080e20b803550010181c1a092910650300052aa6400700c03118008013065152503d60700b0290801d2522a1241901d0b0f505618021041d11f60f09900407401d104003000402c01d65612220701034000754161000c40c41d01c150b01c801200d80d0300c50b50700310301c0e4903118100d070782010140c1c00790301c1034101c0302c060800b08643d908880c011000e0380320700100039070300010310550b460191404d031342d80610805800c0000a81414008003068a02c5025144d14000c140c000c86c20941148080c0a01540690380b01030030050001c0000b0081c01114130808048200302c0e000c4000740c44c07404250b1060141d40e80114406484507540e28010050240c0c04130115441d01410301d0392541305131203024103100f244820001d14102030800e6101c10051045071001e82c0e112117200300c0b500c0f00c4051521800307031000740b240440340690704014808058400607070081140240392000803000c60340c40104070382803961515203071280306142001203901035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 199545431 1250 199544181 199544197
    0x60f030d050f1c05160807030515121f020405130603080a1202070b0109020a030c030e0601150905040e010e06010e0c030604050421030f06050d2307080d0e040b1c02090c 74
    0x42c604410f0040309a02c117500322010003015610008203031345400b41103058a10903a02c48042541481080140e0f1901d002d1401c92001840103c81c1c2000c141451407c08000309441080d4036503000400780002d040540c964040c60011020071b1002602e990344812092140c40a29410040c40b0700a0781d00b007840700d0701102d40c4aa00b08444070480e58482e026000298031003845140820728000c60402024003d0085c222800c82e04005016142c0c40c0410b003030380661100a807441004064140030420340c0e5940b251a801405d007600000d00343c1c1c80841103a20380101a0018080000341c2001c10801e00702e01c01c22a82e101070107a40c0400d00c3d403114035110b418070300c034040710980001466002c000c1c4998141d10800c0400e0700200d0600180d5a5803050019941d4030000c00b07414141888001c503031404110000e01070220000080702c40c455591281c01c3d00300b1100103d1200080c0b01c0795100c10440c0761500850480501c1181e5501d000c03421600080034201160500034029180500080d09103002441580c81017 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 199546681 1250 199545431 199545487
    0x30c03030115110a21030b0307080c15031308090114030a0e07090b130c0c0c09140105061c0b0102030412210201050f071b020a03030206060f030d050f 66
    0x256100d1145181118040c81d02c440041d1034800007004079100002e24400f0a0380180180d0240c0d80580341404101844e0b2134803400381615015106582d0700c0420a84000741420f02c060490000040e0030010315404c06e60044903505001d1050003015a60840410046688040700a680c2c0403600d00590741d0183d607480354034604a001c4100031804407582c00c180c1c826000442952141d0761500c03100011607210103040f0780c0100b4045110154810380e07070303c0802c1000c45410b14080349400b070391701e02c5d8645076140c00c080d1010780c0313840700a18600258441c45026181c100d840d1810810408284285031007003483c001c1e20356445140303020382a4000d08c00c69010707003141301101e0b06c14580c604180203c020016080718020034510090b5416034410b100d194026030304d50b10084040e03100c948084460101c20080a0003040003c20200b0050341c507040c40c500254401d40180055207804010400100442c00e0028083d40088000c0240180c2c00002c0319070060825054540b05d500c1d4003010301c504071070682110a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 199547931 1250 199546681 199546687
    0x6030606080f0d05040803070305030405030c010612060b0a050d02060a031e06030b0c030114220216021206250306051002010e10061203080702250f0e041e020102030c03 74
    0x8980c10205158003542c0e61101240c0d0b08a00c19141120305105502c183c042c1358005204440000303200300020340d0001d0184c1d040324200b403489003403907007121084c1c0d1014480c1c082507210030003005039038042c1d064501000c0380c00800c414503100200b01c085500d00402481000001031030300002d4000d074088050075034649403698154a002e80000c005200d07502040d1040341101002031030215002040301e068a02a01400c00d83c02907503014419018070a041d11440011200801c240c0c03510079102908a005500d10156103580242c0184a00210b40020301e030000e8101804001c0f05241d145075480e40d23111104c401142400b6002c0c0110000c1c91150403990384004082c0458a905605401c0703554404444411340b40441b088500400c1155260301c0340010404d4810810b0010a01809490385d00000701d00583c1e040f01041c0c1c1000340440710750382d00c90040c5e0780c8208080c4802d501992504014042d09101c400c090b0810340c44203810100d0a400c448050034110380302208591080c03007505d800e2a040001c50751 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 199549181 1250 199547931 199547939
    0x11151303050c120708120a0c05060c090f0d0f02090702070308030c070c050a12060203060117040b09010f0212060f150c010e10111c02040b040303030501080d020705150a0306030606 79
    0x24a90303038808071461054510442c0c10f040c091021a40c0c1045510b81e00040c203034603060382490450342d009000d003003060140030b100f05000304c1c0d4140030b007e100d90300c0680d4140e03585680703000304803008a50b0000e15004040c00a1050300180740210074440064040760360040560f603007101207182260a80004003059030102c10f1240b4005e03444041c0500c984109500b521464551080c4555915a449042084084c691843d07011445e82c0d401190805010701d800200c074407120a14070304070707401501d003100c0c051450002c0040c90082840313051042c2c4e44404055250090200045c030f0607900150459116a0000c19140e0445d99501303441b034a035841e09c0c8032440d2582c0480c41158000d200e0141804040d005490f1038042481d60741c170481d204c1c1c2c0104061203081420108003101c40d02c070141c900940b01c0703a003048003041506c04c10015000030b502c2a038011540e503041203003503420146c54901c044255403040c241031000e940e904160051104c40c1d80103d40d101c0f6080c40c1c044024280307070340c0003900251502c20042 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 199550431 1250 199549181 199549183
    0x260c060402040b0f0604060804110901180f0b0d060506030102090409050304061d100813212703020d0f0c0f0e100f0501050705150702010c12091115130305 68
    0x58800e900803541042040c2d907603010b21544600c0c14030b04540c0300c4020401800304500415542e50003602a44501c00c8129101d800314540200c01c1c0c00c41504201442c3c06108580351501031810f50300141c43c41407000140f0140801da04004428008084a44420024602d502c0941c15a004001c00510034800081d00e805c040791240e0060140000054581c58a900d2520035041560303032a0601802c25000c1e44010031040f203450347d02520241500341d40d85030f00800b081c1d0300414840c1100300400c00c4c2c40b458440020103050241100c000c02800e015540c2d8039074180c0c0b59035880001f00c80e0141c4401c15001c0b9640341c908044401c4107002400c030f004c4032401142c6603503a503501c2802d55201c0242001103803203800d240300f11380c0094402c952020220308001d00c07280d4442c00280580901c45e0f411218981c0740824414024002143d10320b005079528458224440c0e17000d0380824101d00786034010440039000d504ca038004000d801124030b02480300016501c900050040032601541c8021080b4802c50f5101d00e011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 199551681 1250 199550431 199550443
    0x80606060d020c06251409010c0f0f050d03060611150405030409050c03010311090402240705030c280b0a0c0c0602130509060105090a150207030c14030106090209030a260c 75
    0x6600c5c89a440b10a00f0a09004070380300d039800c1030340900103820900083c0044840e44d000c0c9504886109107a4482000110b240343d2000480d485000a8049109a900010100c03070890307119004014544494a00130103010401d1400740c0c201048803045070b600c1e41059841d501c6982d0103204890f04d40810080510048009035040c1d81c031500507010003070004803c00000801c1030342c02030b40c412101c501e8505008003144181603100204c40c1264280f052070746429007940c100f880d690150313412905840d9464110400b20001192405075180c8401e12151250b1035101c0c001495031020304da5500319054200c0c011041078a1486e4800c005545d1080481402800c1c0d9a051003010b0041400b1070101c1c410b907000700140c82002801500039180c083c542680761488055440159041d8041c0010210200e001001c014001e40140c910624419121205050854031203a0002803e03a10500a84005940c04201e84080503044403070300c0c0c030b034a020034040c2460900e0b031008141110750000f015100c141000c222 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 199552931 1250 199551681 199551721
    0x4110417010902040c030501030b130222320408030903042102011205011401051c02070b040b1303170601140408070504050a020a02031c0f050f1807080606060d020c06 73
    0x2051017101c0700804180d0039038500780401803900c4c603403e0000d142e0184050101c4940c070700080244000c44100508103482c03082c1c0e400340b10b443c640c90b00c5181a00d02c403103142440d0704c2140f203c00c40d4403900307891400305100c10014000134105c40300080131031408101042502c0191001c0d85013540182d076403d41035001041c102074200d0110741090040450440c035841218125003090400c0c0e40b207410240011511648010350f0f40340c001200b121030401000103071000d005e004c2d02c41c0c1d46034070341c0f070420342094208481d000701100260b410b05102000001d5001c040d10b0901b54200c11400500d41741c07680181e80d8840301d001211402d590100e00000d4448001844004964054030100499214900c884040e403080340418070159000300705001c6012181441440c03105080c3c007001810b242201c50ba003044d9601507031480c80e0075041d007090180400c03403404030020101107040103195071403528a00c10b0311100300510280c4a0000404c101c0000340481d011038102e0380c19001910080d2038002507a0841c0300200078 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 199554181 1250 199552931 199552939
    0x4060c050f070b0f0d06030b04140f0f190305160b0601090605040308090609060d0f05061804240e030c07030302010b0307060504120f020409230a0f0204110417010902 73
    0x12005a940701281540035a18000c1c10286008220401001d040d4801401e8a14041d640c85000000c590040700050103548240840701000100c0340e406480d0a403901c1c005102034122000001c601c010000d6003d102036903034a455000001c0e80d050582c3c01d8050200444a42440204000104050001c03003510840742601c44840715034994100322594011408001c01d0600304101d424101d01e0060080c000403103008188514042c48000c6000c1520342001c50080f07055110014000e03145040d8007000c1c002103004800465a06c2d00d40c445003c01c1d61031210b11841711100144138a100c0c941c0e0b41210003503c01180c2260354034500d10b0b60b016650f000741d10044d0019480c0081548003480c1c0861161700312480f80c1e079403504107400c0800900500a203448200c4048207141d00c4040140c0b04e90046140941c02200d60821100300003003080c1d0071a08211710388680350050311041c0f0015500105900e034a6070140c40003d4827000101c40c100180c440c030381120ba1002c0170540340b0b01c1130690541004103071910a032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 199555431 1250 199554181 199554193
    0xc0c030d05070b01181d0f1905100f1803110c04140c0306180408070308060406050102030a0e030f12031b0f2d0a05040305121206130902030304060c05 66
    0x40000c071654020064000e0018054400411010b0300c8031701e08142001c00e85000284045958103410105003205100d2803094000850382040c0503414006800000d02c03150540c481400f0b80da464a440340385042c1c05240b2142e856a4004040302035034008001120303041c250403400261410f001d0181060021001c18600c030320301068005040034010b001c5e824940074070031481500c6101107101b01e504000d010f59001010358440401050141c8101e0340164040e030902a6248600e0400414502004000c2c6000d10709000040069980c00811900ca864103480c3c010b41007650200041c0c02c1c107000c900c84c0f181c2c512800311021042c906c410000c50250044d001484484040000e9245030f6000342040594140310520400c1e10178940c4000031803113030410350702007840e031218140074500c542c02070740322480003560104041c010080c2c200280b114020108aa40b420050880c48190111000800c4d090080b101440c1200610a4030f400c0780c881c45500505498596440350300082c103d480390541900c03071344907130 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 199556681 1250 199555431 199555453
    0x312020d0207021f1e0c0c0b03010e06120c1905060304030504051f0c02060d021c0506010f09050307031106120106080a05010e090606090c090a180c020d0813020a05060c0c03 76
    0xc1c1400350303d0004151245d60800c9905600380c0c2c00304002104d020144240808404c000030045030345000581b20320b00e150b545950400503800b01e80307a802030000b80249140035500c1c070090030010343d0004004040702c40d100001c00c800100c078a00142c07580a650810004800d11040580200142050341c00544204081d0705644070700307945000c5070080312004501c5060400303002d03013004c800521400f048003e000d171400c800011815050f0b1005120300c0c0105581c1d100f4040d85681c0200d4980202e499132034400ca8050804002075112000352100030040344441541052a440309016a0b6000505d8004c464082d07940c0d0340c025143e1107044501e00c02c2c0c185401c0011450940c0110b0050055410303000606003503070750b0424064902c0c4054003584140c0403c0c04004059940c0040250150014008012200740c81d04858403d681136a091601950000703046070403000e07400111143d201c08444140d0403032010600200312502c0f001c0e001160007010000e0203040301203000400d002d000c0d00640031901c0b0700501d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 199557931 1250 199556681 199556719
    0xf2c1803190e0a0b16030e0306090c0f01050a05250c0303170a0e03090904060f0c0c0606090203132402072307050f060d150e042013090312020d020702 66
    0x1ca004001c402d0105000c1502c0510318800c0380605d040c8242060350300c580b883c400103450800c3c00c031111000d5034080d0a204c2007500300100b04955200d000e0030107a0401c7c03440303440904907004880b5108044403510400551300201900c441c5a10354005001e108419202e08000f0140c0d598a211080303000d0018002c5040710792103100b0400c4d51040d100103181003405c410104090f880010340b0548000785c64541180e80c0d402c1a21a80c582c14400e516106c0040702c284c98403409440e460392004011a00c18030401c50520303894400c030403189a02010403010070320303252241d400c401c00c0380780310b200c80610102c0c80d1420408084c0c181501f4102d003110f0300400d08400005143c0d41e01f0a40106908800744a0000d0102c2c1400f4000c0c1000c1030030b00302c000c0380f035001c028000320040c003032544060074141c020828031050002058001174102003000c0740040350310052021030300000303c4040d2100304603075801040e010305125400c10131060b01502d105640d160791801000300a9000064145d110781078036910541484c030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 199559181 1250 199557931 199557949
    0x20f061e06090601110d030b0102010e07060206040803041a0a021809012607150509010908120f0d0b0409080a09120b0109020714060705040f2c1803190e 67
    0xc200c422800055850800380242c018001d00b406040c4000141181da090101340712401c1401c0541c0e07800034103507000100080c00c0d104180040703203154000b5403050110710b501080c500c0d03000e80c01003003040d070301d032124a41101c9040e8100300103104035401d002480b00c1c0c14403680052410080c010390840682c0c04107010810590760030b100f14048481074000206801c841c210110160404000076146001c3d44d9114250070001818003001c0002e40000d00800c403580c00091308406015144014a40c0c034681823100c0355030b80304100800c1d900b03807030104140d80c0521141d080188540c901803c24051280c2a24011642c2e030080400f20703000c150f4204001c103e4040400e0081c1038030790000c40c840c10341d034a00701c01c95000358044072054402c0242c0c20101d1451600030451580191020750b1807039502c61402600031254500c0350000d00c001002e21201c42400041c0035407d01a4501c8150181c821751607031010150003100030b000c0403117a80000b10f4000280450743c00100c09144030360301d0b1420b84140b14400c01007091 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 199560431 1250 199559181 199559221
    0x9010606170708010e1807030b0f010f030c0506090f190611010b010c14011103010b04080d0504060c0210021905032701090324020f03040611030c09040e03040b040303020f06 76
    0x24907000040002c000900017443d085080b41e0108000e074060300030340034240185a08261382401d1040b040c40306580000039494010441407142081071401c542d548c41c095082c074883e0300d00c20040412807007801c2e50f0324400a00c081400a00c0e071040041e146010000e050840c0c82154041000c40288924002c418020388085040582d0f50301c3c9540559628402c0e48040044030440319175848141c466010f00a500840c007030712526680075102c0389440071081c50032044111000800500380020000150010720f9024943e5040b180f01c0301c1c984c0ca02000b01e2802d0001c0e030b0400e200d20210001e00c4180304011006068100f100d8428940342640800038240c9180741c0c00c0820300040058004101151540382c04080400400c035070481c1300f201424041050382c00c1004164021070001090000304440391090315104442412103078110315010100343c1c81070048146141c00b41d91141011450840103004480150414038003842d191030700c0e41002951854404d400d00403074400c80000c0741c0420440c4071806140327 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 199561681 1250 199560431 199560437
    0x90516020102090a0e040c0317070c0519060c330608070e040312020c03041503050f07200312070804030f0e030706120b041a040605011706090402060d05090106061707 73
    0x4035190860001c5c40f142d0041059600c0d1000e8039000c00040c42c2c2075129620700c60340041603515450b4904048140d80801c1e07100e1403180211240a80000740c50748043c1c02100c0e1641032074604115541001c0b2407000621403060700782941810a1400040064038501c1e900c44450381c100005600d40c0c0401d555100c8034006c2000c004a01c60004000134844e80451244e0492030b54003509111003100d409240d50419040328401c20401d4800803096039240c45810340c01035109610011740d0818a80c042c1615030031409101d810400d4002000300018200100c61060000342d0614031b0302e241c00e440c02098904140c600b100000c01d0708103184040d0344036244210798143c0c000c000d1320b5185d2170904140c80000304030407240c80d4a5141c600000b2180e5442c400d422074440c4034170b40c51340000741c1081000111481500080e050003850a050b058040c0c0940701c003580814251000321142d01c0380d0000804901900d200490000d061504200191106400c0303001110a26101c01080301c400340c061040054085540d0400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 199562931 1250 199561681 199561699
    0xa03060f06091a040c05160c060f0302130b0a1403010b090414220606051221070c0902070f0f050d020d0f081302150720030f03030a09110a09051602010209 68
    0x703d441c244d4061400154103040c01450550b038454420034528020b4010346009410400c1040155000100c045400709a49011441d0105001e02080424004c1c003c1c6139080c48045810650079000d45403691611110b07160040e100d40e994109001d00b9031081d611103000b10300301941c5074007100c82e0913080c43c02841c000080c50030540045c80e068001c0189440162550b42e01c0c0c11001500381c8848080390b4020204a002e070603000d864200903181d881d41150300c060071030300030030030a40030914111061080e180c1000c0003681d43c04d85406d28040840556802801c002c1001c10f8030004c0150000f048847c005060f002c0c0c40c00b19440ea142a03e02005505003c2e02007121400056011010400c0c4811480d100400340000d9100300e10b50701e00c458200340011100c4c0612404032010710000c0d8021204041400c400a1080c500c5914246440c1d02028004460154580e00d846d01044055990407180f42006840c40341034a98428284015141c00d0341e0a107441c041d400010340c20b680c818001c4a50100010b080401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 199564181 1250 199562931 199562981
    0x1a010f0806031e0a051b010e0607050102090301020c070617010303050304140a0b190b0a27090602130303030513050303061002030d050403020a0b011e150e0a03060f0609 74
    0x1036030a00145100e6040c080d220400040500a0711803c0803120000010042e110080c81c1044c5403419894600200d2015601a2050b613a8049040107041005444c030507203030040e501e40240640104034030b9aa16500204601c0d08905001400c0e004495055880080b86140b100707408003561740c20f02010340050000c000140c042030740f42c07501d400ba854644048882d8541c1310340740c02d401c0c007000351060074460410640d00f400252030760003000c8000104a42d041d021a18201503a4450215900c00280f500300c0d401da5940824503590000140725044a400d5540d008940c0900003807006078041200424907220100f0602425420611082d5a0103c0118510307203c1000f01b225031601000928110310041040c118000f215005d5580160700ca60001c0a0941080c40d0003610150147c001900d43c1c6040c1c80c0c0f410340000002075001c101c0b055075440c8003224104000450b1a802d00c0c200668010900c0000001000303030390341c072800000c070031100108003468076000f2007415620108592a01050940c400d40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 199565431 1250 199564181 199564187
    0x9020705030904050c04170f030307031d16030b090f07052b0c0e0124030c0e12060106020618100b0f091603050c2a1f02030105041a010f 60
    0x450224000d000301ea0500c0300d00e030005004d4a81c2103e51044010000c1002c002014050b800c0311200103081000d00307012001004035030358a0000904440402d621030300d845141c4003407098038501b550f0306a81a1900010180400030710300045110445085506d0f1002810302c54000c51407040d0403150304054140c0342c1c40c1200304404c8400c4045204222400305468802803e00b8014200b00e5074425081d51121626041c0301428200d0140e0200c07002a010181030141e00d0100745603105480400d042c002201c0d00110700890320b03802421121740d0072203425100d00f0320050001541078100d606d0355084a40c1d654505940401840202c501072045600c8452080d1110806800100600300043c21903a440c070200c4000030000308050343d80307120100a0714200e8000a505014566114501c402c0c102c1c54031b0303038003120030712000000746d45112207020094102442c1001401856214407424a000d003d2411807031a41000354400e05c0350354882c900d400a030784448c40d59280d01c0c0d412014141c4482001c0c4035484015 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 199566681 1250 199565431 199565437
    0x4050c0a08100503030408071815150201020d2a02030f0a0e1314090d170408031902131707030816030c06090809010e0f13020d06030c0803070b1503070902 68
    0x11000e51041e102d000c02c82d52820000707400240800030081c4039441c40c1030707048803408114a45403100d240c100305403403c41940010f0300c042251029210b0600c9801a110128024010038900e110003a0412130070540c0c1c40b02a00d110a558214150000e40c43c015000e4142d039240f04940c502100751034140110794015004002d8254801000752810342800880200c4078225080d668410048454850a00c066136200b000305042200682c18107694030b4241c4030248150000003040288552000400101400302c100308084400034820419920b035502e00600040803c910700030589a038405440701d6902e03501c0080d110f41200d4111450601c0c01000c0c5030f00c8000c403080d0080a90501c00c6240010001554030301c24148044d00400445488180e02c000050000c2042414544585910001c11b0f18607540c28448829924000342c0041e6030f450103105800140c0b60903400900400011400043c05003000701c01400c3ca40d215076801e085590b6010304900034001c0d030018041e01948168028440091a6801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 199567931 1250 199566681 199566691
    0x30207060608060901090314090f100513080601080c0f09061c0503070501020a03050105040e1005100905011d060604030b040b060a03060c030c021603022206080a06020a02060604050c0a08 82
    0x40741c4140c0314201145018401c1d40d09840c240e6443c4840428181d00c5045665510000e8036468988480500002e00320818440c0f800c0c030a110070711012000e03a0080c13045802001300f0034240920300d90356168890310307240244160305031780c001d540c0681c1643c030707194050280c0541d0040038403d0540300c0c0c505000100d50400301d103605054081c1841c01c08254104007500c0070601c103a001513510300c0c00c0784e001000ea071010f0344803500a500345545d40f18801c101044075042c900c81100001a560340c5c500884d0b4582645520105105e45410008101d9060740490503030a010940030b180e0310fa48401d414841e40d44a5440702400004210000c40c0001c0c406120951304058000c2101c1600e40e100d4030364500b203545030b02008010070307900c2100c030048580600100e02c10800041c40a00e15a14603000718891814030f5400503d200c0317509a00303510f003402c0c40e0301c9000078040352401c80d0354170055440d214009600c0084580c1c09031040394000f0f155442c00d80252031003840352014072810a0707200d22050340e0244010f04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 199569181 1250 199567931 199567943
    0x4061b0f05060a0209150a021c020c0a0e1005090105061e070618150e0c01030203060a0e01180f110a0c030903140a06061e03030f050913050604050906070f030207 71
    0x950344022640030002540900350380b03030300180d48400890402019108103411100300102c28001e414100d41c010a000540d02d141392914540b0f5440000124201005039031041d900a0035444089003074001d82c103205210b40607d103c55658251280200054154248925a030042c0100300140941c402c00d1140409840c0d40514942062143ea5600043c1d4403015860b05444040649000034090007a0454002c5080b21108002220803518101d03140c3c818019520305040e00000443d00d5600c40d006103400400080c540b070391465031140303c02c0006c2803140350841011428070300c086074107440b1441200b282c00340c04240649400d0303c0031800e9829100c51002603060082c100000800305c2c2908920201c1d8403d10800b80603010118913100301250810f402c54060711200050200d94441d114090f442541e030141440d40045c1141c0e102241c01c0d01c5510011038100211685c0c202c16050f481c2c00641c010301c0c00b1601440140da640c4802680d030310040710440001000008146940f174026801000381702e000b80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 199570431 1250 199569181 199569203
    0xb0f0a0b0c120711010e010804020307060309021f09050a0906050d0b06060c06040b06040c050c06012706060507060605040b0d060513140c1f020c0103051e1302010f020304061b 77
    0x518005240c12440c004d840b080641001c41c125580e200307420440754007007401e1030501c0742482c0c2c0100b0f40e101d8103402440c05040c0d448030750a09640c1c0d48601e01c2c420882c07581803010721130001c0360001c1043c0c0c40c0c3d01c00c50380610500000801c0d80308040c060302040c0d802c003800003038040b102900d07886480300010f814680c1001c0e00300500610103400744a030303600c214003a01c068191410b1107001d02088880c0256240d003044420310401c9403400021981e0f030f0440d1003203030040590710b81c0c042141000090014188110a240c44070029030160082c01802086005840c02c000d01942c0700309000580300d0b11041070fa800b08151516200080340350f81703d42c2d04140480c1c200800d40143c5c0d5074031204e54036540103000c410b42c13014903500301a00d0f00c2245100c9007099004200040204d20b14061b60310040001d419040c5a102d500103000030008074240f55007544104040c069901f0b00035032068220449400903400079052405401d00c9a00001c00c4130b04031005540d0315040071158040100c1c0c024154a03048818484030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 199571681 1250 199570431 199570453
    0xb0d05011817040f090209120316020307061e080a020c16050a080703080f0c0c2e0912030e0316060815030604030c0b100302090c0705010b0f0a0b0c 65
    0x2440381c0d15400c208001035456146040c00c1404021442880860600382c1c100700034001e83d5100010002101c00502016071900c58110000d10260740e0141c118a80b44000b00c0d40d2503003440c04190b0400c0c814004e40079141c0e00e41d1201000c4461891041800840306031244840001d0340c030400c42c850384810f002c140142003034610000799040c074003210b00740c981c441304220b400c2c0000c0c50884c40c001e00410041d0002c0038a0740c51941c402c03002d40124025002d18681c00302d050700c0c011130706000300c4014900080c034042c0d030845504007c5c08480d0b00c8091106101c0e410440e4200d419016000c000103840140b038080510205a6070200c0e0f0150161001c143c0500810307000c4580074000051040140c907942c0c8402500b80352240d480000d000e1004000f5110f81c0c0444140000700780c1004204174280c0d0407140143d05907079459428100c6201c0d42c0d00094010300d0007800c0000f43c01d1000302400c0300a00c15030007130160b6108801000315800304a070044d1741c018050036041240910007030040c90600302850a4440112007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 199572931 1250 199571681 199571683
    0x10203042a080304140f0a1d100803030f01090c0201060501081315020a091a121302061218010f050108030a08070918060614031902090103091401060602150405030d0b0d05 75
    0x254099007800c00d512111005c3c5142c1881446101001918001002860070750290040a41515004962010200030803209102c041000014094040849981b8141110078481c02c007000d128404e026444c051502100d603106004030002c94205a48030906d40c0ca4074044540c81e510120411503400c102107900c0540c1c800d260001e050031100c80e80f640c8949500e40509000b80070781074992000c0701035080141d0200b4160380c800c60350700079070203803a501104482403000c12220310030359484820a4450800700044001103008044181200000230f0010409000044003500c500380651b061070341080c081103811078840c003d019400020b5241140000d9515028403008002c1015a900041e898100c00d00c42c460700032168600001c2408030451452601c80d2080c1070007100c1e904403445680d00041d4501d9181c0c4a504030500041d00200e02c8034001c0100600640206007a00c507020142c01070201800c0700c0c9503180300c2030b480740e40c00c00059031601409004100c010040c014070142e100e5110007070a000700d14 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 199574181 1250 199572931 199572937
    0x6230c0306040b3f030301060e04020403050a0605011701060806130326040b15011209050c1003050612030a021b031615080606040617062106150102010203042a0803 72
    0xc0d416164004c0342e0000b19150705105000c400d0402011699031a0448031000040743e0445c0c4140c0341c010f036074a01d4000054080c1c0b0071540080d00394414400302c0028031165034400c074101d44503001114074510710000307498280c81c03040c8228861a00440d0014080c9005172141c1c201e514440e26042c09200942014100c01e0303400d0043c01022401d001c0704120420074444540c54018843c000a4000c0b001a900024210a07200c08800c5195807680b48a1040100c10400395000e400010000c102070898400000c000304411951a03114a40c1542000d2034542c000c803c542c01c1a0103a40981036072807a810000700394801882d01035415100e80344031078052114464030b82c0d0140100c1c0a200b08400480b84004212050203000c0501c528000c1104100044c0c01802c11080f50b48003562405031030b5103900000700716000c4403818403200e0003240c1e1200041e0001240d680d100307140e003015039401d002c842c2e4012400c07400206c2e401080c1500030081c0d513100f41030309104c0da01416400c07140102c0e41929030300c156007550 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 199575431 1250 199574181 199574209
    0x1003060207060b01030c0e030d1833051602060a1103190201180228090606030209090603060106091703130306090c0906050a03080f27210703060c051e040306230c0306040b 75
    0x82d02c841c12f020080602c01050484031340b403030200d04110f8110081c3c0c014080203c1d00a104100014541c802c142c0030f122070081040d0303034006503626a90b03500d8070340c1948910111200c005510384000f0700058041e58800707118442d0080d01030703281c502003288a020406c0c08181c12001070002d1300d000042002c180c2c042d40c4060f00080c1c3d005600d0f880901c0c1803040605000d440c861194008a0041c486540d0000362007044030312228101c80c0401c10a402542103101e0020980c1028807210000b100384202a004600300314450042080a2382d0303180b038900d04036902400750315405a00f0002c1040403030000c0003d40a03c1040984803072511402100d13010780301f203002d40c00c01180281100c03010410314129040030a4241042c1c03101d1890781c80400d546444814074000106881d507100b40d1000c1c40b5200b0b5003a180210501c000503d000c0180c840700340d07500e81003880122a100d0410440d5462541c03021450b840d13000006034100740a8581d40160010343c1c00040005412a958140c844440e649003001c1941117 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 199576681 1250 199575431 199575479
    0xd020102041a030601090305120d0b09070807120b04050f0f0c0f1903020d020726160210030e0f0a0501051005010e09090c040207080712170f1003060207060b01030c0e030d18 76
    0x600304c50100f00c00b6072f00c507138103294800d00100c2d042206840e0440e280c0c0b5400145498018410181d4120340f100610101d01c0403908580743c8400c01900c480e0702e074203160160031001c1d402d10465a0350401e4180b01d2103180300b1080014000d20501085a00040902d62181d07510f04015040040207108413040b608040c0c020366801c0e0554000108440b0107071050100c101005d002c06140c1032803103005084000014800a000310040096407901078420b81c40344260350030103001d41c0d83c4a03851400082d80c4060660064901d540703000c02150241c0681c0a042c0c0031550b040c1c5850100c141e9680810800340c10023052030b03503036014030030800c03010356558801401010b03c294100c03900c540c2c0d1410708018003500c4c09984018000d52207104050805c200c0905680044c881894000c00e80d0346030881503411507145d100501a0f400401c4400c2000200d401201a6080a03070701001460110201140d41403cdd414170742d41c00d0380126401d40005032213403a00a480340049001c2c00384c040d981c0e540d020342c48586144400e0b0b20f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 199577931 1250 199576681 199576687
    0xc060f0516020106050105040b1c050106050316021605090a0e0d020102071b0303080402060f090603070504080105070e09070e061e040513050c0301060f0e0a0e090d020102041a03060109030512 84
    0x60480100c15098041c0c0c01e480200401410080080d01d40d21560040446103c40415003c480700c441c00c0c1c042103c91a0b031102400746581d83ca07800b40690300b060b00c41ca12054070054242e4003043c800140b89001c4200c1c1b01e813a00d0403034a40424005001c0d0094020418142c03108810400c0c00c104000e81c0701d440320683d000681d104414240254400ca910003070301c90812030b0359400c001081d80285000e8210b03404940c86a50743c40c14030059290b9218410149800c0343e400700c100130800d60801c003c1e02c21103664400900241c9d40c1c1e0001100d1350805c3c56101623104c0c40510100390014851070028580c0d40000d0111450504800c002d207500c40010441c10108100008080c800d609000c80d01da140c0400d060004d00c001e0030450381045180c0014010345041019050140c481c1c10310411140c03e0200c006003200b00303900d403680c80c1c0c50340c0d00c181150859118824205410310341c40c13052017210100c482001e21401030030b401501c010301651010741a50f04001c0e03844004400302c0c109201940d000502d042c8800d903 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 199579181 1250 199577931 199577941
    0x30a0506090f01061a030a02090102030c070e1602030903100e0a2f01020601060504030b2701050609330f2701150f031e020a050c1e0d0c030c060f05 65
    0x1094030b0300f0342c05c907020f141d000c2250108546001c0054980040301c240002da210200300700100d1550241c142084914401e10780001a22035841d0111809260b04910b280140400010240d0b941d11400752115050f600600c110503604016901045ca40080ca03015030304284007685508011540802118110000000c81d02c8241519096040c01142003800900038561402c80098814059440702411501103240000e4001c4a1181a00e0b0a10800d1003a0f1000c81d0010701030b03500802048840e03034002ea10450100d1600c40b0600108008910610702070a1011903c2c55034041d4407440c070960f6600800c3c211440100303542c6d118007103d8049001400c50b10501300405041748203000690000701050800500f55030fa444c0d020045062041c86828003203590900008403140036100300c4000c10380b21f07201240310012654060001c02c014100e05080701c02e5400381d03000c0400920756580d85040d0315408804440b40b800c0c0180070600c035070390190500d5804a110350711610b099070aa071403100d400580e076008100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 199580431 1250 199579181 199579183
    0x5070f1d0105040608250e012309060a0b0f040503011407020105060109030317061504081605060309031603030e030a0c1208092d03070506040b01091a010c02030a0506090f 75
    0x20780100400c5506009151400001949a0502150300c417810f000c52240c101034900e00040500052a00d0307110b00d0031940c0c0d10103402005c00b0204107000c1240720081c07040c0e960742c61f00400050250744003d00c1c0141d158a4200076004a43c0402c0c680720f52040188070014581e9020300c510440b011100715401c01d18548160000e08584006000906000c1204002d001084c1d00c0000030a1071021640d4002071900c0e21000201109490312406000035400034010400c9600419154601000185a00346003601c81d420840c090104070f031420001d90043c0071044c4034440e050165100c89000342070009400040900302c9042d03a10002c100400b08080c5490001000043e480c2c0030182c12a5250034020790504a0f90703036441d50400035043c040d20061101e80806580c05040200207041010200e0740d0301e500601d03004ee1a5201141d0a48a455421000040c0d112040c0500a5482d880d140380041c4816607030010340d48500c01d000c0036601071240b010510b0014104001840c051200301004044800d9907500351 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 199581681 1250 199580431 199580489
    0xe03100504021203030421110601081c030e1002130902030a021201050f180601020f06040605070806010c170706090b0411041112010e060d12050d140103030e090405070f 74
    0x90007644c41007081001081031304a03108460358048a030302000308500c640484110b0032890200c03070540036000000609030400a220a41c0d102c0d161000020003592036402d90032510030000881090300f2410014000204a038024545d01c3e0fa07021052042035225500c01089030812203407441995400201040c0700300e0700301c03001401040121600b001613411040880e14030206c3d111981d24001d801e102003200f82e0f00900181441540017030442d81149810708003800684001d5840c1c401040207a0081000ca5200381c9000320340340d40044900b0441d500490703a0600c00d52000c0403d682003036503140ca55001030f4600f01102d0281d030084091141481d009410841207551a02441c2d98059040041d010040b041c103000c0c50440d002c122018101c0d94889011903000d9003407850040140b070102c068800c0c40758000c800361860034000c402c20044403442c141d8148141c00f003800080e01040b001c49250502c3d00c0e1400c01c07240e000b0310580540d121710756107866a40080b0003130b4000c1d01c019074103c0890a0401101155 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 199582931 1250 199581681 199581709
    0xa0e041518080d05060a211401020a050d05060604060203042114010e060f06030c010e060f070f0302070803030403140304060605031f0e030307080402060a0507020904110103051014010507030e0310050402 89
    0x301d40543d11b4001402051f4012800707003611003030001000e0b4103021140124141400c1c1900080d50f941c4401c100060840d4041b0081641c0503190401090180c10a5070075241501c010750003d603d02400d00d50b01c103141ea080c800c5444031440c0e00300d8000b000542c29010500e05003940000224002250230384441c1032000080080b4808440b00b001c02c081994002400d4102d01000c0c20203a0401d0200d03404a1003900c100350018500b00e800143c0d02c01000900d806d899a04c901035402d88500b6a1544100d43e2a4030083e036000d000120922008446003080100842d00948105ea001440e0f69580001c6401d016401c0c1445504290318aa00001d001c0607000301600091280c029500d11728007150050302e01100940040e006200c0820a40340241c06002150100c680080410001c1d14052900082c044100e003031003400607041001191504071035031001402c1c5d03602e440b041c828004490004403201e0300314840c01d404000c1c100d2480400c1d03440c140b001038146c0e1b000000c00f05483c9403d0040c00b040d00c0c16146 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 199584181 1250 199582931 199582939
    0xb03030d2705030405060d1119080c07020d11010c0b090f0c030304030210050310030c0b0d3c090b1311010c03020604030c08070b130b01050a0e041518080d0506 70
    0x90700c03000500210490f0140c903400c582598540c000f07410740100a2030307000e800381880c410002d42c100442e840b10410030900000e56075124000e41d00c1860480c000d00413140029040700d0407210700300000d4a814002c4840032818035107014a048903407a50704000100361031224a642082201e1548100e00b40014120044190b005514040c070716808284c107048211480713800c02c500030010680d0b5102d12051180259048400f809103181c417064101c80d01d50050302c44007545450b000e803091000000c4505524a401e4103d00049a0149444509010050044082c171200c0e9a021400b0010f0303080c00c455401500b0b24420604d021344039250850b851500790020b641800094100f10000a1b80080d010f80c0c040d905140000000701c3c14030300300259001340c0c0340c0100012044c60400c0307980c000224030010180d0007120300c04426641c40f010f102c1d4012083c0140c5801e4419600014045002c0c000000c076a0b50300e42100040c5a5110b1400c401e6240d0908821901040000390403884d00c4898042c20341c00c060116 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 199585431 1250 199584181 199584251
    0x40209030a2d15050a0902060c01020a020c01033b0a050c0909120a03090501020714010c08010b040807030201181707030302100501060804030c030309080d060905100605030414010b03030d 82
    0x10f261810340c02800489a40e00b561118001a01d070300b5580c01521071158042c1c1115160504421020f020b90004d00005005200d0121846065803080c000c43c007940f040c02c8500801c5c50207000890802c08007000d00100c8011410100b01d03a810020841c7c0030000d80680080c00070070305078508104031008003a0412441e684a80d0300c42000c2501c0000b11380d0110b02d1402c000502403043d180c0340d030290140c0d540203083c1d9200140040c208000c1908071000c8150550f9031064141c0e00d03a1030100c190b0195004114907984010b600384010b5001d4241d50480070038103203000d0985a1741e1040862032000810029041d40c0100904000b0590100b21401208030b0004040c0401d60501900a0184800500c05002c00c0f5080310004240b50095110070036291704150701a80e141d415407050809041039104203d004d52601002600c20040c0f100c1c080c050b151141d50312451a19642c980d1401c80c00e9010400c03406541e14070009105640030801054945443e0402254241060007040442c840444410790414004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 199586681 1250 199585431 199585433
    0x1030605090a0204080105151c050f01090b01050f03070e0a0218100e100e01230c07060306061209080409050408131509050409110415092307180902030402040209030a2d 74
    0xd60400c6400389d072040e89102c41a022401e00c68038211441141c10f00f10b500c0c09a03001d051081008816050390004d880180d5800410380501d5640c210500c10f05854050701030108003902c0544d0018044a032110b0b900b50f0a161200c80007032045036840d1624001b00300000700d200c4007410026071103280141c1604150141020000010b013011210200c0000d0445070031a0590120540c070055482030340b540400c4910458560386d0240c02080745000701400b250080e050704858540d50f000e0328030030701d07030086165042a2038500342802914019204131880f1105014010110041449000040c46445403030041c0d90248000a07080240c0303a0030860069062401207008100c5c18007a80f1084401075400042c000c0051840e03443c4544140c01411443d428207a50810706424804c10043c0102e0051040140743c13141c9005450114000c090718a625507115000c000c201031030b90255520170f0000d00301529090f0304000190600400e900111050024481c0282d8030340d001480741002c3d100c120258400321105 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 199587931 1250 199586681 199586689
    0x60309030304020120030c0106060908032106010c0807080304020a1706040b10090c020304050a090c0206160c0f0f0c060206060105090904050a0507081506041a010e01030605090a020408010515 84
    0x10000f9042c44100210191070300300104500d00081130500c15207031a89070a4036118080c100070700c100d60009207149400303d440359010048486030400c1034101a40c2c0381e0703000c1100f4541c0c100208a02c0c10b201840070301c000810004801024100e202e500c00540e03a150900c10070008c43ca150f0000d02020940c5138000d20f90a8000a0300c9410036040042600f00307548080301c12078007201c203030005110302e41032242920506070000050000d840044540310210b0fa200c501c4c0800712050046050016070201021512102812814800050a0b442d06010001c00c685840c05a07640d105011100b03001086844000d101c5a068250042c00b00f5201401c0d841c203001f00001c09038040c05070054030030f010341c101080402808000001c10303940e000054601180e90780d104661100000c4258a459113400d500280c01c91070288100003050040b00c0100400009010044034040720101d601414556913040101c0e06603240301e9501d10816410783c025070f0715810b11602d0b500390740018001d050054042400c8131f8a07661 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 199589181 1250 199587931 199587937
    0x1060207062a0209180d020c011407020901030201051b030a0f17040b01090216210f0c0203060a050c09041a01110304031a092503021c02030d050307120f0b03010b06030903 75
    0x90100c03080e0f04182c403500075071100d0506115491700c0390310446000e106419000314483c04050006d894107500c4180107000281c4511504500035030095550380103000540c002c00103040381e0085111144407440903009031030b1440d030085a5841c00316203030240d074209403035001c0002401c483d00c800c0501031608156803910107180c0103001c1e142c0d1241d0003051f83c041c030105100000c038810760000c024a0005810741c41c8501c0049019191000060301f035056490b00c41d0284031065811035010b0028012640c907031596100404029200307012544003080603036001e507514000c91000100b00d000a000303401101c0000750000040d4250303800190003d0008001080c841e0043c11441210111480c00695440500d281070015401811050340342e0001e6551058011800c0d5505580c03080d03c03400124800d20b00e80851800380e4410081d8035038010b004140388184210044c0d80c000c1a1801c0900e44c5060110302c040a4440c10303400c207071200f590741c1c10811461a00340525000808152002451070511039040c03900c0c0c1c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 199590431 1250 199589181 199589183
    0xf0b0703020714010e09010e0406060b0304030e0405070504050d030f11010e03030103060905070308030a060302030705010905061b1f1a010305040c14010c0215070201090602010b03030a0305041a01060207062a 91
    0xc011006100743d2130340500000081d0b08801081c0840715a102c6041e0902c10b5410b850030307240a45060004500c120031007080700d00458164640b107452000c8402004040c0ca03004001d602000f00600000920380c40c0c00f0380034a0094070075151180104100c400003450001c0c1021910305a0303062500702d0a240c4c4000c0b003182d05594000202141c500d07400d003806440c0540781c0c2e00061075040c001013000341840082d88001c0540b8400c50544046950302c4004681880407030284943c0020304004245401d03030100d4840700c45250340350548944c411024500c4120080096101c1c80241d207036221410008554504801c00c5602420100301c80c0c18a501d900c0200500c41c042d03040c449400c0440d41a00d81c0c09105000c00e031b140c0c01401841140f60a580d88200c13a000b10504070301140500390080743c2507006000d00c603245140500250b090101500049010346800340040c1c41941082c10004140d51034101c0607800707003005800130702c036a80c42c05100400c14600104c290408200d0620b80c403881c3d030f0117814210703089 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 199591681 1250 199590431 199590449
    0x5070203011506020703060f02030c030c160b0901020c07120503030105060307030e060103150b04090305031314030c010204050a0e01050924030d09080c06041818060e070f0b07030207 80
    0x150509102207030061003a8011803116090000340041c41680c00242c50050768440c40d03051114481d1034040e00140d000944100001000c244006810907a40c2d0018145c0510ba46102c4101c40303519444d1030525980995039440140d40005200e04001d50030864080204800151454485416107900b40c6038003060103507a125900000100300318501c2600404000c5266006559841d45d5030f151021101d080a40c078044c066042c00e100c1c40c007901c1d040c0b023000205c4e030305030302c1e000d24554030203030fa940300e1400c419000c03150b504040d48000c452030810005003c450940100050380c0da414001003000000281d4480350b403401000340103200300e441d0041d180743c100550f2041a8035030f2190f0f042d4541822120342060307415225201148805d2a440104a001c48203040103580d4600740c0c080500040c0d00c0746004200d183c015562081c01c621426501c2035158000082c000890303288035039100e00984070000015900b0350b10400c010b0124107132001d800001044d00d68002d03860f0017565076019464079031a00c07400c804 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 199592931 1250 199591681 199591687
    0xb0c0304060f0908150a0c020f0c010e040f0f050105040506030601211e0507090b040903050f070206070b090c0f0108150f060f0406031a040e12090a0e0103210e0d0305 73
    0x5004181c000003070708920081e22981c40350100401701c0000d04544083c200d0342089681070406002152030014802e200c0e0240c180e1031003079001907540600603e16a078100c0e80d10b03d01c0d00c4c21118a4418060111041240403a055152508005c15507801500e02c0e403190b00a03600400481013120080c10007901900740404021078181001c0d07184a1103e810800011030034450b20301008008510381055405c02102000032a07007980078007088400303520006000c42c80c104200100c82e07c40e000901160340c40209680c3ca05606a0745003402031000f901c45611551000700d2040031898400b800c3d4512890038a040342d10b91030b00310b6007609994000c40b0b51601440c03000003100c0842d01c0d050201c2d1741c2c502200d03507456503c035a180c0c4010010990442c000a04004400003642c80d850103000d1120080701c404000c1c8542080044603454990000b1115036200310f071310710000f0742c11181032101070080d8018009049250b01100d415100000c0011400c410420010300080740340e51500034182c0904c4c4c06145c980c1d2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 199594181 1250 199592931 199592957
    0xf02160308041e050a0b0a06050f060706060b041707060507020901090c0c0605090a0203010b030c0a0e09030702031c08060f10050c0a020901031101090e070927061e0b0c030406 77
    0x756407180d402e002419014604183c00034020300052009002e44a00c840f103043e070b940c0c4041001203c51900403250f109040180c5c24181d031800c640039100b0280610400109541c0e640e0008400d40d009038409800030000d1150804016000e002160041501c1d06007189400c200750300142900d0014086c0400440e541d81c41c4c140c0082c4100c00c03070302403a91b11079001c01440c00c3c59406a50749044031002280b2a42c20b15940b2816420040ba1090b0036a002a060710f015074100245200c5216004128002a100c24410702c009039500300b02d40d0004140d119403140d9840c080d11002011104d00405c010301807040040380c5410340d01c0c0c600c0d102914050ba0b2420589440210b06a94100350304120007a502c003002100220034090903c44400c891002621584035655407114190100b07001215544003207280c401003004401ca450108c06a43c00190300600619043d00e0081011195282c01016041c40d0803500c03054070503105030030f0350050090a446a4180781017095030340c0c0e5910032030140e901048401c042400c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 199595431 1250 199594181 199594193
    0x10c05031612090321060506030604270f170a020a0204021305040915060806040b01140a0312080601081e01030816050307030815090106081b0f0414040f0216030804 72
    0x55000c00c00180c043c40004520704000b08000e00c00140d000c2c3c2c40741c05441c0c02c0c0805c401c0b44290000c031003018040314156561141040000c0560418103c0000500405121816210860759920707600c504400300540c003039414602c0018064460000643d002000000c0b002c94000941c00c003038580c101d40c0035075150f01d241c41403203000c0110b5120641260a12403198100086105210344401071664100011a0342c3c4038150340e2140140c4001d0450f0240380b0040c03000004256091130b0054016107404016a1341e41d40d010700c00e00e100391001d0000340c1d504041c0802507034001e900b81e030011403036803100040c146684860340c0710720010b01c03000741a80e030000752a4000c0d001c150319601e241034201e0240d9807540d4a0b414042e01000040b030300702402c41e2216081d950a4500986d206060710811b030380e240f03d80e46d103014848503076841c00400b105a4407002d00010324020180381c0100040d2050f0b40d000b401c3c034031603202800240da03c000e10003113a00f401484a00112200034080c9401da680501e41000e8945943c1012 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 199596681 1250 199595431 199595447
    0x30201060506040b0903060f06150309071703120c031612110f030406180c05040f09080a020c091e060d081204030306031b060e010c1a0108060711010c050316 69
    0xc0e60b00140e01080020342c648107000a0000944190280ca44594030550440300c200e000321406d0b6400100c402c24401e078040c05a010b594000107040c12034810580b0b880418a02a0800190103200d0744001940d0440d4840c4071022600700e41c031161847e0550420741285a410382c104082c5004200d41a403991004640d150416610340c0c0305160f00c156246221a4a400e00d036001311070a80315903040c2282c00342c0107040e19000c800255080980020114108010000540000310000300a69240c0c004940441c1d182c4005001c0450750b5001000340c400f60000f444102d04000303200d610602c50b19602840c4010030920015032000c1e04842214003083d0314500018a070151480600301018108200700415030141c0c049010b0300d000d02c0c01c0080206054041014144481c0aa5400036403003034080e05a5500402c0b844048600c20707041510381c2c8070074080c071000c013940036880013a0562108003406120380d040391248180c40d440750005e001003440d4030405040391001824000c80c0c00102c284c00c41c3c0c001d1060504d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 199597931 1250 199596681 199596689
    0x3040204143c04120908030703021902040b1806040f0209090115050d020f040608012102040b040b041b0f1704023a0c051008180a02090106170703090807060903020106 73
    0x4200d0a6042508000714003d04d80c400010200c0c0440c100400c03800d0001054840c100d51682c02417002d1400c40d2400c40310780410013000c9030869190f4540c85003542d40c12162460000e150041c0405503d40344080101b91075118421680d154410441c0780c0388e580356101500d0549070300c0681a0310100000c04112501d1040c070b2202040c0314804200880000c00070001031044690316610103030b590340c0700c40c0104c40202e2910130b404030b0235040441c040010f040c150005113058000820002ea4200804007007410f9503000a80c811042e52820031303540b075050300150402c039403448620342040803d6200d5205070a501000d070020344910344900005448a00302c162084490703843c10791000c00c002030358141c191a480032400407500302203020b1000c41c0c2828160941095000e5640c2c507008a511924901414542d0702c800c0d81103540940900e40015031031f010b1002d8024140d81d910042c59145400025998420150200040504102d002c0700411503c0054800c1070350410380005040b00140b4040e801801d513640 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 199599181 1250 199597931 199598041
    0x3070b03070503010509010609050310051807062105100311060f070609050d0305100902090d140610080102160311010f0e0c011202031012260304020414 67
    0x104000c0d84582c03110145049950960b0181c0099072203490a8407c0c4080e4003815800d584040d5a0001220311600039a03000b101c820100505184070301c138010f00705459030b0001e01c041587c400340b0b810141250402c1850400f40ca00040045003481ca2446603050024440900310104800c0b4051980e5201e804403050030340c1e01002e03c7d03501c440502d0600064840c03010141e5060150008406030b4030b00a0203480d02c00c25101c24240f101c2ca00b8544040000d40105042c45d80100d1401c0f000c0000072a55003074586404403150052800d0310b40200b55425042241d00804607990052000703043c080703d00749000003490740c1340c20030350030386038000342c103c2e004041c41d28000c9003460a00d9402c42c40384201065040002e44280e841040c02c4c620f40d004181030b44820b0b01c07100c4102d100f1200070096020b000303e15911852042d40400f80160400f90a055101d03030328001500450b000200780021481c041c411b1320354148540004d112949002000c505105c50400703680f08007440c03119000d8113103a8014203550483e8420007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 199600431 1250 199599181 199599187
    0x2030f03040b012402061602031201060e09090c130f0b101d1c03050304141005180c1302030a0905010609090303060503070b030402211903030b01030606050706050603070b 75
    0x41003000d0502c0b8203100e003060314203a00e01080300c1d10911103041d81281480360020022901c0d070303062440800d49121000400c5000600224040c840031a104600819099850440240b45002044111030001e07044815a6001c034444007441e40381c0c40c0c40e0300030304080d551001038500e065040b083c001d060b41c2200340d98445080f41030216030940000000b40d4102e401c80c1c2080c1260842000d00107a029114402010524541c41450000e0300c59001103900c035200b0074400c21020390780303203d0724642030a100103d40c0654036107042040008880c0080f02c10704800344c00030085209081d0200300d410400024984890341c002000444a0001e80c10083c0c031743c2e40c0103001b003140070740e1502e4480080c40d80010442c002810080000794a250015001c1d041d204010083d51540c0c9560303003040b006408071107001c0050031440320700005100b42402011410414100380040401d03c40c0790050840e11030449841c14507140c40028000c29501c2030590b00042d0b881440042c040c1c890b14006031410519a021a076000800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 199601681 1250 199600431 199600433
    0x504090f05040606050105040b030c0c0a05190209070305160e03031b0304090e03070302031606150e07090b13120c0e04080c010b0303030f07180e0907141f0f02030f0304 74
    0x5076102501c1a4020081004101d844000440c0c00b84100d100305840c024080c008120100751510003062018510403c44921004039504c0c2e41c10608940038007501201c0746002c6a0030340c107121007100d60100407490200881c1c0b8000c141c0d00701a035005101a02009402d2180c1d1081c3e480401c11510011143e903000c1d400f044241707200350b03503941c458040d14404504151091201d1032001081c0c41d103041c1d15801860501c902e001500e00300c0690840d081c0d13800380e200c05803055000325414049010304110b2984111901d040343e4003602c0030350700c1d90041e4030855041054041804501318648165110303102d0040702c0c1e940c5410040a0070380c16400c1000c000d9002c0c4103000c20030a12000404800380740c14020720071007200300200758903800100e8001d001e0803070305000210044d20408111058403102107464085a85944504002980407258041554084a01840b14000f031466948010200722800c444083d03402402035000d054908541045c0305c204a041c0035154024829100c86000c444070198a030320345 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 199602931 1250 199601681 199601711
    0x3051210090f1a0604032a09050a0902040507020c1e01050f0a080910050402031b2d03011d07030204050712020d06090606020d0c0b0612010e0114010602030a12020307050409 76
    0x800f16518070a0040303281c1c030140900b801c0c01030354100d07500716002c0d0980d81608241c042c03004464801c0c10015101d20080440c07642010f218180c0603442c01000002e95200a05c1484110760002d0424010b65003c8801089290380720020410403840d141142002440b0042c01030300c2c54090401411003841020170701c008140c3e07020340740512a00c2d5003400c07a01d042c070b50603080c141100c00079a0040d4050700400c9143c802c9102c844032140c052103018000d5000f80140030a06800101c0e202e49000480140c4242600d003460240208000d103074292030140000360b50005950740e529014400280110340351000220202d01824005400e0011103c0555480811a0240000f040c44d0701800c4001d920b0004003103142407002502d03250301d262544800e00718840d580c032000860034006000c40d07840009203624008404080c0541c012140c0580c2c00803401c0d105403040401d0981c03050f0480710840d4024080c58001941c4019401400e40e00d040c0d0050741d907125260204c9152056401101e41d1908120000c0d1f1b240803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 199604181 1250 199602931 199602941
    0xa06020301031a07050a050a1407140c01080c1309090305040e011502010c05040803070f0501020405030106090501090c2c030a0f030804030206060f060d1503061803030f0903051210090f 81
    0x118442c2d00c5211070340c0704d90341039529005440c501d2000440500c105c1c0030403801610b0800501812222081c00d205281d950900030b142d985004e00415003180da800385955030008034a50308002d01c0500d80f0700b4142d8900701d030101802c051040042c815225500c800c1458007510840340a000400400e064540c0c46104140c011a00d030201100158600002c12104500c104181d070141d80c1c80001552170013045840da410407810000081e20b59550800001400350b5091103002c00905003080c001c222907140002c29401c45070107860000a010000810800417404000844428030340d0006100a001900021906d045081100141102d0490010006160b088418644140d12a6003111020b40e038030b2091105040c403410045400c50424000348400414980100440d03400080c1442c0010b6565141c03541a102411800c510247c0e582909006040e13050280740785074104c490342400750f11820307500241144105040054500d030210041211045140c0454004209204003400388881010521780100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 199605431 1250 199604181 199604213
    0x2030d1d03010c080c1308010c0c0c091505011215121401110d0e030c030f04031b1406090315090129030607110307081305090703051005060c0a0602030103 68
    0xa80890300584034581409040d003001c803150b88802c910f48410308070721845d030844461040217103240c550203c0c80c03080922810075100c5440da2080865126810075007206001c0b50803c0e100e8034100144c10100f5644441c110007114020310340440646400541c00d801001d00e00e40c401c82226101000180c01e40c055400d141400e40110098a494801c010105003203a04507295440e02e48024807120542c031040c0c0c0d11080b11102c440040c3c0f440c020110007000c4c1590700015920b4060003000c41c00384144112011812040a401031803400b006007000d0b0105104030340841140e10078400065401e90b140c4091003500c0318046d042500325040c5c01d110401c0b601a006031103c0d20b56100d000c001702e80e0945e28600403001441d078040e011340360544401d101110b14040301d40ca241c1c400d01c010810000051140401406030f10203d0510381c0320b1904080400c0701525000e080700003018100418050106604815401181d1301103840d999501c0d002c0d80c032a1308082c1d04080c00b40c01076201200000a206008101c15401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 199606681 1250 199605431 199605467
    0x80a0305040504060801020a080705031509041406180c0f0616030801030203060903070b04080d1803091d01060e01030c0905040603050f060105061207030509100c0f02010501211b0302030d 82
    0x1035440b035480c20300300d024522340c3c03030001922900814852802000196080814545c98810110703c44001c154072400907181118900e1003040c00030044213007800840d4004040d200350540e100384503600031744d80321070035a4040d226080082c80108960b9900044501e4641c1da0008895111f885080c046d000a809200680c000c0c060000000d184130808030032140701c194000300c1c6c01042c0c1c44a0302c030b00b2a00e400594030010490382d60304284040c4c4110400070844c10781301356078480030182010100c411110303007078014507035103002000103120494104041105695080c41d00103644545940221201000781d8803968000d443c03c14003106019010991440c4564005d017114241e90341c0e05d09004480c480c605591420f0040d8201242d1618420381100f41c024a00310103c80d010a0031901e0b09088800082c80f0340c0118203d03501d6074951540a000b040d00504141c14940f1010803410302e484101c58800d4801840880250201c244102140300184041c0d030f0058100d40c6100c40221002c1c017503d060308903100035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 199607931 1250 199606681 199606691
    0x50d0c030912050f040e13021f260a0c0e0603010609080708060f0f0403020705150a0318080a2f0a0302060f01051822030305060a0503070e0f0c04080a0305040504 71
    0x12003806401181c10194a241030180340601e4002070000480d005810704084001f0500107d0140e52103406110184a00981084644240b51005481d905520590006802444402506290000100941c454203542c0301007071000074042d04441007181039a0180e8000004070011519540c03001c8080f041e2040c502c11203441c42c0d12480710a94a141c1101c01804403c1a240001c0b00400c1350380c40c40d5080342c4a40116107050352528001075103041d1500001800403004620070700801d9060003205008d416810201c885805261202a030318401e40c0002d03414070182a8105e500154590340040c440e80b0004424040504046119510346401e000158018800c0402050701d800d00100104c1c1226001882030321110440b03010415500d00050691040074030303001814141031814044001035a11070340e40083d403440d1a8040000c84d4940d900084e00a0b0f000490500a0008484202e07030080402c0314803d0719542c600c236900d12284540d030040c2140d0300854818008160b0400050310680f071003145c00b444 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 199609181 1250 199607931 199607963
    0x207060905030d2702010e01140a08060906100c06051e040b01062304060c030e0418050601080a020303120603120705030306100c030c0f0303060b121e1015050d0c0309 73
    0x26a40c1c440c00002c203e044e960003074000040d0300600d04000b0140060404154070540010f040450350007031503100d004240d1580420101e03242070038420754080c03001c0b5401c0da00c0801146009107880300071240106107607035420210b84c01c0c0c810360b00c24003103c0784296030182e1030b85407602c0d2022561500f8494080480c401c0309488400303441c840c100f0040f0904a99406040ca4a4008200c1d00410040415414840504100b0249494502581c41009601c01002001901d54980a8541581617002c24070b15041b08002c000143e501000310350801116201704165034580b000000d0402d01006a41030311200005480320410030302002440c4520380440d100e81d40c0d460106401e03106508140c3d0001c00003000000588001040b1036013901c0014006d140018145880e040d00808030b50003548100f000c99401003c11924501e000840c1c0701840900c001800d29007400403035100c2a20003406141c40103032002000310700681c4100165119203a050400b0b10a041c0000e00240041003409002d484605881103154 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 199610431 1250 199609181 199609211
    0x4020c031315140d06050d030f0f080705072003010e07090c0f0c1407091509060b07020f011101090b0103061d01050709090e0a080a260601050a0507060207060905030d 73
    0x901c0031020b0703203a5030030240f01407090181070b80c40740500c00e81d4503540c1c907008204d40e00d40a0600e00882d10a4a8a10500c0b403942c101524030f040b10000d00e0100300c0160108151281d1200a03506181d50207200c0c9260410000c40c50509182010081c07a0158070b0302500321841e00c80020858100c4600410821005d60405001c4450410313800e803e5020480510aa0340003076a42e4400e44124410182911358241e00c03500003100b078500d0001040203401c90030100340404c3e0424818240104a09042e442c604138061303000ca40d032100001240c40c1403002100c420b0b0401c000039003140b091143d0005e5408099a102c5c5042e4006142042c2c2c00d4040d1482c01c14a40c0f21081c0503c00e007405807103992182c0300b4141c9040140d5000d80750f00c400e020514000e0a810303400158004001d0500c245258030351070714000044503040842c4109040792080700400c1401e0140320b0740c10100300c541500c0d4a140c43d43d9a42c8950601c2000781c820042d00419a9280a1018050040100203011007000c03042003407212030b940350b03241 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 199611681 1250 199610431 199610459
    0x3100c05030f1003110d1118090c01230a3507030c0903060b0307030c03050f120717070201090b0d0c110a02150a18060305010f060801080615030c04020c0313 69
    0x34000034404003420170398600300c0e46a00c502445002c88090018450b00850b502908c001000c10700340e4006414400c00c200d0034404030b2040a000c2c60030648010005030354403241c18642c00354001070100007a605c10000d109140c40c45080c0c0d040e00c2c808050581d000c08205074140985164100454600c000c940002d1190042400d412400d94411703a081d41182c84401c0200224401d96a00d881001070000004003480c00490003180520702400f8004030801a40d814000104500503030074400f04003a50004600c600092000000525001c1d160f00c034520040e900180d66402c070b00d08440000c0360034051001d154004891000c8560b1b0342e520700c0d0300d100c062190340300c150a030020b61050300c1d41d9100101c20f1840c0d026004401061910005889001c410b134500031244e500844c00094584005001c0029180300420050259152000d42903141c02e844c507031580c0340907003846070010040304080c640f558100011540e2100c010021903555181010003a9240e00090300c4503c844840c400c0020748140140c50f0f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 199612931 1250 199611681 199611683
    0xc03130603020405060304141915060b0306060403080a0903022d01080c120a0f0e1b0303130b0a0e04020c0c150301030f0b070c06061202040e0106140f03100c05030f1003 74
    0x401d0443d00c7e1680e541c600c2040c021000324182c1b0031010209101420b03601911400e0780540390700131b5171304c40c016484400e680341e030b80080300413160410601c049502d0761002c076803c0f40e0b00a0411a15202500001c80318240240c2c4081d40c440f29201d200041d0030040400003114a01c09401803074440d09400042d101344404481c190751601c01806608500703020084035650154911500203080c00c881a914002c4036949c0203504e103160300101c66081c0b44003044e82900c4001c10101d000f0341c105070707a41504507036001c914003540407074100c08146601061f0040c000e54425100091065489500d140a4107070740314000004184500303003a031524845480c0c2e1400302c0f816030782c1043c1c648c0c04c0000a51940c40c41500064904002c00c840c000d00000807941700d1090002505065980c5660040c00f4010481070718440884210341c0c0e454854200101105425400c48488054440c001000003800009040c4a2900e00c501621420000c9022003a135100f0b005612488071003c0d966260380760161094150300080c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 199614181 1250 199612931 199612939
    0x2120d18211e0e0103140405030c10110403062409020c0c060c07050607031701090f112b061d010602070605040b0a1202070f030c030207050d020102100f110c03130603020405 76
    0x1002c1c220891180d10089501a0f040c10049060f40b414490f03180980800c650680e519000800d0400714400d00b40001d0803803000785101407007801d12b15403240e030981c407451200034580c45c1c2c0c2d90340c404041c0641450052a240140440e01c10850f90380304000040e62181608036018010828240340c40d18020307003a5040b9458020007070404505000600410703900110080d0148015248228408804010110301070a050203011509011203614603003074079684076031100c042206000b14155854a140c949103020407004940b96161170601c0c20034000c1a4a40156500303600000b041400040c40c150300c2c41c1200c0269085071149da544110403542802a0300030290b40a104110303c2d03c0040c0700342006900f02d0340f450703c0185080069030340c4c0308114549540c1180484c2c0241618001d140c2c041c003015004110550700c030f4118004642c0000d46030070203d03040380205d0750381c0c034401900715500da07000491465045907641c1d60748040c11409566a0001c555049000e0005807000c11224864000d40d421200701074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 199615431 1250 199614181 199614227
    0x15020d02030d0b01020a170c0d080408070204090201030e0d11060c120f0703060906080d0801090b03100e0106080d17070e100c02030c04020a09050301060801050702120d1821 76
    0x42d4901d000e0082a92000d0443c841c52444e8000306030305000c003200b10080b806480b9a01d40c03010640c103080c080800000c0301130004482c10840414001012030345ca00754101d0380003565107c40c2c40140c0041903c100700800b02c5c85120345600340560000c244060322450241111015590040e0007840d1f071055584c08003103035010f14040342804002855540d0800311074140850215100d41050007119280c3e440315240d98030032480c2d03407030356a008000540500000901071156440f1180801c2d5100407645480003666510050b13045002001e50251026250110640d8245100c0190043c40c059150a08080000c03c0c04042513506004290b510210711018009113030072020070606842e00c04d0303449003d03a018000c4040d0180c85940310700c001d020100103a103400600900700f1045c1400c5030100d1b008000581e14090901112036000504c01d04050b69243d03465a58590902000002d00040b41510818000780030301902000a0003400a040c40c1080f0300035080c40c003003424101c5121624001440c0c4c014694 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 199616681 1250 199615431 199615447
    0x609120f0b04050708060f0114010c03020c010c0807020a17060a14010308160c06180501050c070b03060613181415060c15010824040b0a180605040c15020d0203 70
    0x407415030707119000300155400350307968210090514100716030055808402e4001401008840e030900200c0070000c0ca000c02c00c4c42920364029586200e2030b00401c5c11700603106400c204100340c240490742e0240e4051302284082d9981c4510310056039403503541c0b410501610000400b00d00b510b1141c0400c501c6084428541d6034030310749490003554440c0c036600b0501c0b4192500c8001095280c000c0000400c00b81c1c1d0b9521b040108241d0084220b01260042410054208043c144003000060000107031042d51036290b03500c0e22a200050602c0c072480c510340030aa0000e00c000201254000c1080040c500c0100062080c03482d003180210680c44100c809403a01262408803035020304000c0301422002c48200c0071100c80501040c0c504440c1c2e00d09074484270403503114007807000410845001802c1000740802071030034541069915009100c0008060000b2680ea07800c120a12141070104e00c0326041c0c21841c100800e041c00c0c2012403015a00d401050a4a581003d201c0502440084c40b0103109900764090741c186424 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 199617931 1250 199616681 199616693
    0xc050d050901050d02070507051002070e0a0216020901090f06120b0a240b04080706030e030403030302090a180f200d0b0f12031801030b0d0204240902040609120f 71
    0x4406814104142440409100c40c058030086c40e4490251009010749481d150401040c04a80c000043c11508044410070503000e814681d203802890b48003025803100d00002503114880a2186c000c3d40c80203188000260056656000d48452400c58109024a03621110314440c0031611500c01071125005400088000c0e029610408138250b03149000050070000311610840c0d80001c1d00440d1060f240000c0410030381004000040041c911810700b03202e0850b0203200070f912801944401f0f4149030700040c1e01403540da0740c01141005400042500040ca91317003105000010003600c0100307080c0a10740440310064404845000d0001207031203101d5490009114408030140c200e07000001e400418404404800b6591600d00031003203802070004541321210140d01c0800c0d5164103011074141351900008038201d896048002c0f02c440c0d01030f10003150329101080035016003034001c99070305c1007100d4800c0e0105440840750020411654240c0c1c2c1c06201c8c0b91107036009004901f21000007003004c1564160b540001314 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 199619181 1250 199617931 199617937
    0xf0605070f0609061b0e03010c0905120106091b0f0e030607030e0106030b070e01090905060306040b041a0c0405011205060a260d0f0816020d030213030213050a06060c050d05 76
    0x120030031003c140030500e6541c56050390048035413020801150802c08602c41c0e440505141c1c1c0c941c00318000c0c4200901558090b0284100e070140b1400f070b0609071500142910250000001820b10352800c1203036403055440c1d10202c41105260b640000c2c0a0200a105a449a1521865074030002e0141106440310102078004081d40d0344c2a008554845030004049204034501c4c17445a0401d4035010039800c04000014101c0c141c6da0840d9140f1031800007800110707103000420a9006902078500c0506450701d05050040114044c1d01184002c0303500b0800c07025035141c0c0301801c03c80740c0a072a80d442041d03103003c1c1e20341903690446d1402d8200280301340c2000941000c2e07120b0690110380c20b10454102c40f180c00024104000b00c44194007080000e045224000da1010810740d00030780c0007d2414950f003c8a00003034548418441c00300070140c022508030844a9604114801154002e01396031a0308003104418000d48402c03110a05940d1600e0000034400d80107013120740449030701401425120210000c1521160 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 199620431 1250 199619181 199619183
    0x14010c110f060f13060203010308040f0f060e010503070c020904030908010c110a170909070e03060a0605090411040b0a0314150903160f0212031e0c15191b0305010f0605070f 76
    0x40e803940c4c0445c00b00e1000b18041d5004102c1d0a030368504000d83c12104007500d51003003965a42a0104018aa61041c00140c82c20000d00c3c3c180d40c0c1740c0b07410108035031408208901960001c01c03042808205900080c08004499580000b804542d0304c0f03003000d85030041001302401c000d41103100d100000514910300b0216629a40c08100d080015582c00305810480840303601000c100120980c5410b03150400a0541c4000404011300285050802007015808054001000000300d070b0b54080d0729a946401c004500e90002d0001d0304041d56038142010405001c94644402d40181c003a045800b142100c03d01c1e104d070030307400000e40c6000d14940e210760740c500c0a0581a101e132500300c82140016950310107620b69510f03501c001903494141e01d01c0d001904c00d1180e1002d10082408000f000c020390340c0801e4080141c200e41c3c150001c503940d420360050807044a80c4200c3c01030741c40c0c04185002c150140240c4400b800442d90100308581c0c840c0224600d003480c0e406200c0104006002c0840000c050750761000c002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 199621681 1250 199620431 199620451
    0x3031306050309030c06010b0307030608031911010605030f010c09080a110d050f010507030c0e040506130b0d080d060608010f0f0b03072001050604150506090f030a14010c110f060f 79
    0x90700307017440070f0708041082e0403080c6409000401e01c0103c41d8540100005450400080d51410b494902d540010002040d600b03000d0105038800704008031020b601010041401500b5220424028401c0c0d50080c01c8a240c080049100c0d07200110381c0c084c1c00900c4080f8254040c4440042604403070801007480c10701941140c90f0303c200c00d54060001e0003801001d025030001d48000c101800724000c0902011008400d481c02285018100aaa0303a038104848214070380950740059102030a402080c070b40c0d28283e901a216600c0040c6101078500d0703580c06541200c0341a035502c03185907210300c00c000c0902080c3c820072100034004642840b45043c04c9005540241241c1081035075080351810104410304045c00d06042c6075900c004000507410180146115200000702410445003044002006401054444c03400703484d185600a2840c0c030200803a84026030465401c4110388000304409010b054a54101800180204030a619070f00000a4a022901c003a101820711940c40405582d00b42000401030610 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 199622931 1250 199621681 199621687
    0x10b030c04080a08040611030315011407080301030f1106030c0334111b061606240305010614030c01080c040909080d1505180a0207020a150305060303130605030903 72
    0x32100810107030214620480080d5115446e0110140280c10034282d00382058004000b000f400042d003481845109a0034200108806440311004009000b519801090960000008403e012100d042401d210348a0303100402002062014010680030903500c60004140600100c0ea2244280c4020794440d2103524084c00180c0840400750031034042c200307a42c40822021038401c04018000c1c0320f040401c4150000c811100c1c100034002c181c2d07505c07603004052039020300c43c47c203c010031078680c0085145c07491003185c00d414160740e0241c855402a1501c0110390662a0400004e00c9050302081c100fa03800004018101c07151825006403441c030401890303503248940c10000402c0054092051100031070040c8500d41d20f49030030380100320480311200034464031403080403020006561100c2e20003103422030101400744e0703d80706c17880d10b58080d0050034402540318805000c0805c6000d402241c5031038011555905214036121030b0141130f1a8480e10300c00e00400b6803a42001d1000a010394019a004081a81242e107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 199624181 1250 199622931 199622939
    0xa0312090b040b15150703030f061502070e06090402010507081b0d0306030b0105060903060408130909060519050f01050f12010c0e010f05040f05040f0f150f09090b010b030c04 77
    0x381860100d42c1221500f190380140000c9884481c41c000104000b5078904c1911001e0002e001d0440c00f501170020205901e4101020240542d50401d40080118000c0d04000300804003010351a08424040c070303071906242c2d40008600f458054440c82c080e54068407410302d007998644400c0d400758840304141c50030280070005030f00ca28100f000f1104218107682e400140307050944c9405411072030103900c000d1140d01c0600c440307409075901041240d085903001001a0b90340307046942d0042c00402075401455503500c1c00501c442401019040680704200c019140302503814a03040401c2210020340c2c000c00d903d48114018000340c1804400f24610f110024641054403217106603c03400c1d40e6600c00d107140003403964010002196004070f15000c12010906046091509203400c0e000014460b2150070b104507202e0404416050803a84201d2607116000c0d810710591600b0041681511403900c90006011295803000900710068440c034994aa4040c02c100103503407821056650a4201a1518508c0b80081000007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 199625431 1250 199624181 199624193
    0x509030d0306050109090c1704031d0303070b0708091c0513090c02150a1103040507030201030c08040b040b0c0c0a060501080606030115120201210506030c0109080c0910170703050f010e0a031209 85
    0x184030310b02c252f440c00515020b24142c02250b041c4d81101e18000d50045c0b00c4400001c2484003500c0d442861440e00364910f80c1c80c0c2843d07503d08980c0a0b110032100303c1140d10941000e40c03010090072081e848040d40c0901c00e0303484817a00115a00001e00d0001a006204110600320b016182c250b0000c500800109010056440d01d0003c0e0f407003600d0455803a40b10322001c10855805018079a54074046040016107840d10781c0300c1030054100200300805494108002520000c050815580c03503000080407600c464240d8602080103020078019400c1da441040001500307840c050040301001d402d0321408107880351070040b00e03043c440e4003401e0480c103001c0c0c10030311407840e8140000c2e94002da010664000c035403801c00406060500d03004004182c1084030404040c00f5810380040c040d18800c1081e11003a00c26075528400904c2903d10790000c540107102d82c54440d0f0440000034000741528007540a40345400b2a1a44113809c83d400901c019015401c0812107602083c0240c903111000094040b010442c03a80c5640e5607 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 199626681 1250 199625431 199625477
    0x3060a0908220503010b0402070c090203040302070308030f150a0b07062f03040c0905040803011512020a0201060303020601080a0c05011d04020d0c180e150607120509030d0306050109090c 82
    0x80b80800380c1020003040a883c0c04d000d85560420300303407800c624094507500c1d600315401d102d00500f06401d4000000c202054802c0000b0001550080c0d100ca80703a0801c0241c140c1c48140c262000740c1c20fa041205190365500e40b813540c40044a02801d41d184c58003840c1d03602d200180c05500304030407400d02c2c0201c00d170801080880e00896408540c654003a6a8078003446e00358840032040d005031107a02e10b040204800221400c0c112819620391169000540c1384000080f200d0712510046440310754000315660326100d03015080784054910030340a0f200c59a803501c0c461179030b1702c20300710026004450000d8100080e50160303800c1c505090814990000e02c440910100303040e43d01800c1c2420310703540d417603500300d0741f469110f0315110700c0408030554880c80c2491321808840040c4050f01550031035803845080041039682c50200c0300115030000c0c42122030900d42d40054076940102d00e5031130103401740d60312141d00c09110b4441e2744d0030365805031aa500001e061004210041980395041c10a0040011028049104003035031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 199627931 1250 199626681 199626727
    0x30b010224010806090a0f021e1503070e030f0a060e0a140c0f030114061306050d0501020c15071704020a0305011e0c020f0c060c160314061503060a0908 67
    0x9071101e500d802121460100002d00580540c1c00c0b02e09928001140070744050310f81901181d604801403401d031407a4407003209964105501c001c0c850001e0303a1035503d002c040c612030040d0f5160070310381201c41018561504550001d200d10f0303030801d88116001070060b03170012213511841011031301384450300c1da5503965800b02d10056808650140095409d030780780c150410f200c6018280c3c02804030700580c0103a00ea0004010780080d00c170395409450825800050350001000b004020b10340180c200342c90070994000c3d40b11291203034050080e1500701d2101000649454050700866980544090070000d0014030540043c1040360700c14150309000001c02c009000d902c003103e094644a20980c0d076452000000c8030111440507081d03420200d4031010003480850b8840c00c0034800d44005585000300d0340281d041610302c880c5059254101d0401005222541d034842c41921082e00807181540c40305511084020504152258903900c01400500942095003210340d00034800ca00031410081e0b020802e0200040c5046 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 199629181 1250 199627931 199627993
    0x708060c04091a0d0b180a030c06050601030203040f0807060212011d071805010e060408030f0a080f060d02120a0b160201050a0615050c0c040c0c110a15030b0102 71
    0x7400d00c0300340320b81d100d10ba200203a2010140b803060fa00c0b03408204802c0b10450060504c5000e00c0c005050035109082414884a0407000e41d0000c000e1840c020b410b98131391420a4030820318240026003554040c0c0300b1240a9500a440383c958801c5a0741c0c2c01d43d169014900440e02a41c007481040080d05180f050580a84400c55018800a8540d06000e5100b02c0c01400c1e0300410515110001041c0212502c08090300c0c420301e01850350038000c0c00410518880c2d944510f003203100008008a81038049005010941c2280d81c0d1081e5523201c0d514640d40c0c80d181034503403a03403105400e8a038100500e0b044810455420b54501592041c480d079032288219040308a4003e24030900f0596480043c03642885007035801030703175080c040040300d05007142402071607080e8040034144a400200c1c131060f104104441081003900500c28040c420b09108014000004840b080310180141c040d0040c040c604520f0040075100740203c0020107803034095044000d816452070160542c05114401d22405500400c2c1200e0041a20 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 199630431 1250 199629181 199629187
    0x2103100b0409021c091e11060315030d05090312161a010923040f0206040b03010b0403120f0e0f0a031a090c010f05070201080a02040504020a03060513021606020c0708060c 75
    0x903076001031000e0200200c0490b1031725031030100150400f004014034140303d140745c035801840d525100d1003128503510016406000402084003100c451074696104441c10f40a60702100035003001602d003030040c44200c9070326400255132141c220030558003404030890350030b41c1d034203045040351030b001ca0100c81c64244081e0301d1600001842500780c140035180300383c04150721201041c1c440040040d40140040c1004200050180c20304d419981c9510030f68001e0404000310643da0750f925940201c050b8000d1000700c0744071050310302d0203107114024008416030752210385a288500c0c5100c000c02c1901c001044066900041120700400850f11800c040380d06042e24215581641c100005c0b03040c42c04c101c00b140c041c104031034401c0080000d50f01400b134954075582802c080c000c64071400f841350702a000c0c0750001e0b03421a10101d08001c0503541a042041200c0d42a42d501115841d2072072110141d120303035001c21104003964000d110016805134021b01549650b20300b580d01c007641740c000f010701b400016602c0f05a40b841c04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 199631681 1250 199630431 199630447
    0x14130b060d2a0f0b0409110c07060207030317240319110a12020a0603020a2006040c06020c010507020d1407030b010e06100f0c03020a02150a0801082103100b040902 72
    0x900000391400f40441d00740240b40c0602429944102c0c0030b000c0b4440c1d204c003889410b0b01e4520094654404032103058900c0a922011700950b5100b0900c030130380018a80d00304c081080d80108000c58011704e000c8880c0c0da880ba451884c0c80c010700896910990b01845240440034500500100d580c10f120712441c20601e150300034030b081007420741080e0031100d0f501c1524060540142d0b81d800e0000216900d0f81005a00e84840c42420780c2c0c41500c0b008800300e010b000f0b1031440a440008505648103a2081c0c04030500d070342c0c40e094200d030750f00c00f07262505001c0b401c2081030202600e0001b425400041c03003800c4100c0451891308500d03042410a44c011214840c00d40c0c01440102890269107500110a6a0441422000c40b40003440c8000600200c403d1003d24100f5078140342c428803140c0c00094003c1d01600d41007541c1340c10070200350f1003451300e40c0010700080e00110b41309202282540242411103211a00d00654585403029035001410b4181c2584420300002280c000000c0030b0300041811210040c2c4511030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 199632931 1250 199631681 199631753
    0x204050114090f1513060903120801080706110a12030501030507080c090a09020f150c07080a080702010f0207091104031716170d020315030114130b060d 67
    0x41c0e0503a45051a00038441d142e001d481d50f24a2140c105001c40d1440074848000b00900c03994400c1c802103001800e00c10310049000381c2c1054402c41183e22403034031121182240038045900c1d910030b026a501703640042da01041440d12030f08a01514240c80800c0d95260f50b4103554901150a0506440c800f0946550040007405024800310009116000c007038180107036054000743d00314070014418501e503540ca4803a0821754803241e0304858850702c064402c0f01142c05607403d8021580120300081135510800201240701c50307000c224050030690001c03119080908550064505c401842100790461060242c00201112140a1014403802207108169614114205108041000d81e0301211515081182000045000c181c0001d8180c0081c010302c1203005809450900744200b0800e003040d24004018004203180b031182c414080d11084000b00081495100481c200300d00c201c903000044030130000800082203884424540c0282e0003441c0101545403030b6642c0252002c400b815803180e11000a0300d01c10114 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 199634181 1250 199632931 199632947
    0x90f042301150509061308060901090c0f0302060d020a0e0315010503010f0e0d030f0f061707050102060105090f090c090112030905010201051501030932100c1d011403090102040501 79
    0x344a550840010b5620300d80030706240304001605005090000d00c2030340754484640250060300d140f401b03480127403d1a444141c0030f000c0707602d407e6462500f8254005494060725012104a0342d01a00c85030410303940c1d108603002034100241403018040c0300c481001003a5001d1280345100903044c50758001c154100001e0500710741001e0002444589004c25460345c3c0745d00011910b035061186d240c082900010a0b056802034213801f0180032800382003d00120318581030f103a038510340400440440d40081e5851004a030394200a104540e0003018103000300740c004141c205010f60081400c401c0b152400003020201d80c030a04264844800c00c20302c082100d0030190701614040080409100901182c108501c40301e030541403c03c000ca061640c1c0b81000c2c02000000c07002d21625042c507402000c3d00c0050500300b040e0760f542100c0c800360a4010340360b99628030880b41c1700309640c06103143d80303001d00644c1c000d144000341d10405001038184140000048074880507000218070034482000003580b00e0b481c00001410a030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 199635431 1250 199634181 199634189
    0x50406110105010f14030a1509060f050417031305070b09040b040902060301050d111003020c0d0504061e020a050a03030b0a0503060603061f090e15010b071106090f042301 75
    0x40d0400004000d01e91600c44208145d0301501e900300c016110784000a840c0001454008001c7c2000d410507a40e0342c9002e500c25000d81e0f005070010300a40c01203002c01ca00300c601c1100d000704032081c07800942560303080300e2019540c4245c0c3c42c100540046c040e6250300b40340003c4e540c00b040f01034400207106803072030405010b41b07180c680741941d080c8602e0156130700254990205001c0c841c0288404840e4406125001080701c8140001030f090704248410f11000502035440042000824400c0349429001c2a204904607811600203075211101c0000e18401d034509803c1000c03800d0110701c11520020301007941800710408951003900e002980c0e0207924203000110250364440c901c0707074029408014550300d004c502954440e5610302c005154249160110070315004035000034403143c2c50004400004200041c0319032194400c2991000960b980340d1105640e4803d00000a100048003220341c440341c14200c0103007030040c41c0200341c541480b800c0c0340450f0032240c6500c58481c1081c200102030480e034001d58055800744c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 199636681 1250 199635431 199635433
    0xe010b0304031b0c050418021207050922151116060b010f020303040807021203120a0f0513260d1e0c09030b060a1503020d0e030901021f0f0203040305040611 69
    0x5110140c0b90403113090218440d0a001e6a128413002e4400041200a0381c40306a0040c80007140c10b803c481010b0b135070707080c901507203001c4c01d081000305100c941c0d100543c003c400f4039006821003000e90381d40c070b804d0340303200c2e100d4410070203921074520075813103208071025283e400448041e0411128003400c101f4292000b441445050018403e1017519690b400300880307600c00e402c440e1956a40981c0e10101d200030250422442e45804040b419080340c0550040040c0104080d000a0000b40030500d1003c0c200d400c242c40466007880e036602003d0000394400c0d507240109600ba07240070301d8801041040001c0b0340c01025046a05e0341da4905009a0801030350301d0740c81d91441550300b000034510180001d07280784c031640000b508032518400020032942d2850010300181c04540c42c0506881c40040d8050701941107074403d4239090703080160b044a40400082603a8031404140d0040c0340700b01c00c18810301d00320b1488070341c82010380f80c440e47c001720010028002035004611035590f0f15540e0707207017080003441129404907510032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 199637931 1250 199636681 199636727
    0x20c0115050105090904020f150c0105010602011424040501120501180b0f0a0209150c240106050d0209060703020d090905040b040623010e1005040203010806010611070e010b030403 79
    0x280e980c001d013a2055200c09596450441c1c0b118000110362080c1c0304440c1da88244041c1c0354101042003600a040d02248580087c81240d803618400c2e4280c51031000d0b6110304196070000100008907091148001c00709040d0021444000c41d404201641c03026000360300301d02c100500c403c0812000344641078402d1214a5401c1c1480da03913640d81c0e20500e40290012100c0c40085001c6001c1501d03a9040396140000180010340c481400820620150440701d6505d10318054030810001245c00b14043d50018006a240340003140e003800c00503100344e00300d80c1a010384150b083c031040c011a22000003c0c418a13004c0d40080c0307404a0242d0006081c820250005541142040144000074003060005038000c1e80c42400403540090f011181c2c25600c83d0f1084120748404008000640d101d0740e01d041034000c0a4021808101c5900c54080c0401c1e03110038400c0c0c0700280d001c0001040000e00c628007240d6032003910401c1d031b2103030b90780c940743c80b5808403081c2c00040c41880000140410142c00c0401c01d0000b2000840c2158 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 199639181 1250 199637931 199637939
    0x26042607090b03030c0a0b100b070b0406050714041d10080709180b0a14070203090117041e0302010b27150120010501031a091903140409020c0115 64
    0x5110900d0344915014561a0a40c0ca00240e07400d100307039038481d0030107021a1503d14140c244103452280581e0b0581059001c5000852803d016504a44070550400120000703601e4580c2d404004000007040c0c6000c1100c00e007100d8013180e0090004200500968106480040d0603030200d0651003070281c80e101c020020000100041c88002c503080341190003070500020304002010003548400d90300e0a004040781c02c110704014174059030b540300c2c0c5030b482c1100b1404060b5603251401070340e81c2c1c4a403901080c0400c0c2c8180340b000040845408880e4040d100d13414414420031801d032500554002008201c0160b51079000f010b01d207082c40d95640703802c80440002010a400078041c00310401d00e0181848c0d500080c003c0f80c0c00c0341c07640550041040c0c101c204507500510703034400d00b030f190003400280000c403a104411460040e480c61203540c0e440c00b844a0703801a00140304403203505128018488000c034280300f166035003480c0030302410002d440180500c0d84c001da520030002288900710750404211000c04014884284 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 199640287 1106 199639181 199639183
    0x1e030b04060810150605070b0c07080307021507020303040807080d061715060603010503120a182606040309060309050a0b040309050a2c04260426 64
    0x4400400000034803079007641817082c0d40c0011002e0000d040480c1130040c06a41081c01030b802c680c6000a1980e940c03080303402c100c81c80c4015802403c804070300c02901011140c0d004006102552541c50207a8540c40f039070090385809045440081f84400c08441941d001002a01d2003800f06000c95100d40501590307401c1c000e09081041e14400042503280c201003040e28103849000b0060580005070f01d002c0803c54000541c0e00040020040303074002039104a6407410060318a06807090b11600c00e4085ca10060071500910000079031043c0204400701e6404004ca00648440340ba011405e02d0031818001d203440d0011101405180c1504180810150080c00c101e08035003042e00d40e801c80c030740c0c1c5500400d031414000421a81c48024210380701c100268030f420b00307607000b44214548084840107101c0c43c801170b0300150300f42d080c100e40043c0500003054401000314108144201d07005140da0340008013 = true := by decide +kernel

theorem cover : BRFrame.Cov 199460431 199640287 := by
  have h0 := BRFrame.cov_init 199460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 199460431 ≤ n) (h2 : n < 199640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
