-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1749
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:32:27.85647+00:00
-- url     : https://prove2.me/submissions/f5d47f96-436c-4c71-955a-7d4e48b33335

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 314388489 ≤ n < 314568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 314389739 1250 314388489 314388511
    0x30306050f06041a1c020f09040501051509010305060303070c150315120f1a0c0702041a091807030b0106090603050907080c04111209010b030d08041a090a0614 70
    0x8540e81040001c8070240d84641c822a4102c000301c030204c56003030344800a1400e40c2081c0280700d0b08003e8050000d446803508003d001074440d105a01400200c3d0b0059024910494400a0b003200054521080302c41044081c80c011486948440c0480d01d144100f41c1d000340540300c0c0d01d40000d10a401086041103503811070743c0030711001b0389107580c1c0324402c8003d0013090740480e0220b02100005489060142c5c40900c60001da15000074004640074140c40b0481d00e02d02013040005480d011413500f48140410441d039810208807101c07204011a01005004000c5480b0b020300483c3c0c402d0602042240302d008661081c2018480d60312910010142c02051242c54042414140403c503441c002094840c00d0341c14150080005c062a0f001f0040501070f001e42810b400881005620740c0711102c03071ba58038400c0e407200307002140f400c0d491801e0502e040300e800c0754242002106428000000d1301c000e4803c82d80030340800030114503203c0440c114182850803500615082c40c0a10340d240300d128002080d03100f001c0280c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 314390989 1250 314389739 314389759
    0x6060803030f01170105040201091203021507030c0323041b1814060904020d29010b09030f160b03040206092701080a05030301150905030d03020d06051c11061603030605 74
    0x81c1c96401c0c6c620035203009010945c0c4c3c1409008920310b0751202405035020344100c640c682964245513540c1c907422788201c00082d80303031890140304942500610702c201040c0348043c4045068180f00e445801d101400081c21402d4052112005044072070300e40c0003500784031b5040110800c410240c1e4000349036100a800811020000040a514041110074480c54010b4461031480e01c1642e01c41e0202e00301c0414112000000407180d50290300c185100c54042e00203d00d141382c1e20310120040500d4283c08034005c01e1107034010001c040040e000482200301311031030307040742544036102c40c80003e0b0640100da04054100c1e1a41b03c20720010841500030000c1258642002011a6294112580c54004240d0090f010364801c100410a030708030034030003000055052070440c083d141c80d80c1c0003d0038001140d1000c000aa004203031160718020740d21800009080031030f201080201c0d818062a5100701c2d07050043c0c2010705642c8106000d4444100325110b4121000c0341d084079081c0d910703020b0b00030310b250b0103254040da0b1108 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 314392239 1250 314390989 314391029
    0x61c05010321020604030c02040608122101080a0821190c02010501140120060405031c02070309030b060120160e061f020c15090111150c0706060803030f01 68
    0x1141c40030840b000b98040c000c95680c644040c0e440021a0300100d0300107a4039540020380c000144074070201c003103900c0000c0d5910700041101c8498101c200c0c02005007045003034010800d0040000c0d480d541c03954030119207611a0640d41e141047c442d000302d408200d40c0940c0302000b41880261040542800c0d02e031100b00034034041000101d00300d910034004d040a10603042c01c84e4039070758060610340890850b103044d8081c032950f0381203c4505001e8250f408988030b90000c40d154800d400400300700398000d000d03848218109461624010711907441444042d16403941c0801241d016485040c8001c1d641801c4900c400503680d00c44401c40d45c4114180030320043c60150b2001160710f0303400b0306113140200d01c003c10000405000c140220000075038100c100c0c056100e003002c803000c15103926074222516000c4c0c16500c2d4603090010005041d5079024025050142c100f4081c50b1411140000741ca500b0054103101d4a49400302480c0400040815400054441c4808010001040c1224085905a500c541040040c0794294 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 314393489 1250 314392239 314392283
    0x302040f091203091b0305030a0815090103020409060b09042a03020a0b0a2102071e03170702030706060b0415090e01030b04060902120703021903030905040b061c050103 74
    0x4a0700405200c212805100e84601ca80c2295161038001c989120100d482c4441100c101c81c15039008507696003011070955581da80200d40c00d60701c0100d540c000d40d03007a9564000940d00e070a05000c020300c500d90300c1b403514050050a0380082095032014100510501b018180003c20b103625001806046507038550b1125002001d0328008126035018090390080c1f4180381c10082c254200051000400441d880318200b10f0304c40e41000c02c18400c11520041c4d0759111424045012000c43d241100c0d0b078500919144002603101d50b040800c4000d0010911003500c80d103030101d05522840d01c004d48214280702020942c1e249000c000c00031100c07003007840388004208100c10b4a10f1001d1b40704883c2038408840c010004030f8400c03c0e00c5588940700e118009615a02030307002404680003030280448590054605204606140300740b0710489d80d0074500400c941e45035680082100030980030b047d004640303c0403552016200c101c15120740c86d009445d41c00c2000428205800106400d06c41035904040b20002c1460040344 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 314394739 1250 314393489 314393501
    0x5061009020406140a020309030303040606180c08040318152105040f030f0207090504080304060501170d030b0319030203280801090b01090302060a0e090a0b180a0f060f0302040f 78
    0x3058595804da03040580e801002034020174080f00c00c0d03010811480754581d801348000d62040c1d108100c00680c290501d0540c4072007904a40d030034078804e407505002e041537035003123082e8550140c4e2618001601c010385101101a00180b5403000340e85104e1644405a0107800804203202c003900014060741400340103407841c003075440999010b0140c01400070204c010910031040c41c48504020300440d002565074140000803070b141110103540c034040c00710074030081040900a4500400c20055040025050009400e03102c1c401c2840340c1c0240760b60f4850400710390311b041c02803412000719119002054080b42c01e0280d144e52041390f07407a40b0040e2150010554101c034440c0312540358519501c0141a0b0300f405d418030001c0c110b20381407606000d5010130010040c1e940500500d6108a0b5540320038801c014001403050060001c0c207130303da00724240307070030b030443c44e11540c08080c4a0740c00b03040c2810954480304203520040905200e5085814100390f40440d05121940c0600204c0c0e1098800304140301012814000b1514 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 314395989 1250 314394739 314394749
    0x100608040b09030c030a0e01021507050904270506100e090601060509060d0603080a120623010c060f0b01080610170718180b1002060c25050610090204 66
    0x124010200c0d001c103041ca1501e07540107400034203c900d041c14410903070b49036400c402c0c88100000c0603500666040e5074180300148100f42c0c02044806103040403180030304140605480349014030380d103000c1d0342407d4120303150030351142100440a64840c0034a0400a48131041200c21003944202410001280440d41c41002d20031289007010300036a03400c0410840302544005e12640c0e010740d007400741c0f459620240c42844010741c40f07001039035600e000d80c10b4094100c8540c048000d0515140010030054110078060080e0004261002103520300309603801070b5031418003000701034141d03860690f070690507100c00e5000d18020130007600c408480d41c0e1044200301c0f83d403c41c40301c0707000041c400d0f00301c3e0814581251400341d040700541c20850302c0842c0c0c1074030841e20701915030301406800c0d04051100102e0703041c41c840e01c2001003090300c0e0383c41181c0800101941e100005420380000200c005400c0b0710071500c2c1c10202e040020810100c070000107a0f410b2040c1c2e02d103c159440d0301080301500b00020040194804c60381112 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 314397239 1250 314395989 314395997
    0x5180615040c0908060f0106090b041202090901020421051c0e0d03050904020d02030a0510030b010308070602040302060a02100f06060c08280f0f09030f0206070515070210051006 78
    0x628520180000360042c1a2100207200c01c468001c2084e0703009000a030700c200a24540c00e030700307985010401824552250f105001500040200f809004038150004200b16016030301c1c40190f485c0d000d40c5a00900c110380c40790341d11a1034056a54001c40040c2c41c4414480c1c02081200d5031000030300e0850000c400c5102c1c00d40040742d4142c3c000640c0303003000461032843c04d0103410a02c0c10250b80704040b0f4166400320181c62301c5c040d4008108048280d451240f180c00000055070040d0141c1540c2d200d0701c58040600001d0b040d2031000c1144410040550119005160302800325602d0743d07420800a0758404070040310888003070403c2d02d0302e00f83c00c0d2140300d030714100d03205507441040364040c5840e0303400e02c0e80c06100028501484143c0150811040d101050500c10300c0b55121b0010720ba43c0386004140c203038541c2030b00b82080395841d0100701042000200c240c129070110b4040b6600c00d51031418525203c5c0384540010300305054003c0004107500861105d642e1003051400f4403280c0d84206124000047d0340c05400041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 314398489 1250 314397239 314397271
    0x20f010b091504051b030705042417152d04140c0906090307080a0b090a0b06010e060d0c0201020a1b02030304030320161a090306070e0d0b010306051806 67
    0x34903298001c180c000c82050700c40d04170080c01300c0f0405400e40c402c072841804200001020890590020080342000302c00e0080082c083c08005001010301b132207041c40c140b19212880124000b0071244081c1501103c0c0100200032a0024200803100c0c2900c012005031007041501802250303041c00e0041c0e203607140c90b0038803108030350ba5440721054180d00521134003034200c03005010805850300e0801080c030142c601c5000400c0c00d00c206241480b000040184500700c0780d0004610800060407100003540c1003102400c207003803610225400305000b0b026540340c051300641441c141e5000c3e02d40660081050003196940d103c80c04003004095240b0740180d642c0250154000c00003000407a202d00154000d0f000c003c80101c0c9206600f131486807034900d00317001c203010a240c41e500801c1060f80c00c040301032001d20b42105a40c10115440c00198a858000300340105105502e81017801ca0750b5090288200396512041002003540c69081c203100902040b502e10425144086034400c1e41d15000a0182c4562402381c2003031b030a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 314399739 1250 314398489 314398531
    0x4230c011d0402070501090b071103071e05031b06060a0b03040206030601031e0203010e0a060302030619020c03040f17071a2208010b18090309190b0a020f010b09 71
    0x80d450341450381c1508507508100c20615644034001002e03854001d000108200b071490602994500004c0c010f02c0c24003129000d090540440801502c82a9401c0340e1400f2110b600c0d401c0d03090681288074401409800009500c1940c1c0c000d400e16282c1510100c01114011b0391104d06001c0000c50b6402100c0790300d4004c0c4006001071920310021a4003400614010400311035004240f208082200c3c11038988940100040c0141880d19480b02c1c2d204206280a2003c6460b64011a44130f10008c0d0500c1400001a20003400c06900c50301141c100b01500310842c1d0751a40e0340d40314255000841e02546c8080604285142c4039014002554019104028560210031010025042d002d80c030442c040c408600b40c00c5a80c0945085000350790009050150010440b185800100442e800c1d028028a549110b00010302000c4240003040d111003034415a02862401e10005038440d262406074401c0d864a40005000c8050507800715140d82640071980090200096510810100381c204680044c144c020703802c0902c0d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 314400989 1250 314399739 314399747
    0x15120c110304180b061209010c17150d08160203070801051512010608010515040513031d060702030d0f080c090f0f1210060f06051611120f0604230c01 66
    0x4182c003c10000054900380100103d0000c5c0c03c0907020007114003c02d000c001017114280511110501240350000003200f41c40c04440c0140e801134036241155030300902c143e20350388440200b580010b802c8411240c07600c0700300f4400c0c2942c040020049009014500c0300040344107050003030500580c8502c0100202c569440c09110801c460703000302400c25074a4001c00921081c0070700ca080c2c05100700c4c4844664a10b070400500040d603502074a510b40e80303040800d403400441d611004c8001580b800340d104145040c081e0002600754000c207400a9894050f10f10010800342d0400e4804002c1002c0c0c1e01d03012140d0782ca8103040055401500d400c55045511503a0399081880d169001d283c2c062002428540e0542c0c21054441c5052641801c0f510714550301c50062007449070780d01600000304100d20380240b0f07065900d08126001100100c00074034034080b24a15149695480b41100d45110800c001c90301c0c1c0b2400703104159a0352030107a90035100319a5070f0740030001101680e04e004222504401c001c15608442e040111 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 314402239 1250 314400989 314401019
    0x7080111030609040201090315060510170a1104030203071203020f21090604031a071d030a0212011b0c06201c0f0e011d010b0d1b15120c110304 63
    0xa0400001f0301c40400001c10b28503604400300e04001000450a00348024051000b0448520000b402482e90444822409211a241d400b81040c003011030200000c2d035482d5600d00560700700035818000c89202040c4503e000e661001114080e0f401c446030040420091900c500441030400c0e055900c3c04201c0f003c05a02074014081e52101030401071905542e5241c9106000d402c1e03805410400e18041030159160380700011400e00d02545044040c441c2c500310000e5a14008614024003e00010024000c102d4080d40040858541480001e1305c40318099030060910311400002c44102c2e1034100c5608455203c82c025035520486580541c1c0b500c480c517001c200a40c074004c08001041900c4401c0c40c02e1f450520300801c0c14194a0b88000300d41040c2d100740381d0080050321029440d00341e14203001e1928550b210090032214542064810026803880e008a0380030318500d404c0351580380d062103980208194021004103090081d64403c01035101d1310b810071105152480100000c0f035100384814000000020307400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 314403489 1250 314402239 314402243
    0x1120303020c10050708160201050c1215040207150f02041202040b03070f3209040807030c060908040305160b0f1803100c1b05030f0d140a0b030708011103060904 71
    0x3034a01103c1039000000303444045404200044910081c00000030043c1d040c0c8010803030b240024040c034034002d2074030102401142100c0c140e200346a00805c3c1c8070070610700522042c0760050030540d82c030f40142c100000d048050301c000c51030b01c91401c000e01c800300c4514400c0d90141c4050887e0780903600e050750208800340081d215142d500d40201e5030002600308005030900300605424014603040e400f1100c0d004e090107203411103d004101c01743ca04200c103588195000e0b501652082075151076610506044412103c40070001f0141440c01014905000a50f4040c1084078450011250848013031603a40024640e41e1107000c404a0050207080d0120030b04801401b041409850044103621501b40001e2404144003000340b0178550301d0841c0b5903c185c0c000f20380c01c1903048906820814038031607600c8036901d1089403840c940706100170032030818501507a004a40310111403c096411800c120604900030510003100c2d034400e215200300052111018001c0e424100d0403411401d081d5550f010900000500003481 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 314404739 1250 314403489 314403493
    0x405041b030c080d020609151b0c06180a03020a020108060d05010f09030206180703030f11010c090f120309090203090a020306040b0912030c0a1d03100213050901120303020c 76
    0x101121003144440d000354001c03580c0d1211186404909420b0901000051007150031801c02c01001c110700244034043d1341d21066403078419503621040b0382e007440c0d444c081042241100181c2d0600c9140005080e0f4000c00c01c000560354140f940000300303a642d02c9070303003401409a08003040300700140d80140c541c640d000d17601505070740031202a582e4443c00c68500000504c100e035595482c01d010b059041012541c005000c2e51894a05a001c202280d900e01051000500300709600320151a550700c0390385201b441200c00b00081c001000e181d0009001d1055502032240304001000c00024140c02c0340342e82c6140250591604040e440c00c0c0162800070f5070006141c1400e503c101101207006031410000075204900861030044a0b0503c18555400d00c80d0720401100e9200041c030510209200c82e400301c8024000905000c100c2e41d01c1001e103484800f00c1d1015103075050060304544043c8440c5500200050340c000c55542c0d00d07580d103410401220701c40a0050070842d2440d02c94110009000764028418800c040b41 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 314405989 1250 314404739 314404763
    0x801060306140f1f0201050a110708030c0f07062d0209010909090602040308040b1809010608070804050f0f0706091e03200a12060e0f03030a1a04020a050301050108090703050309040504 81
    0x4103189556413451154030043c3e559408120b81120203201e92400e4030a40901c00f49005000e440c1c1c810540806019240c0350400002c0c081c001d6400041201c00141e8454428003c1e0001c50303940c0880100843c45190300324109220100f15030005200721b8090f820142c46800038a070030208900b0003004d1081088802c00d908120200216034490080c00c0101000090550307503c4000a40682d6200c2956200b03004c0c15000c0e0042c0800d0b50022042540100c0381c2c81c20051aa80d036041207450400c0c500a211940d001e016403041c903000c4c000c110101036601d107444e42100f5594030684103040e141c005080b40b155442286060000230b6030b800004400b1541450f1603011100ca0703800090980f07000360320040c1040b1881000a040000b5030142d003154442290282080542c5030b11995100d01c0028038160300187e13515611000c3d40030040e085516560054011902c900c00544054219070080c000d0034003141c844800a40201d034001130203002d4a900030041c0d410a00360000703010241c40060800c03603001241c0f113 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 314407239 1250 314405989 314406019
    0xc0325080114060714010209010f0c0c03110f090c180f0a090e0313090906050a020901080a0c120212060f030f0709051b0a18060e09041205070515070801060306140f 72
    0x24145c403500c40c0c155000507902c2d036802001401d0307482e2110000091000380501d10001c0381e010860713501101d0b008801e143c0d41d0040c402c0040c032a490000403c40d40043c01b0707800d0007070b50b11844003d00100d80f1031003580229a00324100700300500e41301900e110741c0f11143c51030501110701c454020214000c4144101d03424140706500742c240140705908500700c0035a9982900d03044c00001d004042c1c010204140443ca13220b50680001c0440a000b00800211394a451004408510420800c5030030115403d0841d241c0800888115544005030390b514440c1d0410860b10039280360109845440111480081403601d24000812002e000000c0c1881c5140d41440080e680d000b034007100a00c1310307401d26a80c00391007006151440540d00c40c280c000030200300d05003550501e1501d60826a83d08a034000303000741c21707920600b0300484061154100c010198022904d00806580d1700c1c8205c0780c058032071501c9201d242d0780c84080c00c400700d03480e6114030703034204a075911101302e6810040c50500c8010300142221181c45402d07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 314408489 1250 314407239 314407253
    0x12060403020c040f020c0a111f031e0509060a0c090b0712020706180b0c0a0812040302010b0301020307051204050f01020315090606040303020a03051b01050c03250801140607 76
    0x4460540150300118010344891400c0d01c941c42c1600d8a100c021410032008841c55507a6603181d00d0014107410103410783c452140e8680750b903a030703c2007254007900c0090901e4240040140a100450000303406c0c844c2400b022568150007814480d541180082c00c0d16034075404028040e2208028807400c0c4a0540745c040340e040c4150000302042c0c1c0c05500220041152503d00a03c0e143c155800701d0101b1407070f20190205c0d000035004460448020300304071078070b8800e150501410402c04000007040010001165203000d2100880640b00e940a50002c12021030740000341800c0c4e100480d07504000500400001d0303c4400954003168006028000f00e80d0400c0e89881414220f0f801a1070114030700304c01c4401c4600c0b074039018244079407140c402e98807a41041d185690180d0303100e14801c3c2c010140180440d040d8100c01c21141d80c511400d1441009129606141e000c0070200d41c410355030181c620800110b0030a14a41d0041207410710000c5030303038003a5207030f290011610606840c0e080341070b40120100009404900d00d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 314409739 1250 314408489 314408491
    0x12060302090f0f1303050301180f051e01080607090e15040c05180102150a02030711160927030509030c04050f070f02060c1603031d0a0b0604020f16021206 68
    0x4001902000c60804280d10040c480004003004401c0c11003904c40c03000294824256030444034000d090781c071241070904460001d0000008000e00641c985010000011140b00404003500e02180840d00340c1d0342c8440c0941e0300c84004032070010104030403217410070040a000f601268484038141c40403617006c00100000f000e854075000450009580071840c10480c81c021604581c103120240004d000030780034810740900075035000b06042c070f800d5404000940d82d9401515000007054580d019260441441801c0202d2074101e409041d014134030700810301041c002101c843c80c0c20b0f400e0a5008203c9508590750840b003da001b00005a011301641440030071640381c5008190041c1070000c1509002d1804420080242c81e903a040081154031403410700c916484070404440308440030740d18130343c510700a6050541c0070b0f0850301d240e0304d1140d03442c20b005125007001203032241006103e1200300000f525460100016401580e201c800b400c2c4d410418100c8121010180300003136880034064000c101140480c0c5801e14030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 314410989 1250 314409739 314409751
    0x307031805040b1f02070b0c150105060414041e15050f010201050420150d020c070f0b0a0e0d08040b04030b0709060905090403020703050601080a0203010f02191206030209 75
    0x3056081814411500c204400140400781c5080104100c03c81c00528035040c1c02d4005036000c20714900c4101c185109100c81d1002e08400c09010340d03170f0001c8a507041e64500040c00048141880c40e000490a49040011036040356440024502c2c0c0c214410b040000400c10070340c441040325141290603004254901070b140304140b000b8403010f01c40b4503100c140114240e001400030f0469141c042000000b44891004240f80100350340882c03201092034010034840320240c080689d21440100e0700304151780b401c0c0c0050042550324806e407000c0603680c8280c44c072241c6076400392400d40c5000744000b06106124402446255400814000c2c0059013034440c99120b50094000d8022501d0014062081c000305208258009101e40380161196213000d02c0105640400c0c0a124400d000000214042c54800c00c8004040c5400c202505c0070340d65a4800540c5d9400c41203803c900075420845074484061031307482036415134160b02c40c511840c2e5032103a00844080314605a1000c00960361103011001d6166503110300c1c4514 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 314412239 1250 314410989 314410997
    0x190510020d02010e061312050702030105040818090123030106051e010906090b03010905090f0d03050105030c09040b01050f15041805090a030c120504051e0a0609080a080d0b03030703 80
    0x101c18001c009094401141c1102d03441d9100c5418040842480400413020681018100d072141c01000c0c0c04450b54030480001a502d58200030070301090260610051656000713814400f526107146005010700c940d024410522a404d103c2c038222495a0701450a42e13090600030000924640c039030000030f004e1400702d110901204601c41401c1c4480d40c016081d0300140c01c144c141108214908212621030703200500a191245440d100403544401c1c0c03c000c254500c00c01c04095684080349050b0080c001d060074803c02e440f80c81000311511141c00c0c282c56190280e5000741c0740959aa0800c030a002860041c1407a035504040d40d03911034a10030303440c01d018001812514969030110660030f1441020341d54090079880341d680000e03000d900040d03005802010309552140342207050701d2130800c00791481d02941c1d00164000200d100750304000c00d0680004040c1c0501280c102146035203409007200c1c0b00c0e103207010342d410741c1d4131a94062002c1003040d4040d01300250824804145800c072140801d0070f43d000f55904801003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 314413489 1250 314412239 314412253
    0x10020a02090a180c081e030a0c03030b061c0c1704020d050712061a010302090f09040c09110306120a0b1f090c02030a090501020102210a0f0e1606030b06040519051002 73
    0x205c4041c0302a941409802d200180b0310404000e90f15201e1152105000900c17a980d86010100340c02504512414813000b0206502d48403403a22581d00e01d003103082c0d0008414a00030030304042500811600401c42c00b03031545d000b01565250300307118081d503e0982c00d890901c5540710000300d41044181d0ba00c210340c4a4a40071484502901d01c1c000e00700c445204560516006020700b44441e146c010504c00348a5048412100030b07151400c0000e41000540c1005040909010105020b00d07070f4000114019442521440100000d0352180341e200d892a0754000c20500b424408200940c000c1d0a949640c0b0016500100360955140c0b11003045803e0005541c0150700081501d813117040d00701c0350034001410700380000d5180ca406c40ca00308000030000b80380310001442d5800407a01055032940075140d490341d00102003014003603080320755654100607109280305003159038021402038802d0041e016242d60140205042a040a0410050302c0181c0c0180c15848040c10f40000c07550341c0c820302140c0c01d4040c0d4020b0004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 314414739 1250 314413489 314413499
    0x4080f130806010e0103020d081c0216200d08071103010f0902090702010c0207050607140a06060512241905041202070f0b0712051608120610020a02090a180c 69
    0x101a0705a215100384c21007540104050788405a0386101254488941030340d46009080140791103014005e443d031000d20100340c40780c9c0d1121062036003401c3c0d070055009440c40400b44580c031070220240303100c06030040d079164411400540c541d00a80000c900c0382000959031071003000442e08454500c1980c001945d2070f504107200b941800b42c182030708404580700a020032101440c002e9955102031040e00c1c055a00050010240a0801d5084402144140175181700750b8a904111002c1c05080c002c1e03501c28003040380b04401d00680044e48220070030003000102120702040360801203001005010403d5030300c4200229000c3c080c1c9101c1e0500c80c910070307084010114070a1600a1a2035915085800b010b109403030305000301c000c00c3c0e0035a080703c2d62200c10100c5241e8004d004039103901070100d035400c03944840790958042046400c040c14007a45544000e020b1941d5650400c900c15045d000d0705800760300100846030141c202448202da0105040001144a44880c07004d4500d00b2040c290984100e01400c0007448 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 314415989 1250 314414739 314414743
    0x9010204090b01050903060411060f0c030406270905040f020907030e0127080307030608061513020301050904140102091e030601090e1203071b08070323040b0304080f1308 75
    0x840d0b2003c0c6405400c20650b000481d54864014101800f1001d810010001c1d40e540d045c215103500740404441a220046201c005030340703820071b00580012610101c041595003141c9096124911401003a032074015140c1280301c401480050810780c2d10040c3e005092015171140b04056009050b169000101007000784502421280640d42c0062402c09003141e1791080c00500d40c0f0aa50250007900480c2d0342d44485506070700030501580407824502403034003001181100328642840e0a9026144213414940e0184808101c0c03009020340ca80c004103050100d800b1819556090030300304400c20006240240d00400070310409000203409111203200d46500300301d42402d20415004110b0307013200340182c40d054203403551292511a092010301d400440050503551044140414041e01880503e14030402030078624450303071010005034045600c1d42d100218102c060b01203c0140f50b004900c0505160a00723004800380c2e4400b810540c1c203844103109003056014180001c0607524003400d080030b84140b80041d814 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 314417239 1250 314415989 314416001
    0xe1908130501110d110307050a030804110415060c0302150109290303090d0c091d15010e06060703090503070b04030507080f030a0807200d02100203090d050705150901020409 76
    0xa0402c40d50502a694003080014041302d030605030f080651004501924007450340c0554003007c2d0440c807890f003840d400d254008610b640510701515141522444200511054a003607004522456408040401c1114030801c02403103141c0c440d105450303141c03101310450078015400f078019071841030340e50386010a0624809401901c014903046100c3d485440240000e46038002c100103140180d00e402c040008100c00410035501510a01004014000004a0342c85404190503158000e901c107151100c001703e080b40c6100d034101c4851942d110309a517910b07002d100e181e8211020480038070140c0c07d00030071a5a0240201800341417031901c419112841d40c10100e282036072a03840f444c140d42220105070782d040c101008554a25402c2d0034440a1a11119002c442c9024056403c040e07408940c00c0c2e04450b110701069000c3c030514158200c81170082c048a18000301d201c10340d03030b9130704030b034400c1d40c4a00d8918011005020320302d0191b415502c04403c070f060b40303019108048844d6241654005414040f03040300703200e45 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 314418489 1250 314417239 314417249
    0x70503060a060c0c0303030b01120c09090507020303060306270304090218060415080402060409091a1e040b090708060a0204050306070c0201080f091906090c24030e190813 75
    0x42e06145404c3d2030700c0150440c14040134007090f4440e402e0080603401040200c00261906508005420364801d0090403c0c0c8a8085d203581c040c01e0a0114445510010989000380340003800b07402c0c40c0d2500c03a03034140c50b0b250130b07810714480124600402a034590f0a00c003600c0248170202c40960f480b02d003102d0301d4840c0c0607480a8240300b1441400107001c05544000b403210015000d041100300e40d155400051030034040c5a000054090500800004200320503204102038000c2200c036050b942c44403400b480c8641d45200d016468104250b0000f004179194444041e000003400e030541e00d4082c0c545441c43d0601e20102c4d11444c8958000502300042d05007009032692000c0c2c0383c0ba14003e11180c5500080100c1000751600b100c003442c80010501500050207520b016881404e030030071030b00116150040107003095100549081c0d007040000950003288403800001c0070f820001c104008100c0d180b0950041a030070031040c109209483e00c4c403182c2c01c06071100c0110280200c4200b92034402d0560880c0702c403041a001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 314419739 1250 314418489 314418497
    0xf02010b04060609083a020703060515090609160e0a030b0c03070f020309010818100f0f0e240a0b09010303120e0c0a23062109011a0f1305070503060a06 67
    0x101b0b0211a00c40c800c10601c0407007020340182c1b00d00401c1800c13840c4c24000e4001900c8030f032904080c0100001e00b0384c803141307140e08143c130380810550b18501045620441111400c0590103461002c2140f10300c14030841c60451401029013040d2922030305c9075a10700c0400c903500d0501d5407000051291441d00002c0c01c1350b000e0354520085141c000890002020142c015082080007013103041e01c402039500c14031072000503890b13075802003010942d4018881c1c003034140441040034551414a00e032410110105000ca40f00c2500110700b211005000350404903800000c00c0e06d80069500d4080c5038456070343d80482e9000b540a5900c41d5284c01c942201541150815822a03420341e1000042850545502c0d9540d01141c030741510f1725080d50b18256650034400c0c0e58504007544404009143c54842c55402d02c414100f0807003244805aa5681b440100d0032600c45c0044803440f90404605044286451807440d805104041d2418a06813000384c141c800750752050701c4000c0410000320811006040c1001d074140206610303e4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 314420989 1250 314419739 314419783
    0x13515120d12091a07110705150a170703150503061b090a0e011805010914040b0a0605030303091510120209070c023c01090b090d050708030a021203090d0f02010b0406060908 76
    0x1101514036051a16001c0e1000c078a1103452360141c08504c81554440c0e0320102f40e898549401030050111011403001c801040d000400e25040000b5504d00c29005070041449481d602c6079844500e400c0840c1295000c142d40b40003089038801850940c1c000d008101e042c166041c810a0ba40c0161441600580800361070445401c684644000c912a0000c0d04002c207900c0030f486040b02003002d404242c1040d60940320000500c4501840051694507046110038080c025494210b03006811030351030320a001c1c40c4c001101042025261008115420484500380100a529283d000c1404240c00300705e03200c440075528000c02c0071180070303034400840303680c0d60415000102229000603115514078010451441404200c0f0042c94488036031182d1041d401404843c3c04568500300642d9a80c860780405005000d03001800c4190300c2c480d01a64080c040d03003c00307000c051072101800c81d030140321841264119921105010100e4031244a01000341105641d2400100e042c901441d01d458413500d075685074441051 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 314422239 1250 314420989 314420999
    0x3091202010503060405072f010c0306050a06030f0b0a0311042711120f0607020c060306060702060310090f090519030806013515120d12091a071107 65
    0x2e04695104c4c80c02c4034000f03210b1310303407210484006180d200d03500e60910340303840a100003924020135144500c601c1c2000340a110821081182038800d244621a04440d8064042c01303518001e40180d401032103100d000282461000d400601c1c0e0504c039a000b034400f140b00444520310350400d0301039403d01a2001100b000e01c1560340320341402043c0440c20140c0a812000e158000035074640050b500c4403186c02c1c04540f0702a0b00c2e0ba10260300c4210030f94580c005031140c200004030900300141030702c0c40703454001e01490624046400344180e550009105011495018001256003041407142000300075601034001903150707151600a02d040c0c0f10691031001e41210402c001c0000e0380c0095400d503ca24286045001600101c83c1c40d16140c01d806100101c0d50b4a03003201c10306070015151020b200e154907880f070344108400c80f418440300c0008092031000a40002d4449001d01c0e010380c0700c05079420040341c0d00041c001d201d601c403500d007407031550181403010700c9820a0100703171907000482ea07100084410140640a00c2c4c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 314423489 1250 314422239 314422247
    0x13030210090503031b030d020f03180604150e010b03120a0905010c020d020409140105070f0e1023070203030708090301060518010302012003030703140c0c1207060b0307120309120201 80
    0x11003552405c0021500e004030083c001401580e070201210300c419521550003245d485443d80007294124240b65034200d801d10b40b080300180c550302450704400103003054294100418007070004248031100039074884001003529241041440f800e96600e0081c907444a10214004160580c582c1c00f2504021b00e41c0006400369a0310b8150403e04d0790304850008514026180c40c2e0104d0082c01c182000c1e95207000c00304540c840d04004500350700081c42d81c0703490000301294200074200c500c1c040f41c000051840d02441c075200f59001640c505d030044040c034581c2840740540c0000d20f5540031480440c2c1084007c5401d807010b003801d0080c1d202411702250659150fa0b00e00001d4441100140300c041e04200c0b580584203c004031a07184005c1403070750301059941d24608100c0180c040c0000401d0303521905e03a581c002540c01c0c2d040c40107803400554024040d0010380a081200b10050b00459820381d01c1d12303500c4070301c420f007541e0400410006100c0e148103001d200001c1e08003d07110040d19800502c2a0354041c03142c000603a80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 314424739 1250 314423489 314423497
    0x30d20010c020618160b091c05061515071b06080601170c0403020603090c031005151905030a0c090e0c01171503100b190e130609081303021009050303 66
    0x4d0742e11041810160340444510300040302440c3c4000780c0a001c00440c12402c1c14008085e42c035401c2c0c5500907950440c00241600d42c21a107005400e941103800410703468a2408020091904c00a2101e044452203001c00b10095000600c2110751040003200304000c848051a240001c111071b040c001007618100001800c1c48054200c904104400c810008810640c480c0681e8040c40d00600300603283d01d00403803250395903902c40038450b00c40d22464440c4840f8080070301905109000303440030b004a400480d41400485d10a00b805140c0d504021070003c1115101041900d03501400f400342050000d00e45a00d4804070380c0c1d19040d045190308000b00503040c1d0b0342c0244002540040c100d554211580d84ca40070100800ba60000d20740d854000d1031100400556950003030181c4e008116001142e851041c040e06005540c10320441c2515000440004d800c80b907440355280354140100004102c4210941d030700b1400380d11400c8242c2a00245a0090040d8140f204150b45c101c18a400c0c20300c9440c0c24200001c0c5c1e6405 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 314425989 1250 314424739 314424751
    0x312061516030504150f0e1917010605040222060206010312050d1b1e08060a14060d0507080117011e0c0201021e0d0e160b0a0c02030d20010c0206 64
    0x100c91a542002c05206208a50080c5280c05004014522070100105210584212030002500f4000c0c401803c0c541403200e039100c002200c43c0d090000e0710703211082040d12171307000c8110469580c8901c005021340b9070340000c07c034817102c03600d0300f0403404400000c2d0700c0052050780082c02103603c020010b00010b001010000c002142c06e00302103440b44410a5240064119030400d00c039011220f5505508403900a4001610007007490941c080407040760034101e4984a044a07690b43c0b00300300c0d440c100060980e140518040c800041c02803450700301800160000e503282610110005540c00c0010804500c1c0803820190034040d0000034040d02440c10a0602c001141030010044260340e1000302d21514002d50460f04101c080e032080401c400300d241c0012409401074007a1030042800d1036201c21a01c100400c1c581020301c0b030245080d131400e0408904403403581100669a00380000c803400c400259908005210ba085801c2d514400715030030300b0030100041c2a0840004c01d252f810400b122030441c4c1c01141c0158402 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 314427239 1250 314425989 314426017
    0x6050a050f0711061c0b030a1104020d090b040b070311090d0b100f0b030a0605060a0206070c0201030f0e100c080702070324110304050114061c05071703120615 70
    0xc1d11803c118510f0f03501100280d07400100080d405090750b891000c0c1c0c41014081d407804006401402041c561100c040b00b4008002c801d0004204c400d501d000d5001d01078001c00044d00141700c80307a96440c00c0080c841070328280d815644178030821856035414043c2c22046080220384a04116603a00807550384e00da14200186000d10300c00004803520142c2c210f050052680b0100385981c5075131000d202482c1d80c0140c40701c503080ea05001000c10389081c04411644010141d43c000d1190740d980c254104c0d10001c00b050124109178551a031281402c0d4103000703003580b07115050042c02d4001c0404c0003034400c4030045a8000203001443c010098400d8004c1a1402125004540406010050000000690700406070181000e10b040e400120b015444006144035038461002004419101803203a94080700c02c440c00355104d4100e412410f64034188190744518188074a044500303007030f02c3d85800c01102d20785030500b4426902c00b01d080080207003000091754010a05491030901185020140000c1d8850806205104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 314428489 1250 314427239 314427247
    0x301050d03020a1707060e07060f05030a0f0c0801062303070509040e030706091e0803010b280203031f08060a0b1f090501030614010c020f0a0b031306050106050a050f 73
    0x1160082c04440d03d01c41d40724690b5008000c941e056452150000441030b1500c2c1e00d49210900b5012000420006941040c2c490580f00c3c1003040d81182c1c29400208441143c5848140040c0782c0181030042680401240d2034090713080d0b060100041c4841d005017401218402880100c0307803106100411250024402d103005695504003001050291212400c510301d00d210008000c6c05011040c0d229034000340c42102c5500800d005034040007200080c0c03440c05012110304000420407010000003c040c1c24481b18080c80c10783e2840c881001030412160300d400c001d81c0000041044204c0c0f0202c0106042c400920751140c0b19040030122030343e5400040454084079614100440c081d81c0d21000510403510081981c840c81d40302082c02401d503852403240c1400b181c2801300200700e503000004e696495900680d18000800700540070020032180b440507054000304c0300400410030000d200001d5108940c05150b00300200014030302070045400c164490310401100b40022000e00b40d11030222054485050040340c0c40b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 314429739 1250 314428489 314428493
    0x91202013303020d0c0602060106021203010e042f0a05040e1009060207020a140f0d020d26040803070c050303040302130b0312041d010911070201050f0f13090f060b0301050d 76
    0x100600c1c81e04065070001c10b00d43d100c400c0145880010090b24401c2d0301fa2050380e40c0c3e8420a036522481c004480b0048101800184001e0004009645e4840c1c0501c180314004030440c080340d5056140c59001044002c2003400258643c02c249004600400040c0c41c104012006020328039141e00036240580c40064440c0c00038400d0007001e0701070b9a403ca400514240181d641d462403070b5400c200f400c52050040742981d11550141c0740ca40a41c6c0c5110343c000e0111038083c11695a180d00d15040b580501e26841e010000011205d00040c02400c0500801030095540d42c0b428145495a5029a480b0b540710340c0c020042403006850784144205905a0400301141001c401000203081c544084402d916400700400e000070548d002c3e5403400107000101c00d0001282c0d0f2985003c1007035402191620000c40ba041080c81c005510840003414030b0a81c0d00035150030314000100c000c0311940070030101c030340e01d05503c0c0061100820030b1141801281245a00304842c80c6044289140350005100d958030690180d2000d0003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 314430989 1250 314429739 314429831
    0x301054602040e0a0b240304031403100302010e1f0c030207241106151504080105042105040e07050f09032d01020f030f04140a030309120201 62
    0x40840503015040d500c8644869200410075800c4410281e09424a0010038503800d0010340501d06c040c1c85e00d55581da044003543d050503180d0000e4812000c1107001c54001604060742c601541c019001044104100c82c51800010001543c00a4007485108041c1000c10368048041c0e00358080040e1742040c03544101f0a04007a41400026408920030009482c1807200c2110052030041c103041480d101d11a0001c16100440c0d0307581c40403170b07030519501002e4016008a14000080304852046240a9443d1a8480382003609594059908441e800c0c0d46040e8058900c084020121424605103460b83c20580307040e00e84108401d02420080a03c000058034801e00f1031030508458039804007901f2200d4a08101031b110004641031064981b03d01d4080042921101046c000c65407a00280d500d41d5096480780f5418440c40d540c05001202d00c60300d50810251041018003200d40024080e0b10002008626814001144900000c03c0d00440e458182c0b116542c004d5104008070b0500300c007526016480448005175 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 314432239 1250 314430989 314431111
    0x60a0e0601050f040305070611010e07090b0d05070941130b07020a03021e06041533090902010503190f1d1606090905060a0312030209030105 62
    0x450403c40010f030200611200140d0003086072203e6445003540c13011009035908940303055906040710741101004004121160300030765402c2d07200038441041c1d100c0700d03074489142499962040d210f180c0c9a5400800782902c401041110548141000488d003c441c0302c1c810701e100c1050600f00c0a0803421000c245141034404400c8002c43c0d1200703840354142090140a0f540f145804402c50040c4201600000d843d101e84200c0c440d10b100c0c0340c006101589455403085c811402084400c141582d48251024010300060040144e01031071200000c2000204c2c048034812042c5900812611410015841c0060342e0040889034080c50303038201c49105103800208000036000950366001c0550403e888000d5030341e114481c100c1c20304c80c503004a03110540d01f80c0041c04540054032840000c2009140200084030b103940040f50f02c204c1c01010070714400c0c0c90f5618041c0c2d041881c00c2c0c1600082d400700e10301103103003424803c40740c11548000044074040c1000b5043e501401c400031500f102701c6007651044030302c003040800807 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 314433489 1250 314432239 314432257
    0x71a09011103090a02030c040204150e061303030507110f1804030c142a0a0302010507050106090f0509160503030a0302090a120b040c2102060a05090406180e010203060a0e060105 78
    0x14590b241441c940c640d54680d8001030503840390107000c00c420480d1816108407001c03601c14400203001441c1c182000d172100e0015109040d00b03c002040441403007041e004d90350015600c0f07074850546401050601c4000c0c41c032551200c038040c8400101d807204950310410010380020703281c2807000071991103146c200d5110007124001400081d1071184081500c07030101342812181520b070600c81c8551000700310309140100403d60f50f0b4224a060f4818000b42d44903030018004640100d0002c0768250351110f0700e07000c96200c0002d044800d40d03070b8002c0c01151a42400518070100300e024910315100c1c240700000b52603219100510051582c00102c0b590543c0702c031442c92004020a1001d6925482e10342030001500d40111422500400c4188011a001d80b0520400d28942d2901911400589040d400c0c8034159111202060601900340038540d5960b80382e02819000d0180c8917141c3d025005410b0242042da1241d800d045001d03401401000000e484400c80441200c000000421954880c07d0060b40c030b5210360303451 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 314434739 1250 314433489 314433521
    0x1e05010e010501080f0303060d02010c03020f03041509050f090a180212030306030f24041703160e0409031407030c021503062e180b0d0e1002071a0901 66
    0x400c440144040d4032880c12a804c00f0242c6403042c03401c000d140e4030b81c4030498400380d00002980c09403001d0f520803403000c0c441501c41e00460319441c203510307800303071958106030300080107509141e112607102940000854000c000c15511849000c91140001c0d00e403a00c01421510349c1130342c48011a041d40c559186402f0728a0700a002c400b080f191403000e041d140d5004503070b418001c2c45040c0c8100002200003604a00e041e90101c4448440315015051504850003c0c000380d90004250401c10000e0046500542c000c05052404c0940c1e0220301402400409410322400d200701d1805600c0000300307422a4070801d80ca40d4080d200d40c1c1c2c0e81070a10303050f81c29120640340a900a101030413a10041c0c01d0b05401140120411143d0b030002c80320b0501c4200503003911000e5034074082020341003200484c0c000e001c07080300d0300114a21614030360b4551500d00c00d5500180c4079980b038030b515400ba405e0120400d0213581d4500980180a514001c43c940340d8012030507400c5140c1191101d00300002e54140c1c800e6101f071201205200c6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 314435989 1250 314434739 314434751
    0x6190306050f0f0609040303020d020403140604060e01050c30070507060516050a03090c1707060e030d200703060f020a110604020108011202010c020405010e0108071505071e0501 78
    0x81540c010701c001c03140c811220a2880c04212003891040c207181c89018000c0031180e00d592113640c11406034006601c40012141c0030312000c40020240240044484000002402c861815003440c0c03080c0c0c0d101003845889a4036040510200003101400c40d6001c0307552103048480048080f03d0380000500c400590304100c1030350070900503100c2c0e022004201d85c50040c401800f050711800c00e0018440c02c0c458121002c03e100b00880c0700e03100e01130340000020f0750140155a1643d903071030441c80010600c0e0f400303c000c00c1c0c0100c4403d00c641d0703070030000c3c000128505800820b0398165108000d451413400380d8140031180310400201d0003101c0b00f04507440145a000e003043c0004403a40b640d40c400703504008207180100d2088020020250310024019101e103070165500d0b40f2507440c06d07ea0300c418002c0054140d0401c0389003645100541c61782d0280718000c01120044440350362410103154100f541325004172480e034080400d9121826406010b03a140660458554459501000c031180250407034614001d0855080c55 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 314437239 1250 314435989 314435993
    0x30507441003031e02030706090503090907030506010f0206010f1a0c16030c140d080901030617070305010501082a0a09090f0b07030608100b060c03030a0b030c1e010305061903 77
    0x25408100c2e4441c1d207035a52031a0034400390341480144a000c0750016031042c454200440c00d41d070000c40c812409002600d15011200d00418020b05085030100003080e00c0c1c00600029583c40b05c242c00c920368003480a00042d505266040e004e001081c8201070b000d141c072039084910380c04000115050844010110341e40b0040b450100d0007040300c81c1c4001e5a15411501c2d000861540780c241740402040c00801c010550a115035511505410580c0201e040660380d842c00300d400021000d5000c03507091400014000309145103055829035505070480080390304150780150080480c15514407400d40600303104805020b815002c01e4007071206038040521241401c020206001d8030404000f42d0502540e0100310960b51044103500791891840f030203082e540311120b45170360801c0e682c3c4410b00401c4024910351030180c80c03034041c030701e1500244e41625010740c1e50104c1c28164034040008948a1600303440f1500c80000700304c040000360207140e6841d4181910b400c000344403a5541c0c462860b103070b400c441c25910515140c2c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 314438489 1250 314437239 314437261
    0xf0105090a0e04020307060305073f020306030111040503060c03070309020603040b0a150501021002090a0509161b0c0501030515031b01120b090402012106090c03050744 74
    0x181c0301031703000340100d007400f00d41544a4010340c1e02c40d04072516000301603810500c1c400754407107203650b03611102042c0107070410b03c1c65190101c031002903004003000340e26400d01c80c04250131500d0304c00d01284051000c00081141e902d011030002d034000e00740420b0b5510b90340d4841c8150094201d4240c001e50080c400010042084514420203003e000e009504108202c2d9000800c071252240c1d005680c05079202101a00e038842081d0001d101d0b224000c1d22a20b0055500c10100c0c1c1610010f949054001c040c4444d440d949070344c411150074001c00840f0001d00c001503180c0b03990f405d107050b6014103070406842c0d00000b030000c5586007040004d004080c00310351000e120391024107201001001090300090341e0b0b00b03941c10100c009004205640b6401020385007143c41d240d00644170317160118404000d00040c08400e03051700403140b1a100060800a0340881d403401245402011940e0050100d41804440e4be458440c0b0200d01494050140035000007102c40480d800844c81d40d01c2d2454514036400c500082044442004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 314439739 1250 314438489 314438491
    0x5060a0f030b09070813060e061e150108010e061f020d020d0503010b04090e07090608010609180b010302010324030f03020f07230a0b1306120b0d020f0105090a0e 71
    0x31a80d010000d4036080001c004006106440e6503000038410310204090004c042c019141d514440e036000103074a003e80100c2401c1c207a048811072070814802c88a1440360a1001d9034580c44008100045806003e81002030a076071818003403503014000e840c000500e1034560440025007036503c005242141c1100020081d501c0e05200c0c03000c8010700600c00e1080046000d1000e0fa0f06030b4071000540c6091034180b00c4008001e09110506060600c20400c0015204240c1d1090401030f00d981c40000c500702c0d051a49080070b0310310b516088010500305070007803004036440f032442d00d042d2642442c01281e5152052030040280018204001801c844000000200300702d260004543c0791007034003a11110440c90030425152803a42c41511601600940d0b1812103814258140c520a0320041040d52100c1d120f60502c2560b0f000070b1000300c4420b104c0347c018048541c0000000b1051294060f0070701c0000b03140b0380820ba051000c840002e006019498024900f1b80c06082905e00041000e032502d03070255a18094210034442c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 314440989 1250 314439739 314439767
    0x32a0d0609060f260a291612050403120f09060b0d050304171504060b09060411120606040e1315021204031206030804061d0f030a0305030c0405060a 65
    0x80b03000000a6800314000c448802c441842c106001d062404100c691002c00b041d80380e1885901440404c440020341601002050004031154690140080000040d0005000c1c1a03a00b240c4400c0707450600e80d80c0d10001100003550b448c6130118884d1602d2405955130f5502c1c041d02030740181021000b00044440f61710500c0550700600381403000298140c2444001520940d025015400401003403012a150300040e034005402c4038101c500161902403032440b8910240d42c1201c0c0d8588404440300503241940c4131640041c022a0200040958040364100501c01ca400554400d403564000419554a107000d41300107107481500c0200d2031a10302c44204140d621074070100c0350740701e10113280002d41d400d500c2520b1502e01d001055100395200e031340b0107460581d101210ba01111761242004000a07640d14050b00042241c0c1e191400140034000c1e00802d451401c80141c3d000c2c0c44005d070080200e590015030710301240e4160074401c2c1e0341e45402d12007803018440c68002c5500070030005a500d0410b44e2014421002107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 314442239 1250 314440989 314440991
    0x314070e0306131e052107110109153b0907080c031512010c0f12090c09050613020705030904060506090f1018030804090e06010605032a0d0609 63
    0x1036100f444080041d1800b5001410b103d041089040342c180c442c0c0450342d034550107a8100d9000149915a443d080c0000c4030840840c1100800c0040801c580703031205203020202404c1441e203036420302c140c4103507100b081081d1a04000380b41d0a0b41e0031408502d88034141c82c1380040c101060015240c4c2c2aa542260928055070181c94048005981e20340300341c0c0c0c054024441c42c0b150b03038507544550210417000c4011103542c5503c03403d40244844842403d1051074152029901c403c0c1d041c50b00d84602403c00d00b4000400e9140605280d00c4100103441d0784040c0c403d543e1030031301c000740c079445850114039080f1340c5881d41092540f0005131103060100000c050081010704550501480ea00e0f03000b03100250142e000d00030b40100b242c0001c0d01076842c080c22910342801da5031610014881201c203180394040c44662003a00c4c0c101740001c0c144034441550042e1069540b0b5034005103040d51620600070080e1000a2120344004612054a87c2802a84402034179113003aa508054540401d80268001812541324031407840d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 314443489 1250 314442239 314442241
    0x20a0c1124130618090506010528080c0a1e02031309051014090601030f020d11070b070302040807030b06030304030b0c031f1a090f0904050a060515060702010f0314070e0306 76
    0x40c41046220181d4400031803407480540b8282d85d62000c2c11020f0305890500c0401d2001031840c2c40c0f1009506182a20714810521600b101c0d10302400e6600080c0009144460400c0202c40c00d9401102c41480d2041c0d0080c80070204800c40803c9040d401000005548610740001c00500c507203658000341c5c040c402501c000c0511540c0c80d003880c40c10445404030117411110340f100042c00c42d0b000e60700210691000700c001610f88101003d05c0e0080754582581552002c802141d4030040c8004c0b144203903800b903410305046103440c0c109482c86649055601c401000d1615400024140b51000c1c4284d17001103034000d840207200c2c02d25415440305a0001c903003902d1b03190300f4150030301c800c440510341c000201c800700410450003500d40c0700a00010360104012a03040b942400c4d50100d940c46402c04640f003507005401500c2c501c01c0500d40301f82070b100c014200d10130603440b449020580ba03403410110f42010303034242031026010270a0b00c400e8000e401d000c604d000042400f40c08012035250082048007086400714165591 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 314444739 1250 314443489 314443499
    0x403061404020d0809010e1c1703040503030103170f030f011502061005010f0212070521031501030e011503080c150118090318030f02040e01020a0c112413 68
    0x50300318100c40195001529100784804900c901c0001c0005a0040c507110303020036255004170b120003104100c0c00409070800000401804010f54114918610302c07140c4c1495810a603c4156890106000c09414050201c1311412000480e0045a82c075032100b060b9036440380b030031290030f0304108d1091245007031314400e07003010403a85031002c1880ca100d02e0b0407010741c03551142813a004480b404c03040f1503188154455480c00100003580c05c806040c2651081d001450080b0f9011001411440b050400c1241143c09206100160158289003400c03c00300307207000102c6074034120b0228058011074100c00c0f405040f50b5808424004040c005120610400c001c0394440002c0340c0002c222000d00344034809150440084c045803503041034000d60b022500078070717002001f4009108401c28041e00795004680190044c01e0400450902d030042d605951200002103042c0f0464220107407180d545601c00824020328000c0305c00640e900c800c070341c00302c4040c2d6615030b02d1b6600e02c401c440011a80581d44007010a9404440007030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 314445989 1250 314444739 314444771
    0x108010207050d0f020a05060906100807120213090f060605030c0d020d170415020d0207060302031303230a02010203061206010b0412080906071b06031517030409050c040306 76
    0x14016a02900a02c0c3c0a002c1c4030301100d0544c0c101861000b10b004659280d408180c0803c80c2501501d4004007038015410150b49008517a0340c035500c5264903402400c0d0401c103040c941d800c9400820340641d4090344008800300c8210041000c0b81c00205500107122400080c003405921900590320709a0403281e150902c0d008024203215071104c000e41c0203104841380800a80100e01170920101507814141c105074580d54900c10b2080c28880500c01030340158246805603038100701200040200d41021803550906c4140c0c01c00351151544003509001506404849500c5868250030030344000032211522803003074400080c040c0d070040d200c0a11400d2442d08100170a10b010540904075000903c407145454a058003a010824460714140d405480902540e619038540c0401004041d00c1401207090105005c2250004040342d60012400c0618040391903414100c0d0310002400d50341500800000c160003051050719620460f0044004030342031409000c02c49140034040c0c01500e10644040c02400c84400c9201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 314447239 1250 314445989 314445997
    0xa050114040b0c0a060903080906010509041211120d0207060b060405010f0c08130f0302010201050a2007110d141005090606010e120a080d0f0207020604060305060d140106050901080102 81
    0x8000c0c1007080200b000c4a0007400501d1040d214509440f460080d80d04c0b580700f265400c00082d40860441010072020010500406000d0201194111114180303a19a0a040006034490005000115a202ea80f084081061102c50080035031710700e030b5071845030004401a4000e040111000350070141c0e0446a841e2842c00d8600b91174040e5681040f00d14203000c103c540510b491001c0d00e110608110003041041f03098510800380a011a10301e00961a51000900b100c8000b441810f2951030201c40e00700309000100c2002c3d0000c5030074083e0b42c89101030b00300503408071030645125a2080c15030182c0c0c0b04101d01060808100c8400c44165008000c14512410039184122002c48982d003000d00010b03001d42c001c84282e04082c0000e0811821507200800407894083d42c40010340d5407000203e0301c4841c3d40200d001311211441061410350520b02194040350b40c900031400794200381130b190300c00250300c1e46459280ca4070351504030b00b81072010b2650061b194001e100c00d014960281113028004554070405008039 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 314448489 1250 314447239 314447267
    0x405030c0103091e14010204030c051503070f08100801050a0b0f03060408030606070c05061605070f0b0304060f1107030c1502030c0702120f010914010b090906011401031503110a0501 80
    0x4a01300d00c08101d54024501810002110316152040300d00010b41024070140c405035204a001d48803440c1040100086044000c11065040ca41007003044070140d8481100400d003c89820001c005450703005c060640c00300317150420103113907107000c04211001c0c289800240714000160b502d503c0c01d0070b0103010f05868482c102c90140407000c0800108071681000c0d030040802c3e900841540d43d84903203070320000e0220340c010b00419140e0b2100c40a0001800410b0002c0d50007088000001710070381e458015039810358000108041c02455030350032900c1aa03445038000d02e0900d51041d108940c4c03000e03280b802070070301c10400d0810b5442da20110300c4080400c400d4400c8900540000301c15605102c2d299081040c4000c00080c082024040c0b0484155004824002c8100721440795112102c4846c1004c0319908442a0b01000c41c0f103500c02c1c00600c050200045003d90640f5004080244490542030060380507001c100c1d0703115040b20034502c0010030b01150104518061000701c40007003c0580c0e07030004603420749440b049 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 314449739 1250 314448489 314448503
    0x9030f0c15040f3516080d090e130b13050601060806090114010e06030109020904050c0a0c03050d15030b091902030304140102011409010203040b0108010c080f070c06110405030c010309 81
    0x1050041840705119100600300440e6044c9440c0d9051107030346000100c060080d802a03002503001918200504c0c0650041c0004800030507840c0540b01740200b042c00d00740f1454918403825070100b0100140f02c00c444041d941c03c40d400002c4c82c00c0c89108040100e410402c01d0b1298080c1c0000421082e20464849004400080070030301c09900389030b101c010581d210341540d418020a14030055058503100f01860007484804001a1601d246006000595500800550385642d00f04248549250040c4440d0b5049405181c401e031910b10a1102500a00b014a000d00141840c075000000304648104070600c00c850300c40c1034034402804640c20349080101054000e5040e00284418044010b100c0c5800640040500c0081600707160709200c044040029901300382c240e5000000c000c18400801c081500400006000708410b20980c030303004110340400307004071000500e1203011a01c914451162442d040d60401760400108100407030640e85a8814468030303000c0d00624851406a60192040c4050507405c094 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 314450989 1250 314449739 314449769
    0x2060a21060f0e07051309050106030605030f03120903070c0e06040b09070e04150e010803090f06031e0c0d0213050909070303090902030a090f05010b090112051005040809030f0c1504 80
    0x2c07000c4200320014454030070802d06002425000031506c100c58010705440600040c9035040060041c10b56100741c003d20301a52050082c07030742c2e41c9400002c4441455200b0103041d241c1d11a15000d0303045104503c07000e011000001004112401d0b2501c1031400f034001110f00b00107022460051140782601190440042100030f2055819402c043d0401c1039800805003007000032030b888841d4900d03041820703000303441e85600104541c5d4007410710241840030ba03002102c0e100e0442c03070b003030103a845040b0001c070000945818680c0450040d15060068400c160708000d400e648604441004031001c24580c41600d1080e00d001c40450b00340c0030085444000d40b6090b0b5203944510b41403c40c014041d60002d0040c0300030f00c3e03981c440840403800031615104c1d03c5d07104078000304288807110704200d0111010303040380c000049801008400600001040020200710800200c3d4503a114105440603000f52958250580100b0382c850100b2000480c140e01e000c1c50403942480c1d01d10030724500d2012343c010b9008120104640c80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 314452239 1250 314450989 314450999
    0x5060906030319111605040f05010515070c0302060a08041a13061808030f160306050a150c06181a0f071407050d0509040e010b0a05060904060302060a21060f 69
    0x24001d030f4940300302c0307003007520510600c0e000c0075107003100d55060f048541c030b403050040c4001d24140c02140c4c5488100c4509002a504190015103d00c080b100000d0503114006048802c100c00307540c507030000f160007d210350744421801d24060008201140c0c00c640c41c100e5880d04611605240a2180c05902e1009440c004802c1981c0c940004090f1244c80c061168805824032002a000b480118801c002c041500c48560a080d82264800c100203402e00702414203241007800607031161310080301124038001c4040100c40c40442d09840e01e540f40071024002c1802c244075600703400da503000502c0105202c3e8140100c8003003001800102c0c403c2c11381d02e40d107140b412800031903401d034800c012039000c1d21a00c042942c03502083da80c803d454074941048000110702c02140c4030b41c0f079140c144520824070008900078002841e0640c00503001c08094000c440c400c000104240300f00740c40700c0c0e0095000d1540600000d681c5c4503002c802908120382c180e02d9000300080c2c03440b260280007150041c01d0407264840301c80350010b4180 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 314453489 1250 314452239 314452267
    0x714120405010e03151302011d01020d0c08090d0c050a06030213030b252a0b07050a030e030d0b36041509141c081311060a0210050609060303 62
    0x105180d0f62500c2202c1d590301c00c421182c0100c86c0503d014940056a41d1540e10005d440310500c10b04100091103240028001a60085109080e50489243c080481101e618040095000303180c08141c0014001203000c0400a80407103034400c0c0d410484081841503903d80b0110241e1182c081990301c0048150000c10005000400c42c1d40c02039425070300340c1000307140d81c250b41c65203c812820010004813017200170040039089105012181000090103110440c103611040006000644400c007000b05c0054003d40d42d600ca580328410b4202040140c81e0b0301d110350700d408000752032340c0b14001d403158507443c480400c400754210170248400102030600c4019400402c003600c840070010710039521801d00c01c4804106d900684511041644071380d001c5071440c248450740d18036120003404807008600c1e1000c2004c0010f81c015454a42c000354148001d8aa414640741c00a808496600490740140700490310714081500402c074004104806130303082015650b400e08114070418151655a007640013006200e13418410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 314454739 1250 314453489 314453507
    0x5060409020c0c09070923010c1b080a030210060501030203090d0c03030f06090e060f0613090c08030c061b12010b03071809020901020c060909010b032505071412040501 74
    0x901090f200c0e2010700070045200183d0440c1d01d1000240c0c040c0301400300d4808110b600c04201d0741d1054814503299514006004052240b501400d48490107420300e0411025154035400f500d41a401c0d00e003035032501c0c580a55106582c1d40c4070240c0da4100800030445510138400d50f445540a84014440b40d0030311401540d40700880102641055158103130740c1c104100d240507034001459a0800000c55481110000342006c0c1c001e016100880302c09014445580d0720000e0b22142c0030403103840002c2d070450707a00e0074686010159000200d42d0101040510040b43c021030804c0c4202010099516000032811420744640302e0100c1d018030b1480d8582c018005810b0100103550701c0f090501f0018405101d4548088520761035a01c51400305400003040d600559060004130301041054405c1414100003800094101d04140074003030703aa400100020b00007142c229a8120603203070348500d0400b520304c1c106000b8030710b41c000c4606a80d01190034624100c0c1707000011340315624000c07a8031218180f0342804011030764401c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 314455989 1250 314454739 314454757
    0x20f0c010207050118330e0f040b06040905070521161119050303010906120f0201050a12020c0d20100b03070503160f0b0c1506010507051e0105100506040902 69
    0x92101c0000c20120010700756400d04c4402e000815106c0c6908000f65101e80d8111030141c001c200814541c1044d83e2516455603100c1d10301128045030002c00310011402138050b40e444400024100010302c20110380020007056003002403030700d400036218540403440c030302881039070707401245c2e100074814907041441040385415005039802551203426510003200e10340d1003480429152500000010042800b142c49284000d0490340700340340c001115074444400c410340e8418041d050003c006105400c02d0b100b003500d0034814075290b50454483d440841581ea9500e43c420085010414445a0a0400043c030072048089482c00c8010b000c590344003509074000d8031070040300607090301c9800d0300400d9a64080c07140402003800554903003503007854481a59080c6c1c0d129030000741c00d041d0802c0340c03405c5403901080c1401711941b20740302d8445070346401004803007511603420041c2c400c1c000d00300e9111040418101c0c2c0c0d4100c2d80100000d00c40d0352603921140078170440500c190f59018108200811920b405e50b0040c0003180e07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 314457239 1250 314455989 314456027
    0x8070c02040e031c0b03010c02070905040c05090a36140c04020f0306040606030c05070620070f0b0601030c09030311010e070f090c09050612060a0b19020f0c0102070501 74
    0xe800c2d00a030300e590030002d02548154042540030141185500c5031184016003100240160512100040e480d90510b001f81d07200540ca0b003000a0500c250a0f2110000780340140c61041d50f4a044176603000103014000300041e000001d1014510a6038094085903541901b90102c54100d404c655070744064280c89000f41181401081c45104955a0f1403016115102d41444c4017a41c915040e81004205c0d041e98001074245803505004110340c680c01416038061300d42c00a030000d070b903038020248200200d036490030b04520241d00140880410410302c041e103020b43d220769440300c12626480015029136094072440000140f20741c00400c00729206552182200c400c1c0c1c400026890352161032242841c11541003410128071004081040010902c150412914589015584681000000743c017604c01c024201e40061122408141c5950f500114580201045e0755030359903d2820794440c3c4441800d5904160250080c1440c03a401d41d040400c6a0152401c144e02601c0141e0910380152040240d035141d00c8044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 314458489 1250 314457239 314457251
    0xc040510140f0301051603050108030f07030f0908100c02010c0e1509180f010810020c0c01030b01020f10050615090612091c0c140c4e01061508070c0204 67
    0x5403800c0c45000d0003526410b002c0b68501b03082d131002900352201a400010294010004122406000d806803104179526190801c0c61040e075a5045500c030903240c010700320500501200500d05030301a4000c0131002400e400a005060001d2020340b030080c0c120113566004103045800c2e98004004400a1044040007000291103460700d0501680c0701a0446189c40020f074400c00500c0750320405c0010794110300c0072a81c25854a016443c0c1ea039200d201d03800c8101c4c1030540351084054141c0c001d0000200300c1d0a00310454100005200321240549002d03504a401440001c500016202039002144c03c2c502d000b500340e0b890100018444824820000e1229159008200a6010b00400c8902651120b80395a8502c84014082d040c2890f140c01154640440c0b40d0007030220002986a00084070030416800d40c0c0000102d5a852100d4546000e47e0740610a200164441c800e00040c0446c3ca000a034400354020450fa90325000294890041e4010080110700d0740740004144503c80c800500c0000d01c09000402c071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 314459739 1250 314458489 314458519
    0x816141e04020a020102220f0b0309031210030501050f060901060c03080402060307031b020715052a010e070f09060801090506040f05010f0504080a0f08011208070c0806010609080c04051014 83
    0x1403050a289415103280e1f00b41003c00030110355142200c050a59502d44503e142001c07085240c6d00d20030400c0700300140b0040400070342910a588203820096030004020701043c500102d0079070001c44100e82c214400c1c40b000c1e0011848a01c2044800c50040d81503c404031180c507540c00b0000300380c00050001e400c16465019411b0042402114401101a00e40044c40708a04008101c0846c2c280c01c2c40c100100030051000c0b11a4141d41040d4000c09590829075581081800d1601e50140c101020130018074070840340001070090303520328050101d901410301000416100e0704d1a600b03803802e62401074800d500640108004c150200f550818261040c000010b079203c1b00c144100a440c4111816140382d41c0202d407050050ba0018000d85085545240c03402d00c2d5810030703d07045551560400701501740c40000c20900c0801907054680d00c0a40b00c918211049983d40b40e4000740140300c41d0044a020b0f02900c0c00c01759440c14540240e078054004100c0b2040b04d07601381140c03402d00404100060b0381c0111041e00c1c03100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 314460989 1250 314459739 314459767
    0xf191d0a03090f0504020313060209040b0301020a1107410a030c03140a03270504050c190906090b16150e150906070c03090816141e04020a020102 64
    0x540d21a842e0304000d00c0c544040001c4001207035003d280103500400400c190071100c44005040036503c5100181c0f18403007030000c90000c02c00341c010a5015840000c0c0c040c8101e400110783e621221100301101e4049031203518807007002e0031003502c3d1040324400046658607442070040030076550b50b503072004100052030a000580b02c00816841070328250107414040c0281308010358071000d410070001c000c0010000ea940c0c018032811508214070034105175540344040501d40c0060880c01040020401e2081d41440e5103045080e03031040034041c140c0210b000d03e48101d140980d00c02012601030307481e40c011f498982241d0701110785c401c00030030340705804949216000440b40d00c40e0029a10120100003a1403003e010818a88885100d42e158000d1f0800d08200c0301c07000010348158088000c1c5010418000d0030302c1c081d2000102034000099074000c0155030885184201c80344402c56200500000c00600300b0028460365140d5401c1001411901c40f05180c840d060a40083c0090380c0640300042c940740180710502 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 314462239 1250 314460989 314461003
    0xa0501030b1311131e03033c08060d05070509180d0c02130621050307021002010902030705104805010b03010c091a0904021207080f191d 60
    0x35100f442d010441c48094101d500941c0007802c0803003c02c0c2c121462441c10700c011008a4403000307040002c0d0070461900940b00c0d481103c00320708001c0d21081d6034030140d0038a44140030341521410000d203545000801c07524006d040d400255811002412400342420240000c004000748601103109000300030100741b84041188140030f60380d80e503c50b00c022609104100c01d44054101c0740007d40c0c10104103006103400201da0314440c0c406240600c09412035454810300314054620060340c001c1d40340401030030540d010342080d21418030843c140c0391115252000c1080c103000f4541e0800c00500c48100c0951848814018520f01040180000310000c0c0222821000c002c2c800e08000c104900101c5000c00f0044240940351160320100c0c02804210303010f0308018074001c0c0c80e2180d10729481c41243d08101a402d00802c0b10724906000c2c000b95030300e41c0b4101510027280002c0d10340c0c2000517036504c0082c0820000c075144501400203801d02c40d188180041c0301802421540702c3c40c0000f01210090700007120020001c1c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 314463489 1250 314462239 314462261
    0x3051611120705010e0705120c01180e0c12010f0e0411040605030717370312050c07020f0301090221120301030c03030924031e05010305010204091a0a0501030b13 71
    0xc60164081c903a40c0e41030281ca070380403c0c01b80c00c1c508c003c8042c0000120381140a55000e02e8250004100d0b80b800c0c5d46402940e41c00540e01d83d1881c1c060101e030920f524010f060113200d0042d2192242d980d0100002c00e1844c6201d0703410301da2107401c0440c0c00030754010040b17840040004c00101d00700b6101c100003400c00645500112049003c503603090b0301002c1c00d01c241011000580c070070141c5102c40c4016a400b880000082d0303c80700b44071000030b0707003014002c0c8042c0c42403070403010040105140448580045901036041a481000391078500120340c9414051a1941980640440b01d4600d451201d81415100c00c45c840302540a107800c19104040010042c50085000e40f64107010b061860401804038060b6420104101c1d0b1010f400c0d2035444065110841c0c9101245000560914030600301d40100058101d0181d04d00e08050002080c02390540241c41914103054041045620a00c45900c4d00301c0e4075540590451442c0e0400c0200358000d51060741e2030f603005400c10894816106134035088884461710 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 314464739 1250 314463489 314463491
    0x131509120f0206120106050910021c052a010203063c0301060306091109090d230c0609011b05070308130f230105070e010203181f05090f010305161112070501 69
    0xa444803850701c109d0040401d029070028000383c5814550240040c0ca42500060030300800140c1c8030b902416050070000e0210380303a10042c0100d07008041c0203000c2d500955400f03206003507a421040f0100300041a400b01c000c003140092594404001624a00704030680010307034555a901000008501d240c0070311811284100c00c24070302d0313050040c20490b8802c0c018181e440c00c0c0c0d00c03240f42284229042910300c401d00035801c50700d01305070402c0410301031709100364000a80f060040e0000d100300b03008150800c1c9400c0d0b500c070289000000600804980c03034010310b040500020072a10120b45a2101c1e016420803540c010340c500a403454003500c5440c07401441e00036100322030440e01ca02c00e40701c103030070301c140340d01301301c980c64510456484040000e6485c00380385d1075111002007960f1f40110a07580c100f881030031600c100315502c0c2032015013980900650800010039004050281815040c0c6d8402c4c852144030b28003000d9160701101e806801261244580e1611202a00c98003069007038400d240400307401d0a42c45980 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 314465989 1250 314464739 314464747
    0xf0f040302131103071419020a06060e0c09010c060b03061e0105010203070b0a0f060305060901090b0c0f1209030f13090e0c0a1217131509120f020612010605 69
    0x70501c000c10400703800c9404610300d4810ba1100c0c0c0845034080320b421084a19140c0224a4a00301c041000e20440c02c50b000c2e50001444541c03015500030404100060168030200101591805100c00d68401100c06400c05942004090415809070403525205402454001a8100d580b40801c0c074156056407104603250a008210201c84000c000440c0500428406141004035982d2102c04000d00500020441511420084c803061080d5104900854011003110001d00b400c0380751034020400690f007918009107910001c4c041c81c0004040343c18070304e11400407518002a900d410103480e00050042422030004000c0d1070420b40900d40500014130300c0d1140c0d484881e14100020b42102c00f41981c1c1007198001c07800e17000990340d91601e00e01c2120f140c4401400c001110b41707009047e803991000400c024041c00b04485100c070103420b54031030039107401d1a203514559941500c250380034802031080142c44c0c0c52035101c40000400114180031401c1c4090109030900d50f26041d000d5400800740c00500c00030b030f4049 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 314467239 1250 314465989 314465993
    0x1b0307060e03150a09060f05151804030f0504120c05010f2c0310020c010b0108091501090f0b03010f05101e0504110c0610080709020307170c0f0f0403 66
    0x22048900408041c01d0040940c001c2030042910754040c1008681440c2c095400250500c6094100c0d203034543d4010000c110310b00b105986ca5008010035680b540451240d01c02d2138125003081c820f01c0700305034031903151091681d13116501151084211030748402046001d01000a0241e4148802880701d4800e5500150160400000500500c0c0c0e07280720380700300503009845900750000340d07103a2154160783c5413014014009150104e4a07111400711580052480020103401d00d60301903000965000702641d51045949032074000326510302900404100160202d4010031035042c007588980a1450055804901426908000390031200110750000ca1652207904005000541c04c0584002c0c061203003c003000701030a641c102603000d21a015080c0507d550740c001d0405045943c1c2590620380c5805c086929030b01c1d24041446404106100398000c900c120781d404244410240242ca11480c40b650b204510707407500c115442d2031818040c1c041310400d901000001e01c1302c50f80c00000d008540c00c0021803039446140d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 314468489 1250 314467239 314467243
    0x1005010f0801140d0602040f030305130609030510020a0c020603090a170310030b06060417030a080c0708090d020a0e0a0605010e03010c0504031506050409060606020d0e01020c1c051b03 81
    0x3034080c4200401c2070018040b00140d0909035203840c0c4140c480c0200d100d90ba290040080c89180c10401c0e00ca040c001d000000c01d40d105000706440841201d11181c001d43c0c0d58403e588054050000608642240441100860559024100226291410181280442c4c000c141142d20641e036004031500002103072418090300c0c2945403260300028050526518003000c40502c0d031101da00000b40304a113400b001c81c51566489050780c01801c510a241c5c544141d12190155507680401042008a0466030004107102811b400b500c4031a0340081c6054a05082003040106280030060100d9002c10942c00c04103c400000394010712500c0d202c280096020304010015040e01110150302d07119a04101c00c6170b2001e81d08c101031b00c007200e40c080070000c403001d9861241d40c003504240e000706402500c0d01c1210028021183c0001003240c487e03400352551510b9a01e0220307685503007408082e0147e07005c4260409181030020b12403c0c0c0c032a4a481a40d40743d8100c0c0d5440d400c02d50f44a03a100320410011800729080c0c502 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 314469739 1250 314468489 314468507
    0x1d0d1b0b0408070209091c050d110301080c0112090201081302041e0c030612021807020a080c100507030b030d0f050708210f0906130c03120305040b0612120c01090209100501 76
    0x254400030724290700c2841100c007c118040030b80702c0c104600031031b0f00314070608540c003c0d1036200c1d075407102c803501da40e140c0c0310403a51130030034504050011700700044002c000320315880381d45440e94060b0759428403960780c9074201d1848900408102c4c0c200381e89801d60034104804080c2c5040a8103000004600429200303002801e41d10f0307680021800d005442a0000160303600c01d01c90711f4804240030f10310310310b540d48803041c0d0405041e5040034212000000300c0752540b2401080245900703012030070811503502c1e007080440131100c503580d4880e01584450b00941c10a40110300703c1c0e1003100d907842d101d481d000c020303550000d40d03400680c02d00da01004040b048003e030b88000e15a140e03001c6160680445680340405546030303100c1001e08080000c2c0780c01e4050a0034821038040304405103070400030b9000c14880c040740040040504031020741e0020fa0180100d425464108103c81f24008000f00074640c205980c922482d80394400c951140f00c0d03642e02c04654006848281050344109100b45200151a107010005465640 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 314470989 1250 314469739 314469751
    0x1602061318060e19090c0f0e0a0c1205060a090e01060f05121902010e06030106020c01080106030b01020304181d030d0e0a020a03081303060e0c0102011d0d1b0b0408070209 75
    0x100b444020300c003007891058120303803095040f01000100000742074640020300c0819405070036006c03841c20104404081540c51030855840c600d4140044d5070b000442822100100c100304001503400e2882481034020f90800b50b0008001806804866620b01c0c0c0a002c440c6480a140f41170b0751242c0e4100404100c00c40104010708041d00c5210014400074005515150400e0b9200c9188030440908815640f0503080d81c1c3c0d110501900c1c8981d00e5071603002c06075458011280140c0000d15000c0041055480f030b006114000c1d006070020750501e41820108056600814007072000c070343d510180c5014289442d120f0410002a4601455440000c42030796016542d2104c04804039520224200300143c840066401c116a00f0100090310b42d0070f03800500f418035085a00c05030816007441e45041e6005000f042c202042c24090700200111420000011041c4201800740e0070300350848008294200c2c0121103d04030580010500c6001c882c080d80c034140c0c0302d2025101698032103000b060340c1c01141850070070284c000e1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 314472239 1250 314470989 314470991
    0x100603020a12030509100207080a2001020f0304090b0f0406090e12070b0c0c010905070602061008160b03060109120b061c0c03060b010c05060118141302061602061318 73
    0x42c601d51070103400c510616400500032440f242c240341c1740b20f20030300c44d210182c542841030703c0000d5000c5c00d0000702541042c020804601c07150103e02c50941c0000340b01d8861510350030203107082500d0000808000e1414203c116007042b002c8440c00c0440c1d03101d119100161060003c0080d451158060303003440c1c90394030005800b0020341041643c003c40d03011101ca0b9800562100180e80d500e9aa400090142c010303080003c009200f02000403c400d500407071414810802d2064500c203079961035148594450f60f40d607441c8421410004207000780c04440300115030219060400301c10300c0e03544403182040c1c00302c1100140e400c0fa01100610015180504100c0f074105524100c0d465044040d844005160300715110080040e950b0300307180002a4080c08803c1c45880c0c122017a50701642c0d64901c07920b0314002c49813100c002d19103400c00c1d081d4510240d0b800342e8020080728800c110402c800340d092200580c804101c0030381150781c0a00b03807001603032080300400300c0c0084111040e81c8180b070b05804220300140e40c401e40d4201 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 314473489 1250 314472239 314472269
    0x604050f0c030d0e04110f07110f01210b010e0a080115120201020607031a190e070201061508060301020f18011701080307030e0402040b030c1801080f190608100603020a 74
    0x55404001051011360407607000440c00d00c2000907604500c42c5004034510040d01050200a000d1302d051300040411042d03901e018106200c000445512101d00c4603151028421001200c9221403503008040920b018105000445050000244580c2c0180d019000d90380d122424802100005200a0003e00c04000140b02030307011540080d48405000385444201035440c24180e940b10824070340c50f11040405021851007a0803c482030702121010b004a405035010a40415081c40c4144076540854208000c070705190007a880048400c0b28000c0c0606606640a2100754410703070b010b00080c00725001c0c14000649840400c0c0024082000c02240b09402d0100c020041080c2c18000c4200c03144a50305181c00400e600240000400a01641e0010b0185c2440402002520510340d4001d1504e107889010412950b000e490045410103412601242d800100c840803a50a1080e0801066540705a18010402a84032502285404454142c9844a5403149800c20035800c0825040d07015050254040030380d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 314474739 1250 314473489 314473513
    0x1c0f02030306210a02040f0c03110c0703150e01060f0510020a080921060f040c0e070e1c0b04080415050f0307050a02100908120901181509050604050f0c03 68
    0x8446003890310300a4000e9443c0c03032006803080503c0390134586a4010000c001c0014144650401401202c01e0350000c0ba1521940410079104001a918404061401424080d0075507450007011808080c0a15806440d01610b2200142c2805000090b00b12044202601807400c030070480d4980030b482da01c400395000a000c40c008245030b14116141e0900940316041c811103011100701903028240d1954a45000d1038050141c2d05100d403840600480c040e940280074a5200c1740c50760f6200009941e40400306858441c00e82003818400d001c2c0c20b80d21142d02440468540c075464041301400b046404440a110018080c4412a0142e52904901e00a17140c402d05006039100c42c034819120280405052180108090301c9040c800c03c0320b0709001c414002d09102c01c20340c81c507011035560009140c81ea00c2c042d0400002d6940c480500c6580c2041c655040c2c0c0040c8244144c640d80b0f0b01c40407005c0c50748412600c0c0d640b0080071840410040740550710880c0140070290b041d01401e0304001003100e0300c909c01d0b000601d074405 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 314475989 1250 314474739 314474749
    0x703080f0f2b18260c07060311161b050402070b07021b0a0b03040c1d090705061204020904080c0102071b050a0e0c0307120609020a020606040510030b06060c1c0f02030306 75
    0x12249920284050802400144000c0782c0c1e800744c035219601100010380134413a80b0000c90300004072180c03500d09000e0031740f40c100c06c4561406480800c1400c20060a0508040751803c000f01201c000405d0704504280d80f908045000d82c5d0051206903a002c1c1e421007449041541004200e40c100c548a0000402c003410038001500e4400030310949003a001c002c0080b0301400784800a450090004081044202d1031100d840c1065241c01c551a400900a0750310006480c144802140c0d000e8640c2c1441c2603440d0f0325039081018508024100f0742c2c1d0030109204401c1080000d20050401e0350180c0f03503079860341c00d48030440310159029401c9940030300700c0e0303010400201e4016104903030031600c1190200d13102e40e9800c41c01c5070095501c8401c0c0110508018000908071429401414401c00700e0b400d5400a540707000078007094501c29207103161410398030082080400c0140c1000350708900010892480e040c03180c182540b40c0848481c80c25400e0f07104c01003500042ea0031144085104450340059402c61030000c002070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 314477239 1250 314475989 314476031
    0x9170a0209041a240307300b070c0606080c06030408160512030703150501080c07050304090c090f0819150b1201021905040302030703080f0f2b 63
    0x340281c00c050041400c00034040c3c507902c400c041070042c00d1900c1c50302c081c0180415500290000c0415400760500b0b959082c080380702001e41d649401c0402207105691744c401c0600d500c0c02d40100401c003c65a10341c0010340318a803454000c19a03569400c1a0740d0305070a001089038040d500040082e03020007016807250b200c11058075440768011403a151a0340c01c00c083c6d44410848514000d081e0b000e03d40720364141090800c00303503004000325542080102204110070340c50300c1041c020240171034129000178900703050f020003c0546078403600a50381000c0da180200c0d0207640400e2440d001145015509000e50400341030100d000b4405840242140c031040c020b400003c10b1000d030040d00c880010481d84004500b141c000401c0c6800160402c4880221103c0050007074100f00004c080b074804c0007201015a500c90b00954040e41d400a02a0880310f1a661b6160b10340c0d030203249003100004052151026101564029040240c09403540384420210ba42c101102c0212200010748001d190203145204201a00710031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 314478489 1250 314477239 314477243
    0x1203070b0703090c080a05010f0e010c0c080d1d01050103170a0e090c161b05040b0603011e050a080f0607050307050d09020102120708130608040f1b0b040b0a09170a 72
    0x540e0310000c4c00c0420b2030560541040f403ca1080f54407041c10050f056118042031008a001042a100f211070b0407070030f03282c1c80e41c0c10a00141e082182400496418002483d60300e0800c04005038100700880030002c503078900420342046ea5541ca004005000c08902170078490740002c11114a060980f00002d000401c0e07031b00340f19001e00c07905000580000403803401c07240f030b0f4030156024010180c1c103854242c02c00c3c0ca1440300c0482514417000002040d0030107015052203120000c05580c11a800e08844010b103000c01c1080481d07810000c50009050f45560514101400c03170031015088404070b004096103041000782c44481000420402c020303100341c0c4601662030a4103140d802244105003400100d00d01100102c038120380340310000d00d8500300002e08000700204c138000ea0810302c00c50b40e212003d07202c9030710403030340a0280100703a800100010800d561080d0380e01d81004000c84070685904a45205d504142c0201f5241c4200091034803515070005c000b0350003800102042c0c0102040302001c162600004840 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 314479739 1250 314478489 314478491
    0x120607050a031416090503010519181209030c0b0a080106050915040b070c090e0309090a11040906081501081209060f030f040b0109020f0a0804020f030703060b1203070b0703 76
    0x428000180b00e07412030034001d81c0700191001035082c0ba2020310020501081c90030301003044404005882d04060042c40e1251444c00a10f006402d8540503c1e40a065003818007080341c520b1203100c40c002031f0350b48110392182400740c1d10071444074118a80380301d8800268010094000d000c5c0502900950b000b84501e041d55000d00e05181c4a1a0130804200c0324040d83c500c024502c04081400b052100c0c02d040540003c41c0220560a40707141d444500c03030704031003100d1312110382504200051401410405196600000751500021b42c46080412a20342074209803c18240d141c0c40d16010000400e0400200528034481c040608003945460000c599803c0c002500e04038202300800c00000030780e540030035108082c070034040c01940c9140c204030f0400760080440701202d0200c4401c00101d41881d040c400e6404802610300301600e8080800c10036207001c0c200510132640000d2440640c18180c8040c046440154030444010038507681d84403c0281c40d0f06007e081c449954820300000d40810141101d0302c0c0c02c0364850030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 314480989 1250 314479739 314479747
    0x15020114191d0c030d05040509040b062e11011a040e03041e03030207060f05071502040506160b090f1f02040b0c070315050103050c13021b070e0612060705 68
    0x24510701504141e0600300290304404404000440c0102d54411540c604905135501034825070801d50307040c01039000e207075004103d40300010700040f41c11400c5c580241c401061602c610303070250b03441c10021500e40d4a0440030340c100c4d821070302c2c107580001c41031014500c108003c3c00203421031101c601c0b041000340300c201d1050703803510802d400c11142803046402610800320310122042c140798113401e4000c4c541c4000c5005110740600040c402e44112240a000c0f1030507540c00340740c030307540352100e03d00c2c50320500711900c0003542000005550799074100240388400d0f00342d2120010500c9030031702c083d0410009048451a4009041c001318000000c20030000c02d041d038017080300d000c080006400d8000e001d940c0214001030030000310480b100c1000192241102e1241151107001707a003110354142503920030b10004101d1f5210383e446440d28a040d542d1120503804010005003400114040c4085401464810b8961900a2201403014004000c1020390196041d1101980300a0b000000c40c1e031104003c2440082000100d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 314482239 1250 314480989 314481031
    0x1204020402090406030506010302090c03010e070f1701090e0d03060b0f13031712060a1503020306010c061107020906030a1a0c09060a11060604090305090103110d02120115020114 78
    0x641641d80c02d502c05882041107940300e00d443d80d82d500d402c0c0010781c4182040000520640c03603600449040e90300d405017145031911104403d80706d0364400c0c401c010030300a8110004070764500d4511824000c1203490004658080c200ca005c50404001b643d040c010142400014040410b130b1004403688100c2c180c2c0e40c0f50b601d028500c0d0b02c1103040929000100094038918403940c1d00d0a001000d08030398072681e18841800d40751f0744100118402e1620503482003880305880718459500913805194003510604185044160545e40d020840f020211001150a0045048002e500b0200310181d4444005d0f4001c0102c1d0955854001150000303c3c108607490186200140c210022030090710b06651005c0c103002d40324030a050f03002e005040701c03540304a614411200041e05500d030902070250015050344429180a80d404011000341422115074400c0200420003010605528802401412084c546402181d41006400c008020b220f6940c202160305011407215008104100107400c540c5078668500000c284d8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 314483489 1250 314482239 314482241
    0x106021f09061a01090e1003080f0d0c02030a0f020325230601091a1005030a180804081501030c060c1109090c0108010b0a120e0c060304050106061b030512040204 71
    0x181d000030109420011030302c601020781d04655032410b03001d88032520183e40301e034014001000304503480780740c801100e00c04001089440c0020310107001072034401494841c00c6500303c0e058524180864005910000311070118540c04921035018070314510103140b800a00b90400414280402000c411040501e80f07030804100b900e001030090010500d00000c10308100340e19032038541ca030134410000e40b1402c03c0308d00c03542140003203000c502101e0010000e0f6003980d43c0c0601140c080d00001c00900045030b460213280c070303200014122081c44070310400a250780c0c0d50400c07600504115181c40e151800080020040c0001101c44c0714072800d6030507070718202d003800d07546007844400c2c2c5142500041e00b02c2c031202c0501042480114030002c591400703803260846a640c55a8100151041c02030b09800903103145065190030003940c0044044650b43c20440328410001c4001440c250305c00d81d4200c5060b90759810407c15190004883c4640500b5403518040c2104581c5000d0298401e226406540d01d118000103401c560799 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 314484739 1250 314483489 314483501
    0xd0b04091b180b10230403051e0111070b10180f0e03090102030a1b020a060f0f050405010c060518060a09031b030905060c010207060f02210106021f 65
    0x401844000380ca941a01c0c0058800c60103105014aa00401c1c4050120b69001d4001e068070060440c00422265101c102c44140041d1505120101c19220001e54030400001501c05180a00e01820700c40c0511460100071055480403409140d0406188851080b40807050381d04842d002513140245540d1201300341040602508a07802c0a082d1050042e4482010b5010750901000c0000c05c000c0d0412a01d8001d5480c00380960203801a4000c00c01250b9841c4101d02c507c00140044800186200345580000c0382d1205a4000c440080d04194024118561000d100403100a00b8140316240500f40b0300000d0000e401d802c4e028200302d88a00c08515442c20381d00b1001d0038002e0f00f40030394420303080a10b0740c0070107441c00800540c00105c8841c540c600c5030001c0c049071401950f01da00c82c00001d9140c50141308240e0403081c000c200b195806e0040c0f0001c2102c1d40141910f03100c0303481e00141c0d10384030140c00c00e0a0800100001000081c003000500855400042842011507441c0b85001030a018003015000352203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 314485989 1250 314484739 314484743
    0x203010602150f0907060c06200703120b0a05040c020709140f0705160602090619091406040b09010c050a0b04060c120903020c0f13060902091206090312040f120806150c030d0b0409 79
    0x103c1349c1e07131190099000b102801c909442562940c0522000507040c009a80f5040940c650145c4544000c118600c0c003507100c550030001b2401507a80603aa280720402c1282c0039004500b120401a5041043e510340d9032005c0390b401500d50414a01b4500346d00c0e000c0092600c6428001c0000342e0001e211710450359042d050726249150b04800744030910480e0070041010000d03203d00407641540400300c01c00b40c0b030542c0c1503500351882c4540c0c00d41041e0700c0d140111070060407240203035410701512041101041029142c135100e10b0043c440803800c2000300b0401000c5c1506000280102841c0c0038038035000a030301007018a00410225220740070352442a00054900c100ca80e00400864580580080c4000c2990003500f0112800c541152030b047c0080c02c074070f031164400c42700d90600742c008005c10010034541b03608060f04140621146000b00d030003a903c0350850340b4070b184074502103540f01040010500d001a8040b0b41c003003a442d551800c0820134542640d0b2030248041c4032030f04a0b100c6c408501d00ba1078990004034525 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 314487239 1250 314485989 314486021
    0xa03122d0c0303050702070303020c04151a090102070b0c0606010305071e031a030c031011070b0420030f0a0206091503100f06020303041509060b040203010602150f0907060c06 77
    0x8080000c0190007400e071220210082802c0100040c010350000c1000d0007241d0701a00901b403003030a0740c8108002800443d442c940c0009580c0d2002c00e6010b405400c3e0342c034521078140520b540d090a5000649130591aa010701c1041e6030801400300c44540101e0306030340040d020f00303002c01c0544070031009558070000c103000359035000b034059075a0205561641100810104d0010050b81d020055400d040d103130844c55218036015404020008407584440c0c2c000c0101d079840c524110305008503079950090300c88081d202550281090040110030080408520510810413002800b4000052000507203801c02c111010344501e40109d844c90980d2074111910068600c031610340381d6a0700c3c14a580501c100d949001e000e00021030380c40003250941c000030480740141e4000d44005c141e42200e03038118028000205085443c1d80c1c446417071b0030668030307640007460117818540c01030f090448000306001800b107001450b80c03030f890300900240180c03c5004228202074a145281140303c040382400d00c0d078041d01c003800c2554400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 314488489 1250 314487239 314487317
    0x1104181401061a0c0604080a030608151f032f181e010308030f19110d0e0705130504030c12020a02010f0f0816032403020f0a0312 57
    0xa0348042d800401a680241c0c1040345900300b20880320468051007407074441e542e10180c00700f00484c400307102419600c07915140124203103855403001c0341010280440169402c1c008020b0000b160301e120303100701117072140c0141b01d4115451f5440d00490940c01c4112a01c1909100700b480d0404c0032410034190092501400c0c81000c050b15411540402000319610842a404503981041a403c00b8141c24100ca401c0b008903800c2d80c44145480e03017585c50213801d0b550a4050304040502c85003081c02030000048030b0661390f079100c0341e04d98120b4058070750a4890f08083e0308054400d110341d41c4ea00c10503011401850400044954441c5001d41d406503500c40003034000840f54080070a042d500080d00d40c4898401c0c3c1c2e413070070703c220b400d0020b8030a0390300c0044050114110800040c0038119011088090030704600d400306600d0506524080c44010400102042401c04901032056081080c213208a4039402d444e80300c40d11b46141c80f0405142c4e404070b0420100801c4200005031069a00c6081e43d180105820300e40d11 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 314489739 1250 314488489 314488523
    0x10e060307030605043908040b07110d03060f05060906031b07050304080703030329092a071a19020d110a0507030206060a0b07060e070803131809110418 67
    0x1c03090206000d81440720440c4a030000e0501e00c0c5d0083e03240f041440d250420151103030780d036201008a005002002f0007828545403224001c08102185400c8001c2d2000074a5074149921680d102c401c0340c0010340101402c102f0003080ea1103010890307622454448028a500e4443d003182511031240c641c0140a600c004074020402001c0801c507402140c0c82600c0400c1042d0200054824418014090075520301c942000c2c0075640c10001c441907070081052400c010306071000b10806806001a55a040c1c91403004600700c000c00000c03049948803401c2c010b0408400c2d03d018a44030170584040407001d26503d80100f1001010074554111205200c402241203460340074129009040741c02041054005110301d00216a407400c1c107030215800c2d1404d1181b107601c1e222843c0c0701c10010381141800d0340b8441c0f06503000000c254800744040c02a9288104d03580200300d14214070740d1180c0894a0340e68011a150402800001d540807140c0200444156404112032902c801011000001600c01500b01c4c00c00b0902103003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 314490989 1250 314489739 314489771
    0x30e0f0f15130522050a2a030e060106030911042f09030303040605071b11060906160503040f0605090904060b0621160c0206030406021e0d052202010e06030703060504 73
    0x3208945000c0030829544e40708034403007c1e00c1d02c107074010035505032151441c488624074a01071780c2503000d9400c0201c0c403800380024662401009911803800a9038800c01003042291001580e618405c2c01c9030140720503851040250740540032608901a003103400c900182100581c2e0050320300d540001030540741c980c0f13810300b44030005e42030895100000800105102ca49a0a200401151035421440c280d2a410039441480300c19404000380540c00f1100f84212940d8151480da1525802d2080c0080d5441c1c0703151402407003600f81144c10900a1101c01d00402c01e81e603c0b481003180d03000c3d42100b0003090b802040d20118040b441520001e90401a10038860082801c008850a0090280303010310f83d420340c1d00d070804540c5000c0b0307640000d40c410801c2001c5404a1005e401400c4400740d11581420211010040b12405038006a0904c03049030321001080300428103801c64001400c410050910f054002d80e000801980e100d08403070f44600400300100343d01307501c2980403401034903018108020782a40900840 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 314492239 1250 314490989 314491039
    0x1803070906092a0f1215080708010c0c03020607121407030e070617060d0501111602030d0327061b020703050c06040b0318010216030e0f0f151305 64
    0x801205006044001520f95554007003a006216a030390030041d4041030800c131203031410000100c107074907180d0b030b25442c01003041e4001d1402429888001c042607442c158401c0d0075500f1101402c82400419a1840046a008124140d00c004940b030200d00081c00c5245140040001034550310720707040100308024426070180e100350300c441885422524159901c517803c42c2c4002e1b1120340544140121404075403a0304004505504480c440e500104a50502c03030114112900600040080c10007000c00050950600380411410a0540e150a01003060103261000c1005102c0b6003e003841e04420401d0403d01001d80d00c0b4040308517904d014040350b8690b42c0002075582c80715010580e031300e00078208001d0b101c1c03528000b2542150800c045090a42d90390f07812441d10a40740c0307040d084855400300014065a100e122031100b62a01c2a00c441c85200d80c20380c1800409040914101e024608903250000c0d43d65900707040c1c02c20741e07403a07400f1291345100c21114502c40c03000d1580641d401c9046889070340f120a03c4c0c0301c000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 314493489 1250 314492239 314492261
    0x615060309020f04021804020f040e07120b09010f030b0702011b02031e0301050d030507030504051c05060f041509030908120c060906010302060a0c0501180b0129180307090609 77
    0x364a450720070f841000124803e2034071011100980219141d140d0034550050410005145e041030f05141e6540f50400400201315070501c0001c2c000c600a00b51080b440c0b00b0795840071016600c030703180c0d0742c100603c195038400d041c040a01030003130f820300003580c16200750021220b500102d040714480380c140c01000780d520741005d4040c000f541800714103124095101c00540f03041702c2c0000e24420603407042c2d84041d00c01b03912050b025801c0103001c00000c2816228103001c0540211800d50a404010090801c6410010301600d00c5110000100610020410310040080901e104417000140c02c1b0581c507058440d10203542c00a0041d008507580840d0300080348026240d000e4202c0d00741d540c5a9201018241c580e0720900000398042401d00c03410100521841440001e64412400050a08440c001502008183d81411201c960b400c600500c0310094104480f034140419805d04440c0d01c0542c0c10504281c000c10f0781c50b0802c0d0403401100056903408001001c0100700718502004265200c42020740a040b581c550 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 314494739 1250 314493489 314493499
    0x170903010c0e03060403050306060403140c0109080105040203070501180e0901050702010b150403032609101a060d0c09030b0a02040302100504150806030c030d020105090712020d0609061506030902 86
    0x45184a68000c6002c06040e000080103020b89590300e590a5880c2c1e080603101980000040c84003200051454103610070900200c0001c1080a0414000401c0442260440ea07010f034142014040140c6001a21174140c0d6824240445c0c01d15608006000d030f0090303580b00e01d00c01c590300c80503c01204010f62140c0e0049070158001e1000410860a0001d20040d0000c907407d203000401c002c002083c0302d001107006c03511802045200241309038002414640007035604480a03003000b0f001c1516038003e4800d030000c0f40e09905107030b140c2807500c1e40000d506008224800c4c582030b4840d251030008903c07900354000615403200c06035009040070110300c0000c1d00540402ca00550013842c1c0c1d0003031f89000c2c500b0f444c11200075003200035810001d41800c5689010261909406204880b19000301d680c1c14080307000c030004030342e00001d1140782c075182c0e07186031001540c0078a4400e0008684c2d10003507100c0c1c1c0071102015800c40c2c0041685045441c0001c02415104442e04004681440108440b03605400c1b0b00300c035a0003150 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 314495989 1250 314494739 314494751
    0x1112010e090d05120703090f051c020d0f0e030102040b130f21020409020d14030d0f0c05041203120908030406231f03080408030309070b0903060f04080717090301 71
    0x1a45540e81c07142082e0b018042a41402148108030103402010751001840c82d01190b03104207a40c0324541c1000415040341c19800100010381803280c906001c8050142603c0100f2550101c644041c02d070f402120308003c1008850106200c594a09404540050044000480e554117020484112a116500401d070340e240d004440081d0005415030901c200d04001d00c80403204203000e1303007008028051454101d8000c0718031030740c4402180c11411007040588041d00519a100b1107451040121400006a107041c185080e14090b950381c0e1002c01e45040c0c652900003014045103505090b200d030b55800c605520100c2c1041070344030400c1400005103000301d209120134000c0e087c4420980d81c0011030041c8900c03a00d01840000b038980700003078142c40c0382024a00b400d00013280d01c980380d401e8540c0c003c0d004480103a00c0001405004c20082008100a14841c0ea14070b0501e03d0820000351a1340e0017030684000708940c6004034081c031995400b1282d01c0d580c0990103445429000505005c95081610110700c40e5107404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 314497239 1250 314495989 314496001
    0x80a0e120d0e0405251e020118022107030f0b01060c110405061203160209160c0314041203030b0108060402070b0103021c0c091b09060e040e011112010e 67
    0x220030350580407580361101c400309110140300c0100030080400c0315824140441d001c901800c0710314030444a95035078491711074291044c1428580512010b045045a15002ca84035100c01c0491500403400d9048482e100740b510022058001741d101440a40800e000303518000040010440061480d90b00c00d12070300322103030781e5000140c800741c00c2000007900f2103110034940c41140c50290b0169070311420042c85861995070880c030345841d50b04003041e490a44c50710b200d85401585050401d80340d00032110104c000040c0741001d8000c0800104890007030622128181201820140750150740142265210a840e2244242001005000081c0500d404511110042070042c2024001c44400d0385d0801691300f10b90b4a15030034094a004041e01c0b1203080003a101340d000014019080d4a0000c0001c0d40d0003040050b6072422380200c2c0c04185035023100740700c1c50207400c0040e83d0f00000451c4041c03400704c90000341c018040084501500c0029090200b4540001c4c110380e0301084c4451190607156040810000c81c0d480b4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 314498489 1250 314497239 314497243
    0x91002060a1b021f022104110904031403040c21060608121804020904050c0c0c0105090f09130b090f0105011d01030f0804050d0818010801260109080a0e12 68
    0xc0350202d00103820140800020042d004a021032041e001da034010f01c0c1c14414405901c0414010114648122440050105020103e500124185011608801281416540500002d42c41c0c441401d85d01408400242803000c0003803028020059107034201450300391071000720511414100110303140ca28020000c229100005a810244000c0c03101080c03034981c60540c104070b0b03103200e4046203501070b40030003031103505445600544d40550b00d2a100c10744c6510340d4603e03441c240140721400fa410001c007805001507036552039442c0d80210300f00f034901c9241a204c081c040305100034080d07005050350140d2418040300210000e02c81060b5080d40e0300030040e503601d6101e04130380b142e0714030b000c1810710094200500224092544012521744a5012946407a5460020130b0461203290002d6880d40b6020507490b64440c010300400140031401d00c1d2116041d0306064079040c07405480404510240103d0359507082504095101d06020703034000180503240c08803010014460201c07216454004c95070260300c40988100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 314499739 1250 314498489 314498531
    0xa020a03080d05071103040513110c010b010915050906031306090b1e09030403060e07090c08011818060c12141b03071b03120207120912030206010b0708091002060a 72
    0x2405c0060351038203180004100314032840c074080050550341c5140c1c0d141c200900d0001400d02e010304c00c0001c0b510640b07000024101d9a03556010001c044140002e0703012981c3d0202c11200d1090040b50b69685070740751b1000c20380000702142001082189001c031404140a1540c8405202b815005028001d01402800da505413550a8500c03400c590700c140010f20000f281d070f40000909102031012250312641e40c8504105440350984043c011a900700010310000c02c4030184031107003240c4880140255044188201c2c2c00c150501409041650b0700c21309030400c10301c04c000cc40504045000c0a1151101c2c00d08842a400c9042c0d0340c20003020411010f8640001103103040c1d0303200d00403a46621280c2c07060240540c42002c06104200c0c100329212070042031405480c4043c1185501800c4054801020004080c01505203500001500300f200502d410010390300281d100e0564068000300c0d030702c591103403070005141c3c001c0f11002940205000081c41c8529070001d070f841d2090036454400c0c41181780d82c8581840382c4c42 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 314500989 1250 314499739 314499767
    0x33050f1c08071106030103060e01050c030402030a0609020312120a0605030105090a060504030e180603160f060e131404051b0a050616050f07050102010e071508090a020a03080d0507 79
    0x1001080500441e0204010b4020316000d40440d204184405002440e558402d8004546190f030307500504e030084200348a281d520590698140c0d145041c142c000035503520340c80300300401c601d841e0040e007011034a041c021400c98031a0643c5040c3c95203002160201c0d9180210703210791a10b898800001960301d41401420701410720000607000c440c003151560000307048000d100381d061002c2a034100c0703184c2d01c071175106285610b0303007665140760b5040000802d420044400107038040b074000382c20240845000818003038100c41c51406c00c0e5210140b1003011689000705c41e40c0711201146012400c1400d280030300e0420307103da031007103013617409038008045040d000020307404400e03411a0708048280000d080c85e0b001828420709040071100c1071081991000c1ca4400072000d041d00365040300c0010009945c09000c1c640e00c00310b02c0320140621900b00340c448202803a288400b10104104075011456003941405426402038000d0807030034400307850703080503043c0b40c0c800100f000700b081c80e200c00100140d02c1a928030140d01e03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 314502239 1250 314500989 314501029
    0x21b0303130f06060e0c030717071215120f15090503091309020901140a0504020403120c0311060106022404020a091509150303080108030c0c0433050f 66
    0xe1075526072003055442d561003100d90039a18440420410020030040e03200d0111540280d0fa00e1400090050000c0750305020020852100340a01c480b1581010b001c0850040d800000914860580b04100f4030100a600036002980c10804500034000c980e031146c80150301881103001001020700200e0704460100401801e15001401240c1d40391400c840085550000804089103051040d00080c47c448070a038000c10441840205da40214100448801d00400088a04608061a5880305d142241c0603000400810002c441d0200c02c00d404ac851002000001104072070b410340e180e5002a5640c0e020201c07541e8a010141661040000f100e46c8441c440d550242c045481c103480c01050b10050280c3c4910341d41501380440700400d5000280c8110241c40740070300500001c0d1451410b01404803135060700f18010720303002003200090600d400150419000c0b4242e9001500e0503025546400b085508001d4030608120321140b00886201e4000380026601c04641d070540d50843d120400c210603d01c0301c0300d41c03410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 314503489 1250 314502239 314502271
    0xc03120909060d020405150411090607060e0304540c031d010518010603020a06050901120612020315060a06050306060409090803070809060709030f0302010b1201021b0303 75
    0x26041c03005500c0d802a401615100308000c0603800201070302d001311000400e503043c541050600d45800d000701030700089800e08607032a048420000c6001c511420030090030031511401d01d0508100104100d0b001419404001c0642868642d4100d00c04c81d01c0d010300180140000900c20030030040e0056404621444010022a4601418a602c06000c162002c441816511040d421540d0520782c2c280074404245000000c540ca003010440060011200d84216942e1610100340700503200c009401068030200e050040d15420414012951683d4194102c0c8115090807000100081e4500c01c00e40514400c5095070614802c00030040345010040300d40c0740d1703c00c044007001c0081602440041d0707003101c009007030f6507e0203032554000307015141001000c45410701c1c00820850242d50050259400ca050342c40038103428145600c0003445020746000250000301e84243e500c0070103000b54010010705001a185840385404420304034001d41000c07501d10a02c0e0040d801c0c0a0001c800030040f03920407079500c04a5054 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 314504739 1250 314503489 314503507
    0x80706091203030b040902100f1d0607080c1204060f0e0108070906140705030304030e0901090c020a11010e0a08070602010c052701050706091b051e010822050a050c0312 74
    0x54804d450b1a079801c1707a601c0440f10f02585900240c0321038010584c681001c203040140c4001d000c2920b007944034070280541001c11404e035031200100c6090f203400001558032600c00d0746c0385509201c04007450343c0f0748003000600054219040603450311181c0c551303100c101c600144000196007101c0700300c1e14900010a4000c041c040d0a006055880060180458a9060072803580d14246958400e0380c0030380100d1409807003c1214900484c1d00e43c0134103c5160184400068040069038425003280300505c002d403141c400c1107150348100150342d0480320040004207000e40e60400141c5820044c007d4100550900307a0f9101034500035000c4501001480090055011912880c2501c5c0c0921001d240e0400c02c0400c6113501090050091807445030185e03840f042e611140c40885564a141640f00b0307802a1f10844441c81100e0f5240c031241d401400a0801050300d648480e0803441000101441c000840448070425045c480c0001d90000018812812100d255a0901c105030f940c01002c2a03094103140b0030041d00207 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 314505989 1250 314504739 314504741
    0x120c05360721051b070503091e040c0c03020c030102120117070e0c04050307150e0f0613031b0608010b0d1a1201020a0e06040b1b07120302030408070609120303 70
    0x54407071010310340074003185038046907003400001d0381c124101e40076140d205000109680c242c2c40440700c40c659108600e41452507684940f81d00400c0c2030984250500240014943c501305030b15031034624020001c029003c1508801b5109142c00360b0305400521074140010b072941014400c5074131225905407001030680c41d255003400b40300080038400c2c000d401407800028000100d400c001c1e00a20103018120b80707980c20001071514041d0107600040b0301106850415030010f0f04900c4130500310f203040e591140500c01003004104c19101c2c0805c20010031140c82e01c00810301c0810076100420784517074002c00420954034801110059000e00440084038000c01000450710050b51085008200c010442294450070a00080c2e0100d00160400d8030382c2d4002403801f003020742c04240b0181e0424121005403d00e414001c0b210320501540c0c82c8984030a4460401c2c21220780200329141c000c1c802c05020002076007040c030703009440303070018440c6026a116101c80070480b103002d89004000d46000000c2ca0321110282c2c2c0b4214 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 314507239 1250 314505989 314505991
    0x41e0203040819020601140334150f0806300a0f0c0501020f0114010611030403060204060c1509050619140708011404020906090402070c120c0536 64
    0x8a207141c1c10404000003031108010078800f81c105030003070049989400f00c03901e041e114111156129400c030350300008640c90307000e105034610541220305560600142c54a4281f0f0002c0d6000b1017010082e01c11404d44140c0c0c44503034480058507596400070652281020b22a400303100c2282c0c00c000312014407080c3c0100c83d940d21081c201403104d0003290180d40e02d1741c86620700140011002d44a60750410014080d03560104030114211540b54001c000d20f00c1c3c4060b8640d907011060040030204000c0040e806014a02082030341d01464010000319a5a40d07070300c8000d0652908820115808080e480600b0f004122078403a079410a0f4100700604100d54400d2030080d10341d442060310b20110f580c0e035000ca400c0300e9000c0c20403510035007450729400215410043c1c0c0821144083c2e020340c2c07040380100041d041641301c110640d90680400d8501503110b88961a1407140318000b500011a021030f4916520240800d46a141048070030588582c00c5002c002e014401b61600c001c3c80101c0f102d103060003030040e00c41d0f001400d6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 314508489 1250 314507239 314507243
    0xb0a03050c0919020a0801150203070f0b0a06030c0902090a05010f1202030a060e13150e03090d030324090c080c090d0302030d090f1118070509030a020d030f0905041e020304 76
    0x520494150054142c08a0300300e45c0040b000103000c9001889011900c5600400004080c00210b04200340317980c1c0d80d0501034140000400c03086615001c1001000eaa40107040036540c0001c02046091300d035440b400c001d400a0780c0551041110410008003540515103100d40f030a0b2a9444110407500743c11a0380c003a41c0041c5c85000313107a0350b9820002300b442d0a590750a006150490030301c91084010704103918008180440313468200e2a04d0440d441200000048821400303046e9607604050348603090a40040c4803071400704040500d81404d51446a0b101c120400070354181360010041c00c14500000c50f000b03e4110f40304881003800b0080c940f103130700d004007400c140b49220344100d03890960b440c1c5006040d0b5600e12800c4904541c4000b0103001c02c494441100c0c00740b002564032500c0c25030b42e0816030252610181490082c0f2200051003610364500340148516241c01900c00780300c060403803800500d185079250390035001880e08400032034589451b00901d900042ca4100c0c090480e805904140c00a41c0040d00c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 314509739 1250 314508489 314508511
    0x5030f0702030714061b0406200109062a090b0327030d0f1103040302030a08070c0506010617090d050901030f150801060e010603050c070f051608100b0a03050c09 71
    0x1c00181350709407841c1e1042104000360406003007140c1644104607010000c540000d8041c0700501000f03a01100c003803110300200300d04900c503005c12098140108001c0002415607402c22480040d8040e40a68448080b5011020b003112400010406c8882c560345d80195104240b017007001c03400c60760380314007030180e01d0041e80710a12001d0011040c42c0c0c65640202c1101c10b8040c0c84106001080502e07210344400100403a020601c0c40c6020307a0000d403288030f10b282e00001c5c810741a0101d05414828040503014542c04030031240e66584582014001444100b40501c0b20560b4200040b09933202284d4000d5080c010340341d0a06200d00300c40194042d00c10448102042a904c800300e000034410462100000d240d20800090243c1c240008031001750380c141c121001303040c1003406218034546420f00b22031600d5084901540c201050b4580913040c400807950940040304003030008180c80c600402c0d517101d00c50001508000c600314107400e104501c5031600c0041c1003500127540014285c24141c41da0340d444020110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 314510989 1250 314509739 314509747
    0x17040302031308060114031c0c0c18050a0e010c02060406110d0510031406010b0d0902040b06120f061002100c050c030c010204180b100e12030403140d03020a05030f070203 75
    0xc005010b203001a030007100541e2054004110410400c02e110110350030a030068154400d07903201f0889010f0f40801020100080b14481e401409170780302c00d60014200b02841c0c08000700c00d504140000d4001964141d85007031030315070708000c1202e051251201c2d600b01c17034024101c545c1c0c0b60780310a8010034020717501e0a0807810070041a080c512991141074803842900800f860000d0071410642503422031940c3e469140c0d4032000042c4890724890080e600800c1500340086031704005880800c0c040c1092803c500c0d081030700441c0001e698054103900360701c00c1c0c0702c1c8409250f05c0d139100b07401c100b40450340706940390150b040825000b8520340329030007810300c080c200e062891400c1c1110752541d180d94000c6404070190395000c20144214441c0400082d0b0007100460240308081081e000551100800486402482882089035285443c0d1003444211a40c0c41010781c1c0c0c80c1c6580742444400c00d03000c035510608a025102c58014054005e10a440c10712085580d51821075035900354a0b0a140000790101e815844184 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 314512239 1250 314510989 314511007
    0x8010c02060108010e0102040b0d0b0f13050f0a02040b070201080405010b0a0b070512211506040f08010b0925120203250e15130909030207080609030a1704030203 71
    0x40101120444103600510640d807410742d003182100d08010b1a4020340e40104000c2081030850f03416160102c2003c03000041200000b0009034904460b00680b58000c1c2c4282402c0c1180c207031607800540300f4441c0c900741804036a03e58408004a100314001c101895000b030140402651044a45075400b0f403242000044a2492100140510400354019806090000740020801c041440840240402c682c0340904000301001100c070b80c0c04000350246010002000054807030030b46105c49070320003100508000c4d03540b034468032120320022181c003800460b50708001034904079080c04580c1920442c2481c0a846102d01c032546007038032400516003039104100c40281e000c641ca2506100960103211003001d813500c507000c480c00e11000c01400d80d184900380414006682c40710348407a08408100071030000721980e03a6422000c0e941e50071050340c01042000c1c0c941200d500806400003400c00a440d082c0003121a55503504030099070708d21507005800005a0704040400704400c102c40c0164203c2e1081c01904e003000103003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 314513489 1250 314512239 314512241
    0x180102120109020304020a06030603020a030609081b03041e0f030b0717070503070f0c03020a061d0f0105040c2903190c090302240f0f09060403050703020f0a1401180801 74
    0xa0b081140103070390010a00003180b51002040000381301c18103040c00f0051654002403d86901403101418003510361480404011002c0300311400b1101c85811081000c98940700c641c1d81c0e070814043e000c4c0400440d4401c1218665070004142142d011041b41a0300a04556481c000502e010b0044414420205c0d0118004490000e6580c404d01403551000d0300c0f444c0200f8010207902c0d60810300e10a0000711480900802e0b03012550103202030300b0100204000341a1450122a41035282c2c122005000e641c90028603840190001c0d4040c901403c0b088603403503247c003880c154010325042d511040045100200a01d41886005142c1c00003045110032500c1c07000b55023070410303600031045100019801c40001e20452805e001e1900c69080d10030303c100c0661000041c2c090f850f2040f50100910880082801004c40d00745504690000078003801560b140e6590386041076a03120117000807485590034004540b104d00300f520702c41048821001e401c0c1310400f604801580c821090b20340a100e01c0c031500d400456501d1007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 314514739 1250 314513489 314513491
    0x90103030e0306070c0b0f1b0c0709050109021606150b04030b04050d080705040620011418030a05030c030402040b040612020306130b010e1f060c1202120318010212 72
    0x3a40754040740d828040105030801c8001014102030107803807002c010206100d924055849402e03040c403108281c40e24a54050400176809440070f02d01c0000401c051034a00c0031600b40104e40780e0701c0061026903203840940c026401000441121078410004180200d0050f810940240824022001c24951100d6050070b071640a0b801c00c1e20010344082c20301040007000c108480500b50145401c4006060803007008005204074401c0d07508100071a14048421040c410315103072040036500003007100d4060301c155007503902801c03580104010440e10300701c000090084125411034080b030759094510b41d102d051481e0280c20180050360095034940c41a000b40c1c5a900c140342c007070220b40d1070350000301425104251401000400041d031802c540002d803800500800740c1c081c156400403209080540c1c40b09564075800c81d96003510219203900c5900010025000b154040040c1d0050070031544044512806981d40c007000c088042e150102000000c41401e60780c10b10a09141d1450009450521200c80c00300300224 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 314515989 1250 314514739 314514743
    0xb06030424090803130201050c010c0306030b1b04260a1104060501050f030f07020a05160515030708070f021227031605060a050405030a111e03070513020405090103 72
    0x14030030000a00c1089000030404030a854907000e00400c81c4070768481c1102d000c003405114021441c01034200c21a8000c0003902c1c00e40c070182008200741044c07401c008016100f2840309407031440201004c19440c00700c2e091040c400024031031209141500c1c142c0f1759025216040c81506c1d6407601d500c89082c0240d4280480c48007240101c845000b5003454030100002c40b190381d805075051000402c5604c0c115a01441503030b41c8a07040c05042012503840070402c0c0d040c00c0000310020102c0c00f9000c1101060139551054106862060300c080c1c1100780b69190000c07c61101751158400301d0352010000b4410340c8149003841c414841031060f2a10304100b120f82500c0da4100780e01c0c2d42e85254501c0d01d46040e800c91780e159a11210002c074000e00c24140340709002420303025180a881d01a000020310042c13036030700440403a40107200140440301d541321503042c0f40c980003195030140782c03040f0741e4150f035102422581d281c40013054030020b001c0c0080c68504410001c0d5980c6800c1003003405502800300003016525801c120b80258 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 314517239 1250 314515989 314516003
    0x4152307200d050a0b130206040305060126031e0418050117030f0a0503061f020c030d021b131b020307030207120c0b0c011104140406050405011a0d0b060304 69
    0x241021107900c4162244140540655110580c8101103031000481c143d510350010b90782040c0d42c95016060003c144202c401035080200080c1c00402c1200c00100d0701c0c102c5280006025061607041080f944130704040025003584d44c4240103100e030544035107914004024800c100c492500e82d96403403603c1244079401250500a0f540c0c40108080f1555010000740c0c40002000b1318585802c00340b41295034011b01d40340c3c10410030b02000240d40c58840061070f040c003803c0c5009001e407506224a0003540c903224621200c0c081d0180003000103c03035000060341c84c031b0031a15044c00341040c8008000d10034050305119055924a4541c0c4c40f82405480c1c4071030300005440a80d0103199901800d0601030b02d81400e5900c130b2010046c7c4070ba81c01001c035100d2518030302511490440c42c1e03555111506003902500941040001c140070008000840e96410410480f10010030356040c00344540d914204030440b5800d1190316581e0700ea04040010f1000010000c00d0f00304103441c0005540c4c1800004240e9980086404032a10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 314518489 1250 314517239 314517263
    0xb1606110703030b030a0c150302040803180f0d20040b0901060c020102120a050a1d120304170102130b090d0b01320109031509060908040f050604152307 67
    0x45036150040500000081e4010010a5001c0d1f90700040071856100701c88035030005501c8002028804e404890042c1580012251920138071342100c810005529082480340ca400480d001c0242001840c140d4101d80000c540d81080030846200c001c00354510800b150b206a0380e004c207180f1641c90703c40040c064032055880104210030380c800a86002010b05c07808400b43e03420320240d0000d0340c0c0007080311880d0410b460b1042c9609600318020352154000483c003a1312000700031400251081c000080d00c01c81e13a03ea440d010b1003940c4180c0d62801c0384030300c0b640700c0103030000680140880f440100041800c080054004003508030903444d40d10b5064001c0c0c11041500c1034000406030031140b40401e00020b5007070700308402800d60140d00044d01d11185444000d04e030380e12099040340400d41c1580100002d941101c0f00307002c4941140f403c1c99181d4800c0c02080300340c4d4058040811607003802c2d420384e01980c1111014114180ea428802e80da24000d0020150300d606460b4206100300099030041c2420501c030f95810008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 314519739 1250 314518489 314518493
    0xa0803010b0c0606010c050a020d0312051515040803090f0a050907090603050a0c0f080402060409020c2503020d060f060909030203090f0907121d06160311030f010b16061107 76
    0x300200540411704110001c00802c0104130040703144601103078115200c4440070400d11f02500c40a0340400f0246000c3d181c40100440c06008000180c0b03168800c95151074501200c01541d001d500403070088009641c024030140c0c0f02030400a10628494a00801042e003250391000041d9142500325120030020710f00344410801300e5054010190410030744041800046000b4400800c900042c00701c00040003580c002240664850340100d802034461410309656408055132401d6840c1d60500030b1114007040380b2805c8166070b112011203810780c0e03402000002d0344059600c0301006001044c4d0002d06040e40c070240026604083d01c940341200703110350041e64481c52004200040d40180c600300901600311b9004020026a100749140400d0328180400a03607485c0800c2c40c4024142c00c4c1103020700b14400c1c1d10920030b100070f89405483d000e510540e0140050803080000001030700064601c031503007000c624014002806480e01404200d501424021a0003006848200075142c040c0640c10075050b0024004003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 314520989 1250 314519739 314519743
    0x90f09140709051509062806090611061e0c0405041a13050708060d1104060602160803040e010302120c03010c030515011b1b030507060f12091a07020a0803010b0c 71
    0x1d0300c0802c010180700c13255500c90210b02c0045005091501c12590100903030800004070020810107900300818800054661001138a402c0c40c6000708008903506142c00300c1c071501e00040061003031042546c040c0811481e8403242c00d9449010345500e508800078480818a52160f00c90300b1540d107441001d075440040d103081400165901c1d61402d081d010b0410080103000e83d04040440d40007841618450b403c0411414107020100350000300e954006c1c14204005080750b400910803050b41d07400120007070419602c8201d9640c82c803a92180d40f4442804200401c00351500c103c0002e10240c400b41914070300e100704000a400c45009007039001c0400d40e2142030104010721081400a807910071f00f05119490b050300308000001c0601d03180103021405e00c08003a10000c08000c03207071f0000c56010341100c51a9460b40da0162050b403074801c07480b001031041e42c40c28422200b54090241030302d81140c1503190300802041110b02003400104444250702c1082915400115907500850080180024940e2218094584070b4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 314522239 1250 314520989 314520991
    0x30f0327030a0302061506040e04080a03110403170a050d020309070618140411190c060b09061305100b0a051c02040e0a150e13021005040f090f0914070905 68
    0x7402a8411402d0a000075000540c1e540c00c09484000c0142d841141400115148166008101c1c1c80d008641800200502d07000504251105500c007481105900760b60b02c03450380250b10002d445800420760882c003a040d000000d00c1c8524103071420030718101c504d02c0d0200513a8803d4400b11682c1d40b05400030072486e68051034030451541c540710315462075840c0c00c49800310f03101c1d21070440f4404c8d0b03615640c0d0220110210200c0b00c0c1101c07407014210b0040f0203520003511004003202c2c1607901c1e0b41030510905251400000d0035105150040107100050803440b4040000e00004040040c2810240030125000305004068804681c2c0c0ba907401c1d0392a01105111a0040800c1800d00c1204ac01800240002408184082d52003c0b86400002d01d042e00ca25503050025400d51108107181100300c01d0000d03110001a007450450b00940e1441c0404542c80f0007143da901c128804c849401c1081d000a2181008641002c0850007034100701041461a540366a081090441b42e00c01e09544909010031080f19140a12 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 314523489 1250 314522239 314522317
    0x507050f192c030d0f020705040e0c1c0308060a060c06020a11070b04090f050108060412031b1709060402010206060d0f02030d080f01060804020a0b070813080c1e06040311030f03 78
    0x145c641481102079034030702942c011103100300d80b6122951101c0b102080358440e41100185002c03c003180c8034900082659031180203400098030000021540e0031300c0c045003811140a50f840142c44556901d909000350402001c5008002c8402102e860b050420803104020b0109449840ea0300d520780024481110b00c0c2091406202e4201401000140c801081050f441500001e6140004013800300880c001c0c0b4401c5101c4042130189000d0110050303010005003072101480d036501036980c4070f0503c181d079690f100315002401a80300c02c0014040f8185008528520703480751581d82c212540c41d90000307003400c030b1a0072004002107441e4204404600080d10060040c806818a401c40d4142038001c18a0884140a80c86a00200185560400c440c21040716040c20400d4900202c107512544415100d40d280e0000c01c0c811041242c00c824481210300c00c140001600400091400c3e04d1a0b41c2c540300842c0f141650b680c517000b043c90050701c02c03005100800080c240014000307056014924a00060400070041c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 314524739 1250 314523489 314523497
    0xa0b01090f03020d050a0b01060503220f17120112030207170307032f010b0301060501030209010e040f02160b07140708030708180d050d0507050f192c030d 68
    0x2041129031001e4981e41c080c0c98041c2c1c0e5541152042d4204240f82c100403e00080c070300c0c120310000041c1c0320b82c072202030741c00b42c05c00f06841c1281c0f000c0c120a80e503114410b058042c1c6002d00d298440c1000034296050078a0622141c200ca6041c0350100c0d66074070086900f42d2003401145400d01403c8105a41401204064a03160003c00381072045442c1c105d41d207000d0508000d05100006089644001049100001c0101103040e5221144007a070000c0307019007242c1c02c400d0b01942c00e00c000811158007034025100c210740103a641c00000075100c0100000313001249804220540d08000360090005003907031009016016a00010280c202104001d06080c0341080c810304800041c00385030000f5080d1412260032111510b0514141d495070342c03020855003180c0307840d04c03003500c034480c18420081c2d0440c007d08401c0c07a80100c104200c0d9268041529244500b01031410a40d03070801014540558a050b004000c070351502c0c0005048107038040200c80c070160807102079003000b40d01c0c1074400c9510301005604111030091034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 314525989 1250 314524739 314524757
    0x1a0a0206070507020f09130c080d0516080d09081305030a1104090c0f151106010510112508011b090603090503161b1502030306010c1e05060a0b01 64
    0xc0d00c51502404100030060300180d48420b41d07030341113583c0c0c2d1149130013070131901c3d00e00b0300c0b2a4072903000e0b81c0424201c1e65081c0d0f0901c00034510030041201109a19261a0340d031800340c4d2070551910703005480c001110700b103106000840304100b091082d1403c140c8102401550b8003000302c10014507a040340d000c948a94003026404000502c21200300d40b00007801c0d1408035400c0c00d42c2c41c002c400b10f2400d401c903100c180300801001500f00480120f01c40d280195403181d1080c14400c02040d5102e034804d002d200d0f00b048441d03000c4000c651080200c138400000c0c034002d452509040000d41a00440c142c0c0c04818044404a414011040c2c20320807002d0501000306807421000258801034503540342e5208003802d0507a545c0518003401424001c41c1c10b010048584031180b07c20320718095000c2c14082e10a007402e440e40110200780b0712044004802c2d4070100750011411aa210001143c0440a402c000c07505485504c0c4003540340c4040720302510007503100300d000e00514078002c07482c0c01c112801048458100050b006d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 314527239 1250 314525989 314526007
    0x60b03131b180902060d050412110f1c050d020c0312010803070213020309010f02130f050102030a0206010b0a0c050f07030b060f130902060903060f0103230606041508010c03061a 78
    0x3030700c0d200c031106a0b072012500b50554000103c142c001c102c030500310241031404000070090b038200241d00d1065603844401504424000c441d03500c0711494104101a8460440d29541d44ea9001d540002900b9520b042850052080b15010680e007200d40680d55030350000c1296010000c041c0c00050141040c2c000640c101074668002a00c02004490102500d40d400004201c50341c1d82034212002300110030406550358001050f64800401d11481401d06180240e040440d05610120449a50a038580c0c0100700e10303400c01200300c0441c3d021103c00c105010312100c9008c0020810301803c0584407000c006000b0103461810401a01d07030008028601ca280c00c01010f581642d9100360b0300618041038080010681e40900c00318155104044211758103204400c00c000d401004022401c3c1030320b00c660309050f0300d43e41c14224401d01c0d82e01100b09890640121001400500380380e400001c0c07280600e412142d480d0f81e00c2c0c0c4040d01f1030307507010f50300d20000e42c80701000d00c469400d908804041c00448600646015045 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 314528489 1250 314527239 314527259
    0x1615080c03040204150f030c031401020703080718050a0602030304050606190e0a15080d0e030d050406030507020c04020310080601300f0203030415030c02010605030d0f03060b03131b 80
    0x900c0248180c0c0e90b81e01d081c0c01141584000380c0682071003500105511f80b2070802c943c0c200c00c50310045a001c05c440094940c440c0c81030080c0c1d03100d10b030302d40c845025036196010203070b030498040d980c11030321610070a40c00a1960745005072040100302d990007455490070982825400e00000502c264003510300080004088a00ca844d51030461341c50b0008440070383c44a9820201411958000121203e010b601c00302d050300c000700703106002c0c900300e840300c1700c103121400117140e1034a03c0c2d102c00c1c8011890500040003c0c9000e0340226034005000c1c41691504945400042d0880c0c20981e00c038100031131180011700c041c8800b0030402c1d0240201c91408080413401642660300c00c1484040c0800d030010403e0380b60204621030600c1d1820303d5004040d039458907219444012220484030300c01c0c00090400300d01e802e03294010b02c1010b0659801601500c500b184480040d1600c40c0240004010166142e100190066003280a58050300b05400d0344080c5400301d042c0350070910f4005c03605900c3c0c0050f2040030450751100b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 314529739 1250 314528489 314528491
    0x2070b0411040603020f06070516030317010e010e04081b0a060c020f121b031903090606050f0d060506120604060c0e01020706170a02070f032304030b0109110702031615080c03 77
    0x4a03051f07591407804d8503201c0c5c140b91450382066a0801d011030040308040e00035000503505440c078070301c0c0d2a49031780c2e4201c102c034072103002c0c41596428040320002c1008100c00e0802081d91010103814021241c14002c101071900525000030b44a41e40e0701c0c001c1d10b180c80e078107200032042102400020007100300016441005482145124040c00d4a0f2102c0384800ca641481a43c10070100050b01c8458802c040710301501030301a00c8021500585040800308280c078180c0000424030308040c180c0340482e02c1543d12940109000303015664082e04000022060305c400b084101c1c0704034400c480210340c0344e1003071101600c42120110440c1c15500712800038008680e0008003603d01038144000500e65803917401c0810024410b00702d024004907502080c180500d078201d280351103c5130001501c003803a43d41801414110740100d000007031a01e03611070300400c101c2c0c0303e94000240032206440f03007610700f085c00c2d4002882c0034090803032400c240a00650803c0106010b100130745401915003000d08151070003026110040c0f00c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 314530989 1250 314529739 314529769
    0x3010c050c120313050304080607121a1003060f0b0c07060206060907080403090f03030203120a02090d0f020411070510050606181c080a050705070902120403110f0102070b041104060302 81
    0x103000f0001031400790500e44003908440c0c004c410f0743e503526140c00c851610380c4030032204400402e0181120090b405114480c1c000d403910348560300780307040600108020340c4c0030854030188100350302e901c0089445032100071000c00420180040b25514803409102d1800c2c84556031010301507401a504006403515810012030b840f0540740f030201060386e654641900e98401c1e0742c100001100d101500402010f070008020008200a465240315695580c202801a449285401070304138000e05808030011f4014849038002a100070300c00b080701084c0b50302c04e00d92500310401c103492690003100c07654800043d0744541d5400c08001e840300c500e441c030071000b002c840c02c00d5060428011801403605407803002c0d002d0814004294000c40481d51140d660300300070090703008400196014003070030744005451000341c8210b8800c18202e65949038199030300e0b1400c1da08500c00152034206400b859100030040c01080c8000c00d002403248170b02400e94180790504401121800043c50300440ca824030502c050390b55615051113083c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 314532239 1250 314530989 314531023
    0x90212010b0d0204030614011409190c02030702040e0c101b0f110d06051501020f28140304030c05120a060e1e030c010c0f082a130503010c050c 63
    0x20b8480840d0900074415580068421454041340355003410401e8400c5049480d60b800f0030307034540e0003c410801082030950311814640c1e29011594080361054001190f800f0045c0143da0804001c0c0d00071a00f900c00c81c81074a000707600a000b0b04509440c0280e042e100f140d0b03032071600d41c040d00c03814480000850503c2002505141c0b0345404481080441208100b00c000b0241403845014034030300c2d00d03101400c0103072200c8203030303100b803140a0815510000e500c00b0401c5449004040b00102004824410303040340c0d00d01100c20045604040110f46549039000440800c90020340d5100d2641c107060b1000d0042e80c110303030b2240041c005203002ea0080000c11390350700c83d00610001841c4084240b124a08503d403520004910301d20360711010b03c03010200141400340502c0c0020302070000c0510080ba0300a40c0c960fa51004103100701d0104810009103c5031304080d01c0c449982c010003c0729030048030000e400503c401e0b00840c0c1503041c2407003242420301450b10681d41a041c01428942d05040541e110400b01082a13480 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 314533489 1250 314532239 314532247
    0x6120c0603050a0920030d050f040909020d0c150807050c1c031e0614010c021503100f0e070e01083711030a06050d170a031b020c040501090212010b 65
    0x415101d034042c4e102c0702e82c0100882e90000100d40c0042c19420038164151080c0104005100d800b4008c004403071101014008040c0b4160410002c0001400d103036005981060200d0070500004140d0b0381c0080280c0b8406a00050800000c44003c1c00e003d00101038608100e400d00c80c1e8807116000003400195240440036545060015140c00c800506030720b260704842d005444031030250b52200c0d03405603040e283d406000001003108040151410b103102c81000f50019038610000c8070502e80340d0059504224075001a144a40d07540b440902c03092020781004900c0990b0405020981e41c1001d90140c40c90028208511a031409503920401c0000444802001110030b050f800450300c68881030003150f101481f01001420310036039402c007440d04100d54070161503142070004a440d1038803c0d0b260710165400040f540c0416501101e40b0842d4005c40303081c07414107881d0344104e54100f40c41561110707411013980c020f2a2000040f01004203aa0041e480307034154170b1041000f1303842840300600031410760b00b000d44000e0782c0e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 314534739 1250 314533489 314533501
    0x40e071e050a11030414150304021c11090f06120718021309060303020a0c090b060405060d02090901170106090e0d030b03070b13090b030c03100e1609020d06120c060305 74
    0xe040d2214203403d445010000c1c0c04204164101d642481e61102920050095640d51082411600c810f036000f0b0350002c48011f4a00c590100040307025006446000240c2451080c940031840320581600c103da100095401040528106122045c0e04060004001c01d401071600c0c01644007449490b480410243e00022501c08800c050f000c610300402c40ba6600b045440d41da41802502c511000701c0403100c480f0714170400034101c0740c5409030300e121030030060209242c146840b00b00203080c0d00503810a103505070203101045003031361140070190082a02d84000c0950f6481c00c46071070f00310751440e00a03200c0207103401654905150700098642030410a801d00089001480c000a864000075a102440090f07000811684c5042d03015554411142d00200c2031090403660000c00d9111084203102641541c002a00003c03059040c2e00300b500680385071401e131180c403050000c40b100103a180d80c001c10f19843d00000c00302000406440342c2d000401e8a0340e0b032010007032550744d618281000b8601c20801016116804517039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 314535989 1250 314534739 314534747
    0xc020d0e040b18041104110a12050a180606030308070906090e060a0e100305010f05070507150605180f0604140106030e030f04061d09010f031b050312040e071e050a 72
    0x40d403c10201100201e0304d41490602d04860001c03503028041c07401c0285100310891f00340c0a40d40009100d0300d42650b00101e050b1028000d10b0700030000a12962114681418903d50301c0003541868060000440e1203030440c100580826000b90405040000c0c03202d04001c00c42e030000c001c6069800d02c171031565a0303848540c00a02c580c0c8d6140c10101111b044e0703505114140d010003010400b140e00c03481c000d00c5922640e102c0d00040743c1c0211000d4010490800c842d41c0042c05200222141510101e000a500c0e40c031800030a00c00e804d041003c0c91804015801d004400e22003400c1d559024008841c180708038030301d50301e024102450600c5002c003895124400c0c81c0307070100c0c28010756892000b000443d6440c1c0e0755079500280b4000d503031406000c804030361148444041c03c4c161303010350613190000011403401385183c1e580c04c10320050b90803002c40a2002c1d040410660307000e03c030145c10007406981160319541000c45480c0ca8581c05000c42040c000742013100649405900d225a64108807401d2207134441c000c0d80700a503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 314537239 1250 314535989 314536009
    0x6090402090306180709110901120e0102030a0603030908010516050304050307240c02120f0a030615080f0a0506030c0108040201020a02210f010905071502100911040c020d0e040b 78
    0x1d540b50044208102802d00000b800b40d0407440b420741180d0301107944a1003e030840d202d4007041021000c00304451003095000340c403001c2c10208910750000f43c1014121031542280c00517038510640584604003001403562080e13410001d0b01e4500000c0000342481c40c0c41c20003251710a2200c905009003c0009002d03c41d041c400c1d9500b00350054288641030702e012523103000b600e402d00700c00c994480c80c240d007406ca01d81c40096402150300141d003245181012084681e06543c110308071038400c05840f01400300745428406030303c00e09000c16454a000600342401e0207210458010031a050032407034402080f900d90b900144200100c542070800050315100c1e400100d0524441000281d0401920307102140080e9002a8000c4108000c2041c0d036810300c0b1032000075082e201e03142c074044c0003a403240d00f040c02181e18070038100219000a00480c0d1502460b02c1c031030002d03140c1d50b580c00e484240c00e00c400441e241c00d26001d03156541c41141b0103040750002e12034001d0605041321404134042c56a444c95006141c03502c81d051 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 314538489 1250 314537239 314537257
    0x7030804030c0b0a27050c06090a080f010e1c080112024006030f080f0c0a0807021c03050d2f03041e03140a0504050409051606050c070506090402 64
    0x30f0907141c802c402001414084103040301c1004106000070300188540c191100855009002d804400c080d40104041c1d038006507925544508c8212000071400f804000c50641c00c3c69017000860404141080c42e82889142d040d0400e140e0800341100040075844003c040c1902d0804e1941180c0c0d0200d400070541c85000c22000d0901800014441d04418482c2449200130000b02c12401d501183d5101982d815a040341c8402044005907032107a80024a410f00a808503014040e03007030741040c11090899281000202c0d064624560000b040b10660401450100707107040c90030a080c84d40320780ca03900280309101c0c00b901071500d03036590080201400e00d2116480007880034803030600100a41c0810641903588159001c40720016526095200b0004030301400f40c4064140c0c50f2401d80c40c5200c014452543e00036180041040810000800c09a40f14414200b2150055008084240031001c1e15405445503070007110511005100000042c840000c44c6800d40b107040ea0b030680c440c1140340114019001e02031103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 314539739 1250 314538489 314538503
    0x302010b0406090f0e0c0120030c0604080406021005060904021c05030f0d1d0a021009080d09030618021e0a03060e01050601081e010608130606031202071a07030804030c 74
    0x940d003e120f4002250325010448104440f0524460036907856140640150108000d8804520204070f042e40c0801402580401d891034041403000507410a50221002c5480c40ae011609020265040112145249803d54100080c4c103107038000441300100180001c1c841d9501d40a8804c0c915898403401e45625801400c481e01c8e0070340c4207940c91054100ca00702400350761402c5040803500b10001c120755030300300721940603011560483e002d20440051120914040c0154200c0008643da01080300181340c094544c1c5a944041c00d51403c90196000c00a10304503100001000704096584c03000100255800c065a10344100c4404010681c0b2800a0340301601039464580300741c03118501900300c54410003090307071805000c3d61691024a032684294601200c5040c192006010480c0142070140c1c0121251034441520a0b0a0755000c090324402d0f00111030050000f40022040da80401043c000b030602d020107081d480680d140c2c18007031405000c00103010403014501040a25000c2d2500031803403a00120 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 314540989 1250 314539739 314539751
    0x20f030a0c15030f0212060d0c0b040909030e0102010902090115090515072d020d0201050702040c0f020c0a0b12060103020702030d08100b0f1819031110020303010b0d05040302010b04 80
    0xa0014000c0600c0b03002d64020078109134001a14145510855034130882c00452028540c8401050140320400d01c80304840021008002107032940760003001d003009062441020500c8151403500400284040c040c0a06580c1001c124100590b141c0418506442699009d101144070050003241e803205242e00568101040400d0003000c07240100044c011075010742d0116802c09206009446288054007080e51460307800d404850051429003800c220090051410030f0900d01150001021114200941c001198400020000c111380621403042178440480d40781840c0c03882e14001d080a0b22858841485000d0440005030140c1e000b581650007180d00036044413443d03001d40b14050011101035540700d0a2010351040081c0c0d41102000300c4a450600011090a10b009a15180e08800192440703035800f1580100300001d022001c200100194080d50903d0102ca00e404240110302c86011000e5046410810050008034800e10454403000a130210000d51a90f0360701703040f030052030b0750300c40541e2280c1002c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 314542239 1250 314540989 314540999
    0x504150c0503160201061a03042d0816060204090506090a06050f0405041b030c06080c0a050a0f09350d090e07170103061e0b01082e03031707020c0d020f030a0c 70
    0x185100e94411000880424030420406420001442440740cac0c0078005840c000004080c0e402400041c5900c406060442c0740555941090380c01c036412807800389175103000300320081c0f901c2c828080d085020010208040b90816022602144100350b81300e004030b890388089070401141310140e007661402d107004011842d40741d2a0a94000c1c2c960b1181d1800140b000010481d415100030486410423184c0d1a03180c070340311034101e040e96a070340c01c000b0380300c01c0c0180c4200c0000d80040a007140701c7c4040b5072144c414000740b21100041c0c009a0000760800055100c24041c0b000c1c55000100f48003a11506803400141d1750b224213048900c2450701c0e005440c0c10503490300000810846401503000190b840c18200f01401017110080c04541c2d590440c00d002860351404200d18200340c0381400f000e010000208042c200c01d50090850041030f941c400c0b4005218140c41880c41e04460944030341060107440500f007a20b891200045070f60168000c0640704850780a0604415602040b142e042160f21001d85c1030107551758 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 314543489 1250 314542239 314542289
    0xb0f090a090506030d02010c020d030e150a0605150304260f21010b160b0c040f08030309010501120c090c0e0405070e12030c100203060d14010504150c050316020106 72
    0x9a0b03146000748956018401720320f0040c062846071040950003000003c0000b2011800780c1070703241e14100740b130140c00300102001801004084c0b040250240110f030306440c100a10110801a00e50111120740a201340400150529150301803c2d1048104c01c80301ca100580f0240503205020f203008150314009404c17031a01002e2001138a1183c04160400503680c1c1c1c0e22107400362803184611252500448900b600c0c0000d0480e0135040c1c0005400490f0b604068a42000d045151010f800c20145544084100641483c09015003400b602281c80b00c540c08a6041c0d50381d400c201c225014000041d510343c1d2070218510320481601c1c20b0480e00404c240551304021401403c02c5001a2256002d80c64000490108800000458101500704801410204801c80300071000b5000908003aa010b00003400e40743c0400c9807420364507050098400002030741d0815140418030301030b00140b0040380c4c609101000c2d1346207402900352503020100e10311950b4001c000d034804034010305494110042c120b4640c05880c4c005545 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 314544739 1250 314543489 314543491
    0x141b1014031f05092e05061c1503050a110102150c120106141219020c030409060f0b09130902130902030c060c120a050f3f010b0f090a0905 61
    0x1c2602c020040549481c2401400e00003100e9000302807010f481d55290940304444c40d204164417071000580c015071100d0000d40c203907001e81c400c1d90b8101e00c503840004003400c091003000100d00362400c01c901480c4c41c595500d0344424401001500650300d03d42400307a640d000b800f0207040d01c2503600385042c00f817a0400e40b1342466000700002203a00d900503c0049902c80c06100800c1000301030180881c1410030200394036020f40001007980852820060701070581d20300c071740050902d40000001964075541401d00300b004a6900d5440050003218804080003521910003c6804459003651140c48240b0328480003400307807421650003508603802c03030000071002c13825900507882c0ba1b10880545908140d8001040031501840e0b11100307080d004000c0391110402a00001d28005000342402810040c81220595840d000b0031061420710314007515881e01c4425603c0c00540c681e10700402007030000c12400300c1400f12141409240a0200c001a240002c09585001d0b41e100e888020007101c0c809407101c1d401805000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 314545989 1250 314544739 314544781
    0xa0c0206131104020c0709020f030412090b1c0902181b071a060102190b01060f05030702071403010608030403060b04111c2a0903141b101403 62
    0x90348085a00301c0c0000c1024140c550300030000509100c4400c080100075801510010114864490000740c4010b041c005030010610446045841f171030903003000001205070b82c00100800c00c0d10380c410301c01c1142507410b460f86500c2100803801c0380c2c04445100f81c0100700b0380c9030107517104a0740410049050f024988061207070310340a5101c00e01590080b00c400140c0118040103000c540d45441000d01c4500c42040c1c298068814070444456954800e10810a211400c001303481c604141001800110780003803035001404407603e0081e141d071400001c020b4550300355020316402e855420b0600200c2e56400d400003c0601080004d580d5180d03075a207040b000030020055901d0050b4203003801c0008454888081e02c0042441c400d698150790210364000004103603e0040c1c1c600d034994011180f5220341c41e503003020b50107081d648840e0f40090031410181651078241034031120591014000c40301d40075800c0d025901354101a01c43c0c011070f104c20841550031807088034500d00da0034004010441c10191481003c12008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 314547239 1250 314545989 314545993
    0x3030c0a06291219080301060801050105070213050408040510110f0d0c24180303050906010f06050c0703051213050d080412020a081c03051f1a040506030a0c02 70
    0x1401410109155899801d11600030780b1004030030114109080c80407018554a015100c0d440104240c850140740510300980d480382010006018040d000b401c140c0c0900000d0a000e030900d2910350000303000c0307004d0034001c151003901c0d040403801b01b00c8480c043d680540b4000701619061600c02800600301060303540000355510604041004000004c540035080f00d445994a808400140d198103c40d014481d042c2d030212000000410030f401c00c03d105462100140c445054001101804d0041c19254050042c810ba0b4010400402c0402e04449421040742c190341419a01c81d40d000600c40e00303241207548064114007403040d0740d080b12041c41c4000c0c0802080200e280d0803494960381408400504418010301880041005200c1d0018400f0342c08090340c4010400c0600640740c0303240c141030840c4103000101c60a007040c030112000b0b4150096a81c848010100004000b00e0680f0400c80c1ca8014403500746900080750b0744c042228100303022540600005004c80d660303400d222541c40014030805a60074018 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 314548489 1250 314547239 314547251
    0x306030204020313020406050d0305220306020f040806100e06150c010f150e091f09151e14010614040e070906032702010f0306030f06020702030c03070608130c0503030c0a06 76
    0x9e2410306909100701d500741d60f81074200111b0700412000140c02c2d60380d02c0803864030503c000000808500081c13089000c03224515448034031780200c01d0319004015082e292580c02c40d940c2440518891101154000360491700a2106185110006c640340300d189441012035003001e608002c4c4881d9508280c45926204200e050041c1d91411b044940c6034054032041555042802e0078460446003040750039045040100014141c001d5a65410300c8030f4290b01e015152030303191540b00160640d0700c40b034100c010300e03030200500810100d6201c03104400c0050042100303100317001c0d200f0400741948805540252032041848020390919100141100341c841c46a1000030b410113000d0007030500c64560518640c81c880b030840803008441d500541c0d042408a5580301010394400c0004049032410291a0f07003c0c0c01001e005a8410305030040c18180380203110f80c14080e0340064010000d65501c00e060591104854200b5002c020581c5030003200070255600084d418400071500e881280008124008085d12541c0c0422070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 314549739 1250 314548489 314548499
    0x304170f0a082b0b0f0d05030d1a120c0906040603020919140a05090d0e0f0d14160305070b030f04030809010f0f241a21041a0f0c0d0207030306030204020313020406 72
    0x2940c03900c2d0001001034002780701e41c40b0100c070540c001d80100d000c11503241041014001c0401c4460340c030300080303440a500000d64100341d810084d81003034209400362014070410b4250f401080402c0c1c009080400c20b46222000c100040103182d01020364000141130f00a560705084110034040c20050341e1030141e0f40100c4800588050203215442c1014802900c0c0c8080da64050040041c0410703089003e4030034085464502030b41d03890511401e00904407000859445908605100e807030900207030804005400100117010b022000008466030103549440e20041c039035240d0405078050300205691002650512a4100c1500c00c035030400c220804e16560f0102200045010401d101c002130b202d54202544c010b40e042c0d400c1400e07036000b0701c0c00c400155200d018000f03032040103100d15030b0202c03401e641d0000891200303101381c80c600c503110b0303013062880c42024024103040452590512030002e00e826480c1c0e001510104140c020b81000b0021600140115240d00d0301c2d00c0c041d80e981d108140100e00c070b20300d0210003085e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 314550989 1250 314549739 314549749
    0x10609150806011d0c0703140d1505120c09040507030507090605040b04090c15050912030405030f0705090720010606050d0b0405040b060103091b0303020304170f0a082b0b0f 76
    0x507600c9a0144c0a58081d224080c641e200d40c0d11040e81541009060b03d5103540f40d1321801c0082141701d181c045c00280305030703920b50074824080e05500114400d09110b180c505441c1d00024281007802000c40e05088503031a10315100c0d103000040d0307100038414045c80750001403840c0c0d04e605c143d044076020355050028401d01c400b0841201d20504004003152607180b4240b02071f04078a002c00ba518102d40c288980390801c6640041c1225000848004059000140c10f00c110b04042c407170b01c3c08200700e00d03000702161410f040000e69604402040d41080209800b00e00910307005519484911087c030344001c101e00ca4407140c0080541e0300c072040041c1c1546c10840c94040600b000e00c2080d1140317401c0300140045031140001103000c0d10740300d0b800343d600b420040c6450b0798240c2d50751200c0c0700840c0300e40c00850781c035841c03c03161040301c0035140320032401d54100c524508010fa001090207542c1543c01018265100020380805141c60901d02000150905074821112628070b260b220381403100c001c9401c1064000c403036081003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 314552239 1250 314550989 314551019
    0xb060f0102100c120b0319080d0b040501140319050c0112020f032401021b0f0a030b0123090105130c051308010e120301060c11010212070f021e1e0301060915080601 72
    0x50342487c958200c03001040381800600058248c0305400710740c13420b00c0d00000e01521400c2c0c010190b80b1005209000d0390b403904010700b010708090820300040b4500355880d8652181003445225040c4080d550700c070315051056504451201d2030501c01c49449042c140c412031030001c48804401800e10ba07240c10741442d90700000c0c100044041203103644030400d803070400748084140550182908201b0441020000584407469280a082004103000c00518468000780d8a4108004501c1c000c4002d5001888540c980354125100d84104210218590b2038000e4121014800c0102100300c0b070150000c08540288103400201654806008441c1c2c00c0500001e86512440f080c4510004140412900000181c1ea003003601610803050050f07640c0d9480f050603e06540d44048001c84100c4440000c181c00c52501d50240c03425902d080081c0a103484100c00811001024801c01100e85406581850b00d90f81c1c09410040151590490070f208040d0000009038018402c1c0c018000036008000000c0303540b1005007500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 314553489 1250 314552239 314552263
    0x302011407032906160b0f0c03040c03020118050a0b2d040501120908030a140a05190e010e070902030f071803060b060d06300b060f0102100c120b03 65
    0xb0503c105000c5010200c18101d10300541d4100d00c0a1120503c00001a6a0111003a0041a40e0841c9180c11204a1000c40c4000e181840b01c900500501c804210b13840c00340c2e0705503942802c040422010400c04a02d94824a500c1543e10078a008000b0420140040240610245100c451844c130101c0103144080182410a035503d0910144402c02656118291486000c94a000001001d00345510360034115402190030b5000d50380c4170f800d600c060542100c03850b544808601c4040016080c03c814100b50440d0364440044005c0d100c51204400e100c00b0751240681c5032611088401c0c2580c0c030130519000e508100d0b05040684440c81c00240381c0b6001c0c2061443c0f55042e040000c8100e402c0d035035114000d1540520f4030760403032020f0003a014144024400e17030014214096504401104c0c50807144c82001803e9860318a4014080001001a000324299a0400d00443e4952119080a00101e00d400ea00403050b08115082c28440c1d41001e8002600000b2003085100074021800d02d039007895075034a403007844 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 314554739 1250 314553489 314553521
    0x2150103020d020609130f0209100e03070603020c030f04030605040311120f07030509031608010c031503080d1404080904110a021506030c03030408010b130b06040b030403030f09030201140703 84
    0x2d202c0040c90600004c0000d560010009040041013032021000c03a410702c074181410f2a40041d03140000d180c407246d640104540c510f4007003440107034031000c05d03210001ca105103c02d26070041401181c182c0300780180c0b00d0710580038441076222640c9081070809404140c2d0180c3c0400c0da9a42840e8424801248500300c0d0000e100d012807511007449805c41a65200344010b034200082400554100d681c240161444601159242d0114034207011803d402c5078910309920b824580341801020101701c0c1c07042c034801125001543c1c152103400d1191a0780150003000d00ca00c0c44588048100300421071510060400b0210079101042880c8800265001503c02c0c0301b4001c015920040060103a545540d4600307a101034054241c035034800c0d20f10b0110307113160000c0c0c0041240b0303510342c084440181000b0104880d803114194082c00880d0b6040f01045d940c0c07241c2e000f22401d003500040020241402a084030442c2e01c2d103201c0401c03034089030b424020f00a0001207000c05468400c8004101d140d07210b4014540c480440d214 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 314555989 1250 314554739 314554759
    0xe010203070906180509090a0201021002090d0f11090c03090c0607030806040203093c0105010b1b0a02060706060603050601030902010f0e010210150f09021201050d03050c1209010215010302 83
    0x1c042d10208219028507030102c81d2000081781a41301c5020840c050307101c8400408801034244006410003125040d80b9130800d02c184480a240c0d941c171000003c02d590480300200040d0700a0400c84450504610340361741041f4400d061109050f24400110b10940150041c0c650400111007004414031591201a0000e40f050000c241b00b8541a07005580100e15401107800e0703000c0400c4803108814070b8006e05103031004000c2041d0950a00d8103815490410844002c1140d0740c14030322082c0d0a8051100501e142074406410f4503c2600300308450450141c008024903250803031446d180018144500481300001c0c1010085040c6500038082c104907da1705840b074449a03160030008483c2003c00d4200d444c114419082907545501e02440b900342e0914520600c4401d003070070841d44500d03461b200c2e07210b02400e1b88100040350500b0b214004090540340d0481b103c01c0c001031103041c00c8615024000e05007100c0d003e4080701090042c401d0000740108142a000e4900341c03003030700c82015000342d003d100294026040c44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 314557239 1250 314555989 314555999
    0x6090e100e2205010e010b01090f060c050f1006061704020f040e01020405150d0606051303080f210108160b090907050f0c01090b0f0c190909110d0e0102030709 70
    0x9207203540c44902100ca040782e000400d5a00d40ca0a101c101007039650365514084010100341c203015207041c1410a0038451901482c003000e80d175412005105540030040700d14084400c22206016580c504901c12080300c2c41e00030250029001003c00f840b51802041e521030f411003000a030f450038284916001000a580d0705030038405c1c44041c00980098114a5508100c0030516950340644c0740c403002030549201d0384070003039000d001045032010340041003030010070f0204c003070103100708409101035a0340540a039841e00c500440f411428001d6004d0f8207803145080904101e00840c0056450403940003504450341c401008200c54010640c2d0b01410100c1801001151818200068416000481403030207629100d11a1004040c58125212005559450315002418440801c5026401115185045106080a01d101c0099124404034070307100c01d01c0520b901402e0f900804120005000e038200c00d03c045121180c503102c60354403903002e91000914207504800035850503c00c2e2481404561540c1210a081c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 314558489 1250 314557239 314557259
    0x3100f0b03070c03210501090e0102030c0712090b0a020a05100b06160206040b0304050f0f010203130210020a290a110405010c060f180218100b1b010c080106090e10 72
    0x1c2c10503028402c200c5d4030500b04031482c000c141aa540d04950004140d4181090101a9000440c020005a00500506c40030414a0b07080b51802c3d80e1020be082c49134030050b1420340d61018141d112001448002c01c0e010503654010590040a920603010781e495200380d6501c076000c8a085012107a00502e00384034003a440301001e200320240c0e9000809030b5082c01c0c2d5030503030318500e0f9100315401c88968001d16841c90002c0001c100c40d02c64001c3d01c0e8001c0d401c40c0762002c001e03c840c60001d000a80700b14000703519001454000c3c003104131030030b400100b0a00c810121140c40030b0403000d1203101c204000c01d00380c00500d20001c00c3c402c03940203452100c9200e1420340f40ca00110f032400850702c02510800d0b65240d401070710862920806002c40f00381042c844044903d401004080380b4401e0340180400030305010080701245000201090350603503584c040d11015410502c1c1c8005041203040c01c143d628000f20042c2e12600491260b04880844e035070280c05c45d840c2c9800e50300da4031041c6c80c0000140810178048c4002140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 314559739 1250 314558489 314558507
    0x3050a0c231803060a0606020d0905010e0906041b020607090605040509040605180f0105010501030f0b090711100626030703050f1c02070614010906030201080103060902011e0503100f0b0307 83
    0x400c22505810b040070b02c002410000c0640d001c4003015641c10701001900e806001ca941610118142040d0403813501c00040c0400130f40d0380415224220001c001441d607545e0340e008014810043c1d2400555180c152030182d544e01d810381b69800491020500002c8261080081781c0564401a000f11825200c0c0d070f0b203608c040c24010b402000141510300d80c040c9420001c200035400030b41e00100110782c95242900240446100d2001060041c1c28845811070503104e98000581000440c901802001001c5040c5410108003007444080642010000074906034400209400c01c2141003280b1001d040d850381440d03a070f10030710744000d01091040c84154810194100501210402038090340707130300382405c00c5607001c0703031310100341101e5056584413000341c14400741c00c1d640d01414040004014090464001070301c1d9000500c402080c03503885107042801c59114020102c011188070000204ca1541a400944940c1003261004070301c1003440400506460780c4480b030000c0307440815002c2d14548030300c0300858070044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 314560989 1250 314559739 314559757
    0xe010b0d02130903110a080307080105040b060924041d062d0a1502060a0c02070503030904020304110603010308030a1b140c0109080a030e1e0309060c010f06030303050a0c23 76
    0xe800000030803402e01341b25903080607114064a668038540010040c296140c10f810450150f441e00d540700c0700308d880e81021501003800c100c0c0d180c0d9001100507038440c410848501441741c04100800d00241c0240308985412038040c81c1401425a41c1d03036070b018400594030010001282c41c0c0d2044070103504a24a01180da49010050041122262101118007000090011140c01640303d5006c000d41e481072881202291490f52001d440d1a0b0301d0000000c0d560300030380186078400d50b800004101000071034030300c8003034410340540025225a236030b00303111261360011941d03d05c001d41440540e6407000241d05000000c8011625411926407008040354020782040946011940d66080c0c840c1c04503842d403016003507070720507560041f62924411410b01e081220768034450403450b14a20f120350041c7c40c084107498104000b0740d286500d070b00900401a0140c0380e81512100e03c640303815004401d1581c99080507100d12080c03031050104000c021411608600d40c00c0e081545403907151082242c0145040007408088 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 314562239 1250 314560989 314560997
    0x706050a110906072a060305160f200a05070509180a06091109011401110102040b03010603150e0a050714090907030b040f14071403070207050607020604090f0e010b0d02130903 77
    0x740017011510b165143c0c1c10300ea1110360b10a02020402c2e40c0c0d040c02519801031170042c038003105c04940040030703149140d00e103180300500810950a2782c585003400c14031b042c000310b0030048414050441c00d10a413101c517903004035800340361544000380141c40407102445102607554020054640540c40c0d800081c184c03c3c00803501620074658000340ea5030b60103c11070103806004000300e07032105020005440c040b00400542e442d40d00600003000444c0b401c406236130448030941404515409102208115440150820079540d000641408102c0741158810362007000c0341d0300e0f500300074a80a04d41403110300980d803805920460304e0000035007040c800d4101200f08280035001207040d010385402e11041d1088074201220010aa03010480c0e5103074003c06000c04040c1c0d0403000c500e50704017810002d4443c1a14080e2500601c40010f81c00115207482044600030954400104803099001040401401205801c5134166007007049210f8180392100040200d1a802425000501d0703100d034400d006800244819000c0c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 314563489 1250 314562239 314562263
    0x7030c0602040e04050c0a090e0a1b0b070c0801060b0f030619090e03030406141b1c020d23070e1509031504050d090302060d0519020c030706050a11090607 68
    0x1c000c11070007050044e44035002814103201b1078002e10004c12059401820144d040c80c02c40c0c1203074500031410007940750301b054003000340603d803405201c00003003e60310140600000103004018403c1e0b400d50001940d4040000b032207000d80c1e40a02068901909201d0000c049040000c1425890000310461024400a02e950551a1b5890b071440c12a404000d80070000d810000410003007200600c52000d8003c0600e0880200f400e11048061305105a0540409414070004905c90100c01a01c4295622244600103554414464147c07802230300b440803000b4000c0d800301009212100391000a10b11900542c0d0307a04044001450401c0051100b030909081f082c4010410700d5820f46040c001914000c512021540d65404c05241942c58880c59007188070811025090174001a6500c0c0204c0d074085c07030041d10115540d15148400d980f040400c80d500d551035031001a0b0316803030b124044060314441340108410002c0d81ea4501441d82542d00e8003604c01e0803220104000c851524050f009000c510b4040d424a03506 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 314564739 1250 314563489 314563499
    0xf0a18061403100819061103090a020108040f210e09010e16030609110a0908010c0804020d020616030908010f051017030d0501091a0612061c1719110307030c060204 72
    0x130805880f003031243c00c0034000c03410303424041b131030254100301e491b60381103140b4514200c1106519500311642c004d0400c03407031070003107010310045645000c5460741080e001040500102d01100c8540e4201d44c0179004a61540c5040f40d0380d282070040c2604940d207903400250a551400c411220203a00e2002c1601407558544008c1103100280c030900302105d003a00104c41ea25611501e02406c9030001e03070706c90013040c0e04055040c10800d40c083d0a441d001a4107480a0984103407520002d4001d000c0d20104542c0d4046101841090640c031015030811201520300070000d03070001151503000c1d40e44c1240d02d02c1240780c070b00e10200710311504031101c007906000e04010f90b41410600b00c0100241c403c280d003c10090350f01c4100401d03510703d4124040010110444030946452005000c002002c40028107103841825044040741c0c61a160420300303104198403109075280c0c202c01617110030b07403604000304c00c000c00f41610101601282c003c3d04010741d02c0c10b400000310f09058040c0c0d0111024921100b08440c0c890b024480024 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 314565989 1250 314564739 314564743
    0xa02280b010b0a141303061a0301180b09010c090e04021f030b0a0b0712080c1608071406060112050c040e0403022b0509150702060f0a180614031008 65
    0x7002c0d2415030585640c45042000040080b5600c071030109100004100e2911842841c15550301102c0c0e0204011580154910002c080b041007212059055400c145403002c0e02501910032100c281d104d980400b401c1c1d100e8801c164201c0c0d8070254850b003c601c03550018000d1482096100b40d120740300400c880812500171609c20101c11840b040c10001c00d031204521070b06481c11390b807420302800b042d041180c14041507441e4030300624200da6908082c0401400441c2003d007200040301c004440c3c00461500c0304100c0d180000c01c0e54031460b0709580e002c00921980300c0c0035501007091800f07640c0507912810002406c403d180d00801c1e0207040b071200001b003004002000c40340c640440303110f5400380d000f500321001055403000244000e5a20400025903400b0210390080e00300081e540c560100f81c9401d070722078400c1502200c540c07040060195000c1004030310b100801d40442c3c020144042d041e910325140001e418001400801c4a01604020520030b288580b44595410301440c1d11415965070014000c1d6507641e980c2c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 314567239 1250 314565989 314565991
    0x222140a061b120801030510090b070c03020703060513020901050a0f0308030c07170901020607020c01140a1202041e0611100203061c2003030f1b240103030e0103020a02280b 76
    0xf03400700c3c0800c0c2c0100140324082c4051201080070300303c240b14a130510f03a00c03074402040c010804001c0c07200d0318501a050605c00c001200c081c6510517030406c50703428403042a403c03131403000b04120310961442d0300201c0ea50618075104400c5a04c20070382080c4645c21950b507008250001841b428090405000e42400708512581e5050085081e0202598030382e07441d00024100b16000f0030340001e56100724142d07082d42e40e0000d08045124940203a80e41c80c0d88006000311010152604401c2c0243e0010034007140300080c03901340c0310a030049148400d80096480100f5912080d5502038440039400010380d555003403017240c000319031000004221001d80c1d010340d41116003540900c001030b00c90050300355016458254042440e40d503444210020760501e5074104048200344034400300003d2100c4c40700103421100c4001c02c403e0a22b0400d400041d00c003200b249613a2000540c0901c0300760001403407221009075a502a01c22030310075401e40d50261442982c11a49001c0c2d081c41680e501c6a070b0f0b4145480071300402e88104a02e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 314568345 1106 314567239 314567273
    0x9090f1c02070905010905100509010807030f15090b060f0418080a020129010f0503041e030509040c09080d0807080403080a09060222140a061b 63
    0x302d0528240340d00402d15242014000310383d0304c1c40d40d081240b02d5000b1080c0f0040183e41d079030070821492002c1c45800c031150417000050000c22a003145180c84a40501d2000b4a440d10110894040b11583c4500f514441001e07400e000841c5051400610f0f90b100c222403c1c410240c642044400707c0042c00c43c000c2034000e0006091000074001c1d00084e8030400078080f03d800e0340c1454241c040c003d6408008036800a403001e0803031540a4090016a40a250401d01c0702d251240070309050f8007045000c403010740610405108020b4655a18040e1181c40001551911482031500b404603290907103600c00364003400340e00c400b0806541d41c0600004c0d4010341504d001e503c15111403942400800c4601e00c084c001074000030b40480d400307032482c1d100c00b0f883c2190384031842a41c1c0d0310408090380246041d040c1e54403a203850b07002c0001e1842400805010b92030707012090200306459645152441220700b00b = true := by decide +kernel

theorem cover : BRFrame.Cov 314388489 314568345 := by
  have h0 := BRFrame.cov_init 314388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 314388489 ≤ n) (h2 : n < 314568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
