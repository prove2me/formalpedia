-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2507
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:55:08.916195+00:00
-- url     : https://prove2.me/submissions/9921cd65-32f3-4049-9619-f1dfb3830450

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 450719424 ≤ n < 450899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 450720674 1250 450719424 450719443
    0xb2b0c021501050a0501050c24060120072c010603020901120209091803090d0803011505090303250813150c02030a0b070c1e0605060904080a08130b0414 67
    0x1841d0710000600c0280c5880c00c1050544074203083c043e940754890424a4607161100c60b80c500c103550701064003001a411f52603840c1c0510001e0301c135004190b209415507460300d480c0300500000365111440401c0341c5038001040415524003080c40098007114000304030a110b009810003070120b0340002e00d580a0307580c0162522150581c00c038045040440c3d04000912154024101072a2514141803281c6400020710480341c1401c0020482144490f151410314010f800034425002e400c1c411002d552000f0340503008881d40090001c01540c81c2451a80e82c109039095600500000300d00d05500480c0016880d1005000d140a513800c41501c891034044c4082d080d445922080f81017003480524500140c60000e14604000d61281c20810541e803002c00031982d602c244403002c7c001e001c1c400c20b1030405c0030410311803165141c000c1d10f040c061596002e0a0180c8080192001003803001d08001001c070b108d202d82c2615401000c248030030341c800280c0d0b4840c415182c600b40c1d810350b00c41410085c100c5c60704c407040141002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 450721924 1250 450720674 450720703
    0x140708070c0302070302010c0822060f1b0212030f040609051005040815040204110403060f0501080109021804030512040602120901060f0504150504050702161e0b2b0c02 74
    0x540301c036030354000751aa000c5100080c148030489619408000c042020784244038140c09010700344006121810300c02e01014801c00c0e0105810290480c07030180701c0c1d000c40c40c440311421030b01d8526941c50340c01d00001601f201c2074454980030501076646caa0001038020b100401041c0d803405011414482003003403501c0c0010183c800c2c080c00700000c000d1440701254242003078030303c400c07441031a0782d5a0003ca40548580317580203c0d00c1d20001004000c0221a038062445071298039001c0040d6070321002c0d11400c0741e041d007034041c2d4000401c01030781c00c1c3d1071401038801e44e0042c42403409a0070420304540808021206481c22610305401064055030303a0142c000869100940c00c0c001d101007480c00e82002c0d28920940034840c0038507114018044214851110355005000243c8200102c0c034200030025116515940d043e41e0035501e070b00380011203503102ca42248a19409601c4a01140d1030000000d407294420b141498050010f0740501505070044440320303180c00251040410070889a410003401e2003214802800b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 450723174 1250 450721924 450721937
    0x50325090e1e0a0504020f0a060302040e011e0e0a060e01060503090609120d0c05070807240504110d033e0f030d05040219121a06131d0114070807 64
    0x30340e05001c44800703e8014604280005560302c55001051b00c00c1402040590025000000000c1099041d8001c000311641e404c42c44420382d032a042c5270012100c01280724029981c01d54010b200c00c1d14054070706604586406400a60030355103503050710200a09070300c11030124001004100a8020510141e03611500b0300c0040c1030300403981d51100c0e846d802240111f05100da626881d45408a000c0c7d41240c02d032907044031710700e51600068604400e00b03000c4240200000784071100398410800542c01b6032030040da0322011031340700a54034405125803800701c04815002c201c82c2400c07104101e0303403200000c0800c0c0315410f440d11500c602411181084401c240c51010542c0c01408000b204032004010f842400004c0c8c0703004241512030b030000a105442c00340c110046d515441c01c0003d14110b52201c03144001d8499400304000c80c1d010300309883d000700704803441d640108024a2074443c2c25182e0303001c003210500f03a4804100078103c1c0d04101c0d08513200c1e403119503100001f43e0288404035801c04216584a245480c008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 450724424 1250 450723174 450723211
    0x20405100507020114031801111810081b07021f0e030a03080f040c1701290f3102030f1303020703060203070507080f122401050325090e 60
    0x5e092201e2404d51400a03000403010034481c0140e032403141480e4004200900c14040c1b0b5280d101400d0340001c201d00e41c000429032010b003590921200a000c5007415488500d01c540d1a246d9140c0500080402a51500400c01004005a49500c0c0c61884844807110140303c540410074090404900081d032240300340e00100e0b00780e000a5120415a034019a0800c1580c62510b5501e40706580908603004883d46000c00302c03090203040780540c0320104c800f0340365100c414400e02502402c40c0200381c0440720340e007085036104d000180f420903001e21003880d0b040103035040440062510f01084a40b0041c10190004e400005000d440110701101503001903110403a2503102c4502d0781c01942e10b90b154440100b103540c0120000d80041e0050064505068200802c150341d030602c0c0380004101c0d4001d1024840c1c0d1217400700450b0304050002d500018640c40c281c0384c200e000046c00019503580e0802064410040c1d2150000f1400c029440703802142c0210a1f140c5040140c20715101d0482458000c1c81c1c1001c1d0b07443c44060 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 450725674 1250 450724424 450724427
    0xa0e06060d020409080405040c020303090105010f230d020319050606040e0d0f110303100602160602071802040f140a0b070f0f0f1a01080106090603050304060e0a180204051005070201 80
    0x64095442d8101c400248018151030001c2d00e40c00b899010300d80c0146003a866110b02a00440150b100d220440000c004982c4c940e4400840027074076000342c103040398008001105a4000f03580c26030184400420920101d1000d900280c6040404c1d1001003891070003040781e0082000030040785030000000c076810301042e04031140d034580d580940780101c810401c000780310a41e0940212550000b103030b940c600343c03a41d900e00341265030b8004440b4860040140318812030100c01020390403081b01139550740c0d03018102c0c03070345442002d0b000589801380c040741841d82000001207038459444040010041117a50308620300341003040214a128643c4a64402c40040000c00700042541618000c950340c400c007511201621814090751440d00400028110840c04600741040e0101d80e60141c104c82c01e074002408507070384682d10030f4155a090b2000910941c01071006000d224010621050040c0014000c4511180e0f41d682038040703214003180400c1902d82c00217013807240d400c00e841c80d611460441e04010b440c180d42ca900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 450726924 1250 450725674 450725689
    0x2102150a1d07151b0c08060402091501020c090709080105010314010c0212030f190203090a060515011d0d020a030303050105010e09090d201b091312050717070b0a0e0606 74
    0x1040c10802c2c60130013040c40080c90004042c1041e0001c0b90711807056280c0480070350760442600d050303100d03103c9000066000724a1118054424006038040c10b40c050b5800244014014081e03c1001400f810510100d20054240b250500850217012501c1004000500f200e0842d00084482c0f001c6410441000d018075040f071080b0b1313422041920300a250307039982200e05004030a0454695940c2d90000007448080c040004907064000d01070403080040703440d051210141c5200d007034000e0307002c6100040700f010031386035810800e51503200213406114a203082d075000410030301054204402099a420041c0301c3c95a20844a180f0a04c0030307604109141800d0701f525613102d02808107101007080c110030280315000d40102c3e894003003100d042220114a031304400105818080100d140c0540c6628000500110000038107124494000c8082581400500c004039840e500c112029901034000540c5030300803960a0008144031070185800d0b47c2103040440d01d0400362601c41140c1c0d40542d21141c1030000d255207191 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 450728174 1250 450726924 450726959
    0x1e1303120209040c051306020c030a0305160b090307110303091e030a0c0f0e161707021c050901030b0a0506030705071a1303020d0201092102150a1d07 66
    0x40c14050802403199540c060b1103002c500702e42103420410300040668201015201c0c1e080114061198107440303c00483e41c81500c0b041c12130741540517060590210780107000801c42c0800c000154920382d4500d0300e0715a07080d00b060701c0c1e03c940c0340d00024400c424071090904100360454211f02452801e01c4000004c0c001600343c2058944240c4034404411441e0f41c2004010345c000d9000d102c80c01c82640d112096200040c0038468001c3c100c040100240c3c4801c014682002099120b807a8400c070503c11a02c8034003510741c001c1c141e5003544100540b0499024003540c2e403103186032030350342c82c9550743c807540380010291540d04070094092007502c03106105036614201500d50112151810503101c4816003401079540000e17a840d00040d81d03c080502c5240c030844492a40d081d4003d400b00c1d840c1c0500000100d080741c641d508054450400c0c09840d81403529444101d00b0101450300c101c62050b6445a684481000b0a40b25aa1000e68500c82c440318050040c200b083c0d503a01000180004a240c0f1049460103209803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 450729424 1250 450728174 450728177
    0x102060402040507020f0a060605100206040816020a0e0a050a0e1606030c0509120303010617100b09040902060a020705030d02010c09090506180a271505220b1e1303 72
    0x40000a120178802c105004540d10a1030486401c100f007070603c038000344a90302805000d4888400c180500314000540c1a028942c0071000f18540200015008410074008108a900c40b10000d00010400103003c8414001e9021000015842c1450040d4804548115540503040d40040c10030980241c503080c980740840b40103017004a8000c08214040300c6600c1a03180d2540c0c40b80300d01e070210745803c13000000345040e41d0075902c411404207410064a602d1100460704040c0480b00342c0d07824440424000054500044094004160b00485a0000346070760800e6040500607800140100007030316041100580d0f8040031f0000f048481601640100401e0150182c43c001a072254041450b5803911081c4181354902c0241d101c0840c00d052400c1c10191086200342c00c00c845481a0000c003c00c000540b40c101141e010ba440c4a2922070038945402800f0024000c880e080b003030241001d42c454116641c054000d1185403900114608903044141000c60710007401400c0425204100b980524030329011101ea815 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 450730674 1250 450729424 450729431
    0x3050910031104120506101a09010203070c0b030f0f07090302010c080d0204030804080d03060f0501120624080a0e06010b03041b150e010c020a120c1203170114010206040204 76
    0x1520041c1c0240120074440c0010900000e00041d83d440f0100c0c144840f10310a00c1aa500703911043c0111801c000d40707010340c88400701030903414408000c841c2e0003000c036540d040c01560708007003d588a10382145056404040808000800c00031b241c049c900300203900015442c0782500900307003000d00802203283da00000341804400c0e00c01400380300c0280c0c141d60f003280305501c042d0b42d01c40d140c0c680101681c006111740203091254000030403407903001c0d02a2078152809901100b031241e07e03103001110280d00034251108810341c3c030715000c984c0e4207c50490401070903840001007903a0b1212200282410310060414400301e1805031441e00c00c10020546078116003800e1aa50303225183d5051000000500844000b02c130140034000054030a01140c0000076004540c40c2d50700c1115062006503644001600000c2d8060080441400b10760400c071041da8130b0901442c80c541042ea1102801c0001040c41181035000c51081c071349002000301a120503501401d8aa10301c02c80843c0d000300081e568020150000b07206948 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 450731924 1250 450730674 450730699
    0x806041505060d020f161403041520160501092709141504140303101502030c070e060901050d030e0d020d020d0c061202250203150f160c030509 63
    0xa064050340e2850255803a280d94070344007881b010480643c010300403a040c0380d4809002c07844400c040b05940031a02e450381a88981c2410b1802114000d07155041886d81c491440400004440c0800020b094051003c49401019040a001400e800f50507030200b005800c8d1012480c4020103400740340c00d00101011000304d4558a24a481440003001d900700100c10700c520141c2c1150104845115070050b805032070205803075001000706076100d00c01150b010940401d015801c0040241c481803007500c07821544140c900307000d40404d1290410816500446072400c5100512003e40f0b444c0c04241c6c01400b0841320803500301e1050b6070140c0240c48401c440c0380316140300010b60055445840d4550f6403142e0040540c410340c100b13840d284400400c28010540007504001c5a02c02c4807003144211000f050318580c0b000c0164484c0c518480040310083c3c6c0c12605401040b50088194808410050150304d00c0d003984180f074640511804131002460914000308443c92012801098228003203032403140d01510090540305 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 450733174 1250 450731924 450731947
    0x1a0616080403170915070f0f030e0301061d0601180902181003020a02010c09050319060207230c01031505040f0e0d05072a230d060b01080604150506 65
    0x1469101809aa00c0800e0640c60803500f40f0080c45408800c03202c5100b5844a000f0b155001c4c024030074002c110b00c10841d2468082201c02400105803442880c0c0b01c03040c0340800707002c00c0c2518000d40c4002a8806800201c0803500c00900301245e1103002032038038040750411403020b500740380524070444110070340c00610700303800c9000f12120800384100507107a4003100f4000c85000700254046408000103520303219a54031901e1140b0030043c1118001001429590707100320400c1403141d8251130842e0071303503800c01c07030072000440301c8015641c00ca903468048043d58004442260400c660300c1a1281017518120351450b070000101d030240141c50056a00041c00c00c68150154002e00b1020355100051061021000ca0281d000340284009071062020881200c190400c0300d00003203045081240c1d00324003560610070801446c404040f42f00940608800400480001c10080f0300041010348803251641d844000950304001c0d00c2c0e810801c180d50812200200b104155034401c03ca001c0c00e071040710001400341160 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 450734424 1250 450733174 450733177
    0x902041a180c0d060f2c0c0c010f0c02010606020706020d021b0f130605040b0607020303030406020c19030f0305090f0601031412040b0c070e2e0803031008011a061608 73
    0x208035143c04001890f01c070554000d02c030385188194007411002c07051280d9002000c02c1c2d01060113402030340b084001c2d201c0300c0000e0b20a41007110442120340d40c0340402050100b00e4001d1031484560b0703800004146080802c000d041507080e070040341c259401305003403010b000c6d80020b14418010420141c51080300548000030f08001c40d1003001603100d00340c0c10340060740001c0c179404101280d008031410000050300c1000c0c00022b000c0c000010b54075400c188001000300b041c68004021502d825802e03200740d414040401d004a0920300720540005905030103004680390144101078002500800034000c0340c5110004607642c810500009040903d822581034100138104031504400301c0300c61095403215164907540d601d54216010305811445070040000d01d4901c0c008185005000c0f59030507146541c044050900070583c48160220400010540055224000e002031401100c040321042249880c08891358292214080310843d1402100081c1181d5961744007203907000b26490b0103421481c003039801c201465 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 450735674 1250 450734424 450734437
    0x3090201051c270503030402090a0902090f01030506070e0d030c0831050d031209110612040204050109050114130b030708030705070806040f0b060a080f010902041a180c 74
    0x20780b4103032011100001e94220040c40007a0103900c20300e80000662901e02021140e0014045400c02c00105025082c10071407298082d044650110303010009901140b5981c030112420ba00c40015603005104004c800c0c062180c120f55a80380401e1801056000509440350040e0b008081c8130401c02108200074100090300c2c1c100740b082e281803400314103031a0000c11040540c4c003000c81c031000b040d801240510303040b04816000782e007640e0342d100341c0310303180c2c07150401480482c006503030003400b2035000d1900345d940c20010300e801ca10100321038044d403c0c10304c140b0052300c006800200300d05013406c0040c024000080650348040c001104d0b007c0b0000b00c480040f2000707200b10191503405005d1540c0210744290004010105c4520500445030055525a4080c2c0c8a04080d03500800342503004422502088a01550b50780000c1c00414230010319584040b40d07450444031080d481c3c2181d444020030019841c041c850751004a01d40c140f028000c82c2e1583c002402c4400c032003d5003000d81145000704020041000c20745d140c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 450736924 1250 450735674 450735697
    0x3151801060c170a0e1c0b0403050a080a110d0f09140703120203040b0405040c020c090f0907080303040b0a0903020f0a0b01030b150a03170909151f020d0309020105 72
    0x82a50716000001d280c020201d07410b031400701080d4000c201c001d000e00101e031001c103065602c2103482000310082000010007008005010009141071202049121050a028a200f601c403603940c1c40211001a01000c0024182c0d080302c0c2c07034081c41403040743c447c5085860b218001c01c0002000001629494010912808040c0034101c1da613800d021a03020010307002d400d40340140030401201d09201d10403a40c03442640190011484148800c00440c14150852045604c0702e005540075550343c82c011681145088583c42c5100c03810700140180f500782400b1040c081c2c4441c90203580356140640303d2007924103010301800c180c1c540d00c004110916100780704984c24904100c3c1a1094004181010715943c4070a000030349481c41c150000c64104c0c4013602e10110302c1c8a01408030f0000342d15603110044540b01c5405003016514040103851000c5e80d0300d0303040900c0b40130001c0060a6650440d000e105403c102c080640e40c101a15818100b03110f034001138001160b035030b249008500c2d030945100488903806000e601e20b4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 450738174 1250 450736924 450736969
    0x171b040c120f05040201173c070f0e10020c12120301060e01020601050108150909010b060a05040801050a200c0321070f05030126160e09210315 63
    0x4050015000540100e001f640d540030400008050100a1101500d04100e040103d50703000d06140459400c0b2410320707130341820108042c0c040c0c0d491460248000c940c2c04000440c0904d0818216070452005209a4002da90903140c0420002c0e01a40d28201c819403144154176840180310b820b90104622001822486100c0b5100d5039500806819209181c40450160050a00210b255446002424030078407400403100003400000c8144410018041e098000954903110580403546480c4001c02c400c244650322281e807030745004482421240041d24100c4010b007045c00b54084000205220991494070a924684e10310494034244c0c918482c60103c2241c2025031140a4601c0c1502d1251b1791084103591502d07841600e0306542252188400d00074940c00c561442520006220460b1541020300004400c680807070341c030501481c01000403136100b03560443c596410401c01050501607000c80d40c0c0c441a812401c807641041d116002d01004003111b00034031000395414407956401d55242c2840c60b0814090 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 450739424 1250 450738174 450738191
    0x4060615020a0303051e040f0f02030717101a1003021c0b040507030501030302032a03030c0c07140d0b13061b141809060102101401171b040c12 63
    0x80e407902c00103081500405d141800041c04401041c809a61a052400d600040c40c0d6842d500d03181d0140c941401038821a01e850b044500507101040401c4c050046108540000d00303403004400d00c1d0410741420b00d20b01508240003015200d0980c4984656a01d08031800030014071246401c500030b0160101c8901c0c62101d810a000d109410b41e80701580014050300c0034005503981190070f42c281c5000f80300040069104010710303900307004442d0440c003d4903c0d84c07030032003110308101000610b190400d031000004c44500040701c14260904020250040c485c0303080b4403500c10320002c0000d00171006e95034003030400c031065030028203500000741c26030084c01c1c2d000d0005c1140030811456221410380c6101034001007142415000c4075240c40c80213031101f01c000a080010317040c21080c288801010082c05460641c03042ca0000c291980392405546d181c000d41c0c4144007070701d601d0a00000e031007414502107003103590408880565400e9400000720386140c000d80740402e0700e46041004030759651190030001420743c03410741031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 450740674 1250 450739424 450739427
    0x40f060c030203060a091a04150801020423030a050d03090804090e0c0109080118060f02090303030c19050304051e0f030c070905010608060d14031204120801080105010b0a030504060615 81
    0x518002e034820307a03403170926545405041c800c0f0388114011150b000708a4101e502585050341003046a200405400030402d950b444030242aa001504044090300700100440d0b00a24030704110160304000710300424043c1016221952a0860000b1364800c00d41c5502c420020300c0141d000b280c0041000c0c010801c98014030501d069120034054480030300107250340380c00207091801401803035400c1800740402d5000d0451aa00d074001010b83d481c1d461070482c3c0a02545000c0c3e44d0078006140b02d1000c90300601d540341401c02402d6a401c0307040084000b4031500344140004100001803410f000ca107401c00600c02c036000c6441d65850f05000c0e0180242502c0002194000050045001070440c1c117020010301950740c8551050b40d09078021621150401e1034080b803200491003004111003094000300540380307482c03620304c014450050b00f1101650500700003080d90030420b81c401062801441d48100030032055041c2200c4a10342d104d42000c0d20205503d034030202c0c091011643c0403200a080320281e01e020300c09258070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 450741924 1250 450740674 450740677
    0x4141b0a200d020601170d110a0f0804090b0108150402090a1e060e0f0f1c06020706020c0d021216050f030a030e070b0405030c01050703230c190b01030b040f060c0302 73
    0x1042d005000c3c08000046c01d03801c440c42098090002800345c0040031181c682113072424140c440800c1648500252400800c6100350140403260240c040207030340c0d606107803101003614140142107040103100001c2100181080041c00407a110465001da503692a10340051180802d5400040d19200c4401c1d1244244000c00c0403c0100c07840c0392120a079041c00c4104004810140031041c43e001101110341c40c0da00d160180400c51500c019502064a01000d9100c81d401ca0f04a1340341100ca407030340000c902405c900c0030030408601880c40d1000b0710700d2740c4441d144004c031801003020403d8070320b1220703868604120301032122820800381c6100f01e0303882e015081e40c024041e21000d84540d507503003c1e404001c165070880c3e008a130283c0d500a40141104460640111040c0d0700989064080100140a10076820201440402d114401ca511203494519048180d0305000c1009510860740c3e0400703800100044850702150304407034000040b10f42903500e50400c5180c41340340c1c0000030801e034944200000d21540503070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 450743174 1250 450741924 450741943
    0x6030930020c010c08160314030709090e012d020912060a0e03160803060d080d060e070903050a0213021201060804031b21020c120c04141b0a20 63
    0x7030071a0702c0408442c00565000015a4025203c2642008822615070300701402400c1640301e0325002c41d410300707a00d0445110f5082905c034900059104007040000303a5003030051440c0703e40200000c2005400008441480148031489211001d50300580300d60541c205506079040c101024091180d2800ba5141458a5403021950102c05a20f0b18089400b200c0c0004165031000c2c640d245116139044540d1101076164100401c285d5201841009160008040002030012200c40d04008500c250030054022038090b4024092070420040740c108202191002481001c0380e90180c9614002203101c10106019100e0b4000da880140b60031000001d43c10351202000e8403031303402692180350f100386005400c004403074801c102515200041c000340c05d20840160281c41000001e0045440a00660021070040e4000000d03000032500a4a0001224142070103400c06104c110020041d036490420201d885d443d00d107006482c031602011440100c03060003480345660100001ca40e0340c440f80300a01c92566a1070100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 450744424 1250 450743174 450743177
    0x30b060414090901110a050c0703020d0302010903021506010507061104051804110301020f2704110c0712120c03030e03070c03030f0809120703091e210c06030930 71
    0x70300003ca0300c3c00c0c180304034501c4080380c0700c01e0391508141b06d01c06c40716038001005186580c0980303100000165225070010303902034400d400101d030b0f42c8090b040190801c0ca4500b2641d0700c011a8000700582a030344601102e0b4400e910800c0015001c10603000480140180e41266401020001554402e5030b06a1102846107106000c00c0a024520b80240b5083c0c0c02014500400014140050401042142c43c0c14854403407d030955403441d120074000506a80501c1d4a4009010000900e4007206400b44001c4018084075032400c0c05111181d51140c111603a08951038042110f841d001008140c8250011224000d50000302d0340c6517903c50038045a24107141c80220089125401540c5180707014400742031051800801508450303805880c62100b40c0d010080860422100d40408910b00b9144820750608010030342c8070350b0f00e036818418092036841740071b09a03110416400c1d26400000e610003042e041540c00c40e180100c3c07068603924107084002c2402078081c5c20b05004e200720b05072421420b404880f212486 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 450745674 1250 450744424 450744439
    0x9040209011a220f29070f061515231b01060311040b040b030d0819050f071407120e060f0703030b0f04140105040c1112030f0c0901120c030b060414 65
    0x950a003038a03c0b80318005c1380400020346103800005118120080c04840e400340000d40203000301686d0304000c8808108041d40c0d15444050144001e0500481403c41020b29050070710744800c040846107044010302c440405031b4200000d07121802207034429150502c200810082c40025124038140700354003071006145000c1d07444c00d104140d6516243c060000601d201502401b1058804402100e03082801404400800d01c034103569002c0b200c046c824207100b10401008000300e03003003286006106400702004030b04611004d10180f8040350240c4000390181c12903082c034080540c03448002c110103000b0011080042500410100180341c0c01d6042840f000c44101d403460744610719002008210b81c551f81c1008107400728200140618282070380a0030100300c060804201d404004d01400389400750304100d06804c0c44000c001e11881c0044016070a0301326003641c120905000802000802c0b03081444a10350100e82ca42040842c018021390124400c03400141c500359485440c0c60300311041004042c0c056020344d08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 450746924 1250 450745674 450745679
    0x40602010f1b2a061e0207080a032703030b040b120d0c020d05030423010c030c03050702010c210e0307051809010e0102070f0b0609040209011a220f 65
    0xc0502c210003a1100344035008000989a1100701d91941e80051407030b03101018845502142c0c08641294040d4500c80c500c003242c120110410301c00344800442031550441d0040c00301c100011142400e0759070b241c68034580000c040035000007200454100c0084081c043c28025012028503900d0742026120031400d803010f01c03d01c0c040c4428080001804458104160842d6860b0501039106180d81e5540b180014007880d1642d109444450565001c0d074452002041d0b402d051a0943c2c074003699201081c0d80c2424201051442520050805201803c0c01010000f0004802003160302812001c064940c1142c10310070b07000070120400c2c07819044500107901180c0040144c0c44c0e240390000b0440151840684100603c0100c1400d0800000019110661755521201902e1909030300740b014020407405151385415011b081d0408600074070010f0718081c0102c0904d4104805a01d1b042650b504540d40101c08025541d289640c2414a0081c40001c07000c902c3c80710f203030800c0c184129802c14141c7c2d40030395400882c1d0740d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 450748174 1250 450746924 450746951
    0xd060f051308040603110912010509060f01030f0b06120d021e01050919022103030103060e06090706050c0106030f0804030c0b030f040312020d020d0504140106050618010e060d0204060201 82
    0x1441074500621040c4108030034455030384240c00105000c0410305015040400101c000795505405007101201a9983d400304292810104071882c0c01108034a010b14455042d9100d0100314001045c014106402c8440414090340310a40500c20101003242070750702588440d107000b902d45250844413000007602903c910006001032042c6030040890000030a11700e0011b10039404001c0c08040243c0e800000c05c1c0520865405458080d80405c800e41e02842e41d81d81145032082c11034400d00900400e50b4880000c002c801440024440c0545009013880b035221403400121034054903654000800c541d5401a048040158040250080c1c0303110b48054940da5807181e0020096000c200e40b0b02401170840008240802e02810300000d01c001e440308098070702028841071809036846490b03103030341540e0345030100030501840100c005030b01d008440c024001603160800180c0c5270300612200420502030000400200c2e0b000c2d102000703004401400240d00e5184c035420708002500244079510255082c04450070405 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 450749424 1250 450748174 450748201
    0x807020309010e09040305090d1520120c0f070305030a0e0d0903120210050112050d03053318040507090605062b020409090203160303050f0c0304050d060f05 69
    0x480180e651480004443d0100504028003403c1030341400300800c015071a98607140030601d20107000d1000f01c6603448101041100303d4010761800c1c0c508520221100a00c1d0301a44202e40c9000200145402c4644508000100c4c03441015400007840e580050788500701a00300b0055403066180c40001c01030b402041d0300306500d4402100510b4000f5000b1441403002954203c4a80309a80880c41100e40074800000d001044174001c1c0c00031200c52003103110100411008000220b0380e00c046c0d00c0d050115080540007011564036101100403151541040c11040041000b02000c5558000707041080c030403030004600c000482c043e101605c003801224000f10b110b161030f0150360300304c607005011140342c81a00384280303012940030b901c141203070700f050058407100c45024005000a0112a4400034004c0c2d8988101072800d00c1d140a0109104191142003000c240c00038156129015152071455507041520480345c02d500c1290025a800403424003540280308282c0e0004907002c8220804010390340fa41c01c2400d154 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 450750674 1250 450749424 450749437
    0x2704020f0403120c060f050f070311040501030f1b0801210b010b030a140c09040c080603060a0216050a11040609020c060711070803030c030f06010c0f0f021c060b0108070203 76
    0x2020040004200088110f402042c51141c185801d80e03070000076580e0a02525203500500b9a02a115400d005441890419045c1c004000e810100300c5101d030300800000a0040e480b41c10706160b03035481c1a42c1d0824407504182c44483e000c2004d06410703214080080c07c015000e000b010f842d02c103100c0801581a094940300701542c0e800c022650381903840d000c2c169040d0360005090708207a5499501c501403184c2100041c1c0d0107641c003c00505c0d21006468107020841d110703041d61b8020407040ea01842b09503280480c25a4102031801405650744503040c00c2c40100400c7c4400c010098400e9101100910406c0c90042030a8502150213000350f590b103200b48801c2c1d0140d400500c180f60015004a0301071030040041440528004054444032a134030844282035030021142035403103140c00000c008181080291403540842c09080031940c054083d11103030114441d04400415020005000a0641d40e03441104c12400101c2c08680c0c0740090240b400c2e0010700120b07641540030031134000c0851001c81c0048141c0f286c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 450751924 1250 450750674 450750697
    0xa06080d020a031704020d121d04060e01181104080102040f091109130e0f010b04051f03080307180603090c060201060518100905070504030308010501081b0a1103270402 74
    0x15040300c07224004c0c0d80d02e40050022640310016118007800a08207502400300d1204d107032182c500d10194040c0040c500d42002ca0024855032800b0b109001040310040343c9410342d440f80c0090b0f0520030f20b114000000304081d6005c4912980040380008142c0380540051040d203500020348403a29560b0500841030781d8020040c9001c9980030701504a6030f0511092040da00510103002103541602054101d06018071120b0400890751102800e6100b070902d07015240e000300f294042000d02002e583e13220344456203280002030041e203000010582c0507104e2020300c003440800071f180e1441160354050150003840388120440f00d032030808900250071801807042004544010b05100743d0032600022030010400003c006180a08100402140c00c0d216403148501ca20f0305502e40f01d03030341c50450802902800050744054100b0050008108901f288071150040440c45803e150f900d81d0b01c002c9007606c02c00a00c01e404c04091102080001c8107000035049068400f0310b0b021254003028180d03090009910a5102c3e205 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 450753174 1250 450751924 450751937
    0x16090e070f0c1b0b040e090307030c080f0910050403021f050a0c02060d02040e04051501080a0b06030f060a020a2c0d08160b19141605040e0a06080d020a03 68
    0x110301c80c010540b855142e0310500307048603500200007100560300c2441d0043c03000307000301080502120070800185600080aa0010f60030b18a032540c0040100d610000001c026283c0807805504030000e14080d901050001010141c2102050768018125005880300748d01c90200c02000384031164190b6042004003445590b5603290450032803094415084508049030420b80422844500020505c0030748098500b6a04031510b034241800c183e032400407049810014000280010403240b4400504075040a9001402000a540b00f0380040e080c141c0135801c4801c2401540c04220420703e05600610681c4e205440e004204140c036045d0b00441c110028802d642010007424145e40d51a2446411241e82d1241181c00d241007030028502c040001c10364012111841800c00713200c030106102e01d000c1040040d628081103400c146216041501101600001c815041083e16404c40741c4150101c0300908000b0f10801110b0a007526484010840c902c551142070080352034828550b0301c04591070b400c0941554442 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 450754424 1250 450753174 450753197
    0x40b010c03050a140309010204090608060112030e1210090311010c050d05091f0b0102010f0203130609020102100c02160803040e01030b060103180b1005041509021b01020316090e07 79
    0x10707100756000d0071a000a1008030041580021413002c02148216160303400035031203d1030818030f00c0c1903480c3c54009804a81000d401400f0f2035003003030b00314400281c15182800641c4103100110f114506001d0700d64406000704a03071840100c60b940c002d03003c481d00c07035580d41d12140b400b0000c4600b01ca0108020301d0014404000400480645802c8550040e0104080d141c174040306044003250030442d644034028290321490003985a603028840d03624407a0030068103614520749100c4401808691050041c0704075070b18a02c0d40c1c2564420028240720400400082200707d81d4a040a9074624100d50b0400980440c00d00200b101d810210a580c100c99030040c44c02516402d680d103106004400030015410103648d402000c0e07086801454142620340900d061030b02762b080441011549201d0754111900841c20031503524048041c0d040388000300c44a0b0034005880310006000402c000740c0800a25105600100a01c2a003201c0150007140c09005501c881740441d654541e61006500d0450740d541c049542030090 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 450755674 1250 450754424 450754427
    0x402180f0414040b0412020706080403050a03150b0d0b060702030c0907020a02031005090d080411010f0e1216063905100203011404060f051005041d06010e040b010c03 73
    0x11800c14420007400071441e071504207450b5050b810225002e0711340302110410300090041002500c2101001d501c040e042107410260b0141c01110302510043c00c02c00300080341020b15220764091006a0100e90f41c1d000d03020760307134030000c402e5820581b00364031003030324046d0203030090706c0c0460450f24a154044c1c0688290345c03244d030402a120500400320415070013509035100050354140200782440c03641c881c0005d60360500800162030b0560440038101407105a109002c04181c9a406210321000d091030109400c0a00070380844034409561855600304034802050400c4c281c02040c4241101e0003080f2441c195039070352030201c503003004400d810050504206407000e1200314202c80144042c1c81100f181144041035501c052810b407000c228840310301d0340800140121080c10800303542d010300460b404d00c9200d0400540c07010b05111841500d120789041d4140304e1919001c2d01c01d840080c50b0209803408d00c5503440f214440e20301004c440d0311340050007081d6404500e01d86072080965600040c2c1d01d07040f2841043e42c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 450756924 1250 450755674 450755689
    0x6030b180406230c0d0605040e121308011a030610030c14120f06061c0309231002100f021204110f0406081c03090512030408040b0a0f0806040218 64
    0x601228a6040822081d030000c04605250044d1901c5442e280c0d6200c0e0250740c0c008580b0355801c00c510440c02c00c1a501119400021002c0b0303a40c0c00f8400d41662040e03040005d28006038140d120f403c0039400c220859502d04440404003440000c26001d41e042c0b03507111014600b0f4540c89010040c40307400d0416043c0320201c00303644141040c41014124a45851900c40064a04074840b01000015400300c02007103214146008404200f2401034088080781081396405800000240a21b03866003a0810100b0031081041c65642604000500102d0004440380030081d1a07081d4240d0071108141890f10460307000200c1e20899140b1200241d142c0d1440d03c483d0303100190a02c40c00d0303485030310003c440b20803c0241d8030b074403070311009200300c400034246038150901c0e40c1c18010415282406152608090394041a00032aa220111940c469505d0f500c2d075480c44e02c51218002d0390010b0342c0c1e030038010070491842c0303400590780c10410f43c841c1c03031b001c40555541c01008142c3c401c480518441012000341d00205061941 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 450758174 1250 450756924 450756941
    0x4060e031c0905190b0402210a02060d09080f04060801060806060703030c020a0b180118030206061009030f062415030207080409020a0e090a050601170403110d0906030b180406 77
    0x5090f0384c3c5200e1804114284030880000643d080c200300c1041c0310861501401200c01144281c1202e13082d400150441340e04c0b008102d201038011040090b110007048080c2e4480080d0507070000059803a4004400441030340e4002e4040c200c04141054000305486014441242c4074620040809182000c20381d0118080e04030074030003000354070680710304400013008400e040f8400d030020140109600c03046040c890a45e00a044001300304014040c840c004070703a01164495014006079101114000c240c101110042402c2d4005403c04480740c200c6c1041000b65000001e0300e5038410400f0384514400007041035400d689200d2a01c09100403948081324500940190200500900a203400c00395103d00c44070603680000c50172070001d00000075803103982c503100c4001604003540b414100107a249c8400060902500c1407000c840090700b0400080415101d4412104d40e4144c1d07005445a480c10284040d00b500181e00505012900b00148020030f4284641c5000c072143e00400480c00648554482200410f9000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 450759424 1250 450758174 450758183
    0x915100201110418200919030c0b09210a0317161b020a080a23030301030f0f05030d0605090108241b04030b06040f06030203060f0a0608010c050304060e031c09 70
    0x2540e640a061030808041d007401030f5070741710140d40c841c207800801c00e500c1c0c482646030004d03405070001400880c0900902e001510b41c94481d490352210b080d0300084120a1614280c0400c2d00c0521655110340c07404207a612150b0f01c2501c81a135101c048414040c170340d42c0d04440c1c074041c4e2002c00c0040c00782140306114043d2038480a248241c1f50496540100d00300b14440d800c0042150301c820305840c200124480c503090b84100350a00c0d05440d210324003155890744010300c005000101c1a0400c1c0c0e041c0800d00c0001100c4540c0301089950b507034070f0b100106000d0000d034480c1600c01d6407950300000310703c880030130000d08140c07010f00030100d4508034004103005107070041c0c4100c9500d0700448440080c022410300910246001c0e40c00e8101e1803410508000070f503200000c1ca080c44a0600d0070030001a02d00117001034018840c1c3e10a2202a568419000014200359104005540c06d00c40c00e421125002001075020742c4c007480d000c1c400c080c080c0c6d901c543d8074800c0e094407102da6034003c10315504020f5107074040c00085129 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 450760674 1250 450759424 450759431
    0x30708060a080d18150f030b01050d020301030b04020102010614010e22060305031e0909070804060b1504030506090a03140d09060c050d0b01020604120309050c0915100201110418 78
    0x2259021854485440c0c045030206040021300c004440034082c100c3c0003081010300002841e0084036000f0104c8034882080e50506490b509101e03101e0707000750b00ba44c0e00020031a01c119240d40e5070781420900c164041e103040e805940790000c081114801400000803c01040c0c4684401c1c60800081c4040c0d0030f8240030b801e1032810801c040d802e442c038180c042d01c0d0096004070004d54550007005041101004401c052040f0044200103003600c984544078003950001d41800c0c650401d07a114100000074100b0741901d0381c0e000c10b00305a00349802807454090402d507070294003152800d65503d001c0d260341d40810315000d00445c0c0003540416040016100400e1f41c4800d0078000302e40c582803951040300740d44010143d040414004140c1842c1c0c1111403141e5203815100f44028100c1342810b0305e8800d403000c1050802c008264031482d2000c01c0c0102008200d4030601c0141c0711083c98540000108554a01400003910501e5180c030f2001000e0710500810b440388000250061509150550084051c00044000c00b0307820b85 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 450761924 1250 450760674 450760679
    0x2b030905030a031e321605032101050d170d0615080f07120e0304050a0e040b0609010320210607021e0604021003021201030602181005030708060a 64
    0x6040c00080400d9209031929800035000d054801001c01140f018401002121521081041684080c2031010f06000c4002800e2801e48031520310540300d603d040c501c081c80308050050030084004014000e410300c0501207868102c2d04000706000000c20f110344cd50102c01c0702400c001140039401d60100b0104145a1903241c90a031510a0050701d1722684401495001508884c92080e00006610352052200207500c0f800d141c4a20084d182d4030071000102d0303e8588d030b002c1c080540302081081b903024000091030409007940e80c9005a00c01c0b14126011104043d0400100d000b500340742010038141d0781d0000c00c00b03680d244000c0e495800c1e070300c04050703055100742e49041e050707450b45103410440c2e50107800340d01400f0705241407030f000382c0340051404201ca901580c54412a9100c0d4022403400d4205074102c1e00d16168203d0b10b001100a4000c07180030011140d00c039030001041255542c010545464810001d9401d0411101000070301000320348168041201040020002c1c2d00c075103420350b480300008100034049074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 450763174 1250 450761924 450761929
    0x1c0609180b070e0a0f05040507080f0f04240b191d06060409020d02070b0907050109050616060203010806040618030e04020c0a05030c10062102130e0604031d2b030905 73
    0x50817944041580f0320303440000d209a0425004c2c0720f900000300d04083e1110f050810020704409001400c0d1030004804401141c100061300880c60032260078004d00341d5001c41418600b0300200001d4081344d1060300c900d0943d8240000040b0000d044800040d003c2c92102d04000044d00749503c01801a94440310030440890008803d01c041c2100f56000c54005840f48954580010003440180000340d6a130b010000400582e81d112035814103661081d02c01030348031565a4449075682c107016000800395030000c400821280c0b00001c5207882240100c80500020718050204507039541941c05c060001814024038148604085d001490201d00940444070b0010346600e0380303420b6812640002c0404d8010b41c404125084150080d24042c2240350481280300c07491040040012011600083c000e0151b4480000c3c01000d561020803804441d8090300d079145003a1070010b00941d01c24100e134180182302c8000784050300b07041041c0901c500503864190010801400001d000034a008022420004032000114068 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 450764424 1250 450763174 450763189
    0x307020a02130e1b0a060f0c020904060506100f0e060702031606050414040203090c12030c1f1b02071703090301020409020909160e06070609081c0609180b070e 70
    0x641c2540c80040c243c0c0038000c10508045100309400c03812010308000400d40c0d074520ba00e001c2102e19604020701002964602030300e443c5698030010f03501c42c900c0f5041005009164100c1807013441d003180c0e504900854280300b607a01c50144005030000a450480e081b11314145903000f48400b0740010f08481d001c0e51100340d201403016503608a90000703500802e04002401d1080b1200f000201c0450307066045240001d101a9901e01c00d0070860300c2414155410b001c2d10380d040c8111988224034100342d84400224100c4a04802c070203017102a4414a0a107514000602c507200744107642035aa405030020500e003080c404580b0910b0261205070f4001001101c0300c40e9024801000242119880944c1301c0c02d02c0020031030900002401e0304852405e050b0b000801503881503407891900401c4860780d880d0402d9042c12401030280c100001d08440c000104030816102174030400255880c01d00c400e110351034580c070354101941c0c1e003580302c1d54403502100b101c1400110034a0320150f0260f0b003441c00d640000000b10004001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 450765674 1250 450764424 450764449
    0x1009030503031e060105071a06010c05070b1806070302061611030a09090b0604050d060905070906181d070315020c010203011d09031c0b12030a030606032f0307020a02 73
    0xc0b4100074480c50f21030002501c11983c828401d090090a04da00d9450f4020806881d05040743d4519619000614980c080c08e9841d1019800c03400711244546c81745105012580115420b054034107184101510b20f20b0a68200d9044550582c0a0039143c2c4907484043d4bd50b201c010317007500c140040d0305018660880100040c140a981556440280c01e1410300f03a017084541004003540224001c1006101a8442c41c0030916013a0f40400005100261424907074202492034005160880c20414002281016a030090404541c05e40702080042c1182c0d1112800000d041c0c404252500081820000716501c5165200b8140340404054680400e41c0102030890f4000d800640e942036071880340001800c0a20031050380f00f20803030000c0d0b1800c49007484860614540c0c480045a5585824100580c2e40f5003001c0c0b06810340b0024201e03030f02c440c10400d0140140800f0b000d038600080c07a0441e03139240010302034040c00001c0c0500303003003050281402d82078030300380d600050001096101c2c0f52000300041e21000a00840c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 450766924 1250 450765674 450765691
    0x1109091b180a080313060c0c030b0403170a0b0a091e1503030807020705010503010902090102031225091212090f0b1812070605031302060d020d0c05030403020606100903050303 77
    0x12890807404004094580341c00c2041c03e0b5106000c00003807826205003000a0316114188849003800c40c2c64849000700350703608024040c1000000380000c068000500308100906051b407894180c3d07034008202e040303c0b1080011907000c00380d0081000f41c0e40b4158800403600d066400c0314900045503015403402d0700c505d40c0b019142403041c3d0340200245944501065001142407010703051b0300f49000c000034000d01040c09402141603001138400042c0c2c1c02042150b40e00d00300f040b00007495103800b80c916404480030b5125080014054446401650300c1032042c81c090310480c11a00c0c08240083c0c80c2c01d031420744403440080510020f0140460035640c5040d0504c01044181d0400e99555032441d071040000e0800e40166020300c0c0001401517420f600496140f040e03818903c0c0c400e0f02c0355a030000710200003182c0c1c0ca0284d0040c00001d0303038000b00b5035941c000300480020010140481e030342d0000125403e11080b5006801a0491004241281b8046500302100d441340d01e020440340e92a0348031242140c1c01a21100c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 450768174 1250 450766924 450766957
    0x4090b0612070f053705030f3705030403110f0f09060108220807020405070e0d06090302070b030a02030403030c4b211109091b 56
    0x20262404403000d6403010392401c0544071291070140312400008460080622414440c0501c417444014a00c600810744000d064181d0b51808040700901410003d00a103402030041c103039019174a0f50001105400032041110845000d4003900764421f2480c024415186509000b45512000c41c2d000c101900203180a01c51520a05041c2e00801100c1c007542c1c0d00c981d00401d1100d008941036a1801c0c00c19500c10402e003081115a51000075607419404811580010481105005400d02c40d0400181114902c01e4400300071948540d0402e0b11030b41c04d10440c0ca544010304e501090000b4000f030f0400c803540c600c2401181e880a88078450503545820072030b40380c044254003204000a140d45401074030010551814060806001104000b541803003940c5601c070083c0c0850f19a5001181408440b1500424150180c0c2c03000701c5c82000920019041c1c0c0000404034202e00c1d000c1c5001014800c290000380c143e01e003d46807038402820b01c4160100108920502c840d8545e800c080d0b6065040203242a504107800301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 450769424 1250 450768174 450768181
    0x5040611070c0e090a02150a090f120209091204120c0f06030b03010b040509060703020703112e0b22150b1b0604020303091216090c0e01050a020d08060a0504090b 71
    0x42e83d0341d0400400d44c0d6425409886074101580701c140b1003025050f42c072240180e64807160203041d51a80e40300e500c08a01d0307900000b0001494010b503480c2c01c51240c03088400e5509501e412480c00e507560902591203205400404c0104400e07280d42c0100a821880f510403914030942d82c000780d4940070803139840755001c41d40b150300c140101c2c5070a02c140c0286640456040000e42000007000e030750b4030b0b402403078042896400110103003454007544c42d040c61000d840f070440d030403511309050a030361070080b43c1e11302d0304915503059030b00007061694040ea0780c4114014050f2514403503000c0c0340c115003121104403ca003e0340e441d0340041454131042d0110000d044c07141c1e01a03076511002c44130901c40310116940c03001c15800c00414040142d0703003c000c0340d2501c0e50454092440c05c900b52000e50410100340402190781410070000a1464001d0f0001c1000c1038a98982c4154214088011340756031081c142da140040e008208003605c0903004403200350304008064001404075884e00c011404503500104195140e04044080 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 450770674 1250 450769424 450769439
    0x1f02010f06080105071d060408101a090103050c01030207110301050901090b07090308030606280c1b0806041202070902070501060e010504060e1602100501030f0c0f0605090405040611070c 82
    0x1a000140742c02d9000300a181307400b03140181410307204164003150b02c500802810f1181c2d00e18050724050a070342c08c04d031920184010411401080344440403c400002c440000a036450a5406181229001005803c04000d0301004400a40c0250313802c81741007001d40d9203d041500c09100c0c030341c030807201c960001524400c60704122843c2e10b0010402c1080201d500f00a20000e10072800380d0f50042c0c400d44c0c1c8030b51120080010b4200180500040130ba419004402c0d81700065403000304191114003400d503403080420507010314120760107a4080d1002c1680702d5404034000500c01c1c4940c808c04045413042d40c035211388951102c0d003a42d00814080c1c070641c1d1642c4041c440035607180c0b0154010482200e04120241c9403240341b40319108010100303140d1042a8007149400340c02400030700d031a41d0500c0010406580c6a00e40004142da010b5010344603031100a5011031405418a20b035000d541c0c01d5180c1508000c050802c0002074600100201e8921340c0f10f00c4054050700103040a082c103039106440030400d26081815 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 450771924 1250 450770674 450770681
    0xf060f031416090b0921030405040c051e030f070f03091209030c080102130303050d020f040f0303030b04050c04050d02060903010606200706120c03140901050a1d060708061f02010f 79
    0x211603030f01c00c410400b80003181c0d20710f414010061104920007072210346c1c9000c5241940507980c05550060f06000071401c1d020f6005006001d0161030b0369680001074001416a141070104136070003007110385448085981c5500400042c00980361030310f40817507040300b00c0d13807541c0c4c0180449a40c0e0010402d00d240500401c01246883c00c06819200300031818023108a24840d49841e082c840581880302c00210382c510400103404542144003001109aa1503030384500504c0918603070b110a500107450912030041514060103540d001d03001d0404540d06013418042017108141c0d0f0340b4012a8000020002c01c14507442c2801400000c00c06030b12041110159600c1c5102070712500056910150443c04040c001d440d0400400e15040f81c8031003000902881c00d107000d0f00105032078044060300030130ba4002c21881132815008584200034002040c0070100c2c640b900305210a10241008016402c4000041c0c0a280b083d01c070503510200080500426580100107040c415241c0200c81c030041c0d441d2170105c40401c00900 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 450773174 1250 450771924 450771929
    0x212090409150b180408070f14120a090b090a0510022404030206060303130b090a05060d0f060f0b0f03041106030f0114010903050c120c0a1d060306010f060f03141609 73
    0x20301084180c50546e03a641321501c1615001084445100e414a0610424244801c007000c0240c04071500628110b03c500d07001c1e00150308403000200401d0010405600c140d046d03510104010b007004508604100400442030350050f0080c0861052042007c4140c0c0b04d030b000c4100c1d99440c8607160700070341484e06000341040300040005019500c2000702300701c0340c0000b22445040304c040400e415110030301c4400180c40744142c3c1c0d02455000074007180d603000d0481c0a50140918065417441000400c0d0b80c0c4540d4520180207100d000088501403050344906044100155400341c401d417000702c20500b250700040d2141e002961010840410540180420301861140d140c5c000024204407440078a10b54850390385455071900280641d40e00d206950700100c042000e024034940c0244100c0301c071a11040380760700820030300703001c80588100500880c0482c203020a11a042e00c040d4120300402500700342090740c000c0da242c4440d01c1016038a50401011401030360402c0c0c082c404103e090010b81020305001010001031781c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 450774424 1250 450773174 450773209
    0x1303020f01080f191103090303070206100f0b0304020a03080c0303011401080f1f0509070e040f0207260403060204060c120906080114030a0c1e08060103030212090409150b 75
    0x441030012600000c4a49540100501030940f113410007030080030003522141700b00c0c900418010040c081041000f00286100c0c6000354200d070b0031a61101c1821448068901c901c0c154007030440c0c414000e943e400b0b401103a0290000e404a0103031580c903a6507051690003207820301c40c1500040014012110b01480c5a040aa801d04c0c00c580c250074140040303640c8810140ca03031070500710b580d40030908000c080d48014005001c0101a101c1c64500320b40054400303400001214402c0c1d25100c3e5414256803d40700340c0d0900344e0000718202100803900302ca05c03045400c110026411402c2484000005541c82c0010000b50103584d640350203404e61460300f9103a0200c03109020052040245003400207691141081c1e0444002d2004800e0740021000440d06008540d030340030b4000032a10134041408101d000c1d901a40c0c0c2c1d10a2020b040e0a50340d607c0e0582c481c1c0302804014010f03001440b00c8056180c4500140400103030081c40001c442e403482c1c5c1c1d084002d621502441d90b603103440d60f464441501d444000c110481c41007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 450775674 1250 450774424 450774437
    0x10e0712140706080117010f050a02180109030804061407080d0204060813020d0809011103040f060905090708070503150d150531030302090319050105370e031303020f01 74
    0xa04001816001050246c00782c0701240520f81040e00009412031000c580300c11404002d1414424400d41c080c3d403043c02503104006c19002581c80c25481251503400f213130780007158030b8140380c01c0401c01c0704c8048000d1803000d04100180070144c04110a1802020380f0b229100e030042c1d0b602c0c0ba00e4805000414000d004640070f0001040f070801584465002401e516401100300d9a00c0781e03800010307551952400908034080c0b00108012400c2e51541030200f00343c0d10076403030b5010407980d103808011a03104101d4011000404900216010303900500c05140c001c140003030703007803181038072080490020b904c4000d050760048060914861141118821076401005030207112007500c0740e50341e407040d42005190040e04050035900728001403600c2035068a01d861802000e03505004201019211400d429040588107075190a010407684c003044441d1200908000000d49640c1540d40c0c40e0403088a41000100c169a48440488ca070704482130004002c2c05101d003002d809000d0850043c400c159614010381410b0140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 450776924 1250 450775674 450775679
    0xc1f0c0c030f020718050a0506040533101e0f21090209090d0f0302040303142a030a110a11060705150c19080106080a0905010e07121407 60
    0x6109000c80c0306140c041c101003002880080c012441c113103d551000e280c6800445200c4040001c42c0c005601614400030140b1641d200e803010401110820345180d01d141d004201c0b031052900410301d0119181c602c01425901803400c05002c0f648102d00501110000342150540561549a03a005003407825061f18143c852903005480240a0125000103940981041c494501e0201c489801049490340d003d071a4a88501340708640c1d650b521807026603000816107a003044251a44240709a80899070103a856100004111034040c0c0c0c1903100c040c2c0300546001080e040188801c0d10414082d0f00d4210800455984052103001840e81000c12464100c58000c110102e0105400726441b101102080311256982c4004c0e19240e898000441080780c10b48a044040280542607940641601c0c5440c0d0f0202820a81006085400b10001d016501c0441c54943c0443d00c131202a90184402500c5900000340c001c184c600404e05e054015408504415141c03100031080085031441e0000740202c06000f000302c0c60 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 450778174 1250 450776924 450776927
    0x306200406030b220506100519050a030e010e0606150423010c1208010509010806040515070c0203011d16060807300902040510080a06020318030c1f0c 66
    0x1156114007400c00d901c50b50603e400d41d0740c40480071042806800c00c00d10103c001d1840300082c150481d0094403e42030701ea1a185941d00403c12903401940c80e10340d01052044182c0d046d122a0000d0801004040d655009904089000d11640140b01c561400400729803034004108444079149007401c1120075400d200801850707402000a280107452000c02d800700c4142c9000403110800d2442001c2c1c5420500c41c1c59426464000c1480c90503203038140c0d503c2d44180c1c1c031140303a260f4440302910020130700d034403403080b001d110101d0303002858002607289094640e601c12500000c1c203540c010740200301e100c600620f202c95072000400400f014104d40d861080034051410f07030007410038480109a5801e1002c01d1028141c00941c418002c07a414440c182401b841c1c07155072441c000208200c0304124000c1d494400400d002034000d1151508071504880104403001c01070b40c9150194102074803100b050301e5542c02074005113505001500403040c802c00188144620ba148490320f407400d094100340218a0807400040b0503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 450779424 1250 450778174 450778177
    0x30e03032a070c0509010501090506031506040f1716030515190509011a090112081c0513051b211e070306050a050c0301050910051801030620 62
    0x8500740001000d20381c1c1044010301d10148840003040d1151001a00a0400001c40e0500c402c2e03c80503915104541e1700c850042d50310301d000d03002e080c2e4050010b10000e4002c66903208810100c4a026140504240d6078070a602e00d05151034000f00000220000c6480c55141c1c200045002d0b100d1201d941040f0324555184e141e10790700250002c0708441c0f20000014101004000120040091541d04000525000080c10300a01b0081c50381d019801c09500b0580c401d191400301607058610904000c4000304040e600c440c030a601000b040000c00c1040706c021921200705e88289032184c00300d8010540240c0d20b51804c507041c030381c0c42c00d062258501c4d00180400243c0351141c4800c00701c0c4d1041961440480782401030342c5020a140308801c00070b80c6488140c81107100200303131102213900c00d2100b44400e450307445540080d03900c00c031595900c03281c00f4030040010f07142c0090100c2e0440c64041c0e03003c00503919440803030340034004580c040c4036112080f0010010014644a02d007910710036040c41c02004201c036004c0749501e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 450780674 1250 450779424 450779431
    0x51b0901080c0c03030103060b1804050304051908030c0102072f040c0c0b270102090d030e010c0c1202090105060903060c0d0b0d0507061707020c01080a0f140412030e0303 75
    0x4010034000040c603465000001c43e00c49042500c2207075203035a034038907202000d00300c0500d00c94000d007420101c10031661098007a4500407580319010f14140317030524041c802d10300c2c0804080800d88101d4000062140d50030300040c50034155101c005a03950300d660030000c14896201003010400c0ca80403034034400e950300c0c4041066034a801118042074040c603540c0c0c03c44400e00e031032001502c0340d2030340410301080314090780380e0a840c06c281c101ca0701c0d10700c20941e0100b800c0b80940e1012681220380100c1400000e446004a0001c1260504100c05186000e031035001c0e44c2c01003a00068940f000000c15901545482c0703040b58014402141c40c40e2030030003c00086501c407440540240c1040300c0200c0c5001403184190000e0f81e030141e002d45100303119a02e50414071f6403035810b44074131000b2804441b001200f09601d12115841900c0a40051201456078401140c0d031500080c11031100e0755455048290a0364180070319045081901d5a602c010304090508100340444001e05109051a051a1240c2d0010220590b0790 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 450781924 1250 450780674 450780677
    0xd0215060d020d080a0804060c030207020a050603040804150c0203120c0a020d021c150e0c01090b070510060b0a0807020610030623100303030b03060c2b0f02090301051b0901 76
    0x181c40314408143c48182c51440100560b101040c1d40c2882d035406284288900d000300024010741c40000003c1e022441480170107508214458400d0129040820095420921072044180750541d103600d01e92102c0410b09050b0300013440702c1448801c0d4a41001000c0c501c1c094609840d2522061100440d91100c0040d00240100c945c1000141999900703070701000600c0d1a02090117482c040c920749042c0f80d00f01840700c10080b900c1c080c20804050000118040a410182c51750110541803801d030a4482c2c0210500700c40314440c41c441810715900a000e0b11004081000b0002d4644503602c0014100740740003012135045500c18403c1128082002d13407100226a00100b0000d000e060200c41c0d0010030141085480c510550041401003205421600c2e40440b40a46c0d0100003402400d8201500d61030180d0728403002450901640401d031000800550364480c4040b68004c1000349a0f0440d019149c070780c80d03040f007241d90105401099050a02960358400b8000984a41000c8403110302c42042c0181a007450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 450783174 1250 450781924 450781939
    0xa030c03060503070f06120908161e0803010509071e0c080705060c030115020a0809012a0308070210050402031b06070c0b0a09080c0a090e070b040e0106020d021506 72
    0x2404180254000c00c007400002e41910861600c441801c4e1444103103205540000c3c040c0e44600c0a0b8103814401c5400c1c031a80002000e00e00500c81c1c2000c4458070210406481010704a21741d0ba070401d401d20302d1507080f203100314502c6480398545001c00002120040a06081c001c0440e400c01090504c83c4c1040400c030f4450502c152400341e1401d2088007400351580040c06441150305111001456001560480c4c402042c00ea0411400502c202d0f255561142c0c010b0a0030402e00c0340740302f2036002d24103002c01d281e210751846c8102e082c0155844c004440b101415400710b0007190500c241a43c0c18441c2025401729490f0910080c01c150b0301080d070b036010107121517441c1010041d40041568544040301c5d1506c4c0c0100b0b031202e1150b103c03455014542e000c414480080f9001020000c0c403120080f460048440004002e0301585203070802c417201a00540c07828070700038010f003039010581c10042e001500c0a098805002c0c0300755030400300701920b05601100c450080d503201042550240c00d4225200798081c030144d5814 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 450784424 1250 450783174 450783191
    0x60115110d230c0f120a02030a0e040f0504061410050a03062406051c060303050d0b0420040f0b03040b151f0e0907030203010b04121e0302070f060206010b0a03 70
    0x100d00c1652003102c89880100003c2c40c45828080021340f4016448034005072001480c01000c1081113106c0c10071035002581041c488184a24044c4141c1c10313a1344800350000c030b81c03c0440040e1004031041110200d880503030b12910094240d45800c1c881c4e034040c5a0b0720f14036074018100400a5445e8005100040c041526105402c1914444030010b007c140c80402c1031105058941401808603001030101503440c002401ea00701d2402d03094060482181e406031101d5251940e4062444060f0090b203442740d401c962101ca000e05022141c401c1c0c0c6011000d92515681c549040c102d40c4000804903600c0b0024502060040c8000b180070781d0405508281400041030a091000010940f280c00c580c0714070340c080003502417107940d03240c00c0380c000b03044040200c030f44101e59519018141c089000c2030080281100381817000303001c0c3d03941c10800d40000070b0140c044155061903011201d40c0450701c1c0c52080380160801c000812510481c0719481024010f04c3c0082c0846604000d0503803c1e500030b18104204240d102d5820 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 450785674 1250 450784424 450784457
    0xd02030a24080d0201050c0403140c03100204050a05092205010b0312180316121a0103050106030201020f0307020906010309030e0406140a08031206060a0909050405060115110d 77
    0x4500510301e207640301c800101114100615280181c841c151442c0180c2c1103442c071075803042c030403a44202905642d4a04080c115201c41c500c0900340f94150f60103106070804882a03030340c108000d610000c141039003d40e541e03051106001c56400700707500036802110005c05200c0c14029103403495111203845560380c01465001c0c14010301500104c0103c5805000f800304c2d80c0800004a0b00500350080c42e8442038001c880740d0814144d4850103c820034113482d00900302070140d000340480c43c40740d0a01614000d030f01c100005082c031403008000c0c0d1080b03c0c660342d02c02e406c0045580512151103400e1018000e54204140341e008214020f200800e450f040568800c200f00405004004043d044080503001700f0400d5207500342d51001c4580c508215100d40006000011b560713a000086440d000c2111780f003031409450741c5090080c207402c1400400240207040d132000c02c503a1100e200d03da00c00e5014100801e0075501d40303404440b0146138000f510b4200034041000380c1c260000050000300000ac54a01f490840c00718007030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 450786924 1250 450785674 450785681
    0x102011a0d0f1a07020604030e0904230c061c15120204020d111305011b02010519030b060f1e0309061311030a1b092a0909050c0a140c030d02030a 64
    0x480d904140c150f40c1031001540c4e0000c2d03410b01c0f45200b610790170105d00001081140d8084105d81c000d182c400c0c1c0102c0104803e0403134035850140318264044900b101030050002d100b6030025110030220654171442048404554065035815017201183e00013010f0501744400160050f500010b8000e40c0c002645000000003944202c110102c0b407084161903034180040c4090000203445224001107041070350b1038410032006210180240d05854043c90410f901294107032100c4080d4410080c075545070350044094441c1001401807550050318a65100c0324402008824a030ba41c80c18100071101307000300606c4030b0000940c19000b40200e086031000321000e14080d40039600d000612a014045c43d9420000c014211140e0104e8015240a5078819604c500c50081101c400e110035070904444012050312000705001100c04490f204d240c00c072006610b0301c00f4101030342e1041d0344c03880a1000001d048450194040100d290428040b42c00c5460524100c840c1d507a40e008003540b481c1c1e82e0f980003010541c800301a51 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 450788174 1250 450786924 450786953
    0xc030f0c0a060c0507050c0109050f090a091403070b0c0708040e0a060906150815060a140904140609060d0c211407050102060f01051f110601140102011a0d0f 69
    0x4900740016443c0c108010300310b80056504983d988940044926550701406280b0280c1c0e8003d000910180004070801400c103501a01c0c1c02000f950720078100001ca004140d104001445600003107549086500d00f101020b41c00422807500a54144a240b00040b110801c80b412164225891003454541184200041810750f1090301e07242e1500070005507040d4544103420f42c1b451192201c00540d56032715044040e6040304110a030340703e00b003001024180c50207480c1e031610801d0f0400341320f400d110900b0007140403201150382c0900003031900010010685400100164800001e4881280c10644c036500c0e001c81644c00d0103404000340b0011040c001440c5824017050b0ac16801c0048101034151400000d904d0383c0c800c2c0102401806202c001404845102051034100e42014055802c100007a408142c214140c0b03842010410007007114628515804100c6c2e03d02800110011130031841c14500007908582d80ca080800d4084040140000f1903515488620304058100810b04490090752500c01455100768 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 450789424 1250 450788174 450788183
    0x506030a02090a06110d05090a0e04031407060609110a360905060301050c1c0903110a0606060207080a0b0c030406020f0a08011d0103111012060e040501050106050c030f0c0a 76
    0x140320018040740d00500d17849400c00004240c80d0250120103080382d4610501862642121041504000a600003980c1c0c0d6842070007458503030200003014041450940c400b00054681a4445105011818040c400c0f25080c070303c0300c5031017071a2110b2007a010300210301080c10207818521012503002c02c6151aa0074802400c00507041c40c010946441041000340010b41c2e295000350700e00b5000a00381100c0c202220500c082c2541c2c042d1103d203107204803c0c00342034105812400c0164002d00b002c02070701d081150420140c81400b001c14601d0500e00e009107411103a6101007420340c840e0741041e01141c00482c0c640e801140184089603030395030764103040001e40304514441c4500900000c0781c40b640c41e44001954103850a10801015540000840c035041d07503002c0c00094003001454111454034070f007039006066410502d0a00b410300309250740c060300171a00300d5070105848a4542d070400c41000002e00c9468003420041c2410f43c140001000901c3d581e00039040103002d54400041ea05044580c100200c00030640d20 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 450790674 1250 450789424 450789439
    0xc060d02031503010605010c1212020705010504050c150405120c1002030307140a1b0201030e060112060b0307120210030e031303031d0f1c0609080a0807020105100506030a0209 77
    0x1241100095100329081e80080740070241d080300300e01e41806070004442c03050352005c0540d0440d80b00c01c1c00440c12440302105010b640c1c103912525001a002a091090007140000758a01c0c241c1006070030111909200e0b4840c018042c156840b0129075000d40e020b850042c3d45005001a0098110340350200d070141c1144d2000d044031001641d40d82c0000210b2150043c1c6d074940178800d03401c854180c03a0b0f00408140c4400715843c07088584c034000307410b060265568014500441e07103030303002080070f0704104081e00282c62040c22584248203008140c042c1e2440b003d000d6004181d41840c145205190240c1c5520007031040d4039100803003007160f1094020700d03105400301050302c0d500c8080c07402412040a080c4012008a082038010001000c948070b243c00300101e001d4240b200441140b8100216100160101501007100010800101c0e00500c10544010712822860703a6031415032a0141820388000c2551007103a040c41d040104070400200014100d03441910f8494594036000320b084040d01991000c50b400000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 450791924 1250 450790674 450790687
    0x30c020f011e0e010e1615090b070b06030a06090507060314010503100b03030d020324030307050c090915090d090e010803180d050d08011e06140901180b090910150c050c06 75
    0x11b528030750b108491032401c519940b2003c00314183d9640301644140300b41c88405101f0100441c03071100160381d0001005050300c4003004183c0d1104101d68004d8001c0d038483c0d010000511240b500743c03040603003107401c0080031506c3d9890400001c0e900c02e402c8115104007900d600b8100019102001595104070070b60400b99120310b4204a42144d003c1c4018462007a8007281b281c5141c01d04011040320003880e0088060103256030341c801407181550b000340c0440003c0c4106a94204002050600c00e40115403140283c81c44e10314084e03004099030241d03005292000310800041181c8940001100e40080302e00c2940b9000e03407480341c0001c44080c0c0b03900d0040e0841c017a142410a1641d03011038198141c800c3d152846e21641e05880036a41251010b002e44030118031582c080000d0a2251409481001814034203a41c080d5605007001605011039804942900000320b4602c24034038184c0b0850f9400440e40700e0280035a46031003c4140e0b4030807503100d40307401d10640c00340c05018400c00b4861741c0c51481025040603500c05 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 450793174 1250 450791924 450791953
    0xe0a140a08030a200f0d151707050f030705010909270302011e0203060d03080a060b0f0a140703050405010e0a170d09050f09070f020f0d030c020f011e0e010e 69
    0xd2001a04024124001e9004d0841d60b03481d003038480039005485064100700392041d9a40040002000603503480c01c0c001c6000490b040740c00c5c901e8078140904000303040c1c0c4624040602c0302032078030380103510700c40d80105505002c0c69a02401c80401c84e0402480800d001c40c42d61a0580350325043c600c520134200b41d0041c158241030f01500401c003da21003081841c0c03404441d1281c18102d0005035007990b03101c5c4082030780b00c0c042880394031010307000340706210006a00d0740c0d1812950b00641c080c465540719104081418520240c2203503140c00300b0f8448010951600c02c003550020118461800b46905000311b00c5068030303a40c0c0f40c00c84480e010340120a00c0d019a44203080e82c45d076842d54840c3e60307a4001402c01902040311b09124152041b000300141c030075101c6e5120f003c0140d50402c604c4c101c0380114440c2c09511424000c0400c4031040c5440144c03070010300c0030b17241c8400909000c849020411240c3c14408071079040080d260014149008540c00011410b6514103403501402104054201512440d200c0c54200d6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 450794424 1250 450793174 450793181
    0xa120905040f06062007051e03010c0c0318080709050a0915051f05060d05040f1b030209070f1d0a03080720090403050702040f09120908010608010e0a140a08030a 71
    0xf14001e8840c0480d021105d89a0446202e030030748a0407a50308511410406420110700d1003411224003e4110760741d410480c0403e084484075030710b080004600003104020715405c880c0f5800b0308100428003038040e609181081d551460584140c0031610356860016501820342c0e800903241d154050860f01500a0217502240688000d0340c0030030314840182d41800e61012510004800c40e0300103407405040034900701e00203004290040c000d41e41005c50f450f050001800704200c504164580c1f00008116a0a50050000e07200d801030540c01807021050310000f9094100f04009a0030100701e1940ca000845a004140d500000b503200922510b0b0100d000410049584003080740a8014200c04070751042d00310420100300400d0350050085201000501c02504003a084065078460100c00070841042036500c28504c00d03028900304000410702c0d0800c2c826080f083c0190340041c14480300900c4000b4425080356280d803442580184080341d01041501074035000d100c11818141c000013800c1d160b15000b02200080c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 450795674 1250 450794424 450794429
    0x70606061206050a03020f1c0b0106030c050406020c090c0408122512080901110301080c090114130f06090c090611070f0302061305040f0f050c030106020a120905040f06 74
    0x10861288000c07400d00c00610030b400480e2002400010054030b982c00b409a4405061000d03a007120704142400c035101102501804280e1042c2002c0407130390b1403c00c0003000c4030031941c002c00800008020070403070194000340100e01c81c001100c428107a525025800504d5100301e90042e8054020b420120301040a01e0b4090a0781500d0100c2600c0d042110401903031f20b00305160303801000200345d00c4001003114820115250f00080700c0000140c0540c03143c140d140583c009031f20002050340a584068039900707040a0b1503005005d28000d140411034400001034000b20f11600900e4401c1d0703a646030b0500100700f900920000c065100003000b500340120801070104909010700e00101300080041040004c0000b6183d0486034240a80c003c00c908550801c0290741c48601615030002c0500c40200e080da807140700d00740014492410001d0140804c1e080c2e0410707501c00030030050b03005200f4030040000336000b00d82d00300b10540c00040035000120700c400503204072a00d034210780e81041c54080a80c2c00300942c0e034440700a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 450796924 1250 450795674 450795677
    0xc0f0315020304081903060b0d0506310c030b0409030e0a06020606030307060b01171005152107020f071206050630120c01020a0f0c0c060c08070807060606 68
    0x8a00c0300142020050b40b0041d02c009003c840d0800103003100c0c4400c07107204c018800076407801055140d500d0303a03840c10f13035003044c1c010011030743d07440b010300805142440c1c101d20369240031b44c02e44900240f400982800d1044030302d186104527131244071070000544607600003905401c000300100182d4080b800c0007401398202e04a00380c0180c046203004114240006045403080d40700900030f42c9011410b50341c00c005041d00d15072084c1806031508451b500d5250320000c041c450584040069a028030380020031483c0902441c2c0041d0140c410080581c1000d440595a160410706804c40c40080e182e002080b17141004ca400c14400c1c0380501e0300e0110740c50032a941208990390050500b8400c5844410030032448001e0609030128103440c218504900703000c4240c07003040f480390720016034414451500014802e9842500070241c542d50020301680d081e40c00100c00c1e0035196092400c58034030744850b941d40442d035010b80994414440740036822420059040c2c121000c2550001900c0d40f61096464003502034481409090b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 450798174 1250 450796924 450796943
    0x90d14070801050f1005130204241409031e12071406060f030c0910150c12090b0d0207170712020c01050a21060f0b03100e040f030509030a0c0f03 64
    0x2100c1c000c000d5180c0d0300070060720f4060000c1034617240400c0484244145901102c640030f10001900b514012200074003141c02b07070400220620711803002000d48030003500440030204140900d0100b0340b8002800b038450402e004e4564040a5501c0c0b2040c9400881c0407200ca01c444002440020000c180210be050500c00108690080c0c440a0401c0302c4045502c418a4240d07000201e00c5075a45451010b05400030003061600402d079440b0003403c511540d00c0050400411f0865140804000b07056460b100300b400700d0f15014540c80d090a80c40d0000b842600d8800e004150042198002d1090600b0304248070000841c4055070703909503180018400d42580120400350150340c04015071075000d0800c4400b00700035a0781e030092010f080d0440080f100d81b000743c00400e030303a62004003007a9903804802d00005403220144a80c0c0301d1403c10516840b5440c1600318001510350f44060100003900c010564280c160316043c01a100c2e0003030004a07162100b10310001d440e0b1640794800154120502a00740290b901846254 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 450799424 1250 450798174 450798181
    0x40f06031208060f0906010539120f27041401090f050412051303020d0302010501031202070f0509090c04060f08010b03011e110d14070f0c0f020105090d1407080105 72
    0x40304c0c4002c0103420340d400040540000c0c41c158840c01c020a6005262804900c540b00394149c00403040c0340900d098002040319603055030a001d0100000e44481c4007100c140751500d0040d070024000c1c0d001e0011030a0354a0314001d45c02c244054118041c04007020090f00411a011040c1c0d44501005070a200b544600b51402071711300300018080c000e10748640e0300304900c441403c030f14803c200c03002d900684e403040d003646981d540400140d0300c691400712601c0c0030354000319a55040d41406004001000040c0080d58402841040000c2400124900b12281142c050382c0b282d480d41d0415007406c0e08088201c2e030092500b000030844040c51a20b82066840340b5008108076807202d03050600300c0b940c0c0103072065228a00c990840c3c00c0f02d1180c110b82e08100a1004180c180217040d807010341940c0070b44c07680d446240b2500041100721944400000c05610240c070b48034002d03045030b44400c103526403800400707070401034001781207486500c4541d407204c40c1c258802280d40b58625849811900c92a050007100103550825011 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 450800674 1250 450799424 450799429
    0x801050a1b08060d110604050a0902310306050c04080a05280209181c031b0e1e030304120302060907050f030615030c0603040f020f0a08031206040f0603120806 70
    0x211441480084d00100040070540ca800341c0d030104404419602250410001c141511484941002404100400758450b169018054510050019241d11850048100b4141042e80118500c1202d03005500040c2b10b0319503a96000451186801c140143d104442c005003c10100051190f00b45800b200004480c10045064240d183e1203010060b6001c3c50700c10118490a0100c4851a4001801c1c3c00715402d2042d09480c0b501c4001c100c41401000c240d5603041e000552140001180913101246801401804000002070002824150021803407505002c01c2c081c41c0c07401c200300c40250001000c00c00c41102d00b480d0007551107000310340c00b075600d018400e030004a9081010044069290080103841c0035074031034003151000070001c42c80640c10311841c081d090381360b290070700114000da000c1c081c01d808904203401401001c00080c10218024a0084001c010030300020042d6480945103640c910f0444d1500d0001502070008540300521582c40d00400000b04529610003c3d0040c9003130302c4184a60361010704 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 450801924 1250 450800674 450800687
    0x2010f0e01021216170d0b0a0605030c131a040602070906081207060f020d02030f06220c0c0803010603060f060e0a0b070f050a080306040f1a0105090a0801050a1b 71
    0xc265002d83e201c61101080d00c0d0301403025200c01455034040c002c0030821510f4004500c1104103c801c00c0c50f0000403142d07180d450354001c10f83c8110b004c1e11407103040307441e0000090a034031008001606a413130204030019504803030061000202640d82c0d41c000480d1180d89580c6840c0c2c054400d400c01752299070702c00503550034075003c0c0c03100b150f126038080d1442503030f42c011080c819032281c0c00032a03200d580e83d10380d9405000184090003803046800d0b401a03d920305004c041e241014003810003449000340d42c81c00300030071046000135040207103031040110f1114041d01e4180c2d1004000b040003044040301000100c1e445034591311030030443d1034100c40792000300d5a0340c1050314401c281d41c480c0740e0029640c4c3c1d41844501c03c10002042180c0c800d00c1140000b10340c1c2d0b124942480310340d540458540c00c000090024a103028080d0b4010706515440410041c954440040c004400c8404401e050210105d042d00d11035a5070040d24000303185141c000c0c42289002c6030018000c0840603420519070320700c0821400554070408 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 450803174 1250 450801924 450801947
    0x91802120a1d0106031e050f010f020a090e061e03010b0919050f010e0c0a0c12020f060619170a0209010807060206070807050a0c05011107080304170a02060f3102010f 73
    0x10801d072021b400303408032540514180d00702591544918184001d90a10903c618401425003070401600e170400341030004c4c95003820b5840092920b0407001801316540d54030010301507001c2c03840041d6410911000c007080c0527295807001036a000b440179041000e20741c80710322429400c42c50042c08009c283d0303514070100304180b003c1c003520304200c011400240301d040380400103016510140c1084001d42103e40e41d2944084203880303542d40140c0200e07c0803200d07090b040000c9504001c0c2124079840d141360840c03038401100d04500c102500302d00b12145480b24040300380204a03200360081c00749692581c403595980d0b82e642113032041800501c90300001440f00c600c00c807480b6000c0e00307595131139519001c103218044131000c08182083d280d5550710f034599008071561600900e04940318502d40c03501ca01d080e04009401075421007901c0c04004003085801d0882e075012440941c891508007a8122680b03407101d00403040c05c00740c40042c0707032030704a0700e42c0311409015218121041072003607855081c0502c5030803003182c0300000360 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 450804424 1250 450803174 450803183
    0x30c0f06020f0604150b130c09050301060515070206041a21040c0e1b13061d09010e0a0204030807060b0f0f030d11030f030703060303090801020307091802120a1d010603 74
    0x10f8001c64005520310407115043c528403240480c03a02d5160700098140021900a000ca03a5541e18000003040d03007000c441e03030040030114000c00c003031403800300454180142e4005003800c42c140014000115900c40302910040d080b03124190038400301603201da07800c1d68021041c030418040e4442100040180100d202d40c415540304007403c1e0100d2038a11414101e4401034840e080800a8085060103600c2c1031010780140c141940000d0380325072400801501400c4010340000004a100600c414aa00c0d00089181101c5180241420903942e0080d1003009005075000103012035000502c140a026190300700e4031010100b11509117a9160120401511b10080c22503a44c15800c02a2050b0b10180035034000b4850001c9001941e24201000c0c4940e212a44216281c5004c01d41c4e0716030500515900840680103082114001c61070341c1000c403030180c800300d8070348a1100c2e607400211000000311490f80550300d00c1d4054182011040c10502240009000206503040040002d01a4101480320500515044a400c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 450805674 1250 450804424 450804433
    0x7090305070911190318051e060f1f0b0a120b010309050718112a070812090a0308070b0402041a09010515040509070513060e1f09090204030c0f06020f 66
    0x5000710100044c2c20042c90009043d51900c0500c00d5006010030041c1c0da80c4268013405858505039080ca00240041a03524006d50144040004450b07201c01d016070400b04114946e0941c50000d0400403642940e078002002440c0080b80112146400031410070425140610034000749081030700450850f0310444000c1c2c00ea0b404200300f0050307140c0e44084111750103114100820301000070100d041e0658030250051300e500c9032010880303503207071007807106a42c4282c174400140140c580762003055646c5201c80318803a0140c100c0000d0000c2d0a503500c00b0044000d503400984140c8940890030140c3c143c4504603000d0340200d040c6405000c800681c8007811a00301c4009101c03565603400e200c01d12034039860065049840317040800c00843c05a035640c040030300c2981642c1d62107030748400c1d10741c1840610400313a2104090250307071005035180303a81d00451415040d10380103004a220036070035003c0f242d5114a50041a06c980700240c0030041c8240c000424007903485200d04041804e03a18041240d80c2d01500520750311a401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 450806924 1250 450805674 450805687
    0x30606080618060a05040911031c051b03090a0803090301050709080a08030a14010e01140a150e0d06020c01091b0b09060c03130b0703180803040605070c0e07090305070911 75
    0x215203603141d000f000c0a00620481501c4001040c100d9034280020788902800c40d01983e0710740b50400c02c1d001c040b01c1d03400d90309945419049c0301400701e008030b00030005200c0c280c102d00d01001804000307849484a00810030340e0302c1030355a280141c8a17880450558000c0d42000300207600c01340150034100803916100c004100035107440e00d440850340c1014055500140d1613001100ba580c0705c00d843d070750281614040040455140c07540180600801c1203009008016640007000300c0300c0100005000300e002814508841104c041c00280750918182c4001d08441c408110100084015440036042c0c0e8851101e26242030046003242c45410034503c28040341c00720070081030805050410141c0340c00824078040703e0400311080c1003c10080740700c0d00840c801007808501c200505a00900f032034110b2088598240c101801e004400740ca070310441c01958240300c0001400000c03c00c40008000c007c1032940c07a803900c5030412030002400742c01284403e694905c00e400c2c0104840300740d889550302c01c40c00002294640030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 450808174 1250 450806924 450806959
    0xf052401210204141e190c1101051f060c05030301050609061903090314030603101a030a0b010603060f1212090305060721180b06030a210306060806 65
    0x1c0c45026240140c04004142005840e28001c81070b0305000d0410401281c41c024580004003e4002000e280d1949454144600300706038120b07110505440c55408112021515030680301c2081440d4621303801d6280c8001c1000c000c522070b83c1c4080c0005110140b0a05603035504044032000354001010b4030755041000100818a4480c000f40404407010f000c0d58106446407102505080080c021780000c0390319030001c4d41c00c0540c041c01032580b11282e00456401c504154008c02c0c0d4451807281c480c0b060540e906800321108040b5440d42d1404000282216400010340c50101d00a042c28400d05010038204003012481340815900801030310300c50b16241034410342d03035100c5842c0d116207035015005210541030080702044051100d544690ba168890007200c1072600c0d0300e1001704034128884000c062410804103201c1881041180d406070300030b04a148c664a400c1d001034101003004000a08041082104140407034186802c0f41d0350035100d0b2000c000c11076542c0415225500125800d952044103512981c5041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 450809424 1250 450808174 450808199
    0x31e03590904020a031406010e0c071104150f0308071a0108060f04150203150f220e010b0a080d030c0e0904021009082508031204021005070204090f052401 68
    0x10f000404984900365030b07465803180a13410322a00445a040000140601d04c0c0020400d07400060070805513180000b183c0300d21501d601b01301125407145031070b01031800e403000d00e80b800c000182240011540c4840e6892030f120400d5401281c08648419110210389664055014028101c0389000007805503075031480103120321400010021543c3e82c03039411101000b50007900c05540301c0c8590b04000350640d0051000c0001000101c451b1511036504425881590b40034200301719140410800013054514507030040e80c0c0508070101c0c2c996084680440005940c40001030100d050a40e2034070b040200c10009201258040b8200b000580c000300e06502007001400d026481805600d01480c0109c0f40948a101090a00681001c04038101d40c000080c400354424810f842002081400b004510f801d2400c0c1c441000302c81c0c0100064800d0340c01203903080b0300078040d6048070f822960040007004481c0c00c526105458000a4000f500e40e41b243d0310b810906402c01200c0b0300800380c94068a45100c0c2e00c3c1000409c2d41 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 450810674 1250 450809424 450809431
    0xb0a080d0804050a120827070902090103180b010513020921011803090807060810030303020f0d02040306020315030102090f040e0c03151609031e035909 67
    0x94410710344113002040490240c0c02c030400380e6655900f039504041c000c4240d41c00424a800a00d4001c11204840500000404004880c0414000b5855005810050317004000c044d04000c0041003100d200c008010000405074180c4500f2610104810704410302c1030101e025185c2c5142d00802610180d421000250440307510b070450b10400840d1031400e0061215001020f06802c07000b00e011020300b84044502440741c50301614984c40c01c504e00d80f8108188042c0c401c02e501c005414141d0014040c00d0f1803582608a503816150200b041d9902e5580c1e20700900294811107400d250007040c222090b21503d0103000711211546c0090035006014031010070403000b007c028000480300d1080d440066004d403000d00049803229681c110b000c0492400141c00c1c0204001251503c0070010400000d00004000840100001040e24904410082d4500c4d003503500c800c01047c3c45c14029941c584594400304a01c4411040c01080e00c44507031042080c00318111030b043c10302520103c51500c191816600c0c104000c44950 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 450811924 1250 450810674 450810683
    0xa08060409020d081612050a0819141906050103020f0901200a051b0d0203070312030209061c06050118030b040203011d0d030507141b070306020c0109060b0a080d0804 73
    0x4040c0e05940c41c1c1c0b60540c41107a030320180c0e50241766910203100321030707101c41000c00c0c1c10b0501d00d140c42a41c460052038680d00400e01e0007001c006441049260f41c080e070110101d110200710740c060a08121500541590031032000d200c480f0305020011031154464000d071031901e91103d1501742403d8a90300151511600200380170041450780e924002070103001c115205c031240c050750241000d11a242401070002c403003c0310b518083c1d060a003041d401030300d00150b06000c9981101ca050405031220004601900c1007100d2203034440c201007a00701c071080000c50a00c1c00000d6000081201c42c0e694001510144285070812000c100c94040c1000424046043c0c139a1003880200002101c6001e0700b060252540008038055959100c07104101d0915014402c0c140c00584074103040400840d26984040c0328440d1410030040035119030074240703a01508100790000fa561081040d525540886041e5000340903400040d2040b60510241c1308050401040c0d180607a41c40c800601001409480155003600d0083c00444 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 450813174 1250 450811924 450811939
    0x3060f060c020f1e04140403050a0513050a030308071d03120a090b04060302031006020c0d020607030c02090103080d0612020303070b040203030f030a0c0908010b010801150c14010c0201060b0a0806040902 89
    0x440c40d640d0104c1d14403502042e4201103000100341c00900003211520f84500740c1c843c10b01d205100220ba006026100e4540d9203242c260341e6810345203040d0a130040150f0049400101d440b90200c201a04035076580d10410842d41c1c1e020294040401200d03031a81d150040c0c90701604480445d0141c411141d006146480b10341c200400050b40d0342000d05441e41c4158419030020b980802071107032512001c0d44500040a4900c0105404030100380007404200400c1c2c80244070f02000111031003058000e4000741c103030540041c108009583e603402c120380f80398000740c3c1480000c0c0c03503d003012a00c10040c5100702e4409402038000e50a1440540e100d9141003001f4100f40d1b4184020f0000a580401081c0110b00c00d040943c40812200d82a41d00900355136425009069183d0500016402c0c599000110a04658040d480040341060202c0306aa400c03c1b001e80142c80103007a07401100c0e260405400040e100c0006074000c000d21380e84c0c0d440b040700500400000d400018060070109845203001e40100c4591b45c0001c2260 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 450814424 1250 450813174 450813199
    0xf03010509070e1521101508100b0306041b0804061b050405040903020309090c04090c030b1c1e030c021504050a06051c1a0406050603010f090e0102070203010c02070e0703060f060c02 80
    0x61081707501140c0b103030074400320b0700742c03e02c95002e4283d1a010810014204242c01e400c01504415052803035000321411824040b00003410f60391540c112000160040303002514050705400c0061030941d00b00c50556076a42040c070401c903414000b8840c001c0c681c0d9696116030030a4106030811000e05946034083d821884140058182c41d0303510304100d40074030428a041c0750354a14106424080d54900c958040a00d841c10581000b07a440b03042d100151f60b81c00040a1554100501e880c814684001d6140d1981524120011040541100b10016118002c0f00c0c0f86400e034605981040c024826030080309c2d08110020001c201b0f8500a001801604000880003c5941c25907020b520850311101c00604401c02130320041046030038180f00e10300203050261030302441c640c11b110b1045010916072050b006115543c941c28402228298142c42045038002c000b446441c511100096948042d802914000c0c481040402c0d0350600902c550f01c111020014000000382c90b0060598040f2000ca1041c0e0b007241e400d8000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 450815674 1250 450814424 450814477
    0x5090307050a060f0809010c0509040c14032805061c06090206030c04060f020a02030309190e01120213090308041721070207060207080a02190801020f03010509070e15 73
    0x540010f410b642d03840300c0c0d03083c810110041500c03a003d0582d0165901d000d0751900040e5018044408440080c0c4000c01d10000d03844040350280c07080005800d0040011050100410b01903040310f010b62840344104001348002400c480c11903005881c0d0b540e10024040401d01c1040482c604c00380000c1c001d58001071140b900343c012401d81c0d070080703032500c0d107581c0e00140c04c4c0a03c81d04070721144072046007031000700900c0a09a000c01d549101c2c1441481c8100b11307540100100340d4104540d0307000b505020316040340950750b685000078183d0140394120300c10352130070b403400740300303405520074a000590103a8603031806484603103885641d401001a01c41c81524200500408940403000180351401d4003070070141c42d07242c0307044003d041003031070b4114a0464000b450308102078280000d40d40c4545070111150488035050302d045800010a0742c0c80807240d5400450200641010300d00654100d8209075591455aa00c0b0801100c502d040030b0780c03950340400d43d0940c10350040c448070050005104801c117034414600341c2080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 450816924 1250 450815674 450815689
    0x1515031c18030c33020607200109050d020d0507030c022704050c0415240903140705090a091e0201050d09050a110103020a05031b0d0606030b09010f060c02010509030705 74
    0x80071440003c0c010300200c0e01090345500380d484c003030b400d071480c9901401400001c0d02c50703901030090410410180002480a440040074555035403042c00200b061980c0d80c5051900e41c421041c00101600800d0300307402d041405131040301c520383e61503075944124140a0b0b080000720138155100c41013000b028581321458036210058140580d0142c00104001c2c40207000700000c1e9140e140d2030020041e0100c40c100090038070744040c101e0340749260182c54948400c24008480e09000d5a00c00703410b05140440e00c180e0304001040100a456055416044aa0321041d00344292210030000409009072034030f2030a060b0048002c00c48030300d44145041850511705408000642d080584103071031541020351101d0400007083c02140014000707081c29402c080b000e24016000d400700901082002c2031440d500c06843c0c000c48202c0d20042c10000040081d03a03120365004008201c001600e5015480d0b00002060f140200007400044411964424009840310b90046071550001c0482d00d805100d5a0008a5155251035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 450818174 1250 450816924 450816929
    0x509090a1b020304140603091203040c081011040e060d14010f061d0106230f09030c030a020616030908030a0201020909070804120e0607051515031c18030c 68
    0x1c5900c942005040542100441e200402d56000304000c20101d02000e00c00854030908492082e16955501c0c1c0407030411080c241000b0364010004100010030900104602c242c404a40407900040e011102800c2295400a086180d8840c140020445010340452043d4000405070041d00c40341c1d120303540d02c609140c0c10008601d02d0b9441391038400e0601d00a10480e00100703002c40c0f610703010400e4500c4000e41c0310341c1801403004000c00701c0034107000815950040250b106040603100e40c0d0f211308420b45c2c20a42c1244d5620751181c06140401d6030546400500240b54a4004040b9850013003034610f02c0c0f50744c00030903404805002e1441700004007e0300a102074102191960000f6075610f030018100203200c00010010b80620108409100100d0030140f031000c100700c41d0781091708400350b2010004900340580030000305030344200f50780110f004180f281e209000e40649020640307285801740030113480d05402240f4110541c010a80c5808141c4500503e07805428503903d140246512529036610110507034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 450819424 1250 450818174 450818191
    0xb1e010605040611010216080703170c090f010809100b131e060f0e07080703092102070902040308160f0b040f020901050405010302060714030c0d0c17120103060c050909 74
    0x7141c00c02c00f031a00141d50580780744115008600c1c01000596062a1039400100034110341e20100c4c5041c10103005d000b00c103c400d1b41d907005c070b08100d1a14a4148240d07501115000c0d0007080c0451403003c840d409030308014081e500e241c0160112034040300303145000300100100c2c80d078402100d01d0281d84040341d500c99090b440c0e21000e43c00a80c4c00c61080700320161003e95100c072480100d00f000130081c204da252042170304000546004840c9486a04044000e084103c1d0f010f1324038481d110305d4215544d40d10050840d080225002d881003581d03124021000c80c0514407001c2c102c44030070000389020811005041c100c0034452410702ea82c03203484c0c0d05c484203020000c40b0100c44c20f000d03a40a14095180135042070b80100803c4400b0701007903046a001c20254001c150740180101c864030440c1c20010740030300640c1d11091101080f51000c91000a0061900c140c072001516401d842c1c8030148214003a040855801d5900b21461004a92940d0b441c0700003065845591000c12100340501c405a944010100340550100c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 450820674 1250 450819424 450819427
    0xa06200f120c07030f050f0403020a14030607021f09080c0609060a0b0f06090108060d061a01032708030c0d18050f0601050f06130504020403080c071e030b1e010605 72
    0x400280d101c89020140022040c040c0c24031420700080c0d800307403d4034540c4500b450300a459540740c2c152510280540e4100a5112100c0034010958003002941159800ea0450840f05940c40700c00003640c8851205a034003515404500f001d101c03001079a0007a000b120b2060340174500e455045d45919090800555a600c02a000602404a5200c3c1402030302c0c9480811190076425440c0c80d030009499100c0c64500c43c0c180030355140000e40d90707034a86100300300c2203400800c01d000e00d001030048500f141240c0032195001c03d00d0142c8495940f540c5d038401d001d68445441a0b015450019211901a03410003441907015800400400081c82c03454024003480420b074a03050b11510300a850030320b04240004000e00c01603482000108803a607900c018102d0801e209942040d40e4a00c0300303102c002081400d400807034029000160001c04c00004000801c045030800041e9001c4035115551040c180c01310a0300c44100d03c60485052000c2811140559005040821101e8121070110342c3d40ca03080030240c0c031110100f90b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 450821924 1250 450820674 450820687
    0x3010c03051e13141f062c01141c050a0b09010c09090e010204080a05070504180f08031503011a03010e0c01120b03071a130b0c0a06200f 60
    0x107440315807014420200c6003002c1c9602d030004000030155071110004d04811007001c2c0300160213405115050361501000310000300c007000c50304800b02508052040101d60034050b480c0c48071500c1030030b94280000000c2200d44245901e401810425060b21181199201ca1441d500070340c0c104080310000c84591162001c0c08103180c2ea0704101c560580001e004c1c08240c0d0404041d02e0f840340d80010303840c06503440450000b03010010000e18078020300590300048054810b0801c03107010300c24001581411640c040b01c09004140118801d8070342c2018440c1c0c010306031203c00444070009078210340516888041d00490741c95110740301e030020f400e592216a0042100a2050f50b04c0030f40e06081c02901a9080490000c0074000c20079400245400e02c0f82559034000c030b582e5038041e8080d40d4103121120051422040020000c10503c40305002a4854519a40c00f590b1150340080c060344810103039219011400f001e030000c181c81d5240c140181110304c1c810302c40c480d91041c110a40406240103403000d9040030608684170710 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 450823174 1250 450821924 450821941
    0xa0f231501091b080c0d020f030a200a1d0604060302030610020f1b04140c03010f090b012a0203010216051605030a080c0c031009060b010e01140a02030903010c0305 72
    0x300180c01c00c505450601c0742c0740000481d00d608401c0d10280a180a120940e50344108001501030000740c4c00d240e5000041142d200882031010314003503502c40b402002040c0284900c0b5408903440d43d009685020140f08210f80301c0d0143e500000b00302d911071034000c032940c000800940c06501c15006800400e03400b00505c03402d4140600c8440a0640328002444640784194400c0d85d02c45c06007515014040d0181c41b46030007034036580c1240b06061520150410705040a144100da180c01c24055a4200c2c40d903d90001a07030501030248441840042c2c450501840d40c0b070213030501010009040b5040c3e07a0200140c0001030301d00340300401500360f040d40000309010481c40c01904094251519420042c4c80580610070b40ea008140360700503a5018040c1f03980ca26049250f18209000d1801007039240c01018005468440a034003c8000548941c500704032241d0b02d0401921a1607209440e64000359480c00c00310417084d13011005000584a600441e400e141d5a8000a0b00351038903030304514000384d00c031000d02a190 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 450824424 1250 450823174 450823213
    0x80d020d110a0f17061c020409111207030305030708070c120e13050408030c0306011b0b0105130c020d110712080405043213080a080103150b030a0f23 66
    0x303d0203454040d4016003100700d42d00020744080c200310b110b80f14181c0480c0c008954140d42103030595010700140010101ca003000202c6c5e10454124034021801000d019030180b00200d140c0741929410f4031160b00b03540b106202141c00080062040c01030102191846011400302280401048581d81d5007074600d0128000741714aa032160843c04190b507040000744000074450740c046c1c8c1d9000c050050b0700ca4403135071480012a401d4640d0003150b90b8590303082e5418800d2054000519061324415900c10361303d0300d16004142c08407441e507160701006030400c01d407891910380f0072510b10748407987c1041100c90791a200c21181144140011049501c0d80d4000382c10412410709004e01ca60300c080084121882c128a1003032041c40031405452041a1440b800018211003c12542c10381140e802c4054141c460050450141c442da40a001c29100c822004800142c0c8001c5400703010061440500035108900c5641d0b03450014080c096422030300744d115000b004080c8841424181606d0110300e00801c109410004540020f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 450825674 1250 450824424 450824447
    0x5030708060f130609200403060906110f0c01140906040f170f22050d0602030402030703120309051b030723061603090b0306090606340308090a030c080d020d110a 71
    0x46104c405a1511b00c2c8500340507941180d42010f00460b0506a0b440c010f40100501c800080c00c0301e8011800b030400003c0b07040604330200b9488001c1001c40d1003c1d424001c1d4520481d042d5455601840c001000500e01040080c001c601ca030076980c0d00d00403031720021030f0190401c2c61001035064011404000410b10728660300102e041c0c0483d4900c4140c204000320300702c90a404009000d594000020900719102000008011a0002078401d1030880c00c050080240031060826101d6114407005e032000e45040c5458010074501c0100180007440c50320b00081c03180d120124100c42041828400803500d602c945000704030042c40c11541c55000746644c94050b0804200d03030040c6603003071824030410980391a0b4044c3c05802c040110340300d68907030842c040600f0700031861a824201c01000b881e060400c0c40208800380c4100751094a0f000c6a03580d4882c101030b511342c801040500015680708440021486100c02071450b40341101000d440c05902c000010f050b11083d034403070790a690000501131011a407161940c490f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 450826924 1250 450825674 450825701
    0xb010909110901080910050103060f2a0f020a050106170607141c0f0606030b030c0103050c070209040f120c0629040c03150b13080d05030708060f130609 67
    0x211030400c0815001d980110030702e042c180060803001c0b03541a00100b00c07038080d511400d07009001d03940c2c507403a21b50040c2c2000d2140d0305041d41052801d120f10148446200442001c561900343c2d25034100c01d08580b00c9441842140940c0540c00302500171a07000c1c0181e0010300440e400c43d1000750b812000721880c040000707210004201d2880000e1165191107000c4514640c0c0c02d170814202d125034060080d0007007203500046400c880c981180024801c0e01070300030074600f642c03c03001d0300c01c6000440019004d40b44101c3e1248854402007200c02c0051400c625403e400901503e0000c81080183da41c070010285103411410129405805c1002008810700a99210203108000d0140e440769610008648107880c1006511403515110610300a03846644104006481c400c1032040310340d50b403080b0f002c29074450f818a441901c2500008290881c0c002029060314000b5901d0b5441e550340c01800325188200600b0030b517400101011030501c15690000c5031140c1001c000c0d000a5440d1800300034808498110f0104035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 450828174 1250 450826924 450826931
    0x60e04030e010915050a20010506040e071404090501021608070521030601030e0f010609021c0204030305390105070f090510030e190f0606060c02062a0f010b010909 72
    0x800c2503034140114114a45c0c140f198960469a00595a0f03903442000031560294100105280f060150013036801441c042da0200041442c02950f952100198001c0213210800010707946000d042c154485a5068010400181446d10f48880d050a009030400f090701d1000004c039625023130100c24000c01110b01c0b0562155881581c101c2d00101c1c0a01000300424140f664a62500718414418004800c4040c60030001f08241a11003103c0c600039040036881143e400d00d44400d8220b044d03407a1084806582c0c141d26201c0c02e1420a1007414030b150103160312580c03800b041c403100a08617140c5840038031040c150b00c4000b003803500e0f0451b001802c80c8920001c1604000f603d5100b00400c0c2c40d540644191041946400306414000740070752450810000c0c2d03540101d0145090050238030100e404000c01036440b0b010280310203580c8800c120795014100c24040d600c40000c02440307410178030b07414030100480c2880001c00a450013100f000d03414095103082d480026515000e9040b0740e580d006007035202a02e074024080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 450829424 1250 450828174 450828179
    0x703170601120b240a0305010f2907060606050322021e0d020907021f050402030c0f01022505010212030f0f3c0109020a0c1203020706060e04030e0109 66
    0x24032103050400716102e141c0d910b1801114907101c0211850848807414060480801d51103d0030010340c3c46131603031400103441c010001c1010360300100c04d1409c40d581c52203102e10f044007946480c514410903180006200c40c040100000059981c01000c004240a8071502c2d103e2900030703110b148900380a1300345030b101102c43c0368800c0140d42d662000c0c400c00200b03a031860048104800410b07504101c00c078001e0744c0705807440c042140d1150f0007d8000344a035414243e08c100c00ea07100c20514140d0781c040e500258103810850a400c0182010b40e000303080400305104403038445e200b5140b46040b0311114a20340000413140c080034051560100055520100441e00281c514a0249a00000d0301000381840313540d12401c0c0c001c00c031a24200240401c4181d001c14540c2803103404d052405d80e1a203090158035100304101000021004805d00c203885124065032a40c08440700d0681d0b8648409040c80d40b00010f25500f403000c1004034095120b421301030040488955820304040c00e02134540c01014a5103070400030500000e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 450830674 1250 450829424 450829427
    0x17070c06020a350313111002100c0e060a030605030c10051207050715050907060f050316030f09080c15060333150f1002070e09031b030703170601 64
    0x3d040f03407115142c00700b40c0440c9040044528840c05110040c80020003205225001c0c0300b00707000415203482900b007042c0120b0802c062044040013050b503030b405038020380c460405200c0184c20000c401a000d140c80811400440d000501c00d800410607140040d40c0d0391010301907420100800d02d0042000c03540d8400c00c882c0303184000c10034820b0000c4107840f24160404101c11900231426a10550b610104110043e03e00c02e26050082c0300494141540b4030a5040000780c060041440094900503a42c40038519559541e0b0112001b0050300e40d2010550b0320301c080741c0b20213028428615120302c41c4280c3e6607540a11010246411903c5604603064038001040c881241d03030000740c4866154500e2441d00800c0b0314002d986043c4078a190384851248046402c010402140a08203a032045044609418070003490050080c99070446400b100947d00100091010030703c00702500e503000300300c0c1044a00e400d1199070703c411003d0214090360305561004c19040c00b015005029040c00f54401d0710f1118251030080300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 450831924 1250 450830674 450830693
    0x10e0613030e040f0c180e1905040215031602010b0a05012111070c090f0902010e0d14030c070807080102070c1a0910020f010b011d060c0a17070c06020a 67
    0x40101880300081819140fa19283c00c2104030315054101040501203007080600031010a210b242141201c104c0049070041200f040d0f14050106202d9030000e50b030000104000600001e4001d0381d122080f0b003c0301258245000085101d030700c000030350072801e41003d4000307402d441081d00c60a1180c0100001886266802000802071a01c0d0614152030a8a0010500c009100c00c0c0706880c6a08030000e031180521101c8d2107164100c500c0c1c90820400342032000625800c503202000001e0026060f0300031414580340229103004014040c80c1c810707461001180c030320351a640c00003819540c5604680c101308814181070003100000d010820013075140040b5039650112000440c014498010344070b00f82a61b4240c1c8440980781c414002a0074003456500202002e940e8103203940f10f41c440c9600307000400f2025482001c0c5004d559151415882c80c01c100c80c001c200c0c403504400c001170900d1085445400200e6000301000c000240c2484609a41b085d140c1820005240a5007185055600801243c0c00051100d803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 450833174 1250 450831924 450831961
    0x2030d050a050409060f03020a12150c0207080f070302010809120a2f0105011412060402040b0d0515090d0309080d09051e030904150e01060c03030902120609010e06 72
    0x50081d981d903803181019a06402140c0101c402d0350319103040070038040d822402d140300381c03402110764904a550303072140c1c51001135942000a00341c840541160214040e03d0300b0500c0004c03802d0040d24000360721150b105140c19004010046c80754800e0b40d0810030b65822424045e00698414043c10a184040d1020303691441846140410400c14003030740a010086003081034456250705003503000e8030700f41400712400381c41c00f800782c0c0070441440c010b01c100601e404244a050307520804d028000326a500d408003c02401d6400c0321941104501e251180018070500c503c0b80c1014a038450883d0328281001040d20780001b01c00508203151070000c0a4000ca21204240d400d1015030a0703010800c0425407034240d05250451583c00a04079001410000940022000e01800c0b10300392001c01080110800100650801d407044c00c0c034560070030006211207445890001502e500074200402c5600082d80481c0440400c0203840070160003100c1801100c103000e000720012255000000c20080c100854055000040034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 450834424 1250 450833174 450833177
    0x1030605060a0303020a030e19030b041b05030d080a02070b04202704020a030b01090e0c190315180303141e18071a1c110304060b04021903021804050402030d 69
    0x5808d0b00e019940e0a07034802800c0c04100300c8840d41c2c0d5603030f00e4a91504d1005840817600f04681c5000c1c284003080492580382140e00003070040c0181983d40100340c03403000c80604042107542d02081070300d0110f400c0d056824010ba205034403d86010303d03010200d450007426078480c1c3c1e216800d580b507507030030f014103102c0300019250b188000c1c582941c5513440005d0088210354802031681d01d0b0381c8000030f020a49580708400f000c05845c251991507180c2c00030031103416285541707070f050001c62460510204200746d24440c6d640050043c00035414400c100d200c91695003c6104800090b203a0900000c000e41c0f0a80042c0c2100c0900302181440080065410340c80b1b00060581201525060f001c0a400f9400c0001800820040441d000c9000d8040d0347c0d03001c07036480429a104100016118001d103c02c07030380700d60301c010400d2140303440c11512641c0d100c102500000c1c441c0341d40141c003400506540180400c05001880c6c841d1801139592240094a04031a142400303d540305610341b0303080201580300030030110a1820503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 450835674 1250 450834424 450834437
    0x304030215031e13140d0f11030304110303070f0f0204181703150d05070303020d11060a0f0e03030f010905090c0f04020a02010204030c15080a0624052101030605060a0303020a03 78
    0xe81e404d500c0800400e00000e40400300c204aa4050310700c0c0400c610803404100d0307803081ca1000340c2c16020f8031a00c03892036054041c2e5008000060129442c404510101580181139902d01a050340300c0d502d141451000c02e8490151a8200d0421498684075001c1d851080410040e00301100743c440352002501d0480c0030f41d4a050010000341c2525001c03d040152a0000380419090886400d1041e46d400d1580022005441640703043e54a5600681e8401c00101d040e00052202c2c0c0c0c0ca00a141d8054a0001000804a502c814075204201c50500c0034500c602e480e8000c40301e0a45c0341144050945402400c007641a40040400310825110004d10892501090302c01580e544c0400c1c004078024442c650000e001d051111002090400307840300b40700d418030002e0751140841e407a1050210211081c81c811108409003401c1e81ca08170022040e20701c1d179800c0d268144181031008448402d09881c028003900358820004900500c10032003180b00f940c0c1c1100040c0c804242690555402035a104ea032210b015041c0202c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 450836924 1250 450835674 450835681
    0x613050c1308030304020f15031f0b04061701060f0f0c02131103040b07020c280b1308070b040602030421050a03080402030f0c10050c0708030a020304030215031e 71
    0x1442012503000d1280880301e00e011a0355100a10344a07001501d0883c4120540c040000c0d4078a0440c0110004001d07c01c1d1051a50300c6890f220001d00e08040c03041c62001100500000c9c412000358040d000410a80d02e030940314040207046207421190503001b0005125000c0f42d4000d03000d60025071700b42ca010780e41c20000c1e443e200500000c3da81040420420f01c000d404d041c100f40d107150410001d940a076101e2291040f0a031140d4100b0f0703860302e054190307054000d0380300800410640c1860038000560020002741c0e02d01c0f10f480d00410405540034410a400005501000300503031501086894014901c280901d030400b81003c0c00251a44580e120320324884075045444d4412403541e00703403603601581c00021201c605941d0301d000380034400211400c0e4803902a1240c194100301c4042000c0340340810040080c03c03582501c01d41075649030840d0307100c0308072846144404504ea04041000b000302000e140c00960303e0300c1c550720410820314401d49488160080500500c10307442c0c4001410b0543d6110300c2c0021010b6607 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 450838174 1250 450836924 450836941
    0x11b08030c130f121a0108030f070204090f0c0f1a0307050a0908011425170a0e1204051914100509060a030f0e0312150117010b0c15061305 61
    0x1c100760445103c1482a4100107440c00e0010402445984108414071030b0b981c0c425801c3c9840a401d10810300a43c000700b1100c80010b00c400000d018061005100080074070744d42e102c0702c2e0407041c02401100c0404131283d05001c18030302a05080c000b01050b6602c0c02c030b01c5010350103800d403c0c0409820501400008141024282d0260700440e02401c0e50500810004504010744203c0b1031007a01c0426000b1240d4500380311904201c403048c808984203444e51a02001090b0b60601100c1e4002c0405a10981c0c8040700020810309020071406414090713002900c960904040110064100c5000c240542010108109000c1c038542c0405901c031007100d8105a6444040c0301390740318400d107812940c1c00b01c40055098901074166200203010104185c0c03c200104141855540d41c0c41001c0440c4044441c610010b403085040340c03014144060185881c0d000c06000c61007109020b4003c0e04021907000d4081034103e020003040002e140745140d4003441080d5030a141d8041040c0d0300400300b91038ad00b240c4490020708642d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 450839424 1250 450838174 450838207
    0x3070e040302120a030c0e0f010503070c140f0105040203060906060d030c0309030c0b071406060f0607050106090203010303080a0e060f060d030e030303012705040c0b1e070c05011b08030c 82
    0x803150180383e99512000c83d0401001000e5807054000030507110a088150b9041080080b140d542c41a100c182c03554940c0748094500040c2c5490484143d1070981441021803014020039904411140011905061a104040c20300800501d9008168495402c01c6202c0c1c1d14100c0042c002a01800d0a1070400d9081c102200d068001d0f400c0500f00c0302a401f8000350070000c100c000d1254034040d18a051004144d0300c00913440701c80541b00a98400300c1840f01c155a890403100030400140f086000040280d501c40d96076046c0d0f01f00b40e00c1274010441010800c0013035882c038019480601c0c0844080d002918208170100c00340400500340c5400380c16401807500c1018000c0c0b10005041d0b00050842c1d8884d80d640400352020022007440100708040c0f00800502410700c3c3c0240c40c0910340c84608401444d08181804940c2e4001418007080086228500d00024103444020034605c0c2c01040c440e0f90440c01d020001d0603040c4208030404012148030100d80101c0d0707032441500d42103c1200030b810355a1a5031001110325 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 450840674 1250 450839424 450839443
    0xf09062203051b011b09171c0e1f020c040504050309060f0c010e01090c0b0405090a020a0e0a0e060102070803190c261b060601120c0c050f0303070e27040c090213030b090c03070e040302 81
    0x4007004101d0048507841c1801d00ca18031035216400ca038400cd01c00e500b4041a0f43d403c3e14014a00da00c02c2c80a820146020005088010902d00866080510324103000d400d440c40c40c0b110800a95560b5840720074004034500000103025000c1d0086e16292400c0d000c69201400200b405010550100b225403869108803040c9610710307c024000465a0b850700342c214100003081e5a440d01600c2800ba000600001c00302c1510000c40003d0711882203540c80c80e00035540382d45018021644051800145110039200e030305205032154540000300c0d200c5150350750b44a00700e204921031102d10f0340400b0401c516682e100c200e44507000e040300d8000c28407480c2c070602070310b5045c540e030402401400340209011000c1800800355110381895034176075000006501c140000441198901020441780714180804030584100322904a445000c15144070341d5200c004600700c0e00091806240001454810400d1024029115400c90500805404d04048960010b552610607101d19000d42d004000050180750090061880 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 450841924 1250 450840674 450840679
    0x203060409150507020f07231f0503090c222004081501092f04171c0807090e0a020c03030f09062203051b011b09171c0e 53
    0x150380c10b8000c0d02c00c02800d000c50b00d0000510400658a40c81c0c500090b04d41c04803000b9004402c103407140101600c2c55408101c1e40d581c0c21014101c020b001206c03d80b450000e9108040da522501d9003418a4032900b1b06a041c03901c1c07440307649107a00201d10001c401842d40084400c0610001d01126003400d4405110203421209245a10208001843c1381c400300340c49882c00d05000d880d000b1a80c83e81c0c40c0b03030112160125000d551003c02c5815006800e0310106410780c1da80c80c0510781c1d003080e03540c00b40c490f0700041e2140c210301290000404035003047c8100e160181c40f40918140705071149410040100b018125203c0c80d60307800740c0b11021031030800c0254102e6003441030810a4988e02c1c90b000708816415441610010001d2203148001a18150745010214282c0c0d403511016156142d262003c40c0c26800c80c0d03c40010190124a00a00b0198240b04640407111a5030100590541d001005003c494199000030300601e51200202201d18012400031000a401c4143c103d4101c1c2c80c00d41100c0000005252a4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 450843174 1250 450841924 450841943
    0xb0a0c05160609140114090105040c060503180d11010515010f0c0318120507170a0201050705150414010e0a05100c090b070b0109110a091a16080d050c19030203060409 73
    0x556480046d000700201e803510584295a81d1078003a9003038206c1c3da04980c06402e9510310721003401118030860045821443c20802820b422141c0001d65091503201c00283d00031810340321600341e0490b402c2c01400e5000306404000c401c0400d60b400007810400d00c09034104104100780340d06808050080c04084501042c107044000000d0b104d046240115039440b105139280d20620303500140708030040501684800b549000303055850074503401990030340c10406085034607000d4850515140c0d505001540d104601581d49100d42d43c46a000c0380c0c0c00c403115054a403200c2e070801c10306000482c40006402000080003140000c0f0070401c02021600034220f41c01c030841c120030015806090003000000d46040e030f40c0c81c00040260074400c084c1a01c3c0c51103180c0c1014045059110f00b0441a88003144900286005074030b914a0046107614007040d03908d4100302280c03885000300340c542d6040403a1280543c0410004a6076180018a500082d07001c138090781c0d103400305500040004c0440d00c0d80d400086626503c00c840700d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 450844424 1250 450843174 450843203
    0xe060d050a0204210807020904061d1c03111c0e12071a0424110703021b06070305071106041a0d0c0513090f0e06070801030b0a0c05160609 61
    0x12070180d40548151442072000c00c60101c01c02c20209646030340c59074000c0107185000416401e04c001044000c0040da03d107546c0340c00310308000340c1302d0341e140805c0c00b106e00c0034090000da0140c051000d0342d0009100000c06240140005024080004840b0804000c6038042e4898481d03058540250041032501580c070f004910f41c20030402c1801014040180c41030320050180a6110360008110004480140c1303500720b804039032102503036241c011000310448044082030400640d000c841e49544a003074201e0069222a0801403044039201c2100d40e035103c00c440d190f1074200141c80007052070040c661702401c13014102580100d5641e03010200e5004110071002c1c1845510406a03110441d008581d441095a0500d9050b1007694410350442c2c5640d10562000490141058403c80c0207050071141095410396074503c09568000800809120f00385560b913041a0f581503142100c0c40040142c1140c0300642001e40c228140d580083c10303a400da0782450191605c0b49070078101000900580300c006413400b885100ea1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 450845674 1250 450844424 450844441
    0xf170a061b091a040902070501061a0d0e07030f1407030c0303030f050603060907090b0a090f0b1203090603070305061c0501060f0f2412141519060e060d05 68
    0x20004074541e900c80c2d449865580100f80b107000c12140b82c1c1c0d00800c80c104014004040940d001d880700a00a6000161103a203404170814412141c00100440c0240892241d00b032907040c0c02982000c00343d40c2d0140001e28503580e50810383c0015a80003d1028102018003409804200080301c000d540100903403440d96500d04000d8000e0101081004030141804000760785410300290f07450090752444020b2130446e145c19400c3c002000503195956102260b0303200090044d01030b00802c0c3e0320407200380780022303003000303000030010a03109013041d003a410381040c8600c1c0701c6a50f822044d02c1d1b000486003804141d681d00e80300040c80c003160900c4040c41d41c10350341e006003083c00815400f1806881d003802c1104030040e100c1c0300101c00f100940c03040c2000590f840001c580c02c07050030140842d118885040141261404000c0107080e507c4860022007450f034800100681140140002c070352581d020b0301c880034506a29481070b4400724860088806006101c010f241907600c80b1012142e440b90401d10030800c50400c3c448 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 450846924 1250 450845674 450845711
    0x60c030f210108011b03051b1b06010e010b041a1210090e030405030a1b030206070f060b060702030303070309140d080114151c02040b070305070c080303010f170a06 72
    0x3540c070100c00e040002250340001481a000f000003000841880c5241c012021009802c0c0208103203140c9003800f9914102c0c03c0c0c0c140c05800c10380404010316559502d031045d181e1400505034080000381848000400200c260032003141c0c1560f03255070a50304800406c0d0350703002c05031159440a180300314550003005001401030a6100035516024400d04c034110055403e2030f80c2e40030714041c540c0c0c0754101c80c0d1218001440b406043d140c0801031030a1403021035a0740c000070056000850705640304400d51600a041183c50b10400c1d03240d00040303d18608142c202c2c3c000ca5a41d01000309440b051540c1c40c0501014850180600800d1240900840b80c0e12072520308002c1a0035820301c174003640c1d0100240c0401f860701c0c294181d0500d1408840020707042c95550b900c1341e510408418841407095500304000f00d82e60300841d004108850107610303000d940b41c0342c91801d050540d08903800f00050750810b2005004046904110b013045500b0944c00300c144c1c0c00e1008400c0d0405000c00c0e00104442c1c6880014007403506041c8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 450848174 1250 450846924 450846967
    0x6030c07031b0809130605060d0b0d0c0305101b0e01050a021005150306090a0837030615031406011d03031801080c0c0c06072303031503010e0c060c030f 67
    0x554400c0042c01740d251540948025014490f4841300c18007494445c65180e40c0003141d40d60004018086075011501c0711140d89100d6001070b54a50024100c180e5141c1c007500921041604044103505201200d88004014481c8000541d042000000310b8843c10b80c42003003500e9502c0100c0c0000c00c0181401b4981c1c02d422006040210f002c0d00408000075001c040120302441583e421200700ca00e0f00f4031084107002d0250b0501a8100500503485d105484180d40800c1224040007a807000115241400c000604840c8401901000c050606240e0039050f00310b0301c038460f0000c2007070800d680c00064015003844c041010003402e80d098400410301d8070107242c0c07454416849880a8a0301e11076512580c10800480c400d0224411070382d402000c00074150b042080041203460300030f000841440144448089a403001e11580350f045500100c1071009241c2c821149142c1820200e008012805e400208683c40d01c090301405840f0f03c00c08654410942d00c28422601106003190b90117664441411000b40d4200900 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 450849424 1250 450848174 450848179
    0x7180f080c09060a0509060d0f0501020a080603030712030e10021309230103080a2c011202070c290304080d0b0d0312050727050907020c06030c07031b0809 68
    0xa071030a8203a0428400c654001c80001d881802c0c00b9051105010010001a10700c98124140605890100340d840d43d1400c0b000744100009039440301c4180d002401c503007000d0421442038008009400c006000420b102c54030045900f004101c038100450b2007404c05180c006104c0480b400081d40c0c0d01d034000d84561000944125940c1005400f101154403907000b50443c2c1c40140c01d000100050020030410009001d4075041c40c6020205405100c00031f4402c000560100061708500080010a560b0440407107846400c244004500701101a200c1d202d4841c050321480e00300c1c02207081c0d01403441c209e0160304c1101c1a0640364003075903400c0501e03081d800c59120240c1c401d0303000c1c40c1041031001d40c5070054a40d98260b815541e000100391403404948010706000d004a01840042130720440ba40050f903948001070406074082031005840c000a006403d100108144115002480071141c95541c480075650060700040c52140c0f5207595140a96140070802104880007907010011005c1041007402001070a809 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 450850674 1250 450849424 450849433
    0x2120c010906270f020d02132901230c010c1e0207050a03020f0a0302040501060309060b090601020703030f021213090b01080f0c1c0f020310060c020109030b07180f08 73
    0x5603851184410214406003c40d0b59140d0340c14010800700b004c00901140006c1440e01d40121a40c0019a00303400050621601902d4107444011040000001d00700560044462074030f1010003c0020301c0350840d030060030000140b054420311841c0b0810256202d440c0d046000b00198440442c02070145402122280c130800040305901009606c0800c40400301d60020b4402c10009082d40c1c2041040c1513007403121a0041c400780b4002000d641c460150900801c100e8400068620369030504100303030b45054261500440307a0009001c2aa64009481e90480e501458030910104500700d0803428901c58a02c26a0b5491000c00c0120201c0c0907010000d08942d044002000b02c411a00019102c0c10720440c0c0424140c0106c80000c1c01400700000181152040b020440002d079030f51070501405c5038a480e00d081070290b408010052544804181040a00a030303040c121a03064407940002c0c2a50198000103219040d201c1c00708552a003d044000790b60824500112a01d039100d49220808207620321445045114 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 450851924 1250 450850674 450850691
    0x1f02010f05270a02150c010b030a111503130b0c0c03040305010c08091507121503050a0c05061206190e04150623360a050a050f04020409020102120c010906 68
    0x140021850141603002d843d40085a030b1000003001700d0b40100024001c0e41d500c4410b070075003d6a01788658003486124211021021407000144014403500a00070a5121420414041111080f05100141503800000d400c0031b40d454420000c102c1c0540d0b087c0d000a880045800300801c60f06401c03400e400c250903903030255a41d80744150310740c2c2c5064441d07080007411101c0000c581014402c401e860391000d0307903d801203002c905102c0c408280c60724903801a84d0581040c13222404000b9418941c500425080310410b0a10329000c0c02802b102c0e1001d01518032441e47d4441401004d070082200f90000c00009034008400d180c2428803082e0172400c50303442c1020624103400852071174041e110311080b0440c003e07032074420300d180c007002d0004440d40e81c1c550080086c080d01100c0d21003c0148220500c0705034030310441c240c0741010344a40f401c0d103030040d11004005040c14104802080c0340f07401164010b070102d80110b02c1d6903860006034200030101768902c3c000030000901004a200542145070002d00c40c240410401c079 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 450853174 1250 450851924 450852001
    0x21c060b0108060f010c03031a0a0b0903010e030405030d08071803080c01050c0313020607060e01020a05071202030f0f1b0d030902090f01030b041b0f120b060f1f02010f05 75
    0xa13201c00c026021411400080780400d02c00d03071010140503408030100e035542c4190700004908050580c4644075500c000500c0c54034a05081c000c0c03004d2a03050200460a03c3c0c20710000a84841d130a0622a0400040500085001d0b01c11801e43e01c5400c0400f41c41d00b04180c40b41040010340e0b2202091003895801d0002280c0d0000d008400c9038400c0344000002c510b560302640c00c010256101e034005490041d2148003500800c4002c1c8000e056842060f200d46903a400300380340401d80d1032030f90078010b41950011700c6803120385d80b0b00d4021910301e2078035019030030f645a900f0803e0200d01d1090072a000e41511039142041c4015815070f004400303490086850201c5580e9070094205c40081c2400010a01413001001c2030010b4076182c1c5079900b861a114800058584907801c006842403194080410980750062100030b21000049690b0021400d0303030b0140c4503200480118805c0d4007171412801110002c80c0c0c0c0b101d400c5100398002c103801c10142d1401d000300d060880807080b80019904441410041c192100725048 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 450854424 1250 450853174 450853189
    0xc12150503120c03070b0a09170a120b01110609030a030b060408070608041a0702070302010908010e060c0a0903020d0c0302040c080702060c1b031605060c0705030405040207021c060b010806 83
    0x4510090040c18600e01031082c0c0304058105060310100f520051105800040000c02164407610314402c0000e8041c42e542041c0c14409464010920449010850410902ea01c08607684000c220144040350341c440c910300403144007401e0100501e440c0141d500380b02d403150001c8011b091410455805101100070142008190b1103030380701d0094180d000c0d8100704a07040c0100c10b21580b060051030b4520705001003e00000e50041d084075120016002158248119a08001c1000260a40e80d008001c0300c0042a21940d0702d4402415035456120081001484c0a03c21a4070602440d0b0240400418800602d4001c04003511f5000407072049082003955034120f803150520b2407190045a000300844e4840c002c1c40c62040d4044200e0b40c61840d40c05403002403960301000180440c01c204a440720b8441028200b5a0402601400340b400d00c403c100598000310f1000001e0f01e0a07281d0488006075a03441034400903104c03000e4600320002940b0501a0003060000c998824040154280c07244020781d0348841c10040706 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 450855674 1250 450854424 450854429
    0xc0f02010605010507060f1404050715030501230411040b130e040803010b0705030f030106080708010e011d15040e1509011e02070f06180203010e0604030503011703040302040c1215 79
    0x144d0600040010502d290002c4409a060303140014403841d44403200240143c044400351505e0380318440402040c182c4010590010200c2d15003004154100610940c2d400c400c00780740041c0382610030300344074290f8480d03000e007070600070b4424003aa07100c1e66520728410f1a04500c20000b03c0e4442c1240000d89200403448940c850b40d4070640d030a00d182c0c2451551251a00400825a5a0b100601001006001c09002140039083d680c884003a1803801c0b80c001840e03124141c002d60800f07666200108418a030800c6c25114003200f5403507902240d91640e941c5641c0800b10741200f6030140c104010303050b403c0e07008100c101c817510042c0522201d40c1d84004030103090b1014401280c807091082545082550220750190803e544552040b404007600344e2a04800e640035a40c075096194001500c1c00c003107140900c03c0d0081c14082d000a030201c0e1030035032000b4040b40014811440381100304050107041401c20320854002d95402801000b00f0041183c0c000c00a03404c04502c480300a10f005100c02210309401414400c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 450856924 1250 450855674 450855677
    0x40e030f0304080c0607080402091609090b04150308090306070e010207120812040605010f1202060f25050114010b19030c05070b0f0912030c040302010315090509010c0f0201060501 79
    0x600040328002109aa10003041691004400e1284001c00c140600510f400345039941e50360401420180100411240040c000d0000e20001d07000041031a40c01c010540122a1030030310011305c0d62103c1000c80e010b03041003100304c40c081c40c0911022080004480103042c2c1d4550513412291107a455040980b2004107510304640540c3c0103c800708405080703034054a5280784a004078504143d8401d085800d80d60095400300d6149458a00611150081845a10091050021040500030f1680100e0f00d2445180c003807298540c0001100e0240000a9a10900d028503103941c07030b1694886170504030f0080039498207007101d10124000004e511700185054038908a10350f44e045881c01c074a030b44c2c00e9005100810640c1c3c2880b4090100001047c03003441d04030305c503900e0034000042c03e01d80301401e6070034410541c5c1020031010040c070a22140c03403194400d5500b40d0b0340c20f013400541d0310b2400f8052501c10034240d00282d401d0341083c00b0401050b07010b40150030006241d85480d9400c44000314264245d80b0540120303030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 450858174 1250 450856924 450856927
    0xf030a0215040c03050607021b030c09060f03190b1e0705031303031b02010f0b06030403050d0b0105040b180f01020304052d100f0801061b0b04020339040e03 69
    0xc0181c0840c1480c0c0180c85124a90401036496440f1402d1060842c1c48002582080042260800d90f0003410300d9000c20071001782880048040001e04000405807105010310305110101c1090b0704d0030040500710701710001c006c1c406201a0300d040b107080e5008450685c000640a50a03050909048100750301a01c1c1d5615000e003541d0b59511000c01d0100c0d000c0c0d042d0308150f20b52403141000e070368000d07107548a0352641c0e001280e131001c6201110246c5442c1d50000380101e400300704200100e41d20000341e42c2c080c21ba080010450030b4000c001282c1e240960f8104400041c400150b451661451034a10400160103403481001e036030140303005907120f00452051640081040e100065049000001c9146220a07400440036140c404008100950080b904140100703480f00d10180ba8160440fa00e24010603251900346620b106685010203110104203004020364030790400b11f03045580038490b41820002082900082002100340300304081250403100008000902060605042500800803100070003801103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 450859424 1250 450858174 450858193
    0x603121103030c030a23070f141801110f070b19090305060c070f0803012c010506070305091c080a1205090303270d030506100e030a02040b01030b0901090e0f030a02 72
    0x2002c0d01150340180c07421904c05652414446c1d14265450140d040d5039202020780b0a1424040c01070b40000950b403400c1c1c0e8080c0040c180c2562440d8550084003800c2c40e0800600d075041004507e46580d40fa14244240202d80e4045000000100070b404c07448041e007100f19410040c40b0003611015507500010303206400c0540065400c3c07001500410000d4032030f00c00c1e0751200d5100e490b504807075002a00242c030400300c080d00b200d91003038615901d803c1c04880c00090200c9035141c80c000030f04034818140c1c020f050000c04580c000581d43d914941a020591081e2036501360502440c0900300f0307074060482d0002160503441801c0840c1074030300c186441805180003e61030f6403100031110100c0407504180b0700c0070403c005501c14080f4002c2c4a5941400704503100450141055401c0101345c0800d50104400c026081d406408103581c00140340f4800f90b015500024200c0021004034003400620344416080303d0054000107030700007145c0c0080701000102094410443d0080c0354192207200c1c802c0540b0042e4401c4c082c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 450860674 1250 450859424 450859441
    0x905061c020c12030a0c09080625140316090f1406091c0b0f0c0712031a03070b0c06010e16030b03010225020f0102060907060503090a060603121103030c03 68
    0x900b40454448100d0340300002404000d034107a030003103801100c0503480300116120150820030000203000c035040030f4166440c0401c00400801c04464403051424494103130a2401801204d849420450144a4641d42d103854001c083c91030a0b20f1802c10001a22054001450b0080031810300a0318020138120300304441c58010004290013441c0043d41c0020403000c0d10900f07054410259200512490810710701e0310b003409042400740d90050a105000d03001b08803107000a508072000d1748408406041c0040c2107440203685002c0c50488a5005415210740c07000820500b41040141181c1000241103179010b81c0c035252405540c003404c0d1407056014405281c6401254065000a9090f0f10b01400060a055100c1899480f50340051203c0311501065a42d0006604140840b80c0610313000380000e10312410441000c0e540c81c0d4803889074004100d4040045400454144800a1100e030418002d00035a61241882911070150007040004120038810900b04500c020064134410015240945d0441e501c42c0e10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 450861924 1250 450860674 450860677
    0x609080304051e06161703011421030c1605062d1303210305040503030112050708030c010606120915050601111203070e01020708071505280905061c02 66
    0xe0340070150804240c03c4841e51241c80140c4000d0046043c4c4130503c0e0034505100c02032560301810f0402205080005105942c1c6c87c08081d9840b0300d06886611518403007c80b96547c0040003180f0101600000504078030001000596102031030441e00340c0c60800d590755003044014482c14070040d502c0c20082011089400500c1c0304c240f514442d4010030b030318040040022040c4028640c000f147c0008001c004100c0c0042100c2859800d900d035418204690300302612081c3d500d0105210f07521108405c518807404004050010b1001030100204403500e810080c600c55020b030050703000c0c90340010b140400355400d41c0140e004074580280c000d40b08074100d82ca143c51881c060030004000505100005800315907100040180130b0f0703101a08032410351207040c9590001c002c640f40407101030466020403410b218081d400b041807401c5600c86e182070902202000b0055030320340208551280c0001660003400079086010508c07108a401503600e01c992141c4410403c000c500400c0c20404440c04060b0689801121550 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 450863174 1250 450861924 450861949
    0x14120a030b030a0c15090f06021f0216110d0803090a031107060807050f070f11030c010c0b01211b0305060a0507170619080c04050906040519061503031701060908030405 74
    0x50550500b1f511151803106161556116000580c8503c40d6180380d09180a04808081d260710030543c504694110040014840030320054401c0805400f4046583d4403c40160100741e4400f806580324689100119114045000e0940100e0302484410041e4140461001e054810544a20f10a521080002c844507005100a000040e5040004101045203200c05013486407082d21032001000060044c0b5061403400c1143ca81400f800c4403024000403020040341d030641d200d00200c554016001e14060000114581001e440c059088005c00b044291500d003d409690041c41212015107500002c0e204079101254000c001502505240000484800c04250818001094441d00c0c4644a00208004060368032041c020303403101e4001c01e9141014001d160f402a000342c040c101c0f80c503040e140d460305c80b1000c10303070305100d10503820240003004010f82c0041d1980c0d1102c2002c043c0d554482c41c0243c040d945154103c0400d01006000246a51081340d40005840b0b0031005142824075000074010a40c0c1e140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 450864424 1250 450863174 450863177
    0x2160803040c0e011203120507020a030e030c0913030e030a03050301060c0c051e01080c1e0706020409020f03070e09010f120204091401230403170414120a030b030a0c15 74
    0x100b00020071010302c0410710702030902ea50700c8100405180c60301034034450340c0982caa0401c81c207100c10820f8094001c542804019054208070103602041c00001e400e1411450362513600003140c805000d5140205881301d038182d4429154214041212810942d50718010035000700000c4013040180021481a10b0341c6840510600014950030345500c0010655106102040000ca0000030700e08459030340110050b40101e812003245c0c0c5008003000160081c060510108481140b0008014041204c15812034004005c03a40c0c9c00c545481080c007023047d15610075180350380048c2c0c16020040d06490841540c40c129090500606041c911f04110001c6e4030303111003c10380e0701c07a42d1180301002084180c190a1760303440d0303400000a2140c60340b50740c01100010401080d41446047c6003000006a04031810703100f0340d1642c4410b49000d0f038031890042e0207100d440b202e8922501840d529070410444001c080e1a5030351154805204002c0c05100b8160351b05009580902071070080c0504110f0300d01d03440c5003002010b415 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 450865674 1250 450864424 450864443
    0x902161e0b0901020a0f051c11070c0b031e15150903070e0106020d0c0327050d0b010906090903350903041a040e06010e0a051905130216080304 63
    0x9807101e1003206811942100a40d40001d0660b00301c40d88070b10501c018142c2c608055051401820303a404c05c841302c605e10740030041d648907a03404915010006503030856900400c1d466000e038a422003000307160825101d0031000c2020140c031840280600b0720452040d100003c1840e182d941010410664031f42129000b52009405c105508c0710741c0b41806081d02906088040b00100d5251080c001d00d480c43e0300034a9010003045440030000039500191241c2d103840d08035104a03059180c240280c5000006a200c10b51109020344c030340701001005018203041300d4800800b0001142e0f1010388030161868203c0083c00100d060b24401c0d80180050a101121902036070016003a40d00240c07280600c0c20107550b44c4d1416400030404200c00d114502a031840c082c100b805031414540b600d18210420342c2e002c0c2900d414400300f101d0904035900d41480c40d10090034018920b401140c103858440580059501945015005602c0b241310038889600888218102810318035404602c04d4540e0481c1c2c0d040030384211039841c60b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 450866924 1250 450865674 450865733
    0x1f0305100b0414090603010c021b01020316060c11010e120f1201030b0906090102040f061b080313050f0f03070201120b0d081206010c0201050a032309010c09090216 72
    0x306002074000b0b085141036480980104408000c5144c4000b4a2607201344e040041d1203001d1030b40800c1c001c1d0341e030400885101e41d9010480040c1e0448c0200e0310307001c02c2100940e03105020b107c002d0b0046004c50083da00c407161600d003203581ca6400d0b901660030200003940f200741011420b50002000308046071000ca8814148400a100b5058002d070a0f8415a0705407881c205024590340140401c9030007010200c0210f24151a02a00842511040c8035640501840d84070007040030b00d0b680d1102001d00d900200082d41e03480c1c440e101c00c03080c0d030700c0c400203a80d00c1c415424102171900c00010241c5080303c0f00002142029000d5004450081d151002c4016442d11002c02000d203440303611140303c030a44a1131050303460344031416101340c0652006190b03604100c8510b09c0900941d803c9022600650350078900800c080301000c8000c4c509240b0204400030000c8184104003003000194421441c0991a65a41159503500c04020050307004440070f0300c00c4544c00ea6410383c0050321f11007520441c5001194941e2180b003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 450868174 1250 450866924 450866939
    0x1d010c0602071101080a0207021507140109031e05030c120403050c1903080a02090901031502070b10060906021c0c1a040b04020406060c0312050a090212030c010501051f030510 77
    0x8114240440f03000e650074900300c1c010341e0050f142e503500c80100c90381141445190b40004021500030700c2d800d0040070780020004248030b280b00c001556803107035400038421168240340041586051408030b52145081ca81d2a94440380f180703040341d004060f440340580c24552604003401c564130014004400b4132004002c080d9500c1002d0040c92600c40d030300000d42c03c604009082c0680795820050081d010716104010100300d65542c40c61281c10340340c00090880b001d0a0114030f82c4000d10a1160182150b00084200a4042ca580388558142c4501e0380c1d031461519502ca4040e40c3c1c80320342d1b0400511100200403410071491141418828403801810921005c4503005d40700481004251829103200415a0400040d03080c01d000b1400100182d1802400617550341d02d00502c2c8031744d07510700c1850032500d0f0000700e8404440703078100d50300d210380081918a036880c020001c181d880d8444403554040307500340400080c8500c2c2c40007905141007010f562401c005014820b0460040c64000d01500c00043c0020780800e149 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 450869424 1250 450868174 450868177
    0x405040b0a0f08061b040e13170c0105060f030601120b07050d0507080603011b021504050f030a05070506010503070338090714240a05090927060402011d010c0602 71
    0x202607a4014020608004c1043c20040000e02e610300611170080208006501126811962002080e00000310f0441c032490150540b51080c00140c2c2e00140c04500c01c1b02c2d180042d8040c6010b0f0204513003c0c200b40550005042d140c0c00300744200d0340401d0700710410502140c03001c281036500408520745546040410703c480000c8030300944500c00010f103000204152410248100c1341c40c00740e0701d40382000d010354a01c002540e958904c58595006403200001c0740c10040304111074100c00d49410240c07901e60303e0400c0c004003941c204034801c1e40c4510448000280500303000c59042e054a070003c030444078112010000d0072000a44242d00c2c540c0f00a00301c1c04025100f901043c05000e045040c1c00342440a140142d40c0d90b9200f00c07126540c0c41100c0c202001100c4000c1240d2000840f070362034144c19207401e00c01c1019602402140c2182e5000b54103001003010705c80810b080003103041000031310310900f9044981d6041c2c2e12030080b60024081005282c1207913003807092900128201c001490516103007240c0e99111000e9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 450870674 1250 450869424 450869429
    0x80c0f030a021225031a0f130609080703020c091326190206010513023c0409050406061211090a110c0601060e091506070201140c100507030b03030405040b0a0f 70
    0x80304c096140a10400c01c0038040741c800b081174003840740e001e0b06000c0840b09404201906038031031105d12a07a2841000780a03044480000d0b04482e100d52500d0310741c100a0b49401c00701e15190301c03a1180c00000b0b40e040b4480050f422301d190700141c200881005510591307080700d0540ba120f0300c0b00c04041c403155103451444502101c0d148400d43c00781000e5454101440040f406800310750045d40e00500070100e605401016400405a8403405003108110b90003203000d0804441d0003400d01c0541c00100440d031032000e40c110301d000e148641c0d010007090707559032100b241d6840c0c0050014840b040c2c940814615143c0805010f42040c0350420000312071742143c8040341d5a0f805030b031052245800080040040310342021001503001c2003911040340c17034509142c1c0c0403400d4034a4400e6910801001c90003800f5a44034071912102500130b10407056036101c844141c159554080d05110305907600389170020f03130118420300407442c42403005002141050304100411014140c40e9040603009442c0c408001506210354519100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 450871924 1250 450870674 450870733
    0xf03140a09110a05010e2416020f040501150305090316060b10020606060304060e2e050c0a0903080705010207020612011a030105060a0e040f0e07080c0f030a0212 71
    0x1481140340c0307800500b01840200301441800c07100d4080200341d030010343d1100381e0f04048130b0f03105100c40b0024981d8215150101e40f002840b1010441c1e610702611006100c001e00e00846e640100b40201c481000250b400c24003d503101b81d5510065020018000e42000350411004020f80f8201050b0045059201c8804034007605c05030740313950030450641404e52030341550081900c05010140b40100200b030984c4409400100401e0b6039036070003120302c00300740b001d40d88aa89080c4190701d55050340b504030b0158030340c115101c00d070b01e4508000304082c0c515800486c1c2854400e40c4849070814030395200c0b08502d4210840958095400304440c1d0f00503940c0000074400c45008010100c06035041c1002c4981c0d040800e542400440e03003c10060109654400554a520107103141009651040c81d01050180034945004401b1900b01a501c0c081c504022440800307454810048804840e524800c01c8140035484110540640081100b0070150502c00c42621511200b04201d0714454410034801c0c641c10b100000480 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 450873174 1250 450871924 450871931
    0x60510021614010807080702030903070e010801151a09010e030102040e100b0301180207140607230f0406050f130e0a140412031505090a0209090105030d0f0f03140a 72
    0x11450150607607900262000034600014002c500c2d0000e00103000c098205800e00065500146495108100300c502504021341a214038541ea0104a805804c00b0f0050000b25401c090f0f03040301e032000c0012500110b401090480710105046640740069038003004500c1d04011501c2001400c0d0307102400200014118000c42150525103c0c6060f0780b0580e640c1c1180405203c00c10042182601c10401c00b540301080050043e034070702c01850290308110f00d60b000d4101ca809034800f0040c1c80c80d04200700401c60109101d004030044408000c5d80c12a05c03511604100d100c005010a00840e48130710040d10280c0b6420702c200385004c10603070a0b130304800803692101d40f503958018100042d0500d140030f1081880c008119a013914141980c941491604004003c000c040d61072403071703035225030701d04200070003c1501510a920600303180301c1601c0607601c08000d59002d401d60748c0001480303040001e80f0040380b00c080e07070b6092141503c008003114050301d610b28440c2010b45510b04016600c4241050b40c0c081c005200001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 450874424 1250 450873174 450873193
    0x5060307050d0e0a02040b09010617190c0e0f1c060213080a150605010c08070219120f021002210d060302060a030b010909020c0c2803050604050c030a0305040e0a06051002 75
    0x2038500c1440588d01811000004128071034116001c1c60345050403c1e5080c01595900b031000301550400311030420a1030410756085485034010b10002154041600d40c40d21038041ea40c288101c0310407651000a111300952248008101c481c0c2c0074002c0e01c1c0b150500c030145540d0f68810180380a43d604400c0c0c03450301b4144121040c240c007500c62070b03004000a0810401401c0540c590b00010b00440501034051180c1528540803082c4e59420540580000410034480300518108002c0034001b5503022401050400c040c284079a00024041c182480540c3c03018401c0450075200e002607420410341c404e5034503140c010100050780d0700301c003030100c4241e296130020b0340d100140001421030340d0550155246034410881e0444040c00800c1c402e0307010301c068032403107800c003200030540074494200c00003585006020784011041200210300d45010ba80103508851140070307007504168540241c42c0005010400400c41008824200b0041e0b50b48443c1324000003800c2551500801c505841c5e001200c00140c1012108 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 450875674 1250 450874424 450874429
    0x905030316083649110f0d1d04060803090409030e0603010b0405030706020303090d030b300d1403060931061107050705060307050d0e0a02 61
    0x100070800c480d14161815007003c1900d00740e2508a9400e6204412643c2140300100f40700d40c0410f01d080010700c1c120340c144040c0440640c070901803038035030000e4160400ea9030000c0c3d0300042a80088400c028060720030b000d00064040e10a03000e0510750000c1c80c040c0c10320156840c4d1052148584001c4181c903034017030240521b498092043c050500c8603200b94904081444002800002c2e19212001560005080000750030306854451b80b82c0d0080f035100784004004600358544001400484000790116003006450380c106989a00040300c01c1000b0f9445011024421407094022030040701c0050009040301d64151454854401d4803403480030084200c240c451200c601c10458640c802e0480d1410b60f11403041c50103010751602c00a4626413140c00c854010882140c50001561400310f15050942c6103806a000010003d400c062010723146030b407904403648000d0007070a0803150b540e84c0c0701c40585101c0d410042048090340000d006001089014846100782c540c541c45111241d403c004020554807078941704 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 450876924 1250 450875674 450875701
    0xe030a050d0807111501030602030c0903010e0c0913030c020402070c050d03030e0615090f10050303040e0403140306330705160602121207050d06060c1407050f0105030a06030609050303 81
    0x204c0d032100d94420b840c846002c0001c2d120031410f4a60000d005a07407522200004030550180c0440b0740da15519006519591803400640040c0c80e0a0075942c1c41031b039a03201141c070300c6450886c0c00007a0100f140019205c0042c0307425402400a144a140200c079056282c102103140c41c03056140880102c0e5441281031819403007004025484445884401c041e00490008140030401c064444011070380d01034085030071044450351590240c040601180d0f2280d64400d1000c52054050f101500402d61550101e5034900c0010100c1703200d00c8019114a526001c0e04481400e4044a4001c0c5068071021102200c1d90001c240010014035003d04020030719014101405076135440766601200540d4058030340001d140c03019030261907800008065403481c80d0b0b42c101041da541d01c0350070440c0b6540c40c5481d00c086a5150030030903411000c0d000d006a820180a144009940d403400d84c0500b60348100341e007010b00560747c0b0842c0115481050f28101242d01381d5280d841705d054403c43e860072102a0004020407010303079902d00c07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 450878174 1250 450876924 450876947
    0x21303080f120a0506030c040e0d082a03010f0b1e03060d210207080610260a0b0106080a0c02030412151503030f0206131e0c0e0a1a0306070e030a050d0807 68
    0x48d0100035034402e10744c2e07241e5a2079818002c4030030301c00842c0004d64544004400d00501e240b80c1401803004c0f602d0300340c2800c00e540c424000c030035a00c1400180864201203c1c4203aa22181d03882c0c90090784001b5000d0b5101842e00000c10b111340c021254255440040c40c2c007104201b41c0c0c1149405860f08007040c0c00c0290070500c4a401c800c0155201004110a90850b80d2690b02220303469158015410401040c030030141d0003c4c1c40812191041a4001d803c020805101504071017056444120b240c440d01c866405481c0100413401c0141d005000c1440707100a2540245071440c0324403003a075940741d4a0120101900c2c45950245481d0b440100704106064000b5041c9104180902c003516552410750b04100d45110035450107010082c0b1b0440e40d2608104a03207240c440b50303400c607000d80c510b141d44203800808901c0c101c460030001820820b010b090014049032610700074000802034030081c0c0e40c10304211510481ca000300ca90520554880b0b45c080360b4148800007480c40103665829103481c0484016080203a40c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 450879424 1250 450878174 450878179
    0x7090606020c1806030f0a11010f020c1011030408070f0e061801030f1103060f0402120708060a0b1503010902041d090307030c0203070f06170703021303080f120a0506030c 75
    0x30200b0b006559a42007001c48030407040c201c1c0143d440f43d40109181c0820443c1d030340418031070011620180141554030040c480001d036a019644000410101d0701c0c1c4030f8411025400c0190b000c9482c813440c0c0102010640743c826442260708156940c40541d05c1c1984c0b690200c1c003013011180043c00490030b01c01d1384c9688200c058a102e00e0182c100546c588821905210142040c03a00011403c00c0000c00d000003842480000d0446055007401072501c081e440c02520200d204e170000f0309000040319408500c01c405c68003020040e040640d540d0000c84007600000c0c13821980484a400103541003100440a14064a8030480c0162140d003040f80d1510341c610303501c601012000103031040040b070103400012141100d0703041c90521070f40807a504c082303032510802d608160420050310402081c40d6502c840f0b022481100304220401c19211107005400701d1144551202039246a22014404540b90034001d20b1006011040c281c42d008000068901c8140141c0710050656100d6041c0500b03481c2c100624190700c00304 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 450880674 1250 450879424 450879433
    0x8062b05060c07030c0335150405070c170903010e0f10020906040303030f0902060d020c01180308010b0c1614013b0f1315060801050f01050f1b0709060602 68
    0x1504c0252010b049550010104111004514000440300007440d020b02c41c0c0c0300d14040100309903900190260000c45010310000340c40261907166151a0007514001c1e5110b840306040c0c01545d8403801161201d00c0211302c2160002c100040154800348110820281c2843c09800300007010005941050710407c2202241341c010702c030307402c45590380c0340840702140c0c0d0508002074003103000341070790006d001070b0341002e944621f0100c0c94030102880c90b0003c084c14801c1d90006c0214643c5800d1403103120000e01d00280010b0700714401403000202d014003c0544107942c004680718081c14000c02401c200c000c0d00701a20000840d4408209940c120485080c10009500c54200b848001c10800e0452074583d00c81c1200f00c402e1040c00200c03912114143c1e4034010019002e00325001460410001401d07010201c1d91010710316000000ea628466aa194180d5000a003c0010044504011243c541010000b004982020050400009000c0035134a648490500c06405818500a1410103c0f0100d90000c400c0d50030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 450881924 1250 450880674 450880687
    0x112081603090602071e15030f0c030c0f1805010f17040c05100507110103050712091a01124e110d0c061d06070c150903020d08062b05060c 61
    0xc411408020b03078800c4581b2004007d00940e0482c09040c03443c0f01400e0280ca0540d00c41c41311030341170308000a0112151110154585280c00445101c0c1c0e1400240e88000c21a031406c1c40b040d0701c94101e0548154061a15000c20308200824942e500401d5408503039000c482c9108002d103003050f500c424005881c60070860f09181283d00c80b201c0b10342d1611805ca04140d61031001410310360040103041c04c0303960000f0b401c1040a40a03d072030780d04a00e86032f80380c002d03003036401000181885403524150700242d030004000103101d8040c1a540700501e220a40b41050075100745103040c1c000d0041407a248014148101030b03940b1292107001034850f0ba1003940315aa9508445c00381c1d040c031504403102c5d0040650207100000d0011501c01c0341900038100102200041c06440c040c09880780d40040b44610190080703802a0190110303854210894081e90001000f40c0c200700072521609001d44080c5900180c0540038140100300c0c2032060b284400703c1190b44405218040c400001d0010803c110743c1d011100b03d118503d0402c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 450883174 1250 450881924 450881969
    0x2403020309100e030c15010e13020d0b060a17030304230c0f0a03080a051b01020a080f040c0302060a051308060402300102031008060709060503011208160309060207 72
    0x41c09680d181c0c0c0d0064650010702c1d43c40104004840c41c0b040c03004151110140103d1203251440001e03c00c035000c1215200200342041151010800403580c0101b16440b04521070340c400e01c044c480240700d41d074826051040000c05550100c02d1084402c0d40d4000366503645442c0c03401c200641c44403103181d072914150f45000c41d001140080c0c0b0400174501103462424400404002030f8108140341c0008242e0540403484601e003940140c080c0085010400251240000090f4101c0c01c0740a00060400060f107200046440c042140072256040b50007011820503040d101d8010808a86c0403c0b030010005a00140c0030208010756001034011700202d0015151904150700040d00050140340803403610301d60841c0c03900e00303074002c10190044034400e45c000f9503c03403500b21026200e40d00d0a1103040e45030700401c1c0c00242040e20909402c2c0542d5401d4481c98107590901c203604c1c0690001200481c0c0010080056003d20520721182c010900d100340e580f0040d8a0a0810003400d1200940c4424030140320300c6611035042 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 450884424 1250 450883174 450883183
    0x1805091207020402092806020d0801140102030c06161805060a050f040e04050a2a060e0f04020409020c07170346090510171b042403020309 61
    0x100c455590303458a030a800083c00078130401d84403680c444802100c042d1621401c182c0709086800782c40c11200710f6039843d901641c0310351420280c0c0000507404401880803001c4a150354801800c10320441c4c1c10400d9003580c0f0346c5490810340c0c44910482100204003521035100540d0002c403800f0072010141c151820300840c0041c01000d642c0710074002c1c045011040350840c942550010031508034410420700b0541003054540e03160180a480c0005d0a0810425111260048007440803402076140e0368030340b602904a42c04001c8001080c0d2000144c8400209070340c550026101400d0f007840d0041c4c0d640320541b010b0340703007c1c0203a20081c000280c1c03000e40f40819038007006803441076a4402c080054401c0040c86c809940b1422b50220112842c040030208e10340c4a54031245a03d0400d545814594a032118100b0046031000401c801c0050400c090703030710034044c0310b541c0242c10500004401910740c13000d25406420390001d030407030001d031441d04080c912054020204003100115a09085156041283c040c9844 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 450885674 1250 450884424 450884443
    0x1060506041809141905010b0402070218060103110a0e0a05030f120705070b0a02010f0507080603070b07080d06120303050604020307051603110d052a0319050c01090606180509 77
    0x10a40d240416004e1140b400800307500c084401c0d00b540e943d001d03141681480c20f112403209403540e61030214032206034101403080b102c620307800614a480e00c6030f20666043c0283e40090006041503201c024281e203110b03034000a480c003400f9940b500d1142424210034002c0e039180e1580810302c60b60140e03c102c041e080c00401c0e02c003c080e9503411001e940f03440c1030030500e19159042c0d1001081180008072111059419071189001c404214418405a01c800004031192071041e00d0b2207a01d600710300d00c10864001000000c00d403451041d16240d00f408034100603030301140e20715404902d4036044c00720032504143d454807a1991150045a086007181802c2d0402407440c01003081000b6922070f452080d0301494004e0045614000c0c452040721030201d00440c00610079041603440468001c3d010204440411250b40e13800100c003034410045081100d0300d549070030b03030100a480282c180481003042c01036060007070091000e241c2c09658082045460020844140407a400840086500d020b0a1000f1810042a001c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 450886924 1250 450885674 450885719
    0x306040b130303060302090f1503070501121a180105030709020301081911131d0a02030a020f0d050d1e05071203110904180303051305031611210106050604 68
    0x1400307110341c03500350000c10441d000a580580c00200300144c0d04408071120b407140b000180399a0b01640c9480615540304258000c0e1408910380313446100700c04907558003051036048000c400101c3c0001000218003d1404280400d03010a00c110041c003107410200801c070010031001c50210328546c54821425105c1401d0440300311041d41880b106018000140d5000000d2000101130034180c202000c40d483c010b0011490300828000300000d000400d010100d0041c5009402802a04589030b080c1d080083d0704251800c1503a11030743c5001480d001c00e40422a06502c540d258540304058186002041d4185401668460030444200400d00004100200700294001e040c107000c2916025415902421302030300f040142c01034900b0040400d001b040210000415001e5181040262262461302150710810130014000760300801c8259601080c008401c60304da40600b40718038441d15900b001034001142c0c1417094404045865540e450440d080c8202001440c6c11261145480d1412500b907100c070540380c1103047d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 450888174 1250 450886924 450886951
    0x8040201050c010e0f010e0307020603011716060305070305011203050d0507020709020711090f01050109030f0c05040c0e0301060509101a070c06050a08100e011517090f0c0306040b 79
    0x10216405041666440e152000003844081e0b0796155455407144210841d450710342c01c00b072140909042c0802101da07140e4024114030703c0c60382401d11960b400100d142040d0414803e640c1c202c800071500900b054007400895401255a040c2030500909480040c0c02207030792010740700548030000303400c0700c00c442500700c00d088089066030300c0c0c400503424080c061b884405924000a0458108400c0e545025452601103982246c66221042401c0100209005440c0810720f81107042c004611402080485c3c0c6225070b903510071f0a43c94901203801c0d940e00000d1700000c104e07a00266082c9103400c2c080c0d1000340c00d041e00e08050601c1c080701c00341c001c08441d12030051100c00c002020611851044103c64a2603000041055402d5441ca0000d025034040d1030741c400010f1130000030030900301803614500121490700c5024520fa03400d210820340000c0c219040002409140720347c0c5169483c0a030307030807841080800042c2c04d0b20640721007100e0030711060b842031602c40c0d080300ac100310000c0e0b84006502e8002a07814001c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 450889424 1250 450888174 450888181
    0x12103030e0d090f090b01051b030c0d17180c06090d0c0f06021b0102100b0319060b030111070b0a09021305040813051806010806010507020d06020403050d051303020108 74
    0xa40007059140340c54151406407210000840760000b48880881c1e84558003e0b5201e5903c074000c1d4101d9645a030580d00083c400c002890386140c5141c03200c21100d85007015603203002c880610461030454410182e2020490441840200105a880c036951181d079034006242002e11025000d078848902e15500c40c440c00000c2011055a1a0112045031142d8400401c0c54400d84400c003003031160f1540d101d030400500c19084001c2d401d000c2031050703c0105006030001e203643c21000040034050300c0c00403012030300741c8214141da1b550008082c01910505015a8000980311042400e01d820b40d441420b9505180c40100240d81c005a0201c0101da84948550300008a17100588001002c0100203100706c42000d04140a01052150b00e00003400c61078009800c1b1900c06543d9010700603055081c00d108041030103806e0000f2015406440d123a41d00c4101490b040d45004004d44c000b8441480c2c5c400207642040c0d000c81c0601c2004020490740741c88400a0801c03904101c00809404058034440c08002e0402c81e100d4040b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 450890674 1250 450889424 450889427
    0x90e06030a081827060d0503040b030a0f0c110f0a1104051e090606040b0f060a1808030705160501050c030307030b030c0406080a0c1502030409270506010e0f012103 72
    0x200000888010035050300407034103940040c0504041400c2c0714040460710017140440c42c2059140540c0c59201c0091030400e440c002d04005203030401001c0300035a9071500003403040b400080c41401072840060300c0b20b281e500c05012525150111a0b000e000c07407a80907501d10f41c003045a420300810500800c850101c2c05070fa0744040d075800e4521010803101042c2c000f805101c464400440d44600ca11002c0e03030104200c0d2000310820000d00742580780142c000108100e1a9086841410080c14200d41401c0c420100c90340d60514610b50f50140005030b0b1660044101c0d44c043d29000c00e544e00090209180075070400545440c03540e1240b00c042c0c050300600d1365030658070f9219201804003094040c40200f00b04111a0b03204e003100e8850504680454001004180c00300b0030709001c0b1200301291030f00d54000e41c18142003007542030003850f5030400c09052031284100b052440300d030100c07240345103072044015000035458411402c1d0162000f0309002d02c209921401440181900301251015000c1c1255040d112451781c1030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 450891924 1250 450890674 450890707
    0xb09040b0a030320120a030c020f0610080c090c04063b010e0102010903050405040b011404030c050a090c1e0c0506040602030105030c01050c0a0f0503040b0415090e06030a08 76
    0x95007500108500740c008241600098144503445000030840502d4030b82140903915014440d00611a04409200040a10348254860315070003601d8012103e000000d80700480c0303070120485203001445600c0d001400f2140090011070802c5105468480310340c2044242c2c1c0113180268001c040801291220301d0391500b0b0044420043c00303000014551740e43c009011846409142c218500d400b10301c42e0a56120b403544148038804d806500350f5140341c01c0600780001c200203001114030745c2d0f0403c0441d80c40c840035040c1a00040005510821903260b4080c50541071041800081d4000e081c018540701c00d4942c0542c00c40300c0c2e003120320081100e540034003240039010b9401884030f0303002409030300c5040700300002c011517a80254141d890071000c0701c01d04201807004443d588145455090700d60803059001380002e60091400c210144110243c9040031380312a5942d016401c280c0c00b0580c20b5030600880c40c046074100ca0300c10094072824000c0c00d03c80c5004000b00742c0e070700d6000c08010140c820009003190814107060 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 450893174 1250 450891924 450891941
    0xa0b01021207171b0d1403061503130b10030b07020d0503010303030506060c0a03090f050402091f0e0603040308010f09020708180a1e030c12030207030b07120e061009150b0904 77
    0x1c2c030f084010380c421040d0ba803e501c12010006c0f0b0a8145000850072031130701503038443e01004001c00c000c0302415420141e1174001605400e080c49094a004001030842c610b00740c450404000701040c44c61a40c1000d0525010150820066400580310150fa9035400012203040d83d4142c03c0208183e226140810702d20311500564002a020355540c0004042d40300968008440c2625109604192503038100800c0b40308020141c0c0d40035623178050161914101c0b24004540c0721160501c2c01201002c1c4c80070501070340c001c46080780000c103140010310138040803018000150007800c1c000c50800c1855038a56401e0321601c5042020f081014000d4001580d0f003030402c03006410f0301d100c0c80f10040501c00d0071034500b00040c0003c840c1103d2040c000708824141340d261500c115010f600070300c0c807686507032241101c04501030416010444482c200e40c58510b9140610305284440900400b95031170120203542c25651240c20046000d818003003003030b520b00a41d030081c10a0750103003404c2581c2c1e40d2400b00044d00401014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 450894424 1250 450893174 450893197
    0x807020a080f030f0705041424031608070201090c03020f1306090606020f0a0b071206030c030309051207050325090e030322030207030807051e060a0b0102120717 71
    0x641c2c82550032000c0301850003079121400c1092203445001c01662140154010081315000c4104420074501e4280c44004800062701040c0c5a21440d9803500400f55204940140c8031074410000901041e6020b100e083e481001072000b0404c00b162903407075801490362844040c0c481c100c240c650b0031195030340b5081d034141c0010f201001c1048543d44e8010201900c0b29100d0600580500138500b190740801080c03506010350320040c03043c0c450b920520f00750341c8010101203a0040780c0e40d8410100c002b92704040300c0300107503000751203202c04c1c64942010001e641400f40e4084000d43c011060412154800184045001d4001c2c3c00b000400e82e5490b5138600a0b0280342d200e09403c41c201501c4040001021004502446854a00044040014000762004104040e004005070f02225040000c640140d016105041c4140e054035962894034501c0305640070403045603c03081c0c2280f0140980c4140902c541404510280060040b00814030f07060542030040d154090305118002d04010b02d22043c0e00126000781881 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 450895674 1250 450894424 450894427
    0x904080c0312070f111507081801020f0405151c1d060a091122270b0f010923060103061e0509010609050d110105091816090e070807020a08 61
    0x1004004c24407000c00030000b022640506801028000101d0000c2c1d0301c0841c118182c59688503680c04540740782c001044505800d0079800d140c904040c0c20b00061244042c1e841c0d0554581c0d040004010038846551401402b8003c2002106800f60014886d00040080d040340094003526090080c202c0103070125214005001d0315081241090596003e6031b0b800b03020b40262000703007682200f030091044203e91032010705038a0014020300012190170412000340e02c50700800f05020500300b109103c1001c14411200348086000300000342e0b400301c2c200c84c01001003440502408100e902034000382c40e490300c00c02046a071a080001c4090340a504040f00501c0c0102c160071280c0001da0301034484002d9805924490b074031080002441c45e100d141c0e07030340949000500c44210301e041940e413880c640410903600d50500c4000d10100e940c1d551984140400c15030300c036100125525040190844031854001040c00b8000040d1081c400401d2581752075502c41c071141006130040c0ca580c82c069150401195000340744980 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 450896924 1250 450895674 450895681
    0x1b01030204091508070e09150603070e040515061c030c022107090c0f140d110412060e0d020c1201021e070537060213080109020a12020904080c0312 65
    0x141da03c1000101c03804042502c00d440d865800d4226400c0084e124080c05500c0301c007018255401440445412103001000c90302001e56990002120320412a0140c82a400080c80d6074400c5020340f120a034031810480e980503d1031071140c41240d903940350030009010032040c1d44002c02151103007a000542045c404114050010399004038a41c0c031052402242d65803070070302108240040c000d02104242d40001e03101d03000103c000d080145029003040030707000000b03030300c03180745407941c1101d0001400a03004680200c03549800c581040340580d40b544010300c081347c0c0281c0341d110303010ba03012480b651124801c5403840e540720380207840e19019000b0301641c50f0310100080c0250001c190400010075859100d0010758101400d4004040b00140600c030160703d211001c00b52180c4404035a41d08a00300074419030700103041c0500c1086209000c007590300030054aa6444000303005501d05042c11400a206007240043c5c81c00681d0f000c07400c040405400282803090111f010041d1b000240251030051810300e40c58040c514 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 450898174 1250 450896924 450896951
    0x72702040806190917090d1401061a041d091501090f0b030f1b01030f240f06020c060706022104060b0f01020318010e030304030803010f05060703021b0103020409 71
    0x10a80d5654180010b4040f82065241c0c00d0280398000c5400c180c039000003900d004180c640692007100406c0d44655402034040c00500c0e084084180e00890780700018503541013030466550030703a070110340c1c03e084401407200b040313024100c1400b641c1155092298034600c0d100c07401003d180c851628440356160040c140040755081d2550700151001c2d00c9082d040c07084401040526032070b8040c4002e10300e45070b0408496490413000c3c50100280440d010715000480b5290100200200c480c079850341624201e44080c0d42c0f904115003a0040050411540d0080009261402c06540c42110980c103c1c0980c0d00030030345100303000b5070b54161412052a014280360041c4114a440d0341d40600702ca003241d1507460b090804c095030500e43c0c00d6201902060b001180b92a61050411080c2a40706a42c02d04000c2e040d00346c0301d0b0070788041c40940000d5201d80f010716244e505003100e1810103205c9402c1140107007020700844012a5000a046d00c03a2044113004104003814000102d010b032055400c10603109080640401004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 450899280 1106 450898174 450898183
    0x70609060e150d0213240f0c061d0609070605030108030a03020f04050418050f0d17090c04050108030c1006060e060c010905010504200a080727020408 66
    0x4008000071041c3c0c0e001e0030100c0d11294003a5010401801d80021380448880407441c0c440300806c0b0010014084111080c0003820071514080f218148561644024100040302030f00949d5016032951070782e41c8100079140500548240200000c3c014413400c03c3c2c1e416242d1880c0a140781c0500c2031811006500000b5221440ca00b08000000707003541e6521a03403940c00070700200d086075210079082040c1072000400d22042e2070780020741c0c20030800c2d911000280303200c04030420310b047c951030780f0084078900380319003000c150040d00e06000801c0940e000409007155004840807140881031802020058484a1080402080c0d2101080020749001030117031010542d204000180039080782c50701c0f800c1d18010741d426510300c2c034940503403030f0303018915842d2603000b800c10b55040c0c141620f80440b0035585c00c1a840303500d40c00308491080c407400c10a4440e0094020785107002c29911140c5814066485 = true := by decide +kernel

theorem cover : BRFrame.Cov 450719424 450899280 := by
  have h0 := BRFrame.cov_init 450719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 450719424 ≤ n) (h2 : n < 450899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
