-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0066
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:39:40.002832+00:00
-- url     : https://prove2.me/submissions/936ab4c9-e176-4c58-8d32-e4008cf9af63

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 11690654 ≤ n < 11870510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 11691904 1250 11690654 11690677
    0x31103010903050f030403031d030304020f040b0303040501030506031c180f0b07020108060a03080406020307030201051311190f090207050f010504020604050103020d0b0301020a0c14010501050d02011110050108030a14 95
    0x8111031406a04c1881c007a5820620a00c0c0c007042407190507401840c007403103038484078032141c1001082c8001c42c0341055484101d03880540b01800072201e071600181e1240a584030755414103032114006600740c1d8090121200c0c41411071030540b022441140010008108206035000c900c248050101d080700400300490111840c80780c802e03190801c90786c0111580c0300040e0605402280080380840000c1e1281c024101402142d40116160601c2d403c000b400e544010b0107940c0b50240c110122400301d844a12041c4a40d0000c0e50303410040580030304290000342ca03503030040300941c6c80030001143e280480e80081000c1409102113400c00c41225041500300c40060b14000d5100d8020001080154003a030040d009655804400154003140d1001103801d980c042042c0304000360195000340c0400c01600d0320000504070041c000c00c010360600c004501c40c0d803902c01e0003a0510076030822810018204000c000111007400c2f505203c81e582d98041559603400c001040c401003950541415103440001080c0e40021042 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 11693154 1250 11691904 11691907
    0x506240d0f0b0a0303050c1504050c011b05030c1b031606030b010203130902030a060b1204080310090c0c020102210702151201060903020a0512030a030f0e0a050703110301090305 78
    0xc0044800800300d2451003814151101041942a03492030034480045020751074035030b921908108020b007000c0303100c4800003140c00d00c2018040031403000621903000010a007842c0c510700b140081c65034034080020038010451301c80050007a0418002190902001c8c82c1704409011822101081546980c1d0481c040c0040b56440c1d4020000d0620a42003841e4000e011f0058a150400b04c403005145a6219000312003d59000414403900d10712610401703005108000010b424006c681c1c4159684e141d0141c0040c0c400480400030920400f080c3d60f00c00012704000304104003280d80300300c01a00305042801c2c240e0143c014282c01d89100c0d00c1d0429108901c4008011003407910302280d0070802200642009945120018044e000d80128145c559a02070101c40d11040403240c51071040182002d005c0c2c02075402004440d00e0311011010010940c0c41e0b000305800e010400c01074401503800100f1304241c034003c4920600c00d161050000100b00403090f280035541041d280762115041c54240c504452000b000900b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 11694404 1250 11693154 11693167
    0x3030403030504020f1801050a050409030c12050409050702060a0b040b0102190c031b080106082109031c030920010503040807080f0304060f0b030a0215070305091003050624 76
    0x70030303440030364441d02c000e000c44031020501c0b000c00c464a0512410002805111005109902c1e1900d18100107010485040c02141ca941c0c2c0e00521b50310040c0070080030290504029554503000e00150340c041d10050702c04000c1407078042d40003540c41c1c2c02036982c0c4015516003002c40c031841c20a40034030000312030103800509903045c5102c2c070410381a080d40300035a40c031a00020044002002e9001e02e00700c48a80c54101c0f0940340c10401c0740e5085880791b07800015280e02c0030400c600801c030210600f846882c59850745544419000001c41c0c00d04180606980c2003501c1059084503603500340c0d00040c1c0040c00740705210b110450b10035a90000614900c56640800e0082c8000303800640440000c0c01450f02c20152141092050710070400180c00541d02101c13000d0300c4002d1040d240234184104c0c0710000f000c900510507002c4135004106482c01c01d040c83e003103841002442500b03060040c8110b0f40422000741c09403295180c107010080081009079a039511400343c0091582d042c8000208030030001445c040524503240 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 11695654 1250 11694404 11694407
    0x308040b0903030c01020a030e06010807030b0612030d0608010204091104030b0f1e340f050c0106031a0906060303030403020303060915120d0e010903030203040e090c0604080c040b010e0303030403 86
    0x1c000d5180e4a40c5480108618002c000d02800500f101c030704151004103086400004c00f506204050b0021101035004040030000300e0701542c101c1c4c1e000341c4e066421140c68000880f803242584160050b45506e241048800140c21a055004004844810344208001200f00b4000c110718480e9100c06486034040038085560f40e05481805900140800c03031250302c104124514085d48441142c41d1101c14094460b9a02c0c8144250490954a042e6540181940300d41c0c4502828480d03400b00e01100300f25020402c02d000050942c0070f64050760300304003203015022021600d0084100d0840d0100c0d880e0013844049402402e0001c01d690041e54150017650956460a092141001c0d000307001810508427181a0145030310f42c0001c649551031260b01610700c4150060014184040301f15000d410441038003001c00100340e011056a05440006001540a032100710301d1134076005403602080d0740080d0000d0700040d01c10000920004d089001d60381401440300b00b20040d96003810304036041ea0960000c000250000c1e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 11696904 1250 11695654 11695657
    0x309030e10030221070305070306061b030203040f090218030a20040b04050403020f07050306010b0702010503040c08030c030703030609020307090e0622060e06030304030201090b0f040315060e100308040b 89
    0x7444640390040c00d08480041c00c08000003203800184078100d01c0410301208590500038558030011341d0505100703062a02d00001c0245101e400c02410b88480f881800c02010320031300803500240922100d400c1030701e88440c4500000e600c100350009410302200680030aa007800b00e82a00c06940054034000216101420802c1c00700c4526a500d0740582e4450340080c841e6204c1c49010b0245010382d006004200c0303005001850000c203034020300d1207070784454010040da0840e04201e840490b03080c6011512602ca03441c1018804c1e20a4010305841d00010401c001d42a0b000009040080d02a950510150341e44000c8030040303120558070b1500091050300706000300000c40000399000b200150402150031907840c802c0524031200e0480d03060b500d0f101c02d4100181403480c488560000411005549400d01d59170019049440a1090341d501040c0480c4a880e0000c0700c0703040e1401150040042030783c030400d44149100801e07090203202c0c1a10100c2020501040544038400240c0e9400324909103403d044c2454980503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 11698154 1250 11696904 11696929
    0x906021c080105091b1204020f0f0f0607020a051e0109060305090604060c020a02090a020d0f05090a060504020d0b040303060303030e0309030c0f0609060d090201030516120b060903031306030501060309030e 90
    0x1a45d602c0700e0719022662060061100344018603660b0343d581010710401400703035011400d043c03181e81d01c0b142c2e071b95051f5100b03280007a1154089903183e41e1083e0303d10104810300c5e0581d1060364840c0d802910080e105e0b406100700e43c044a001d9035041c071590788844050b422224207031a014800d500110003c0c000034101c1d4840d078044502801141c8800080382d002a9079520201c488803805d54011402c042104101d00136038031021241c070030074041e600e0982c152584d1030391000d4000d00065211004a401c0d5156100c540c82d40c26000004c1e442d50b4603040c20060701500003480218002850148a8007000304040155140c00d41c00130f000e00000d0f142d800801208000994090368049010059010107a031120000c128011035014046a018a140005400c5940043c0703108a00760300d0148170540c10f9030019400c41c1c1c01034010f00010b00e6107000c10108245000f0300441a03003511001130441c81c072880c400b101c0700032240c40366024031040e030300c0d00012415a41920b0b4008c0100d17030240c81c0340300c0c6803401000d10f414 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 11699404 1250 11698154 11698171
    0x1d010c020604150f0e0301060803070b1806010303020a020907141c0605030a0f02040c0f050304080307030609020f0d060807050a0608130507030f030e1903060209011205070906021c08010509 83
    0x509854072002031403080036204401c085a1004419914184c005c011600481001c800820400d85810501ca4483c49010401005103042c1c0740050140040c01881e28080203640044a200390f84903e0f001e986d5000c8a5000d03841007090100207400984200604810382c40403842041c03c012841da8108000a150180c0180c0319441d48070104460300e040002c1184640100c0d680480a03100707006210898082840101c1000058410ba0380501d401100f141e8100e0750204d09140d403544c859508400034480364000c00c120381c0c0000341203404824100003429100c04802c0d800c01040e0740d1008125501c501a1040c207400c641162000c010850060034900d90100000b040d40c294503500c0d80e5080e0900c2031a4000301c41c4d182682c80301e4028140e00040103941e40e0815928014421900e01c0c0e80038100f0140e00c170080c030b03843d0000360800c802d0b441400485941c085c52201803185080c105c1000e49113911500075140144902c40749920000355070b03200740c0804c10795611240da5990902c4248181d800d0700515401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 11700654 1250 11699404 11699407
    0x309030c050f0c040e01050609040201050c0109050703030302040503100c020c041d030406020114010b040f030b0604090b040b01050112020304020a05010c050703140105060109060302070506011e03020909010501030203010c1d010c0206 102
    0x410700600481c1c0039501442c0c05042c0d41482c3d402040102d130242c103110200350789480d0400159440d0140c080e03400a4090820a45030910641c2442c054060340600a000d40139110001007015090f4001d4000e44108501782e61030040040807c83c2240e10640f03105005900240030300095041c558000303081c1da01e80d800490001c180d507440d25451540300307500000c0181c0d5608103030040408012009405880ba46d80d65a18051a0800a0b0510380035800301602004411000c182d07560b40d107922890140764440498403680c945410b100d1000300d0244601c0f1b01043d039083c0c0d510000c003030714801c03130344166401007900c51494100401120668202c04088030580324000c0c012000c10718290004801e15800800070945140030707000105408015800817007410b005000c1030300001c1c1e0204410381510032403201008092120100d581000324140c0c0043e40280404041c80340045045d00650b059034000e42c002c0c400d0360540442204d500c111944528070007614100340a00700d62040c4000e4046600003030a05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 11701904 1250 11700654 11700677
    0xe0604020904110307170f07080a0e0a0c050f0f01050f030601022a15040803030711010b04020a03020d140c0a08040206092107080105100902090312030c0403031101110406030903 78
    0x307048428440f425500780c44040100103405900c030a040700303ca9040381141989003000b0443d1418084082c0c2034106000815001170b200610640c0009511506102180c00f6011181030002e410200382c0075250060301400e04035419800c040c440207141840c10b96540345480c007102800d0b02660000b816050441c020701c015606200ca1240800915507100384101c0d0794150224100004001c2412040b80036800500040006c4c02010050729444402420a5007e860b001d29015006200040095601910114150390329583c0341d4098000c051068108200c800d003001003140f80d001c412070b0000b51844040000441c3c00380303c0ca2500740c0080c070103080641414801400520940c101000240080c40145440c0300300e00030400010740148541e800801c41d50800044400114203e40582100c40e41c0010701003006880800c00400c0480390740030042e440e801c2c85007046e1070b260703c5848141c001a40f07990b00b00396180010310480c0d140c000040740280c40c01d0318200055002d000350b101c045d01404044e0310903 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 11703154 1250 11701904 11701909
    0x9010c080d060e09010b0102060103020d0813050604060906020c0409020a1502100603080307020d0806060306010e030a020607050102030105130204061b02010e100206010602100204030c03140f010e0c0a080105100e06040209 97
    0x840e4050803001c0c0c034403c040e20f040640e95084542001c903443c1154813000041015860b852005181140c000008998903074100c000c00141811503441a038015000060015186500500f52015548a039081d9109101140d080200340c41c01184080d51040901d80100036215a031415403055802e00e00641d1502620300c25000221041a401660191400410851001c2c0e0601885200344110b06150345241012000702c2c019000c000c101605116090000552941d07040010002e413640c014900c07a640d060341d01e030190203500b0a2107018000e910940c8561661041e5000381e80503100701d030380c0d4002420010b10800305003420b040c8050b4140f03c2010b030000700640780d0a08203481200281c0045c0015450038800914020300d0341581c00c001d603c14001480010b02010a1208980e0000000503400e083c032641c0e00e0a040032030600c440558030b41144951190404100ea081405003101e541d8100d276550304141d400c0c0c1e04203d48641000d1000d00b01442420000442c0036002440070b0401400c22904001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 11704404 1250 11703154 11703161
    0xa051839070210031806050622060603050f13060506061c0902010e01031e0203070302250210080114090c1c06030b010f0506030f0901020d0c0e011101050c09010c080d 73
    0x40e040c903940001258000c0d41044508500d11004510301084010107a201c030791404003080300d0040c074880d114000b181e00341d55048002102140b0003620322596030141030380c00e0000c00795881107101280c18036001a075a008880e00842c40348414001c900700a185640e18140100f40082146510860038412100c00c00350072070350b105024584200016207603020b070001514172462020282d0405040480302da503d003480380040c45000000340710142c1c4a40380e440381030380a40951640058084503150b00e0301c21120501b0f009449050094592840519034140111260442406440c00038010070101d11014180a003461b075004140060b41428011004040580310f1075140030440703081e0300e5440a01c103005100c990070303004068074030100d9000c5240c200070500d18000202001c1441200c0f0000605034402034040304c400c040d84141c10004156070749005001c9070451003107540040d10815403004107510521906005512141c2a1814111210011500100c3c00c0c00304580c584000c1c841502007480500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 11705654 1250 11704404 11704501
    0x1180303150b0307092705040510140402100f0207050a0602070602010b03030a0c02010c06021204081b0f06010b0c07030501050901020403030f020a08031302120a030e0a0518 76
    0x1030380400c00c540c0c1c0e0014820044455040781c0c07100c80702001480191900102004105c81c40141e0000c0c084050305c2c1c40044801c80120414041400c03c0100000c01c130010a041e1079031000901c08024966410a0044071705070700300d034000d40050030000014101400740305d212440079243c1c0b0480d1280f035111001701e905110342c0c1d4400c5026900c460002c2c010190203001d0301c04007180c01e400644c181401ca0100a16810015102a0504c04407155031014400c00f40c0403a4000000f03440d05000b282094902039405a010880060726140310a1004114a001186008005460b1001042140d0900104603419400111903428900c40c00b4400030000b4828051030740328907000c200050f2a1865410041d0100200c103d150302150418010b0000103502281500e81000c85c01c10040700381c04481c0b000c2001400103803407005040c4100d00e09602010391001038400703400c00c103440111489a9032803d00015607048100380b048003c5060000b1a04030050b2041a00f180d400d1402c0a42c080090400c1c0e0041038211 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 11706904 1250 11705654 11705657
    0x702040c0e01020c01080c07030e060d0e030a081f03020f0f0901030f1103030406050a031e050405061f08060a02070c0e010b0405030d0f0507021002030c0115090606020304050d03050705011803 84
    0x203005507119a014421580f09100c02c1c203041c607075480e02c009000090310032100028140294160614001d032142d0056403c5603199881c10804201001244c03981c0e40c1000b0070910024910b04005800c0c9048805560100c0c83e0190034031403500e007190b080015450812806039001201c00314040c449a545641d050700850190a11203e62a0103080915500e07480da55141d00036403080000b0842642d0100031a0a81c031154a00015202d9603034040c00180e85200404030b241c142030405010510501150150040703e0185030003414180c2a0f42114100d00e4520900c481508000b00040e40c2603041c1e001000258840c1507000101d03a1180361000c4031400c00e03040198501c5022400780202e0600704002040040281000109080804002002445410b0000307014100ea605c1415080d0700800550313545514481c000d1022040441c800c00040c84075100d03a14400341400700008003507001001b182c2c20380388040e2100c0c19291241e2026640c2d5032082504a94943da103804224a027143e05900141c440d00c603 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 11708154 1250 11706904 11706917
    0xd0f0204030c0b03060a060309030e091501031b050a0c060b0604030b0f091605062d0702010306050d020102030f031b07030305041415071d190305060907060c02040506060702040c 78
    0x7076041941d4481900d401c0301106800c1042886055a10322401c941198958034003c510140c045c0390484550340130907403d5130015500e1080c0302201d02c1c9242c80c80c40011081c0c0c1d040000c2003100c0e800d10a0f0165140b400d1000c02d01c00c100054519114001d480c1c040d03401068082010b601c50030100d17800341d01582c010340314000c1c20740900032050110320301c6035000428080200f958003c0d040469007421303600d03c2050301c1008000740103590101030740380142d03a82a840d44942201a0307400003481896010070000c900081c0391850100d15898444480340c80c858040e8025403c003801d40460312102e51000c0c01d80854000802c20b0b5914400341c00000b44205440303541c1c0419282007914148800140040d03a50765a0b40140306841401c84400104a030b02201c18941200c42d412044402d0400c40001d2011640055081d803040512a0360081804210b0b4811400c986007641c5c0c10b51015164040c50080f54001070703500000c1401362400350800e9801c2407006000c285809011381c0094100d404510581c0003141c80c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 11709404 1250 11708154 11708159
    0x10b030c0f04050d0b06011403150607060b0901080d0207050102061005040b010c080c032a0d080a0e01060e04030f02030a02060c0904060504050406050f09010c0e130605030f010204030c0609030f030e03030d0f0204 93
    0x74010408238460803a8542142981040c1003000422040c0e1300d9030070702070080840c1c8403090160036045041000009461580c8658440c1d000766111501c0a0807036003d80314042c0c0000d9a5440040d040340300311403241c61458601d090404000c00340c21040007850400015030f0788180881c2c1410000c001070701700c40004650301c0d620301011005008140010303202e5010202c5011201e16030100c0c0801030140346280c080e0f2103540c0e440f0780d10001c11124442c0b407a10343c42c1c240c002c03800310010b1100c6800b0f14080e8403041030403007a8610032666403007a038460b200160042c0300411000030300c100c050041d40200500c007042d42c0d600c40b4045400c84501311400e0300c40030340792418010010607020180d508280312100a1025801c0d055001e881100b12404481c014404207100c401a032200d5480240038100c01030903100022940400d003400b0f9002400159506c06080c140050700c18000e419000891b070784026405400105501e041e2104860b118559802d400200320020421207548070761654140c41d00700042e00c890 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 11710654 1250 11709404 11709407
    0x30708010b0a0c0209060111010204060503010801110307020d0e010c0b090a120e03070311030102070b0c0a0305060109030b16020f0f16050f090112060902060703110114010b030c0f04050d0b0601 85
    0x1001070744218600c0800b04224041140e000c414001e0b01601511565400e0319a00012101508104034620a551004c1004642d8590081c01141291060002400100c051400b094820320082e10b0180140c1c1c0415246188113028010007224100141403c180f0b0201b151035180d1540c1e0220b41108807a0804501501081141c03448056407040b603103000c0074034189410202e0340e584642d001c00341c000303800c9203400c8003e0b0b90250101c0d6030040d400322000069040c1300d61940d0a9800c07800414020908200000f142035215a9071001100c0d0044a400c2494031900c0444200051007100302c0e04500502d02c0004c003520f000c114425160341701038014079400e14038207000210f0725504d400c070501c56112000386541c0c5554401c402d0381516500e0403030001400091518600400c10608021340080c1c01084400034035810a035419003045021000b03002c00107120200002d825000d00405805a00c14008180060b603020301030301c140c00001c07240c14a00358a0b280064840700303245070112100e0312040d04200701c55 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 11711904 1250 11710654 11710667
    0x2130e010c03240e01051507020d06050f011e0303050c030d051005040c020606090a020f120109050103140114041209080307140d020a0503040302060a0921030f0e0a0306050403021c03020307 83
    0x880040d83c0c0565400d01103444a104810b120340c0f4810309288200319106000102100c05c8581d0082c802500c072001c0d882c0520140000b191140c524450803000010134011100102d51521840d0711614451802c540d002d0790b46403c8070001b20714a1000384504c480ca800c55100d114050b0710084c1d200d00000d85000100710a4071a81c0c0e02040c2150024010f10241d6190700d01e0282d085089044003507200d400d0343c01c0b008094025200782c0582d0a0305603000213400006a40b005068900034608224015507118070f01d404c0e07500c0b80c0308103100d0403030400c0094040f65072900d0003605841140780030f18134075a440c10503600e1600415010f4950b00607544500112100c10041041e844281d0f00240400c6081d5481e0141c4a0043d440003a008150015503005201c0c415840710015140950718020f003500382940c40b01140c40f000c20102c021900c49001e86220a00604140c140540300504484145081d541d0f408040c0c10042c0044041d8030607c0c1c011034104401c0c2005a20214681d44d005840c0c1c9003060004110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 11713154 1250 11711904 11711951
    0x140a170c0c060f041a01090203011a03010e0708040203120706020c070602010c02070e190c050c070b0906040b0d0605060f120609010501050307030b03100e01020a0305010b0c070302130e010c03 84
    0x141008101c5901103a00c0442c4a9510011560190485076240d0a1080500544680c5d5202d020000800461507242e658040e50503120032400307850071a5549412540244001e0003908444410a00084c0305c40e44074441c4698090710103800c2d100e004480100c902070981180c0412582950045500300c641c0f82c04100b40c40040080b0310081c400181e103000040d440301c800f8010217000520740c20018510300e9820007a00c40584819034204041e20806c01c2c002c0094210701d140030761a0261a8000400041c0002030712804040108060b15051900c00d200d4050382c0201e10014400d48c07200d0b40095180ea860700a450402d4040706840da07a035001310b0007803200c3d41c1c00030030040c495440c0c00c0052116980c898240ca0b800b00c020b05001134035a8500c00024503200c0c0d41c016140c401c0d0b00301340c7c21800b42101900030700001c1540da01d052005176243e150b0702c0e030301e800f8078a01c02070981d101200030030140c40c01001c0000c0b1041d0100c0c0014600c20101421406c0d108110102c2001c00d03128580c4000503406000400358 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 11714404 1250 11713154 11713171
    0x60c02040b0603060109170a0218061305060a0603020702010309051b030d03051311011803050106081005150402030402060d060e01061b12200601091a18040204020703140a17 76
    0x6146842c00020302030300400d005028200c0c0c0f01d12080c0c0b172012000c1006d00511500104035010300b0020520b41101d40340700f24bc02a020312101903189503000a0350182c10700920006059190701d90130040101c000350000c1000b42e04040d03c07000d420002c1501445465500c10942c4006e000c00541c1d2001d15292240400ca200e0805203410100207104001040440216078062651009a80e00c500100d4062a16215a0b0103140d540c01d800010050305501200480e00306101340d80021802000b0501120011036000021307a000400701c1d42a440d0540c004c40d80180b0050105040a0000352650100da01d41c3d00300300000d104100040c000150485140065005150300c5c1170049103559440e10700b400581180032003404040c40701103921050304070340b509091111900f00c944569441c1103002c0076000303540102e24180748004845905090090783e901009401040880c846d0b102c55081c48000e40c0b00315026410090b40e9580b80150003001c600410a4001035a076500b140566951011201c1101600031203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 11715654 1250 11714404 11714407
    0xc0203030f07030209061902060405060610020a0204091a07020d020610120b09030405030d05040e0705030123040603080406020a0b06011d04020c010207020604030b01030c05060f090f041401060c02040b06 89
    0x11141c4240d0a032039808042c5160158407020940c01188003801a40c600884500a540800741d0b01940090054800c5000c0c804440c1e07241c03115400e201d00703014001440d20040e080824808054101904140c80c40f0f8402c440903041440e4203080000c0340d407019204180140c00014200050700e074100001c1e80c012184541580b402c0d0310b886001400b5581041008284004810016919800c184213842c01420003805035502c0a0b0b017590001c20035032040c0940c59000e0003842c0403c80c0c0d44d01c101c00380c034141c2d031151051009021440030011111079042e054a5803003500e07020003100150800d8060001401d96800030007921240b0f103055040b84d0402485241080305461002001140401c0b031040381c800d0036100141d543c26003175041030181c4221138020390083d00c0060000100290740803014104e81c000c04034540c0c0107465004116041c440c151512401d80414001c81d9000d241003a000ea9200000a200003105105009001000b0300c00341d20030030100b2070180c0c403c425802d02d8012440c49003421600d19 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 11716904 1250 11715654 11715661
    0x602120301030212100203011d0a02040e061c1502030a14070504120c030b1303020607050c031215030706020c03010b01030e1c050708030108060105040b03010c020a03052b09060c020303 81
    0x110824041484003a12403200070f46070f0400c025003404034802013004000d056650390b841e80300c40c8042e084038100110003e440c0b8400184100842c1c0b0030740c0c3c161380c2c03141c00701c1407540c1340d10f410002080e01500c15000c81245d400d00190016860a44401540e58000780141c0c403840c0660b90300084424500003d8010b0480000b0007411a40c80401c4034240e80355801c0720b81d0104403e0038a061280d156800040c180e44908085c0124424201000d101c024829400c90b0110340d40c048044500e4000c02c2c0b88548503600911a81988950001003254003c2d95600d0540d1100e180400103498080c450f481200541c00004c8032880c6c5080c20b0280c003600f44001c0c241480481e440c504001d94410b50400415008260010b414401c14400c008991640c5d07000742d500c0e030f01d95031203299464407400b0a2249034440c85c50126406001d08060041a5050003290043c0c11a14040d40301540d86a20004403621004403c6210720303004640003c58104c2d0300d0412800180f005d2484c5400011914006044000d652003071080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 11718154 1250 11716904 11716933
    0x40506041b03020c1005090304050307050303070308040609030c02040c1706030c0a03120306030f140106050a0b03070309140a0f14010207050303070309050102090a03030206100b130b030c130305060106090602 91
    0x100701c4040903480e0050703480c42d141034002d051403040b18983c80d00b20306007410701c9403614001003d4010342e9011400d640cae07820b65a204040d40c9108286005000c80c1000c800100412040e910140100b030107420444038100482d40060304480f1103500300b0001c1003044051104511f580c022250303007c0c000741c0060a0f01ca51003000914090180d11000740b007800c4510b0800c4649100ea00801c0042d588a404440706507481e01d00248803903852000c1070007940c43c05034001894603080c2d50002c03c60300110000740c42c41e10b4014044014010030f800986626001640f00016030b03800300030307591410b802500c1d90200d14a030b6150a0340308076815025481c03160300601454021500c003204603034200a0504001880300007915090340680103050100344d001c0380c543d600209040c0c021540e1442801c0031010020b4a40e10740308810400d026082c1c14800031122141c3c14411003886500031030300f02001c80085410400381c008026001d44554104480607002040100452a0002c4030070300980b5041c0040d00c09100389508 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 11719404 1250 11718154 11718191
    0xf01140114070203120c07170a0c120309030c0b040e010e04020f011b050615010806010201060b0d0b0f03060115080c0a0c080f07120306080709021201290307080604050604 75
    0x608422107800900c000071540c00704882c956107081d000115031140d6151000c40c0d114119841214403000b14a00d08282c1c0107004201640003e41c030002d910f059509041c011000c40c06415030850912035111400300c04900314103034800040c1100504240e88608205069902c0b040c103902001d249046a020300c001650b54010002111a0a01e401c4403002d4100c0f041d14111014104041c105008200500029200184500e81c0b07200c0281c0350005580c440714012800c0720302c94807407442484024840804090100c0c1c1081c411594000d06410024a41d400080d0a003202a8490346141c5801e500f540d416070340001c0203503031285001d4080c03802c00002d4036001c0c1c0cd040d565200200f6914000404035507e1155505980c80903070804054402d0035481c04000d0010501070141b100d00b486042c10020308507600b4000c032050585010b000c0c1d4030591078901c05c42054040903402c00245150102d99061002094018500c01d0015607908404c5007003910902c011950007418490142c2e04050014042801511 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 11720654 1250 11719404 11719427
    0x1e0702090c0307050706050708070e0d12080a020405120f0d05030c031b16110109090c020304050f010e03030c0303040204060b04060c0f060b030a0506010302040e0105090601090c0e04060e0f011401 86
    0x10141076881e40c0d400811a40345c0b2070242c0040007617142c042803241c020340c0b008404c0e200d4000c41d110403860346818420440c48901c14840140742040084800946500c900c101c0d6402840f0400050b08103516100011141171403501c401b0202d90101d0621442c0003801c000c0100303614954207000380b55061081c2e0a0805101c014440e075810110642c803002c0300c100b84000c545100d015041d0040b201c90302d81c60004228940141410f001508580f13000c94100d08510813901c02c20342640055180500d01420700122280f907910340c0b810700c17026200741c9040341c405100030840303180203a001d942c2e64038182c8108004c455054201e14000001032000b0703c6469040001e549145030026540c4415000d1485c0101c040d160b600d91083c3c0502600305c1040c06c100740014817a040c0d038402c542c1407020780c1d00103550500300c40d0215800c0307500d41d010400420840005901c42d40c0d001c0340038500f40c2c41080700c06004c04c003942d03610341c41003003410040010480d4102c2408003850140c40d294403080041150540020042000031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 11721904 1250 11720654 11720671
    0xa0b0112090203070f0308030601020105010501020f15060303090a03080a080c0a080703090f060606050c010b09040f02010c030207080102040b09030c0d030e010e06040305100225020d0b150a0305031e070209 90
    0x1a038820003550f60420001307000b85940300c401c01c0f1550b10781c588104a03400c20b40781a400741d801c100021031150300114904040c0002e1400502c2080800c1d5212040030101500d140d8040c0010404503049486071a8100b010754010302c042c6648500780b220013000a4801001051006814065003541c154410140ca030000e4040c03502140398441d905207078a00803402c4100610076481c11a00064140c0c002014045003001e80008204551401051002c0c0d424219001414207030584001801580074103080c0384a680680704548116407565410f50881e40b184d0004050b00c0000300d236940140c942044801c0780d002058501140140260380c0c09010020003040d402d0601c4200d0b0400841c50f241ca1080d01c00540e08541194007901901c00001c000794013451024403503115045040382100320949200c079809501408043e11400d8603102e1045049014000c400400d4114040805503079032500e138000035502401c051559022514a4005c9821414034400003503a014071080c00540c1d0f80101031980103100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 11723154 1250 11721904 11721911
    0x1507030209030106030302061e011203050a02030d0f050f0601030e0c0f0301020d0f06030b0f0123010306051e03010c02010605060d0f06032901051c030f02070b04080a06050a0b0112 79
    0x44440a80281c012410030503015807070000008103055002030740394090803005100d9078603610b0090762003004003024041c40b00030154041c28a40007d100d0380092a49180c40d10507a414854035000090590b03e1150b80c548807a0b807200140026100070000040d08040242006c10040704c900b4529034403102e904150f20b1080c0034123036488605440a40407960300341d1101d20304101000400c60514002c141900058500c50360b42c400107125002072518943c160313401c80003140d210040400c25100043c200905440c100758644900084070b0301c0f8100c8070302400303400881c0280c41d4078420082c10f00312104038945000316030504508002c1516080102c83c20303254912000300d00c40c10881c0107500641840e610040256940b0181c01c50030008070718000070000c9001d074081d05166682c104110310030b207203102c000c24100e00780d42e04c410019010f400381103004003a03401514100c564995007404642c0040d0701c103103c00e070411902c0800700203c500c60280e10a00340d00041086c0c541100000344004404a000f0780040e64 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 11724404 1250 11723154 11723161
    0x403080a09150606110708010e03040b0306040204031401023f0604020c03030f040606060c2d020604061227020d170406110607020705090c180d030302030601020d0c030215 75
    0x8810ba03001c10541a940414862203540e440d0007400c00c1d0031030f00c042c04240034111021440d4076060080d4040e081b0f041000b54201802c010500d0111703400030f46841d500a501b0000080050381c2001c5001c0300c9500d072000161601c0064954842c440c1100c80008003c3c1010000303001c482000c2124051054030300b0070840302660310080402e00a110380c0c0b07450f410310300c070110411182005031001c15120314030514090041c41e03556502911900c00e40308001f0b0040700c40e6010901c0700310301c03d0148150b41c8440c012140c045d0003203030049603c40c2e2058200030002201c0c1c03003200d1141e5515000b0403401c0c1c5034606c420b04001d158005250074542c44540e009210305010032204040c0f11143c050001295542c11409a0382c43c2e4407070001d00800c95a4166201d1405441c0022b403d00d4004903905044500c00b170690642561001000784041d407100c0f81e0048040032040501eaa2500c6034825a24810301c0398070010380d242040340019113000ea00504190410070400c01c0040000c0e8003151650600c1c200c1018110300340c9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 11725654 1250 11724404 11724413
    0x1090902030c0d140d02030a0503130503090d03030204140a03080406051b0f030403020103230411130207060f05010f060c02060304030912050604060501050307061d0a1205010903170403080a09 84
    0x1c0d0b0b6559250307006a2080e840000c1c860000c00c010101d440c280e04446030074403d190240d86a02030070035558082281400013510742e1440c07181c889941c0d441041034a1400d50001c00240c50104003000c01d400084d40800c090000800125400c0b4200004640d9031800c0f0b032859031992451312590003840200310010403418034010141c42440342400a02c07080d20210748031001041e0356600180300076400a410200001000d6a8411656090340e0411100360032650351910b407440d8082030356100a400c9262080c405860480030b101130301c0c019210302e41c08a610b001805040c000da45042c0c212402070703500c50404001c41e0360081f208406803641501e81c1c0740c4aa90340e04094406030090f900241d4a159106980c00800502150a0384258840d41e82040a6600d44050550701c00701405404d02182d4030900d240140406440c1c0002c0700f500080503c801030362144242042031b051810110307101c0e03442d01e05000030540c000c03041c00e142c104a5109030300b051415460040c072031907014000075103040c4ea8006000610 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 11726904 1250 11725654 11725663
    0xb0406030803090a1e0b0f0403050c25050108070203070611070602030c0910140703030e0f12042903060d0201020f032109030301030203031e0d0906021801030605090109090203 77
    0x1150400740103900c92410714400d90311014001c02c01c90b091001032101c90a1070300e81c0341c4515882c0741c001e414107a070345c0d98403258041c540c40060419010302406001d80b841d00c0320304111194070000c00c4880c3e80d008502c10f05c01d40300c450711213800541c140315001007006089070313001003954401c1c0e0300300c00081020010f8800b882c00920403c10b0141c48103000100304881c1c2c42c00000146400d620944414550b0043e0305022503035685454806801801d00b00442c0010a00c40d41184141c80c0102c0241c410746001c0381c001d43e28001c00a032101f09040c1d4045800c0040c28880000000540c0c1855030014080115401940c0395200080c56288994000d602038020769200304680e06520300300b501243e544840b4017000c4007450444000091404400c540090015840802035a040300c0d4094021804c101c4825007000f00426045401c1207000018841159400205d0141c4401d05000b1400180d460a40054000203a584140250706050501e00700704140c0d1503d45813141196a00b210015400742d4134030000c1e051 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 11728154 1250 11726904 11726909
    0x10c0f1412070509130e0607121503030207060f0905030601090c050c060406020405100c12050705160e0f010501080702120d06030f08280801030f02010905030102030901050901050604090804090b0406 87
    0x1d1495040002d001d411400500034030340300311030540a000c501044201640c511803501101e0f0341203407011602c0d01d07006014502c030096807800c020074008004610529460061f601c10740060344507290400a45030003000803403104400340303010764103107090002080d035610040c850080516500c20741408118410000d032400039920300140c4149085c2400c20101941060144501c01c519180c240d86900740103404424070603071700c06d01c58507903685006002c0d035803908020801d07505405101400b52044280c10000307006044221882d41c1c0d06c0c01c0083c0c8001c1400c0050300203d050050080c00e205a068000440703421003244ca00c0b2240c0d40f8000c60b03081a0285c00540d00060090070288031840070018000040d10344a00740a0001a580004000388405103299035502c00100d00d0001c01400810741240c046080c4138010b06184020300d5940c80400c1c220707841241c943c1c0302655240c3c2806407440013030165542095003140c1c180010880740e12664020f104a108039030505584040b49409900d071741d08036030700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 11729404 1250 11728154 11728177
    0x100e0c0f070b07020a0303150627080d02010c1b0803040b0705041203030209040507020604020109090c0302040b0d0f0b0111070902030a0b0a060203072a0e09010905070f030201090503010c0f14 84
    0xb81e0500000195543c0c904810840100b41404081c84c40704803110300380012128981d803440c03c0d0015009400c3c4207140e09403c6200c5040280802145483c020460b8100d00801c0f6400010031407401c202c0285080c91144040248a007c40318031808a00c424003503c1c0c015403c42c403410b2040d110000180c0f044d1180d684017030100c80300620903c043c5501507010740000402903405108682e120903040b41c407950100ea0080c0802c0c040001400218503030f034001480e161035410018501600e40c10417042c0c0d0307085540d080c140e42d500d51741b8840c5440480e00030300031a01000c0c01e10909641c0c88000060300c401d40c50103040010b66004c00043e41c60402030b0404981e28078041c2c100070500d43c40e100000d48030f0f4080c50b41640d554403124105d10307054001403091400075006070040904582001c0300038507610400b800e004c90301c2d034851030102e02040051003036500600546081d01c0965241d84000742072000158042c1d44640d141803070741070380c0c0f41c0c00800d101218a440c1c940300d910502d00d444280c0d40c5010b190b50010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 11730654 1250 11729404 11729423
    0x60112060b070506090609030319020409020301141002010e030901030c0309020d0c0f0f03080901050304021305010e06150c030301051507080a05030f13020a05041806050a0203060405100e0c0f07 85
    0x180c0040074001842028020f10130345640c1d135940803050f55501016940200d50740d01c2040060346a403201b40d45905c41040358200540703415642d0001c00240d0b00300780c008010b0500c803002c1200061900d2990100313100103030300080c041159400e0382d0382c0d00e9028040e581c90603d610781c40403910711403103640304101459000744080303030802c003a0502d204142042d019038580d880103544081032207010810b201084a41c4454102c1c0760104c5d01004407126000500300b01c0c1c100c4440d4112545800079402428085c0c20411409421843c01c4010028000e040076422094220100b102c410030000100449054910030380d01c05415400480714801d030784c81084001f400300c070404030385112000c1d801801140208141a0b0700383d120f032101d500b103200030402020000c1d8080d0140c8001c012a052a07080181854117500c0c0000144840c0c0c3c80b400140c41003240e410004541c0081000160f00d03051282c00d8000b209018140c403801c1c10488007504000780900480c600240201e0480750200c80722007120426a030015001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 11731904 1250 11730654 11730659
    0x3180f140109020303070f12020714010507110909010c020105071701140609100210150803030f06060d020d020304051005040b040b060d02040204090e070501050c0c09090a1202150f100e06011206 85
    0x1558040c4411f10221421050000300d5071141e803000540d4000e0790300c3d441201040e04d200c00019038007980455003c0324400708508100c1c00030355070306003034070302c21069840045009100f44030000d08562004180d0f00c00d01000e0040d03100381c07004503400d260648141c0002c280c0c0b107a0184000030b131140112000c603a13002c007800480c141405d90125007490010000c600501c4818030f50b01c40001c01c4200350041040580c01403002903000c1641c000e45a0b0000d4001d000e080c0f802490030800410799014241400240ea000170a000801404120391085028401410015400c00b5610345d0940d0714080c0015041c0080d01c0003051107a601d0112248449600500c11962140d80d440f0141c054010642151440d005102e000502940540c0c111503852000202800741d00c070100b01040071050001d41640b00e20710807100c3c80c1c00007a240300c2c83d1408484158005000a041007008003600801c010900015180b0303600500c10600081e91098094484d000512000d581d070b2000101d415800c03812070068070a0401000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 11733154 1250 11731904 11731913
    0x5120705040908070c090902060f09010c020603010801090c09020309030f0a02070e0a0504030305060f06041505120a0506030f01020a0c0602030402040209040609061a070b0414120a02070603180f14010902030307 92
    0x10038225128843e45d0f0840c42c0c3d0b440704101210342d0b11201a40240c001c01602e0b03a01a06070009048004050400540c05a602d4020030190f420903002117178140c0d524a10b90013440074690800c001080c0c210310952075031030406078454480c05503500c0107803000700102c1c031950701c20700074024a0302a08000103000141d180200000e00900f8081e5000e030302083c94440032a0850412480c3d00321420303170150003103103854a440c0500729864008600790301041802c1c890326803803081c0d64003403601415000c0e01c08030381420120105414032a005191170000da204010210059402000810100d078208030b00585a0303841d4004100030b4412900381580c414502100807c45111032703800042500c00740340e54548004001003810307500d441081c5001d807908100320300140000300e04050205100151030700745c64025400c0e0030b80c00210f40120100741d000d07812611003031115940c10b00c00c1001d0800c844410344000501c549604000e800c0b43c81c805403c5503950303240c0c0410718a094000045059014017120b41e52040341c01d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 11734404 1250 11733154 11733157
    0x115050a060309080408100c0306060806090c0c0c030a0b0406060609030308010b0d0912090317040506030612010e03070b0603060601080411010c02040e030f0403020906041b050901090e07020a030201050a05070905120705040908 99
    0x235040200349000c0d40851054414041d45d0721601c1c010304613203555181c08084d0310864009403070580440c80b556182088a450500c1540320061080c000802207040c1031400400f0344005400510400c0400c80301000071079030102c1d00c241180c01e1201c541c0d5650303038100f0a0401502106202070103608034200c28000096214095508407400b0b01380b1241000b506800e100894030951089590040c4144007285040c608031076103600240001e4000144585400070701401c40c0c00c041e00a869409105e0704102444c1028041164088824642000c4a261984e5540c0700051008045410030110001c95011901e41d40d00c0401c445022804407500c84428000707000c40c41d070044c0400c901422942002c61500e0030b0034054480075488041c85000002070503070040700c813a001100340e141040504080002c0032050098240d008928aa014080200e890f080c06400d480317026090b416614684010010201d502500e48800e55000b22480d800500502c03004500d03008264112552240c90030454004010a090 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 11735654 1250 11734404 11734421
    0xa0206070510050f0c04030311030d0608030307020708010c0f0804111f020c0303040303050702012303010603020403020f0d0309051002100203091f0c0806011101150303110115050a06030908040810 86
    0x21010310613039803101101402c4000c02d4600c5c100741107044c04140000390140894103141c6d80c1000c112414045074200e410705503034a550110103141c1001085c0304c44964107001175005401444000e00c910000c1100080c224a02c20340c04408005c45100400c04222400c0803003841d515004010111090f8102c2c0c01e91303004800c00c45082c0243c4203844015000b4100070081e5000c0b0b030f07059202d2500302810f9400641e0341b0041000c080c9054068600301038111084440550f020340300c1c640d801600d0740e0440c81070007240d032540c0c0702c00e034401e04207031501c5da00095205528205540d000c4e1480c5921511250302a840d180400b10228460f500200410004050005a103c030407003201130704c0348070b41c00c1124528044039405a203007000a141c40000807078650091803043c0c0c80c41c0c901c500028580800348504c070000d0006800440028041d42080c80004009002e81c5074080740038030001204525110000b08607010502c1000107042c1c40d0020302090042c00b6054030700500c03205058881400340c40300624010040718 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 11736904 1250 11735654 11735683
    0x506090f07080604080304110a090f02040f0902090a0902090607020a03120e0121020f04050303030702010606110d020a020906060403050a0c03020405070905010f0e0f0613140607020d080304050a02060705 89
    0x11000040b01c0318000f5402d8011600540a1071564980c0d031140310040300015203203a0000c81d0b4541c005424411407080f204900313020400103031070354200700a507a28203840c1e5100108a0307005021a80c40d95a032042076808590b60500c00503a40c103200c0020411501400c900030303500c014903140c000180440d9240c241003a1815a0b21400d14680c004e0042d01c0c421404414500c0d11160700c502071107a821194002c003803695000034481c0c1415034500c0042c2c03842d40201c1c1c0d541c005135100ca004000c501d4120302802070812442001d0082c08849000007503451445950281c4102140400704085882e082c007254007954110041d648404d0290619400e19030040c40101c1c000d80c5424006010b07a84a55800f2007910016500c40b00207003e641d00488115200c1d0861940c0454480000421a9511802807201d81010706145407503610b00a0016038000706034500034001c02e03007003100703100580d11000c10720703403043c2e010542ca0b031a03450341d0900c40d150064000000750840e80c006040e00c24060001001207016296 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 11738154 1250 11736904 11736913
    0x90914090d050703050a0c02030703060c0f090f05010203091e1206070e030304050d0f1b1202040f050405060f0c070501020a0c02030f0106180c1101110702150901050403021005070506090f 82
    0x2070100ea95115451001c0d0029600b031201281c494072074640070345804e000804845509840341c54520807100420f00010102e00120300001c02550040280e20041c5400188c0807100b51405002030740b2031090b02d840710321803010162101900d0a13070044964800d030000c4c095000c039441400b40ca690b0740d40140c8002001c40d992240c1801c2ca40380c00412141518000740901d204100d8944d039030b1029905800b801c1302c0a140059415030901d001d0344582e4002d000800a04049071668010700046403940144010700504200c01c010118030f000801d142c0080141a40007595529170410078031500030240d0050455000003010803d044d48030000c4201c840c000c034252a601000721300a02d01b220300340c2c0f1886800c00903200045400160a038003c1c41c105449040040740071084400d0682158050f41009010030b40c00f103400c8055040690590a504014550303070352405e8108800070b80280914440284204490b80c0c1d29a0340c1ca10400c02d50310b0f096840811a20b29042c00017525031141c45440000b43e46100707 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 11739404 1250 11738154 11738173
    0x20604020a0e040210120207060c02061509010b041509030501060e0f0c0313020f0105070c0f030b07081003060f0b060a030501081b22140c030108100608031909091409 73
    0x416003414040c3d54004c0c900003da040103002960010580980700110560900000001c1000390160610010580d40602803c6c6801c60031041d00108000845015032140300c0144451582c04003245c007582c07031540040350b0720030394a0406c4641024640000b011942440000580500150f04660080104582992040d0389030285c001da04e00044407460281c0d012a4032110242c2840702c92103450200606d4041d10300b05050f158404144c0785948054200d8030028810030030b2104642d40c441d00079025107808071650600300e0100c4101d0445000140585d60b0318032015041c41410703401916004000707806243c0354049404044c0041c482441840c0f0240a446010001d80030b0707001010308031342c400400149203180b405011003070200041c4a16070202d81d80d0081140e20200c0803402030301c00c4c54100d00ca15035960400701068142005118003d08150800b0f106002c10b800101c240c490941044989040c0e0300c1c800581203030641c565038003038592545491420008900c80e020418483c80410081b00d00051 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 11740654 1250 11739404 11739419
    0x414040b0607051c0302040504060806090d0305010509150a23011403010b040303030905010b03030c0d0306050102010618200c0703060e0a02150703020a02060a030b100804020a060e0a0801020a020604020a 89
    0x4030340540100703260481ca03400551321080300207010503644d0a00e00141400d807120082001c880b115003100144c6d90201d810001518410808a141d40c00246000d12207075241c203001c141074860180c04a161194061074944240d11201c2c3c28000619101c0c2460003141070f11080040f5400c4080c2d0928001750950010361054205982200d040b03401c0380301000d186c540b450310110000c10000300d0858255480c0c100c0000300e550100090300d1742042c008050810310140380381c05000c80311182e00c11411742e410b041040000c2191044164401039880381c021034416403280040880040b2580601620b0a000c921882003100008408081d81c2c0701d8042040088a5200101d60303c40c00d0003c001d60001c0c4e425410940340304070710b0140c580c01d48a07004842242c12940d00146203034118040b1000042e980b0049140700c2d1070000421400d1400b68200f5100300d06041d00400c420410600900042c0441040b5a000540b5a21414002001648021529200340c848029190041a10241d00c24040c0d00740215611 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 11741904 1250 11740654 11740657
    0x100501140f040905030f07050705030102070501060f090b010c020904030e0a0b03100609050a06050702130204060e0f040207030c0602130509010e04050c061809070507140d0917030306041109060414040b06 89
    0xf15003142c0150b0070b110031038030f0031200c9902031041282c05000d12440001c150700c00b40042d248062003200081106401c002507071142c1c200c00d50014200c28100000c203c21660000c0440d00c400340c050721030442e036585a0030292a4810710002c1c03680c00c9010720300300050700103d0f01d020307600803c412441c8542240ea1401c04840781e5201e801802c0d4040041d50f070400045018400408040c1e1002d000400d0314135120101d04c08a0300550301240200307440c4001d1451910303140c0030404414404803411420036085032002041c3c80d4103a40000c024544c00500b0b000118500108034008240007480c03d00c1a42c0c40e410301c00742240040d00c084903580b0030f11801c1203403071418400351503c01440310200c0700000c00c6841005590003001d440e85081c07142c1000440d0100743c010030090041980d62000308105520042d0040050301c131a41706003003200c0406045208080d02001b1650081411034000c10362200d17030402c1d000c0c00e02c12407100c1a13000c4000a00042d05000650100e50000307000c07201005400c0b00c490511225 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 11743154 1250 11741904 11741921
    0xf160201122007050f0d05040305010605010918050a022a060f130b07030204050402040602011a0312070f0503120f0108010c05030105090118111303200a030201050a02100501140f04 79
    0x301035a101c948402070440b0190050300c0c012011070b49441c0803094500c0c1001000704035000090700004042c018000700340a038100a000a20b86480070034540f142d0071781202c1402d03601004080c1c486020070450240b94064807403402c2420381d1150f42580740c030070700301e9265440b4072046024080c100005100400d016601407107000c240440c00003440266880340c01c013280040407001491350070f20001c606511130744080c02c0545001d4000050711032103c0d072800d00316002c0a040b41c1c03280d44411030441074000490705585000e80d04c03c2c15800c01c00c4d100d14015086000711241881e41c08020820841e840f203104032810304a0306090b008000d03a20ba02e00b81124144024011144c01c1146100100184400c2a4502c034074000704100010301c6020170018600182c0c0300407580c29040e80c0002c0305100741700e09151400510088580c901180e000140080703004c880152102905100d400710b500d8140034000c0c070901125000c0f400042003150784034000c254031001020f400b2405013814440d9400799041511030500f6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 11744404 1250 11743154 11743181
    0x1203120203060d0b09070e01030c031401111602030307080f070b07020a03020a0b04060b0d06020a03060806010503150705070f150501050303160b06011404080f06071707030507050f16020112 83
    0x4590300c0946800402e040c0207040220b040c841d01e1b0f0f00180c2102c603289105e000c0d40c0309806c05440e00d440d40c1415100301170803240a01c2c09034503105003900500c1034002280c010080c613450440c100b100030b00019045000c3c007c0d005e0b25031100002c40030344910304100100821481a84020790988603144103c2c2c0d038007030350000140984e0000306a0b80100b07503040b040551007882900c0c003080d820200300100e04011303020481116019000308000c2a5260540100f0024041106c014050740d0300d08800a903440749026030701e0f60b41c1c0d80014081042d45110720b00b1110060340050107510042002d2034140a6040400071603050240b9003000400d45140c080100d584140d4220381a030a04842c079129414040405020315045c005164010595018a100a00000d0160340082c02452501c055172900b0140002e0000341003050141183d903070250b88910702c94006a03d0315001400381d64805080d100340c440d40321040c0d40094041403403101c0702c643c50f14401e5120b00c01ea90304240b405110340801c042da001241d5064 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 11745654 1250 11744404 11744419
    0x60504060905010e0604091404020109050f010206010b180a030f11040903120b01031d0105010509010e04020105030403050d0612050303160306050607060b18090d020706050f0a050315040501120312020306 89
    0x140f03621814089403a604003c000a18141d40c904085044515042d2164140800c840401c0305560300701606a0082030141c035020058803070030000035200d2805004009070b02c0c0703000c038595520200700840c0c04d000040280403c05119243d0411100742d13100c01c84100c6145054901c2840c150809020b1184d0656064031000420090181b003c0090074121001504040d9259141e400c40b903c3c2807000070886c0c0b101c2d0000603855052800744110010160410840804804140b02c0180d07440421603500680515225880700a0030701810044c2c18a039101109075108490130f00c080c420044008c6001d0040b8044007032031003528035000d50076110f8901c10703107a11400c2844407601144c0240c00039107684030020151548104508088410b0941c15100072400350302280d914500f10b5010051280030f0034242c00d0140c14030b0703035524400c0a184030ba8002c0c507080003004400f00e4080b41056501d013615820050040c0300c030390703100c2d0000e912850541405800081e81104c8100c50200c480c42140c0c091500a028403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 11746904 1250 11745654 11745659
    0xf080309011e0e0604090902120d05070803040303140106030f05070206010305072108030903040f08031204030c020f15030702010b0a080c041e0e0706140306010e1201061a040f0605040609 82
    0x400c0c10b00c12040000080c4500700c8414801a07555900a01c00380c4920710001900074000e0040c030001c0c10350340041400c3e80e0700071918042400d03001001c0e55040f951040c280d90b966543c03440c00b2405050248400100c01102d80c00110b12150182c100c29140010084c003040315640307521003207941d000c0c09e2102800c00e0f00040c800707022201c0c80d4003814030746a100c40c0c2c0c0c0596003140c680c1c40340c80300e903c2110100d0300e6400100c0e052228000720f400c508000c1000100842c01e184040200440c0751387c010707000030248501c60214070110b4465103034080004000905440d40c0000d50151112240d10403101000154a0030000c14401c2c5052012001540d030700c2c01c001d0039400b00d001d080c000102403500c9942c0d101d4000c012101c034004514003d104450038200040c1140030300e020b6002c1d00e0300e00141c42641e0040d5040c4100700701a68000c0c0303402d1445804503080700f020005410114010506504040e40340c41d66042c0008262300c0b00c0700203100321002d1650145220ba6200c1080b11540228083c07a00000d5040004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 11748154 1250 11746904 11746937
    0x2010b0117090102041a0903061e060904060f1503060e0a030c150e030406050705010b010509090604090303020c1608060109050108060c0a0509040504060c08010503070605040b0318160f08030901 85
    0x7a944200c1d07100005140588842ca401c1c074003440c284512400007000a0b03010b6540c10140310458014507030344011148248446004424040d00500740e40c042c1c0300f40000038003800115040300584860b140b6040100d001018003009806115020640300c8a040070001c0c401c21030f0019000410541664074907800107410b41d10114041c02c600c6862180c15182c1c11a0113440b01c05000510003000c00e51602580d540c0305140c4242522224071005051000078402c000f42501c1d20b4004603030004048400254580341481c068009014145802203244158811889100800007400c02910895002c0b11083da07078540713034401610405d0003001d0080d00080c020a04001303816028041c1045141032250404001f035010030200c0341d086509854a81e101d1044903c600d030814449070150070107030701424000d0b0401e14050704911903032241d03e00c041800000251080b0384d40c0c9407400c401607005d081d15000207619a1207280002c050040141210780000002900700d400011584d503880c044e100c49a000f80d0700030760b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 11749404 1250 11748154 11748197
    0x10501050a030b0d020907020d030614060d020c01140a09020f040506031c0c06020703170a0902030601140607020604030501060501120b101110050c0309010b0d0206030c070f05010504061b02010b01 86
    0xe42d44e4114800c00c80103001a074484030345c10305c642020b60003403155601c0d0100c0242039401550015100801c2d41c002034019031508402c031283c41d148202c000d6503840049042900600d208002c004a60100300244500c0d0007803030f000743c108280200da813100d041d04550208401c84000ba0707006a4035034045c408041c070321070300024001002c46040c200b031441e1100c02c1e1034030390aa901c400411000202200101801c00c40400b4149402013000c08040049007100c0d400f00740c2d03070081030040340c1c10a0b0a4842051080d55290101c0c3d58407980601155116603892810714003a04540c0242c0b40030032a4903941444210f03072440b801d022480010303c0c1c40c1180c0200d15040c3c0317244200302d0040485004070742034501080c903d80511805190b071660215a0303031a1017401103086071801841e8521030b00d0b501c0e100001503507070501540c0d00090440d020a540311654580021090a8103200804550a250401c000e201450b13100303260140355002400c6000401913412030896000300310190216008002e001c0000c0300169 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 11750654 1250 11749404 11749421
    0x50402010504080a05100507020c0a0b091203040b030403140c07050d031e0908060709080c0906040e0604050d08010f03080d09020102030d0e060a0606050301060c06090302030702040c0314060603010501050a03 91
    0x1001d07071520303840d082c1c0c050134003803442d030180c0b1319030701c40a10b0809000f82441010360180c40d910150101186400000b004880b542c4102ca01d40e040100b20102c242d92041d4158503224031550849544070f640302c4151049420446044d4003280130640c18040260344d031400ca43c81c5113029070203070080314141010001038151201c4150100001d00a0301e10303424444480c5078048000c25100e10b000b00303103008640c41c5407100c020300040030401820320802c4500400900001e1001d0304584c1c038156562500c001c1002002c552040d01098440d98007840706014012400c1e410401c180e50301c0344041c0c0e0300c038007144040c08845d10004000d44400c005a81040f0269071114001c90303c144162890050740018200948584580c524a02e421107818400349140c41c0c4210310007003502d0b0030814119850035a020380110090080503040c291101049400c0500c01c0c01103c0c0700990040040024010000c0e0040061407010030485103c110000402c02c07500d8844143c80c100c2e80705035515480c2440e0150102e01910a40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 11751904 1250 11750654 11750657
    0x3120412080702040e01150503010b0102070603090f0503120a0c03140a09030908161d010503210d05010603020c19081b01060302030102030406020712090f0302091e01060f020c010305010f030605040201 88
    0x42c0144401a030b214000c0341800e01d03a000010580c043c0c103002180c445225903201e10321a030314010402482c1e9070003260060840e491820000360424030741c01c140d00a4201400010111301002034031614403280f20032440d0050001a800300709889030b260f0241c00f2034040d00d41100034040c1650000355200300d160403402105101c0d280c080d02069030f40c02a2403404241340394141d0300d5181c3e0340007405402c103c0005200800c0c800400d01e090f5500d440086625038034180e80713598071589041980054000810100d42071528044010009580e48200060083d0001c0c0c031400514000d013010008040b160b00058041540c110740d800c2d00c0c1a402031801c400703000c10030210354419522510008090780e820710246119a003c0c039030240e545c41d61843c1c40010240d40c80007103001e03c418030b00b091100c0303c8090000302c162541555800f21984440c44031021002d00e00109807034400d280400454403590100100b900078846408841c600420705005600b540c034240613480301030100620810104e03085030402500523006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 11753154 1250 11751904 11751907
    0xf0e150303190201020c10050f01030308040206070b07020607270605090a0806091b03070303050a0302030403030b030604051006063006050604030b0610050a0503060118080322050312041208 83
    0xc030542c0c0105550240095025035404694400101814800c900104d44142d8003001945000e1000100c51007060001400304005a800141113459800480f0b44031900310326031412a01e840d0748001d544460807182c980008242c600d1411100003543c1c1e100101e110b580c0c02c074403400390802030704a072590090341e250741e84070002c0b000006e01c0e50424402d290264030035a01610207020881306481c1c44040d5040340394040d0b805083c0820100381e001d070940c0d0302d1449500c0c0241c5e0fa9141c2c0c0c1011000350261100740ca5050148100f804201703d130014000509040d43e501c107124559860a040e80d00001c4280406440d28040c7c940440580040020001100444c1d00001d1420b0f00e90010800c641c0140d08100c8002c1030070000e20030580f800b22540140150289003582c5000c094a400811500028083d14140300503221041c1c00c001c50307442481c0c040c1c0718443c1142d0f20740c504800c9442904042503504501803400540c0443c450602040703803800b030100c0300390507480c0c00d01c0e0071712051030500070711410354001c0340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 11754404 1250 11753154 11753167
    0xd02060d0207140706020705030714010c1e0302010f020309070605070507080d0507150504020a090b0a0503010f0209011808121804090804030203150103170f0705010f05100f0e150303 80
    0x603407000e00304181c003c8440c00300480704107808510305120b0743c10400a55100c40c404011668000a403842600c6281d250f610741a8840c02c016030b14114003da00030070064514941e105101c2c0341c0c0148040080c0a83e00902c0703905907140c0b040d004c0b44003c0e581e41c1c840d5000401c1c2405801d002c3c0006003a214030800c100c94810340e80302030250501c00c141d4204400114000794840902c416011201841c1808000030400c41c01c150740008c0021455100b201215030b102c00c040c08a45e911aa0014014000603009104104e1070500c80d00080d03002076071140c04290907034001d201001c0420050000c3d10079032401040700c45a1500007030480e0300044d00c07117050981540c0c1e040c20f49071240c0c000d070f440d03803480f03a4492604c6904604c10542461030326407800c58803200c054010004a00313460040c0d100318800b6020326036607a94048001e802840343d02c0010b04250300f04803803010720a016034071540c852000c00d00c06a5040d9203600b404c440b4102184143c681d6450140c02194285184e212014106440202140d28010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 11755654 1250 11754404 11754427
    0x70b0f070c2d05030c06060901170616030902040507030f0e070e060411041211040507020303160f0c050304030b0105091b07060f0605090a06080f030c15060d0f0b010f060c0f020d0206 80
    0xa0205c200e0403500e800180c10f004080c284403030101d000d040c540e0204501035104074031072170741c442c030080940358130003040340012400364000e0707001d408019000f82c0300f4041c5142404000d8045c0c09201c3d2101c0f03183c2e15151002c240340d1400302e810380c10b654610300d0040d081c0d01e40104110152103950380d40404990108400034003440360640c00840345100b6010399170050304e00010001290801005d440a54000b08201720040360240390034070800000341003801811682c24000c4402c00704a40c0000d041d80301c0043c0110503c040c00e011541260802c860700300340da540c0c0c0d02031511056000985510005c40c28005140010794980240c14141d541038000a0416610380c006604814241c1d0749440f50fa982da5818000400d0500241c0c191a030180c4c000c6180ca601d040915030f660702c90b1a04141415150f002081d80e603030b94180c100d103c540d082048071040380036500f8090750003002817081105101c0000b200156a5000d400160300aa802450f5404103c200c2d8089c850014000f2608913400507040109030100f4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 11756904 1250 11755654 11755657
    0xb06030f18030a020601081207110909031b01090203010f02040312080a180305030603071406090103050a060801060303050a0906080105010c06020c0a0501020d0e06060a0803040312020c0303070b0f070c2d0503 91
    0x300000c4e402840c6a501d40841c1d181040d42600f0701e0707a0483c6080081d0800709540f01122003807414242c0c0c2c01121650384201c80c500758086c14510803a12440340c1d00750703450010150400c40d10340703008030001c2000080e4181c190003203100f280b00c001d1a14001003c40051039005140303c5500500c1580b000c00c2d2091100c80426101c00e00c03d07400c13008200c000c4103006c4541800c20002c00640551109000300504030000031700c850041d000e60300d0408d502c2c1e0340002d01603411078010a008201070b0000344580c40d00d0345400b5100e40c2120345c001d4001142e41c0e000180141c0b003020380c11304840040e1a5403c4d110150f403501d0004c0c0d4400c240785003903486086001e40005100748020400300c0000c1e0000103000c0d234a6a2200c3c00e1481c0a0109445a4000c0078284144c1101008582c204c9030b100c2d0308001d041000d0750303040e801d01c80e0b0722030b405526010224203002400102d4040700d00c00c4404104001280e95844015544000000b20151090300740d130300070380d83e500707400600c040b40612503800345c000701035a80c0e40d8540355 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 11758154 1250 11756904 11756917
    0x309050d0807110409110609031507090305060a060e04060207021c0c150c0b070e03070f0906060905060705070b0a0207050402040f0302010801120519020f090a0c02060105040b06030f1803 82
    0x81c410004440060001d442419040404102e60500c95803109480d000c1c801c000b01c01d030161059100040d5940d0b560340401c5441c00540c0e10082c4c20015203000d04016000d000c49210903515800360343d0006541d0140303803181c0c2c000c1d520703014140031168450b80c071000000c0d000850100d810a44100c494000f0003d5480c104610350710800050b07000b0380c1054200350b0fa100b0503880c40c40921041d000e089000a0002103181c3c0c0c0610146058441850a440081d107007490343da2160095103000400800c1072086a0400800e03203695440c1c92244076610300a0001911842801408541004038180141c100f46402000c01c501c0c0780c030454412540b1b8800107000c81e4000e620a60110701404810011035800115290041c21010701000303042840b611059142c0280104505070480c01c220b0320800c6513a809074a21200c03d02911004040c90402d0946c00244111011030b03000d4440e072400050745203010701070045040001342501d805c5840b05040d04c0e1007520054801040c400320700c45480943d600800c081c158 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 11759404 1250 11758154 11758163
    0xa110d0501051008071505090607050a080406050a02010506010807050306130e03040b0c0d0906121112040b07020610050105070615031b030b06090103080406110a02040204170c040608060708040309050d 88
    0x480a11303007100603103080c0d441e910200482054146200c240c130380050546540c480709490300ca940d40490714189041c9801d81c50000c0202101080114580d903100000d0b0480315003035002048940c844d20015100c141d003c4440d0307000610100700094050403c40464001450511408181c1c0401144000e00b16009900000303050000450021250700c4200300f800b43c2c4000904003100c1c00b40c1400001040803240300d880d00c80f2a46c40d80c10401498540340c007111b00d04840422103200c1420a85402520040141c03500030061080710302040301c07481d10300303003040032510705850b040c1c43c0042c9a91120041c0c407040b05405800036200760f0000106a68841c2c940c9400c00611401e4505400d601d00155585c03005000300d40500c82c0c2000500c00245020100d400ba61140c0c104890150581d18040c0e18052211800a4006001240c00994000d001c407020114898003c152500740600c0000c1c00200c80c1c051288910302d0b13204030b01143c2044d000f00c0a25130418042d05c0e00c080703156100d40103e282480204000c44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 11760654 1250 11759404 11759431
    0x510031d0309150415050a020304030210080a0b01020601150c05070e010608011e05030a1e020a0b0406020706020a0210030c050c030c0c010806010c15050a0e0f03070605070503090a110d050105 84
    0x2c40c03034114802c10030006606521400e1505091425101c880c54203c840c0c24800009107100301e5078006c0055800866000b044000095005040200114010b6880c080300f0780c14200d42200c030390300200707096050b2258004440c0480d002034004841e03c6040078000d45950180010119058550191082c0a4510707030700c660740c180d40340c24041c080c400201c2000504510003480c05210b03a42d008280b900301c1a4001640d80580b0180e00700070340d00d46809040095106583c000700194034201c850240c0202c1d611a003e0703c2c003d03551408c060b42c031840c1e542d600940c460004006c00519134026889840e8103121850281e09181c00070030003510350b038407030800300da41a80204a11300e00c035a484010a58000300a00e48124126015990302c04007020990f94900c2203526040002c1641c0c50707a601010060030003104980840c040088025160341c004101520401d041c8000030701030724000c0b0100c80c051194540102a2054207464009044d00742040d065070010105e03080c0004294240680703030003160f120003a0f1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 11761904 1250 11760654 11760667
    0xe0d0312020d05011707060207030c0306050a020405100e040c0203091f0509030607090801060501140d0c0e0a0e06030709090f03030b01031103010e070809010507020d030504060e0322080a0c0510031d03 88
    0x45d40b501c00c141d401030046600c000414000141101c410400300c0c1d9010340045421307100c0c48001c0c4081e00441c0c200c1c2da007040704080003500a0740c0c810400302145005540030004000ba44c00f080b42c80e4480c1d007400701c2c0c11141c441c100d0000c8204001c0794000d01c00c0c442c5020341c202101d0070b0001e810441d0a540040020f0050002485400020720514000304000d00746804186e01c00d40c5000e0032030040c203280c0311210b41e45200c4030a00d40e005401030066100c0044c031810351b4649544100619034402e558040c024400e0074030106480350f40340700c0c000b03e45801c074a82e83d12510301036904901a00d84042c540741055220000582e41000e4040034601825044641d0036451400300c0000b403c500005040302c5060303040030300b807000240c3c001c075090948509500c0c01007844d075202d0405030050170201401c01d91724840092028443e00014912a0358024207582c0e415940740d80b400500c1d40d0314402040a483c0c40d100d020100414a00107081944001d89801c010a5807800440360403206407850668409030382000a64 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 11763154 1250 11761904 11761949
    0x6030b040b040c06090e040b180d02160b07030e09090c0402031305060a0b0a05040b0f030a03050a110a0201021018050106031203290913080c030a0e010e0d0312020d0501 74
    0x303200c05440316245c07600d141031400e03181e1800000040e101928501d019000b00b4441d4040301c4240c0308248414045548003550903000039615041000403140b20781c411000880c3c504a010101d9091a4140d583e0780000c25000042190303894010340285035034444c48000096644850000c0c42c482c4a0304622600214081e050803414800002c08a00c051450101d8000190740c4410b030081c20b903071095400140d9507180b4400305041e004c0c5288050b45c94810400c43d0030030161702400a22140c0c820381c2c0c5040780c251400c41c0842c3daa801e2040020302603080014564603008642d44002c00d40112007410950135071841d00c0d100d0031035455403c2035400b551a1089030070b0b0030307416002c1d0040060079400350803000020040041107000340700c01060b1003030301d410002c0f070a044414440c07003d000b81c03c40070860351241d141074600e980341c2c025000700c80460482080d003007072076015084103111140c0107400010403e040750303000c030781c1c9803002c2000210550b42845040700024041c400e440c064261740c1a00d84c46c0c1440da944 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 11764404 1250 11763154 11763173
    0x70308090307020a0e06030c041103040201020c030a030903060209060403150902040501050d050a11010c0209090a02010e010503070f08040618060603060f090203030d1104030b1303170106140c0106030b040b04 91
    0x100e01400c1e4810001c4070010b0710380c6520002100e2105810040325201d441c000f80c00d12101b9400c982c2d00134182070880c404a01c03504001c60065100340c08a540c0074030110249916034800d44400360120b07440403410000b241c016001000d00260080029240544940d100d0111044001220007071310394030300005003141440c0c0300301c601400048030300091079030481d030b07840780e0b54a0b10641c0144070002c40c0080c48440e9000b40d02d0304042d598020828000c518160102c19502c4218660584c0043c4050394600d005501a000700e038001c42d169030f038a003221450390b102130307030307005e101600c1154555620400c00608038001d0030300300743c03840c860100410341e14514141141501c0b05200805181d81c130b45104000180e030000129070368240102c80204040c807451444540301c0c01107a1014105003100c00400c69041290740107245a42d102e515803c8041c0842d610443e10014240600d0001c0350f82d11540e40700c60045000078008801c2100004202c080d140ea650b030320981000e6070308584030364414050008002c1c0c2c100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 11765654 1250 11764404 11764411
    0x1b0807020a32091005122e060b090d0f05100f0b03010b040b0f130f09060603020102010e1c270602060612061b0c010b030a0b150d02030304051203120c070308 69
    0x80f43c1e0703905403c008030704030007070800d500c152803144071525010a0030f60802d01c6404140d001c0407204400040b4484104400307150610904d00c0c025190860100c2c02062001c1660a00c0e030020306507082c0f4980c150360348007a54203103200c140d0300f5103d510034101c0b940b402800b90401410f81480081240d20590f0181408d44441d5414284200d0418050394100e0f101c0010780c4444400c11162201d5003180411620010301c0c8014084000505140c9640280203264100c00f0459100380d0080010585130b2002645400711301409003400c603081c510000c2c815200381d580c0000303010302c001e20343ea40c4800380d02040d1840069a0007000582c1000c4200310a901d044111a01010fa40d03102030061480c060000140b5401800a21300a400d404200100549800d502c52460500094221146589542881a5901411105a00000c003e0320005059080c1011200202035010380114186070402e0304004d0608002d000043c8184410300401e22840c402880c02c46c00ba904a1044c1c40d07a8920f2400c00038903144009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 11766904 1250 11765654 11765659
    0x3072a060c0215030c04120b0105151903020d0b0a0e0106110304080303010b030406090f0605040c0803040b03010308071a1005180906160306080d080a0501061b0807020a32 75
    0x200411405070703c0c0e0901c140c1d02581d4804907141d50f0b0355001201801170069401c505080c02606069008014202e041907060b10b800b19080c00c11070307000b41c0880c0198841c0d0701c1e0085515004500d0544224000c0e00076155098108401242c2c040412020845605141d0300814400681c4d000401407a50001414001c41181902842c5414203001c0d115a6921061213400702841c40000014107020f2160320001040e94040701c04104161541011005820265000d441c0308901c0c4000042c8404000304807000c8820a4041c181981e00e075440300c19998000c46019104140382c413142031415190101e0840c0300380b9135145810101c40c1080e0a0003003150030380005040750302040c4140107658200041722540030b00003020300081e010740d020048002d0802580b083c00280b15010082c0d0820745c21200d42c602c110609841002180c3c2d858508991b03420034580c12944000c0c49550714ac021498500007000c080e070002c2c0004401990352040120f00344030a55008140c18552140b494250a010300e1010902204 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 11768154 1250 11766904 11766917
    0x5090c07020307060804020a0f0303050c0606061606050c0903060c0301030303050a02070209010510021204060507020118030c0e0408070210030c020609010b0310020706060905040302010603030206010f0b0f03070203072a06 97
    0x150340403e50740e00040c040c940c140894003000400311356900b10400041d04407124501c403200d41c1ca18000c0c1058010204a484074002d041c0056928280107081e141324984011031558000841d80300d950003404042c1603201d644a003002034095a0302c04002c118041d08807680581d5a942c558240107086500280404890600400070b540241c2c1d00c408003581990b204644104451106140a07450001000e6035803201420219000034041d800c4000b40040c64001e80350038841c1d550140d07802541c40140e0200814000c102e07101407009480d0018019401f6200d60070a516041107071300011035030b818208104000a0b1503c4507201e409034140700842d041311800d002804544040300c0080e072a0020b01214040d5a41d002c6504410702c40c160b04103000500c18075800b0410703820181002400303400306020542c00b5101d10300002600c040900842422107401817a00c03030505808030002e240940c00a408807046100c00d2160a000c100002c152007203410000f0000d4030702a403030014681201856078001c8060251 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 11769404 1250 11768154 11768167
    0x60a02070206031501021f0c0909050405030a030c11010e0a0c080109021014070f050604050105071403010504090804050310060315020405060d0504020a15020f0105010e0402010507030806010e04090c05090c 90
    0x942c6000c2d660007030300c0e8020310b085049103000100e10384158010300c00c0d541030300d00415060a584a601032a01e1700c50b0340ea034510320513854550b250103440d410f030f40082582c2c2c820043d17001c20034402e40c0441001805403500340c030100340d886482070075100500c603228055001441c0314010007102501403001031801000070720141c0501c0e0000703040b502c40f00c2480002c1c41410b410007400c0074a00da0071202d0031507200714250318899403420000c0e62041300b114121195842d100100302440d0048010200d20495400007234a9a800c00003400054606420209c51260090002084554080c40055003800301c1420000f4004d1a43c144000390104105030801c01d944100814030085d00c1d90f00440d5244024084080307495180d500c0402d00805003903003d00e00359100e1842038455242d000c10030310300800c9004c00900c2907980314001815210b405890003030109404000c10000640030304016030340b10105040c008900800400402c00340c46c01e00404558010764810207102d140341c4100c6040e00310105c40c4074203040c41c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 11770654 1250 11769404 11769409
    0x709080307021504080f07030506060d02031c0903060204081b01050c100209030708010c02030c150f01030b07030e01111e030106091208040306020d05180a0201080721090b010305060a020702 83
    0x7003540e00203030081030016941400030865034200c5004043c540111000b0340d40b134000890b216034403408122114042c50001c1075941c0b4144441c40055900140540b0400d45810113640b00742903900703540001c0c013440000000c007090081c405030000b080340d0800361101c48400c40800200d950100e90040c1484014045501d00150009090202a0700d064005030394140c00b0000a1170582168006d1009600f0000c186280c00c2d0b01102405404105c241210240c416070b007e5003c5040f003c44420f583e29181c02c0040010500f1001d00c1c0e60441d0080c00c0020350b2002c070030340c501c1c2540c08450801062020001d00c2c11015032100a05c0713842204103d070390300d00319411b001d0020550b5070640315006079a8014841d56040c400540d086070011540b00204555036580e40c0506405818110b03501000038595600054440e80c022421500d0194160343d10000395a0741213040d10040e0303104c58070030765006900d404000150b802d40f14403244203019607540c002940c51071030500d181001c000c0020515500601c4802d0041c1c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 11771904 1250 11770654 11770657
    0x10020309011b06020304060603150203090a0201050a1106041101020f07050a030f150f090c0905060f0402160f050a0b0601020304060507290a0506030c0d020604091112190507090803 79
    0x34142480d005241e02c04100051400c0e5104607406451940b00006000030030103664400380c100d074452401100f40c40c2040902004a0100701c800448a030082c0303500100542c4207000400d00d0450300d0400e108070340b122140040c40e02c001281d046540700544800c1c082d00350380402000c2c603140300010003000903500b410041400445580b200a00c5811407002103010405181c02d4048604025203080280744e140c4603c00c000b406000405844c00d11a005010801a1586c01214420349026103207a501c11059000d102c020761141602e003880030200010701d000282d641e28811030050241006044503403480c24000f2120390050909030543d40200000c009240e0401c0a60341c0268020b072101007940d001e084165a4281c40e259a109203036007030010402602a40e0b40814090001076045a4624103c0014821400040c8401950040701403208100414040c0c000108102200310040d0030702060b0039807480380d00c1c001d5501084200c0b44002d03007050000307544107076039010140f49810b01c0e03218039010720300307407603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 11773154 1250 11771904 11771917
    0x3010b030c1f03020c150a060b0306030303040201080a061a070c0f0509070513260105060109050a140d0f05030a020606030303010b0a08070c1506080606040e060c030a1104170c100203 80
    0x84420114810458000c0e03060322070f404a030798180c0700c040054059281d4815011204910103d2420002003102030640040e01d03c92f2801600039407550700c86400544507104020040442c01da2103240101d420306000903c10740100c0f2000c8201d849810510706210884030507040b8801007464a501006a0ba4480ca4072682244081c127003581e640e08249058440c2d171a00d0f800020900c01d8916490000342120f52880e0b0090101200070492a11070000440d1820700500ca05540000c800005110b01d4180f68a10345c070004c001080108218290740ea0000355000d0210155000e81000c64041101901480503591100c0100c01441c6598140011502a030003610580b50800126200058805002c1c0e0a95041a41c0144c440c1c454640c1590200c1c5c003419240c01042010700500002c1201410280100c2d104688450007030700b100c1c4d540c0c415042440d040140904011500c1c1c041c541d60103036408005101a213120806005800400100c0701c1ca80340314dd13030304d2600a0203c10070245245a021096580 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 11774404 1250 11773154 11773189
    0x503010b0d06050d0b0108010c090b03010504020d09120e0a0e0106020d030209030a0506010f090b0607021302030603031b0c0405070c05151e010b0307030b030f0303040b070c050d0e03010b030c 84
    0x115082502003201c0140010f4201c5034000c81c6090103e8203010079011202e0488800300c000340038505d1003400071600790ba52480360020b00013041c0018482440c0940250070031106110340000c0d4003542e600e5803680062260410300120300015420601410709a40c15409400616104000c652604000075620500107100c070080660114401c0341964091140700c910341d40000c126005961100880f01e460b1000e442808513580c60702c50084642e040c05020351725040e400a00650300380c81302c0000d841c0603610060134141d00d40010030011100a1243d01e4142c80d5840501c01801c4440c2e00d41d05010465402030410011b000f091504072001501c00600c004c40c81040c0400000d8640711010030060441c2580310555420b08558004501c04140001a61084443e41da007440030079246d0007819207030301e1039488074800c03034108100041c0407400380b5200d250480c043e0300d801c06008a994580768103042e44014803000241081c0b0030044d140c54240110a03001d02c0440c0a400e54100c0100084c0030b5400354400c000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 11775654 1250 11774404 11774407
    0x3030b10090303120e03030f0f010501020f0a02040c180902040302030709051306090309092f04030f0305030705090616051501050a060806030102090a0e01031202030a0f0513030c090609110a0503010b 87
    0x2ca080d48035170801d110440c02c42c022030b03072241000918085001012903044045c400c10200001d00e43d031000405120304503000d030242ca040c00058092001421550001c40d080c002e9004242084201d00d00342c02d00241280800103848608500c10142484e00981c0890b00d00c074100020300000b8215103c40b60b80c8554844000588460146410b448240341e075400ec0c002c3e1032820304a62070340a9000340d085040081e5034803c44400342a90040401405140809411703000d404200d0400a80120010742c0c100702103040150802540c5000100e95900462081542548882c5c1e0300007081230800520414400c100f13488442c0b5030415021a2804415209485c10800188007046450301e003941120308003000a05144059a200c9142a1070780741c0a200032a4410138a400e110041031003c410303101442c43e507a80d1204205e10070b420454164019004a00748100c200600100156007a9032220080892080106a880c0340000090031280e4030050000301d2241001a20002e42d888000c03241502c2d0010445c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 11776904 1250 11775654 11775677
    0x30c0a09050306010f030215030405191e080a0201051b0a0c061d0102030f0a0212011412010c08010807060c0210080c04031202100b0f0a0509060d0503040f0303030b10090303 76
    0x31640d10506500858050080000224290080b03000700d4044d28002d6900501c035040101c01840288411100074000c0c0e0040d015240000304c8000f20f01d5501c0d8003c03902012554203403e0034070100c1d00d00030402c840070100098103044658080c00341c540d0026808201e441409034400b8202000e108442c40c16040046070302c001c1c400c10134180d02011010a40700300b80300c02c10344080c150a00075841592008041c6003072800040300705803180216080d40c0000040300e2302d164681244000015294464181d03c014540e04014040800f403085194511955440da07901d9454503200368280300d184c1c1c00544c10040c2d585c143c140943c4590b240c0201803005031404c54460707602d03e0308000c01400b0315000280540c0c5114a00b1400c40d500054060104038901c4080004054140420414250b104143e42c0c014004d181c0070003051515aa40341d5114802500f0385019603c140e9500d0700b150f0181e08802e00c0c5400c000c8044c41450340c10720444448140c242c5212080c402d000c0d9021b0140407080c80000c1c100316029148 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 11778154 1250 11776904 11776907
    0x20c01180e0a0207060b15120613090c050111150121080a0509030c2b05010e0307201912080f04090c03050a020301060905190e01060c0302010501060f05030c0a 70
    0x28503419032a5441800e042c200c9801a41c0709002c1543d4807030030b003d403d81c6c030f80c034051600030008180d8200880c604000250849420304c0002c05681e800825030802926401035801544021031081a80d07a01c45400d201c00509100005100080d0580c0500c0421403852844403100b81901c0041c02640c003941144116051011190003008224501c0400d4841100d0b4000010300b080300c10031415205052492018050360b801500500e140206a4810b100e0a4100100c082c140345801340b000800d40b40441c0008a02d550f022031812a504105020494608a6584001085194210b403000382c48441c90303250380708150b81030151380505d0088000b1041002940360403039528002d007015654403590b4520482c0c008020b190380c00404039003458005890925240300b01c84c1030b1402c03500c4040a10341402d00341302d4130307644075208441074002c005d00210340c10085a000e940200f02d20360b911461040103180c02802c1d5070301a8014000e0055a1040c4c00b22039800006aa0740840e0307404030940c0f1403840d03100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 11779404 1250 11778154 11778197
    0x10516050702040b030d020f01050a0b06070803060102010605090910061509030308090304080a11040b0f0619050c01020408010605011701060206010506090103090c0e0901060803031302090c07140c12010507020c01 93
    0x15040e900d4030608030b807941007c1e004212507070303143c4481008005607520301000350155088402520351109042082030300140e41ca402664000f40c06100010b465612000481c168201c1030790138000f5948003204650300780340580202400780c000c44c80c501c0098230810300040c100c45e065020040a000c594000940000d0b403c009450091071210201ca0710000981000a01011011100390042d0f003001620801400c001802115440c0c01500b40d500e4052501090800304140c0100c900403c0010084904030203400d0015102034851040009002450403001500500603050850b8407801000c004000513600406c1e041d04441081e90160b0f961140d000049006001180c4028006550204041400c426060035140f10313400840003080240c2c0c0310441540d4a00040300e1350303d03103054660311110041c108039022580040941005034185600c0e6543c00c48100880c40c415007165008070008200c52524018122080c440800200000d091070f220080d120990006410305110400d907a98014124404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 11780654 1250 11779404 11779421
    0x304020907230904060b0a090905060d020307090e0d090f050103020a030e01020a08060f010c05060a02070203010605090c070303140603060402010c05033009030406020a030f0203040e070302030a0e01051605070204 93
    0x40074242240c003082e460b90203801281145026074942600490525000d400722039403c400c2da00c441e1002c40c039001d00070001d03003030040c03080b900302161a12640c01070300c0802004002d40207042010800840005c14a8500003000c2c12001c1005806d2008010044c0e43c094406c4c107480f001e10303025960740311801064000d04480000c85d8099031000070840c4140c2d510400c00d5001e010112070b0b2440c01010040112940f41611901510941241001c5141400194000c1a05620142c004940f481d610360019200d001c0c11142d5180c44a00003940d03030201540b510448034010940e0011801604100003c241d43d064010030003030600640b04440c1003480402c00607548503c6622440b0141018000700c1d41c00c1c0700705403441341e25031201600c01281407008007006a5007603800319401071012a207681c804684a070034045e40181540010880070a08800d0001c2c2288140540c0c0c40141e40c82c206603107140112188801c4486076640341c403040c803800d2b0780e010302c4d042c059540a00d01075480d492180000303402001200f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 11781904 1250 11780654 11780687
    0x30b04020f040315050106140d0e0f0f030301060e010c0b0402010302030a1e0b030610030201080417190804110904020105040519170f060f040302030703030903050c06010803040906060905060304020907 88
    0x21400101304600d409007940002c5044000340800d1344d0f12074040d900031f106225402d00c4c0010500c05100c5520080c0d2100189010003000c83d54a0301e4440003071814002c010180300c52a030800001409034941011050085135400e02e010286d6000a48441d4a88035000d08000e04241d00080490100c0121b50000941c840f00f00100c1442079012183d200002e100e80c10003503000b4002d40380010008140000e000c02201d070180c44006003581e8542d92030b108c150b41e000d00300036085001d0241c082e0030708603a68065128041394a5500303407401c00741040050301031800c482c14816403680d4200f01c01070340c1c0001960202d50098620f140048249140040701e015183c1012040380340c0d00302080c9800b98002100b900c0600c13140190b43c2c1a85400c0070070441c1c0101200c0250143e4801c0000c81c0c0024441e50050750f2080c000c1c60700724103003815000b0440c28a03400780d00840c41ca500101d424041130b101481500c004225500701032042070300d0f002c0841c04034003005101a118000240010f21240e000f5209903c0f6000e21 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 11783154 1250 11781904 11781907
    0x1c0209040c0201020406030609090503040b09010203071203091a07090b0c0304080303090106090b060c07050f06090301090b07030e0c010e0f0103060b040303081e06030c04090201021207030c110402040b0406030b04020f 95
    0x164507000703000f034200d84103c2d4002801d00e6000540d5102ca40304080040d83c102000d10f02c0c0c04e0500d49814000d5029204050452000b0411240402d0344e107450704011024940c2c1c08108807007681407450102c2c1d07109091032045c180d86000c0c083d83c40d0b0045201421a10522405516a44815103140c00c40c042c07980602d40d54000002081040181035218000380c8040c008200f040703069030320500c44180545803200c01a40c0c03144005000d6890004803000004400803c0c441c41c248040011a01b9503143c000100e41d03101400040c801002e815005030000010a00010050b405510340020700e10141a10450b000e9a0b4010150070f159200360807210142c94210541569666a4a0002d0100104686030007240c1103640c00c1c0443c0086c400760140c01410003c000384140704420040000410300b020080f4150321407042c90454488001000c0c002c5c1c24020740340c40c0c01d0f007074060038a404071b0300142090303903c0740d4030400051042d901c1800a039001c0c4c0d141c0d131400040015210011600901c00c3d0304034900030140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 11784404 1250 11783154 11783171
    0xc19110a030809100c020603040803060d0804060c140c0307050607080408030a090602010b0105030105010e120c04050c0d050109050405060f0c04123801050d05010204030206030c0301060807020a0302031c020904 92
    0x1410b006000503041541c0704030412071913541c11140078042c600000d600c40020000b03d03012813200c0e0051900814005d145d0401ca4040d0341d07a020b0141d00035440032003c15049482142400703690704203601c0a108060103810181c1840002135143c20300b40c004d55100d250081209010b00000200303640161081e4800c0307a64603114810003600140070351007100011360801020085551154041c2c904031541a11154040c01070f617001c0094000103081c4c4c104040c4900f000c00390b00b5640c1c90003264012010404401d47d1022841000402e81d2070580280c10050b0170001403000084c0001a45d80c4e10425001040041da122002c022500f4031590b1b210601c094a02c04011040c4040c900c6140021a03c00105642182c0c13a60343b50442c0051100c84886045c548100420050424a0965011600c075030001890b00c0e440b0782c0012016001992140c1303a03040088014024103400031803564028000d80010640390308a039500079500d218120b26208540d4599070a032000110580549280c5003009009221458 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 11785654 1250 11784404 11784413
    0x3050108060a090c0e040305070f0803011e0f06080403021006060203030106030509061603020c07050402030406050103050118050604020f0114030f04030909060b0712021203090708060a020c19110a03 87
    0x110a01500340c40d07004040200307014402512810140d194403c00310540c0b1440d0482c0d41d203408000034419011300c0300410460b0002080010005c2801c2d1151500c145c0300d504040d01a0b01c2c440c01468110051480c0701014007012640796840000c8030301a01d044007a07a6075a01d8101d0034061528180710000e801d048010480e03503004005141a58401d07941040103543d408102e50b6a980306480c1e0100c0b07007241d0403d034044507200390014044074411504540c10b441d580c43c0410100e038805c070380566145950f00d0050042240a0007540301d8000c03d00c41000700f00c03105484a0742c4806011304001d110303807513624030042c59074001d6421a04124076030751003d8503441c0800715070090038400c03181100060400040460a2101c47c4a6403041d40c00c14002681409040d6941c580e0340f484072038898007984140c50440c05603c01382030045126220210140114501d069489840c10001516440b01d40740103100c1000031b44d07000908008564440e01c3c0c034541000c15400c100c440c40c041030045a8002e41c43e95008028003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 11786904 1250 11785654 11785661
    0x30708040605060609010e010e0a15020c0f0607020306150d0807050109030f020609030d0905010e0a03120e120f0306040905010f0207030207050a0f0e07021603030c0201030507090503060c16050d03 86
    0x100d01030341040c0503c2d902c40d800c1240134400d035101940822611140e0180300d522819035031704c902002a04100c0b480381c4400c20f4154076a84a40714900503481420154190f061000d440e1280050a68844e4140306240c0d00180c0c0f0385c0001030461800076848181d02906550f008048214180c000945641e1003540c0e082c964043d1900e400242c01117022202ca94903001e00c002070040c810380081014600b082c6203411038601810300d00505030f8856480d604a502011028000000c2d000e129842d51038a038424030b80c04000341d505a511041e16608103401c044541440031040386d001540c4039481680e01d5480800080c020700b2401d0018080e58a0003103013190341d4185070b0050050078000d030200d44020b41d407403081014110709801944045c0b40500410481000340d841040d0b000310503401640c0c1d180f072181c1403d0022000703030f5000764001000480e8000955030188201900040751b4a803030403506082c1408280d803100302822a20ba55200040d00703015907000d04800710606980101a41d440e0080d820004014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 11788154 1250 11786904 11786911
    0x90a020a030305090f09010503030405040b0604050910081501060e012d0806180105060702060313051c0306050303030402030c09100911030402030601060f0e0411040b0c061602031e07060b0303030708 87
    0x1780036010000519442c4c100700060482c0e4000340294074090816080c40064505000d615810110034000800c440c0e9800c51000d214035026030100d003085107004981482c08c640380ea80880d82402042c01400007681c0010b402084100a00f89000070741070040701000000206800c00095068034103030701011076881080070b402030000300c4102c04010b821142d03843e08c20700d080c450030703511003020080c070401420710304041c5521280701010300c4013004071915154102410800d2044522014150210b0780d0340e054818034024000a50080d811454140e011a40d64074803208968459140e07070f00051020401c1c40711103005031440290030300c046000c400c002c04441d00b080c1c0b01280301c0d004480000c1180c40c854040d07035098600b10399070b1680e254051000c1c4001003c0044010300c135074404210124a080f06c00b8002c0890fa03044c0001000240782c014060481481011745210841d0002c1003d41842c0180d0000e01149102e451080d80c0d440c86585880d500800aa2810f00d40501010041010b0540c00c003480912 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 11789404 1250 11788154 11788159
    0x203070905030c0303090d0f02031207050105040b010f0b0319110403030c06060504020a050d050402060409050702030307020d02030307021e0c1801090b0607171b100902190617090a020a03030509 85
    0x340f89214010103489005408119410140c070400300000b04243c540303841080b5002070b0a5452100c0c2c900103482c082d510090301a2030985d1114140400c002184070a207005080c8100302d1014541000003045051002620311000000058100854610340ba07004184080c601852075031703510750b02e1801806120451a0680e2140e160010000c0c442c2894000c54448205076651585442d04c03508003900180800f41042c2d0700440705001c041482c2c007140c0f1950f8024500d940055031a4605200028645841090980211740060060100d0315800003a0742100101e403d111001d41c1086003407440c134001d40d00301040d500014071910070780d0051a0b0f1000d907050b01c1d4a04024080d0700a90010f00a41d440f03068001400e58020b001070500c80000c00c00900b200d08450b5000402d1180d40e0086107142c05950402041344070b603a001000b0862500c144107004080d224104403c00b40e20b03001c0081d02486894414180d0280d80c0c0f000038840809c1400540d0035581d00400c8171003040d450342401880342d080300d0800350 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 11790654 1250 11789404 11789413
    0x102151303081e0105150906030703050906060d0201021903030b0306040819091508090a140c030d11030301030b040c0b040609050907020f0a080f0c0102040306020c12250c0801020307090503 83
    0x607214101007009580c42e80f10840c5240442c0d1800c0300344810900341001d5207500210500600c0c0003035540c5030040d07020305455503001c0350504094121070704041c0c1c041c00042c0704000a122090040c0d13004518194441c201c1d09e484030540207a8101540070700580180e1030341c5801560100020810040050308211104640703179840f054807e0b0080e5800071141c000e44c20422003090105c0b40701c901c40c00290f507005007040180e44000c0700c0f6036a180e075103c000c00070a06203500100c0820314941020400c035204c4640c580fa26081203001c1e842c01c0d5072603200c18040541401280e07000a800d001506140348000c0000e446940d03a0703243da507007008042e0b0b0010f01849114218940200d0032041c03001a04084a80c0d040006d420031001c10780c1c60450543c089662041c42c014140202c0190381c5081c80900002d40c004c50005d6a2004500f1510741803401684c0c40050b56941440146644102c43c020f40300280d03404030a00311541d006040800300300c400303a404030400e98000800c102410784d00c1008007048480550454 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 11791904 1250 11790654 11790661
    0x306130207050102071e08030a0507050d0e07031203090201080402040f0216060c0914100806030f03040e0f06010809030f03040303090605070c0515070e01080a060909051b04090f03050306010215130308 88
    0x2546c070414243d04c083c1c2030301014008071700c0b605c506600c80f58208103241041890103a0201c0314005030f500710f103008007407a0400381081003442981c00074803000d2440351500700611409580060102c03139011348080d0090341c2d1500c1800c00d030180740d81280c1c00700301004143c2c00842003034604000905000101c240000d400d040700000e801803820141000800c0080010140540345403046501c890020316040d070500c00c0d20300350f0908900a10051025200502d003240742490100c5403100303018009400d190402c002d005c10040107040210076980300594242c000c556940b03903400c04030040d155414010f00541c3c5040b051040b407130740004800310f07818440e40690300d900c85400c00d600d15081003164203101040514580c01110340c880c079101a4409001c0000050060321444280f0494a12060407507145d4013031a91100c04640d183c46134440340710101c40520902800783d6404203600501301008040c4280480801d185a000307008402204800340d0700d445092030502412802200f0445041c0d000c00c0a02012 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 11793154 1250 11791904 11791943
    0x20c030c03030130150b04140709030501050f041208040f06020d090303050f06090601032408030c06090708030906180d150b030303010f03020105090a03082701030b0a0605030613020705010207 84
    0x4081c0f0403508061007648110304503044a01601c0d03d49203096115036901208c0001503070344000903016101503690742000f1400e45c41d000742159406010681609103100c10400040c400d18039602e403010b01071170002ca498940b23103025804281581d000070450360002c1080210b0010342c0e849000f94901965041c0640e4403480119000c140003030711080d0b0005050400a50700f035000342c1142e00d100035040c0411185400b440341e040c40d0f12a141c0c00c0309150307800008004180c214200f040f160040c000308007401b622817030024020351300d11540f03900c1130080c4804504c0c0401e05017016002c001860300a041c0c091840140e142581108100030741110002d80b07080c0860340e85080c0041580c1c103840201c8500070103242903800546081e0440341300e241d4442d200c4c6c0307008400103084501a11041c0c131140101c4542c038a4050781d00504188950780c4904061910000010581c0d5891113401221500c2c1000da5507500e07200c0200b2150b90f0703040e03500c00c40240002180c0040210540c000c0c1a003a014003d04042401c18440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 11794404 1250 11793154 11793239
    0x70b1c1b080a02030601090302030109050604060b0a181d0d0207090c0e03030301090e0a0f050d12050f0a0e120c07050406050402090d06050903090d0308040b150d0303020c030c030301 80
    0x503500001501d40e00099800304450b801107403c494141004c1d0902d540d00d6000070300303403400ca000407900c03034206030144401c01a240c06881035000086542c0e4035818107003d0804101c02c0403240d030381e80743e6441c9c00c2c141e0001b01d4aa012b03c6961800745094a0103110072910180da04c07007192003175040d5603103001600d400040c4911500408000010082c500d50791a081c1d100e03006c1c24801400350303440c0c01031840c0d40001810001119100d14400c1d000b402c0c50a0f105440070b480041008060390a1034141001c102c40200307a00740c5244c1c801c42d0004005400d00350400654600340018000201250000603490f10f01c0e0b40010b407d00032148111800d0042c0358407201800241e010f0010207940011945c181741d0300152841e0003244c1d0008035202220304008041000400c0000426025401314841d1018042405288030046900c200468091324100c8900004588203001051028040540c0422840c3c1040020700c216180070556008603501c0e9615010100382550704100440d01c208145511010304034074400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 11795654 1250 11794404 11794451
    0x2010204060e040f150f080c010305040c050d0510020c0309041a011407061b050301051903030906050c1c030b03100509030414040b0301051501030b010e0a05040905070b1c 75
    0xb40d400c40c0715a42c0000b480302400308800015101e507203400c83c10b1004558400b64000600d64003140303030541c51809600d1400c0121800b4102c0c105401d000c05c000214644920031412520162003845450142c0c2c02d0542c00c0582d44c6241078015800014001c010780c0d00040600401c480c12142000305564404d0543c01031101d00143c81d003c14010130600c660715140c0009002680d006a102148010b1720200d450718400d601426000840e03800b100611580c1441c50624284040c541820420306007951030142011503c0d2045204011000a14607841d4a00303028103800f6084c1d046400343c0440c0c002c0c4018010704690440c650080c070880810100a6031640261406070408501a40c5071500f0100a0700c0d0400c105402c403134016480c0e44405849440c02d1141501c64a042502c81c1400240e4100060542d00107164003410072404941c1051141d450980e9481190821140041d1002c5141780c45410151107501910942c00f0200e1030b076142001c1c2003154501024040e1082004d041340840c4604000e1080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 11796904 1250 11795654 11795657
    0x10050c0a080f040b040303080403030c03150b0d0b030a0b0103021c11010c0204020705060405060604060909080405040e0a020a031103060a020a0507020d11030109080c0606011103180409140313060201020406 90
    0x64010004100070100400031212110116482c3c1601c4451a03032281d44076500880001c0e689404100c24186e043c492215025140e03c1c040c0540602c805880b0720f203015034054010442c10004014000b0b07000b07540b100b0034038880030342560300f024801d090500c0d4a841c00d00c000c0e401f810301c100f007251501020070f650001c000e82c0172100d452000307040c03001100e180c1038001080782c011390700700800001b040e0100701daa8450740c0f0440084c0342d540b074003800344000e40d000755105c0c10302d1500306000340c03000801c00340c02e0701c058410503a00003640c1c981b040940b9290198140000c0c0d007140e110040071050000494800782c09500640858120783c80b40103002c4102e20802001e000010b074240078590041c0361003020015201d0080c4800000d0510010002c0e084500910086170720102c002006509003e00380300700e507442070003401c140305080c0d40a0740b500d40f6441040002c0c50446100a9128072543c1c07a43d010301082600300000500c0028107005070f81c0d5070303131014132001008503803a98002441441402102c0030345505 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 11798154 1250 11796904 11796913
    0x60105040608071b080c0106060906050a080406140c03040b070806150d0e010c020106060306050402040303020601120503040e270109050304090c020c0301050907030c0f21030201020c060406060510050c 88
    0xa021080b20214806040c640c00c21004080858460020043c0406854000c500a40d03464401d10041400c403041980070030700b48100d180b0300700403454020303058030040d080394205580107548038034044009080803206000c1d808901c000340007001d4501000765114503c210380d8044503440351242a0342059049600e81d5202460361603003002c00302000050f0000000002001c254031114130301c070701d080d518044c600d4030040c0c2d5100c42c200310319641406188000c0000752030442c40c19041d514000e4640e4014041d804400c08524107001c00c2100400480f0001c0c81514010703003050402d903082440303912000c152542e001c2d03290284c0c44a980d6041c4540441941e0250045181514140401d00503082a042140541c0140c4094000070744007030045600c62038610011301111802c40c0340000588101d9000340312161a507044c2400040c540303251103e94101d6150900e41544243e10342280603126513002040c0e20300404090100700300e0b242c0c0209081d10700c01c5440e81368002c81e842084a4602611140b184a40d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 11799404 1250 11798154 11798159
    0x60306040902031f0b0a0611030f03100909030503010501080105030d0207060807020102090d0b040204060b0331061a030d0c020303030c07020a030b070503040b0709060e101206080610050906010504 86
    0x2000d81c01655024405401d403030715480e200500701c5405040d8900c101c04c07240c8414040e0043c0c07a01c100d001001c0c2015082c690700041452402ca40d0343c2c01541c80806069200201141016801c0010040201240541407100c1a0320707140040c2140c20038824a804a01c040e40049618940031403100c80078000c0d54014a205490640304440074075014040342d055550802064010b500c81500910743ca5000d403458800b1820b05205020844040e035100c01d03411034052040c032104110541c0c0404403000200c2c503c00d899402105810000644114028065031030040341c078039000441100f020402c00101c050359031000004006841e85100c410009616030000c000044410558202408444d80040c003c2c0c0c0200b0b0b101e603a0010241000d890702408108040108402c01400b903241d668003c00c1803134445001c61608402400311a1000a1a481403821040f84141188600031040005031a00c10a101050740c41050b0340e156002511904020350b851000826241080c0740c043c1c0c0202010b95865146c940b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 11800654 1250 11799404 11799409
    0x20a090e12161101050c070801050114010e01090608040305040905010e04020a061b0201050d0612140c030a0209010303120b1e030106050a060c020d03030b0312031f0305060718080703060207120302030105060306 92
    0xf51504028140f00c82030040c0f80e40030800704880d00c0a49040d40000490354100202120041c050305182c03410004185d40100d0581d0380700200904558660a092480e038403103142c15186802160814580380d490503000041e400c282c1d908060189009440c00c1204c5612004221100b11411900800b0788001c00000300c015403044000b004050425800022890703181c0e4543d08648280b824241c4195013144022164441c0a0040791401c08003100240400d0038281d0128076441c0052102405111041201490781c0209030007003c092040285140d40e1b00d841240e0340036088041d412b43c90701940c03034402c0100f42400c001600006541164407005600401542045040090040110704064907000500328586040111400f61b00d14615010348030b14141000b00e800d80c101d1444a440d84001800030008100003081498006a451420250030305e0b07640303030500407180c284e44045150721408000000307008403030b805080300703602c10070252100c103500b200c048043c0d01007030051703641c07144041003c0340da1403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 11801904 1250 11800654 11800673
    0xe0405010e0114010903061103190203011d040f0c030503031603051302060a0207030507030605180606010c0809030f030d0203070e0a2102150c010902090a090c0909030507020a090e1216 81
    0x18481417600b140099143e42eaa03c1c250303205040c40f540804000700030307c01101c00078103c2c9000200c075084114210340c5002e4440401c0c1203628280200ca18110001c5001e0001c000122101c5940110041d00780c542c0d80e1070107075a43ea104440407041000317003104011425101c0d0003258000c148d0385000c2d508248081e002c1080540c8000860000c2d841804400000244284101e40c020360055400085903e4400300003244051540504034450b0000c000b000482da8000910318291500480c0340e944640c20540420301c0c00980e4130a05a06101c007151030070181c0c4a80c7c00440c8280c03065550554102070800500401c0505409140e800144c4030020000c41c1042d050b00034030340c40c0000c094808051711034924036480e9004a1030520a03075150b4050109504015044603008a450369041041300103d80700c00304424400d00440040a40302c1c03d0200505208005841e1001d400601d1609001c4d5138440b840c00030545a81c240502c0d00459070110310b040c200809403012001c0204040d0b448060a50344e54404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 11803154 1250 11801904 11801939
    0x1090515060d0c06020d120501030302060711070f08030309010e0109020a180f0501080114150105070609050a08030c030411060406050301060503090a0507060509040609020301080316030c0206190e0405010e01 91
    0x70101800002c40400c1c981c1c54a8401442581c018040d000003850004041c4008001010342190400c00100001b07030703001960541c8203a907450002805951075504a003030a0032a40005460004000c010514500110043d8020240c0e6070081101c0c0c550164207500b600c0080074007a5110040860810a840c0b11500d00005403100c100c0000c0c41803084c1034002d080f100c080c0c000759510382d59084001c07100061800007a4201024000b8007002c5655140000c082d0320400500420441d122038240003004000c00070010016484229640c4915103076401c1c10207034008139801c3e07401182444041c8100d0a06004031401d948455941c245141c0c00c2c41c0003981c1e19031001d072441c100791196149440200304203101030005001541d90715917a9448a400300029500706420071860b4034410401040704bd1800021100e0303944080c0c000360783c5d102450030156003400c0d0000e4080d401103c005540c103115200700b8988038400605444031122102010248411035100740129890300d480c00780140031880125440654 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 11804404 1250 11803154 11803159
    0x120313050106080d0c0303051b03011401030207020603041410020c0a02041a0901090c0905030606060405010c03120e0705040e030307020706030e0c0d060b010e0315040201030b04020f120105030c030109051506 91
    0x8520b9a141c0c91549443c00384d07015000003034100c004001c1056458043c0503000707400c15003ca185c2d001d0134540d40ca01803006105440340b6060109440c4007a90103901038030887c0350000d203501c0e100d2905043c040e07000380c00c4500d102070900580000301543e040a1081c3c0c4e03000c2e11002c000380010342036235007031100404c416007005161400451044116984100042e4068047c0f254003080c00848403202a1014242c3d0700510310980002d8200803231a2611420f4404540003480d2245d550031190906440f0350282c14034101360b00f41440c891035503698000801b0000c17604150b604000001071903480c241c40340400e07180b02c401a008610304000c41442600980401c0400b0000d40e0140c25031031000030a01038090b01b08403549925540102025a00080e18502d4070200340e01601c506150092010302c4a940144024141541d8040c5410f0f60b88407503040d181020000c080c540d545611115280240c80d409100c0e41c1d100f032090041d600c1003410b06019a602c825030040c020312040e1406c414011400a009200d47c1c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 11805654 1250 11804404 11804411
    0x609070302223602090406050406020903100c02070b04030305120c0d020a0206060312040602030f0a0e0406030b0402090a02190302091305010f030b070801060807030513020603090304171203130501 86
    0x101c01c2c031a00c0c818104040300d603e0f458401d140300441500200301000300b032864194205800360340981c4452640c168025848103002038290b40b42d19211000b80200640d1541607c40c40c8001015a0802c0d413020f03074140400c0c2c0032204c000340d8540e02080c941c450382c0002800210240044178180e20b8001c8200d03005814140202d00306040600c0e200100d070000c450480040c0d00600a014180c00c2c03d021144c84048014629440d1904009011b90713640305030001014141000905601024824601d0b03103da030380018014800d607552801c114640481c1541c1c1030b4840c4110030081605000c49100b03c401030100e4280c000140c008241c0c0580c000d4001c2d01183e5040a030307004a408001d20203110b150301824503100b51240b45c50031070030291441c0400070028030034001a10300510443d500300001e04c0d40300750306181c0403506507250031250009613114100203400c1000441480120350b4044050070642c1c5040030750303400c24041164407a94401104440000410302000402c0b040c44500854240c090701500010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 11806904 1250 11805654 11805709
    0xf050c010f1107020f0d050a02060c0f0610080c01030903020d050c010204090603050f060106050f0915120a051515040e070908030309060114040b0306060f01030905030f030601030e0609070302 84
    0x141d040c0c5000d440d4103049024005809011071600c0310519403c0b200c2510840f400c001290b40e0140e542030652070181c801c5801282441c00c40c10308103c42900e184500095404904040b80742e10000c8903140100440c50081e8444d07840076511a10410002540681c004d02864182c49801d40c0c16a1082c0381e4012995000c000c049800016405041d00640c410300041654005c4100641d00340001a0061801c00c18100003100042041c5070580750f05500441e400c1ba034424500e0f818078028400c99415121240040b4104115007a5079845944580c6090b0100000001000d04100032900f90040c007010040091000707110070000c103070302554070050758102804045e0b140c074415450f40d003049038000c40e01d0344101c005001040e07038950000d004110644d0705108182148000a88500e0014841e82c0511960709032400182e1082e00310b01b1400d60000180ca03661a10004a08a1070344220ba040f40032a00f889501101c0803000240544105461009001c00303a0a5900300b100c51415904500100a03480d80c05 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 11808154 1250 11806904 11806931
    0xf031a0303031305060705070b06060906121005040c020f060a050601050702030a0b04020f01030203060d0204090302010b130608060f0c0d0b1f0806090907120204020d09140f0601080304060f050c01 86
    0x3180140c0f0380500b8034030880d40c18035046140c400010988010840c0030f024070000955458215600410f007140c44c0d5417110351a0000c1407aa0203690b2681e0f01c1100c108040c007041106940c518004e68409803004d000ba5410b0082c01c0e40d0312400c01d8a01c48455010000143c101c1c1e91303660080342c022805141c640d2805d903080c1c0003e46480c1c0d000c1c0c825550011484107200840c9020314812004113001c0c02d0540c00c5242010018469001480b001ba0085454825900405201b90b000d8004039400403e5609001c0c0e400c2c014000501c114002e1049174461040824445814100d0442c8108196142c032483e01122008000242241c8401c060b088242c0541c008165102c80301444042c1c10180e564a2003880c00300f040055000300584503445681020000340140302e80300d05003401d01501030302c2c05690b50100040303880081140c444040c05e400340c0316244940200002c580d46c00c0c2590050100c414590304c0e0140c4640740e120f00c0c8500780c003040d84061044000c9004038040d2083c0f800c0701000003460f0550040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 11809404 1250 11808154 11808157
    0x50703181425170106030c060e130609090204050f04020306130c0504020a0f030b011701060c1406100302100305011512020c0105010b0d0606050403020a1e08010f0207030305010e04030f031a0303 85
    0x80d582c0007040103018481000d400f00401400b2034108020b1000b50300c2c0d603c914280300072502401042050040728042c4644a0138081d142d07402081000b0800700b80d80714514001400800b03422480707142004041005403d107890301764040d54008000e03001031f46901d0315010b01480c040c2012500c1c111403102c0018541d8891002d841082c50301d072288400401d00010041c112104400c0c220305011039a078403241201e43e01e001590554101e8200780c80c00a89904040340d0940c0c0e9101401d99502c68035040101c0100442504002c40f0720035a4280c9154481c001c003078007520024018000d4034480d50005a00c0e0502c140040215000015001841c050035513038061709644007608120040100002c80315040c80c485d1254400504a61070079609150a50303002440040c02403194000c040c849604400d40413142181c03180051100d01c00800440842401900194008080540c0400d14000000895402d002d003050f2191750b2607503c128080000250690040c070300300960408414039071542d0b1107240c50810 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 11810654 1250 11809404 11809453
    0x6030f0d0e090c120406020a02030d0609140f010e0609070e040906060302030d03020a020303060607060b1309020a0f03050a1506090c0504030c090c05030103080702031906020c010507031814 83
    0x240c800306145074200c14040d0792103000e00058900c107002c00c4103c80401c0441601c0390001d44c03115006d80d0701d4007082300491a5000b400d45d4951903501e041c60001d005002c56201154185500c3d0802466036a19041521095070034071803c04001c00840c00240145840f50090307a205000342040412001e401c008102194200c260403501c00fa99040f0610039854200044800030702e0a1606510785982414025101c1c000640903601440c804220082000042d401c51000110040c2001207400c6254040c0f5000e0215070006038003a0711740803000f1900c003079081056801d694014005054444041d078865100c0356442e101e4840310790f51024046802541802050021482c1d40d4806403600d0840c24500782d10800c96002c2101b1130b01e8227030406007803a00107050740c1c1126040000e80f41c40e4072840c00428100002450084a41d211a540c80010030050b98064060003004800800c0b0a54900740140c085a6038803410742e82e12940a45c01c500010125040d80032641a01d4056810030019828050510b00002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 11811904 1250 11810654 11810657
    0x10f0c050a0c080d02070801021911150903130b040b03010605130f08070905090102040e01030305030915010608090d0309050327060403030e01021501060c08220b0c0f06011d06030f0d 80
    0x200124414698104000c1d0b0252801f940210303d000d4409450300d8091703c5000c410801c1c0540c0801099240a0500c807120b03603ca00b82500c100d40f40382c403004c010307101e074070800e0b0050b20711018510100f1461f2110301620141c540322151185103034208a401d072096044440d10040c4441110000f08092800c50700d114002d102c408020100f440c1820840819540d000344401d0050f031040c00100944503581c1c080b681101d41508249990780c40d60189541054840c00400c1c840140f040000503900750b11580c083d21840c0da00e0142c0340130800100b03080341a522450009007284c0e000740308003507090401c03004034060000714040310549090304030045105c60300030782d00545c081a001d400e60121941c051254818107000621001003542c144680600080017402014188110100e00141d0000400c10350106003d11000d00003d2141c2d00d0140000b82d0784580c1d6082076034041c10b200b6040c050b0b00000c01d0b6040e15442403c40d0f01c1804480e030000902e2a008022651502c83c1d0301560884c1d001c2403142e03a8001c40716 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 11813154 1250 11811904 11811913
    0x7060e0307090e060c0702060d0203090c0a0801020703020c0f0409050601120204060b04061202030703141006021b1c0c1208120f01050907030e1e1c020c010f0c050a0c08 74
    0x151810107040003a1984402c800ca07060403142d04007024082000c0307501003210600300d07459542600100e58503000f002c1004d4100c52000060045d044030000e00304920400845a807070038692115150344c280c1c09030581c0140582d0007100c03481c0303441ca000318059401c0f078405880002c4100380d0303454580c80c0c400d003a4015491006101803681c198105030190348007400000f0b003428607251034840010f205000060b0761501d0b665000c000b0544017440b03034110742283e8090b029500d4241c1004448421107003154480c42000d07100303407400700a800040c100048561400204296955000003248001d03420400904032a0240c52100c081381d42c22881c0d0304182690f0042c032086480b09060140402030a81c0580740300f148031101c00041000384d588440859001c485d526011402c840c403d84507a262010501c1d5205448500a8038421049c0001070a42800c07501410807407031001245001366141c10044021500081d07030112405a01d6006040ba101d03014402c03001c8800111a0ba195440820003d40001d0f900303401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 11814404 1250 11813154 11813177
    0x5091002040b2503140f09040606030209010e03010501050a030b09071502060403090b040b0904021309060602031c05010602030f0c10060b0a0206070e090105100302120c0a0813030203030f09030702030706 89
    0x1045160280400880b403607003801150300b84c4001d04030300c1401507080000340f40056904000340041c400c0d81c2110300003410900a103611104050702079040070700428000b8000700e894030703c0c81c9414011a070403901c018014038401400d50711412500d0200074810071b41752191450000d944113143d0945150021507601401403400e061400030703d0b41c0815403020f1002d50040c40240800b0800500721000128100c500503511080701d18400d8018a19a0200040515000d0000f401d241c01100404228426094502144c2883d071550000c8610130300030940143d00600040c48080c020710000c240c0f200b000011641c0c45e28003090090140d60f0a0f40049201e4200419a200d525404000117500714800d41001c02c0068010000714410b842d051080030b10404c140d0101c45e00c0c1c3c0c0d01a41c104e52070703810304660082040c80c0580340d40c500da9100c1d03065200003c120400041c28180240c0c0940700d55a416030203540b554075410142c144181018200b100300d40001c024500c0180d5040080300001c146c0e80c1c840000565 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 11815654 1250 11814404 11814427
    0x1d1309030c08031f080303040503030105040c0c02030607030c0e1504050405070c05010c120e0f0606010e010306030804030f05070501050301080d08041109071d030a0201051b010b060409050411060702030a0605091002040b 96
    0x413800d0380100c2d600d81c400d209200014002000382c0b41911410348000a48a6100c00212101c11510f20041c0d01401070405100d1829450713000000f5110158403100014400c3c0c1c03080c01003904505000a032040410301c010b00180c035080d00040d402030b045240054100c0002d840c2c032403c4a854602030000b24050010301411100f10b40524403d481d0a0405040060b1018800c10344443c0300a00140c1005446480d12000d6070080d40540c1c00365800080f42038889440e4030304904003a11901090741c15100d40d50340011b01e5803081c82102c0c103840e03400d00944103415110006a82c1e01c84060401c507054881d00d46044125195131600714814100c1c0c0c2c3c0c8580d0410741d04c2554220f507103419000b1600940000c0300c1800580d0300101211030b11062000c10001c0b002120038210700501710a811654031076070003d40040c404800d600000d018601441c600075100c00307800d0400c58544640003000750960014450100071034010b900055002e0209401d0b24000040404200101d9100c0c1d0030092801320081034000202 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 11816904 1250 11815654 11815711
    0xb0d0507020615010c0201081801140615030106051c0908030901020310060e010f050d0e010501120b01051008040602070f0204050a0c1d0105030118020403021e011d1309030c0803 78
    0x141c9001032003024880c0303c0000030803100704024040e05015600c8007241c80d2078080b600708034125510713038000c0103041c2e441c9100444010003911458030901d004003206600c002c00b20104c0381200c1c0f10b92901480c080003548803030308a109070210341c61404d5a9125520201c0c40711002940318076403140c0010ba5070301d042c02c00c0600c0020355402c0141040704d01a01c003111070340c02c24450311001c0304a007451342d203400129007010081c0030308951003040340d400c01000089207110f0954801080c0d100da4051303003440c1c0c0c0390740500404000303000038440001c41c40c1000c40c3c0400c0e040d80c01000d01038041c96250114410039004a4240c54095a400d030300e031075403a014100350710350003000c8402480c45d001504040503003c0000078110f02040c012025088e108541c0000b000c2e22943c1101e0003554007600e5100000c19031460351251f001080380d445e02140240d00c181c07512a14510004482c0c0c20001d000c0710500d0001002807000741050042102403203400310308000420200c802442c420003048240040304465031807101e010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 11818154 1250 11816904 11816911
    0x4060306090f0501150309020406150507020306010605030f040f02030f060c090a050906090c0c0712060203071202030910050702150408041d0c03010e060f040f0c0206100303020a110a0b0d05070206 86
    0x8481c98030f401441680101e42807040842c2d16840c01190ba241c0c20300020f0028107440c0c1c070100d1410510702d0301170100360b0044044d00855000f00e09482b01350b030340d070f000680741ca02c02202c000916415490004002513000b801c60600c6070300140455401a0382c0b49849440d140c401c1d68824079078100429940400d03d00052203a01800003030b40d0b49580707420034a0114802413005842c120882c000071600202c01e072400c000385401400700d07295592040d003090a0450003540182c40303c400140c400a28091034910742d00859004000c1c44004103110545480984000e08010300302c50114021409013500c2508a03e03511400b69020740101e43d51503150052140040405260714500d04c0300c05800c001c10301c04d80c07100380c070b0443c0c880a03c01c004640d1042c001400000513152a41c0c2c0c001d00d40030802181b60324603405aa01e81c4501e400326a42e94858813404140c1906c58440100145d10800000d4001040500d90455000c0094000e600041c2c07284990a9030350480c1d012920f2940c0e45104000c0e081e503040001c50f82 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 11819404 1250 11818154 11818181
    0x40e100f06020a020310020706150b0a180302090619050402040b040e060d0f0f02010e040c0c02030607180611030903010603120201050a050105130e0a0b01171c020309010f02010e01020406030609 85
    0x2d141c1c00f5408240c079506d4031003000c1402a80070501e013040c05480e80010b101d018071031001c14140c0d0340b43c0501c4100c0790419800b09000800c0c0c0f00c400507031200c04003001c1d001c1d02d400404c400000e60f1124104442c90040b0001100101c0e80c629000804d42c980f40041c20141c120a1103154541d41001c401e0381110000918592282a0083d40382f0046401d61408928036908500103a0004a81380016101c0034010299550000e1800e01403400495004110740100d9100320b00352a081d44030000111140c90b2404601d40c401c0c00144420070800b4020141c4d08030113490081078030b051441c0c3d6030000b402c4500c240d0051325a440399200442000e80c3c20300c1030b640e100034030041c108811b505000200710507044242880a03510303940c0d202301290403800c02c2030702c1513276511100281d85980c451419902040c06034030002250b1103041c3d0301a000000000c05031004108a030700850a01c1e002d00011541c402c43c20410301e0555581c0c40da4807280d0b007002e000038000f5040d01e4030042041440e00c000c2c0403c41d20505036112 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 11820654 1250 11819404 11819413
    0x150a110706140d090c090e0606030a0201020d1d0a0e160503010f03020402030402010314090705100302090d032102070501021803010b0a03020f0f060403110f0102060106020607080a02040e100f0602 86
    0x100c1180c00036807219240159620b10341c0c490240401040040000c40405807006050040000d58408140c022980401c0310006640300d03915103200381940d0304d101810080c09a040044855072103071050184600d902d42803c1c8031100b0b00c1c034860119158005580040194880000400185506110b2840c0c40d030070b940c2c60700f14619890711031010314101080c0002841182c002002c40d0075a07102c0d8101001032080c40350a14400e00385000c8599403002c0611490b8080c8c0100f4182c440f000340644266101c074200034101082480d06a54111012541c1c2c2038207851404900c0280f10340001544003620301c030f03442400016500e2644400c40f02980c003c0768050345c440c0e81484a591400c1d00e03043d184400f10303907050359500d0b041901c14001562480b01151199000301d400708000050000070010f4900e20f04050315407a21840764038004903115042401040c015910034030104098a20902c640d59218003051001400d02d03031980350284c1202025580000005002c050a11890186440c544001d245900040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 11821904 1250 11820654 11820659
    0x1031805060403030903031b1106060303090a0306090602160302030301080c06030108100c0e060a030501090f0603080f0304170403060c021519021c060617090a0305030112060902150a1107 82
    0x240c0c1e5a500810080030507868841c08070401d03010740c01105002c03170104909081031084580c004d1900b20318807030b4041e2900c900d10229266060200841c0d26401000e0061500141183c0741d003405000c00343c1040301d030182d00b089209400c14030440229403d42c4a54041e690340d524100c0c280b49400e00c1041d6491103180300f0401001107070000105a80c00400301400428000b0b4031072000c0e51004619034a55030000380000f0008203095142c1e01880c10395640d65010040101c10f98920f104a503c28003000b0203480c010096140c101034064040c0d0f912034490410164058032040000503030b90000d51085440540300d444c1c1806058043c0071031180704114101c21030443c13a003850f41c1c002c90142c100e0140900c9a0009071070701440d09001310340e500d034005c03001d0a10525581e004020701010a00c035120718000f07500d1001c5420000d01041125541c0d4040e80e80c00d0031a400c6c101c04000401c00c60808541207955048403800507100e0b9400040c450800201c0740c0d850f1031880c80003804804402050b441c60380c1040e0420f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 11823154 1250 11821904 11821913
    0x20a050310060206060f0d030207030212030705011104060e01081b1204020f01020d0207060318120206010e071103040501081504290609150913050a060302010e0319030302090a050607060b010318 85
    0x4001c00e540c401c8604000d51841fa0405078180012a0000b81d0041c00d100008000c1400010007001c80c588607800812403541c00f00e03000c82c5d86015074040c04c0f00190a08d0302c00d030310701d602c190501c0da00309021b40342034107044020004011055100b00300b80390500c0741400800055140400e43c14148140c01e002070154082c0c540310094640701d860044800341940e03164250100214508503800b0780764005801d0400d40034905001e55146c00900c166001254843d00140c40c4501c9400070314200d9910100131800d0030b08007001500e50b80300c01401d01034800c4a9612602c1565694090f4034049082030a0304006154811a0300000c00c1560000c5401104204245407150b154050401b0500040422564982840e080019580802510310321801400c2506002042c02d1552000040307034400d884001c0807600f018103154072168800103110a640c0c5c004180c1c800300707000c0e800800d44084000c00701f80c4525200c5000a40d40d0304036010648035030381d03500b2410f022941c1500c54100c0c0441843d14140200c10555074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 11824404 1250 11823154 11823169
    0x50a0905060c0a02120c09091f0f02070602070c0302030705180a09050a080403060b03060609010605090909011508010f06080606060f0c0114070c0b010603020405151b01020a05031006020606 83
    0x500350003248005102c0c1031242041c002aa04250300800c10380b1580c1d10250074170713a83c03c40300d00261b20403982e01c13010801100c0000303040c04035081d0401103040403406c190007660040c00030b10891400300d9020401d060018009200802c2d8480c85000c080000b54118014103190a2550300050700540e00c1c00c444521070810111081e0b4040004180030445000c6458035508124103000001c040d007a0105001c42007160036005041000410b50448805075952020004007000a02c61400030400070000300d2414208841100d0780144203400224900c02e090705000c0044010b03520031030743c0f82d544100522500005000d104001c15440008000034100b042c00101c481c407610345481001e00300081d240381454001e4009041940f8030340c001030a10303e455240602031004108088070311110741c10000c10014024425642602c01c09071202100e0b803810040303d41c03940c2c4201000c6420414a0100e1070001d08240020300075030303460b0341d112501c070705069100c02e0314801182c01800964001c141040081d468652 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 11825654 1250 11824404 11824409
    0xd150b0409020304060204050604030b0a1103060907030b0f0907090504060803040b040b030403120f0b0102150405060105060a05190e0a1409040201121b050307020709060806160513090903030c050a09 87
    0xc00060f501d89543c0f8201300248146e80c41103030043d801090000500040c0d5840e0b0384070f20700d12002171180c980d010040104500c02100c540c0d078442c01c03103808140d01c03500c640d11100b80420302814164040610900094480c0c0080300c40c0000902d801d0001d02c620f04043c0100c0004204c0740d40198282420400e8600040c0110300400340103040c08000601494420111100c46000111041040620f0210040d000d06600584580940b03c3e044003039074241c451064091003a504403010b0402d03642400c003004941d81c0605001001c001c02800003110854603076028114280240c1c4414a990025000780448039419038000000c0d00000c5c60030070b10b642c40d00124642c2c803aa0910f40aa2280b00450001c002401e01031000705410405241000103160000029801a5004e400f240d6403d513803240030b0400e88181d4000d02d0141c3d008140840d81802c0304001881400c1d8030741c20550304184000c2c0305556000c3e505c1e070200b00626140c3c01c80307600b855014450303c156400b10346400c07031400103442c0b4003031303c0c408072031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 11826904 1250 11825654 11825669
    0x16030b03070e010311010513080127050706050d0b04020315031606020309060313050109060c08060307060c08070c1502250e0414010608030a080405060a0605030a060504020312030c0d150b04 83
    0x1803c1171583e0b00c07400465807600030000300442880d03120741c0e48600130100d2010158015203030a40700c2354107052904203080301c1c9502c04018003005080c5041200c907900141001c1181d5a00e030784600c072803545c40340091031140401d4040301d0007a20700c0c0e808041c601103042d00401c91604003101c0c2804400d5000c400c48003003aa090340d50a5680d00c9030383e05403142d01411315000d8410751901e9a04401c1080319084072400c0c51140e80d440b1400e89030030040540f01c544030303c581c002103141c449555000500b0306000e802d440f0702580080301010b903038060542a41e04410722017001038001072a94480c05203842040c10a40c60300b00780c1078010358201010f03801c2000c00540050284041c6e000e260752800825003060014040d00425203844200100c0084c0410000b51030407101401104000b6594500380e10485080700c0c5d004000300342d0314503962201d00c01414050f0040c2c2e0940035070090401281d1240e0001e5015144040c0d01e05d640e10500744200007280d2444000720322080041d8000c105100801c8290750549480 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 11828154 1250 11826904 11826923
    0x106050a080a1109040c080f060402090102031606060b1b0105090109030c030806030a05030a021b0301050603030301050114091c06150506041701020d060605091008060d0b0403120516030b03070e0103 87
    0x501d000c0843c6401140910750f0b1060400c0788507035420b580003046038012000c03a5200d01083d00e402040000f40d0140c0200540140d00500c00d51082c65050190701180d14000c2c040081c0c010b0f04d13214600d4090b0300c0320f0840d00718003003441d0080503e03071003d00c20b0f298000c401c01d008001860071507400800f119080300000d01048804030114074a95000d0198501d032a5001f811a5943c141c2c000018bd20f0700113441c031f0803109201c00b094400d03007401c1c10300441e8071403007008000d0b51031a800c2100540311420003284042800320305210f40c080702d484040141110505e1060040c0300700120b4540319069414000c1000714044a542040005448078402c4e202540c1203039018414054001c807074540240680c8407040701150904400003005034215004081019040d030b101031980742d840f4400d0310300440550b80c807508008440d040c01e02041074001416000361003450300318207049103070200e1400c2c0c803800da60000401640c1c44054409540604c10314034402401d0b006401c5882c50850010084a01444040c00700f402 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 11829404 1250 11828154 11828171
    0x1050705010e0106030606080706030204080d05031e0103030201060302090c0901020601031103010b0d0f02040507110c01050904022a0712020d080c011104080706080a06030819030204090603050102070b0106050a080a 94
    0x1082d00301c82035205a81c002080016980c1c18203001400240c4164400c038020f22401084080c400d0007210280e0b11f04000500c2c20550000c02100c055200904803038840e042ca405070050841e0500f4410700841c041d0340045201ca09500403c0440e42d8090490559054200844101641c010035150304480d041200e0060051100b004a405001d000c450a5072003101520908100400312940303880403402170f10200000d907240c03c0182c80162103140c448080d648204142c094542c8114000d10314400c0103840036040c00e1620300d00141c0b1202c8030301d0907407044e2003c00c285281d81200300192002884040131500e560f0444d50040340000f0f100d144068408000001c0c14400041c09401080e00b035010492000d0303403241d443c0e1101751511264028480000e484c280441d0315211540241d00c1541d40000075146014003a002d03403101240c4000484007031540911000848884034450b02c00198028000580e58240354502901e0b081e82c160049000c0c03241c18000e002c0e01913400502c66500c051820000507207800c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 11830654 1250 11829404 11829413
    0xf120609020c010905100203091b0a0f0b0c0c01140a0c08070503030103030c290703091703100f1217070c0e1003061409031c0e010905061006050705060105010507 71
    0x2055001414010300005040030703000015844071300310500501c180c074004402030603450140d1006880c01d05490340000001c8400c61208245800d40d06401489100c0283d903c401004c217411641d440b00050703203000300780c040c0ca541d428044440c5842c800d20301212080900c082d44000c9009030130b101d07000c2202e100030079801c000c03000d41280e171110340002c2125141e43c1d5901d0014000102110200c0356060012680c45803141030140f04034100f50614840d80860b40d425100310b00504c2c2ea0081654903c0040c8054601c0c0c0f1038020045007d84111010038010b10300b00300006581c03041d1a4800848411020b54401c0401d65081440c14031b1101480b00e6543c4e071411f820440c17041ba00030740055112060f80401d10040c4080740080c28116445484180040c00c0300800008010504581c601096002000072060300034039401012540c100c02a00040e1010460f5481821118180ea080311264000303410b00400d0518602050024599071604519240c000d41e0b41d45d48500301803190f1414032002082200070030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 11831904 1250 11830654 11830661
    0x1104060311160602040512150103030c02011803080306150906030402010311070c09020702120c09070e0301060f0806013003030b04021605010f0c170411030f0607021515010f12 77
    0x211510b002c400700c491800c00100035441842028894800401d0425600d04042205100e01c10710201d07080d002d0786903031800d0301c1002070751740c0880c10841fa07986035a01c203003020b0242c4005140652a015124035021052104030082020100ea0000040c0642d4003a0307070b101011242d02070b0342803802103001e0b402410300c0d154a0141e0303c80140305410311540861600440d50103451000e0003200d50340c500c3c50348030802e640c8900740e9400c140d802a42e500c0000c4d00682c041d100e440a8101c01600002c0c40303540c1d500c41e80c10340540c4c5803c0310440e0f410840040081d4a80c00700f1028544100390507071641d241c41d0b1000d14400440d0301400a00b0325844040c104442d42c2c4660540300e0404000f81d4401d8142c9043c540355000301006c0104c018558900058803078100d1144102c494170300980981b51000d070300c841e2511480d410000c950305505104240403400100418000346000341c015030014061111000c4c0020b40d9000003d26400104812481141083e03901120005503c070660604003008039a22031a40041c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 11833154 1250 11831904 11831917
    0x9040f0302030f03090105150609030c1504090603080903010f0e100504081207020a03080f1504020f070203010212010303090803070c0e0601090f060c0b0606090f100507050106030303050405060a1104060311 90
    0x342d1404000c2000c942419000302348610096110310010050450801c48140a844034290305540410411100e60801c0c00c003580303440c24100c3c201800c2c1655a00f00f0016100700e40c000721080d1002141c084a141001d02131070381d6100c20300000f0700c11000030311490ba42e80c585000e11004d40c20748800100b000d1094000c200c07900e442c0400c1c4401c0440ca01090080c0d0307918010541240065030b5400081e408a074a05000303401114038846000c2c20150b40c0c020031019400c5140003105001d81009100010780c3c0034401010441088003452003103626604028162400c0c43d4844542d40d0410000280000c91069400c0305a800244148425849000040b11040030750382100003005401d02000c10303603540200c810013640e403017440c100203a03a98900c107020b444c4c0980c2e104140c108880c241c0c100503d01d86021b5142d0902e00c1860083e050081030348403907007518416441900460340d80d030240402d003d810300031960701501041080c014a00c8002e014200740c8201c0c403482c0c040658603c0c0c0c220000300420100d804 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 11834404 1250 11833154 11833177
    0x804030318140d0f050f0a030e01180c08060f0a02160506040b0a0c1d040513060207150f020a08060405060a030f061d1603030c0201050910090e06010207030209040f030203 75
    0x291100c081c030302040c400d03466640d48921803090b19050300c3c80c0c91003078a0041c100d01c06a6501d5040a402c030040031226004000b0100c20705444488031b86030160248582c4c5040703280580b0148589855041c94450343c059508060420f411800400c00c000c181040c00d290028003100307005030f540211403488280c9500040f0001c040b4050309003400244055900a10301031102540108001d0324040000d03503101600d07001003066504140007d4501c1e1605074002680200c00c100100450b0f082c80c1d881d00101da01c0a4000c40d03c00c454800e00d0452104944103055450b10301c1c040451400d8480d54014041c11401420035100c1c589803800110309488589141004561008030f002c266440da15250014141080c0080684000703141800da5503840042c90300d10900042d2003178552141151811540400d82c0c0b1401e07411700ca0308022450260700c13481d00f414410300c805e03500c90729094241141414607220142602c3d04661200c0340600169951140c0160020703844807800c3c031480401c1ca000d0782580981e215604 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 11835654 1250 11834404 11834441
    0x209041a090c09150901050d030306080d050d05010905010e04020f030c040f020918040201080c0c010b0a12020a050415060809100203010608160c03050405040f0b040203150f0a03020f0108040303 85
    0x500035000401004482040320206030340d60304e15201d811a0075011410340e03400750403180100400c0c00c2c07402c0c201c11b040d0b00a25002c11415109c00d07610380742c0010981108001800010100040c1c8020300c24540500b00b0082c05008551502682c09480f03a0b0181c0080c0c8038003154800540c443c0d5042085441e00750002d401072004e5010705124200039040070342c03a01c0c00340c0b00503e0707261107064520046a100f07d9058441c1083e0b03844841c104e000a400c406503a841540d45c902c1d04540b03075950f0011303860003441410030180b071a080034030502c02e04054503070042d03000d541000401390007001c0241e41e00c03007070780d031580783c183c3d00350b80c409000a01c0c0544c1030b40001c00c0c13148004000314a8543c00928144a1826900804072000900300200d4000d810100041c1c0010f8052205004a25154028100458504c4004101000640001400c80c1d000303489500032904103011107607090a2903082c011650300c040302e0031140c0e98a15004580d803056100e501904124103000002d003014020341c80001e08000401000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 11836904 1250 11835654 11835661
    0xb0301151e0b030708070804060b0306040b0103031b02031f060302060c030406110d020d1b0c091b0201020f040302010e011403070c110f010c03051c020c030a090b040609030209041a 79
    0x1c541c01030700224800c0e50054152000c01c40c9050340049a00880c903507541c52845944110040b6450240a801141c02e0341e00c50340d4030300342c43c1d808000185c0500c1c003411102042c3e514519010f030480d900c5400e01e8007500d15441300c03c80540e8010601c08400325010f280145060b0040804c1c0e070080c829500f00952000006c14008000b60002025205440180c0c03128290703014204c2c80c0d03a5a41e401200c200e00103a1081030aa40c610703101c0c00c17409583c0710316807200b9050a0055511050691060f803c01c000d406e1361201c400c0c556020440d442c00c081801e81c0000c41c544025402e02c103c1d0340c1f249000190512000c020300003000e912884008100356001e42140361281400580201503400030314094038001010062004685040849402c105030140c44203102408650343c29a50754114510420b48140d2803003c1c0c0e04a02c810740001c041c07041e0b0000182d5034a010451028209480b5504000c0040c0c0080c0400d00030a82c00220780c01c1543d40480340e814032552140350040070110000080000c034090310b000e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 11838154 1250 11836904 11836919
    0x12010e0601180c08010b090d0303180b060306130201021209030715050a09090e03120c09060a0315080106030c0b07050a06060b0a11010507050a0c0503040305010501080a03120606080a0b030115 84
    0x119140348110b04401c2c01000003500d01280c025a082c040c45c00020802c100346d01c204d03d840072900250398800d08012030700d11500c90081040708240c4200b81c4015000d50208412860180103080c0c0c04010701c4070701d80001c0e8a640000359110121950441c1d03506d0009490b195964041010100425072103103a13034400c00c88038500400039000720a4882c045110326101040d69000350155404403000300008505207124405100408400a44100d030702520400030815a500e6820080c0240038407078401055007a44a0144014810303035a11101d96645449003d000248014914108803051007075130917114129803c1050030702d8011400105002d00d08003001030114224406000340c0300303c1d0b1b01c8040b40150f801c0810b40c01ea401c1111150300192040205c54802070207152912001801001142d051076182d9444a08541c0b082e040b80f000366002e50311450070181e000840ca210114403d4091104502e030a1000e40103100c0544070300000c03501d80c0f07032000c0c00d51800d500c112140144500d9040405964400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 11839404 1250 11838154 11838179
    0x6120503040608070206150405070e06030c0a0908190308040c0902070b060111070b03070f0905040e06040b07050403030e010806062101080c0406030503030109020c0a08030103080307090608130212010e0601 90
    0x184008107840d1000140c09600100c3d05507c034032041c004a040c0745100d9400c0000404009240324144501002c802540e07440c2c00d4007461040c507003494403e6844441c0d12000d0070204c1c00d64002c3d1165489182c840900703620003080b810324207901d8103002034661a07500c1c0c040100d0825400545010b03102041c2e00c1c1c1401404050f02c2d019600c2078858584800c01c081c0c0c26511a100c0380103840d170701081000841c103a50310641105204d012117142644116485100044c207136508815080000ea20080a000512250791a403035004406402c2c080c1c41e1511310394000c2c0c821158460214103102217400044d095446002c2210b1100000d0031700d4084600464a10315103a21003809901518032620b0031041e06800c20b032141500f641c0d041002076045a181154590123035001c0380401a06000b00703a401400265030202031806940301e544165240c0c030f8241d000510000303550f401002046a86001d2040e43e04600b8490b41205805440d414200e05500454901601c61407501071414400c080001506005800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 11840654 1250 11839404 11839409
    0x706021306080f0702060705090a050a0e0702071205071406070f0b040b01050d08120c120a0b090604060b0d0902040b030a031110020a0f030f0b04090605061201020307050f030a0612050304 82
    0x3140c880b81902d40c142d02002601007183c00760301503440900030504060142d070241070710020003401441c45544410100303108401c6a07010f952540050018044c3c82a01400408050201d8200107441260360392141541c1d03241754851a000c500c035203442400603803140030894100e2074000d4413600622490b4030b01035960784030450302600e208044038000701d600d117000d60340d400c10250019111400c00d1050144840c07001405440752030180d10030800c0c24a122022407111740b082012550000c1c060a01100b4444d20001c010b00242c0b05600d88401400044002e80a65010a220b018005080c0391180b01050040c5550260742d540b510031000b00c00c0805a2110400404040842c2030710f64011a000c400804d80c02071509990110764000e5082000a200c0c0d4003000d41c0041041780070070f01e80d24000100301110349100050710407035225810499642031611300c0ca81c3d2000c110008506d180391034500206240074911030003000500020200d40c842f10796412240280c01e2001d5040d0b64074010b45002c81d83c030750051 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 11841904 1250 11840654 11840657
    0xf0e030703120e0304050909070906170105010909080403150e1b030f030405010806060a02011e0203060415030206040b070c030c060c1401050405030a0c0614190e01091e080706021306 80
    0x3200c0091941041d4010b6103e9001c42400440c1001e0a104c20402e180d07800400c0725140388a00d6100244a00490042d5002090400010965012442815425542c058000004207130a000d410b40001d0002c10494089a030860707040480d0f46240f844420280c40000e680c2c0c180f601c036403214540c1d40602a17007941d00c0044201c0894100007009110503499000e14420640170030341210014000382003030303401004048918400011800c2c5e4800e08440c41410100034a60043c3e400310400c41079041c240b280d6000b000618076484201c074030710750003c0e0b000d00c00d0380180742c1c204001048800c200000c82e1880b4000d10341c4401d6442c00e068440000800c1c0400102040d103650510141210070758406125085c042c0d9045805180341c0240a41c05440c0f03409560001c032820355a0b40344001215041c160a60b018a0170790000305011602c19500a0a171140c0c0501d034061130740340843c454001020100c141c201a0302029000800d07410a0425508600030b4101c09010035000041c142003c0544941c840e080e50180d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 11843154 1250 11841904 11841917
    0x5010c0e03010b120a0f0302031b1c05031510030e0303010803031e01060504230d0308011a0a020c0d0c08161505070f031d06070c1401140a0e040f0e030703 68
    0x50700c04c03c003500640c2900c001c00c039005107051001040c2c111203581c2c042c5000303004071f03460180725008803070402c08041c0000c07503a6044440c004078000490002580e03020003a20702a0b0840c03c090042500440110b151548503107003c02e90380c1d000c0350007900704d40b40c02040401940d80320340e52504095201c2c2e00448500501070003d007143c4850f0448921064140e45440d030b103450400d41001030802c90052040348103041050740030350858059032202c120f440c8903807195940c1e81c0310354940241e11030004984060b040c4511402d100070034000d40e0000398209180c4048408542c1401c2c1c609001c401e0b121950000710450140601c14614a000c00c1003910444a071451100c480202401d4115010b0051500041044404c6204940403d12a440c01c0000000c0c800315008074034003010015038941c1c0f2440d011202c001390355004000200045580e02241fa0080c00c101e10450074280f0004000c0c8611800b02d002e02002001c009144d440b0f6601159030346400e041e08114038034065442035580d802914044002480 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 11844404 1250 11843154 11843171
    0xf0705041805060117010b090108071b031b1403040f0801050c0304020118230a05040b09070c0602090607060f0b01090b030a0c03090b040b01060f0e03060103060b04020705010c0e0301 80
    0x49042220304985408028080056074414040302070040a0489030410000d8001280c0c080c4010340d0103802400d520707507550750360301d441e1001526442000704030800744400901c1840c15040c0c54840b03550041d0785460040400c1003445a5812040c0c2840e00c09000018204102d0240b00300020040c420f4900c00f2850000b003954482c1590309036207081f0385a5481041c01c2c00450015401854524070880d1602d44814078903440d84068405001c010f90001701d04e00905000003c6821b140c40c82c040502002d03181401840100004160b88940142a24041140002001040c0a030341c0e410b840840380c000388034a0b5541a103003442c00107800e959041140035031a0480e0a59150300480d103490840d140306803c02e04540d1001c450b84001c21008401005160f1156010301c00544041280b62059209549401042d41004001024640c1c0c0040038020700041129901255400080f0103044030390002000c01c480b461a800302e40a4050554020481d40c02c1c000341d48102c54110140103619101903008000180 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 11845654 1250 11844404 11844407
    0x20a050f0313050906010302190504140319030f0c06050103030e0405010902030609180a051e060c18270a0c02010b010507080f0f0403020a0306020702031b0102030306090403020717060f07 82
    0x40b50854080c19502c41d500304120074284103401c0342c0c0c40001410018182800620124034200030080780c1e01c0051000281031040c01c641580010081c0016001031017001e4440006000f11640c00b0805004d1100700000004020312a942e200789590f40004280040e5a6a107006032541c08400b06461042c0d04000020400b164980b081e81e2207164001c051015640724420021481580380c43e40100b5800340740b00400220750108140b0a156526002c0540d00d0582d410301c1d18244a00a0224030003040c003000082d148040020400d5841c03030b011508010200303100b94504190310511085901c03c0007034801000100401644031501c000c0315034000f80500c070146001103a951141e03160041075500b082c400c22000034022006428011901d4841a00c1d02e6160340010750803441907030085032110740000d12002142410300440c81440d83c87c41207043c118802400107904e070300004001a00401410001509162003001940700605150555144502c1501c8000f9111031044411a02000a0401260059 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 11846904 1250 11845654 11845657
    0x60305060310020c060f180304060507060e0a1203020d0204050406060e040b0a060c0602030a0f020403050307050c0904030804060207030c14010b0a0e07020703140c1e0f01080105060306010e061207020a050f03 91
    0x2424025251a6581c81580402000e015001000c1f803602d0500d44141414100024005011180c42c0d29031210f02c1c0b0b02d0f0a40c242c4043c000101050f801c40011200080e003a02050841c2110604026807a011030301b941000078025540002c0e4401c1c288100050641e0701301001404429040c0c5041c8080ba03103907018050400781c18494a000507000004001c04201c581d4044d640142c5280000306620289480c200c00360307041904151600d4100140080804c0001c0009046040702541c025066182c04c0c1c0300038081000042000e0869600051800109482200202c5520707030301110146a000300c0c5a8454000c000d8100f0b010f015849402011610101d21002d461003031840b54010308125085a07642a01094458404400e030b100790a405d06440ea030320b05050822420041c6045980550582040980d44440803118144440400107010940343e0004890348081c007800c2c1080c00984070000b0581c0f510403640900320008081c400e00c40c1555000c14600301560040d4211801c0ca428080b031640c8a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 11848154 1250 11846904 11846917
    0x130b010509060c0c0d0803160806150c030c1b040f060e0a180503040b0703030501120201020c010f02120f03090d0216090504030c1203060e100e040605061906030506031002 75
    0x3103002880500d84034542080100040f0b144102a140403568450204040488a4030210f0b0404408000c20070071002004620b940f2036844d00e0a52064180140816505c8040301c0e5260041c1000290080800da0100200c6107403000c50421581c00c0c0389003800e280c09a010030720340c02d8822400e0201c00da81002d024000c54094648001e04041d072510f8104082008000c402e8102c000380070b04181c102d01240c000d00180c0000e11a10034101e603201400d1400600301d4005070040d4003550110020140585d03030020f04131074642c2080c06d00c3d00d01c07116003030710603861f0018041001c0c0f900c10002924480c00170040014500900b640c1040740c1480c101e209050f82c40704000180c203503500d20300300e4040010b2841c0783c00042e089400782c1024a044030680e00c0703010030402c1488074078002c00d8035880d0030000350b020300e840c19905c1807040940000c003604220f11000701800c003805c007508490b102c0b0085040c903030701e90076034444124101d00c0015400c0c0da01d03000a0301900301120030f08c1c86409102c01841c1c030f0b5501402210f030f1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 11849404 1250 11848154 11848157
    0x30a02060112020a0f0603090209010501030e0a031404090207030504050307091e0c030605120303040c0e070f030506040204090603050d0909050112080304050a02060409091407030506060d080d0903030209130b01 92
    0x1560382c2007070144085100301c2c4105a070f10501c010000550b20480e05c0905010313012980c3c01140d0880700f40140300e030581044e130103541018501a558030b6150404609015050b0b4940b0f400130840c600c020681e03045002d580c01c08401e07035100040100802d034110307004100315041031342a11842c90355503a120b0216145116400040310000c000e114a800207030340300c1424144542400030305a602c481c0401e1000ca1401070309440e84c1e00000601081c0020313000d4007002860b2400d0340780c2d07442c82c0c081401007264802c90b1078031040c580c40f80081829a074560301030f5005041c020008000e100da5a050843d40c0309050504440411f01482e004505030980d400341a06885d100144080c03004955590f180483c0d1008005030351a006000500c40103a07103050051008007544580070a071038460381006500320a5840794005294440c2c0e40800002c2c030045046076202c181150701100000a5003000b9885215144d000700219103408020010940c140d80601300000060703502da40c04070001700d81e080803503040d94074a90 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 11850654 1250 11849404 11849413
    0x5040f0c051c02190806090f06150a0e03030a031d07050607150b040e030306030d020606090402040507140705070905061c06050a0204080109050303010302030606030604110607020105190206090f030a02 88
    0x1c40b40b05078254030822a4851100620703100b8281041d01c031655000c48000300141c510024420b00d4a00070140710740110141110081905002c0d0001c2d21804003812034440c004004614046d5450040c081601d644401030156591042c4140004004000106a4203d82451440318030140480080d88a01341c801c09001640f401c2103e40380d5142c0c4140f0b0100c1c50720442d850303103817040e59074441d40200314208004000031074607810818105806c00c48101c40c0841198046070421069a549100bd540c005806880015507901e640c00100d03034000d210f02e10320203e01400030704401040783c0050218116190749030100056280d0004228925449101c50410185420440070118007264402600302c008250014900755a49545a0944480c00019155604040700420950405025540d80300100714054015403506658842c10004044442806090302090203411640034800f116040c1ca4200e0398450444c0c00382000954441040390072003c0350207403c0d2484002c10002090300c0f06805d080c2c0240 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 11851904 1250 11850654 11850667
    0x908030405090c04090e0703030e03240411090405030301060905010903020d060f0213030f06050112050624090a0c09060207080d08091203040b04030305060303040b090f0d061505040f0c05 82
    0x1071200c000781c480401000704100028285c4410301c2090315401e4520058a5603500e1030038050000c12211410900a4119500640028000395182c0340414000300b00111140c4860922a054580760744a0301e0f00a0350440900042c08400800b450480d11a1360301c1010654580c00115015462440300940000e1038110880004a468000d01c100c907242020050401c01004600d25019041e0740c000c1d03a04900c0c0c6c14540c07090040c00d014032070152604000440c40e80c1c210b6034540343e0b030380b030004c200b4480c41c00041e00344c8514a80903e01e00b141410014500300d0760b818100e10b2400102a1a5080c101288042c02c000400a0000c0b981030122000e090107040e500341d050364152818072006014912501690100024032020031015500450043c1540742c0340340340c91300e40a8101c84e00906807a10961050200708102c5180b0030850320942016a1403488009003003010500040d0180c0c40141200c1c10f04030302502404441c00401c0c11503400300c41c1403016103810649142100c001071202c40004d2801c0116 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 11853154 1250 11851904 11851909
    0x70b0a020c330609060a050112020d0603080a02010b01020f0304090b011b030503090601090603080901030914070b2205090106080403020304030506070806100305070914030c0301110a0f0908030405 86
    0x2038a03085080506850049501d4503104075082c404074000020070142d01c5030511407414100710b06a01c800f082da2110040e042590014000c40c40e5841840e04001c400c0c404d401c1e40172080e0b01a5000035003080b200b40f18032900e91514041d03a800c810540c41c01586081d49103826076100040c2044466107040145145c1414030f016a00030b40000072180f41400301218000550081241d0b07034511890090350340c10b4590410201d50f505000341a80f2034814603050100500205210000f00c079803801c024200010410890714040c841e190302025941c19901500e84c001401ca0710942c000c1032032800b0303220810103a601c001c92104078045640030312034028003804014000c040c0604040fa401600a00444e400c140e500c0c1c0d01e0340e14294080780d0650000b4030342c0c0244011420540e02106054100e410240518070f01140028074403041c501c200f04542000c000c019055413402d11003580c00d000d000d0000c0c4100c89000b4841001d9500030044c0000040c03101b6004a00c2e50710a00c02131003030307034402c00240d45454500401c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 11854404 1250 11853154 11853157
    0x30209060a080f010218060319150302062b021305040506120610030203070605040b0d0906020d060f050f0a0602060f070e2106010b0301120813030227070302070b0a02 73
    0x900780c120358000c1c03000c120300c2020400c41d024000707900005a5600e445882a85405034040d180382e00a001c14014030003000352520004903520b21011000840c040e076103400705050070a07580701a400050000791051204d00c16801c840c3c164020508903641d4500d182c4040d8100c0c89200c1c21344445803031080c000d0100d450a0b4100a4100c03c005004c0700d004481201c000b42080003e03a403492281c5060b950800460505000317142c018102820b08505041c81c0190540d540c2c8511001c40521540c4e0300350040c1008101d6064546040c0c00c1001040890f0325070200351a5076090f1700809204280710400e6141d60328000240a081d035103e5805030609440e160381d1200fa02c03001400d441c0601c14848001e007401d480f01220860f025070490007902244401e100c006046c000183c00c031071800c1030100014486804c541c401c199007607520690300b40e035682042d101000c0ca22600d4000940c0030b034183d002e000002051000d03410408051401c0090652641003080e42203201e20b803030040c4960050800240034280a50 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 11855654 1250 11854404 11854411
    0x309070501110a1406070801090507080126030a02010b0102010605040603110112060312090501030f270503070c090c090902030403020a03110a1218090525020f0102130302010e06070b01030209 84
    0x1111900f15865803201c88503035800c0000f50a03a4000c000b00004140d0215500e401041a21010440c03030820030001044c883e414040e4031040203401414109001b208585071600c01403280540352035030f8a402c0006c0c06000d40320b2150b4011340c244800442c3e180b9081c81190100c0ea800741801a0196070040107413511744005507052110750b83d4030400030101d030030182c12000400c0103607190000b1300d05000001d000c4030b0600300b0355440203207404100119503007500c502d04000b4800c6042d003444000c80b840c7c050f1552007031a00c0101074401a040004003050950005140082c964450300c43c00380c1c9808904040303000481d405001640540c00c0742001c280200080e00720402e0b000160754454000d03489100344490b850f003828000400003d015208281c22400307410240021141c244040d0030082069a050070304480d0f0402100403c80c038052215000308234a41115000400954441c844803042050760822031009a0105981ca41d000b10241703407a804440c2e48541c44400400e50740d0943d028001c000a00a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 11856904 1250 11855654 11855687
    0xc0d030e0a08030a080a0518100209060c07030606170f03030c03100302041505120106080709020a03060f080c03070905060d03030f0b0d0b0103020f0d0b040b060f060714070602030309070501 83
    0x20040442c02c8101403004001480c519211001c0d281891241d040484200800b1a10b00c070100640d0125102c601207110351fa003d10386540580c0324000340d800201144640c0900e04c03041d1040040020400055400c1081120825004000044203401504d030b15034954590004054004000084c0310340e00d010091b6400c0400721411502045d100ea010900725603007108491400e500d48201007080703141080b581c01e5040754000003404a01e07e003000250f03480d02d06005009003607030042110f00075203112307500400c004d140706500160980d0307803281c800303440b540c500948c10701074084c9200c082010001401002e0040c4800303003000369607842c0390f10110002c1084d040340c04001601c80c42c070040aa6119410405001d02400f404281e0754554030401901054120340d40d809940c020300058045802440c2d100e9000b500303c10f107500c10340d540d600000d41d8040701d218416400320022896a0a000c500003441f4140018101100e43c03080d11884103030303500d01048944490560014a0a0110794032807015101c0d128401c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 11858154 1250 11856904 11856919
    0xa050105010c080d0c0905090f1501030605030309040b13090309030302120306010804030507020301140106020d03180b01170703020a0306020a02010e07080c01030e01020c060c09030d0c15020a020c030105040303060501020f0c0d030e 101
    0x207c000140d070103c030a5415640c4035040c4000e0144107000101c0c50480c1080c03d080810429160601190312400f0f20915144556a219031500c950b4460710b00e030584e100e508500c00c011040355481d01400c60089400154010302c2040809501c1c080550220383c028441619104515074072a40c00b2940d40e4014982207070035548844442d0f892040540b03c00c1d002e011036030040c00817050940c0340101100c1c3d40014005c080c0c2c0380c4403c001d000c50140d808550550302c0000d5042c0841301c000803d60b1a0440e90b601c000d4001c4400079001050082320340c06000c2040c00e41d402800200d21005400e82d80b8500c0d4001c649041d0084040c00500b58082d0740702025989405002509082c48400714074240041296a01c001c0c0b2400250303800d032850140303c0d811441405082c045504c4249c1c0d103640b007140a0500c2c0c2c00840381d6001444030701c42d5000b0001400d88190040003400341d4507041c5802005401f480c480c403405403061030405600c0d01400304817480581006403e00007602c00e192005c07520801045510b9030008030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 11859404 1250 11858154 11858159
    0x3090316030306051302070c0b030417040602030306010e0409020102060609070e090108030d0c0215060d030309021009030209090c010e0f01090302060304051b10020a1203020912060a050105010c080d0c09 89
    0x103a810221100703000340c400040d01842e14042c81a481030302c2948444451042100b1400108200302e050207560056101c603890386d80b9442d19400500e8411090700c40640d001ca000581140d00100075485104203903503001c108007690080c03000340d0380714242c000d025820003030000311281041403d41d94401c81c54981000340c18158008a1543c400030f800000054000242c034041100035030240031048001440146078412090043c01a041005010b080c41103088081c80b80502d882508011001500204000388580c10044098201c0380d072440100c1c0114401c9001501040c8085401d00580206840d1288041c15680800c112811a158224103000301e540000c0090707101c0d04041c5100782d204000a10349140c114800c440700c40c90083d5610710030701100425103520360b1301080407198241e12a000c0b55040c8813140041d00680a802086600301c2600014650026030006160380a201d60b440100003a03621940112a0560280009000c1d4041000350414248959114002007103461030b15081494 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 11860654 1250 11859404 11859427
    0x20103020904060303050403140d0f0e010203041d07091a1e0c060408120a090c03030503100504050c04050910030305030402060c030706020d14060a030320100e0601030b010f030803040602030903 85
    0x14003a0f08180c000603008031f0103204000042400141841c03900c0b0017040050803441c1c000f420799818040c5a01080300708444035040e41d00801c1581d0140514000444c1220b11740c0e6608940b6040444101001070302c5008005170344400c0303c03500c44440c20401911361138051440c94000341c0e15487c01d04031178400c0b01086940b01107901844540c0c01144200000c5a03a5222240c0d2000304200181c4140b030018036048200e000545a6480c860803254142059901d0355280744801c0d500c0b2169910a68120b402c2008203d00ea600d1080140140e03601110f00f13080701e032075941c103010564105020040c08100c0400c041030141c5020300162891002490450345081056695074041e41c0180700c50003407060303c44854035054a280511503078000002c0d90300c020144c0c43d41d2801424900100002140800036181e0b03084800000d21072a180c00e2181903040c8468081008013591b0360301c0903c0107550702c038580c00011070a51004200f0b001283e420241c00b500b1a240c60720350742c00941c400b41c140c11162104200506480 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 11861904 1250 11860654 11860661
    0x8030a0e0310020f04030c0b0408061512010504030206060a060806090103020f061e0d06080102030f0403030c0c02030a120305010b030c0409050c0403020405130b090a05210f040b0d0b01050c06070c020103020904 92
    0xe1060407000c1d481764990301d030a20800c00a41c11866800006200510001c40001807081e0300400113201d120f01a100303440460720076060754080c0782c03907942031800b004181600001c0e0740b800317180c080c2d03400690559113000c2224003071010360b641d03a40060b04400400240c80d0038030500c1c0700010001c14035441c1807101c0200c88000307928010b14940c070990120307510031098031a11844c4010006440250f25510f40f0300d000ca0742c2104003c0009060654900d00400003a10a01a01c01c105074090102d0307212071003070300f400070507200340c07a070380000080c00d040011881d0111182503d00808641b482141828100304940001c0c0c100106000340d5804140030000c0582d54138040c45001b6208c8091001c04005241440032054000500b00c18695101501d01070001d040060440460362084180c45400102402170f008144140c1c41c81800002e0049800310b0b0100707100e4014102200d860004001801d0014015545030151a805452076080840041c084902840c100708003035105150043c68001100005800c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 11863154 1250 11861904 11861917
    0xc060901090606050d03050901030510050a14040f06060912060f1805010b030613060f020403080a110c0f18090f0d0203070b0105090103020303070210052511090108030a0e031002 78
    0x960744030071401c4180701040c410350340a02004e40e1080441c0d0816180909248a082d54290405640300b0020390309641c40c1c951031001c0c1ca00141001411a80e64000b07100740303041030344494483d500d059072036210a002407203820221030b059141e146189180280075000c682542600b03481b85502c0b45c07083c60180f6820f1041403460645041c0c0b84400070341c90700f0001e08482c40d1700c00350740c020b40c81070b001c0c04419800e80100800c0c0651005000c21020107030031921001c1d001784d5100510b0f8401c00b0401e00700b9550482825010200c103801150041c400d043c04004c40d034001c0445807900030384103541081ea1801c112502d075600c00b29a00c01c40760114048244c141c641204000c1010040c6c1002c17425004101c2c41c081c8090040008981d2034400b5411500042d07200e01c225400240f0802c11844100d00d09400b48040e40c141103401c01056484500840507900300c00c420b860100d43d41c08102844401034504400464107a07103e03a4025414091282029150003401c0758000da894403c0c2240705414019600080c800d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 11864404 1250 11863154 11863171
    0x801060b03010905160813050a0203010c05071a0c090402030601030e0a0605090f061005060c10060b09040b030a0b0f0c07020402031005040b060403030503060108070504030b040f03080a06050a0302060c030c06 91
    0x680b50300d0881d00408a8201504803651403003181d0103c9130080e88810865084850840c40750184401031804038034121201100079015400c10070384001050700103014010302c5c2d008000d1000c054032560505104200b08841d00a010901401062040c2c01c142d03018603841901814000781e00510004503a00d02031101c0000c072240c2c1e80326000c1220b03051381800403000d441081d034001c040340c0c2015500c411040c0c400b0701885005a001161140d0015820402400c003c0521007080200641b5581c0361155540400c0c0414021404d01d2074849403030800003020410f99421600422550300c1d2801d03140e1803908003422100304480c080c00690056174070f520003540181001c04000304824038110910050b18001d11490344a00701c10302c17041011a400408895119001b460004002d5451035800d85c0d20340070b6a0005404410741c1d8041000b0010240c215150300e6000c4d4a4505d0166035446144081d60700c54000c1c0e80c1c00038149501003005080c02c001610038030ba050f1040c0c0b404c00641280107450000121585039 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 11865654 1250 11864404 11864407
    0x1403060d080304050c0a0501020a08030c0706060b0d14060105070b060d02040b1008040501050606030402090103060c0c080a050a020606042702030f0a030207030308010504050c0a0f090503060106170903030103120503040302070801060b 102
    0x5100e1b20b018034094008017801c0c00038140300324a986030f143d81408020000024a0310020f026000c11405038405005050703c0d10803943c079104c5204001e0300800380d01024258601a4401041c003d40c01502980ca0440d40895002c80c00d646400600c03644407103a100c02c9820079101c106e0070a00c2ea658540b10030a1014640d40c0844030314050408509544001e04240c1c0200001c106100140c0c0b180c0242e139065030f4010710003148c1101d81020450702d03100c0408002d400880c0200780401142c0e4041d005006880c429800c840154540904000403100302c1152008031021543c01542d115856001004d182d074001410358840c1c008282c0039504027910f803142240160407100c024010507800c03000c0c144c00b411303080d1000c00c0f0700e2070140f002000b140b040310001001d012420b00407048991140b58550041c1c0400f605888507540e440d071000d0040d1148411140301d200341000041c18113a000020789040300d030072907003148242c4122041aa1554409403040e0118050902d010511080034080d44000340758003240603 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 11866904 1250 11865654 11865673
    0xf1206121505091c020a08040b040305011508071401020307021f0210110306120f01060315060611060109020a180e010302040b040b0a0b03090109170301080c0a061403060d08030405 79
    0x912141c0300d00d000030503100c1c40e24043c003142074000101c030034200440d4410444404c4036104140c0c40c102405200030100b0000060204140e00d418002c1d1045910600090040030007581c0051003401c039a02400350568008981000035482d00000c00d006040107005507440e020098010550200c02580d4014882400304c3c3d4054442d5410818215140c584030700c01c00948455101803001484040c042c90301c9080d01c645610310030801806141e00c0d1044181c002c212803692481d1540f100d004031030b035924890740742c204006101e6015081c2c00505114074000707071890ba82032241400c000d40088180000300140c1e8566041c18070100c11403d0301904a0705031152842d85148100320640304a20070040c02581001451900e0352220a048000da800102500d0b407a6610302c0b50041c01018110f101418813003590101010b041c0d0140021b50503101e960f01a2400c0101034000d00860241390300c1860300056844134030076240d003507400103140c00c144001d06038641e90b440c90300c440485400613a01940d09070040e5004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 11868154 1250 11866904 11866913
    0x6020909060d0c0b09040209030a06090b0610021f02090607050102090306060409080a030b0310020a0801181b08090313060210050619050105090a0515030109050709050904030f120612 80
    0x1490340c40001102c0070424120742d60340d1605044441d1003802204039001c03806002a64030703034041c3c1c0c001d17640c00782c00c613502481a8180000540300c450030544e0301c10542c0000c1111410040e00e841d20396181c6800521000501c08220348009203e40c041c058096824031602e10681d85440040031070341e0003200056190102d035410181840c40c05400f8a01c22841d00180d0300000d110310082c0d4042d55494200040c90340004800709080200c0b0741c0e4107413680317440011820f042030b41150000d8181e40211017480e082c0500a1030810071540c0220f100500c4075145c00468030603c1c414000745900a0107c0b080c0c0e401c1c140705015083c44218613030401c10242c1c1288460140540da10300c0b43c15800340c811a0140b85c1c044061072010085011801550b0410000041c00720040c2c444070024402080040c120b1120b22210b082000c031070740c00a0040044441c1010080f611880c07040107650141c0350028032060091300c4035503041d60b00f5007000440a044c8004200e080101e41640d21984000340b4180210041e0340400707291 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 11869404 1250 11868154 11868169
    0x14010605030102041404020d0b040501090207140f0a0f03020a02040212071107050604091515030501050909030c070605090d05010e030918100e090f0319030b010c030f030f0e060103060209 82
    0x490700a03072040c4810800f10b0100f40d00c1c42031240c0162401a41d60904102c918064200c2c2c00b2410707001800d20000080751140b81d0700501036280103a1302001130118045426464100e941c42c1f00c0000c2d4003002e69000070411000e80910150301c00e0048034180f0fa03103039000c2001d9030802031081d810309075924100b0000343d030000303408000745802002900304079050000140c4103020b40c0c024030550035070300c1101001140c40381c0c04810107400c84041c0c0a0305800b51900090260009000701d074098024080440c101107000000d85080c0d00c4040040c29466042950031a100c1c1c1040b0b030f06a5202000d1892a0003007442840340907a0000540040c50740d45103610144010145008100007170f10300c0d19170402c01c14a40d41c2c220442504d01d024050000f41d11018a194030b00b04450061039414040054031071080f07610151841c01c0020385450030300c0020364000064a000300081030140214403203200343e6203006d21a600480680c0c080d2900000c5600007a507145242000903001168865070000d00d104040c600a41d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 11870510 1106 11869404 11869409
    0x15130c06052a06070e0913060504080702060c011505010906080c0a0201020903060702071a030105010806010e0a12030503190b0303040909080d0207030e0406050103021806030a090f140106 82
    0x410b19403220010380308140030480900c0b00035814205001040d11070804aa505da41300d5059484504c0a000010001c40c1c000c02c0c100001c100581c0c80b1005071080b81d066034000114090304903810f6145010940115061007821202000f20701c1c1c1c4240e525500c095294800c075241c2800c0102079019009150364903505000e2841040091b942c009400070480d2850000e81c4c0c20340a5210f680ba5031440700b0300071640001d80700b10020b100c0c0d50040803c0e155051021b8a100c4003580c0da000691603c100e512030403800208000284201d441c02804180810201c11004106a0396072a000a039a03100741d03ca002c2e6143d448603149010300980905440b4a00b00c244010b6540e90602d103401402141d20101980c0314074501200400c11754401e10965003407a81d84158003d000324541c1c10005550030080020b060651150480c4000a4042030401c0d0540d1160140502081c80045507909588403034 = true := by decide +kernel

theorem cover : BRFrame.Cov 11690654 11870510 := by
  have h0 := BRFrame.cov_init 11690654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11690654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 11690654 ≤ n) (h2 : n < 11870510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
