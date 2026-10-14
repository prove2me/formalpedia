-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2843
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:54:12.366362+00:00
-- url     : https://prove2.me/submissions/9c4fd248-afec-4734-8116-7b846723392b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 511151079 ≤ n < 511330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 511152329 1250 511151079 511151171
    0x408092701120312020a0c0308090a0203150a150b1804060f0603020304030507050601061d040e10050c0f180f03030f04120602120f0912091f0507080a03 67
    0x148914104a000101000c0403d442000a11100386040d10215181c60104000031b2041c90000012408a519480421203043c4002030811610b94001e0041907522004508044030351009402c1244894a03031000019040c8100d0007103002c2d100c1101e00d00d4850180a050b402110000341009014516200c0148100d400c0070320024152000d0b400d01507502e0b1a04c0c5411120f510481a000d803540c080d01c800418081d60000350f041e01c6800420583d07100c542503408000894500d01d400c2001c0b40d1003070b448800500082c0c0c020303e600040850480781412060b01c5019101c2d80a00301d040c50142c010344402c0c0451803c02014140340714260000d43c102102c1d403030b19801034865406880142400d00032404100320380e64048070f090208071071018a80d410709803011850180251480074041c000d207000e07004400c1600f4144d440003140184100c1c4d1072806030700e17007250011035013007402e0400c9410004180402d2040740141107001e402d40c3c0001d00030424891055411350010301e41c071881e40d2045280c034a8080b81c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 511153579 1250 511152329 511152331
    0x60a0b49020d0807051f020306090a051e150a060e030f0a050604030c0609060905010c030b01020c0a172815060b030703020d14010617010e0103052104050904080927 72
    0x1010000ca076840d6094107040c1d01c0d0504c8005100b41e1901c0a605118620070f068008d90b010f14010340340c0c45425104c16a16405071034041f07031803143c02c1c041c441c040114070300048401c51b000034059800c4054200520b0200c2c8401406800400203d0071071034043e08917042c10072140f40c81f0b403d0180070700031804190341c0d0301e07403206401b80005d410401c0c0d5951b43c4080c480581d110106c43c60f44040104203448551401a000e000030001e0000841d00e0409880495400410700c00c02801000b00441ca1290500036001e0072200e84405c1501c00d40319410071072000c030007500400390484602c44c06003031582e07a844c508101c0804260004414072820030200700889041402030f29081203d9090140e1203007103e03a440b03002004803400040915000c10000a1030542280c84001002c4c42c2260110441c1c0e21184002c204103001e1100500326800340300100c1c0034060b00e83c0c0715820340214841382031600fa40c0301e001610240e000e0301d0560b92810002040080c0e4642000f8204908001c1c0c0d42c8128040301c50f01b04100d600344 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 511154829 1250 511153579 511153583
    0x1030b07081b0a0806040f060f060507170d200a05030114011b03080117120403020d02030313030804090c031803032f030402040501080f060a0b49020d 66
    0x1c0000216140d401000c0600d9000040d9102d69a2924481040103103010b0081c1c540e1801186405046041c1c42414043d400588012283c20076800b0302e001000c880960042d00c05403410f2000c800041005078007803005001c60100c2010100740440c030001000608801da100ba0f000402e000c1103070703040c040d42010549044646444030751080c1d00000c2c00582c0c1c8010161449954100c814024404064000d41428180d03800811880010ae0380000400d0740c40380c116451139402c800905c030800c01450080226140e103840682541d0400540205282d03200304560011508082c01040c280b003031440078490042c4061140c5020b00c4019184c03021030780e02081004c400ba04068032541c842035400c56414164480c1e00e0030001282c2c0e0f08042050030401500141d904901c214104000010710240002c0c0a125450f5810013602540e02c03948040d5000b40040c510494002c001c4003072024140600d016983c80302106a20005034809140041092403420000000d020700c004200701c40142e2209100506d25035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 511156079 1250 511154829 511154837
    0x11060109110405030f10050a06080604020d0317090a06050f01060e24040e09011401150809010908040b07020315010b070311160f030308101202130b0402030915090601030b07 76
    0x1020301e0600d54203031003290080f42d0144520020040001e400140c02d402c0d002c04100200103a441d8104994140c0e0694840c02203181e201a000c40e001d86082c403c2d52081501c2030400e00380d1540d03c0702d4001501501140d0704899a080582d1141c05e1144c00e029030740c0c0c0000c0003841d41125605140002c0c180940004900380243c0404035820030045c0c1d2200451005c0701c1c4044219111035554041c00450b6800b00c5500045509146503218060b000346d03499810380c1c4240204241c034004c1c040c1c040b900c20340028000503444d903d54800b240414800c00c0103002400e8000e000c1d03992047d05005144c508080c0030320581e8484441070040240030304810650b00600e40c1890561180c03082045694030780302209000311030304804c2e0500001c0900c447c2410900300d034030031b444403029607840c02d84601c01d500040c40703000b064459460341c9000501d00b0f40303056005c0e8020b03075400141e01070341003003c42d0480e08201c1d42203405500c20f005065000d40074400056005c600d040041c00d43c1d605640d101440300c00081c0c0032030140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 511157329 1250 511156079 511156091
    0x120d0e0f07030c0e0f043e01110721111e0118030b0a020a050403050f06042121140c030910021e16140a0b0112030e15090d08030609010611060109 64
    0x202540c401c01e04500c5c400801f02c007401581c00b1402211020f4102521804114801001340403014082070620490788480350403910031345401070001801c05e0800b011504521201103803003030340d03544500c401008291801d0f21a19060010f00140c2820031490380da07440b00d000410104000b0750740442c800e81c840004400962103e41d0315400751a14011030300010704070b0050300c00000c509030000400c5440745014652140e1403442645a041d451424001d600000511080d940c0c0e20306036055404001080c0f412000240680c11031112a44d248410740c2e10451003400002840313402c0c2c40421141d01c01d40d044d00d42c21441e0510340c404403001711060f0094040c05801c08182c00d14108095424904d0554002039076400c0d001100c3c3d44507444900e50030086032012210f83c0003081c409244801244120351544490400708141000c11a01045140c0c0d00c00c8500000c2240f01e0954540b8042d609000344114010b0b5181c3c20541c0800524000c160403034402c014a408440c41d81c1180020386504582580000140c6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 511158579 1250 511157329 511157363
    0x405070f05043614030a03050619210b1f05010201020f090d020a05030307030e010f0f0f2a0c09050a0b06180312070b040201020708060108120d0e0f07030c0e0f04 71
    0x54020207034405000d0714044c19250201c40c50200040105644558003000543c1d200c00400c5024400340b502840718614803e414055080c03c035501d0742c2c1129040354002d0003502c40d0744e5141c410802c00c80c0d841e24400c90800041d604403ca180e07880000c0c0000340025402c0c81302d0842c03036203507501410301003a104603d2880d084e400d54413500c1c94400a00000303030070b4a9491200f0708015203807540d044a014001000241d078182614480d283c40c1414916555401f010003c840000b107841580901d10110010004569501008a0038104480143c41a10764400c034a241c500e000c01210030091281505500380b03911014165541000c49000401600358022100c528802107450000c030314505601e503840004142040c042c1c4622200d11482c803d074202c0c1c3c41991601ca0060b240c040a103d40205940004c3e80315120340d00000c090911141c1c1c62100140400d04840301c0f610301030000f000c00c80e554001040a00621130181ea001000d00301ca829800750a00f0b00428200103040c0083c009045e41010494503d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 511159829 1250 511158579 511158671
    0xb0909040f020604060504031104090f03030f0b1f020715020a0f0c05031509100c021b1216060210020c0706080703090b09070609050f06090d0312050405070f0504 71
    0x10070070b900940f20740d4942da242e010280003988a03000030355441c092035154a0a500c0c1901808403403603030101c1f100c181540c0c5603505801402d601000b0010480e21220300c10030644a113503251144040030352803042072800c1407502900300400b681100c0d03080781800c010415102d40001f82d003180d0b26885050b0380740c0b803182e609100b89800095041203506000704606a001c1c202e2030080076000b40030030001d65050b068000015800ca420080c820005a04281840d404400e0341110101481710302401c1180d490240c0c3c4915420602c1c01e00180c85200040c510074405660b0400c01041c00c1d5210280c218038110745070207000d90f140c0d0140b00c0e51080103500d06c00600864800c1d040114015400704000c600c81c04c00105603511307141640542d40010780c2c0240700151524244003d070001d104060401480d2020034401d0201401d40c13100c0603003e200601e021020426001d21909100302d000304041c02e0507604104982d0303d890f8032a401148240c0c00c104c0c2c06498550348a05c8858020421209800402d00d540041c42e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 511161079 1250 511159829 511159853
    0x8100b0c0c01090b19050f09130c0801290d020412030c11040c140310150905030d082415070303200f0706050a0207140109030e0a0b090904 61
    0x9141000c9510a5080000506214101e5003600c3d044203283d103a6401802c68000d040c00200b402801e00c003c04002d0b8041c2c002041c08504848519243c0041d03070000c83c17142e0542045501a0517a00c880b46040d003980944054090306403d4000201032007000c260484003400d000048009000004101210020395811500180415102003207031105d2410040c004103842c100a403600703820a01072586074030f854850101ca844290706d52040846608500044c5da4000601c00b00503020750f0354010a01e0200c82c051080d00d1400d175074441004609040501d8204042c42c04404140040c0313070103010020104c1c10340540320756400612480c0c5840f4440004000a540c800302d85040c24000a450040c103134181c110894001d6940c900342904082002010241c0c800d0b1107001c4444078049c001100087c85540002c1e8221507040f6000d41014011707140c4100c50b02103640440541d039540c0d05410109504050b803060f40c400202d07007040380c0c1486d182c0002d0003480380001c081d2003020320100250801281c8002c2c0303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 511162329 1250 511161079 511161089
    0x1b07080f040e0c190228060e120c070501080f1305070b030a0207051608030406050a0e04060b0711040c0816020708030301060206060102070b0f0409090204020903100b1203030402100810 81
    0x10001605080f001d40a00703034000c032030301031100e1101c40d207800103030380000740a0301a1400c1d00f614602d007002441580034080c6081d80c045403070503228103a02046000402c412081218040360059a03070200c3c14103285420031950045060200340c10400400707020340c80b4040c1e171001c1a440340c20404100c6242c882e040c07040c103400802c1200301c08801d000c1324044640c00742800c28860001c0b520401030513009406c03086032901c9606c2c429481084217103d150703c101c000d0205031030305040159140c6010000581507521540002201c40f60100d00001409024800e441d00d8001c26581008903604000c002011868010030100e50b8500b445100002c0c60310810a2400401c40c03102900e48958407514000e40311141500c0003401485428004107040303900404980c00a10003501080c94140350100d050042c0c54442c00680e403083e805d2010707110648003404200520aa600781c00902140d4100400200752080a081101580140b041000607102c0e4140f0851100007400c01401d2655a40070615640040e5004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 511163579 1250 511162329 511162349
    0xa051c09021e06070b0405010e210306060f0c070315050606160b0601120504230d093627020a1a071a060109050915041e11121b07080f04 60
    0x4000502c074040d4408194400c401c0c3c203031008ad86c40c1c405c42c0b00c0200201420720f0210203040001c1150f030715040c8020040305a0010103182000c03842a40f250802c00e03158010790720300d018500c0c000e21409a620415500c14004c0710b400c1d00304241d16290444406030120014108020b00002c189039a0040c42c00c1c6603240046213042c0010726251801001c0b900201c10004a080041d95010104500108101038804076070340d40c030313041e45261150490a019040d5060000050300001c0c484140d03440d058007519030b03095958003040222040820038a4050640040724040241c1c2105500507074820210b0030172140f200401030455900395114001ea071040a10003800903c01d4404100740741000b4003291321480d400d0300c4680c6400e9039442400003d0034201c1d44d041001d04031281048062425512003540200b43c004401101d03203200000d102102e5848461420030240443c410060000d000480390303005c4042500c0c440480f28407503070900540542c3c02d004004100c0460020074489100003990018070307030100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 511164829 1250 511163579 511163581
    0xa17030306131e09050d091a0306010e0d03080403090608060d0b04081303240203060f040c020a02060d020d110406090b0307051c0615030605330a051c09021e06070b 72
    0x1210300000c0500c0c2804171440d0181c060745035645401010743e442201d0002504115108680e00c50130901c2d0301c01484541444038201d107000f107645600540b4a1030307a200344c45288036410982405044070119900c11410000e040040141c20b480d420300b41440d40d6480f0546008927141c13480d1604042c014440d20801d080e08200d00081440220840354100d8044c080313002ca860907040c1128010792008039403090b0803605642840d1100e06060f032101c00c0709501481955060015640041c030140e004004040b80c4940100d860700c0d5260031b9200b0242e030400d1103800c031407800d0310b081e1014180505a1040000c10040032000138440c130300034800c4a21074042d44040d441034071064071050b4020082d034004c0070804291201c40180c003901038410101540c000403d00b01d0407074114070b403191000c1c40200407030400120600e803442e40640441d0240c180c410b183d440f0607881d08070016810301403058552548020b281006450005a04c9050030b8250040350300300c0740034010075008041400791050382402003500e45000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 511166079 1250 511164829 511164881
    0x40b1309020a051306020109030e060d241502060f07030e0307060c050301090b04092006090d0506150627040216050c0123120402030c090f060a1703030613 68
    0x701c01001134000540310300000c1515100228222002002c0040200b1445819070703031207140040c0a03122407003001201103040d075455880315017141e200000794040c0154400b400d1005840c460300d400089401880100440d02c0c101502003006280900303401c0901d41c0e14050003d580d94203004480303925401c03510030f01c503440c000c3c0c2000740164070902c01c01d410140f4007022030545190900940f281160003d0304003085c003542c5101441c08036047c0591a500150803c0420125190009143e910700e00600241025190a08114800341c0354901c01611442040090b4070340075010030f41040c0c0200c41a80d0501c138542c548004075000b881400d03203000994112a2500003001700c0001d140c0e0010401b83d9501842c83c3d50006200740c40a0140002480d0110a00c00304010500f0046280d40c4140018120364484c8420b10206145050654801d801c056400c0100a150f05281e0300c0c01c2d00502d03070b901019001000c2002440d443c0c3c000a42141d21681340f091402246d2902c42d0004040c0b00c1401e821405200019 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 511167329 1250 511166079 511166087
    0x1c0b0408030411010c020d020112060f0807080f010c0c0b0405030f0c031905040b09010503060a0519090e031603050a0201061a0a020c06070c05061606142208040b1309020a 75
    0xb2503040b500741000c406100540e5102d0010412501d0f800352803a811300e02c07590b00642d414440d2411210550703650f8080000d426040e030440000400210014003034150030107055030308203009054448116030500d04011050750744402004880754102150341d0f2907458902c0e0090441c1701d1803c44c03d100c807402040601840401000070070020380340c800d1551050744842401c3d0f4450146119044800400381711000c81c1d03500400043d41d100000410b1b401525840b88001900145045800501600800c400340000b0040380708000c1d43c80c4910700110304002c01080300e01e1451a0b05000241004400f15441054a000b500440080c01e00141702c020507410300e1507500c0c00394000054850051042c942040c0080c00c00030700f01c540d080e4004080c12221824441844410750010380781c0c102c0303001e4400e21500400c80600c46e5510401c0168a903101c64105846072144030748603d40c2d41c00810080c40d0085c1c002031a0b10085404031207181c040581c4582090940701125400e40e0b0190403818000140300300082c0d48 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 511168579 1250 511167329 511167331
    0x3040b01060206090c030607110309040204030804060206070c021e01030219020c1008010e010608131203090308061c15090512030a05160503152805040c0201020a0804021c0b040803 79
    0x1c20303800c5440741d50700c200e02c0d25503881129480a416802050101e510184112041c0c003e14213104c0031070340380410001c049002c9038040c0e4425100d0100118050145ca07505004480d000960b5182505955405400080c90441d0803201010315000d1480c0250141e40242c06607242840c03400319aa4481b2403040d0081d440d0318290804901c030784900000541c40600502c00507060300c11124003010359070300300003099410b484090f0026181a0803400010009424440c865032021415940402d8030025494003070042100600510b2190b008000249580d41c1c41d245201d50042e08030385451540d131b0006074400c0040011180c00741081c055620484014049403000b5401007030800d81c10003080e0303106000710034034426458213240021410004500c4d04800004142c541420040000e0100400402080c240e401040c04000207454108002c0200b49024414240311b1210b1340001d61a00c0000040144200b00c010702c020301c551500030045240d803a09120746600a580480799000c1800d050030b1560150700 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 511169829 1250 511168579 511168589
    0x30203010e0d02100c021207050d0206011505031b0c10020910030e1b0406150c06060618030b040507210b090c0f0603180106061d03070b03270303040b01 67
    0xc2810705240c141c0000249000c1011000c0d40a4080107032416603d030701414004050800718462051b442c4050756244008100305840f640060008000c51400642400b8050340800c1740001580424540c00350400d00300d90b400558103109503da003070790410305500da000303d01080b103c03072051840200034200305900901101400301c1c3d0039a041c0114000c11070a46003040c1c445e03511500602e1810a64020b4905020403e4800500200300a9100c3d0000310060421007110303c001407000e005c410922000b44a920b01a1050303241400c80e02c20100024400c450061000400c1b00c181d4800050507c0000d00041000e410303103440c40342c464021120b43d65031300b00d543c50041d02c11901e0100031600c8440d0000c1e01b02c200c02e0010300304103079901e00300b420010b240c2c200410050402100030901402e0440a21a50300a0b0600380c8802009000d90482200c0502c140003400c1e0103580328070000d00031880d60ba01600ea00c05403420303038111411000000046506210403691943c0e110220500c010001c1e04180743d81a14 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 511171079 1250 511169829 511169831
    0x30e0d050d0e240a140904020703090e070f230f04060810090e0a020103230c030910110403020409030c050321090a200409050304091401050307030c05060304020a0302130603020301 79
    0x8a00c0c4405003680c0c000350301049040711401c0100000460045c41501e0040c00d1030400c003030600301c1c00000300e82a0b030b11110045000808250b424000300500e10b261a80020580c58200028011590084c0c0a0403907075890001503400d402c00c15a419601404807181c030210401401c1d1102d0380d03140c018061250545074104549101500845d20041901c10100c03003000441c01030408503070769001036008003171031504e43c000740c0130400044401103242e10205001e8482030705a00d940785069a00079082c00714044a480034141040241d8400401c00c10035035054035011038001034100e0591606841c24504807030003e00034040824060907806500600b105882d4000360f4900960342c88007809515008484002800320310111000c80340503030301c2c003d403400c4180041d00c0020004031686809142d46c00652140c51001e85039442c00800640408880d401000c081d03004000450655a501800d61228041d0500a0310040006019980c030020102c0066401400c0d025411015201b000c001c0e0489000590080d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 511172329 1250 511171079 511171099
    0x30c0509011a0313060902090f010302010e010c0c0e0703140106270305032703010f0906060e040203060a020f09060a03020a020c090c040b0c100212010e0c0403030c030e0d050d0e 78
    0xb0300e024002c038078940040e0300740a07403659407008a005404200a442a9082a80e80c045000180c031405401800313a04000001d1105624601c00145141c10510000e030420001c3c0c2c00c040d00064441d400081541d0f000030758030450b80c0e20701c20103d008042c0710904040f401c070701400000760b55030001c0c5409000c41070044202c800704d00341c141030660160315104c0202a41c1c0100120312000c04442d00241490402150403802c80e00040c1c0007a0954802c08011010950f540c408203040020314800d5400400d003140c84401c2c18500303a0002a1146030041038208910340020301903807115001001c54848401c0100349580718142c03508001c00070741211000303c02520500031728550751f10342809228400e00f030003c0c6007454a4200240c034592500320002514040c8240c4044011100d480d001400c0748101394403004890350325090606070b007010094942c900940042005001003540300075180701c40394060416001401c2c00c100403a07020300074460040e00c2d90041101603078005511055580d041c10007110b1000c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 511173579 1250 511172329 511172339
    0xd0c03020f033a05010b210c09091518180105010b0f0901020313090b100c0213020921010e010b010e1c050a0602070c03030908030702100e130204030c050901 69
    0x1882c03107000e003640c10b07940d42c1103480074004003403055142c5080500128070103043d1100c4040c6090340c0c403e07004125143d4000ca1719045812604118140d00d45d500c0d000c07c80182404400c1c80c1462141000039030203590b0103400141a5241607003011500100500b1004030242455441d00c04a2000c0e038080c45200140c28101c009588140a5141a1005481130900d000c4401640b00215441410802d05502050000b40c08a140c9109030308000c0540c0c10012965807501030402424000d6050420300344100c00b01214013688914082e0640111204c0c00140e4070366081000035130581c1c20001088140002c40d00700c00b940b040640042030080f2101d002845080c45580c01076522031000b461403038100645c65410611001300030142000240a102a41c81d441d1098031010b00b42c0e48020010744402550f84020003c0651110389140100202e5000c0c0d4280040c60780000e1140d8030401c8030204220400d03a44120030b503a45401c1a10507840c00d00c04560701e0350b40e8600b00c8003e2580b0320a4501c2800700d40f000042d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 511174829 1250 511173579 511173583
    0x1e06020304061b020c120a0c15020111031b090a0302130c0912021f2c0f090705160503091816080403120e0a0804090203060405180a20030d0c03020f 65
    0x4249161340c000d084c01500c2035050040118403940d80020a1140c0542000418a0521308002412404c1c1032444941d003501000b0342900c0d284010004001010001c001c1940101d02d24010500400e010391651401e0701c04c009a221001a00080c3d4004100b1080d60101c1e145580400150360b007685454001c580d55403c8020f9030010348078081e40000d9508481411030341d0540004140650030309003599810b80d00001081d9442d00e8103a0b000c00d602000c2d903281101d25007a034071041b00340f000711142100b034680294002e0060141001403040c00000f905100200681407080c1c81040201500058884218810350a4541825903042d0691030101041c0c0e2007a501c1181c4040c4182d415882b40308155091701412030040805881a030300354005d0b040a42c00042d21031008000034103003030f00c5c050380780c1c01d04504100441d00040c01c9070300000710748002001110000300324140040d4018075881c3d50320450501c403d89606c811705500c1c0e85400f83c510888407464010301706031b6005d0f01903800c95040318a4086200d03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 511176079 1250 511174829 511174871
    0x210603120d09141207030810050d0f05011424120d0c060908070303020301210c1208040b030f010e0f070e090601180603271104091e0602030406 63
    0x180491504001010032600c032500240c221034401c50b100f59210090100e4241045071008001c038003450700240c240141940310381180e41081c0078111501500345040d00180304607505d038034020200f10945a000d8184403080d0b000d60bc0c0480311034100d542c0c52030308070079890a00c0d11107070711a08024481201d861007418483c8089035083c061800a20001444c10803e90792003034400c10840b01e0780e44400c80c20000801c86400340000d14441d845c00b50300d030350420480301d01410b52200103400e000040240c180101d00b0032807180c0e0441d101d080680c94000c02070b01f08090360307100d0368115501c3c5420010138022030b51605028281210940030132203080340c0341c4240e0404038410a948010000701c0789042d00b041440e2069020343c218105040c55241c032030303980a8011502c045980140c3c040b9176501100b004060501c01c070030804008030a03c41b030b54601c141d540c0c0c0c00c1c0408038214180c095980d41c21410201300001d02c0c60000300804540e250b01c509040d00e03019000c1c1d84111400c44010342484101003410492504c0e40e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 511177329 1250 511176079 511176103
    0x6060c050712020d060908070201090e07120f06050a030c2405040b1309140411011b06021b070906031112030304020f06192f0706120b06210603 63
    0x16000861500c0c031050b40d240400441a640030021183c4800061664855984210701c0b41c40c05a880e54102d000140644102f84e0000c01c0680c810310400c541c8903440347c4240d02c3c060344039900103400c0402454000040c4030316006150030801c100b10100911200318002c02c102c900f20691881d110400c032108210b034001d5407001e0310100d041030000b880262141c202404600c950303001d8589400d40d40d02a40c0c016169440c440300b08008400c402d00090000303100e55408404000c1c28171590b00d07000f07400c2000c64200f844030045c02565010840e4015420071440800e40302810200302e6040b15101d059810007040b9a1108a60600d0725030001e11050130031045080908440001842c03d5940c0e9800348500c5034030004000c3c2d403211b0100701d86490400f0310200068a040702d9920100445101ca840c010322140600015045050303503d070000ea903000004010313041e6121840c081d5400c0030040858406451001502c9c0d500000114070305521216400c079041802e4540444000c50b83c94038001c0c0740e1031740050510 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 511178579 1250 511177329 511177333
    0x1712090a0b1813051603020a050d0b0d1209061e1403131407050a050409260d05010b22030201050d0b010e0604171b01022d010c02030a020106060c05 65
    0xc011540140c8094480b00900240c4051400c0884000900009100e00c148140c1a5070718144088151840d0754021014402d0804603e4a41c00d004045c00a004801d0014541c03a1540c1d0040840e0311039180c000c004560006000d5421280320201401c1600c40303020b480000f403142c50608e914403c0c041e028462081c1c03151a01a21400d41d106507101d55030008181780142e502036000c0d240001d040c0e8510310454181040984030903420102004102e4034140d02940c0316038204009103001c1031042a016603c4ada4000704a0000000000c1080c000d010303080b611000146007100000e00c40899400420010703a4032000042c11400e000201140d0440602004e400960140980d404240c5a607020000e40e10f414100ba10480b10103030300207440c1c0d9000e80c00252003c98502c81c00f014401040120210f100450b4404281070088440001c2d6107083c26050028186d00c0104a40007140140e42d41c0411440483c000307005d40d5082c10b0010b9036a80c42129541c0042d0b10704500012070038071401484200c030b580140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 511179829 1250 511178579 511178599
    0x3090f1f05041a0a020901032009040e0a060c02030702011e090b03070903202b080a0509040513030e04110d0b01020c1206010317251b171209 62
    0x1030030034010310004100301c40440d1030b1060710048070084000b0303074071505070a500941c1c1e4400c080700060540d204d44441d01030880d05481c02c3c1c115080000b068600e949c005490005640380045021480d00303104440c003514051800d02a1340d9069030210060484034000c1e2614094084099000c040685240d140240003031000c10b818044080500000c0d41c114005d41342c0000398a4aa403030320b0020071003000003000101c103003e2860400e420418075900b078a1444005510080c008052040f0007006000310040c0b40800c002a0811014000e070240d030768280000c0d20802c41340c0f8002c2440c00a106104c5015400310f0034440b01c0d0314039460a8011140c415040d810306a0810350b20b0f56881d00500300740d51144d81940104124a0703a83c1d01c85010810003000d01100400e00d651550500d136805041454580e03102c0c45003044508840d001031003031850007510b01d480080d1202c419040c1110340300c0c0220340030030700c41050503000603030700030303901c6003142c0d40b508138400ea403480c51190f80c40746114460140340a4102c03107501 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 511181079 1250 511179829 511179883
    0x3040204050c040b07140c06040801020c010609020720040f0f090323071e0f0309060e030115062012040302010806040b010c02132a030c020a080d0e070803040b03090f 73
    0x404842c0008054000c80c0d1f40300c1c9000002070010340090b0400451a980407440458014090241d1401003c99420841c03411029844440b202e003203600301002070003034861410b160707a242c0354001d03007044801c2c2d04100300c0c51608100150240c0b404440a40004425040000c3c0c4510882c41c00c04403000104030b0745240c0842d0f039440c0318a00c0c1202e20700c2000d04005641f00c601042000d84000e4411f0300c03995464042ca4181800070300a100c0051840e8002c0c1e140c600d0300703100f40071003070604010385a07941002201c1741415a2075113150400a07596040c540a0b80c0f19007100d0940c01000340054030700c01d8a4201140d0b942405001c119032070303030340c0140c0029045c0305010b0150500341040c0c000c0c4840c0d440040303601200f40c10701460300d950141c1d0108018280c0a60210f1055051142d0b415420952000c0d0085442546446900d40602490b0100035550b407810040120341c10441d04c0c0080c20101c00b500d44880d913608030705206400481d0b140040d03004203602004130180201d002d1000c4400d0300d8801041e0003101c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 511182329 1250 511181079 511181093
    0x2032509110c1203040506091f020c030904060e060a120b010306050c0c060f16020d020d0305090a0609120e0d2a0815042307050d02010e09040803040204050c040b07 72
    0x14070007195200208014607040c559080c400a034812105110340d550728202840c0051400e41d00034600c07200b50300040070194108118a02c48030241e4540b500158031803012025160441c45110bc42a50044c07504100255868005e15503d03c41c600851700e55070095614050340310b521800c110001c05843c0410300600000e55650b00c529003004c0100340782401d0040d003000c00c41c40d20781c00b41e0380402c111b16841c00b00884007c02800344445610580302611480703a020360301950360382d10783c2040400c1c140c68400059032100700704418442250044400d10140515050031101c01c00c4940d140d00c0003546c00745074000d01b814508440e00c1016406444000300004162aa542c2480059400b01b000850b10070300003421502082150400c5001c0d003541c500f5403c103840c000d40170601a80d220041d440c3c0c140c2e240c0140134008035a40301240c1d419a01550740f00c1c03551004031400c01780c44808582c06a1a441808184444c43d0003640c416442650200300541320014003800b140038a00c03d43c664034504110400000c2d031a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 511183579 1250 511182329 511182341
    0x608120a02010207020a0f0f12110d050c0d06060f0501020a020d062403050f010c020d0c080702031608060103051203060a030201031a0405010924050a030308070e0607080702032509 79
    0x800d100050130b08580d540050a010583d41c4540d80903001441d0500c010261030342100d0040000d24100840303520503544200d244500c2c032101e00e108803801c0c1541000c3c04010b01581c80e00800080c80c12201e29580d140c04002400d640c011103000c3c0710418004607195000081c82d038801d60b001006a8000d00c025590b2001910303422505180c208a40421703d04030300e030300313180080103180f040018250246118a6480c2142c20208407007045511003001c0d41a06a0410009580140c10255050f6206e40c5800400d29000a4100860240f110301000240c6d480e40454083d060764400c034259059110801203490003400182e9000d41c0c8143d040008000641c06a8070101d038900030380c81446070319028080007800b1107400740d002c102c445484100d01c03a00000e4254070203940841039952002400d061501141c240d00b15400024140080780c0f0100d4a039501800c406000d0100c01856141d5400b241e151100841e009088124001c0c0b04103400300d04004010003a40c1025140d03000249211032400d2581c10107061 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 511184829 1250 511183579 511183597
    0x10309051e1c0215090a0f061a010c0c050103020c160905061008070e010c06090b01181104080304155a1227020f031c08060120070e0a060812 62
    0x4284406c1c44001140742c29942c009030700030705c000207580e4485000015400c1640807541d040002d0050440000f40c410856001620303c00c3c40c0068540c1c0e00c2c504290302e0601c903081e00c20001c500c100f00c00100142550801449020190340041c1d40f082d6801c0141d400003803d0b40c100d4041007182418a0455109034400c551540c00780d00c01041c000b440740c407100740008d82a00854140450b401003000100f800e405103c0004010003505403070b00d45041c008030f450b4001c60042c0c1c031899100034040d58003644940c0005410021401e20031032009451071b10741c01442c81c4020040c45809032a5405907030620790000ca07150940c8601903500d000f0303040000c1240d02c5408452401e820b02e5332030501b0701c4e400700c1000364000000e02c1d100445001076910700420079448900003203d4480c1e0322401019816014040300480c01032500d0034802c086841e0360f801071f100300803202400182082d400419000306031000454008171640d00300d10100c10386403400150142c809034006c003100c66005106d450604516040108605c403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 511186079 1250 511184829 511184833
    0x32c011413390807050105091c0218010b070302060c070b07180b0d0b0f0303040b04091e14040b090d211103070207061409010c080306010309051e1c021509 68
    0x30501282d40c0701c1001d1280400c0301e8208103600501036504100a031101420003400c2c071500b0600140d0018001101b010182d0407200ca840380d1210454450388218001c81c01e015014480e690f8460b041d0030200d412014007a0010310030340b00400e04500c0e42d20205c8115540142e005240c6a903815000d54881ca000d0190310982601c10f08000351101400c4050001c0b840071445c0400c0f5500da0030100000c0e185400c2c1101c0c0320f1b8008110801c21540608111021036610050125000c0c010b051003e01e018022405950000e05051103540240c00080d42e40e80300b1841030034001003c1c0c845c0e0683d203550300258a100750100d211001061030221400c4c1c4880b030300305103507140411640d6080d007800c4a241c206649940250f444154240034841e0400c1c54a405504041d4040e42401d1000c00020859000f42070090314a0f103000000c580c2d0350b4400d8000340303e520303000b038202c3d0fa00130000b210412150390340c1103911001c0c0c0642d40c1c1011b07800300945840100116a640100322544400d103c9060100000e44200f604d8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 511187329 1250 511186079 511186133
    0x30609060d0507080a0b06030d020d21020d06031a01060504050d140d0906020f0c0d030507030302090915030d0302031e06010c12080403030b010302210601032c011413 73
    0x200c0c100515405004561302900c2003a0040c03800d0640200003400403440b03a004002c030300e4181a400240e0102842892500da0900703440040700b110090036411105541e5800018031000c0441d5503040755003204c1c07040c800c44d0110808844200203d00080c0924000610200400c101342d20300402001c0c5003501031440b0140003080741c0182441e0000748000c0401042d40317000c04005c06a01404100b078101e030017002910300d03110042d00141482401c210000d051000104d01002850721943c140c4514500180c150740b42c90411885022001e040d02064502c64464800d200c14028400c2c001d0f00d024031042c2c088059440000004010003100c01840b4038100000c082184020030410300392034200d00d9280c0c441070440c0c206810000e090318101c1141034103050040003c1100306500d0202d10803600607224000702c2c6521400012030180c6a012031301c0c0c840c4a0103490151344002607181d43c982031003c0800821416001032840348411900b1a98100303480700c41000780d00032800603080c1200203d0141d80c02d10340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 511188579 1250 511187329 511187333
    0x6040608010504111c0f0221030a030b040f0b0f0d0f151506030e0303040210090b040612050108150c030705210a0b0102063306040303050c06010911030609060d 70
    0x21581d0071101904c0e080c460564011031800c141c46280300001020341c0a0584120f142c840708000000804001e00500100aa0170082d0a0072050581c01410000540f035440b49400f0707004001e840714003a6184554500071544070a40c1c1588140019028003511017004a82c4c0c100030440e0100d511942a9100c1c0940740c00f9070002031442a000d810003180000001d400f14941c01e00f00e8413031085030094000c0c980380c1300703800106810020950394800d078120f80405480c240c04d0402c460940380c0342e00190052101140119282e5000710103012502c0e081c11040000b40e81c2d03500303920b654070035400b01c080810007603502141405004000441c3d002038107040ca00d10b04041112980643d0003032040c01d50700b4940d8401801080052070040301c3c45400300340300500407410300561107503421000e21401c0701c142c10004032143d644c40606048101215006149a44a690b0390070082c00320b42c40051001e816025110000c04c02d01018410045802c02600342282586d0b100405c3c80914030025282070360140f122101100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 511189829 1250 511188579 511188581
    0x40207020a0e010608010503010504020d0f0302070509090f06090c0d150e030d020c0c180c0a09050a0f0f0801150b0a12050103050106060f020a0210080c520303050604060801 76
    0x1005080010b1a64560740c03602e0001444604103820161113a41880c00340009030340c82e2001070ad03040d078200700111202e11003481c1c10380c50400f660788a1500003204908001c0c40380c0c030100c0c01c0c0c055140d03c8401d54040e5908c071440c0c2c1e9150b81c11080c0a903809049440a10007050b400b20f140e100c0440c0640000480f1501021002d01c1c3d9001a520800310b9500014044842c44050103c1d1914500540d580d03070074598418441554140c000781000c9103080081100c2914500c64060031006100281510340003907110f00210702c1841d03407402030b062210910140040c0b21b4174144a04c3c11441c01d0005d002c03000c03500300401c1d03200c0c507400704550a040000844448a640310a4800e40e0300961081c400011207518282d4090101c020500b11101550000d42643c0c01507281c9200700d04c0c40009520b0601e00d590340342c2100010500034449620f107030001840ca02d442840c480c1d80254501c40c43da0b544c8400c01e00c140021550202c9240144020f016030702480310300000e0203900204e40040000784049a1107848404841c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 511191079 1250 511189829 511189849
    0x620010204150e031504020f13020c030712020a0b01090c11031314011b020f181f12120f02030f0c0a02210703080a0201021603030c020708061504090204020702 70
    0x1c070b911040d02d242d4145003a0000c20481c0441c000f40c0c05030032485020b07811100401e400030710190007442c5000e081812a03860568605400d0340030841152640842d42c9250354a811504048510f5030f4030219503010740f400020540b55075540081c640c00643e08100c00c07480586074407615034007800f41c5805800d00380e560a00c003604110201c004901c6040d460500071140f84904055500d0520400c00404600c880c8480791203600b4503019038002103900898000701d4140801c0004043c03d14040d002440000c1c050001403514842e0748a003640041c2c0d4403075040c1e54516040c000c0041002c41140366151583c0d0254035a45922402801541c0c18400e8885080c646580314071001c01d81500004820b01c2103182c8682c202d0030203c1c64984602e0881089041182c1d100200d0001805d1144045030008945100b50112a65003401e100780c1e0001d10903d240c041c029082e105a807401600401a0100b0b2050000070400d105003414401903d600e2450303814040100104030040e270308607800308075082c00340c0c44009140c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 511192329 1250 511191079 511191089
    0x150c101a1c061a01020d030e1908130e0c070f0515011215020304050a170423010807030506011d031504050606030d170114042004150809070620010204 66
    0x780d805101035280c8031007101d503490b280b100f0000707283c254100b080c0d9002640c902c03228114200080c1da014138a107034a1814413001006612580e5040441d02004034260107005031049041d0034180316a10751000018010045803007001240d0141714100102c2c02c110b02d1070307035046c3c000d01c150303020818505003101d030951090704080c141c8904030400d002009045010001400140300045055080550740d071900c501558034060301c281d4140340d500110121181c1103c005212103d480b20308003e407007881300a840322130b4441c1408100b0000006103900e02a00425100c4da10583d200b000e8002c1d0007003e44640303c0044010780d0035110307460700d068141111550017030065004500400251400e04109450502046e40c04002c0008500200c150a100d01da89581507552400178450303041400c1c404580200889201b086200e400c5040034420b02c0c1132000200140d4540250078100072410140c1a10000025100314209501a660802c843e030f2040c81c6043c0b034440d00e2015603951031282000182a42c010782c1007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 511193579 1250 511192329 511192369
    0x30703140720011211032d04150b240f0c0609030d5f0a051e0105040b190303030e06010e0103030806010e0604170309150c101a 56
    0xd0b40556070014242100c0a5480700b05100e25003004955513503e0001400907610001d0024078004c50011421016031042c1d0b03903610141c0c4c01d01d09400c05004440710002c180082d80c2c5001c0ca101c030340e410f01600e003600c1a4a455002d18000f00700344450600c40d4000c0561105407032051190024000084c030485004035204130040d621081d058401d4022038007244088a07800403034400001c60601e080d0800e81c89400072100c000101020030031090060360418281ca50317004c09020306160380b1011421450b00420420408000c0c55446130983c440c4031429402e00394400b456000100300d00c0c6000c3d01301c2003803c0d03809400031500440b8140d07500100000e0380c0089020030707118907951107410010413a20340100380d0140400084d51460701c02812014000c0d111504012402a03200010384501085500504000b5000035039914a000e606441e03400510500f40300354083d0703050410b40e1b0000019241c444154030b0142c2004c256100b150700080a074105070003010212032010781d01c6a5501c50000c0c50060700740c80 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 511194829 1250 511193579 511193633
    0x211c18030303090c060c0201020d05130515070501060506180405130204050412030c0507031e02071a0a0212040522061a1803062406040306050a02040510020106080307031407 76
    0x9824070300300e81d05800c00030401492442d00801f42c0e0380011449624596810000d590700102111220002443c2e0001500100c01740402c8901d01c04910082c81560f000d88020441252a40200003007841080742180d990868a034980a81c4d1416512803a00040c0108400511802c5540401e050703035003c54045c1c40100b60011515030403500741c0607000c2c4504071868075624121031a50041c040d0304040c518581080c0d8260544254180200b0044014020b041c40302400008914036014041e80b202c0c50f107000501601485082c04000c01e0141c8085c3e880040c4412030207010210300e108080301012107401f259031610000030b04108136243e1884411a00360b01d065485019010485801e0b810b1210180258000810071070b000c1c0c80d103a0b000f03404409001d0755003406020b00c0001010340c000d540003c0c1050703243c40c050100c0903550380d005004840c001d079081c00d940e54211909030308171405070ac507100c0150000c100400c0042e05c10311148130f802040a100c1404d000d0240c407400c00110312444541403110b0120 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 511196079 1250 511194829 511194833
    0x5090319020c0a060c021201060e0f0406020720010e0303070b0a050702030f0a0305150d020904060e0111030f010f0b0f19170a05010924150e1e211c1803030309 70
    0x400d411400f00c400009c0c03001624107058201c03100801003000a080002502140400103250121141541c101c2d1005812180032404400c0e610080f000090100d104030a90504d14200407050b280e035660815500d6001c2c0d40ca6280c2500034000007000c41c021400300300680ca440c80100b0010b082225104d0b41d00150364502900000360510500c40041e2082c1c1c99038842c1c4005035078802e5181e03802a17200c1c0e0003003003030700b0001c00c007601420b9441c280ca03580440100c00c00c540450000646812074401f00503a0403c03960720881c5841030301c2040f6840102840401c402c0302611006220315000c00c0f8a0b2625030381c0c2c0b03501286181d0300c2d6002070381d00100c40740c1c0b100010840c2e12079900514100036050b030b01105202e45400c18502c41c04d101031103449483c02e08140c500c80018007840f60741e88540c1026006018014004100760742c0c0c210341e10200d40c8900014034800110150004c141c0c542d2150749402803000800054140c0403980018009404200c0c2c020304082e440040080000002d40c0300e9140496408003034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 511197329 1250 511196079 511196089
    0x618020d050708160c29060a0e060616030216150e031b0409020f0904050307060509070609030201200729130b0d0b060406050d0c020105090319020c0a060c02 69
    0x900a1020004544140001d41020fa5010151025903040103038104030380d0725001070078522120f100c0511480c0c1b035501c503810b0740c9046000c070710444d8201c80c069007642c4c9940321810285020740d20745401080500c81c00c1e15601c1c4980e00055024001e0044810b80c0c401c100001840c0703103160300304a200816402c1001705881c6c20201e0f6840d1814210090120082e0844140e11180d1041c1411403040ea2180100025526000001e0a007103401800804240c40c180c1802a503075803044000b00c60311442c0034006803542c030011594200f51101990b541d428589150011105079101e800224800c02540c3d0303030504900750800450005010146200300f81d40d006146a038550a880302d00c00c0301c02c0c90f0400071003040c802c42d002c580080d14621202140c4400401c504400140f01c0284025082700d8000b03004160b00740c0102c040c005850b54800148811005240c04030b090740c005591300790700c40d4014400c1c03c0441403c2c1c0c02c0351a00811a01c110368080c0c850b58005514bc085540c00070020034a0034450000354141 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 511198579 1250 511197329 511197331
    0x141e1f0504020f0c161a090a05040905030c120414060d180c080c04061a0304050f160f12020d030e0d0605101a030709062604110405100503030316030618020d05 70
    0x1c05503c02c4c10130300e4018030012003207110041544071b09000036825020342c1c0c1d190f1444041c04000d0020041107034a071500c07aa41c0e52201d45c440300d440c85002807a19003110148200d405840d6041219445800032105012894102401039583d940d201d200c0c2c4082c0314041000716000c1030140350901c10951610285504010b142c81549000d142410350030700070000355420040228030f00305415a500d640e542012400c5c4116104179164078050b5264451120110355a420292001000301c12441966494490300d071b11815070740290844a001d4001d008240500301e1180c4072107014062081000495070382004640c4201c869014034512030314180503040c0300d00e5880010307011240f007103841c5091414010b4420000e40c4120410000c8007081c281714444546c029031413191401000041900340780c940303901c0c40e554246500d4002c6103800f0000d01c6c4000042c5140085890240140d49180c071148500c0920303c0d490044101450b49a10340011b83c0702c20803101070300243c01e182e40103807605114009281a150 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 511199829 1250 511198579 511198603
    0x8130302040c020a0f0b040f410c13152304060602060f0603010603080a020a02130c05040b0309030432010804020a0b0c070b0d141e1f0504020f0c 64
    0x300132158040001c0340e03a044038008035080300248081d0741d42c0789044000589440d50050900300e00084900c1c0752106a15000b440c2d074a581c149070421580362011560351103030642a41c9881d844042d0360b0f100c504002d0b00421080b21a20070201d1503081300c1d00d81c0d81031325143e548030030000941d4081100210064909860106801710740900c8100d03d011002035481401800c01d419111115001c02e843da80c00758000c00095a0214000380c8030840490007070f48407160108103a0003504545480d4142450501c00c110043c401e584803241040c0c00c10404000c00c2d00000c4c2a81d020744401c010101e03540c5640d00164604022204c1400c0c0408010200c1904190b03442c1c44090501100205000050390b40c020001c081e0b685a41d010358888604044840c60404198001e07001500c0010b0f980c00c56203841d4014030f45181c0200480b104585440c64111402101458440424103110022540802400c03c410301c01008020002d0082c1d030700ca0300054104d91100400c405e065400242c0c4030043c2c8814003aa02c030381c0b4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 511201079 1250 511199829 511199833
    0xc030c060c09060703050c010902130b030c120d0c0606030c08010b1302090105030703020306040b091f06141b160b0d05070206310f06061d130201080403090308130302040c02 76
    0x80d075002c08508140103c10f001014458003040703041007103100b580500f0b4003a4000b401450300030040395040c00208a208a064000e00410228070101e05140007408421a010300041181c8445d0141c110341d0203540c1c0303404844603030700c0d000700102007020b038640303034026224400002828002d1030040100b103480c60043c0c0802140184403495460fa000003c0c0d907405009410050f80d01d0307440300c0000d4003d003400c405141d401500c3c1d50501c200f482920381041d80d007269001c0785140642d22031a080d12803013030307080c0c44110b174190401903404804400e01e1540050030280044480d46c0300c2c01405500c1c104580d8115508019002c20750390001c0b0040c2c000c60f030b0001c80b68000b401e030724242841441180c01061101c403000114a1010b2030180c00f400740c5175800035800c00030550b0341c4029860300c0005400b10384100d4104540c40404466005142038a060040b020041401c40e5074405030b0040d6406440140b085d42481142900040814800c0c40107080f44940c00000d02103030390031071042004503400f034140c400c119 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 511202329 1250 511201079 511201087
    0xc2304150c0f030f0c0f05061f030c0302062217070e04120c050c0303040e19050f07030c0909020c1e0706140705010e030a02060a0605010c0c0e06010e060c030c060c 72
    0x856400c07000c02000d5901480c1c030f003c484c071140b10705076203040d80c42c0c20090100c40e55042c2c8406001c0c0100300240644c00700044482c1400c080584698584042c5c00080c00341d60304c50008000500e480d80003450341a03030030500750500c10042981c0e01c00041c0b590780550b9501000114403204114103000e108003070260802e01100340d05140e201c1880b1828020045400d20000290860901c0801c00013824582c0004003225a142d0b01c03140098402002030392044000780c29800d100c1c8142e021030140601c01c1e80c01c034074024101e91b60100d0450180104101c18002d0003284100403488041c2d600080070000f5141e0000c210b02c00039440c40c0010080440c40c40140c68020060500c06170380c1c01210288440045100952180d940c2e00b03050713004203811144050684000a49000e2041e008140144100c04c00c0c0c41c10001d03980c0c0e4400550f030070300c00c4c0203006158440c41803003070058034030344c0f101c058005406141040d21a810a40442e100f907100303c48a0702c0e140d0001c903408400381400c1140c142e000e808030201c0350070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 511203579 1250 511202329 511202333
    0x1603020d0f140921030f1504020c07050a0909050d0c150903090510110709020c07051c0b070f0509040c0309050a0b0114120703060509100203010e04060606050306090a0c2304150c 78
    0x4e6010103012030740410740320000318042542540c0301c03c41f01c000050003159200140005590346218520070680110300700d81c0005034100d030340c2c03003000c071030b160800c1c041c01d4040c0800c88211007a0a1101e0116240a003003a000c000d403407202e1082c092036a210362100c904245c03d0000b0030580003844440741040116000101184090218000c41103030707000140582c031000c00c44611420988150403580c1c2144070811700c04034800004030425266070092001400340e4640381c004841c4c95241200f994042042041845844d0500e6803203404446507901d0b000a40144d03a03650030382840c040e80d8054800400e030b840140000c4030a83c2010440e40b6040b01c40201c1c040fa04607150340c99441c10312000c5c01c4295140001081e0410900420100f103513030030b104550340e6840d1119240e10540c140da040d13403594502440820124001c2c404c0720301580d001018944955103080300000601a10a4610200310940f94800340c807609a90500080c0c441c0000c07070903101d5060885006014592008040030000c00c2c181100c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 511204829 1250 511203579 511203643
    0x9050612070e0c0705060f04020f06070f240c020f0618060a1119032003060607120302270f09060d140102040f17060705031603020d0f1409 61
    0x4851440c0030612159480d5140e00d5804c1c01184005002400345404000e20900005840b43c419482200d03941150030030344041c4012406030040c001c0c050681c40003034801084107280c0320140c9641c1040e4068110500400305c00c1500d1200c104d64000d07038000031020100000070b00905502506205081d0108440301e5242907480e180900484091550b50007480200ac55240c12105020f400e84405160a82c840000400500545440308140d01c13440c805c11a9010704001105d000da40002c00150515075640c0314403246240400041082c540c7c00c102c607d40c92240c100c56840d6071030011340c8007a460011a01804005400907484500c260403140400c00c65079600364045060682100b01e00b40542491b14103280240f02d681c02c8802121040c0000040e031031003050307115048401c40e1080d1800c98440e20415100c9010668a0b0554009450074a030682403095000d0708810f007022402180841d1481e859104a030381780c04021605010450400c20341583c1008003045181d11030280130308010707040c0141c40c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 511206079 1250 511204829 511204843
    0x402040b040b18121b0a170d080f070c120c0b0c1804051b180904060203150405010501020c12160e0f070c02103b0114070804090207020a0b0f030109050612 68
    0x181c3e17500c80c98418240c40340c0300d014640300503001610b80090a40c125a000302c0e0b41c0e028170020040042c1803100001c00c602c0148400500515054540c6620460b0325030304ca800c03008560301c440040040b080c2c523800102c2c142c0c401d518080d8048007120355030303100c2c04a00380c0000c5050740d40c036a01035030512081c0b0106002419071000c0402ca503c04403526154180ba20cc440340103803104036a845041032090105002c01d603070040d0302612801c054500d1058102040c841950402d03c0f0703040c056044001c0203003150411103000c10803440003406031000c3d004003d83c001703c07090458000040354144507017004900014185c0040d00450507003030038448004550300260f00c500164800408200030400710300240901d8950080031ba84407000900c03d820500c500c8030a20348040341d089070010700090440030040350070703904440c4e4540c0c2040c3d03074038076041c140f10201000c1d6000c100100e801c00b030040c00005a8050728405441e00c040461222036903945401881c400f0f40318080d0480e44071b03195190040140b6040003d01c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 511207329 1250 511206079 511206103
    0xf0e04080309160801021201120c05011805041a010206070207030c210b0f041205070807080306031c03020414012c121005040506100815060402040b040b1812 69
    0x2070707a640c0d1002d820600b0a10040c0c5102c1c5040d1403420702090101040d0090314020f00003003204400c0e6030b640c42d0080110440304034054803500890b80c041c0210f5104a020090b000c03000c00d9890a80c43c1d4550115040f1281000184e02d883e030081c062000640e814410282c0188483c070003001018116164480106034034400e0030380c1c0003240c260024140c0100308404003429041107034821240780803010900d2a80d02141d040320349403081c007002c1c1c0085001d241a2555a900080c440d400c0403900d66402e2440e074009002d881e030510900440c01c10000b078511208a042070b0b03a943c050388440ca4407920b03e81e0703140700c11640d40c1400426617400f01200d07490100d002903d92001c0c011501c48501c0800b06410700b04449201c0c040380243c2541c40d60340809908001c0c09140f1907000c840485c0c8e00c1880b4045207050728002e0181c139402000d462140d40e04030342681500110004c01c01860270760703aa82c60100a030300560004a05030b00116102140c64030703075200c00c041c00f80107407000106040c3c12060b46803105003c0740300f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 511208579 1250 511207329 511207343
    0x50a050f070f12052805070e010c06060509040302070e0a0513030c061d01021206060a02030415050c030403150f0905060601050711191e080d26010e0702070f0e04 71
    0x44007920503c281c1c1005041498a00200803a050040110342d00d00907400c0e01409104640c40411100c543c248a500e2041410390342d04040c84140d00c00444084200b8041038a820740c48400105582d50740310303416801644207400808070b07180792071036608458100038140010079141c64200550104c041c10300c1401d0035414035205060204501d130000c010001d078001440d11422205d200e004d080350560040a843c0d81307920221400c0e40d02c0e80c080007a18411241c400005030418002003160107003c849640e44030160f81049410a00f54501039851034100da4015600000c0038860204580014495220b01031a203800030b024050080d143c0640d106000340a2f80e04000c0e002031544140303d000f180c940704c038110080060a203400e490100040d20b4034280074800b040c80d15401040101c0b80600c0001d0116030381d16001e4456580b007040282c40e0790510452000440c29424441e0b18619140c1139200e0203080140c85403100d03400c010174000d1234030316079400c5009203480b094404d20011520f03003002544142d02c081 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 511209829 1250 511208579 511208597
    0x160c06020c0115180f090804030605061c0303021e072003070f141525020d0219060207080f10090311030f120c070803191d060a050a050f07 61
    0x121950041800214191103000540000700b4580c41c0b034403050a0004100c80107025450b540c2c5104d05c2125542c03140101000c0080004100040b030540000303a0013400249180a558001c448955020b8041c481c101c00180d8000740000f41000040a40e5628000c00e504090800300e0f00c0d600d9608404d0f0b08031115010504c5c00d43d01200c90307a01080030070042e04000150198080c0c1d6210300c0c0d050f60b6841d11003d0722030000c030200e80c00b044201900381c80c5c0e100c40300781d200544d0568448492206480b240016078104001c1c100010141e107074002e54007a0b880c400014015a00d1030b1800c000e0504200da0024202500300e4010000d48520000300c08148490450b400680008640760648035410101010021400089101001800030748054600300400c4081c55806664560f003d400034411880b006007030346010710101d03d98696035008003000c155400300000300f110424500ea540c0741100400c1090a9000204201d241300d00d0340515600241001e42c00d00541c140102c480d1042c14000303180b4010442215 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 511211079 1250 511209829 511209847
    0x71407150626010c082208090a0b0a03060b030601090501180302040603080c0c040c14032e030615120b0c0403080f0306120a03121e0c020d08160c0602 66
    0x9880040182448800b40c0381c605042a0503200740c5032020402200c951074030000c140c865024031052445440151007401103400507403001c800200c0e4007030003600c400b070b0140508c01c41d0781c81d0800340c14040d116242c0150b807241300ca0900101075a01c50342000e45450010b10038000e1503601b100400d001c0e1802401c1144401071100d55140e80142a544040d511a003455000020300441c44024244800c0380000d844c08400c00200f4482986d41540200700040c0c00010150940703d145000745402c420030a1042c083c1911104069411030500a89003182c1c102d442070400c09c2000d1845500c3c00401210404440185014042e102541e180c290140401205c01c000442d241848030846000e1940b0036400d98503000540c58002a030741048070a640030340c42c11902141c90100c00120409944e41c55914860b0f031503010390116014081808040c01d100d024007080c010b41c030b0807038010340400302c044c2e60090a014072400b4008110000241c81d8442a515040c45a450a5840a50300e0340c03803134100c034002da0340d80d80342 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 511212329 1250 511211079 511211081
    0x307201b0607050a06020d0c08100501021b01030b18241c140f0106050a1d0601050904020702030613020901050a230a050d1410020c210c060a090b07140715 68
    0x102001740014400102d4040d15162a8070501c000d214955841c500c6a03100e070383c800ca1241043c040c0d640542d001d040c5003052200142141860401d040c5008a50400d41c0c002040303030504000c00e03a040c402e6001c420802220200c070b03100360600c40c507136848045100900300072a030340000342c40d81072000c100c00c41c0c21001440000e80c400a520007481c4110317168a0354a908050082202e030040b6445031040110008040c0b00340b0031054080342824400e0043d5032541c0d401990168046802142c00079001d0140001680d000e100e25881000d010b040d8038444001d510411241c00c00503040140315949020050003203904003031307003140d80ba10a240850b515002550000740c1e644e05507481564815001650401000f40e0500081c5464030814105c881503661a40c8901c1031303000e916040081d0341d0044030b2424082c01d120050080e018180700b5102c2c41c1c202d90880050414000300d84070240c0350788845000c001c006104480341c2e48900c140c60681c10350303045206200c2051140700b501a2400c1489a421907500b007507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 511213579 1250 511212329 511212343
    0x2010c0504090b03070f121a06100e13020a020105060906060f030a020f040308040b090301290d0f140f0705100e1e03010e010b010230070302030f0307201b060705 71
    0x225005005585941465204206141c200da440d10010084408d4158402c0303058042c0c0c100405da140d404800903030864440044100e86c60784034480300c1c0d600381040000c0c4028a014449540085454544079007070080208003e0802809940204010003001902c001602d411024851300983c3d109009803e2800c1c43c05541c002400c800e80005001500a02106c010420345005030001d004428421600208029600b00301038178890300c1ca420301c2101d05d003680f2803c00c01071040b010300701284c08640343d5140000b6042000c001a07407206c018400b078018204200c8009200440d42c007040c1100c0110001d14410100140c54052034000040c2c3e1803542c03036581c0c1030034145c038050002c104c0380d140031004a02070031403020a54058010f40120622020341d0b10212542c2c00c1c175111002e2440131081548580561100300300360214081070189a038079040d01c000a501498055a079031600a0080d0b10302040c880315004003503003652180c094104004c00340c00080d1100341080313400c151501d0303450900702d081541d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 511214829 1250 511213579 511213589
    0xf060a0f0f03060f0902070b0f010f051003140406060501021614010309110409050705010324140a030c060503180102030f0a11041a041508090a0803220b0106020c0102010c0504090b0307 81
    0x41c05580854010170341d6000d008414050703441c840180d15000d101c8001d1003000c0c0945038100074800b00174001030401c040d0200f8100000d18000910082030790241003900b4080d203088687c581c40700d40c10006580d04018000309001900d03500001c292400030000302c68801140c910b41810b480d203441400b40082d00340c1a1600d8040580280802c40485c500380e03403520300c03a01400f4042881e0400c440780030120075521424810300090b10141c03050500c00721180e44441e0210303403540040c2013034000c000101444000d80080c010740d00c071541c403400d025062459040c80013401c0b294a80c41841001142e8100016494118410440c0003d580c00040301c44040b9115640040540780d080703040c0340480c610f654004000b03c91a0320110302c0000d0040204440988081c0c9004c4d02691004003918003280080d4029500115182044c20301a0f00301c01030740e0107118905105484400d00a801044655018004444c0d620f0b024802001000107950024000b4010f0707004401e11513070344940021454508100c0030700a02 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 511216079 1250 511214829 511214849
    0x7031a040c0906120606080a0504080906040b0a0f05030402030607140f1c06080609030307110109020d0f050606030105010b07080c12040b0d0b0102070501051b010b06180f060a0f0f0306 81
    0x440101c01070b10240c0188070f0032000a0940c00c40041c8100c0600c101401d42e6442c0c0d1f2a110103441c3c0c101eaa40241170054000d60f045c00c02004240d403241d0340e00d00200000c1542954464450043c01005007040d05115202d80600200700200b000581c2d000c00c400754010660b090082a032100d9088950183c000c060f00034140c13140003d680313130004040100c0707480e040c5c0d00782d44240002a12a000c0e592684000d0702d201c2d015500c00e00100d60703181d01494007120b0300007248000060440054000034002d5443d90000d880c00518081c4040c281320007807203496803100c0c09070028403465240c60002c51051081d000003800688000c5102c1c101541e0501c0304130000e065150030561140d450344000c1100e42d00100d00805103510342084507406500101d01c0360125003050310791a06000d0174000b81907403801c80081a0b401365503039880c07449003070307403500084d040c0c0300d4228010300c1052581400f401400071241c040d0f10f11941b030600c2180d070b80070707880201c21102c00650301d002008881c101d201a006010306170081c000349 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 511217329 1250 511216079 511216091
    0x1f06051c0c0207050a1203092705010e06011101050906130312050f0603060709080709090201030f093e0f010c0f0308040c15020a0b13061805150702030307031a04 71
    0x8a900003070040544c0d2048440030100750b030700c00c500c00505044030401400301d509a0400c001815103425000b00c5403c110390b264903131001e50355942049810980021113000300e881c00b48134441d680080c5190201c00f0000c002c1200e400c2508000340d031620000e2240140b442c0e035543c000101446002010820803501c04c0600c400d0503d0b119004107205d08913450343c083d21034003000403103640c802e26519044444c482e015292031030810118001400c46103c09a06040d1121041d030220f4616110fa103084d079004602c00b000882401d215801d1102074401c24014180254444104a0040e02c00c0305640c0130084400d901c6914640300142c411607541000548040c51b40e02e10300f414950080c007510310442c46220703081061900c81e01140c014031500030010f00103a000c8105000001d61000802d90403001000036059002d141d9503801e02030f90722030b0f49260f500e07003014103040702004420062111101283d00021007545008240256280801060310040545038020018200e8164448580340c034409030050042c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 511218579 1250 511217329 511217351
    0xf051008041205071a011d100b09010311130312030e0705210a03020d02191a07110102040b04050a09090b0c090607020616020a0b0c0304031103030c071d1f06051c 71
    0x201785024403600d044008098000600d44454400c0ca500c0b4803002c0c02d424081505107100740e40140c20400030241070694440b40d4070011500900034000e4074401800800141c0c0c11480c1621160002c070114000349400c0c049003401455020400300d0a8640a8404004404000300300c00b00c035007402c48000d025401010241c405155021a01c041c11000355000c03034a02c207841c4071507003980c0000354602510807110610a00002a2100d09d0150010018a00b0030b00309940102d2050072684140e01504251a00040400150420800c10401422800d40c10000503c458403400c003050700051910544001c0000c17900358540e5840b081e05c8545070044c00d065110802c20101d0031f0301c1038102609034801e01c18000e0028201a0344422140c21250a0002e1410603180d69240c41c100d000044000b075160105122880032000c040100c0001480500c41d1175560b069800c603200d69440e030150008480503130040488640c0c0700307001002822a88030340b6050380e603070800c0d03402c0c00060b0b840c1103801d40c003503070900100c80b803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 511219829 1250 511218579 511218623
    0x9080f19030e070e010b0a03090b0709060216060e1c0f111206090c0112110c031308070305031b0a0b0f16030b090a05040c03080309070f05100804120507 67
    0x2003220580e00c0070000580705a211a5840350144140d821a003911030041c02001401e80140200a54078100801c840020381d65144407002c048610400181700c203c4100302007503040103010500b02508601c042854180301009201101100f07016009450507410007880c0c998601e01040034035007000d0584030740e607594504500c0349507109030010300c1401c1c00403442c250044c1c0030844602a0480c2c0009044041412006582580c8502c1c001c0c60a25a66015480d500c0d5020b0300914206403601c01031551408140280c001039041500b00056990000b0014030000e0000000c907114120800001021102036507612450844000c400601d80030007203040c008540c0c0901401c502a0380c4819001c42e035075140b410101d088403108101e40340e210703c2041c040303040d8980541c08245c20500503400c040d005516601c232964a6442610b50b89107130b81c0312140400038800210b0400e0050041102c0e00807509201d280e00515010002d071010b800c000d400304441d1060307406081100c003626401240c801c00351004802c166 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 511221079 1250 511219829 511219867
    0x60e0a0210030e0601090e030403080d0b040c0f0e012f0d0f020a0b190e060c180d0506270109050312010b0c0601030b04060b090a050601110d1209080f 66
    0x34080ca111549140041d4040c0c0211040580352500601d00d0b07a1a210070000601035002c0340d48024041044080040b03146100105900c8030300e548049074016011042c0000c8640a00d030050400110012000030039501507600074028400b41707011190075100035201d004140717040340c410303544c0c0c0c18034002d80301201404160103480c0c0480e0303242c0b52002c4000781c5080c0d0b221010220b00801c0490100001401407a05860804000f00d1041c00010010104441507240800a5a03541419500801c0c03c02d0025102c04401e0306d0303480251141590710420ba507595030f0b1030314050101040111424200502390203d0080d1203e1038004070000c1c00050300e03904040c1d48a174029407401101d90800c0001040d00381001048640d101407080050800b61318545034001d8180000e4021540142c40344c08070b4403655140110b56014040d070341c40024076802e00308000b51906854074100c0d04590041d03000c150b10b0a4120b00e803a03480e00b24110b400300e420380007490a10f40920a0b600121076918010a0024185569103894 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 511222329 1250 511221079 511221083
    0x1e091c020c04050f0c0a12020408030304030c120c0b040b0901200d152106020d050a050601020d110d031a060d0e0f07030b070c030e121b0d2607060e0a 66
    0xb0095901d03135a00754a4582e00494169000c4002040500d09052181e00c408013086848540182015201c40025066500c143e50540000e110001c29005014201d07001c1d150300b840504001d03042000650340c201051000510203029401c0d0000000c0c02d0760400e420041d046140032000341d40b41d80c50900405544d800c04007152200d00d1512901d0322045e240078500106940c1240c0c114042102400305841910140341400c50328180c083c000380400d42c149000740740c00307100d01900120740f500d450000280703440d01d007400f40400c01003c081e001718840c0c000318620310180b413103240c045840405140543d03940241e052150f9000700e00055004121030716544014000210380d07050700d0814002c803070300541d5a400c9000c007030a2801010041200d50703000340307803c1c00614031a040c0310090f07082520004d940c5006551521141c0e0f0011086200c542c1c1c9202d5030b64040d0042210303049155420f980311086090240740051103203196500d00d500c4805a07100c20380342c406d5404001400b048c0034000c2c1d0715446600401003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 511223579 1250 511222329 511222331
    0xc0a06110a0201060503061e19020a0e10050307141b250501020a05100506010909020c1b220b2b03090f0617070516051e01051e091c020c04 61
    0x1001c40c8525012071024040c0501a62a01c6100c901c608c4862180c2d501400b142509441d14182c10340300300050025042c83c04041c3c440c0b01050006c03000303210340905440c0404040107410030400142541280307104840042c0130020a84034040801d04031f0303048910340c0c0d2000c031601c0354a01316410109007428118441d5071a141007038647d5514070042e03903a0b0305040da004005d40c015002554a480b001e61103240e00c08014940340d4001561042c9480032030780b04405184694024221035120b41d4140e03182c19030700308425a0141d41c000010705980305820b1280e8070240c4010344813410544190389028140c9810f03200000305002018200441d003444988803002100400d10841d0002051408a4903a0089908580700c0729021b041d0116140000180181054203108061061002020822104641240c400c10007000ca5141e038002d083e04000c4000a2005a6030500003008905025480d19549102d031b030f14074400090b00e800a0139811b013180d00b041481d502265811205200b94002a980501a42514 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 511224829 1250 511223579 511223591
    0x5010c031116050c0d030f1d0105040e0406020409060b0307091d010e06030703060f1a0d050316080d0f0902040506010801050306060d030207150201021306080411060c0a06110a0201 79
    0x40103505a40041040c0405400c05025030000301c19080c00d5011020720941c00d403120a01c1090001e004503201020640008000200c10041c064201000089980e51164140d94540038100028160702c600e00408040c010640702040c20060550103842c060900354005006035500c0e000c225600c1c2c1c1040b81c04100060880900060004d40105003040c00c02c00f001128295a08121403161004c2000e0403040c3c140c4100500000032950500c0b030300c00700300c02c101000701d041901c42e41ca0f000500b4004900c0c3d031044a407502c0c2c0000042c000400c4850171081c008010a0104140c1040341440c0600b040026900b410301c080c07103e5030a01d030790051a950384210340400450303c0780801100c00c41e009004107905580a040403501e40e281c4200406072051003072046400e0a03489000b2540b01d1a034416090002d41e40128444400484502d4080042c043c0352130520468078068440000524484c09064000c210008680024400a0000f40d0000d0782050043c44118400710002815901c8200d00c00f0055282075 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 511226079 1250 511224829 511224851
    0xf1b0706080f0c1b1e0f0c09161404030309030201120212040b090c1f0206091c0302070602090616020913020a03200d050307020a09020405060a110705130204030501 72
    0x204214007980780d003808440d10b42c1c0da807414840a980907610b64045004010500801c002c0200174480c0001c1c40310400346038820303038051000c1c5415070200311280e003034005240d025048c2d00d40800c680e038010002d2540005103c800341c0c081d6508400c4003006403600c1800600842419001030103003048038401c1e40c0380300619803091185000c031b0040d00c814240341c2c002c6001141c00b1802e0850159008038400068a41000c480c00010b01d8010b1351446107140380c1d810724920166250103000f1680e0108030040a80340010900c21040e00131407160110005150f03000c2501818080d20364166403040e400508019034404006500f407607130251102e4200c2c8102c10010024101400707a8000150642e0b000e00b5820714039083d079840c110144150b24016020f1560303808400d446603521180300824038002d0000d03550303c6810380140103484050303800036503103180104810449915854115400c0100707606c0c2c21103030b0280080000b0b061140c81c3e48202e034840042c801c0131517169100d81c010011280b24400030400d0350070740 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 511227329 1250 511226079 511226087
    0x61207080c070809010e010909020d0515150409180c061d190605160f0c03060b180c0d06081c230708130902161e1203110f1b0706 57
    0x81080182200d2043c8512551355028402035a410001410325000e440d031549143c0080360041c00b11140c0b81c41d200c4080c8144501c43c0920f45046d4001a07a601700414103020308540d05c2d104a1003100c007500d5450500ad10f10118400c800140640c0c45400b000e40245d4441c0001e00c440100d51100c0d2050701c8070601141c1902d8200954a1605103000100307000fa40340c81e50a1700c95801c000c40914003504c5100c0300c000040e009244c40071069105200c0002220300f0740c01d10030b0848603950041806960032401c208081d84441d080941c0c0441340001e0306030381d03a4507241410040c1040358007903403a521030f00e070700d520b8003911405006000380b0642d42c81070b2184013813815918034001e45075000319500d88104521004500300301c3c001c1102080070707030364000741d165030700b140808a074000c4226810941c03000001d81d00308180c1d140c2840700f0550511412100c107031247c643d903030040342c04041541419030b42d12050003900300f988250b030b0100f010750b45210345400e94441078021022007404809283d00074050041012802 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 511228579 1250 511227329 511227337
    0x90f110a05090c0d0b030f0a0302060708010803030103020f0d0b04120e03010203041a0408130306020301030b0a0b0102100c180f05090f0f040611070213090203100b03060a1505061207080c 82
    0xc02000b128098a0395a00040b01e40d00142e03ea4060984640c1c03c00c500f51000c100d42e01c0241d5080d00200b04000c2c850400030b041c03031030251566081040b1a401000314860000076039040d01c2d0102c1c1c010240100f0480020b0220280c1071008200f4000101040b052110601d039400b030034015038a5940001c0b25000c01c045c200d01c8200d0740201548950301c0d007868040303103a0010325031042c4280030b404c4c074100e01a50f030980c140d146a402100c14540000c014020400316042c0035420600c0c4400c14017000d694500040e450b032000f00120480160344081c0390034078501c01c808444003480043c80380c2c0c5100b9128a08030144900302c0c000c050040356440c0214040e64450300e0243d211700c1e242c16240442e626070799601c4010f030041a5034221301c1c28007800310002580d20b9554200004010040006d43d1500901c14142001050a207580703101d0324009d940a07440c0c5001c960a03a200c8601d140000e0198102c2008039415051600400d800032000300d8502842a40c100c00c03140180d0054a0710081507880c0d0100340b8030303442 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 511229829 1250 511228579 511228589
    0x170f0601030b04141203090c0607120e01050f040f1d06010903260406030c0908061308030c1603050d1803090b0c07090e0102040311030d0e150d090f110a 67
    0x8401001003010031070840d4016041403144007290389407880c11040b1407030170040303d04c8500c5c802400020701011003800c01110341c030f20b541a40d01c1c3c0d091034441d4485203000901210340b60700b400460708007900030b0782c0300c0c1e0101d945812684203281d482350346480600c0f060352143d00962849880703840c41801002e071803044d040c0c0300e1003050799009045402d603629410078804a0f0341c407034100204081d07413000000842001c0c00103840b007654000741e26880c0540003410301403039612140c21030308100c0078054041c00ca0748c642e85045400000d860765903140c07101420214801d442002c10003a004004900c10554082d004100c8140120403e100d222403e140742e41c002d6180c0d0340000e0104d03d0481080240d861200082e00c83c03221210142c0345120350305c03040d020960310004030388900d41e580050180308200d8082184074981074150010088074140050252464103005040c5218081d003021108110716543c0c1103400300c0046a00522804c40c1528082e0619010401c04454680683c44d404c0b80c4c909000209600b224 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 511231079 1250 511229829 511229833
    0x10b09060714100203070e1003050408040b0c0a05030708121005011706041b0206090d0306050906061b030a0c120507021806120304080a0605070f230403140601170f 72
    0x101c46941e6080140780d044019903001c1c007450043c00184a058070185101d0341c00ca0315424010760079003042245c2e071009083c3d141c061510313280500c40800c10030421703503003a201400081039903000c10008003031501e0002c5400401611001a1400400403603401404c0c0c03114122901100d1a01e6400300544500418010280001c0e4a200d246103507150741c980c45500841302420000d514042106c060140d00416407581d80583c0c048014061009000c03c09000203e000e4502002094103020000d03541d502d014102920849011031541d20483c1000e00e490030801040d401c4030f40d21011500003500b0303106149030607a40c1000407060310340d1a034010f404036401c941e030041c4050460200c41d0868400b0700720180100e038004112514101110b20104018030262048000a0075885007519154040e503400070544800c00444443c200c001d9074204501c1745100d03c3c2d9041d148803012140400050074010f41d0300c058030141d03261807403001000022800f54140c0d5000d500b00b61b00c2c121309103200340c0e07a50959651803c1a07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 511232329 1250 511231079 511231087
    0xf180f052704030509040b0d032007030f020f032a0a0f080307030c140f0a1b0e010e0a02090405180f240a06090203040822032102010906020d0b0306010b0906 69
    0xd2044c801003003403100062000440444510100c3c0043c50404021004a102504605d104031011400303406d5440c3c840e4014081d150455840c400d0740c001c880d01c024000c070440e07444401150ba00740b0410310f070f011402401c0c2183c1401600300400025680c02050301455a45002152003078a0740300404c25203980c00015032030a400d680e000c030341c1e060550100b91088070040d140503181440501c80f00d03424009880091070461021304000310b154280b107130700300d25010b0115420001c102c032210a4a0440e2a10f0103000b4150743d80c91180d40c0a840b480700e0b80c1b5801072038402007280c4a900500c5410140c1c191104950380b000c13540859a41d1000081e00c54000c03d100006003400d10403140140a900418007600424519508c007406401e9800a0724102c421000c089111410358140420b484079807918840c11085451450b00c4511a110101e209050301d0301104040092080c002d40011085075440042190343d80b2500152800400c0300540c1184030780112400061400e103070409480311441c0041059140c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 511233579 1250 511232329 511232333
    0xf0309050603011a090a0513090303050f0f271912030509071208070501021b060708070f050304050f07090608010c021609181a15011b02010f180f052704 67
    0x640c1218400c075034006d1140702e02081c0754507402d0422030415030808004c01c110ba200c0c900a411b540c00102002069070b0900100848926180710094000c03469501082d81030702c603905500c540880703510313a01c2040e06c141c2c0c1d0710b4030091904000480b20f107801078070009154406031030211b09842d82a15000c00c694030580d018003404200e541c012200c180710310f1016140c03031070700d030794450980e0000b08141c0611462203010701c50350441402466440300103032030040d02520340203c0143c00503283c1c04041003040310200000e0100101080001c1d103101081c0c048407800ca03a9130709040d02818a6016281c115402c00d48031201450000400c80851204400000c240c00d0404618000910140001c1c0280c1007200c85018082011510031f0519800c50412020303c40c81e022000780701918080390340740c0c1003101884a00c542c00d031240c102c0f1084aa8246001e0003071012195007141c8010540600c00c4540a803000002440321304400d1800031200181c0f0010702481014a203a4801d11071130311040f0329a9000c1c000540 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 511234829 1250 511233579 511233629
    0x20105061509061e041a0705030d1d01021218121227010234020411040819060608032a070b0a08090106050906031e0c0301090f030905060301 62
    0xc00e8003070160806051203000e1081c50740003841c80d40d044c1841800018284803070800c0d90030f404140e00e840311b815443d0071600d42d070b45c5581e44501404c58500541d80c844031041e103421030480101842c800b40080d511042e00080300007030405d040c0ca52a05801c11241c1101c00d40300c001c1100b4609042e0507401c075041507910358034060809401808940302a0948801d0715400042070070821455420000050715070090310780d200c41814826540d9806403090a8040c814640c0c00c020318011241d050b10080b9500c440f180458459008039003181e0094090041c0e0101d18000d80d4020040080c01100144403642d504d540c503946921079003003521a81e440050707071020245070310034403030404100078421070354141d5a40d00302c19015006244080300242c440d505218006109018200c0a00011210f1071001d041010000755a000c02d40f000307280d00d81c8901880b13606160240311034401c44030040c00038400c030000c070300d8028418000800d044000c41c001075000f184074140142078074141d914070750025410000d5071203030030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 511236079 1250 511234829 511234837
    0x106050405010c1b0602060115020303331c17030408270a0e04030206090607020c221103040213050405060f04020310140a061a040603020f161a070201050615 69
    0x244c0d0304000003102508071010140c3c4103008258940c0940125414040810701207031404450204550060041c40421900c84503800f4059848030400d0360031458104280088071440c80c501c82e800840d08c1902211000807c03903807031880b8031800b900e003201401045060800d000c152005400544c00344011303004004041502c0a03400c4001c0324a80311010000009071000190380c02c1006050f000b031040c441013680401203142c115088401a00c61468011030096450800d0500140b1840c00500c003030300b40c000c1240d44a802c8074080030040c450200426080c520310b502c02d03034049015040440280b8074080f12849624020b41d80040a07010315113075600c0b03504040c1c00c05001641e2501401044001d07490302d03071203106000001c03a03a01000300e1034480c3e695012035103a80c0c4400b150703440303260015000100d0310781180c01f69440d60900580307680031003c056405010b0f400c41b01c03403200c85400804c024030014300d00000702081c41260044c15aa80d0040403402d848040d24036982080f1840702c80b2034600c124902030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 511237329 1250 511236079 511236083
    0xc03070c0c0b0c0c01080105042a140301150f09030c0e06011103031801050105030a0203120309010e0a060f0c05191112040f05032e02071a040312060503060106050405010c 75
    0x1241100340c0341d4082d94003560145103036076119400081d0300c032059604a0301017401000300315010462404541800a1010a1500c52680201c0c811407c8498540210341e0300e400542081d0301c842d00c9685512035015041000c17107a8401240075020388105a92203030203000152a8082550070010b89094041c160f4820084c0406062040728070482c0d406540800c0514030414400346208030a410314848107003180c1b01a0000781c003a41102e01018056240064074000d001c04a401e420395030780d125940c9034014241810301d00c266000300c801410a001c0700c0d8005043c0206e2240d02000b001d00500030035240b81c4070344075100c028013904105000480c1c1c020780741c200240815006a42c504508840d072401c00303034042d40001e10366901c03540d000d02c12401e0412034182c9181542984035044065110140e0b000030041120156280e0002812030401c45008400020081940100407060800380780260412205c5480c4e406144c0c40c0460004182c136001500c2070480e031090f20b43d02c2ca000d00303100046071030b10070312002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 511238579 1250 511237329 511237343
    0x306060b090d150207060c0302130e011a03090c06070312050a0923011d030a090b07081b0a050109060f1a010e0607020402040b030403081609030203062d010b0c010b03060c03070c 78
    0x2003800031806ea4004d0b04e280702215500140d0798000d8103141610b83c4142d42200c0380f890000744c014030058000e61200507a800044050644130303601d86054920704000740e0b041a41025011800ca001c05420200000503144100000c2c0416036648240800b1604c0c1030700050000c010014100d540340c0500f400618a092520001003280040d20316400203a402e0842d40103401d6100054042080740d00440000140c03000501c1c191408106407111038440c0200c4c00c4240b00c1c1070304003003040541d400411540c001e40ea4070078002e02c51071520b0b00b851002085601d0303413140810300f0100d0300f0308000780e201401406400142c41d1710b0724a41540051100d240c1082000720303042a8200000303c0d813210004043c512070780c8650b6840c221454511241600454280c0100040c0117003d8428001030780c000c5070301688401015491000140041d840740c1c521001d40c140b40112035951400480c41404840c005d15480076840300902c01e1100040c00e0650340c040807101d0043d000c005001080741ea45c8603100d030b2416a806200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 511239829 1250 511238579 511238587
    0x1e05030403080c03090a03031e080c0d0c1106070e040515010206070e0f18060a0e040c23060a0903050d05040b12070c33140f10090903090306060b090d1502 68
    0x12401b0001c0e603400941c04509000184032081401c8070300e81720031030414540b03c411410006108000ca00410b0400190030b41c4602c41460317141c0c812000b80c408000500c0440f0000c0c10301001c003500c040104803400d030080e82808005130380500c0b0030310f50300c0c03410b00107078010100742d5a140c2048030b55940c4400d65503402020629070504503036465070120b6882054010080390303030512170100b00344100e03642c7c0880ca4000c0d8901c02c10012038031031450a011141e000e64841c5424241c20704082d16961202c41c400e600a1011551500d080c2d8007100070300c240c901c07900440c0c015012a040503155401140300d0700e00344840401c041100b880141d00030075082651414200001c0300d040e900c0d082903544484c00981d01d049400d5024114502d1180c0c12840001500002c0149000303180280d8411070008240d03100b59500c504c0424140c02400861500a003e0303804200324156032880c001b08105060304c0706503552030810002260740080c010881d000d424008180c514488084c5c0e5400c640e0406015255140950902c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 511241079 1250 511239829 511239847
    0xf060e180a18080c1006080307150b0616020405060102010b10030e10050903180a030b0105011b050d0512152202040b1b010c02070810110c0a0308041e05030403080c03 73
    0x40003400c181c842c001d61a184c82c500d900707181ca019908011a281281031030130800140001000303c40a15400a17041515a001c2e0b4220602819607201015008000000c524400c140c080c04506800b51080718180540e4455000481c02c0c0d4000742e892503445920703c3e0010324924082c1d03000940c0c042c102070541e05280e2010001800b2074a0813102030350309400c0014406040b85149039880a0796004864498100b421600d8440a900e414000d807418007848102d441000d0304803524100d400d035403013000c54500301c2e01d030b250007001078000559920100d60394001180f400d070800c0142c0418080045c0081341035100d5100140b602e9004d14903260283d6230700308008550000755000070500e4602d00c103003040d08140103502450031240c802c3c06841c11500410414010804085910f0540100c410804240c0703089007111940c1c10710035a1007106403441102d218408054100c1380c040d01c00d0b401002c40c610003e9106034080914100300d0001405908100014030016007400c0141c0440210170086034200352400d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 511242329 1250 511241079 511241111
    0xa210803040606210f030e010513030326010305151305032107030c020d080a0e100b0405160903030f110a030c05010e0c0306011208090303070c0f060e180a 68
    0x640701a039a50343c0b038480034003d8000f00c128a40b600c040541920f1080c0c200c44e00d81c002c003c00c0d103000c020100b086420f207180031684070308192100c144120a00c81a5540d807440c0103003000c658241c00350207083c0031310111710b09507125006542c100c941013800b41c1202040301940ca880641c0042c00100a408514210700c04220100090240c00c100c45060010501c0c8140c0c40702c2e516140104010201414000c1d0039100c1d40c1e0216200c903810041e820200d5282c0c40d443d0860002e0424070005140074881d0a81c5200d00c0381031a085071401c180c069a04001940b14000c030045501c4901c8544004120300005c20000a072068140140340da103145003240c9403242da074007e94184035460717005a000803090900e003028010b080c42180c40d134200840c0100301e044043d502081d261401440f40c035001428401c000c105000e010001c861444070010b080c3c0e0369518003450507403050060340c00385929218030f14501054450068004920318580105000c041d440c821060010a0200610000101d62070700400074101c111 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 511243579 1250 511242329 511242331
    0x40b03010801060302010813080a030c090506070303020d0c020a0302120a0e06040909140321090a121d06072004060306020a0c03020c2704030203090306010306091208060a210803 78
    0x5840c00400d502d444e5000040c0101400340c0341c42d20f011001000d900000304031000320707100111241000b03d032080c0030710000e07640c403a940c1d03001c20781044000030180101607055000741200c030541001048504501e0404a0340c40412810040c0560f0050349a24101c5030003102400040f5460326100d00022000703404241c1540069000c5040b107901e40f201e007002c101300921000b83e0000240d00450501d0078040c03000d842e100d00c40a003103040744040408103000c5103052245031141038002031000407480068600401546000e03000c00180100554555000e1618108407441c42e6003140515000c0d06840c80403524180b00101281d500550340d110020002e00d445c005481c28507038a49540c190f140040c207000c0e04052a59528520072900941c160301c1c03070b0000240c0207502d10b0305284010510303911807906910710b100c0d0278001603162180341c00000801c0039039003003c102a4401d09254504e01840c0d42c083c0c4042c0c10a03225190f1100e0340f4a002d1000d0200c1c03507920540c0603a0b855010f00125000c0e200c411090740 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 511244829 1250 511243579 511243589
    0x121c0f020306010e0f03030d020730110601060f111f050601141c020f040e090d110105060a300605180703080a120605130f050109060515030a02040b0301 67
    0xd000300c2044081d603003001114003803c405440302059541c0785400661a481800c6d940c1800755400704000d818800700502c68240003143c100c240e03584202e113601130742c444500580700d000014003007002c81410800215001d4100c4140303440d2254035900d802000e450000105002c5603691080e2100b0301d013000081030044160351010f68000649007007440006055020032411a40080342c1040500449003d003500c5825000f80302c80c00580759003045950310f140344120707803114a001d4a201d040c04100203010441420034446902d0b08096244020038860030784100315001035105007800320400917060150400c0c10f1843c0000005083c03410088003480100907c40426945580e80d6801c0000d4141804942d5100801d040700a0000f20f00e9561154032503c41c071903024081202c40d0604c500d22100980101c00603010007840f03c0000e1160314512030041403c0c0b00302400403030500c0000240510b4600ca02c109895020b0103580c0380110082c10031020b9800540340c803481503070800000a51591440195020304 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 511246079 1250 511244829 511244831
    0x110105041115040605121314071401031427010c08100e0103021003110f0a020303061f0e01321c020a05030f0711030c0f1b0102121c0f 59
    0x40503030018442c04404044014500e00307400c00040c01040c0d00b02080e98061014080032420558440e070710b4042805007981c00801045a1fa98107000340e40c0085000026503038404143da007101c801c0001101510101c0320042000d40c0390f1400303d0400d003181000c000c295042c041d01307410010039540401d400c60307101c17100c03940000b40780505020502c4407842c02907004051007005200b540d41507400090071034601c0e81c01901856035a181101c0e80c1004202038510034407280514984807200c62034069100d070300031110548100050700e501d1411000820300c4030707001d8480b42d4401c2c0b0b0a6581c680150381099480b0002d0700a040102c4c40304850144e85072502032807000780e90625445034140c0c00348108002c0c41001109602c0d00500841c4070a07541b1030f0035658412068501c014094460342c40c10703284072009000503d16808009901d0145110010341101c0c8801100121801e41120b01c9881c1e082c15843d04003240160044c0c80c01a54260410024000c0e0728a0130003023281c3c100181540d00110780741110750421107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 511247329 1250 511246079 511246103
    0x702041d0f0606040c2106050a0f14030f0c060c03040f1203140a0212220e090708190201030b1c0c03031413180b041503061808091011010504 62
    0x111814402c030364200380c00351414404824091809030900d0f983d80c03080c0c840688840c0e0b100300f4a6245c2c0d0001e6004140240004c600580c8032101d5085205660058590100c0204c0c01d10b81141000201c00d074940c510040a84100c285480c2000810340c0300d1854424184010300022550500240c040d00c000d00e410399031f0308440f0040d46005040019401d5034180321080600480c00d4490300803aa00c603680c1e81e080382c91503031071072100c8200400101c02c40d070300d2540c006240030206131803221000c682d0066001c00b040300c3d0290341e6036450907500d1102c2440d509509000300c02000c0154000d400040c4445401010a150303441c03400300200d0b8488107054260707031842d0500300c20000d05400410b07042840c10290001c80c1350907540c4010f4041500288500c010b40b40b00f0400c03c5010700740d25030044d40c40240c000d1041c018218401e8808ad00075440740800d4601900d480b018000300c0d84000d040840441d407004500d420806140104400321030505d18042c01c1c01503048003811140020300ca82807103640718080344004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 511248579 1250 511247329 511247353
    0x2030901050906100e040c170a021309033e0c09010f06080402010c1e0f02120325030509090f0901050105090c04030615271515050702041d 61
    0x95440c050040825900084103001125608012201c25204440f48200e203903100e611f03105801c00f91a9000694412410081142c029008035401c0a114000c56a407042ca220001142040791004c86008002c104031200c0200c1023040501c070380000780d02c0c1c0049451018800070f0780540c1041e0440341401c694008498804440c613000d141140548080c0c5d0300c1041050800030301034244100a8030281c14030203003804070341c10003c0c0351021040c425045001c601e82166285008030f203009449008038480c020203125004110000000e48451141c0d4446080c200c03507032003817100c801c0440c000054082210801c124a1542c0390030340401d001e4986d00280040030704d00520249d0840d181a0806449034a841003400115036130001a5010760b500140d002503a50300c0318040740c4084111f40d0001070800194154684212400928844180c1c0310440c2803100410141104d0840b400a002e80c50b81c1c40034001c55803c0c45031040020b420342a101810000c0c2901341c03400e082c5020454104038054aa1140c0882d01c0c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 511249829 1250 511248579 511248581
    0x3080a0306080105041a10210303051e011707030602181201060e270a05070303121107060515090a023f040f060f060e0114100e041d0102030901 63
    0x1c024841c18000f00140d0400b607849408100c032072036100c00400003041c0410300c1c54001d050703298001c1540c0705100c50300040c482d02a03582e460561070168003082ca000001030100c00003032680002051010341c0c0030903030381c00c1030030300e202c601c240e00203160301c6108614000c80041c560b8401800040d000307c94100c0500c1d160400c0010707424058040b00034a9050110400c030254070004656008a110040100d4056118050b4031a8444580c21122248100c2020409014001c2070240c00e490195440b48149001e90004030151050801004560038080150b040410700c5176201e190049160050001c1d10110320000403042d44064400446041d400039519403107000007090621004e00395000c0000b030052004440044000d404209569503c8503400202002662211051000d034082c10400c8403c0040c90303280300406681c02107201c13801c0e0000000c100c4001d4801c43c12500035005148160391010f8000482d4011400108580c11035101d4860600302c0c0d0700002141c803006000c800040e240d01c3c3c4065094 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 511251079 1250 511249829 511249841
    0x2418110105070f02090a0e0a110405060a06120c0e03060a0f0b030c06030411280801110c0307150b0411090f0a050a29070506040215030705181903080a03 67
    0xe050000801121000407280103503c0850740d0100c41c107910607078940c440c080c0030384460f410090782400703400c0d500010841400700941c2c2e0407005541c00c0025580310418814101c5441c00340c9404107200c2c00d0407100c40300454000c1c0400c002c41c0d00e04005142c5485010900d0814103490b8440302c80e440b4035250807a440c0c6072040d141d12040c00c800500a6902410125010b440043d2000d40159107414820348142c41d0031490001030b840800038160381d042604400c4011b00702c03602544c1d103130754200b05002280502003400c3d22030310318060000d507141148542e0340716083c80580b681459507503103560105956a07242d21408180e21700c0745c88115522041001000264240507460500c26000040b040c00f013929603041410941c0d0094a2052806640300c006690444000c81005060071001640310f0400c8000301d1101c0c0a94401c0d0f5098400341310140000c00a03010444940c00015014446e000408c500c54800c503603104406005103181070f4150121070f00f211550f8109807001000012603a400d80e0f8944614 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 511252329 1250 511251079 511251113
    0x15080c1002061b090f210c0102070b0d0b01110f0a060f1109060a0201060f0b07060c08041e1113021b010e1c180f061103040e042418 58
    0x160005240c40c0b0f10705078a0701e141d081d00c803140b21004111102251100802003904440092080c8050032000001b1003c003805800396031014001c0d418000310650002034180b0a4607210f0000074280a54004050b0041c40803c141504205902c0f2036810103203403e000c00c0040c02607580203400b0340c8409040c0b410558000b0402c0380301052800c1c4400d02c02e4a020350568400c1c6034115405941ca41d901c150481c050301241e00140c41d2801c41d40d50028614030620000c00040c0e104030303010301103021140400e0314000740c2110081c080103001644544040345a8802c840170324030502d080c002c02209400032402c081580462042107035030010b9580c190702c07212024404c0c051082c2009000304c03540c0c0100103896900e13a45071203001020404400b03e03103a00070744882a485034a01d02010079541d80d40d08446240100b84a80c0000c60b04841e1b08401c00d0a01108503025940e1024507075542e600c0355030b01d544000c4c407030b64001c00c40303042201440c140080c0c190054505450b1030414041100c0d01504000000120100350 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 511253579 1250 511252329 511252333
    0xb0f1207110708150c03040c150f030b06280207120b0106020f12040306150b1306090609030f020f030102070b011d010909050613050106051201090c050907080a090615080c1002 77
    0x7042c020381d03041e034400344c2e48100c03c0780c0030302e1b16500d132490700047d20402e542001c0150b10154081e480d0b415440305d4000da241005640a206907403030842404000d00c00c1141110041e2030006c003a04021500100900070840a4030440302015034490b107160408403031100c201d640d19540300040003003e03410052081401c00c0d1502a000d04d25004481c00064850f42c072000b00255103c3c1b40040300c00100041c0e0000030b22003102c10341d5480203080000c4491070443d001c2c1c80040380e0b9069001c1203d512515912050b690b210f801820502016000c1008590340b04002c00d9040d0340800c40c3c000041c100d0207106000300001a0140007407500f10301c00100c0030005030003010300701e440d00500350003141c40081d003284c10604c1307991824094004c3e402d100b40503101a80050740c0103100c1507011541a2015480580e0f1940030721b0200004680740c10401100301002c2d01c039140014030000103d02c0c1120b060f409204800d21032100021100310715411800f4407100d55018100315005200041400e04000f1140c0340100d181d480 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 511254829 1250 511253579 511253593
    0x80d031a090f04030c05010b06030a050f180307031b08040b0406020c010e060403110f1906140c150c0c01090f05010e01050106140f1c0204150203030601090b0f1207110708 75
    0x12102c0c02d142c0004002904010320708518505100e02948160082213029058598a28025614201800003990006005c040c5040003490048003000348580350140c0001951a01e10540c800329150040e01e084085440d10490250780014010030003400100000e01d0243e4860785084c030043d091849114469060180e0a46540300c1c655801c002c0300e05496000c42401c81312000030700858251080d500c0610f0b007010083c801802d846603815000d0044a04565a03aa14401c20041107011070150317051010003039203d0b15503c848007203180c052540c00016103805906100e48942c0310ba0039207174402c009883c4908403408080a100081c020190a914841d0090201c0d51500d4001000e011120040000643c8041802490812500101c455100751b11109601c10b1405078001c50007035000d4400c456075408448180c0c0d880500100c2a41d101d110305854555500740f81402c1516507034841481001380a00800070b429580e1502102d803401000c040e5503124000036841200c0c5c2c03a003120b5810005503540549 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 511256079 1250 511254829 511254841
    0x50a06050319020f1210051f0602030705121e070803040308070507050a02100314160e0a0b120c0d0e210403111009030f0b04020907080705090f0307080d031a09 70
    0x91001c1c4c0c1d281500d244501085c1d1120f4203003800111210307135110508103802d0124144401210300b0340300c2c50345125150860340d5600140d03940d10070b480b002803040d040031030101121041100076200301e0345404a503840d0b2002e41c401f0314200e9400383d20110791400004c4103100501d0b90001344c1c503038031080908003140b410b403650302d0300c0ea51005124402031103811005080390b0064400c0d04526440c100e83c0000c1030301070421131080701d9104a0700411a00084000b40c0403116458050454021505000b460f24505042c21840154680c2d0090101d00e500c07404000f4844555054803c0c543e2817000c6001070000e14003038844000d40b90f2a000c8080b00300f9a8140401d00218824160052120100311480360840115070360a0b00c069015500150604040d0b046010500490b9031050307102c6c074800c84040c500c0344d87e0440261251102602d04d80d000034814089061641000c401000a251006003211981a500c420709841e01031414200000241c5984403008541d001c0c0e0310b2000250801c4909103401c0c9012 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 511257329 1250 511256079 511256089
    0x20706081501020a15020906070503040302120c0603011401052701030606031a0f130e0f24190f0c0e0f030109030f050d0905120a0e150d020d020904050a0605031902 72
    0xc65001c0d0100c210400c0540e03185a05c3c0d4111502204040d100b1600d13202c1c6401c1031600ea42092209a005614600444200200c04103400c103031010010810760950742449000e03004a107403035900c00e0502c0b00400ca403214a50a5039001e0044071240060780c01003810803000101900c0550f441176041c9414102000c844010b20110164581d50654114100140d52000a022407103000ca50010711841c182640704000341c04190340e510130940008984000c2c25549038407550850b03e80d0005014001c0e00d01049022104040b4003a00d01454000032440030645001c1204603004880080b0108c1c0900d480314a0f2401c040f0250781001e601203000b08040398440e20007401040400e62014204840081c81c101c803822030798002514190040111440000c000101030111350151000d0300205403d0f0380420341514000c4803c4040e1b04a420035079042524107034554001c0e40240a90104c81070b000c0c001700c200d5448520546225260761000403452600d803105041c2088840f00c1c9001d948485054801c0c05038170b031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 511258579 1250 511257329 511257343
    0xd080714120a05090a1802040303180b04090e011d01060609050604080c010c02060412051506040b03100f091a0612030a0f0509060d0212060f03071d07140a02070608150102 75
    0x1441c100f0b96581d80f0180001040700c0d5440d040f00314403449104000311070f050a80e0240055034400e031154080301d1040064181415800e101d51b60b85824100010301c2020b059400180120f00640004910302c10601604903140310b01e42c0102c40142e40d01c0000700102079000003002d000b014280d40303407868181800c0d0107548848070303001d1013810705c8443d0401c8802c544802007102c0050060000413803540015241054803815603c002114522101b0b0204615151034415400c118200800408403440d05030b403820080d0200744040c114817550b40181c1c0c001305400904d44600100272000b541805d1510004003c8102c070f00c000103842d07540c0180450000389402100040c50401c1500703020391130308a40c4000071014481c003400321074441d00100b078056040085000c424040c210895203100580005014550f0312001c40c419406c600d00045602003090383e001c0c0c42c0c941c024003d86040d000000310a000301d00c0ba60700c030000e0b460040e070007044101b1069500c08080c070341091404040c10415041000000c0d62168 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 511259829 1250 511258579 511258597
    0xf021c05040b070e01081f05030304031a06042310080313091506170405100606031a04020c070b0913060b2706270901060f1202070b040b0c04050d08071412 68
    0x1604428041fa02004103140c801088000d040729651916440e000150b1014080400242d940c1100070900b81c0c80c10303000d010003006030341c1e506290013105040e03120004003024041042d940001e84002c18102024001000322004d003001c8001460f1800e503004003219502a22030758502081030082c4503040d032050000c03230150442c0d103544485840b01e0400c9800c0641c0400c42c0011186041d400044054054000c640000d030b0100c041850640302c5018082607100701061880683c010171402e108000c0703040007421803078a003e80002d80f41440310300a64201c4201d82c10015110102150070003446000015086201c1c0c80c41d00c7c1c40c940b51182c5c202184140c011100542085041c010002c0801141585607620312200148043c10035607590b1000f6240540e03001c9020009050a0106109414103000311003400d54001c218411507900c50311204030892000d05000401c8504010009030395a55902c0f194656000b925400d54441503403401024010303100c40121941e4102124828491004105982181e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 511261079 1250 511259829 511259851
    0x5030d050a211a0102150c041a210f090d120f0e01020c070e09010c0e010c1b1502010c030519020a02030c0d080f150d0201050306180a060e0903040305100f021c05040b070e0108 77
    0x414201c0f20127815009000080168400032291074500418150407180903158044108030f0988400410b15140c0c0b80c480d02d4240800c0d880800400000c12662007645043d540c0c83d800182080e2501200d400d9a000e0310301c14040381d0050000b4070042c1c04900e10f160300003040743d00821842001e0708010300300c0d980101c0b003907051011546d51072082c0590500c80e03943e40f45807883e20120240e01e840540421f0307058451000010b44c6030201c5000c501d0f00a102e082d01480207500100318078605e0140c100e0183d4407480404d42180018070100412020410140ca0352424030f490b1500d032450303d0072045040c0c41006042d600410080000c8103440c0d1609213010003015020710f0050b50b01da070740c0004919034595841e034040d24a00190100000070b40c860388054140d03213180d55001110f40744ca1001d0342c0e03640210f0101030440d030000b025131400c1d01c0003540500b401c3c000b00c1001500300032082403083c07003120151a8a112154540040001b041610500d5507400140b40c20114030664414000030009180200000402 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 511262329 1250 511261079 511261109
    0xb010203041d060a0509042409030903020d020103090804080703110603040206120c09060a02030d0b040e2e09030507171c090807020319030905030d050a211a0102150c04 74
    0x2501c410b0341384005880d000c0c05091080c2840c0c941155074030700303046043d00d00c400d1604501c1c1c0c424400c0d00590354a1a05650348040c4d56045030201303c0158042c04041341816074428425002800d844040c0000300700391170103040c160b45541081c07040b0000003960b031031003110b003081008016980d4800307a982d5510110801151540c0d941c802c1c6219215210340da0354000000304105101a900000800034511008820300154000380c1c2031000f0b03656400c140c0e6410390884401516030918800003030506d8200103c21005110791046041c0403a0040c000503800110000340c0c01050048003080341d5414039400c4005442d003e0581c0803248002d092150f071500c0b0175104d208403414007511000f5583d91540007403d480300c40d00f140f21000307900b11008500f00c003c17034a03d000011303061030081a030390000d08268645034904010301c601100e450080e00404000d031800c074040304442c18a80d2240310700d01210f4404a0320f80c94a0300b00064039140403800018070113240c02c410412031384048400c0c0e40c11141140409165 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 511263579 1250 511262329 511262341
    0x10602120f0d060806131b030503070201052d0702090709080303070c020a15051b0a1a060d0b160e03240402180c19050702030d0f05041a0903010b010203041d 69
    0x83c00381540507451034880c40040c0034682160a41400034184034010016140c0d031503480940302c030041c0c1d100251017904280001005540508020a0158080e00381280300a0642c2413104044841c84070344c0003c910301181c144118140b000b41560481d0f02403c1001d8018076190000d56688801460030041090080d40c01003151a00b8070184042d0466010500b28034042040042c460b41142064094800d114591035030380190201e44884400d03044080f01900700c05a1403501d440700000340c100703038210000881d04000708812400490160b0fa0b0341c40349145c04040f840b40102443c19220b240c1d4401e4004840c0d203040e501001030440c10300c0d080356800458503503460002410340d1078541da0681c2e00b450040100103800c4031b40c0c0028020580c40b080490030308000b0701c41c1102d00d401482c00080d0560301c440846884103002e5400180c503070300d503440c11529013904c0d500070040b1900b08000075004404049040c2200703150a0040e07860082c0d0a2000b5403c01c2c0c540551316441c030b82c01e00c13261070302c0310310440110359 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 511264829 1250 511263579 511263581
    0xf0d0e010203130909051c0f0c02060408010f3303020d0303020c03030a020403021e0f0d0804090f1407140304030305131a24030703031d0910030506010602120f0d 71
    0x26400d40f04100ca60500c96550030244c0181c0368883d0700326110700840410524200070803220b040c141e907455860215064105030261480101c0d10010f03030f4480700c01d010000343c505003402540b180030a4498003040300145440090207400a5810041907080b000a44460030141d2805c90011240c04031442c50b9801f00d1820260300a1040c07007080b540c00d000020030070240b030003a5001402128030a80c0c14040011203401d075015013076401d446280c0d201c00015840c0b6214a4a01088a020782c0181040b0b45003a0340c924400003115607604542e01265200e2599540e9025044203059100485003000d00b020281c0c801004c80c1840014001001e2607aa00b01242c42c07044804c42d002291a0f2209140e007810400800900303c1c0c180440d50b0701c1070505442c50700000700c50b0036801c0b200780c104040e0040150500b103607020703540d002c0304c2503040140403d003031014215590307034081080c02290f01c1c05c0e100c1031942c1181403150500d80140c10640c1594040800801e921228030129401c4003400301c000c5031280005402c140c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 511266079 1250 511264829 511264837
    0x30d080c04031a01060207061b0609030306080106091d0102030103030f0f030b0a060c060b0a05010525060f090317060607170928060e090703050c0c0f070608090f0d0e010203 76
    0x3800d2644903c09040b04a00c4a403011810380f1030903000c54041070344d914422a8000b40b0280b11300c0244903805804400034855810103500c01d4428100814685d0722503401508586050380314119641e01c42e818108200000c50544010b003041c1c00007036165605540b030240040244034080c0d42003007441341c040780c0420703c0795002c0722140354010049000c035a5a410000c041501a8a0551f1400e2034a9142d40451401c04141400c880042e11014108100c1800c041d07008800c89005615940c1c2d007640c01d0700054014402d200c04141c80d0440054803040504005088107c400740c403040c155080c80512105a49650942c2c0d00603074000424000c2d480280e410050318010351001c50781020303a040c4d80640c4107600c1c5891129100c01070b0000340c44c907030b643c0c2d10840d400600e83c0c135925008018071001c108503d00c070760008c0303034041d1191503001e182008030300303045107002c1c0c0d00b00030302149402840b41484180d5100000c0b0750015104001030860510841034181c44d002d60083c02002e00102402c8000143d001344155 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 511267329 1250 511266079 511266083
    0x30b0c131211010e01030c20120705151f03080f04030516050907051608090103110d020c0613050d1d0604120c0b04080709050604060b030403021006050a05030d080c0403 74
    0xc08000101c61400c2c40c618501d0000c0b00b07011424420041104d075221344130b50941c4030810703612030080c13910340b2a402c0004040e0ba080c090b1280164070300ca210089040c001800361074883c0c2d0040084890800e103164000b000a0145220300441040f500054140814508242ca8000c14500c4c0d81d4820440c40d494244130b90340c002800c90107011000d00b4504d513070b075000e2021180281c4050b402560f0b440c20480b040d101e14000031140e8200c01240c1d0b40802d07103180151958203418100016100c0d0382a140c100c05d9002440c1d0745402035000501c0c1760001e00c0600a090700161091041d1401c3d9200e541c1d52034a6010021402c0100110041c5000c6c0c94002101d101c10004005824140c1c0e07076440792800341246030044030a0360301c00b80e400b400003101104101220200d4600c500688122800c280840b40a4440580216405510f83e0b501086021a5034010341c06548250001c2186206103401c1c6800c4d9400e503402944038800024040080c1e840101e40407032012402d1402502e16607403501c5d080007a004517080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 511268579 1250 511267329 511267349
    0x50a020c07300f02040b01050a050a05070f33020702331801140304020307050907050712030c1e0906230a08041b030f0206090102031c0b040b030106030b0c13 69
    0x24107018881640843d81200740203131030900020384200015500c030301c500f085075000036000f0040e80c0c8000e0b105d84090f010707161182810000490f400d8861080c40006801d004e4519141d81c0e482c1680035600881825460320098400e5040103003030740003e00020000c43e13030070015084103014036a0700e4128906a0403100c141d084401d4641710000500b0010165982f0b50303902103002d0641100900b00d050703040c0e034415a4002c1c01801c55900701018003601c1000903082200740034051008800080c84000400791428080d64009445409088028400e03c1c6c0071251251482080b8640c0399503560150365a015603056080807003e50041890542071141b902d035201c03140e41d501003201000030b603100034a14000e5010700711020b0700d420f14110312865000307544001081200b080e00340d200142840c0003e8800d4020500540f810200c484070b41c00300c00c0207100e883c4603209a99030102ea59a103850f200d042c18004c401e5000708180c604540d03545105060213840f0b1040080040b072050400e140d407103200e4001d000d04200f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 511269829 1250 511268579 511268669
    0x8071e08090a050103021201120507031205030703050c09030a11190f05040605150301120201030b0907020109030f1d0d0f050a030e04180807120306050a18050a020c07 73
    0x42400540c0c10500c01e9901c2a00b41c004000340540c800d0003074511b07158000030724440b0741e4130302884041202740c103e02c2220344d4012410000007041a901089114a442d916825640c0c9041d5400074216100200580d001c408148221419a04c000560520f115403002c2c0119a59008000003405041c5d805503040c2e0351081c0f103401203041c0030b85c8060001216800e4400303200b010785400810811810709000701081c2c8009100400000030702404089025006040014070069141c01003041070700d0858403500540c0d11900d41e0000c05500c000360741c8a85030a40390808034074580e0000030301c800c803004440500c0742e0800c001d20814402c411044010300d582c01000c403918505589805405420855651885185003103200e04190440d03451910b0403681c1700314164940010303942c61003014114002c40004050ba0303400e0101c2e80d62110512100603041c0a83d034080100516070801050340d1000304401030440c01417103070f000d00070300015901094900d1071012100030741403010305410412152010115000c8018 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 511271079 1250 511269829 511269833
    0x203160309180e0f01020c0a2901090b03061b090f1c050609190b0403050a1206060207030203240105060a0c050d030501091508060c1308060114090106020d0c08071e 72
    0x40e005001c000d071100c00355615450400f036107600302c3c0100009566180c100030408c00000d484d0080c650f4008482900149407040341502e421440b01d02600610031640d034070207405295103404c111941c1d1208880180f406d060307007500c250682c3e600410340d6450250f100324242500e956141400c031100c82c004120107010010081c1017050b07130741d1401e80d107008450058400d914514015042aa852a80c10242c41320b05511141d604560541c04010380c2c0c01003240c0c074002c503000320342070b4043c20001b804140c1c010010213085004050804460170050b0f90945040303440e01d1900c4405498a0b411034608890054031091500820768021240c60301c0181503010344411103003070b10740680c89181601c0003840100041c0440e003c4040c44d01c1e006018a41aa40c486800070722480c0302d01000f041c1c44e241c07d15200444270fa541c0d0401c1c0c1381034030a030030070f048012000740e50380550b080c0000850300416040c4001c04021007000c0014013100d840081c05022100002600000d21050324000c1040c44915590000b00080034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 511272329 1250 511271079 511271081
    0x3151a071112010b0109060503010e2e031b060c0f0212100f0507090803070302071a090a0305060f060910150c1a0f0109112212080325020316030918 65
    0x1040c04e10340030401c00071010401500c904280c906031540242144550b0f21020159100b581059002040950360b82d1a60015842000f0124000f940720344601074a550340c410090503c082c007500980c00b04140340741c001c0041036060310740302259078060303a00e1030058a002c0d28560404030401d424034012400e0000000d154102903005a01c40c4440b90740e50b10030107403200f00054a03886800340250040e4001c0605215001c0d0108070741c131844024032595840d0a0040011803e403801c154001e07200368000c00208403d007403040c2d050035400b1404036206082c03481c000000c4190203034207014000c3d14180f2208504100750103051090396198000d03614511001c0c1142400c2c0307400c07c0841d2402000400c5600004800c400b078004c00b4407580760307070301c40a060214642544041d01c09484007100ba0360288200069100f0b9100d002c015414000c4104965929080104103111591480045a840c440c1000145050341c0401074520302c5201095481200d03419040c100c8000b61590881c0880c84203149401c0c03000102 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 511273579 1250 511272329 511272341
    0xa170306010306050612040b0c0c1519020913020a051312120203090d080904091e201c050c0301020d09140a020306070f051204110103151a07111201 65
    0x340d0b01070240c5520b500034440280142442942c0d5810400301080018a144441503400700710219840c0c00c2101050019290207008030181e2820030541d81440035100b800506580030b0cc08080c01503151140e00b070042144818020245100c465020030084100c0e44034004075980c420707a07440c0342c1aa258032079880100762083d402080312a40c49640700d1640c22800401034546500c0000c01c2480f09880f036440d0b00020f50311109415901603070305c5201c03a0000d0080b0300803e1030281c1c00080c1c800d9100040c90140d031000260018805485030721580c14103030b640c1e0603010003900d01c1441c00c0c0a400421528080d49029500d2030000c2e499400441d00e110089103a03480035121700d00403045102e202081034541a100c5000306000b80d095004900040c4c0b901d40034580381002c1d1103541ca401481c2507000c00c008604410142d40c2102e4018540c116000c0d80e6a050140c0d82c0f801111841c18041140f41c0f00c840c0180740000b00103c0c0e4628004902c600a101d008100121a004040c000e4100c06c9890002c5038000c0507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 511274829 1250 511273579 511273591
    0x402070c06030b04110306040b18040c1a04030c0909020303070b040b150a0b0901052a0705090133020a060204030b010914010e0c030a09240e010c140307020a1703 71
    0x80740c50f9074078203185002d010714059060328110961658981e1320a100c0940081041590000c5180c4108090660000c1015104601800c50260481d0401c1c10036040d02a404c0c3c0302005a044c180000c0c00414585d08840c004ca4400314000549a030304d92012a0a5015584020384649010010407081c010f00b206903510902c40000e030390120300f14407410003401c0d010754025034181000900c50080c055025000038466145000c0d2040d0307110074552860703040f000c00b42e242552070b504520383c104040e042c60300500c1c3c050291841c40000c141c2c550495030071000e022401c801d01c501c025030b1800300b00303d009120580d1120340003d010340d6199260308168000040071f00c240c0742171a2030907440d170303509501004000b8141c850030b4415903c240c03034800c0500e050360009014881996547d44507200040d00d0108028192004c0d40706089800711207401c2c000c2102c400080302005a418804034207403540d40070b0f5a401c1407044129010341c036900c030403000728070340300c44404002d21403100004450580c0030312001540c411a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 511276079 1250 511274829 511274831
    0x9091202190507050f15040b0d0c2a0606080d03050105030c0103020309071811030a1506030e0c19121a0601020706080f04170f0d0b0306060a06050a030b0402070c0603 73
    0x1085100c1c0300c52800310803406006030300407482c240310914007504c420310600802052481d000344c8954509070309a00691016180b07400000d20703039480036107030b0103003503030300036a03818010802400e03c604203054005411003c2512003c141c0701d541004400d9214601070030705c078002c49a40c901c507444040c004100078050f1340c1c828030410125010b2076210b802102e129403600c00142481e18034065142985c030000700c402c1300d60a80c803801c0751080030b03103180007551003121420004103202d09101c2c02c0c1c41701c507032640e0000390070141008800780203240001040e2008032020340d03100f000362404808445104c81c840d003003c1c40300e0341c41d0b441c0041400640c0c550030083d4007118854144540b500c40041e640d43d8858481c81d804240010300049041e03100301851903026004941061401d000c5030b1800006600100320718001110108005070004124800e030900d4903015002440b490800c000081c0d09807500f07110381e03004c201c2d001400d00440c0e44030f0340040012803c090f00a6440b41400d00d0600201145c5010350340c006 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 511277329 1250 511276079 511276093
    0x30309011d030c1911060706050403080f090304051c02030118120f1b0501140c0c24060d0302070f030501142a090406050a0909030e090915040c09091202 67
    0x1141011080318007492010300103101304c03810b00705030f14004540e940e0300780c40c02d6104030312854084d11030400504049200303640000b0249090b01d0041e1200c2c002074584015019064100314039060300008131801d440084a01650805800849600412861900035019402c212099400350140811110184d200b60740f80c00e041c0a652a00f150701d640310012050003d5040c2e018000c0003c00001c40b021828010310010404c0d9007100d4200c005500c054881034095100025031240c40d210500c44004d0800c2c030700760000740707480542d03085280c2c0c800050000303440b40d41e810f0100410103000300030749070090864100305a0f0b031507540d00f045030081070070389080c6030107545120000c4c22465103c90401325030a18003a07201d07040007400321895041c1d084100101e82090307a55101041698039070b2410340c020b03c402d050208240046203401001c902c2c101d0f44031307030054007440280007010202051074404a9481501c140e04d69a6504140d409540c00342d20811400b407078020a001841585584440005444c3e002c032420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 511278579 1250 511277329 511277381
    0xf0303070f17070f020108060a03080a0905040b1504091a1203090f040504032316080415090522060b070b090d08062b061805120906030c160503030901 66
    0x100703124214000b000c50301c131036500c480190b0042249503081071002d8912a01e00f922039948075102d074024811070000c212070800400c13581c9000e015a840245042c0d400c0200d0524040c0308081a0103a40955500035071551004091003600c40c0901807181c3d0010300794030002805007142501c0303512140e40c55000b044814603104050601d80540d9002c0d541c181e4540ca0a160104c06c441c615000d03501caa03240c031050401000d609400d00002c290310480c0103d015940e0340e45400d0326204910300e5540c803003060090300270003005556568880e4a1042e0a01c1e444912110200110000200030b6a00031403205400403400b10113100a40c0101c920403d20b25040f16503609101c0c0b01621081000c0303400f594401060141c64200360094000e1441d0380d03074038907404d041d600b91950b501400d4825040c8000c2001261034509800d1100c10000c5d900700204000d001403600003a10007091f2180b000421140030000005001c0300d00326a44d0396003c031101d400c00d09494890520404c4107002e099414a031000f40c10b045d00f80000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 511279829 1250 511278579 511278623
    0x1050409020d021e032508120a1b020301051003060b0a0e0a15030803013f030c03050d050f0a1409030a0f110607020114151e0f0303070f 60
    0x1011940041c00380d0000145039003000b100844c2005156031070811101040400e0300c08102242818219969401904110005004045d2101c6c0c1c400100396103c424401d54528884084503800040c82c64a084501c4280c1c503098640c80c8003441c001c1d0550b01c0c0070304205024410301c1c110030035a0f1140c02c09000b8141400304101d0216664040c1850003420070f8007090464000741d101980f144040c02e40c0c0f03005940c1c1ca40b620b580030340099102040090727200080c00a84c06410300c043e01c208100d021040840c6000762130081c0d01d4805840024244615103024101f0305020b0429160503903800c005c00c0c01a1b1500c000c0e2540948400c1d80c00e4030140e410008000e190303c42d0360700481d01c116a10b600540c18104104401c440e548190004442030140c80303940700410b00c2d8184840c40c401c248076000811154030400322140b94040013421803a41c440d00780c0b81c8109650342c00f0a8101d100d91408194406c02c0c0f00a030001e0700804450034020340c5407200140040810820a00031840c07075004890303079107144d00e007580c8840c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 511281079 1250 511279829 511279841
    0x110619080103230628090b180a0b0609100506070f0c0906032d14010b010e0109061e0302040f0303020610061416080f041410030614010c0f081c05010504 67
    0x649400c001c0006960041407a5100400705c03003201c04003240528040024116580c15005030b40c070390b0044080182400340702c07c00c0c070f504145100052103a40200d4039803500d04000075140350b01c9161a40d000c5541040341c5511240500030060516560f01e2491500000c0302140c0c100c00c843c0300c403021200003224180c0b88507040483e60402d28400e88905180d01c0c4424204161410002503d01ca440c1417000c2031402c10100b100c2d80c150000011051a40c100142c0b1084c0b0034008541000701460342888125400980d01801030380d2500380901c41c15032901c0682c003030300036500a240f03140e00900c0d00105150740010450b00840300200107415840c2c4480c0300b12503070f0325080300484401c102000f0507450140c2030074030080b54501a0300d0450408548c20308861456016a02020450f03004c09610461450300740c1e1041c0e51200c3d5030034204507552411100c4282ea50400103624103002d2480c0c41402072024040c82030b03801c2c0e58858a801c0c3c2c0c2d041d1801280744500384c04401c80251502d80000418607040501c964 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 511282329 1250 511281079 511281143
    0x40609060b0c15091b040912050706150315020901110d090906080714060a0c06140f150306060111120a03060f080c010c0602031305010c03020301052704110619080103 73
    0x580001c0300c0c02d082c0b2400c45c1c03100300300c803170b400c10368840c0f400c40030409104100c41c61814503680c03255030780581d0a010b001e55003440c114034500c0c1000b800400005483c034804841401c42d0010151711b4007414001a9060a0603070f00300c644034003450420b4043e090f8000c1054007a9015917204100094503850b5144e50f07040c460181e0300030807003086031b0002145440000b50038207000ca8075000c640c108082d07440f801912131507151105082d080b01c0910440c00d030262036465102c42c58a915282c40391005001980d5034001401150500a0740400f0403001c0c003051007081701c540b194203166a40c0741c0c08080020028103c074070811540d14451000440c24800204081140000503036030380c41c003600a5120f2100a5202602d007201095a9960401c0040c03c03c0c05802200a91518010303121740c980800e00208412491920405443c2940f8140d0740c6542c22040c51341268202204c8484174074000d0100311144100f01caa140704d188203c2d150f54480c0c0c0d01440703e5040c3c0c1d110794281c078040c5c0c40544000d41010320040382 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 511283579 1250 511282329 511282333
    0x616020105040206031807081c08010503060403200c1809060c1315110109061e02040b1e070c03050105190c0816021609050a0b0604030302070306020306040609060b0c1509 75
    0x104030146c2100300c1610f0540d41c20000da43c0b465559291891801d5500035031400e480e0109000d188900390400b44041c01400d094016000510300340d81c0003048000301c21284c50341000c0c40c0c080b280702c2e903000b004100401000908820102c68041080b070600b07034012a0807440310722410f80025409100801134650701c00e0717010b581c0e010103414694401d580003a84000b00d0100040340c411f044980c0c0c003d0144411a6010b1a00090b94003210000103c11030a82d00d012030703aa0f0b0040000b040340f2140b29080340c1541d04074032940c4210b113003e8242c0804074403800101802c1c190f54402c010003400b0065020b0760160503c40d183c0c0007429162114802039908140010000c51490710010741c0140b03003401d9071040025240f05035045540c211481042d2500e468110041d42d554800810100043c20f104d220307000c1c8001c440c00e608243c40e55034020750728505030200918180e0088040740d0346456a0300040d001e0014111300340101034551b44d6a000c0c3e41c11070850031f20244034684040c030307480c0c0748a1000d074010710360000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 511284829 1250 511283579 511283581
    0xc180f03050d03020c01112107030b01090b0c0a0606030b100603050f15120706020c0f03011103130f0213020901020114090705010c0311070b040303090f0501080612011d061602010504020603 83
    0x2c01940207400c40310040c0708654880d01e4800d0b100001d03900900000d828118481841002240c06100d404801010700c011b05190481c4054235030b80045414044804c6200001da40d5002d800020f81000d8542000810141c10044044104909401c2030b9108030b800b0b0104091950340d4281c102c00360781d42503e02c20340702c5070200c0108955000d0014450030b0403101900c07411003182c00e691000c3c6800c06550018005811000d4001194902402c09925074141213000380311440141c00c0f1a0b40c0307840050600300c0100c20303170090102009411070782e0030318032500100000001b026203408040a175000c20b2000c1d0044d481c068008103440c51800e0a940a0844d645c01800081e0a110055400c901c2c00713942641030009141d51882c8204041121101421140b080542c82d03514615001c0d1105038030781c0009000c3e40c03007440248038603644002480c4c1c1c003c0c81100c403a141000c1e0000c0c02030041a10346603403411200d511004a6919000088807805030146000d80c0d8986240003504908880742a1402948040200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 511286079 1250 511284829 511284853
    0xb060403150e06040302280b0117100905060f0f150103020a0507060609060503070602060f0a0203060a0e1e09030f03010308090a0509040b04030f05161704090c180f0305 74
    0x5903150080740000d5000141242600d08081c507128088508600503404480f89240c0c1c3c5000034825007103013212510030700d104980d9070740d940c1d00781505024501d4080004140320840c45405c015410715251600000c10949420f404c0c01c0d03445460071500300b08000450000308807880828010f09115560108442d48041c4001d80110f01070340c0040c0d826020420248025401304e00f0034802d250003441500c8002450703500e44410f0504005d1294410000d41d04800c08004080503000d40203540030440c0c2c0001a43c80c5d65200c0028401d12003030304030500e0051010704200d440807080c81d0417000300701e28220b0098030b41d0343d02e04002e03a01d02c148059112911000d000400001700c918006d40a15807000700714400b1103880c0d001040d082c0c1c20480b415036401a0b8081480180340c4c0001c9604111016032900c54644522150440700720b1501e00e00c0203225001d81400b084004088000350390140007400e40c144907805a1500003882a044010102c00400c0540c6001a80c0074844c5408004c6a038004090300340d4480c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 511287329 1250 511286079 511286093
    0x10c0f0206131d01050907020a0f030903080417061005010e04050a06030203030a120b0109031101080a0608010608010c03271b0b07060f24090905120a11060a0b060403 73
    0x110040340c01c2101030100b4860032407110142409071400081d000c2c80900c1c0904540c000c86010780c0540e00400b80c180030b00c4042035003c2011441c00d6040450071140c90840e24045414544513880500401f0002c50045010103154010388440020b0304201c17592174882481d00d482c0c061881c071a05001c10440003444c0d1086c1420f40025501007040d9000281655807500440e0942d40302e40111000160701c0070000141403858491619044420b2070079031090340c21581d80303080b07100741180d00b54103010f03202c00040e4103501c0341c2c0c100c0c20141803080000d12005594104503406005810f212201090900c52a85000b8005101800925400311071401c00074500341c40300402c5499100b8003a0a6111120010841408010041560a200c0c01d40040d138036080f0f000204c01c0b51046400d284100c009081075109803e80d800d1010b00340ca03220b92001030b003000c042c45e00c40d142800c10300110020140210780700800541101000070b108980c8000d8030300950700e0100220807a6000800303c3d500a000b4442800400c0ea0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 511288579 1250 511287329 511287353
    0x408180f1e01030608010c05070506010e04080909040f060c0806031e030409110403050102040602340e07020c0301050c030601140406140f0f1b0d0302070812070207030b0c0a0f0c02010c 81
    0xc10f0600046030b54503460420700b03503100d891240001c20000102201005000c001c44d90040c86007030201086410f20340d031440c5045c403031350350098820110003003c2420300500d48440d5401d55440344040002c2400c420f0301030b026082c02c981051080c0140d42c40000c000c8003a101501d14020039201542c0790030706105031600280002d25070889801018003002c0009502440200082c04c0700d41c008042d00f00d1420052032800808103140001c0c1c2c0900914182c10700d40b91411101a40c4c40c0702e0108001c1c0d13503500d000f01e00e04a002c0203070079810340c00c040a00414501e400700841c000c02e4280d850410301440010b034450b1900ca80c1c425540003402d056503c00f00c240d0260090311513804d03000c140c1c601e00120f050300710000d500258000c840381d1410b81c2c050703a00050200001802022203007800e50510303140d5110b4110314020000c003a240411f011000400440c03090042601071039001c400100a42000503182c800c40d0481581e050111300d02c01450040b150255200c0c0d8500d42c1c1c165100214480d05550b05250103003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 511289829 1250 511288579 511288639
    0x1109030601030f21030609050105060405010f1d06160203060f0103170f131e0e0c090f06041706041e0f0f03090911250b040b0408040506030408180f 65
    0x60f000e040281a103c140b540d44d0501005a5008190103091038114030440b50107901052007118100020441d07070f6002004824880384078242079581090401c2c03001d01c40c1d1882074101d0791022001440038034010440780f0722a1400e00a0741110303c3c6a03106421802072650a000280007821078081070000390100400902d004224414020308210b92481454000d01c0c1d15040b40f034688501c4403c640d0071040d081204001030409440040644c181020520380c40c1c41074030075a034090449030350740c0c0b415500d807202194020540503000340c0c0b513014081ca0503620794001740c1c0c0446191454001039400400202051103c10343c0180b10300c50a1000e0360303101411180052011018402c0c8050005591a040d104501502c400b040c080e0340e81d20301012008094405000c1c0b403242000030015080c0201e000c000a0640c030036803103201c082054440d414001c0380c5010310380c095a803007940001040b08004400d4041c00d940056440244560f950301801c0140103411029810740041c022143c80c1c0c4940039114414403c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 511291079 1250 511289829 511289843
    0x11041d1503010207031d030105150103020c010209120604020111030a121802040507091a1305010e130c05130803030f04060c09120503130b0310122909011109030601030f 74
    0x3100c00e101190998000c01c50640210b080840d503209002280c0b038507886c0e940c0c0c08030020002da180900c10041240e2114032400c3c10580d0205108000761401d5048550f20040141141490203141d95102c0c0d69860441d0124000b640300d55612042c800e00005503840e141d100e803152003003406405c401400070701c040f00350100845103603005040541c8a40c400d0500854141e03485d00c01250510041841544200001310403c190410001c02c07040080c40c22401920000d1800c2c807410041c00001404007242c01a00c0d00d41e16291030f54001c14150481d004102901c00140011011692007440c5904e82c00112129036030b80d91210000b50000c0c1322580440350245072410401e000d5525008416007540e4410801c50302980f0004614081c4445070170040700402e00100704500d14600b0307810660b10b480c400e22030b080700e13940d90344040002c001340040d4030880100c10000a0040c10303612141203042e80e0054030340c8042540303072003108802d94a640c001c0f1903240101500902090b441c44d5615101020500c0c1c05a5034a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 511292329 1250 511291079 511291111
    0x150209040b0307140d0606031a01261203060604030b1320060306040b04181b0f06020a0305030430090902250c0905090a0b0603070501082212020307030311041d 70
    0x981504441d00142e4120255619943c182a02c08890bc55045012040f5100d503c0246990300030019155900c004030700c00040d00c1e5101d0b071011a800e801140c03c01081103d0440c10031443d10368046d501d4807014041c17002c43c07500300c0740c910401301c3d84e0304540704264111101700300164136410a43c003c16098200980006454200c4000c602d00b9106000021146604c14002011100e1008005180585011000d004041e481c1c6500a56941100c500050078000044000340c2400754141d0300312045620030b42c482040030981060080c030f0407920344d4000c0110f604408c2c0800c800c8842d1003918620407203022044000c030300a8a41103880e4207441070844540950078004036002d0260b0241c2e9015404000003400a81358500d0305002e0b07040000e0009000394090007040141340c3e8031511280e041500814081c40c50000300000507600e5101000c060300a0780c07032100c07200865900100074981a07000e50b60030003003224004101d00c01442984601e00201840b8460000c402030342604003500401900418015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 511293579 1250 511292329 511292333
    0x90a180c080c0c07060f05040807030b090f06060102070611010b06220806090d030b040b03060412021002031302090c1b06060108060d0309060807020703150209040b0307140d060603 79
    0x115120024201191611540945069500401040d03003050500500505041104220303aa0300c413101e102c0c9904212442c07031003501d818010070072100074019034025140c030079880342803d0483d14030a0b00c1c1000d6922030140c54502d80784000c50309038001c0700140e01030459146040b004988400c100b82c403080007556034561400352a62410014100c034141914446000700144007078100c00882c5030b03c005559040385080084a00000c200b1010411880c100081d0080e158000f1600619038290b44d01c0d010b104a0b824002801103004e0802d50103225039003201c000041c0b11840400b80c1c0000d484041124000400c040018684140310039480403800903e10b0500e401c18940040424070000035040d182c0001060003901d5900c001100d912003c250745001c42d000441d5030081503d01a44100d4013003000380300111326000c0c400d008240c000e540202040d4100024150400000d6000f0800c5c140304030300c1c0c07100c0e81c0c2003070601188500464800d040501610420801404092420007004680c800d58503040840 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 511294829 1250 511293579 511293599
    0x150204080303130201020c1e010c15090b0a1a030a021003111909060503070c060e0f010c02071d010b070b09011b02060f060405060307050d11030a120807090608010605090a 75
    0x100c11041200d0ba80d44000f4180006800d040b03942030000c1c05030002c84c0084031481081008110900c80a01e400d03c2039039400d04111040c0180407202c008007604100d0003d0500407035808207801a41108400c00009a05000303001c4c4000240e407200d038160b007001402001502c0c010b82c5d40420b88079142404240d5132010b100240d040c0d88000e00c00e98452104544e1032844642c13000a210107072003a403d2061441c100300001074003920301e4400050503070740c0b44e052000c01c0c40f10034440000120544d500078403020341d548001948a42c5140210700621142c203190500402c58000001e040310b00c5425103600e450465140c0311440380d0020200d020b550f40b00c40100c0700c2410060a1383e00d8415080c0c0c045d214504000c64800d2000402a2405100d40c1c00e00092045c02e540108070017049410454400c2e200c074605240c500142030030800e020740c0c14003850760111b0500018aa03941038065880da1342e01074950304c50205484c01c103200d0181c000010b40e07200052040c24018002010400c4004008890040d55110211 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 511296079 1250 511294829 511294831
    0x810060c0308250c030201200714100203190b1507020105130b0d0501080c010305010b09010e040b04020d14070c15050c070f0c05010f0302040b070308071103070b0f0901020306010903150204080303 86
    0x400085803014200c0605134203114a081d041d821034880c1d2024289500010860b006456001d00804140305280c1850b02041042c83d003114071380bc6c429900c81c90400600c031b000c1900440c1c8149140d090420740846031034628140b110360100c0c0042d03030341044401d8004480c9a000046a4045c0030b501c004046401c55400740905140745c2242c10103c0c0c3c1d503050007265400d10803403000041c10b0501700b4005100d601d0110741501c0e4a1402841c0515103040e0180c002400341021210043d00310344000340b4014480c00d107030046040028507015080c1140c950010840c0c12001ca040d01903c0a506585111140030403a00015000701c2d69115050a1500700d4599002c2201c01070811200d0814a000c104155600300d40c0300c4050900600f4114102441c3c00240c98203841034083c001c0c2080780d8940007840c12800740101c0d0030404030401c00c5036103031049482c00112055003602c00c650780955210000da0410014022030344200410395034114540d1541d56041240702c0b0581030764120540034003010492a00800181d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 511297329 1250 511296079 511296151
    0x310020309010207140d270b0c0714090c030a020904020408061303030510030c0b2b0b0901050d110103090203010b03010f0b0f040527070302040905030a0810060c0308 73
    0x590350025403500000540840740b992a086d0024841d50034a00e820414040d000c81481081d00c2c81c490000d5032101c445c515507048030500d81d90100f102043d5500000d100b100365207000422044281102c1d041112141d0100c90400580030104001514800c00d40c0240006030300c00b40001d410b20fa2109800e03070074030340300715550300001a1480020080c180c4c0b5018039604101c80c00d100718007060840c0c07601e0301d6110460144281e2020001140101140d800340c001607035021881000d00013203003915560000e825030450403032184680200210340ca1074400c0c003416400d03a101d8044559228101c006601401c4842010b0740e041d565003c4e40800c0b92001c1c046c0d84280020948005a455180c50400003c4180342c161540624605010031200e07800151000301c10040751010f0303210359031180d105145004003c0e0002034016042800b41410007400001606807240c1035151016075039070b41582d20182072460700c2fa030340001d0103d541d02404280175040daa5089114030200f1038400c141690b015000802c1714100c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 511298579 1250 511297329 511297331
    0x90d0f020c13020d05010e0112080711150705070e01140111100e0c0306150102340e01170a020102060a0903050906190807020102070308060f031015060905090108030d0b031002030901 80
    0x104c450030041a00c0754030f02400b00300c00c0900c01e550400041d080c0c0542c10160042040800150080510600e0709440c002d0180040031404890024403a92589411206c000c840340d05c5000f0010492801c44201641600c050001c0381ea10b20030b0f8600116104d00c00d0011600d501c0c041c0e054944208180c0d0301404280520f00c00050410034251000d05281004c001d2520f10441582d00100d1600c1c0e038049184000f4100012204100800012582c0d990128649840c1848844000c0c005052103400780f585040341d4043d2550043c2e540314000098440708a42d82c0240107800c4040010345030700c29a070041c40700314028640642030103807840100312154480880e18051400721855540b4060f882204e0a84c00283e43c8025801d200c159500500704103800f4190900c0358454003000042601c00b0841c01e8944045000b051000c0250301240d40110603690050f00e0004801441c04255410b040d0700d05412503138100e0003103243c01100c0f0b01c40001003070140c021950500540d40944040031090000e0750044c803050740 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 511299829 1250 511298579 511298587
    0xe010e0c1003110306060c07210605060303070c06050d230901061205061614030a050f070903170a0207050d300e040b040209040c020f0f06090d0f020c1302 68
    0x2001111481d007040c1c0820181440c0000303103280c54040c1a2500f00805031455a11929142d28107405c2568640015039031140228080c0d01140300d028045040501a6408100c151030f140e0034184c03a482082d078003408000d0351440030010544a400100410400f42c0c0001410681344030030040041014000d40045501803c2071100341002849034800602d10b41d41400d542141c5d0340e07a40d80d103842d402410621f440d00c41c43e14003034841d0701495030510860140020030340c2c4d915084501c200105810b4580c100c5400f511000210b5850040740114190f0b5001042244148034403840007010f54004001d100460194800c000382540380c0303203000080241b107203404a40b1900c055921210961400c10820a51600b070100103404681014103001c3c0d010090310041022030383c00d4003040107446040b840c1504145009c1c4c0c80000f4a901080801c00c841c00442a201a09600001503698190582d17502c400c0360403403001050850301852519500503210700540e0001001c040020305003c001107080c0090300d130002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 511301079 1250 511299829 511299853
    0x60d03090812030f01060305160c0305090d0f0b071b0b0603070b0705060108010c02010b090109180c14010e06040510080702120d0501080f06011a0903030d0606112404020d060e010e 79
    0x303031200317015140c1032404214502d40440590100401c000c8003005120300039544030140752055040364003c101c00750010b24a00c49500d06000700d00700c070b00001d4840548420100d90034500c180c280303400c88440d0a20355124006d003900c412071891401f42c01160700d84a01980040c038046841d02901610740540702508943d0f1401c04500c0c20340e540c090407001164542107840516a54070000141900d141c41360003e203a5043d40b040010034000342c040a0f040200b40c44000420300f0320080d04c840395603802c0e03172014030000c07501043c8080b9004a0240d10307841702c01e01a4040c51684500c0a150348424244111038000e181025115030a80c0700a202d00d1807140c940c4014801300004000c0058040d07489802882c5661401c084440d0000740100d4501c0c440c4800200b080c01581d00b042036400458079180d0410407903544e503a01600c4c010078076480d851140a00718040000d07a181c0c440384030721050308003400d001030f5076168200000ca45000e00c040b169180c0d140c050300103407003003481000000c10f10304004140c540994 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 511302329 1250 511301079 511301101
    0x6120c0918120c120a0e0301140603070512120703050d020c1b01171602070801110a1103120402040902042318010209030a11010c02091f0f0b03060d0309081203 70
    0x681c00c05066964100451001500e0005144c003078640c1d402c421036294110780d02c088981c1c03202c0407640b680c15800e2004420322000081e132140d00904086003200c0083d90b94000b03001d11440321080b003409642100c01d951002c040c41000034a0344a00c02c0c44c0c8285418115203c0500301d0300400f50200003540301018001056012903000c182c5014242404540c500d10030900000c017410003000c1445a5006414154030781d4020070460300038081e010000c0c0101e40c0c1c00a01d8207401c0d080407032913500080180d02114a075030b001101700e805219a0b80c0188185543e039400f0b02004d02403104049070000d9584000015122103424010740e0240440d56110090600145a0400070310881605540b64410401403070507580014425040e00d600ca006407003a181d000c2c0058801341d01004c1c0185d0448580f00410250218a400c245041d0030712140d9140f031251590002218003074140502c84da41403081012031120715041c403d0074184c6101c1d2401d0383c0b0282d141c1c003480b0705115041c0d100302002d1002105000c0c00c0814 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 511303579 1250 511302329 511302343
    0x24030203011109090718090606120b0409120c030c020a0801020a080a050907030b27031306030b0109090b03010923060f06060301120606050a0b1809040b06120c0918 72
    0x9104000c9051102090001c2c0610001030300010a1200308054000d05006c4c546005006100144041028664940e0b0142282906142a003001e03881c0c4007401595290910540ca038a035000503910010114003a07040c0c0e0100c00c0e011058082c0f000b10303030340b00c00144e50301c51b403a5025280d04800503807544040e0758080c0a03258081d000c080031500300b1080060a820010700c0d01c048942041e00b003522521601d80c03500c2e20a03483c1118501061811224107407090000009148014181480c1c581183e6210412011204000c1c000d500088000e142086030000d01d8214070103088008000107040307031080d0b84a040401e102c60300c00e503022140641b43e200b440c500f848155070144040c0500041da14001000501910050007100d000c03101c2800800c084c0801540a4030142001400c03602e8040d45640005290360088036600801440c41c082c00c070381a003800071035180078650104850340192120001c0215007440c000808000e44030302c924036070003a510942c1c00c5000f044c1800702448040c51707880740c03181410303d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 511304829 1250 511303579 511303601
    0x2070210090806100e060f0609060c0a030206010f0f121a07020c0109050f181008060720010b010e04021605030f04050a060809030706051e1014010e010e132403020301 73
    0x1e151001008442c04002e40c595100a08035480071482c1c00010020782c00b070103122780664200d8004500000510000542a003025001c2d80031140c20f41c0c1c2e10260042d22401031300900011710120441040703800c02c0550800130781441111407001d40300c5101d1241401070f40448039540181d0024808a21650b00a82241c01a040c1503401c0c02d80b0414050100d0010061401c040d2074004a0100140c80012507541400262040d2070654045040c02c480c0100502550f0454040018a000003000c0c0c0450501c0703240500c80068580c054600007110421000750490781d0140c107400850403550b0b00041040c4000c00d00e044038514942e44560629041c4051400903400110520088105005091000006032940650320803008030301c80e5a40c4040081c442d1986400d40d540c103d0304814412a8500010078100b030341c0c00443c481506a000d0001103e0589840e08681d0201d4140d0421000500b82609032020002d1034002c0460340032842d0203010451007404a1081c1059441c20b414070441c6420b01801c05170034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 511306079 1250 511304829 511304851
    0x2070324291206040b060d0503040f060f0c0f110415091a03010618020d0f0f02070311120f0c0f340e060d0302210a090b070807031202070210090806 65
    0x20b040400055a2060058000317130a0124040015030669202d1120281166201054035201c50342c40703d804100030218007030f01300403807001900d800da400d07c0b4141d84904290848010812401c0d00d45030040510b126072202d40d00a9242c1844800112148801c40300500e06110005294240d20014113000034030090b4051090341000c10810a1100f0001c0c1c60b00441e01c94040103903503071a29034200e00200b0340d40365000c402e5824101209411041c13580589400e60007601c40040b15100c1507d255150000b81e030300f4004201c8140b144d07449074078204001e4003009007001c0840b1622000144100d140482c1200180d2441c040310104c05d00405c01d652240e12509100c03c5004161418800e203c0c40800b0001e240fa40a10003165981d81410b100b0040c866a080c0c140050507904403002c00c480c1d00c52f5119660010208105c250b00007048541c2204a0741c1c1340350000f117240c0c1000075035601182c841882c90700c0080e205400780f00e9000980d41d203280f4480e86010030f031111041c1c21b182401080c2854030003061081d0300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 511307329 1250 511306079 511306099
    0x3090c011803030e100201090b040606030201030509070608010b0c011503050a170a02341403120301080d0305060307150903200109091517160e070207032429 69
    0x84e041034182c2c2d440380c8102c41c516000008000202d0040149182c0900120456000d04c41840f0f01c1d035000c402940d00030fa80c2444141d6590000da942c444072807054000003000000100494060b40d009000084210000861042a441c0da003801481d42c54105032404c2d00442040410051402c64074180081c3d9501901e041040c0164081d48803242c94002e0b01c00d011404850000f00314091400ca022801c070002034a00c030795103e1189222103c4801c144a001c0c4c4558200004926908010780b41200d0806005182c0da044441d8110040c0c070002d04a140c15100e03030800420985040e07142340d10704526a54500950781d01d5400c01c54220a148081c0040d080400d00d81441c90b81d034410305080a461841c10049469206012801000503155008034001840d458030781d030759414045121010201c5070b00c1d901c8440e40e140c80c102640300300292040720169008020400c000f40d0100d0405010303c401c0140080705044d48505030066807100080c841141980c0c110154008909480703400d000d00c0305603002065 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 511308579 1250 511307329 511307333
    0x3050106092f16060c1e030b0d060b0402040b0a080402090604090b06090c0c03040306020414040b09041104090803150915061e090d0c03120c0c05010806041103090c011803 75
    0x780c0c1d05544004900c88006500c5081e1401c2100b07043c540ca074819010441c08604d0070009107440454110380031448800484402102e00c40d00070780e20444002444003070849056698600105510740460f60480d4007800009940300d1a000903064134034161f12003140c1e602c0c0038070420006650080105104a140c40030311b0307001c81e8005001950214081d0b6803054145c0351700c1c44140190140d1095031543d84800200481040910740240c022613011040103c1580040c1d000c00c0251110781c0300710750f0803051860000f00855a511010701030403c000e8000a00d000880d02c509a4950048824005182d8000262202400c03c085025400800b000c03211401e803100c1340c0004e00740c0c4120803031254510003409580b6000d11510702201e5150070b004007150607202440c80c02c00050710140c40150b6084032108503480b400c5000e02542d8203529440100240f03e607040100640c0c40c010081d2095420586da0340c010f00c61855107400450141d1101c0006001b024070380383c001001130000e80000707807030b40e110503e013000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 511309829 1250 511308579 511308641
    0x10308130f030c030b2502150a020909070c0314030c0301170703211b030804050f010501060e060a180f050a0503030c0d0305130803010e101205060601051806040305010609 75
    0x1c1583d5101c1c038220b050f5110305210340701b8811b07042050388401c140c2d40316040d41c0f16000643d04a002d080000300b0000c81c1c1e0307803500e05030483c0903034070300a82c00c0020880000d02d40d911515408401c14443c1c1400d01c0015031495030945da5070000c88132a03050a2001006000482445020050407898040200b40c03150031a55103850071030380d03010800c184844000c0c500f41031a000b0310a076500102a0500400090380c1810014050b090545080d160b0307006030380d11052260018003420341669110707240c0c0484c0d01d140d8000d200d110313400b00d1005410042c034008140d2202c11203030444c20003890401100d00b5070909020810441c410b071503110903c2175108020f6035403000700102d450800b20b04541000241c9640d24141c14211956807240101071160020011a4040e98910800c2c0504007070b0129a421a40b1804141c8899a0030100a40300340d12003000141998800d4000f081003031b0312140c04c090358546100208010ba0401d800481c3c80c0d035103448081c00800300d540309807030020094002c02581c5140060307602c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 511311079 1250 511309829 511309853
    0x140411060906090306091b09040c1520010b03010b04140c0304050705120d0f091d061908030702100e060a0e031e0616050c030d02031e010308130f03 65
    0x1900400340070449200540c0c6000a0303031168a4080c090300c03001c5c41d15684c4107803580e103580f4150702c00c0e03401d0303007070350b0025040184e1594440c55000460603030840c10a42082c180d4030380c170040c003820401c650318940001d440000303520008040820020895036a5101003600395550741c211540035910701120541c1d229006444181c2010031002516030300c5d12141412420700d54540c000d2a08522160f61064003031030001025030f500c403081e941e40c01c001400d0b9803040f62800c40034070500d082e8900076107002504011550401d90040c4000b016451840c80e0201c21000e156034650240f1a03e4102040d4481542080c09002c5030b05c10482c9001d00b0a90a03075400603e090162010341000c00041600c0041252030820540800130201c4190502c10f0f40c694803a513580303030400c076062800c4500100c20465030901030401d98007030b104d1103400355003007440560b001402908010220032856100511140300c0c082c2c04014540a5400340150756911030403020242d00150301c65015880f624041d010410101e10f17907013190 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 511312329 1250 511311079 511311113
    0x40c1e0507050304030c0b070c09140601120905120c010b04050105180406090209040f030f02010506090610090302090c040602250b090d02030708010b0f0301290a091e1404 75
    0x35a2100c8441c1002071540c02139030402000c0c3c0384072000216007440395201410786140718a10b60203107e42c84010f00001e507003d01c49503004c114280c0000c6030030343d80545102500740103000000204940f20340c46151402d41c8030301e2214200680080d220070450401c0c014104481015202445154035001c0400c075030f44460a0a607405619000114041000c0354228100e015001042c800403800d0034200100102a040006c801203920f9000700101c0740e0040c01050301c1000c0c02480d41c4c001d5514031041c0030a05a03a2a0218104a8041e0b804001640c40c404030501030181c1c00e140c2a00c65041290107850031011240e00c2203040c00e1040c0912400540324400300c1a90140e0f008030b41c6501e03612010561800a02c00002d6250140030400b05030030b201507000b0205440203c5a000400d44800241403c80d545a03c1c4400d4414407041d40303441c00003201c09415111900588005080b9a56441d102c08031222082004011105991680d50003040ca01641503140307041c14003c0c0541c01c19a0300d28540c04000084 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 511313579 1250 511312329 511312337
    0x25180f050a05040e19080405010906080708011703040e130b0c03010305060403050a0e040e2a0904020d170703170703140619090204030c030212030903060106080c090a14040c1e 77
    0x1c0300d079800c4107000b0b0750320b00c0c5c0d80110244040d000f03e00d40039981d50054050310780010480400095158860080d49008c1e0b192511a61450390030003007940c4032071010341c1d80d188581c4010040020b01c04503071500307075204000c0000e41211296007842c0465828801a1014a0b00307a000c2c0010310103c0c2d008181d094100341d060511b06d0340c0d51490841915502000c05102d0303401868206030805481d00850403e0301140c0e55205402c00b1a0300b20b0100f40b1180d54503600c80e0304029064001001410301c040c5c07500c007841c0280d110585280710110100800c0e80001801c03000904c1e6011030604c0509608a01c94000f10541020f100e0410f031101d000312110001071419200d000150a02c01c400072205441401070520102c007035503501e882e400c1080c0c0045142c88103c0c02402020305029040401005813941c03160000d001e04116480d006003221014009400700740404401c000208c40c0c0c0e0b07a040c005000926203540748650001040040008680380081020180038a840145220b40d0100860036103410031810 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 511314829 1250 511313579 511313591
    0x9140c0312090a051003090320030a050903210706050c090d020d03270f050f090402010c06060503100509010c03050130050f1f0b01140325180f050a0504 67
    0xf00d40c42c405600c0150840701c654034524403550305d500070444482c0652665000f0301c51501490b00c065094250380c4104c1d402c18003910000d144074900900c501d4038001d0450360060100a01e21000e8142d1001c1202541b000103504d0b801c1005c40d001c0e485d8850b21045880d410105c042010808443c42200000d2003055464000300c10940901030ba00c1001e03100340d00c00480c801c1441c6610b00c0894541c0210440c0248003c000280d030300d8505200f1114a001a1580d4030b95112640150b42848142c0c904498280c0c4500000c51543c5007080868003000040d840450b060034007290782030031100228074041c2014148001071016020452101c00c184181c010f0340e48440a84201a41c0181c50483c0000e219000c0c1c0f19484408a500154410242c2c044c1e06180080520710301c0d00c00c04481030000040c0c08900c40c950500e4070300804201565105100c000b0006152813040b150085008030059000b0202d2011000641420350380e12040024100001d00f00504908102c000b4400400300c2c0710320b0b0b1207952112 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 511316079 1250 511314829 511314847
    0x603090809040e0a0b070f03110c100c0c0807050102040603291e1309030e0d1e022e08100e0f060301141302102c0a120609140c0312 58
    0x10002c00145c20440c0b01000307081000340100810910101d5070700081c2459179007880c141e4100110380781e900c1540010603020071001c5880025002c03001c030440a00603c0a602c2010928900040c50704038840d00c00103944501b810310142c00c48609403000000c100701114903050320b02c0081d4205135928002c64841110066108100d907018604501441d00040c0b252161220300c0ca5070741040c51030f24803d803950680c0000c13020500c403e044007154080d04109814002000301d60046050310b103c11b0019000788624546504030b0114a480420b05404845145002c0321902d41d00480d103c2e086081080c0c01c1800c2c500e4801080d020000103810041544120f40c08100165000d502c00910314103180a011403d1401301e40c40034210889041c1640515010f12030300000612903114107230040201d0001418945944080d100c10448034210075810507002400411084152901c190700144540808a000e140d80c0c500341d240801465201c1d405a444045c203103030039a501041c0050001041d5010b15100c1c410a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 511317329 1250 511316079 511316083
    0xf09030f0e150c0708010b0315011406040e07020d020606041a062d031e1b0715050c0c010e01020c0304060503191d0606180a0f0209060d060f0603090809040e 69
    0x1040e458803003800b0010f0701010f812004554031044840560003000000314100501d40c950746070420b11b100c907014000040c0308500d031840d100b10401001414040c186501c0ea01c0c0c807410814140c0f1540c015034030002c007280f410381c1d040103803e500000030745043c810141d42d204098102c03ca91803080e84918804140700300660151320001001e0940b2048100c201018030039040e000f5030040c2c403106c4018003d200924801140112600d0140c10055400740103031204040c04621904050400c40d000c8402d0481c1072034540d060b00030640242402c00d00203075105c2c01480c04030b003140c80740c5801e084c0590060201c0a0501c03008415038007198840d040841e5207036568402008084452075281d200f01d440c0c040c0c550038080240e0031940307010680c1400c40d40c064a07007004011812441d0075140c80c81d411490009402e840d92070700546078081d40400054186181c20307000034a650000201040c0d26a6214000c100345003080070b90340000c0c805c2d41810000041d041c2c5440301c5500c10301c08040c3c091503d54400580394241 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 511318579 1250 511317329 511317349
    0x81f02070f06090b0705070b070503060103140709060e19053115050906130e0316050c031c050301090c0c060903030b040f06120b040c030209010b030a0f09030f0e 71
    0x8840300a011000c0c1c1440e04100500c01c003103090300c4076200d4100045c4114026800c0305c0c0d2964100c00d2a5803daa06e08204843c154070042c071150415484000240300c103800e4803915401410349803280b41c4540d0030060300801c159110400c4512940381000c2d03c0c0801948100ca10003030720001d84961031825014213111a40d4100f444080900464804200d00200030a42c04246000c0514400c0c8030150303980d80c10442c1d00710007520740c190b05c5002c0388810400c400311a031007031130031140e40029a800c01440c240e1200e003141030008150365036080301905085501c6c0c1400109040c2940d078581011074240c940004200740014080c0140469450801c034040c0b6004076004e0f1055a840a024001000b107840c0040180104120484c095400c0c50380854030040940980d105a8450180c4a00b4024070b544a40002c81d80c0030f00192a1807031007100c08809078850b0300750716001e04803044980c1c1d0384c1c6c103004c10b03c070048031490000e4090310307071401140c0000680d016840e0040d11686180c41d4000b40c41c0301d00013600c0600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 511319829 1250 511318579 511318583
    0x100309031d060702030f06100f061b033c0314131a0c0901180602031e1201080312010503070617180d0207030203060108011505100e19080f07081f0207 66
    0x10030130306c421105503000201e15201b03140c1600d00f00d09041d030380c0909240c0b2880303502440e400320350000341e00008403c140c031142c02450300914100341b40c2c0c2807401d124180030303203014440f81c007500c191480b6209801b80c1881480d40c4155500e8104400020000c030303000c01d500060510440c5800f500c40950911a80308040900b604125109440504054038115603c2d400007894502050058601e800101103101c500c20451b14550069407a004071044000e0540304103501c1700c070b44100140005000d107000030344890302900e82c0c1c030011a690391013030b0b0a06207003e030140d100c2c5100b40c0c072008040c402250701c00390054290520a80d95051500c6080c07400c1644042210703961014483c0c41c16410300281d0010311001101e000f0380950b00640d803209501d500765840c95101e4040b0400010042005081c40c0307044410300380030ba1401110960403400090500021800503501c002e403d400180040356042c03002420080c041c0c0000c286035883c1205e06619002c4005e5140e001e41b154501102071040f041e0101c0310655 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 511321079 1250 511319829 511319833
    0x3150d1b12050f0d02100f0603081602011409030a2d0503031f050a0521070321031802100c0b04060203071103040803250807050a02100309031d06070203 67
    0x40d01c49215400381d580001082e102441044001001241c3c04030302e1418100c440e40c00f620f401205808000080c0c48a55104070700f0355650710000020804ac1000b4000c0c4440c82600740405407140e00005113202f03201d550a119403a0b00b0000c1040e03d82d40015103480c1580d1151034a50f0403000c024401d0701842c00c0c04120b225080c180303000b0008028000c0011031042400840407121120100840001d09201380509608020000030522040c81d0180f11440325040a0301c01500680e05684d2807070904074281d1080b210244600c0402c1079030304507407080c00302c16844c92808114071911101440d00a6040840c064040c9110004a0007a98882e1403c91025900820302d1001030500c0d1403c000258011503015001900c2141240300040c000310494003202c3c0c4100041d0309291080450100310b2003040180310101c8441d043d4000058515000f4200250080c0041e11646c1150b0051010703540001e680c0b0410545010905400680c005807688030841d00c082802c2c07010704070000070554038441c0103406075042c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 511322329 1250 511321079 511321133
    0xe150105040b132301201c0c0510020a02060a20040b0d0f150b0d0615020c0f091b0d090204110a02010e0606090703051b160b01050603150d 61
    0x85801d24480d40c044a4500d2403407211002201030081444c00b150306040d0009010b895403c0b031040d80041e140a0000b0700d102a1902c106504140195a0301d02c0440c08010403c00c0003100107002c810304c181005440038940551030190744520003900e07900010094403600365141c130748241c00b01120440d546202c200c601c61964541d21841046800c1d005100700d4900780741404002004020640140e040804000d100411802d0a0120b02855900402400400750350f4564002a595002c0000d0030b0380c40b800354018001041c2c1950a001d600704210540f2400fa094000901c100104e40e00d144c041648070041d84c0c1c41c0c6519032259500058107243e000654400d09158822440110500003402501d0642d0001c102c03980044a009458080894185a11896880c000b402144c041e4011690000304d41c9200400403690340300105994124007101000700c030b00120b44000b0415906629409032504656250443c075000c4521103024600425184c09609480d03810b208102d41d040c424861050820154024 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 511323579 1250 511322329 511322347
    0x7050a140114150a030f080d110408100507080711030708040f05090106020106080d08130212070914040807030513170d1b020109030b1503060406020a080106090e150105040b 76
    0x10703010074010b020300388000501059090b9140a20740b18580c01c0a03140d40e0700245981c9528440100343c1c80181d460140c100440b0f001700c0c90038890890020b11010403140c4650906007254a008074114400301100d1915045c0036140703800c603002581c41146864480708125141d120a4210b010f10070001708107090201d00820000300d40e09290b410381c1c00581d5250126071340c4280490030b0303458610800015805c07108000290700e104110444d4401d01b40c0020582150719070b030205100f1003507200c000301c00e9004184140300c24a020b00130121340c2c03400400358040310706013515110325903c03482d0002401d01c8400615150505100c402c2a0300600c180d500f5050018094500130352100f048565890029001a02d81680d03051304081400c6000e030180e40d6110300e1750441e624100700c0c0c20040c00c408010902285047c03110707a410041030784214800e8402580b00d440c0c2d11409498842c040e00984288648154207005c0200c0b510402c9a008840e0015881c460f4425401039903030f4842c0b90070100300c0381c01c0050300542d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 511324829 1250 511323579 511323581
    0x24070c050114010312021c050f07051f0e0a170310051507030207091e0c140c030c061e0703050c04030210110601050603011206091103070608100e1b07050a1401 70
    0xc104d81c050b201d00352490240f02806c0b030f1900d99102101401d0b500c15648546c0c40ca109001038180e51a40c50714241ca061a00e8460902d0103003d204048030a9a5014807507080d10340b075029807203170010500001c1c030844c085641e80b00c000c801c1e100051000d180d00400080c03019000dd031102d100804000d480903000509030001d414203580040d005034050705c542280001d10060b148640a480d20130720310203540002c8580301c50405400843d001d84c1c00c1110209205000c0c1c01c1d0f020081c0782d203030040d000561b0340c0e9240c198441e0410000506030840170002d901000e141c00c1c000002c80c0c2d84842103150020b0301c1e60b00c07001c0401d143c0c00f5981000e901300c0d010701c07562036101c1c0d0441e030f200151210b50400c4518981c4c1c1d403410080e1301e2109000301c85801e240c9002403000681240c02c00311019200782510420100ca21002c00e10305540340e0b1102c8000740c910341c02c1c000784d4076004050710040e00380e100c0010a1171511059071501800c1d4000c0d402c60707030300000403128180075040c0928440107910880d950000300700400f00c01c1c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 511326079 1250 511324829 511324831
    0x11d0304030b0f0c03040f020301061e050a0b090105070b040314040e010e090607090b0d1e0516020d0207121e050f1603020907050a120c050307030b0324070c050114 72
    0x90b0310241050110703240c0c2c101e000c4007030b101d804140b0300d00e46555142d40e2074180c035040c0c1d080c04036015902c030b99010400803200c40d0b031082e19403a07450303014041500d0202040900b08440d40050300070781c810080902c45983c008129091103401c03891455694966290031260303002c1d19911400c9400003c2000725901c112981d07068100d4050070310044440d151054696107521003503030404080f542050042040e104148003500741054100c03800529021100c0d40c0b200250744082c030403030582e9640e00070400100f03440503220170b400b1114070090850305003401d001f0b555902580509201c88034040210400c202800309001040c100f50580f1000d07010b21450000d980d240306104403c5a40542d040c015486e031410400d01c0200ca400812300b820584540e40140c81c180e000d10100b00030410354000360001807046000b41200c05d84c0560310303641e50b8502403030001c0849000c001240d200750081c2c01042c40031005201c803120b195803010011455516881030a0358051386c0c0d010300500d69402c04000a034413900c050402 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 511327329 1250 511326079 511326083
    0x106050a0305071b150b09090a0c060c11090606090301090f060c020c03030f28020607031401030f0b06040209030a212d052b060503010203070210050603011d030403 72
    0x601241e00d81d03100030b0f84d000440c00085510440346124550100d0080c3c001c040854120030000114a020440480d05c0c600d070443e9621026440300a11100f0050300e030400d100100418a065441c084040e95038801400c00f03103d8043c0300e201d43c40c0200d01c0c01d035520f02c11140e42c6070004008100848140c9080d0040d01c9a02006580041c80d014001440364004503c5d48c8215000402540c6031400007881c90789940c0096403e441041d80750352850009000500d4132402da11400d030010710091030001801000e542d500b110703008020000780010800608900e4050f1802c41d40604009010f54890340494001e016400c411035061141000d00c005000201c0b2054580d6088034107055201ca00c400025565500382d03403011042842c4011101c0307110628100c900401c1241840c14502e0000240e8001c08042e2030301921050030220320801151803a0503100e480e00a20342a0001d50662030440380183d203910403030204019403070b240c000081031030b03400398000044500c1d40d80c1c000b54110701800c4065940c0c3c01c03034002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 511328579 1250 511327329 511327331
    0x323090c0406060e1c0c060c0512130302061c0513030e0315061c060203010906060e0f0609100c050106030b06010f02010605030d12090c1e050405010f030f1a0106050a03 74
    0x21038111420180150b10035640903031100900198182c040c408240b0040ba400c519a590301060710002814203500f00d0300600700c540d1009800300442c20001c3c03d102c49417049400f842010000c4001800c06403040c3c3c2c003100e0301200c0054680c001d440003809403c0c030110b4244140c03440c040401c002c09401d070360040040d44c040d580c0d0104100c6d0240602d0740d00e1004501002c160102d0a00049403481d01d14281240c06404070101d1b00520041e50741c10050740c00030f0700b01c0c0c0881515490148074040c2d02c18946611248101d8210f0300100111000c07614511402041500500041e0808100c0d14010b40424040030340c004020814030365a81884a038030320003540c071207000800e4075082c016070b903205004410076a100100a00480c0c502c0480030780d002c0c4124284403041a85074540c08010a80036445c4000a10814103200b0b820002e0b4030700315414440982045115525020060042001440400d002c0e29880107180e08800024102605404041c14402c00b000c03440c0320000c035403da4880c020304010745984d14 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 511329829 1250 511328579 511328593
    0x1150f0b0f18030a05030d020a0f020303160f0201020403020303180114030f0f15060a08010609120b0c0705011b05091e10030c090911030105030d050408120901032309 73
    0x203012403188110010290590014004a03000410030290b90000032801001c07640c92120580c0c60300d082d40c0220744140c6ca503640c0030940500454020310340b102ca240941c03001c0c501d145000d070212500864001d40c08000c00074100186d6105c10f000b5070486004d1900242229200c0d00008034296041040020041c0001d5041840c03a00c00c10407201603d02a03202c1c1c8818a40560795250080c03401d400c0185014001d151207079175420f2940762140140342081030799a03121825810040d010f0a00c000560040e64103046c070740b1480b40400c016181c403507000070305404401c0e542e548504000d40942458640d400b08480c0c158181401950044014640040d00707039a070414400c0c64907281c1c900044400045600020006002c0d44114440c1d80b0010740442141040c0c49002d48031a0000120b848008072200d16960009c0140450b150800000341070180500d40949881d04000c2e1051319402c5230071400300e0380070340400c2e42c410700da0181e0081c14203c900c055414042c852910062071660005803402041800350318 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 511330935 1106 511329829 511329839
    0x50904050303090105360708010c1112160f061d030408010b06090a06050a0203190c0201030c03050708060613050d0b061009030c2601150f 61
    0x40000c41c0c0ba450031034030641c21528064085000179100041c4010040c000c0381c40c01d280300301018421000c0d4001020305914103165a00040b0300340d400c01d509103002c550b11216441045180c0d000300c40e940111030300325403294440c845440400c0400c00c060303440850550110f003840c4a201d01000206640c8440309001442c03039a0444100303680000504111828090048801e00c04080b0313070041c500300d034410020f6440107940c0700e004140a004211200c4d900d00034010f0718080c038551840c6150309803a682c001801c036166450201e000ca0310b401109481207110b441003034441d000c0c90325404425124002041881c0e0420b0940010310400d2032000b20f1130ba11800c102d400003a21420381c45925003400780c200310b440b005041181040001d04c100800115000d40e081c0d50407100708c0100418600920360030b540702d41d200003113600750365802d04441041070152600c890084404e096101400b040e294 = true := by decide +kernel

theorem cover : BRFrame.Cov 511151079 511330935 := by
  have h0 := BRFrame.cov_init 511151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 511151079 ≤ n) (h2 : n < 511330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
