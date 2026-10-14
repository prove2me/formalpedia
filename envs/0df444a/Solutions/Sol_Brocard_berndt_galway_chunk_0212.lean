-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0212
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:29:38.497908+00:00
-- url     : https://prove2.me/submissions/5d9ce7a7-2850-41d3-b012-269fc025767b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 37949645 ≤ n < 38129501 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 37950895 1250 37949645 37949647
    0xc090e0405010b03070311010207050108060f0d1a040602041503020a20120c070306050106020303040b071d120105010612060b030a0c2a0318031a04030e04061805100602030a05 77
    0x20301040401d600035254070a00504550510f640c0f89440c00b01c40703061122490041c0100034000801c0d500031454507000d910004c00c5031401c50549030500c088118000820b072090040754001c0072209117140c00b401e0081d80142c2000d81d456042c4084d80d000d0400300500c50301054410801c4104861b4003800c0b4040b43c01c400b01984180b451244c08042c40c0804800f21440001000608448030910025140d02200d11803002400320b0783e83d94409903102d02040781e004e8052081d075000119203511030200e00400d1620360025500e402100404220b04100464007142c06079911070040c004283c0052440f112034040c100d05000c128100b0f0b84082d80c500010740b80644103502d03031403403180c1d50740241c6450801025190003000303042400030310785040808800c000e0300401c00d6541403140c0040c070180090b0070390fa0030212411809110600700401d0000040082e000c004401240b10310700c6e0b03600c0c01040c0081c4074203840d5411041c070046c005412241d002d0403540c46404610707010052650044107a4140d940541001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 37952145 1250 37950895 37950901
    0x90b04051e060c01020a0809010e06091e01090f081804050108030f030c04030f0b0f0112080313150219030e150f0a020d0903050a02060703050f06100c0602030c070311010c090e 77
    0x4907402c0e0062000031080f55001160140c1102c1c0e01c101d41c10b1050b000c00c2c0c003c0c882c4500131032072945c44000584040c801a00300d4456011041c132415040b030551101c080001443c00f0150b103e10140011303401e82140e00711000107101024101c0341d0101c0d009184100e6081240d5403400b2451640c1e03104038020214810380200014514482243c1034400035074125070081034141c040d20306011038010880d640d182c2002c0c2840041a0910302d04030781030102c1da00601070391a50b120145540e02890101c04119141c46d1a401181c0d1582c510b800078000d40c5038035010091405400020144c1681d0300b582c0d26075000d0b070001b4001c26203012080c0056030011034442d05805a6101c1ea1031000c00313842074084075442142029821400c241d40300008000c0d01c00903500741c48841d03d0380c4200710f0030748a05956201112121201003103151801002103800c4071580d007010248240d141e5203c02c160b80080710960507200001c030f6150305058100e807580140c00c60078002003145c2c0030f034030714090440101c40c020700c82605446800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 37953395 1250 37952145 37952149
    0x90d030c020304063902030f1b060f071b0819021807020a05010204030803040b011d060f0103020c06040f020f190905060d0503190306090b0303090d050a0f030f090b04051e 75
    0x2401300c81017080720040d50410130400c1000c4101c41c210004a009129014107025900004078008004044207205a03101100d000200821500800b0f04091020403c001e00d07400100090031820300003010400d000d00d568544560142000c204d41c1c0016001141e20342e018006940d40e45140070800e1803010000ca21b40c0703417010124500281888006c0c690341c0300040210034066010302651045218211b2090301faa202c3d12000c0303080d1000c0b55010214090343c000314825140a030781d0300c1c0d40a130061400604040d980700005103002019541a1400d0950340680000d60918943e050b900710419200e11102600308103480100713280303a20030400d60599030700100e0070a944085440004541000841341c40d1000d411a03107003c20071407020100030901c0c123034002800c0c5160f07000da0820340c2c20040141d070400c4111000d00081400e00703070007211140594503150700010074204855007414000d90b07484042d003401c9a8042c05038000782e0040002c542c01440100304550300c0607800001c4c0d5120b4200c180c040e030340d5a40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 37954645 1250 37953395 37953437
    0x4020a02010b1005070c050a0605070b06030c1c020a050d0c030609030c060c03020306090a0c140f0f0a050a110601030b060607150f020d230c0c03041d090d030c02030406 74
    0xb00c0140d01c030040f4804400c03c194400c0207080e8440c000e0a4600d11030b5031362001c21030094a54840d240c0800e106020b603c02081d242410190300410280c1900c1444003194009540d03400380c0440e8145080c0d070103450009500b0801d20300006031400b900c00c10000c400507141c200715807115200040a0326201c808600405105095083c00581c0c8070000344001d0300c80d00700241c00b075001243c2c036901030b000361800580014240d0040c262080500e03118a18a13120200a00b801c036441035030a0490390f041040035101510605e00204122203e0341d480e10b48488040300000c100d503000d00034840203075012030700601c0030070019600290004000c8403070b541d81fa0401c0c80c3c41104d2048074004052804e01c2c0c02482d0444034403640050442d0804500104003803a0003503000c110b190f15241000c4209101c11000590b892154801400300740e9084d0106d07403d01f542c411a80e414400c5201c4407440412500c000e0107401c0310200301c40e15000c00c0300e040600c5106d9081c04000e50700d0007244540d00400c403403d00c890b0342402c4050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 37955895 1250 37954645 37954661
    0xd0e01020f07060c020d08010b0906090d0308010317030606030105010522030b01080d020f0607030507090807030507030c080303060d030509060403170301030c0b120a0902060d050a0e07080304030f0204020a0201 92
    0x1402952601030480c6100d034182c001c2c0b00141c4640341025900c0d0441071000c0388840c1306c90141e8890100316402c09803044c8190300f01e02281d0f034029100300b0070b041c242e5444198090260740b2035502c18445604600d4070b0f001c0010340d0360000480071814810700c480e03a500c03007041d641510300a103800d680b900e000c0c0d40383c0b02c2c0000d1003030174040141d82285008018040e600c90101c1c16141c06400b11031003002c894a04a03034403084020400d041e600000f000c91100ca129800c100d07002222890142040d6459032100740c00c1904560084440368445041003081154042c0e6000c002d0091001079401c40c500300b804600d00e82c020000040401c000081c94039040d590703210940d000345411044620a00001d00c01c1070509510038041600c0c880881a030020751041800d003103a070303240303814507092445440b0000726201400071640201c0e07120006104c010030000d45482003501c160f01c010310115030507404144290615803260042c8000d600104010300200d0f2607079030050485581070741d00623500c50b2000c8040340100303004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 37957145 1250 37955895 37955921
    0x507060905010501080111180910080f060a1109060a0806041107050304080c03010e07031202120307030902010f0807020a0807060906061205010606080103020d12021c050a0809010612080d 82
    0x4030082003480301c1544528140c400810080203244a0315140f5040c03405801d9102402c2c13604800c28441c28103082190a0704149074001ca0803090752a9000c07581841002600300360170754402c1003004810b050a000311001c1981105d090b0b45860345440124405200e0100c40708107100c926404035150342c5540d880400c0d0328440c0050507880342042d151007512030340b25100b441e1032032143c80d0042d2602d14043c0300d903d509440201c0181f0320b940c9942c2d268500c00504890000035401121100051000a003004600c210320a43e40010707941000d100141c91205040c00030390030020210108a40282c0006041c15510f030821002c1e03440b0725051400901a100300c4c60010012805d08400060100350b0030288060035124000034000d190f00d5520441e4103420903c0040d48c0504524030403004105c03041c0c007a803101c524510581e00700c10300100111451031a407440c40360016100084041d405a03101140a0700124008000d000d05840c00c0d140c0158100301c41009403041000090b40050f0f40c48540c0700c1d08003080c030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 37958395 1250 37957145 37957151
    0x1805030a0203040f050604210f02040c09030209070306150c0606081005060111011104030201050a02160b0a031a0f01050c160306020d0e0a1709030a050f03040311030a1104020a050706 80
    0x30a400c02500e940040c401d40f045070190190200d85482c0c09002d89007030b1083c8001c060f450061118080048503407a200039100550380c00300340e801607290b90050030491001501c030022214a544140a006500103080380c0415142c0389080c00003015000d6036900300241441c119002c0c0c1c84600b0050014401a403181446119060b82080c002c595a004036121f08000d03210307009280c00c1200c0c22803e0341c603240080d02e107641040201740015030045c00502100310052046981c141c40d0644060f040e40201d030441c441003403010400e40c11340d543c940a40c4421600d1084040a0030144002089a00006c40c5825050100c0403c000100d40401c10804050001c0310180305400f5a403810070030001c0d88409890f4020b60300700340d5159100d4030005041c0d50b803903510640610031000d10000c18404d0b41c110310301a0340d140c020b1103050400b20b4010070a0005800e188006140d0712451494618054490317101414003a4111aa8074070124900d40a0f07006007140c192409681c0b07440d0780408071110303c100e04c0c006210500e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 37959645 1250 37958395 37958407
    0x91a03030c0c03070f06020d230304060f1a0a030f062301030c12110d110301021b0727020a02010b04061d0f2a0f03070503040c0f030b0109180503 64
    0x50002000b005854054098031030040e2614840031680b036850040c0d001681c070004905281600c280240c000c00c01080074176102d606141503140001c7c4e07100b03840030b4500303c0d01d56039502600549449203150341c6143d403031a90244030810000c100042e00e28840a40303038118030412002403103c250060304150111507048000401060080b441c880e500703000c01c4d039403504c08680200f080e80340c407860001c106802c801030000401c010700400100e210400000c440e0f00300d210245400d80c0d1070074006020b0b10b04007581d07580c0401c000b01c10003500c0c080440d4407000700380c1940007204841400070100900c45c1c5503c40005640da03030100005070f000d00b884020803a002071400b1000200c104111030265005e00b485c40088a90380c460003600c90346290300759072545a05802d440582e40ca00404000011041180b8001034240801d0b50841e41c400d400485048012560002c100070030000001400c41c090701d441034003079200c2c1c0e055454a8400503014020310388100d40c0d81b60a5510003920407900001160301c4822a513581c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 37960895 1250 37959645 37959667
    0x905060f010e010f030308130609080f04050f0a0b090607050c0306040b01030501050a05070504140a0b030106050915040b030f060d051204060207080a0f030f050409021305100e010207091a0303 84
    0x10424490b0b00c50782c2d9403140c00410100340c41c0b5440780c1100e402d03942d01891600c912044d00d00c00d03003008200302c5015546110b0b40f03002030125030190140003540c40c941501d03a89490b0500a2aa102441e00d40c4200324802c0e00f07000040b12901902d520880650310035441c0d9149103801880c01041e50812030703040c41101c041000300140d1644c1181680d10540c020310460b03d80c101e1a105460040d24480b000c50360a10083c4100103d94042811140004040c041540e46d505a014815842a0011000142e002071908101d081501e511420805151501131030107252040400305408090031a040c40c140101c00700b5590342c0c032002015805600b00060b1030f0100c2c045001d000b815801403180304054001c0c000005080000820079030402c5030400014441c0c2c0b00c1e80d540480b050850b1910355400e004040c44003017000c0e1110f1003c8e00c500700b0b030003031900c4901d400c00342013004031403100c03203420300700200050148901d1b64003040b810110b42032000301086280311008040010700a54846540501c40031980c0c00c07000e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 37962145 1250 37960895 37960921
    0x507170711030105040b0403080c0f16022106010306020304020604090c020a0203070501030605010212030c27030c1c020d060b0402180405060d0201050a0e040216060b0306071107030201050904090506 87
    0xe4401d020403400140e1075400d050903520210380c06400e9114410000300468000e40103d82e1100c0403085181c645460200c41c00c071143c100b8001040c0356024051414111300341624500030f00c18407148820118001400c070565100414040140195000302c0840c0c110344440050310041d000c104414040c03001c0e0044004d5589a9001c0c09910031703c55003034005110b50080c424441a2a81030303000e010b0b9100d03040d900f4481540f019140040300d4104000c030035000e103c1000200d60007007488a001000d45d03200010186040d01d82180d0904c41c103840c03410918001c50720003400d00a40e50650710314403203901c1820940d0050940302506504103000043c24008800d49986080002a080b00c040116444035401d1002040e882c02c3d00a011071010002d0740030302030040490104018000b40054a45041d100c082507400b420944201d90f1292550280f40c62480c0602ca600e501504600d000791150f098500660703601c56070b0788406414007000061001d881d4480780c1140d6001600075048400e2802c01c91668541 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 37963395 1250 37962145 37962157
    0xa020904060f0618090c020705011805030105010b030117010b0d030e0a080303130506100602121321030f02010b1011010b040e0606030f0307030f0e06070b0a020904060501050c030316050717 83
    0x4e01d81c40180460f80d00010710a071a00e00b46260b000741511403d0000544c0c1a0b10f01101d0404003802e889800103075540d09006640c040c1c9100c030803081d1a07500d4868500800300428441c66400d03418541c40070303401e46888001d980210703094a8140030f0490107c0110b03841c003100b80c0000007540070001c10468405844043d00340310310710400495180e41e5401f86d6049150101340500401078002081c0b44e0710440000015003031590119090b2204660f07a140301c41d0300c03d20301d00c281d0b040c01005204002c041c03613001070030010344503581d000034080300c0d180b10b000811100c444150b0341d050003034544e08004589401d40c8540020700010b4003c004015048510507a210030884649200b8801c945014900100203c1510b0714580d0503200c50680d820000000c0e200c2c01a0420102d401c11000c1c0404030104041803292800ba0240c0c540c0165500c44030414441a110950411418040d0800285000003030000c112079200c41d010500c0390ba03020440c041154940308882020380301c0c00e50b5030000c40590b0541002415 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 37964645 1250 37963395 37963427
    0xd0606030614120604060504051e151509040303020c0f0102041d061903020904110d0b0601020610030c170111130f1421100204030506040c05040e03030a020904060f06 73
    0x140095264040058148800e03c0f294055040300011500140a0b6086581c12070321072019960b0404000b80041038a500106480c202a0b000e0445c0b9071111400c03254150300584400d61042d02900f40e070380401e07130307000014000a041503400503203500c01c440c080c04a000c1c5804804000d554860b074410306080b1103103020754101c0c0300c0c0b0440008034801c1d15001c40d4800c2c3c2c950704840c0d026125891074080002d03000300240291503400c00704400441c2941c0311041240307150701c0740b50400e03880d0a0000c002858280010b20766140f0222051040c008110407405020032503219070403038080005000c10075405000c0740584946d03003100205241c0c1c04620f600c1581400e49a60100e00101c2c541d84d0f00100b00f80c4200192119041083c02240c0003003d8042071145004003000c508a405c150159141d1001303c1e4043c5d4001c0c5e5507030700070500b800100145400d152006100440b0280301c4040c03c00810746d140d01c40600721580e9590300045d411000e4942e5040000104110050b00d5650b070703503810300039090206000c4400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 37965895 1250 37964645 37964669
    0x3160b01090e06010e04030c08070c180e0105010b0702090a0603020904140c0402030c07030c06110d020903010f020906190207080d030507020d02010c0e04020901120903050a0809030307021c050d06060306 89
    0x1112402c00051030504039080b1402e0b000141c0c645031030503152404015003e865019003004900041034100c5950401420030034118038141010b2900f80007100c21000c0d940045074140b0004001c0c003902c010544546039011a24030741a41c95001601c3c0050074a84e000a411401c1042000140300805514514040c50003080c1c2d07071012000d9007080b08a20007182c0181030805c042c1306540200344914a003c2c2414890080020354083c0d890680ca05a0402850f02c5075440d000110f004c540d09080c0542140e6549021095043c815038400003030550194250000d04640c204007240b0364248204503000040005d00c0640d5510006060010041c0204442c104090300c240c410b4030171804d1052280c8040b0f811682d4a02105480c0c20041001a40c0180300c424104400b81c400d1a1100245224505c8418420b840380740d940c24031014013405007100103004102540040c410031007070a4010400400744031075661181060304030440107131128003410fa0402600d41c079220300401d007640c141d80154240c1c2e20b102541 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 37967145 1250 37965895 37965911
    0x50405151b1501120f03050a020c1e03010f02040e0105040915050403020c0411030f01060f03060906150207050603010305060c07170a090303020705060a020304121406040305030708150102060609040503160b0109 92
    0x4201c648030744401002c00105c91080c601007032044000e8544041c41d032040d54400c2d400b100c00034020b5211055944a030100c8100301100724a82480341455104117054191308281c42c003040c24078070030414400d4500868031740c00e0102c10003a40110808802046e030304100294245401d0003541c032103048a120780900e140140c909400703040039040c0d1380729165212886800d0380c240002102c801c00030854100605446070404100c1c9036003405004060540078800160814101400034a010107507031020f4001c29080005101144010410681c8401c0c047d0322941e4850451a200ea000015280f0f003c58654011411041c031360f0340040c1980071079000307600b2201044c1c1c4440c100041e6214001c000c00c01740e0710800c410064024290800381009000d404d000605100b181c4143c2d007441400c0b682140000c1c400000c1003a104e03001840c8a030000c240b035000c0da03858005680040d603100f401510142c4640d15460025041060400c211016084c0b402540704807120107140480e90303587d0078010030203c01c0c00c00c961 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 37968395 1250 37967145 37967159
    0xa0801031a090c040b031212100b03070c060209011407110306010803090d020904021927060e010303050304020a09060f06120c0206060d0615060804050d0e01050405151b1501 76
    0xc1c0c24040d542640103000349076034a100304402030130740d41019505070043d08a44002e0240343c401030b05a038040350541c80305900d0300c014440105201500146003007003043c42409441607200c20040344056024400599400c101c0c1c00517201880c240424100c9520001040403c200394a00b1202030040c3c181c1c1110196600e4520f03c0e5100e019600b9440d403c90301c0980c112000d85421420260043e0015200b0144801c200464010100d607a4000c007841d02c2480c440ca944102c0460b41c17400c80c044030508100075441c102102c200c030b2203e0610000e81006400f001207010341d6078503440c840040c680c9400802000341d4030307500c566101c00136200729800b0030901c80d0658060115801290f81d10400c5070301500c6103503510801c0100c81044020181c4280c2d0346c82880560806900c0031110240c003442c3c03100c941724038040c5400c03490320f40810305035000c01402710f106442d40c1c1d80190940b0184d8404855898801d03840900e04541030107040aa455115080d2112107404140030070840e0a00014100c8100144e0300c03446 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 37969645 1250 37968395 37968443
    0x2060601020604021e0d08030c0304021008090d1d03010606020616050301120303180602070f1119090b01050f0409020403061d0a03030b010c0203060f192007020a030203030a080103 79
    0x9000317504542c5942011100540e50403d80c0c411020040100002c0640c9843d2041d02d900110b481140000740042031200b9490004040f40c40003019243c2800646030030700c406030303c91074030040b050188440e000040c1c0d116042c400e1018903040016000b0000c040d03880c07800035554017040e1601e610280c00200d1084550b4441c00c101e82c16a074980f1540940b860240d070b001c4008080d9000d032116a003010744a103000045840c0001d1111a010712444105481d039801c080b0400403c10110340d00c29000c0e1307550950000f00055109045031468140050701d282e5501c0142c81505c9000d030382030280c507000200411907241c50350282c8162401780500300198502191b000c0c2d60850300e50342c001c8442c0d025074131003000207109802040c0d60f68410f1400056254a07039010034038041c0240d8080417003189090400c40756500e81003000c0d0000004440c14014404000c02c102d0030b090160b100903d83c0340300010000d0554560010782c400455026040300e60704c00b0058130040c0400000e003c101e884940c0070204c0c0e001d9183c0c0708 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 37970895 1250 37969645 37969651
    0x150b0d0f1b0b09060f040315021c050f040204270501060e010605090a0b032503020a0305070509010905091317030a0b010f050d24150e0a030803010e100b1603020606010206 75
    0x4900c40d4a084018810013086411111618400301e41c2084044005074118a030b2280011740104090380341d0b0b094017000342c00000b190750b0546040c2d14207001c20000081c59080315801039015900000c040c261003450340f50503051400c410300c50006500d84034040100550064048840050391a112642c94130411a420300c00c3d103d10952249808034140b1802100100540d00304072030a5420038901c18000c101201507840c0740450380404c1e4040b07607e448441d014090598011450b1611700e01c0c00b4400c01c0040d106501074052a0b02620584000981400481845803a001d0f0410098084203001251300351541e4803c54500003c5401d00040082c5540a02e160a00c3c0342e000c0c0d15200d007098108911240140001d00f0390040659800515410b41e4000c03c1c1b54002030100d02030030a50b80d002c00032000d425008100d5a1900508001108102090518040c1c905403441c040c0710001d29190040d001d252062590415202182e00080200260048003c507244480c403030307001d07624039503680001640c441c2011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 37972145 1250 37970895 37970909
    0x51e1008011803081b0903150a0b010810060509030f010504060b0a0b07031d060d0e060615040e0604090311010c0c0311030c060103060c090801090b04050f030c0a150b0d0f1b 76
    0x8008181c20f00504840c000c40e58052817040d0b0700703100045001a14005408038549540100300c0280040d0009a00032000246802c2c2000c101604210619030b40300441481004108480400c160f0810380d400d000d0102420f0740000240302d1810325040040003008081c50851140b44601c2303001507010740c2d84050318160398154981c807070400c4400d6500d80c01c81075005107070b07036124408200f8103c1d5a001841901a2410900c0080400c0e2030000c1c28406030000c240c400810a00c0180010401c20480c0d010351a440002524007091031040f07440c040d00c2500204490b50410350034003048060040c4e114600c002c040340a80c0d6405004001c5c07600b1203450b885900554821030b04a0f1006101107502c0c2d4000c03070035061a6103015113078070f0ba48104103070841e030480c10111800120b083c14132042c05001c12a030441d44500001451070300d05c41c082041e50f11180b8050080150440760b44442001e103469111a03d0b5000207400404c5441031458460080c542300001250400c200f02c03102d148013521080020151000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 37973395 1250 37972145 37972157
    0x30e0604030504260a0309080d03061211041d100506040207030c11120706030e0c060c030301030f06090b0411010f080903090402030a1107080d060504150306051e1008011803 76
    0x2880c00300003507240203505061306010f03c0b046220b400303501004845540f5019689280045040410340360820070892030280415040c05001d0140c08103041c020b4101650004280c0303040480800810080c20900c94000b80030038116400806491001c10206c000e0700450004000270703a141c50412049010300c0070050001045544944005070312803401d14150140108000311036010003d01c42d1030511290000360004c0d40314a00355108440c100304540c0411b03021030300e0a041c0440d030300085035a0302051101030720491001076644280080740c0c1c809030074140c100c06081101e2400d0300300300004e540c0550403580010118020b010486224000c16400342032080041c5180c0000c02c810440031b504098101c511aa40d50886107040b00c4103407000340580b610805840d62100b040c1c019080803101541d2103a0f010710705003982c05061a880e00030a03c2682c0d440f403c00902a03c40242912800300c2c68078a00441c070b003134081441008500400d80400704c0c2c215800070f2002103550401000c0ca040a498003c021400d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 37974645 1250 37973395 37973399
    0x80d081b070f0f050a060507030b030601080d0203030624070c0501080f0402010f030b010e040e0c1e060406111c030b040c020703020306070c26030f011205100c0311071101030e0604030504 82
    0x5085401d5074804e001380110343c01850075455a100b04e4030140c915001181c0c0e2110503c0480c00c050151600401c0c40101074114080714440c040c0d00c07440004d00c602d104510310209403d10550030040d141d5102c45100b00c450310341c1c0182c98403030007a90080c02040d010805a90000311156a031880c070500c5154181d5408003500c00944081e03025081184210303052015504141c00203441780c2c8109515150504000c180c05002c0d00305201038002103c40c6e1006290b03842011030740710b494202c02c4800311201440c010100e104101602400c00d031404001c1401e00c420400040d0301c10340e0580241650340401c440c1000034800036001070b40d071406103120080d010f07002100051003542c0a20010030005020302c4038410344140000f5a911120804022444940404070510000001c401d040c40d01618122442c60f200c00702c6034803541e0740c0f00c400b580e016009a071120204090540f081e041014186082c0c807039592548050302c0c4c44084144080c4406000a1070f1911103688200c002804601480d0140c8485203014 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 37975895 1250 37974645 37974653
    0x1903030302030604020c06130201030e03122208030708040507080a2301020f030906090106060c02031507050c0102040b0705010f02040b03011208090d0f0303060f150e0a080d081b070f 80
    0x1420003099264130650074070121002c0702c0180b09481c40f94110700840e4105003000d10026040711045143c4078504e520500c142902a04801d952139000f062485400450004a8000c80c54040300750000400c8a400401801244e58008440c00e005501c0344040d20885030b26030b404655038120b0000041c0c055190145641140700b0040e200f84003d1441d000054940051050300f00007aa10990b0340e4006942302c2400c02080150a104003030240441e803400c1001c00710140c0019680325507212070440000413141c003080e4032030301840c00c0340c40c2040508020354840d80e507082c50013243c0e0000d01c025262035081070800e81e00c1682e07c1c030803101a605a5036600e8116400c0040382412220411000c603000750041042032116582d8014a04425101d81501d0301d99000c80d24005054070003a500c521b011a41018050100070006c3c644d0160758862440c0c0741802d280c100307001543e0403400e540320a0250140d200e0303054101d54440b444501c40c8062110740c448140c01801705601d28492a48040c200c0803403040f2810000f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 37977145 1250 37975895 37975897
    0x901020f090418020a03050d0e0301050402100305311703012105010f141602071802070f12020616050306060d0c12050c0409060608060603011401020a1515051903030302 74
    0x81c440203c04000148080e0740441c04d005000d400540d41503100064010b9456840345030101c00c0e010590082c012420319030701150f100b040b04c01643e410b040c1c4820024045d0b11100e0b2000c500c00c814624000c00007100c0791074004480c1d01c2c00300242ca07900c80c0c1000034403509501b4000c0382d0403104081207190010381c84080107491020f4000c030071952952a40342e40042c1010034010410f1704885140d0b144004d041c04d644540c5e050044401110954000340e5080106030804441012501c0380440301580e110321510f401c041980039074100401101c1c1c0800500d00c519400280b80344100d440d0840d2002c03d882e0644207582a010480d0400da026504006800310a2050b03001491801c0315410000c140056031780e5040c05440c411030720140c03250008241040017400d680039000003028541000e03051400c2030f00100c0c00d0790ac41401031010b00340340c174032140815901c00c000000441d83c1119a005000305040204400340089003001a5010101c28003c5810719140c035090f05c840001040c055105461943c040c0c0c06 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 37978395 1250 37977145 37977161
    0x30b040f0605010602030a0e03010c0905010e03100908030604200d0c1103070303151e03080c120a02010504050c010806030d0810051002030306040c08010f030807020d060c0806090901020f0904 84
    0x6103102035880004606000d45406464039070081e54941d00b03c0345c0b000f0b104440c80d00041e03100ea070600124207141d5401100001c1500c2c004e2801d0007940145001117403400984420518040349030030308030410b1140a1003e5801442c08603070500c01d03294012680c50172003000c8481d0f038418903003c10000884e2103250b40204620845401c00f9000700100058607070554110fa0800da000ca0f440382e45918151311480008006861a44510381002120364441030303c1c0940307800000c04190000071803400d019001c200b800c0d41c400100b01425035600c890031000b4064901030301d0071075061003201a00e43c41c035802060058443c00b000380060101c0701d51541c0858045402034550180c0d81c2071132602080b56240c5680401c0c0d03248041d00155030303c0c02d0041c00c1c00200d582e00c41902e001c0041a1006010181441c280141200d410160042d15280107000182c003201c0d2241000f0082c43c9001d0315252400c0d00034481e00c0c40340c14119101d035401e40c0c03844601d50a0780b207174000e641703080c640401c06440c46203040d40c8507200c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 37979645 1250 37978395 37978403
    0xd06050f2a180a03080706060e07020a061112190c08070c110a0f060c0c080601080a0807150218041a010206010510050d060308120112080301030b07050705010c0503060f0316030b04 79
    0x1615403580c10104101e9000391300242d80074940000c01109004003800707400300502c2820f41d0b503d030503e08050000e440b224088801468107840300c00c2403440e600000705070368115000c40080405801c14a00a4503105c40840c80858454100712202096078043c0d82810b10a200c00e40301c80307200d140b007556000154442c2c0428035034030a65074ac5004c9210034610078400c3c090045030b25403064420007800c00000303c03d150f51148e2000c1d4441d0006000d404400b14200303200e5540304042985408103460588070204101120780c440038404100c0c4280c1c816032610400101c401918104004043c0c84030080001d5014020309015900c144010040342c00c021605002000316031822074100300707194480c103050350440d900039581039070080703142c0020031003c0c0da40c00d00408181e8460700f4100c80c2c0c0ea07100c3ea8140414071014001e00f0ba4003000511441c0141e003118403890b40000204600f0604010290443d0402d80700103021f01e48000c0c0001d090700700012080c0c460402054042c06151450ba0f03880c0b00540020070440d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 37980895 1250 37979645 37979677
    0x1080105090d0206011a210103080c0106050a03050a0609031202130f05010206100e150603040c030515071d0a09090f03120902031c020c0a0806161e0c02030304050d06050f2a 76
    0xd640e507882c0301f41c00c41c060351007101da1665030701c902127060342910070580107144202c003030100400000350001000b2800d154050b0002c40c040059003000d072070300e4010000c4070082500010f814005514012480c40949203050100c4282c140c0b030700c0c01245c0d288030456490b021096200814002c400100f11499071004600501c0610140c100011600070b400039501116076007204a404d1040140520554a0421000303038042c9662601180c024091520072145207050383c40400e0011107900c4500c06140a005401010f0110914601e0101a40404000150009500b005e240c11000752140202d05540b50010300500304100102c4182e440b518100c244201584180c0a11404545501080000400020b40a801c00345069162030420121040c410010401216141d080a10b00e66076011044161803801e401040c00134400b0900e0740c41203411141c1d06c02034411035541044941e070130040c1b007401e001280c05181e4a90036152407680803202c20704960110140d920a50620f40d03072010740b4640c0c40b052161 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 37982145 1250 37980895 37980937
    0x80405010822020d060e070b120a02030708071d090f0702010c02030906040b0903160810060501020a020108180a06020d0b0307081b13020d050c03060f09010302100f03020403080301080105090d0206011a 88
    0x55191821f0790713016140032400030492061101114509030b5000392500300130361441c40d0580d4000c0680c81300070407007024019140c400080300d2826403654214041c0180414400d410709402100013070340b040351034100540c00c000b0030144140c408415101c141c10003500c41410070341000220384003504008200c40c3c25200740c607a85940c0c94402c01006004244d54009080820a40b00c0400c003580c4480d0001030540d4400304007940183da10640c801ea002036450310f60b40025180c98110340c1040b414075005030640c3d00210b546e5a0b001203036804031035051422800ca0707030341c20b80d504003541d01d440040380c0c00040440b103500c0600c00d80c00c2a8501038034116401000518048803ea103680c102d901c1524056288075010040040310b09010ba450644444100c3d280075240d0300d1030380003540610b0205a10000c00c81c1c00e0091726446d500a80594015560114603181c80c0d43c0c552010600134141113900b490b903031045402c1582c0850000c5400c4e81600c1030340b42e88290035007552800604542c001211030411840755400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 37983395 1250 37982145 37982171
    0x4060309060b030d031b02030702090a0c030902151b0f0304060e0102030c030d060509070302093006010e0f0105061c050c0c010507080f060f0a050904061404080405010822020d06 78
    0xb40c4c8404025030f4400081140f0031a98144911000c91400b07000d41d4010000300c5c016a5948594607031000d14034001203240c4041d01401c802410076540d00a40101d818041c8000d101481d030701500d8030310f401c8028100012010f00b0150740d42c100c00c400c0011a604104010b01c161440b501034940580d1060040b00c0c50040300000e0b8500c1d41d0f000201030110350f41d403000300f40035518141c4101031300800c8616066050400000001d0800311081500300c941d000304d030b4503440a010702c03032202c49068100902520345070f680d130b0682685c3c1810b04840500c118003007000045180e00d0140140c640301007001c11000444603034008014014203000e4000070228134140010400d83d0000d00695200d0410390751405018242000017554102020f030449204200e5007004c86d80e182c0340c02c2c15182c1240c00032101e07059661610300b0000c004003c3c2c104500048a801070401c0140311800b0028401c40d174081e602d036074440c1e8444900c4091a400701141c08144511081c8603800345c680b84058200c0e4601403c0300064649500c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 37984645 1250 37983395 37983403
    0x30905030a0302030108070929040f090812180a0f0201050d0507020d0906020c010e0409140a0506090d0503010e0601050a0201060b03010906090e0109050601060c080403060524030109020604060309060b03 89
    0xc41c1400207030008014803403900c003804158010000340405003c40c5846852002c5200c1c6007980682100c0e00055a003c503c0c0e843c0d0300082c40200494104003c20200c60402c0011a40000c010f016032000190100b012450700c2e000e40840c400502001d8410070703c0301c0c2d40c0ca40724641002801c0e81000401d00c10220300484038401d00d0b00806031034008122050001342c01800143c260351015040d0b41200d040d20301980d80140d9170000500b012100010810042d107130581048610045031070341031181e0304c100fa00f0000e000560364040c9101c682281d18070780e50a001120640700034000d03000d91070000c002040e025400342d0081d18a141d1580004603002c2d03110b0751425400d81007680461001070300d840013005445d5003032007002c1e074510118000b481030803402d072a0035548010600c1140c6c00c201082c1010414021440c0130388005e154084014055030406c1c2070f59541a009000c0041103001e92140300310401c1c601489281c0300f90ba4080c0009060500d00704059004124185c13040c0d80c8503481d002840d0b46540c043c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 37985895 1250 37984645 37984657
    0x7031b050702011706150a0c0503040e0105011709150402011b0c1703131e030c0e040c1203020c0f03100624020609030904020a0519081f03021305060103090503 70
    0x250350152141c160340001400c41c0c2a0808044d04c00e002c64080c030007240c40d40034006081d800300c00100e40d5240403066084555800c0c41001070b002e40000308020507030015601d100e074100d41c400d17031f11000014030100400c01c544c0340c00e403100c460035401105039807502d2400b03c8450368040d005041900700d1a1031a00001a42000c860084815200b980c07400c0c0f010210032084428448000e500850501c0c94000d20325072682d0a0740114028220f50303419240c130003503010142102859018401c802441d80e584103000b803681d000d8a00301d8591400c0e40021490b950740d03407441007a540d095401042400c1d041810b02c00e00304500c040d0b140d00350003100c101a91011050142d08001c02d4480400d45030700040e003406001c400b074103950840454103e40d083c031003015800000d40796810021100103035107401e4048141d030f07244550885025181c1c0b13880e05480205d0340012030f1a204600c1150540d0105000010210f0508400d000003540514a001c00840500f016808290700c000c0c1070400060003822601c85503d140c21407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 37987145 1250 37985895 37985897
    0x3080c0105070813030806040509120c1b010507050303060f010905041d010c0f090e0a060f080f07060813080903010228020706030b0d030807021f0207021507110907031b 74
    0x21414404060f601c60f41e0183d200320000da004207026074580d4004e10b1040081c100c40d00c01d540710300c0401c00028090191602a00301a0319842da54000b5911403a00d8143e03400c2d41c8401250300c5c08820407994020000c5030405540040594915591401000202c0302400046410801c2502001c600c6823503070300c180380800c0c040320303607160b01540320011150035203100007003200820068a07002112143c0280c03000d0242c0304503124004282d903d20206800030b08603584102142c0c4000d04000030300050210381c81102c410701c64103684407562a0070047c0c4d00b150068645031b000b10301d1b4103c1c1d02c001c0f032a5a4040c16941038000e0000d440c01921140d00701d9014441c0c04030345032540440411030b0a45804110b0368000781110304051184590303690025160b1200400050240142c600c0020580b901c24000e1280001080140300d0100c505030f000c16000750415074040740203186c144041851400c55a068640a079804404c585020080506200710180050030a0f424181c40d60100c000301c1c00301590700c600500309 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 37988395 1250 37987145 37987151
    0x1020a0203040f1706010b030a0207330c0e0d0c03050708151303020c060a05070b04030e12060c0d09030c060204060c06050c030702060a0e0705030f070608010b0313060c0903080c01 79
    0x1480e80c0f541e204000d5500c840c0c1022900807201c126900041a000d0441344000d0080e600c03903841c001800c010b4441d006008008a00018100003400802c0408509000c0328224417460200311507051012103041d50418004510075280c91540384c503012441e541d2251041c0000405240d03a0b580d89032502e070b002d4104500c9034200ca20b0041e22503402c01c800a5001d41c0042c0b03010030308445078a002c0c0d00d0b241031500d92805508001101c2410b07900610403204441c1d40701c4124001071500d030400070856029030b003a00d44122003070204151501000186140101c0e0070600c282d2030240003442c1e070002862451001c03020b00c01cbc5100c038500421000d2015000900e030b6921280500e880625080c42100c000402c80780100000f482030050407680014000d40c402ca07804400a601c1075032812541c94510a58451941403148801d03108600c10003048000c03c994141d2a40c06044e40c03104505441d81c002128449241540700450038003042582d00070b241c03241954105000c00680382e03266043d0640c0801d8074400c850791 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 37989645 1250 37988395 37988399
    0x7170f010f020a08070f0806010f0302120702100e0d1d031f060801060501050c0c010e0a05130e0c090903030a0203040816050a03020c01020304050d0602030a0e0d1e2d0201060801020a020304 83
    0x3030007040c0c09178012624a800c490405584401070040c0c1e501904050400a103030304148800382c081d03411103104060901d440125494003000c02582d8410510038603051909001505508034400203800304403500d1a01c03070200c0c0541100205a40c403151044042e0b00d4850380d080c80400040907840e1040c1840f02c03c0001c00c2e22800c1107078003400d5901c04c5d0b11081c1001410816410114004103e40303000d04024030740151711400f0362002a0b803c1c0440c1c1c1051382d20061140340005117240d130f40c0c4103940085420307068030210f5507020b0401c0350a183c1103920256a400400020300300100d6940199406807080300c40e2410300549510503803412055841c12120b650051809009040d01001039071404e010034070065280a060030080b540039182d20000030005900800892061030300c0303401100d203032614402100d0b0b40d4664410020984200740754041c8091000390440500580b0501c0340c0c4241c000b80901041c03205008015000c3c4280c26044101c085559584011030003407000c0c00100f0703641899030300440d2503038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 37990895 1250 37989645 37989647
    0xf050906180a0b0601030b011e17060405011d0705071b0e101503020c100203070306050a140904032601080718051005090c1204150506011107170f010f020a 68
    0x250300307a031141e01d966014194000008206000650340420207280100302c80700c100005840841002501001c00070045030305100591340003c03103a4012042c042500c50703644820041c403044820a0003007071400904903108a03030b0812101e13500c0750400c145281c40d0346810003a40301d89080381e6000c0b126512403505040300300519281b0054042c0c01981040c000e41e0b0704c034907011200a20300848640340040c54bc01042d0340d2400b80c018440e0308402101c6550640d902c0c503052200074001e00032801360a200d0741c40c800022a0800042d00c40c52124040a0818081d0b80c40303d44050b500300c1c2100440d409810019280b03641955039415039036000b00a41d2008014040c01e1200050708003800160702e1010929002c10001041102e62110040f40e0050760026440d84034458800b0980c49202c200202c80405a07041c40200002c9241c90008801c45c130f00100440c2d1100001140c001d205522001129849048180301c0c0007034031085003488804a5086030f1080120100031401d43d1000d054240300075a0220b0041441 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 37992145 1250 37990895 37990921
    0x806040b030a021507050f03030a06060801030f030318060c0e030706020c03062409010612050f04030519110f030c010608060402030319050f04080a05010f060803090904060f050906 79
    0x410455061025045150201c0d68500720040c01074842c20502c0c00c0900304521603c12610001d0b0072400b41e402c10300d08121450342d280d106990240c52640f600c0000aa018032488206040c0d95111841e25034440713071514210098110300401850180340c0300e20b0724001a0540c8034540c0780c3d644913240c44203a1400b410405080050a521103803c1d17401031110000b8a59000c01d295601c800e0b2080d2200c99029003501c135026444600000c2a04242c000001080d0990440c1303035071080081d45441070255a540301c0c3c00650f11441074400a0204009202c812801124012100030100c0103107403000d003500070701000a00e0040d040a412a0301d4000040303074002040d003030140f1000380020000030445401d055011940e02c1c42103001c490025818035146070540ea103d4002c4645603002100503684440d01c40d0701c4a611100e458104403065880d12a00c0345005488c0e00a00d0704503421000510b0034a0003603414842c6046000304103d40c1d86680c3e07030588074880003520075540603140305401041d0705d1400c41019055 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 37993395 1250 37992145 37992151
    0x60e040b100b1b0f1609050c0405010915020114181005070e060711030a03090603051003080919121110051305040b180c130614030114010504080102030106050301030308 74
    0xe809072494050290b01c22402c2102c21440c5201a8040320f08500311109003452110030a6040c68080e032200c22000f004501e040c0d2040e200c10100400c200d0300d8404c4490340c1481944a02404640483d50800c90181850310540054803980000f0601c40380003907010513803580072180750380406e42c4002042564001040f006050040e039000c100314a08282d800a00320600c2000b03503030b10880c40002c0207402c01030301c041030400d20700c005002c0714107507445d5281c0503082120398003441000900d010002000d4102d1042100100e9420510300c0380740c01090702c1444101c00010482c80c1c0c00b03400e01240042d0340d0710303885e04e00101c0d20700421140714413000d0710040040389601036002a0400c0010310180c40010185882c41c4210b9400302e800051110462010651110000d62104502425441086240300c9444010058003144001e01c2c07420545a082c262801c4611081c80504550f00b0f000501180d802a988050382420506003241010f64403140c19003a070740242c1040c00050004070041081540240020350 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 37994645 1250 37993395 37993411
    0x30a0f0306030f020d05030705010204030b06090f04030c031211030c07060e07030803060906040b03030309010902040501051801091107020310020405240304060c0311160b070f02100c0210060e040b 86
    0x40307030307034510f0725180060010000040e106070b1411808000300f080030000c985111341e01500943d01c4550740e050000f46103800b00c40710f0780121480d1000491220680500c14441c40c1d05845403101c00440c3d89080364100000f4129222040d81c0380070b0401240001005180b146503040c041e2991501c6618184055840c950940010ba0f07006000920000b5405420349600101c2a1910b07103159481e8000a0064181c000402c0c0d0140800010b01040010640052441d6802581c0a002c00c1c0d03a41e4080c4241c4290007000c4084881e0206c006001d6059143c0000740e004d4222025541801010303000282003031a40360206040b40e500090800460500034244220346a00b44400300b10106d02c0740c00b501103440002c09c000c020a50f070f8145848024000c0c1d105800c03d03d160100b050320b42c000702c10014586030040a0a94605035101e0004210900c44c00007400c411806030701030980941800f440300042c02d490b50f00076003580a80d0300450070f51a0750348a5140100b206c045c0000503400c0604007803243c1c3c80c020b04a00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 37995895 1250 37994645 37994651
    0xf1a1011060109020a180b03040c050a1208030411060301120c12080d0f06180e01061a04060804030c0501110307080a0c02060619080708010204030311030406020d0c03051308030a0f03 80
    0x40d02404041101d6044448450001d43c0c1c4104443c81102e4402260031601408103004e00c000c00c00950b07103006944154400c24010550035184d0013000817810300c40c811750441c418903101e0b00c000118544050f5400c00c0c4210007039000f24401c880000e44503042600702c03581941002c80010103000032500000b00910030705028003540072046d11070412512807000005216926020b10340d040f038501e50b1060700200400e51205942c0100c80100c0006041584c040c20215130a040c80441d00c0400c0d050480403843d000e0003098546807404600744c1e2070020082099041c080515048408500d0038055503051600110150343d8038a0100030140030352101608a582892600000d030f0310781c640008549801210440325101d90310b20780c2c1007401c0702620540000255000328040000e1801c01500900152842502c41085540347c03e12034a0303507030040f031203084c1c0141e104c0050443d0023070042d4070804030540a407500500d8001c048103050903004080e400032103d82c0c00056800350305a800b54480c072844656240074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 37997145 1250 37995895 37995917
    0x607030504050709110c0a150b030304050d020d0212030d02030a0e0604050a0303020d02070c03050d090b1201030b0a0e030a180501090e0604020903030c0706080f0a06080a0b0603010f1a10 82
    0x4207558500600880504c2540c65180303038195504841901e00403007010084500301000382c901100071090b10340b610710390542031102e513012503d0003000341e40640d54054894607180c5a1350b0200480c1581143c016a006a103030502c0a000350424001401c503c407802c6005a62030404540c5a012a005c4840c04920ba0b04400103000c00600041551074048d901880c0c0580c81c1c0d0510020203009101d412402001c0501e1002c00108005001c2092160078000c0e03291050003a0350381c01c0e4206248105079062003804514001130002036000300703030250410b905150000725161102d909074595480038002c000441c481d0320100380d0b80b07a00040044003606080c60012403c0c0e10f010100018540040c3c4858421a00401c02c2003031a1010010b40c4d03515400c0108a50a03142d1340d40340078002d540143d0b80342d04281c040e42c00261500c8036601820046611400041c580308a01d40c851140380c20000e001c140c0d0554035000700c4401000383e80142c201c1c0e40450700008494540c16010000d10010070b010703620a0205400766 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 37998395 1250 37997145 37997153
    0xb0c0c1b011b060615090905070c0f2604030807061a0a060c050c091006080105031912090503060a0b031501080a0209090114010f090b0405010b1812070305010b030607030504 76
    0x1041e9107441c0c006120000b001c0c42440e010b4003030040c5030801c100701d69805041000391603001544d0300c00c48407081420400340c0c5806004645000041201910740c401014040c130001300d4810040e43c54000c1d1170038200310303140007228000c440d621940c82510120301c04140703281407201c00e2080c0c2c08450111301141c40c22450070302c0440c003503100a11688044c041840308100510600b8840d060b0b00c210010505c8040c1d1600711040d0380c1020060183c0b0b00024803000010a0b9800c00160703030041c980f04d50b10420294a40da87d03411136059144192142004001c0c40d0010341624200051401088011008511050600f080c1072500800c24082c1202d0010305004005055001c111011141d806450000d10b030b90325141000c1c050000c550b0103440c00801c81000140d5a1040800c850584078124002e004038075000d01004280c44080c010030035440f40c02c110740300800305800021054010083e128152540c1402482030074650240e2007564265140c0000715082c0c51b042c84443d61000d01ca0a082050381444d0322 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 37999645 1250 37998395 37998407
    0x2010b030c130902060409050c030702060c0f030103080903100903111515010e060705030c0a0b070c0b07030b030a0204020d0f06080a0507060e01091518060509150706090b0c0c1b01 79
    0x1010b100182d80344042e50642d00c0340806c03103000d0070783c0000501c02428100b0b00d13040d07143d00c01c50b00c40e0014014800880d02c2c40c0e284100325005400b101c060b0710308690031034803071823503d6101030301c2c10340c2c1131040b502c400141d00a07502503908000d000b61100802c5500202d40d4604007103041401080b2502d5010411420340c0c02d0031040d072201c9801f0b03c0c1c60f184184104c80490001e10840001078014400801c5010300f209000400c07174401e40c45140182865207034440d0580300045209001040c5004523400641c400780b103540880d04058004003103070907587e111b0700480c08981c00a90210200d0342c4030300b041d0404158070301517040100180c0d0010403103581280ca40301c2e180c900501603d001c00440f180980d00680c071078405000038082407440030720909201c0301c000d00000440384902d51412008840050210301034000e032082c0c010049d050922580c40b40c0c20a080d240c1c8000400c03141d9540e102c9040c0c022903440001984100324450106580d00c50700c3d5042498000c20121313403d595040c807601d428060768081 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 38000895 1250 37999645 37999669
    0x105070b0604060e01090e010b0108060d0204050405120708180111030a08040204140702060402041d1e030d02030f090708031305061309020f091201090b0103080a021c0309020102010b030c 82
    0x108038044140c68600018026001e164401002c40c1e9501d0004664401568018518449410020000c00c2001401502d02c200c04aa20035840b02d909172100d009400c060b0802c550180c4503006072035480c941e17481515525004940c003665203040c0400c4180001c2d6101e0425001100e090170440c012500c502c424a03641d1143c41c40b8603081021178004030f000c42d2a65004240380c003000581e1009940340404000b907a810040785c0c20b0b4412070401034000340c000c1c00b2100e0b60640c1d111100243c00032030040e26041c0d1400c00e507451316610510040240c03884000c0280301540c040c8003440390781c843d40e0806205183ca4105250401766440d0010084060854401020881164002e42c0c0ca60b4072194820080340450165900c841740c07032800060b81c051040001c00051000440440f00600c0c80d04a0483c818200d40032124018494180000144085000e4002a1049031650b10454918504c0e8285103027030501090040d40102e602d98a001c0304568080c020841250001e400421401000d40c000501400080d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 38002145 1250 38000895 38000903
    0x82401080a08030115050d06030b070e0a0503060601030c020f0607020a0b0f0f06010c0305120a050a0614100c020d1a01031202030a021b06040305030f030103020a0e04150507090e04150b0f010507 85
    0x13000342071700540c0140103445e61030a20354401c020303041d45d905050003070a02c1120300000141d10607920440c5407a00500394402d80780090010403156441200640c000d1524401c02e409511400c41e248184103010071815200d50590f40c040c0100c40d0003490030100f40000a041d504500d401c4400300040300041c0d00e034079039022009103410102c0c8903031030400381c4e4240304800420111780c83c00d004201a4000c10303003006004048140707003007009590b81e0014145012000f4501503010310b0190f075064085108080140c0041c0c002000c641074500c0355074481e16001035400980c1603101c05007004005110b000d9a1640001e030290029519080b01480d001b0345500d2a07415009480c0804500c1c003040740c46010680c1d015540c403608580c1d841c004c213091003404da0130901c000c9214040d9868045141120092f41a02899221011082002c0400e50306005010004c2c001c1040000b41d100000d1240c107940d140900541c082d020305150b400c01d40105105842103c04d446000e045031410342c0841ea640304086401890704 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 38003395 1250 38002145 38002169
    0x30a0b0a09030e0d030905130b0a05040522050607140406080f181603020f030703020319020303090d0b0a050703060b1c06050303030403050406020d0c0804140406082401080a080301 79
    0x1c0d240507583c9200401036a40c200048008500c2019000502801903c10480303022038001030058840741a20b60381d404007034100344400c00c00c12150506070007083c1c10032000c9482e5035900401c00040c04c1c0c050040c80301a0b50591010b03050102d0b0701c0e008025807040c180d42e90081403605003011405010f84102506060313840c031404001400841d584820760110315501d006582800380c4a8940800b8810740740801c2e485090480003036644c900c1e0014035a01141d034050040d1508402140109110086003032060381c050000308400550303a910860100324062060182c0012405c1503a460340c2221802002241803518000083c031001441000b590304407401e0f40000808400f89180d400b01520312540010341511001c4103000c00c02d030f04400908107951a41d800c4950b1117050410494211172060f0016151800400c01444054180d5015141400c0c0150020a8090ba1442110310b807410340807240c4400e41c907200c5150011401408014014058a40108a8000300b80c4440203184018410040070200d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 38004645 1250 38003395 38003411
    0x1b0604140d060e070f0302120706020717010b09070305010e0f09030405040b0d0501150501120c0c20030a1b050105030105030c0d051204030b04060f021c020903120f0405010e030a0b0a 80
    0x502c9070003180c4205442c0066403c0c40e039480c520150030741c405000491149217400d42c01300210308001545402c54400c0d90040019500c0c00002010521740804005240e540318400c0d001c4989070884150700440300c90b54006a00d42c546181d441044501410800d0003100000510000c83c074000706580a88008942c0040c0c00d0700003900050400503107034401806942000881400300714030164880450307900381c0725440b88038491b4804004a072003401c4c1c03220108416900d400003259007039442d110030141d142c0b400a546c00048001030314141d04c3d5071003207840010403000c4154041c108008040109401e003040b9045504040000e81c46a04089806000310000c28406017440406c102e00000d07007895011243d030320f075100e08110514000803501a40e105040c5203030600c042d030f41e920880e01c110079000c0007001c1201a000030207019502c54a0896414896101d45101d030707100b1500100812541e25201c2c95542e460f003400908610074035101c85100750000c105040208181441440d808281d104000640c15 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 38005895 1250 38004645 38004653
    0x70f1509020a080c030c0109030c030b06062203020102160b0d0906090b090d0215131202010213081006060806060d0c0302041502010e0606060c070303080604020c0f1b0604140d 77
    0x220101002940c80b521164001030115000f10308031850701000e5050b04c0f0050840301c010b40e409409840300400390203460341c080002c280280300944c1c0090008110610700b1924a134031420692240001c4407411500d12420400c40d80c0400100000d00c4840b251440c41c03a03d81242c59000d80540c4d820341700003030b8450001808200c8264017011545510842d034100c0c90812121484d83c0d84818215040580304040724071019480c955445803162440c0301c21501e214040e07907101560072801e05945c02c1559000c1c0040e0241c00c4000130346101404284000b08541d1480612050a41c1c015500940600c0140d00070700815865030400c41d40c03800200607000c1881c3d00c0c10708084000748141c1c1d00c86c01e079007100c0441407016194190040211010b100080364400d89a1a007006114400d0300b070503000a600c034007410400a0f004685003170744a01d00400c014142902d000c0490b050290005120519070002c2406065090f44a40d0181c82c60005a4a2038100303428800941000f80089030254810081200070b03178104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 38007145 1250 38005895 38005901
    0xe0c0306191d030a0503070809150406020a02101a01021b03070b0708040510110606011403161b1a1005010905040e03160503270303030105090612030c0303010515070f15 74
    0xc81948201c030394139040003000600035082900c1001c00141c83e200403414202c4001201d5401c0341c209090144513441b580d071000c0c000d50156030608154001e50704000c550b22483c3c450a43c4000300b8142c0c4c10008a007110009003002080c442d000c1c0c40642860040d4540c0d200000c01005840090003540c2c0c0d0341c00c1d03d04100c6003500940d032219070300203103c0e0521420594014174020005244808a4440d52100401910301c908549080000b03a041070002411810a580550b80e2010303e5007400355204412861440700d50003803810940741e000e0000c4d0305040c542040703c072407580090760000c200300301401c0000007002d0190621400d489184c5500115405060900c00c49080380220a209824020766103046030b1a5003064180504c086102d10000a02080d0000610041c034002005945035a09160401400200c05800300e80c000c4092201c207145000c08000078402c20070200e0046881790b01d0038040180d41040c0203181c40580b071091207080d002400283c001c1c10166030014048030501c10900c880002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 38008395 1250 38007145 38007191
    0x70311160b090f0105160e0d0210050f070c03080909060108010e1308040b13050405010602030a0c0b0403020f0613060506011e08091c08040605060f030628060303030e0c030619 77
    0x95540780a06001c062132552042100d4206d09441d80d40d40503c03100c6c2081000520050080d4000c0d40d01100314042520074030080c8028400d0351082810822507403112620304455070405c403a18013000031545124a4420700e010383c0006d0910707000c0b40c590b05250000400782e1001d004014a621050325400401c03054500b0fa5005e444038a0446850346641c1d648941541c1e0b107880f407180641e04d0f003000404d10500c04070890381d00c076025850f002c404403040c2da5000b072402c200a10035802c6005140c1da01d071071060103000d00342c0034461000b05a481001503080c00000c640020317082c94140150300302c55503883e8104100f06900ba80e1941000315075543c41c00c901d00d080140c141402083c006170702617030020940e0421640c2e401a0302602040005954100c00d00a914400500240d4594090340c0041e50207903289003d86249114460b00404080740b0804000503114550400c8001c42e440705040798806000300718851000c0022001071405050800000c0c0c6018100100c1d440d1381c1b610b84210810788007c005003884 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 38009645 1250 38008395 38008423
    0x10e010810020a05040e0f0a05090606010c02240403150506010302070314070f02030f01062d0b030c09090f040201030506030109020907030b01020a02030f03040e01060207031101030c0c1a070311160b09 88
    0x46c04e4504015840c0c1070f000304030380100701c15242001003030504a000809512891041c0c40301030100081d41c08111450540089402c4450b14551403008061f00000c0540011881811600e071382c02e011000480544134001c002034105881801400003003588102c2c60034030f011042c00926500e0600d42401040810241c1c000303900340c45001c4280c01e480c0070550105003200d201d0b00380e45103040030120964809040500c3ea50140301103940d010310056100400450f048440c0b85942c914041440c00070a071500d1044994684202c4400104010365805024150b40108203d008000c0d2001325400a00c1c036640280c40842059a101205400c590080044280181e0018102e594455140c180c071a52070f4081d00800920040440000440c00d0002455509803980f05c6000702c5c0d0f102200c0d004400408110400d042000021100d000c04150034140203802001d00350b0f8501d18610349060041c1c2520310a01c808501130300104031010860588081c01000d41d984180b0031035031a11108011480c01d4146c1f90621 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 38010895 1250 38009645 38009669
    0x40b0402090d0b071101140105010807120603051c0f0801030602030601090503010504050309011407030c060506040f020a03090201021204081005090a0c060903022706010c03090f090203060405010e010810020a0504 93
    0x1024882c0c80f00f001c0d842a405680c68414400e0342140135404e03500c0c5510700041161600e0700501066000c0c1e658150700c0041c82c030300340c1403000316030302d524054509540c4141d80c0c5401c07048012407a8070400401b003c1100e040d084c0140701d505a010024604d140500c40500015404004140a607120b60080b10040400a00034800303810310703043c21030b12035001c040c10034045480c400344900a06858010756038400e401d6161001d01c9140e40e1241e0002c1c3c0002411a076009540d0b484019042600788050300040116560014190341c8070b200291502e60003484003441c0c0700062008008900c0c0000380d140b4401d030825004106504d500c16a140352000303d09009280088448001c11525032100c1c2c0082101d0080303d81d1142c15802407042074080400014042c0706da0302031000500c555000780000001d0501c28034000c0240c540e690841040840c140d00305030040d0750000144055403429000c0c1e54003600717000304c404201c0d5141400380c82da15140c0e800244042500403501c60740443c01103081c0c8009001d0400c00c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 38012145 1250 38010895 38010919
    0x91803040815090607030b031b0d021003020a1103090a120213060b07030f0302030708010608090a0c08011406030f030301060f030f0c0903061407021b0604090e060402010207120302070302040b040209 87
    0x30795082c0034112104038481c4144400070f0a0580b00b8068020004005000360210000b0004d107415200940d81151340c101219880d200c0c0143c82c0c09004030421141a540161902c044540080554070101d922548660086c0482113007a07031040c03500c0088407400390b02c00300200c0c00c41c40032408411301c80c0c051899a910f00580020b4680743c0c40d00501c02c444c03003644c64401c0c60b00154810741c01ca010940d006000030f0880b100611406000e000c55503041400c085c1107d00e4207081d82d8421501c3c1c0c81633080b2103000e075188c80711916130080911005401480c124041c02240b132041620590b40e0105200d10703010010010380391440317103000390b004100000507071009210300905039002514803809440101c40980c0340007a940d03c1a80384070349450048080754064050a040304050713090300352041b118690722040400002030010702500c2040c58030b160240191216113454000a030400b059540000c100194419400c0f001950200b126030076254100c400080e00313460500450024000c05000300e4100b4982015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 38013395 1250 38012145 38012173
    0x32d020403020306010e04080702270414070f081b120307060c201209041404051b010c03090608100b03070905040e120904020c01090219050406060801050918030408 72
    0x10400da038001d5003201c1300d40c0d0f621007861103034280c11200a481090203112941c0140741140b240712055200b0041400050641d03030380d44902d80701c103807000ca8042441807404140302c1d8040c05820000e06000c0d0224415526201002d03844030451809070044038004da201c0c0c40aa40c80fc01589403400491080380d440e000d907840c00800400100080c01c0220f042402c502c42c40c40040446084200300301d17009400c400481c0511810f19410107007015902548801611803003100b1028028403840c000d1000b0001020781044c0310f890000042c2075a81002072281c0c28501207074028092b94100d88c01840c01400d595500c001542c41c10070345810030b96080174000148180304da4054061416139800b11420412002ca400100e070303a89010004907520480284013095492400e0380c054003000480800120340740705958001401c59100e498082c640800009003844642060320900000d46100d0916100b5541000d002464500b030007170898044800c80c103015850440f06105440040001c1002c44101052540c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 38014645 1250 38013395 38013397
    0x1e03070302070b07020d03140f1201030b0a0203070804110a090f0b030c0105040f09050c0702040c09031b1a0c0106030c06020309031011030c030a0e0303010603020c0c040b10032d02 79
    0x4250010310802d000801c040b4082c50403120b41d5070b0b00610726401c1c0c0d041603509641803041d0610459521b01c0c14000070150200802c0117000e00c02c0340c1c0c45c8410b0b10750f0540c541000c01c10300c0904080c03902481801004070944c0c20565650300f0a4002285d000c0032004440040e812081c2a0401f0030540d040c0101070702d44105c542c000880018086040d41d402c28246401110103016903c1051542c0c0c0b9072280400901d00c0b241c0c000e03600005114610361400c22139401003425601c00d411071600056009804000784008484e001001d03c64040c810318141d46807098145d403c09510074418030748000041d5898a1000952110703009503440080512a00c0e91540082d450b9080300c180e06000e80208000081c511300903104201c805c2d070a00714014110b85500100c4012600000d00621110396074200084c04a4010030103117008001c0766401594800b41451464201380c424016680181d00f001c040d80c0b0142d40300705052a5880d000e01c2c00151950700a8964070300d6103540d0055603420017001c005030700d6290541d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 38015895 1250 38014645 38014657
    0x4030818040b0306070909020a0201060308042409080325050109030306060210090c060302090112060f060e06120106080703091a010504060e070203070f081c0e01060b07080d0506031e03 81
    0x19001c02c1004448070074903840700e4045030940c5c0000c410f11018030102c285580903041c80700c3c051000040254407a07a403040d46600036041901041a11220340c050400145105041c03194107207031010216180c00e8900750b49001d40301c00b200703269440100c0054421492a1900429034001009100941c024280a0001c01a90107001c00601a90f6100107000d60380740078030700511f6803181084440380d1034003004400a410443c00e1604010419140c2004c0d01076a00420300604100d0340c1d010f079218508040504059031001000d805424240b0010020340c1d4000051070445034603003007030b4260381d4401c1d108400810342408024044030a111850782d0f58804010f41e68140c0741d080d10200650b40c0c507004812150700c4200d48480050703004012420000b803440040c8041140b01301c004901780030701c240d0b40e2080010158852038035990344200186c0141c1090180d000103000070340c0b400b443d001603a00d0b08c640502c65010360380740e007503140c0c00802ca054034200020650021504492041c0400a00e82c59480360701c10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 38017145 1250 38015895 38015899
    0x24090c08060a0b060d0c020c030703060b1903031205061302121f0302030601060c020a1a0a020c01050412110d230d140a0c05010e0106080307020111120702060f04030818 74
    0xc1d000545944400e209500e100c0000905017418030644030200f00140a401c00d9800450041d01d11110380c0e41c800300550303c06036100d88000304101c5500d0040c0700c03540c0051440c4501b860340d41001007011941210042d40007015004001c5519030707880b4041100054041d05c841c00309407000891001610080a030117000e546032010248c00180b5102e04690004140e000c0603605400c444010000c55000d2aa014040f0f0f09c041c1c60102860382c1c0e2513103581c5180b036120411101850005190000550520107031885400034200300b401e050500b8582a41200c1900009102d800c01060703640c81a981e12078400c9850394400c0a200c29030b41c0101640c442000c1080300d15100e072180c4401000900e01800800c40300110303401e240303070034134800c80c034100e0b5402d44007041514079550b00d008410382c880080c0105030140008a005507629041c03840014418596038075205032a810801c1c1c1500384180da94111880a40c0407103a80e603d408555000340124400c03940000c000560024003100c1200d885983d100c042042 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 38018395 1250 38017145 38017153
    0x4060320010806091b0c0c03030a0f0e0306040506130201030e0a03090512060103020904020d08071407151b060b06040e0a1d01090201020d030203090a15020d05010506041224090c08 79
    0x20f01041c0141c00d503040e60b4a0600b00c110341ca41175820b50200000c0c080b02007602c0101c0d00c1c3d034803241c00800d0469022850b41d4001507550b0040e44c900079041134090781700c19000d034014805840c1c01d44805880308001350882009030740e160144000e5a219800a90305480b141080e214041224034020381450710740c1c8140f41c001c801174003000400e00c201080c194120380d0041d0405142d40d80700c1c1d0030407292590042045a84c41018000300c1c01050308092400b107800c0885009003042c500307184010301900c0600a0240030481003070154201805881122100d0691040020030000d90420000300107003d00e0300013400e408003120401c401d00742e150300403240060154000c00b400c2e100c10b58505081e074100850190250340700782a40c840d114440c0e4001c1d0b030302c02e140809564041d40c481d0341d11051200030310b000414040e000308842c80381c004248034140c018202200c12034a040d290084100c1610901640904441a0700b0046c0c000304000024080d1058803400c070811907501a4a370030365480545006842452003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 38019645 1250 38018395 38018401
    0x1a01020d0903030203030f06010c0501090c05090901020a090302121509060a1a010c020120030a03020904050a0509071a090402031e010f0501091809050a030c17030c030106030b040603200108 83
    0x402040a2402d0300d4043d4042c526558620540990030003020b003030385042000e90342d100e1011400030320495820620901d0141e03444c603d0311003040072800004d00048426441003000c20701c03d0b03400c10385510032650305a440490a550750401c0c03070305202185c00c03050409074192040001030140403409520500c04684100302d1040383e500c03600e5441000c6640940818207000d060340156014100100304507803a0101001c04a12568000b0300f980c2280040c00042a000b28081c881c0f860b00d1700441760b012000c500200424a040181656500d006220340c20109032440350b82070198040c601100c0171307520081c00030340d660b042500b1410284419080511040000c40001041446588400d03030300b1640141d403600d580d1810100d030491503501005012907240d54807520000010018401074200d28081d4981150b015210b0804642012a0034405845084108108903d070300020b02668103440d01c915001540391441c10105004081980000c0c10403000440b802804801c0c880b00d500714030000380e84900c1692 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 38020895 1250 38019645 38019647
    0x91208010e0705120a0b12010e0304030c080a030509010503070504031b08011508031909050405070e03121608070f051507030e0601140904080409020403060b210606040507020c041a01020d 82
    0x10003600450102c040081002c1482241c2c660410b0a1500b00107000387c03032107441d441d8168210f9003102c100d2081504086010070500980c045c4440040c202c40d0040d2501c00340558006100c2d124103a0601c0c10300c100800455107880c810701c246c80141d0380c00303207800d0f103a030500c000c81c030344c01071003d1007001b0f260b600303200391f41d01450071040b2000f040b0362418000b181024072002c003007140040ca1134020401c1000404000072680d40724080c1c80d0088a07a82c4814960608490506003402e4400c05050806c81c0c080000920a100ba00120240e442c2c00c403800a40b40c8440b4038000e42107070448800075002d84035003c3c8240a0203000c0c035205010320300c203480401501030842c1420f07854407000d1103040b061103100c400340340e25800d02c0c4903401d03446417040300304900d0700c0c0d02e60700203d00b00d8209400680f5601c0e80e4022030011402c00c4c5010302880300c00001d000900440049030643d541c01c008000d6030045490304085910240204400c21101c00c00030020b12507488882e040344140342c01140e1550044c410040054105 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 38022145 1250 38020895 38020897
    0xc06020106030b150901050f0301020c030409020304060e06011a0d02120702100605031b06070303140106050d060e010b03060409081b0c03060105010c08040b13030204060909050105180304090e01091208010e0705 92
    0x1c4000038140d240f460707190808005c010b2010780c2030030390155000c004cc100e6509e0103100500191201c0030006880f0b0034241000d40c00c407204c0303c40710341150340040014000e04403008200c40c882c241013101196555504104840031b07000b1600016480d0380d800081c89080307900480c10a0340c14080f0441005a15621030815a80700d032510040f00c480d48603505002e0302820326900624555010341404034802045440b00d00440c035092f80910f00296000c030700303840005038a0244000401701e2446e00d150650400781020014800078081074829030351070b1000c00800074490300b07a81c0c0c68140300341c941447c65001c00d1701644411000d40c0c854807038002e00c0c001280c2980142c14000140f0707003241070700341850301303051040c61107500c07410004011545502c0c0000040c5e5030750103450060142c0100c00308042c1c01902e00030b42511000380500050000014006244800010641d4211140e080010845121f12001c0c1401010b02c000068031800c141c03640d182c80a500542c03d80d048680d200e038600750b00c1e0b403000001c82e03003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 38023395 1250 38022145 38022181
    0x30417040501050a0302070503130807090606030b01051c06050316030b090601030305160c1e081b06161109040b07020607020a08070209060105161113021e160c06020106030b 76
    0x1042040c01102d480601ca80d000d000b07d60720400c01c0f030707186c5002c02c44802d108414541c48504560b11548042c0800000790150400400c0181802c0c040c000d48140003a00740d0040440041d00505100300c00b500c0702c90142c201000030b0101406446010b07014800507102c00e59240001c0d9064440c40b000310f4100f40c400a0094120794040e52840e0034622a00c82c1c440708218081c1c030540700e10015150100e0103052107400c50011504e1601a0030803c0e11f003040381030402c1c01c250001d4021198210311409152100d40840d2040c400707641c802d1341d4950840c600102d1000e50b444040e600204034030200030401c049542090700550258088940ca030750344940899450070441401808800c00f441500700508195810541284050401030f0800641051190306502c0e0f030a02030300c641c5d18410305ca41d007a082085409240c059100025840e081c03515094218010203035502c2580d141c80050104038118050f20210400c5138440044800180c0d2201e00074080e015600069411258040204040c0b008130380340162 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 38024645 1250 38023395 38023397
    0x905250e04021f050a0f11031219020406050904230106080a06091b090e07052b0203071701050109050a030b07020a0c0b03010806153109060e0601060801230a050405040305030417040501 81
    0x40380c400c0e400912788201101070840401c0c842a9a2214001e6055001030801381c211030ba00c058032521240100001d654210b40c0f600f08100980c0b90841d0380d2030b11000780341d05480f5242800d10b01c80e03c40e00000001010a507205071602d44c070b0404000145200d121040014400c030b07680c0d1951031900d440c03603c2400700050382c502011a070700308210050001c010059100e040d11548080e440b0000c4001c80c40300f039074011251035000500c50403042143c0d003a1142503c1c090309080ca000303803d190400d004a441110360740406048004818001114035208210021100e0b9020606141c11540ca2140860642082c040c0d09000d008030303000240010185141c00d94260002858603c00041992100c074024094995005c0728480c100750030744c400c0a039400340c3d801c1d1340d00c90740c5c0025107844249140c40c200711040e0044420881448010071004d800440b5a942047c0360880b00c007624404200060799894a540c0b0081d0058101001c100c14943c111024512807070242408000a42e15081d01c20001c0c811402518 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 38025895 1250 38024645 38024647
    0x90c030703051e07180e15150a090506062703031614060408070206130e1005031e06040209090a0203010c1205060d02010f030b06090d060905250e04021f050a0f1103 72
    0x1584402d0303e43c00c042e41b889625816109204a20856000c1c081e104031103940070421620f00d0350f4114107003024420300030145c03501c0401044c00c00380005810761241044c0340c4c81004102030076110360b000b00450300b99070600080803a45e58800140d20340b000031a200340144c0d030b401e01d0f42003c4c0200703800101d00300d03128550026900d841c3c00354139420860107810500110482001015021501e02c02030400c03940034002c00c107045a9400d18000804d0f280c0150390741000f11032041e0790907800301290006101504980e0448940303203581d0b18410704030700d440c0b00400041e6143d03007450940e0356601d402001d1800c0741507140c0c00601c00c0f42d40d10020300c45802280000280083c900040c645003040c4643c0c454584400700509980c40c2886c00c4000600e1903c0b546800d985075940c0c1c02c130403020013100300005a02c0d003400900e0540441e4034070792643d1404070305209012800c102c400010f0115a10b041c841009080041a10907140600b800001d110340c0000c03111a0101e601049814002406107102c8101500050021 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 38027145 1250 38025895 38025929
    0x816080103061e1109040c0e13020708070602070f03140c0607050a020316050c0901050a0b030103030f0e0414042306061c080a0c03180302030303040209090c030703051e07 75
    0x21001080d00303440f800d50721105080d186800c01c0e103034040d2043d207008808001c0e07101c284500070082190707107024a503801d00440395002d071000c1d11061504001c1c105458001030300c2d5412030030454100c3c0300e060310050081e40300043c08402c1092501039100814065555044040c5007802d00c42914400c2486d400c4455001e400003c1800e80300340020000c1d0849031055070304141039543e00d407803040c0c1910821146078116446000741428002e0013140140022244844483c0c50200b09000300d200600018040001078884500c50700d003d2111000600000341c01080543c000c0080304116a10603a0100d46250917a102c848000c402068006007440c0100b0180802e078441ca0300300100d0314980340c0c0080b40d414860807140003007500003010b0048560603446044102005103401406014002c0c85030740c1c040d2507d201031026032000801d40382d1299050395038030101d480361b824103498007d8203000a40d01d441099408401c0140214030030407078010b00459283c200b01014101d588881050081c0d8014082400300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 38028395 1250 38027145 38027153
    0xf02030f15120d0203041d100905060d082206020d09051908010e060108060106020d08060904060e010204090f0b0612070c14060106050c0f060115051e030f04030816080103 75
    0x41e0301d0302000a04110150342c2e1101c225090480845610300503070008a01000060189116595043c048601030141031a000d140c6001ca5030160085061803540c840000310607031035450b8200307070041d00104059158400200c94401110480c40707039070340398080c0301c0d0300007082c174000103156444045a44510210600b818103010800440c8104050031140c456400240c0600a00c19140c021100b003028003169030601c0920340c03500d407040e03004108550094405c541216800418241c002000300c502c2410f5440710700f002030203003944428843c860351000900146802c0395500c2900e45000e00c40703080c8a419400800c014080c003800410f860445103560020b482e86204020f1100711030320480c001c0e0803c04000b00d50703502c3d050302608550040340f0002244000305608101810240c01c8000c02014298108003e095850203820115000e001000c54152102c4414200740c505034120109040e440e45408a0300d8180107a0548080c0d001c641080040b50110080101068082d1702e9610b810200b81d103940d403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 38029645 1250 38028395 38028421
    0x2010612060c0f09030b0a18020616050f0d0c03050d021b0c0a050103022109030c100b0a080d0905040b030102040b0c100e03040e04020907051204030f140405010e0f010201021303060e010f02030f 85
    0x10541c051a410323400030300180d99440141240480c1ea515040c11000d4501e4928507000043c90714100a9110350703a0f40e820300d980402520540d0b9418a8225200c140c0f002d41b6002074080e20255001495200c59034024407600080e503403650300781c119a070a5089a84c2c8005504a108a0402417a070b00040b000642c46000302280b4907400c07210060469241c10b2a0310500703410f2110444088560a803108941e50262510307030788800c00703406d0003005040c0c13121400101812802951143c640a180c5031960a44255001c0d8141e90051224030301141e6a800708071051a01c60240c00b980c00d003c2490b00b02505680340000090f20150b402c4042c0f01d00700d0381c8660f002c2015101004000d101000005c010107418501c442049900940c82070712104501c004a00c80a070181c60b09184904180c40e050000300107907130784400d81400242d010380c0c000f8044560000100d02900c41d8500300310001c034109100204104003039000c030070391600f030000800222010342141c0c0140d2006407480740c6200920000300300c03d60341c200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 38030895 1250 38029645 38029661
    0x50403020603070c2f01030c080604150504060801021312031b080d1404050f062a04270e010204050904060b03150903070c050d050604030f02010612060c0f09030b0a 72
    0x208004c8116002541c40c1022810200100124886281140ba04034100100208210003090074180301b1400300850007084000010504d03403040e5141d182080c2d1451001c103411002d000702404c01e1040680b91600d01d4040c0d48010720700201e030340c003400000a0451200440c10082541503645d480c9400388814503111a030b003140c0080e603100c60100b006101da501940f140740d401c00c0107550903101d549428106981040f90742d401507002504900c0410184140c54010010f03d140e0300d060145110a2004262600b809181c02c60a4900d986010000302a800780c00d1007422042024410301440019407045801d0f070046100d4a50010804804140005c142d908080401c7e40060704a0b580b2061030448210010f000b560300b00302d81e400c00201042402040e0140398041c01040d40e000c07013946030603a1441d664480040000d07040000d003081185900b03200f90000700091007400f180d400d41c004181400001030100d4624240455030307076001220224003074000340c0c081f070f41c0150010718259035003c500b2001e00800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 38032145 1250 38030895 38030897
    0x60e0d0b0412022a03010f0608061b070203011a09070915050306030309150301230d0b060a080105040503120114010806100e040510140105071101050d0e060405010e160605040302060307 81
    0x15402507402c080e51021300034203d5265072081d01c1c0e50503412007410300711801d04409588990410400380100f050014282d038000b00940050103030310b07a4001c0c103426a4010000002c1d0f243d401c11305117182d40c000c203000c590b841260484846400791941d0702d080d14505080d03c207040c51f42c0315403020440d80354010400f45901c01c00140035a864542100b000072090118441c80400e90303000440103204500c20180c00e01e8110360304054070807071141e06000294420b10300380c1c0010700c01c00740b90f0f0001d04035469034035192009041c010003c0c031540c200351030300303a803280c100c0d00c01449403110090000516105516003800b8000713040c2c42c1c00300c480e200d4500303019102d601d60101409028070702c0c244820f162298412503200c0c540d00303e0341450307035800c1003071070a0542c3e1201005410080c092040c1404504941d20f41d145100b000d080040c0d45560364424100039001d071091703100c107034041e040030041840702c10340080ba003a1840f41c0546021060085000b00c0c0304170719020365030000d00103000503c01410040011742d001092 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 38033395 1250 38032145 38032153
    0x15040b04020109030210080702100e060408070804170106050906010f0c151b0804061a0102060f04110901060c11030601120209041a16030606210c0311030907060e0d0b041202 76
    0x21382d00419036819042d0f0306140080c1801080001a540c14000c2d4510b40803e0b0f08240602000d00708001c1d607903080070f400030b4040000004c1203410082050100d8008001001228040301600c21407035008041501ca080d01850b02400020348640c4540042c4070317080034036103851101c802c02d5101c580042c030f8188d40d003092450391200c00e08035204a802d51418410345940c0c0c3e02e409464580350481c2074070000d8624162000e00e000d85240240c0c0c0105140783d1102014101c004c1d0b541d40c43c10704425011120047c140c0180e0100000300b0101c0e4002c4402425900070440c480c1c0300c86c05e8109041d42c81409100720700c81160003110104c014a00b4485031900540264005016403d13958421201d100c41580c610001440290003c0d02060309805580c009120034181198103685540d10380400f081e100c04041d501035900d08010031060300a911001c56103002e0788210381c5074900548400d075101810701070348001c65840e009464140c030782490304400b10395004d40b04441c192640d5030382c0c9080d050018000019401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 38034645 1250 38033395 38033399
    0x15040902070311011b14040f0501120b0a0303050714070b0301050d060209101110060602030904090317010609050a0504020301031505040f0f060603031103070f0210051209030301080705010215040b04020109 90
    0x7030034040d00304843c1760000500200b1080e55009484142c920002c0414520103210420600360421030b0340e402c981d02070030030341e0904202c11200d000511030318201ca940100314240200c1410b0703204010304070541c0301d040104890300500d09015039407021881125451241000140902e003030001080c03510603c1600c0160600450742d0014400741c50b0341101000081c03c20010100d444e10812045403040a510000c1051500704400251070703208142e1514040c50300d400b064020180b04507402410728403061031400c03e40d610390030300034000750283c81020b00c520b4030b03000042030701e14041c801c03a8101c0b50b1010035824024a04032100000d010010403d0b56405035104014010480025040320701e58444d4900296003800c0d880c0141140f096205200d280f40e1044c812a8002080c40087d40d100540403038025444801d00b04080311984688405507442d5034069050000e120b4002000d035068400400c2603e500350f407200700490ba6540070701c0c190142c0000800101d404036250541c00c0350098018035001c0507030340d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 38035895 1250 38034645 38034677
    0x518060a0e031020040e010302061303200102010e01020f16081303050a020102011a10120b0a08030c1c0801031106070803040b040b1005010207090b0604090e030403050c150409020703 80
    0x5091200e40d0340901d52282c0410f95040500c20091244086844d100d6003002e040c04002006410140002400342c000000c9041036807440000580c000e550010840c42841c4a030203184111030b46185001d40998209615807008100600036500e4144041030390a0030280407040c2080300d0360848401391090001004207420481c8449401c4010b140075200900d928801d0344002421510394001030071f040075038154000c82c65525000074500619052a000403040300c0590741c0801000040d443c2c961101412500203024070740070000d0048030304110151105d00e1141c03400214042d0725401c3e41400a02104d00500001c1e5094444040e441d00250139541004455550103000c0d40c010f035025591410882e0030030041190300781000b42d0106000b050009914900f50010303594101e940541c400090f250a13440b40d5680310407094600914040c0403e1101300e0f041043c0c66100c0d413003030100b560309008410350005541041400c0c4406416501421450545010079540c002c0d00311540c100e08000301085c44024403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 38037145 1250 38035895 38035903
    0xc080c070e0411040b06070b1e07020c120f0307080c0f03041212020f120717030106030c09170a02010c0203150a0606030b01180303030c02071a03060f010518060a0e03 73
    0x3070410341403024058142401d0480100e501c242d8043e02c1242031102400498031808180c038001c41d40a0303286038060b21070b2205a008050740018051b142280c8808102020390f00084a00d040c1e401074549401e1115800206600c0e15070701c121914941d4010031402c400903511038010194000d010003554400d00300c9060b00742c01c507031241d4400c00a190111104106006e141c0d0301800d2545000c3c00140641c00050a00d1500c52121009483e86080045420300a0019000300100e2074110503500030f69070340e110100900105401e200c140c0c00600c3c150380101301540101340886422100800074040415158011107600c007860030202d03018090318030750450280b07410303a02501410106034081605401d1100c0141102c4a088030a810017804448c0e0110b5200f41c4800d040a41e07426141c080b03030341e00c440b0100780d02c4c2c40e81c02c0d44910300700306421001e50428800d840155000300001c88440c0c0120710100c00441e480c0c0a201107290152210000c4a1000c0c907002d0010b00b1440c0381804c0405102c1d0a010010307041c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 38038395 1250 38037145 38037149
    0x191e080d0302130605180105090307090204031a090d0206040209190203090114060d020d06020a050f070c060201060605030903030a0e0f0d05040306050703060e071202070b1501080901020c0c010c080c07 88
    0x320b40c0110364151150580703620200980307140d140250a284000d85621240c4c1d2602c1c10450621100007246413954505000354005401800400d41d61290ba074500030745003030783d900741c00d40001c961580414408400807940032040300c4550b0040101d5180c0d0b4003042500080900030001d50800c0100300440e0b85d0503070001d188160418800044c4142491300d10700030345600146402d204420b080701400044e42c840029181c1150003840061b1901a4200c003030f2414800c01a1009030001c02040382c0c07003049101a459001d40300301e507000f8407403940d58032800c0e07843d808252040800b80d002400024142d15065100440103c101800c540c0103100d038080290500070782c2c3c0c84090000384009400e20610206c1d0040c10341020355480c013004541d203000c10003500020090304980401000f0700700d0803524481a01901e22082d0070001c440c1c514203100c940c400c051400c00407803038041810440025003125041c030030348980c480c5480103440c14204800044407028107120044500103c280108280c0150403c80703d00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 38039645 1250 38038395 38038397
    0x2040f0e070305010602030306010c03210501030804180207200a180c0801120f02090709030b0c070203010c0216060c050a0f0501050702060a0902030705010806040f110315191e080d 79
    0x20090a1009000b015168140c2000c419584200188205239a001c141d80c40c00c660185452000c00e0198880f1540307030202024a03d9405060030b00100901031818014000c80c0c3d00f00008041002c0b0280300c140580c060302d000a4404c40d40b0580350b040e031000c4c00500f101105001044110003c0d1941445c1030501400300c0c0004000b6603032001d07246a035800c660780a014000003071641c513400d5515941c0098020500100a003d544031001240415000c1c140c000e01030340d4000707a283c1d003501d050f54140c07225411402080c1d01ca0345c204244400614004141c90306200c000010140b41603003011030035180102801012140da101e10002203001c0780c401d140404082d4407030400400c2c1070401f20f9000b442c240001d03201c44030302071405a03880c0040e1380001d41001280c0302070070400341c1941c1300800200140b20041c000703000e00c0e05107450228420624401548514020b111003059000008c0902c00c000342a411007407985020710600788201c00c0e403e0a43c0d1218001c3c4038601ca655503d5405840c2400652076610b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 38040895 1250 38039645 38039669
    0x8091504110f04050103020303090613080118060b0d0209010905190510030302010605150703030507030e030705010905120f040902030606130f030209011715070e030d0e0a0b03070f0f0302040f 84
    0x250140c42d2449900d0031a0600b1101440340c1c0d415034001944900c42e2250452040d240010803011500b0020010b000410010000708618080300d40d4164070324050079003c4803210f1910b02c01052900e00041d009031802d80107040420b07640e09140c5054000d00015060002c1c1104076035259103e403103180100707442140039241a104041c6503150182c252002500407512074282108402109181103003940d402e2505484c000c90261100700e0298000e144a40000f003503400006186018042d05400c40c00c9401e128000311200091030741e500343c01d0303802400500d800b4160304100410030801c5a8014540007800104190b02d04035a400c0c3c005540780141d4844040030340c114208205601d001c4130028010204500342ca003442506248103912042090480c0c4041d02007640030611061064400540092000d405c90380e520035005400342c80d4050400b00603214000010010808401c003a05903802a0790540710700b840f290603480300303546a01d0b03038240346000c01d0390910001824403907a440507801000c14075110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 38042145 1250 38040895 38040923
    0x6110d1a130b0303070f0204091406040c050103060501020705040e1203010e090d0201330305030301140405130201080f041a040b01170114011502030f28020703030507020108091504 79
    0x8448500c06410208000500d00b0440000540780803084904079940101c00f52a01c91a500c0010001c1c44008800350806030390030940100e03450005000341c0a40e0141c040c41c0c0760300f0764503401142030720454000c0e41e0040e0000da01c10041e03400c164100756003609204c0161141c035420b152041019400176400094903540701d005014401c2c0040c00700b403440004510007400001d024030b5040540d05c51401700d0b0301940412181c00100078500500c40380c00ba640c0702c010b40790b0703c0d40d690360300e840280c01002d03000b4443c0d031904002c02e04c03210740e00c051b40403c1581a101d0301030541c2c5030000e84490241c0181f040d18140c4644852040500b00c0241e400e209511414155095505000d04282040c400b18080741644e0701d8034040f00301d030f00048011241160100c03000041c0e040c0d4000803c034194022000544480300d00451305603102c0d12040c00c12000840c280000994880e910041240e60b14110301c00035010410410028000d94480d100003907114014104880c2c0c4076401c1740000b5804c0c03100300d5054078128107103011 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 38043395 1250 38042145 38042149
    0x7050c090a06051804020d080c01020c0a030203030106030c0c0f11150c010c080a0b0901090f0209120615060f0313030504030f0302100b0f010806040f061511100e060406110d1a 77
    0x8011004c3c0020f0700c1d10b2106181690200350100501c0c903018280001c003184504100311309404541c082800207040d2000e6260303900e0080d40da900213014440c08a0308008003064542d1003510f03032800d401d401040002c2c041910351241c01c1242c040210322500422402d0340000d25a205000030243d00b2540c50000881c00d85408000b030603450301401c0140000d0074030070020402d50700c0520700382c1910450400081c604460301c0451000348120b1001527002480c0704c0d0b00e43c03e442008101c0c0c1d84100d03004012210401080002c008040c400c5090740b0304002c10600111385802140d0500503807181c440d04200e0324050305e81d114407851240c14602100181d1004411038480c0c4031a008002c0183c0f0291403000b080b035501800640500c10041c14a80104d42c0c941507100599079a400c084020101c104003009050384030381000301032004203008080c1a1003080c8003000303a20404c0c407a9000d4160301d41c010b06416101c070303500c150141800d41e20720840080b0a01258040c29000d101d000b070440462070404005484c0841 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 38044645 1250 38043395 38043409
    0x51201050d02100810090908071104020c0a0f02030a24062102010c150203090a06150509010b090d120f0e04020406090e0405011b0c0b090d050a030207050c090a0605 72
    0x3032030080900c0804000142c07940c2d501c400d507030380407030804d90070658450341c811060000541c0209121070030500700000b4412164010442c240c042c0ca2032180003510791003400140d11480c40c0221715a40f0940b2030340301188021844945407840203040d2501e5114580b12101d03207010a41c40700994000d850403271200b1110502c01c020003428081c001c0082c1511051204404655504002c0e0622010802d074208001c2e61050416405000b00c004548030308100c034400307584112407402140d0707281c5400010f07481210148011411920001e04648090703090070103c0003280c00040300190065030f008020030001e0031100d2a8000110250f50742038105001c0c0f9402001c464190b02854040d5204120a00c100d5501c00c41c1c0c1c40941d035964811207102e03103c61900c40d004186040340040c804842c0d000d0400f40307a80c00948001c403940101c0b0058034645a0842c40f43d12120700b80200804101c04010051030301d4045e4001c0d103003090041040d01c00710032451010a01c140011545403542941d112030600c01451300c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 38045895 1250 38044645 38044649
    0xa090e060d030906110102070c06090302010207141e040b0a0e0907050a0e0c0f0d0903020106051f08060126090307050106080601080a0206090402071a06030c040b01050910180303051201 81
    0xc0300d1548024003500d01410f883c52034000c01081060000e48a200711509404403183d182c1e02c0000e007410755580d82d4005007411000e0008074010b00540c0000035881c0d2108083e600b008100501243c040f208600b00494107001b1401d825802546402c1e00805540d55280c1c0c2000800c8030b0041c08240b4a00001401d04018840c0c105601c590b1050000b030000701c841400031544492280780d01d960784c5400c5034155040c2d00407140b032522030328200320301c2c0c404065064100408071032055900d01802a15100605011603d91004030009550780c4002036081d0310a00c4000c070309486103084001650b03408604d5202060040303a081400d60300004009080103024403138540240706031400350009504003045151500c10a00f0f002e489032102140c2c19000d55950750407580d1650f0f1141d00702070b506c1c1621350100342c0d0401c211082d42c400c0c049c0008403c7e0724101401a0540c0740816500d10785400c0e5a03508000440d02505848004c0046c4017114070700d0039103406c00303880245001c0d440300f86d1030b04034940c12501e01da00d0513 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 38047145 1250 38045895 38045899
    0x305010605070519020a050603010b090312091c030302040807080c030f0304030309060507051c0201050a140106051b031608031602071202010302031807060309021e090103020919020a090e06 83
    0x100704070b4010a10100b10180041e0300540c0d5420700998500000c0d8241001d900810790119000000060940c2144024483d1100503015900e403488481c18203a4a0700507001201c2c0c00044184c9801070310000751100b105080e11a0030010b081c6515101d00130718240b00c507000040710343e0044029807001d1404011040880c800d84005501c1c240c19507a00030304a803264400c0100380700f0702180f0001000810300c8000340100e603001e903e0311401714264000f0301908068032800001407401107808141051100c8142c180d80d0350341c41d024606040c41030b1800005074100c00700d1102c0e0009000607050302049454198086014005072a26400c00803011990310480742c2080081d54001360081000511800d4031100050f02405c005881c0d0351074070b80c0303108824804030541d00c1034090f0b41d41c0810110740650120912600940c1c940d50300300040b4003a440d031042c140c3c54003584004504010001450111426540b000418011109440f00d4800200603030308588403a4010030a4031509001c1c0104280b0182e07401401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 38048395 1250 38047145 38047147
    0xb0f04061205010518150405071706011e05160b010b04170a0203120a020c0a080d0f020f060a0b1305040807060e03070b0403030506032107030908060106120b0a05091302010305010605 80
    0x5031600054005e0540550402c002c00d0850000761004250324040900e43c002400902844c81c000da002490042c013507586000d1002200042801540708130601000801800761440074280751150a5980784c00c078000d0401c2c1070b04e2402c40c02d000983c4d125207c074000d004030300981741c0780c03820321400781414081415410000d9100100b5803025a6002902c121203c4401035402d40d92406804101d003400c841881a5410a4101000240300c141c005004400385001383d80e0340c442d010000804a07229007031f04080030507551143e4049000910b00d40d000851201009044600f02801881d20005076042140c1c281c2c0c211001050220600469008011101103400c0c06149824030716552107040700e60180015041640e40c0000a00da510f081244411144c001d0010701b60f489408468a8059845000200e00048480000094180d0005000c1d0305070380c1c9903115082135405006101c002440803429071a800078501e08000307056106c240b0083d0048414a640760b1030b015450002600740c0d80103912500c10840 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 38049645 1250 38048395 38048399
    0x5040c050f070219030b130201030b01020705010c0b0702070f080c010e0405090303040b04020402040515071101080112080c01140a0b01020f0c060f0c0106030501110706050601020d21060b0f0406120501 88
    0x40320000300d41205504030380444c90741909407a207654842c4181c0009040003014403d20034005107045480c0310b0b49200b40e81c24452002c0400049840d030010b841254042440104d0b624001982c04020340d81c000f08070710483d44030301d554840e10190302c0c1042c3e001d0a42500704001094483d6403000418480600c161414005402d105680300da403448000c0000e021011040c0200c0c04540c2c9130340454008003002002c0252400c04010040c205500040c000c442040800c40306201950082001c0c5040703e1250303030201c134504c03200c0e100d54032180d000c01102140c0755650007040148074801d402150003103c0a90000a0500f03640c4000391801c1d5040e410b01c0c40c2940040760031070496545004440f03038404035001b103545078a6000c1c02c490140540c3c2c0c0000b8869424110b4100340742103420068008203004031828002508c5400041e0b80b80c0c1070300c818000000b21703c56061301d2482c03075105000d8906180200d0000ba415955050808280c000f8262a4980e0100003070810003540c0c410601d14070894000c42c1040194 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 38050895 1250 38049645 38049667
    0xc08010c08070503040f020901091e090209010509070909140405100614040903090b0301030b0f10030b04110f0a0b0c0106050604050607020909030d1107170a0207030b280605040c05 79
    0x140050a40c000c0003c004000380801c603103003454410a960240000070596110340060024001c2c0c845d00d1808150060040c4504420a019603208550041c2249100c0e908240130b006000030004c0440041c8a40350750002000c440300e1007000350007102c501d440c03480e60620b450401d0400740f92203d0b00e0b45c481c1c105503090141c0d83c2440b603110509074003214001988081803805803034500241e0703c0701c0c4ea0307100040000000d002039020114131031341941d4559940740d50751240d8650044030502025012180380000640020011000b210700d400c0002c2544800d00d0080b40000da00840c15005941c100d803001c14a904440c00074002c28000e0002241e00a041500740300100340309008906000c2d00c6001c540001c03580c50300060044540051000e0014021084184010001503024044c02c90b1a070304a80081d005007141c00f42500c51100c0d095000e04442c80c69604c2d84006410050245108045c2c3d102c2c0d400340f80f81083c40040302060203c4030101e00581b500d01000700311031044452806201341003000d16030403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 38052145 1250 38050895 38050907
    0x114210a23070b0a030906050c040302010e01080106080a020706061203020c01030606020a020112021e07060c080105040203010e0a0e030408030a030608070b0f030414010f020d020702101805040216020405130c08010c 94
    0x2c0e640da044426144d440a04084026081c0a000074019600d0101400000200c040040095074000e0302d401540c4d0550000450700410309100d55000106803001080d113484064008000840c001d84000ca00903448008442d83c140c0001012405607010b481400c1c0b0958060080340c0081080c0e00160078aa5a1600083c00c40d4100c0d00c54400380d581c0c0080c0e2004407007001070902000c049110305103a103070481403030300d40000c1101e184a10045411100005101c2c9401c0c001c0381c1c161f4000100c0240c2c0b548032200c501d00680645405032034980001e200105005004102a080c03620700c6031b030045101490103c00c5070510500b50851008400c080080d050308041c200101d07900310794051040080d030204410b00a00500300c0030985480a80009210b40c1400c4c46a00500040382c02100d009626201d84102a00e068902d0389281c9140a1803a03420007143c90a94082d029980540548645c941499800038003159030071100b03080d07403148600ca20b200744000703400490081d007074241c000c0009050541000e801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 38053395 1250 38052145 38052149
    0x41401080a0516110a0605040b07080907210c150306050f240d150f06020c01020105090d0507050a0804090207051b0105030f04050f06010603050603010e01060e0114210a2307 76
    0x10b102d5030460080c0904010451050183d4006c802001903081520f4111440041501c5910000d101c0c1c13004560710b60000724601048402d5913200c81501d44410602c0c10001d0300c4001c00341ca040001d0300c00000c24403240c0d00c41c0e1030300d042d071a540010b4607420001000a84030a0102c40f901840707502c01c400c1c816407a503402e04020258400841c6480703460840048000d41064600210601d00d010000100c01c0c88420039002070322120b80a94011128940049003203900444150006032f000b017140390390071030148004120326401a01601c40703503c0103032a0700d9072036480340d484040d90780e60020300c0f03c080c44014059650800000c4c05c400060f200d00c03000007045404003074a20148940000d0110302002010402e076840c40c06c0440a0318150760390303490051700504c0f00f281c11900070b503301102803123401c0c41031103540d040c0c4404081c01c2c240c46e42040d1101c10710040d18604e46412003420214614004508038268400e0480403000b4000ea01da686000c00c144c0c84480310040503280714103000441c0d41400315884003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 38054645 1250 38053395 38053397
    0x30606020a0809060f04090e0102090909010525030e07030c08070b120114040222060206010f270b0a0f05040606050304020d1403090a0e1008060c0412020102030708041401080a0516 79
    0x5100c8901205d580079610590344541c06551070009100d41782081034000d885525400c44020304540d60300c04141303003614001c40300c20088012281520088544581440007440401e240c00140030300d80c2c1448a1414000350019107441c0341b038100801c6082030410450010b0300c000401e041c10911404800070b08520706014500150f00985596240c039107940d03050301c0e0b410311484403102e81c02d1035030448008503803a94010a0b005003e01701c00401c1c034600158421080312204803400f10031001e4541d05900b1918440741e50010381e80c50703900341706866554141344009408001640035440d8508002c01013150025400903081c000c0500030000940e443d4826140e205401c880b00d050040d0f01821010305603c00c02011a92000c0c0982020a140c0c2440e0034840c4600c90b00070400f04184e031216040795681100f104c44116010080100b0321496440c60030140e8214411300481f42014059a0754400c160440d4101140e0754003940307100c3c2c0f125079101c0035564100310840130400c01410306130516012410401e15102c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 38055895 1250 38054645 38054647
    0x90e0702010b0d110301090606030303050a060b0306010c02060304020415030305030a0e060c0d0e0c0a0f0503100902280803040e070806040b030c0d08070203060c0c0d0203041d06040905010e010c030606020a080906 93
    0x211302e80d1000c0d00000311301c60b0b00c0740b17081015580364036014004210507902284841d140c07003404180041d8142c100c80c080c08058658800004565003000260380c00240b0407a0001e40313841c001d0503c54100c40702000075502c640c0b5401d4591400e01c1c0e82c07a04032103141d140307118154000e0f03080c0311400d81130f00c0860340020706005000c250f00a164006520f0215441c40c50751b003045070307003a00065051100032480c003500c9080b0241d808003074140d814042a14410000694000986103400390031302500c81a4140b000112010620b482e5a00e0700c50301d04541055100b156680440400c11004a5010701c00d258440310460341000700c448030402280d5541c02c00c074602030041481c1d038a84000d002c1202c003965400d40e40102100c1007460b00341030a03803140c0c020340745441180c40f84034104a1000d00100941d02910410322a81480d00c42ca04510000c015014141640081e03680f040100424030038080c050000e8040000440d48251012000b8203c6416a00c00750131900102140740004900404a4082000c01c41d140c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 38057145 1250 38055895 38055923
    0x70201022101030b060d0311070602070f060c081206010c12020604061d1e030d150602010c11030702041107060c03050603071d010506030601090806090606211c0909060303090e0702010b0d 82
    0x142c030b20803151801c0001d58401e2700f000241e180c0d4000749071710948071010701c07807001d05540d150244c88824600000030700c1341c48103110303010b041040d90022aa002c04140341c01c2000c152251254100307103220340b0b01100180c001c8010032003400340c1d42c02080d40c00780d610a4034900780d900180380715031078100c00c04052402c0c076010743c806a907101007002681c0c2a105214130070020302451041031b690178026032040102550a00b01a41080c50050b000c0c0c0c00d03180041405145040c0b26035017000000c0c107582152029101d824042c010202d41c00f441a400c4610b8070b1b8800003943d043c441d040501d0314074030b940088040100c1a140e07070000d0714001d60590444406550007912910303a0300058515928581000c0c10318071504007084140c283c002aa40d004260a98400706403400340c00750040041524400c109481c0c0c03100c080c10344507814080f07940303004104d21b00d401405181c480311010242c80e1258420f0300092030254051044100400c00c150b001003043c0003c001d050001404140122030380c60028104040326498 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 38058395 1250 38057145 38057147
    0x70c0803070f0e060a030e07050303030402031b03100504050f10020f04030f110d030f1e0903030807030603020303130306050a02190807090f0f1401170c07020d02040203070201022101030b060d03 85
    0xa02c81c10040092089031900c5c1542c80c010020900043c00f51800d21411500003034905012003124011900a0003804250381141011040398466400706601071242c3e1081d9401d800c020304c10749002d28443e070050000440d00440817490013a1320b4102c014502d10411040387c5403c030b034008850071070360f203c0c49058070040a410024008586d10030781c590886200c460220804d60b001659507034564880c0c9444444c014480d41d90b2510780100c10350031001c103a1821341440881d0142d42600d61124992501003607464482e40482d0940e0003440004066000b05d010070f00170032105009642d07112000345800c6040503031203c1625280300550802c0ca05000c401008580110300c105408000b81c80900b29801d80503a40f2582c1d500420340d60700c51085030003550883c8244a43c0304c0d5183e84000a0200c005441c60740340d03c130a00381d60398445c0b40b0490380304170700302d1981006071218009584510b41c507800040e1070b00d01005505161000302e007001c02e001690500140001081c3e1582c240d00090107940180c4080b40611f8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 38059645 1250 38058395 38058407
    0x9090c05040b1207021501120b0919060b040612020603060609120616090603140718030c0b0409050c0301060813150e060103170909010932090105070c0803070f 70
    0x2c5035424220010b561448a00302d011414000c21480e802c841d203503800000e4034400128213029042e8441426030110002c20720107102c440c0c1080782203041d58909014403082c0c1b01901c84400c011a42c03907841e0150001c8a01d06841040000d007000c1c2d5015041c120a82e0010389644030041140340300389004100c4d01c4868a07a44846403000d0b0030917003103a415092217841103038a000015aa1000034881c42e00c00b0910380d01c42c2c060882e44a0a40030701000988690f00103544070f0700300003012012002e040c00d0000200300c2400180000b40369024100c2d80d41d600340300210040d250300402c008000b260401c0100841517110a030198847c002c2c50300142024080e1030078502c100c0b4120309610400c0d041c1416045122404201241201c2c4100d0840004181e4151410010b0181e03948080d40302e0407080c010403e00035190040a4007021505480c0e004030030040ca0201882204924142e21681803801c05c10700802c24860542c00400c1810054a200810307940d90b255407100814207004c00c46007106915416008013 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 38060895 1250 38059645 38059649
    0xf091a070b040b0103060b040b0f01110309030114010e06180103080703050712050306011706010215060409080a0c0312060e0103020f0d06050108030909010e0405031911030d0204050f01090609090c0504 88
    0x51101c1c4058201410301e0880b0b94002c0c0000d40d1024034180b07502402d46020b00c2000030100e00501001e00800c000302c0195080609840c12403e280010083e03080310350340a2141c120070010329200c03070023a0750401140b500c0f130780070040c420360080d2039105181c1a41d0030450801c9044a502003a07542e0340740900d180840c0e8600032140000c24a280250a50b45e140350804055807060100303030398058000d203052104c4c828680041d070340c40340076803c0f2344c3c08a404616400e024139844500a40041000c104650306c0500c40c0e4031803082a0300244100b0203060030583c1c001ca807070204614086040c09020700b000441251031006100c000c0c03090b07410700301e01d0000361070b5048001e00131904207000308000d6942c1d0b000591240d10222200e88241001c0b0000f003604180c1451050042d50032500540c00c0080007440b0361000c0e4400c4245c4000d00052442800781c00030100010304441b021440c000da1968604824403440011481d4194103020301d0150911500303902c6040042281ca0103880404c00d210396802c150f076580f00f56 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 38062145 1250 38060895 38060903
    0x31b072105010506010306030c090902041b031407030212010501080702150c1e030108030403081605060106091706061e0406030219030209060a08032a0604050a05060105010f091a07 79
    0x800d40e0844103240003010000c03180c0588024803666541c0001141100c05600008180ca58040002d120b142203c8d48003d188074806800091006401654071401614014014000a4407654143d4941c02c421149075006901c0d41425410310201000f4198041700500490341040017420000d2100340c401c205514022040c47ca000d0010b061020700c0307141c2c552040c407070151001d00c08130401d00c00ca202d401c1100c0c100ca0151000e0350030942590f44544031944004a52420908041d01c0342c40801c0d02401018006d007860340398140030926203011b0749000800080c011126401ca6020070080c3d8032055511441c65035042901c00d610321044000800420851700060b400c06020141c0420607165a09a58242c0703008650790042c44c0d0b582410800303034804a02901001d6001840300f06100104515051504000b1401e0401c007460800035103443c121080320151a15844600c042080c407005101a40c003510f02868080003182003d200a80082d03800e209414050318101024940446c04c541030b24541540 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 38063395 1250 38062145 38062169
    0xc030c06020c060109060b04120f020f03030301080601080d030203061f2c0a140303070803101a070c1401090b0d0605040501080307110103090b0604050402010e090901090b0f040302031b07 82
    0x100c4003500f030b40c0d039109000f062601d0b8a04440481e43c540c0380f034241e50482c1d400c4030034418004520750303800d600132404150498002c044001c0c1c41c903c540d02403010311301038030300c800082509624103401145401c580c3c0994030300f49071041050040c19212000f40880b20b40704400c042e07400400d843c20459450844d0700404a182c0b05130002c40520151140344c14410f9001210799200e0b40307403a801c0080d04000b80c140d005d64164001c00040e4000f903600001b8640c4807100310034402c9211b41d1020020070542c880810760080b60320015001003000320080404028008040040102d49d10110010b445500e02d40030f0944085004140d80c4990170301500054084d180142c801d00444d65100b4446903660032044044030140c49041c0f880055512174840c500c00c0a8000c064100350340c86a034240300041070050410b87c10810000a0704483d80c5803118a180100008400058020355904041c003012101424200e0324603442e01c244408070740c0c00800c0d07400c0713078208000c0055085d45607608907181c043d00d40d0061301c1c9185 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 38064645 1250 38063395 38063407
    0xa0e06030703060815013002040203101d070516020301180c030b160203030a02090d051e100203130602090a0f060201020406030e01021903020d14040605060a080607050a0c030c0602 79
    0x6410341041c4201e4800004540a01c4030190418038500004d000b03142031800d0440b1f00504e00d0048091030800d00d4499900c0b6003010110f500842c0c10b0360303c11030b41c803201032121070000c204810040d09580c00b040c12452241c68039040c10107004246103cac007a900745c070039201c910f035000555070203502603404201c0140044014030280c0c40c0408024400b440140da10300c0000002884400b100030b0080001142d5902462455a45a070070350029003000e6000390b007082d4903108031000920704101540c52003240c40304640d0b40707000b1510724034a00050305606044650051051203a0340d40350084014101d5400400941c40d41d944401113010707800355a109107581403258600040310f64041d0300030300698020741d42c24001521709a50440c03d030b100341e00d01c03c0d1000003c44000c40716907120740e000e07101d40c0c0902040440c1280c514103040072070f00825901030311000d603100c050010520384550050b00402d403050103000e0381c0c505039001034100d024003040035080c00303c0c0ca41400304052040800203500b41c1d01120854441c8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 38065895 1250 38064645 38064647
    0x30f050906130915270603080c0109051b09190e15070210050603030706051005060c010b030c0306010b030103080307090b07061d0303090d03020c07050d0f030e0105160201050a0e060307 81
    0x80c2c644240700c1038918140c0080d200050106680c0142d0b850501c0020b07441c80c109541010103a003103184904c81e160386680100000720300500500744616244008558420503080850130044420504000d46040ca00c0b402c1607510342c41c040070b03802006c1c9010808024944103484003c0d007200c0901d004203001e103c001507420103150903280d014030343c6036003103d00d004020207480c021144107488481d4594420f0006000080494108170b030b1100c403907030b41c0788400d55844010440541180f030031840c0382d9440d508030001c1410100300f02251070a084000b000c0b103501d0000302500310b22040c00302421504000001402160203180040010141169001d41c1c0301400d09041006200580140d441d180a0b44502e481041000090300d000700300c0000580b030400181c0000750021f520001d00d211990040c05400126684e410380305241c428010b8201c0ca4804101c2d117030082c85240008a03480c18840241b09085507070390300e03600b65402140e0a0a195551f17900000c001d907a481c4d080700d0000c4e4000000010007800d5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 38067145 1250 38065895 38065927
    0x30c0a09080d090905070306030611040302031002031b0c010b061206030615010f050705010e06010803030405070b070c0b071b0306020a0224061909050c0a0f0e01020a030f050906 78
    0x10122903a24810115164201d407516108204680e400103003404805002001455120640000c25401c00150266491f501c03481903641c20200400e01c1e03c030200c0d0400660805201c030046001301042c0031440d601e410302c01c005007100b50400c40e920815000c9146564501e0951001d000081c1c018003140d00e4a000b450003072085001203401900078001c0303801060040e204d00100620a44058440b4000902e8034041181c040c1c00040c0155142d64070f851001d001c00300b091003491f000c2c003011030141da601d241c5402c01c0c0b850310540ba844440d08040c100300030408524420760400650710404441c569481140c1400700c1214075082d480c400d4080380a50000c108501c5500800030b2000b65020f56280d107406a13a95165580d4a10f01c26143c4090313000010005d103032611036000300343d03103c1c0380308030081d6207a0001c20b0131034204658002c45950300103a005a855003001c0701c45c1c0c0b510002d2400c5a1107100ea800002c0d00c0d00754003440102403140480d203e00030a40220140e03803030144094034554486610079903042d50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 38068395 1250 38067145 38067157
    0x220506010e04020306030a020603151c030923040c050f0309070305010605060a14030405010e0d050306010216060f030c091203030203010504050a050f010608041a012607260102040b030c 81
    0x100d0801c0a074039026050900a40784103070802400f60592428a8007442507692004107100b15036844400d080c002965540044a030154080c4803103081d10000b8030b8040c3c40241d0b250040c203180000070b00d49a80217150030841540e030140c1582c001c6541009214141c5481c047c101555a0300c2c0008010404074990018405c01120f00a50003407160f940d0b2041401070300d106000c2d0080014888a650351100c5c0d1050004580051088000103080180003606a0801c0000d1402c1800500000306215041d81d040041c8a111040000816196458400054101030031018460b090584800280e44405e000d410284024014110010348410240c070340200298024001c0c41d105618010100781814102d00c1040d10a403d42c5030001050307403c0a406944032800240212134034101007a084090440e0441c1c00c034003e140c50000b518031070220101180310b102160034002c001e13900070b0380204050300c04403d44800071084c40c1d2159001e5601800402e01901c144d411503c00c0020010a01890000440003408 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 38069645 1250 38068395 38068397
    0x10b0c01060f140607050c0414041208010b0306010e0103110d09210203040e0a06030204020f040e07030506030309100507020307030c0614040e0103060b040902120607320922050601 79
    0x246034031548240b03201c14842c0248511a804002d00710b8490600d14000c00741c2d1400745041b103802404610004054803010313410030800306404d2090108011030400442c41400490074004490741c10011342c244030703000082c030301410001d0746000f440380d99002e1392041d640780400c485650380d281a0a05070f44013806505c5801c40d9440881e18442c503249000050b64600204a0740c0078520b402e140c881041c0d1526405440c1c000f08999076100000140e546100034805541d074080031a484615061203d1800e4000400140605040030200070b01070f034000c800c032440401f0444e401040142da01c54203da990091100c02500740c0711343d01001c001e101075034040008031000d5503183c4020300250324000c08240030303510030b0345c2e10317200c1c00d600600000d0b0103904121140b00c8050400181c044603a0002032030b440c0082c0d05940281c01c8482889181a803000c503403004c50910108980050140411020a01c00200081005603401244500c610f40c0d440d80c0080d04500e5213081d1100c41c03415a1501d000404081ea9124 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 38070895 1250 38069645 38069651
    0x18020405013005030712090915030209160806100e091e010506120703050604020702030a030e1509030303010302061605060103030e030610081009020118030318080304080304060c0309030b010b0c01 86
    0x385004080301c071072082503004020318206021686d41c40b01d05a403950004040c404200c0e170205440d6a2881021002440e80450526107032035030041c40031036403001c0c00c1e03030940307800c0c1c070400c00802038001c0480f90b00803200303444030403d0040c078010455907010102c3c48154803c440400348030004000c070000b107121900303503a201039039a6a03d01c10088030380b01708160546015052800600f1950003030348100d038010b102801c0075140c00d2082d4000ba0038843e0400d0102c0100e6039007042066a41001c41c0e81c5001c91100c100d400303142006440c0065a2400140300091003020300040001005248017052013445a10904480465849203000340959009102c6540031b44110781c00258040045038054040301d0041d0702411043c2c00011051024000c140c2c81a818401c520085003038081000001c20002c500035603806400385411b805580e64100c0755030007160980d1090005104000011003100e00300e404900703203100c040341145416a0010556031015100e4149c0320000104151020000c020003800b0700020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 38072145 1250 38070895 38070959
    0x8060a05060d03030b03070f030308041a070c060e030409020c0609060606070209070c050c0a091409012a120c030c0806090403020c0d020102030408010f0912021207061802040501 78
    0x80000c6035021203600354050365069032400424000c0d0310500000c000501552a829100c5001210481c0d40358030481c0060081ca080106218144000aa044076041074284440c100800c0c020001c02e41ca0001415803541d0355002c0c0c40c280d40270400c1307400a1131800e4040d52103107255040242ca820084802062707501848000403007914045c0c0490780040d1340149038034180d8517048421075103494500002c032020301c20900c1600c1140c4d00c0420100040088030720105558220114990414030040c01c1074100f40c2c1000d9071168015030000006954148010701e050184818900c11980401401c3c0143ea1843c07918000d0103200d507240d0403030312041010f03459642c281e071180d33018801458011203014005030400d400c040d5580c90802142c0ca0403500510480f41000c1d01c5040301ca084416904420042543d942c2840003000304560090f0206e08080c0042d040310100c81704040071a1090b06c80080401c0e9880e0f1880408501202c0766400d0039030080c01c2000251303107800302d4160740d000700201c0800f000031000308 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 38073395 1250 38072145 38072161
    0x912070302180415050405030702090f07090501140316050706020d0f0501061b140c0603010e041106030f01061407141614060714030403050f0a0309090507021b0103240806 75
    0x38080c1c4d50059800740c0840011190720000c007405003046607540810400f40001d0303521225050300503069411200741c40c2c104140083d26968541e071146061260340e42e40d400d049045002541d6124151084204502c986118200c44034816404c0082100340302003554800c4052031b5000c4022071103451410032135642c0383c800660740b010a640001e01061000560b080c00601841d400d080d0011000044416103400c0b807000034a144c01c242c100c04c250100001c104001c2c0070240000941400055588900d07509290740d403200c010105014030020321000858403152400c54004454080e40c200350380746443c1100008243c1c41d61811121610601d00e100c0300800ca803041c1c200010705083c1c000f4105480d04240f0341e101342684449010b81c41142c0806c1c000080450824015440e41800b82c0c00a481c2903d16450041c0c403055040c2c02c00810980360a0030010300640000d08148000d4034422800e443c80c2c0154012030181210120980c042079030242e04a220a0246807203000341c0d9440c8007684e80300d65503401d07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 38074645 1250 38073395 38073439
    0x110a030203030a0309020625020a050f0a03030f050d02030103110f040608030904050a06030609030207080607080709050f040f0606021e03031b030405070b16020306070806030705060f0912070302 85
    0x40654542c20401550b01102e000c5d5120075000780c4080c012034204607680741000140d44840304410803000900041c6411480c09004040c040e050031070320201d1000d0590041020428540002001e00c1800402c08a940b0301074030550f0300710220a202550741c0d41e141d00e801c08240d0341049595010b512070b0b055520a529140c082c00c019205c583c80198117001903142007002400b40a003810f00c0003652040701101141041c0501c40899000c0d4008002d03882ca0b1449041c64a000100000c00300296042070140c0e0940c4004194110b4070115040a12252890f000500901c0c064407000b500620348400080c01540116260011159803426156000340131174115032244011245441c41140031002c400060f20800080d6411500a5040b151481e8454050f4105540602d15601d04100c8000800c0c0841c5001c010b80c030f80c0700101b498400c032142020400700e0f50700c10283c040d0a100d0a804215079014a0514054445980009240c5420110b4070491551900c01c0c5000c140e00501892803201554641e83c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 38075895 1250 38074645 38074649
    0x16060203030c0a0908070e01050109120b04080304060209100905010e0405100b030403170108280506010b0a02160b030a140c07080703030902180f01080106081c020f1504110a 76
    0x24014614680d07854100d00d0007544110042ca06009640e00003080082c0304000004c003406002d010242c0b5941031800140000c602c0d40e004500382c0008007a19030014003940d40c506c2d0407a40c0281c1641d02e03074933180ba0000186c0100c40000c0c1d040031004c8600c03074550b03921031106c0302160400e0700c1d01c0b107034017003014184410795900315186400da0108450811409032140f000b594401d01078607103103085031245241a29800d00030f9100c2409070b4002c01c3c42c40346406030100c4209440500c10703122040c4c080c1a0342d546441d44030500c50ba02047d0400300b50401e01900034030103519002d00380c80a0f04000ea8480864860541058421041c814540510300300f107070300b80d210171a014120700e54007141044003a50364483d140d40544021010513071621968401a141c8100c03000501c111240c00c000185001703540e5003000001688006070a82c1041e904001e0074102040032018108003085004110b400650182d00c0c00b4840c1d0707a006258030482c0749902a212200c01003502440c031503200740d281d1508001c01c106c4050018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 38077145 1250 38075895 38075897
    0x30c06010302090414030703030b0a0605071101081906030309081002160b040326160207050109060c0f0b07020313060f050d0c0908010507020102040503070b180d0305070501021801021606 82
    0x2090040c8007500c3c0450384030f940039104003007003281c0c8040e0100d8030342940c21440c8100c2c00302e07840d504000458a0041080000b030324840c504982008865206c4403a203000b06107007181407101c4c0c500825440301c1121a00301001d00407040a010050303492030000d08010040c45850113078044c0c5103061440741e9142c0200e94002c02c96005011405a160300c80c0303112144060300840c01d10044280d940003801c2c4800040c5100d00b0203c400d11141c1c42c4c800388040b11034a20012490071034109400a10581c2e030032a0015040d20114940142103000a28000917183c241c10800b916410203281049241603001009002d502c480000c11011180d5510045e22448001c0342140301040b01444072900d00b071003a40c0010b41320702441c50035207590396403200400e00f1142c00352622801030f500050300340445d040030031006000300050146d1a10f00089418844100400803100d9072142c041c3c4c07407060b0145071040301614400b1b60048000c41d0742e07101070b000850240c1240620f0798090301a1030f4480f4030f44008880a40101c80f15 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 38078395 1250 38077145 38077153
    0x603010b04030803151801030b06030106210c05090103050a020a090207020108041203090f050303010f080606060316090b1309050a180305030a06080601090501081509030a0503040201030b1c06050603030c 89
    0x155603802c04103400003030405201004a42c95028940d0b1001861131207100d100c20b1b13107402941141444071b0181401441140640c1c1800e6041210113203400d89440841c001c42c509440d08a01442e11080003482c55010035481103c080020062100201c0c44881c1c0510859445100d942d031528010268010340c48040c4c0864040800180400e802e5842001760380360600d000135640b8044d64a0380d4003030b4100e4805660316031010005000d660345c0a44258050094440103220526181c0c00007203182c8002040d54118030991082e540c0c229026841c2031000c0c181000e101c41d16010140c0d501080d00020707115000700301d418a000324108080900c641c8031050b80d1103000810780b4500340c030103503913550001c1c26020159590780c500080c14401072000c0740c0a000052800302d0594504103400380340502c650b048900044400050113620f0034008103ca0b10411030341000341c0c0365915800180c0091000121490b041030051580c41545084866100720b441d200b8481084240c0701c000074103580b0300490081d007100340c2c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 38079645 1250 38078395 38078399
    0xc010c031d0c0609060705030a030c030b01031503080705030c0d030c0e09041101031e020403150606020d021903170106020a02010201060608070c08070809061b01050114100f090906080307050601050603010b04 91
    0x8210f0010000400e02600c8503290140e80e907111031560740580b450303230000703075440d00360640c0d1aa060248a111035000d180c02d00c2141500c451401030114903110040c59020f0010704c010170010244160381008000740700b9a24050650540600a8429224aa40003501410122541e46004000a402103402404c021014040380c4010b40040206d1038030b9107003100884007826a00314040c001071024610a4a8034480366011101c1a000d80354560400d601355013094800011156002440e4140600c005e0b003000083c508506047e5408803119000c0b4070252042c0c0c00102c0c4c042c3e00000d24101e50780c0300783e008000c4580c0d07528046a000c00140e45040c00641d50800a0002c216140301914805029400c40c0e450030a0104c00201e1541c400c1031034410040d2441c030f400501030300070300c90709004052400d00e180038510300784006035240e180c03007040380148280d8408580049100350885005070001220401c0085d0700c445075540c0da0b0300410011070b01032190b6000481c2a062540030b036412610f9030705415090034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 38080895 1250 38079645 38079649
    0x10816140108060109030b010602010b01030e0102040501050f07030c050a080a110d08061212070c032d060c11060f2403030f0a0c0618060f02030907051012020c010c031d0c 75
    0x8406401541000b840c5c41000c400728014500c258000e1400e5000051050f1503d0000750996a8030102ea040b5648144400c200780c2c0d800400311003040400004440e55030308549401e6880482001d005056403050390580010061010010200340c0c01a4840300d41030459003204a5843c036134681c08100040c46040440e00a08100005c2c003402d01549050328080c0d0102c050294454011800907a0b44e00c0082c0810424401c441010602c040600810b540c5050180d0682994000900d000148042c1c1c0d03030015400e055104030f01c10609030103600b00791403803030400c01a0700d9041042990703002c4104980b1100c281c6603001243c240101c90310301602440c1008814112484140c0010400703005128035080d620001450030f22440d414804060f00000c107014260070f14104070365036a50a05052841001030004442c800202c8034100d40e0102c40c02c0c00703103100b00f0908aa40400441c081c00c0c4450010581c0400e00406412090101c101ea035000c10940f04c1c45a4503540c4c0b12400c00d18030505801c0703011402614 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 38082145 1250 38080895 38080907
    0x601080903030411130609111806030106171302030f01050f060102010b01080105040203040804050d060e0c010311090f13020a020106051009030317070e060708090f0402030114010c110a0e0108161401 87
    0x21744100c160004a240d0b079807210106840b055004040710f03c10020b8064240a80181d04101004007540c03207034119814444d010301004d0400c1001d00044044a0005101104002c104a2869800b80a0f20800c03640a840300f40a41000e132104104100040300023a500e510512a100c1007140582d90280180d1070001031000030751000d0705c2030710480c0c000c00010070161601518268541c0c860a8002803a1a1a00c1c03076500b800a0a0740241c101030900403040200d070803203001d0b00c40a24085aa040c1408800800298070740c81c2d00b40034060403800481e030b03050b1098040d440038040311016035404031407210303a460880318490780c1e000c010041150110781c083d102030600390180e80013140b030030003110343c81c0c5030000202d03c1d810071141112030090000c0d9040b49414618244000c003c0c0035281903003154144100c40d007002c450521264100402c0d045104140085201e0203080d6000240800354032503110159154000e00074015294248200e0302c21000800481c81c05804407220820000741461303000e0011204 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 38083395 1250 38082145 38082169
    0x60501090c0215150d0b042622080d0309020f030d020604032303040f060c08091b030c13090309140609010807051209031803030403150216050f01050601080903030411 73
    0xd29003c100142d69499107001408018058000300380c151600e0300d04860140740541e0100300c91601c2c007244455280c005009e64031050305041507466070104500740f502032880250300000581c4980365071040310700e41540c03001042c43d00950300c40c20005620000c1c55912000c113040380006034031450005000c42d200d0380c082c50442600e40481c50811009000c0c200080d042600d080c0c440b0394030100c5110401030940300b000b186400714148078581d444c1412910351107420a1008440390186100014841c1c1d8081c42010000c1900410312b440766050114400c00038100048101c0101d4648000030920710b50001e43c007038441c0001004240b40562a400446800c1d00180c203070b90601a0500645041031030b04013690780b041c075059000350303140e0360350f0340c114003003420129142402504204801e00c00b0504545180720301400689026a44070440d500c0191130b0f400d9440302502c1800f070040d0070700800006400807800b60400b41e03107424064075450031321501c070303c0107650040078596102200b04040c1440c642c0150 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 38084645 1250 38083395 38083411
    0x9010302040902030708010c03021b0604020a0302010f11030309030a030606090b16060b04140603010b0105040b030f13050d090303080105270402060906040305010506100302040806180c040f09060501090c0215 91
    0x11031700340e40c0c040c034a080d205071000d1840801c1e000b0545000720b0b1404d00701b2000500d030050081609042c640c022951401c024000681003203c52800c0c0d02405014a2190076000400000c590740e80c9017a50a19450742c10004031f03180040c1c148180007074010301c100c082d40155195020210b1030301120000c1c66500c0804000f04072207143e1a1071100c01143c0d41c0d40b11b803c00c41c50002d146500b951515000701400c555802424a06024050100b400032050710740c25680c2c0b21522201c4107050b51902414403082840d0030700001c01501c1400400c000c180d03404074807582168400e84030700302d1a07604c0f0401c01041062016030b45041080c0490b40900508940d980590000c3c0040c01c61450008100041591a4040c0e0400e44d0745d40e460b0070911910f41049050380c00b131402646030850401d4100354003e902c1e00e4024110000c1503480540862103047c0c140881c4601d03d000138000c0046043e5100d41001410001b0020380c1c0035890300c0c0000410a6030307800785802090199024100c1040380c0c0e60030554070040030345681 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 38085895 1250 38084645 38084653
    0x307120b0d020402030a050609010806160302030405071205030d060e011404020319061715090c0909031201060305060f03010e030a050d020f0406091707050a0e060d0b07090513020304020901030204090203 89
    0x50050b0302c07184011802503071000e401287e14988001808008001a031007004658000810841c0081d03040b81c04104003041494003681d00d48030b90401078907100ca207400c0400025040e070407100410a000005141e6248162414040c26035201081b4124820900c11000c41c6500440800c0c41850198011940101e91075604c0212115840c2410b04541c81030700844c0351440c0030960103820b40420000030486030aa004829890710740020b500340c4074400e0510707884c094407062012410148090040c0c69184000d0b440038000c41d07035a4003004020b0401511038500840032656075510904042c080e14003503000c2e14004529102030180d04894540c4440020315800342e0a000440d8130307410301e00c003c0000308030903544c05094a0422500c0450000041c1940c0802c2d40140300411141d00c680d80044201c5030500c198031119900d00c8041142400f00301d0f00200b80d2190344040004107900700c045482691400d50b561000941a444044100c0c0700684010f9800000500100300600e4150054406c003440079080da = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 38087145 1250 38085895 38085919
    0x10302062206030f0e0303040c0e06130507030203040b1324060306060315050106050c07060804020d050a0b040312140a090206040f0b12061c200a0605041a0307120b 72
    0x454040d02a400c0b00c0c0c00240c803501400081c811a0040690000d04240518510f042603540c913070b1113080500c00c040d1140e03202000900c4554400689541d50854800c0501a41c07810490043c0250300858089415170040b070081110b400329421400510b550040245201d48010b002101d100e0280042c038582d01c0e900d942c0040006141c5004070790055210b908003044c03003030b06861400c0171758005811031000c010080c001da00e201a40003485c50100c07207003420458142e80740d500100e600035001d036030003920510aa4064100b0400c108618070300c56402607540480140c005220082500e0f02d981221103555815070100c0c000c515980d0040e0540392000b4000e80c0f400365520f004000041055100004e4170700045071101c403030200c0703403c2d1540c8400201c40c0741d9800d070155081070603108050300019026564400c0300d034615162046210a403010300520480d000755070360360020b060354068000c5110780302046030420303039402011094072300072480c5031207004a80c0c0c22150008010440c0c0c4035030542c002d41010b08 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 38088395 1250 38087145 38087197
    0x5061b070807180b010509010903060203060a03081c0f02390a030807030605010302090a0306150503031b011505031507020a1a090c01020d23040902040b0a080901110301030206 77
    0x60b04024992041092107108202c0c05441c2182ca10080c56414440104100d111036a0b1090010080e298844801622034031540c001c80c40c24141c9410041440d1000030300e40441c5e140002c0d03c4c00072000590014445020040400320681c064102c2d80d92442c400141c2d0800000c180b0031000c030711000c03071100d0551080a00c400c1107140002c0c41209401080c201750a110200350b06000e01c3d800b401c428201507140c5050075020580c90302203480054002540c03601c00c81f80c2404228040001000b008040300d440c0c07156000741c0c9040502e02c2240d40015840c0104003d5088025044007084403401009840c01c1c600003000c9101d152401003241045004a8a0040003d0b02680304241d480d14000014061498901c48a03072400c0e40c1c3c9520203065501890f00e5200c0c450340114000070511200c50f901301150f60040c250310090180381c21a03800c00d40041400301d100302a01c0f01605004c3d2107070f0341d614501d0b140c00741c0607402c0b10440e4070340c04000c010800050001d81000c2d40180861300009124030310000300505 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 38089645 1250 38088395 38088403
    0x405061e030703020405120a020306040305090103020c581e020c010e0306101505091201021216020304060813140c12030903061515030403180f05061b0708 68
    0x303942d078040380e40030405104ea41080c1881d480c2c40c92501001b00201d040c1600002e1366090010401400c12070000380c51003041c0d00c02e8054442d001042004c4a890745403501200c1400381e00340f10041c0100d40091465040c8c402ca9140c59440c142080700020070042c042c42250074807220700712200050010412580800c0700003d034200307400c0f0340c2c540c4c0640500f00400c4001444203a1030500d00380300c0d42c00b2809100c02d11541c109100b04640c00d03450f041099071825101a5100d00a5a4066600100096206400c07003010f40051061180f01e003000e201e10b9440a00780c1610210703d00002c0300603403080c00709103e69030185400e260090718400e074103262204a640d03907003948000c80301036000300e410100400d00e65007010241810a1448030014500f00078444000ca0f07030f034110007030203000c20f605209941030241e241d03400e0307001441d084007208507500d01d81414050f000c11150400386260361101000061040f28002800040c0c3d0030003451640781c4502d030894080741c84c0300c0c906d41c04600c1c05a60000141070300100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 38090895 1250 38089645 38089651
    0xb091b0d030e060f0307080114030607030b1302040806090606060c2104030f050a02191202011202121003050d0e010813020f0603180c041401060f02030d06030f140a03050405061e03 79
    0xa03070309661301d02c0e1000e0000c00c95a010ba01090425440d04802c549d96500802d4440c0e00c50340034580052070702e10840c00100340324643c0c81c1c080110740c40050f010800c6900403c3c41751052100e81e0864000317889000512045124440110016800949a03038044010080404c0d6000740d1008019081c0380e00c9889551640d20261400c903a194011003003941181040c4011480120008006a620746d01c0d02e070708500c0c0007030342d8a402410013082c0d008000000c415541510b201d1f41d03828103444001c2c5002240d01002d00c00c2400180d4651046c00040100c091007000d4034104040d040e528290241c4942c085081a03125515040f07038000c108a01c81d807120344440010714403075250000744400000301c580e0120300740076803040700074080c1d030034041e50900501c014681c50781120810300d400c0030303a00c5960070700702e0850185a4048606030b00b40407001080c400ba240c24408803900440004003140504107401c1c1d0740d000001001004100b003071100301f01c02e2400c08080d10951101c00d0000d00c13011482102e00c0000c0d4421 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 38092145 1250 38090895 38090917
    0xa0b1b100207030f030b0f0607050f010905061009061a09030109050a060204170c0d0803060a0905040f02090a02030702210d09060914030a02370f0b091b0d030e06 71
    0x2007840c1c010306130302c200c00791052102e50030208604480c1c080440c403420f10868180d40541c80020301e410401204010703203000e0714030010080144500c0361805a4550200b074940d4001d10200110216101e02c0c1442410708032041c04c100c6949408040034008032035040407408641c195038414085000c0b80091103801c10092241ca40144e07110305040701911841900302c6011041d50109400403001e846031140619281e4100110741d44a58078500010740742c03007590700031900c5142070000b80410010040c061070b20a40c03007210034106c3e9a031500504400c03800304666a100603403104102481c040800d0030724102c01941296014684069000c0d20401d8401c2020112141071f598140d220500082d01c5c1c01c500e00d0b0044402a40c030b48003812070020358500320200c865074000c86100c0b00700d6084201c820303540c0d000703c600310803980390700e81508059014421081060342d0703090740040010b000303580124640f44911071400418642c4450101072140d24400790b00d04905100415001c0d81d540e5071990007400d03000400b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 38093395 1250 38092145 38092147
    0x501080403050405061210140d08030c1608040515120f040302030c010618060b04030201050a03050a230a050601090b0409050928050c01140d0b0a090f0e0115050a0b1b1002 75
    0x5c020352640d007d02180e40b1030244034010740400011580c5400d2081d400d5500011115129114548184006d104401240304003078100c2c96a4020480c0d04009002114422a0078907000c00110340d070246680300b890b600d088402c0d0000c00244118880e480c68503000ba003e48100c9052803500da07005807c58070300f0b803c044407599010380c51040915850040001411001c4011030400d403642d40080c0080c000d22100c00300307041d10f40c000606040c2041d40280c208540d20312070005803a8001d040c00407442c0703068800000361414400080c081c2d5011f8070b036002c1206c2c00014868609031400221400400000d000c4c01e0702c9000318082101007060748a20b641c2031038403030044031120b10490f1400c0c07480e2030030b0501d18905210b09041400090409841603d902003140c1c0700111303046d901c403030000f0080b01c082d402800c0b01618041c80540001240e900804803801800000c214030703803989100010b8661548100c0d0b0380402c0044083c4004490000501b060076070032160382c000d086000303091604001000e0300110396198 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 38094645 1250 38093395 38093401
    0x4260318030c030d021203090c0301110a12060b031b0705010e0718050105030d0e03032215020304030f030c02030f030a0216050616060c180e090607050c0705010804030504050612 78
    0x340074442d004a6030400c4004069220381114080c0d103a42c0002080401a038012000402e5088244142211040020003c003e0744400b01da40f083c02d5041600c01c000010305015803030b192040d203840b070300e015500c10f41c1074142075545800e1003070111080855182c4c8102010b01c503100003e038090040c4806003e010001c3c140e101d081088081010004004a00700107003030030010056a03d01180001e0781079002e1074980010504240801d00d0351059804141c0b20313052405110300100e06ca10021130540340068030822041b101d40c5022a52405030340400b51107000760301d0102001901035148105400c1c070103000e03150b854104050460860b00095078110150b04100212501c40c1c0c1d001c940000603240456203541410040104030041854840b0010700180d902d5919100d041d010f40240c08881f0b0040c1d01e03000c40e60351240e550b180301403c250f50031022489403a022035001401101664200031464005094251401c0011a0741c540040d006a003440790400c000b003542d481745001080305420a441f104642e003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 38095895 1250 38094645 38094649
    0x21c0213030303110412020f01050f18010f030903020712060917030a1401030b04030819020c070e10030b191b0804020f090702030403060506130c02070f0f030804260318 74
    0x14040000600da44c10080105000c07808004030800c01413501a2a00342c0000604401070320544102e45940c820f4201c0800e9044900012009a042c806802c2c4d81c1c600c41d1109155054040e140c40110013405a0052442440158400060400d04502690010a07519400e45940d400300485800f0081d16050000400c411902c445c0203444038034076009001862980345840d15450700c030001d0030040070000d008000c98000c0c50b0920fa120030b140030000c030855841c0111308031076030303034050f00e128014440f0044000590f480c008030124804a03500941c050304142d032200c54030340c0001c400a48242c0c905540f282d100080c40e000c1d041c030741da8822090321800003500309030040002c0342c102070424500c41c5001d00100710825a0110075076048a030301c8000454681c4030140000e030000c08550462110510f480381c2e03030311b54580c002010b10032140100398400f15992102e10281070380a0314040644101d10422040041c210b40c10461000000026030101d01180c0300400581154803400040016281d2a082c1c10514 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 38097145 1250 38095895 38095901
    0x7030b0609040b15030a02100504050301050f090a0212030d020a17060d11120109050f010c091211010804030201090204060305010b0103140f0604092402270a09021c0213030303 77
    0x410304a405608516180d42d40282c0c41d54014414819102c1e1000d101e201505c0801807034a5155006003442010340407100d004265803c5889076500c20741c01e160124011404034207240c2e0041e904070000c2c00381c101c103d07000d001c01050f034038080080e40d1008005424131500288080c1c0460b031031541d00d413601220b11041e81071001c50b001c3d0201c0e00c18000d801c003000004d01480980ca482110648081c12210999094603006041664007e003103802440302c591030503071040d80044042c054a80740c40c440c81382c0780c4000384c40040410700004c003010300c485590000c541c0903078800e0b98028482d10002c103141da40d980c00302e801d070b4034241e000b20b5143e0746801200c041503825004428030000344181100443ca050f44400d0201d101c0500614011a520701c000001c1c880c1490b0103000d803440309103a44d6208005520f0307500096120039203564480c000515540009940b80309180c240100c000e048040c1542002c101100030b600070f42000e43e040d6142c0300c20446c42d100742d0018002c06a07550807840381d0345140d414017070f0503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 38098395 1250 38097145 38097151
    0x4150206060a060e010e0411090d3c030302030c1c0603060e010c080103110d0219030308070e060307031505031608120f030a0c030906020c1606031e02071a040507030b 73
    0x180000d55220300500d1b64000c803030034040501102e01040d0404440340c072810521079200990381103008400f085090140c60100c01810340490119510359921b640d03c40300080d0b0001c4840c0d054035803040300740e0f004280b00350091134200584141c010f1a020f29100c0740601009481c2003040803a80701c0f0740400034003103070748030360310804803280300034402042d400c840186170a005000080c010500711403500c0e8161035091840c440b142d80a0100391000c0440e07010f00042d02020b100c00c50000b9481e400181c0c505200f50182424141c02a10190542e201c0907401d5015010354448a02c0e6500c2e0b5120005140d030301000040401100704214011090078209083d04042e08005106545102003200103001a08001100d502104109001507220751001048024250039207000e06068000b04800c180b2680104103a0700280c44880282009503542c1d105a00340c4107403c01b82c0d042d11107038a0340e95071050007607002000718510800d0800c05040c0101240000808151015241580584800d00030417000703a542e550 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 38099645 1250 38098395 38098397
    0xf02010e06010602070b0d06050405010e01170304030f14120a0c03090905100302010c08040e010e06040506040e03160f0c030c050114120103080a0c0204050c03061009030b060904030504150206060a06 87
    0x40940c1010f001950314586480b5001402030009581c105110040c3e01901c040c10000b041403025594603101e064203101c0038029406654956102020020000000c03607045a038480c0f251b12107110036445040c2019003c4107500c9546c041e0f9010003c07001103034002051190195120881c0f202e181303040040031a003607500448007a503c1c24003403081000000011500310303076092901440307014480c50450030301c2c0529404404280414030002c20006148881940700d01f0f0165002c12651b91940200000d0320b046142107100754104004502c0454401240c0741d84060041d415044e1500032030343c0390032118100f68130075141c444440005110302c0d0790201648080100a1210398148100702130240e69182043c0706c02070042c04c0014070303003005600a00045070843e0300140708200a280c11441070103990b10844410f403207200c5142030000320720f0042c4c41c0c10056a4102e0503003a0b0903503039141407005d0703c04003500a03414090148000a160b0304540c6044902614541c0a0402c5c1c1c00c10409002c915695604004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 38100895 1250 38099645 38099653
    0xf0b0301060b0403060221010f0603050c07030c02060a020c0306040b070206060102070303020709020a09080d11300304031407030221030408030f061c0503031801020304050601030803060604090603030f02010e 91
    0x14502c6907007514140c80d040200180c0d00c41d0700ca881c1d0410f50014a100d883d240d2154800020072071010b0303c0c540e04841064801703110320303036482c0d4080b909482040002004160004500d00c007509210001d09660019401200d800c00d9445001030b151000840b02100d5a030000d80412002a505000043e003100e000c1c00280b22090948e903001e51500110300070b00044039800300e00c001c200381c4120230580003003403100c1c20760703002e441100e1000304880c4501c040755980e8031851401c40c00c19501c15007400e0300e0340c1d20a012101c004040c182100c8940c5c1c40500140c08200c141540c1d1009910840024101030380710313400410340d10a003c034883c181710307100d40460b250074001403040101082e80d84048940c4042d480324800015641e84000903901c10611040704100d00440c10360208101e000402180a418210350904c241491442454241d11007141d008115400c01030040000031040405580c0100000744050309050b1200915412900303d607000b50000703020b011001e0310490b0280325080c64039560700050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 38102145 1250 38100895 38100899
    0x60b090a0b071e11090414010608030f040501030e011401080303040605070c02010503041202072309010f142202030a050a050601020703050616020106090c080402030d020f060c0318060a0f0b030106 86
    0xa10440d40d40059040c0c802c07403d00c0030f50400045106070820580d009181844d1804d0506080c43c0c0142010502600d661800d180820105000029500f450044c0b1200b680b4050528004402a00400781042101e40d00e600480084100020b101c601918030040210380b02c2c80c007801d04a00b0380350045d0000d070600c080180c00c640581d078001c0880c3c1d0700c581c02c00c1c4001890030302e0000c201d15003c0300303a102642c059292125040842c0031352406090000c012200c1d0700c526601c501d21031030702214611038110b81e60403242a5000d0350602c5501d2000e004020200819030040d05a400003c0c2d90040301e5000d8459a6841000410420b9207e010f801580c2840184001429940c800b55100405448071514040c9031010307466280c405d400400217805014014409400d00c02005080340b0001c1e1022842801641d9a03814940d100050441c0c00b504e191001340071640720400300584991014100f0f000c1e20400c02d002d41c228600c20046c203805611035080024400d41d90000c50000c540d44840128400c1e4108042 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 38103395 1250 38102145 38102153
    0xa060e10050a050712051204030206090115050a06030b03070f0b09011b050709050606070606080a1e0305030601051b010513020a0b0403030806040c030207020901030302031c111c0b04060b090a0b07 86
    0x2c0c0d0b0201036103c002c9042c4007030b41c81429106030054007c6072103d42121800c000403da80030031098010800034000340948518031208801034090350040c00c0d04150199000c1100c940701c0c2c4c0002d11a2000901030710b401c01d4854059014600b0250881411000002580c00541d60720401e080900c45561043e9008003246a9420707440b030620f03114459916450724007080140d5038031030842c1e5441361f02c80020440250340d04501501d9034a000e6081d20120307500030100702e800d45515030300c0d01210707030541d11645990b036500c0042d98581c100a10302e801c4015003484590f42c481091042c5800f0780210381102c0711804040c0304120140150360130141c80071800340300420000e0342090b40180c07c14011900071404490461086000b4003035064042d50214030a0300010a068010005190316220000940070400c0210b07896000d03202c04456040950340100840700c4031800c110182e10703200d050307040b0100b0f100c40700c0030010703007641ca4540200c0c00076400060302c03c41c503141c5490303000000c0c8002c04005d07080c0710741c940f1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 38104645 1250 38103395 38103397
    0x140d08060d060b0301020409060f0306060503030c0d03150312020f0d0f02030f09040902030105040c030302060a05010f03030c0507081213050f010206040b09010e100b010e09040b180c0a060e10050a05 87
    0x74002c00c03980d12605000400d80e001e4040d1405801d03200c0341000700b03030f94801ca031440842e002d01c0301380ca400e440c0c168042043d04000c006c81e085071031701c030f002810103d5401c80c00700c00819418010008600d42c50703038007200003460161107402906999004024220050350b8030390800d1819241082486010901c12460940100688101620058070951514840000b141c041c00c0d50200c029410751818080000700130b25582a0400d4900030741c225005030f81d4074401f5404480d000c0c014140008000d8408100103442980d4400b01d82c0c0c4904103130744000d5503c02c1e01d24a01120003513409111440403c0c8140382c0c0003182c000c0001423708480c04001d400031480041e45402018001400b00c130348420004a41c2e01d025001110410228011176082da803100078250300030b002d902091350001c2d4804000196916003281c4450040e03800000c03400301a29500700c02c14500c0e0000d244500300b40214507006031699a03403407103100140410740740d07d03400e42108405c220040089503840341c203004040c06243c0d500d640c070070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 38105895 1250 38104645 38104669
    0xc09080616020a060906150b030609040206160c081b03150703020703050f040b04090b0306151009030f050313150503130807080a1d0105160b060109050d140d0806 71
    0x6020003509201c0d00504070304054070070b500139003080d003814402400c100b0b40b80e0162440b0036004e0342640b030050316900791402610040d1202c2e544154888042805850004003d205c0c055540002c12034841c425560304c14404c58560102d0015001134107120584003c0e4002d002d01c0c818120094500052220584000715401800b00303401c040e404640030701014080c42c00c5510300880c2c0c000840e200c9965480e1036409600c80d000d038072415420300c10301c00950305002440728003c80018040c4080300140304140901030541400c01c4c7c00b04848050004003040c44c40307400008460061001c0e540c2e40044409000a40c100c40d400043c82e43c0740004521b82c407503031210030740790880c01c050b03228481c414280c1414201070003480006895a08000b400180c3c2d603800c425803084091020500001840d03d8000555460042544050750044006940400140f14bc50f0003a44810141400708001d034480f000b04a140880c290121180740c601055006d080300100510110089a840c102c100c130314006010501a216070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 38107145 1250 38105895 38105911
    0x609010c091a0405031203060a05010f0c0605060f040609020c011104060206070c08040e0a0507030606181a040f0605031801180807050709020d02220f12060e0a0606090c090806 77
    0x1c0304024101c40300b000212002000020b048600c4210014440405a03106a903214070030b10102c500094154090340c0c4001402d09240c4480e000001e050b11a032014060040070258414180c0000c41050747e100e1260402601c41c1c03401c01a103445244000324210369003558910179042e0240b20802600c0c3d4005035480c2c0c4018141340c010048019880c100c0140d0080360011802e1298102c02c0100c04040c0f907102c18422001d564051010580c2d540c425111040031003030104000b80101018450294003840f144990034603481240d15042e80d0301d20340700e140b50351904401c00041c4c0000030b01c5080b5490101812441049000800401841542c00e100112714003074028100103001c64a02c090000c244418802018030a42c290355400075000c51a00035440f1010305164400c05419400e05143c03042041000d03904c00b104104049403d1010f4165032945000c8210745003520b480c507124078200288404101644034905c00f01d111810a0912003d440c0812501c0c2c041042d10380e000c001020740054010b804c0840707 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 38108395 1250 38107145 38107169
    0x120c010f02010e0105040f0218190207030e0310020703120b01050301030303090302031303030e040e010e0304050613030804091a061801030203060a08160e010501020609072c040507080609010c09 85
    0x2104240c1c09070120400c0f24a01d546400204024818918101044a4803c88066881e190580e02403944020165080c0307a800c8803a041c0d1024101480e0b0017030035041d001e400e00c140080325210009141515a10000700101e4001c184403040540010301c41040501480c0d00707000d80010310000800324001484042c04241d1540c0c001313010b15002384100e03540504020a240407035034890501030003c511108040d402a03150281c0014900c6062290034011926100035524040c41c2108101240d00650150240b030401100000002108880140001c02c449074011030001e41c81504201580c81481116010704410801d060307040c40004801e8032403a609080060f00c0c0c0e10380c040490f26171800c54104106034440c0c0c0d610704400c07405843d0704404450205001c01082da80307071001283c0324041038440340041e07441080180020300d0305c40726541ba1980c01118010f050008486002c1e030352201650240d4440c0c020b003600b400780990921500e44d100c200500280407511030210014000380f600e00c507002104038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 38109645 1250 38108395 38108417
    0x6050a0f0815060c07082503020d1a150a05090103020f091009020a1d01170f0a0b0402160507060302030c07151d0d0315030206180f04060f0603050105120c01 69
    0x1c41d03549040304150081d00d0355894444c01c843c52940c5240c03601a03884e0310b214016200409205401584602c01c000440000c0c40f98959424071003c1d500c2c0b078504480022080c2c0c07140380c41c2d96020038140d1081c6039500b09058001c0341d85091000400302c0c0d40040307005801040061000d1b80711460103800c0d01d041562150f1003556140d000303d9100c0a9038200c05241c0c1d00001e1a040040e078031030007010070144603009c400c17003003405840152055080104140b40c13080c0140f0008040c41d00300180150b00c0b9120120106151000b130340010100e80c4070070310303d20b15a18843c1210061000070028a0b000c0c00450500314078605000038805c14034081c03035100919418100c010b403e035401807070f0440d405440a07034000c03d0500c5022103440d0346420040300d41d540024600510385448005402448003100c1e000b901c501d1500074880490034105052000c8071390804205c40d60020140c40700e200b00d600a020000c2c00e0079a55003005d600409070b8006a000e01d00c42c0440e4001c4421640c008a10480300030001d00782030400034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 38110895 1250 38109645 38109661
    0x1a040317150a090204050a08010605010e100216030c030b1006200a17032a0d0f140c0301180e03121003140705010e190e06030c0301020705010f0606050a0f08 69
    0x284801c015541151034071800103200b500b190090019a5000c466000c11640c170b810416080341c1d6a445003600040c00000c0c1e01500d41005c2101c0b850072060761064815a0960301c0071200b800309a58812038150b0501c1c4410024021a00451a00302d286503914190141c5131a10081010b041019514001142843c441c20380d400c0c1000f290700103d510506111202c40030782107210542d002100c0d0303250f1110b512000205615808200800b5065030040080d080c1102c450f21038004056404c409a4180c1d0380d42c06081c001c0302080d42c560321451103100240e1b03580d030404800fa402d6001c800c1e13a038418681030290965a066001c0241c562000e05c11415204c19a1000f58102014101d82d002611a413001e041c0d000c0d01c01c401086000565600f0b803941c107500101803060246044840d0031140d0200074140c810f101503c0760394401604071800800311500084580f001a0882c0d1040c031007156203a42d00c118240088466000c1d030b500900c0182000e40c100600300c04041c000d408004d4252080100c40c134001707202a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 38112145 1250 38110895 38110921
    0xa0b0109080f0d0e1e010509130509010204091401060207060c06090501021204020f03010b06090904030509060703020c0a050a120b07031b03150e0405030706021c090609061d1209060903030703020a1a040317 90
    0xc40c0c1c480b0014042c40c102100314bd4000d5010b40aa90390003805d26051044580b000c040041c12112264000d05110b0300c1c2040895500d00c50030350803258203444441c01e074089a4240051f00c0aa060408100082e00382441040405038810100d54003d90410400d501141e031940309036400d112094aa107545940d962a0443d43d52241548082e4000c0d00801c2c81000e0650000700c020400400b0790360401026120f000b0800702250307521852185050182030403000980d030300c01017908107000d81030104100310507000f50011421f004000e800001d5540302902c51000c6007000b47c0340100004440c40c0e169041c140c0340c8903101c2c402c0d410068030494000032000707684980310603001c03000e10301d60400700001491031400401501040c00290b4519040c01058203504040c0c4919840c80c4200750010408040045507003560f90f080355804030361051051040c02e40030f032014401002c00d244640d026046003101440d004806941c80340401301900800d0303003000002504880c03141c20700072045003a20a2981e4440d174443c99 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 38113395 1250 38112145 38112169
    0x50d0204090203010603060608150a0614010c05010605061b070b12070503180304030812070311190302040509042114030a05420607020303030a0b0109080f0d0e1e010509 74
    0x4401e1601400083c21107001c1000c0d101110341d040cac0700700303552250b000310401e6800364020410149100711650800e90300076401c00c030f485031042c400491003031b41c1c800c00500710303411038030869000d00030070205a408054180004006092214030b210b040001c0140f21203191702e001801d84e004d1040000100b0020301020380103a0206510100b1a99240e4991a003507602e0b4000400303090301c0420000102d80824040d000b0507840d03800c48000c19081410101410812040c2c0b48140301c00c3c180e0800c400b00380c64807068480c2c0c0c4950700402c0c4c00040100c0c8400e040302030102c0720001c482080a4a0324110010203c03204498200c0950301010a41da200d000114140b050390300c00c0c400c0c40c5420100d81111100284000450a00d90b601c8210400c0c502d41042c00b125110b03102d00254150010000181c40c40f402d035020140c2440103251255040f51201c041c40e16150b2051480c034016800381a104058683c042507000180200f910700000c01202d54180700100b40300c21000905205010818120a844182c20150 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 38114645 1250 38113395 38113403
    0x905030d050405030c010f020a031a03061b0909151c0305040b0304030e0301090605010302030f0706080c1b0f03040801050703020f09010c061104030c0e010b04081e0106030f0501020901090f050d0204090203010603 93
    0x2041c9001c41f03654025800107003d42c01203410018480000520380720301e143c241b00d015014200790b55854400000f507080040202070100f600380f00103e4103403681c1c50b10f54814480f00f0b400c1c5030850620010004010140010500440180c107072100c0041e91000039501100d03840200d441d00c0381c0b610320b01500d003207030101f111540541c0f0b0b00c1d141c42d080c0b100c00d4001904880c02501074601c0a50b078030a88030b4079080c4500960300418080d40c00b1800744603001005000380221540031900c44000d03610402d040004003203904100b9030002c10240729071071007845030301c1e00198981411860100c000d03103041150b010f00f0b83e9460600030720741c020b6414014107810005816a0140b030840d6a15240d1901310444042e90207000200d8113a40d00202d011038085045405881481c0c0082600201d0040f80070008418803049846c03554032600c000002442c21000c0c05100b600ca1030000d616442000c0004114951981c800001100c4090040080751507014610310041d405540c0464402c1c614008280500441d43c0028 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 38115895 1250 38114645 38114651
    0x20a030807081b010203060303180a080706090e060102010b0f01030b24070309050f0307030b07020307050a0305121f06050a050909040506010303110a1101050d0e0d0e0102010c030905030d050405030c01 88
    0x1404210011000b04203030210840c00c0183d82c002484400c0c203d0008450883c0c00d0792040110204075000d1592000c440c510040400680300d44a02e401814944590b01c0780340400c20281c02400303e0a508603d007a4058028030080102c25070040c0016812403000d214141415503d1001e02041c1e2614050714840c2c42c10400b96503003031662004014110f500003002500062007425012031540750a040c2904503401c003d0007041401d04580310062040b0024040c00c0645c8030402244000850912014164030f01036100c0f00e45552840240c2e008148004114045d850996412103101c04110070b0300340150fa04504e0f26a07114440f00505880700d102e403900300307548681a40d08020400000054103416030b48290340742410243c0400740c090b07942c8517403d0000d042d07021181d50780c0d41139403240000d040d0901600700040340d55400700c0c0c929810b1601e4040a000090717880b10b074640f05546c090044118000c090314080008480981344e05889005081c5241036068031000802c052040c100180d03804a44000d00070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 38117145 1250 38115895 38115907
    0x4020a1b03020304050f030601030b01030219090c0513050603090a120201020c01020c1011030112030c020d060504051b120316080c061f09050105010f0810080d0207050a0b0f070807020a0308 83
    0x40e60f00e0308184900b5100d850041468400343c10003049140c100c0e46d00992109082e401d40d802c008001d1a11007460002100c0e0480000c0e003030b20140100d005410580e110300e541e6004400024000b01030b60f40265024201c100f00344405a58000f4110300d203a078004040500f0742503400003c0340603200c0c50171140d50660000c50800c4194001099940042c514074408200d90701c007000400419000900c45c03041420a114406004603010b1176003b00340c1480202006201d40c3d1668482e41200c1051350b00307407858ae0041d151070a000c4000303910981c0b80482112080a82000310500ca40c1e02c2c401c0e5108400c00808403c1036004000600c006e0b19080c0c400002076030420b00e0459021404124400c2c0c8003040e00542c01c00c001024041849030606071a4181c2da19001c0c20644003003a00c400d40c5c040c2100c0300803c4030440c0017581000c1406040c12500d6641d01400c01c8601e02801c122412040760003a03d0404400c0041c900b11200440403a0403150b030104c1c0c000c2d00d03a140780c00080d2010b041c2e0ba001a01e81e032000690307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 38118395 1250 38117145 38117147
    0x702010b0d060e0610030f0f0201090902070506060307051914030f1c0912030e010806010c060204060201021206091e1e07030506040e06010803090f0609060a0201020307020615090604020a1b03 84
    0x200000d540355044444c1599010b60646207100284000341496800704002004600d140c11900007090060404240d4556141e01080490780184815901d64101d44140606854140711030f00060104890608026001050641021400e48198140040889003031310103501c0a000a035817034034000040c4d030792407401c664003c201d003941a9050030010744001e101140703a001d164a0088003603050342d10461003c20500040d10766400160081e41402a03070b1070003d000848600042010f480140e0001d80c4859150340a04e42c4454081d205601c104038150801031044c41c0c49408030014039184810052588034611815a003c4241c414070b5142402c3d40104010103801d034000c01d01503481500c2c1000307001c0d030f0040007946400080c024151150800c2181000c94034002c0b030b0361030010b50014009071401004500140c582c0d8003170501c1c04050b0350007100300404190140714242d0300040c64400200c010260100103482e620008000a210340d9000c14141c1c80c162061903404944141c40e40600140703a51420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 38119645 1250 38118395 38118401
    0xe070609080d120c020102090a0f090b0604150c0215040603051e0f07030b01030b030105040c03020a1a040e100503190210030c05030a020904020f030f04050105060d020310050702010b0d06 82
    0x260000300e400c000c0005046440000d101100488a5480c8001440e5190010014088000d0b400003151340030302007004156110035041d0300808141a503071507480d10b0452580c0544541020721407141c1d40500040040d2480c03000b000240194515100c191100d0500c0001c501c2108554410ba401d000400c001c1a01605648502c0c016040c6a20103002010551a06e41014030704a071031315015510400460610741c001d8104400a500505000c141c1102d000d02190031180101c03400d4075001112a010001c0d0308104d45850007403c5484a42d00c0d6003240400d030000c85105500c14000340c50030b418000ba016010340030245002d00b20060566503142708440908031468220441a40f0501c070208000c01041e010f480342d4910300e83d03075458103801c40e0b07541c146120003504402116900107408104400001d08280001d40c464086192580f845041905001e421145e00521003800750320f0020411001d41e40c002144500b8503d454800300c1c46650b2500201d025000200c1016040040d1288030820455960 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 38120895 1250 38119645 38119649
    0x6030f0c08010513030507020f0a180b0909010c02030a0c0305070c030302010e1c090302090c120906070f090509040b0405071503090302011a01080f0a0e1902011209030909021602040e07 81
    0x40003440a600c5002d010b04c48940203040060124004101d8000107092a01c00806e9108004051030400d0f5a11225603040f20482000790141d030382d80b0b10840d01d862500305940307070300031110700d0003040354801c400006981d91050480314818403101d90717003850406116000702d07070550b030f40224050100c0da42c071301e8013a020300110701c000141401070294605181007144e0000d03034075079000c1c0d9071a042549107400303203d541c03440030780000103a000422503d48542520b04032140034a00c1c0b4001040d5500d40010000e010800c542244000c02401c01010042c50703840c0c0c06401d40141e00720f0214113070f03a03c0b18a06107141841d66441018880744280c101e6503001d416501281c0030700d010345c00912510240140003090a18142d6001c0d000c9521000450740d50385178800c04c00d6012036200d01c0015112503070000646042c1a8001d14003010761000b25030300455900c100b0400c1460201d2030b0600500310700d82d0b4040c00f401c80c607001d0301c2071003680420b948500e414030800306648250094000c0000402986c519901c801080c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 38122145 1250 38120895 38120909
    0x603090209070305100b07080702061909090501081e010f05040c05011403040c15020f120406090e100501050a05040518010305060f0903030402040b0126010311040903020a0b0a06030f0c 81
    0x40000e4840e0b07003c1d00038188184840c007100f4900c40e081c07506552041d080742d5030944508105010810058452100801132541a00400b40040b90b030404000c0c9181d020303411400078070381000c0c0104080c1d4000185000c2d101c00c0201010002546000d04c1c5c1d00500080c00004003441c00c0a05101c2440300005000040e103500baa40d2240c1e00f502041c00d04524402a10010560003030100100124040580c9840c0480007510590340c64001440a2610781405d41100d050b01030800601040500d8104040e603004051160f50081c091412200c0d44407041d46507c00d180c1440000100004114440c00895019100c000e00c40c8030499000c1004204002c02404120703081d00c1048046039500400b011440e02c00d4507600011440e50359035500303000151160f035036854184844888101e845801c40030150348003c42862914a0b07640c598204200c00728000480c041c000c0786072215550200740d01240c0078411a0304289412242d0300c541961500030308143d0b00103800682c09224400401c003091043c14115858 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 38123395 1250 38122145 38122159
    0x110c100b100903080412031412010e060a06021902130f020702130b0a1815060807020601060e01020c150d02070c06080c180f010c021201020a021c05030c0d09080406030902 75
    0x200709840500490001801100c0300344820080e00720380d2074084170514404d251240d04100c3d00810740e03202da00300342d110280100e075160041c0003124000c41007540c0043d0403102d9002061600d003001e5140c184030310602058402c215440c9080d03441701c0300c0700d46d01c040c48520104407001040200c2002908241c1c0102e109001d09144458518082c3c000c6540003400104210034180c5030138020842442e86089000f41c80340c0f82e4288211000000968800401903515025039a250919009007001016000f4405204400300e82d925142d038000b0343e0000420303054564500c2d003d10170f0303210300e054000c0f2421061028000203144040086100e0f0380002c641c4140c075002c41540b10600e4000071809600110081c0c101852081000e51034000303290740d4401c40606004019022a4002c2107074807441502c50300c0541e40000d00c07568200d030304008000400305401081e58040b20a120004c4c000d1202410714aa4101e000c0b1f64940c06651039400100216444014203a64a40d103110180142000c0082a0f2040780 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 38124645 1250 38123395 38123419
    0xe03060126160605130308040b0d0e070305030d0c02030c0a0804080d090501020c0607140a06050105030c040608030909040512030906100803070f1203110d050901051315110c100b 78
    0x4a84000b86140c8108008841c10284201d030b060300018681c541400305c0c85400004102078400401c09410800c09903a40c44a9011004085d2000348107801800c2e80450f001b0004508080f0507944646c40f00c080103e000600f141040385503009040a101103806458000c10030000d42400410851744414255070407643ca4030010f45541d80140318040c0503070803100e009102480c000f001040c056100740d0840032a094400c442a20307100c0310344030464140e0707550f034014001c6150030442210130190840b0306224040c02d020415480707000e0307801190300820b26080410304210047c094a0700703040e1142d050a0303d9240007015203640e69019580f104400210810201e604100030044400c4207402a10500102003a40c3c0c800c120500c20300c0761035040694030051001d94140c030740000c0107056404071001c60030b82801e80c4ea260840c0e5000d007098807a059108024000144801d0149025071400310001841c0602d82429015500c0758812281c0710380034010891001c0010340c1e0229801010980c3c220304004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 38125895 1250 38124645 38124719
    0x10503060a05040f0914190f03031407090302010e0f03030706050c0403020907120605010311120414010e03130e06011d2103070b010509011d090a020d03080108060703060320010e030601 81
    0x100810070301107840c881e18201c7c94045040303400c50381c0d16070f882840d00058034003040c0004542c550055602c500020100041001550380c0612030001500b0300701c600035868010034000907928441c91500030b080645400004d00c580d680c4206850045030042c12000c0c10303180c211001040310030b0183e244c07040703580b50840202d0b00d07500c64480d04050600c143c0100345460304000d0003c820503401442203410441d03102040000704828002e07401105031400042d03880307440c40340b0103001c014580d8020302d18148480040040a81e0f02403c0c044103030707031009032030310801c061100880d00010410103c0600711010403440003020000100600b1005c2c007030100d1001990300c4004001c1000400c0c80307409826112400c8c0d14140070b030134184840c0c00400c00c1017160000405940401c1654a0140041d0086450760004002c40c0a00307120700780d888169454200300c1182103903190200002c85a00c4422410a0300c000d60101e41d00540180045920050403644103682d64042a21400c1e07040c0b8a000e42c1031400c04c003e030410b07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 38127145 1250 38125895 38125903
    0xe19031518020d060b0f03070609060923060703050c010212090d0807020616090e04050303010312030204061b080d0501090c0f021914030d020309061501051305010503060a05040f0914 80
    0xeaa0b004100600800e020b44414024001c004078161303010b00c0d15110000555010441000104995220858034a2400d50050036200d19680508103942a8009580303442d1001000b200c078520040f107005803242c0d001d041c120341c5401143c10301c0f1403561000414815425505020a10138a240011140320240720601158004001d652903005a8002d83c08982d80b03400403404042000c66504d000c08509030349841d01a00f00800340e600b500c2d0785e000080180203002e0f104603018000c07507141c201075240502c0d000004051030043d10003000d21207103c6540000700040308048a19400c05141c0a211a5860b60311000040200344c18920110f607a026114002c00e0003c14003c01d001d64208600700c03044401c0c1c50b003c00345440482164580d010400440ca061701c2144045e5001d0040313680144401e28081d0000b111050303c904106040c414148148011110341c0e00d009401e0350003c3c81c05544a07111103004c04e0803010141c2049902505207004100d0250301540481040c0d40500500325040c0824031806482d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 38128395 1250 38127145 38127191
    0x41e080a0308040308181b100212040603050411060c0d03050a0c08060f0102120c0604050615090a0c030209030106140a0e01030c090207080f03011d070306060504060e190315 76
    0x402c0800d000100402d00800003158003444c124401e500b0460451200c074140880c0b1404100160b000707500210050811070344921380c568160000308039003020090707030b03617050300903441840205078031240017034108032003910445440c0394090140d5031504103a0492a03101c00c555003207a40000d142400050125881d8080c074640e035086d1340c4840695444081c00e00c003c11030300780340060661003281074a42c1c0000b036000c020098403442401400440c206807502c507080881c06480c48540304450310b003c40c0a80ea0341888550800e02c5550001b072005200c0c00c0075000703401003064580c2d065107850000078501801a03050130342c5010840e01802d44e03d49900802c0441d9100380400740286600301000e1082d503a0b568007c1c040c142c0141d204504104400100010940c000d0300b04880a0810b540004500340031340442c66001180390405111031800c00600810300c0c083c80c8198010003082c12155169074840104020104608650403400192203042c04042c2c040c050388000000c910300209550140c90030b0350302c00700d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 38129501 1106 38128395 38128397
    0x9040305070606050a0e0c090102070f0906080c030d02120f0f0f1b06040503090d031106010305010219050a0c0605180601060905150301120f0f08041e080a03 69
    0x183c400e5948020702500034900c0c04d101402c04d0b081980d5203d83e81aa4840d194100708004078500120345e442640b4080074140c0c041030305480741c1c101209507a50042100c25480c6030400341a0780b403004405c05801a04101e00c2005202c829a00800c54106480411420944a008124260340c00042c02980c01400001c0c40e16095407030000c4074050194940290800303181039162181c90344144c141052160050040380410180544003420318211600121606503840e443c200b030007948140b044003242c0c0d00224038000013611074011a5980529a659803001c84c03481d5030313804050b20f070183c0750800000b851044030940304402c004040c020034090b40c0d003441c05c1c1d20303081c00e01020b0200070100d00340050003000140071001003402c99a094039803044d00b107240c00d1038608000c5482d001c0e003c0002e0042400050005601c0c11020325a685810009055102c0e580c0c0c440d0125525100c2003c010 = true := by decide +kernel

theorem cover : BRFrame.Cov 37949645 38129501 := by
  have h0 := BRFrame.cov_init 37949645
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37949645 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 37949645 ≤ n) (h2 : n < 38129501) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
