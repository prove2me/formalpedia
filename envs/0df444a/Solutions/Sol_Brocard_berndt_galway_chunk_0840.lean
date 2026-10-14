-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0840
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:05:47.230354+00:00
-- url     : https://prove2.me/submissions/b1964d07-a63e-4e10-bb46-aadef2a65d3e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 150899280 ≤ n < 151079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 150900530 1250 150899280 150899317
    0x180f081605090412180b1314030c040216020306041407060207080a110f060d090506070309031d010c1403091c020f010c0305090a141206010501360b 65
    0xc0d80c0d4211254815a48010980c414548442d111101200203414104050007928405240d00c81c0b03804541100401107000d4856075207079494580403c0641c147d0000b1891401801040b0349a41c000c103414054000c00e550050f1520302118450310750701554900030b0f4050146034180b0041c010420300208041005104440460f50ba440d0100d13650701080c421011607410040c8418006168030180501600c2c000700f058500e100030b14005100c0e90f2025980381e40484e40e8080c2c40c0c04122007484080e85c0b2402c0380c20204a13110702d949001d4458030001c3c0c0ca00c1d60070409150141c03ca13a010b41c841c160140d8101d016100703080c00020700c840d9203500644140b4840c0f11840303601c0d102d80140031842c1e90215400b4040d01e85c90314000005490b03c1001308011024081c044c130140c1d54607245c4440c0785000304040140e1602420368807040c80003000c1e10081c1c8452542124005101e10b036004400c07441c202451a94070400e42840e81d10030032000380c1400350955404030303c50380000c00300c01640140055240c0804030070346 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 150901780 1250 150900530 150900553
    0x60f0d0b031f05070207090c050c011401050f0420120f010b0702060a030c09091a010e042715230a06060207090b030c0405010905010f09020c030d0c180f08 68
    0x2e031070b0864018420040780340014034464420a80000390024400d00484031150b48034860706040e64122040341c00000d80126400200070424000c541c2d025102d845000c0655041ca40402c200c002c400721240d000720f0729a0001440c03528000000410540000316113502c985843d4546203c005054800e03c1d22a0350107400401c000c1d0480007107900d0725600a00c00e500c0c0001c0348606402520454101d40280428183d00042190260180f5040c03030ba007048550800c90031070000580079500c0700420f140168a80401400e010308125a0342041210401c1c2e00450103d02d450708a9840b804095680701c1c060420203142041d8078041006034440d4180380f100a460b03556664104202c400343c0c4141c10040c4d00c00401081401d2869104258100014054620303003402c4001007801c0e583e0070307400f10f040709035204010410381e000310000101034026440150b14061182e01c00990368003881c00e44161440d0344100414a00340903d110410300007190000c60a00343e40e41c0c0e440c410803480d5214494030b50007096030005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 150903030 1250 150901780 150901783
    0x8040308030624070f14120d141014060d0f0203010f14181b19030e15060f0a0806070918060812030603010e06101a030403050901031109060f0d0b03 65
    0x7418400c80f114043c14110642c541407140711004500365007a00c02c0c0041907203190001e0282000840d10b55142c43c0d03640b00344240c994111503100003944071403c5954180030b102c6080004003411074481d03010703c802000d50750700010700506c221149040000d186c80c02e00740b9120b0064025504031280e002c415026243d070303a03030362900042d440c84c000c0398091820002d544d05136583c080040e13044181e400006900c1d56401d80040c240f0f0f4441d2504a02030040c241e81062001d40c1030042c3e1608100e0700380644001c02c0c041e0121681103002524080c403602c2281c1045003952100805a0000e0284408642c4141010940078200e400640a40541400590800042803e0a0003100d003102c1c9240c0c01002285040000c0b04155080584141e516548942c5506000c0004200c214007442c98051805180d034070707102c0040602c550612022aa0710310500070400403079000016940750090a0801151194480003618124805c00e00c585078408808104060300c0f010030b80c050150140251000c01a810304d000815 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 150904280 1250 150903030 150903079
    0x10b010c0201080415020c030d020919031203020a12060306020309100605030d080402061303030810080703030e0d0201020a050303010816171213211b060509120a080403080306 77
    0xa400f1500e210080380024007a844580300920b00d0b00700050400c00b110b0001401c503806102803c28098021449601e24a000d0031b8a0400a07044c841040c0c441d881e43e540d0198540c58060724509050380401c90001d418019041040f80820280c01080165140d19058000350025100c902e0140324980e807085001d5090f07c100000d5400080c020305501e0b040e01c40840d20b1200c010030880c3c2004003030209840704110715100b48050f520a07180c401c060b00c3e108002151004040d8001406680026800c2020a410118240719000c054540510301c00c403a00040c0e280401c2c40000510f0381c440040006032907000031400442444075460140000e941d5040c0714408000d0008010b00c154001d046821804411701d401851030550542180d41c540780d90f03051143c5140201070007031240f00744c034900030403c00c0500c10949150302d91585a00002a0501e00c006103039008016220f8060f1400100019a00c04c0411841611690180c01140c2d03640d201e10b003074505600140c400358010303100306001007020010340519 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 150905530 1250 150904280 150904283
    0x5030d030504112b0f02060708070201021902011b021207030308090d0e09010b0304260d111603110a06061205150919080405090406090b0a0905070b07060b21010b010c 73
    0x1a0713064514000a40e254080704400110b82c03020010081c28016100d000c0a000218022110252540c00c00e000190501c0da0308072aa021440200c140c1c140141c1c0c11407000c5da2062003848004420382298404a40060068050381842d4030074500c0000803d94450380c1c06103d203d015003078400103058010246c1d5025900229994801e11950040c03001001e4100590380c4180980c254034803031004050400b03100c000c941e40c1c1c0307402d1210024095100712113502428441c88259025075150001c041e900c1c020000e2602c80c0103007046241c00b800030101d0801c0100010385508181e01b0048540c1d12002488015208a4120703410301402200700d00fa0010807104a02c070300c028030040c0c0080340b401d046d440d003a94007240003120358220901001c252611155140c0d403185200e22800540c82465040c995003040e40144900030036420041040c0c00108082007031f004a0b604d00c40720646404040c680317000034100842ca425007000d1885248149590074524000c8036400200003041802c40040c01107804d03080e1000c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 150906780 1250 150905530 150905569
    0xe0607080301090f111306021605030607030f230f0709031205162a080d020c150408061e07020303060901050607020409080307050c0c03060106171005030d03050411 72
    0x40088641c1500101c4e40c4a070103040000b0250410905120a42c1000b6103664030350340d004038280080c0c2d404019004040b51480810405985041300003075845000500010030980c9900c020009081c05400407a044e1480c41080c110f11740c3c50501840d80000d0450f98118680100c1000c10b1409000f01c01d001c056039040124044c4848130030400741c0301648031f60308680b8030500440d0000702060140d00740c2200c40103084140d81601e4150389889244404541080d5965080000100c0821360001281c3c1100001a644031031003c1d0b2002d0341582c80c0c040c0e81c0c0124a54000d61040002441c06c0d10200c403e401d84008803152030f620b544100326030b00c0c00102c0d0380f5500310300315070010301042c588a80901aaa0710041c0081441203480d0b66a5055400c10303038285022440105010000300c5050191007038003181a40140039541c5806401001000c4c0407044400207214840407031103494854000c80090180134003180c104c40c804e0351004004010441381a2211444100310030880d15081a4681c4401c00044 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 150908030 1250 150906780 150906787
    0xc0702010c021903080304140c1e0f01110a050c010f09030209060d021201150510140403170c0105040302030a080109090c0626010b092407060c030605120705010e060708 74
    0x50900180b81c00600303c0c0002ca103c010400000980a0f0004522543c4154003000e03070700c40c1c0c042c00340d4039000c0d40d01a4503100d0f004501c1c8000c1c0000d580058250104001c03209040001031b1840140e0700c02e00440200c072500d020300d800d04420b019000607101d0f01100f080c2d0720652840c440c7d2104456504240c04000d41c00f02050300401c1032441d1219030080d8060000f0300c51000040301d07031040fa0850b14062183d1512440f629010409450302520744145000d0343d0030722205481c01c0c001705d030b8424455800005c02c00d00d141d600c045550803101f4180c5001da114840200140e09040c00c1c080d60303d411544101c00000e03104000442c249640c0d0044082c91503100000c501460b003400425140e41503a6401c002c0124075000101080d1031000030044d000304056040c4642d0b400e02e01c2c2c148013003424101549141040b6044031a0708001c00c01c400c0b04c00031500900001100c0703043c000102e000d00b200381d200e1580000d10103c00d80c04050042000c504580c002d80301c02418a001c00b0600115001e060b00240203901e051 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 150909280 1250 150908030 150908033
    0x2061306141903091a04050a05240109051803040e01090b060a0c3005040503070e070813080706050103060b04060e07051c0b030a030c14061504090f0209010810050c0702010c 76
    0x4d0300901c8540b032045124604e032851800031881d0b1104102d40556059114081d4081400001d0096040c000e8444c4c28044803014100081140d054040c4580041035940c1c02c0010800b40141c1c4031400400018400e403640c0703e0745e070049483e8181082c0692282c2ca4a42190f81c441441c001089484c030709050303101c04414035815201e03448100800c4804902ea5086644111200511121240c1600c0f0468440e00c2c1c603030381044181443c00030381e81c0019414482c80c1080c00600740e0032581e281e9024002d101149514161868003403014010034800412507800d000000c81081469008803410710030503034041002c0c0365030750361b441004213094900501007401048840c06007680201b40c4202148040c1c008100b084407400801c2c5003d24000007500002d6809486200b01b007043d11030500b920003208002c1400b41050b41044000044100003244501e50b41c515031410071031200100c00a20303070000c050801c50360f51449101d444103c0c114590383c501d454040001c420070810000d41d0811074044e550b040c082040b9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 150910530 1250 150909280 150909287
    0x318010f0618021c02041203020c2e11010212040203010c02010605150c070308180907090501082e0b0a0e0d080d05060105070b04030e01110c0d06020313020613061419 73
    0x134420304003e000e4042000f0302c4040c010300043c402040300713500300e1380f02103018100282400e0103118002e1044c1151005c24600c0c14000341c4800811031091598000b80e40e5a400540d03a144031001c00306101c4d400402c150b1044024544618070480c001d030001e00108600f030004900321103542c05a80c0d8403582c403008071401941c600003d4412151b18404586059071a600c0d0310740d607034009560a20b00ba0420000e10412402c0195030341d900300f100c078248a0b18a9050a00180031060000d10510282d030800f442c0b1005540902802c5950140288042000e541c40303514400069110210101c00305001001115440c10203d030104026900810341d03504000c08035100c02c000e01006030204d0704101c070074848100414044c0b50228061486501c905044282a000242408280c101c088160790008050b0110300c1e1110082c0c0c20b0407a61140300103a6035a600020a202c49511240194001c180800e420a0090702980f40106449064842115442c3c90700d00810248c80b40c019030035070240708080700401c030600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 150911780 1250 150910530 150910537
    0x9221a0711060c03070207050406090f111801030906091b030212030a0917010905060a060f090c08070e0111030d15050402040f0306090606030206030f070906020303062110020318010f061802 83
    0x1051041d141f6080d1b0701c000240c150341d000c0d00b03c2141e10790355281d070715002056485110745c0c581c034102241d414221030000d0608884409039030346062548604100d810880e16034410004182c1c4442c0e140a01d0074846a40e9044d203000c1c0c001280960300415035a100708034000150b1f500c09003565154800b090401401e038401c0103901d0b150910f50343d2216103407000581c003813003458410030201e0800600720349030810301100b5113040d500c40d0340b02514188500400a40c0000c81307550008203818540c0c0188880401200c0b250344041c004c1c2410b00000c1140300101c010394001c52100315100e84040e407080e850b00d003000704a104074800c091b0000d900d40d01c1080021420703000942c40d01d0003210001290343e42ca401003032003544100c48060361210780404000460390000754207009007955100031421031031300d00b010410416000e54291080120b0b0441d4820b004803c0040c41c10b2092540e40075500e0303050111188551900080900400c0d509000e000f6503d20780500c2a2130440704454a1300c20301c0d0805101c408020361 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 150913030 1250 150911780 150911791
    0x6090f07031103010f110c0c19060c0c05030d0e0301050609130f03090506070c03030305090a03050f0f09060f0705070e0403120203070e03070b030106140f070209221a0711060c03 78
    0x1500d4550030319001c5c0312403150117010840c0984007540c600001550b2400c004c5070106441c0f01e0041e000015150305200c440700d50665603107040c500518495070500c80c80c100703519031003241e051150f048890803ea90081d100104c405080d002840a51031300300411001000c104c4101001001c4900142c000c00e0420001d956003d009080c420386650300e41021400036441321905480c091014442002010b17418401c00d0342c00604a005040090059900200140300d0300915907030305035010512107200e140b8202118444940201195510403049100c21416004001c042c0c4481c05042000070701c840019000b54070681e0b00d44d9a0b07a40488203840d0f144000c1d0005480582003105c02a20400240c508000610152029a016689039850418000c08075062401340d029030364800c1c001000090b450505580407254112080111555001079080d0401d1210701d01c01c00501c2c2104044080c0700b20740b04c20244145045141c07000650382c400080e200034041c1401c00b06291300c140000744880c0101005140c012 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 150914280 1250 150913030 150913033
    0x5091c0c0f05160b090a03020f0111010504061b080c090405070c140f01050105030307020102100209060f040902040f09020a0509123406140a0309030c140c010206090f07031103 77
    0x1480d40c035031009045884004690070350002043d04410380035901c0280080c418803000e43e103051030180225041c082c561200900035a04c05402c401c4a038010120000240c01f1080204907030728007424010080c01c1c2141e1034a210038080071864420b00e02c0341c412a07214500213000c062404a8110034000200802080c40d0b040080207403030080080e200c2d95500d510400444000c1401c6108400311508403041130b032040d03101e07a008000c64070050340c0104040c0d41d0410045801620f03082e074007010a03900e108043c2c3c1c0c00b03440c40c5e00141c08507090690f6405801590106460305102c5134507544203504911445440901040c03090011069519003441c81c01c034454078800950756050b11025840310a52103442141691058143c4e21000880100d1342500081a241c034001142c065010510f94007403180003410000c05440c0c03001c0c1410f06018401003221542e11110031a800084a1410fa85031030190602c00e0050180340045401080005503403005090500041c02c6e000f4038560324840d008403404849600b6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 150915530 1250 150914280 150914297
    0x10b040e01020a020c0a06090504150f0b1210030b06130912090302040b1c031220190309020303030a1805030409050f070c1214070605010f1805091c 65
    0x162594000d44400c0810040090307192441d42c90081e0400c08800b4445014040c040b50400000303510070084021214142c60009413100d03100840b00c0c1701e074140c1d003001c034101d5454400000c1c41e1281c00001d06c640001c581c04203081d5100c603a00186001e15501c000741555213007201103182d03890300070f504c00907881c2a030500140300384a075582c0412109a1051000100d580280200103500b014025610840c0080b1210000e41c8880b1801c002d81180000014007000b48180e491808100903034400e201a910001e40702074128516000400254428443c000c1d082c0d0082c2d020070115070103400392212650380100030b0741c11a5515290f290040c64a500d5103040440c080f20400080740080c0018009000303112404030341460030141c4481030f0003002c2c0c0b83c0340411103000c0e00900890301100c5079084040451801c0a50350040040d074052901515030080d15562412000040c038414001c029402c03a503046040840645180840c0f800302c5008880321400d5800200d50300c020100d07604114009030741e003402d0800742c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 150916780 1250 150915530 150915551
    0x40212031909050f030102030606070b070c050304030804260a030336060b100507031404090516090b070503040b300105031e1905011e0b040b1014030901 67
    0x98103010841c0303120115150b51000d20103420208403540d5055001c0d0001d500d5800c0000101d040c9200c1c440c0080e00c41445440494880d1340300c2c00c403400307403260404100c076280d46d142c2c02c000d91180c0c424031544d40c250400c0c8061980c040c400002a150310a5058051b290801031030703c0507805082041840d00050f80000c01040c92003c2070500d41e0002c42081000406500c40d500d00402100c1180041038800e090200114038401d40c000c0403124059850b2410005241c0c0c1c007551260140255046407102c2810002002440d052803040749844000d0b03aa41c11946559038000c0811070321401c070011380290020801403001e0203441d00200070078101c6d48411405203c5040d40c40c229506200d142d00c0840360100010002441c080220707003101007003003d075000c0c01c6481e10090f568131145030324031054801c195007080c1d041c003800794081b414151107004166402c10021022000811940b400070344101d180641c42003050800e50794002901449483e801606042c8071040e0801d074200034042c0b0015034a0f10314400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 150918030 1250 150916780 150916807
    0x9130b0409060b0909070f3303020a0e01080702032205040603051f02120a09170c0d1403040302060f040c03170304031e08150a0312110609070501020604021203 70
    0x500c05409610002011480b00007002544240a000d8002651090f041400744040c071a00700c00885a023403071520315002c50903d98044480c0c4880403a105000d80c01180080607406800801c0c4000065650407005601c104c015500c40c4800d8540c0c500503401071090701e035020804040c94030009900403844814640d544006010b60700389400403a03941e08036605401c01100c00d1045c540005103500c1c0154200003401c8110b003c5408000d0001a007a80c480c10001c081c06040d20861607180c2c82083e0082d83c1d101d415246036a80c5941c825090009500c12210511000700d070400e40e80940c1d410380c0034042644406c1401c04050b403001d4415030344060f0f0204004000358407445004401e00b400610780d912460319040103004030a10102103041700d0781c0507202c81211a40040c4c001d40c401402e408240b0051480804604400c209400081a4540b04082c1c032030340e5074100060041c9010214210344140c0c1c3d070300e602192581c415101e0940580d028034081001480d14003145540c01d101c0c40100ca041c2900901c001c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 150919280 1250 150918030 150918041
    0x702030a0b040c06080901090809102c1201020c06130311070807090c030b0307060503100513050f06030a051c03020d14060f150f160213050f060904050309130b04 71
    0x80f5600c441d00c44003044044c1d04581e0701a80050914003c024403000c0351145a607611940310018458484010030741c42d500d000301c00c0c241129811180a041c1c000d405082c07511000706484440707120f801492808507090a05008a0352220030f05009416544c441107014810b1850307806027207060100c81c0c404004032010821110009100a800a02d030707507480c200d414001c64092001c020201030920448540507200020b680088841914103540d41e5903c0c071954482c0780445800040e4442c80f4450004480d014641045009401c0200034544545440c01055514944030100030030f290024840c88883c80b500481d110041c620340d0401500d000241180e20040b6074034103500441d0744842d0018031205040c0310481d558003410644807501c09015403030100c43c25016034800c54240c0440026100c4000088850329101c0c183c0c05408981864103078400312010f41011120045100a002c0c0040c2e400e24040d41c841d80501d4000e4065864210b07000103110f9520100030207104059140c104002050310340d403040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 150920530 1250 150919280 150919283
    0x20a050907030c0e2e02031603050c01050a150b0901120501060c0302120c250e01030b04031101110f07030201060f06121103010605041e050604030b0906070915050702030a0b04 77
    0x10405032855000d0b0031a0b100c3d580e024010315091090b024a0501040e18080381780090780c2000c0c0c24003e10b00101c4c558410000700c3e80000c4c003072041f502c0c01c154201010308400c14900000744003e5030303600303980360499103401c00c0c01c2c014100f0308004000791554a002411b5900d010301d0b00e1180400f4120001044d14820303804100003560140c100c1381030540c10b00000b45500d16045160740341101d18007805544001d005808a6164180d801c080e01040c00c41459500034645407490140d1980d5a04100c1038608080360140c020492900f040310390741c5410300c205442d00302a100400d00705442d0b0500f001d900c0e042050110300350740d0303a0b4401143e41c00004140c2d030020a02a43c1d920784d418400406a01503c201821180081d036040c00107002e800e4008042d18140c0b80d9100382c1209110600444801f281c0d1150700540c0c000305d0008001c4207124002260910072503640013121303e031352607130842118518250300c54050b5070380f400002c214820f44540c1c01448c2e072600040848007220056242c8545405003901e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 150921780 1250 150920530 150920537
    0x5070206031306021215010e01020601140d06060b03091b0303041511060411040f0b03070b0a0c0b0108060402040c0203070b1902070515060907110d050d0e0a2303090a0909020a050907 80
    0x2009240f5015081869100a0a2808030840308c990380020b90f40e45818000c0820a884100801d840303038507040300310540309030055418841661354102d0042a50310603a8504141d00507150141081c80b011742c0e0343c01ea403080160046103020f04e0b0807004419420040c4006040003000304004070900c00410407240110300500074074034450343d000d082004845104100c1c50206042c50042c40e11540c003c295442143c62105280d543c071a01180100c807100348100b4024603000040001090080c4009091403045100b0303141000310244440c1e060340d0300e00490340014413102c1050001048030382e07586140050b0303104c5590b005d410b01100b56900360501d480c1802c203005100e40034040122030310380004040e411901d03c0c200140340c80380420720300343c490385100c0e540414050001582d00215078181e01554282041005075a584107041c6000511030f850703e17040f200707441092040c01607000004000c0320036020005040d40381082c40c001011019100e414001e980c491450000081c00b074030340850140c0b0860f6280d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 150923030 1250 150921780 150921817
    0xf0b250905040b01180e1b040806100509012402010b061210050a1a0a020c0d0302060405101104030f05030708030c0403051006030807030305060a0f060c0b160507020603130602 77
    0xc2800b08880e00d000000e8100044141d0003a00c032092403446105590801d40440c0d00350b03588441d00040e00940032103000d05480009000541c3c08000b041103405444000c42c600241c6680e80c0c104001080203004440c581429030303031500224002007805a0203a0100c0c000400c2c05030b50240000d0a540040304d542602000c50010080c001d0015800ba00262400302c3d0005519410100e03600512000010440b07480300c0005807a0b0196070080090903501304c0010000049006180360003901ea220075503080340c0da84a10000c07051180114090023109107580c1c0100c5082600e1501c035200000310608095901c1d000401468010444001c01075100d02403c0110a940e0391451070158a89035100d165000081e141c00410b000242a02c1c003201c400c29010700e408030b069114a00007460a20f0036a1083c94107120b11640000e82507040130513115024081c400040b00c0380c0d10402181d014a040c3c4c018940002c9080010400600e0000c010f150440e0a45104101098850342e41c0012030b0b0140c803918001900c000d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 150924280 1250 150923030 150923039
    0x2070f08010b09060301020a02030307120b0402161a1612091727090a0203150d05010c03060801050c030403050a09120c0f080c0d02090a090f060e010c0206040f0b2509 73
    0x183d2555410040a500841ca0628880402912400701038074150400c1005440c503803131070607513400c05584114010b000b15902c00c0403901407081140c40c0002116a44104c6001c0e829280c001c01c100d6115648500f003840440c1c2d10404200d4848181500207100c0c01c0d680d00340d140c0401c8858101040503003842001c141d40d00564180d1088085043c840d50a2191007022104c0c959252110041c0d04400c0d444005a00d030740718104841062008c000c000c82d001040d42c00c003402400015085518810040e807410000c3c10744a0761302c3d50030f0f034900b2908c0130078282d400c202190000c0e06c90700c01416682c8803072900d0210300e926402c44807030396800380324280e4486003009410301002c24441071900040c040030307008204102084011a5020f118030001920031180b04001401d0211103400204450707038050765516008401d450030360003d29041000b09660b41c41c203260801d540f80009200d074001c541100324071801104c02d585000c14101b0062081d204058080740c400001945440800d41004e0749449015080307041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 150925530 1250 150924280 150924289
    0x60402040c0311043305182b0b0c0405030601050f0315090705091501020c0d050709020d0f0605040608060a05150907110c03120d02030912070f05010506090c09010c0302070f08010b 79
    0x2502c103485c0040062182d5541d200d400608440e0b40c440580340041c01710490a00046110800d205031440d000107c01c414480004010801090756109048040d0103450384010b4602031f00603401026010f074014401486945450b2405004456000301214031001c000e00c0780038411101611401c25a178400e039800d11052a00020669000c175001c03da0081100d50400001c0d40c402041c002580102040070440d0306200c0306100841c0a03045240043d55102c0010301908018030368070b0049042645406004549882c250240c81d00b10703001c0d00010310b00c50700d0700d59400006140c0038040340c01c1d06a6030f40d0b41081913100c0d40c1b40d45c2d1040741c0c10348900300800c034110300301400c1160b00d4580d50701c2604010010741d400c104c2036040c2c0c3d200040240c40140c980e40e40e584101d1610104034030b14604030b04003007000010012501c900c00d4145219a00a10081c0c403100309208040800b5542a0340185082c0900300f0b0701e51140e50191a058043d2044400003561980710865216180c1c000440036516900c40f204141403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 150926780 1250 150925530 150925589
    0x6080118021612020f0102030115021b030c121603080a030b18070f0504080a06150b030c1902100e06090c01080903030c030910060f06030c0c05060402040c031104 71
    0x1440081d0b160250ba4802240e401e510881c0007001209100110320009100300003520710f07801c142008540c0c0b541c4524408006e5002009107400501c501e8000c0e100300c1400e2201d202c6d141002500a080102003002080100d00b1800c040c9080c510542f20b5a41000c4030440c40d03c801540180000390f5140b5440400a0565040022441c001e0262040300409081c035029504c2e4005e50ba841c154208101e01e2030111900d20440d440903640e031040620308418403a940d4454054280c0e0f000c52203001540d2028900b1140c0011205604240703c14809030030889801603140700311303090520554400d60b064034001012030b081c10f0030b08000c540c4294200040803608200e0010544002d091400c82031614603800b5a07030348401440c09905030f01c08408200c190714100084010b850f154041401882e407542e82e50940740005e842220006403c1140005a050180084501645c0c12002400540ea90b540912014210309a8100100755a2750b40c104807540f581000b40c0701404620301d13140b003039a20820030b60f1426003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 150928030 1250 150926780 150926819
    0x80d0c080a0f0504050a061d060c040f06020d050f0702060c061801150311100903120302190905031009020609060c0a060e0c0102060a050408193f0f0b0a060801 70
    0x30f1601c010301010690000794a01042e500290100e4071381400e404240440700c41858040351440317807030140b081c48050340000d402996448150b0050039680ca40040b40d031002d5450350713240401c104003c0d20801e81820001048541e0010703010519000c0890200d81c0340c541c4c2202c1030014158260840041c455080c020b0303181e0850f0a045440007542961905a10701202c40d0205106030701c18003000d000705024480450086d908001c2041111001401c041d004e0b500014482c00940e030503564202005004002501c03c1e00d00280081c00c0140d0881100d50051244a8069a1142013801441e41d280d40d802e004160a00c0c4142c05080b000c0c606251450a4a0003080e150b250798010140c02c1c04940d07170015803a9445101207001041a8445080c040c0640c4918a02c1c04408840440301c80c0174603400684586010128211889405c0054110840c04008411090f2850400035980d18202d84007034000460400010703000040c407a010340001800000e0503440f03000880c454800400000c040419000701c1c1d003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 150929280 1250 150928030 150928061
    0x9080309160902190327050604050607020109030905060703030b0a06091d010515160f12020f06010b0307050c121204230307020d06020c011d0c0409110d080d0c080a 72
    0x1d01c00013041075840703000c0e90003810543d562010043c0d031803104103040542400c045071105007500c90700345552180000c94090300c2c1c0340302d182c000c034220710302c14450081683c1d0140d9074242c0c1c150a01c1c0806c0500d52041d00c09500701629000078440d5950790b0b8410304020725403900c821011b0b92a0010074264a13010708038020a4840300c1d40104155101c540040c0320700070100d800030342d4510011181500d5010020b41c00380001c0185001c0c102000082c1c0c180b03250b849415021239042c03000305042e2607a00c3c1424001c0c400b24a0b424408a1011070150740589002141841580c12000000e89d002c444d90304001d9071622013400a209000500c200ba03410507606612426021349036100703148180343d136445a031900901034000e1401c00743c180322456054440945103031f0024850300c038032034402c0e0801d02a5005200540e00440368520218940b0b44519821036034000c040314840915801000610004000251441441040045801000c4e40305070100ca07211911082c01c14140180ba880072121280909180e2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 150930530 1250 150929280 150929287
    0x2060a1d0c040c0203040308040b030f01080607021e1e030d0605030601060914061b06010e1f05040c050f19140c1504020a0909032303100308090409080309160902 71
    0x40300404a00090601e0066501060700001480101c5c03951203160700c050b221f084c005c900400e004040b000214040c0c001c14407180078598803200c0032920350005440010142e031044810714000c1200301c0300440307825040740c156070013461102c1042001c00000c926005040d04006042c025800e9144241006018180c0040170150704000001e0804080781c010300c3c454114803170130b01c0a941d4402003111040203080c0403000b41600b0740001c043d42c1d0790081c0101c1241e00078480004484480626060b4018000c0e0081d8401c500c0c94902400001e14000500f801080b800300100344100012200078680e4040c101d607520f0386101c282034000c01c0c4a4040c20700c0c83e422a030820044a5016000070400d100c143c01841d15403603a1600c3c40090342d40c080329480718000d541801c0400703051580044c02c1101000c0910095407103502e4600c1c2c0300c2c14500c4100c0d40b080481c05004400c0c80480d11001c003515005d24003030b000040d280d00c15264852150030407144581241d0000c07035240b400c02c070500009802000c004505508 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 150931780 1250 150930530 150930581
    0xf0d0c02010b01170405031b031b0c01170a0914061605040b04060e0406050a171005040f0b0a1e0b010e01021b060a0905090106030606111c031a090702060a 68
    0x11a04c440b014a400c80200001040034424144100c90b030b43c60104040e035102103044114182c80b0b410040006000015082014450741004560f0202c0128141e49400140d11940c07202403140101411441c5160340e0703812081e0000740d078032041c484403500403001080345103000a25420505000d20740c6104200703040c00100300016800b8191000c1d20040d04010361070390b41e1980410018007403079001551052959100007141e4030b0407800d00100c0818081550031001c2800e1195040c0c4406a0700184480c130015034120200b070344502c069400c01050000400c0c009915805c2400c003800e100c441c01e40599442541041e80e42c0c00801e00302c17142d0001e0001e042c041c00c0c2070b01c951071200310068010b8002c940004910031260710810240000d410700500d000c98030358503910300a0040c2510301900c0301103038290f01d2a0f15a40c0e00020304080c0c0d502c1f10014901c803085609000c60180c41c10b000303000c4d5080c01c0100ad1070460755494513011b00c903642a0340100713842c0c41c1112032641520010200c221008009011a01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 150933030 1250 150931780 150931787
    0x1c0206060d11150d0e0f0703141002040e01051206040b01060e0d020301140a110f030712110712080a020903071e0305190303140717100b0f0d0c02010b01 67
    0xa40c800001c94458001007100c1c145000590350a40c030007544100b121920826038120719001c0c18440c010424100261310b0301584140e603c0c40f070840550700992018408000050300310032600071488552050300c1203c000d84111009030b8010350403012030881041e00500c1141400b00288401a40400051000e41000e40f0b0700b641401042c01005c0402104d00d20414481d11540c00e40140c140d8050020444404180c01c0003550402c02d5600c09141820f04280e07901c9808688280c40c0c03030f504694005495030300e9608082d2812000c06680811081e00c81c110b00c0c210f0842c0001500f403042c018504074002e02140f420060903004010000c2944d944140004100b5441c002070650030354207038031a03490408512401c59105500e8030790005245201d00401c2e01c4000e0b5060f054500d000748645c80a020f20804280300a483d49003c4034803c000034162200c100b0352040106440c1d0f04108102e0200c02003649658a060280e884016240c00c4950001040c00c9010301c00d114447c1c0034407061008025034400400000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 150934280 1250 150933030 150933043
    0xa020105061507170906070f38092e050601030501080d1202160c0303020c0108190c03140901091406070903081b1c0f080c0f0c190305040302031c02 65
    0x2c3c0140c01e80300035482e844e0a40030100d4070001c800900d000e40fa4000340c6072042000c040d0080803601c0c0001c01d122200e0805401c24042c07030304101500c1d1a0b116100c5403509075260800280320140394451142e4a180040310303003d0714090142d10314038000003100d408440300b094580181a05041505e03210040115240c0421000d030454940e103440300441e140c2102039000b80c01240558080e42d011140361008215100070f112044920a4090b50074003110070780151140c0004541000d52410b954880244207500c0d5400241108183d08000a5880d82506143d50701001202c1130200da85d580c04402090000d14400d078801100260020034991170820380c01009101507106c028003030030010941049a0041c03402c840309044900301103c0340c0c99105c103165105400c2070f031780031008201c4a843c044005407048190610402c1c0c0c1340c0c401894907401c040c0c030362071030b9000707001d034010601448009046045a40d00702c80c166500a80d030f07294480e03065004040c100f01c08252201e102c941250000c584598010441 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 150935530 1250 150934280 150934283
    0x180307061218140f15090601061440081b060d02030901090201030c021b130e2b0503010f060c020402040302090702060f09010618090816030201020a020105061507 71
    0x20079040c031260319007407900030b003644010a034018012070041c000c0c1c00042d10044813000c1900700c1c2d0103207503a03a120381003264083e12246d071190451001409014002c002018003c0c900d01e03003c1d07103400e41c1003440701020820914102e101d03100c01440d41652441040003945840b44010124121030304e00440c1036554400c0480c994185518540030f0825580c4c2c0c001607900c3c0d210719030415940c9140102c0454002d01381c81030101e01080c5003000c4030541c90710000d252040500405a8040840e018104001c2c1001c6c00c0716900d507402d62210860008150300340700c031000d2801040c128841228600103c0314940c10015155400c0100c280010400b4030a15440c100403074940b81083c02c503da59500207d4003a2080e90400b81d000381c10750007402071180d0b001038032500c2031a641c4451101c40d250460042e080c0c40040c82920141c0400302240791003400c00c2c0c0d0065030b5640c410b002c0a0700d403902d001c604c1109112800410b07009030350f010aa6003c50342e028007996034004d0045801c9009100454400a42402500310 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 150936780 1250 150935530 150935567
    0x11808061803040305190203100204030b040609240509060117060c0c1c211b030510030b09030c0d050324010309080d061703040b030c0a0e090a0218030706 68
    0x1481c0381c1c6141c060049401840c1c1010076540181c000031a860b40601024008034000d00c9001400140d5905605c02e883c290f070380c40644c84609031075607110702c4050314042005680e820310400d0703054054011078490349514940c0d00808145468999903142c1040b005a200030103901a240107041220070104006a105110484560302c039040d04008a2070030444040030260445101d4428110300e402001183c1c25140403035035000300c4a602d070342c18801d884101035041c0c40101000000402c440c001d070022a0712002c170201d02006607560740c903103120441c411b44028006401c00180c40760120424018040399000b54145603156040a41c40b41c012200e80c1c20110b060070001208038102c583c805d070401441d00d60403201c50743c2c0b921740b6a454034000300071382d00c100c1034204058680c111316440c0c0482520100d0306148078180c199a9040000403087c0d100a03a51420010781100b0120140e81e03490106005910070b00c00141c455281314094010302c50b076500c1c601d209501c4140104210750b407000020503410b52040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 150938030 1250 150936780 150936811
    0xe0a140a02210c030303010906090506040b01050a030f0b090717130b01050f0607061a210c0139020406050d02090606250807020405010f030305180109030602120601180806 75
    0x10b01d402c2040a0803082e6040c0000000055107410a0300f010b821740b8601d280400207500c42000b00011221b543c020749010980600c03440822a010381d000c1040f0b541560008149040342000048406200315080e5000c203c68010b00e003007401c500d00304e42c0c1e4451580e8111820096164881e1a41a441403054030310070a00a000c858894545005803404158421018080720700c2030403a40301401548000c49000381c00c000d070401444a407241c04004404004005030090f1002c001c0115510340708180f00c2c0d64400c0001d0380f144103607038082d0302450b43d41424048905801c00d8520401c41071b40d1703156025500c90b40c07000d1007107009a5a51402c040e0000022a40c50740d50700c030700c0d1216854180d81601c040030310490f00d00e03820040c0075803030b07004003c0c8510807102040a6a281c24100400e2407042c000980010800d0014400b903070400b07901a2441503050400450b902e07640e0350f84105a03849613103a40c404440c0c5409215181d41c00c441d00702c1000d409c0303904c1100c88900b0a601c0581c2d442000307100e20310030380032507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 150939280 1250 150938030 150938089
    0x305030c03031e3306030a0c260f0606130909021809100e0f07030503040503012f0c0c040623010311071118010806160801150f120e0a140a02 62
    0x100c0d641c13001c502c09401680c50f441d15022543c000c2c89201e80d80c002140813000349044c0d1034142081005400100b081210309921401414103010500420064001034100b01c004840d40d009600f4400a109403040801c0060315481030000b40740c802416000c07400345002c14001201404100c410900042c2d0030000349500700d040d012803a00c04003000c089164003840c040030050080200040050b200141c0091040440c401001c00c40c0020403802d000e1600054181c0c0b640313195003500280501d03c3c0c2c007021500354010410014080380c000d5849a009110311403400c04500c90008602403040c2d0007401c042001025071012500303903218030701c0010a0400c00c03500e925810707592215001e00e007000e900885145580c4034582c0e26591441592162001c2c00c0d1480c03040300c100d10600d0480d040e203003000301407a500d03104d00d14140d0303040304141c1180703060282e200d00f405a08032003481000189c0c04072400510f015480ba04100e0600303a550301d0f58020b90740040840d80d0158a94245001039550308801501d50803012 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 150940530 1250 150939280 150939361
    0x204050d031b060606020c04110301030b010308131a0301030320030d09080d020304060903021605030703020105030901020c16060e0a050f090c0408010c0806040c081e0603070305030c03031e 83
    0x1000001c03d6546000c0e00031610680c002601c0721024010384080000c0c901d629411840d0b400240b04c001e1105071000f00520015081201611248855442c0c2600ba69140d00d00f21041e9022401d009032000008001007050591000d0b00c11114114030300046540c0d01841b02d215124411030000ca4a05512001c5040070800420700301c48510701c0b50a800c41d2203041c10724104025028a001c2640140300f01c510024940030100031a81c100c50b0002c009018081c510ba0041d500d6810003003030005155400c1c00104450b01e424000c20284107101d0030100013103400c02001030151040247d00e07902640c0107543c00d00c466218483e010a50301012903405903160388031070340c1803490300c1150020030031542000c0c130040c404c0c1d4121a10902400702210107129864100f02c088483c21000c0700c050488103030701c1c0705545001d0740044100b5000711028040d5071207142c0b07035215030b8a5640803c5040d83c0a900000401400c400c034a001010010104085810720f8206114480c100c04408043c203007c1190039414840b10886 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 150941780 1250 150940530 150940577
    0xa0f030c09050409050d030b03150a0b0a0915090c0201201803190605010e060306070e240408070b04030c0b030a18120f020303091b0d081209100204050d03 68
    0x20001d01c14800e03e03d0b2172501941b00c0c8901c885540100b418000340c40d0a515010403001310f41c440340b4407008000d41d00d0389914805001d02c2070341290003122409022603c080c0c0782c06065800074880c00074040b000e107000c540e8000c483c0440e00c0181107924080d6401080c403100000d6882c81c03c44044000e4403025925840b954107880340f080e0780d41c9482140e8161580306654aa0100710601601040080c0ea0342c0d1191248905803c98800307030301d17400080002d051240140364181d120361019203204c0c0340e1005c035a840d884080b201c4015010180b80814100b00d41c540400240020b00744140c0b842e1b04261459940c181000c5140c06501c0c2842c0002c0000fa0610742d0680c0024880310501c80e0800780f0340e14900b82000340d80d2030019105c000905100b13040100c80d0002044a0290010f40000c0c106c1100c02d48090002010510440e030340440c00721140000706e94407102a200d02ca4055010180c02e04215014515001d400d0304801d050070b0041c0402c1003683d442c1e0030000b40d441c0d01400e1154507204585c1d118400c503035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 150943030 1250 150941780 150941789
    0x405010c112806031404020f0603040c0503030a020f19050a0803151e040c0819020c0a02150a02060906010e070509010509040f0204150318020103020a0c0803010e07140a0f030c09 78
    0x103042c1040ba01482c500c106104a07001a141080000d0101c460a00c003503d00700d07006134019140d54144040b0f0b06141004580c00750151201c104520340300d0700064103640c0301101d60340c011ba200314122400300c00c080c40400c8016201e4841e00d82c2c00b1a1560f10140c46040c00100a0300080c008400200c0c1702c2f8403c211410301d084018114451460341da80e01403a4102141c1140d8022403400140721146800703070340a28050002d001a9009480c00040480c001e0f6000055000c014086c0c2901b030300058494041704650b9400100c04140c603100882c00081c034080f40200b1440381940403000400424810280868000400c0c0c40d1003a81d840c0e8510050380c0e18800e4503403250b0003502e09000d85045003c00c0d409403007510340c1c01c000780130300c0442c44034101d007030707451000780e6401c00f076030b001d0f0240015030090380200452040e9003401e40c00d91407070361183c01302d54000343d024080300b004100400001c550703c803e904030003950030f000150624a2060005203001d01010944007410380d00c480d19240540107800217002803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 150944280 1250 150943030 150943069
    0x31605060a1107081005010e060d021302070c090207051203070c0b070e1c03020606040b0a050f0307050d08030a0c14030601030b15040906080606030a020102100906060b040902120c0405010c11 84
    0xc030b0ba150085640d4440117524001c0c81480e0800121b61640c80d00c0c0400d0103917000401156032a402c1d07408004a410f032003426200d01030347c03c005007400581100e010700004c1002e41001030315080b03181001c0e401c2c904100344188680c0c03020802c00944907088451011855082006004a9924000f06a400500843c0c045500c40f0844902504a26000d07c40e080c01a12036070076100591111020300040e107101d240601c0c0d00c00d00505040c442802d0103240a8444c480003000c49038000da80d0004281400c00d12001550400310010800a56440c1c0d030203640c08029071440c094001d0070862400c0c00140c08084e0446040580743d10400071075694000301c006194081d110800d031f41d6551081c0d5440145010301c40e100140c001c41001a00310320780403590380c131141e03010703000b5013600341c0c2020003c0003c0c05440412581d09940700d03408552903803000058030240151000c010398070b0032442451154040006c0040034800300c100024401079a21914900762a58000419041e07000c00e040000d0010680c0480807109 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 150945530 1250 150944280 150944293
    0x121803070b040e07030e010501080304090e010605060304031d01080c040e0711030f09041407020a080a020a080d0f1a0a1205030706050f010f09110a050901110f0102031005031605060a11 81
    0x7520f1a10100c0c0c00b0300c000752010820141440b00301426940244600c0f21141c10511042103a043c46401101c0201140c03000010503580380c00010341c89800039a4250300148108003001c3c0010311481d08034030140c0c02420440d045281124155545200314080c01074544420f00209041d240034445030344850701000182d079112005e8082600c0c80d40c100f000403512441c10b0090780003c8880d91007005014007600e41c042c1441c4456600c640640790f0000d680d1500b188103404207880851501000380542072240b060201d01020040c0014050303d4030810211101c50340b1f0f026400071643c44250030b0042700c040100c41200600681003103815070151140142c010303402c100c10024402030340da80c4d26041e5100c900406403001c2d295508a01243d60842e05000054001c00884901e00c1c00f50008e0104480b05141c84400910813a00240c10031000c00e1000c10710369004002d0001c07040041200c803014040a07001484070314001290000c0c4003d80f481018000d407400130341510013502c6129540101800c0304111280b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 150946780 1250 150945530 150945539
    0x110a0303050309160b072a06020102030703060e1510020c150304030201050106022a0d05030d06090c03021c0f020403080414040506060910110f15010314121803070b04 73
    0x10b40c0b0032181250715015108507120302902c841031500546160212840c1490084e0b55282d040303a0b00d54812044950311041220700359038040d2505400385c101c542c005070312810301039009825500103030042d082c1d1540301002c210314412400c28070001c012045420b2550040ca8041c16400c000443e1400c42c0c11000008184414100884c003c50065100380d00820060f0ba99000c01c07a294001d07080204240032984010184064200e0520360000c20700030192628410560b46441c03541d8001071165181c21744034441080700300e1f10f42c03082242207a41030406611b011034100c0345600b110f485131000700c011a43c42c00307803421140069066070702940d480052265210740355075000c005440d000700c00c580f14504000000303040b402c1a009440c00450003829004850a0380a002d80c0d41e00c0300710705500518440c41680400c010340400480440307032542c50f03000c1c07455419424001c8142a20300c3d4095590b5100030790b6481d80301d5080c4116141c40710f0070104070307102980c0c000c000390030081e03950321501d00c4003004a000709 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 150948030 1250 150946780 150946787
    0x41a0d0501021b0601060801030b0604110d1416140d0209040e1b0103140c0c0a120c11030102070302030a05070507090f020a1101060b0306040e010e0a111305060603040807110a0303 79
    0x140004010b00303807000e0f02c0341811041d903450409026030b200007070b5104010000114080c100a80007c0c00420100f00c81d004e0b0381c0d607085150800c060202020782c48204440c6444401c0786400d03040a4407100801911300f08038005401c4081c46000c2c46c4003443c0014104228207a658161042003100070000c0c000300320b908602c00d607201688144108421500d034404183ea60092041e07648240011100c6039290352100c010600e6070300510040d4503180101101440083c11140300352900030900e0302d80300060b40550501c1d80c82254a8000d6030b0080e80704003c0700c00801d400000381c0300b10780d04078a040750f07541e400343c5082070034011160b00c64a07a031350a0000c10000c0c43c019401a101440c1d0503901c000e0300072003800f025421b0303400920031030320044020000b20308a0304042e0001072031240107800209182590605130352901ca074540068910028040c0c4d022081e24210002a032407440d07128080c8401d0500e0340000e81c0c2440007400041008130000b0f5801c7c200721007600d0140c0413032801040c681c0010703644d04020303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 150949280 1250 150948030 150948037
    0x10c110310020307140403030c030c030201090b090706030b0303030609150102120703030f050a090c14010c1e03020d02060f010b0a0c0803070f1209030504030611091c0b0a090201020c041a0d050102 86
    0x244003081040051742c2c9150b50f9002543c044a030503548654100c9026182a2022901c11405408554075800c18401082c1042e80c10360241da07400d4028501189000307030007400c850304c140e420352207500204188507495032900b80c42038100c19103c01c9501282c0392480182d2401241c000d081c1c01c5d402c400729000341403540541c40b43c0800c44c900310041c0701c0d0365600303248041200d0070400000c2205e54001000d0006124202d41c2c5040c885040c1072048518407140c442c004c40c041480b440c1c102007008603005e10b04256050100580610203800100741504000410401c0c0d80c905000704505120040758a1510301d100b800404102c1d50011031240d541d042c6204014025100d109481021600c3d40051070054480380c8a08100580c0548c1d65501f090b086a541c400501030303840001e201c5030424482078540380e441a90004d2080d03a1050200c588600c0742c86d10003440e00009246000c001d243c1503560380980d801017260140c90034100c500182c068003c40e0b21041c0f1202c0031402c0ba4001480c14020f0b07041040540c0107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 150950530 1250 150949280 150949291
    0x180c090b0103061a07030e0114030708060604050a0902031006050301030b070509010c0209041407080303090c010e0301140f0f06062104061d0a031404060e0d080c010207030e040c030e0309010c1103100203 89
    0x15002102014801962700c248030200e4032500c0401040081c036980d20496180e42c00c51401811245084d543da00090000b00b200e4100600d0305500000f4440d030b540d24910b40800622907030418038110345c51510b40c1c100c40c1038001c0a150034000e00107281a00c5a02c250022440107600404400c02800c06040c5450522404261024a4400c2e0400400c03451000001d5912500e05000209244000c1c140112024149038500310380540d251180b9204401c84000c0c9680320f0703a256041848946400620541e040a024044501550f000c00001d03800c85040c42d20b41d0080c0032a074040300e003251a070b480d100b401400300240171200381c401c0d440070140d50f50001c00c080b800140070313550300c10411b0030010b0046070030f10440c828030380030400c1a4050328690030300201c1001c044d400303800340703600306480601285d003a64010389046000400340391101059260521400c1103000c00d501e820099110041310950342d9104000d0014144003810741d156007045041802420040700281c2556005000d8400c2d80020750001d40f003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 150951780 1250 150950530 150950537
    0x315060f09030c1504090e03040806041a010f0f0902031f030501020307020c0303030105100e0a170703150c0906031109040e0d170f0601120b091003030201180c090b0103061a0703 78
    0x4024118034104d40c2102d40c22068010781c5141616044122000300608200700703440d80018000054001007c0c000c00f441540148a0003140242c120b041c1c001c4030305d05800146031041014014800c2400d004c2141040c2c801e92600141d49880300c4000c50194540d0b58200600d68140301008020404190080d6000752090307000c50f0720300c11010081645070b000901131300c0d070040301040d042d1128622600b90000302c044042d0542d54400e48900e40000861000010300e840c0d50301c00b01c003c00404c581009915081e8080d00002c01001038a440024685901c2d403103003034201a181e0044c4a080c0400104660084000510400c0414440c2806c113446803a0442d04030089075150310b0003407840081c0314405200e0244c1e850782d1111170351178000558803c2c4404181400c1c50741d658280b9407a9861b40882940101545640c0454a906e0b514009013034500ca42205040c401c0e00600010015242800d2202503031107051007c1907100d214001200181404e070b00210f2541040100148203040e00802440c00c82d00a030f5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 150953030 1250 150951780 150951793
    0xc07051509030c040f09020604080c0a0501050a08061e100801031506080601030b09191a010b04080c121501030c03060b010e0112020d110c07091b050f0315060f0903 72
    0x14151403003030084502041d0503410207040301e03a40707203001d5000501c800461000050a002c05401040880d0400d800c180010303030140280041c0740c1f403d0302a100c024042485d040b4607001d440e100080c0b00b054082c1c40280141c01d02111900380c11030070a02401541c0c1c010f003480e04601c410b420b00400317904c02071100b5600c0d41c0c4030f07101140905615010341d6003551070400041c007450f40785640e41042400c1c0180711030340500460a041c1284416010780481c0345006a208078a203e8620b03900ca1010101a4040d65000c1c00c02c0000300984080801d552206800c00c46c1e4000307079035091080950404812080041d003d002a0001000700800b01d8400002c3d80c0c001c0e01c04104690300c000042d80e0000402e000140880c50960009010800ca900101044c100f09500441e86146a005a50b5107420403030f2040078a4001c54003d0042403914440d139003d250344540404e072074005d100000303404c0b84690b034290441010300100207034201116a40c1c0f1201e410000d0241940e42c03d050305014840c0d00042c072100d200b40603d5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 150954280 1250 150953030 150953059
    0x90903180a030f081e070b01050310050403090b0c010207080a1e050906120c0904050702100c140412140f1b030c0f0f0d081204060b0a0806010e071101020c0705 70
    0x881824064aa000f001c1d18030540d0103032141d14058000103001180070f0740460f1042d140c03040340c034080c00241e48940e8404501d541894205402c180043c0001903a1500d040e08001c0820350085610048480710403103076544d40c10742041c05001e03100f40341c40a0003207000000c0f0481da09603c0b01c080c10116550301c1409a450740c40c00002c031018410689e07076a51006040c40111010550b10031155044085190f010346000d5500e0049400d0311070844150002d070f0041c4602d41190a042d011381c200c0050309103080d542c6100300e445e080d00c45014a0003404a06142d50440d01d040100b9943c50001141141046800c8014442015540c031030444044941c0e000c11014540b28a050000e60b40070030a4005040303184440000082c8100b81002d50b0100b07500801d6900036101040c400e43c028180e880e4841d03901c0009103042c0c18108151611401003e009460030300042107000c00208859065403000c111540d415181c082c800c40c0c02d45900f98002040d944002108885800001004422036005460a03058150b85 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 150955530 1250 150954280 150954289
    0xb1206060a0501081e0a060909060c1206120b04050705090103080a090608011203110c041109040e06040305030c1e0a0f090e150d0213051006020105240909070509090318 74
    0x1640d10001e51708070b000342d0200e0303101c0d40003032940c2c04041c2d00e0001400c9641e401100c02507911400b81603814a41c0c030601d50706642d1b4000c80740003100440c03003424054680390401c42110309004500c041d040080400108080040c00d01441c001010010440a5196140d00b40b5207210340c407e0b502107001c81d00d03502c00020824003c090450407212010260645000709445c241d4005902c40068170340c034003801200181a075602c1c403880c11901b034101d40003500c541c00d050621040b111007034220403840d80010100400207910904032544054144010740c1c60301440351000d410211a90940855150f0214428002d0795000000c035003240b030315594a160040e0303520b40c1c051171414160f903d81d4a000c501403900c0745d10704080d90490100c1e48041d000407601400300351084102e03003041e1601207040507d8802000500c0e824002d036a0046054820b0b0f0800c512500583c810074245040414015400203000900c80c02013401114014203025010741070030f250203d443c50f141d610180c0c281c00500c0002540d041c06081 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 150956780 1250 150955530 150955547
    0x909031e03230403020708030406180905041211070503100903080a061809150f1d150115050d1a1e241303050a020a0b0c0d050d0b1206060a0501 63
    0x4030950050080020510402c128140080c020b40541c41140700000d8100f80400040c4020552552040030f000750101908072180c00300d50181d44218100010320000c12400c0c3c02c200b54601d4141071a00100c580c28003228241b03143c907804268503020320b0b900c1c250005001d800c000300b4140310360b4400d0703d1542c4962404003240e80702d02070b45802d0b0100006e10448000c1c0d507804886824042c90103c25080c08200604060b070ba111001c016000e5100c0608000b92026089a00120000d40000c1c10308180704440c1c2c80c80707069051044c0c822a0400c800c1d5428218010070460710800416201813050003c2d044c900440a0020040e030303800f032090740c0a40000d03014100811014900002c00b01c94002204040100d21114615403402a4820070460601d880c4184da06400045104001402d40742580d4010081002c8007079100343c1725480204040a400000400c05191f5002740f420219101c0314009000f42c010184510642c0e00040411295004a94001070b118400c01c012102580240d1b250b800442c2e8110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 150958030 1250 150956780 150956801
    0xe0606160305030c070f1103010e0f06040204020d021204030305160c0b04060506030f03161205031e0712020d02030108120f03070c0f06110909070207050a05060d060909031e03 77
    0x140303541285400a88030b200190741041c10080b0307032402c00c40182c6030003840300344c4554211020301140014070100c4c1402c0c091031940b130030b546d0050129890032525240e1180301c02003000344036a6000414030712200c415030648035180034a1092490b41d1400303103400340c000d04083e42c1e0819030019411a00420611908203003411b03070b500c00072003481926030b603076124082c21000e40420340c140102403095131440e90400280c520114001e601c400c208109080000c0b46c00c00d0550550304205c01003040090410614011044003003005007a4440d95503880000c0715481c103905e4802c100240002042106001ca6401450607606802c0c1590100008a81528920700c6540842c04078600184001040640510f041031041c80c0540700f0445904040d68494040b6102c5440704803100001041c21032042c20020710856005155000400409060400244904640388207841c46030b04005145070b2140c02940201c001843c0710076061040a00c545000f0704010f859507610010450500b06100e4480d210f07008014000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 150959280 1250 150958030 150958057
    0xf090907030b0a09140a0309060c03081305010f02031608010504020414060d0209090a0903030b0d171615020301030302150c0d02030603031308060114010302040f0b2b02040e0606 78
    0x49246503908101c10000411070030141340c0c0c9403c2c09010840503e03503a0840250b040103014181c619240103485500705030084803c2001050451000035007018910f6040307030689000f02e0300588185405405010000a0006070034004024450149100030310351002c00d280e92210040d5030780b00c1050100300d0266110380c05440cbc00a0481900c0e60403d4001001c48892503800549424900c4001c00e442400070fa440000031503a503184a0145940351007270b000c45800c03c0350548800001a118512803110242c1035180b0450b00252a0465004001c0d0f0b460245502115910a80041e145004002e401c2440107401600440031240c25100000d6042031013130f0084030710a8248201450508001d41009150f2901403004001c4c400e04002401c0030603000f0186880149500d40c1231411058542000c15291814540144411700c0f0410540e4104000d8541d10841a86c41c1c980d000c42d004080c100d5020000341c40403100c0c1c4001c0310102030b50010400d9130310307018107120076032100014007049100f56030010140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 150960530 1250 150959280 150959293
    0xd0809070b09120105010b0417010506031f140405030307080c0a020a0b0c0d090606050a090b01020a020d0309031a010f060f050a030507030608010c030902030d03090c0b0304020102100606020c0f0909 87
    0x500e2041d029020460028000443c1120003080c140d08480080e00507102448011a04020406115540d02100c804c200c00030300c0345013008000b20750340d2142c0304050303000d2010320721052071003a40319800915000c0005c03120160a01b06800d04980702da0040e645100054034410000c1c0e4078400b031808036801880c099004005680e01900c50a02641014001000c032030401c01003000c035080c05004012079980215000140c0038540810800c0b03500a81d03114460042c1000300c404100e81c0c0200d12a800e01d901550451f050016616049480d01c0d81900010105005034440040c031140d0400818140c500160007049070a4071100300740d600040c1e9405203000180704100e0010f1092198018030b0700202241400b01e126500e44100ea420b480c80a014800000c0e40c0d6842001540b41c00c10000341c0524003401c003000b0459080c0c940c0341c2205518043d81000d080d001000c901164806c20042e49080611041003014540b5103000035142d50718220b00c0d034807581074a241070101d450807414450150705068001c041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 150961780 1250 150960530 150960539
    0x30309090e1e030a0e01021b06030a06030f050a0303150f090b1f021b0a080c01080711060106090311090f060d0203011b020c0117010509040305030a090609080c0d080907 74
    0x9810601c41e441c000d80603002e400c5803800c4000b214507209281240185442e1003403440f00034442003034084803504552140d290410428500c040139820100140c64881d030700d96078400c402e070242a2980c4000e0196002019800c04e00201203074118035503200703580600070250b045a10895081c1075020348201a1106201041010499880114118005440c108200140f1944c8140b020381181014000d6085110300105565403841c001c41c11303807800c40e14030b140c890800c0181d0359903941500309a81849040e00202d04198010b1156025150b2030034200e030711541e1190001401c10280344000c6030f0f40d03581000510802c0ca4038401c0c50f80305d44420030380304020790303200d00410110062145017a43c05d0355881254408140c041007407811520959001008002049800100410905d45020006032607400040c1310b5580d525005642003905485c080b51039498100946000303080c5e06000519079460031900e0010400102c014150000c02d040a50f06104244101504c043e4000c460301812a00000418003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 150963030 1250 150961780 150961799
    0x30c09040614090d090918030327051606030b0d06050601050d02040e06240a0f0e04020a0806040c1704020913080d020304020a0504020a0e09090c04060e0612010501030309 75
    0x6521500501e004100103040c00400706030140191010405034200101901c0c44e144c112080300b000301468070041220050040045201c0e103100e070f00c007c0405d41c95800f00f28040c1c4c005c10240414003044581441038500d01d1400d00d95400e0300c078028115103512a400024614068407070912031020140030030005246503a5510018400100300d2414410240424441e400301480940041d01030780c1042d000c2820700f2000c0000240503d1890441285100f07802c040c5412583d06544c410082030a04001c0110b40d410301f982c07a280141c000316005071003c250034150940c0401d4250284d0070940d01001000d00317032001200d00d070100000c1000040002c502040041c00e0240f01240e00490424022030150302a83d58000141c0c0310704008484039030003105010640c58500c001c0c200800c0c080301c0461401600c0d481c0600241401c40301c05100702c0c0d9940008282c01814400080e01c2c440040c801c111135a20359801c05250034080e180680515000040e40b60050014401c681c180c9401d9200d406d0490f15085240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 150964280 1250 150963030 150963049
    0x131e2c041b12230a020a031b0306020c01020703030c23031503030c0a0b010518071107030209190501080c061903061d070f030c050a03110702090406090c080705030c 72
    0x22100c01862400010b2a819002a24030480e8440d804507401161040c1c00000b1510b943d406100321a00004141001039a50700c000400300c903405501c40001a0380811310030070641080e03201510f090300000c0e407115181c070194020103030107200e030300c003081179124200c1c003110010080700001e1040c55010300707a01e03641048c0402440d40b2003c0f140f80040c0d41e4412a011a08540100448a609130302c0203c0601c00c2203080700c0d41c1070141006540a8818034a1000c03140e0724520046c210505001e00490815401c4a060000401940d000f411a000310304007900980788240c1d101c41d0210080e0315060000c40e1011000c41c00c0201c0f158000e09207400d00481d1300b00160300c0c81010f466401415960070002840d00f001d008c0348040c0762088001c146462400110103006110103000d00c60425240020020310503400c007040c0c1d6030a5045260008a034481400313000554464820f0281d40070308004200005c00c000d58001d658103d11426070114480c0d82ca0240581c1c0300881d015040d81908204c01422007410201081c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 150965530 1250 150964280 150964313
    0x60f0d060213090203070f021c0c140f060a0b060403050304031725060b04090302120c0111040b031f060804031d090a09021c080708131e2c04 62
    0x500d00a5002c1e10203100440940c0a0701d410b075004000c025215800040d41c007a50f1103680060011461445007246e041d200311500602800301518560050081d02c0300d039000d400a07000e080380c942041d41c640050350b5180444410a0850500200400340d0a0200988003145e070b03c40011801d2500716a509082c03040d02903a2224492001e00502554841c00e00312805144070400ca034542040c1d40e41400740a40d80b0081c141c034051410031a0b03400019600141c00c41060410700c02c41d40e12482d421264901400c030003222403000d01c4001c076000c21000000c400441c043c04091881210424880f0307a0088048900c1c071544021680702d500240c042401402401104072941003403070108502900011113a41c000d89103012665034403480c82007103003000e40c1400014581c082d10000d42c101a40d44100d9984950714000b011000c0215611820014100e0000c02801d6054144261035644950369854242d4611441650b9141111401480e4140d02c10100418002014200146da00c9880d400f0414851820 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 150966780 1250 150965530 150965543
    0x1219140a2c3a06060303090605070812070216060915030c2304050d110108010b0f1e04050301090312050a06060c02010e030c041d0c120c12010e0607080702010e06060f0d 74
    0x400b49611006030301c10030903a4418800044d0b1242541401446072806410007414031108000c8413001ca41c2c0c10081d2000c1032000d4240740000d940740c010032401c1c0046407282801d81d6000002c0880d50715000490501030740c000d00400030082002c2c071001c40980720090059004640042e052185000c030002d03d4104a10f80d440070245000d9580001c1051258003200655540381c1104414080790f0384802c48500402802c100a030070448100d19001d110b00c5400e150a80c4803e40c404445c0e85168500c1c180e03802003034020001c0040e00c066040c0904111a46800400301c98a0540092000a070b6803080c0026200c0947d50140d0081060b80195407124401c815035078117200d4a905841c41d50303500e01403d2a0618a0050320071a0030043d140c02c1c1c50b00078085881445206000240e80c1e85103000510041d091070112242c04010044080c05801444292841002d9010f01c00820190f42d0f00900f155000301e100d54000c100e0a4100d681e0942c880c103096030195401841c0d224000d603a454101082022030707003c0e80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 150968030 1250 150966780 150966859
    0xf080714070c08160302060301060c03120e030316050a020c090601030e0f010e070501080f060402070f061103040b06011d060315040905100507021219140a2c 69
    0x50080503420a1400b22401c1068010911a04005109620101c039090141400d001d00b1030340002c40354001401200e0400080300c482005142c81030024481c0c0d070040b00e00401100042001305600d80c1cac41210203049550b00c0c03014242e0510300c0340c81101c0450341e403613002d450390207084400c0011071100544640d04141e184c40003038000c10003e003c0040c040e2500000007074203a1910a805003041c285901080c1030000110401011902d2489116886281140d006951304c20a14203d80b002c0e06038400a8041c0380750007408d041e400044401075018a010303244011107980c401e801140d2000007040001c0003041000d1b1511081d042c814040c50300b140745440300c2c0c03401d46078110108007240c400c04000c1e101035201164030700c41080603100301900700c149840507040d84907101b82000754500c00e000301103a2041101c01c100513401c0c40740c3c58900306051240c2c001a030b25602c450b401016a498140f04403880e91400403401d4a084060500c64044500a01035008900c0d5031030340560405c0242c01c0152200c8602d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 150969280 1250 150968030 150968057
    0x11010e06030f010501020705040c1704020102070f0618090e0316020303040503011e0c0306270209180a05070504080a081308060103030503100e1003060b130f0608120a0f0807 76
    0xc0207140309440d03112080e0020341c50034000a02e403604581c81503005620700014420309552200146009035516100c1844d9500c1764070040f4540000e039405080b00c0000850080380311f580c031078000700c800c1ca00ca0440c1c3c030896442c4c00e000000c0300c1082c429824a80d00c1003080000056041a09580703c0e0f00080c00d90b4140f40e035540c0070900303440c009040c6d1582003c140c1440b0007429902c5c07080407034140581c641049114140161361141800b0482020050001d0251102c0c1c002e900380c0445c0c824800103031107401c1d081d0b00d004030781300b0881060318000c1400341414000360009201c0c800b030790102c809182c0204103410950721611800c0e44015807040004001080200b8000e50400c140d90003103100b55902560b0345020164011510929002000290303004030910081c0c0a020103400c0549030441f03070000342d035151701c400a1054407980c102226850708002c60030f0840d031142d6220ba412180c3d1481554000113900c5030f56155486154012400708034170340401011144107012895015a95003401106a60031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 150970530 1250 150969280 150969289
    0x15120303011205100507020c090c040b161a040809061608070f0c061107230d03020d0e030109020d060b0a0902160606051909050603010f0f020304030e01081311010e 72
    0x90700800c400b240420081c10402104002080c04060080c038100903605160400940380c1c42c0c1a06810304c140030050100304442c10701c801721002172901c000882d9880403d6500511408280f4105a80006031082c541c071081030300341c400e14820380e806045a07141c034009004211580e0040402800701c05031085541d4006000880104000341c0150001c1c500d00d038036440d0a4068107183e402c207404001855604441c1000700107041c60039039265441c2103544030140140c495125801092403944210038601030b20074140c01280015210b00c09544404050421070300341402d81c0c071001c5d0001d40140f0604880d00105001c0d50104003010b6000300a020641c1d95190b5510030f90700181041005190304a26900400182d0310030b41d0010305055513200980c980c0030000800c0c3c00343c144921402e294917800040c0c0300d03075000c0d88001c400b1a040e0780c08100710942c004442e80207401c211000c0b40410120b404100d640e42c000da103918800c41d0a9100729514450300d075680d01140c280007030240d043c0820b1420340001d9a95 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 150971780 1250 150970530 150970537
    0x405090a020603040b1b07120c0204090204091202062a070501060f030b160e01050304061a0d060e0d09080304061101090c031a011512051506040b04180b09151203 71
    0x1018641c1030b07818409400e0b81c0c2c0e03000d00c00c0c0c2840082000c20034a0000b81e25041002408c207001c0c00c0113454403140c0c0c00842c004d41211040254018580020384081103000240219508030541c04c49000303913284c41d80210141042805902400c4405919030520000040282030304c074803910010820554a03580940c0344411500b00f1200f0344280400c20201d20120485420000c4031031604404019500001801a12000d00060015601d4190103101e80300c0c001080195800043c003840c1070300003e0700b001c400600800c0342c1003800d401441030300000c4070f102e0300c3c6100c10b5403541406503203007034600807040d203943d08483c0641801d55203071900c0b040440c20781c6101500950040d02405201c0c10240030002464005030848002941d040a4000243d0352240c00c20010946070309000500742c6038001e2501c0042560720105611810003d8080340f00301c03204014100700d5103480e041e5001519000340702c40651310b10000c1d50303070040d040b000014150b0074001d002e84200240503000300021341c1d074403403007500395817 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 150973030 1250 150971780 150971783
    0x14030408030a050301030614040c09021b1c020105060a060806010c060b0a030c060f0201270305070219050913031409210102090109321c06061d04110405090a02060304 73
    0x60f0048010030034844240990081c0009058828859103440c0e5107945517086503000d4a40305543c04035540d016202c5455441010403444021a6400c50700c010100d005014005050030040d4240004504107080c4001454140e40c01a203641c030155540340c0044441903106030094441507202e82c50a80c0c2901d40103260006075000300101c0b420f0740d09000c4058a0a41c603241440304683c904000a40004180e02c41401410000706500341500b041e401c04403040e00558402a501c40b140b216042c800c0c440d5002d61104030707103003500c4801207a5510030303010080d603040003000303170102e1030340d041c0c0101c0056150010400c1142c02040c1400c44080c503440da03c5047d100d501002001da50001c2c0c440302540c0c001e50804000d00c15507130b603104580c0070018071145144003024a0301c0d10365a2828503051959030301d00003148600d10b000c443d00000c402407c0c0385d006071201e03100b002040411208a581c440981d2a0303901d109a1b00001200403c1c1403000138000144001462504503000d1401c0d03940c0160345510085015a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 150974280 1250 150973030 150973037
    0x7090908040e0c031017070f090203010807120305090427050109050610080705060309010207020607080d0c08070203070f020f030d11010b1210090c0509040311060a060f0314030408030a 81
    0x1c5003800c1e801450b605001c2d00089604a003842007105603001c8550f504140c1d41000c100800841919203210f02c4c0034919040360348150409100440c00304a5036010b036040714000701c01c8440207a41c0350101c54544418180150000d0010081c00c0c1e030a040c19080200b04e00001d040755804014100c442031219540300e503040f84c40ba51640c0060060001c10040c06802c03c0d10050444401703032424000550f514114400c20b4018080400010401142903040d90301c081d40103000c0c50b5a4071010f14102c0c1e140e070300c101d081c2020240f4040c40e07052a180716098992090505070000e5107404c00c144c1701c4c00c40d1007403d480200e07408652a0180050390310300b486200a201c0c2c29440d5207140e800d802070344609403007072014014040c00d2622200b030b41c48500014181495200108001104800750074200750008007900a0b45e00600c03401c00344010554084aa0384400d2041d0301a5040c2b51070b12500303d015a0010301c1140d900242c8042c0c1480410100201e062429200c00c04a81c40d003a07640f2502421a081038960b040070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 150975530 1250 150974280 150974287
    0x509030a0c0b03090f0d050a030f1b0908070609050f040506040e250b090102030a0f0c12171b030a022203140d02030304050d11010e010501080c0f091909020307090908 73
    0x2100d005c1101902c2c0401d103a0213001e61014009006003180a40c201400815460f401e070182d10802d103034850310107a80c01511544100705100006000d6134610300c907420700c91040810010728107208000400a07102c0051440d55021102c004000290601400c42a406030340c031020a103d83d50300700081c0108510b40852001c411484111421040209500407500d00d0305c200b104803000da80c007004075040846d440c01c111a20030b400346812100390086a00050a08190a9410340c11f96044210b00d190400a1f424064807030b40c41c20a89c2d0428140166071080b9640b050010680740d40403500a845520800001402103810b0102070442808296206036140b000450706500080003c0c400c011042030240029071641c1010741d10550b59150314201e0408021124000000c40c54003904400c4c61882004007d10095840e1540c081c0c54a104981d00e0b8845c04901260308400d040015290380b003520110812004485040101c9018000c00c090480e03040c0643d210111310b0755540c0c402e80020501402d1001d45 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 150976780 1250 150975530 150975541
    0x1403030c0a0c1509031e03090b030f010f08031c02030c0706060b0a0206130c05040c050405030102190f02010c080606090a030c06031b0c0b2e08060405010c030b010f0509030a0c0b03 79
    0xf41a06001c0c0320100865403400740040784000e40d041d90503840c1420100d00d04411400c080310352041d01d42111001c107000205002d164000200042c0c1640d450070000742d10580c0c1d413030310a6620b01c5032091001e500d02d4005445286100030340d000e035611541c80102d140c0390510a641c1c000032103070103400c1140b14502c00700d220f1070815170400c80c1c50750040c080840d0a160440d1a240c01d03000d0b110707920411340318544515050f519a032182c41a1001446c0142c001e6442e800717280400407180020317100e0703400080d015090200c2c005105018040d46100c00d41c42d404903546401d818004071380e014076010340c0c01c4501d0680010018600030b0215000f02132a40e070004002e81c8403078245440208100709242044140300b548000f00b4083d44840e904002007a04411080c1c4c18603c48040074038607c21918a00b12005d1000540c800b0007090003031250348100000c000c83c0401610950454080303200a43c0003030020003400706081d010700028203901800508550203100d41c1c2c0d42d50110b14040d03412602d0070f03520110070f105 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 150978030 1250 150976780 150976799
    0x130608121b01090812060f060c010b2817030714060718030206030f1302090a09050c0303120105011d0301050717060f03101104080f0a050d11071403030c0a0c 69
    0xd0802030300d0003d000040340c50712030b00b84a0040902c1228900da83c080815003e54400942440c1c03400050003003501c8501d0103550500030b1841d00c004600420400195941c941d40c5044500041040807442c0b125403410f2404140340313070340d44915204480c40300300440300101d00d243c420b20025000300d400a00d902c0c0740c0f5500040140003030302403e0707590852034202400141d0b200001e4aa2110400107401582d9480e40c98061f51070900840c0a504a80c040702071103403460f11038000c00482c0b0700443c00c81d0845c00862003403590303030303ca00c041c2400d21040400060043d0361007407220265441e014110700a403540103500190031030b402955034802113a044c804555040b100c01c4845030f4484c0d0101c66003104c5001d5040403039115451401c80b4134140740c1d40c075401111003001a09540c06001404125090002c04055031682c88009000c2a13070740748a80f908000c9035620070030100500b00e42c60b4025001c690314004c1d10420054100d00d0f0940e06010034000180c0710320b410401802c081c0d02a107880e0b162180f929083c2c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 150979280 1250 150978030 150978067
    0x90a03171e040b0409050903070b0a06050307060804020f01030509030c0d170601050903060109110c12030f09030403050a0f030311030708060a090627090c1403010b09070e13060812 79
    0x15000318000b440108019088030042c1d40c02c130b81001c503012807290b4500d00d20030b046100744103004050405030814094003103007aa12a10070f90f0b6003641250580d0b51180019108110103c41c020350102940b05641d80a5100341c001503044003aa00803030382042c50303c8180d907003030032006500301d00050030b07101034130414038140b0201503000b140a00b069454200c15801180d12000140100c03c15981c403009512807100080080b100780344001d0060742c801181c1100e400807503501c2a01c0710080c0400300404140d10707500c04400c903401c481d800300040003c0245580d60503400d03051070708141c05040c1e55440903204140000ccc0210702c20791a40d9103074090f601c0c00e04200000317482e441d04a029803038680079060000c0d103940500060f80301240920000c810040b82c060350041c03d5484001444408090000114034420500c04040d801c4110001e02c2080001d000788490402d048481500044030314000f510241451041a9800481c514010903104d4070742c00c4c050b00d40400c051580d03140c020009101401001c0f0038012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 150980530 1250 150979280 150979327
    0x6040b1b0d050a020a03030b06090a0b12010e06062b0906150e07020c01030b04180c06030509010212040b0709031e020306010b0406020304060f2102030f0907051005090a0317 76
    0x7401c1943d1200000e58130491410000d05050b07a1b0610701c030311a0ba41e00d01360744419000504040035103031105504034a0740c000218421520b001040042440041c00d1521071003038101034403607410071112407101001507124660804022010756420303c045451781c010f96074002c0c0552000f182c070035413040701e041921201c1c0e8414040c00f800340d82880b01140d404074038107802c16003d190204003400188001001840d00400d0200175440302c0ca414820040074130111021500395032010170450351200b03d0b4500b42c0c80b481040b104010000000a000602c502d00c40c25041100b40c54000d05554527a500e0b0300b000c1000da0404803908800000d24003c5240c1004000c2c050449842c4c034505141c6003078800303996405280996000e00540a518044040c45507181d011540d4140310f400c49102c0090f000074000390300c140c0d11501850100760004510000004a000484401800100001240c58000c0301c0b5508032403d041c0e4425600386002012984142c03c40c226000c4035010b030b5503503004440c12f811810794400c88 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 150981780 1250 150980530 150980537
    0xc0e280b0406030c060e1234030b01062003030408070602070605040606051302130b280f0e010c020306010512010e0f06180714060a050c0a0302010e06070215130206040b1b0d 76
    0xc14101c2e40004682429807035685814860b030f90723030740704400401c4010400443c43c0b11028084004240100112000c0c100d40c0ca85d1207010300c0d203a6400071381c1d480c0143c60080b040a46d00810110b00044c1c1c1c0352008204803070044800604000607070340e0b0344080d15400d035030684070b16444000500c45881e189a80328603000c02d040c4110324080f40c50701114480d1480348a8052501ca001c2003021000c2240c012071105021202c0542600103010702000d000c1f60809840840007402580072495503501a0722800d015580040013010103a2902080110040074003002101c42e540301d41381c145c00440c08101006a4140400c0a000280390281c9140c1c084186c580c0040341c290f008001c10814084c6000155030303084c3d003da0b403a9942e0000b0640550f00c902ca09002190540700340c907000000e042e0706620450050007003034162aa00d4070780540890360b0303403641403410303950740205d002290328131011b50702007102c051000e000307242000e6590241c445039800c00d059032110300880b4840d542600c1014040740013090034506 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 150983030 1250 150981780 150981799
    0x18150e01180806060d02030a020a0e01181a0907030e0304030305090f090c190c140f0d03062315030705030f0a060e130c080d0302070c0e280b0406030c060e 68
    0x42c480e0340e4818001e0302d03050013001080400d406548086c00307500354654000e450340c45481d17652424640300c01401d1052640e02d102ca62940e070051096030190f4400c4c00c96909107100c07507000342810014610001f41c010b40a041e0354055040d032880d8180081d01c0158001d89480c0d460350103c1091200410703515036028400d1420f0810000849511800d0300e945000d20780d0411144280054244c810006030301019110b20f1042e2940b40c0013901c0081e4044940345104182c404440c0342c0ba01c00d070b05498481c000d140c500f00d030107030004641804000010000401c02007003800f041412100110450340141c0340d42d00001e900008002c3c50301c14101c4050303000201da82040100505e000b0030b40284180c050030048880641d4100380050040002c1c90324064480001038800c010700140c40a002540145030171198041e03004400961085174104881c40780c2042841d0482810000d59180300041058a4580c3d482d0b55842404406172681d10404010b14861000d8198850038008042d0400701c02003030700c074401c44100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 150984280 1250 150983030 150983039
    0x60503070b09281d0405010b03060402091302040204031203053907020402120f09070f030209070f110105010311130c140903070824090312010618150e0118 68
    0xb80101221200f80c0400244100c030103841080c00040d80758003001d106408241400210050302e80800c1c02213205030300811a0010360801c7c59115081110041e503c030560400081682d00e6041981101d1131008200502d090f80383c1d5101294003071000c0c00c510000340d4030410403000c07030b0342e14100c030f480c20700300038806454066200c180b40641c9084107800000c03039038045203a00464030b031601a40c008204414a417034079858180c1030000314080440d1400c0d007038854400000741140703810300500d040c1d0790060402c118a42c0d80501c19a21545452083d10030403240c9801074182c1d550030311410740030750311600044811400b0300d81000a02e02c00c224060484500d40b43c0148086504400c03000001d003202d00865807100710a800090520b42c090303001c05d80030b004401c00e01000005043e01a025002e044645405544895100135a81c0c000e0820f0f003081da0007108010f10419000e02c100c50554580500718000580c0c59441c5201d90b5461701105001183d09013441681542e0170035450100c0802d2079903d0801c035850f0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 150985530 1250 150984280 150984289
    0xc03050a050c0910140d0209090c040609110d020c07051903120503010b160204020f04030f061401080a080c0a1415150a060e040b06070b18010207080d0510030204060801060503070b09 80
    0x900c0303103601c80703080c64171941030075162401c0d500303105a00141540600e18140c801180c4508085200134821454200c000c11155040d00c21030a070401e24514003814028031124444c020341c462220100c981c4a441d20020b0a80e44207180324240700107400c41c044c0d1445ca1880c10b0030640c900120380105100301031006101c0120850b00b500c403a5490b4901154100c0f40300e0020030024829182150051000054040184401024094011071103944100000c1c100c2c0c00308602103103800e020b0b92043c1e800c0603805002283c820700250124034040002c0c0c5102100a82e00c610b4004003c200107401c0b13421094090440000c01031200c0e500c0494800d0001c40d00100d00005841c2da0018050034051000c14002c0c400c03d519143d00600ba20074020740032a03518550781c103040210980032282c03003100707401c0c016031014041018004e540700c40340d0043d0524208683c08160704007410008242c001c000e22404400409a13440d402560020912900000390b2641010141400c000341f617003061031080000c22452046444 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 150986780 1250 150985530 150985561
    0x10050a020a0e010c1b0906061101060807030f0501020405060d0b091302060316050d06080a02090709030b0f0c0d09030306140a051315080102070321090f030e030a0c03050a050c09 78
    0x400346001d50021000d4a00f04045d0f4141800c0ca070301c240b2110101044061896010382c00352006511030144040080b5a5a800d0f94018014031201d50030104003000020445c0485c50030551041e0005420325850307a0224519422507494111035a8903038002601c24204030030b40580011105c944504480300640200303080c5d1102801da41090214113007032000d0580b0800c16102c0c0401010010300695998400ea50f0782c1d100b41e20400d0f440b6030306260200e04140d02400080003200ea016005202e0f60b608c854641800c0d84009102d0720364100c003000060540c808510401042a100e900c0c000740301070604c00d5031080381d030100c485207001d83c50000e001d02503a0380c1c04036501c5605001006c0130a0081e2001100c64510040360700c034819541c008640002019001410110f401c03c401a50b072a162191035001c0081d2069200090500d00641d1580e0011030710440e1400c070a01d6014040720300500c4aa551084902c00f26070042d42c154026004080030000f050062000f02081150550074504000405441c80e03034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 150988030 1250 150986780 150986807
    0xe0603070b0f040906080708071d010612140f090606150d0218150705060f0103020d140c192c0a09051606030e0705041802041a0d030210050a020a 64
    0xc0000c20500311030b0a000d0100d902410501c00140101562150070035a40c00060082000300c2c02410400b09010040e1740f00449003150038105449240d103421802c0e01c01c0c0310740040100c2d01035250b0880d01d100001401501e8018100403002d1103ea24108030205d00304003000d04028400c26810804580301c050100596015000c890001130b43c8420800d95500c86004040d050354024042180b84103c4001030030161044a01407030548d40c0300d50305c0c1c024512020600340802503004c0302d805002000b04142420001000c41540c08440c046001c2c0c0001800700c1c405807042003504400290240030000d00300c0160000e00004c1c100e9980c1e400001c02c0c843d4007080004003001c80780c5030b548012009001003080f0311021186a104a00c01c500c3e240e00d0014041d0000d2214a00d4500c110000040c9a041038400c1440c000020507001d0314000b0340ea4200809400d038800741070010850104440d0165403084d104528180c803a400801231090500f034890706440c00241503419803032061141240c41c0360003036041803c0380e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 150989280 1250 150988030 150988049
    0x601110c03070b09040e011d01050703110706021c020313061103041a040501020d020a0503070809060f0a02161b05100801150302090612101701060312200f01020a03060e060307 77
    0x2900c032040410010483e01e00c1c6c0d00c5c025801d007288100302010010002c00718003400c40c001c0c003c50380c41940c258203440da0a410020303494000c00001002c10100e0340034000d83c81803007042c05d080d20301101401c82a600140d07211031190f03410180c801d04006003442a18034503a041055981145000d440f6401c101c02c003442c1468040755103c000a04100d001e41c1180c06601d02c0000c01c54646002440c020b000f40c100321444808110307a240420f40030b41000031070f10302c260031104c9511690b80c0c52042c86030107508403003c0b030740d955480651300f2400a03162100d001003e242881c06100c08034036100c100204860544680e03c240f0034200300500c100000d0044800c4803216505026030341da202040451003030322030001401c040104131f0090081201e034651340d40e001c0382c515080e054080c03011980864200c425038400102070380807001c6240d05487c0240381d031119014601c002c0c0d10100104051250401c040302c20445016540001c4034082c454042c400c21020b002c40300070080d00c614040000c40c0ea2100d6901481c3c0d200d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 150990530 1250 150989280 150989287
    0x1d010909030c0c0f0504060e090c010f0c02090f07030b0618010c110d0f0c06030b010905190e0702300a0c080d0c03050406110a0c030804060917030601110c03070b 71
    0x10700d4002d50808402c550b000980c00105540c3c0c1e10004840c4000e402024455410310310000340e400c0fa807488407070080384207101804c2100d45080054513a001500750f06018020070341d40040250740d84c0100300d03210b0003015034807048030304c0e1010005040310b0389000048d12800e401d11103442d40141c0244114144902803c11003c058514202245240740d0b0307102e07440c2c1c0f0110b088604420400b101d0181340f1058426051014010317156141074041d41c0540540600041d84150b081008d841c1c414800800004100490300c0811b4039110303203070240c0170203d41701e50240e4880e4000329404909128003803125801310000194a1214043e142203c1c4a00e150040802c00d00491b00b406001c2503a0859039031300c43e008000c0029010010001e00a04001c60b410f0310501e1400140b142c4d04007100b4101c1d00510203603905c10713114518550b02075031680405001920313020f90398800c01d00003551034048000796500b01e86086843e8648000010541420050700c14582c1e00040481501c0d5280050f0140c1a0344403413020310386 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 150991780 1250 150990530 150990533
    0x40f0b07140d090506090304050f040203060609030a21170c0307021204080a0209150907080405030c0706111006030309142202030709171507110619061d010909 70
    0x1050080c0319581c03860110009501c1e00405902d51000283c2c0c2d1051040c1c3d40d199a03140e0300c039916030180d48641a00300c034001c1601400d62805500a540c0b003034009011ba030804402c1008070385402c0345488111150300c0c443e03400b0740b041d09100095450141440c42d000d07a50406504c00d450b1ba1000183c0081100c3c0004030110b511740d402400303e13940101d44d000c461511107070f485692942d2840f401e801079005040010208449881d0b00b0850600c1400c003070a1108103031a4480101e40f20300d001001980c990006100d01d0f0b1702e402090040710014034140da00d41251203002000b4a0419881c0100c0c900d0f0240741840c200002138200d20b40c030040790810050300c180e83c28610b0100303080040d0541d46c40100c0da1b40c07800c0c0e62203510560340554040c05880c0c0d5000c941d6904c80a440b081d80c01c0604854215501111183c40c1c190050000c0f44d501020f24908561842c0303050312200c0c0b400800b40e1f80c402c5010600b6100c250900b54510031b8000400342289501c0c801c1c009005102c440080c1801006c070340c151500c0c207130f40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 150993030 1250 150991780 150991787
    0x6011202030a0206031e040c0603060603050618061309080918041a100906090203151005030a0c09170a02090a020a1e02030f0309030904061a0a030b13020408030c060f040f0b07 77
    0x488002e0380020381b0041380307403d10300f148048505018803000300b0310301000800c41504c00c2c8903d620032140548009031000002041c00400c6900500040c0c0c400e51081d20a0448030850040c00c0c126441200d1130b6803078641510402c890b40c820b50281c1089040484100008628041001c000000c912200105291a010348014800410740c00c640f0450342000c1c80001c10f594940e00440c45039034404d001c00d006011403000c00009408030503002300000d0003440402c0c1058000c0d030103980703054460704040ca0065501c1d00804040d01940c99050016004020060f0030b6041645885034814140c607002c6190030440c100180240d0f08001c6024600045040c0c5802c1303040c020002c464010f014544c0c0c80e45c0364688902916503e6101c0544c050050341041d500103108940b100580054824042c19207042c031020144c22001400341b172541ca0b502040f45001e640740c0310568401407003c0c1000354040d56983c462220080e290000213003c0b2545090400d040001003181041c10343c440e9079010072000201e482e9140200c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 150994280 1250 150993030 150993061
    0x60f040b1c050604140a0803150a030c06180611030a2627150a0e070e010609030303180c03080c030c011109010224070e1215010806011202030a020603 66
    0xe8004403005000c8400e1060019140b44514416035141002c44200001d1750386401010b0030042103800c040c00841d40000d1041c440158020014010301e00346940c0303031602019030486030b11980210f0091045400e640d02031000c0f80000d0056400c25850070081001115a41e110707070034500041000c03051004010340300c000301194021000c0302603041c8170308003403018110076210502c1c83c2c00d20610903034045603c1d9101150b1080d868034425540d600c243d076480c20310400f419180401030010300030000c010a10440000b0340310301812040c0d80e080d803a01d00b1858060101c07604241c0c00e042c5188230481c100d001940c015041c00039039030b10240c040d0721034000c2c60300c0c14590b008607001100b60b94204460004000c51860141085030400d80c226a084ca822460401404151080e940d00c585a1030000030f0340580a202010307041038000d400c18190048424006080100401407640c1102c2e10600402c4042e908000700d602500400c1301c0c1240c1c030205603000a60385c1e00c15460003401000080700207204041c054102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 150995530 1250 150994280 150994309
    0x1050a02161502060a09020d030305041109090105070e1c1b0306060308071211060114012a0201110f061b12042307050a0905041b090b030114060f040b 66
    0x400001c60b200c40c101c0708500382c40050741c001480b40324009010780d20359004520031341c0d802a1078480400b0b074a480450140c8401001510100011035150590761503211078944900010300001440c2d0900400083c890482c00032002d1017000001c41c40740101c8500000401002c0c0e02c1540018260005a00100c0a00301588040d189a00c0c0000000c203020038a4014032903584640488030030b0350103000003901c466075030380f280800a074030000052080c4e141c2e44152030110740c41414108920407241400303803072101c0c0e111813881c80d054040e1070250031942c0140200341c940000d2009046c040400400c0240c0d101402000c100c00314020301588045201440304031801644200c014004500d031609011000312540030480b8440c2900907150210228040b80e003005440300240004c43d09803401007014050b120240090350700b010014010b2612200481e102d500500c8044008164000528101421506451504e2401d10102010060160303110740d6160640101100c001440a411102047c56045000103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 150996780 1250 150995530 150995563
    0x60705060901050a020403150b0103110409060510090303050f180904030c170306060405040207080d14040c060810061b06050c0c060901090b04030f021203040b04120201061401050a02 80
    0x444405006000c00d129109101000081c0100c0c0c590030843c2040b4415440003401386039034007103c203501030115009015100c0051502003041d40c0d800320b2400980e40f06a1156155036920041040a804d01c000070101c40c4c4602d003003030740b9243d14544024226219109a240006100140c48101032020340d40101e454080908644450710382440c1c060007150101d1001e8412003071103010032012900741b4044a11420002e0a002d040911380420300000e5000701d41700b00d42c4200248003250202140e0b02c02c0c00780c420b00d0f05900e58003504041c20091102c244039001801005044070030415002415594003080f82c62625041e60080316591101100780b00c2d106006180f5400c0c80300b03209014504002034003140c0c02030000c0e911661140d14055080302c818100c010700c200103900000b0007090003014202c10090302ca0054074403500741d20003400915841181c0480307400c000c110511041c41f07414007584282c1c026600080118038144525503404200b84d6403031030b042281c0060203030401071080c000c0c0d500c41a040c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 150998030 1250 150996780 150996787
    0x40314030c161e030c060f0c0609050d180518180d0306080c09011d0618091c03050702060109051909050d0806060406080f0606070b040b010e071110020a0c0206 70
    0x218a4503201ca1140b24142d8074100c43d03000c1541240600c0140c0342240c0c2d00050b0500030714074004003500c50031501401402484840303a8000086603070380c007426522030311581c06410140480c150180200080c5c0d604007400c0a500a402e000a84401d820012a480190700d02003040d40d8506065822800808000b8050b00800e030750b032000c1e1601900300030143c81c2550b0555001c034900c5424010f402c00248030740760f03582c0002500c55840c0000200410740044000c2d001201e0000c9010f03000315145410369500e841903001703041c00c2070341000c0c540003003440843c50b00e01480f0b18204100020759a0300103005084c404c2d540c41d0003007401403c4400c0e905154807107143d07040c00424224200a5212802030042c2004186040002505850400100c230182c0f039640d2a100100e881d0b0401c55240528001c01143d080a4100403420203e0b002440a0784128440c1004940039810504101030740b01b0b010340a0800d109401c000034103203100121301e40d501e00780000340060311a0400f00d402c481c800c600c15400f0f03402c0b10000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 150999280 1250 150998030 150998053
    0x60e0105040b090f120912070602070e0c030106020303040204110c0109082205030d0c0302010603080d091a061e04090209011206051b0d1a040f150812040314030c 71
    0x190415031040780101d0040d04150343d09840c554440120303000c6044141c00208440c1840d0803040090080070300d01504901000064480403450080950400000740c5e20154003040072140d100c00e043d500082000015055502d0b141020b5504d01020300001d2040e91100421490f04100314251180003810600a02000300b040c20130559a51049814454580150418940c0110341c100030b10112100a002091002c000200449a0040080007101103541702c100020100b40c20380c000d0030341500d500e100003900c2212031404510a0200610342c180303401c119000c03c510396480e02e40294040101440b0087d421a241300090014540818001d6215010800115910f08000403034902035228042c2042562164900701086003c00381200780100f004024104c4c04481c9508502c00d03911250040181e0340141c2d01c0040c0544115140302c00b42d03581e03951898403040c0e500420b40c0c801888044007a003811007080301c0d00411032140e800003500144204804064041081048950350b2298000391074241010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 151000530 1250 150999280 150999283
    0x1306020a21060335030c030105130b100e030304080f01021c050919140106090c12020708030c0702120312042a1e0504090807021507080904020313060e 66
    0xe0a800010400400c0190840607520702ca030030242d0760071040160201400700440e040091002181401602d05202c202c00395201103000742d4041c01429959603242e60405051003180d0650319141070620f07007400e0700d20145494000b000c2b000090030340f400c41e40e040700900c0420f25500c11036201581510070306680c01c840f8030040d40603202c202200540c007454030903058070603800e482069401c1465600001e000928105910301241e00043c41241641003030400015254212482c07980000c1c121515142d150f18203e41c800805618500e01020450901c0d42a0301c40c516a40402000307107144180c00201e0740300391340d52048c079807001c017008034201e0795210031500b45110020825a42194005644001040a00c510f503e401390a0050440d24200f00d80c0740611000c03017503045034014042564001070100b055180c5014062900c2c0c051281166540400c1c41840840b8106114913400354038180711000010310400d003111451607003100c01503180d4070380940e8840d052200d504010003092600c121000603500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 151001780 1250 151000530 151000547
    0x90f060115030b060304080901080414151807061e1e030204090f0b0d060b0f03100e060106090f03060509031204050604020102011103150910030206040b0c331306020a 73
    0x20070340e80612100080909201140c081a10020000d400502c01800c05501c03030202c0d66405030085400044201c600081141000a833240c1d000e8076a05260800500307900030341c003000c078082840004000040c42c208000707020a900c9010b904c7d441004a1120f403442e880b8240c4a950440c1a580d0080401c0b01300002030000e602600c1000d1a26040190202d2140050320401040d040701401a0401b82d0095443d80300429034014a20b9010507020040790b0310740c404100542c4800d000702d02c000380c40501d26400034a0040d05a0055040002c00c00c0103201000143d04140e0440780d0200c1d0114241d1070f42c01280382140240150482590007101c104000e10200051082c0198001c3c3c0081021704083c01c212500d6100450b20a420b60040742d04075115420b0444034036a101c45681a114401c2d61261700241081d8400d50028040101c080341400300800180041610b0044401090068039040072008001c20282c0d40e40d9402c489410740040e4201e201e44605040c1d950f4850340466545100b140003608092 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 151003030 1250 151001780 151001819
    0x5010501080a050705030d0503191d03070605150a0312050913020d0e1204050d0303060503060702030403050d0e0d060b010309060c110d080c120408070b010e0f0924090f0601 76
    0x10413001d0010301400c000c64480e880341c0030383d40c8540c903503502d8030402170954412010800c5415075401a03195041131030031440d5004900e1101460366085c0a04051017520005009920ba020607046d0004003682d6510a08c02117030740c44a02214152110310b8103680d180a0351031003a4120400c8560503d18001039401451382445c00c0c442013044419403000240c0da900c0f08621580384d61420403081c40185012460b29004074440c0c50003142c6182c4600c0801c0c203002040e6018000b59001050500030803c0520011180c010b26190400000080700000f5464030801d4001500896039814007800a03440f07a00700c05031003500b2200900a034500e0300d50061201454440030394960181e018408180c602c210442d074040d1031001c1d0210700700813054000c400d2107030000c0c2003100e06405c01c00102e80000d80d0540702030b000f4505021964480c0c0342000701400c01e03180050a541403904082d0748840e130511464071140303041880a2030050a651340d03024081c40c2007a2a0542882440781c8000000c001103075514401104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 151004280 1250 151003030 151003033
    0x60e03030d09050a02011e020a03122301081509060604050604060e0708160c05030403021201060e090c0306011508132306090d030207020d12030b0406080c0f0307050f01180305010501080a05 83
    0x7103040344551140040500d40c00140c1005140d89d000c40e11910341d21211781303089800061700e00e40f0200e5803050200c40071200706071700794000c004102e42c403000e104032025205a1783c0c2500142c504261502d03180c140c01041140f08a6030341000c81d0302038440340d00c0310700a80b60003540342030039040c0160050100d0300101d88003268012003926054401d4481c5020070301e0076620000030350401d4156400c21840d14441c561a000c590f6844000041003501182c416000f200300c140a002e40c0c440c03440900d42810f1058010103002d00359916401c170074581c01010154803402c0c0c030ba104d10100d8003500d80280f00030254000c0c40302c1071818441e00124294040791203401813000b8030481d0503010400205400ba4090440060b500514054020740450034400030707841c03804a949030009810382800000350480b24550041c05195009000301c505d64204040004a804021001424100d141000003805200070380074590400c03142d03512a002c0d400c204503400011b964000c0090101e03603116119540d59080b82d8006407180d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 151005530 1250 151004280 151004297
    0xa15030f050c1002030a080a0b0607030c03090b090105070210090801020d0e1b0d03050a050f0703080405060a1401050f0f0307061e0801030320030c100b28060e03030d09050a0201 78
    0xe840c1034038000303c0354001500950304101c0c0c43d04c003d45000c000103152812194482c400600070707544c0c04004044240c401c0d00c1c2e005118515090003445940d29402000000c0c104125141e4140c0e008000e0303402c215411201480310048841c0115155540c540c090700c1e2072f42c008280050980350783c1c1c2040d01c0700210041141d50441e210b20610380021401c005403504100854002808284104001d10890042d0700f082842e200350340c440341c4090740c420300302640000d81c441d0602c02089018400c9507000300748a4018421441d080e417500c0c4501e00180308251191004540201c1103480303c400c07811050900505552844d5a104405405050f00048080140d00080d0030307407040d10b000300038160690780c1540d01e1100031440b030511f00201e07030000740560307000f84401d004002d041c41e8208514000e00301340c0c2001040c112010428000084804402d0b6100c400d1902c0300c10441d141825100d20441e0a42d140880c07011003480040380c294407034040c0082499052950b0076082c0070780059200506c5200baa82c0071032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 151006780 1250 151005530 151005553
    0x414060304110405040c080604030537030203060d14030a03061a1611040203070908100c0203090d02150705070e060d2001120c030e010e0d080f0a15030f05 68
    0x85520084900074000038203100c100c107035800d00341d001603400b81c85011410410358039030344401d20341002213504800003400094070101c2e007040040303400000031381100c150002e942c11039200d50f60411a41c04200800d0ba0100004400b9510105000c0d00c89030040746000682103010807261301daa00c5020391700c001c81d040080000340c101465481c15440074103811800d0804400404803682d011900e10141c4d403144815604440310703501c034802540241c505860350b0030105c0c41e0901c240c1c00c02c6040108028520314154103030b800d054002c802c07a424a03604480d900c0310612113200080c1c501104c0454100d078000f0110b403400c00c0007000501d50382502c280500c54100c80d9102003c005062410004c01400001c0400c0300b58410030a0820001c00c0074014100003002c0c070254540389045607250103050700045d1b01c0e00c1594000000c20322401c1007400c401c00240004021580d0040c1070b07540040c1540c40c2c00c07030b5100c002400014aa50000b2880380f892842080300645e01c4c14021503415100c0815581401071005054 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 151008030 1250 151006780 151006789
    0x603020907080c0708130302060a050c071410030e101103070e0f1e040b031b09010506071e0309150305192d090f03050c0601090b060706090f05120414 66
    0x240700f207012190062600340d60b5500e001d51038001008800c0403070303c0c000c40440107a036004080e00e10300c0042d035075807a165030301100a580342003640c4d8024420040b1114201300c0c69118400c26800d0b41c550f5080204086000c3c202c240e20b0000340c4110030007820303d000c400384c0000700d04400a500810b03542d520700d8503103241c481c02c00c00c85c1c0400389001d9034004000705241030486e80350000784480c002d000700300281c0165190081381c01c017a6607075045448118a4041d460007460038981c004e01401e01512041d0034242c15540708188040b8200f54808042a050040b5041600c02d88101e4050241f4800d21102000100000340240c41c0c00d07684000b6840d03e12010240c8800284a28004003100001409200003c0301c000d0b40d202c0102040540380c0c0e501c1d044403a0104e0300c00080014010311a90700d45039211405036440d4148a07040e04000e00c61810035040d114140d603042d003130304c0302d180c0c11410000c0c0c924560b15008066070807881c8000c046000f141044480a0b500350081c1088403504683e0a01c3c682c84201040b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 151009280 1250 151008030 151008047
    0x8030301050a1401020c090f0610050909011a040f0b04050922080f09030a0b07110f150721090311070303050f071403040e070201150321050405130603020907 69
    0x40b9001075100104008100f400c0000107060441801a501012002008125981c034101e51000c041c10300c0703105200e02414803400c00c40808006241075070400b910720380060004081882200745007000075000c2500031a0034001ca4005020b10100251000c0c2e1740d00d61201607030018400d40e4814200700d40014501d40400b4828080e285890803581903405140e03a90540c90381009000110043c024883c42c40035490401455000c240a1005803074980361103e0010300302c5100c91038510254100d9881d045103083c001904191400b92981e0006070740d502c43d8002c032480c0011602842403081c0d050f1180c14220600c1c1d108407001d5000b5910091681860680c070707a952001440005c5c000b680c02c101c2114040d607060090000c03070f4802c40401c0c811443e01450315185402581107650002004024885d00e20303024410001c0391000001c44114080c990b0702c3c0c41044140e050001d1460b040c1e0910416840c0d07102c0d41c00c440103404014800b0066083d01d200b004001e014500081b030041c00d41801041d8a14003030b00c5103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 151010530 1250 151009280 151009289
    0x20d0801030807170408030d05010f09090b070c0611040311011205150906030a02220b03060601140d091209031401020c0a0f050307120c0b0f01051f140a031508030301 73
    0xe140098079960004d0700725400e0800c400d51503040c0030120303000c002480100a03c0e107a013500400c00b9414a10704110402d12980213003412498044d1110010791080102e59228a00b428885012051414080003410b2202c04110b00d60b080010003004004000b600c107403400c402a07881c10400c100170405a803c9440664541c2281100c43e44000c1040c5441205241d00c454081c081e1281083d40d030340814402c400740400310000d0341540610001d550304034498240c031044100c00812142c03c0000021b0034601d404010b8801d2a440007034202c41084070b5400c40500c0c0755012004290f01c004464000386000102c1c0002c0744d82c00960019011a41c0c014000d594102c0ca001e409012117032929524490f1001340f0038400c1b15103003c14424040402c02c25803004c0f0780c03002191a024034a1750300b45004030000c00000c001c00c495401032401440f1075102d43d01284892032220b1b09803c02d03036988480a554600304a02d40030061180010803050166140d00503d00721b041041d2007090b00d41d04c914519899000c00d004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 151011780 1250 151010530 151010543
    0x1710050405071e05030a14160506090112140408030a180218070903051204050a06021b04050901060b0309031908040317070e1e0a06050708030105060304111c0201020d080103 76
    0x405022003d6205001e0301e00511038041c07540341d20354440c0400d04180d402c8800341d8440225201080755024103000609030300001202c0f0980c014100400103c480c000c004e0854104a00910050710008039a40600d011400e000c0b41140b99283c1481c0480503a42301300c0300d60f815103040102544200c084a50f0510141d640241400029818a0402d40c407209004212000308051203500001251007072190341090445c09408558482c18202031041c6555240c0c042c01c03c66110060742018203584c41102c1c42d0303028013100c001c1007685a03281d07041e000d0300301600104203485d40007042c40b224500c008010043c043d030300d22401440b0210908291400c0f40211406800702d8500607135400e41c1c00b41c510300e455000b65281410b070704c914010400b10f040244480520131180f0324603200710180d8600320550b58000c100c0340c43d1007840c12202e65034162841c0010302c01c01e40114800700101b000c008855003100080e01003e400900c10558440715030304001c4400c40d059000d40108181c081c0205c0c0320b00030b40c9040c0c80c0c03c02ca = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 151013030 1250 151011780 151011793
    0x10b040212010e0606070b070c02033c010e030a0207050a080a02150904060e1906240302070c05031515062802120d09051507140d151710050405 63
    0x24201c81403443c0c0202801e83c8040c0800001d4005110f104409004002d0340d62004603c14252061618141d0180c00010510b011280110075102028804400d040a1018081011481c0102047c050901000c1602c524000415500070080d400a1010215042264030941280e80c0700c454946036800800060340184254040c04803c012000c000c1c0704004010b00000f8030b1903514812014600d0094883d980b10900031ba00201c241d074220f002c0c90000e46120800e03061000740014619035001c0766103000c01c0c241034011841070140442e5032048002400040c09a03110461102800d40f00d20004803850218041000308071105030400d0000c0d81c0170391140000d0501c803840181c4040410b85400c0076504214070510b942c031030f03c0c0030010001c1c051305140c0307040209005c01585401ca040440c00200080107082403030412804503413214640c0c910b809440781d0305d59a00060f4101c60003030540e44007005100104207c002070340060100c401c3d4410f0042805882d40940d10101c8141611001d0310050019403048 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 151014280 1250 151013030 151013039
    0x22a0d020108040c03020a09090201030b01110619020d060b04080f0a030e041a100e030d0c0206030c0c070b0c03071202031206040b0f2d010f090905072609010b04021201 74
    0xc1d00142d41190060054540704c039529030000b0715400440d0407000c210782c0c840d00315000310b58050185409401c42401d081c040c2148030091144e442c4001001030305403961910b51101011001c0e4111000211000000d00c01580c030381072465041e07400b51151030000c1c820031442291041001c50741c1c40401d40d0569400e040c0150041c20000038007a60505600c04418080a45026503102100c400040c507181c1c451a01d02c0048034101420f0068490440062021080c10040141d0b41e800481e64414a4090181d440319551030300180b400d511034001e4401800002001401c0420020203042101d01c681d03060511040c84440032a00c134000ca440341428403c11001260701c03031600d40c110806038078010f0803910100d20711800080015040b120291030401d945038681c030141c0302c003a103030403110701080c20910143c006400c4011301c11042c80c440d907801a0b07560004140c40d18401c1110010481c0800c0441c8514000c03501448400b41c425030703251a40c2c1d031804070142110300b4240250303103040208801c0351b401d6a181 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 151015530 1250 151014280 151014287
    0x71101030b12011e051b030402060a05071202060415060602030304030c080d1a090604060602031803120c011a04060b0405010810120516090b060301050d02180106022a0d0201 76
    0x60a070312070b400030410035000040203007442110300e4010168990036900e20b03a03d4030003040342c10140c44a05000e60f010101c14244007540100c80c2c010754140c0710700703a07904a0980e0031102d5001e984401842c0e6030041c0c162400d482d80c0050154090303405801900180c0d0b9403100313004201e030100d100e2000982c100380002000701e03018130400300120b8012018149000c80280050080301d0110104044841c0143d40020756410140040d581c420401d0340d0070000181480390203980c900910450740000c0324180364203040d5481c20701c5031000940307465034036070385034051910454081c4c180f42c2d070008980340081e2046d40c401d00d41800703803200b00c0f1101003e041c6070a007042d004580301e1900400c140103440141e83c0000d5a030701c0700384511110034040e1028040881d20030200c0482c03204283c0c00b01070900d0402a042040b6070b601c204a90450303c08580c0b00c4a85850380c40400c4040c20074812410500f68104000a0041d0300890948108090404a00200e01c0714140320000302d01d04003039490300420410b180b40c005501 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 151016780 1250 151015530 151015541
    0x12060d0606090f020408100501050901170708061e0f0f0a02180303220b0a05040909020117070801090608030304051506011202040602070f0605031e0c0705061003021507110103 77
    0x90480411001d440b846400180c81c146200d200c01d1030707070000d010020094244000e00b40442080e82c140400d514140018580c140103001d400081c03071980310034840c111801c0004000401e61041990201c0c07030300e201c0b0007543c00010003a0100d0114148006003401c515440c205104060b2a62103480b50740303a0400340d400941040400c01d40c5a009083e0340081340d2b40070000b814201a84401040c511101c40c080c1c43c824141c554004440030388288082c0c030405410074155020342d00d00580020b0344041ea400101c2d0041c840d1032011990440d01c4003484180d99204003068160759010a0501440781d4500c4195524031007240c000e0400d0b040411104c0491200c0d450310354100405241c404d236541c04420000c0100d0707000360301ca24003680c0002020810110580065070052044d800c2041c107500e0a81c0002480503030035007206800324150700020300350269840030b68800540102c00c03a1840e182080d1304180c00072107800705901c9070307801030350643e800424081200c82e10395108444a040d05132a10040d4050031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 151018030 1250 151016780 151016783
    0x5130f080f0d05090c0a0602070609030318120b0912040e0402040504020d0b0a05011a0306030d180b13263c031801050c03072405070f020f0312060d 65
    0x2041001000c2c07851106000349405240700c10050001c0303e460b001042840b00b210790102040d9007111504005079a007190301201240c0d05410100c1c0a1703a150113504500386040c1c0c0101862000500c004801e001080c007506100d4440d16040320250f03007640d00c11050600582c4075080202c05448001340050409070082ca40091020b424641c0034443d50790b030542c1c0c186044402c6052290355200400004100440c0390030101d6164460390b03c1c504002c00441e486200440d00070b801c4c4100104850f0705c403403100403207400810a012801d5141c040740d864462051b441e6201c0c44514641900800c803c01c3c80c108048140c2c440709030010580c280d0141e486404828841070140030b250320020060100503a040c0c2d040b92861940d40c00340d07076100340304044408800d9800080c00d0412500344040501644000103c5040d00c0d0420f8004030f4903808500e040c800d040c62803485001c12400c12062014071070304030300141d003550025000d4a00b80414007085584d80e010f0070143c10448503041c401306590741494502d00c12450f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 151019280 1250 151018030 151018057
    0x1b0f02120703050604110406050609060c071a0901030f02031e0403110607050d150501020607050c070b04030b01050907140901030203060d0b090606030d0c05030a11031903020301050405130f08 84
    0x10391440344200d0402030300703510944503078020b4002c120070005c0c070b40204404104225400c00609040c54049901401403418080c0510310008900c40320600c1040400024000308485200c5000c100388100019000080c4141c00300c0d043c038041440461540c000d9900c1061340364100d110f030f4128203d0003060076034080c0c4190103000340101c54006143c0144090781c807845d402e468642d0b0300c40107052058120b40b400021100300748107001c4107110341d07030b4081900c81d042000342c503003e625022480d1815040c94419806200b81e0f1100140000420413568502812580200d030f0b19003040d0365041050340c030b4002178070903019854030400588050350300a902035a0408401341441d03080d540e140d61213615410094a680b41c2c6076210004004c20740c9000c01280095440b14038107007203070900c0f40c1d0741d09649000302d0100c0014003400790285c848001c02001503c04200c0031a5032002076a01e250000b4000398420701645000f60306000011b0a083c0b00b40c03590842095215500c500c0c0a60a91200c240030303001500510440e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 151020530 1250 151019280 151019299
    0xe130807020a0308030703090c05030d0804110a0e10080705030f030a05070c090509070503010509031216110307140607030e060613150b12090a030f0c02030304150807030b011b0f02 79
    0x3144c09100598840c030401d8a00040081d0b140c1418010b41125034002e0380301381d100089100d0010f621030034050300b00754484541004020f14500113041040f160f0003492464000b2010030140d20030100c40b0780102c03050076040d550360036165401d00d03450b03440d00e0801850f02d601c01c2203101c0c9914403e50040892602a0903c0340415444840e144c06aa1080e50000d409038402003013800a13103000c0c4900b98104c0e90b1480150310b00001e400c0c2c400b141c0c20300284801041c0d0607542800c1d84c804d0190310100c4030184031106503980c0b0042440c0c9640c1e00e0364603080001340342c819032000a441030b0080c03050004c41007002d030081000d581c07482c00304000b030a04001c0c240301c01911000100004147d40f0102c2c0050000123030a15107905100408007201e00000303110300c015910545c900c10100e600404000b549288614042071010524001319242d07109907131194401510300c00c0300042150340039000501400b0f181e94240003100071800110f501c01c0c1c107101d070100b20041c494005800245601c800060080c030262140c2c10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 151021780 1250 151020530 151020533
    0x50a080703022b0b040c0c020402072a150905060301180603020a080a050c0a050612180a030801060e0a06080a0f0603060207051f050c07080d0f0905160e130807020a03 73
    0x44400030b0101c0c1c2d801083c01d5800f440143c140500030700711549000e1300e00b0070418414150084ca1001c1e14600a801164001120b41c107001400303000f504100790728a07050703d001e804000e010241100078070844d510b0040e0b60405255262060a03030300111400140300c20f0131a400c000904c10b40d6048e02440a09140e903a607800030042e140e06c0d02c0c240052901c407014204c00102414224200300c4080319552040c65801c0c4141304036a0f6901c00e80329070325a4244100070350354802c0e084049070003400780801c183d4411101c04504050340b00e9806410f0350181d40e1106484040c0806010f03076002c9500130302c00810220307000900c80d004154490a9540003042c4041080b03603032034440d242281c3c0070300303420307a82500f0070142810042c1a0366501070074040c214208010925010003844040e02075564010720010000400000c0c901030381d004602c01c510381c0c00041140d0610741ca021a0f40303500b05001000030080d80c040000340e0f0749100207014812100070340042803000040d654900da541c000d02049a000b01600400310 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 151023030 1250 151021780 151021807
    0x2040509011d0706020f03030610080601050f030115030e0a0201080f070203160501050f07111513051c030506030703050c0d0c0e0f0108010b0a080d0e12010f0228050a08070302 77
    0xb014490048042d0100c02c1c01c1c284024200100c3c03840301200d0760301c10820711440d174441e0405100760080c1454080520313258480101d40310f100c0c85100501515001c03001003558085003020310320310405501c00b000707410303405c03400c007512200d85150190100f801f46c80000c00141c032004105512612610503203203020303018400d500000c900740303400356410381d901c4042102451001480320740000350f81c10000100c2115180d006e42d0b803031103074450032a1500c2c140c1c0416004203c507004040c2d20f40d0b0050503101c44005000c00a5054541c1d140c011000a0a140104140e402c002c24442c0c1507a4000c07020380768000480042c17084585102c0700031121414070100000300700742d80d040494010b94000c82d1800c29549419843e9007034601d1403441d10b210304d209000030805050006400101c0b0441420704080d002d010b180019100007c04800900a5080c07d22050300312110f0f500402e4052010054000c9a100107070302c040c491140c5840d40340208100b0024854a14003480000383e02480303510300075140911052145 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 151024280 1250 151023030 151023071
    0x1e180a0b060a1e03080f28031103060a050d02060918010608010603060b1204110303130e0a0c050a11010b0d1101030f0c0f110703020603010b030612010606020a0204050901 75
    0xa654522034001440560728110742080010441c51240c50400480307100000b60001144c4001030025100142c5240080700e114162120b09800f42c1f031012258203090110043c0100f8220584c0000349402c00000c003404800c0c05980c0903280c0500740d004450f08040520415007980710084e82d0100040c046150036541e103030000c001000b8040b0750082c09500d4014090402101a0801c109050620206101e0860800103070313002007024104a0859803150300389912082540c11409170140030000700321441030078403800f0104641c800c0c41804955500c030f10448d81240d81170390b084000500300300b0010071003034441c0e640204080b114100002c0c2c2d041c0b05c003000a4114600310b01c00c880310840301115441660b0036209514500c40c00d480180b02c0d240355101e009144042d04101041400003034800354a00040402c5000041c0d41d01800050341c9503141e00d51908150400c84010f8401c0d000c1e00517940764108180510700450316160003c2480054036401c01c006480300905c0903c0c10340daa200c0c844110704440380c46 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 151025530 1250 151024280 151024283
    0x405040e0a0803130b011706160c05070801051501030b0306070e1f032a0c02090a060b0c160501170a0b061603120606030b03070e0a14071206050103051e180a 69
    0x644c244e080e038548041c0950059000010042054400c1c1c5445040400d04590000780071000065012a000007603607409641d140103012803040c1240420146815481240102c144040441040c0c3c0000c1c0114141c0d40c0100c1040e4054028a02003281680251050074140c50003d100c422000d65032000030406a410316000c00c0001c0d150600304038030148481403e072290420030030003072031205021001f40c07400c8108000207028264040000b50444459800180603100350000c50b940c0e55100e543c0c0c0c0ea551803e08000c541101e102d40300018071503006084c1035510303805c00c03190300440e65a07502c0240020441d101140780c10800801000780d034103a030400c481d5140c5111b611007909240c0d0240740c043c00c503081a04010103052030f18104d001296000a0300c442121803005e12401031303580c1d02900202034020205103c140990100611815540003502071150000110302041516520341c0110300ba11001d0700d03803400c0c0e5840744000340900e107061000103501840441c0014a00c049810003d032414940d03080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 151026780 1250 151025530 151025551
    0x1e080a030203010612050402030a0308041b080c1203030f070f0309080a0807080603010b0d020d0501200304030305090d050a050c07080d0e1e150c070f0306050711070602030405040e0a0803 82
    0x18403046400c040d80e41c0340c8505d88141000301d85800e81c0880d0341c50001c4003004d828010700b000001c1c10441860040c4001000c1405000c00440c2d542c0d5031503035038446241c6194401c0c0c41ca0303102c0c1314a814001040d24400c1c90104401000358685060598082d072040542c0810542c0b103090f1540441c1038070004281c421901d41c3c5000c058581640024000c0c0350152503e44680d04160811442e942c0d011144e607000b41d0111421070001d036092400c1e41c0102042c5c404030614030701000c4a4446400610083c1d0312803030090301c05010310f81d00d0344807098032414014858008500144035092074240309101030920780e0392050403100c8042c1c4456070685000071540c106400103d080e4258000c078200b10400381c6800039112000c0303100c40c1441c8001035601214040c074064a802c04508503803030700c8040206200a0840000d0145002c0e10703420104050201100d4040c04201d0076202c20848210018420007100c80b00c5d070286080c0380c2400c0400010b45a44c802040440c4114036842c8007180380d035001140210740003035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 151028030 1250 151026780 151026787
    0x5190902030c18181906090501080c0108090a030c030507050f120c010c0e06090108090a1416080c09190e1006050901050627040207150609110702030a1e080a0302 71
    0x29034441c10010f94040b41c0902d1103070b0303d490360403031111104507040152140b1524405044000302c6008000c90b51240e840e42d4140703800061540d00101da03900755a0310aa82da01d00b0744c0d80d480d0405544404040c030050000c3c96030300203800841e01c40c4000d450a284560140c803003400e52541281d207041c40c84080c00b101c6030800151307a401000700344100500d85d043e40c10122003140c05440011014000c0442441c188524480082c421450078015003070081d0703200b500c0c6880c13896071082c80740da80c68038100140310701c000c600e4000c540d40707000091007181404028000e10242d5030302e44c82c45e05610701d42602100c80c140c0384c0c0e00d090600d00e402d020f000700d42a04641e00161452504d000c20442003810381c8094000d01d0100014050908050764100102d80d24903065982c204e44a00807500a110748940076117040700200500000c40029041501155000e070814095002e000111400611952000075415800a40440d000035048101c0240c01b410080512034056482d4a46403540e038004100b0100003135001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 151029280 1250 151028030 151028047
    0x19020909070216060201230702070b030f010303080112110409062003040b0a200f0d0c0509040e030a020c1e0a24030203071209110418050106120302060105190902030c 73
    0xa100f0503005110324402440040034820101411102c4156010114444900002e04079402004440b00500c00440d01c2d07a0749141c00d107600b80a4a1081c08114001303441c0358000034404442c1c1175101d00c01500520704080802024041100520420b4030454080c2e0b1100c0c0c0c01d0120b02e0b8024036240100480e1048180c0e0b0780341500c0c1c02c4650820080590655614100c0a6529001d10368408282d80380074034030455891400c81481d12080c0143d0841e909031a0801803020885540704001d4040c119003540c0911061031040d0040b9120f010300c01d40c0000513130060704c0d40e4401c0d24090101895141960070340c80c108403003420204402c040c96421040e044441204502030307210240d00c00140030841031400b10709506200600a01d190007110000c400d40c0d4840d0340950600a94400035242114002c104108500c0340341c424050395139050405844079440c00d0800210b86900403c88411154180d0180c00350368201800c101e403000074031039a40b02c41c01c841000454140c9481c8015030143c26600b10080d100c0450707 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 151030530 1250 151029280 151029313
    0x120d0e03030705070501080712050109060821180604090207030206040b091902100e030a03021f0911041104080f1c0c0c06030203060105070f0602040312080906190209090702 76
    0x14201280c080d0340100b01540c046540400c030300050303d20919080c011515101411075441e10280d490710b040038a400300003c0c1541c003e90100003216403c005540d0000c0c80140e40a80080d2002c10b2500300a004110305020000351000b01c284400c0d00a104038142030301d031a11a004c0741c1001d4411805a0b03c1607040c03009010b8030300c140783c0e4040c002c200102801c07080d490b4600c0c020303119180002c1c05a045941000c2c00a80200e41c104a03440c4084c0446070100300b9410b000b5038860301152052400950034a50030783e60482c80c0984020242c00090320005c016030740080c000100041e406134a0008014032010944140a021441407440740000901c06803100c000f1b850b1110448500880034440c5190f0a880010403849a80c0b0442e02c4c41d0400689a0f582c1c9401640c0c58030400e00014480c2c0034038000c01041000030703406401604d0040000c1200310f240c035442502c0305001522000503079403080c000100015020101480405504c040140c14080d1500105803040c1d02560510003581001e840c06801060 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 151031780 1250 151030530 151030547
    0x230901030e03030403050412031719050109020406140d060305060c090a050a05100c0318060503010315020a09090e0114090f011a0a030308060d02060f0d0509210d0b120d 74
    0x6910166283d820706030350161140c8118492440b180c16240c6030b0105141c01200440c80e01c0200104015032407804000030030385030196200141041e8907080010450310454402c2d6010343c0c500341c4802c1e030007000321a501c8180e03801540700c1030345003902c89401100142050219500070200e100d01d6644a0070701c0e100b040400052600014060f03c544641040159125603129000f01c109007418070020a26040889000d1a89105040d488079050070008881d40d10400071412640a0b020705491b41140511000503445141030001c006040481d0600400c50b50f0780c0f00740c81c0951084000940441e01c1003400c0720400b41101d02820070b0f006041d42d240740113402c1c06900c007203051411382d04030307030490248c00108048584e01028040110440004645031540015456044d4000f00f2752b42d00e03a103410300c1070642607121000d125045800d20300800c1e03080000080900e000400031502141700c0c9540f00d4070500c50742003c1c29141540e030b21480040d01036202c000d40c2020032140303c2c1c0a00f40344040d05401900c10301 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 151033030 1250 151031780 151031801
    0x336060f080c030c1614030703031803020309060d06090f0605010e0315011a0d050a060f0e060607030f050d0f02030619030c0312110601060201090201090b180405060123090103 77
    0xc503001049680300018007100e900c1310b107103c8455244c2510910203c84051040c030f00400c190285050f0703101e080000006440b04520030350381407080c125003040502e00259082d5006026900a1140e10610325142c80501003001e00d040000680980e102072040c10f9806800f407080c00c2940d18803080c481540d101e030700d0350000d11040d40100b60003041060307c468035440512a02c98020b6909036480c640d12110401c4420210000c1001d000c41c0c00d106010200500c0644510500b03034807448000619039100c09461446070100520710f90400d21a500c054421900300203118003048020810b200412901d44148800da405000380161203282010602020031400c080d801c2650603211810400501148400019682c1c4000c8004080001c40015607001154180d001503a020b5180045000d507815440710b070180d4000d0340c40030b903640e80c5d8070501c122522451400505450200e10f40c00398600740b540120f40c00000624000280891040d4500800802210b50604800740040d64080030340e8907004100920 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 151034280 1250 151033030 151033037
    0x30a0b070906081e04030e01050f031008060105030604030f0c1a0708010312050f09060a02011d0f011406030c0909030913020c06150a15090b07050105190204120336060f 74
    0x410141404c052610401080141000300100000801d03034807603825180c05035485905d01d512414150b580c0d08458420f400b4000d002e214104c00000c1030b2400140d894050380d01500d41d08a40f8503a4842160003070303403101c810341d040c041410140300e00d09400c000051280e00c2d1507440503105e50452802c522145200600340342000003d100c3c0d005052060b004441c0303004e0381113a01b6603883d03149400a9001d04182c042442d61045000c856411030361300403601d80203541c40400204010540c042440c51080004da400640541c41600034000c141003c5210340d40001c5500d0480b404c0c24803000004120700a0014000394541d00840d49401c29001007240701e03000318440d0060740544003564007185101e04240304061049243d01e00c40602140605c070003201518032035110650790807803400c0c4107000e000c2c161098061200410907540c5a54403510030b070f50544442d14000e1200c0c44190728200c0728103500c001169142102910f1100c20202809405802c1100001101e01c01074503004002c0e00c2c840d0040b03020300a1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 151035530 1250 151034280 151034311
    0x8010807061205040c0806011e0905150d0f05030a050406080105030604240902040f0b011b0c0909020105090303160c06020105070801060f0e030d08180304050303030a0209030a0b07090608 82
    0xd500a40d6005031510380340c000280700d54035418020180e04c2c06034082021400b8841c000305289a004141241d501f003000a0270b41c0c00e0b81c4c0c80c420300c2c003200c4045400302190100240c0c3c0350789a140482c03425018a01411419101c070000303071540d47c11648058110000300d50005402c10900d40c0194449004103003c40180015141c20303101c28009244824110349100807840082c2d180c03001035800030301040c2d0081c00800200c181503940c000284040b5041c98081210b8144503800401558102d081c0240d00c014202d82092038a0101c4002d800710300c0b412414044103101c40d1400d0f84003040035207008100d0300e00c5800b07040c005003007001c5141800c1e0131032811a41801c0401810036000030119045403030510b480200f068820004580c003070403440b40c040e414026842240019640320b000c03a070180d8070407200034104d1000021001d94a1240d4440c258042d08140002201c20005601406450101405850228509542c0e5003d400022101c0c0004205c04000500519500c080300c42e50014244105440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 151036780 1250 151035530 151035539
    0x20109050718060b030c030f0405240f09010915020c120d02120106020a0302073b22050606060706150b030f06040b01080f0a0618060911040e01030b060406030f06020a08010807 77
    0x41b603100040030784c1e040d40c01d040045007c1001c00c00100d451000c92190365203440f01c0000c00c1c42ca12880c00d540320741410440b040481d02c5030606201c3d90041961085045100030000129030010f900000c2c01150f40b0702400f83c45104042d00d58008080b0820400ca00581e00c9403040c09040c00d078281030b00007204643c0588120340000e500001d8000541e480c000300e8284007032021001c041c0003c98020b08850400c0e070300781d9864031741107420700c840e014012640e11000c0041c1d00c54210104982c1400025050394040000710312641481401419054041c0c100400e03131582420040751002130a90011210480000410561030b8160040942101c0210b500b0b11200200c82c0000788240c40c003800c8445000a00300c00b1903002d05241e80070310000c00c2c02107580340c40100c2e01d00e1068000c1486100d0840290300380000c0a0080810008a40030f6505070103502d455642140c071a541d0010307000340025005aa00d400200211300084109051075124036000340e5030302c20b910001408031106034003480307896000780d00500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 151038030 1250 151036780 151036801
    0x60902040c170f04150903020307050601052d0303070c0e07030b1c06020a121503140304261006030c1d060307090e0a02120304030209010e06060316020109050718060b03 74
    0x10740204210b9210f036100d85a6040c00f41400c1d806042180340b5610740500101050f030003001034110f0600403420f5501a81c2ea910921049003a01c036800c14201640c03858400e007840084144e9034001074050120307801c0041c1b540d90140b070401140c0282d11040990810080040d0307040c09411283d01e400e59004c40c0d003070052041000c1440c403010005145eaa00401c0a0001c0b42c490f90580102c1e240c1d0090500c401c0e01c40c0340c04142d4130800c0d40400da880220b41c0101c41624040042100d08072000c0d0780064074100011810314809a0410300902440e009400d103080340c0d0040d90150342c018500424034404000d103440d0051b0751055404d0141e40a65141800f0806a0307500840d1182c119040603501142840c4011360047c10031524010007580070540c20b100142c0711400201610960740709403100081ca980380c0c2280300d110b25046a5940d0706c908208001441034000c2600b0081080c040c1c0008113079002c030b44c4d9030b0071b050a00d540c00201c494041c80c800300d0720034211401884001c00070320315504c2c994100058280e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 151039280 1250 151038030 151038077
    0x1121d01023f06030c0a031110020a1518050a03020325050c0108070c02040216030806060316120933020f030a021e03010905100e01050d06050a1107060902040c 70
    0x400302c280d41c282c00110207031001d1040305203042c0c006000c080040c1e103034a40316200c03000175800c00e4065003081c07403212146400024030035841604918608015183c418030000503007005d0824403480500c0390380c40000108108807024456103c0c4c1c014545a0b52030b6801c1a05000071841076210b03902d00c2c4c0b0034141c04100c01040280300b20000386801c0c1d0b040d0380c0c1c0c20000e444038940c00350000e402c00d10004010307202c540c4c051301c00707000c0c1032003503607001c1503903c3c1d4008000041c007064811001311280c004240b42070a0041c2600c59507218840800314281c225a12050030303c0951340031140119076900c20168420b1100700c00c5004502540c2030842c10900140e000f41d00c0350200500410f466507000640304802e1103c6a4420f5001c00c051501e141e81390703120108031002d824203130344210680645c000d0104984044040c001d05980000d4040d5501903803a0300c4400191034068008a4444d545405240400c2420070061038a00c0c01a003003c03031103200f00e01c1400304032103d50484004200003036010440e181c4449003038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 151040530 1250 151039280 151039387
    0x20306013c020f100603020a0b030408160201020a150e0f0708030901050d020d021c0e0a030c0605061f0c020307090507020c0d11040609050105091302010e01121d0102 73
    0x10591a14908002da24041d8102d100080350300c03806000c040b41808a402c0f403402d0724403d40d402c4180355070f54000c0e100b40e8007040d41d0041420100740032084010400b16074282c20140148116070f4407280c2034480032250310100c4143c24009440b0018001c58200400c802d0400d00d81440c01000710034a0405516100d0049682807410014000340700303410200c09070141d070004003641c0000c40d80c519905882d1400c00250441d00300e413450901c0c0e14020020f0300804d0800c1c03c90303095101c40107004260364500005080007001c103a48044008000c10000849850103056907449444808a81c403050040501e05000c1707a0100310038500300002c00c0b80b020b9022580800c1404159aa02d440d444540f1704001c2c3c2c900c1905075290000d14040c00010312030340a402080c100c0c1c0c001e80c1c052405889400c2e4079444408202000b80c041001c01082000651051101007200941c1c81c03400039850303a031a640c085070000449100f844030b13900820038a80e6241702909000000c000300a85000d104240d094181d0500030600c00e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 151041780 1250 151040530 151040627
    0xc0901030b010e0916110a050d0516050d0207140603091b0a03150b0f0616030e0409050102031608160c17040806040311061f050420070602030601 64
    0x1400007469008403000300442c58000e02d902c002e4a403100c0c001d0112501c201940700040d01d081e0450803080c5004c02d054007450f4015000e4044a950140e00313803140d6200d0030780140d81d8105819400c0105109014218035881158080c05035540f5002c00410743e1441a0940d0744252001c105101040da030002d503001d440c0c1c0c51110540100c0d141e41001a08140160344094855540444460707444c0140e03920082c903900c012146c6801d4400c540c03061041c00c0c000c000b0040c0c0d00c61240400702010030f024a203a00f00c2c3c05e800030404619801d1640c3c41c00e0070781e0002c0d10744106100d000b040340484c0c3c079000040590304c00d05003013284003140c5031014010051030050f90081e100c81c00b031795092050390080208440241541204542c51400c180c80c000308601c000300804400c5014040c0894507514483c181460f00e410300449509030305090504000091802842802d110b003035500940d004000300d000580f1409028100050310703490f002c00050854507992070000142d10403026180440c000400103110321500414 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 151043030 1250 151041780 151041791
    0x30b03030301090504170a020d080a02070803072001020c15010905040b1b13031212050610050f07060507050711040605090c0706150f06090504050108030405100504031704031103060c090103 83
    0x6c00c50000701c504260350b03048240010780800f41d0b40c0c0000701e10741200807568030810340c4d170740e08400c2c41c049008d07030700004144100c00c00100c0c1c8024440c01c2c690440d240c400366404081c00710703002c1c081e00320f900108a03d82141c110840c06280030044501a0703006100044007031100349016500d055400100500801003030303c01c803604850546212040e80c1040411001c510140c2da224241303212032225000700d210004121815800d03801e0450b004140c0642d4000d4004403a5a018500549244e0442000724460311010301501020941c0380c02040d0080200b078507241d6440d4850305024400c0c01038020384034040c81c14010100840c0c3c030b0360360b80540c1c0300b0b9150b580d15444944030300c2e00030060300d00307101d4191042c26800800303c1d00c01d0700b2180517021155039494040c07419907100e05000607a102440307074540a41091104201c5424214000c4902035150318280e80f820fa100d588030204982c078030660009142c00800c1c20f204010503003901c2e40148904400500991816200703e030050303c2400c500354101a00c3c0ca = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 151044280 1250 151043030 151043033
    0xb0f180c07020306040602070b0907241806080105012604020105181302030603010e0a02060909040519050a0201030b031b0f03010f1b02150106120b1203070501051501030b03030301090504 82
    0x44141d40615600800b81ea60340d04050600e440690445102510703408121000f28044180000b450001c94640030703a40203010401d1030f51f454009000c4510081071141d00348038100b2021941036802d026002c02d0b103415159504220006080102107006020100300c007132000741500c11040f00095200b81e0920b425982d0f61940320b40c2403d5005d020a2507500240d401c6c0d8450121905034003e944142010f4000b0085e00690101090ba101491500a900328000f08110540c50030480408c0303034054081c00407269a039408203490146140150803d41e401c1c0c11041c40c0c0e07002c5684c0f41c001c50418030700440041c42c441202110305019021540c1da0b080c41141c01402030b03505500e0070340008542d0030300c0740800c110440c1c840c040d020b444440070305880014000c45a0059410312070004003070581c3c0b05e0b503403074081211074550104010001d00142c1c0c1d42c40082c0040c81c3c24000307000c00080c00d400d03114400100d17a504245014640c1c9111016080d810b050808260161a40300041600d0445500707402c00718840d1030307a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 151045530 1250 151044280 151044301
    0x11070e0a15050301050a090308061005031302040633050c100b01030605030d050d0b0105030f0a020d1104031202010c030209030c0906040f020f03090d05030630030a0e0102010b0f18 79
    0x1c0e902c002e03015400c110401804c400d1580c80f002c00d1034081d46504007030742d580c0420000c0e000c626035880b80110b8010b00c00314082c1441c001d4a04107480c400307407001410304e444034901d07240740680c0b41c558000e003a0080c55403d0150618410600b0034905400c01900b0a2201e25055480740c60042001c00c20307940d11070307080704943e1090300550014070b40a01070b51031210010400401c554081400d01e807400e400d1503a8441c155100c0e03801c903846600c0c0f00b0025031807902e6602140d0040d40c006040304c0441034550580380081d2a601c4c000380001d500c10441d085064100020280c25030f00c2080110041c0b40c81801454059140803c5059101100300d40144040d03407804009001020199500500307a031001c2240400313401d41c2d40044d40600690300c11541c402158080c00c9400344002c03100d45802484031003440b099a00b0441c4006c0000b0004007810002c2003aa4101c140b03143c02c9607000c500020035802c06000c49503028401e6018110040e107a0091203039140c00410101034082802c2000700540900003403500d00e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 151046780 1250 151045530 151045571
    0x50a11010912030e010c150f0b15090d0501140a020307170408160309090216020a12080d0b21010c0314040803070f050c010903020709050f3709050106030311070e0a 72
    0x501081440f058002c2d43d0b00740b002040241d624023500f41c0b9101900500c0c0c13070516440081d440c4411001c44c03074035a421062100d49c00b4840002c40e07d96403620f0020704582e044410707840c8942d09080006881b0b2410b100003c20007184910105010440030302840049118401151a00300d50064006030025080c601107035880341c640c2c04030208030701c0401d0404081d035000f40e0b40d04240b4003c44000e00c0c1c0c0e80d1901034812160540c0580100080010440c03045400d803a80c000503222000148800980303510311003980c00d1441c0c88071500c00681d54480c0110709481d00f61040c200918400a11280140b90035640c0302c201d444080c1060040c0010100c078801c6107449401180c04115030400280700304500c901d80a503035065140901901035090100148847c4100300c0310b1792050200c49600d04d000c00505280c51440c480000072420b0303050003600a844e03042c110340100c0c442c4134416400040c10340e2071750800808501d2840c50b401d103240c0219408005410101003407541040e9800da0000346040e00a00d911112076 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 151048030 1250 151046780 151046783
    0xa0504090608030d050106110601050112140a0b0910050d0204020310030206041205010f02070312050403260402030c0303120a0e0a02130e0601090e0a111201020304050a11010912030e010c 82
    0x41c1829000b00b0407001c04005422405128502070029980364034041e078110035440100640b541c89071004011035846908600150403841d140001c051009181c1e01500c0c00b0300b191101501500d03018125290709004600d80ea10401c0710a0360050507090800141480d0403d0b140603128540103c0030401f0402042e5508004503801406940d665641c0c400003100045c0300752060300c0e154a00002042d241c1414003c03034900035403660310340040510014541c401008085c00c254108103003100d09484100350003804c110b01c0e82115460b20f001d46400c1c4105403800e0f0003103030800d000360000d10261002e07415030119190031000035003020943c0740151f9091403501c1081c400c0a5032000f400070b200f007004880c951004942c00c3c4101c054071416a240d002c1d200070382c0c800b2418142c8a40c8400d1010020400420f107142e45008001c0c61514203111030785403e802ea07041a82c0681d560341100741c51500f0440608000204e281083c05c0030740d180780c0b80000491802c020807801a050100c0d104039a00348c0c0e03220388145005103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 151049280 1250 151048030 151048049
    0x3020f09041404110a0608131403031315020403020a030b0a090b1005030c0a0b04140105040f031a011e0902070201020102120106031e0e06070c08070618060b06071104020a0504 77
    0x1900c5004051400b00c1c2c01d4606403003503a6107803141c502e113003003040510040c3c81182e15810042e0b160b5250065065102c5001603c00031000c913119101c484051005500508114102d03100d48000c1d81000a0001e800b1f0309140d04440c41080200016101c0205038000c403a001503250034544d0310030500c1c4003d0700303001038002c2200c40c1100811a802684100d0350041da1415000c40d12161418018002c4008013802043c803400c1c0140020080e00115880007410404103241c51418540d030b80e5084120303004550012190034210b03907100030560180414450052100745440044498880342c0c00704122001e0241c40c03480b907000180700041da4000d40440c0e0b4004048103414280f5139450700001c0041c003402014800c000300c0e611102440a616018601c40c00d0710312005405562141801920102c82e440e10407205507038144201d401050b00342c40f8170600340103038040c40400b680403480c0010440300d41d071004611400082c440023000c01d4144101109110b0306941c0103035a038560000aa41c9030217540c2c81609031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 151050530 1250 151049280 151049291
    0x708030c03040b0f061e030f07090504120c0f020603040c0b0c210708091e03070303080a050c040605070210030f0e1e0f06071206030b07081803090d0303020f0904 71
    0x4035405000114481d9000e070020000584503106142d00c0100241d8406610044400420346180107034480c1c1c040f5000c004044655803c01d0400b85400c4c290b640d4869041d0301e54400421041c40001490140d00703085502d000302e0078459903960500720401c0e0030300280c0100c8020002908000002c008003000e8901004800d860700403204195039200690442903124011031050603059007910030503101015400401c150418000030107101c0d05140c50400c2c0718801c2c0c1040700104882e1401e005281c00395020b40e0344d1000601e00720301074005448014124454102c2d08108c10410241d11005452460b64121307032040c500c4c07220000444c0941845c014802c460780c940400d03280171a40000d240755009240180180140442104480c0c40f50903036031030a02c003504502c0004815034031072070301c0f0141401c180034001030894403a101c5046d0b0075000c40d905000310b07409100340120b02080c3c2071910000006400214900964803010411041c0741e1a0700900b407680202ea203074408030b415000c0d0740c0d5100025100700003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 151051780 1250 151050530 151050541
    0x301031502040e15010f090b090f0a0e090a050105151503150a081005010515040608041502070b09160305070618081c12061203081312021f0e0c010f05070803 69
    0xc86400300c032130403800300310441d1600325981e00401100c000c4031070300c0004604101500c0d040c401440c000e8140c0e1548060440804150044420102c5019900c0b603801880036000300e20f482c5084a90141060200150310384020889603560403047c82101003c00c2c45c0e945a03140c00761541e81d10701940c008198465005580450868000545018181a01c403c140540e91b81e91050100302400c0207a0340340c000008010902086005014860b00a03201e00e42505488007060522001c98024002c01c0703130014400402e00c1440e103400c2246020013551070420100c0d0a10755692240d8179a02c2f849008144000400a8656826100341080007040280300f030300c013000343da413203912207140c1c40d4051030000c100900700032046120244101025a4040710510601801d5502c00361424034008203014a14001c1082c003100062211228800c0070140350000d241410348400c0d50316008601e41803001e200b526240601c40d42500000781002900801e00744500d03600011f80302150540700340e250243c003008001040c0305 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 151053030 1250 151051780 151051801
    0x130911031203090c0a0803091203130b030403080703020307020703061a060c0102040e130f0219030f031d040207320d0203041802040602030a0e030f0d0c050606040c02030301031502040e 81
    0x521512040f01541c0ba020401ca00300511088980035980142e402170104040904143e00c14065440c00032080340c2c140301084003441c041e0982d5030805280950084103000805401442d51034111006040035820b601d8007410003582c440042c800030300010380b981c010f00d880302c6659000340c03c240b5000d80b0351551030310810460307400b035400391244105040740840040e01040e055440d141000b5408020241103843c25000c200001898681a800182d00d8200c000005807a8915069000b8800c0d01c80d2101ca0083c1000541400450540180100d00401005c00000c0c40141444072940501b10f1042804407900401041090303100e480d5400b81c403858030720518140c2c000028104032074030840042c2c000b07c454a000d030240d015a1142c040568000d100000817940680100a800d200240441d061600c0404010786480c070301e41408070100b140320000360280b00f4207024545c0d0108042c5c80501c1030580d2610000d689100520015280006610040c50a001160111401020001c241d028981400702d2101c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 151054280 1250 151053030 151053037
    0xa0b0a170a0209010f0303050315030106090c0c0c0608010b040e0c070507170606010c151a09100e09060103020a1205100504140f060f15010908100204080f010b1309110312 75
    0x6910030070745480005041005000d40030146c81c0d25649030307130550f29803c0500d01c3e03035254071804581c10f5484040204080c1030902c502d400441e400d42d94825108018148400d0500c4a900300d60b04102e020b00041c041482c00f081205c04440715070140c006241d17104890300a143c0039210f4018000e020384000000c09080992804601c0360045068940b10b440760b0303005644d02c3d030241c03400a019507003102c000107030342c201c5603c0007411007590721480803003540740300002c0c2030310000b103800310a40b0f0a21813051060003111980aa881010031000346819410f580025144121034030170b12144a208440c00010041c090019542e001c1a2040500c40c600382480e11300101813a0000d001c25621500b071030700084040001302c00c4e01400c81c000310007034142c0f01c1c0c040c2ca002d40990446502d040c002c650710300054440b02000111650b5101120068485040009080c01c090861390154242d1303040c00c0002c07041e070741c03078400d032104044082100040980081c0b800710b4002038403003090740e81401680c440481248100004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 151055530 1250 151054280 151054283
    0xd0506010302010f030b01020d030e0a05010603120e030118060b1504031a06030c1005030a020c070f03030e091504090609020d06050f060d05101d06040302030403060c0c0b0a0b0a170a 80
    0x8280c011320f00d500c0c080b4200d40000d40c2690050b4030111550708160f005e42e1008110b10b40d040140da90500e0f250316807900f0b4548990089800c620404181d440b101da2122803400100c0d0b0403030090014500e0040c518400f4070407880b0103000380366103000c100141d55071039100078840c4078611640c84c0c58541c2e81c10403038485811030544031980b03040900060024940441c8100380c000d0014040c003640002c0c02411500fa4100604c1d0b610b007582e0170850700c400090304210000080041c0c04003241140e007140340040051000ca07041d140102090414880301d074503400125582c01105030383c00a04c00b64981080e0001c3c0400704d1005e5000313400380d2041424801150000c0380700f440710303041c0215580c8804091020344900104003508540180072040181101034200c4e21540701c03012024492600300c01805820440d00752009c40159000040820811815000c0c1480c2a492400e0800780340b90309803607481c0b5900000b0a03c0311002c0d91042c4005c40d0ba940c02d0940005014500803103081e440ca089080d65a0f800c29400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 151056780 1250 151055530 151055537
    0x1403030103060c050903031209030903070e01050f0301050f07050337061512020f0408010c020a0b1b07121202030c0c0708010522060603150c0305070201200702010203090d050601030201 81
    0xb991240303030300130411200c560b80050300852401e0485e01030107891050140032921240000c00031101c66660400161015020400d41c80c03034254034100c204942c032104607441034000e904210030011a07811441c002580000c05090980d40d941c0d840b0350302c1003921000d00840c81e8050890b49006d83d00038000b44070080c040c540c8201089000e8890002d00390562003580031000088030380e840c1c006684425000361a14040e503004444c2040e0f101e000107420344030304d0760390000160300041d2441e043c00403650b83e007a00002d03984140f0140030501031100041c0c1c810348002801401f400345d80082c1030382c440c0082c243c0d9020b00010464503820a00d0104000b94022000007141d88550358002c5940d80b07040c42070380c0c000d2075440886810b0f5604001c0c1034422200e03c0e0016108941d50380800000b05085010b00031506140090018581d00c0040000d012600080c0184007160b01d4204003e0032440031482480e00003004032903a41d1180d50a100407491403246102c403c0e04000c01612010401100040c000e05a0740300741c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 151058030 1250 151056780 151056791
    0xd1a10060206071d0d061d010207150c090e060d050615030f06310b0903031608060307061110021b0d230901110307030e010212040b25140303010306 65
    0xb201144c1690b26901032881000800c900c5141a02e000d65103803502a00c101c9012880c078010007036001001c1b0b802c0c0044515650005001c804202c4400c0c21703890b60b0402d80c5802c022003100c0d104010410786050103484520341000e130100e5542c2d918849052105507200d02210140d240040b21514050480390b40c042c064854212442c110040100b41644148860303d030764a810102000b40d809960083d01948c00343d0250840da40012940c040300b140d104080500c000c40d961f041041502d411082c8001c2c00400b0401e202c02441402e170380100c3c00004a4910307261034400e810189212608040414061240840c0300103101e101d0841c100b10f040082e0404941aa550f5907602e050550f85e20100700201c003051580d0003202d07421484020050041c0403c1858120b41c20550351500c0d0749554442c642c15000314003440a4054070750390402030718201f50b001c00b00c0c0c1400c0c03e02c1d2000f0208903000310204244041103244141e5103c00001140810301394002c0040c403142c0100b020120b880e41d00c00e0006480b031600f044c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 151059280 1250 151058030 151058041
    0x6040b130b01020709110d021e030108010c08130f0201030b030705032401060201020a0c14010f02070f0b22020d05160b0409060e0c0f07020102070b0c011515020c0d1a10060206 77
    0x52203404021404040c015107000f02541c0407c009520400c901122850002c1d000401d0300200006075000e810608000201500d1403200649801030090000002101c141900000182c3d040000741031036a0a00b0301249203021000003e00344400d6421003500b5209202c0d600c4102840483c07024070b4001207880701041c5989604c4101c0c00e0744030b00010100491101e402c50b000103110610510450580d0714000507205040b0700d5480266800140203a807000c4101030700200388a0b05902460300415001c1d1014441483c2e5031103042e10103000b56000e03104000c01004c1d40c0038810203002d0382070020481c2480c0750400d91140b10200b0950000e00a841510b460940040f6914540442c01c900420801c40403a040018034406024250301004e401ca045004861300081c0f0b00f10403001030001041a40008a8588140d007006458810254007404a51070b030384004280710390300441d000090040036648018568101d040225900c1d00d603012000d84881d021082241e0415203000780801c0d10016402d5485035150b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 151060530 1250 151059280 151059299
    0x4020d1d010c021207060609060b0904150f0b0c10020c031c0504051c050c06190b06030c030619241d0102250503030c06040308061905010806040b130b010207 69
    0x1c5480400b69100d400d2204c100c000324000303008914807940000c200c40da2160130b0803003079803440d502c54508598081000107491030140a00c0001441d244008001d0502d004500f00f188440b034071540c0302111000403100300b201402c1c4424115000915402e550303a4100b505026030721350040c96503008801601c4d0b45070042c43d070540a041e0160b90440002c01c0c4190446541c02c50821075496a0418018200400703200c400092218034802c0884c6010488205000c483e1001034841100c45207201d110200100072090540784280d03a000707802514003072540070b1b0340300c48824610180d8015031038800a400e9682c91840c45c01468218000f040d565054540000d40e02c2015084411403505e40960130028a1030466488800004507030f841103440c14030440c0c1d5600202e0704640c8107040c1d031f880e185c00860421046c0340c1c01501854112200359200c0701c180300e2010200905456500400341000310f20000301d0115615a04040d5034840018082402c4544d505c80000043c4101500700d4054009d803400050074451 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 151061780 1250 151060530 151060541
    0x311041805060618040203130f0308070807050a0207090207050c06130f050a030b0a200d02031006020d0912110418121805040902030f06010608220206070f0c0504020d1d01 75
    0xd00d400038409003c804e1013000040c1d0801842090701c24840100c030008102184198a00380740a03480c1c12043e0b040213000108a490018041c9080c084202b0212030401d07030020741441110703031003140161100003600c0c01da170815415140860f404080410035044040c8155031540841e080b406160b40d281e69a64284841c0d0a65031001a09042c0d00500141100b1900d0b0440c85405013845070100d01e0540e041909041c80e00300d20440f00080354080101315111011202c003101604980c00240305889202c900144100b605000b0b001c21812004200000c000100c141104e403850010300510a0350b50703145141c401c0e459a40300568002d608050740303181c914000d10088445400c0a4400c035480703410001071102401f907056007241c15201380d03d400c01c02c0110901049020303001e26543e1502d18180003e000081d610841861241040b00c00c0f41c600060f500c0001315607030542d00c4040a018601c02e4101040900c0c2242e00c03072500107000040e9001a00c846500112070f2041c20412002070185000c0e0132400c890 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 151063030 1250 151061780 151061797
    0x30b0f1e010b04050f0a0906120b0a060e011503150306090303050a1a0613080a0308180f0a03110f0f2401080a0b0c0f0d15080a030905090703110418050606 68
    0x20003c000c00c0c000750500002c4104078040107004181c04a91351040c040445420f6481001440d007400c003c6000c02403088802c0c4d0b0085584881801040d003440e4045581744010b100700010840ea0781076030300c5010b0182e000251008401e60300c442005e0b0740c80c14003001412003028110700081ca0940050403001c1e00e88281ca104641ba4000040480604000d0240c142d200300e01d03410030480c1004002841200070014880058821342d5582c6050901d80400f1812030300845d0b000045402c0005c044030000c0d000105081c032290185440c1d62111002c10342c1e9400e04901c0d514011140c01000c6d5904011413000907030480501084c0704004d11802c1c20101500e69910070302405506030004294100420f59008000341c00c154800c8219240c180c0741c5001c540c09501c40d40c884400c0d903450302840071030710ba05c61610900426046028190300741301690001c1c86c109950080b64401c4001c0e01c08210540d22945c070040c0c00c145560301590391246c540c924203084140e07810103174074103908000000d41030381001010341c0c0e001c6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 151064280 1250 151063030 151063049
    0x603020c0d0f170a0902030f061b0a170906041101021b091e010305070518060607060926091504030201081902070b07030903030e0105060f1306030b0f1e01 68
    0x2078000070100d0703807040081000d108020800b0f454410105440000700c1c05608081000568000c00344141130400d4101c911040c5107130015010000341c4c000603446e146203d07101030440c99488218410a40780c1d190191512000001c0c010201b007a0b2100010b100c60056000d6a88101d14444481c0126590007440002c207440702c05c2c40c02302c85c1079030402d0200240c2246681e826280e1041c2c3c4515280c0c5549001d07402034856038050007080280b800e0461201d920000c404600c100d051602d41b01190052181e28401420150744075040c9007481400080600c12529500c009408030951a82500d1345801c010701b8680f09107980050a0510100c450440d4112941a160802a41d03a0048640b0281080d9610b08142c25002c200c2100011143e224880c030903070031030b207001842c2c02c41d07401c1c001c08441240c10f010441d80e05d0101442115a51000165410081100c50708001c41c80d403410300c07002e8aa182c2c0001c00c220100d00500c940010003003a107600c80c0c5140c92108411a1960364078800b826020310819051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 151065530 1250 151064280 151064293
    0x50c040513060f0b062d0a053007020102071103061303080907050d030302031f0305060612010912020706080912030606030421050d0b0d0c050f010c06140109060603020c 74
    0x2d12142c1050f40c940c90034500c00a214101240801c05542c0601c41500384015030f6405800c204410980700603004030668002400c20f260b800c0050035610404000740c18407007104101c1810202c4000e080110840744104000207070030301041c040e0207500200422074803084222802100d40c1000104180708941003440b034051904a624291f590240140000c071050244603408249900d4031700801c500300748241e030010782d240f5118102c20044106460064081c41d40c00804002240d00007410a4001070101c1d100c04000c03d0302407009004209140b802007904c142d40308072000064000c139400f8101c0d000758460219560302c20b6045034540c0340e0541010f105c00014800b042403410110003455209104041f404103014102880c2141c112441110b10001000014200316130003c81c040d2658810050b185040d040c0307140d90303a48103010428082c590040342595180700c5c26138842d0000ca1381c00c0743c01c0f074801c010100070019601c41b580001d001d0560303120b08244002030110302c43d108442d024040d82028100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 151066780 1250 151065530 151065533
    0x1d0705090c0a0f140c03030a050601110a02040c02030405150405031212070804080705031306020d170606030606040b030c030a050f04050c0111031c0603050705030703020a0303081b0a020a050c040513 87
    0x920140c414220010060f05440607070844800d5001400c0a4175018005e545a10300031440405554004003002c2c104189001001d090000001e07a468032b956040790f0114924202c01d00072851402281d200c264003500b0b0302180d03040016500010400c0d160207400b0382c0e054139449401c1040754400c4141c01348020003c100007031152403080c150a9000b610505500789070614546500c2c5c40c640041d4410b05260400321f00c100041034041112005002c601d00b0824201050381d252111000c0c0004c1000c1e00500e40003001903003607591503044401405450a03680d031682850740c1c01c650560000c0741e02462203450310001c542541e566020726031085500c540140744036480e260045a6240c21030201a11500c0148001d030540c4081e52003401c458602c009001a10300e140d0304040c1d1801165a000e28041e400280b4144050f03103a6400c0181501d41608000c01c2c40e4540d21481855100100d08502886401081c2c4002daaa404520310644d1070140044966130f550080800044640a980041202006420510 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 151068030 1250 151066780 151066787
    0x10902090102030d0c030c03061a0f090409050a03050d05070c1716060509010c09050a0e1308040e040f11040b060a0e0303040801051018020901051c0f1d0705090c0a 72
    0x224800040c410b0724200440a5101d0085e101c5550481000c251a800883c0344141e040c818070000703186a480711400f070010080d480d5214840d8100e4100d80500001e20144a502c0b0342c1c00c901140c660050407140841407609004000b600722180c090354003806c01001c500810300c60b0b0690050160040c561003030386c1e8100340142d01c10b940300f09030f240d0340f0742c0042c00c2e603a001c142345100f0307540b06007030020011030100b034421002014002c094001340c0c0f0403051050180000b124111203070b540580005007080c203c4103103091040c441d00580e80480541151001000100a6001809446240314984032500800c0480410054600c08084035411800c02e10100703207071038881e506a03520341c2e0015060302c0c60326444901003803c1d94001c03a1189035201410a040043c04407030441c02040400b000c00031400c054402000820718410420001c44207c3e0300041410445041e92051500d0114050104505140c154011114444151f100c01c85800780482c009030710300300720201c0e502c2060252042450001d40d20800e6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 151069280 1250 151068030 151068037
    0x9070603090203100f05150303030c03010501111e0c0108060d0f1e0b0c07020906010c03023a0807020f0c0d02120a0c060804050c0f010f030c1b080c0c06040509010902 73
    0x1030b641882001c1104c042c014181c864002c0030804100007081e02c1c58260317085d4007103030070041d48a40a035004000b00030f103034020300301500c4c1501c0c82441c10001d101640c01e200e518007030032150f802c030b42c88140c0c40c2907180708540014045466030f000e0302e510380745568560410005288500d00034020008003003070780780000d003490f404000740a620b00303002e0300922460f1600d95402404a480c200c0060001400070103602d01124000d0b40b000003480c240140501a640c0292a8040c100300039413404410148810100796484074059400f204140c2000020349a400040c842d0000b80c583d0701c054000c041c2180780314480800c200121101c06080c0e554840040c2c0d00340b00300303087d0400b10140d08cc010180c940c40000e200003102070003400c655440b0205400c040c2803c3c1d042050480c1070034441c1300c2d40460494140d8001d8400c1d00607941d141000551210450b409850043c5000303040d90200d0712010180e000c0041d4900a40b5222100004840d1014003a806100c0d107480b8030b0251070b5001d005000100b0402c03030f0031b4005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 151070530 1250 151069280 151069283
    0x8070c26040b0d061215091716030f1e140d0504050d09050303040e0412091509090501080105100b0c0102090925030c0f051b0307030206040314030907060309 69
    0x840300ca0380315052100328941254020303000200000400100d03021a43c011000940300d04444c003059001140d036001050f18a56400d024482e403034046040c2884010001108412241940c1c02d5855000409410071514800400c5020510751510038410031b20502c08800143c1301841c018421040c1c02074190740f920a400619a6000b5042000780340214050094034052481030000f04000700700707010041c1640d40260030060103a481400f0410410610003155900f00b50095003181c000034090008940d4040660031440b01c2c0300031725040203862075000050304100e800c100b20400040c0d80b0350790994240c0b0b00a40350201210718901061000b22980e6000704240700070740c400103203004039007000304403081d400301c8040350000c15102c0c0c0840107068252030700c2085100c61030b04000d08012290090f002d41d101c01c030081e007000004242102c92421041d40794602d0304a00048a4454042380f40096958400300c41c11000501c1c0b1940c8230040b8585003041c2c0c0d000b021f00307401410485040c407804500038030348645c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 151071780 1250 151070530 151070573
    0x615030d0c020f0406030b010e1b07020609040f050c09040f0603050601151e02010902011706010c201509010207080a03090603020315120d030c02150a0506030f06090604110108070c 79
    0x200b83c61035a0fa0303440b03075600452162038000001c2d850081c000ca040c400c01012100501e150310810800c074003120040702c0045604803000c1c0e89442008000c00c4c01806040c2014a01c5440e200600c02d00e0b00000000d0034500c00c044a041c040000040f4a04080d940588001030160b4003070001032100420070f150b1900810381610f0040d1280030b1458024034109010805200035035901c00b903d034191350703210040c46402c0390041800740681c104800002c10310400400701a001000d41518181484100d40340300f0040080103001000b03903c01c0d0b18403050140e2016107241e02500c07803c6000111010003203a40120140c043d01c90040e910304c1e10300c1c250042c1d8070040000303400030300c194100c480c40d640e09030050342000044002031115a40c1d02d10068100d070b10070342e640c1c41551b0012030443c43c1c00c0030010321207601080d900000700b1242c13210b0002c286040c0b01a08214900d000302410001d0304000080c601c0d120b50301a020011492102d0401500c4403841500c40c1d10020b0710204155020404208126800b02e58822 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 151073030 1250 151071780 151071799
    0x30402030f0a030c02030d08040308060d020418110f04140103080304030c020414060301050a0501150c0c03021c05060c031b18090106020a060501050307121704120609050615030d0c02 80
    0x901c003600341801000110003003031425150301c06504080090030f921681f2410074484d141800e8501604000000b0078580c447c041e055010011512540c01c40100c1500c85144c03032407600407a00d00b21036000c2c540d98950340180c01c1070280c68100d1070a4096501c103805100c0d1000d030350340d007541c41e60f0401e5407000700107405200c5030441500041e02e0310710038592080410340110580c1d0030040d041500b034070300280440c40511f017070400601c032070324000c0c0ea041c05850190400110340c1601d0300c0e00c0403142002d51b1020f0760280c004001c0781806040c0f0170b001d424241c850002e4030b20341e64801105030747d40d0000b51403240180c00c3c80b82c1e4034184480d440380245903110ba4400c3c0208900b040d8400186114006d800c00401600030034854010002d59000d01030142000314043d090903030402c040c0c040035900c05903000e001e12441200b61400741303000c0e008840241080c0a40842c00301750701e040c0140a0004240b0072502c0d4070405000820040300103400c0583e640c0014040d0015951912003268608403102c4140d030300c402040c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 151074280 1250 151073030 151073053
    0x91a1806010905010608060906010818070f09020a090609080303010614090d060209040f0504051c0908030408070314210d0605090406060e130308010b160f1103070f050303090603040203 81
    0x411034940202181d0001003180d42c1000001801104042c1c40326000c0c100380c000340f100342e0f070b005280960f00a10b400408403030720740d90700a030034500b40c0164171544035850306907404a40b61041d1b400800360001c05403160200141d9a0344116101c2c2c80c14850352240f0303001840140404d500c04c1818140261881d242d032420a1101400070344651402c5800711012540002c0490301803d05001c0d11900d94401d01040050345096141e02e6281c6250107070103a81c00c0c10401050940d03501407803010000d0292041100e07255610344080e103980b11210b000a403010298040040a1501c000800030a51034000b5040e036245a400039281106070002054045d0712501d940001c035041c1c988031030700c601c00c600900001c00c900c0c0ca40030b004a200040900b8410800c01269503141c0401e0f00f12610342c3c11a002403241a40c2c0340407a8819050074a001070b030081c80c281d0401100000d206c000e40030000124000c0382a10820b0340c0e600c0860002540611403650113400920040304285010005142e11500103002ea5030b584400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 151075530 1250 151074280 151074283
    0x501140907080d033920061801290301060f0b0a0e030c062d070f1407030c031406010906060219062a0e0103090804210c06051c091a18 59
    0x4c10300440c0701d00200442c0141c02d540c003510b60a445c0c0f40c50f440c04107149060680461316030350000c0c03052304480c031182c810f54034002007507011421501740c181e6400c00d88152400c4a50707080d0b12401880d8402e40c2446404583e40029190000446000d00c040d83c0c0703000745254064036810b4110900d942d0500407022481426100c0300002d14100d561a03803034640c1c22450341e003140f60344080018443c04545083c810b00c80056064446a02c006801203455600d182d0903454840c9000f5035504010701d001c118110020400c24002c42e901c1c1e004c20381c0e109070b8030b990380c9601d814003c0700c00c180f10309801030b48a00016118100c0480c0d0207404035003d0240850403e035041d26000072040c0e40306080d080c88194006441d4a103500428404103480300346400e0282e444151900aa680101e004040c0030121001304900b10724071105520800c9940005650b80c0b2956861001e00190003031511220740010f01440501e00316403030320030315207026071101000000e03c500714490104c40b40b0040503450215401c040b02d4180c0b550 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 151076780 1250 151075530 151075601
    0x3080c07032a170a0602030117070b031e1504060e0a0b0d230c0a0312091208030c030601050705010908090109080a050601060e0a0f032603060d08030c0f04030501140907080d03 77
    0xc004580d80d0407005d002703036001d2420100f0b9002d040c40c41414424020402100d455400d02c402400c81c03030101d09d45900080c91069030400695070740c850310b00b080024404011181103440740d400c4003002c100001c00082030011091100400038500c036040280160302810300a05c01080e030b2401c1c0101c2c0c20a1403401c000c240980313519002a0380900b030401c800544a03034001070803805400f1000c902001d00c04641d50f0340d030307036400083c2c082c0020354404070000b00e040c1d225005540f000e13501302d4028000b0489a0400364165801101c041c2c1c000b03583d600000c03502b41c60000d403500005a00000601185c0e01c0e04404443c0b425124400070761000c3c1c541c1c0002406949c1c011114051030250042010380001000a04159103203050822014001401048610b654581c0e40c4000b0715000580030760f40756900c0b40a01e01e58410782c1040c1c03d8041001c98044140700f0150300c03011040e12500c5c001c0b84035490758407400ba912485441407454a030f010011030000b0328825080385078000c3d5030320101415100740b07010301c298190 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 151078030 1250 151076780 151076789
    0x102070611091f020a110d020d0614010801022a0c090115030c0e030a060b0406091404050c09040503030109150b07031805060a12021303080c07032a170a06020301 71
    0x20340124041c0700c14500001c03c00305001c034400c0904540241c00c14065182d01544034081c015211070400e201d8103885041e5180ca24950007442c1c01541406498030100504c100070741020018030703900c0007084903c814030845120cc076a005100350000f10045050041d07040c1c003c00380440c1d010701c0c41300418030703213568040c079000c1e240a0990700344038480210000e003100c120030821810040c500c2d505c4c54180d01c002c104a2034882c2c1158000c5501992040814041c00b55a4441000d8600c2c04914001030f1541c03148440c02944600141c50800c80c0c00340c104a54041d007074078040c0c01e64104000400814050364014401469000c44e011055540c038111807069411245040d0049802c41c05040c0c2600c003004001e03409498112099400d007683c0460040c480603962068103901a4002000c3c2001c401c417600c890025540310610315a517008002542e40c071107115100071224100d00c420f40303210b1000071000d0000c4c00c0a1040c2c40100e182d00d03124040e480305500b8280106a40601400e00001c5600303030000718082c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 151079136 1106 151078030 151078061
    0x909010608030301060f090801050408030105061303060c050405030d0f0206180f071d070914011b02030609061608190b151804060503010c0e040e01020706 68
    0x400240d0003460301d5100100000030829071095030340d000c17000c8075515114644d6a40750400e007070725002d0350018a400c0060005100d281005806094620000300706000d100c0e81e00d482e9001140e02102003840050070006040c0039a060070808060703803c1030f5107881403040c4407c1c1c6d0b00039110301010300681000090340180d408020002c000030010300c04130805841d41c10359100310031000007000714802c0b075035440c501300005d00b5030740200d840c07008807907480941035544625000111805d500c1c0e488000341c528021484240075840c00c01a5500c9018950001c00d16404d00c440f000e44c40403071401020782048035000c01c01028519038400e1001c0003445c401f020800a00d8200000d090804101031542098030115141200d10158001e10700c0400342074a0401c50030707444005060a881a0304445c201140029060345100c3c14035510961202116500050414525903902000e42d14803c0c60740411 = true := by decide +kernel

theorem cover : BRFrame.Cov 150899280 151079136 := by
  have h0 := BRFrame.cov_init 150899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 150899280 ≤ n) (h2 : n < 151079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
