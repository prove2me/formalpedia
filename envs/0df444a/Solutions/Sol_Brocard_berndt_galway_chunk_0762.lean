-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0762
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:38:33.053375+00:00
-- url     : https://prove2.me/submissions/839cd9c5-0668-44f4-ab19-54ba77278fdb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 136870503 ≤ n < 137050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 136871753 1250 136870503 136870541
    0x31b15040b090405130c0315110c060402090f0405060f04060e010504050a02042414060405030a0b010303080703140a1a041a0411070b0408031e01030803070206010501110a0201080901 80
    0x34000d018016070200310303014010f61501e400141c0c0c040099010802584c1e1003c520f00002d0b203161901f0400d012002d5000b101660f5881b030860041ea1800300400c00060004060301945c40c080c010810902c1c1c0003402d8140c4044d904d0100710010f40003088007903014000041c1210707a605c6505261000342280445000316601e01002d00003404000518591440e00c211810300540540000c00706202da0701d1501082c40c3c01e201c0209002041103581d601c00c1e0749601030034490829030346000080c0f8044107454155041c140e0400180706041e41710100c1070b40080d40d03040500070100384404800d1402e0b002012f0350041c0ba698503804120128055000201d400b005205014251004544c081c0c0664080b01084c450b40c0b03400a42c4184e40f0001c0e00780c0da009900151036040903900c580b11101d07a68001442c00143c2c05c0004401c0d500120180c010f2406180241c4403143c8a00e4000360282c0742513010b802160500c24003401901900c00000346400d0095420302e40003c2d41d89400825601600c006d1290030050345035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 136873003 1250 136871753 136871759
    0x403060903020609010b060f0d1a0a0b0a0e031615020703061b12090b06120304091d060714040b1e07140706050901080115020a0b0406050601020f0309031b1504 70
    0x8002186409000310308002c211b95842c00c0104045480f50702400c000c024800d2185c04650041039000305032844104200a60600820300001c01c0ba44180d0400d61011002007200b03420300e81d200f4079003491041d095004246c40110020f40390590325280c030881001c50480408001c81a209200800085900140c00e03c40c0c030003001e0752a8000001041c00d0400107003101d4007401f030886240140d07800c49401401d011865100c1000340102d07210040480461131100300400a1030903640d200d904241c111001122081400040c400c500382080540040708104c03401554019103200901200c0803140c90740d007025070b943e500e16218900c0c20a506c1050909010100310030050041c0318140c485900ca006041c1d407841512403034141d4050280f00149400218007400500421491060140740f51525004903580c0716880c4d6242c4000c6842103030211650382d203a4003480040d580400001000c91000c5000e14100200131002c01c0d55a2620040d008130302049082005268a641d12004040c40d0410003d0382e403136403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 136874253 1250 136873003 136873007
    0xf0203010207150c12060b030703050c0708040b040302010905031507082a09041506050a180504020703031e090803040b040311060703050405120301120b27060103050111030c1605030403060903 84
    0x4100130001010403107940006002108078420b8100383c0b02000e8900e829500e9000003180200001030201008070410032044021403e4040584000c0c000c040700c040c1da42b070451000404c042c00c0b0794022402640401f659500126151907207c0c0c1c040381c0c51801e2442c0707030399860f02650080f9018031040c0c40340071a46803000040000800502d540001135070700b48481d480c00541c0d122a1100d5105140010780c1c28042c080c11580300ea640c4001c40001c030182c1a0a09880704000348c12a0702c080421800320b942d81025030f01c08840428078101c083c00c4035004202540b80c503192142039120080000306038000b0b41d40000c0405000e5012200c0c0701d12107008548052405080c05801000152801d0b03405218005141c0a13189490702102e0607611600c10040d07a4020703680e43c1010000c2d0240a400e0b50442595100c45685000c0503841d1951104600030076165146041a500b150420400e0044400341001002b644c401d101c3c1c216084003803116a50b01c0b082d01603003486c1d81140190340000300160b00700365040007816 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 136875503 1250 136874253 136874261
    0xf0309050d030e1c20060d02040b0705010c0305010f0b03060411040e07030612020a060804050f010e0307110301050403051207050d14370b0f0d030207081501080a0f020301020715 78
    0x1e1416668100c5103441ca00500700b0036580780c00020402c06100c4091205c80c1080700c000d03002c0d88006800c01e42842d18407030303410050781c001d5080030030304220206506040c800240120303c010452414100b0541d41802004032600903d4050341e40c3c01c0c803000020030415161a4000d4103502d01380002c032500e4a071551844486940243c40b001c0010b41452004580d01d2041c00c1c0e0305600744c2d4000c0180c214185071007000c1d1031030a40204152218002c401b580ea080760401c0c001c0403504803207100995a90191440c2240680c40400c48144c06a0f1603c001c000003c0e0300003085451035100c0403135031f8a96a5846104544a02c125900030000301e0a000800040e102603e02c440e000c1d5850590301c840e40b0608499141c5007008018117011222245400e11510998a03030108141d500060035214110100e00302040b0502c841803022801640668010050a0301c24011980c443c04c010011829a51400003c1d65440e800c1c110061f01080c2001300407002c43d0f4096040320b01180d40800c00002038180007022030010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 136876753 1250 136875503 136875527
    0x1515060a0903050312041b050306060909010f0903051e040b0702060f071a0604060e06150a0c0206040b031506310e0f0615070807060b060c0709020409060f050d0f0309050d03 76
    0x21034010390707024804200721f4034543c3c20f03208013a006000e95542c000c10007803400307030190003518075542e0741c000007281e1201401450945402522940c1d070300e80307a40700b1a101403002580100030204d0140410722040700d190303080b100d4082d01140c096488540e140107480e082c1c80f90a1000380001400c1c8220030b002c1d21104c030700c240b0805044034104480c40e0340b080c094680240489203190f001201498010040030200003130b0031490f44030704d00000c000280b5804246d082d8082d4004207800759000c800c00c140c41a01035103840c0c2260040c3c1e00d65080940b4104415884214540090016410303103a0280294075078072400002170100b020182550300b840c200003840d00c00306844d0640a2901c0c46840f03040420f101d0201c42540b41d005042d01d18140c221340300c4800400c16541c50640c0040100103280d040706042080307101800c0d14030001690342d40342c001101c086501c00d6210301540b0b070860004000036542c03500c0445260b5040b4403068240311741e82c5411250b140c10782e00100c0c0d0100c40b0000c200b040c194407800103494 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 136878003 1250 136876753 136876763
    0x1c0501030215040305101509020d0504020901050109030203100e390901061403060a030512040e0f0709060503060109170708061f03021c020405040b091515060a090305031204 76
    0x4400300b54551102e912072404042c005501c40d4410701a1a81d840c0e2002000d14601321006542c50788907803040090741d0140500d0090252264140020341c40c10344841e90042c070007420418401c6180d0780c00710782c4920300002c0103c03405136203136040310741d4079414000501d800000500782c0c1060501100c15406807444481c4c038820115654019035880d040401d52a4160b40d50380d195401d1080c040704030012903034002807030300c5c0d0071201d074080000c00034030100280708082d031940c032080da1110301302031400002032801051030261401e04001d1114803a0400c0305036003559864500240c0e269194001a80c4440f8642d2001c038903001c144409031341081011030700307000303032180b110039075840ba252040d400441c0000101c0c43c80f05410500800c00041c0b4081c4064001c0001c940c1c40b614404100780c001800300c076000c40d000c0e2145265a82080025503003803140240302c405000c2c1a400360700b040d00104442c0414000340d00d0044c507002407840c0d8507034042d000400003964071904407039a5105000b440d201c1c140082d5070817030f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 136879253 1250 136878003 136878019
    0x108040804120f26040b0705010207020603010306060e0c0910050c01140c03090d0513050d170f0405150703091a0d060306150b040b071203021c09030e01020f12030702031c05010302 79
    0x3001c0c071341c0c42c0300e90a0054042c03d016080a04141065403664800301003203030315644c02c20000c4016110440514021350003150002181440d004a40e4443c2100402d900c1e0004e004101ca9080380e991442c403640625000c1c545076494043c0e00a80e68014503681c00840032000050080196241941c0010351160302081c2c00e8030700c080300f03140c4103580500070f443c40750201a5400c4424045410140d649803403c9005100c241028814100c10402c45e5101003a000b40a9000203010b00081c108840700e002c00d02d00000c51903241c00c0881e10020311900e2280a403a501a00d088240300089900c06c003540d15840312003030100f0540395171740783c03400040c1061960414500380351100001d0080f113030b00030345048610b145021894104245d0f00c0241c250700308191102415401e02c51855022015154042c0700740010720300056800f00e1b1b0901070b008903048000c09045500007102340e0b00142c800700740803048002c100003a5489407079210050341180503002d000c0003544003242980c00c281007642c1015049074007d07500c0351 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 136880503 1250 136879253 136879283
    0x417070615210204020a2f150402010503060d030908030c0f060c070b0a0f11040b030709092c0a020301020309160b0a09050f03010f0c0c02011403040f020108040804120f 74
    0x14016a810741078921080c5042c884000160920b5001054000c4641c585a00359441d11464030900700103020750814000301213a50215102c0c410002d000d649180004002980c0c03030954002480381c4070050042e401b601503035a01508041c02881c0c00c030050075001c81500d844031289030f115540d4000305084a452032040201007a85001c0040031111a2a00400800c41d80c1c0e5480884a014101241021400607030324050f81060388a150060800740c03041d0384103966a4248070b5002007091585800000c1c9151901c0340e41c640c103150034108120905030354040003181d01d44030345095040144017a400b0350035500000c10440304220200d40c0349030f04510001500011903c034040e0f8086802070700854004241448024845890814400581c402c4000c0001ca40140401c1d0203100362417803481d407a400300d16408a803600315a007102d42212405071110b1910f003907141c242c66480d099003001d03102034107016020020405200030a4112000383c85044c000500c1c4240b07900e8018107107120410180c0d803100400d0605 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 136881753 1250 136880503 136880519
    0xb0d050a0612080a02070e0103080a030506010f36031419020109050909190b01081b1003090807080a121d07060e0406090f0501050a2405030417070615 66
    0x70106941d880002c16107010110307900c0180503070003010400c0c150b204020b00018408101070005000c0e5210300d0905444642041001d01655005488581407040c581c07007695101d9441611000d181622050450041454203075001050311b984c0c0c0c0914840700c03502c4011090154101039192404900c000701c401c0414441e030000071041c031b0903a000b0f00113031850101b00524584000c0c041d4001075032405035a088581c4184050f4403000c40342d002c07030300c581611004000c003803020b20110400c0c00d8007000f10300c15050341e50001030700c01844500d280141642c4400240c03c1c0300c0b904d41642c1c030040d03001c844641d072a031010001503c0f0403002643c5104840c2484054882c100500000400c0141c041c1c00801c0c041d800c01c42d0a4564820301c60106030800c3d560030002030702c0c0f681030103484003c129003200010254105018030a0070041c0350003501c000300c56018004400e61548080120355442441e01e25101d03200c1e4900546166454288503400700b6021845034140b100e103034404441c1c0e89807408000d590640d21440c07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 136883003 1250 136881753 136881761
    0x415021c06150c0b0f070302040503010c0e0306010b09012a0c06080f1e0601080a02090a030c140603010602100c020309090705090117072a0507120302070801060f0302010e010212040b0d050a 83
    0x1041d10900001203911003995084151b0012424207016042a440b40d01003070841c0c401c0c2030141d0010380380526603140c0341414040d071400342072844102031030a00010000b070289130301c104d5445411032085042ca5007080352020302c1d80591354007101d051072072542d4410040c0f074980c054507012003420701c00000c544010080c481c5280c005d210400c0b9605542c0e5228011344500342c00400c1a04074540070070121595684048010001c2c511806009080f9401c0c1005c100b0b032843c00015072802a40104014807030380b034001a20050910012402080f1060f690f03404030309600607002000c2e0410170351002d025010307170401c024080032076003039072840c00303078880e003203200ba1a4003080e2911008101c1411901a0340c041f525514803444c4400c4003c240f96a0940e03980c1443d0180da507020710368050f1b00000120400d94140240c5004249a0000340112820040e5400840781e413444001d05001d01c100408020380d0090140c02c0c03000c0e000078481900da50b6507000e032011940c01504d40404152400000401c51040b0b841 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 136884253 1250 136883003 136883027
    0x7080705160803040302012d05150d0f1e03050406120c05030a020a0c050303040506011a030105030618100e010c090506030c03060f120619050703090203060415021c0615 74
    0x14104100007050301c0301e42080c1d10290064007107548520401c2303060061080004554180040903020b03440f05030b0192012503070098001000c6140d040c00800d40d40d5141c0070f1011130640c1004502c1e0b83c000044c6026051049040fa48c42e2500803007081c12424580c02001800032118551610400d001801031160103c81c85c0c0818030300400d0f014004182c509541e0b6003d0111600c5c20300381031000c941c03640c0354180b846d0011a4100c481c0da11650041c8030450145a900d0005000c1000d11415541860002901d0390070040880c3d44140f278030200342800003410440b0f1000d0082c04541002181824000d481c082e0505c0c240103000701f03441d80c070300203442d080400489208151b201d103424103607150402045036143d2f08050701c0342d200309203a4042c24148014403803280180f8a010b0703048124515402010252200200410145840c2c840954091303117021446541c0305502103d500c00811803080c030030000380a05942d03192180026100510b214215500c50b905031052680441c12425040c00d080791181c40c0c0c0a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 136885503 1250 136884253 136884277
    0x9031504150605180103080c160b21010807050907260f07020d02071701090b010b030f01050d0201020a0303050601051b0f0f1903030c0905060f120c030c07020d06090c03080307080705 80
    0x2004002041d047c50240001c41d503604150340c40400c07110b00e07000c0300e510070741c00c21421110700145008020078401c111001c0c802c05c0042903056585410f0380c1984800d01840343d0717400303188004001100d0601c10050303140a444841d58410031406550703018501c0c41c5040785d1a50280304a2008219034030700000e014020890381d2f038010405981441d0742c1c0750114514000030000e540d05c4503601400900403120310742c042c0c0841100d450f2a803130903002070400d02e00d060f400309000740c803018510000b41c3d0b400b245e400d012075010b060102d1145c903040012a900e11400d80c1d030355040c02c8054195680050b01260805118500c0011202d259841030715240d190040154185241c110b03d042020020380603070031a0002139007901300656540d03130799800b1030350039448cc003551a00d00400050346103203c0c070354030003460700304e0303100c0c0f0740389040d803401b000e42101b2407080d441c0c007038410400c1d0101202040415000b803600c441d40316801103051507403403900140e543c100740c81c80004100c10900103020b60340301e10180c9002c01c03080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 136886753 1250 136885503 136885549
    0x30f090d050c030a030513050103060e0703020310080f011a03060129190906030f0e070605070c0b07110306010602060c0409020705010e1b0102011404020904060209031504150605 78
    0x480108110300e100d403202140c4600440410311456502481900394140c06500c55940d101140d10112030b1656041d000107060500c2e203c030a1040c144030f11100c83d07000104c2c1c100142e890301ca18140c540c0c0e040d0964064903051060f10440014160190010b61000c1c0d00c8410b0b1070045125a010507486803024007919803401c6148000095100b1f09034581c000080400f01c13558503090305101c00240d49010701c142c06001c42c5404404100c00d5a15124501c00c280500c00c1c1002045107405255848000354030490b81004000300b000703800c0c03104428100c0300801d041c030405652001c4030301d0710a545408a0014a03c00d02031480009480382c00491540d2281222010551405d820306403130308001d4000040541d1103650713840c070400f0344d00000c015041c0b10410609402d03000488000009080d18052414550901440381c288001070301c0b40281d82c1c0d0010b0788040050380b0f600488010074606014211034400c890362704824130042c00035442001020001070314051260b10344603800e0000c0402c0f051200c06600e804c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 136888003 1250 136886753 136886767
    0x601030203041401050a06060906020f15061c060c09050909060402040f1b0e0a06030c020c0409110303030112051902030d1215090212100317090112180501060602030f 73
    0x4a03500650703001d481048518070301c0c1c0c4145a0182100d03801c80f000c52202d03039120380c284406500042e0301d80c01010a03200900c1c080c038580d0480ea40303a00c400d51180d40c4451010300814441d030b84803800000c504d20181031400c5801118240200540b040060302004a1050540400c0300d00b0207840482c4a001600c0c0146829101da60034000108a440c8000707200320790b40d14035100d1208904c2a2007103400090b0380e800307031080340f900200110b248160344440141880d002000905540129800a800c0412980040c004c0d44c00d0624550071072082c500c060b4107000000000c100703080c504280440701c5010300b0031544020100c2ca0780401d00c06400d1000303541540034601203d04280309061040b40e030100c200011524001540010846a801c1c0e040280313503c2c4c0103d400300e401070020200b00e50140074460070390400e5240d600d8209403104c0039410408082d4000600010300c0e4050704442c241034440c52420800c1081d030000b00c030200032500f8401c0340c5550800500058030382c400015500d040e80d62100d024500781c6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 136889253 1250 136888003 136888007
    0x370506100f0f03020f04030f050f01150e06030102040312090906060503040c0b0313050f03071a16081509040f0302100b0f0418060c0818072303010b10090518040b0601 73
    0x1030340c82c10001c02c00d5000c006a404240d02c00010700b00943c480c034151000c0000c5840c142d0308101d80450f0410362070b89031000c2e030410001d0300048403048800581c0c001540382c4400e00401d0180c81140c01c094105a055400414500e0b8040588811600c0e011020011b01d07844503000c0f10944030654015180804015044c03021204072070003580c014072800f03111940403299940300c0f4200804111458490b4001013158424040c4000c4035150500c03400000d101d0a01d842c1e103000b15181a00e02c03181003000035040c0004d0304480004000c0c6113029000301840c01c07520301840c103403e424041036811401030003100e00740814502580148440300e03400801000c00994004180401440c1001d206030102404462400100b0010321910010800c9580c4814140c60258191105d404211070484001d0340003280400a11810041680c2600e0202d1584034032031401da000240500780609440380c0c04555030480845542d0051005412207006868403e0000d0010781d0920705404121405046a101200000c034158 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 136890503 1250 136889253 136889267
    0x2030f04170307050706090611071508071101050c0a0f0806030c1216030615060221090103090228060c0201120504061e0603030905040c0f08370506100f 67
    0x38481c20700b1281081e8080c0c441c42d107020102c2d4072600208600c044c00340400d55001201c0e804111031342000b400700c01d14040d4107900d1403101075211001c1041500c08075003918440c01420366218845402404181001c40d800c1d030a07540003002c180003050811010300042030003107281600c40e000c020064000e00d03040340c06110340d8003a0213040124900604c11880c000d24808126440598040c44000425030070382000b074600042d00303400510175944285220444018510034a6100384101b50705e0b1034650b580710740140c01070007070008000d60000722070b8051400b100d2542010303090002c101c015105159a5210706548030901c061010780028070030000e440541120703401081d00b0034410030300092910104942d12003034031a03002028041c00e4644004100f456801500ca40140c01d0449042106d041000000f42c45c070800151581d003440024000950404100c0800440001000441d0800c0086042c4040d020795030342910244503924103030206a050800701c1c9000803030700058840281d41581c000007a42c100c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 136891753 1250 136890503 136890539
    0x30204031b1d131211010c0815040b0d030e03030d02040e06010306060e0f060315040606020a06060b121609080619061401052703010c210908090103020f0c0304120201080702030f04 79
    0x803020603451128145c07001d11031111000060741c0d490301e0504082103504078501d1192081ca101d45d01b8000e252307040e90795840048035030941c54202008401800408a411030103130607030904900380f012900066000a441505101c1c000980e410483c4035125141550041c020403032090b009844080551910305100c00150b0700944580c1ca07040c1401a500000380035104103800c0000140c00101c4446d04000316405514061300c030800c03484c2d00b8000c84c00d41d0314803400c50080101c10f42c80e044002e85070a070b038002c00c4500b002c0c240203015510f4501c0c22f0a1150640a8410041e01c80d4900c2d00100043d4041c3c600309100302e55005a4a043ca055100c1155001500300070884c000e0480e288240c80203030795003d2003000d9240e8196128180402510304001c41c0e8009035110080a00c1c3c1420540b40008900d141242c145c6842400c1c01619109502c816415034003905500c51824400080c000c00c0d000280c0c2c20303d006d558404d0b69060550b582d8004100c4c3c4074001c502c548000e4800c00d20080c030481c1207000d081c20030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 136893003 1250 136891753 136891757
    0x1602030c030105011e060215060103020f070b04080c07050418020108071e0306091d07050105030705070606030c08060c1c1e0c0908010f09020102060412030204031b1d1312 75
    0x4010384200c0041e00b100c10a81c042040641042002c1e41000031101c2071200401c51800a01501501c004495041d2030000707115504040e400640d0f0065000e0078429175542070b0308806102406d242a01d051a8154849410b03d51a48625803001803503142c58010000340080c48411101c400d030b0140e0043d5008140984400140403905080004d07008071a0300c40300349a15190f45c04504249407071500401c9414800504c1d411082c0c0f40c04202040000040a400300d072428a8920303034079610b9050444490040020045c0581e0504000005100d45850460f041e41c11840a940b12600e034203961030001c3c031a254000703000d82e403260062115450b1030340c040c00514094801c44011000200074000c2192a80400f41c0040341d00c00d1010b1200c0d5409106241118005400400182c4c1060b00003035617990004100034205c00d1765080c1651071600c00d805960045a0044020640b22130000d44c0c4008002607000b12040803085a000280001c080d0b6090b50091400390111103001860740c0b2001d1204554000e1003007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 136894253 1250 136893003 136893013
    0x1a060301090f06021804090b0403180b0409020408010501141305090c15220513050a0209060a32160302120412140319050a03090203100b0f03010908160203 68
    0x8144202c0d0074040191080000503034408601404500c0d401680c1c0907a030155103880030f8080011022100186c1041c1c2506103d4182c80f050b09821041c2401900882c0500d440070500099050064010f8419184483c1c002e01541c7e0304c0700c0c2e40300020110300d04103541c0582c100740d0440701030550b5809035400409010a0311000002107004c5858401014000d80b400c0c50000f650641c2840c078409841d8031494540b00a400592030000000d404040d49001c00700e11542e41c60118080341c0d5580d044070040c0c0d40181845447d01c10918014010154a02424910781044691594400c10201d4a0904055004a21810141c1c803c1c2050500400d2400031000c0d44200c0c144900e6800000c4050802442d0b0000000710694480ca030107174070500303640b501c108190700078844000705002003103900b10000c2075440d006844800c80c0d6001c4014000d15100070350035003d500301c0404062019000740100c040190740240300000f0400506088940b0200c005e003003070310140300c080d50b01015012000b07007850000f01199 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 136895503 1250 136894253 136894271
    0x30117070806010605030f090f06070f03060f0f0315020307020d0e01020313031506060302090307060e030a060f050a05010501180b13050411180a1d0c040806130201090807031a060301 80
    0x902d8084280c00080c04680d0200c200b244085110080c2640310080e4009401d4400d201d54106c0d0351100d0240c2190140440c2d000c1c00c1010070b00c00e60050000340807102c0c9200400d540c41ca104c0f00507620601090719601c451101d654600710b854022207028100a078020f19076090100021240c111288003850304600040016031545e0420110321405140600c10110703030100075545020807100c869000070241401403154040c5981c3c0802d0a00c101d9285081c9041450442c400203800c0202800004002500d00b03480c5d02c401c15400e038420b43c03040b400c0190401199807101d00640d000c018a030000d0340c44002e40601402840e1401c00179001049224540080b05038a4000203000d0f01e441c03c861b4254100c000c64107406002c042028000d81c00000d0350032030951070401d000780403103450000c184604500880f0110308510216070072200140340b094151501404c1040074a9840f80c000d51059000030404400400d40203804100d00c0e08407a07220040c2032001c03070003048407685000d0050005505541c1c1d40011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 136896753 1250 136895503 136895519
    0x8030c0d0207061d07060e06030405070e0405031809090d1202190206040b0f04020d0f0f08070b07081819020a051005040608090102030c220302040612030207080f0303011707 76
    0x50b00019228000120b036281030100c40c1001e422205000028551180a081110a80200001c056401d0503140f440c0e4941c1c5034241149010020790140b81980c1a850804c810b1001c044082e0081030090a18031004105000c20058004000d071041ea500d81c1150400c114102d02a0208645004c0381c420003500706a1945022409000031541000158024404010811680c100e40c264400240403e1801d00d00301500030a66074408030600401d1324004901d400c0c1480308840703000c00c42c00c4d440007065507201210b1505092034481030701c03244041414880494401402400350b00550807290000340005401c06130070b1b41c103406854105a03045a150180030403103454511880c24500e295480b010b555610340f100080641c0001413008005910510501c41c610f5814002c440c030b14182d942c48100c000c040d05400040d1030340258002980700c1d1500c0000111501008040f102c824000e400340c0720304d59620300305079031500042d48286500c2e8008100520030700c00d0802581d400e040c0f8035400c03101465240c00318 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 136898003 1250 136896753 136896757
    0x905010b03030a0908010608071202120c091321050a0e01170702030301080f03070b0627090c040b0111071a0403060e1b01020d020a08090f0d06050a0e1908030c0d02 72
    0x40b00000b5030301401400817078007d0180300c00401107003008040380c43c6400c40089144581c0d1900a10030824500580385040042200d0100742c1c100501102c4182043e03d205240006501001c981d03080c40c4c200c042030204224400c400007a11076454540c50f007500c240e000c803108070009a0b0b02e414003010000c0c002c02d42d8a034060b01445556280c000750b0341d80d41025400c5243c4000700d004400c69501c00c004050004da079019141e50061820b40f10140300c4200100aa1400c203032079018002c08850702030030442d202c0e030006010300b1809000d94040080b01080e0004403504000d10710903805541c0203040801100d01ea01c00f080840541c038a03081403c0c6500c1e80d4401050741c0700315100d0810b03607111814903841e0000815a642600a0034001071003116040d6a0207134030b80c0104080640b45590108000340ca0341c0381c2c200d0a400030f040040030143e01e51668500350b001824143c482a10ba10300e0400004481d000010b90043c184940d600b040450441d103560b02e2105a20040c0031644020007448901c202c2001400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 136899253 1250 136898003 136898017
    0x504110d02030a020409060b342f0414060f010302070b070309020310020a120f0f090b010e130206030c16170c100203070504120f02190f08070501080a0905010b0303 72
    0x7201603a918a4145143c0aa40064008c0c1c12243c03002c11811560750861041d09a100c844030500303000c0551102d4900314040c0c900000603007540e1410707035050506000900646440f000c815020461042600d00b408100d640000202c1e42c04407145000c80c0c010300d8040c403024071187c030514026242090903901c0100240f002d40c0d039000070130313210203d50f000c40c9400d04c0403585182040c4821418407403401c100514011004418030078a039074600154460324515041008504035003d030501940047d0b1500d80c110f074001740b01d00544900b04001040100020009107110781e500181641c0c01c0d03444101c80d07074081b40d210506880c0703540d4104000d000003403428401c40f19556071001100e9211459155801d0074940041000902203104100b0080c10396007005c2540e0a4640c1115100d01c08441c030b28010615200401d80070394030443c1d4100d404040c14048591005461000c0040107150390340e80d062036550411805030314082006040064003d41c044c3d440040064000c800108100000001007400c642c4600 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 136900503 1250 136899253 136899271
    0x130806010515090d230606040209010f0c0317180c030109171309090c0503060f040209011203031509020301031e030c110310141f0b040303030c11070605040e0606130504110d0203 78
    0x2642c00c0e00c005c142032080c5548540d0684040d0b24290010000824036038541001005001407191200180340c480c10b0002030402c2e0258860480f030420402d0004803040d6155040c000d4403031241c100241e81010301608030350a034083d02000d0942d110124542d91a005010a904040c294120004031400706014407060a40100c000002c46810b110078582040703001000c015891641c2c4040c000140c0340d0101041c11030780149a1191120a1890200c006c0c01d08a08458280d40a020700407680342d200d0390085040780d208888071600f0403400020524070000798080a0041040c3d8183c0d200400c1c040c2c06a00c01c002e50090070b95403451200c0b00c0d0a41100c040500704e644803c0c1401c00c0051907817014002201300c1503980bc41280036442c180d66140c00d8407803804024109a1038070000548280039070071001440310113206849129484010080194200c0d2141d401000d0004000c01d9450414030101d0703021103810b00c0044c04041c03c00c42448040c2842c1a4200d00300f900c00c0200402180c954405580078103203c1e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 136901753 1250 136900503 136900553
    0x709240b0304110906030c040c0c0c031109090d0206060616050105100306050a02070c0b09061b0d080c040e1626040501050708060619021e0102130806010515090d 71
    0x741082e22a00f9100c0c000365002d082d581081c4001a900050802102e0300d04440101c1c468500b80c1c012a050000c83e40001c020070b080542c040100100004251080311060b43d0300d114990740e8038240c41d6203d103514080ad0140c3c22200c0170510034208a401040d212050b16000d0208851540d039075800c40d0310483d4000380800020701c003802044040d01405801044044080d4101801912400c0d0820298481d00e144071200151019030707074503803d003038804c565101a41d041090342140a041e07116645200d0110010300f40308000f5101a00803029a000c0d1a02c0b50713100d4646547d0000040d086550b00324424003800a00c1001070107117003003030f585071207083c50f503d001e07180c039042503d000b13400c0d118003804660901000a0400529440e41810340b10810000c90990f58800340118040e030030603800c1c1004500c180300c00116242880415001045039815240308040ba40e03586545480c0c03584030a00a141c1e00020055150660700740f45400b4140e0b04030001c0182c10b05003040c0d42c0d00644400c0b082681b00d040362035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 136903003 1250 136901753 136901761
    0x5070c0b0901030e0d021902240a0f031401030b070c1203240501020307021306080105010b090f0d11040e01020c010e0114010806150d030e22060609080709240b03 71
    0x11500130b1240702106030700241046204904040d4a070721060800e07550b40d007401009201555a4240b0010b0322076003d44a101070510842c100410079880202c12074003160803681d076210030034070900c03a40c0e640503c0403a2a000e0390b400e603034400c01208005003060041140c102c202c800429420380c1421710303000250301d00045008080314049070740300141180c0c85842c40006400c0003580d8022041f40d12859044a210400f034100008000080c202508140520742c0b8110021401c03081c248014a01c0e40e00446410202c903e50008122005d052980c2c0100312015085d81d404c01800d10390440e040c40c01e041d200141c1400d040e10310380c0c0c1c01c4481c0c6140005a41c0c0d1180054003039518140c1c5810b002d0120480540a1850440c051001602140d5621405601d11020320003d15101b0499031518007402003200d104840000c424405590000500f440d9252410000080d01806141d20030111080440076060061612200c0f0700146581c41c00c034140b1040c420724052204031801081409048448981a22401c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 136904253 1250 136903003 136903007
    0x7080c030f010203190209060c0a03020c120303040f0b060409020418020907081b1305060a0810051c0f060e0d0201060e0f040213050403050405130e06130305160305070c0b0901 77
    0x2030791503074404691042045c480c05c011036a03103050b89402240e0015a03a88044008681c0901c1394031081803260081414038010503902182c29941c100c0308503401e1a9503003c5006442d2284410740c0c5c010300d85200000e0481c0082d40600b55994816001000060340302c2c040c0d00803d0551310110400d0b240c06611881f58811442c00b1841560401460b2030040100e142008020300340d144020f25501d408040411038442d00b82e42510b10038081c00c0701521039a220543e0300360150501000343e488034170503454448085a01d0601c0903041488941c3c2e011020380358a035540b079091000079440d40a0303e809403030381d100d00c46003181004805260107650f8000034000b450003401c440b2618002d007980382c9160008051202581c1c0b103082441001c409003038000f078a0384543c84d0030788503481181d01103900644e0131403000c14104510b901000c00202004183c4806586401400d41c00d8201060000c0110b541884094182013946900c005114800c1c00c181d4a4070341c15469110342c08074250710492580d0000180b06a841d6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 136905503 1250 136904253 136904263
    0x10090b0703030506030d080103030903080d0204170c0a06020102032e0306020c0f0606030105130305030712060b0409140708040f0602120c0304110a08061612020a0801030b0f09071a070507080c03 85
    0x4092451f14030001c0d415075500810898192001520006000c40d04480b01040b981c116802003403010000c0380c19010000c80c660304c5540b207601d1184214443c81e0006500382c0180200c0e4400d43d228103c001c00402070f22b400c104041300d10b5680c01050810008040000f400703c0c402020403043d9240204005440c3e02251490203000618060083c3d04043c10302150181c1814101c0c001d03541420115160380d90808100c683c5250710814040c00c0d82402d0000514102000051082d1090958284040104104c520b40d0010041e1801000651113400140100d000180c900400c58410800035161442c1101c500c2d001c100305a46517102408000140700c00c001c0c003180145850300d400d80310010000c0c44d04400300d0700c4003401007150261015081280c50910f1107012a981d0742500100d0464496000d08802006584240030413a0349049202c0482d0010039042c0c2400d1082060710001e007516402d2035000030342c0d60006501c102c0558814040c4400250051100a024025440080180b0010001018940 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 136906753 1250 136905503 136905523
    0x3060506130603150e03070209180f0115050103150e040606050901080118020f0414100608090a0f0f08090d0b040b070314040b0c0c07152c10090b070303050603 70
    0xe00e800000c1001130050300009942520940e0005040c00c8181d50031810b62281c20350082d40164001d0801440040030301d03407402c071595a02c003280c05000c05045072608803a808081202d029082000402c01980f1903007118514024003005004019078600d840280e070001030700c049950f143c88034010f00890404002d03060040c01148000d0000760081460541c0b40d42c1428000f90142c3c4042e201d000150b190703504000d00b0380301c40320080d40c1b052418090801d0011b03040e00852000500481c041003d421000805c0780c0c040c1d4011440000c42c0c1d4081c0d59000c00c08404180488070450103200481e100c1c0d6944034580021401a00040178a16191030442c1d04650002c000c3c2080c50319200310441080c0b005603c0c6039001741d2201d00c940150700d4001984500d40540742c81500c140c442e991010485012203401c00e812a00583c6610a040464100307800303040c0c40342405041e50031100c05001b1610301d8807061b001c2c891841410441c136401d40700c614001c1c50b5840800140d010a4449040c48102d0a0400c5071802c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 136908003 1250 136906753 136906789
    0xb0103020405180402040e030d09020310050c0a03020304051e0c011e050d0b0307050402030412020105060f0117060f030f0703020109120b0c07150f1e060605190306050a03060506 78
    0xe0a030808001a803034401828010100c0007903c0c000900b19140c5901000e241c100400849448a80110101d405820111012070103030040c91071030302403400315020302401034180605036802c19001e024118000c0d080104107484c039200c0d04103040d490709106030075502850b400c000540030307085403d00050039500e84100b50300d00704910b0812098109600c82d003501c6003110500c1c40490700e07101800000c1d18124554005a6126100209110400072510101408105150001c1c001d5603680401c001020403042c13031441c04640d01d100e01d1071800610b00311803540020014441c6a5003802c1802007481c14198017450407642e8403040092041d036030400e0150300240504c000d2444c4195440e516400a000082d060b40741501c00407a5080421104078070200d0148002d200c10001c00089078061009400503105015060350301c1c3d064000d00c3c101c42c1c007800c001d52301191525490039006100e40c104034110241c0c1d08042564610001c120790782c03010303503000085000354000700312802d05e0010400010010550108 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 136909253 1250 136908003 136908007
    0x4050d080306030f1b100e06030f06030d03020405060304020621040c06020f06010f0b0304030203070803040f0311010b0906090612060a05010e06220914010507020a1b051e0d080f0a030b010302 84
    0x1001c084200800717001241d00f0f5407883c0c400c43c410001540c07812030001c1c6265221002008100d03c205034414080d100b8101181224007000100710309400720720984c00f0b01d64106008100041c0581400d600501c039401510b10300040c80102c241e0000d069000588040b01d040421503070802000b603041140d075600c0502134010301172a514000324420307114150720880444000100004040c94002c1c0300303403000350760082c41e031030390301d16052030f1242c1c4000300504200d012810320b1980201400c1c0510ad860303a1108042c081a071182c03a46020000058001001550300560341082e450030204180030660084849210114455042c1484851201c0d00140340303600843c0c04c810600340188800201149500711008005040109420f020758001d01c0140da290080d270900c1d0501202560018151780322a00407a241c103102c8030503e01300a0310481a01c65107520500c00c047c1119902041c0300035000e1444001c03e0b5500502075503031410225048074205001446000c41c030002d201d07030140900c6c90f22400920b0218 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 136910503 1250 136909253 136909273
    0x60f0d02121f330506040308041e030803181c03050103061a0102060406050c16140606010302040b040302010e030a0c06080702070603090b0a021c05150a0f1d07020304050d080306030f 80
    0x41e005094070449004500d0460585204090110180044c04010b06070036500c0342c4909155590743e009203d005840d6003070b050b05400a040c803000c4c980650f03521003016407954488400a1088a020088008450203904101d01203014a80c98084600700603803004240c9600d141403d0017101e04900342d1f0b6a082c904c02051507600d0381d0128403154080e5102c0300003d4261240d483e00c00c00360148402d400b0310070b0070150145040c0100500c0e1201c1191650041303030030b40c1e41d46900460aa00031882807645078a03050000340015030198100c2c00c2c160002600315000d040c1d0503180e44503003103107650100010400e82810b1000c6a03506020040107824242814040e046041e43d070100002e82c020905401541e01007204c21103200484100c0462100f80c0340103214a00b07251400f042841035191189204880414002031025035032009041103e41c041a012300308c0400d500038260360940144101c085000420001c6107a6481801d01c0c400c450003825110b440b8035150090501e0410060b140010540c00103103d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 136911753 1250 136910503 136910531
    0x309030316030207050315040b090a08041716090902090a020c0303040b060105070b070207060f02011104060818011b121506120f0e0f01060e01030308060f0d02121f 72
    0x101c4086000d8540c01c92042224102242040d4580d04016414011682c0300305502c01440e0356540241c0c064402e40c0400d40f10040380580d244202400140000414001048851b40c0c000c0b48240c085031602c01d4490005054030040a0340d07505030026120310b50380d04003807410347c00c1c00c15020713078040161281189011201c0c001d544c0d032070200410060080702c1180010303580303900c0349003910040703540f02410707400d10704204070042e4030703190a401004006540d403c0441c484a10500074642050b500e070100364079060400c0350450b05407000130240782c0d02c09021000c0f1520702000348034922107007603000754100d04100e200c14020503414103c9880a0658107152111981c6416030307210b60115a110700388040c4c1c41c60740c7c0c44148050840d101c1c0d051540f03481c00c0743c4849031540110764040395154400003085030544406107104003600030b010250008824000041680c140381c52020300c00100104140e01509880c0d0000d2400c6030b2081c00c210f026045007011950765001c0800c0c01d003142203042000e00a035000c1d0826 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 136913003 1250 136911753 136911757
    0x10b0403020f01030905010f050106030c0512040809040b0d03020606030705040608061513020d0e0d0302130605070c0b070f0204060b0a05070f080c0f0717070e04020409030e040c2003090303 83
    0xc0640704411621001103141c3c000d80c00749445591007002400f050064801c013000801c001d102325004039043c80384140d0500c2c4690115516890415419026603c50380c90f01d062940140d80f1898009544141c0e880b40c5550700071440188522039401415180f400c0c0003814209402580107502031800c0190034410b442000c1070644c0e03c4000010403041c0c0402801c001000c051076007076440d0b900c906c002541c001580aa811000400c0d680c982110700a0196010850803823007000313810300b21070421903814440e081c414002010070034091903100c0000ba88800e40135446501031601101e10380b020003480342c11420980a80300041c07d0005502d801e005445c1d40c060030030f2185001c01403420f0262802c40c8208a8030400303881144141100321100d00d10105102607964855009804208480780e42d0304c04015000244041680c1d00d445070601683c0342d560901001d014601000c50911600c10260581c0e03071102d220382841c031103140e44c60400000e4407a000c00d80d080c1d01c581b01600d958104100c003003036070380700002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 136914253 1250 136913003 136913009
    0xc0403200d06050402030a0b010b07020a0e04020607140a0515060405060a140118030605010801051806240315071e05040f03080f04170606090a09030c030302030a020d062408010b04 79
    0x50103e200c1d035036440020300b0540340c10001001e0b08600d1001040200c4040003810320144241c4a440f5540c3c0c6943c0d821b4601641120000d500c048100040c00003d01401c00c2c0543c40400001203400400d0380f40e990314140401659452645442c1c130702004110314040c0103007a00700409441e500e4689040100801100c054061441c0c1848503a908048041039064030004c001c5030003c80c01c100b83e585420445004e800295820344980c546000c1c2c40180d07a070007086a6000302024501846415003c10144400e0041220200d50500400c51051522406401710742c1c4690415aa6045044024941c0210310b80b207000812040020511081c8140300d1050f69580c103403604a00c5450f150306005100070003504c21600045036040c81403030400c02e00e80001030b059000c1c0138202c501d016503a4650411004941085030050005030001c1c5141c80070a000350700854200000500151a2864814412017a202107601001d100319400c0d82ea2242800d54441d641c0103130032185816030003945403481c08401070280380 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 136915503 1250 136914253 136914263
    0x1020709022208010f0606050c0601050114090306100f17060609040203120708040603050c091f031b20120a051c110304050d03020a0c23060c0403200d 66
    0x24038a0a25410980342d06401c0c5071202c502454642c03240001400380c840d12841d800a42c4c10040040741903802001510585031440c0000d000307581c80d00c0d00454410050b03d0352450602e03400c1101e11240c1c0c0701806900d109103402d03542044200d142400b02d03246045c1690001e4800c1203002c05866043e80c000c200c281e04910704440b03141e140e45490000030304210510024000c0550300040b107108200e140c8c0c0203401101e1464408200c55036400010b90720f544100c0c2d020340d5008004800d280d103030801640174000004000c4c5000500300303804034014401c0340d070070a44107030129640c850306d04030410714030031007401d0380071a80b01404000a0100c01101a4016180f0b37900a00801007120007003500d01d200155075095003002e062205c06603250f085c40c200d0b881510292803900445400900d1755029000b16803c03001c01e85e46402e0b501405440700c40313030302c8140030301e4042807040103000c40d1080000b001740030b028200030b41d280e594851071440c1103441040c0b0b104881800d45101c0403008001e50300c542030861026081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 136916753 1250 136915503 136915507
    0x12090312060f0d02190e180111090109031b080d0203040513060302010e06030403031415040b010206010e0a110c01020403120906080702071814010311040b030a17070309030f050303071d0102070902 86
    0x419105d12200040c0d044400e2124421040044182d1154043c81000400700c1c007c1003c40b01d1168660b02c03034810103c40070f0100e49002801c10005500d4041a050000703204440030702e1684644280e4240001d0542c2d00d00140d101003024030107498100f42800c080c0a010b031040122514560019040c6402e600c04184101d03400b00004090500a410510103080444200c10542c5013041401d600004d49002c484c0c015031034026624165400029058182c451128804255642c1c400701d0001500c0e9035102400e041308140010b201001c0300340040e01c00b0b10700c40d004040c020001034400908a8888c1e92201d0200020401031100854000c1039031802d681400102440c8100c824240d00058a0b800700030903152030441c00008188618092800e42d011012241800303001000b02c10075030f544000e000090000c072a20010112045c80020003451070324864104802c07c1a629101d513000074004004c01c0e00c164000104000714182d21138001450b0701b01648044ca240440800000d50700c82c0759029508200b540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 136918003 1250 136916753 136916779
    0x130b0418020a1217070501051005060711061c050c12060904030e010c061d160f0f0b07031701090501090506010903120e15041d0703020406120c030212090312060f0d02 73
    0x608000c60402c1c09084440b03170f038480d240d190241c001d220841d1072640d404205507010900d4a000001c442505030040e42c40c03e500c151000400000751f200d20046440803c03040b503941d200f0a824081d151103400d58055071030321841050b2a0401c030001c0100842e100308502401c103c002030304941d80031484072080c03804515005080ca000340040a0200808070030003c9000c0c42045040001200701d4108080c0d00c0f10460340d9a43c804003901400135004503407102110a03030500001d203015010f0a0200d01a02c2c003614140c600500c000e5881d0030031b80181c640140c07260300600c6081000d000b416007103102072800c0d0000c2e03441c5460f28049200b011040340d041051565807400140c0e034840a01d80601e0f51090360b41c0e42c80395034010000481d560a041c145404201c4400942154008e2007528119030154880039540e07010050494010032032400b0182c2490303800c0c0f1900d0242c6110b05440341c130400078000103580e2925045407907a0860710050026200c3c3d0619071b4607000b50346610711500600c40d41a500d80c0307a040b00c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 136919253 1250 136918003 136918013
    0x6010c050a0f0c09050a0504030f030b0d110612090304080d0926010608010e01021201050d08030105010f030e0a120816050f07020f0607061b020a030801060807020c130b0418020a12 79
    0x15a907000700102810031007800482e48071781d0311988c0280d21a0b100c1a054015400b021341c1901c0c00c80c91240d17401920481c03d0340c0811000c000d1041ca0700030080c42e82d4a86501c84081c90340003101501d44104035840400c0a10000c40104807202e03030b03040d0604046514501d040340100901a0001c03914a2010304644021035501c402d400c440d0103442c0c02c0c0001d00100102080c15030003500204261955400c0c0840002550b0412001014010f42c103d2581460f5a003420015035030703901c44c40807071402c060b51007038140440d003814000d000844d03105128403680d00a400e42c00504a1401800203117540380c0503401f05004541200c1101c14810030b14564644644643c0005009150401440c036044000010f01d001040b00e1640009040100300601c00c15a030800c010490b40c03800c241600030046214080188070300360188008a50200c0c039441102c2c0e0f5000c0348408926800886d07204216119141c2d425400326150a003d00540040f44c482203200f00c03002600002c24034081407180791030b4071011080c4082801 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 136920503 1250 136919253 136919273
    0x201061802090d050604200901050312071e0f150b0915030a02270702070e0c0d0e150f09030c071406071b0501020c06120628030c05040506010c050a0f 66
    0x241c0040517195903151030b06004032940180b020b02541c50305021f81401c2c3d00d00d45501102c5c10703076078003030002c207100300c42c2490354a1a40c3c020202583c0903e01d480700c80c135110802c407031400029880340c203201034580017501e408194a01d100d00700c0c0e103240f4204641d40d4519203900d030846a108905421541c1550400c6004c24148042250701941020768400100b611000f40f00d08403214805103483c4504071f550743d8600300e844401c42d0203045c28199140340440e41c13690700c1601404040800f46c40000302c4d0340010032220324003640f0103107400e8240d07020000c21141814294400b07501c0b4041501075850441400d01c41038907800c0741c2c0101040454042213034041501c40c0c405440d1038943c000141001c5110000c40750b00540c015100700d0b030051207841c039101441e00704003003550f000c0c8185000440440d20746804203c8076000508607441e07040744260a0360a40b10300403e2144c010b40c051200e445070b81c1d05000074082030f40c1e801819035050210154408000a04c0010180724094004000880840061806100344 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 136921753 1250 136920503 136920529
    0x409020f1011030412140a02100e032d0601080715120e0708030408060108031624020a030f14041a070507052406010801080601090e0c0603090106060f020106180209 72
    0x1880f0100d00030400d810880540400c09004903100050303640e1742000789aa980c40808000d4002840c450b014a10501070190380b2500301000b0140d90201c40f0032000210804150121041540b00c04001e4400e00001803112601401c01c24010708025404c10400000800041c3d506400700040704005038181074142d80441003144d01507081c0c411681d40e4000c4280e4030b0704035001d0b515290240800009080d10000215076500301d030009220b00f061815201c03c2c0c8041c001083d11261540c3c01d65103c0c84800382c91000303000141c1e4076100041c1d44141100d61038110341040170044230303035046036080c800400c0c0044e1309441207402e0500200e0b000d076102c210071640e5000d1100020310038400c035210807a02c1343c1e246187e402000303c481e0801c00c1640d1100c004407809042841440d84175000000140300703025081d00441032103880c02044541a1800c0d4004c18240d601c1101c403a06580d5407440300348269640710649080e84040c52009020b000d0a10701c044101c2c00301d1111100c2c0450b03000964001c180caa45100d0080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 136923003 1250 136921753 136921787
    0x31503020a23210d0f0f0c02010c05012c010b09040807050a08040b03011404020a1d03070e09010221040c052101020d0f0609060602070b16021c03020105060409020f10 73
    0x450500b10b03010703c12442101c803c1d01e803400303810810389125202d000000300700c0790181c4e980c0c80764031003088058540c42050070f4181e040028101080b00810303424091140002c00d49544440070845602c5000c0300320200b408040426414149141126075540401ca034000780c100d03126503a24040ca00d0094642900f6202c001c04141011030300160403000314001e941212070344102c070784e10b2544c860200401ca00c01d010007030011a41c415107414003000d10b002c0c03001440e2005012140400d0704d60841e042106821103118050341c2d000120451504054200c4039403540c88a824650b01d82000e649180b0ba40c00a40609400b820140480300804141940e04c0c201d034881040085641d00010b41e0204003030040e41540340c042d9420080005060230162103030707004480c501d6014200c2a82424400c1001c1d612044106044402c4a4041d0300540c2da402c6800c8813020450350344442c10300140c034000e82034034402803945125a290204c9080540c036030a0214508440c129112011070b19941001c0e10b890b8052404904 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 136924253 1250 136923003 136923019
    0x4150e090303040b13020102060a0e07080f011a0d0c0e04050a061a1011100e12130911030408040302060d0f0c020a110402030705160303090803041101031503020a23 72
    0x800c048040700a6000364040d050304030840d03072509040b0351031361240c0340c2c004d005a220400094136100c20758442c0311120980c80a0720b4090781da60418900d051444c000314642a552040e501030140e0181d2108080c4940070364841e0400240c50311f403014045102d2003034041d04640c02000408100c403c2c003000c51002d5206600700183c084001013021170483c0b41c0082340c0141e00454541220720301400c2841c17104c00880d00101044407900e03c120001e0f01840c41c80003042d00c205202c0b507405d150f10001a202100d004290070000c645404241c00540701c8000e08602c003004200f0600020841c40011074086c0c3e41c044d20701d241e5640a80052900a09600d14068800d0349014603a0f2a00c0b64041070700301002e8095039862a102e03444000b00412032105803540700125038100001000a00401c0d44103009034040d0600084039001921640525802190100c800c00f100b407440c81115030f014414200824203000880340c1244c11503010502000d203074050000c0c140c00040c800c2051004120b5000e10721000640881 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 136925503 1250 136924253 136924261
    0xa0c020d1404150c110d0b06011808060a0e120406020c0906030c040e01060603230406050601050f0403030f08090318011206030609060603030f02030a08061017400204150e 75
    0x5100100c0e16130102e920f1030340801c00584901c0c29904102140703401c4115411151109001542c0c02240150500e07040301101c0d03030011703080805118051051407a84e802244c060100d0780c2c6e140c10407060540d040402d9100f44400c0c40a541d001480ba0740d06141900c44840c1900c5820010349060244101950710608100250a2541c01900200126507840d20180700c00b011600c0f07440f081500e510000c8004140303000028012500d1a0070050f0040c030181001d42c903140352050044043e0344a5003054003c0f03003041c101d81c0c0302e003035009034120744c8a6420000345091680c0c424820503e9203041480e903040115202403005032090340c1e4802c900640d48000b0030088078025241c40c2d00038000c148010740100340c4a90b00803061314000f02c03c59401b000701342d441c4801c994400003008086e9140d2070b412810815621030740c0c0b402020000f03036607000c2e0380c08124129030080c3e02e000f00c8603050000110712200c1c0840060701c4001c2c11140280c0c2c4500c0d5412680805e80450000c610684540b0341d80c0208001e4032030000788 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 136926753 1250 136925503 136925507
    0x503010e0a060c0918020307050c15010311010806180603030405030f07030c0506070b07030906020d0f15060302041508131a151503010303050a0e1f080a0c020d140415 73
    0x901107103441a40d0501c044a141c01c0207071901c00c90b510890189030300503105003100c810030303a00466100d8000d04040c0d041000408510b843c004140740780070b9003e6820001031003407120780100da0200000074a0200c54501e4804081401502505440c1d5032040007003001c81c459690600a880103490090b00300c42105c03500320092a0ba40107a840217071421075000b1804078244c01d1110450b21469080010191076465007030085000b440d0410b425503009078280710303984950900340500d50811110200c0804c00341c00040c200c212030740d869480030061510402040110701014203440420600506103401d45540c2c0340d12343e0724505d00b40c0b503000b007242d9078034144015502c0c4e49040f405e00490442603504003080e0044180044c43c40158240c0b07951010038401080064071030001000c40c128585030000c0801c044102103010034070505820040705259100410b001e990100b132141e4044034a0034280807038121550065200e4a046142a0030001c4400355941ca003480c040031940184036046261200e107201002c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 136928003 1250 136926753 136926763
    0x40f081612050a11030405030703081c06090e060601020d0f230a031410051e0103200301050f01080f010e070c0516050a0b03040215030613060b03060102010b190504050705040503010e 80
    0x1140000c03916140d0444220072000051b502517410181c02005564110346501d1100d810001c3c040400d9503444107403116603a400c2c0100001455401d03030106250804400e0390381000001880309045500c60319580d20a590310a0258060000904007000100850041080e005000c20b052800501c800691009407990580c403170380c025200640800c070740c0d0320f0741c0c0c40c0342c000300b034052142c9541701442c03090900004e155000092482001410001441c030000b190800d41715008038552035440c1c0300800100a0f50501c02e003402006042440d2811451030300203050300c0018010b001d0b241002c1f01070000074948a000d507030324244458200003191741ea205107015081020729035000d2070f80204080c02000400744d01c0401541d0040713900401e445a40b658904005c1542c0e00001e00e001d51124441003da480000070303104940c0078144c0c070b50549680745007100c00607080d64035010166018a61002c0c0400003072001c140384209852044a010440307498195048817907005036004180d00d5460310201034118240051 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 136929253 1250 136928003 136928017
    0x6090415140102070617070c1b0806061915050f0d0c0207050907020d080703180302011a061306120f1a03100b01090b0c010f0c12060509040f08161205 66
    0x400d100d54107218004903201c1a40d0f20a1002250703c5d81901c040030442c190340554081250b1070402e40784142074480040b220b58904c0c1c00c542e2144003442c10700c4611424495254000819a100c0d91800e41e62921003004070f20b40e114002c80c0c1c1c034103044440e0546201324211078840c881407218546034816107005e10005c10344041c000e809481b445000041d40d0406480f100e2042c07943d50043c20340d07016084419166080c2c004c01d500c04042d0340d55992561107100c1003100c400300e40280d00000d02290031001201d150300500c2070310ba2103204288a400c0701400742030101404e030341040c178000c40440541580b00010306040784502c0030b45400c0031310f19034020107201740d00d0105041c1242280e68140c105408178085607070002d001400900a50003c1c0010b5426000a000385104500009101c1041c411180d048030340c4400030b000041d01e03032409100820390902600016080450b400d02a505140d80c5d001a0125401801031042202103404091503110702444022242c000c03003c2d8186043c0b480d8000c00540c071042c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 136930503 1250 136929253 136929269
    0x302060301151d330309010b0f0409080324030a03050a120b030606190b0d050403091a070f0203010b09070201051801090807170d020a0201020702040b041401050f06090415 75
    0x40000043da1000e1481403900c00f0141901405a4000414079888460301e408041c6045800405110003048900294490f1a920000140d2007050504103c800702420600500c03c9080c91103c0010030000005c5941061070024000c2088120003514084000c0c0c2442c4180c1c9400b0721000c0d60107254021004203500146548e401c40c443c0d051200301d20440303071202c8a0710f40590091000802d5810700d2910403450000c80d4101c0d5602c40d03070720400c52070341e035100c3c516000c40d05407200d05001c105604100104042d00c42001c903250026402c50090300340b40100c00d8042e1000d100ca4118500350340302940708102c5403002074818a010718107a540a406460161001c18001c00c1c40030a1150141041c4070321407001d41d0020441d841c180e00c42e19100c2e40c0c40030013a04005003c008118518422110744000c200b100d070b140d00051b84851040c0100411580e81e80d507654000c0d400c107a50032518102c1015024152202141d0041c9500200004920940a0b1100701a00079280070104110809600080800c0721204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 136931753 1250 136930503 136930517
    0xd0203070f030e0d08090c0306010312200d030b040b0910060e040b090105040f150815010905010605071b120605040c0603060503100b0103092a0918031206030206030115 74
    0x18800b2800c690851615000d1038001c1024590414440c2032800c0d04011800c1c122108207001c440040d0812200303170310883c0c869441005d0001807607007200410a41103141075900c0aa00c400004203902c0300c2e50080d0134020140c2e14416003070180e940390f11003941242d01401d199080d1038503a4007034038102c6035402040086141032100641134900b90080e038810720805082040d0503441c113401d01015041aa20301e0344510f4580c500207024482e1586650f0081c000c003030040484103d5102507461707908043e046803506a0030000103101e00f981000480741d4050b0f01c1010340440d142c1150256244d000c054000c06140702d078100a15003481407540000c0e00441c001c145c2400c01c0b40d034501c016011a03149204071509904804408050841d0a07440070b01d801d01d040c180414100019540c502610400203000181c00b00312111094030892040ca02c0f40203071103040b0081016203070004e45503952590040004041001e2000c0b111051020303500701c43c005603400b400c0c1c2a100d58442c184094640c5c0e1030001040001c00c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 136933003 1250 136931753 136931777
    0x10e040b0a181b02030406030510060906050903011d16051009060c051c03090303050601030c0909020c070b030915091b2e08150904120e030a05030d020307 68
    0x91080a504060080400d18510310300703040c80740c0b59880e045041e002a5074603140141070b10010078962a82404650165907507908003c4042c044690180c600e5036100d0841c1e40910034950000058030680e03842e42002600c13400000002405050b800d001c400103140c243c1402c0b0503146001600c00e50b0b450001b42130311419615a001e012414a1620360f0100140035500200840ca010720b40008501d030241e0705962406c403010a104408462142000000070343e6070649a0600d9454480d09030003030402d203418000b010748490020001a51400344008490b400541c5215080301000300400400d4503001082c0c5074038020b030f08d03141c80e000340001e002021402c031000140f90b40c1010a02c6131804038201180001c00303000d003050101e044103080b10380307140c01190b460810034410fa02002006080c0b49540b200d00514094403c00c8200050010540c0196503e1051100049004070391540041c81031030400e142c0c05401000030302d004600c400c06402d502001409a0503512207070002d42c45142103880700031081388 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 136934253 1250 136933003 136933009
    0xd090602010203150f01200303070908030c1c0903051902040c1404060507060e03180420030408030411091003060c110316020f18010305010c020102161209090218010e 73
    0x203c2260507a26485030080c0c0c1c0403481c034248800c2030a0720010300d003840c8203c9240552400c2c00360022128803d5502c003004014000b54043c0501014040d850051350414440000c0c0305e035940190203c0032009890045030815051007181b14600854010040ba0040c2036166240c007100100f0b5481030f80030b02d0030800c04941d03d0380145010450844c074100d150303181c9072425600700ca00e40c022103400c444c0a601e40310880d482840c1000a0540d44510007210400b42506a00f0003085401c00410502d000803204000d4031510704c4141035961090300884001d43c2c9a440346040c5071500d5648900c59071241014043c080700c064480c501605891042000300004605171030141d406000c0385074000c0f038a600401442c0120f000a5408001280c8098615035001400c100010780101d082d0400e01c0e088405a80100140002401500f50110660000710f01d0800b8111135602112500300c4094041060100020981c6100c0e14944e4001c202c0044115194802c6500250120b4151001c5e240021115110604146 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 136935503 1250 136934253 136934257
    0x110702091003120e150c0d03060501021605090402120a03020d0f021603060f060f0b0d050105150f0f0706050c0307021506101803080706061505030105060702060702040e0f0d0906020102 81
    0x183e00b08102c0000d00c1d55283d403c4418488403038595401030b80241040504410100190a90101100191142d400c81031801011121a81c0c0158110f46c012804031120420700015041550301c00e0b03504032042e60707032400803500300241c3c0e00300001144600800d0b041410303070118810340742c61300070390716a010380444c40d204998030040020210f0b841288020304100044065000c14103041c5260b601240c12a603600343c140c0004901c1c0c0c40000702c180c00203403889044489115482c0581003c8610003030700110909505124022005085907058001a00542180b0740d4010f40d0485030384a0b006200524211422400580040e40c030750000d4402d440828084085480f4114482d5802400010044601800848003510380800070354034260354150100129401000030030400340039541c04501c0a1400d00c80e0484d6005440700c08080040500042c80103a0381e81040b12107503138048548548914107400041c0c001c1c2920116407285c0d104141410044840100d0407201a0441d41c80b041d80f5542d4405090b405d074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 136936753 1250 136935503 136935509
    0xe0103030504050907020109021e030f070b030a0b01210911010e0907080604110c07030b070f050d050402040f091101030e0a02030703120504080a03030e120c06040605191107020910 79
    0xc1036042c88207201c00d0400b5a02c46034420020710001c682c116183d00890302d0052400042d081c10100350076100524141045144100002240100040340c980380c02d000701d500014024141c0c0546690450b50507a203d10588041091541411303042548141c402038001c0036002002c5030440683ca240044a600440032000300a070064145406a51030000c1150b50160040c01d00c0ea210b0b0b41e55600d41d5000c074452010f400b0003a8110000c200035400c2d42001180c02c0c100030108001c0100c000031282d01d0951140680d171840f0040c0c0d00104003a00d4504c0041d0260180f00000032040345021158001e220119071101920b481c00e8800304400b0b0149003125450741d07a0820042c0d007590085908000040c800355442c0c00c0d050317181c034006040c5074603204d426045c1100c9102c00d0340001c0d00c45020340e0340c0800c18806020f2000141c0d2a951a1120541c80ca80d11801c0c0140003405441d540c1c8000f8a007500b0520002124030403c0c3e070100300c00c0f520380ca0152243e8100c55826409a01154002140340020518910036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 136938003 1250 136936753 136936757
    0x903070606140919110a0e0414061f120c020327150f0706050403020a110916080a06030503040602100513111c0605040b0402090f010609090b0103091205040f0e010303 73
    0x2155a4403d18100c494548031407221030550700c424141614034254064455966190798100844881c82c0410041e202d500071400302d1020303927400717101ca150fa038145c4040c00d00700c407004400510001c400d82500c01440d25114101100c0c10503103102e1301694080001c0c0426030008101cbd1141c1d038403107540520748c0464201e00c0364010703062103405d0002480c2c0c80041c00542c1c0d611520f5501e8814169581000d4840c2a87d045001d60300c9424200c081003068946c003552180d042d11a001035103818102c04880f142858240410303c034070b503c0440c101e610250000d00103140c004048a64440e940c00c0000c0da0b921001070208082881d150104541d040e80503400c03004142c00205104491646a00b040f0880213030464000e01209038082c040009221402241c3c4614060320b10b00445d031826005000307001c00000c20204521003810018400c0c15003042d505026240050310010340d903002800168010005138101600710368078010309644c1d1541c090010025502e0b490701c0171032035907528000618400021701000300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 136939253 1250 136938003 136938019
    0x30601090216060c0305061203030609070c0609020307030507090e0f0309010509010207030f05010207060e0a02181e0103050601050a0f08060403081e090708160f0e04020d0506090307060614 83
    0x3684241c01500086003409000320303141141c0d40d00d0a00300c07043c01407204003180c1ca41081014901d0700d002d000328120261005945540b0b0711100180550500801040034081d80c21844828460140d00c4901100c1d4080c0c112086281c5034105142d603418648180c1941ca814000c03e80f041104c0440c8410700c0e0003030b80c03004500b08014440150380c40d8016014a42c1144201c89000000c40c0381c0c1b00000a100b40500d00050341d820b180d0820f4015611845020502540000c2804005840703154412010200000d1000d85a89039205544180c048100340d005549140034004001d11401003001c0d8100c4004503510b181e01559020301890b08101ca1250b02001e4100000003400b080c09030078000d074410a80031008888040c60300c000d004144040e5100e041641c0315641c140119802000303542c40c0810030401c6407510070b02e0000f0080000b03a160048924200302200840d0454581d440705551040d8448140e42e03403485c0c07402c1c16507078941064000380c03091401c4c10400240d201c1d48500780650050090412a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 136940503 1250 136939253 136939259
    0x18040b01030c05030c0714060a140f01030b13020301020f0c0f0c0a05060d0c09051f020601090e0a0602070809030d1d180c0a0905040c051c0216030c050309090103030f080f06030601 79
    0x92040c6d04001e00640300d1001c1001d107503444010a1156622030042d4140c0000c6006802d031124600003001001851a03003000c0380184003050012194903400030301d40802100c082d00f10310102e800780c000c88010306c1d0658004a000801d00d80b02141454402c2c0d010402c99405085610801c01d80b904548502c540149040001110182c0d4070342200381000c44a040481d1442d61303d0f00032a0305000060071844508203060700900d2443c1c4e045c0842030040201d00020b21403404101425030302c40c1c55070200140401c3e0b00245a400304104003098810b054801003c0d91001b5400d140c000d08207010380c4021b8158459607070100710340c500c1d10f6030003150f00790800380c10f414840d60740018131030483d4484401c4400303100450074001042c0e5201c0c000c0010450943d40e542e511240c107910200d60320550b555213043d105005004924a41100845440b0602d805103000f207021101800d080c1c1c194851160b0b560342094603580040f040c50741042406003410042c1d0785001e075075a209040170900c000c06850b61079050704203034010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 136941753 1250 136940503 136940521
    0x90103170a031b0305090105060f1507030e042a0c0b010e060d020d0320010207050a020415030c030605071407120503090717060a0c0813030507140318040b01030c0503 73
    0x180940c0c007080e05002481081c002c0c12600f50b031540c0342e68400003a0301c0d90100000c0700000e01a0355003002c0f050310360903c16100b1500150181000109507880c529000c103800e018107200318115640d03540050030070000000c8a06e81410050151064038600d1130f9090b41c2000c0c1e5030f10903001803004507040380c0b01001c6030b42405039682d40c50b0400391056030301c6218003c2010144c0d5448502c07482540c400d03205e89220a102c110300d404507201c1c80342200d40742c2c1d10610044020480100700c42045950441c2c000810a40302c21600d07040c01025000270740b131800140c01c040b081010039400780740a00c011303444044607085050b10005070f0388507a00700106600300c4207504401c182e01442c091a04040080260303040b50740c58001102940300c0300c131446a0b90368080803d100041d0120322440c070720050180b40034000e44c54540000b40c442e800c40c00d4003c1c20024005075070003e0216641c04207500c801001c095960f1803054210780c1c1d03100c00c402074410380300f41e01d407070036001056021717115007032807191f164954505555443c100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 136943003 1250 136941753 136941757
    0x50405040c26010608010501050403150203090a050a14011401031a070e030a24050403020303010608040807120509040e0105060a06030e150f1b0406140c0a050d030e0c09010317 77
    0x461400e000c1400d409032501e03034000d40d840c40300b21041200000c456240c500014400340c4180e0105062050400003400400c030200141110048500e4000d40e413511403010f111b152481d10b00015256014501140302004090381c4200703004190300b8000d01c6031119407550101c8030301080c40001d1080d0751480840f081c0200ca90443c0e030b4090a41d017484400030300c1060108ec20000c260108460040d92100c4407601e9110702007440e0301c1c00c0745480b010000351900f982e010390703603201c10f005510902c558840007a040101500455250f680c2c0058464240000450050000e4200c951f18600c80c9040584121500605201d143d210310b03001880c1c0103100c2d140100590040c00c082d5940104c43c0503001c3c1c01040b10144407032050049200502e440c1080c0303865502e4103260b2082c104c528000540030042000b038954803c014a024181540d01c9668a1221518240c5888048207005105005030394107143c4943e003591203902d281800304140d8414560311410805142824007000b010741d20514000401580a480 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 136944253 1250 136943003 136943021
    0x7091e0b0a0b0f070308010b070c03020d0f0602040e0115020a020f011202040e1503100204050a032901180e0304050307030822140f0306091c1704060204030309060f05040504 76
    0x3501d001ea58645503148007540c84051250140040004e101042540c00003005004000038000d490820016903503042d401d6004d80301c080d12030f1001c82098024003c1000c1c0c810b8440d03034081001c40d51341d40d035a411912549001d2082e90501c2c80043c502c1c06e003c0d800030540c28151075008043c0481b80396110019180c0c082a99159540a907003031001080d85050b691215004040495913145c03514003100030145086290420b901d4030074014841000399480b1054800300303032130f4020300d5400d0250303040000c0b103610102d59007000b9000c02d20900010300302e10744080c407200d03510460b0320601030b0f0141c0150555480c81503200c2c20340c00d5800701c8020004610054041c1000c90310100a50001581d0711103c0c00e039940301508840c07100d41c80114840c250740f90005060070700480a90162509180c170800726902e078240008540741d903011000c07004418511a50702d00010000c4416180301a0030541001ca0081d001408101c4c08503000600129481c4d009490b800b03805101c2d551200d1905081c403060002600b0000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 136945503 1250 136944253 136944259
    0x30c010c0b1f03080705070f080616140310050f011805090606040f0609180c020c0108040507080f060a060f0e0103120c150912050301180e0a120c030207091e0b 70
    0x2a0b40c9a4826010481560043d401815000c0d03c40f140350401c5401c04201380c1c0884410071161a007002a26408551a41e108224821044111691840c25940c40900039418210440b0000402180d05040c803800026584185c0c0c03940e103001a01030043d20780c1d514001c214001840403c40411481c0b42c010042d03648114003401d898101692076540c0e0050b10455004203000c29102e5070300740707c0c050101040702007109444034244501849011701035103e04190b2081410070007250006004c0c0002044408002c1014900300c420304151070081503150300f000c0c2d4a14030118185400000e00a0b0b40205010980703038400d101ca01d8991855807170107030007141e021144092150310f52034517021a250403540032003202d092101280b82c102c185070501a00341443d8441007030000030300062020000c620080d1030381c5120301c400019040c84240b031052500d20701801c02840c914180310f84c41c0015601c1008505648e201c0d400f00e56442742c03200070b02c0e030079900500c0880300780030014800c4005904482d000b1200711030003e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 136946753 1250 136945503 136945531
    0x1c0506030f011b030f151203090503030309010e0610031e0f0b011401030f2c0118030203070b18030703050a0e0a080c010e040212060906270114030c010c0b 68
    0x10045280c25656040e002c19890b40001c0411504140c25016000200e20320900070070440d001100c481b5004402405022004000400c03442e003014084e41956014100050403039840e4031380040d0700b9010340580b203008071075401a6400300303041c84261409181503c0d0b2001d80c1d100d050b101d40d1010900b5401c014020754400070f0110700040401e00700c08031940a060342d48585980c0c2034541c1c0024003075620340c1000e90081132500d1440388600700f545a22041c1c40c1c51481c1d06d604d0000140d900309000d0041c000e5200c0035144140d0300c12040680000c010f1074000d11030b0034a81c4113540c0341004603440130b841c03200ca41e1003908104641c9000038401d41c010b00a55580d818040e0006082c1004150b410b0710903045188194050700b0b0210b00c0b580c10003145c6141c020300b181c1c00e62810215600e1801c9164000c0d2242c0d010308280e80108800790303950403041250141c881070786180c2c0200c4450300c26403d0000c0c0b0071400c003181c010f0034052003401d0219003941480e406031504081c590080d0f03116984020002d10740e172a00411 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 136948003 1250 136946753 136946773
    0x303120417070506010e0f090d030c03020f0409020d0501080304030c0306021b0105070c0507080f0c041d0d03020d05070e063106022b020715020a0c090e0f031c050603 73
    0x7540946021401600246180d44c1001540481000050900084040300d0410081d14410002d610821103029180108001c80701c91002e0300680500d21800100d04400320b0302150784400c65001c2c068900300b501080c0a50390360fa0300c2042c1c89106500001d400781a0f005000d0021803c82d4009011484418021640c2c080d021001503086030015101c03a0000b59100c00b0300c90500c101007202001900007a806810940314044c5801d0780c0d01038441d550ba000d00c0c0c44cae9017081402e10080901c030724501807060903264500980d0320020021360090503c0940d251030200071903820340c4250000780d0480005042c00d41f0f4120300e034807000c24424000351000d10f064102155210b92408a80000c00100080e40060441d43d0b80e400791030403401e8001c4070015083c16250f000b16401a8001550011114a00c0800002100c03810049040c640031400107002d55103041c10008844039258040041005180c0a480c542c0300700300c0903180c4074491114640312558004080c21100003c962080784c00c600010304071540e40d40c07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 136949253 1250 136948003 136948043
    0x8040e010303080a0f020921070f060816020109020a050409020a0512010f061a030f07170c1c05060906101b0303020703090b0301060215181c0201061403031204 70
    0x10241c1080700000d207032400b400215669801070b42c3c130b4009980025401c1c8050100403859505542d14409820b210103203207030022031024400c4c200541304189420841030340310781020340302260648983c0d80c495a840304070f00f800391061103400703412540104100b04251411041001502c805a402c1c0e034464802d071000155a503070b0903000103206000c68008181c001e8845460012100c29522415960001200e0801d200d44802c049036400100100c4541d11341c4c0340c0341000c59042c0310b480b403000c07048500202802580040c0501070302d16030b40b85225082e45070311000d4498041e21030654200c0d420488800109400b46010f41d1101d40744466403901990015400000342280c0c1468481940460707800500713841410781c407130064000741003140503003840c0d075241180080da0360303403440040344240c42c1000120b0740c1c0c501c0041c40906225805022107501c405611a800620444102540055072074074a0008803112030700c62260784000c004000d18100f02500320310502000008008a40e020b0450741c0d103801d1340f9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 136950503 1250 136949253 136949279
    0x3031207030b0a05090912030c0412030509090903090102070512010b03070b040e010501050403150c0e03030705060a050a0b06040302241201031e051011040f0e0a050c04060503130804 80
    0x5421507501240e240b0380d21003031002c400c0e0310350840c40c0520b8442d4108a06c9810000b03a43c1000d40460741d14903583d42c0d4208405040e4021504402c181d4406110300d141415440301c06460300003000c40e241480e9440741031840c0c2d600c7c4245483c050141c0c10048007088140f8014852501c100c00000c0080382d1121a200020701b410216080310408800100781444180c2c2c140110b140034000a003400c628090458481c000c40030036030701c8440d070750640700c2a03800c03480c0748210300c001100720002e002c898842500d80342c117584035030382140d85e0254149404006220b025117806a440c0203500070300054a000c0c219000d002601854407441c03926221501d0303030101244e80c40c0300106561410540b03e40321075419460f0455840040c1c0c2d0001203150401580140460703404968165084800440012004405c03105514240920f42c8401c42e050140e00d00002c2d01d07a0311142580c400c400180082041e50380f8155034040703600071400749500041003400025608a606422030b610179006444150406644191911102d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 136951753 1250 136950503 136950511
    0x10c150e10050103110102010b011202130f03080d050a06120227010b07060c050a0509060a03090210020a0b0c160b0c2502030d0c150902180103030c02090c0310060c02030312 76
    0x110b651000100103000c5c40c052201450b800c04d10007400640701c0000020484264102143c0071181c1c0020420322401c1040c01d0b50009081c040103401070255030f030429440c1900240380002d00d890074200000d045020034452a4151404c12040d180760300744075000c0c000903121b120041e51030906c1144601c850494031040c594001c3c41000941582d500c2c0d10324013002034800004200d4184001840390510b81743d0808155058110151141c0e9185c06020000f10080e00c82000003075080094070644202080d400701d0407071201030040d113401d61f80380c480d4079004001e44a844120040094840e1100001a109800d41078012513042003442c20984800c0780e54110700c89681d420003130781c0540c001038411414280103d1440c0c0080342480050102140c480c0d44441c0e4030f500c41c10902e00d62340c00d030700e40455841041070707264a8074001c80110150b859150140c14801004001d038403c1c2c580c10001600c000703440307040740e00c42c0c01d1075000400030510308041503074a071031009002c9a050200f40034030682c08800b00940c600c6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 136953003 1250 136951753 136951783
    0x4050108060105130606050301061224080c030c030d050306030715031b0201051302060901030f1a03070e1003060c05070821010605070503071e080703030209130902010c150e 76
    0x2035514100802c411004d020114040303c5061410802c10150041309403411150b190030141a0600040c4a0500a050000341c40041d50a0080e88a01d80c2880442234400e8940d100d044460ba2542141010759403030700400d0302c2c0d603d5840031800645152161020b103030080000f4085620030b60302d4050110310b0340c1e048189080060b40e40c17158416005001e1450540b5402c2c40c0c0001c02c51420b041c0456213520030f914901074040d2100045001d101c3c0d110740d000c6000b14a41d0301d02001405c0ca01e5000302c0845942421081c441c0c803030380e9804a010403000c80703071a024030842c081c0604024074550b1003202400c1900100e2052090510208011402c2e0300010540d5540040d540c1058266044100e1040744041c1c100404000c028000c050000d0000800c0340d40c405d400041c0c00d0030210004224000c0c08002c030710300404d01d08020a21000b01601174004c1c0400c00801c0f604022014800e584840885030256400390000c1c641c50003010128179500d06c84003002581460200d4103170300c40e42d0341c02d20b0403800b4480001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 136954253 1250 136953003 136953013
    0x3070201020d0b090105060a080903160c0e160c060c051207080f0c1e03061306060c060b01170609070210060816120b0f0a06031a06040e07030804170a0204050108 71
    0x1c80c101500c292288407401300e8500c080d5504120210700680507103012071082c030074403001013120800f08100b9110484000002c2e0940120185001e0440e20083d119549001d048a804900c54410b01032003e281c1c0401e43d51090780c02c3c00d0545801e0b0140c0b040240e040b051180811580209500340d0140e2403003207480d6119284207042045a840440400601d1501507010074401c0421881c0070010100820078404d5070952a80c0f604070005d2906941c1c240c4141d43c0e1850200001801a004151002c0d2075004400401074060500015500c0780b030001e185002e104041f00010f49549412003c69400071030b10710451b0b41040c2260840300460706642c00c044071540c40794205800280c0c0d00f10300310300504540c540703035a13030310306e55944200000f000544444000400035001482002031ba0340140011504003099246aa41c003022007511500d094a42c02e000301d091080301c0311034420025501089a91019000345042d103014034000144142c0b4800a42034080d600760080940d1b1903005d040d001e0900500604 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 136955503 1250 136954253 136954267
    0x1803070b07110d030212070c05030f06070f0323070c0615150309020607030c03020f0724020a02030706050d020d0608060a051f03020f010309120c020a08031c0b04110307020102 77
    0x22441c0b0500d941640324040070542000000d9002c80c02000001c42d0b80581a1142018134000088000e030b03410103a003501c5a00c1190100070710010750036000f1600740d21140c0c00f5040c4104201d0546007024029410080e03207102c003c0c0c0c11400e440b045913100041d072503d580e108040e65500c6003036905031940c05881400031001488400c40040c1c1524401c1401d003410088800180e010400b90701030707500050103000f0500400750a1500a1080660441494040e074080c140c40b064030700402800d001c1900048400c034a441c002ca1800015000b1086030001c000b06189450301c4002c031100d40c403c04021545580a000b8200416841d01400014140c07440182c101c0d407910755520703002c0b550700411000700c46103084000311a42010480a0b0b054980617501c4407084c080800068000e4250410010300440d1600e000e040e6060b409100000c1040c4211111984955035203100ea0707881c0100c20f010228540661805009860181d000e440d405002510104d0030303026040d40b41c09180c2007201e00f800583d40028040e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 136956753 1250 136955503 136955513
    0x60a090905060307030c050f0a0503100e0d050a170a1e0207051002090a03060b0102012306032a0f030f150109060f0f06110109061d0106090506060f1803070b07 70
    0x1c103a1001081d001007107020b25588504000c00082d00c00c40b402902a0001e0240c02d4903024500805007002030104d450b034107600507000b0003c040342c0104540a0240c00380b00d00b40c081c03040088807101202c03640e942c2c100050f848090175030240041d01020040380d480c00d0040c0600d10003801140440414000117071154101e04103135050080038801462140e1042047c4819a80c0d03406013001602e80014000500702c40140c0180d0041c03141d40040e003c500004c6802400300c00805110364402ea1050b0181c9035118a03d50050030341c0008030010540201c04c0f0a00450141800011000d281d2801011102c1c01c01d02e1041d072600381003a01501c100103c8240b07005008a9185004410040c1064241e403003440d0b140010340c082e201541d01400042201c1002641140902500319203030741900820200680f4600b00d600d95604a80c2620030704c059403d10708006815000e0b88034242c8540e00140c0b4880c40c00c207041843c0311042c1d101100e4420481c11070030300c005403600c04218400182070207043c000d603140c00034142 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 136958003 1250 136956753 136956761
    0x30c291f1205030f0f09060f040510030506061b0304150801170d020a0f0206070b0a1d011505090c04090609020405120a0201090b0d020705010e0a060b09070504060c030509060a0909 79
    0x1c81c4001840c81550100002d01c004102d55903a03002d40c0810b038962845c0034204140c0d1080c000307450791012000c610fa070049002d82c03004004881c1c0c2141d0f200602c50080c8010b4007590b008541240e800300341400003164942d07034030415072503071031451040c0c074038140e1503500042010381810b20403070005403154014403000c4068a03d2010031030f4001c004081000301c0103002035403240e06400040807103401c00d140200b151184e42c00c1e00d00c0150b22501c2c4401c94034100a41c20000d000000009031680040081c4031a048018454064051040344200ca01c0c0e500300824491541009005015001e4080000141c9010184146005048108405642c0300e25001c10820503010b0b0140c40b5040380c2105107170302c0060786c00901c54030480b440840585c1c3c40e4030026107110003d004220018015508101c0d044407844404103900c06001e10589040050540c1c000a206040404480c0300011560801003444098000c81003900d5051280c60305510340fa03901c40100303600740c0021030b0f810080b842d120810311204925004d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 136959253 1250 136958003 136958009
    0xd0b060309030901111c050a090302120c031e030708030c120a060311041a0103090c120b04020a240c150e030307232506020f070b13030c291f 62
    0x801030040d03139002daa0f103103450840a01b034031050050016050191901409203900250b40081c041039980d400003d4041d03c40c1403070302840f03209000c0d813806207242440c200480066040c2c25030003141000300300da9546801d548090a41c0100c8002441b071540d00442c0c00307418034030902d0303160300126081c2d256140c20750314910140d410b03034415030400e0600784201807c10b0043c82c005609103000f042000f0203040c01c0356000c00c04d404c120401c00061980005011000c0e410a000b24426a2280c1c4000d0741c44403e041d000c100d128401c40c03c514102a003100743e510074441c0040d840d014641d11051804455500c0044880a85102d0780581000c010800d009410200e45800c554482a081c0030140792044251840c0c8a05090500141d9803003098402c196151201340c7c94180d401102155194009062030040d070b00295800c840488160002a0340269002030010b0314952644401d07000d42c07081d6a03450b40a59010703017030349201125802d03402c11510201f10614000c900000b4100c1c5415070310f22a210b41000d05030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 136960503 1250 136959253 136959287
    0x90a0b180f0105070303051302210c0d08070201271706060108042406031202030301080f0a05060f09150103060c11010506061603170a020d0605090402010c080d0b060309030901 77
    0xe0303040c4030181d03040404c8544082d40341ca40014281e5035540484048a5000070282d048000c900c2075144141441d10522403079090101110089440d550070420480700034400148450001d020b41c000550050000d02503111013007240200d40c1070b0324442031034000d5082e84030004c0301c400c0c1c5000e0031500380c00b40003003a0482405e00e41038074145040d441c0d141c501c3e2040804103120400d80052141000b801e940301ca0042e552121009098541a0000950b00c0c1c1003801021181d02a1081c001e19000b00020094159076005010b42103c1d40c03090f091500c1944000c1420030540607200c5030980d50528641c600d4040d51241500160305049208010303c1003081001440e01d5030300d440d003440b403150389031002c0c0c400e6201c480e004124402a503290844100a10001d1941c82040302d81c244200701940e81c002d000e070070008000400c8140d64810420914010907a4041c4c0424609100307800880d541500a12186c2c500c3c01c0046220f0a01c400403409a13402140e940e0040d07080803900040707541e402008110031400417 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 136961753 1250 136960503 136960519
    0xb0609030c100c08030901050612071409040c03020d1209210b06040212010807080d0509010e1302251202030405010210090302010605060d0903080105120a030311090a0b18 75
    0x8010a984600c000a5207100301c00003901000719612812007880c1d00d0351300c03245850316800d26084e000c1c0070b8201034603d41c1c400e54090b014500000000140c0100f11042c00d4103404010f20684240311500d60081d000b600c0408032400d010001d42c58184054031498418545c500d0043c3d05000e0040c03045003150043e5030011b210b40900400d1101c1d00d84007241e060b030080780031421030300c514001900a00c980603101d070b1515403280001410a502181c2e800450318040d0540e03514004148088925228144900d4003081c01a86001a542403c4c41c0c64000451035042c0186809445a5030f82071902c60f0140026182a91560440401c1410b211610074100d00e13000460405003400001713915010001c210640b100c1c0d68000303034000e06100f500004001c1c1405001030f681c402c0c06201d428050642ca202c1640401c9001000003000c0c1808180030707011001c0d420281040f1929547c045000c3c000b200705684110344140088082a0348441c0c010008100302c00c40c4a60b02c900b814105007100300506c08040c420140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 136963003 1250 136961753 136961767
    0xc1715010512130c0b0a1103070201080c0d0f06091d1203011802120c0a0e0d0b0105040905010605040e0a14011a0d0302010e12031f080706030e0a0503120a0b06 70
    0x4502030b580c0c01012a68a103000d5691094001c41c9030959907005440c3c2c4a030480c0015000c003201004050100311a0b4520b40b41070440c1c40344540e280f05040009001a003240001001c1060010140943c690390000100e402c6120b5041442564800d0b003003064860b0307851042403514100c1ca0250b8070114803100161403038042d10102c280e03490105120701c105c50030741d418001440041c039078100c0d0641080d610403456035040940010159400803c49440880d2002c007014116280a46000c141030340d00448808080e800c20301071001070700c60448102c5e420340d00c500c800304481e52140111004181000d000b003002419038200b506528480c040c0214403649000c07881c2c981d9005031240711440b06c0d4240c409a00e40506840c0490040100980c4150f803401048544a011942a8020740c0944184c07002d2010000c41c2e004084504c090354482c0c403000da4043e0008000d164080e40101403040c0c01035080d00d00304d04954651504540c42030720742d00d6404d0803c0040003c0c0348102d21075410b04100c190fa15508041c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 136964253 1250 136963003 136963007
    0x50406180b090d110d0e03100e1e011a040e0f010e0c0108010b0c070b0a0908150411100203030a050402030703080f1c0608030a030b190e0402180c0409090f060c171501 73
    0x2440700d880c5806c0025002c806141d03624108008200d45554120400c030282c1c8111042d0344481c44200171600500c49a000c200c034040d8140540e00e410740c906c100300344403008564101f100911240c0d81c807038501c4c01440b844207800042842105841c9134000090a64002e103040010071016050b000000c4000003400010020700c00004d030748040d507000c01400c3c0d964102c00e10083c0d5100b2240d600c0106a88100c0304c080f4920149001d0b2640070303610800c02c41d0710b14200c50082050343d402d83c4400d00010b80c014000900d414205030003080e00640081e06980c441502d03a03e40740602d0b4800c500005200706e00041c01c65040070740c219400340d20094854100480340c00d02d4085505c034403400c9522810551190b10940e05c541d29200c0e202442a11014900036860740c0745042880d200046505034400c410fa9605500d2442202c03070002c0c0320302018940b41d490030b0b06044c41710001700303d0a20140c4030b01d101d80705140d000803510320070816605940d855500702078801901038090300d0b130018031044105041c10050301c420790f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 136965503 1250 136964253 136964263
    0x3120f0f0e19030f0c08030703150803030705070f0f0b0c270f01030e010f0e010911060a1b05070305030d0e0c0f060a2714010906030618050406180b090d11 68
    0x30b5031510705105503082500d0219000441e4103001b600380035001050008070342d010307401121402c0403486040040741c3d43c5c51201d912800205c40c0d00c00403034002c202c610002503440d04403c01a91081007034001e0045151a00b003446003048501e10344c81d210015076041e9107841001c10300017440e080e81414045040380c4001c078294885e00c001042c181030300c0f82401c01010a081d00075135025000f1044c00c00c5a070340c1b9032104034041d060342c000642d0078280e848032401c4030782041c070200c40c82500303141c994840e60002c00c600301484980051044c0c0b4140101c1c40048000b41e01032005114440c0e54071380101e0b080310035034a07090404095040262081c02072540c0714001d038660005480d4146404e0a0032005c45450180c640c0c1c03100c400907226251201d0f10980400c62000051040c4c3c007910007070740c40002c240e840f10700903401c0712200d005010202c0604007001c00d030040940c000c1a0310511500f0046a000300d103510f02c101d501c150316011103490989008005004404000c490740c51000b07031800d810b60110320b01e410354941e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 136966753 1250 136965503 136965553
    0x20c0f06040c12050c0f03010912080a23060d020d05030d0203060a0803070210110f070801020c0c030703080d1a041b0f14090d050c100e040b010302210403120f0f0e 72
    0x3e0300030031b01d4103506070b5086d408240d0098000008544801c2800740080002e0001c4a8428a192409000da14500d103101c038200c410940ca01801d4400c0c4e200c103010003265059900c0c0480c0c3c403070800c002010009000f44094510f0080042015840342000401c00409803c140c1008103690300620201d00035a80e40012840300440c58105040309890203034245040440840796081c403880351090004901310158010880020000300b0b90b21580711000c10140c40354110310018004003810710104604401a900c820404610034031203a82e44040b00d0b0104003550580c0840e400103030542000320004940000061140e0b40d280d2400310070b49102040002407a000300b1840c01c0c000c0701c80f4400c807010481c0c03c20040484040040100006080ca210010a40ca980300d880380e006500304204051107502030b0095a000d0036001003019008800c051410720444002401a0100581d02d10011000310003403160001c880c500c3c030000f15000079440114810b48aa9800748603103540400c0c0001d030100500401d140c0f0b1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 136968003 1250 136966753 136966759
    0x20a140612060418051c0f0f030203070203120703090308010801230603030903160602011407050d15090c030204030308060f1503041b0f061b0c1404020c0f06040c12050c 74
    0x125480304000300c0e000304030180c100c402c0d1207285408034045c041c002814041c1c00101d1100141c0180d109403044400c0d2000c02c075070301d0220390111503a031b41c0ba5005c0e4000d154007086a104580c1000702d04010902129010b44d45c0c00c020903070f600061824103501402603400b41c804080244500d1040c1c000d1180482c111401100c1c90780b01803c04140c80d41d13030a00888807542c100804540007a00c1c00429904030242c14418070016610f0151b0342c441000c00390104500c27400c01500c40724186450080c50002824055503200c1250b621300c0c0011441d00e940d0f100c1c0c5868400160b400603112410340c513000c0e14040e0090942d40c45400e0480b080407050f42d40705005a00c0a400300c04c07440c2c03a900c452820a0104501d0340c29044000e0200d07202159010500220074112001541c5100c0031420b484115180e000c02510041e00301e00002d074040c8590018488200300a8102420040c60280e84084060908240c8405c44006400000500081c400c5013070f6150003804142001e10320180c03d56883c02c0d5101800100580 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 136969253 1250 136968003 136968037
    0x70e0f01030f020403080910022a010e0a061d0a03050a020d021507060f14040b06010e010903060e01020405040b031204090f0605130b03100c0c0f0c030503040e04020a1406 75
    0x595074030a0700500429108000199111a200d10b012100b60700300d100d07118010b0303e10848144903a071000070510050f0130103850b103003448842d002c80b400c010b0700d400f48480d044c0000c1214141c0c0580310846030800034101c603a09c503410141c10740880088070045c1c807030192144040c0c0c50b0034000300301e0204680250070b604807105040b40a40b4404a4880c40310100c25901c081d0000c41c10340c1c10300c0000d40000003680391504041280710034104000075001d800395000780038203410000050b62540540c098521110050420060130740c1d9a1388c8031025221f400d001551a650003040c01c12190410b40100c10031810110090315902d419012413216601844c404d010b10103890f5020440c80c01d050303602c0140504400b4003070541c241045030742c000c00380c8081106580203104c3c00c110012011744901c1079040c03c006542d10a01400459250441d083c2c00000c0c080d201c0b40305512000000600400042c001440869080101d030f140c180100040403c0562046d5411648011240d00c2951508101d612444000c500c0324 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 136970503 1250 136969253 136969279
    0x90a051b04030f05070e0f0415020d02070510051005090411011209030215010b09030a030507110901120b010905040b0a0c120c021b040c0215070314010b0405090f070e 73
    0xc0c00d2144804860016540068003006000c244190300e4034242c02102180ca03007641c1c500f440c450014046603071512501070b0001207000035000c2880d00048402e40d40c000b500708400c42030314900300e034030030302080352164018013480c01280c1c41d0340101c551205080008028003881c1c8000300300b50342801003000301990822000b9400340c0e03014221041c400c0743e207400d0800c0006000d10b80a59181c07a004018140c00c01c89200028001c8205c600701c910741d03040607006e000080354503a0151501d80000a0803111544d00c024807903100e4888040d118020044100000880403a80c20124141c104c1a0000b0003640c0c2408108408500402c41c0150007882ca0180000c0e00d00d05410201c3c1e142000149000541d420b1168400354258000740f4554410094000f58000009040411088030f641c12491000760f001007008522b03080c03180c404982d1010b0f8504002c0f6001e80f92081c0c5d00c2380140240c001140706100030400f0310035418660201030340b01054000040c100c0c20b002c2e40c013601c80440404042e1044c0541f881ba1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 136971753 1250 136970503 136970521
    0xa020907170c03040b0f06060406030b1c0c03031e09060e030c0411030121150903050d020d0603060e01090308010509180f210f040e060f090f06090a0b090a05 69
    0x1c0314401c0440000142400c1c203900c0282280c2c0180e07002d640c0591080045031000d41281185806410700402c00340c60186448006d030040d01c02c0740c05040d880101d140103100d4500100b404882c2441c8a542c01c1c0f1421401c600d00036100411441c20000c640c0c0741160340802c49a0041d05140c2503900301d044c080749511503900043c1c80e04002c0c0d251150403d0800c00c8054514001c030000d181660f40380c1000d01801101032005000f100300030700340a0110503060b00001c6000001c0c1c1d0005014a0017494224542011006a4000d031380c484943d40302000d40d41c003c01c00612030203210b04000922244001d11840d01640c50051100b50103014180c8216240c50114412078604607909070202c0ca8801523403a012820b00b400b07600c440c046400004004007414603045080700000844101e000c03244080c40c14a81001c0c7d6902c42d8407401020190000c017000400c7c00d035642c0307542c1d0b9540300310306441c0b030003469151903000e0102150340900f00070016420500170742035580ea0041d20742c0d0700010001c0c1c00155a42d403e150 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 136973003 1250 136971753 136971767
    0xe060114191508040506090a0b0f060102010b03031909050913140c0a0603061401080c0315030c04180606090614040203090304090509030a08070203040609090903030905030d0e01060b0a020a020907 86
    0x4801280c40d095808908400e8014404a02c40d030301034406c1d40c1481e40c501c1c1240e0744030290010700a1101e0042d500051740342080503842d5800510610000071490110070201e46140c2c00a82e0541e0210350440881d180742c0d502c0850039015204c2901d1080460a02d081c0003210490702e0040100040100768180400c40b400b0400044004802000c0e00460750352000003400404c001d0090080341040e100825140e5400f66003401d010f21900d84c001d03444c50340e0f4102c807140c0d0005002e018a41c98041c0d03200400c540d81d228018082d080b00c1c421581e81281c0c00c07900c0d040f0b044904603802030f1040ca0070711904101c03110340080000803840d01600d007d652961104501801c3d44203d1b0822103000e850b0101384404420000041d103d01170041c0c81e1100d698448030741c18ad036a4010b40c4074140c00030315145800d01007000710750041990f603440707070130045002103040c1d45050458002000401100790b9800d985044924240074103030003015620070700f41c500f68803004001d481d894540e4010b40608080d00120340712078401c03d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 136974253 1250 136973003 136973009
    0xd060e0a0c0f0306051303020307020907050c0601030b0f10060203030601030c140d0e16050904020f0105120c1908090a14070f060302070308010504051315020903060a0f0e06011419 79
    0x114005540740d50102c0b0140704a40000d0344c41914182c00541d042c664540c00d007460301e4041c0c00035401c00700360b075081003041c0344001c0042c01008000d03c0348820008003004000c6c040c6214a445080e6858850602c40c0d99001c002d02d40315603c00e0b140b108000042d004004c4981141080c038000c900c00c001e4030704c181c50b01104601428001d440c0040c1a03454104158018941c6481c504181c440c02144580704001c0c0700664068a40d00200c00c00c00b050061810b0314030500500410b0418a040021901c510400e12100b15901134403000b00007007160780082219500324120302c5030b007854141800c003460f101d5600d8415840040102c07140240c0350018440410010009010840e0501c12a54942d07000401942200303004401159074070001040e1850b25025403442010800030751541d5424a864044030b030201d50040e01d07500c6034200200c0200d52020b05c2200d2040401c0100442c210044040352012101d000321501c800307400850040c04406610403001e42410705c1264030742c51f180138000603040b0a041941c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 136975503 1250 136974253 136974263
    0x62803020604150e0909030f25030816020a11040911030d05090103050c09130902040e010e1e1f0f0209042d05070e0103091a010b070b070203090d060e0a 67
    0x1041c0058818001d003108502e040e110340d0313007441c031404a40074401040c20907034130007105400c00d05c21074050700b4042001d001084086000b01d00141d920548001c803855080500341d00003141d4208110000300544d5648040743c026100030f0200e20410385480e6441c10300044150300c507c1d1240c05107401d001c0380d041c00d40c0c003240780102910941c0c1c1d00070001400e180d101d1581180402d00f000000b85848003131000ba1410050040c0c260048840c1d504000c80c010117115200b00c0e0301c140e4031501c141845800348580d4401c0551440100b00c841511a49890410241d0504410b51b60117031603142550300c101010f242180110100c04522121403407012006809904109500305203444a10007440f0281c201a44c0241280711300c1101810303800da08281592000c0741c494001c101c0c02d051030240707175100f980240c2469000b0130080800345c60420840011050a90281600410120350720082c40141060603400040314001585082e0b82d4402190f9104022840a002c0b16030740d141c500400c0101340400740403a5400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 136976753 1250 136975503 136975507
    0x302040507180605040308030c03040317090c04111602060304060608120a030b0406081b0303040f120309080109020d0f051f0f1109090105040506060d11070611030628030206 76
    0xa008010420150000b20004481441a00080780360081d021a802d80b40c00904203840d598580c0c20b10002603001070401c400700311000100e000707004070243d0340c03500170060309010300b00842c0a4070401098820222043c146500104000035026400035101560160b064900c41d40700e645900f043c00040105034000702c01c90007041d03500c0c003029008100520304d8054544007000101d01480511040381c4050042d0f50b40d5500c00c1c120840340400000114000e00340c010116450300b625031030100300c554000c0d8081c1210400e1042403508054211041402919004008001d034400c3ea40001d0020350b88850007500c4025001c107d50f0038000140801c4c000488884c4801c04d6a51640301c01400421180c5012090180b1b0b103158260305e000440304440d401100106105030076400c2508000040c40d0140c00140d000c40200500d04d102c01c401d006084038844a001ea041c2c0303418481c00c1c4402a141c0c20000000085010401c001184e07807100c1400495143c5000e00404507404200259520709941e0030296100c000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 136978003 1250 136976753 136976761
    0x7020a0c03260309070501140412060b0f0303120424050708040201081b0d3c140702030304030c020f0312040f0608130b060f0a090903081501020a020d080403020405 72
    0x40305100d0501c414880a800b0020003110a0410b58081038440310001d40211204000c19032007006002d5000b414070058a203001c2e513420314140319030b402c58412110180c45140000c0c02c4e02d81540450001d0317809502452409044890390750300076500500062400f20f803c501e955407541c00e1010b8403c08545841c0802c02410300d1040500741d18000c89049000030001800140615001c07600400c04102040805040c421080041000351054980c0007907040c03d04841c0007580c034458414107045450a5103034020000481d01c00006070f901d4040c0c0c003402000034006001005a0000849501942628000404204900c0000c00c3c0500030003905502d44500090901e00700042c1000303008450b6041001100756030303a42c2c4103440c901c2044030b40140c041140d0f03d00300081503500b0110340c1d11050044c16003031010844400251420203641104903650340e1070481004042e00814040d07046008402c0b20b00d440458030000130340d01e01d280d06c4024000c15503409080f0811010100b5100a190700034821b01103450 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 136979253 1250 136978003 136978013
    0xb0c010f0c0f140306060f12040302150c0409090611041509080106030206160615060e04050f10050607051905012007080a032f090a050402031e07020a0c03 68
    0x11848800400a074500384103014100e000e0116001e0665641e03e82c44200c50300d40c424021150002401d03142c200604120860f00c0c64500f10041c000e032001c01240c084c1a040908000385004819540d0007043c0c2010302c140010251444141c0d8221041c804001c20106001e2500d14043c2c408c050110708589808a0003040e9240360a614514444203503694160403955000114269106480083d40001040160b2000c0801c14008a40c60310f00482002ca13030014200c40c0156203208a80c031203030001e60510801c00c2e2510b440e010303064200c107c1c56032a03641030516441c08031442d81e4501c91140f049100141e0700701040014080401c2040300c0002d511401d90071070401c14080d000090040f8080403108800008003c0e6440965a50640228006003054800141600102091512044001e01d03848106241450340040361540da5485c005181e220013512041c801115580e401051045006004206400010401c070010817442d045c804021516500300c2642000d41c0b041d8050f00b25401602c0c0030042c04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 136980503 1250 136979253 136979261
    0x303080714091c02120a03020a2a0b0d060b07080705010b0a0605070803131514090318040902011701230f1c02060c010c020c0a09060f120c0b0c01 64
    0x41003645654039101c0d05810760154612035841c02c03942c400e5090680724121850200f01c0c280311480030307004440101260640d02d180c004103810840050703002141c0310b000c0150040313161485002c290451200d45511208605507040103000e040c0e140d031400b0400c0c02c00030001d0340120b0700500240e43d055030750b64001d0800c00756981c0440030994856080c5203000c121420181d21010440b103040c0e44003418113145a0b1014001e600141059104190907041355020440d14030030b48194035101107000034040f03a90018540400c1005000402c40e0708188101280c0c24142d683c0d8004000382103600180d04401480103039414010003040400145c041e40000c60500c0c01c050400000000e503903035800b0f12401a44c1040394003080c0d01c500541015240030038140280d101d103400340c0d4251006102504003043d0440280c00c498030480032100580c41100b11744600d0030401e625070007810b40d10109108982c10b02501084802e0f09101e00311005002d19002d0f030a000c03141d007410002d0212018290b5450100e109890b002e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 136981753 1250 136980503 136980511
    0x20319030b0f0108090304120c091a030d0206130206031009060605040603050a090c03080a0309140309090108160b0d02210901050708010503070501050d0b0901080708060c0c190203100501030308 85
    0xc50340b0102c404080d602030046248a403200f90000e61400c0e080114420707581184e620121402c009030136000c81c0540090060115517061503020592810040c0b003010f2030070340d440358400190341094050052403d800c044900c0307000d405856140e540d450380045408003d0040e840000020301d800004140b450b803100050040310700e10f90b020301c40c5460340c04184084501c225002070084030300d1801040020801c0d4040e010081d024140090505102c4d111809000100e21060340640c0000404000740c0c5803d040b96030161402070b000340850400356070750105001c1c0b1409018103240340411124012039007501280c001c51240e01508401d450b281e852401c0d2403505440018040d400d020004504901c111803283c12242d0040c018200c1b82d18180c01515203511483d48409a503488050950054503004456402800b807140101086c03031410b8403040c18480c01400a4203128410849584001000110106201e003011003c202da5001d51000034640f08030804400c2d05281804000410305401c0b103512482 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 136983003 1250 136981753 136981759
    0x60504030c02031b03030304020d030e0411090406061103030a18140d090501030b0f01081902030f060135060612040302010e010c020a020102060406240e0403120b0f10020319030b 78
    0x1c148070090030384e030184044902d40ea4050740300f4000075000d40780591103407100707601a08041101003800c001141c00e48008400c0000c46038000241d91800d418284254030040500d80392a2800201041c032683d100e10002c0c2100b40100d031501c0900103280307000104e800c600f9a0101c04d552440700e00440194941c0200c0001c080418102c900006481d4064010a090400021310300e00700b00611a0055400074400f4000c41c07207101030501e6420280c081c52006500402404181221078a8410001885540c41450140b0542010208a24103c040d225820448502c000c1009400e0f0365010208c0c0d69800760090110030707045418148401d044c0c044d8080f900c1a4080c2000340140482d111060341c0ea0804018028010303405900050081045503005207032001800400031410704000b00c0c030901100c00d94001340b110b890707000180010140c1040500c1d0110498540034054507518900150032030740c4061240c0d000f01c2180350b0800046100740b0880e25624003012421144550240f001801420466038440c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 136984253 1250 136983003 136983013
    0x3050a14060303030613150b09040b030d050f030c160303200406021203100306090b0f0604050609040b061207080c0f040e031903020d02121e0c0a1407060504030c0203 73
    0x650200c002051081c071000e00114a15140c0301c061101500b44101c4488030240c0d6542000700700424100d8840c02040040e20403901c44800c1400c100482e85926038031031180d44000c20f03a540c3c0b60340010944103180c1e98140e10585969035895410424440c0f0455034840c44442c050b04010180c16034030102c142d00d40040c00b19904042558840140e1140d0302031000903920160f40c00d040324100c04021940490124000d2142c9942c0350740e010309541c008201250044510820803da03441030344a01c6900c10811501408141048000320700900c10191000d0550390900300000c1c0d8a0712540d480245003840c1c50212a8580d075039089071074983d081c0303403c10b80c4030321094003550301d42d407906000d50744000c00354902079480d02d40d1501051340c10460f0030780c00314207058090044004c845850300c0900751406003400403080c140707420340000410329520310415040c1d0742e28030300344406913000805030f400c0a071090a0500c02200f1201c14202c20340a042c4d401012035003410304000030582d20281684000344240c007290 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 136985503 1250 136984253 136984271
    0x20a09021b060705031f03080c03040312051e0a022514030f030405012d080106110d09050103051e09010603030e01081510030e030a03090c0501030e03090402070c1503050a 75
    0xa502e642041d41d1401c000344052010843c10000e900140c03004180c102100300d0070b01da4940d2414510b4000001c1089160004941001409100c0f82d140c81e01d9001803902c03034604103004ca80e6070218a820000c1040081002c1000c1c1c0107540204541c01841403191001039151520000382c1598400c18001c1e15111885c0e2010007180e828000b40e051206069000030314146420300004640b00a90b18500c01c1c040c0440844000b21018001c8114a580c80580e4912015604011001c0c0a88104040717004041e0b001c0c40c08802c5241e0f2100d850410b0710401d02c0c2c040303070907111450000003250000c108000782080c610107018081a05600c024101c0744a9114901107404410045d154440102c440354030800410040700c0031480e021000d45120145801c001866200e03225071185190486101c003008242e807003402d013050000e0ba0680d4001014240f070188048031a03140a1610380c06681320885c0503a80110b021703030800c103840da42ca40c00f40014012000c03aa9508200c005d02402042e10700b4400c6d175140603226 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 136986753 1250 136985503 136985557
    0x30907061b080306040905150c0a0806060403150c02030d0e07030b010e01050d030c0501090f06140a0203090312181218030c0d12021510060809061312020307020a0902 73
    0x820720550000411421551400b080c0b002034000e4800840d5680550741c1301400081d10091043e002d8030780850750f01e440300104079018010000181c07e2a2069605010030400203140003c40c40403086c0a90000c2050900700c0c0c8164030714010070301c22004050500c0c1c3c0311100780b600081c1c01d104803402040e0b40b22440c0d0382d5215501000d1428020742d80c01c40389042104c0c02082c050310b154580c0b85e21545c00010712101a4440c0c58020508a104568140e207940f01c0c1c41c0748481ba4465142c01c5800141c00f189035050a014003680ca02c18071001c225000340c02000690544c082408070740354550034006640300c9541c4a40248a55886842036002c00c41040d160900c450400140b40441810007030201c2c0c941c2256070f11a44500c2000180d45001c6100758840001c031403900c26245d6000300d80c04060100482c1c01c002c401381000d94010655180d651008040003060441c2c034444030040c0350083c24004e0300c801c0c066170481c1584a41341010350001e120b034500049464240e402480c501d0168801d6603000c510200360 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 136988003 1250 136986753 136986797
    0x7032301180f0210090306060902090909010c020c1c08071416030503040e0c0c0f010c170412140415020a03030605040209010e0603150d0b18070303050a121103090706 73
    0x3800b402512454603005081081c1801000d034080e09207880c00350394035542c4400340c45907900034210a54003c6280d08450500f034135483d0300310403000000d0050311b0211000a40e290280030420384034441d0704c504010000c021303040e0240061b030010011a921411814041e00c1010344540c030320445d00c900590203403540d14862801054907441030185281510300354141d9a004006040082500c2d020440889a18400c21500c40144540c00c004504508010303001341403c81c0300d0103203044241884c001c10000404942c03000740030344000d04044101c4010742603100d140f4010364024983c0455540d4140c10704580008241c41810310030ba4060040903201c40906c000c2e40035158000c0d01080ad541091f04c220728dc01d201840c1d01ca07041c141d18240e10710440703000960074038600c40b00b03445070303250107060140c41c01d0041c0f880b4032461071200c0200700c0d103403440d5030003811817003015160001c10041c1ca4102e0180052900722603c00003e40c020f840d141d040841030107440b0412403040d00049405203c545080d498041c070303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 136989253 1250 136988003 136988051
    0x50c0a05032b03022101090b0f0604051002030702061305090606040305060a0509190b011a210405010204050d0b060406090b06040603020d09060203040b0f0714070206090307032301 79
    0x20b00181d00440b254507081036080742044001895000d10100e183c000d0304805050a6003408041024154174050403042220107807080301d4001c0c000303545440390540f114000c440071580140c0c0e21140341030064070102c3c258010414002e5100030001016959107103008817983c00e490003151135039995100c80041240c00d114510004003280c21900000d04113410750350040703500c4183d40707003540e0100f00c81040c0854025041001140d84400c1d100041c8240e117000a10b0203448080e1002c51843c0c0104411014450030b0008140640c3d81040e000040801070290142c4008080103400020903e00c14545440d0101085501c030f800f40d0300d040000034106400b401503100345a405000035180a051403401c0b0042e6002441c1403101a440d110500d001452a20066105034020f500da44102d00b032040c9284a01c11000e85100d0411004000d050001210b807002c444001e0390441d519a42c03240c04401081c144205035001502c0380c00a145100fa00c20555020645080c4016008000600f110b0119103001c00c1044 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 136990503 1250 136989253 136989283
    0x30711010e0d05120406020c060f0702090a1e0b0108060102070e151206010b091302090a060c06180605070306050315010603090302150a06090c0221030601030b04020304050c0a0503 79
    0x444840140d50080070003059249018005a0302030107240c94003440d182c070140294032000c00018040294983c1844007000c0e80707804607811440c048000182680c5030140085c0a8481e040c41e0007c00c1d00d00005900c454001510140c0a424402c240d410080041c102c120b40355001c200d600c00028207542c40451004161006030010038900d8450b000c02d20390a0341c4492240e60410000e806510071080d08001080c020110140c4441d42c80003104141302000e8507a070400b140b20750040c000c1c07207810b90b942403501c0191170003881c203169440c089040c00c1001c0e014560a1258562100307298070284065900994484c0600d41c40a210084e80c980c02e040e610341510040c8240c0c4010000180600c52103604000391150091048074020f10301007a442c0e902c2e400566220b1030142e40d0709410800340909004040c806a0b40d800501440c589060840302c80013600013561088138400400120313968000e41c880079001801034401c640340d140c145031141e500c0807148403440c415180094006210300d000546080c003c80c0071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 136991753 1250 136990503 136990523
    0x9050f04060b0102011103010e0610050a12090c0e040b010906080a03080606340c0e070c020d03090f0b03011a04050112090303061a031006050a02150c04090501080a11030307 76
    0x941c54140040000007015030465490307040070100180c02d400a98080c01e00540301c3c402034104401000480d5400b00010710a00c5010700c0002d80c0f403a00000030284440700c07444042140c00e043d1400f00c0d1010b0700382d00101821040c000034801481a00d848440c161603052408101c01c546844940b40c1d2410110780041c009005200001c1d02401c2c01c0000d4003061641d050590071096112415882000161540c801c0085402c0c010788103200c1c14826000042084040c403401c2d50900b000c0041103041d604402900070109081307003404252040310780d20001c1020040381000913443c0c2c1002c1003145d0007881030440b042d1000354000d0003119408116801c072001611050184d004003e902c4014210741d40c401e40505507110000030390044564541c01800300310030400341c1c0d00e00d802503010209560a8100780100041400100d066680003d4060801000004a0005552041c0c1655114840e541200b019142000c00001d801031002901e03141d51840741c040f482d8416080000d040d0ba0703004410020b002c0e9000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 136993003 1250 136991753 136991761
    0x150c030d020f04050a03050a03080c16020d15020307020307050f0309090f0a090804060c150e0d031505030a0507180b0a140303070b0f061002150a0c0c06060906060909050f 75
    0x50780c02081000e4a403405a410240d8031380010f0b820000f254005d940f41d400003c1c000041543c42070600da40810b40044450500707400002200009416040c000c1c0540c0700c891503502480303000e602034902004002029952442c11400003520f907000b1b048219518131a05600342540c1c01c0200c01d40c2c01840700506445080e6640b240c5030070404202030100c11426130355031101404142c111000300f000d80459201c0c0c4804400718981801c2400844201c920400d24092008011180106a0a624801514012418a04c8500d0103080d640c0f2a901c8140c1c548a040414810004003042c0c800440d4440341880d4000484408450107a0781420300c7d150303104002050900004141080c0d0300b00042000d02180c0c00e09a159840340d03001d0341c05484002110b100c88040202615005e280303107218008500c060000070740400c640158100000d0030040d4829200c03000200c049200300b543e01c2d00d40d40c02010910103580c0d14600c04d801032009014890000ba000c0c400406c1d0584c090145a00030b030040c041c01821552 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 136994253 1250 136993003 136993027
    0xc031b0603100305030301030606050901080a020f211c030509031305041d0316050d0914090417132610050c090607061a0d0b07180f09020306150c03 65
    0x400104915003202d18400c0100118208102035806544158000221641468104003030050141d04c0142917a0195464000503100c23a0010444000191910200107038800c504a0b42c2e030b412480790703c02a100e80038422480129202e40e10004242c030351400c100d581c4811104549a1186900590500302c5010b000c01c02810306500000c003c0da02d00d0048291800542005411940300c0041902504550502241401300c1813020320705186d00c9091007260145080318030320a0381c2481c0609481200b101c80001c2c1440b490006d003410000790001b403c2c0d80c41409047c0341c401c41102c0e000e000656007560f100c42c400b020b850307440c0f0b2101c9010070000704101c01211441c54090080240a02034920042c0300d101140d403200006005018495003010030045801c1c0400038888850300e040600c00c0c60340c014000b000c00c0000301100c0e001070042c503042a071102c14003001c0c1c0c1711402943c0030500c19110201d00007070324141076024502804c81241d28148805000300688034034024500c014919400401402131580 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 136995503 1250 136994253 136994257
    0xe060303070c0e3303070f081002210117011413080a030b04060f06120902092d040f0b07020705090c0d060302100302030402030d050f2502030703140c031b06 69
    0x4070140650654104c0c491a01c80c0e41c0040c000080440903042d035288a640c40d06000d544098901c02c82c00940f85407500340b07003595070652005c10a0109038005060090a044200b04582448403244014007550b90740183c20365240e01d0404005455280540404059a00c0303804240100b641110410f940840340c0c407002d11940c01031003100706055403107104818a4580d402000028841d400e0901c2d07846240500280070807903083e10325070f1884c0c84e0080c01001a030b21a40c0454210b030480d602010441c080c0410302c4110b009610280942a020100708410004041c1d20603080f01d101d000c008690ba16112418bd81c0e50569000e100e0303004c000000094030201000010700220742c1020000702c1e4030b0b650790300130a140f01c00804400780003c1e000000c0005504041090784004580d0785401c510307161a0001541540c050b000d10311210380700e41d100f0f103440b59009022a0361314503001000c0c0c1e13403080e070f0300d140400d00005d4118024290f4044c0740ca225046140115011038116100003808100040321401c1101135 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 136996753 1250 136995503 136995511
    0x30406171501170705120c0d06060219060b0a090f0213170a0206090102010902090a020d0b0a030c06360e0115020a02090402061308030306010e04020703020a06091106130e060303070c0e 81
    0xc0800d00001266003841c1000502074101901e1f1150b40341c03002c013400401da410b41d42001043d03501c103451071640702c0c2c00340e0f0b16a242035402c01000140c0042c2c01000413a569125401101c01d213041c4150744083d50031981c0100418600c0d00445520791b6034402c68512000d02840e00c0d140c054000d2541000542000d02c0240945481440009a43c1c0d1982e0b00140d220002070344d0004071070f54082a140801c8071248202c1c0c600700c000b00c440040003817844c2c4d00c0001c00031160080c02e040103d07c6120207010300000e0740421103e4250806480b408074403086080c850034043c420101020000d50002407a24400c00740022001500d90144c416481341d80c0910030307007110140003260024000c0188000440c000d0000b00b014060b118080d568a091401c00144007606410050b07200301c0c03042082c10f00003a0000b810345c0304640d0041d40031840b41504c2c00c0c4000d8540d09404580c2d0088000038810041c48201040e4009035140f102c03128580351624814161b40b400391440c001c01c800403000060040120012246a00c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 136998003 1250 136996753 136996757
    0x1a0c37060b04060305031b060112060f110c0307151a0f03070e1905070206010b031609170c0301060902040e010303050d020d0216020306160909020d0e0304061715011707 74
    0x7241e00404003140845119074425681c640011503040e032403400104081004114a02c0241059410407900ca84085440f110051406549038141e40f4454240d030400e0400c91411541582c82c2c4940c9403100ea05c95000840441d508500e29501050a82c064483c1d18800301d00720032242010134410040c00500c0c0004003102d5414810f411700003a05070100c1c0b00342071003041c4505003036840d65030125004042c1c4601600c4501590005001404a400807805a0703602290045141c00ca4502503081690201c0349a00314914038808000c0d0301c1446240041d907082013a506a0082050a50b1040c400b0100d006502070f111507965400010000300b0301c02c0c2c018168072210680d0062416210a8000080360b00080c1c2c540c0f14040b5002184040d86014401194090b80c0c1c0e0710b4000d40e4101054004000c030f6646d0146050300341d07002c141203c4200c502e9026522098220003100d90396501e625002e0801a00824445918410400094003100b408540b118102e0010703140c1011000c039800070700040b03000003000142 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 136999253 1250 136998003 136998011
    0x507090c050903100212072010020a090905060a140a090609050402100512070f05070501110309162301121b110a02010806060d02041a0c3706 62
    0x1001082442851184801519503503900d0303007180b0a15003003410018032864014070610031032040868500005511410034600211142c0b2041090b600e1840c80484541081c0300b01a4589030140031640104001034160319490b802a5991140c80250340c001c80d801a00304002600c02c115060041019040c062402482a04820f0701d8100d02021900e4940c0322221403500c800c00e100c158101710308031807880c06040c03a100e803802c04064810600400c0281c904001c11a040260560f102d01c110142c80c0d0103580f100081c081403280c0c01070a445a00261158521401000c85841c08100354800181c111b40b0b45005da100c00d40388100c6001c0401031890441307410b00182007003411001c0641c1c414200d80b140250501c076110110044010300508180c212080c5a51016a40401603030f04100000d51150045424a0f902c000c1121444040d0040754400c043c040800401ca003020b000f01d0000e0300100b40a0030480344070150f4240305d1954918240d51443c0200c2003280d94099460040c90202030050107804d0100d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 137000503 1250 136999253 136999259
    0xa0c0201051807090905070506030403020a0c0b161103100f1401050f0d0b070216030b070906080907050d020f120f060a020310120606080d050a1707050406050a18030308040311070e0703090507 84
    0x389d942d802214210016000303e617a00d010021a03440001c05840900700c0582004201e802c4220003420541c1e0181240e100304560701d4665504200c500c2080881850500c40100221440b2002e08020a5001c0401404200108541c2010a541c22100070003c0844d42c5410302500c9249200070040c020004600915541120304007566624070000c41c1b040880300c4191500c040c00804060003500304400b040840c90520000e04c00c0007c1c800c080c1c880445090200001e5031001624030050b508590303030000e965803116103008a0125a1180700c4000070190340c1c4079554104500101e2108507000040307072220250902c040c10341003041480715445144000750858032103e149140030303c00588000041c0c00052001da0b01a0b001c3e01105056507086252441420040c0c00a001c0d0b006a006000c100302d0b000c281100300500c10300103d14072001d03040d030011800e51682002400d089c41100c003a0003083d5081852203641e5800601071045640005480050740c0710508101c014203c404401d4803140300310a004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 137001753 1250 137000503 137000509
    0x3021c1710080d141902031e13080c09071412040b0a0b011b030507020607120302120903090a1806082a011403040303090602120a0c02010518070909050705 68
    0xd000e1001c0340c181e5000c0a142002642c680880c0d0303045801000754901880704c200c0c9624050b101c085000b0750881e2a200d00340c5034128030354000d15003007100142c02c44040409000d5450010712803103412242500d881504c509030746503100101d02c0c005410100c0c03100019034551069a0800c1d18508070850719107010f88040b086030b041e007010344003aa940401c0c40240031108803d4440c000500302c0a08107548840d0f4440c90b681042c80e0a9a0090140140000c1400455447d182200d103155889801c4006005100380c00030005d403c00e28072040241d52030000304106600c00000e4404121005019148a900f81401d001d24091a80551041907440e801c0205206900703200c130119221014100c01140c241103840035411710360451440d41401260500e00807604010310441c0c1d809505800c003c20300310030394608074000f132040301c5960490202130414044405000c3e001200072901c182d00034002500e8400281d4403d408501021070160b1001c3c008000c0c1c90342d942c00c002d401074007031015201300c0c0e9a51804 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 137003003 1250 137001753 137001797
    0xc050a0302100c0c020d0b090304050a0305010b0f1f0f200109020a0e0403090b0711040e031315020304170f010617060a02040609030f060e03040909060609050403021c 73
    0x2084026030403030140c0b00c036041c40034030400755039143c0380c60404503004039500800c129508101016210301500000180d04c1c07003080044a001300000340202d407441e55281030441c02080240d1001c5c0c42040c0c5e446c1850340c28581a42c60802103200c10620b0040400074942c196012001c810003c0c05010304a0b25034031a22080048011540140c14008502e070a1140f040040c4c44940ba0049054588244203200100e54040d828900b901c442c03c0a10340c0c1c0c2d02150403c691824031880c00f00750b2007402c1c0700e806da9a503200400580b01c094072900c00304203081d88943c848683d00e0700e030364629070050307009101c1040b4107603411600d08500ca0342d40c021340d54615100000c90b0f09640c5150003810f00812280800100070204010070707031703004c41e001c0310450030305003090b00003040b1655600c0080c055841080e021401d11400d87e0085207043c4d00d01c01100c0c0e585548401141c007400803404140c803090320700900040c1039105c030f02941e032040758035a01901c0b1074400c45d41e42440c0c0303e1400302c5000420103500c1c0d50030784c920ba0180d5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 137004253 1250 137003003 137003023
    0x6020c0708060c030c03042303072301090803150f060706020903060a050103020a0b0703021005010e01060f1701030305030405030c010504060b1c0209040321020403060b0108010b03040812070c05 85
    0x1000d0801a810503001a10784000580320703042e620010801c03c441c10306040152030704541e014186031303a002c2d24030340c1c18003041d0300f800c102c03196a00000540408100201e2042401c92030740940b041281d041001c6401d00b00c6444a10180281c1d8003000040d113020b100d0140890031080040c4501c0b03200802030085101504a048111079596000400b54140d10b020000c45501500b5400b05106540c19640403c0d1181d0852060300d0002a01050180406009101107007400d031000d0700400c12503039503007113051480e1020300c194404a608840031082140c407955803922066001c100540311a440c503541298694070040c400d84440c0002d101600c20360000380074590146000d0900418810882001c2100c1180740360b03030380c1c2c02000c010300414005864a83c41d06a0240e0941002c00086801039141034180b5130740441c44915520000d000320412110782d1060252040070f9984040f50b07038844003d0001d070b203c00d80e00580125400e006000340882c01c16280c3c1e9201d0315070316140c0700d12581c1daa90145000340e118 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 137005503 1250 137004253 137004277
    0xc1503230a0b2b02060f03090604140307030e060705030903070e25020c01030b03100603210f08040807030c020405010639020d0c03020d0311121c02090a030602 70
    0x42070080081c1103010700006003008890802d202e108041c402c00c0300c1e0340c1c4002d0321850b0000e61404942550345680070b5521048490300f406907a803516030b20858031070404423030403100016458010104000004140c034802d982c1604c80c091000804000c000075500706820860b541d00c010414051251010f00c001801804044044000d600344503800d072400c140061b0404000b900e05e20380c1010015400202d00c42620301c00e0a000600d04241004242001d00d54481601c00b00d04000c000020000369410783c01141c0b1412200f29480c0b24441c4d0100d940703008800001c0005034020f400720307010a0460004000107886810485c6c064007003a030200d8142c4200360702030b01c086140030300804004000c4c4038002100100b242600e0011055225034041c1c11302903054040d0065020709810410042820301403000b8503001030290214000b185001420b4007000da1000200340a400c0590724220045000e40c0c80c00c81030f15604801620382940c07000001d40041a18603441403200740b0001c04140c4500c024614806ea04c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 137006753 1250 137005503 137005571
    0x10c020f2e0e011409011b02040614030c0301090c061103070b010b1b01060e2d01090b0a150207050111010f0507020304050f09040f17040e070305060a0608040c1503 72
    0x2282001c0c0c40e01c00402100e034180001c0c4c105220208610310125004060b0900f00762104491200c01c0e0350001159590080d040b030714044021504040324900c190440310b0407001c4504224048041c1800e940c4040300c020030110000320300703000d000d000f180310900741e8168608407820002d003030b21009402002030784590f091202c0001c0009000c2d812084104207075400d10001d0007214a0b042c203400200100911651070140a5220000006240300f12010a00144403d0045a50715410444010060441d60602c50118050700203081024080c21012640d00350700a400b042d46404015900c40301142101026035580300b0040c030804106104031801004103500564490f8144400e001c04c84003072444041c45003401100704400201800941c03008680d100341e181c0068240c0c01e950342d0050243c0e800001880407050200041c241e80755018500c01c400445600e5000c5641d60000c1c0d46c0c1e0842a50060090618841c040c001102c074003440c180044d09070b150008102d1f40d0a50600e66264a0f000224142850 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 137008003 1250 137006753 137006839
    0xf0307180506070510050a0b0a1e080d120c030209180a20040b0f040803070b0603010f090305091002120d0501170303061008070c0209040809130209010c020f 69
    0x4a03200c10001d4042618003e1900d0f5203516400e41c0d03260f41c441c03480a05510740340003901c12913007908003105081d0050001c0403000d449441d40c50344d51300c0c3c401045010015451001a21071170020f500d1400ca01c4c1900c4400650b40d41c24428000b800212050f80241038003081003681d00d896503060070520008034030740c0c003910b82010010b10080d141d4108203d130501c5421914151a8010041113404803402401c00380e40d00c11850341209014051644807000c980030101700107081c008043c002c1d61181c9411002040500c68180c0ea4104580700c0b41030260000d002404550310078140b081c1055200022801113803103000421000c00c00c29880f02d000d1071055910340004201d84c0c0e01c2c14280100c50b00190024508600e09540403c0c4503d280041038070801508102044200380141c1c65013012640290070780e80940390038201078025900c00980540074150790f842820315000207101385c90500b40141e4038021413001a4003086030562804144540c0f000d940300e804d1800e010341c58145501c12652624200406d03038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 137009253 1250 137008003 137008037
    0x612070f0306081b04060312110c0a0b040902030604060b1b0c0406081f06091d0c0102060402060906091c0501090c06020303061516060f061e0305030403020907050f0307 74
    0x401208640141802c000d401d0042e59000708200d00300c18482c1d03500b1001243c07100000740140c00c03c1d0b440981190300d100c0710002220341c860103221070021284200c6645074811030900040c81c08034401c01c00252014001800403020b2900110f23004040100042125a00e512504000c0c1c2d03c01d1101d0003800c8031000158621040031301c0030031900d450450b001c2040300c1c50018069103a44fd02452004102c05028040044035125030000028248441c0c0400c0001c82c0c0134400a0010340b18045000c4612610980d40c0c03c944c800070744507124590182106081c04039030002c1c0900e0350003120132107074801000a0301c9007071560303040503104000d0301950000c154000c15007003070360100d401500f01c881190401c208012141c0c4070a03282c80f02c9119080070b190340d034681c0c040180c0705101d4000c03401031400d802c1284451440030305030440c5044e0742c440f54004041c112040385406c804c41c0c042c0310042094000307100c10800351604a60b0164084001e0415900d800c09005156880398001c460304800b00c2c0c1e52401c5003282034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 137010503 1250 137009253 137009267
    0x15040c02030a1202030402060307030b011e09030c0902180f0307180f0c02070602061302041107050a121d12011401030b0f01090b130b1908030904180201140a030902061207 75
    0x50f1001108501d0740c106500410080e11000344140141902e80c96051416446102c1d088081c0c0c0b6542d90011341d40010580051690100340b1098603001c0e800980824902001e00c200d48401181245520040851070140f101040101103080d605020f000350000f030040d54400c1902e10303024440c400090401102031444221080388801d1421940000020f011084e0005642a0880904a00c020000810380300240140c02020010300d5010700c0480c140c0100480001c030f9581840c400c42100a261038606000c80c3c0048481681041c00c851191180e0351505120030b00403d5816180004144024800380d40200c0480c281d008036030200303404007002281d01080c041c1502501b41a07a040c40005d10080c0010400802ca03055407556942e2454080125a10b06583c0780c0148a804100c01c034041ea54005180c0b00c1e00104a901d00403800c0c040340c8203c00610103540c0780d400340d05031141c02103013907207a6a2a540303400030200101410b41d503406d40405607031480060309a41282455490700c610788500021b01304 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 137011753 1250 137010503 137010527
    0xe010609230f0711030418020306010906020115030308091504030908072918100207030b060f0603041b0b0f0a12060f05100302091207060912030905010815040c02030a 73
    0x241c0020010b00450b0038886220581240162508041000740c3c1c103840d9040d84115846054007a07603801904c913050006030041d52041100741c0321a45440d9542d242070342654110040b40e840c240b11950144000380c0101c00b071541101c1c1041c215034440200071300c0f08455120649007500410103c00c020000100100a10340150012035860900c00301004031803100c0c49801e000c1c2d01c01800b00031070790200514610f40000e0440c0e03c0140710f21030000304024040d40750780c6240801c0e1155904a03000500505108100344041d210260005140d5a1580c850700d410041002c0801d902c940d81e00700000d90461184084c1000c0d1007146041070b80d40e1181d1a0150911440c45824030300607040101c10068000d8400145048541c1070340c00140544c41c007101200203100b1280415403041c185480c01500c101c0020380b000c00e840b16520b0b1080000d03218112003585065070840140058158682071081d54814942d03140c015452410020006c94528002025551a03403000c0c030050340046610005039500050030102d0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 137013003 1250 137011753 137011811
    0xc06030b01020c1507020a030605180a02151e030a0c09050316031e0f060506040605030f0303061009081e07330903080309030307080c04081f0e010609 66
    0x5044030080010b525480c110314158480c54001000003040b8040004031450190300070500c413a1143c80e4503184008100c203840d00c03a082c00d030707a401c80c4121010019504442d150000d00c100c610302f0f45403603a0320341c5521030001e000b0103015020042c0c803040303802e001071401003000407004030b404091508010030342e482c180c1c003c5200f503000c428001101c07100a541d4009403070b0030070300710781000408071165072007a1039280000b441c8410510300e1b0340a111540d44003602031441120180401543d070300c205a40c5400f0b40c01480300640080011900500e0041d40c805414446405e00b6019aa03030b07003d83c035080410710030b001c1042e11581c403150b5520b11800c1c000400600140702300740240d0100d030500401d111000310303041c0074030f00d0414507202207690160a80400640c3d00111581d50381c50b120740300544070380098400d4808994900049504003c9500585041e07903600801002d031a55189255401d8000c44010030400c0d40e95900300f9003e10b1020f0042d007016042a1001041021152004140394000c58048000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 137014253 1250 137013003 137013011
    0xc09040308071215060306080c0a0b160213020a0503150105041203031505030a050f100b0f28060c03080105120c0105030702030d0501061d0414060105071a130c0603 72
    0x800240c20641c200c0e041449480e0103103065104029100050002222840820381a01c900003406649a001101540e162500341c800c580005401d00418400f14014100e105200740701740400131510b8690385c1d5040b8001003251440c40079108010040f41c1c080d107244400158000b0070003111500144131450b00c81c0d402e181171840d191030034800180382d00c6083c5000741090303100e082d0b4000402007a1806001750100900341c5881101034a0410358400c030001000c100c3d400f42d2039568031030580070710415002d1000501440503010400c400c0244100c0340c4008544990072000c4241620a0110b8249001e41119240d0350140002c500307010341402016880700c0d10590451903e03400021010816002015007820400d40781d460b040382c16400c600a10900c0d20b00c0c42d150800010b0300d140d000f25078404004000d1010406480382500340425030307050240c81c8040b07400385d0340492820b52080000304004c5000b030b011507846c001d90f684d00e0003c0c100c06841a120201c1d22864480900007400103140061526040401c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 137015503 1250 137014253 137014261
    0x603110909060a090c0b0c0307050f160501030c031404050705010306080f0304030201081b0309010605040f1401140105070506010e01380304021813060e01021314030304050307060c050c09 82
    0x550789401c02881440440e40344d0101d0740c00c1002d003000240107020f10301c4d25991550304601c0d10f10395940208200b039815120300c5181248203400407680302d000728222641c0468440c100310041d00646402d004060030569201c2800c80c64101400c0350a0103248104040d1903030a140200050070744445411404803904400324a11100300b000007102c00712642805c0070079280d55444c0082070941180b8201030305100d1300008000b8401019800304068400c2213a08100d812010703100c0c442190600f5100a0b01c4401880c01805800c605141c404489a81490005e00d440300c60303690b1604050302070307015880345068000144100220541e0b07031510004082ca01c1e8005080c45101103075080c07002c50703059144050020219055455012940100b0560b051080b103560810241d00c1c42d0301c100c2c000e8192141da103051b0b00020b103140107000726010b03080c000002e5141e090418482d03000d80c1c83d00f0032140d94188020880041c0944043c01150010816911011507048190502d1410301e400402c1107403161506170104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 137016753 1250 137015503 137015521
    0xa03030e192303061509010e1503030a05030405010501150f0809010f0e03091302160f0f0b090a02010e1203120c123409150201060302300c0d020105071b0906031109 72
    0x6c00d04641550141081c103468202c8054010740c21150399903010f01002664402c0260410002d43c0503600c241c000300300a86e80c5414064003111861103480c00076100c0d01c1c00d42e014a00c01c2c4a1070f0742200c9620000280c01c8038000900301140d04000c5018019040460f0854140c07600740760051500ca0003040c158a021b04054410324074103d0752070002c040f4550392482009000110b1840c0322506d511200308807460030f20032126a40c622000710100d0000390240400081410b18210710024041e000b402181000e845000c24404842c00608042104d0710501031009240f4198010700d00910703294100c1c041c0058070b410b04c00312003001c0400c5201349051504034094045d40c42103001c41101e00c024902c0d070410311050000c030301404a541c030103540000c1502501c605015403600910500305401c1120100c02e200300201c0361501b420b40682d6074051500d514040155000304014090315118100325000345a0070690440f40d000035422494072181c0c1ca803002e008100c02f11035151199a0102d401e4501460301c0d080c030b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 137018003 1250 137016753 137016769
    0x31506031a04080d020d020415020d020c010c050a0203070905100902040b090d061e0f0b0a0317030601090914071407050705010e0d0206070f0b01050a03030e1923030615 74
    0x3095500140705000900b40102081a640c21012040d810340d900d01003190640003940042c06142c113100c04403046240000d00004881c100c100da40d8001e0090381c20a0300064907580002d0b041035410b030081c11001c1d03005035403c0c40800064480c402c0c000031a401d02869140380141a41c001c0078030544104000c1c0711029120043c0c81043c041120400c1c2ca800342031034040b0251207100c41900341180d042140b05000300d89500698803600d821103081004040704c1c41005002c110511010702034001004651500303035410401150f0248042c10304e4044d07269078a070050300712040c0030f11401304181c02d81300740200513900c06551803804120f09081c0b0f0601141d502c0d11912944144113090600100144c12030385a20742c0200c1d44001500108000d40b00c00e07060a0211030b003039003440222556040305001080520b0682c18410030740c1c0c3c1503541cac0400c0000013005d0001842c4551080d003c842441d6100081ea500f12990b603494900e0a00b010074046ca5100050515202c8080c1850340a001c2d1405400d140351280300d6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 137019253 1250 137018003 137018033
    0xd020f0307091a0712050d0221070509150702010e0319030906030204060503060108061c0605040209060d05070b07080d060b0706050c1c091e1406240d020a15030603150603 75
    0x5e0002e5100565450544c0d071403166801141443d800814442400d40c216505a0700c0408a1900503840e96a5114200c50611504071084e51010254810107070444410025101151040c1001468021000d00003841c01208041c43c0700c0c528840300d01c4404050344880940014030407810b055080609110018005000007403005042091101c001021962403004107115104809026401c10440d810008050a41100c00341c0c0a120003901183d418100801e1946006800402420441e414444560450350003908250351082c1c05102c01c040a0030360b4441d540c01010100c64007542d4001f2440c0000a0300d50092814102e50018032803102c1c1d0311003100c0d2100354800000700c0003030648440e2400780710110f6001c0d8100340e403901441207a0108540760044540283c802c0702203d0555444c00038000c0205014040f08040e07078012301c0a10f0542c10000300402c2960310040014030201e40301c00110088840303448609000903141e00c0d08106002c440741801c00a100e04000c24001c44c0d0441e1180c3d40c401030340e80 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 137020503 1250 137019253 137019263
    0x50118080307030c0909050a02041e120308040c031b0509150901060f020a0506091609020c12090d0203010f0f06060c050c2716030c05070c17030d020f0307091a07 71
    0x25244c2e1090300c180c0d5400c001c0c01510300208000d080000f6200000d4000340240400c0c480c181c035900c039414401481e40350032204c2c0041e403907010302116541100c50440280046840d1101d541d00417001a01c0340d0560101486000000d504003883d00080118081c0041c0c6851104040110705040c1d684415030a10705541326814040301081e010001245058640310000c5c00b240120b0091000c601400704111005104100301ca0b12801e4680c480c1c07004a01c203000d424000b55008110904144489201a11360048001c10040c019030103500030900351004075840b03058040da81ca03a2580070050500c60400900002d00d89000360480580d6803682d90003180d007081d0b200ea00d1401d80081c2585218070f483c44010004c40383c5854a09004001c003884040d20700e482008a4103113485c60550622034000e881031160404026480e06183c00c4101203900c051081665a60104005e0226803000c24000ac4c455845c841c841c265907813904d10f000501d001c4268002d00f2078115641140d001541c0c040d429120000d03000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 137021753 1250 137020503 137020511
    0x804020916050f040e010f060203130504090303020c0f0a060509070810050a2a0212181002010b04090803040204050a02030103030f0807021e0d110d020a03052508040305011808030703 80
    0x8240075122030203812000c3d00c6140300010f000ca00f01007010038070360403a244507494450f03454030380f0b1040e40c49002c3c1c0030120a0711054010100900d00d040c0e04a15003207402401d00501e0b1560041110341001d56203150100035610050a46080104a2045950108106000e08445030508100341e0b100d80d4003840b5194520703203c002040b40c0030040d90101c0c04421808001c1070003aa90903c003c03008014403e10300d8058060044191080c0c0f120b00101c416003003045400c004130a0110b01080001c0040550305c10444d0b41e20518103803162071310301c2261241c80c069a5940e4070307031805204200c10b85c1e6000303041c400000e005000420001c0e8101103007048591003414003415541d91280201d1030302200107050130400140740d00d501d000000c00710b0310f10f908000c07907582c041184c6c0361014103d960302c10680301c01005901c1024140c02182c0300318080c196080404210b480c00c258100c400160011740310340c058810501c00a010002c010702407103103038440034042481c5942c1c03c00544402580d40801070a1106250721 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 137023003 1250 137021753 137021791
    0x213050103020f041508010602060a050103170a020a0b1f08030a020705010516060501090207030813081b0c040e150114060904050a0e0604030504052701150507080c0c04050708040209 80
    0x250b01642c010789217090101c2c0e983c1008000c0180b01440038400d0f040035002d0000403400b0791004c0c2c00303440d040c0d9402a40120858952104d6006280d0000758100e00b1401071002d810005100714116034011000003403030408a0801400d400c2401c4459842040c0d507600030000ea03c81e558002c1100c1d0201d4a003400c19a0b140d01100c480c000958500e2003005007118544070000c074805802e50f01a05505000317035074240031540c622194030864210380001402880c01400150700300756081040321081076100c0305a600c0c0b6000e550100c5c00b5503103480c1c40d42c0341540024813099000c50005902d5801024841c000b01c4201d48000c022402d10b00c60308486501841d1580c0006001410b17541140d110f4081c0107040ba0740354909030400600917007050041c9032107018042142007030140345484550301c1004410054203e030b4a01140c02e500c09402d1a80001880f0090000e4000700d01d40602606500040c20080c00001c4040801c0008464000301200240b1201e88140405030f1500300140e68031002e4040c10301c0420907 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 137024253 1250 137023003 137023027
    0xf031c02090d0f050703061d070b0a02010f0515011e0503040f17181c02030c12070312030f05181911060c100e01020909041205040b030106050a12021305010302 70
    0x42c041e0014000080000000003040000030302c030400c42c1d028407030402a84080b8503442c847c00b8000f420f220140e0384081703010f02c801c49645008004001c01ea0000148000364240c6040543d98112120141000704007041112540c010a40c0c030a400f00200d108031a80c1e1000101520a00002e84090118820320343d101c0f0800440160088280580580c1c01c2d07103400001c07c42a80525000c1c038014002d902180c10003c4d4240400c10700340c1e8159008020340741c507800300d03400d1001c45d0040c0c0c3d207850503500c12800c0c0003006c54000810105001032a66012882c2103c2040600c00c2c1d500c0540090704030341c1d0b002040244142c0215045041400001910301405420b003001c820182800b038809500c1840040c1c9080030322000200c281c0340f94100181400b2100001003450f00700d0140d83c180726000150302c00003400081c0c5400780d02d00f020a25082c03003428151603a07803110b080d030801d80005010480019820403066000515000b0450094405620b02034a000b0380919040d610721410741415004501002c03221 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 137025503 1250 137024253 137024269
    0x6010b070501090b09060601020705011b020d060902061606060608010f05010c1103061905160c170f03070314060a0302150a02030d09030305040318030804050f06070606060905030f031c0209 83
    0x160130416203e1542032082200d6103076002602e0b000d0161149820001c0c1c2940240010240b40c00030800b0084644200d800348481c80381001d004450746030f620100940180c2e1208050b11075000e0401d02000c40182c1ca1070041d04031113403900004140401c40004202103030700407420805450080c0780192540506141031981ea8000c40308179641801040c080003140c403040341800300c40002401042c041d580310035020231107038890124542c3c0042d10321503908000c1012405c3c0b1071301c0c030b2040c5c0039103038079001c40d808100c512a0815a00940003030346a41d01c80f480d9103914209240c1149046070385240040c0b65900189031480c5560030085101000706800b00513500a0040c1c2d03004030400c0c03030300380455003051030004c00401d011a01100800c8100d15a88660000c0040c240166035010b4185841c00f0704000800003441d035214500c41d4861002c1108070f00040041c0190030003050184c80700c07086182440100b50800c40020361141e0309600138441315074062055200c0041181064500503915041c1901150140c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 137026753 1250 137025503 137025521
    0x5040f090b0921040b0a050708120717060301140a050703060317070c0f06020703030309060b042306030a2f090c0307091403061f05211e06010b070501 66
    0x1458000100100380e900460b42061600d68098203400d43c0c0d0082c0d02d464140c0c040ca0241c040480c00900c003082d00321303000b100200070701c2e0300078a200c0c0d082520008404161010854243c0d0004074071500074440c0b0410b01d29040d802c020101d0003800503400e030b648074001c030300c100070702d401c80141e120340c0881d46450095200c0300165070446000c04080c1d21084d040d14095220a0301125182041000080c0b0381800701142015120141e028164181c9180c901700c0c00b8001d400400c1c1d9803290356281c8416aa561482100000d0040454050700040079094802182c0c000034982c90098001e404400d0020781c600740d0080ba220044085122100c0e003a80302614810304040b4040e8200c918801030000c00003201003d10710503060707607942055403074844201d030180640c031104403078060b4050702c08180b407208040c00c4800300122844c4e010382125520000241500d40d040c00c500d400518038444684030744410711070002218540c01d03001001c0c4125841c0107507500c80c14400d5003007041020461504201d0290042458 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 137028003 1250 137026753 137026763
    0x109140904080d110702030d0305040c0905090c1e01141309020318030708031602120327030a0909110306060a0c060f090b0105130905030301140a03080309030306090a110405040f09 79
    0x403100710b08118181e1a03205c458240e2186c420f50012420f0b03144280aa00e1107564000a00b9103c98a000781e4a0302900c8086c1441d8003502484404252945070164000c1c03800e50400600680c100c0090000350906540402d094480c050400007085141c0500850100301ca503000c000503540e42c7c075515580f00341c0c501c0d11807151441c00000b503684144440c260182d402404051b03c0e0680b6045c030341c030f01070740d4400914030300301600030092002589426802c0d0120b4101380803400c4200041501d41e1a440c01e40d8845e04440340403403183d28081c030a000c0f151007500058a04c0202c800d185040c04030014515002d9582c1d51010008090801420454103400c040d54801102005001041c01071600000002003401010701400c07140d42004e0494817240034242855400002942ca56420301c0040304002c3c01d40b00140303401c9032280000000081510005600c120507050165840303042c05810021041006003400b400907040c10b82c1c6154035803120007164100c4130112800a4030845025442010380000000500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 137029253 1250 137028003 137028011
    0x702060a0521010602061914190605090402030c040b0d0606032303070c030201030b0319050313080a031b0204090204050403080103021302180913080c0a110109140904080d 75
    0x258a9030410082c01c910080c91104041124985851101c5000309208100043e880b101c0422444400030010076500d80c402680820b001400d07109540002105a501e41c42d03994400d002071640c6480d5102d41405890200c42c4e24000b41065000a541c440b260706c0b045200f0b91361000c01210594a2030a10b41909074030003001d1161542e80c0c204080d2404005402c400484c00c1d13070510381c9032101c0100c00c0394407032640008418403040c11a001113005105101c040780d05031150b11184000f82400890050510348100011036603103880c1c02c040303900518150301c4200daa902c01400000000c0d001103205921a90024208050114500008015095254002e5001854241400149035220400c0b50507039009443c0070a008144284103422440b0b10051010b8031481c0c409500d04074902040900c1c1c21160440751454100318985030081c0991195a4107903042e804444140d0402858040201d456002401d01d11615842d004101d24425032480401d407140040900040800c1001001c0d1030700d03001300540400c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 137030503 1250 137029253 137029267
    0x70f020c06310612060504060e04061e090c05030f03030118020c0c040204080c030601050a081b0f0303280c0b0c07231509070f05090c0705061e0f2202010302070206 72
    0x500300112081450542d141407401c081b40c141040d0040500b11000303080d4004841d80c07031b80c0ba504020602404031300e1210007800d440c0c00c084400c5009038001c641c005d41030420090f203030004261502e000c0207800055a0810b01c010080804800600303600c200b190b04000d82d441d4298810617080010b40142c039684148045008124208009a03484110342c003501141c2a90b42c9071003c0101c001500c2c80391040582c4224819481c13884081d41d000c0d170750600a80340c107117844480303000071f41507400155650103440b0100240c0008481381000c681c00b0101281080301e05092180c50350074100b48014150305087c2000110032042100c07071454109884030700081c022815407004030031510b502c1d00400002031140000e02158000a010401000303e403100003421925624190501c81c0c044030003000e101070083c00f4000c01000c0740045c004d1910607440d81c0c09a440c480c0701005d04004c3c08102400d0b0030700081c0c90000300903040448540442d0040b04694100240c8038480c40100e000e882114002500310710080f0b801 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 137031753 1250 137030503 137030507
    0x11070303080f0702210f070c0e040203120c0303011211090114010e0307050607020f01050c0303070201020307110c090105061303050304090603022e0503040f0204050f070f020c063106 80
    0x34502500722248844003d8880b280b08070307600d11080d0726041d040118221030149008a0000a1255604c00d800c2c0905040c0640c4440044010a038040400414164200421131609120202c5031555080603641056107030380d440e41c0e032804140143e92080646148480600c581400e000c001c1c4e01c001010b4903415030b122844000a24040b544881c00b06110311541c02c4180f802281031819140c0240c0a01d081003500d80030091114070145c1d8081c107200040045d030940000c140300561207040c80d03400141c4d9a0614500c0200706158801300003405800c41c428013070030355564680507030445408948040d1504003000c0c03102c00405181d4070086c024800041c3c001031030902c0340c00110442c0d000700d80c100d008890050200080c801011a81c40c0f01400311008078038a03074062005180c22a01030702e0500e403154501c0d4082400c6542c00d4a0110800703200904008140754421072443c0300340c61b24800390404520540210308540103038007014407000758071304030b1504508039410040d08504c0b540b10030f54440c80c1c0c4d070240 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 137033003 1250 137031753 137031767
    0xe07030b03010501050a1d060f030d0e0907090810090201020c180f01051002100f020906030406050a0f02040506070803191d06010b040f0311131104051c021f11070303 73
    0x3050080d400d1500001e024038140701000b0441c1c101c00c0c0c000510500d8500200c0c4001c400504171617000100c00318140a5440130000c6074800034117521010304c1650458100501010014030010420402441c140010704001c01c0b510f06040c003440c5c0210700341301d243c40140d060128100b036180d005890248e06400519000700114040c9980190482c1d560f41c848081c402c50f0307000441803d01507441860350b02058005603200320400c0407101c60043c04c00c0e059800048c40e990046d03400365250380d2140180405160340e841400c2000341021000c601d07203498200807542c0b41c0243e440140007010044000b90180303250008541003c048040c00704104481c0e0100710494202903e4500d05520070480040348a9a0314000c403026510a2200030701c3d0380f4619914140d4400074100c0c01d9410441604040300d0b10030990042c0b1000c0c0b180d802e00e880e1902d082030f060080d00e0241e661680904c0140070300c0d0703101680381c00200700445440c50401a01c80c00c000e00060b141007070b1b40c0c046142144036840d4004103155100b88 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 137034253 1250 137033003 137033021
    0x206030c1309050f04140705030601270b0307091109060409050712020a020c060309030c15070e0604030b0402122103070801240f0e040509010905070b0a0504030b100e0703 75
    0x1a014031020b03110328103003080b2003007111080b00100003440402d000c07600c082c1c9050303c0324103134100300c8103050303258804a805c129003079001900000301d4030308403402d009140307284070b4064410b10010000c018260001a07502e035018402c0006003076950300d04459205901d02180e01003030000c0d101d56502e60b81d07030b07400c0e02c010304084643c0400030704034840700b800402a6000310b84881c400c0d6401800c50a904008006460340701410b541c20501c01085403a01c0d508040c8002082da000d40860206c1130710b030025018000480091405100311010802840040c8083e40001c0c8c0040d01504d03509040006000e4503494135110341942800749140b0030ba01c4068490030310040d40314090a59400c10b5990f603c0c3c1c0c508a0800f005c0c410390454003c82540c2e010154441c0c1040d01035245546024010840d0700c078041021a003050303494102c2c0f65155603110003400700c1002510010036000c000e481c50a441008001d0850196000050049038854041105403840080c800d001c0c0500d0902102c0c01e04109201400620000c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 137035503 1250 137034253 137034277
    0x702160f0306140f0a0c1b0303060f0504060321050c0601080a02040b060a0806041505040903020a05071505040312170a091b050117060301090c0305060a050a0614010305060307030206030c 82
    0x140015449202080f803a01401380d440e8090299240c808a440103000e2100034042000300040802c11440070509101d10720a00940740050880c0c1000c1071402182c3d1180c101c140200d060180400c0000c400707031416410101e292595201000c0510005c40f46441240401320b807070310a10300041002c0b003020035052000791007180c08020005240c01403014600800340140e0209061400069241c01d280d04a68061142c40480d10380f032640b100c00140c1151442e59068006030b11908199042000400c000b038060419006800f40c0c001058400038200e101d103000007040034070b10b20100b0b0344090040c101e030001541150440405860425615030050a1724141030b0f41d070760030001e0a650414a400046400d8500684d0741c0c2d03a443c690442d0070040004040c180541565279041c544010840140044020311301ca4006041a81041c0a295080d00d4001c1c01181c11541761210030080034940d0008483c1e106402e08012961b43e941e03400081c2041c101c0d9001030742199000041003211129503006156000f05c070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 137036753 1250 137035503 137035511
    0x1608160509040f0e030a030905060609010503060103021012020f07050c120304090e0c09040f1a090d030905030c070609050a210b040c080a11010e030f150702160f0306 73
    0x692521051010004444020580801110381641002c0d00240340480c20003001140e9034101300c100c1403541d03000c03940c9040003994442001c4c04000051000d03d81011085800b13941c0c071750600000a84402040c440284100e40c60440c030b034441c6001d0185c400c9202402c604c119158120750308025005d5002c048111400c1c007502da24a0754a00d0310b07420b0a40c0c4502060000c3d802c00341010405d42c0180f001c401e03040c6042c410f500940c1c0140c0d64080c01c0703520442c071410905020400c249801a5844004032011164100c030030108501070600103206a00300c0d03200c1c5400308a44842c3c4c01d0103410b511031041d80e410b80b0b000d202c45c04144550060611004c40304103035000c40e0107a40d95040e03c40300128030414050090046070400e0302151000300c030180c0040c007036490600b0742d550711400645401c05040c000c4500d1103c03500043d941e5a0040302c140e02d42d01c4241d0282100c40752495072242c44d40101817a25500003050700205003018420000da00c125a00d00d043e440b41d2540302d600307413a441c50141c84100c42d05414 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 137038003 1250 137036753 137036761
    0x3021003020703120c0509091501030509030406141818070206090c06031603020408060709140103060e160315060507050d1e050702012a02040501080c06090f0a0504051608 75
    0x200303100b00c42200d41c05a03544500030750302040210240014007104070800800707002c401c5c00340d50343d509064090340c020320b85034100a001b68000b4051b40d000401d050080c4c0c10a020420038250441c0702218120110303802e0550b10304d9a400110410340c01c1929603a08403120800900d0b0b111a0300c50810f01802850b0201d5483d035503455180d5a4a0000b480203580107802031022030b4862041d03c454556083e21810054242919028014540182290f98400044020343e04003d0703e079041c00600c01c02c0100f031070700b07200541c1010040c031901c0901804009080240020151280f482940701d5244401c00c0901d402c4c071590741c0c502c01009604041030999160040b80504003100303000e0000030300002c40d065451400381c00002e00036541908154820b906200c501d0313803416414a180c0c01040042d40551200c4490030000d80107200440340c058001350101c2d80640d44640c01583c4c2c21083c0d54406100b107a03030780c04040384240428190080c0350b12958000342080b052152104400a910483c2d541c295514480b40ea1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 137039253 1250 137038003 137038007
    0xf0f0f0702032b050c010f020c06011d04020108190b040e0a0311060f010512030c06040f03110c0109300803180a080a05030a02130b03071206030209010501110a05010510030210 77
    0x2010b030900b40400c80036840c003c010354000c201800c0401c2c00000005201e0100c04c10800c281ea00061a948660304030358010311002044d045681c1e200340e000400400d440c40d050b80040c1981d50301a01d103000064440582e00324210858100704000c1c00060802e1003400d190200301983d0381000c000480201d8448a00d04803400000181103120300d48842003480d641c2d01e8a001d019030810080f550b81003a0108000030f9203046010000b490049206009400381d2403c039040040031481c02c42030340520740d04010301c0e021051307903c40061025075070034105602c0c42708104c40c56901040c420851003d609495201404203100d0000c020310f200300205032900316403000e5050401e880e4141d00074010003404050110b2419184568059540402008001480e01d24902181d00d0254055840142c1191000040007800c50303000e4a06260070140d0070007405060700307603030000d00c4001050141c0d50402c480c41c8840301d40780b2420040c0420392070308000208440d0030056522182c01015001c10b9005540e26021804440c1c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 137040503 1250 137039253 137039293
    0xb03060f0103020409080c010606020a120203030f04060e071208030115080f0a09140a05071a04081f060b19031109010c0f0c0f0906051918020f0f0f070203 68
    0x825900600c00c01da003150301304030007403804071410740e0382450522011075440c009208010180c40300350010160303850035141050911003103081da08210b400900034883c9400c1b01048090300507a0001c070200316444640190741c9420181e034000b503c0e61540240000902004000440c1642d40ca0704003d03c034075002520641d1810410788d121901c4101000009014882580c0112017951140c04588a14150000381c80d1512555100607909904072070003c000c510301e24001d19600c6142d4040090800e481e01d07a10320f4607581052185440740001c60209035800503241e11841c0507280c0403042e11340311000403100409c2815006108800310b40703048005200282d00d070090300c0c60003805135900d444990243d1f450b901c5021110308100d0380b81000b01c10106494220351040302c0900641c0d400020b0907850300e002c014104d02c110505800d024110403050205554961403241041903408000d40d0701c0a0014a6440c1440785110a44000d18080340d0918208034200082000314000c804841d1540c110791503400b100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 137041753 1250 137040503 137040511
    0x1c06050f090f0106141201030303020913051b07080f040b0d05090114180106091b090509040302030f0a0e0a0e011409060f011d030303180f010c080606090f040615030b0306 75
    0x1a40d408001002207910032610b640140d640d005c1c031036003018990841c04166800a8100f280072907004500350140e4140443e180c2c0c240229880284100d003008503440c0020114121001d01401c00058000d090102070422a0b04041c41609856500d41c1d4903480d62065801c42040c140043c2e060001207030344c0490500480380044170340111002d1645810781c007140c00c01d600074039106072135407142c01c00100d03845188950449041004a480b401d5045214010b241d030b4015003145114803040000d0002090f4000195a5000d45032111150b9a0100d140103480c071414080265601c501c044801081e032000b1009054122680325a0000e07106030604100445000700b101c88a420007402c210a170b140e03601c510a400c100311003460742d1600000d1780101280c1141c1c800c0315060403400355040303440b00700d0100b00100081d0110400080101c544101d80041c0341d0100a01030600c50800820032040580e1168141c83c400031009108101d0540d880e10b08100c804040c20525011904d4803c3d0241d060074049a100e1007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 137043003 1250 137041753 137041771
    0x1603020309030406050a110a06021b060f0a0c1106010f0f05041a1507060612020102060c070c050108060f0306100501020c030a081e040b0a0905100507050d141c06050f09 74
    0x14642418022030b140e8206084000c1080b19084801e00320881c1404035448c002e01a50700036a9401c05804201c19003640f10031280c0c80380c0d111008101004890984240c0c000e21018004180d4441840c021100300403082e40340d4070180900d90000440c041075212100807265038110115000e5912030401080710600c03000300c071540400d0700b15445c4516000704a454605c0c500e080ca0740c1021255161001194401d0700310001c81441c000b19030041d50f8041196640c00504001018584607041d62031640c0c440c2c99203d060305211115001c039000b5036610968aaa040002d001c40b030b000c1c07502c4880c1d0f103c40c0d9a544035090150140041d68010b41c1030110380c40e4045500b01c2d00103440e12180401e640c005280211690b00c3c06c50060001182005101d4014039103026103030b035070400c0c040c240401c01031f900c000c01056006104082014800052001c100c00b09808000d052090324480c20b145000003e220b5005181cbc441402c1c00445407001c4419403015058039010368031504072400c4a000d1060402c019034840d20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 137044253 1250 137043003 137043007
    0x30f03090706210c110f03073f09031406070905030d1d0a03080c0709050c0405090a05040f0501020d06030308010812031308040f03060b31020918040803160302030903 73
    0x106480543c1c01035800081c0c00c1c43d117088600312129151741000305480c421000c0c3e4000207081420300503c0c5000c0a4200420071460b01d154400c05e00401c0791000700d21056541d69825003855900038040c1a68100654020120030304814044010070b031164030171101e11003c224101e50200d03130303800e001601a02c00079140d01c03444c04100610005501c8581c0c0e01070550342c008888840030000485e020b01415450940b5001403000f00e080040c0c45003a65002410b803041d00700140010402070340c800d541a5000350523110001201e840383c1c01c1082c6240700c461005419507000040032206800e4960048088a00a6980420310b90b00d40026070b854a1801022400090b0b05001107800c1000a2000c41445441088441d01c2d141d034604049101100c1307a072064821680e180ba1901441c01d018441580b1070030f0181400b02c06220342c82000440307000e140134144409901098072015a141e000c01c1e1200c600e445401c80380c50b032030300d458035580e036a00440fa41d4018070002c0d401004c40c507001c0d00a990103070b056040514 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 137045503 1250 137044253 137044307
    0xc050f12090609040603080c07030b18030d02030402010e04060b09031e070314031e09150a090605091c050604050f161e180f060f1a1b030f03090706 65
    0x402c903504034060907540503980e0b40b000000a0140e80003884d01c0c15040e03010300307c140d2950925848108000340300483d201c1d0703a11500c400b490008000c83d201018404001603c82d2140d000484070003120084e1190007130300e0000042070390081280540300d101e40c100d0407507040400950707245040380b08000d040400c4e60301544042c000101005400c0692030031002c2124140703460302c0500c40e4000f01d8240d2403070100c0800216030501e41000c0c0c51001400410400c1036151000742f041c000e0490401e4840c4404101010a041c006035980d901c80c00c000c3c12485040780074500007803c0090301d44105660440362485206505003c9040c04551a41d402510000d81c102092030108101c0030403000c8528001e078000456408140c132248030301500044040342e1400262400076008074011141150442c0c1d000c014041410032142c0c070070f4509140044890705070240c4940c11240101d10750805102444194000490100c290303d0032100038502c02c447c000c0440d8009583d40e00c1c00d50b000040000c0c0e590300e40d0880481c070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 137046753 1250 137045503 137045509
    0xa0305031b0906070c05030c0105040602030d0c090f060512100e01060c0602070c030f0510110901030209030304050307030312050f04032a02100c03180f120609020603070c050f1209 79
    0x10001403440031004a160a02c15000201180c0c80b940f01180d050341c0695050003075003800c200d0910044800c1c240180303403604145019542c2d0040c0010020341644424a070400fa901c16815903004098140d00c600802ea242c1078090810340111000a03614030261000680d20941c0c0c400d810200d400f41e412800069017405801c65440314003602c1580c3e03094080018100207403a040c0d04100642c060706c4004481191441c1c0385081050720030240f18a1400d010081c1a209220004c4400385802428010f80d03525811000c2030540c056640b00a525010b490000414103410005041c10381903500020800d5030b456407084001d00b9000c1d207000e03000459240c0c441c1c849801e10407107803480e1f4524510040c055915a40042c0c4100400e0082c9030024803500c100e9400c140d04090403080b0040d8041c0301032189070411110304020012480303070045904842d9a00300600c0110340c4002d6001d0303005001142d40e0b1034400000782803809032040440b001d2180c500c034800d020101042d01c03c0e82400040804e032410008100f0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 137048003 1250 137046753 137046781
    0x102071b03081e0f0f0309010b0906030606041a030703060c2c040207081c020c010c1704030f0909021801140c07092423030f03070b10050603090109020901080a030503 73
    0x810f101d4103002c205056114404502510000e08202c1c0170a5591502c0007805080d500ca4200b810700840008041c04400d960100b66298480070030754001440c0440340007242c1c8684150512903416000e020703004001c0c081c00750001d41d581a5181c54820008102c10131160044540881403007815807941001d166500d4030350010b040d80c5000300582424550500000b101485081016407046540000c2d5509800800e0007034240d020035604104201a100201d545203d480080004040000c2d00442c419924010401e500c080c2401c0c080441d01d50b0317442c02c2000c0c11084100c41d0175000c2030780c58082c00409492042107401641000002c1c2006c82e1900783c0c402c000d0b1400701c4419880704c0c03200100103112000100c0f81401841c1d0f5038110941d81400c1071015030009084140a030180e00064903900b00280c0000131500c1c0350382e015156441558910421034000304243e00701d2a40508000181b0020701415049865030b68000c903039805c04d40e40d0f00c00c9100d950303200012006001c140b0500c00034030103100740c0c44 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 137049253 1250 137048003 137048047
    0xf07060f051e0c010501030303050601090308030f180a03030509060105101e020327150c0304151b080a0212160206070c1a190306050603060616080c0102071b0308 71
    0x188540c901040c030342c880540c0303030048003184205a641d00e00420a0540c540115034000c8005c0c04c0003280e55003151074030001c0e4800100b01c812480034030404101850510081c80201c03200354002c0d03482400161800601900c015a071010031407040c80000b02d52440c1c03416044401250369283e030002d00c0308a00440c031103806514820301c15130009020881c00484520550f00a1003d08100700d228941c07400c0c10048000c414034200685030341c0a11681880078000070444007510103104d22181c070387d240b841085880302d5010748401d40800240150804000d1150041c044400554003514419610850b41002d2405804640079420b000804018090305002c00202040c90007101d0802c00143c9860000c1c0183c1c5103158074003110080000d40e012900b040326a07202c111001440d09015070b40c03908000944034040a4a90340c4560300002705500074042c04000d40e15903592050120380c544943c604018001e41001c0b40954281d4030008148070f400c280c0e0fa01010a0703d40c440700070307420002c021180c0300450740441 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 137050359 1106 137049253 137049277
    0x90c032803120618050403020c10210f020c0a1e030806010e030102070b070201021815030a1518020405120604110402180916020f07060f05 61
    0x215440e040c1038161400c1009a02d8841c600001842150300c01c280c15455004002000d4016402051080c4e000c0c1c6c09444030342010100f40480058915105000603500300b03240d030751208200c00c28500c0c15102d801c000859002420362038040b6400603240045c0e40d80000216410460403550382c1c010440c0d100713110004c4254035a4040c117000000740280d414806840303440c85c00c43d00c2c01d505071345038107812011102c0356003040344002e0f000b9031000e44007000b00c10180020840a080070000d026401a00b80002440d66641408810050400d0103650045030004c0c032000661610300e00709100c1048031080016540e51401c01044130b40c4105215000854001208120200b0300080714807501d05415038015a4840304540c03500140e08886100030783c00344501c824031078204e1052940f90700e11003103a022146114503c04050b42c1e107017590721810000440c6400300f0003640b44904c0141c070b005558a = true := by decide +kernel

theorem cover : BRFrame.Cov 136870503 137050359 := by
  have h0 := BRFrame.cov_init 136870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 136870503 ≤ n) (h2 : n < 137050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
