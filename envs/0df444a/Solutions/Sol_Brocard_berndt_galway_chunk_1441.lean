-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1441
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:00:22.843393+00:00
-- url     : https://prove2.me/submissions/f7d6b9e8-e4e0-4f50-a929-d43fcd8b5463

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 258992805 ≤ n < 259172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 258994055 1250 258992805 258992809
    0x61917070203040e011214060c4f080d030207050c19120510092f060703080a0b0d05070303020106062d0c06110406180503031902030d0614 61
    0x1400240500c0210340c02404188503541c0081c0303c4504403000c0351003601c2284004d14020082c8545201d01c00b869020320010455100044c0b0300500e1084001462035010f03184038141d00e0342da4202410315054640d082501100c074007a01e41d800c1c10a00078102040c19490340d0741c403800c61400440c0b0520740006a00403400e4420000c0400c2441103140c004c440c0d442d2580b903107030418250908548a40750201e103034a0005c40c1440f1040c0425103000c403200d10140700310000d50801a030019030b506003000440c0c540290444001440b19100f0390f40000c010001850100c0f192000c580344803000d4161030000756905000345541e500c11406542640c807a401601c031880c59818041e0031600c203503208109004c102e0b200a441c141131314000065400365101c4c50040c81824001c00c852034030407140c0082480f450040c03140c4482c141d08010304201c07a401d941e811004c000880a0f81d5401c004c1c0d202e07164056000b4014420034007040f41c4800900d8000748100c80c204800b55500b441a51902d5000d20400914101422518 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 258995305 1250 258994055 258994097
    0x90a0203011a090c03040521070c0609140a05010905120f01050709030c080705030715031803030f0f02192003072405040c03020603060303070f1209170a110619 70
    0x2503131100d0250943c6415180d40342c82d081d00329071340b01103e080e2004045119420900b80d52003160013200f5032501a45840380640341c11824016140306405040040400d1b00d8596112016580181c0d1a041d055240106201c0021038962464541c3e01450181c031180010900c06c0e181309007100d5581840562440c1405810001035401080060b000f250050001d5100010110115500103e00701d407070703032200c400407002400104502d0502420f00400d54050650680200d40c002c075019004210041808800070224411402c407444240c50044864079118003c40d41841c0d882c08103242c545a154000c415641188d10040088403505241003890844002d032203045405400d002c002000306041030303104d18501044c80d11009114017000400518a43c07001d0040c1c0b901e16074020714805c0c0d90b04a03440c0403100030040842404c0000c21001002440d01c4800d1030300384540d184600a4072000240da2a00421390300c10048040d000b850070031864060300c201810600b00744040c0d5070380b4040c107440e00c54188d604c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 258996555 1250 258995305 258995311
    0x115450e0d11070e041b0305010f0b030c0103090507031e0b160807030b0916090f03060e010c08010f1a27030114010506121003080c030310050402120c03090a0203011a09 74
    0x3180c0c4002c0c0f0511020a0302c1008580140d04140d1014011403150000040035a00b900014100e50a10000002c0d8480d6600700044012003207080d180c00c000340000450440350f5142029200d540920010404214207400a49841a081e1008103001039603031180d84140200f680c1c403d050400c003e801700480390744a01d0890f00543d281c07a00303016410030b00b0002000b40074040d1003020311110042c90400c0d1345011312030361f00050004c80d1a56403a81e550f802d18100402c6904140c0d01507500b03141c40b645400d84144109410790b881600002c100d01c0c10712154440619184c0790a4128204c02c0085010f014000c4001035103040210180751901a048024142503644001d0549603503d141001031004d41e4601d0140c50015880300030010b415030300c6101c1c3c400860100d6201400c501030000d1003c02c887e0b03021000314480c5110001c030103001681d44007400102d114a152032414258014042000350700c034100196041030011040358152002074000038212503411040d1201030811000e50500789c20304240c002d40c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 258997805 1250 258996555 258996587
    0xc0606050d021003051504110d0501080f06040807060b061812060f0604270f0c0b0c0a06020a0225060e01020a0203280b090115450e0d 59
    0x1281c03607481e404211041e03100c01c250014191241c0c00a07414602516000400d81d9005200748985026090701c0c1425601882c40c3c1c07520f0f1402c2c54000310b41110001510112165000000c1049565580750b803026500305801c1258240d445072512030300b503503030207028015006801d100349200661780d1040003900c41d18200c0d0302c81240c01140402000540001645502103400d83e0302141c1e401c011201c250b08032204154007000c40640c0c2000038144000d0320100120b55110301c6030503030415121115000180120b18042c0507960210b100500010980c1d006005068507900440f20700c0d0f80c05c0b255240014904031841d0000741e41801c0e080140e00d0740200b1188005000703001a04180b5080c1d0082070712203440c916826401c140307011003401c1c0481c006525080b0503811001c00010b604200060074003802c800d9616000442420343c5c0410780f441000d1a880300703105039080350040c5c450303c43d104865142c03030300100c014150854400038840b113480703000d005007181140002c0c20301c07100d01040240040307e0040c0588 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 258999055 1250 258997805 258997819
    0x41a07021e1c03140a11130b130501080f0a090309051201090c0b040f0905060a05030a0c05010f05190e01110106030305120106090506070602160f050d02060601031b030506031204060c060605 83
    0x4200b10138151005a080b44d002207000c02c4c000100b02c40414603106050159202d00c104d500300007410b004580c083c00300110409218110346695000440b401a41656007096240c90707407004c181b4a01c90780d400105e180d4030034140304103d99542c4000403118000350b00803110a9448000345403c01c4180c1c07403080040c1c0044540e290400b810300c0a14400d00040b4001c00750b0300340d5160045086590780ca08000300410b0014100e501c000d0182c80c06e40b034512483c2c40f4480c00b02d0404610004114015800c2e2480c00044014a01300018070400c103c0303400350748038a000e060040c603203813401c000d010a0007000084c500070780315580d0307403070141c0e91418404c08141c0c000405c00c40780c7c500c02d00050799840200d4110b103030440400f40c0c40300c01840c1e9032000002c80072030007411500314800083c01c10202281b9441100143d800352001035075424015410ba0b140c030100003ca050303000b0341c80d0410501992149400610103412241018010b44240d29140c0c03080d00320801081e10400742c0300800206006480103050156412 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 259000305 1250 258999055 258999071
    0x92102100507021318061d010207030504180603020105030a0f0603080c01090506060910050d150203011401030e0606101d0405090616030c0507080703051207080108010e06041a07021e1c03 82
    0x4840141756002c0f00400036521800394072142e0743c0e4907650754604044c5c00000c641e105480d1034050026441703031084288a007101620b419141029100301c2c0210707a01a19250310f180c1d1243d54100050400000002c1c0b0f65545010100100d084003020b043c0c9a14410000910415140cd00c18079100b001410540f01e82c2200d000c120320701c9206091241121400d403680f9403d0725030b9113802403030726000d003080340080f504c00300c0006940201c0e074050a1081000781c90800604421124a5031100c20443da1a038003c1300944509580f1440784d02010b4130001040d106007000603010340000c058a6040d03c035801c20b1b0b8811014401c82e01d05401c0c80c003a018484d4141000003d00c601d801400b140103c0070040c15401010501c18107045c01502204e201080d0301170a816546000030001d88586028021030241d90300e024280ea040010000d1584e00450b0401c140d401c065415071841c0c240104010072400031401900b00031602da0500a452203c001e890340050001440c0000d0040c0520040c05000402c01d800e007150 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 259001555 1250 259000305 259000331
    0x6032d0f121b1507030605041b0c021516080703030c050c0604080d020c030d0e06010b12180307020319050d08041a070e0d11120705010921021005070213 67
    0x1200e40c940c03040d046851684142401c2181482d1410f4a420b0205800000308a80e09915901a000390f40040700d0401c17a1078001c01036850101e05400e41d01022541e85403203040541b914520381d135440040f40b031b8010b1410001101e01c5201c3c41c84031000325001030010a4003010950580a04403281308517140042c28007850340c040a5603400045c001810401000400401c044243c0d0102c17503012070400e040360703a144580d80c0004020410041854001d01070346e070010550441082c100c0b484884480b90b89034041e1101c511010300c83e030300140c2c01c216500c030070000701c40103031414458072800000400040c40040c6281c2403143c2001d07103000090040280c13030400c000026103400c103c28005400f80503825500d54886400751600c1c100105a980e004141603001400c1000c80c00f025001d0300015101d000d41c500300885180c0d0b030b9540394090b03a8041604500e041c002e01d41040300c031030596100708a800302214400c1c0c0204002080c1603c5000000b41d0024200080d406c1c0751503005200920124104108105502 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 259002805 1250 259001555 259001557
    0x120408070e040512070c0e0414070501020106050607030302130504480c03020f06010f08070503010212040209040c18020307030b090114190305010f0b1f08040b06032d0f12 75
    0x441400903080100e07154060100d20303810140901282404c0d40300d507083c40c1c14013140d00c00b51130100e09d40d18852244045100c1d4810b001d00c1c000ca51020700070300d09008042d030f8290302a40083c0c02e02d400415508600003122b41d6280503021029405800b201c00000c0860381c2100942c0582401114488114882c81d232121000c00400b03144000721b2508015400003490224100120807003803030f0a0340304e180000314907038046803508000c45414008949146940700240740c2070b4042c190728407841051200001d800b601308051543c2c0c0c030038428004000caa0f45c030360811100464010041c1181142d000c0200881c4940520980c0d41c3c07030400301c6100c440703580b41000d20500e403410041060301804100701d81c030342c20f4140d8424000286900c8002405030004100f07481004103080c01c6480d03c150900342c0a003201040d40c901c2d00c02084c1881da1000082d649588a5110084010308000d4140c0301d10300303007011814002e44002c0384800c0342403050307070341509003031041480d041954102c4a0700d038124688100903040000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 259004055 1250 259002805 259002823
    0x190c1b0e010306020d091202030903010b0a03081902071701090b0f1512030f0409091a1501080c0702040f0f050c0405010c1203092415060c2003120408070e0405 70
    0x9005a0340715175403142c00c40038201c11040108031803003540001e680941c011003c0c2101d00c206800030448010200100b10450b0460f00c0302400803d4100005914248841e004000582290044034200f9a40751600c04481001c802c4210090355039655020400449209042d00a113800780e03e03001a081c00050180214151b640b014442c01d00b1642d07080b252034042c4180c80c880c41c010036010b40c80c2e907544c1c030744040030b042003500440c0c0c55210060340039040e403a5400e01c24060400e143c64815500414001035441810290100f071170240113102510059985000e40f01094003400000704060310107240c0c0400362100500404031405052000380f009984c080c0d070500301c04d904102c1407000d000d00c1c0c180640013000400e0001d04200d50320b01c1c5003000c007035542051075007146001d041003045840e10b4010a5202200e4061813000031101c403440404a083c8010348104074a60540003140c0034240000a803030080d8691080c20b00c1840458100407186041c40341c00001c0c0040d004051f024501561695210f021038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 259005305 1250 259004055 259004063
    0x60303140306031b0f0618030601090509030d050907030f08091e060d090606080a030f0f0206070f08090f06090a020a0f0b040509100503030f070209071701090908190c1b0e0103 77
    0x120900c0c0c01030b6919480410908030020388640d82d5025480042c020b0087d00c014a14028880c0d5000040d8600d40c500c01d840c410004070000d1400c01031300c0020320002c1d00001e415004548101e00700440440c203120b0908003203a00c42d540c055030314212030041c07180640c40d0040c1c40151400107144010207840350401c60700403076010000000c81135107600e0070380b006001c1900203004ea8824004401d0030150030000c6000344201544610505852170102280c0d00c5400721020400078070070940300013815000c0c00d46190003400c1038083d14200745084004624083c0c0868140d245a80300618500540c14010822006404030b2500d045a5a0400c8040400c1d48100d20409004a02c00400600003030b03400e24030f140103080001d040d25a10f5440040020341a04195000d9209410160100310940e00603220034280034a00810014160b180c120304070005c00007414113950224041000310b01c8021904d40e001c9006000d070700c0b00c078a11051410f10000321400c030405481203181103070301030061510303128189045a41c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 259006555 1250 259005305 259005343
    0xe0a08030316030e0a0303091502070809040921020d0e042715140601080606031311010507020405100602010c0203030108070312090b070c08061302130207140d020106030314030603 79
    0x391a012001400725448440117030143c2c600810400d9410781100e51181c1c091107038080c400b503160340d01008030301c40c04000414044c810071042e641ca0034140c010800860043c1c48440c5621640c900304407080320340504550040e0070245000e00419002a4601483c180644040284044206016404440c0e070f81005000a00ea0741c04078041104c030103a4110030740008a0309011218210158407400c0d9400c2e1011707801b141c1800300140d194100341c01600d00c035510440210280c060191206a52807800b004c02904001c0c2c10060a0090b807150b0041034026131204003c0d2050345d00e4800000e007141d101d8444078045400c10001013243d40343c0011540203513600300440301611036401d00152040300c0c481e404407440783c001040174014000b100424808543c489002e848c0c8513a00d405640c0300178442840d0096001d805490b10888440c800d501811f50309204030302d20744450204610381841c2c02d800d0b80398200180e44801d01030041640c403070011011305101190550441c200600026101ca01d20710004002d410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 259007805 1250 259006555 259006591
    0x6050f1b030c0d0e0f0d030c020103090c050a0f030204050a020c1509070f0e06190815090f032b0b0d080307090509070203040608090c011b05150a05070e0a080303 71
    0xa09000b112200c041c0402140d001c401030b01000b40410043d0030556108051150000da0380d418000704040140782d060340c075040a500c1c1507005500801c2a9002074600407001c941c0800d0784e4645144c07080c0a0085280d0131070300b551a503c100400d4170002400101628011b010010781c4e0303000010907008005801005040568a480388035103020941da00c0441c001205080008000a4003200d0034040d21041e01c0884100d20422001481c0c90b070309226600c0c01d03601c49642d0805607208099025003101090090f51110040040071030f14507048a8042c4000c102d00341000740d4680707207149a00a0014440c001400b100007010001403c482d001900545814000000100c0b100d01c02c0b26030300003816000380203031154241950b0007592500310740504008503005001058410800140200c800070301607442d02079800b03150945428410725404201c40510130060150217540512002c00d104101b4941c00146d50310f415031005200003034854950b4080e045690040c403844070048200c1c0c0d48491071030b941d071000e80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 259009055 1250 259007805 259007857
    0x915060703210216030e031515010c020d061d0111090103051801090803090f03030c0d090c12060b0405130533040b460902060d06030c06050f 62
    0x121001c09030b0010610021303e042c0c894451100300310342c1d18080d0703480d04d6141d1080d1060640e0f680c03a4208400020049100007640108020b540c0800c0003810715040310034405503070110300130446854040b02d81a8680502409203034407801300c03640d5105030800a100d59002c04071500c09510611142604254a44001480b28081ca1400d45000c600d6800204400c5a580c10f00d1902d0740c0060300e1030b0a49019480080c44003000002c00e9a0144107240d03032003458610b420907071100414200070100c52013000105c0010f40c203a03255586e0740380e8034080e4401081c4803010368208402c0310001440c0680c4418580d0100021801c000750414a600340517005600581200c6201c0c1c4421b00113403500c2880301d01038020001000441100d00740154a5401890790648040891003244c81c500000c0701d8001c008110140c5490012041c00f8040c10702d511800155000d6030303004150f0550220000840150300d40d41c0030010000c0004442c0020320b024600542410341013040100140320b0000000d41a041c4c018461100d9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 259010305 1250 259009055 259009097
    0x304020a1d090111090315070c1209050406050a0303020c01080c040f03080d050105010f080708040c0f0b0a0e03010c050405130f0518010513080a030c0e130b0915060703 74
    0x141c225a44200c0400401d1500100080000c0b11500d4595080650090454256500f56111030100a014010314003c110380d81451820080120741008503e441060226000c000002d41510340303951034180c207905200501081e252140d20150003004510010000f00754085030108003100d0903e0000d00f1512040c0c070083e018050380c2c00031985800440c07000010007d0320b600a081407001c44100344103981c0e0350001941c40e01c00103910710000c591280001000540f0030440d003a40144248260209240c0750502040810304640100d494040005145130003150400c4a101c7c064800b00e0003032001e9109918003c003180580d00c00c403401062400b0481c4080000354009214402d03100c0003c020f13514001000403001f046116100300c082d440d240102c0c171084401c206003488545c00c075150519200358994200c00a140101010b070030051741c0d80c0f0f0081641d440007480d00c00309007440380200e04010789008100030540090210260405042d000000c55101c1c0384c00d0381c0f8110340609010419000e800024522 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 259011555 1250 259010305 259010309
    0x9010c02100504090f020708041a070606030b09101b110109021305190b030a11010201090c030308100501021b102604150b18060a05030a140613170304020a 68
    0xc04001007515003a01039100010b48100c4005800074071005032005821000c0f84a10701d07000e40540003c00c0244600c3c1c002e030003141c4c13066240c0d11740030749840f0301620740400b03c03403042d00112800084901801944031003000080240340700044108880a00d00c1c514843d81007624007860240071041c2454400d000382944440a0310b81c0181c40d98281d100700107807803402007200f298150b12607035444c0226441c864a82c030070500c0104c0040d000b040c50390216120b21400b00e0424029030704540d01c8041000029441c110080010751180c0c0381c400560420030404102450940c015a045610896a0454507031008407009103205090307488000960b28440c00300c600c801e4010b4601d450408036540301d40e05000b046416440345020314858490310116040c2801504c0c0f41050803a400107440d032441a003091a0103509802010080c43c80e011140d0f10004241031440e030b294144d8106220348640402d100b01440079550140740301c00d071802c40340f0140c0c1e035000300072031051801080a180800014110b446400d04000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 259012805 1250 259011555 259011559
    0x307060f0306081209040c08010e0604050a0204080a03030b120c01021e0c033a08162709060602060705040b0c01021c15050f0a06030209040209090f250e0609010c02 72
    0x81d580d210b006085103a6030205d20824060703444c000d2240c10003480340c65654141e40610003547c10940741c44040001401c4040c051000069080100094071030040080c1320f01c852080e203011641500040802c40c82c03200140c5a90300c42d07005565071020701ea0703012138200d031000039450b111300500001d6502c4d149000c101c056115014442c1d4204013980b10028803460281002d45c206083c040d01c0c450f2000300e1042e03d401c003204007184040011411518489880704520074141c507003580190035940c246098001980601a00104620003d00440019028010203048039000070021818000801442c42c03003284038411001c6c1c0302107542c5042c10002c2d01201c2c078041c48a081c1e09620442c09041c0c500a108140980c01d0442d1311000004403402d0580150800281c0201000d08180c0f9200040d0080d51000d241c45a00c682d00b000300980300d030744226903140a044507000e0403a41c1d14255151040041c401d1440040700c042940c07280c00c070540e2040076802180816580c16440f5500c15005036401c0a00100081d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 259014055 1250 259012805 259012813
    0xc09030a0b101d0a110414060d0e0106060c0510141f0506030408251203020c0c061b060c030411040c050d050406020a0f170c090607140a14010b0307060f030608 70
    0x4400300021911180039402500d010010303813441d111700000a05ca1441000c4000c203c015103103c40e854840040d0100350141040403030103000c001d04090845030550041004103420f401d400c02441400c0201c86c401c2d05010400b04029100341c0c00038002d0480003001e0440003c440d80c5190a003804c24440a002428058442a100e00b402e24102c9150b8001184050644c2c210307071010300d1400580c09010070b2094000c44c00303000080c0c1002044010798807422009180f8450801012559200d1034000e01d80c0300ca909000e0b5030107a00d0240114289180507040c0801035100380148000b00f4560700c40d002000500700c60004203100781071405d44040c007d020302c03503692919000802080c04440e4004015003200e03940c0380c5100003c410f100795900e501940d0f80110035440c00c8000b43c040c0700040b00810520a00804031410400181d840c010091031320081d201c081d07001030301003100300001103501e0300c540161a0002d100721035100010a0342d49159100389410001c66841c070707032001c500aa10003006028644151 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 259015305 1250 259014055 259014089
    0x909060f0405100515040b091b0a050f04080c0108060a1d0411210f030a0815030705120c100512310c03150509031c140411090c09030a0b10 61
    0x507640382a54000d1480c010342c03c08405519900d0030100841c420401d9141c90741046140c1d049270070b02c5d504100015418450308011029240403980c0c0900010302500c40140304221250000500050018083e207000d0590310f03d05024079456000d03800d1090300a41031b0b8810603540c50402030242e143c180c180681050b442d00c400320312682e03030708075032906071790440129118001d030300810340ea40703100308483c00d17000032b90303510110b080300f0f07403414040d500a90005d044458081e210030006000d400c81c4200042e285d806400200317580d00342088590010300150030f080e13091014044e50300105c0d0308020440001c000302e0b91030400c9040030303401150b45043d4445c50f01403030842e1180382c000c140b01c000b400f042c0c45d40f01c0024008480704243d0b0298a1160441c48091400c28451640c80350310384140300d04100b04507854010015400c4403945080348218020304118071014400d01c28080302400151401004503020800700341e060700c00003681c4c903482da07116414006983e104902000036040b60381016201521504c0a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 259016555 1250 259015305 259015321
    0x403080c12210105030309030316060608120703020d02070b0a030e15090a030801050906100c0c0302031b0f190b0a03090218010608070c0f0b0613110d0b0909060f04051005 75
    0x1584006540502101c2c441c1d80314070400d55603000d802103080c0e0603072042000d00f4050002e00c401100213031090700042205512400d0407400c02a80c6120080351076800320b8000f092650400c6112072105540c00541152410502404d038a845035509001c2455281e1480c810380b29070400c09a0a4a542111207191a0522405183d12200404003c0d000114504004645880d0050446004c1c00005001a03a204010078003034411038120001992031011401e00000503031004d00141c0504100c0c2000c01c1d0707a0780803800802c0303290043c170705044c2e0040032540008418074a003081c07003030183c481504001d0b880341540d00d0700303c1c0600308411000b50003240c0441d00c140a6000c41d601d0906a40864480100d00c0c0d0b40d000080311460100c04028060175500041007020400034005e0640100016010041c0010182880740982e0140c8400e406c1c07002d0001004c0c100c0d208035124012a03d2401c0b510903101e428454410340e61813401600104a601e600341c0403404103d020030105910510814044c81549402d4403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 259017805 1250 259016555 259016587
    0x10b03074116060507020304030602121803071205090a0807080a061d0c09040206070209070801030212070305030d051302150702090105060901120506040f1806060608010b0403080c12 80
    0x114510101030441c0e42801c400240390706580e01004420002081580c036034449a0203800040c040304154002044048042401d50000745100b016510760b842c2030741481300c04c0b000385c0b005800e401c11540e0414030500c80082d20000c04c5204c0ca21003881d0040e103440791071000510000b020360092040d80304c4c2c07040000d040031001c500300d10003600440301081600c0009030310f282028000380d13400d540740d00308201d0050140b604900154003c0c1c000b41c1860b05280165001c00d42003201940e0070b1003c01c00580040046150a100324004010150b024140c46846c50303568035070702d0142c80c4103070303203000d8582001030b034072043c1088641180f0780c004240d6000c41c24000700d40580d50b801032500381d01031085007001051504140045130303410001a5035004444294000c0380740105406003005038410f48418410880051901480f0504031003109100484691490720300c0440d0448d90102017400074180041107101880c400b03071001c680e008161141d841d95151260350510100c860100e1760240b02180410180340c03080c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 259019055 1250 259017805 259017887
    0x16230703110c0319080304030210060305030310080c0105070b091606050a09080106230a17030a0e18130611040f0302040c2c0d05010207030e10030501030b010b0307 72
    0x1402d40d00402c10050074181c0303c0058001c43e814040050495200141890f0019640720f806403050313a80d0741160398903600a845c0141d10a0f20700e503001105101200301814001c03c000e0444000420306056035800103041401510406450000c5074800189040000e1000c036003090503c05620740443d845040140254101c15060000101801c0000c98010014455074080d90140c1c0180002000300c2e00f0000c040710342e800c1046800c10a04540011100c0800c800034071100382c04d03406035803a0300c10901b0080154a61460b40792052400107000020041500560798020b1716962210003201c0c3e07141020350180c4500301c51602c450000003400243ea02400581c0c4e016207100b1541030214070050481210540c140e2508107400010038015142050b5000c40c01c462002d02c09000e03990041050f171101c500720b8020000a40c0030480c8941641e1444c54000d807480140203940c1010040c950450f110310315402e0050240042c48800000130403107180c040d41e46141c950080070348070158003a62a41c5000780c440d200d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 259020305 1250 259019055 259019087
    0x20c0a030801170616020f010c0f030c0306030206030402040e1504060c09080f0706050a1101050901090605010e070f050f070f0f0203010c02030c0a02061b16030b06060316230703 78
    0x1c040041001c1180341c076100c04030340400c0c00508168a400076144640c4e8400c0000c80305501c100c60150442400c28052162070301d4042e19916510f600000000e010740c2c840c200380c0c0b0109460103d0900060351400c040d40d40003074065074001036160114107428508400c00c2240503000400400b0402000416000100884070300d0340c4201ca4155559000741e9a07140c0401010500d4004400c00e11a040c41500035201c1030103c5e103050030b1818441d40d0307501c0c02c450301a1541062651a0b141110902000e80a0240102030142c000031b96840c0c0701000511200c0c40ca48a4402c0210009540207070289000a854a42d50410940360321000c00b40f821010107410310400701c0c0294248981081e5003400441512890140600074054040196080216507840b11403150082010740c500710f698214100107024480720031240f4031441760b085041419010310014825442650108200451200084c0c140c01784076600c0d05041e02e0241554007610311482856a25130914840402c3c42024164451701c1c65a1030445 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 259021555 1250 259020305 259020317
    0x130507020a0f0c06021b0d02040911040608010b030618030301030b0a0209100e012019020406080303010e07031a0f0d0f0b07020a14071a0d020f070f0b0a050114060705010609020c0a03 80
    0x814420404041b0b100104150b011008940400250400d0317040724050794426a0420f003400c0b01000017400b1140b20382c000c040e00c0c5c0c0d9144640c0030710741402c10029400054200d0600228030390703081320a036288414000200346801500200314a141581c040e200819070041510900c4443d000c0020008810118004c0c00075046201c1240f120b11104d092000001c40c410180494000c20b18141c03c401002d0b020890304165202000648000f0074009276010340a0103810194604021600400750fa41c10741c0100c078181104981c442071076035030440380d08030340c08241c500018086650402e1a40100b40c0007001d881e007105e16013088103565000c0744000034207110ba0082d040c440c00f13a923403c6507034290500405404052100042c189140030b000a01110002114013610b00301c000e0340d4800950300501c60031140700349012500e40c20003042d011015800140020708200c036600d0441d400b80c11480080009015031000241401444400c0d0429806000650003c0d950342e1441c04d40141d8a4501c5030042e400112 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 259022805 1250 259021555 259021573
    0x1103090a1220060d0b01110613121d0d0201110d031e020301051003090525061106270c0a030c05030f0d0e040f0b09070f030c020c130507020a0f0c0602 66
    0x8001c01c000c00b0109400f80c083c03030800340e121300120010041c1100c5181409030032a0544c890180800903188144040b02c0e80c02543c1c402482c1079422440c0c4d034005601031042c580c4a1608130750180310380030560041150040040c0405000507904283e40341011409402984c1d0320700e50540e003640040f60340c5c0071804900d201b40784003e240d000403400300703004695008000d0418041c2c081c0c86030700440800c50051040d5100d8050190703115100481d5045401c000009044080100d140c09c040c2803a030341007580000c3e04181c5000c00b00001d40704500f14032503146c0c02401c0b01c54044c0c1e00e01005107500340c400250800e0045030f1a41040780515078244140d621078890543c2d46081204046100031080132143c41b05225030200c801088007030401c4c018000340c0c047c3d907200c0c2c0e803240d940c6008500e4002d20310f0791900c105140926800409841d0300d0720000d001d660251700d0003e00c50320b440d110440003440101c2c0024983d124020101d0800101240190030740c9003082502d030501c10700da6959000c03034a4503001c42d80c40c22 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 259024055 1250 259022805 259022843
    0x60f0f0603030a02060604050a140405070501030510080c1504080d09090b0103090344061201060b0901050d0f06030804080606030105011d1003020303031527071103090a12 75
    0x111035465a44010317041072000c9005810b10390081c54010f00d5103a030201d100e803040080714900f5a0112415a45079200360810002940c061003000d0700030205148910510b4184000f040c0d443d0210f4240d24000c0c0318074110f41e80c07807002c200151800307080c04a0070342e10b4800100310010b003294200d0040f012000d1420300c66440e158040e2141048007036040e10f49149284414005d407005464921350649141c1080a40d403844901c1d004201c2c0d100c030440903102d0014200030381444500501464401c0300c50b89440e40078060220300c0380a40301424000d28060f0f60720100078040101402c0b04110440b4a9400c000d000300401c5500c40c050010f540540044450030350712841010300740ca00a103c3c03401c00400001043c4896018210240c1c1d0000c0304148940c025566036001c00e00c0c581c41200c103181c9003000302c4503a40c0c043c0382003145180b05520004c0000f41c0c0000c0703500140f5050601503c40d07801d000c2c0b800c281000301c500034025079190002c001c1400313000039510b0203c880001c5030804210ba0180d04171507104200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 259025305 1250 259024055 259024057
    0x9030111180a0b0c150703060305060708010618060207050f03010b0a0321090b0a050a05070209040605160503310c06050a1704170d0902060309030a0905030f0316080c060f0f060303 79
    0x507900260040c584917004c141d1060341c682e406040001016200c1f030001c0b001c943d04110013809041184d80c0c2140541c035203000240781d416091905c3d80d4040c48007504205c032660001d0306905481007150900110320210000074010048400541c1e00194501000002d2001c045200c140c0340b40b81d100d8001100d511190210759a00c014000e1540506c0b09100c0c10070443c1c861005000300c00708500b402072500096400207240344d90219011142280c64408000c50200300c1c0700000e00109280c1050340c214146001103121014030550b111460360815401603515043c0e4001040145030085020381015881d9040105290301501c0c0c514041074030702150034040302152074428450342d0004818001001d10a18500b0300758880307601c1d0038902e40c549821002587d41c0c8070046001d0070f1700c1802035035a5000340c040641610b88903440548030390010750741909220004012030315200d041551950a45c80c0034580300341d1900486080720310324803031501000408102c21804602681070407624002036500c0604159417 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 259026555 1250 259025305 259025317
    0xf090e2d1e0406090b180c0114040317040f0b07020307060e211c02030c061303120209040f1406010206010b0310030b13060c0c060b0405040f020609030111180a0b 71
    0x100e04003a00800c40d40107260460380003441150003058004240d221039005201c01d075000860f5503034000940175445420441c40d60342803420b00f0400c01c104c0c1440c0b94108540207900c406018822489113006811040c4400c85002d072001c11a000c80154440c60410840d420010b4124020b00c50480040740c020300640c000c4130720783c500400f5101c02410110b150221003507000704180840c480d01010030b011281107111a500842d195000f940c85070104000140303462400f902c0c00144d11200010f87c80803940c000c20362040080d40200159465008a001c41e00410943c44a03140051a1880070b8488210401c2c5690046209900302c3c0c0160762110910900c600c801d950021042e0b0003120200b00007200074102980c0030f603241d44e095a80022503141d10302912601041d00c400070b07804101d4031041280600c612101c0b03030b00c11b031802c000c2c1703140541d0340c01000503890305c02a1040e040030400003000d550940003003a2405100d0b11441e140e00403d0400701c103910b004091b582c401e6840b8100031654920b100709541c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 259027805 1250 259026555 259026571
    0x906011d060f100e09130516060203030c0715050420101d01030605030d0804050f0307020607110616050c040b04110d0e03070b040309091b0f0f090e2d 66
    0x2001020500420101034000b800c103800340114600d81c4802c0340d6801c85d4151090704541401a4981414902241405801c11503645a4190900c00388080c550000a0b43d5001980c80700d0b043d5501a2420000d100c5041c035108141a1410701c401c100c200702c502d04032440c1c85c19001402d80c0c4c040d0440020403060303100e048403620000321203880303540080008035040301e161141810001829912503000c08d081c2a0944180004038642505100402c0030030000400b810122202131810074081e6030018200b84034410018104a032f0350b903501a03c41d03545200302c070380355540084480310740003481c6030258480d05182091032242d1301d04621200c030340c101800307401214050140b104c0d10b80200715680d000103040c00d00d00d080540c8030a200c0180001d02d01020349008070b01a440e0344000911b010109419902036041030910a4203ca510001030303a040301c1140050600d0b41800740c19141030240856030b00300164030512400f00c1c3e0000340a40707400071f80030059141550b001c90001c1300640c00c0002c40c142006840400c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 259029055 1250 259027805 259027819
    0x250308040204050c0702120d18060801090f0e0105090a0318050a0504020c0f0f0109120905130b151b011107020907080a0906020307080f010e09151e0906011d06 70
    0x10014070705640203543c04501c10051900308850b1b40c010913201d842415108400342d100d02d035803501c03080e007080c0a980c81c9155181c00d200d069080420040c4100b1040c4111044141c84401010078054140c0110400f156040c008200d2031070a14009036840500354801d4003c1035643d0905144082d041d0004001d8440180026400c186001d0038040294448038542015014845041e0603d501c02d01c0741d0b8424030540c90012502c0405403c01d1056030281004480500c041a9020019900c81c1a1118203120391a400050200c1e003031030105042140c06420f4900b541c40009139400181c1c0300c080b1391040d03030142200030402c1e0305880d00030340440d11070b03080041d6028141e040080c00d40d0f4460720a0f254031400c00000401c195815070b94600583c0c1064401c1800303d10300404010b000030b80d42c241c8500400e0221a1846d00e814400e03181d0f610b0700030320f120130404000c00320300040d919100c60000295400a401720002540b40961189403548800c2c012a0901e80071204544881c0c500e85e0203c81c040c680c0209a6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 259030305 1250 259029055 259029061
    0xa0b070c030915091418100905061804060c020705031204060e060408070b1c02030109050a18201c08040e010807050f012a140c01030203090703030c0c030b070302250308 74
    0x3c00c1704015542d003640d8820a0b0005003400144880850783c014810b1f2088540c0c024180000c0c1c00c162403000307040318000c460f8600d40c02341c07a00c448070a150300aa00004005030f0080780c10012403c118447e0011a00340c13080d0440055035144150081044a0250759180841c840f10001c0001d80d108038441c00a96911684060201d140d600004022004101100c14400c44050007100245e030004d0380803e01040c1da850400501708c04501400c10301903868240342c040000c40d559203611041c14600002c3c9044030302c0585c0c240380c0c0c032000c5101c0c0e002c41003204118201a03503403402440940c02800b800010f40e0900f0000680310074001840270694400030b04c510b0000410500450300c1602442145c00140711075544003551a0040c02c500d412980220b0b180125543c1e65280c4c64078000040649904241c4108200081c040c0d0101e80c034400c0c0c0303031b01d80707040f60324007581d030904d00f010719229040600240c030701106108060303415600420300313102d11010100c54070420050030240005410005008a6191000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 259031555 1250 259030305 259030319
    0x9041401030f0b0709120302010209182502010f09050601090b0a0612020d020702040f0c2303190905030409141e0708040c1802070c0e060612090a0b070c03091509 71
    0xf4555101099180000980340d0362506043c0030180410150050703580010b181c00c0c14145808022a0380b180713081c0100240c00d1030f0a0300078050300c0096101c96040313000c080c2403982c24400c0d000b488a035501e00b0340501108126050480e2034801c01e00c00c10060a2400d80e04c5401420840c0307802040700d9a030303101c0c0c01090450111440295220700303540907191b0790030010503005036a03078896605480c0401400244d031031850f0314090429062081649036440c1c0d00300103003641e07901c03120849500001044103145181c613621260310150242c4007000703002e400045408201500d280d400728454440d03030041c0028588501003040d41e16546610003220940d1075200241c0c01a02581d0b0b080d0f0468864400000b6483d5101c0130000c00d64694014681d1450300024214240400d04803010040d00e41d003100c80f00c0f41d050981c0051514401c00c1254298281b4110002d02151000d0281000c2079030007070b0310f00710f91b490b013400300400030001c8480440c0410814a0080303034541d408040d140c480e440c55200c440f03074076041c40741e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 259032805 1250 259031555 259031573
    0x1a030a0507180602060702010b0f150d06090513050c0d02090601032a1106150a15050702030d08040b10080706051b030a050910020111040e250509041401030f 69
    0x1101c40103000c03040e1908840c0b040c8540e01c2e4401004140d0143c130301ca007031a040c020f0940c0c840c0704249114180c024112034083ea602005091640220900307035541c0c0e401842284050240c43d407001c0c1e0518500b41c20000d4010f451900012140e200b00c00b91207503000e01d0303002c104e844281a04041d41140312000040c81d1940a03904c00042a85400880b0b8005540042c2c2c1031041400d60406000103808044110302ca00820407425402404900d01912101d1183d004078000032a0b0b84510880c8079a640d01c41d80c12180108110f07500f064002e01514a1500400760107058980140c40c11215a160000012000c465a00c0b1603400d030b8000d2005005810324108089030036030017560341405581a542d841c81181c040c10001440340b03100a4407010f86411941c4100403407410b600341008196410034041c40c0c8094041e9003114150380310007100c1e00079a261565070002642c244c0003508542200594000606504032000d0300c000c110407107040c0800202c9001d20030303c6c01007c1c07000400914000c1d0882e030000d060a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 259034055 1250 259032805 259032811
    0xb04021309121112040806041205071b05090601051204060203180a1b0e01060203040504020d061226120c03041e08040509010b1207031109030a08040503071a030a05 72
    0x1041078100c6031110503410031071486010104059840060a205042c001d9032541007516080504183c079040e8000d48034900104000d0200c1c40800356a40858010800e82d04e616811503a5030394001071488900c09003180c0740c0140c44c401c1e8100b0f00000c141c0d61042c2c0880c3c100ca4044e101142c101e0710340d070f41d41e140603410141201449041c20350042c0407025042026148850046005480a25a07a2000c039102180c0c0e41241c40d082c00c50500600c181030b0000700f2502203071015180169569030b1038030349900034035041d0085252111000001001d024182030321041110149100c0b180b144540c41c540f000d24811960341044009541c00010060004000075591080c041d081d04084845131880603040c4004000f41120590400718060200341800e50740140074064006540749011b01ca000c900382c1c1058018180010507484140c030415140c0000140c170550080036003100c215442c1ca05d026003071900207004040c000d120f030a00010760000720000755140700300100340c1c9501d5a10b4000081d07014010003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 259035305 1250 259034055 259034089
    0x80a0806030c1e100f05180d0b010806090f0106050a06140c06070801060e010f0c080702010216091a06090f120c1807020c0a030302030a230705070305190b0402 70
    0x40600d00090743c0319080364100c2c0000841142c4510030702d8404020110002086003400c019103940351004003500981190700c1804581001200d4a075004009684816401300040c0040e2103900002100240021954000c0d45260240d400c40c2401003050b5088071194450b80d60701c051040c07010060580903122042c02c829001c0e00c114070304040b1101440c40e00b04113440c0d600018800d58010485640c1c0a0301440401809281c004612116014014250b480d200c0010b040d400e00081e1038411a0300030020200c00710600c0f4482256240d6070b00034180181040360300c13400c0301b1804068411081c5000800c80f0f140c0e800051505c01440071000921140280007600303504244160305c01c002136692035102020121040d0056101c451414942c000c0c240400310001c5800741ca0309200c1030000135000b005840d007107101481c103011410000d00300848401281e080800540b580020000f00303004006c15407106a070f004904030751588a0040410082c40307290080a00717141140d001044c01807500d400342c09030810791 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 259036555 1250 259035305 259035313
    0x1121090409050a0302030306100827030c01050405071502073804030b01061d01140a09030c03081308070e0601050d0b042d0902010503040f030c0b0a050a0f09080a080603 74
    0x1c00d90303030740707190200b010010741c00341c0d0000c000c101c1585001c464400c1440000d290410480c00c20604418041c0c14401e040907166040c2d00c000c0d00c2c3e03420304005469500c03e08000a00c220f08190810a840e5440c0780075003000c00030322507128082d030b9000141c0a011104100300c03070f003000c2c050064800403000d021019862028001204808080301d5040504059400f6444694140d454050040c0c0316450100800340a01d515031b0441000d6a000340010b0049030300c4c06800c941c0c07410814001c03619010143c20080901c3c03a1030002005020104028102d92096085500303200c5827600d083c40c0d0303109020700c07076040c2e50740805000840551091002e0007203450300c08008224901d0840009040c6c804c60b88400803541086540d18451044540c1240030019181d14204142001c40d00001c150b03200081014040f408c485444408252203a20790300c0d80310b030b00442c40c41614202b0701e1007400a010140e8005010905000b12495891941e10801c100264041c40f028540691a042503545800042a056141c02 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 259037805 1250 259036555 259036571
    0x1061d0d020612160306060e1305190207030201020c010b030309030a1401060b04080d0e091902070c03020603010b03040b01061b02090406060b040f09051501083c04020111210904 78
    0x3800183e824054013035503102c0f0211036849100101140c000b54403003010426403041e01440758032240d40e00c0581100c07003800461076681301182a4000400c5100c448007061002801100707055040d400b5201036103110f00280401c903426000c05549004010040d03905811030f01180c0e0009075443e4486a44a6206002055069581040202c650440e91201003e42c1100c620000e8896119210801800044070034075454100002480f100e00c05102c051649030b03500017194010303c070031401a5070082d40d00910241d070b25030710781d203444c10b0a03041500c04030354280d0410004100c19028148040c020344034402203216141443c1c00300554920060016154a540c0c2c16001c40c0051030f5000900250115035100d01c840352501000c1c80403188020106c0440c0c02540405d04440da07840020250861200489000d03088510f0380c030713140020303101c00120f2910598181d030943c900060400c001d00c80d41c000d0300d500000d00c076019006900c80702e0301310700c8442020310740940c0c0a0903031440000d048080b1002d480095088 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 259039055 1250 259037805 259037827
    0x61911060a05011e030309060c060b0d050a1b060c0b06010309170405030d111903020f0a150605010309021503091905060a0533010c02040f1401061d0d0206 68
    0x300681d0642402602c80c0018804074120307418540c4622400c100307081e0810310315240200044140e00900d001c0050f03040c00e0303a007403101c23076013080e49050801010380b0101001d514040ea541d1444001c211411040c0701c007520b2034505c60401c0f810407074a107a12058405102a5a802045c500050460303040c540c8c0c039502800030030a840545422f038503210941940d500c1c10241054500500900034104002c10500054403980000c280b01000131503040c1801d06d035418601d0241d040030b0310306084081a2040410f60410702c07005050300381091100700810020702d5116401181510070040e0040d401c00c0d65014603000c004a442d00640e80002d10409581000b54000d8094485000002041e00c10380d0043c014010261070130720529411080080801010b0070022008424030311610843c646040592075401c40c45900070301e0300f015446d0b4010020414030005140d404010322040c0d0b1075548c202503c00000c14074034010180d5400c1c2042c07103c000c0c1d06500e910720401c81071505c0c242c0200c3c0c21800c1801051008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 259040305 1250 259039055 259039063
    0x120d02070b1315020a0e10051b01091e0803060d051903050711010305101a0d06170705030c01140d090b180c1807050306030a0510020c0615061911 64
    0x1660458031003204440303090401425110403a4400f0384058410000c43c0c1841d03410403a20285100283c0d113043c0c04400d0908103448a016040e03c00d803020111621042c908907065000d20302c0c541c0315880d01d5004040380e1800c041c000c0741c50040141400002c10100701d15260004002042138803510494960076050b111410007041c401da8118045580030501c0740410042100405403030b102803038100003a1428840d8114029614428980c10404a200303011a0f01b030b4075401c450b038080981c0710134401d95542e000c0303041400540071000b20203805001d01c04602e40c42c0100702c4582d00d207070503540c11900d1203d9080c0a507455021216840d41139988800403400587c0701220544640400c0c0204501d0b0b201248040b41404c03910529144114141012000d061030810340e440d410184514165840360380703040109103850309419001d8035032322505040480010281d0020044401d108064420303075102c5038204c5200e280b18030380859100d2418020f00e18260600c01c165121000246014140139007040300140c20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 259041555 1250 259040305 259040311
    0xc17040b07060f050402030c0114190f1112030a180501050a02190306060c0b1e0115020f0a1203050919080306151303020909070801060b0912070602120d02070b 70
    0x80e000129054042c4000d0f032040c1c40c00c08040a03424440c2d890142e001030b4451350307203200c004e06000d520075a14003a101c410303040d40c0c0710000140025511b0380c07004a000d17001c0f2400c1010800007503084100210711100200360410030340d48182c101c90642e29080f07102405440560290003c07501030313600000c085003003400b4aa014146041300180d0713454842c0044003404914464080500d41895410458141d000d88000000382c3c215050703a046480d20700402402c50035808560007c43d0703e19001040008141e1042d0301882c1c050380840d00f0b0030402840058131444040c1029010540c40884108442d001c5d420007584034540c43e0580c3c1030140b000e074507114440d0310000259442d1401000300300c5a410500b01c5800c2c80b041c0b80003050304103c0c10607002c4c0c403800a43e000c000e000c0e007640004208610420440f40000d040c81400904c6815103e107400001604010360861203400c1e00050141500c501181c3d0030b0aa50256000c1c00c42d0303e9042501c0d24003980724010708022260b08104071000f0400b00202c91f80 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 259042805 1250 259041555 259041569
    0x5070e01150e0a0e0a0f0f060906051203030a0213150305060a080c060417011b020c090606090f0f0103020c0d08101413021c02040b030702010507050316030b0d0803010e16020601060f0c1704 83
    0xc2d201e27050070304540032188147c0065000780c030182c616040a805c0001601d81c000754441e4056136035804001c2807000c41131154410310306240030802031000c03942c040c0c1015200d40015106c003507581e9501d0f90002c0d5541804a40c03260004020817041c811042c00642e0ba1950300e803020000300b00044002c00810310b90f51034450300310041c0c00130000e0703d000d413030031450050300004111088c6080c07261080c00540d10104540f1200e2003041c2c91140043d1690281e01591550740c1800140c030401e03860340c00c004e80400c800b1036141164040191020640380081ea030350706440c04001c1c151203160f1031084200e50096001c0e1103420030300801d2014400701c4e4040da0005001400032541c4490703c0f0f0403e00406825140094003c03810305c501441017040040d61020a40810441c0d40760104220400c035002c204546481c403800341007000c8c000008550301044181541c041c003034181c1201c00c1c40d144028102d81f181000c0c000c080000d610076070065016481040b000766050f000390450004e103101d20a0310031151703009510580d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 259044055 1250 259042805 259042811
    0x70e040b07020304060801051c0c090e07210b070c08190e04110a0507081b0102030402012007050d210305180703050c04050c040305070e01150e0a0e0a0f0f 68
    0x8012030a1900368011005000a6080a08121014111040500131540111000d511361410520403100b18441c01e5001342000c034000d525400d156000e0300114508101e188035040f000550500c0c80d058400d15505113452800d048581690f45002d5071a0241c601000c0088101c01030b00421104001081010922000038409258482020f4856420300e80071a104a281c203058109803000c0b10102c9820007010310300b0943c0d549251425000d41d004005090152400d03403110712100460542c01540140d0007602c0d107240309420001690300c0d002003a00b0141040e048034404004608081d00c0c010221403050030356032201d04503e40c804500d4910303003220b0b0340065114410702020708441c0e4480d20266510381e0141081c1821034960a64500703207450000d00413540e80c0e00140e00c0c90010b00a680c00355601c8801d84421594465410a540200b801103800032001110040032250184402070300454024180e2003440e45803070b9181403041c5006015003101a11030030f80b1503440c48244582112001840000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 259045305 1250 259044055 259044061
    0x1505010e1603050405060105220e010c11070303091203030f02190e0a0b0f0306030304051509010315120f11060c0601030c05090906010b21070c02010e0a0f0e040501020c070e 76
    0x2011004803000c14000d040c0b0f440280004200c002c01c215041d1042661400c42880000e981003450203500b004440342c0604e0000d246078240383c10b42200d00000920b988100000c40300416140d264001840010f02054890100b0020003102ea00300500e000d00070b003000200702403059140c00582c1d11441000c0d5008040c04e00c0020119000076070744a144c40c0075558811084c0c10150b01803c144600104500d200d030b00800007070a1651304108840280070007030526004c4000d55404406550001102c40740800d05044030440341d9040120040704640b0741c41c900000121050b2140d150b1101c01c0041a0748050140e214402c59481d15001002e554107510003c0c0019031460810010b0102103030441841044120107200300b200000030701c54150bc01b60300c2d26a50312045c01d4022103240408411178004850b010301042161a08480f800381207038002e884141010b91440c1c100404100c16010b03080390320402c1c1c0000e00150184506444d441449030000619042ca07020007035181040c0d130340c0120005007942e0f00b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 259046555 1250 259045305 259045321
    0x30a05040c081209040207060603080703020a0b060603040c031b0b0408150a05090a0b07021603060b010f0201090308010911040305010504080712020303040c060507290604060506190c1505010e 84
    0x40002d100c200080c048a00c4054a4500e140c070030340301e01c41d1050360003045500c103001c401e03800440111351181855036034410303a140294076052131100a0ba4246454000103d4904110f030461384a16030160014442c00d040d03590310780c0d480c80306004901c501108070001090b503c41080043c130103404da00d0002d040e591100b407184015900300510b03182101d810b00041c001c0080c800120b10700c02d5175000008102c00e9032100d0089240c060100ca080e03c0324680c013880042030105070340c003080410b1002e0765100890403494100b41c0c262640920014002441c00b07004018281056003d10201400016070070301d02917030f0b5180c031429500b0a44060f1681c4000161510421020000e0212401c5840c0091421460907840303407150060140b1406050180008200c002c100b803c1d8000c01c0030000704250418400c0088094840c076100860312180268900b9002248501d061003d0311141004c6002c2801107509011080350000e030308031030442d680c0022589240f841122402180d002e40018003100c1c03094541151 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 259047805 1250 259046555 259046573
    0x405040c0203041d0702030c1501090501051c110102030702060d02220b121b1b1002040f0b0c0f060f0a05060907200712080301090e120301140312030a0504 68
    0x400c003081d58000c000030820400d01d4090700030301541c0c0904600d080c1c0d403404000d9041d071007001410342c12400340301400000081100d03505410784540100400c407981c2c0759410b22070500252403444030340e404e409566000098024850341034010040c41540d081c21220343c00300d1801d402c0400740780c07107250300030440342090020585403c940c05000302c004c01100340b07400800071035440340c4608038000500d540001582401c04660361036540b6181542240c3d40e20079400840803401101c08543d0107401030300e40d80c681007207060081c1e5047d142c020801442c0c03140340c81c000500d1580006080e40c214014480e0410b000107040c0a00d900c103e40d03290201480c2d01e4801400421140010041440b0f09042011f10100742d5002d084114440610108135403007030001c00d05a440c003802584503e00c0c0c41400340b900d0081205520285040f204a03c1013408a090045d100740d03207407540742c0c40b01d0301c03170036000d2004224a0041260600b040e00001d81034034a1030250f5050355005030703c00c030b446400c1e046e1910107000422640f40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 259049055 1250 259047805 259047821
    0x6060409111c12051c090c03020a08160519140310050f07091505030112020a0302120307021302070b070c0f06061502160e24090103230c010509100314070302040504 72
    0x4606149080400e460b19001c990401782c031106541c1e510b030380c10303170420040c091188061500180260055a40e43c1e150580d180d0300030081045946910384006114140317a40a8031142078022404500c08e0300300040c040503660001e6480c1d60602c150350002c07110111511505001c4d07007050103070501d240b800540107041070000e6804180d2100342800c00c05840c56002054905440000c3e1100c5a25000e0b40000389101880307030000707176014582c56114083c8a01c00002094254402d40b403551070758203941009000ca0142680181130100218009102c140c4902c00903414580b041a600480ca206901c608048400fa41c201000d1400c10b00c09102c0500d03010840700c4505540712100311220b0b82800d001c60010792000e41203840002c946162039100c881b000d800316000080140c8080a030b5070b0b40b0f09108801c6400f0f084601022030500c812029588004150351a4031007040c1c4503640740403045814007080043c07030400f50040654824940b18000054883c45005840a07540540c0f0782d41003008000882c1e03041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 259050305 1250 259049055 259049057
    0x3020903061003150c05071a060109061d09041407140a120302100b01020106030f060507091707150c0501051602060903040612020a03020f030c070507090b0306060409111c12 76
    0x1509007000050780c0c14044a0305607030b1446002c0740da01c02044046c1c1d158090001d0040402812001546c1003814814280c0d1080a00766181401242d6a5a09031104c40c00040e0003c0500c00d0703441504c110703040503030107160000d124680c403854440320050818280602500702d00d005c035011101c402140e01d4440d1640e000303001c00907000008050070b85d0b8087d543d01000c001d00c44109490312056a00c5a000394009030065070402544e05214a079881c1c0034005090803504903002c01c01c007541c00310300402509024030760407880b5001802403900384400d91210309401e9040104100014100c0e1001510a000c5c04d8080e00c0500003000901c162214040d050060041c03040005030300a0100f044802c1c0e00200c215810b00d1600001652846000e0302100a4415080e40840d40340300003042c85080c042e610000d007603041c042c1054074041905c6002d07c2d0305680c0004180d6a05900001c0421007518060b4003074525140f00d0740b901c0c0b0102d200c03000420b10b08641c01070710380950194070300c0c2401400400c00703802040000d6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 259051555 1250 259050305 259050331
    0x3020c120d030c0e060706020405040c0f0c08031012151109150306040908040821030112140705041b020106051207030b09071e031b0e0a090515070302090306 69
    0xc0c2140503601c200015101c0d08264031000d80401403402042402d508150103820b840d40da0729941401e5000e940035104139402a481c00d0303000303049284500418441021140c0c0e4001d401035140c0c4811a4940018000840000029000007a20708000e60002c203407610501d0076070000041c16420b0821030f5800031250000900401c8441c605503203038146504030000c001426a11b0340c0300e18010030300402e0300603c010000e940001c0d01280e0700c040080c8104107000365030f00c030101201142c175030400980000c0c8244c100f10200c010344800000c80c410010001581488200c482c1c541d41c2d00e0024041d1108110015848500420080e6070700c1d1b4280101e002820041d180e035080104518100d5031f40d2a5203100107070000b903480d004210030b12401e0001f20014503283c8110004051503404d147d0318030409200481f80100f14000c00200d2000208101d02194811030040c0c1003585c801091101821400e14101c0b25805030464840100c0140d003100360003540265801a22a6407a205241c90804080e0040642d018 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 259052805 1250 259051555 259051579
    0x90c1e0e01061b0f030c050f071a03070e0901090204180509030906070203100e070906140a052710090c02070b03040206070c05030a1a01141c030c08041203020c 70
    0xc0e034111400c503e05a5045990700003d1445018140c42c014401030340301d0100f40a055020016500c00c0c0d02401c161810a0704840b981e5030b030f40e559445070304608034080c5000401c0d011340c1c0d00519842915420110150280c070b000080c80c2010036084100d580d58045414044c107500012580041d034800201045a801c0c01c1546503a06c0c092080c03108c0c4500c400103260400c64034103001198400102050078005051050301131611001c00d8061110f2107480c000e8000b0301c031a0808100010100e003e041c4d4001c45041805011240d081d04402c0340181541c01d04d0210020301805410b07109000c00700c007003400030b801c01f590b185c02c0d2554040d5010440d071011100b8424150148120b03a0001d60490301c2d140d549400e840d205c804c080300c03640856071601605a604051010100450703001411003211090a42e8851240b40e5682244c1211903030001c00002800c1e1141c0050544c4e404818041e040854403050240e44d106882e40c4584c100001610f001c2241c4801c06070104113991604100300d03000444a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 259054055 1250 259052805 259052819
    0x2010b010e010804080f09060a1101050a0c1707020102040b040608060a060207080d1107030f0f020306061507171e0a030509010902061207030605040c0c0c1d0127090c1e 74
    0x80191020b802607074009100c080d010b424404841e040d0324003032300050311403030220006050701c14034030401c0d0910b50a0800044c1c2c100d116224516509803507464145042c00040405800e441c07000b481d03681590350801c03001c1007905540c0090001031440baa9281c1c0c5a02d0500b052140040e81e81d40623400390b60100e001030024030800319141040605c28500072815505072021640790030300c10b40c0301501c1d032807c211811040c800e0007202c0c000c0740b90094045403900d84844050101104100540c4411030409000c1200040c4c590b1443c00000201e81d95628188584107000d002109030544018102040008028020355018080d04d980003002034000c00003130b500c0b40c021071224803034418204000079018000072402400380d40194064540600304220441509001a12000c0c164000303a9034200f440c8000605207000010401e0028200031030312510741d00c0c04020450320740008070524120901c03064001c041e10118800d110003140240d4800021a1074006d07140d20200040300d0300038800c200040144900 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 259055305 1250 259054055 259054067
    0x705030c130e040b0406050f06061e07020415050916021b010521092a0f030a0f080d0f0c0906050c1011070501060608040506060d08040815010602010b010e01 69
    0x314044000d915501d2a10802034072040e1682d8014039030ba01062414481800018107031144103a01c100c81c00c100b25203405481189030001224965440002003002c11300d0f030318000d141e400b144d11000ca2843d00301282c650000d024be0b101c412009032502414141017025141903400c554210710070aa04256901c1c1c086002512003948841010000b00c1e0b056a07004242d202c2c800f00d031180d004070716001305403c5454070103019030310341598459418810300c602d03400001c509180411000000b020340142c180316020a002d6280c0c00102d025506010740000c030307008240705c007802d0280d152240340b080b6a07135542c241c0703244101e4404605000d041e078501138071b03a090380c1d410180380000d440e81030402d1604d80355141e80e02c03403070030f00280804c00707500e414a070018021022004c060b090031440303a8000e1081c0b039255801203070b0402084401178107030381c81403020a04504200a04a81c0280181e000300d2510752074007881e901d0b10801840810f45219040e00402050b5820700c503c0350322190903c0c0400800035030030700003084 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 259056555 1250 259055305 259055311
    0x150c04030b06090c39010c1704050114090a051006050d030309080c010f1406030607050301090c090308190201050c03060a17100c0c0308060d080d02071505011203020f06070503 77
    0x201c40810200e165443c00e682518141c400c0345900710b00c00d010201041d45d00ca40448010450650701c0b82d4400135144060003048100750183d0b58175140340c02110200c61000c00090401e440c555650040150b281c0c00034829580f26086050003800f05407450300c3c0c041c2c900b00c1400d481055003490100113200a03500d02405c8100680c00d4500403a030540d0504104202d4420030144038929031a141c480708c06410960000444052043d0fa44d00807a5200010315864400c00c940700d4000600c1000107108118443e400020411002e00d407149000b6260f07036030f1502c1948074003141c59441100c02c42141f40c103030f424020580c1c0920700012490442c10b02c940440c051000c28060421440e44d1314000c0d851f1100200311407541c500540f5000d01c8107100c082c1c0040d1800300580420750010b2a034200240040c1400c07985116556441000b00d8903028904144000a403c00002114100791000800421503410b0059134041c0c4841c441e0007000300d80624004e85061158100c80c04142c0140c2d04111805030040241ca42c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 259057805 1250 259056555 259056559
    0x60e010f0905040501060c02120601060219050c04020723010606050307031d0d09030311120d020a0e0406030b092a0906130603060f0f0b092e0305150c04030b06 70
    0x121616100d5029240c000c265080710350482d10706000007441a030302510300081035000703490106c1c080f1450405581c90708002d004034009607120000742c4940001042800400b18010010780b4035085041002130107a0f482500c05031110510340f5254544091440d16a505c15507400000304030043c031341040a0708130b00004000d6414161b0f2143c021107140e01002e041c09480c0741c0002602d00f20720701100064130011190105078006942403503030041108002940c5441c05581b2544d59080414100c0500043d600007045007003040b942d4240401251140e000d044003440c402c1030b40648a240c550002c1d45014504080c1c6e041c860503900c02c01500c400c980c004400035503010b448403a40d5580303400c041020104c56003007410305036243c01800014485150b003e00c003640e031020030500440340c60700380507410746459107095030380f14000d2004a02c02c6030280905646080440403000c01540c11004001c4003104141d205480c5900304445100308400300400580d444078181c03124500b00b9046403242c50002d000181494 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 259059055 1250 259057805 259057817
    0x21030c0c15090f01140d0906092a030f0c051f03050702030715050403032702030d0807020319030e0d0206090c01090e0a050601120501060c020a0806010b0f0f0904090503030f0907060e01 81
    0x118805170801121100310001701d0034004580d0500c2d182006202c21307c030940b5259049081080015400015a0a03c49410154100203421364a828441c24030b945d00441310380304031000000f4143c8820340d8182083c0307240101d0b084101e601a4003c0c054410082402e411900100030140c0001c9180100004000b41d40800041d00d59075440d0680052100c08a0140802003c0c1804c0c26034a0442c0811a08140302741d05451400784040d100ba41c2804050301e0003c0940c1042c4001e064189170003d584103030011614020030f90b40e84201d0b155092512459944005030000800c2211500080025a61a000a01c3d010410b5482c020a04e1400d8401a01103120540c8032404500c140c0e11800c10000c1019040e00d0070841c41d651010040d0060313003401c0003240a0031440d03000040c000d1021405604840281d10414034010f40c03091100c150b6400543c0545048038148007440103611307584039412825108000a5036a41030001002c2c806500062500400d68000300c0240226079009440c10b500c1002820302c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 259060305 1250 259059055 259059077
    0x3031b131202031005180c01090b0d0c0c0804060203040603140610110c1c0203010e060c0d0b0312030a150918061e050a0222080a0221030c0c15090f01 66
    0x64181102104e400d071a2608000a010741d14801002100e9840688821035024031880001920f683c209403282007005c41087c00b0141c48420742e6040310552000514180c40c00500a507180c0c074258100da00b000e0010b07440803400f4080c0d29014402d0313040c88000000300080d240303400c1c1d0000301c00b41e4074000c403681002003181321315a80d5401040213100b80100180300d90720004c1c084c0c1c4082d10303013000c1c1c140c1a4402d600300900c4120300c42011a01502038011f80000915258226840402510701001496018420380b28107a107403503000000307540100010100440c2080718000380b031000030180d42284410524112071141941c6d5014010690f0991090000c01d0040b1854004000d80c0982000708443d94103000401c0001c103000d0340180b04041c0da0143d200c4440c100203417801504a200d0050300180e81c00428950058504552680e01c004608903444543c46001c40e00a070441e00f2030781c40b440742640168840310b11803403e48800b14001c0e0004099508004403400002c071500c0307042501d0307410b0050600b10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 259061555 1250 259060305 259060309
    0x90522080d020a110f0c1804030801140102031b030901030b19031b050d0605090d110606091305030d0509102a021c0e0f06131509030f030203031b131202 67
    0x3a60644c5000720f4184c45011100010b04e03921082e01c0041c681c070510046124186048003000340901071501034ad55041c60ba030800d0001c19503020040851419440240030280300014001c010640810026000e143c23507030a00c1c000501a01c0303070025014400c101d125008205004618045070071203400c080902070a14110800c20308004240e000a9003020310400301b5824001140c02c46070040302080c0c05c80345402d202c08130854104281c0204100640c010340085190743c541040060382149030070040c10700740c4c8115918649149c0c484c009004946841e60b081210201d801d0020020644449030140005000508500c520710104a020000250300a401115844c4200000411340180916520158503101409860842c0301074115204200303030301100311344d0308001094880d44820303800d87c3c40c20b141c01e003a95440c00c9442d03000c15404100b008080040440c44d6100e800300c115009400ac0d660368148481c0079000da8011103804100c07404104002c0d50702510700f41c0071004880c0405c2000d8082020740c40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 259062805 1250 259061555 259061567
    0xc06060506070302030304140c0f0126040f0303060501030b01270305030309011e090206070b04080f0f0304030806100207050d02010504090f02040602160609031103010f06090522080d020a 82
    0x3078201401007030110425800200450065004249089000544039849681c40c8050481c55800c00c030034810710840340d4010300f4200e00e010a1110405c0b07407101c03290802d8099000440f81135175034a029240b0042416014450600076000a03e01400240520800a0700e000c0c3c040da264122407025001004050f54a0a8103201450b03000003a82d55a080400f5101e0103004e5420406803818200c1c0301042180400f403040d900180d602900d01c0381000810744072045480c0c402041aa0034620422020b07000306400e40082c006001015080340d01d904160500801c41c00300140312600801c0c600c0c0750025050f0700004c2140c01c555003100c1c081240350082c0b004940600643d03110307040540c1040d5080601180c2500600107607621542211407092014460f88603900b01440b80b080850100c0c0024000f003048407521100e840e0026001186c000d101070345181c01ca64041c0d1040d038500c0c0e610014480050003810f2001e252042e0b18a0500310404152188000f40c071840026a00c0f0039030000d40c0401c0140140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 259064055 1250 259062805 259062809
    0x1090204050702032502092208040816050d020a0e06040b031501050f010807231603021f020705060c070c03020d0516090c02031902070b0a090e0c04150c0606 69
    0x40c10600c818181400040e540b5045601307560074a0100c0802d2244081512031701c0e011141d0020310150542d15250507044010400e4040745100c120f91700803000c0402e4841d0300500040203132900500c001c0e4427152710b04c940b1030003d41106109010b52628030015a03941c031089416590b1461020709540c40d1600050010b10541400c140c040c0101d07031000030690288084e6030704841007a40d103d9500b80d00c4600449402904035405008220012801c62611110880054220008011191428100c120345030020655001d040300141c0c070200c0283c1224040c13910030f440f0400040420350a001d03403030755583c0e15014000c02c9860300710b001188130b005020440c4550001960090f00240e451886418130b5500e40312481581041c02506c09400100220184210031688140303074082c41c01c04443e40e05600e032403c05215618214840c05001242a8110b4802040d5803505034881074612441d24540c6034036480003e1904050003c140410000c022240c060442c039a1024a00150025070510700800144555 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 259065305 1250 259064055 259064059
    0x2071410031a04140f090d05070b060114120a15080304031b03140a03030507020a0308010612060f0603270309030b0a0f050114090a0b01020d031d0a030201061505180f03010902 77
    0x440400d21381c1440741c061007401a60b001040c9120b940c1c4103c841c3c0c5c0e85010681030b40000500404c601d00108603d154440d8000e08140f41203400c0f222440b0704920309400440c58100d61401720014803403c40c00f5442441030781e00c05a100e200981c0d262842141d106c1c00317544000313040c540303a22130007148041741005030b0000b942d404202d001314072a07048071090760382c4000d04003240460302e0315010480450000a0309070015600d0b036660140c036030074003004861803942d0800c80c0d2501620381c0c4c00868011b00d507505003805001c40b9540000d03801d118144014503c015941d00c0b001e0751000d40c0d954030100b50f00000860076242c000b4004030780c54481011800007015128101c6004902d0701001140d00d440c1030040e1400580c044841e4009a02c490344460200c8070391054041c0540c1c045a1030003072140c002d400203901c101c0341c00c00542e442d4030041300d41820220140780850042c0d54400e0b0600100105c811580d00c0300c4078138503109082c14445406440564008020759101e00030210900000340d82c2504541c0e22940c1c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 259066555 1250 259065305 259065311
    0x1c02010902040e0a0c0b1306200604050d0f0903080306100519050d050901050723070212060702012301030f0f05100506091b0f0a0225030302071410031a04 68
    0x440440591a1800d5102c05c491a82c444d0790001280c0d5415410354644848280420010528119098484506482c50301564441f48500e507502c099003030000920a90140c0c0c003401004007280001401100b43d8800c500910082c207030107101240400055a41c0101c05403001d01c422110a401610749008960580c812558007030450905103902c540900320700c0c0c840d071400b4006625000e17161401d0f41c004507080000602885100b0740001012410030206035083c22025240000a402150441c00d0400541d01c080c0d005409105a40354240b00314140191722100701c400d198103450301c01c0e07004c0d181840054068844103941400b800044074524000c0d40d8440c0445000a52040c1e950014003c11501188900303002c90008504007101c9503107108c0f81ca520449145800c0c0703102080d25198200d80000000c62040b0140060901ea140c00080c20100121a000c0b1a062840c40e00a01c0e080b49500481a0b400541803104000d441d2029801440c0380349050100b074409071004544c41c030b080302c20b03074407036220381 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 259067805 1250 259066555 259066571
    0xf04030c051b0f060708090d0c0b0a0201020301080f0109031403040204060e01080a030e04050c0702130608060f0a0b010914100228110303030403140d090605270d021c0201090204 78
    0x1594140a0010020f50358540e000d42d801c07040128a0281c6240a0003040040000c0d25040c0340840081c084a442081403080468480e01800d6954010702c00d0140980e5000006001c2c0d207608011681c0445621002880a44e4243c4e800804500312500c4c3c49001d544007101180071540d458001c64003522020010f02403035a5154206a5140b42110b001c3d0045403241a020145060901555204030000c001840c13078074601c0c0e0b0a10180b0124101c401c44601e07070312000410303600d10a01540c1d0186107070645a1529060401e0880c0485198035070ba14148481c90100704407441540381411b40c00724003251080a00d0400e03003426410201100c00740c00c0a607101900c1e1a103c0c4a01c00340d42d10540d070042400103a542422800c1c15964802506c001e000b0407c1e008080404e480010010305858007541c00109141d1166580c0c0710680c2c5081da03948802c9050b4001e030582c1c1070301104110f0044a40c000c01060302080c3e01101030348424051002132420401c007000d02c00058001d400ca5200343e80c3c058000c1040311 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 259069055 1250 259067805 259067833
    0x312050708010e24010c030507020405011508010b070c0b0703023408030f0301032a0b041a12070509030c06030a090302060112080d0f0f050906010302011e05030f04030c05 75
    0x20802d0060100c0005483c1c04a01d16510016a44404c451011220160418070000560300180c05100403070811201b0000440103840b6070003014024100d416290b030541c10883c4002e8510b900507041071040004c00d01c80c4501155100e11a0400c560103244102d41d2607007c0e01b4100e05000c1e42607466940032205000c01100301c003c000c03180e860032100848208013545c072004078980320321404c071460b00c80b12400e10062000c123240d44219609003a81100034a030f441450344082505001561064284080100d0200480941085041c008140c002c404074503105060f09001c03039419000c0d004000304100880c03201d229850401c0341c41e00c1e140004001c241c60345000b008050240c11440e50440c0140100070000404004a1107055a410b500083e1182040050b04215004016016104400d45d488040c00f51058449220b035030700908030072014100325810744c0005800241041d20043e804030180b070300720500707a80c404140d98104400c60004007854442d030500300c5800c06d4181c00030300940500c2a00c032000d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 259070305 1250 259069055 259069067
    0x206031303031104060c111f0c03020d05210415020708030901150806040f170403060b01110c0a090209061902060117031608090a0f120b01050d0f03050703120507 71
    0x241c400d40d0240880c20f188644540103006500c42d01c400b00e0950000c410005d600c42074108070a210142c0f80344c10105100d20002100c129045043c00802c3c00000712130705042d070602c40044403650500700249441e440710700d24182142a6000e880b070b100f680c800403a0420141d0340144892b1141c4040541d16543da605144296920981d0301004540c41c2c040504210b60103c03072404100c0c0c01140142500e6522621240c0b00c05000c8402201c02c01000401c50400303014110281c0007079070050300000b406450b800005003000a900509050aa01c40b0fa13071583e143e580c180307806081d1401d80030b01580342d14008001c10054060082e072031011050011618800660000c5c0e82c60480d040c46071501b2000510052003600c0e0310502d207170228130030800c0207064041410b41c5c00500c19448090a40c1201c0380d80e90305200d00e6081503400600941110042c20000e201c1c04288250250004031800c080c0e160695580025054614200505014010814006040c000e580070300e072040120100b4031582c508008000c00c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 259071555 1250 259070305 259070341
    0x5090c12060915150406060905033d0b030706051207030e031206030a020a0305011a0a08030405040b010909020706321b0405041a210c0108040f020603 66
    0x28188411103480c500100180c0107000e98240d030301038004111840030000d15501d0080801291070030300c0d01031142c6601d6a104020043c84583d443d0007031581064101070806440e11103100000002d03450005885080785a0311481c85c01c0902c41c4d000401d03400c103165000d8106502c40582c103002d6440000b44250700040103280c181804034600c4690b684005041d0100e40f41c2c840c48101381c1c4c0c01030194695000078070300d18940002c1c0040c21142c1c4010540d000541500454008031105d94640c0b50914040b0b0103c0c8034900345460445501c4425400c01a00d90342c0d03802184030f440d20464072507404448590103154450701800098500352341c0c45c2d5207800c0410141648086c58011400e40400e00290343e8010940909600460380704034003562948118286080c0405400303010f01c0c0c104100004250f6914841c804004202801e80c4c503a008980c1c080140010b17250220b031302d8500358010058002a00894100100c40b0309080c500419142c909000c5074202c2140e1000b074020b2400001c2c4404041032010b0048 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 259072805 1250 259071555 259071559
    0x1207090f0605030f0f07050f040b100c020a0f030b040204091106030103060207050705100c1704090903020a020a0e0c250f030c0209061f030e03070f0c0806010b070b0c090a0905090c 79
    0x144c0da840700c1c40725607655002002c2d00d0350301c3d030801c00c0c00303200c14904144981010700e40140082514504040082d8404103040c0004000c10006007800c011818110f1030b03c002005032484031406580795441c0c140199100402c0240321300d545030150b504005d000303031030f1420391000500840d8681d0b8603407404200950014100780c0c2c40e0320609000140c1ca28140da58254030340c1c0c40766115800c10740f4940da08010340408103d0814030540c03e10000c503500312a8482c081013a4000d50090286081d14014080d007100c0d035410a10038078440008000701072000340110303411600703481c036070381f115400d0200301c0c5c01c1d0348409480007440c0424400d00a0285648419803224542c001c462840032500d80004000700c00080301a065084800700d003860482c1c40c000d43c44504010040b1056034508101c03030740c030350000b40074145084070030b04000708007030000700c0003082206c0c09001209500d40c5808031a44949001050040c4180604580044d41c40c203240c44449030a0300601c000001804030b4141018000c0d244d119141c401d038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 259074055 1250 259072805 259072813
    0xf030717100e2d24150d2004051201050402150a0c1e06051005011e200304030b0a05132004050a0e0d02010213090903090b0d05040204050a0b0901051207090f060503 72
    0x40c4c0a41d02c0700d48220810303200107000c0d000c946410410a81c00d81c01034803031503100550360f80001178514010300320412111451241d55030380300d05042c10000001d5060700020007582c909410000180c0718202d170705414101d106a09a00c4600b04182143c450040303900040c0219601d09201d2082c0c005003041c000d0651040034113204c242e54548104440100c0c901c59680098106c400500b03284041c4100d00da40c0c0411490102c10714400c0c0000908903252680c0383c2c2030a03900008041052184140c003072504444280300c18081400c1208840710010304035980a0854480c1d080c08081d584542102c403030380c40c50050021310540c80d018114a0041c211b0442e0400c190064003014000c2d01e106108441618018895000b501c03410040d80300001e04040034101c0c02d2050b40c0c5030128490080d24007805240240002c045001d00c5c161050006580300584001c0c4481e04100c524280c03a552114203a06440301900e10604c00c241d400c89242c030345401544180038981c500505850910300341d42001e4180d8001b54111 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 259075305 1250 259074055 259074091
    0x1e04090f0903090503190b0717011205060603060c19030b100206010503010b011107031b03020d080d11040806060909010f0e011a01020d02030d05060a05060f030717100e2d 75
    0x11580320092015107000821b4180704184c00203003401404c2d6001500c40c6003417810f00842030700709200300200303800c40d0807a103500c280740200f004420030219a1021051340580503038100030089040601500803d07040000a00102090043c480c0c2c2c0021081c51008060702200d84440030040d450b95800e028090080d400c00b541ca90070303940224200610208420000d00301d50f0b155496801d40900c440d16101c2030707905900c40c000701503647c040c0d0706998203006080d640e075640007851001c01110f14205021b00048401c1c031081040380320210b54140e00c400c041d14000119914440454018101a031030010481e02d8040c16807916441540960070341c6040d8012408003400503001a40d4802c401d510000060340100110b00300ca2455801c11a080030000d8084200300703440e200021600e80003000200c40050000c010010202d9001c41001e405201d00701d140800740c14000c00c0030981d44081d001701c03c0f03010445004642e086502c08038003010340d91142d85441c0045800c201003c140407051b207407000d000d0010952 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 259076555 1250 259075305 259075309
    0x150813113c01050702010818060408120601090501120f060e0a15051804031b05060a0b19031502070813060906020607092102060c0f0607021905031e04090f09030905 72
    0x4459101c08161a024100891a0b00440c0e54041c014604900c48000071038000c1d0b120340030022540a030b4410b001164171940010b0911070500340081c906810012048070401543c1d802a11182d05040c1203000850140114444135003e0141d40e401924400e035000200b001403c40e65001581140c001c1410040e8159985c082000c0101220391009440c030030f090108000034001c00038a8942d40125900340e481d1206500d8443c2800421a540741ba07964982101440d54540007051101c1034850b0903000b6056411070b00c420b030011403e0301a11141c580e0026001c4140900c00050b24209041b1114450718203884020081a034a2a0b04c00c440242c0b00b003201041185005a84000075515030003a1036010310311b580c5510100c50300c0401d00382d8001c007041080c0b0039181030034400910303030007071007070051443d4140300600a2410040004111030742000c203180b00005000131084648240d41ca1620400c4001c050f000c8038004c0c4903d1388404960b5140c80c09a5100051942200038554000c2c1c480f0f140d41d96441c81 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 259077805 1250 259076555 259076659
    0x80304050f0f0a05040513050102030f0109060e1e06010509030f070e10080a0201121b080f0a090809092d010306060f030218090f0f0708060115081311 66
    0x41c01c00d60142c0e881009100c603061a1b4402c941c042003100071192010150348840e803c907401680c03007003800c0d107035240103000640c0e0600504008000036650b04d0342c1c0d0319040e05030301070b02c0100101c0c500701c109008020508981c03203032043c0d5a8005005095500c00b4049940340d5075140f406100700804900401c00145445002c038103914111000f04000d0600010700350300445004511200b004441a6502c00c28900400040e0b4018541d200c0741c2caa842c40d904113401c1d08011290000d00300d0380998204412040001d40a20a0b520b4984084c0c8580c1c4050300c68040702c00741e607800e2001d00c900404100000c8840c18926020060480380a200c08110380e6485803600d00d840c002030701010f904124590000c80441c15212421030b4000c00413819904402d06901c0428184801c02c0c01c0e803022588120400d11201b0014802c06004100b0300c3c517002560140940042d0040d60020a150120820844580140b200c0e40d03242c2030100030b0042600d0400d00031043c8020f101441002512483d4142d8080d900d90b00703204034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 259079055 1250 259077805 259077829
    0xb0c19080a1b060519050a021602010809030706020a02071410090302060d060306020f0711040c08012105150702011503080f0c2119090302010503040605041407080304050f 75
    0x25145425024401074401c50280c400c50311100e00d00700d10400100e0220b2107900c0c0240c441d51882170b8040300c03001d0541c2c180c41024141450b154030401031010145541003520124a07030a090900d40c550791484054258040c000018100300c1c000a003c0700031a03400314107a0155400541d140c0c2c480315141060100d0741d422a00010042044c010b02400549402e8003d400200030782000482c0140d142c3d80c0e107034141d8014402d03159141e0310101d841d00030050444002410910150303010811007584410040000302c0611902c8102080364000000c0e82c0340c007080190390103801c002180c0c10240c1301e601a840c5c40d4011100c25005520b170032449c09540808560000c116900720084034101a2442a83c040e96840051101040d114600c000420b204400400122085400302c62585900300d14108955030002503080b8010040f90768000e000507130f080b405032070700940c00510018079540c039450f020100c00c0d50203481002d00e2040b030340700190719000080180146c400c01d84d43d4400210b0003d060000344c0007a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 259080305 1250 259079055 259079063
    0xf03090102100b190602010e0106060e0616050a050102040e012402120c0102041e030c050a12030509180f04020109090b01080a11090607060603020301051e0f090c03070b0c19 76
    0x4111039803440310940e04100d440349002013845450b405000602c41021003035511410240c0d44421040c1902c4000b84034031001440b650610405072451100001e00c18031810003280c840d03510030400035081c030004012010006034030400841daa183c9881405e00001002d20600a0b0143c105100983e420781c0c4030050340f0800c425800034694000180040313029904800c04800e100e40d4240b100044035010002c0992a181c0c440510228003800c50805c1108061140c2116000c1c00040200708400d841c8444c107000010f415290254071016402d00003072050072100d82c510704141000c07050214120200030114000c40c1b01341c95401060366611501420765030071030651404202c40800060300707100c4981003074050505242505280480d00c0001515541120400f42c410030340d141c0050045003000d11501d0741091181222503100c2c0e1a0f008000c0c00400020070560980b01541c002c1610000c08001514100c4801810340303d01076110201c411254110305040742c03d5104142e56180a4800804030161940e00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 259081555 1250 259080305 259080313
    0x40605060a0c110112060f080f03041a0d020904021218010b150f0403080c1e0c0607060f0f1d16030209071404081e010b03010b0a12020f060a0e030f03090102 69
    0xd9141c3c070b02030003101c0c20201d060005c0e0070040c0900e1017007841290094205004003600e920300f86038800d40751049260906034907920401c401d01555030b0b450004030f841c0391101103460740c8050004108000e4001d48141903042400810754650100103c0045441028810440c114114440d20140d00b6258155101500865512036600c90100040d004100c01c00f800440e15250a0783c070307914500583d0040703286040d1600a0f80d10301c0ca10507800c202450303071118007000404180550000146d00ca10900c14002c0c0700c075944d441c0d20074030600700340c101c1c0541840740300007042114030b040010301c0bc0c1640c4c280c0c6901c65001d84003d114000781260131b05802d880e000b9184002503500e51105641c81914040e003040c00e03080a200000d400c0604000555500304c4c0ea0703011038590b00303414040c2030a6800784c1308014401c0e4105070450a1544462010b10200d64610a51618100b11400442c01056401404030740085001803007035102504801d00d0407510302e06508031484040c81c038035100d80324000c404542c0e0060300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 259082805 1250 259081555 259081577
    0x60e031005101716080f0d02030301060207050f0315040302070609051f08070c33140c13080318180403080f0a1107241812030603080d020702040605060a 67
    0x1860000e03d8480c54412080341c41c0700c01072610394250101283e01102c0168411040b12050300320030702100900000600045046504112010303442e0300090050038000c050450507001d45640410140e0807406a442020119081504000752520303002d000d080041031414070002210300b00200500c080e0450310316480003641440104560388400682807504001c5040c0d400c2002c1000741c107840c040e21f80c0b0044400001c0072040c038118507a812100d02546101d160814484210f540c600745030f50b00c1105181d115075914004e0a80072071000c41a00459124070000c01e4940400b40580d00701040e481080780e080380c081000d07010b0f40080800840340200020303101c0300441d000c17040c040c0715107400140c0284081740c8240c0d050003031402a044003a003901c0240800b408084003100f008a00c1c01821800300d402d02284104002c200d480240f03004000704035558035404444803a10a520440184d58082021983d54a03100000c60194118440680c0b1943c039112000940e468458103c640304512a143c80100007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 259084055 1250 259082805 259082819
    0xe0d020a0c091a030607030b010815102f07030c1e0b070602120f0711010c020a030507050c0402071a060901062c06130e0c070218070306030c060e03100510 68
    0xc1281281030500c005580744440700c0d0394090017143c2c411107460f030f00060801c2d03501000500044019140700628005100c0c800d50503291404001d14144d020b0400c1100e070200800c0352260407800021a10000d100c0640d81d070000709020400f8012603020780b106500d10342c2c4540324801025004c1420174010f41e5040d02c100a0f2041110150010350300030740c1c0041c02d0813600d03401109541011110701c0701c100c9100741000041038002d0f005960801c0401c00810600500a1001c0d5998550b0795014042c06030110340c1000b004420080f050b188140940190348a1401e80b4016201c000c012085294100b04000041d4440c2029a4658101c82842d40d130301a8041d01454404d0344046d0f880c4141200218061015503a9250344004211124900440303000e81c9240c60221900144e010f441d01100c4c04003082075602596407040030161040d0350804140454441c0401a001424690720041800c000148006104c1e50030107121280f0070810b40585410302c944103401011501308840307242c40781001e1803080c0700e02 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 259085305 1250 259084055 259084061
    0x13150501080c040609170c060304060902040e0a050601091d120a021b0a0911070b0f090c010905090a15120501050f070201020310090c1710060207050105070503070204150302040f0e0d020a0c09 84
    0x2a140c040c2d0f20303903035040c7c0d021540d00d60040301c095501c00c0e02c80341d4180440c182481812920464040541f944103010780e03440d0f440705010720500c00303000c1d219a0b159007a908040002c401401c5401c00701e0700710300241c1402e050030f034118010240c00741c0900e4820b015041c3d035000c0c3c007d4100200030f010400f001d0501c0100c000524005006030302401c0c0034040078001030300720000b150140c5c455891034400c52070040d0600749401c42d00c1c03030000e041080825040001317840308884507410105000c00031414940b42031600c412140d85e6841200c3d40340b1551540030911030107501540c098031096007495820b5445010580c2031b03110a40e48a03050455144040220070500d910001404d40305180c100560040d11000000c00a42990740c0750500c2c0080c2002c00c0b8554041090b000204801c3c2000e81c144919030b180d064aa01485402901403503d81030703000c41c0d50150a2100020b541d005104100c0c03a014041c4480041007401001c8845104412000d0040c900019605400d2948640400c0c0c002d8101610080a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 259086555 1250 259085305 259085339
    0x71406031312180b0c030706230406090b0711060f1f081c020a0206190302070f05030901081510030b04180305030f070311030a090213150501080c040609 67
    0xc82100300201c03000180501107820248405640d4121004041c01c20440101440b6070105464103410842c81c90300701404029264400c1e00118002101c0092044003001d204040e206a851442c00004201c10481641e02000c4d0b41070060300070340b0f05640d070b01409880d1061901d00d0800c0c0f40d800100040c0c0c000031011606607001960a07150040c0c100060303107003040102d8076042a060f980140112040e00c030400c5a00314a800803910007408264020780203c0c200f44a030003c084c402c100c5071594400511f000e501150b45095101030900f0b942c64890914584075000034400741d00194000001c5152860300c010b504141e104007c2900c010058258416001030031046280d540180d260746802c03140c80006020b00c100540039407900d40e0382c0c0c6001c000380100e00c00001c0198013418a02808601c02d090200140c80d07000b0307200c21001a40c805c1d540002400200d218100840e49414030340500000c000301c0386080125103007038941099540340d40408507214042d50003043c001502e0980b080108000030018025 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 259087805 1250 259086555 259086571
    0x60a050a030609050a050d020c040e06060a1206020408030d140a060605161a070306170610120f060504080d060602060402060702010807050408010212070e0607030804060c03020c06130b0907140603 86
    0x1c01700c0b9964455090461903100d03103002d030308005880c4110381054002c1c1ca02040c0002c0103481e843c40c040c0300140c1d0b501c3c02402a4110010329020100c20002d4a604480140c00410100d94403114000700c240040c100318080621660006c1010464503403182c09214140c501c152155814801140240103042d8103030042510703510590500c1020104018034014004e00c2c550f80c0210701ca50820240301361306c41118051b02c3d100d9100f5010005080480d01c002002e0b1141c090800c40e121502e030806c220302c880c40c0035026160502d8803050108200c0208010402108090300030311210341e6413601684c4614088070040d40000c0200100c40044d0f22844196038001ea0b0b5082041c01d054a50141c42d0881c1c019020709402803260406000827203821043e503605940b0111002e0b450900190307001480380a015100a000702e80b2004a00b8086000ea0140c0790304071442400c48803207140c46149100c0c041351102e419250034107017501007481c000011601500741c3d504450041c45a1004074103001c1c3c50351004002032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 259089055 1250 259087805 259087813
    0x9100f080a0b041404050321090d050a03060504020d0f0e0c060d0228050c01110403081e040518010e010b07120503041106070f030e0a082e110d05060a050a03060905 72
    0x1360100c00311504150003940034100560321100d441c1c10441c02d0650020211043c3d9000b1410031031040300c000b4070412402190b15002d42c5502e82e40e0740c00c0c2c0c0503001c42d4100e964014000309450200590750783c0b000580b219004014800030404400fa6500c81d2140090560014401c2201611aa07070f10b40040000360311411040c40003031440400d500c6102c600d01c9520001510004216100301401d011b9400b0010685020350b19241c51940c0e900c04a1244514103012800900d81000388505c00b40d098400038107010302403412402c0d007030304045800002402698608071007400040391400360802580c0e42c042d4800c01014428100003025200c1703403c0100b08841981d94126444a02c0d202c04010303120003449100b0354603400013207103005002d030b0300d80603441c50003503003008001c01c03c0300d2001600d5940c100d14050048070413101504400d040101146424801cae605220141c0000f0103418000c3c00c0c20690520208441d440d0385041207501d081520907242d008200303101c05c0c404204241d0203200d600e44198115 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 259090305 1250 259089055 259089071
    0xf0a030218181f050f0f1503040b010315141303090308040f06090906030c030f0c092c0a05060a0905032811010b03030f030711010609050114040b030706260c09100f080a0b04 76
    0x611090b88c0304540445550540c0401081042014003160300f264500c40020300c0005515450544448001002004a810310090080c181805401820003864100e260280e407152200c40207142d1294030703c205400a0000c80000518101ea0302c1250103907079110196448240c50f5880d120b0801580030415113a02c45485800141cdc685180f00360f02c3d6051444a1041d18070328402c0400708450800c22a510268020342c40500005102240c050fa104991900020f40140c460a10500c1c1d80a988048107a81c44440714400c0d40b0018081c0802068080340c1c0c405488105160740142a00c0c0c449115981580c0140704100c102220400910f500040030300d00034030ba01e96100d140f00d00352500c0c0e501c0b900b0410b0307075540148114880301003c0c0c69000d90a4074140301c010741500c042503841415202d0642000004e0981c1441c10b094101c0c8914100c00b040101101c0d4100700072822241e83c00320412500c0348035000001c445940c021001e50307008542e40e849003049a80c07000100005000714075203076540680e5504074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 259091555 1250 259090305 259090339
    0x303020c10050702011401140f042007110306070212030121050d1211090d060c030e0607020c031509060612030f04030b0a0b060f0a030218181f050f0f 66
    0x2582d40b08492950001c20320492549645140340710603048803030741c885403000486040d16295001c004800301a20002555a091034400c8e8010f03600c1c8082c0e40107544006505000e1024003880540002c0e001c40c1070302c0254944541c160b9a450024012000141c418070040199141080981c4421a03540403140c00c9a1102ea0720307a03041102051010010075481014003000c1205071207420000954010001e292a2001001440f152400ca000078401a2120380074500103129330440040500b130002200d5070b6082410300a5201c000403081c0501a00c134032090041c03900344c1b111030603003c0c1c09075402500d8103403200d50a100d005680c201101c400b510003003004009568035040240b00031400b030795900180341040d4903480203403000002e00510a85051001d55800c00c101c07806c50391108154240103a4540c161940600910b09280c50b07594403600c0300c51a5202c0c542104855803042400550301400d646a5110b00442049140201c94002e2454401d0090728109100901510034006000a4064040800c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 259092805 1250 259091555 259091561
    0x3040507050a091505010302040b0d0b03070f170d080601091715091f060501210b09010311010e010914151b0c010906030603020102032a07080d09060c050a0303020c10 73
    0xc0081d48040d40c4900c0400c21400040c104c0014141c2441e05501e02850840c00a42d1405410143c4442d00d07030b2500c0c1c04410340d40c1080144c006014102016200c1681c0c1c0f25220041d0000040c1105580503404103030450300c1c820500c1e64031408050312440c01060a043d08a42040600300e040301040c8111001d007a1100030094006101d0b1040200401d005000111540c17211083d0782c0b90b20032468103200c000c2c03105130303080049007a0700303030103400b400c1c0740945100d40080240805040300e41c1c010400d400080244198603004c820758140030b803500c0e10210114001103800001520500e02c2150617002e00b903070b171403820030650100712a04c628030328204900601a4500480424a11103050b0f2017180030604550308481075a00500c0c1501703080102600d5500041e4880c0700d401429030340d11604140da4041c5850071581b03504020740c00011a9055910390704401d41c3d40303120380e03886404600140340000703030b071845081641900d5900c000500030510440c4e4080c0d02940000740c11031040d004a21002d220505244 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 259094055 1250 259092805 259092809
    0x22701140c15091015180c050f070303020301050103061d010e060607050709090308180d0c08070f0f0201110a050a06020c15090307060c050a021b060d020a05070b0a0603150203040507050a 82
    0x1d000b070300b580c0300448030b000200c5d122101c800c0c40345920a030042200c0e00c5150001182c8a8103024003007001c0400d42e500303d0b2980b08083c1064101d00b8080348800901d585540918140c030307001c1e01c04010319629450368022080b0b503c400d114046094030300602058214410060308520003910440c10076401380d440310b08118113074100070410780ea10110007040c10b03400700300c594100b000200300e06040c2c4864000c903900c2e01941c83c07000080c408001c060004010081040f02e000d66042100c8000c1c40d0400d16185502e6010034905a000609904a50007842404255100d48540c0003004024480d05983c44101940106082c460f80c0e0040d4080407550800d5020618482c04060000d15034404007490100c0880c0c0d00d044509042000a101000c11581c0005e41c4061403403020517040c0c01c413003c0307d001076150311444100c9850f140c0082080481c0c07903001400b07412054402c41d2508200c2c0d65006100c4e0440b480380c44007901410b491203801940030020740c000d54105004030188c070040b0b42c50714042000d00340305e6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 259095305 1250 259094055 259094071
    0x31b0c0213063003020703140a0c06020f06070504060f03051003020306070210050f010e0f28060602070503061303110703020901060e0f180c0a0e04050a022701140c15 73
    0x4240309450411405031043d0701c000418841c00c049650985000356902240e0000420000c00d8512220b00d03d0802c01c410741c1c0442d07104c40e02880c01c8ae01d8103030082d10b03400e506040c051a40304200100e000e040c0910259420349407142d03102c420700c122a0300114040e000c058038441006514003008005a2800e2261074451207440c1c0081030710003a2103460380308440c0000c10303e07000e00d80090010702036806801c843c143c100c11220304070270268481440181903100c110750304280300700903904205598492600720b41d048135042d809079102d280d03481c1d05241d08c0b1041140c2899500304200300c0e400001c1d000760380c4800070300c1d1b00004032290540c030b07580031a940c52002e800040210305200240b81d454a409120312503411402d40d5403034884426080800a84140603082d2402c120b40440c100d44603522a08440b056842c00510a004504125068000a6011342040b5801204184c55980101c1080030303102030991060351201c4000c0c10150481d8015003000ca0010310034081c200c1c41c0051100c081c0402030240c0c140d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 259096555 1250 259095305 259095329
    0x1b130c0216090501030b0c0d0e06040605060a0506070c06111e01021e0702010c020f180c09040e1504080a1b0b1603110d0203100302060f19031b0c021306 67
    0x16401c251515111548150350302420900140001817400b020543c0200f107158000e0741301e805254031100a4400c1815050262281c1010002032000c1904518040d0505403030180420342c42d0401e0069510030158040c0810140d4082008064450101030f048504104141c412901c0c0300b601d00003440103c00c0380c07051580c0d00454001d00d0444c9499171660400403013480249040d2650340080d05003c5038142c042d100300c6007941e45141503151a1030000400750700400445c42440c04068282c119086682041c0c0a00e281641128440e2000110001000307091800000507542d140e4032b000315544203200b03a40410031b00c039010140c42c0d1002c00d0b034020034521030764015119203014081c03c40010128500c4600b01800d00d1441c04510042d40c0448580e46403210000d65030b991004110b10f4030102c25031009401c0307140092007d00c00c80d5a034020780109058a2410b20850440503002c0b8103540c4409a25109952482c40005060703011f17410a1400d5403005e416000f815145119840c113340d00ea611180080740 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 259097805 1250 259096555 259096573
    0x807030503060a0f080a0b04021302040b0403060507020307020a12032609010b040515010e0a15020607090603050403090501050a0e0411041d0c0702090901020d0f020a030e0703051b130c02 82
    0x140402040d80a001001412244076245c00840d81e03071a01c020101a1642a014010806644403502c00000d036501d00c2c04107560b5983e5881155803254481d20041d00d00514107070109403028408011200c00640040195040608011820650099400c0114140111910751090b0881503410420032080c645070801518500b0300103190031348a00c1240b043c800e03403805040003802000d01a0a5a0708030080c84e001050146c103201195050195411010040001c10400d001e0540d00240c0305200d03102c6c40d55030030800c682d41c61090342605d006480040108840300d9050045501c2100a41521441407405422020a800206003254440d80d0b005024100000b818000614070410300d40c1c2d0305542082d4108245043c201140d041d00403150002c2c410007030840410520282501640c1625a841070100100e80811248500030340c07103640040082401c2c5408000d0340711000c40c41c80116508080034003100090010b01c01e800c03441d116800c1e0b500800d20b4001404041c464456618065400d40040407014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 259099055 1250 259097805 259097809
    0x120702010b0d1419052e0e010504170307050703031a09180706021216050304230a0e160503060a1a070501050c03070f03020706060b0c100606110307020d050703080703050306 76
    0x220b134109989241000c50801c000041c00000d1800f000d2203031011103005076086e0b01c6038022525548000b0700d028a090002004c0118419400070340158405c0e0307242507c041c01d40d05602c6c4507000840d0310102062080c44601c020034044d82004401c000c0c0d141d05031105541020014246a01c2550909aa05604405010085810030480e000727000310780014014483c01c0e541e14525489500c000f8050780020307000348010040e080069a01410030104240521551581c4d05852140c00d01c1c4001d01c0342c01c0400000070344808025100340203d201000f946d800742c0c40c08800399120f9002410a641160b1a01301c0094008119201405e480c2400c05e8040d40e40c018600f001ca0940d0005006250600d13020010f20800c41d03000b18481e80305140504025885e000385060038001040294006441d2507800100c0c80101000410b402c032500e454448100409920344c982103034490351400204403103520401425001d4600300000f100703020700c40c0701220b070113075182d0350364400d203801654045020403404001e01100e8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 259100305 1250 259099055 259099063
    0x1c03031d0c090c1e1909050f0907230705161a03131109040302010f060602061506071110110105340309021009030c0504050c120702010b0d14 62
    0x2034100032000301205040100000c0c0e1100026100289059001900d800021a00910070b902c00c3c0c8686202038881003501c80c035403401c0c1424a00716000903200c0c000404c440c5012502484844805001d100a130f0741d42440030b40e8041c0808407200303803141d250b01010004c10244402412500d03c5400505800c1d0501d030410324055003250090040640740f00f40204152400b03a00340d0b42c1c0300442d1b5035241d40c10304890420640c3d1082c807120705500041d00204120a0607015040300203a1110340c0b5042002c00d5888100301e868034412b90b85203c4c4008540c200060a1600341c019002003030241d03c4000034001014002143d40081d41c0b80343c0c0100d0b048540010703c00001380b00b060745c01105102e014150750f00001c01403100c40319140070042d41100f1070690070b190900c254800500c16901405080c1000c005050180010226100455048107032074000b1a40741098050103000f207185422160900110b00d03000018454020100e4045660700d60500c03900d070f80c0e103146001c807a074040d0911002c070100c2001c4103810 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 259101555 1250 259100305 259100351
    0xb031b130f050d05060c0313050a1415010803040513110a09050907020d170a1e061701020415030c180b0a1b110108060f03100209121207060504021c0303 67
    0x4200f000300b0215000c07580c0450619805038042c04541d070f42e035565100403d980d44d0080400b8001e48030741881e40d410002600a40110115842e0860301d141e00d40c400c00c800340910034054910b1541040c8001c00182c01c2025104072034141059000c076265000413001d0b650707a0408074403140000c0c50000b00300698204041380c1d542064140c0f001c0e1038002004000034004103904800c610600d03150a0026440580950000504000c1124445040181c640e46103001c1c000d42d005000801912918201009005100f107900f1621400c864040d44e800c4004280c0091180082440511100c0300d0b404111041500d800809021072400940c1c80c0c68405c1801054005901011035a1003919566100415651004d408184509280030900c0d9607400c0d012a81480654080503014821191035184060f0544c0182240c03410070345214291740d0003241c2141d03680320041c8500100500412045001c03c0807a01701940c842d00184c250700407000c803400000a2081c90950039000030b6a0350001240050a00ca80211 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 259102805 1250 259101555 259101559
    0x6011401090b0306090a110a0809160302030a0219050a030606300f060f0e03070b06061911070b0c06070914032a10110c01020d090b031b130f05 63
    0x16410544000e82d030780b1010705164401c00102c1d0004003d00d082d5006240402034a5500d40e46660303180340042e20341c3d0302c161000c4405000d460920110300f0890aa0342d400c80b03400030014950b00d074198003400510051120301d031943c040b5070030b0003049945410b014030000714469440024902e2070003a8100101000501c0100310030110300c0144003100310341580e00c413100d4100740d05100004c0c461034140c00909900c586a400241040d03200d02c825440400501402406042c1c2c11049507240d41c104501882400f00101c01c1e005991090075105c1d2140c6d9030241410030307040c21109925103d010300c0d081600b201c1250b076500d038000810441ea0a030301442c81c000074001c4450389030048110200090f01d4882040d0384840c008050001c0c100c68108980d0540010500540329100720024000f0051038a001003a41001902c600b8012402d2035100044040d40140c4c20307501c2801d690300f002012500795002604008940701c00d0700000140d082c10310000c100f903580840c0264000c40c6480409800540307654003040c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 259104055 1250 259102805 259102817
    0xc0815070c03031a10120e0a0302032a03030c0a12060b0405100c0606080102091008190b010e040e0102030907080703050601270204060c111c021c1406011401 69
    0x2400d603820908030210749501d400c0200e2200880b00c1c0400c94100710f441600c1e4444e0b410741c4542c070400e81100744d0a82000b110b502c01c0c0241d50030446d00b20341e02d0440c3c040040042c1c0c030801c203541481003013078003441c1c440c900c1803c03c4102d026008620b520b1500103880940b6540d400059610b58103800001403041030b02c2c1f5090512030a850706c1c038000003074041c52188038040d00c0e880c00324042c4c82c0d205d003103850303a020341c849400c000440c2c942c900e241c000d40001c3c207043d000340b0b410984c0030001030165681342d00c02c00141842400801d611400a03000d071511420650601200c2022040d40b0341c1d482c061b01400c2c52503040016106c1c605400e0251400c5815400000c59810240c403d00109a022880e1070560700000180180e0542c07a03820002107401451085010900c089408155a5803051004410600030f03000c960002480004011181010100e25807440d5401a111401801c01800201001000301484c446c0d840702740d1660b40b481d8030000000c4403550801c100522500190219241042c0c4080c40c0170 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 259105305 1250 259104055 259104061
    0x5010905070f050c01180f0201020105060d0b1530120705030f3603070506040e060f0102030c0109061d120f03060303130e0402011211070b040c030506040c0815 70
    0x1400090200694000300400051304002140c003d400901b161a808040d83e00355031114103000000300c1e1003880403401542441d021801a2420001c141481500031407882c41907103400003a0550351500544840d0040c8031001600c001030b088051075002c4a404851840c449600845c1d001d060001926250260403400d01c80c22011075000025524400e15200045940305006041c01690b0000c0000521482251526808601000d5044842e500c0c6040d001c681415481e5000c1103114021401440c2c2c0800804000600c00d1420400d0140d0030704060040c0c070b2508801c00041802d550204006880d082d03102c200442c02804860880c000c5041114050034400c0d0301e090700b01145110340380c10b0f60808070300480031510554040c02256950603c0005900744141d4606113410b04070812a800c1e800709880c0d16088002074813a0007400802030444800d540b5040341d40e0340300f0025890180054401d06511000880000c5003088800d0189014110b604c0d1a64036200c1e0716450940c040e801660154100001c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 259106555 1250 259105305 259105307
    0xe0106020c0607020a03020a080a0507050604180c030b120c03060f09030702010c0c12150b0f090c0d021b061906050117061810090c0302030c0708070503040b19030501090507 76
    0x71900c508441154160b80d01c24050000520889030707a00003030342c49015440005030100c40080c0c10a241ea20500c140d0700b020343da50040200d107002e0b601c5440c070500380920f440080c1036500d9000030f11440c1c0702d00b40002c40e0201900814850f0031001002202c1d0f80c0078900c00c0d090791400300901d5601c4601c140d4a0111780c070308140070359164018010028180100040b01400700101580d0b03000180ca05005021003425660410703011860405060076960b5252201e05002030401c00044a0300d4240a4102e03e01c0d07460b0b40c0300c0c0032841e502500c0030120b143c1d070a0196920710f0042aa070321508800d15401440d40c0c0c01c1c03500c490f141c8600c21307400e6111428035150301000700ea42c10821001c10307100c040b00303440b0407903503044e02040c01041c003440c0c10b4480407034000400c0b820784550702120054490b02c4900300030b030a040280903400c904c019918072011140c144a0680001c0045e4000c0880300e104206036810a55250325400664200881c82c0e07070310303034800c031042003000c2d6151207000d0040000440502040c00d004030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 259107805 1250 259106555 259106563
    0x20417030301030f021903150207030e010206040b04140c0a080304050405010f120308060409081b0c03010606080f1003080c03041a0301050d03080601020313030c18051b16020409030c0c0e010602 85
    0x200034003c2003100c45440d01c0c4811081b10307100075a004a00784011100081180c0c00075442071130300f03c02003941044900700d01d520000e0704600c140d40c810126a95500c940c0c490649007044105442450712030403846d140c40361a200e103650010500c0d54000c5884505000810060700d005810000c03025214440420160403100304240303400b03801d0300f4050b03c56114600403501901c40000d001d02003507000502e22040c04201071262807504042803e4a241701d4071441050309035a2240b0454000446507000701d0308010044035641d41081e4101072036404c40f55240e40b0700b00c7e1600940070254554001050400119160b96400301d4a402444140d5203158105030002c0d01a00d4181c10150130015408005000c0e64003c100700c40600c0351008654900a40d02d182145800c2c4990180140c00c0c11010519400c03400c01d4090b03c0d005020880300f00425140006d440507007900304260510208110a28a1026840350300c650030540d406070b030311514038062906000003402640c0e40602400500c0e100100141c582c081 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 259109055 1250 259107805 259107833
    0xa0b040902060409050a0603061d01110a020327030601030b070201050c071e11150a140a09030201111c030207140a120c050c060309010b0901090c0503010501080c16030302041703030103 81
    0x4c2d4000a07191900e620580c01040f454200401e41c074a0b10032007180240c0c640502c2d07203800c08140024000b03891102c034210428040c011104026074000e01220340429056810a07010b20031070201415240c19600c0001e15046007a130043e9000d111101c14030003865828010b09520000d01c28200340360800582c2c55451204c00355101140000c240b203110810401c402030b00180030f00d00102181024600c4002d60021a40580081e401103030f0341c1c0d200482e408540c034080d125001c00540310000d503286160010b5171410014100035441e801028061601c0e41c840007020040a281c554005840d0341c920f02e055101601000d90300f102662244400000282403003640102121191400511410309460640c1c078050928840c60751060001c0104484003c5c1544852403005080300e10100c9640e03503a5920302110510340c050000510100014421940119401d503085000d28030050b107405600081040a071010364001c070b0001e900014104515404070900341050703003145002e98550752540d41c0e5120380d10108 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 259110305 1250 259109055 259109069
    0xf021c09031101030902131e051504050c1216090e040b0a0e0109080c101107030e040504140105040c06030f0b0a1208043c150e030f03120a0b0409020604 67
    0x1d16000000ba074884e4010b8107400340d001d007414088000f00003000f00640300c031748900a444688071143c607031000c2c2c450050500901100c2180000f10041c0c006100c05000c0c000e0141380c18180c2000200da80c0c9498016035441420890100300c04040c90580040c240401ca50102c0300e4400120180008076100100ca55086410b21000190b1020206441d078058488a20301410030500402e0f4000e12100209002106030b00120741049001c08036969516180220a00a4005024440e10781e0844c14940e10a6400c50300403112020002200c05506007501c1c003c503821600501c0c00300d41000070384d4041c02540c1d8440c007840020b0144400c1c85000c103440d800140301d0300c1168140440c202080c022240c00b12009000407481203100e21507103914410038000c0c40c100e00c000c801c103c1110710104905912541c003c0d070b01e0b1810f40003600284504200e80c000c00f484180c507414040e010764001210000c00040c208880b031012012040d00d0291000d03c201c81e508001907016a052a40c00030050350b50f42d04071340964402b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 259111555 1250 259110305 259110323
    0x360901090204060b191d0a061106130b0f04150c0c060b01020714270124020307080a081801061203181d0a06080610031b06050301090207020111010207030f021c0903 72
    0x400c0d54054146c0c89202e504481144008602c043e401002c001d682c000000840b500c549a000301e002000e080c04c40003402c841740c4a00814400c407140918940c01a02808588602503414400982100c1260342200c01040d101750107482081124000c0940c001ca00740080c03d003e900d803030002c11640200c180914400d020240902d089100c58100c4514881c0d0040440120b030340c0c48808060a0f81c0071250b6104052090301e4054044a100004480d5840c1d07004010a00f0136449000c182c51881f0702810080b44440001d0380c3c4800240244100c03001400f502c0108200b000301401c000e0181c19410215908000011800340403079414a001100b402c0780740c1c1d0b8003001e59955808560010030268011a541340a0502840700c0c081002500c4425240643c802e44031100c803034151010840114884c01d8086001440100041941c2c0da0107400d804e80107041c0340c00c018058002040c01ca0f80600022004100201c2106170650746c100710705810742e40164035a4001b004040c00c0a4220004c41c400105000c01c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 259112805 1250 259111555 259111577
    0x40b01030906050a0c02070b04150503040f060f0c0e03120403030c03260106090603020c0a1b050301021b0c010c03052706030702071a0702360901090204060b19 70
    0x4425032080c084075070040d0040186081c20807200019200f10b81d15800148900e484c0860b6a0400d141140c04945203008000000954110103503001d80000b801902c0203502c104880d80414164043e00f86816615a400200c1d028090b001509200c0c003410710300c3c001c1d407041c45113080003070010381150240c80e0182440c0740b141c00540b0b030483d0b58205264403900000d0082c0c07141400c0f4030301c0e0519a03050b00c8440d114158007545441c4120101d003d0100d8000090340019031140200e038050010244050302034800e016080d403240d0202e405c0e6032004203180d01ca0210390b0f0103a00c02c00d9050140e0f00c0840c00c2440d010b5441c10041d10300078035a0203569200101040528580d10990908a0701e8084440026040c580c6903d0074030000381d01c2d4070040c441d00354002100e1022001a060b140f0807030710042ea008029480c0301140ca190390010b424007241c144461500c071342804816034200c10800d07208100003000460034000c030f80f050000352511944403a004001c02d01a542c00c00344442003d41003000d0500c0c280d0340c992 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 259114055 1250 259112805 259112807
    0x1a0403020d060e0d121d060f0a0608011d010b0102011815060906060e010e090603030d02220b1e16020609030c1203040302010801081c050a03020f0d06081911040b01 72
    0x101c0320700b942e80c3c210322070320918101440d0010b16035010011101e6040103c45902600286940040484c044481e080540080d994500d42c0f10f07050740008030324400003100e98030f0f00e820500712200103c04208802c2d1138020380a202109001d0b115030b2003400c0c03000380701c4c100c0c86144100803015124002001c410102112940b00d010907801200208400d0b8806d0040315a103c00c05440c80d000401175074000f4401380808822424510702c110701808028008501d00590640c3c0d400080d04120302d1030b00341610440030007040c200c8558510019000440000e03958490007000d60740014040315407421105010702c00624040c0810707141500c10750701501c02e02c0d540c0342c90302e0010b41440003848a05900c205c2c00c03018100c031407174004080d100f568801c0c0c0340c00003140d1f00c82182c1c541d1002c900d0300b000f440407031100c0892141c1d807140c00a40341c6a0341900340907090400f1491003540340e411504030280d050fa9200b0b000c01c403615041284012008840809540040b05c94484a01840d40203086900072a281c3c49120116 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 259115305 1250 259114055 259114061
    0xc06070302030f1602090a05010b090607061d16090c0909020a020a020415150302040506071e0b010303030906110705070e0c04120506100515030402011d190509011a0403020d06 77
    0x2031464581c00384c0e6200e5201101410503600d104003a03009003659000102d5901861107918103a6022010340350802ca840f41c1044940d43c0b100e80d017295025120440c00021040717880c0048038140c1c02d140179000500c15a0807410f5449401d6100d4900d00d4208214080002d82002c7c41d00141c41440d100541d8407803c0d038a00f0380c5840342c141d100a41081c0b40c894403441102080b142901903d140042030740d042e0b040b485048042e40039030b02030241d102c0b800b0080840000e0f134001d048039919060703800c1103030712000d240c031001e1880d4801d80c002d4000c41c2e1500e9001c07041140b280716100042800c184203a0400c2c089494061b5500028003480c40024180c50210340d1001741c1a090358020100c464421311420014a8881d89400094424454400c5140d0300480d10380b4140312984842c00c1d222003070904542da680c0044980c5007040340001d14441c146001c07071495464005580c0c450301c001602d604c47c00c80c5090188400c1c094140d0001c2042c40c800c01e190840d45903010f0803502100c1c0c048440200081103406c0c08001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 259116555 1250 259115305 259115317
    0x33405210f0414010c092603030705190305090c0411040b0a03060306050901020f0d0b040207020904060b0f060f0d0e0c0d0f060f0504170c0c0901080f0f0a03020c0607030203 76
    0x10884038100400100c001140754411072080750100120380a0091460030b84010103494400704d078081d941800901c0c0e11140b4001c1170f8000c420340055000e1104855401c46d401552a00b0010340006221604482e540850700046c000c60316003001289407803509191155070002d40c0d648240d860718101c0c5c0440c0007500a80b03010f014082c1c0902d40e540881c1c0380c0038000f80403a00c0200c8199003420002280e0b0708042c820382c3e040030308010b28140b501c000c80e42c80c00700900c0640a07141d0300c55424054080503884400c8103e129a12440700000c1191020703040080010380c2250091240c2d2041104c00e10b0084001d09441c2c15007103803040455030f0300750ba200450070302c1c4c85a0201e40d048403c008040007840840715075209890700a0a08008001c01c251080d02640c004442c060b00c440c100f0743c902c0900300e040c6401004015200c0043e01c1c001c000344000158064030aa00c060850b42c02405490b074204418040d17540d1a051070300003008000016034010b92691303071260342188030b80c001080c2c00d000c0c18024002c07502 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 259117805 1250 259116555 259116607
    0x4030905041a03060c0c0a1202070b0a0504090f0b03190314031303090b04030302070b091908030306040b040b0901120f0b0c0a09060c02030a020f0d080c03033405 71
    0xc00200d19074003214611000414a2091140b0744c04214041e504004840b00042e9150190110400300c3d1501030b24450084000c4085201d904d10010300d00030100050042216180d40d42e540e281d181003038950039a0a41841c0c8a0024900a100b49040d600007500607184c0701c041d03044858143d610308068400030940100700c80d044030000104803100b81c403081100c1c5050304c01c1d111244182d888506254480c0100e0000601692100c44d090280d036600001030034000c000246540c0c01c00b69400940e1300d2141413a8400d104950000c81446143e00d080e0084902e4048207079401c03c94030601100092200606100d1103500c011801c04103070912a03041d0803404841d4100101c01244d0070400e1030220690b004240303280002d0712645001c102503120f041c6019070107400500038408100716400300b0244a090503942d907032052020445400159000002d8100742c05110003454503440d100442d041d0070410741c0301000d4081c21081769071564102640407041c07044d06a1414603110f0909500c50103841c1d070f404010302 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 259119055 1250 259117805 259117811
    0x70903030e041d0a020910060c020103110d091a0a18060203070c12180b0c0307120905220c0314190b0904050f0c22020d0603060204060f080f0705030f0403090504 71
    0x8400440008841d141135100355065001503940441365202c8070101c1c026480041d0842220001640c800c1d04440034920360245001c0c98030440d03010301d03030031100c4106085820700a500c40580c03611900d428040d03071080e4034000602040c0c98049500103c05840c1d20000c103810760220114860704c1c842c0304405040c44d03000e41d10300554400c80c0300140c0307048120752410411758070141000c2110f010040a5070241400342c0300450600106c0d54584210080c10420303c01004040080000c080d07554441d0b1406000840c4401e12610340d941b14031720b041d6001070200a0505040144001c480e0300340702c0c00c103580916141c0400b24289440b1003200b025100c000300e03450303111a01400b40400d10101048003545104084110351980400c4414040840072840000500f031100040021000c02c80d07400401030001210000205107490b0364420f0103d8101d030b004400081c840c03030031450b85103402c401ea06401c0842070007820128508104014640d10006000c1d1a0300d4041c131020504240c01407820a000e0b04000b8018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 259120305 1250 259119055 259119101
    0x80102070f0b1003240b1c060f0903230f13060806030a0c0611120d060f060e030601060e010507020909010e010f1a0d15181103010203070903030e04 65
    0x480718111000e420707540e298a10000c10030700028000303840101c0341d00060880304c44c040803400c0313100101c00d04081070ba102d85400b50b60300e0702d40e144d403440212003900b45402c4024003d00d0030480700701e60300d900500c03a02c0da162a41040101c0d800140041450440864000114081c801c8900081c0a20f40718258101c40100e00b40c0c1002e2580032495081d100c01d03903205501ca41d81c2d2010150303100782c04078016045039840c3c102844201e00c182c243b0000c070b145030700484441c91581380d0030b401690b000442682c00c0e9580d540045c8004150780440d00010009480c1c0007103041000d10003e600c441043c801e000074000300862064083c1d016800381d41246800900340b24161400032000e50281c010502524036079442e0414071744a8010510801d080c007040000c81c80d5500c1c5441c0240f09540d01c2c105000d5820408801024814107250301813480000e80b2000400e210450520b0048100c1044400e042d20a034014003c2140c1c507648052100e0444c1e40515003003040c1c06030034012400801042440b802011541156 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 259121555 1250 259120305 259120313
    0x11060403090e0f0f0a0b01050c0604080315100f0f0e0d050f01060b130b090103090507080f0d11151005030703060b190305030307080901060e010303080f01080c010509011808010207 79
    0x703000032507080b0030000c0c6107540d904180351040c45007110940c4e140302c2d00300c0114400092542c4160010703041070410510308540c65607a00c1c81c00d10111012541c00000004001d4820790b940105030301d020741692140032025036040007400e018107a600d800c040003201c61511120380d1280074101a808000703001590220300b28100130f0740b60000480d070403405600b8008009880d0040c1811039002c0d05001001914007405d00482c200039501c050f030307001e04054132110a8008600f00740900e400030042c040041c00080d81a001160421041080703140510126081d580e044a40220380300c0003010004007020103941eaa004152248503180e00025050310549202108000b0350b51301c980014141101ca60355004045507060104503103d000040003900305102190145000301034060300501078400100d0311a884030480b40481c8800d03402680018980d6041c4002141c0c1860b18074058200d9602601c1c3c02d12150740060158401c0c1141c00f41086540b00f0a04410401c1c1c2d510346010b090b171407000355600d038242c0c10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 259122805 1250 259121555 259121567
    0x91c03060e0f0f070807020a1704090204080a1208040c03030807020a1202071410050702010c1e0308010618031205070f05060c04061403010807090509010f0e010c02071710020a11060403 81
    0x41e0b0701481c0c416200841d012601450320303170348030300e060343e004000e0701801d40d40c2c480f089251440c0480020710203200200d003002e413078000b8002a00491005140c80b2440341003d075612007003c802032051186103014040401d020035541410b0b00d030141410400d9880c2c0c078008920b042c407a1440a0901e0304c114040360b58595001c5803a00458a1a12900307903290103941c10469444658000307000450382c2001a00019402100b5404885000c1c41c0c81001d00d9100c0e910010281c1c00300502200080c40b88001030200a4000c0c5044c194a001610b1200c0e903141903554114419446092250500c140403d10400b040754610b03c0305046584030055680c5820441ea142d0b8641e040b0340130300c00200d403c0688a03080f0380868010703a8100d601d008010440703d490010600018003010709200025500c80c40c2d20244540304d4050801e0555100c0000100c00c00c94034030085c2006c940360840c1d40c80352017080000d0305c00741c00041c14842043c42058016035818120340160380d0030b940480b4035003017802038070104024150001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 259124055 1250 259122805 259122811
    0xd42020f09120d110328050f0c100606050c06010603020d02070c0e100b21040606030b131509020607060b040213030507030303201e0f16050d0503091c03060e0f 70
    0x2032103140c41303040c6a443c0562030780212400c424141e131102078490a00344000c58115032000705401c2640ca00b034207104802c02c0e240c1c030000d96000603901210319800132000700d12035080140f0984c6001c90a007501a0f6125031100418801c040030580c011840000320b08250703040354001c0d42e011114030400d0350ba941190207004000c42c6d42149030b800040000030000c1d84402100c03420341320750300d445030700403680c200078411a00040c00540341c0700d0f910344c0084000396090f0310f068011042c41d8841500c5003136514164000002d0034a05040e12802c000300e80b00141c9982096440b480e81c0044041810311164010034003e01440c40e0b4042c0ca0f1000f060000305001002c68004142d90c000d5400b407122084150303881203031420f0000c2500803040700304040c011800ca80310075003603042c0c142040c079440d00c0900301400100b5006080007012030082c0d81e07805c0082000400a618006002e820300c1415031404c03040580e00c4050003940410695002c0400c00c0c5090701c80d80c000300141c42c100103100c0d4141400428891541000c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 259125305 1250 259124055 259124057
    0x604080a05060c0a0915140301031b0602011a01050d23040b0a0504020906010c02012c1306060906050c0106080607080703050a27060204050d42020f09120d 68
    0x190118000d0f074100030490b05681d00310b031a60300c3c03114a00b0b01030f0300d034006400a2070400c00070101903c3c0d1400a4540045008500901110221000c10a0210030031707030045d0300050a41e0300d84240b00b91450300300c101d01c410005007420840d4650310002e5140380039103070041001824008194611040d410350000d000d008a00031202403110390b4030b4141100490301c00b0341d00a584940ca80000a940e90b12505103402118810b01d4080e00c1001c4124245c0c06d56841d400720007050220342c804a50700ca003021440b61044d00030449040c0040341ca01000a40064010702500040200000300c8515040c000d402034802095000200c1e41c0918180c230004200403425100d443c002070515001c1070201c45a030041c00110320a00310a589101a84a054460304241d1030003100c1c03050b000e000c0003d02da03550002103070020b405100842100e01141442a80003036951076217940e003805a620507a50741020b07840480340c505412100590b40c0810240b040c1c0180079190301d00741d2201903c0c0340b9810200c2d01140400c008441 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 259126555 1250 259125305 259125313
    0x50a08060f07050f250506010f06020d05190f1704050c0108010e0601021c020a05010e0a03020708030f032208130f05010f2c030a06061802041508090c0604080a05 71
    0x4a000880f07452041002e0030381800d41c103014020f080220303c08880401c0c00044641917089207140c0c1e890341410426400350060010300c0804002c00c1d601401000d070aa004d86c50454502880c09020320340e02d201419044081042c544d07000101c85000700c43c184541e0a8581d03025445182c64500706aa5840300103620b40080d0b1004000110121200185401034605801414410400c20003800041403001d81050440c400c001130800895020f01c03039a401c1011800141c4070140040c08d0103880c0c80d0300b070f502c101c040754130401c0a121903402e0803050300d400201000903504883da03158681d4038540c0c1d46c22000f81c5221000182c0903c1c5207046401c0d4070440b02041d03189181140d40c0c600548100c143c0c007400602051a07002c0880001240f00b000407c19020740007181800000a40402c1c680100070780100e42c000d90f01e8006000140b2802d003052640188070f00203514041c10000d102e00750110f00c1d1080070500c0304000c0864840d200500a4112289000c0d1815845d96991094140d40f64030f111410b4036180a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 259127805 1250 259126555 259126561
    0x20316050a05010519030903030213060e040c020601051804030c08030c13050f0d0609080706050106080f0906070509090a061e050a0b04050609060313020306070f0305060118090c09050a08060f 84
    0x4011010b17501c0031981220b41c0070304805804015405044d16010407001c06a0811207002410040807006024140c107940c0c4100c0452101d084c4011585001e0341d403000c0d903109400412142e500e1814105154400c040001030342d071983d1906490200d14548005c001000110801c200e12100d40050301c11184a840000445a40c03501809503100c03030111a99045115074001101081c0d494020041051103810054a8100c242e1110401c840e001e0f004000040c42c04028010000340807184240c000144d800540b12505001c40040c21910502080d14007aa0040b00000d0f0124000d0344810300402c82c100d0480380c0311127622600c4030520070340e01410307208503850071000c2616280c080c10740e0191000034104c146000304480412042d50001043c80d4450350488100d44010388040c40f0003800317110300751500070301c80d481c1c0100a400e458004005a0410030301007520080d0310208c40c44042258078484000411240e054401c89000c207840d0011030304100d00300c0c8001100306001481d180704e003070452401203c0351 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 259129055 1250 259127805 259127807
    0x60f040221060606160b04030810090605010203030103023304082a01030e0f0109060f050a05060f10110303010806011d0108030a0e0a031e050118032307020316050a0501 74
    0x20400010310071070741d10040c000b403418204072004180d07000d28100040b40c40341081c2d4070102503000032901180040d401e401170008550341a5201400380000500601c881400c09000035546d0005220183c0f0902c2c10400c441c4230740e041e1080c08500d120348801030b9504010203129a00d4140e0180c4540e0345c4074414890f440701c041c900184281c500366842c00c101d0810425407001100500b03201415440b40b801565404040c9050074401c11480510481000c5241c00a1081c40303001c0719401410f680e90141058100282c623a0b9040c00c01807443d8003120b403414801c4ac20201182e6030500c0700340801c2184800000440d0716000011094102ca4402c681d9101040441c130006e21024000e00c40c1d445564070500c610f0100c1c5001da2603d404505010740b4040040c0c1c0e50b625103e400480049509269000201007031050000030f01070041910048049002e00c91015a03004000110040484040e18820150b4490550301c01044516140c0c005040f107004041036041c000f0144281e22566102da580c0040010b903035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 259130305 1250 259129055 259129099
    0x61401090e1323010e10020703051c0f0207080c011d030403060507032a090602032109010b10080916060507110307030204181506030c0b0a050c060f0402 67
    0x611014046440709448002000b071040030303614012507000207040010340b1000c0c0303002e52211030704140d003001181501000c8065420003180500020560340104040008207030020121004501c603048069910a4407001c400020020001138030040c900004400050090030009000744000c0c0c4c0c030003008003495503004d01c89a0400100302e001641c0060200308082600343d4801c584c040b010b81000304003880c0c1380e0b19881003407220100d030f58688082030b070b00ea0b500aa8002142005001a80015032408041c0c0c9001c0c5e4481b000540340405000c0c00000142c80320400f90000d116981c1c018140300241d900005014104400441d00040325114003900140c1002c0b43d1981c0074100c071115260149000d640e5250300c20702c0110303032a0258061103042c41c000b006843d00c1c4038403000c184050f51500c40306009844d104403000d90518511217024141402803011070308501d00802140e03580780c1c030a503a815800c5800c0e5910b0140140d10b1549010b80402c0ac256804125003842c131851003224011001d4500c0b880140304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 259131555 1250 259130305 259130309
    0xb061239040204030b060d0609050d11011b02060a090614070c29070509030109300311091c08040f0e060607051c020a0213021e0c030f03060406030506090106140109 72
    0x681171060100b4201c0c1400b0000305c010390300443c1701041c1a0125180d191810640408000000f51301c1c8003030604801c406e200d015248070340074462020320604a10000d5640360082d00e0211225900d8202c8000c0110316800030b1840d80b800a0350f03045c5441c041401904104060350180d804070010890800c0c0f4043d201800c10f000118940c60041384c3e100e814040752290411511160903640e1b1301c81003804101300300081000b119039640440003001c03c80305c1c01490b00d125440d8990505007491541001c0c200c005003034508505050b035100d9090108071401082d0707031010000180c00301c0c01c00900402e028821030401030035110815401103690b1121014498148101c12000c0c280b50030000c0a444a040136040c103158000c980e204469102c004d50f000240c2100314044041c03c1d8641c0081c0c3c4118005c48009003109040c502500c181c2068051014a43c50344154100d14961f00c00000000342e0a41d1250f01080107582c115049490907d0000c10183c0280b001c4e004819035905241c1c582d416540c402e400c8241 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 259132805 1250 259131555 259131563
    0xc090509011104030804060e0f0d051c0311031b0909010b0a141204110102030d0c0314100609031104060f03031214010807090b1507030801060801080601030b06123904020403 76
    0x890700c0d1802008807a0f02c4d0303020014603800a01c6d10101c40ca4ac2d80d400901030071480c0644081c0600a1000c514115440e81c480710000c2810309109101d901e1031021410b903035115090034901c00c4890034242c0072101d284520f81c401139000c02d0410001c10422800300c0540396511030750322079180c180c40c0010358040601841c084202c1d4400c02d4000140081c00700141c0703060210041c011603042c207240d9900e072400c0d115150012000259910080c105142240c00c034103801096000c50401d02a05004c0c000341071406034000075207410305540c0c5180041e1242d50203e03005180230020800050749070301d8010880140704205504650401d0241421021054240c3e030480c0c449200804981d481c1074049805460019540e40e03001d014600000c070140c0385580180521807282d6104100d03903040c140050501d030410b8002c040039520800041c8001802514000d0b04244210307002d000301c10405003e1072400340007418102c1c41405040c0002760076000700b05c6d034418441c03003054045208660841408202d006501c4050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 259134055 1250 259132805 259132807
    0x306050a060309032a05100e031909030516082b110c0411040617040201021e0f0f01020a090b09030706051b01230f07080c0306010302070c0905090111040308 69
    0xc01e0500990250030214401c0c140010a13410311600c103644810a42c8480c4510b0a00e200c4a00400000f40410004032001c2d100801c250b0000000c115906d0150f4031a08a6072444000300c007000e14042c0b00035a0042d54000c0858145484001010108403030394403540003c0d100740107118461038045251030207415080c0c00c0d2800600e10b1042d04840c900287d207100c0340c02d8010741d07120320016261805068040050451400d40d611f2400302c1c018074000802d034104405040300404d010040c0e034046913550302c541140c1041e17040000040360443c240700c001d90703c0308006e20500c0d5001405200c103401928039204030341c8512070841d54441c5200c40038810100c405030315801404003400380c18010005030428010002a9200b008200c41200d030846402014025404600d1080c415011b4a011644e030b511804500d00c1c0c403024100402d02130003400c3c02402001c1003200220000d0903076480382e815121055040944414040d503542c55803402041e0590b403000d00c0b54245052103129a408004039000c9070b81c080145 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 259135305 1250 259134055 259134059
    0x402030d0f0e04020403080702090906071e050f0a020c100908031c060305030c07082b0c11060409090c0f060f0c020d080a0216050f0f09100306090b0103030f0306050a 73
    0x71690100030711036074014440501c00c0c02c1c0c2c0b0743d03c41c1e1002e04086c40c85079400541d10b400d18010000c0b5450014240c9840d90300440810150560003c4141c015107007110f161180800c0c0075100b540c250150808014641c1000704884000340d500040c420040c030070a44082e00400e00100c01114202c5035401080c00d107510400c150102c0001c10340e98243c01c03489480000651310b889540d00d500310360007e5101d448a0b40028010302458005020049600c00303600b08444520080300030f4046036030700081040301442440790510007880b09081507800b820400402a540e207036141d64114000300a0002c040e00d071700f45d040101089a01407079030b0b04800d07100b49031900414440807d10442b0240c035082401ca0b00f00c80f0b290911400038007018040c18424600c0c1d005014070218540c0944056010380e800244109010450032600f0340719106d5007917507008260faa0005903518490030390303818505640001c140c0c0d40b0b0441d041040c8100310b11914145e0b403180c3d40e001c180f51081c0340100d00f40c1d005030290b251f00007144a01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 259136555 1250 259135305 259135307
    0x190b0105180a03140f0d020105040f060b0f042316020703021507020a14030105060a051f050c06010306050103031b03140d1d01020d0b0402040305120f040e0721050402030d 75
    0x1004201c00004103034110ba19283c1d40d54049208080b55800340035401180254040700c4c040c0241c050300728491008008070b1030181c03510880c0d00c0c40c3c1d010203414107681d2012850f00b0b4031806245142c044000d44240001c0d503032408001c03035502503c0b039101c564540c0c220204610100481805046001950003004c80c1800c54003040170102c058401000a170b070040040d0300040c0ca80303240307000041c0200b40714941c018007d1000c0c9429500002d012a100b504034000900c1669125142c062140000d0503011003a0150340d00151014450340010304654814000000108400c982019042c4d038401d82c6c3c1c02c2d003103a503080030030552007400c0d410003008160b40d0b03221441c40300c841c0c1d80905650903880701c010940c41c0801000b252803104003402401d03c0d03500090300902480550040051240003038404525091450315640d840b550348043c480640180000d079807045c0038041003640c010308010303601c6820b00d0604180c003a101003004280d484c00640041d070b4100b8489401d20a0a20464018028203250000f580c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 259137805 1250 259136555 259136587
    0xc1a07200a08120c21010e010506030910150801020d0903020114131e02090702010903080108030f09120c03071d01090506011d01111204051207050d110402120f190b0105 74
    0x700c90010b280602c1981842064502000013244820f4062151703541404000401c102c2d0580043d4022481041400074050713001501840c090315403180010241c030328032001820740300981d10040c800e40c004600e5141d02e0482d40e0000c840540309030002c00c01021403805600f4030700c100f1102101c00c0740030301c0408070110b003010030015020444001130030619041070b400250034040136102080143e54840e025020550003d50782c501406c8104010b5090078400c40040710300f4402e40c60b00c0c5000b008000040312500404100e500c090030001003d4400c3e241c0c0740c91560701e031082001d1194000c5c00182d000001c0324000c500c02d1500400041e502c0c801003034100c803030100d516181c62f8656410041c0e070b1050082400428010b0207030248182d40790998482c41c0400b0000d903100300e001c0f03103915a001700c1010803c07076a409a680440c0c1d0703445101c0c0342c000d1900100240c000d000d0581d07150340800030b60b0104190128100b80c003a108409000c402ca0324002440c582c0000c41321500016400308c1e104008540c5503a581e00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 259139055 1250 259137805 259137811
    0x6120b040809040f0506040c02010b030d0e0d050106030b090607030212060402162315060a0e1b0f030117010506031209040605040f05071b020901060c1a07200a0812 72
    0x4101c0919080c00d4101050488a5100402049550b5181031041524040c0640140c100c2944024000ea068040c0006e4540e08821150014454032030b050b1882602d5515448a90603009030081003495960b05003580c1c81d10045800e0340e60781c06100c0005140301c1c02071007510351068112a20181550fa032105000095104104000c1c401800c07214003000a001c107904c81c500350b0303481d000400004070100200d501c0c0050302980c0a6072500c0b41000c00c5075640f980c4a9034811508010418441515180b101d224580440d13201000c21000c0007403170f0400703080d560000307504880362403500140071034200305c0301800c03100300ba2907465058100041c21200b042c06400030f032400410003031002403510740c1e9a00050456014001e1901b09540b33400800040c00c0c2c03c131001c441c0ca145002d100d0000501d15138009281411305009000601c19240700130002d1056802d4054130040c2d40f5000b40a15041c0882d0142c0502d902500d0111000c0707139071204034080000407501c1200558010b804506102052680282d601001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 259140305 1250 259139055 259139063
    0xa03082d07050c030910031a0a03080a0516050d0c0209130506061e090a0506010806120601030f06020702101806090e0a11130608010f050109060f0305090c0604030605010f0906120b04 80
    0x34459050941c0d01c41c200285601d689880006119030540b140c2084034400230306080c403a1414000401c0401e914804884c0c2503111031030700d15a2843d2440015014400c40303139001d8281e00c1000054403280b03800c60104ca0200d4001c44040348540c0e208140c241d00c1e100d40c1c1c40300a06e03540050002c40d40d542042c0400300c114040c0301d000d040c0c404982001017078012008031003171a60f464448060104a5800208040d04800184c51900401400301c20542d41c80c0c41c1844020202c80d042c1a8801c03e1141560544030350650082a2521212003072034000c0030400500d43c101600310160000281050041c01601c0444414075104003031036444020803802490880009032450070308110b10b8000c400c1040550000d84041d071541c8000d035040202c01160b0851940105040c000074540070700c0050780000e0348104c000707128540030400769544440c00f4200785680040a40003c00420084104481c54021078140c0300b000d514150260340c3d4201d00c1381656418071a400c0100178003039514010401101402b5030040c00303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 259141555 1250 259140305 259140307
    0x40b01020f01020a05040e0c040509040f1a0a1d0105061e18010f08122110080601080a05101b050a020309060d020a021006031e02120a03082d07050c03 66
    0x103501c01c414260781c4000503c0000490008043c03041c1d0032a54402230700010b650040e1401c0c1814140440c0740544040c0000c2c04c00d800740450320080001d007201c62000c415050102e48204e0910740309130800750101e20013500720400d084a00100094051054501c5510000e0140b50b9200301840f09010701c82c18000816001100070405803d01701c1c40c074514074001d19980d40d24140c41854080d03c1410f00000223b0720010315010082120440214080041420141604150070ba12016038038031803074000360b0120301c00303020303c1000142c030702c1020401d02e9100c1c2c080c00c19190044100380c41a41150000350b010707001d62100740c1c01b41c19018441d00240c46074250600480749032280c0d03c00051001d401010601a07015000031394a65500c3d0b040c0496081459030380300502c403035400d60380c1e41210030940c02c0610b810814891034040544d03890040164400da00b060598504400500b0001c02c00e41046034090031a102a02e43d01c1380c1541c581120800c2d140f00503681454640700c40204448a86c06081f0702303121440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 259142805 1250 259141555 259141573
    0x1f031d060114030d14090103020f071b0914040b01260613020109060e0a03080a030f020f18222a08040323090f01090f090b130902030a02040b0102 64
    0x810156029003410b400d42c0312a9500302d000c1500d0819560014800c02680004980904400b0000e46030340386000d09000da111095400217200d103006a040c081c10503d4100b200000c0a149407138144141c85100c0707000d1080e0f030460b520001402c03805030ba00810800c40180100b1940b010124281464a10704107040c1c0b0050404603a5854a2010740b5849000721490f0040e00c01c640c0c0015020300104017608042406101c508006204505d161001901c0110001406001c140c480c2d4000e0300305014401c001c54070380c0c64100d4504015040030020001d14404880615004c4c5008a02a2000c401032019054404078140758500a06810784a03060042c20ba0b801d010030700305a8601454a549240e51071541d980380500b0001d1035101c21001d20310310800381580c04050b8030080021100100b030162045041000c8140040f03410b80455404001001c41d4464049100c0b50940c028002d5250200ea032070071408844850001103075009040298154000c69108006051680169421460500548255803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 259144055 1250 259142805 259142861
    0x50c06070c0e0702030d053301050d0606090315090804030303090813080c01030605190b070812090706030b030d05070b04380c0a02030406081909030c020f1f03 70
    0xc0b02914040c0c050f82011404404e400c810b440741e158040044004d54003c60320b04000d020300c0000403444040c1e02c0c519642541c0659005000b1541c41040128040100d00da0703518004000d004180411100b0020309544c61584404501803070400d10341090a4501c3c0c00d207540c0d0160300038076000c00b0403100e2080c00c1c801d10b10400740d800c014800902310007001d05840c402e01c600060441c1e0194100d5032107541d0300d11941001070b204440c000c5c1551500500c0541c0c0b9000e0303040c059a603008080d051203030240003904122052030081500c00c1224842d4405001c0c15030200105603c50400041d860b000503402c1c00b810300480c0d0b0006e800fa130410b00440062490000420040b4400582920654242001c1312890341c002a00303c84a150f00012801c901801d0840d0a5802503c1744914441d90040100341008661082c1085440c001c071a4512001000800101d01d000350203030480d10742c113174420a0700d01c4100b005401c01c030320b0610300c05149121690641c640340c0000e500601c90640d140d805191010340a00a0f1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 259145305 1250 259144055 259144079
    0x303031b031504060f090f050702061f080f07030b0901020306010507030f050d0908030108070e01150302030414030304120801061e052a0606030f03070b010e060112021803100603050c06070c 83
    0xc3e000090b00140006e0030b0441e4030050740c80226140401c0c92424040205550380410095003001e2244001d007200307007051003182040c04441d0450f8441e40208582c04010070b10000c4c0c5001124400e450105059a0b1640428202d0100302c03100c50203c0d108000c0c080009214041c60041c441407030820a040192010240045600000085130015000001030142000c20005440103f0010314070110644c100161030321004a1465003200f03040d00403011408010207101da844100400b41c0442e41c0300c1c038203401c0c0000d00090b0320110f2004200d451002055041c82400c8045141d03045842502001025074403c482560021010030120012982910b40480d03c002d40507034803816881c000c2c131590800c0000c040c02c2902030302c00c10029600810011000506c400750356030444a400c00800001e5441900507181c603180f55401140040c40040c04203028202d100c25845144025400c585103008141702d1007040310102d0102900c254003011450905140000c0140413071446002e003100300300ea03503c29242103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 259146555 1250 259145305 259145309
    0xe06070b10170703050703020d0602041205061005090601022d12041805070c080a0201110304080a0f02030319020f0706060e0703180c05010302071b1e050303031b03150406 75
    0x41d01d040d81c1d020003100c14407440310081c41104001600002d407465640030360355038180c440280100303130764030400e801d211195041d1001050100105004a1801d1424540b80c038801c48a181c030b1801034604c0410745d400c00c07129880c0f003403a043c2c004000c40324100c0102500341c145005005c0280300801990301d101c03802072100208118501c1009a12581810f601c1012030300456031001003985000c007007110641d440048100c40c00e41101c10260782d02c204070b5040b0301600d513030030844900920010030b1004101000300184402d8617960381d0380d0300481c010041240c503440f056540890025680c0f09180e07881100e68010464000c1402d807041c40e001c12555540d00780e404550102d032100140070208030f00181c16000b404840d2051000402c0000b1495031a250207000c1b50080398105a804a101d4041207040310b19210442e00c1510b16201c219035400f24004d0741c0207172181c260780360b0120450000da1820000706480c040d0424040014a45100f50070703100d02c0d900010481500101e0a43d1042d03100e0310b07203200e5040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 259147805 1250 259146555 259146571
    0x2120a05011112010b0a09051e100507050606011d0120070b04170705180601020118060f060503011505101707050315010c02030c01081315050121120e06070b 69
    0x5140d05510070f030921030800c140d20041c1080000c100b80807030b42d0381c0100e00d03100790b81084a40c0040600054001002110700b40d204907040381c0f04a1449140c11b4012010703022036442042218a40e07a175240c0112140b00081c0d03c2e5501c40341d0f10082501c11503001702400c918580a01030703c40d481140b018030051406240d039005120b11400040c041c020341c000010001a00000000100070303d84c50700000c0b41c00c1351441c02001d07400305041e00220700a6803003900071a100c0f007203c080005955401d41005002803450b0151071038068a85000024203040c103018004007800b10a8000400034680000e02c0390000d5007040341802c01940d200c03003041c131070801c6194600940440c1c0d0381c40e4603441c2031a92506001d288105450512a9201285006070f800043c02c1c44502c4080c603150400303440d1001845280c4000302e10080030001892100e082c89500c0c0e501041c101c4d240c046039000074559036641c01040b00c220309406850307020440f20005199008150b880c20560010700042e1030440c154682003074200701528855 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 259149055 1250 259147805 259147807
    0x20d050f04020a0e0c070308100b0c0705090106021b0609040b090907090b0a0e0a0c05040510020604060b040207020a0b0307020c130b13060f060c060b0306040c06030f090305040302120a050111 84
    0x2206600308142e00602a1000101100d00b45c01c090329003c0c0c1500860070024100140712001402c80d81c0d5010b80040100504c0c001a5200c03080312205645607a094000d003800342e90708100010341c1c5807000440a80f0020301810150448084d9424410346501c07100703015030030030b488022805c46c5440342c41503140324240301d80191071190305054240045c0c1300940241841155403030014000909400c8003207400160003140000d848246c01c206940c0c0340a0b40d0f0180d640008031302003008545402065451240c0e104140c1041560303051b01c100802c0b4041c40030b001e9000342c4000e80c203202500341c4000071608003c413401211001814140000e030188003030050502c1c1a611100c20001d14100483c41294003d46044188043c81c100901e04c1c0072000248920ac0810482c1d240d80402e0080d03039030141501d00da0240c141c42c160b02e41424500303e4007140e8455800064500719004002142d144101552107901d541c0d80c82c941403450b02045102109403d503821346014944284000400900c104800841c80421403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 259150305 1250 259149055 259149061
    0x10c021c0803041401020405180a1d0307030801050d050a0803100b030c07060507080f06041e020a02070e07050403030c1101030b0901180b06073201050f010906080f0705040f020d050f 80
    0x1036130b0f071100c070003000401d60b00512050100b42ea0702403041c18403074540002580c0d180e0780c514010020f000340156420350180c0b44226100c8210000c4014206c2074080d0311a07082c0ea980c1d5038280f003080740f09000003070800d40104da204d90000391080011600700d030200d203440d0311064407254880c0c850b46c020b0f2480303000b0b0103001507220100a22801440c0c0d03c01801d0500140d02c1c50203103d0310140c2e0800034040c901c619596100006040142c0ca01d14507204802d840454845000f403c01954982160040d81c003420403007400903200c540300310102e03020380707038581c2d101c1b0036024480d0f076480f524400035100c96051645943d4110070a031110000c2034001c2ca01985000410050804e185003101c2c1c46d512414041c0c40c08125072030100b2041c20314100016606c0181c480d5510003443e44207207030022800380d844503500340b03424000804441c54000b810703144407210400002d03070ba40c1c80d00d80e41c440d0040f141c0707040c0d900b00d144100858601540035420450040714050319107001c040d21001194001c03108192404550824 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 259151555 1250 259150305 259150313
    0xd05180d0201270c09150e0a05010f08070303170a0b060a020d031d0a0f02030109120314131a061c15050c04060c0f1b08030703020d0f0509010c021c080304 68
    0x305083c031519484004a242080392254004c24445002d00080213480b80d00d1100032500e01800352004185010407080c05091444509016290a21907003842401001c00811016404103100007101d5050b10340e800465800c00b005007003150002c0400d45074607660300d07081c3c0c01030b101d11005014059a40d070140040003050500034044580316840c80c000350004144401c0032510005804900c0b030b42040b0a280400c180380b00080c003524800780010907554080c1407080040780c0680020030f1010418401310201d5480c2d410400213040e0511020301040b4050f0400e6198024014506400c001c01401c1c41c04c0d01c44070444c0115100305142d0080303800311016000c54500711070511801d83c01250103182e00b89000c0c1380c0b050050100c81d42d6034020b4000c00c1d1013820a420010603a01100c01c2c4070103030700b00c0943d2543e9900a10303200d800117030003a400360003400ca80340e038079078810609504000d200d91035003070074101c40400440f14034040202c01ca1b080085e88500d1020700f40c203030010000b04c61240b07680503901d26040c94 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 259152805 1250 259151555 259151591
    0x12020a060e0f070b070809180109050a0c05031512061906050301091110050d0606030e0c010c050714060c01020d020703020f01020309060403110c221406060d05180d0201 74
    0x5545101034001c03441c2d1100342d4401007100022200148005034030780c441ca0501041ca4422801000d5010410308035210341044040740d41030481c0e034403043c1000599030f0f00f00c466050f581c80305002e400181c1c00f040010401104200360b8020790b05d001d0452520801c0352004103181940688241580300030501407404c00c44114001da1001d400182c000b0f004000b0103070baa400142c0a084c0c0f92910502030385100b01c0800e8403600541d800f604201d0014451036550320300150040c0128602a0440d0003a50744442c100c0d40921046083c2c00e60080080400700e29144180110b90980c8005540c429000c101c003944083d000d002914012101000c01aa15001450040d103012510100c000c0c65034014810088602400b05d4100c0d40b007605030902400c07444c01406554108020b21803c164098100b036500f15542c001c1c14210060120b41c00400c000c1d04035000300081c00310408a800c194000e4007004082c550000c586c10250b00304030f5010f50003044012a01e46181415030040b03a001c0140c0d983d589690022564203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 259154055 1250 259152805 259152821
    0x9010506190503070303050915181005070b0a0e160305010c090618140a1e090f0b09040602090a1d060103111216090f09050402030c0103020306130506010c12020a06 72
    0x203004040014501070101380c0314449884042c0504c040412504040e4880c0c0c4200c0700c41b2a0381c800c019075503908400001c201e401010700454081e00f80c0d0440d152159001da01151102c90b0800785072240c0791381d0b8514020241a05a82c540c1c0355020392011544945c1741c460288019520403000481c60402a180003465903500354040020400c00e81100701c0c61054800034041a5100d544c8000340507046600441c420241d181d10a03c0300322070040c0140d00c042c0032602803006444031382d070040c09001e54171040380d003d40781154146640101e14102040024140340c2c020000300d00041c0c0030700502661800c000307200311106112807070030b000280204800c41d82e241c400c00380b140f188440c40908107048446021103024000b00519a00304440545106850243c141030008044409100060f2619603004034003509056404074000d114001d0000c100d50302a000b83c9100308409010000500c0c181d07103940014203009045107061014044140020400d0005483d550400603002841810400e1912808a484603 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 259155305 1250 259154055 259154089
    0x12010b03061612200403050c09011509060e040605030102040e0a0c020313030803180d020703030315050904020603040f0b07030e0c1e06070309090207110a06021f0c110609010506 78
    0x4021140e401500002c101c1e02c1c08001e5400080c3c0308864504d180c100320030804490201e000c010800008200001504000f00e8609485101c10340e642d510040c40700018083c0c40c4030200f05030038400d00007184603214803a801d40009002182c0a556a03004c2401ca0348a0b40041b22900c03501001c000443c812401030300c9484a00748025490441e400c0325861203840c03540801840510004040380c01c94001c0e03902000130240d14020707903141204620000c3d55403021440304601090612550030590405800d12034221040503141c40c413107540340da00700140d551009000f180c5a10003061020301044040c90fa1601c2000c00d0f0720005820001717800b0140c5810741c0700441e284a070170611545810b4070300740000130b84906401e460498817960a403509888105081c1c20400c0020710100c3c182c0f040c041c080a40301c940e85020744608072880c0c0c84d60030417030301d504803451f103100c680420a4540b00703400f01c26400b00040701c1e000d01d8402150081141c580f41000c205640e030f2403170382e9111070620030b8074640310200101e00420 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 259156555 1250 259155305 259155331
    0xd0f2412080409020304020d0203010e0609101a040504150501030503090a05030a11010302031012151506090501120b0402030f0109060501030204140d03020a080304080403150209060d0b03030912010b0306 89
    0x21030740d51400c80e00c01d43c0601c0100c150044081021900c40a01d080c0000d41d0041c02401680c58525019965120450300c656880c4903444210006d860988501c50301c100729990190301440041c41407002400000c0c10858040440c0c4002400c600d1181c0b2a0b6406944104055560b0301100d00811014082c2138028610039000045010f001811a482984030a1406c3c21302503101d540729000300c9910001c0368041140c0d03940d00d0000300e04000c9c0750020b0314072072000c03038008221074080c00303c3d0441c442c01a40580000301d81002c0c0288560340c0180c9528048021500303020900d1400c031801f0a0070b03070701305640046070840c030b1900610143c0110b02600010740400c0c41c003141010710b040300400c400c1b80e070b14003204d02071440081110241403003407001c0d044072900826485d07980d00709840d00078950307482440142c99001d0310040210018046000310703610180d00811490602003050f0440004107541d20388242e062200300401c50710768880300c01507442c0160b00e50001039001202c2081c5410000c00a000c0c5d004414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 259157805 1250 259156555 259156589
    0x1912031805100203090f0a05040606090806180d0e0607080f28050732030a0809060f0105040f0e0601060c110d0803011802070b0f070f080601140d0f24 66
    0x183c0013065682c40d510413201c00c400e1886030008142e400300f40381c2180350041d09180000c204aa002045041103441c4201103410681e41c1d0030809561a0105964103441d8006959030041d05110b0500950311749401070085150407400d40d12103119038014800f140152030003040d110310250000203d1010440c100741140f40700188210003c060b4810214000c080c946820402034210703480c40034000c03661400d81e2000c4140c3d44040b0030705a40b50030007502c1d17400194401000412840000c505c6600811308801c49508036401c10342040068501c81d030004c44c1e078641c2c030440f544083c501080343c2d80c02021161190151800d40d41090801c201e140d407480743c00360315001c00103c0000d100d60308a81c11207038100f851174900420655480060311403004040c280204500611456014940500380903880c151265100401445019034082001701c40403030201301800140c01014002c1f400921940c68140340c00116001c08603621b004807035400749012103000d81042c0b0b88000f0b19125038410042c11032900c0c0199004c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 259159055 1250 259157805 259157807
    0x50f13030b2a0d020d06030602131e0e070e0d0c091406100c020604091e0b100f030515130504050c01050315130b04140a05061c02191203180510 63
    0x6807099001229001d0000f0030499040d1294191120010b61400c00c0c0600c07030782d0f400d06401075008282c80030360a00c203900d00010142c01050301c11500c0754040d04c07a415214075041d40380d101388800401321024010808a100441daa40038552050030b849022003821090501107804211014a4000d001184502003880015501c0b410f00140200701d41c50012040c005901c08644d8500560348200d06543c24000074951245458000018441c030800081200ca00200200000a03000410340c1c408030f1070349401c040036580703c1e4001a07485050080c040701601e20802c0030a400e080c62421070403509680c1d01c140403c20009000c41c1c080791200746881030031030074101c2410400000c40300c1241d10030303203404051280f2010247c108031403400e00180200483d01c0107203004c4842841c00c4070040305091401e80040c0302440c008201010044803a5800104a00ca95084c030861070403030300d401c0c8480c1e150b2110014081410b0b8507400d180b64440e503034003449101c40c80034070700d020209500060301c0b0b1001000315100007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 259160305 1250 259159055 259159111
    0x1107020a15021e010203070e0a03080d15050d05010926030a05040512040612050c1c0504080c120703030c09050619230c1513030c03050f13030b 63
    0x503400050a10100c00901c91060703103041d0f480440d40075a2250560400761001066020b148261f04517200c104802c0c12000400122483c41e0100034403a00b001c0c00028140420303684080780500302d91440030030316511100080d0346c1403400c0c01c00f00e4090b911030304000b00300103110940b0308052510391598500c8094049076034031503020042c06034050990390400034041c04020000c00c4d18040003142c080b903860703840e00c00c0101542c81645280c850141001d000c00d0b9840344400c2210002940181c485c11000340e0384000340050140a0400d0b12403000c18409036111101c1440342c0e81000c98002412555000c142c42c02600766441003050b401400201c04c0200101c2e19a00700311014854554105541e9904144090f5440b085818124120202d01c4080501c00145800200301c014030035400c070781c1c8818202081e0100542d081b604031003500c0315940280d0002c0d008540c0c2c001ca151080c01c00303608104200c0c8180c6017503007098429149020368100308001744071400d104c0ca074204580d007009521100d0f08040030200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 259161555 1250 259160305 259160309
    0x11106060a1509050415060809162d0608010305120a0c2d030f020f030c03070308071202030c0403150509070501110309030a0c1511060112030e090405010c031107020a 73
    0x60100500d1504110b0344120700100240c080180304008a010304000c5508410b81c60142c1008544090081b5103800d2001030701002c44000c0d00c1c0008141c904120481d02e0340d0182055001c40c10b8180032940c0d00b440b00030f0f649400500340540d10715040e580345051141c03524110880f5881460b608007d00d01025500046403088a41c0000c8004c14901c0c58441004410024003842c1c454191501814030406038031001910911040307a080b1070a0b0841007031082c0c5c03a80320741000390b0555402013140c2c2c0c000034091444e2503484050303802c1c480810851512f0000c03c0e03a0044400d4401e502c0001018000c10144001d50342c40300d2115481040759107812042d0580d2106180181d50500c162488224500101081201c1c0340d44000381c25035440c4170740c43c41c0010ba107a042d40203040400c0c40046148900c1c620034039103d0179242d10000100f01030b0740b900c2d0b03a031101046500c41c2a02000004c1e240b903031494841e04900340c0a00c0c460400064410668200103044403600c0c6071481e582c410811030340001d66640844101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 259162805 1250 259161555 259161569
    0x1b120a020c040b060c0a03110c03010b0906041a03070803070303060b0906030406051b0a081008030903120901020a0215030405060c031b0f1908010806090d08130311011a011106060a 79
    0x5200c2d0902e400003640c5016140b0ba0400c10703c40e03480c90351b081550160b4030300a1500c0c004101c4140d5550070301010f00b40d0700d10318156904110b0721000103440c0e00e0650480b16640e000c01801c1d148803540c07034021034200380264000e40e00c50341c00010307614200356140c070504000f049813a4a150814914200140e00c901c00988043c00160b200c3c40403c08061800c101c410f126503004241c0d694866584401518034901180c442d400311500d8140021940e40200445540040c0100546098600c1c60075840a41e00040340c100c0c11440b030f40d051500140c807035016880c4222441c040721522441c03d0706d031103450240006d0403111b030314205200703000e0300c030040c246858001d000c03020569446000e02001c803101800f80c0c1150001404400c961045195000003059041e00c0102c02951003503075481010031794542c81901000005100407000a80c2c1c00d12249200b6070300362283c9404140c80f0315103180c050a40b090030b000089100444a101051581c0050540903140084009444685801400541d40700151720400c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 259164055 1250 259162805 259162811
    0x6010f0e06040e01060b032a09180405010b0901031a07030614060d021204260306030c0d080903071502010c03140403231305011103072d05031b120a020c04 68
    0x841401403c1d0440401b80011070401501da203130800e48040d0b10400720349407101d0550207141c400030464452044a03c0d1010203402100c0c0d603402c000d56145100c100510030740c0d455580702c603449180d81c0e65400d4940210700900c50848540c42004c807065410a014144405051034251304004d40c5e4814141191110070031500a40c48203041e5176410302900c61a85000d605201e0305003048108160f41c0307004001c0c0b060380810000c60051041404403540f0065807404d83c198000e0615040ca494020555010b15128001c55400c0c0b641a4000c03914202c95034010200904440b51341c0070b40b1550912410307001076402c0c44d00b8451078145140307081e6094005000607080150300141c841007200351000c0d0070100b512001690f595422044810380c05101d0303602441d03001a2501c100f20b0302492002050360300480d04414007404509040103607900010700099580e0648071266002400b29030240080c0019034941002044c0364a01e24004c2d500f40190300c865200c41c000c4c00d00c4540b40090380042c002d4007801d0250b03400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 259165305 1250 259164055 259164071
    0x50f0601080f2214010e160902090a1e060e030a0819110f01060302010305100b12040213061409061203030c0f04030b011e052218020406031406010f0e0604 68
    0xf060383d540d40310000141004449503101040f490755995030b910944100204041c04800440c0c6441c1c158520300550100000c01c018003103014117030300501340140000c051000c1d555841031802600300312400a96004180d100c0100107031500064003034903004045002d410111045e83d0b074851280162811320601a00e180141c03600c0320302403141c0d15031190280c030071603e108a07a4040ea034003808090102701d00190070280031514100c071180c0d09206691000304641c0c02c0205100d01e20003c03960041050741c0c45518207038010144d00861181c480030b0314a01640710405080c8505209201c8005008940101555003040f12204004000d0301d40100c00b80309055620721480d04064000d0145420161100c6261400020791410b1000b14140c03e600e82c514040b5400e64500410281712207051003541e25002d910740c0c003210194168401e411407500801c0f81410245a6000300782111519001158804051001480100c00800c00c460041103d010006c03034203403c0c40c01600007004060251402030f502c81540d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 259166555 1250 259165305 259165321
    0x50301060f180515070303061202060a030f0908030c0a0e0f06090108070e03010f0b0306070e0312090402070c031202060a0c1d01050c1218010e031902060d0f0f050f0601080f 76
    0x100c040101001000c26407094130403c606011a0701c20724044012914002001507402902410b5504041e002400f25003861904c81050300504101d449000d5215981e900c00c000180104000c1c500552031090161b440d48000e03800546441808a2941d01c51a00b44410003071aa0310801101d039541d0f028607000100c0d85500700107848143d040000240d040d4240050008040c1090b481300098581c124101c0e0940e0b151864190341401c8030b02c5042d81c15410180980c04601c040700020401c500d40070700014034164140e00c8242c0300003001d420440b0b04003000749070311038255410049103030041c101020400881640383c0000d405420b1440e0015102c406811000c1840d80c00740d000d840101545400b43d5840c00ea00c0c012410b010340c8003028201d8104008160124694412408096000005802051100c0085182c03440c030242d4040304a0b8040030402081d0fa8540d040c3c001c03001211410140071420540c21482603095036401031080d0446520702080240c980e900c00b071195000b803001030002c5aa502e450074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 259167805 1250 259166555 259166597
    0x206030a110f0a02010f140f040b091603050706030c08151c080c01050601090f0308030a1a130c090509070206060d03020f0d0503090d0e0d06020c01270b0601050301060f 74
    0xc15444200b004540304240030f070190040c0c0b18a001e489800c0080c011929030025900c4402d441185c0c001c200400002c001030700341109250084000b000305c400200010054400c1940c0c2900104d4440d01308000c2085002d415004050126041d42448549480e215100b0b0f99080d80804101d40b084110b8503498a9141c10300004501c001d400001d0309e40c1d694022030b040341c0646419142180040c021200018202c02410760540035a41c2c48034085107151901080c40c0d01401e40c502200b81018415117503443c0d656030302038465800c07250000d80803507030403011003000d4000e0185900840c01410048200030b20103502182407980180201c1d01c0030318110361810220301e00a04010381912912650050304940c0313030440061446007524901326402c02c00012811a09000c541d00541e4000082c1107050b00003580e5030b0040d03e40b04680000000d1304002964031040948000182d400c4054465054030b02840a4100b041d41e0050003828254074551610f01c00404031000007088000704400c9101f12140008220 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 259169055 1250 259167805 259167817
    0x503031912060b0c03030708090c01091a0c010c09061202091305130501060803040e06040912050307020a05100f0e2a04021908101203050714030d060609170a0206030a11 74
    0x200c00f40e6290801800000c0e5254000d0310090040f8004c48001080988001004000c0340f90603901e000810f8038010b290fa10310b40743c081400d030300322109020144080030b00740309000702d40310256104582e852820501400308035807003a40c81034150040001d0007154071040300c00c0c2348541c88050001207030383d640c4415055014518900a02c40d500b000b00000399a00000b0280081e039002c0c080c800c0072519000108400c03100d00c2d0000812041030b809210340240e00484c06194810b03090300560302c40d18090740d911070400c00ba40c0841c1004c03540d500c4a80102d500c05204060704440e80000a0a070f10200445131426824029098021415404440e000907101d64041d12a80c1500c0d00b05002241b9800001a150f94003c039a0341d900b0440e130382e40c0040e440c500c9407005004250180c40e00c2c2c3c0303007182036110140c4640340702100b4402480100308203a1140c441d489800010300242e91014010717030a00071044490243c840e9545032aa0101040c0c89c0542d41d90380c1126000781802100141592a072100003140d40111 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 259170305 1250 259169055 259169069
    0x10513030503090f01080f01061b050303100e0703140117030c0a0537120e030f0f06070201020c0618070806010e100501050304082a070f0f050303191206 67
    0x2180001041003800006065891001c59070209640d01ca1001166158000c503844401c81e0b904400410000703005130744030b20345040f0b40982400c03814000d0b107031103207141d10136220b031480240600020404614140c03a0507401110320b150038442d4054803047c00841c1d80040c0107000d00e50701d0700c100203e44000c0400455808107040720130359541281a040c820f40b908440e042c03400c85a681317505103101802600b503010202c3c620b040082c4003c03e00070b0700c03541614440b00b0088021b0200301c541c208210740e001c029151b42c416084004054180900c40000d060000240808041d680140030329a1030f1440492219406101301c2000806c64020f1700005140044d85c2e442240b160156800100c0c21402c8410214407654007001c041c080296903000444442c40110b03005802030605202c8620089a000c1c041c03e540307028000201c1b45801e02a1899040410b03951010300040c0407400704200b000da1a441001c020507007200a1030070600781c01e4201c4190750fa54804501041030603001340310030814640c800b001a0040c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 259171555 1250 259170305 259170337
    0x902061b030c1b0a0f080a0b0c040b03090606030c30010603140618150c131a12010807030c290403030e040b0d0c0b2a030a14070b150105 60
    0x2031035503115403e8201e10007a5004210015000c00c6000b20f03242e40d64210f0343c00300c00a0104400b2501d034040440c8001e0708420303d20700200800030f540155180914095640800a0b02c21402d04008061030820030f1a00d10b4064690b80c64441540070b900a44002601942400e81c1e40740a40126001d00510494000800c5098000f858400052000402da8840c8000c1c0d101460441142882540c0d0740c010f600340d81d85100d0741c900c00540c00c080a0000303008100c0540e40842521034581c51501320b003054464408a520340e0215101240404811113903004203040b00c041c00a02e4195100c1c2680c10400c1c0c024000344240c1c06102040d085070548000071010328640700d491701c0b541c603468010700040e1240301c054452420084102124a00f242c29441d511b0340c000582035400d0304d0074200c048580c100112500341b1b407094a680c50140b03440c48100c001c0d503048540c007840d138540c5401c2d0003406000040c41307100c1642800782710000c001000e4150082c2c006074905d610103507114000b00101d415210350000e000038059 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 259172661 1106 259171555 259171573
    0x3100b0a0b0310060e1311030615040503100905031201060e04050a0b0f010f1107090b0a0803040e0403050310080d121b0509091506040b0406080106030902061b030c 72
    0x10f0041c185601754081c24285070201e480d201f03084010054000104281c034640596041034407501d40254070b080509003008665504400203440104c15030f00c0114000344201001900d940c0402c07200002142d60316000028402d884002080340110309140100c0c011010500034002c7d002e0300a001e01881c3d01022004442684004141070180402d0406020180300301f0f11000c4080c00d600e00c0b0219501546d1000c1c01000d03d02580042d03181e410510043c085034000602543d04240c01d4036126444c2d0b2202d06500c80a80420390021038184550408100d95503000b503e503415032129140100241082a00003401844001c004480015800c00054030035243c10110150007581d240100c0c2c1c0240400000f0030803503031250304034455086001c85c2c100503056001c414580548401d20f414000e15200c1e9011403446e002e64080001c80c4604840b03540e18050b02007059802c4400a5402c6914860b = true := by decide +kernel

theorem cover : BRFrame.Cov 258992805 259172661 := by
  have h0 := BRFrame.cov_init 258992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 258992805 ≤ n) (h2 : n < 259172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
