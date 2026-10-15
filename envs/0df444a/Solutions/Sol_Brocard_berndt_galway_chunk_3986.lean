-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3986
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:14:50.225732+00:00
-- url     : https://prove2.me/submissions/f5f08522-d8d9-4c3d-adae-2c0d1e8affce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 716726618 ≤ n < 716906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 716727868 1250 716726618 716726651
    0x903030f140103060e03070c08011b0c080904020906070203011503020f01030b1c030309051209010201061203050703110708010c080f010503010509070b03150607050c1026090a061e 79
    0x80011505401ea95942c0c03961300c031a40a40017598440e00c50b4007041201c04003184000e2a0072001d001d0200020400c601c0800325014510240503814041108240800380000c40c50412560703041021100961503a22501c001346a610440300000d505d5840c1001d16500006410081c03000c40f8000c039107504e440c0085600540c01c1d10385510969612041c0c078010340c0c403503c0c001d0420f440c1e000d00130700d40018172681d2035495518004d550421000e81100c00708440c1815a07090103110080d007002e210414403000b096a001e062405407150040c1405408001803070514401c002c05002490390100a01001001f6040a8034280c0107640450580380c0310800454141014001c89018200385002041038902c4e1400c40a4a900041c1c0007010507140005010021b41e1448050300805005202501c1042c4940040118001680ca03800c0240110042403d80aa0054041060299034000005a10343e1000c6c15a410140d002c00002c00711803402014104260301408406401d044c810f00410400e25826042c04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 716729118 1250 716727868 716727881
    0x120311390415050103050a0207021801030b0c1c0f1103010b04091811060304061b08090105094c1407090b030c0c190b0a2403020f130f0903030f 63
    0x15031142c401503040101e54429808258010307410382005007000601da00182c44981480c03604100008444010700900441010713143d0400b94005507580783c881002d070a4010641507d05040701980d13140000c40c914040c64105010042c00511010796a60b100c1440d96200c2d0010b002e0f40b8041481c107201200b90441d030780207000c1724641010300d6076240d080c40001c002c0700e5400140205c076041d403500700d80d00d010040c003080d85503101c030241c481e1906441c0807201035003180d0000381003130015480011328216608030344243c0c0400110340040040030201403845405250310309640d01054001a0028410003426684110142c0001d862030f0a81501c0c1d840c01124076000b207006440e603483c410004103201a25082c006c0000b040000243c0b0002901c4d050003002500341003800741d40032440c5500708001c0304410b2080443c141c441c11940072800610380f002500d98134440c0002805400d050603020b0484d83c2d854869200c040319141c091064103c4d2001d2140a0702101104401081c10300b440b0307410b0800d084c040c0c00c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 716730368 1250 716729118 716729141
    0x3050106032906280509041404170f0c03040e04031e0207090b0a05030f0604030210381c03170c070204050703060b07050f0706091203113904 62
    0xc0e02c80a414008200e510703440b000725613480071042462a161840c0f041c610418100300783c0c0701e841d00d5a5200c0c0503c0b080d1b0342c03803900c2400146134503400c20000075000d85004000543c220b105d6602d500c000c604440c198071484059054034400400d0001c0c0201c07100c04030fa84120301c40c0c4ea82e040510140d4004000800c4c501c1d03100c0000d03800600007030101d5032960b03010308902c91004041156490f52200802d0505110303007440285d9801200402080c15010030115020040304e850400054003580c103051258071003411441ca200315881c0c034568070f001a0008002c0600d000401c510301e001c00c20580482c0c0d040d003412048000c0703042041c00d001c000142302c460f54031039135040c25583d2404c1c41550030403006210003007884051540c6e030200801c0030400c88000d000794600c40c2c0000c05428440300c20030b500d0000d40f41e00110801850b40410b00c03c000985100358026985030400c17010064810050034102920408620440c00d0300020784591280c3c2e00030100d50002640d094031000700135510a010549480b50b014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 716731618 1250 716730368 716730431
    0x1412030d02130e24030c010203040b090d060c020730020d020a03080a05040905060913080307110d1e02010603051905010b040f020702091f090903050d09030305010603 73
    0xa440d0340129400810050b103141910038440740c0c80355104a0202000d40e01c0c4054141c00088982403c5070038444010100320803401000240ca4100000350741e0303c21400742c40031861001c20404450341301c420143c3d403031079403245003031040541c8440c00275922000d6116291804250a003a0304010b5200324980c4a1110305030b0102080003216024055803410ba404101d030040c46181001001c50001c1c0003070200b0000c81d42c0c880c0c1e034440c90a45001706642000e0310716841080c8907014801103001ca240505259a4421406522590789540c141d50700071000c1e03640c2002c0e019005005601c154040719034032074580100c0100c600e50111440c22400c0700c415000080c800d0340000740203884002440d0390b0308001e500c00c90000c902c0034881c0012034151500101005800d540104a000441c5002002c281d8000201100329030b0f0702d144e044807981c06014600c0303590169961085102c00f814820030031100824800141402800003910703009000b01800d1141c14002441d24501d038454040000d82ca43d442d0088096 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 716732868 1250 716731618 716731627
    0x1306080604030c03200c01120e03090919050f0709060e1003201342030e011a09091f020f07290c04031a070e030115141203 54
    0x2c1c2034800c100d98500075024408544280c41d0340000300000c049484030240050051501c4070ba00151054025030b07111005a810000030f2103000700c000050302e0150208030342a1501d91902400c0c0311404070a000011a0b207405c00003000340c8902c046030700700d0007100c00d6500c00d2042e0795114000c0301c92282801c02580d2028824421081192081d04410742000701c5241c0440b614070b805200b109513a0007001384041c00c042d1114100011a1890102d48060002c1c0311050f0b1900740390060302c1424911902c403c1c01d8003a001e040382c0300191282d48142036202985008201036504100f040c00315529014031544a10301040015600113000b0401e07082d50b011440301e0781201c43d08000c20001941003208040f0607000248002e00200b5595086058180c0344480c503100704583c00d0201c20340d0ac2c00000c2180000e0841003100700b0000360000c2e0001080c000075003503003140d522030000480c1e5801501c80703182e40c50343c03c200c07031080e84500307071031480c821201144141c2078511306541c1805400c041c0c0421000c2207400521 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 716734118 1250 716732868 716732873
    0x40e042f090601050c1905010c080f07030c0215150301050105010e0105091c0c24031b05070303061e2102010c170c03071103160e07030b01200a021306080604 69
    0xc1d603141c11400506045091103150070b012494100403401044201220380c0d0350350b0510000707100d035900600d654607201d021850700d0400651904405482c0b9420035a6900341d00034070038030a01010407040d290381c2840f10a42000e80c03810760000004101644203510b48000040c1d1580201130b004103d42041e100e450a00c00a00100413200040e00e1040081d0090000a400040c41c00c0403100003800040244500e148400b01d648842402c801000c4000d2501c1c000500801c0c525115444101c0307503061070450b60b2400503203000c0f0040c4ca030a038040c0c0391032102c0c00c1c115201c00190030008401d07240700c00000c039401500360390b8070301741e0820140019010404590006010920350300b5580c001a0031017851901d02000028802d14550001e9030540d9191007041c0c0ca00d41c540340a00a04003401c980075103420840381060f400040698004c5c00c2141030641d1000040c0041c0d010348150513003001c0070b0100c08541ca490300001500c88010b0403040344215a042c0021446143d503204503401d1300c1005005064a548a5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 716735368 1250 716734118 716734129
    0x60521070f0e030703050607021c0c0c0314101104060f050717130b0708031008210d0603020301020d02090a0b040e01031e05100606180e060d1403040e042f 68
    0x21001030740c050041c0741010020074000c014480c00743c0384a03401406941100241240540b802d09004ac00300850ba2110300042500380009805a9400030050400d80307101c29201460803490401c034800043c10b19183c62200d02040c8080c0044941607280d2803c450305010f021581780c41242c03030081150000f0050411803800c038002030074600d04019041801252280c240e548540c2001c041241d07429800010040c0a5641ca06401c008012080c010405480034800f031030400c1c441004a41c10703034440818030403140344141d048800219006030085690340018038a6401940c0500b010500540d9103010024518261004450403204c00241d80e02c6280d08540d103a0320460703d01900314040c20700801e00d10b408184188003a0004480744074000450a00c0c010b8080c1a0f600100403044891050882c10404001c041500340c0d1700c0602100e4a208841403032900703148642116541c010144008034000c1501512003c5450149004240c0320020521000040c4c401058001980b0098440c5118807917035070818 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 716736618 1250 716735368 716735387
    0x1f021002270105120c07020f0f09130606050a06021e0f0a08070309091103040b0601050f0a031e050414160501090b031506030a02120c0306090c0304050f07060521070f 73
    0x145019481c1142660300044c052406442c0100d10f40c4d800545c2400f1440c05800610760440f0546541c1c210388511000a04813620084c5601c055042c1c061030307042003003d640d0205019140007070104800f503072182d42c025a04c1c14043d00ba103404922800c15205c2010340005c506c02d20601007801010b952215588a0f06c031a00261400c03410f102e42c3d1500806c440780c0b5030040008081e5085074058407403078242001448100f0241085050040c00c0010302da41c2c01280003100c40c41c106608002c80c003052104500a1082d0b2205d0f25410500d10340b005202c2000320603031168040403200c404803810000b01c2c0f14441e03c0982140b0609001c59031401c001c04c04920048083c0d9807000403000d003000b81808030800300324039600445a6446155000410311070302c0b40c580311501d40000c2c07056412400c520781500030844000003e004080c41200110009003080820801e14040d00824030a0780c0c03e4659031130024105802c95905038110451003400031103140a160940da100300741b290303990102e1103940c10064a800d04c131b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 716737868 1250 716736618 716736697
    0x12030207080307080a02100b011b02180a0e0d02030a083d06020d0c080d1d01020705012315040e0f030309060f09070b07060510051f021002 61
    0x1100d400150300101030003e0305005000300482507076005403990082c1081c0c000d074108240030385001a82c00441e41e11a581104c4401050021190b82200c0d00001d542c10f500c541070714000c0e078100b80c10000c6500860308440c1040e01009d0482d0380c5213241160130ba032680030b468541400101c500c1c000904010600510080720744860700010021004138004905490548160074000009608200081a81040b4005899200b403420040b4107440f43d442c04d8aa00c904d05c0b1003441540ca4140b03010b29041a041d83c0d08045e40804001c65482d6031614046010b040c1c002c0c0c100c00341c44c0641c940c03410f070a25000d50301032142099031000d82d903882c1014200300c02407040b9460a1442c2c4034024104151b2902080154014141c030300080c1031a01d8081d0180c810488002c1800e2210780041e401000001382c51000d407800b00f60b00a601080c1c50307541c0c40d2140c0c3c3e0039501d40e0020364015003520003000d4582c0c64001c5868090b070321b6400d0328a4410b10042500582c0b00d0340510f41080f984000d40302080380619019881c8501 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 716739118 1250 716737868 716737873
    0xf06140d060b07030c0c050114180f120c0405060103141b0910050d05010902070f0611070c030f02030606040501060c030e122e0b0a03021909020408010b03060109090c120302 76
    0x1501c9580041840d0800c3c40300300d010881d2048950300f07110012004034000c01c42441d00c140b540c0d1001008000900840d19240440d802c034a00b8030903155202d0308925000c0384094050101c01568002c904e6565224040c0c20f8003882c9410082040c130b505c070f070180d6032500001d01092151030f1a001803007030000300c040d011207403140010b00c8000a20307030301c8001210b030301350050780c807a51111441303449281100e906904c400c901e00e104214070305c0026809111008aa500b00c04000b0f164001c80ca42e00c0311512452030f00138454400100040100419141200d03840c038026411034a281c0c2e40c2c4014031003118800c0c003805c0f02003810342c030341c0d180007a1081180710300c451000780000104000c40c0c0c00390b034074040d56005240b09442c400b41c0ca00c46541e10480342038248100854090100c04111400705007000700902001c1d00822118020245e0301d11039000702e8004160031503045641e0740c0d841d0505030081003007400840c407a00030174000040c94407150080e401c04039000070b100c0e540300c0c4c035108050141e0303400c5036411820360 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 716740368 1250 716739118 716739131
    0x20109050909011a03060f04120c2f0a0803040b0c0c0904031e0804030806010c050102070c03060f0e06100506070c0f03030c031709070605090301090b0c090306010f06140d 75
    0x307494503040300780180c030908004100c10301c001c04d000340e07480c451011560080e0b0000081040101e401000309400075044035044005403007280003285e214185030b01c05000380126480d59500d0019001e40d030a85024490100d0b10100344010420043d1000d92282ca200c90b03100313000c18040384040740028900c800a8204075941800118003042c0f50700b80c21034042c1c010803200e0b03404420760680a60b0b400c45101452074880c015241c50366001d800154040d02150400250340c42250401400354111290142c100c00c203100c1041d40d92400102402c1000440384940f800d026112161303560004140c0d004100342c1021440c12403c00d01444000d030043c41d0240c0f001d10100b0350004010740d100391044007941c00380d5600b0f8034003500d90030058100010003d02c08984487c2204100303188501044c0d010a0b104d481c98420795031b81e00710001074054140104040e02d2059090240188038010a005003101c071010b4059a00580c0e0f507113141001c0c000148518808107880c0000c180710110035100821900b561f03014000b408 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 716741618 1250 716740368 716740379
    0xf0e01031401150201060605190804020a031406090f01060b090402030a020405090114041a240c0111070606060509010203030a2408030702090109110a03020c01140c21071704020109 79
    0xc1e4070080e03008100d0703186200b0098001581c2030041d400500b101d414000c0c07034040c1c030044081c4503032151090402040744e10404201103580d000ca1120046800c44d400c42034000c0703240c1341161130350000e90f0214042d1040542c006090001070041c0421202e0b034164031410542c0403003d22010b54401890314135496420070000c2003940d1030b0500b10b0301810701d002c0c801d000080d8803070501041720304510100c016003040160345005641e4040014803440070b108403d11183c80070413516009401742d40d0207400b80d0350924038803140365202c61000d070003102d004840074081c03690354550541c1c05114100f0030f02e0040c0c20800019202100c150050101540100d0200355210180103150b8008441078100401c0c0350800206031040d8580102918003520415004101c02e0164043d200d000b0312459101e0b8041c1074000c031300b0004104080d8480c07040c2607845072907041c40d40360000204c020340d07001400801c641402e0131301c66421022030340b94040c030a460300d03211039403524898036981d41c0c00500103004904010400001050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 716742868 1250 716741618 716741651
    0x8090d051608061018090201020a080409270506220501050c1206040e0606040e03090d05030304020306150105030c090d1515120210080709170615100f0e0103 69
    0x78034052058103903040c6810200e205080543c0548098030f080400c1d0b20a100d881c00042c415142034a40d081d00040488a81c40141e080c0701c908200681400c0010900185003040e40d00959040b00e950002c01e410000d4072480e81c81801403402d000780099110f00300007248660079292a13a0190b144000242c9000341d29541d035401d546044440443c241c4c00403920900741100ca840803a0440422201030020041e21804070369603080041c900c44c85581c50b04116107a13a0014800c5840000d00540300b40d00b0002c0c1400d2155483d80180c600724000e128071030028002c001280301030b90100c40c05075540c503c3c0d91a64803485542d904031180c056840310006004000003200603030080704e40d01c6803c4000c250fa81c0c0070b00c0384910780c1c41594804d00c0403001c080c81900059841d0021004211481e081c03100d0355813620352007114501016002540c648000311285020180300141c854490b40c1c28407610060500c40c030f000d06c8103140d900346024003c10380b100805180d080c003c0650302c0c440e27001890001186e00c84146000b4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 716744118 1250 716742868 716742883
    0x1507110d1506260102071505060f030a0c030209060a0e010e0c1b010c1404260a0b040302010504211e11030a09030b07031116060612390308090d05 64
    0x6007181900092011145891903c100d8440c00021420084140caa06210b111042e0900700341c565582c0002e2241d668140b0800801134000e03084802030641c41c50084c10040080c041603201c2c1c400c10b000641c642c0340104191090711000351440750361b070b442c100e42c9012a000c0170341090604202030040360f035070048500400a107400841c00110310000d5540c0b010308503c0c1003400380030707050034100800d009107134900f000c600d40b400070501103d031300180c0c03c81c0d2281407400c9400c6c018905840c4005000c103060741504220300490090007100340c100100f0781007000c0c0030141000c540109000303000c09001001130991b10114104d0a060000c1034080000e0040e05551005a9080c08544005c1042c0144941c1d0041d20781e1240c200c0c00e01b04054421380c2001f54250040c44411007008600c1c9190804000f965003101005211740728074540c1c030715a5072801070031b00c0d0030161081e0f0183e1010310070b144506185218149105100d1140344c0000c034203507220540c203644010401a045203200d902031001480810004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 716745368 1250 716744118 716744129
    0x14061e0f0705160b030907050105070c081f0e060f0f090f0f0d090902160224040e160c0b0c13030203030408070303120e03090d060f050a0b1507110d1506 67
    0x148601d10210496071144901c3c2d400c1a040e844041c030801805000009448040d12824280b00351501346a2a041e1341480440d001440b0a00404803400340303002c050700924100300010f40e0240800081252195528001290740d94584008600810041070740c040380e954102059000743c1c0c50644c0c1c02d01d0b0091038001d145001e81c001c0c1d071003400d8000d1040d5000c14641c0191003025001d46c6032030b64080519031243c2c400880a40315400700f481c607503944040143c139202c100800c0e503146911349554540d8148403883c211084c070160441d16010002d242d100b401408203482d440315520b41c090b140c16042d00165001018001300b1014000004409a60704002410052802800404445003035180051403c0c44502304401d001d420300c000c00d00543c1020096405500041c1d4980011800609142001d000b02c4148c0141140c900b0b402e0103801211500300c680380c201c054582e400c5903142200140c845209d0070f400581008420503854072585020314081c0e6059010710803a120a60074031154808540043c2d100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 716746618 1250 716745368 716745373
    0xc100c1a040b070215040209070807120c2003120a150b120a0605090709150e04050a38040207020301021e0702011b050d0e01110f0105040b0114061e0f0705 68
    0x20410f0481d07041113400c3c0d00d101c0702007062034941060740c00305045c9180038202d28184410580050001d5100f1492600d890807101c500340700c2e0008a43c00501014800c4861250300341800d815419841c00002c2100e0f00201e03401e0752486541c3e1034002e800e006080c0d400000364031035004000020000074540280145101217681c020340c40c105200d0307513002c440c2e5a5101c2401401103508200c0745ca90800110030460301080345030721180c1280d403000c41f100c00c03034000030543c01450602801303014032076a802104070407081c2e030300c00a070301c4050242401c0070901c15904103071b66201d0101204480c14160054040540b001d00058140190f94020b43c410340b4000d04d220040c40c03000308880040d9030f4041540348003402444108150010b02d030f15650380701d0b8420702106050184984016440f03901c00c041c9012582da005041d18440030391482c0c068082c000964041d161101c0450001c14072440905100f6100e05008012524013900d8845005170145d88941440d00300d40d0501c0585541001c40c0000c0002c0c6224001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 716747868 1250 716746618 716746621
    0x3070b011d2e030b0118111611030106080604140c04020909060d05070503030d020a180b04170102040b18040c030b0913080f0708090306090c100c1a040b 67
    0x851921104550000740c0c10065407030074401c001840c510720000400036545061110081c1102c10880c4606641c00180741106140c000100891802c0403485201d00c1300c00284011808540c03000d50700c0c01003600903442140942c840301c0006240d0401c1c5290144043c00101e07150341d0b03500c01903040c00e10848060701c258518801d02d0808940038410301d01e903d0002c580440c1000441004a4000d23100284514080d0700f40342d02c901c8c2032100400158008040060450350f648021a0303441000c1d4211050700404180415111035880010607080b00a6a0042e0f6484c0d042074503000d008110a00b0b40700c41001c0030f560801c40803850401c148010311500c030202411408140c0d90a041c40120f03100309812030101840e0401e10b40040d592007003890b41211040c0b1512009a04c0c9042869184c81a01d044070300c1400c0c002124420880204050101900c4c00ca099a00507550150b4541d211186868441d070302001c0310183d0840719004100911113103001e0200d0341c940072141001c07000304000c2594156080d000090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 716749118 1250 716747868 716747879
    0x30111190f0201050c09040b060d0903120605010804050d181208090a08010b090c18300604050a060203101502061006030e0606090406090525060c20010e0303070b01 72
    0x441d4a07110904500c000c0100d4640219924024082c041c0307441d201c1c43d20f81c3c50b84111951a00180c46000034070366010029454149030141440381074034240c01105042100010f11580240d10b880e03c00c9410001800040010a00456801d11007030066519040004800314256030841040744035507114081c400e646610b050104032114840b0350001c00b01d41e0601c508803009803100411079411440012682c6d8070707070004450b621a0744c40e044e0383c41d40d00301407544620084440f01d40024460503482c0c2c0717581da9500c502c51214a40301c3c04c08076005455135100c80b8034080015402d5004680c40351000d51002c2c0015280c0c0100e0344813460301226800164403c500340320f03001c03c1403401c2c0360003030016003030422038035100c0e040854440b10300901c06171050001d41d00007000c1c088944c0100a4085d404000c1e600c03800441150084610f0380302d900c440c5261000f82020410b1402054041c4a46030070000305c1c0181c100d50b070024054038900000581c104008000c070070440340c80800280c0001d0744103000c0551b0030360410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 716750368 1250 716749118 716749127
    0x803250c050709060b0d0b01050f0d05061e1030050a0608030301060909051b0c070305010c0315090e0c090c120901090206120a02040506030f07020f01092003011119 72
    0x1a084243c45600d8000704000760500401141c15114000764041000040d000041e5a54000c644040040c042c001070300d983d00303244a0740100d01c07500c0c0071507290040c3d03c084100081200d400c1090540c11010301d15006031058000d4000e4086078550000c2440990015074030254072002e03c1c40340e800b4042e11041841880c4580c0e00603400600302c40c1c0d00840c159890034000900d00310b11481003c01d02ea80c1d44001c60440c0c80c2c400c442040144030181c400c1da40d0454000c2031641c0d441c4610064070390b035292140402c1924420702802c20640320301300100700c01a0030006500020200301030411418800c101d10895943c489507000c1d4420040300f0043e40e1a641343d0030041c43d10040017080c01580303034500a03181c8010f960b15401e0703c42c20740720041d00700000d80c1d400010710003e2240b9001941d01031004070400086200f40e0240c5031007500164207803080b840c2100c210701c2c26500c07a076000520b110810645110721003c0c907500b08034034000050002c01c0c9003118401c1c241c626404822040601c0f2854141003c1e0240c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 716751618 1250 716750368 716750383
    0x1706030f030f130902040311130b0918010b0909010c02070b0306090115050423010905121c030207020406081e28060204031515080a0f0803250c05 64
    0xa401a1022124424a640d12441140c2c00391281040204058060ba2100b090380340181c44220b04c11941c954a030b052030704209043c003091901c5151100e1512444082e540074000c01d400000d012540303284c8400326061400100304d14a00072a40da1000385030115a42d0717191240c00b0350310103000010321070541d81e0300a0401c0c03581c1e04255895001001801100d444410300d1a0441d0029030310800e52044010044880b03228641c410898052040e07864442c00390700966909082c03c00340c031140c120583d28010b120701c2c0a481c01d52140c054106045000440070441190015090149001407820f4041e40c005022246290407003c0f4951203058841d40b8060251580c060751007158000780115040c82c414400501451101030440c02c00f14070782e8400300415501620055580006821888401c01c048a0001c5c180755420490403003404500140810002c12240c0e80960401c20485100303240d500d401c0025030018049089424540003202086056401d02e44131810031940c920798600c0050404c980f03000315 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 716752868 1250 716751618 716751631
    0x402160c150e0d150608101a120d0c15020c0c0a09090b0a0e030409060b130f080a02012102030403171f03120c1b05011e080f0408041517 60
    0x200c403100101e02d42e6801d020a20003c0d07004c0c01040b5440c60488008000d0304450f4450362281c03261800032020341800750411102d290b1500010b03040307000300b142045101d05050360707081e078030307801200725000c1440c820b0805c1840300740518961340c001503418200c0c404a0b840f2003d0007601d900606480209480d02c43c4036240240040a01409003503403584501d100a83e010b02202e004695130340840020311401d00c2954002e2806840802c02c40f545c0da4805001c69004040703091440300025408030722002c45a802d201500d84043c01080d46d1065a07005680050040c441c0114542002c812130301000102e0000390300c81e070b110383e548440c03821700c60165040106000c0c2002d99603820b445e400100240c901e5160004136038221241c03108042d484041643c089000d0340c030207489100c0002e03011211668500c9488100e0f0b07005c1c1c2c0d610341c4204440820121102500050360300260711710010030b650115080780d4640190140c1105441c1c0740d62441d44070403621000d225003011039080c0e40c401400c40d01c0f5030003007a4440d5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 716754118 1250 716752868 716752877
    0x4150215070f030614011416020301050703020403030201051003031202130b07142a010e041407020c0f0406030b07030207020604080a050706080108160e10084204020d020402160c15 79
    0x14000c400103440503d40c0c00d40f82c180180c010230b12150075510003942c0e0b03038819000740007008103040200001300607502c10b01058001d5801c1101091110030018030440c1260b815030359104032a1402d42841c2c029500001c1c1000c00503990000c01700d600a0400001c02419100f00d220000c030f500c1c3d00301480e05140ea0a50f14203075207024031968401000381a0b2014951072000d00c2d0035244035441500180050461264107801d0201c404100003095030002868840c60200301d42290200e050b5104104c1a00c1060200414040da10310224680500940142245910080103203040039201c0000d04d1801e40390500a440d40d600c038100400015400589082c05001c00d036002d04100b40030703910740a05502e0903114501c00f00c00148000350701a181001042c0c054580706003900d03480c80074900c203205131b404d040c800d480c4181501860411400c1b100402030031115500d4240c602581e840e13408001d2001c14200081c8d811a4003040354034160b01190040f018124030600706541310034141340800b500415096125010700c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 716755368 1250 716754118 716754149
    0x40e0106091a0a05030a18050a17090d26030903120a060e060f061306030f0e0102090306070c06020d020a0503091b032d030304032c0604150215070f0306 67
    0x865442d022142c00050f141030041c1e6a40b1381c170000d40300400c0c240780305100501c1001d20010400c803020507a0080b0500560a512204031940942001489036507a402d50101e0842d01040000c0c0c14060480000c01c0f0004000b00e4140e0090400c4980764400c0703c0b9000240c00c0003070011100c00d00310036640d8004c900314a0800c901400d01c0d030300000c0e00e40041e007414460410311684c6240c80e6503490465241d01c01000350316244655031400600900940e4076814005070511601c1c89000780c0c140b0907171f06050710003401444951101101644d119403004815912590201b00b80119004140001c0840140e9aa2071036034038600404d0103802d0404204104085111444e0b04103d81d50740001c50001200c80010196160180854802d0100c1d050207101c0409000c00310400c0185a005071b254002d66440911081e544080c110040040c03191810401d64891000e000a006a5411055246020000c3d0046840004252071440c0e44280c0888030080082c1549c020500c1c220b0349405151700a21200e900c48040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 716756618 1250 716755368 716755409
    0x70b1e1207090e2505031504060909260703080a0f02070c0510020f0606190801090305270102070b0307050d1a01030e0714010c2103050a0507021b090a0908040e010609 73
    0x1104010404c0104000f0044045650781e02c5200726881d000740d00620400c01c040d40c031503d500190465002c01e0344d06e20151000b41c0c80c18607000085c0313190000c00116052a000440d0380a407204035000d0520283c0c150b03101440540344029100030b00c095800b544002c207041d8685000c02030035082e14444c410454001554400e2002400107000f500310004907500c095854400481201e0116a5840040190b0138035428100317264001d00140160034401e24403021440b03502101d003884903103da03007042c01a4807417030040041880c2d00c0c01441d00b08903c1d1030f240d8500790017082c00c50143c40c1d030221f10154a80380114a56601d41c0c162066403510303d01b20028090485c034020400421401089007107062000c11140b2004000e20f039108109110041c10110081000020300200240011901811505c2c982000700c1c0a042c00054500e07064800e0840e00e0b80d06402020500101c00300140100e45c40da5166114200022030341c030007800107490181d83c030300955031600c24018920034131a1301002040e48100610001d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 716757868 1250 716756618 716756671
    0x2d04030b0a29061606050702070b1c05040816110102011a0d120302040e1008070e040b0406110f0417060a0504030504031713060e01080702070b1e1207090e 68
    0x2c924803151206000060744030302142491092020952040c86004007078020006540d000c1c500420140d0300311040b0175201d0740341200c603202e0030107404061840d6415020300c007205600910b034042d1003002060706164a01d05a110015000c0004030342c4100c01e80111001543e0920030302c4103032503000341e441c0c1c800c900090218940c401c078110302034040c4030b10003c401200c074020b404580003011048075000040c07400601030605290070b07011340325182c040d5881c00910485074081860189400c902d04408949403a03a0311001418031480131811038600f40041c2046050540c043c0008021500744003800100544150b03040200050225410a02e04018040802da0100544007507036030001c4006072821441a0340d45103401412000000c06070342d043c0c040340700c9a01445112134070341c081c0c81704800340d00c600c441680c842016006003c00c0510902c0450840c0703c0c11417070b6050080038a590a442c20303030343c1c44980c07800c0b020031070701000892181441080310000b1742c1980343e4880540d812060700e511003108083c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 716759118 1250 716757868 716757911
    0xf050412050f09060f0c030c07060207050a0308121003060c05041703040e060d0309050a03150e010c02061302060d0c051c020a0206130203010e16060905011e052d04030b0a 75
    0x140204d0002c181c0c40540e80d9000304882102000c0b000301da448601c80401c4a40d290885d008200050040820000d030324200800243c055035030241c142c6092250b510100e4441a070002c2405850100500c00040840d516104007402c0c2c4465555155031981400c0200643c200200d9955014ad40f08000402004a903420319a0704000100c038800305048090404845407002608032580c04810020000100101c40b1644848110011814011481c070228514200c1310f0180384840903800c030382d0010750101102c041806581744014115402c4c44c4081000d40f007295403804805000c03071000164081d983c01c800d0500941e031401c11005615040e205640207440e918090b04200d0020883d0584100319039003034101b1616030012100b01e4000c49904403400d130034810f00d40b0412005c90910784010649510820807146111884448600101c06100b011105903000184183e03d4036000110221421090030352801c62602c401030094446085081069a0800190491501d42d140005150340c0034596802407 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 716760368 1250 716759118 716759137
    0x80921010c140313020a0315020d05070309030c021309060501090203010302120f0a03050d0f0f0504030f030c050301230a12050715080f0907170303010f0e0105310f050412050f 77
    0x1348640c100d40c4003041a0a80503080149204000c20541c0142d0381603502411540b41c50160920003521425801d50883d1800d02c80500003416186071000035081c42c0d5141c1d0801d280c480d10000b155000d0782c4a40c4100c45081c0c0050b0707080307034000004200f9480c0c03443c5c02440003540440a0702003018503600440e03407a088188006c0c01d0003004601074502213070592044505001c0d448082c054515941d417030300020031040b5012000b040140d103981148502c68800ca00000305c0f20b485103441c507402c00694480701c407695410b4103030307510b2400211601519140c5000000300040007403040c40b940145004e6051000700e03042148414109401c20304095402a880750704411103174282c0440e91102c00355103041182c40d401040b45003020900c0d20402680c000300442c100c90034507164289441d1203040251000c0350030304c20183e00440c40e41c00300d8005480c3d90810745044254190360040308100c240c40038269a41a110b40780829030300c0b4200001d004601070308942000301441c1540c46d02c80b560607094030b140200d040b00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 716761618 1250 716760368 716760391
    0x1050415080705090d0602091e0d14070f080a0b011a04092a17090a020f122427070909080702090103080403050f03090a0909080921010c1403 62
    0x2c912114054421034800903030141c500d4110300241e09210020394464110240034030424500c48402c000c21242c00c10703a44000030316900c81c3c0b4401d03480d00780c111060451a1a102d000d050300014031442e456a40f440140101030144c001220142001c814088050f4011718041081346043c7c0ca0721105041210165000d040e80020360440f10150000f81812550712040e0901564400140c0300b90400460016800403034001c03107160380c521256540381c0e5411000290001c034408a400450b2400e000380203000341004089464100200860420903402c00781c00505114201c1c4c103122005002c00c4a0003580748285607000d4114242403402651035485109400d50345076650386200c01c101080081740d00c0d5503001425084696160300346030380950b00511040720b00b48521b10010440c00004026038017203c0f4000d1035141070318546140030024240e000011652100c0400c0759100c10b50388d9044454142e4400c2903268101d001c160034940c21140355800c1c12090001040400303041d8040706040384d6100042e05035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 716762868 1250 716761618 716761621
    0x402060307020a14030c0706030e0a0204110c0a0b04031e090905070512041118040b04023105270714150c030309060a0605060306010809100213050f0105041508 70
    0x8100d007440c800001c02008040745104009080e074001000d040a4401b29041c0d6103002e50707410080d0112003800072151070301d80000b4204005031505038400400266232845017440d1051803084542443c083c060111a04184032050006140c0c1c0601d441c49200706005002490307904c0200082c0c1402c2c42c8d4420500740c5915480040e404510843c16554072000940801c0010f050614007420740fa241d2860841c05203040079803182240040840c2c00b8010754021640c51070b180c486409020410380b41c0c1c0034038103c994080104c1c940b0b00900503448002d82e407180d9030004150070980d0002c0075040b41c405444483c900c0503054a002d11801086e210111004079a4049186040b40042820f182c5400e00d41000c003030000c500c510421401100540c4a0f4500303500340c4000c0e50390003c281c0c0c101e500320f0007041e8000a0a0001038844d500038000c0540042c0d44000f101c0112138000c0c00102a07900805a089030581000010480741c00c01c1c040006200c202400c1c900e041c00e0601e149880b07080792002c0940104003d100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 716764118 1250 716762868 716762881
    0xb0f0a0204080d12050f0c07080a090e010303030f0b04110a03020306031603080c0c0d030c0b0709031b05030c03120927040309081e03160204022205011404050904020603 74
    0x10304a030000c00d014026100044a00340b00504903081c9002d038680114200740000d804a640c80c5a201d1040c5031000815040541035203565600d038000c22118004d0100d400004101110301051560080d07100e8be0b00481d2a4500301108000d0f0351001d076180b409542040f4484018400c80d00540342500301c14a001601c1741c0d00d10740080c0c6401101820503403d1481401c0100522189000525140c0c0d02c1108450305001510b084c0400c40702180805400240d44034213a400280a0010f40c035000303503451619220700b54803501d4050344400400c81c003828450769108108060708040c020004c00301c0045000d0111320701c03100d8074401e00384a1054414812881252488414129604c0c0c0800d030f080e2101128065103424070f0007070300c2800d03d4081e07210144101c0342070481e501340a451100d00800000041d50810001429030062031500d2003049074030540a0000c0e0f41d00a5031070421324400190001c040c1e01241c41d110000d03013642c000000b980e0880908000910041d181d05040e180c00c607a040d148256a95101c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 716765368 1250 716764118 716764121
    0x9010309050c06190813052e0c02010f0609020906070f14030a020109030e09060a0e18030f070204050f04080a080a110c06010f0623070f0f1a0a090b0f0a 67
    0x102d021580700304007007081d08212421001030210601c07141c444410035154650050400c1400c200001c09590000640c05d0100240101c4a4041c24035140d40c85403030718403201c3d4007042d07036a0b802805005070b54807808850440580e010b10401005010005c502c2d0444c6440440d045220b0f0950107408840350445031001c03c4128409120840d40c20015a52901101d0700024007070001c82c0015000100c3c00b030088583d9180600c1d4150142034028003401c0d000e45420340c03001101c04020304503d402901a038541040714424001400ca6502c0401550f60343c4189204110440d20b01074101c8088966040c1000000394041040f40d40c0030100341400b450030b541c1c43c080d00c000b600c0880100350791201d001c2070b1078610140c00640389051300c01c6401e002c0c110076201e9030b007281c1500240311640c1c164102070320150442000b00f001010180e014212022561400340c4440015070320111045500c0305c1810b403c001304502e180707100d6030004401030041c03006c444640c80300d4403071010141105100415610106030a078030f45 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 716766618 1250 716765368 716765383
    0x204020c03040506180a090509190203073b040f0615050d05030a172a040509010602030406020d0906050d05060a0e0c070201080a1401060f1239050901030905 69
    0x14425555160582215a000220800d1042c0a86d62104002c20384d030b0001c1c042c00c1d01c20b07815500189412400072400b82c0f40721860480a9806006a04000ca14203502c030741c100a0940f07800120004040c03142440220012544400d007900c0315008003448001100c0c4224603540345e400c10404030709070080c008100040c01c407640c042070744400041a00020420084060041c0c0030041d115440641501c66494800442c100c55029901c05c408800c02d119041c02410201890030072000382d8202038450340400e8078203100f03030001d0703025038004241040155810001501104102c0c80c00f00300d4140f8110303018189003d044041d00745681c0380e00024071304c1d071602c500510050035a10607204490a001031503009583c0020130582c00600c0d4500001d80e01245400780490360200100980fa080c0c0ca42541180c12420404001003000320b03d10807030140e40054001c4558044583d021014084100e1584a29004a11803100c90030f4656070032012060350040d0503942c854000382030108050316680340441c1071820 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 716767868 1250 716766618 716766629
    0xd12020f0301030c140d030905060706020702040c0804140d050406030b190e0a0b0603010b0906370e010f080601030b03150f010620120d0227040f0e06040204020c0304 73
    0xc000c4000014014158001e2003140c0c0c50100421901c1492028040610600c8001402046031941c04000d18244080186141401004014244078aaa00003070554803480c45050001c0c030890b05100602041e150507103a040d6820340141003030500c1410140c0540114440c210a040d40c550540005840b17002030119080d0540910001d0301c0d03120200780c0580d040036110039440510704460740007281448400c070703416105000b0846091181c10010021198030042ca401b02d40c8421aa07180800d50a907803044904c03c3c3c41070009040f4440c80d10703005003110004107801e070410034120b0281001070703000f21415801590030728000c00c1c0e44400c4004a460701c0c5862030f882009242c1d1104004011034031a001130b060744d2640e603d61086541d1182c1d8a0b0262010341d207046216048803d80c0d4241d17a01000c010009501d20b0b04015003403242c0c2402c0318006141c1200c0703025002e4002200808140f80c503100b052200d1708440c0d810060078140180701030392800002c00090146500103821118030b102041a80d00900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 716769118 1250 716767868 716767897
    0x2060702041d0a200a1809140d031a0f04050c09060a031b020708030307260108150a0c0f080903040b0f1e0a140912060705090306090705030d1202 64
    0x202000c2e401e56900b0b0707031541541d203c00d680d507030002e09513800000542c4d05000180364a402030b08152902e4407990880003050720a6603202c00003030001d011004044501140807010f4454403d04100c00380c20350f91010150b440c450b017408000a6183e0742c801c00103030605400e4400040e10394810b090716005100e05680e84c7d503c20004140380b40540e034150400a615001d400380c001c1130000e40801030780d44145900641c2600d401c14400101c1c52440b03070b480841032180340b400c201001c05101146a040c3d01c0207800030032154004440340c0d02c01141d0109050f41000412800f0042c074000d6100003450001c00d500070274100300540001c030309220420003e441c060006000e695a039003584843c0780321560f102410000b5a00620380115001c2c01c1c51005903865040c00ba200d45020601c0080000308a41c030029007290312081c846004011104108140d52040380c030354549170364480c00481010319295004028a48a40c0103042c284071546020820824500041c00c06880d00e40303182070148007034024070302c1c80350440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 716770368 1250 716769118 716769161
    0xb16140d09050c060901091703042619170a0c05071e120302031606090b0a060f090902030c01032309212b24030b010b0301030f0206070204 61
    0x1000c90340c041c00c44540b288040340c00441c0400d043c040e0302c1c040c0e20006070110b0302401c2d003003004060b0801c95024244080040c3d034500707504d80101d110985075801076900d003007020040d007105514007040766204142c80c0060f0100c1152541d62015004d5400c10062a640280814048541c07802410f14040d45607111054a00c0385498400b51000b100d2030700d000c0d0412a400c06000035000c0051001441c0c0150150301443c0340c800c9940c0d4002418958030700c100c40c001c4c2e13500026000701b041c808246d406031601100200d20b081c5850144051041c05820080a13240340030340d0440180e40015000400c60310a00b808129441015030190301007082074078071000d0740711002c2002040f410110f2010006151060f100c0d410f844010350829403030060450035140303407910300c0c8014440028000e1198694100220100b00d0108103a42c1300c10703072051540074143e104d150300414070400890b080d80034090f01d82c840d0198219891600c9000f403035456000060b0060704005140300a64a50380c00007484c5004604801261 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 716771618 1250 716770368 716770387
    0x9020d2603040b09010501060f090306390306050f0a030209060a080316051509060f042105070203010c080603070e040512070305090307050307080a0204022101060504061b0b1614 78
    0x10a80441c0c4c51020b075403824002140703041c022100c0d9412181c0d199203060f281c5055a0310000180170741d204199565440700d108060801c1e042100580d010707100b106001d03101003060300c05003d0307402c2130300441e01c03d040c2d4031492030703140c1c892842c0c810031603404a81d8000f00b40c6031000880e085507029044269903000c0005c1140d085c00c2810744001d0510721070360403500d412064080c00518400705840300c00050b00044081740b1140d0803602803a41190040143c00100340c0252078400414044401c0800481c601048400c1941b40c20311816403009207905041100785442030000b81c85c2d040c14000c12148400c0760003c41d0034000c0c01c00500d031200506911041c1c0d100d5440c10082e2442c1c1200075018401c1c0306041000c40c0b00d00b40810400111441c400007025034071000c0c3d003080081c0d04280c100e802c4080315103180300c1c0100544401d4500a0189407250f42d69503003403220041c5031408803210041c4019221a4850000314941500c42d40006807004951404841c00c204884c0505403450401c0303e404003150f101d01c0b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 716772868 1250 716771618 716771633
    0x606130b0d14061f0f0b1809071110060b19121503060b030109080a0f05220806070f02030324130e072c09070b2b09020d260304 56
    0x903042e09040304008001c09a40070008002030086071032802e83c45d0403c009400103c80a8510728003243c4503072039800241c2010844c42c100031a84180051030822006541d0801442020181c0c2c04200301444042e040043c091070354410080c20700d18040031384283c1801c180c40381284210030100d0f1074040c080c10000c1903c03d038485000b4042590303854540340c48000d80c0d107414415009034070341c02007a060030b14840c08800c0d00c010001503840700c00d0200410040034640002c400301030f800080d00040304449810140300a141020041400060160130013031074010035000015254000002510000d10703500b809458031304080080307070003a00850700401e2904000b071550410110a00c400d400c98074050764590040c400100c008201c00b19103444c011110921000240c0c00c254480140811216000d0342c412140c0903d603c07a051409507413000d4180110290460b030812010070300c52040a2007084602c1e0001082401e0340b9800814031840080c2200c4104140c04007030100601d202801c50301d03444d185c18940c0c2c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 716774118 1250 716772868 716772871
    0x307020f061c0203100611060a0c0504120c090c05031302090402040e060a050105011d01090b0c210307030c08041a180307061a0105030709120f062a020606130b0d1406 73
    0x1009180350740c0c000306e4071500c520b221803600c082c408020b01c2d464982c15a40300050008144606c2000000c000100741030f10403007a17805185101d280003400030741c80c1140020849045500241c1001400c20600c10610b00d801c5102c1c1401d40c0407100507070a511284001001054140c5100f07d40703000300300410408031000c1e44101d0481e9420b03241c102e04c1e032040e00301e052111160801c000e40466881103050001c00c011101501e4080d003200210790b0950003c9085144890002420100c84540003007040511a0b040c068410301c14018201401d290803c1d076500382c0c02e034240c0000340200011580000d44510390489103a142420490266030307694599041800203000c40c5081c40700510317541c0301e000d11030394410000c90784559002d9552110080c140a110f203030804e5103880641d200344103000c0130400300e01944036242201c0d040341000c1000c400c19610b4034252402061001080d50030010401030310392100b885402e0318105070040002e071230300c0540016140b281d034514090042d50f100645020312610000703505 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 716775368 1250 716774118 716774131
    0x70c0e060f04110a0c062307180302153a1a060f0715020d1a0301140606071416230a06050c0c0d12030e010b030307020f061c0203 57
    0x1e0060a01100a02040d0780349030b01000c07034107a400c0008004e071921070569079001c68402e603800310718001030500c00d4010b00c4440390005407010054052214194101080005018840071141507940c55a00001d0408602000c030000701c0900140d032021800886d0507a188040d6644c503140070f02d1826188000102d095200c0031902145040303466079036101c0071312143c1151030000340300500d484c040f030880c541650040e400c21035200d203446949980d000d00c02c2c00581120003180c0c03000500350410110075000d1801c1a000c0321b000364500306420440000e50140540e2000066440c0c079919079451514120003800300100395030a00035001e40141049580301100102d619000c078036201074514103070900c0103044000103550701ca030850f401080150300038405000d400c51420161000c0044220214035409041141100e00c000080d010940e0140c142c8107008084607900002c028001040740880e50f01e204254010348100051200070440e036440c04201e59270a001c1141c1600e07049802740303150000c0d410a460300d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 716776618 1250 716775368 716775379
    0x60105010f11070e160804170a111b0a0e130201110a150903031409070e0403031d07030204150515091507060e0d050306030a060c0201060b07030207031703040b0106030b030102070c0e06 81
    0x217050624804c0e0706050185800c00101450b86508043d0b280c03d9512039000070303050000f00714403209012028482913102611480040b8040080001084030300810394003c00044131031003040c03003402a451014a48050360a092502003440f00e0b2000c07514061400d44024803030070122800e030340d00c0d81c1e09820800a980c46510180000c600320f201285400408030f41808480d80110400c00a400c070911400760003038000e040c00a40c40e010000041d8800910310745030002544030310403c00860400780300d0082e0000080402e48901c81c00d00c0b0000d08200e0b89810380607060400820f1003a11517861514462035002d00c00001907a601ea20b140c41009003c80c2200c60348a401030311041c002060061040724440c8400130003034082039200d81d641e03600401c0068102401c56588100100b10105810b00907c10b00d4041d400030b080c40c924600d4442e13540310301d840c14500032a105000f80000640701c540280d040d01e00070300700852003090140200307009010790782c1d019003601c1c2c02e9400020300b0751000a100380110b805a62 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 716777868 1250 716776618 716776651
    0x31a040e01060e1e04080913181b0602030901050705070f031505132d08130e01090c02030702060c120715050f04050715050903060f180f060105010f11070e 68
    0x111207103440c4e440303200001644400c0e4009030005410b10000c10b9101c900030404403150800305640402c4a904030a188035036440b1207260b07802e0040c02076186102c91400480d030a411414414001e441e8080c0704400c03814017401158020802400f03001a202070b0881100180103141c0da803d2040f03200c1c00e801145600245840d01140c44914038001006426030000615080c40b0324451412540360702072820a0309841503241440d000070400307401095a16a0124411900c40c105680d43c061201c1c107a1114800d54a0001d2540c4007903000310540c0c0410340c0442c0c005441d80d801e1a1241d0800d80302410351104c0e40d100003454410008080c80031040c241c054641080700b5a511410301020703140a0341c000d40940c0c81311000704841c00c0c107203007005201003c601d130050525001c080400e2408401341c92140344180c2640411510804d50b0411880840700d20300180f02e141c0400d0a819141c0038107001f0541001020400100c01500483c007840c00014800111240e40d6521030702c0b80034038a010340301c40d24102006003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 716779118 1250 716777868 716777881
    0x70c0e0f10060305040b270d080a0b010903020f090426270f090c070602030c040e100f0603150b0a02060f13051207050f100606080c0705030901031a040e01060e 70
    0x204e2548911b600112004003626425464056031003407030501920000003131400e261080c014020201c003005031ba1503002c0c0c50308181c040c0c141a5a03098408504000818034200050798650483e0202e0f00004c0c1c0da1019261110308118001000081035201070b035501d0584001419044801428440100d01c1d01c1682c51a080c0e10030f801018402d495554041e4030000ca004441c50a900050b13040800f48508a1602c14159501002d90308112105a00341030007240400248100f403400035445152112064002c038104600700c40c0f41140d0340101c104040c2c0d40c040105001c0016110100034191244506486410141001350b03110000c03610207422a10b000041040e03140d047c0b07002000154004054032080f030039220100041d4004203800c1e201e900c140e03203038414502400c0c031a10b000c4850041010a002c3e08152001d0070740c40c00030701080c0e0300b41c00401c04200030503004415511001d00c246400700d50295204c030300c1215056400c050310351003031601d01e48502c800b405510100072900810200c0d4065036403c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 716780368 1250 716779118 716779121
    0x315031203090d171915060504140a06020a030c0507030209190e011a010e0a170a031b03050307080402010908060723090a0b030c0c0304060903060f0606090605070c0e0f100603 77
    0x1030b000542c0c100c003400e002c0391041005d8103130900c4d5150000703000600c0b030084803c11048401c01c1e03480000482e0300040c00340100209600032000c206419200c0f4005240f03458402503a645d4100406002c000c6481c4415003084000d00428004503002081c4600b1401c1014400c104844420101460035281018442045106008031031760041c4c84404441c0c50741080d00191842c501000580307501441c0042e0100e0000e00390001840c1c8400e400c801803070341003100e140250440c480107900a0104c0306000284000170703400000c4940c05801880e00344825140c84c4016120708120360070580882c010401001100b0341c0c000414105840c0d48502d0320082101c0d0f00c5020360740e12802c074210345c2028027100107002802c41700e001150030041c1e1200c0d003440c02404149640c1140c1040d0070203400607448200400a000381401613420b104c2824008210386460140041d00311400c500c641c105100c0c0200742403050102a02018004001e00c0d00407801c18075100061403842c0e034040303c5c10b083c205002d0b4004141c2d076200c1e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 716781618 1250 716780368 716780387
    0x90d0309030f21050103030f0207140a2c090d0f0806060703050c0a050a0c321201090b0405012703050901080a0612030206060a0503030903070b0315031203090d 70
    0x55118801d14902c142421141410640c00c0f00741285103d0844032031800a0b0b20a1030f00a40c000d644244008544c1c5030b0003420004a030340b1207801e400c2d004008020703655400c0c015130200c41d42c407150b010404581c0c0e00d04074500010b401d48003194521400410400c1300012940074403008a40e51518000444000140e606a805883c400d401c50342c14030220000901400c02403514003016021111a54000c1d91440c0c41c1015562084134144d20704030007045a62071148002c0e03000100010002e41480012140c01b8140f206d040000e4400c600081f000007041200394041081d0f0b98002c3c503042020320341800d0442c082c007021000d4034406a585558045029050020a0f0100d0383c590340c0d40740341c0300759032004585038100a400000801d0756900001021103501c41044013140c8a030700602214500b40007080b4120740c0396403007507020790410450303490a41e90114200040d1000144070a40380c1d02e90f42c160399041440010380030f40520682030b026071084104800396215110341c00071261801d02031079048808101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 716782868 1250 716781618 716781623
    0x5010c110609010c02100b21010e07060509010c021005090d11240a030b0307050d032c030a061a04060e040b06040c14070311030a0e030f01150b0c0321090d0309 70
    0x22002c5200c80700f41160300001507c81005104207511381ca9082600103005d0b25140b44141d6a54448100c00c94990601020303000703048070b04060f400d1190620000e49020043c000080c41070001c82804200180550300350340346104007a12242403048030b071400d010702400326070340341d8410000704021102c40c02242c058484aa284450381e5404d14420301015001781002a00065040c0a1600c000c64182c49d08810881c88030300030ba880c0007990014508030360a415890030780f40001102c00b1160042528002030300d090f500e600c800b000403807502d500c1c48202030300540031560341d0080c241440080d80c42007140c0310a0041c0d006403160556038580d0780c1008201c4070703070714694000f1a9a01304928122207140c0d002e0103406020f400d01c1846040441a02825940410f4408000c01c0c0c40c1d180089580c01c1c10044e07924001d10410003000200241e4800741021140c0740b00c0c100611b0b100094485504000340180d4a50f00042600704800c14000c0d20141c11201041314010b40d07520030114280f1080f80703e0b0044a4074141c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 716784118 1250 716782868 716782873
    0x2803020f0111070f150213032001230c010e060402270703050a0e07030507170f030f07301403060904031214090f0d110d0f090305010c110609010c02 65
    0x100c80e6aa0880020813015003601d1034100e10800286802c22030005040b003203521a100c07c461411841e0228510030300300c18140003a00b184030800c0050340c200e191800b420b40c031125003004000c180d00070160a031141810390100ca5003070001614451b0400906503004520840d020f21806100c481c2420704140d643d08800120014030000c64007050196009580048225070007190800c40c2031a01441c0c2a01540200d03690f50003c075040002c030b41c900c3c140c1c40c081c01009000d0903000f60004525030381d038020300580910900001030070200300205c0d0084c042c118604840e00c07501d030800c089090440c461911321100c0110340f1800070110307110103020480e445044002d040c81e12a84880d10704881030b00310f41d5440142c140c0d0f10246c002e540550001c0c0184144000402408195080341030503080501040f01030041c410320310100e07007400e2404252602c9401e00d501e001d514503d250322048500c0d10310360784090400e510740302004840f50303480601308091807103800443d803458550f035000074200c86c11011a000142c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 716785368 1250 716784118 716784127
    0xc0207150f08060f042307021f0b0616050706020105010b0406120f0f06080615040507171f0b07061d070611010605060c060f0106030903050306060a022803020f0111 72
    0x1240142d840b280c0201c00a06012804400c07403001c0703012900000011200a200517140c81c0100c441444071540c4420703036101400e040395201034807542e10001102c041c0c22554407040c0f11245e5489010135130740404000e9181c1e40950b1940d0030010345600e4280501c1006500301000840c9850350402110100c9404e5a289440140e0403011079005010066406140e59114a014590703001d0a001c1c034405401e10300d02510950034030480c1c110384484450b1031940070320704000810881d00c3c1c102c210585c0540c24034a20542c1030341ca04030014154000090071110300c501603040411005410000360064622814041140056403011500d02606d0844016041e5203c4941481100e2044190020741400030001142e86134071000051803540048008200c40e9000c00100300404000e1a21280101643e003030401c181442500c006090f840003c0000340103503000140c0071120384c4200320481d17445503101d075030444c0d5041c4002268000a1420300c1134005204200c0b1501c0b8480c010720821442d90b0501031482d140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 716786618 1250 716785368 716785397
    0x21c06050f0d03110f070b0c01050a050c0f0a020f060411030f011a010c03170f041a060102030403080f0c0601030311010c1e140f03010308030a0e2103130212010c020715 74
    0x2e00080c098003806014244030105401e20403c46d58029041c5031010b0f0f52100041040c060031540014010003c06051600340540d260008086840c0b6110000c2941d5944201180603490030b820b542c1d0b040841c5c403a2004000c1480600310203100d500d00d0480643c0d43c3c42184812403801e81d01c0c42e0034042182200d00361a00380315070245103900c84d843d01c28100340d06000025920b60048620448049202c2c1080030100004c02039800d854001e504c104081c141024240040001c0d5640030701d01000300103a50000c0d004e200b101d40d500c10760b81200c8407a01214450768503480c0003450107280098441096003028800c02800307020310f80a00d0030034002c00c4928840501c41c03008440b00141c61100369807000741001009100080b81c00150302031070043e07800c10364078108141e544045481400340c1189a420500044d122842060f04150381c02c0019810036490f610ba1010f02c100700900408001d41c003410503192a1711801d019003208520352442c0c2c090b5001c41d0b545030800d040e80c2200400303442c0003481081400300d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 716787868 1250 716786618 716786627
    0x303040f09060e0906091c090e09100c050f0301050603040f0f050109030f050a021216080a09080c0402160b19020c100609050106090b0703121811010e0a090504020310021c06050f0d03 80
    0x20050a50700d40400382e581c1c0e4809c541c1841c00b05440e20040e0760000081c107481d0108a0246644040403490a070346407840c0d102e0600880d0006018031482108d0010124003030000c1c2c8911103040319006110410341b40c507245046070082074032400480215a000041040003409141a03034101e09541e0003a020800518085050315442a0100c0c50041110ba001801290150001c1e1600c504262582e4080d54100704110b0b180180744801207105030b00410004043c5010707240c9101c0300681c002201030311910350300d0001c1060710062544071549072010604034041d110002e5088407001503000204003a5031601103800560f1300900548011030020b000070441616200014841c20380130349420026015181c5510066070030300070080301c817002080c89200c00d0084400d400d00900c03909003030451811403400d002c128050381e00d03c60041280c1e5600005402d40d14240705114030030704011804c46d81c40003201060a081c40c1041c0c0b07010030f06442c10801013200c1c02c0c002141031007000010b11420a0309040c1c2d0302180c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 716789118 1250 716787868 716787913
    0x70213020c01180b0603030f09210f0102041703041d13020a03080a080703060f052e0305040c090501060203032e06051c05041e020303040f09060e090609 67
    0x20340c2040259084a402c1c880c0101e0a890008560036050040c281011001c40140c80c1910980042200300300d540c05400407560181026265402d10704180c3c40fa182d0048024056403070f4500910406040d00c0d074042d4000c0095444840c1c00c485007030ba030704160700d699000d0380c05001000301c1c62003082008010340c80307042e652100c03c5181d481c8d448521580810502c034110741c0300301c82c6060081084080da0b82c026001c294070201c10f203410801e0704d241104c00340410000d03204480c003c2203040343c0d11440d0b00881d40030b03c0c411341881e80b110140160641340100203100850702510784e42d40d40304000c52000c01a014441c100c881d240e00440c1140c0b00c05203e42008c12004900020f140700041c4a0403d01c0b805840010081c1000d4071440d0301c4910710100e20958046610004240c01d1405042200041c0c1c000f00d59444020b81c500f07200701c0f0658520101e491403003160070900905031558000250f81015811140c292034159103e01c0842d00ea161221340c1c0c903e001c0d18101880c2e00b026070103c464400147d43c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 716790368 1250 716789118 716789149
    0x20919202209020a0207090b031c0e030106090203010f03020f1005120c07140606100c0302061b0f04170c0d03120b0109050d050a0209070801030201120b010c120c0b06150702 76
    0x1e80c0955861070000d0407a8068080c900143c0c20424041003101d68078403c142c4c04c40b000790040e0050840600e181c2444180600da00c00c02e01112901800c101c2d28254866405000344490031966940c4400d0101c0c540300d002e12080784036440f400202c00c07250402c0c0c0740d00b44249840351680341c10043c00742140c034007141d030007080101c0a80041c0403280210b45c10a18160443d55400302a0102d400d0810921070a8083ca10030102032100728042c200c0041e600241c40c9600c0280040c40c807903a8a001c0f00991858070071146401291880810b010402040ea100c120421002c100200c42c5e0280007501440603081c400765000e00410f1001106506a803910f81040d950b00105142c80b80049880b0700003e450f558540a0075181c075803000a11408500780550019003041d03550505a00d19891a1300003030803038139100c010039030f85600c3e03003600d043e0b0780d014400218130300c1d9002c007101e041086542c0c801440c182c20100b082c3e40500b0484081001410051582c0300040c2160079610b2030042290244041c8040042e007d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 716791618 1250 716790368 716790427
    0x90221060117100501030813080d020d1d0d0b090709110d0903030b1005180402030906060d031e0c0501051803090f060f0d060e01080d080601030e0a02091920 69
    0x407100807440c9106003401b8500ca40200740c2c4034683c0507015a5035140e1a00442655400f072098140c52070380006040000502600d040c0e07508072144c034000d802d41e110380300c0b5180d0000c2001e00003c0c1041040102e45100c0c01c0110200d13440155182408815181c4d401d0700c215070302da810071a110700001140c1104002034001d0a001c030b6520264400314500c1018440b2000000e43c022030011010440032406a6020100321415411030400c42c22007612110042c0c1014415010440040201401552403c00c40380c1071000c0403480c44103090001e40742e202c0001c03048800707510f840e00042e00f041c620f4007050b81c2c11000c40b0065047c0405001400f178800081c09031598410b9007445101c4043d00307400f00401c600c1140740d5000c58401c0c07409104090200068000040d141c00241c106a50140e01264142d4080001d00c1c0100319154440da0702d034280001c19401a410031100d104100f030700e441c00114000440d004400070000c00195140710500c50500c2050105020420070142303070080c10540140ca610b50854a1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 716792868 1250 716791618 716791633
    0x31419140c15070e030a0c050d172107080906040b0711070b0a1719020f0f0a0e01020c0109060c0803060105041503060305070e0105031c0e0d06090221060117 69
    0x58252410000c0034149a14082d01c2c4104500d081d481404c2c514080d105034003c00c40716000b40c1e209400a51180a030728008d0a011005c0c03414880c108850f0150796090b83c0b10141e036146102d820ba81d01c0c24000c2c044c9900e0003020300c080f403403507403040038083d10031124a00584031544503030b0b0711004107190103019441005400c400045240d201805030200400c207a90f00241d480000d0203018040c1c13042d07500c9078484001144108030032180c104d2011940c4007100c000042c1d58601c407441030303041b501510042e00c60030300b804244500380715046030391118000dd0036022144e02c0d076100030045680784114010740340022612440c41d00050015406190001814140103051580369004c3e650745041065003031001070740300c0d40c0c100144402448414040c1400f18101c409540c1400042984c502c0348090b030303481070943e0002e40c4032002c0c4141070440075868000c100c44500d120718208200545a0448268451140400050343c81060114440724001510028101581c60034186c0c030038181e000d03410301a640c002c044c3c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 716794118 1250 716792868 716792887
    0x20a061d070f080708150a0c030f0507030203180c18060a03020613030b1b0f030a0b0a080a0512090d030f020705040f020a08060f011b0809031903141914 67
    0x21000c00980b607000700502096181c42c81c49460034240750b02000850300f00d005065214545800100d51192400201140c4541c03c00800c82c010200485003510a6140006209a49034036800850040040703410350100e1010505203540c949000764840c0d41d01c909000607804580303400c0030010742c0c0072900401c2110050380c1e0303070046210381d44800061101540d000c0d00c01d00810075601841a000001800d040c02200c4036054804001d2260318152008914007000003095000a900a500540c00161007075130388940d00d0700015550079885c0400c44d4a0b001c0c040b401061a0443c0701602c45115000b4a0b041c40100b071030f28252503041802c41030304110300950401143c6900c03540298540501a6640141e9665500c10010a800b00c0500150310884040301000c00e0b60381c3c00400c40801501c151564800c15071580380040840c4144046581c1500504a1500d070a00303488441c0c556030350098580e142c0d4100311403220b00b942c1c45100901d000c2c0c80700000710040c030780340316030b0712072104584480e0080e240c0300c1c042 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 716795368 1250 716794118 716794123
    0x15050307030602090a0e0606070f14010906020d060b180607140d170c030f010e0a090c0906090c170a0207030c0b040c0512030a02060f0c07080d050103031e020a061d 72
    0x20380042d140260009220036090070107031500e10061030f458040d0140c50034002d0000341d05202d045409802d41c50601034490610201c10800c0500b021581c000304589001403414030065000520111906407904200203203a04a400c01c8a078000203410803441285405070030000325410640d820340b039880d856600313001940410004540c111429450740c075010340c0d0800124084c0040109071884101080c0f0a0060386a0314200450546e1590001e43c0c0d03040c0d0300c0403c0c4000910b09140c0c00303006014540c0000405028603444002924a085801c2c015a1070081c3e0a4031141c02c3c442e889c6080642c0400018034032040e030380c0900092407007803505045401072504d81503c0c80c10269400e03900d100c125002001a46015800b071600030300040f001d07600340714100c1400b0751610b00c014207118900c02c5600001e81454880401c4602842c1d000f03440a880303003140035001d4010031090100303d01080410651084a0881110300820b1035140c1c2d00410604c030555641d03101400c81712108600d1030462007030000241109 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 716796618 1250 716795368 716795383
    0x1c050906070c140f090403032a05030f01050904151104030f0b0907091104060c08040f0b030f0709050a06030b040b090a0b041d0c101101151706070210150503 69
    0x800a074a8070300d040290366030a02c00900f100d64400c2c4565000900280c071000c80c0d03180d101d501400c000401c00c2855000144085c850100441c2c201404c407103a12109401030b02a500608041d004842217a80750814845050815503000c0e2120514040b031501c40c0510760807127081c0803480c1803107d08156982e55031031444048403a041324210004810041c030781800304a098000c005a00f818019074040c03400f03e010358803490198508000340d0b882c1a8050082081c2110010000c00302c2080042d5a01c0000e414035400c00e903495035032070402c44042042103206010a50556100620302000c4a1414009a00900c8242c0304103400607290340042000d030342c0d080c0a041c030070300b600e4101041c46c0c880c0408210468103000c071118030003204500b401c5078a100020302400c0c0707440705868a501c956001001a621a41e040910303003003641c00c19552500035040b203448041160000d22514508030324100c3c00c1ca440e0303542101e40d040142d0003076200c0312085480f80c02106d500c04c044006d9080050300d510100c1d040455 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 716797868 1250 716796618 716796623
    0x703020f030a020a0f0e13090212060f010609060903022110141911030103060b060c0304030614010602030307120f090c0f03020a05090906012723010b0c1c05090607 72
    0x10f000c11003000c1d1941000c1800b0f07140c00207150404500c1003075000103400007140c06c5d090310b019980340d0800c81152a0072580c802030018403822980c0e5894209544079400f607007401040c00081c9038820002d469401201c2c0701e01945c1d0300034071a0b41940c2000e09a01100c00140700316210380e10400710114105080c1e807040400d9021040340b4810f0b40e1502c0107030000414003004030200101d01c0c0c10083c400a41c01607041e2415281c1c0160b001c40e1103444000051001e0107140300d0b602a5000001d800800c21116a00c605125040c2d060320110680c1e903100260b072240400c417141004501c0f00001c040e2919100d62041c8034402821000040d4075005071501710789034a460300b043d8040c1044440c140213515040803480010700302150017800900c2e040f083d00b03031600d2046c4501848224810411010044290509801000e00070382c2001403d00300c101c80c0601200d101a030490b042000400400d207550090100c1d45001c900100800c40364090880f00c40d4020112451071040200070300180b880c135035030000204845030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 716799118 1250 716797868 716797871
    0x60a050601090b0a03150f06050d0903031112010f05010e0906040e2a03010e0703030903080a0306150e0103140105030a0b1b0301170c030106061b05011d0a1a15090703020f030a 77
    0xc0e201c0c1200d141b441002c1e008418450b0340c031802001006d0b071040840e90f42554000c0c001c6291302c2d040ca0f055000e05061100440c0300d038004a59803600b100a811100d04840c40990080c200540d01c0b40191101b070052100c85410290500004403542000d82041c0043e240c1c40044030681c948032003503034044d61100d0b90396078140001d0050540031490240a6280b0141070341d40640001441c50360041c103000324900c4010b081242c007003400c9a0460103580100001c1481100b91a0b01101c1028003c00072000000c106000ca850002d0454880c0b03c2c260000d81603580142c01450a505951030307880d400340c0f004140101c0c2c9400d000c00d80fa40d4600c014041d50007020800c0c001c0d80302c4440ca4250718103140460b080c45020b68903100c001c102c002c0d84903210003403415019500018611250406034050813848402c1e54400500042c6603001d40000200c400d1010301680202e030030782c040e600303001403407120580c0c0011400c00c0d203181c0459907103008818290012810700300181341c040c810b40a290a9042140d040348020b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 716800368 1250 716799118 716799131
    0x18051902090105100c031d060403030f03151a0d0b0d03031d011b050306030102070210270b03060f130e03041a120c0c07030c0332060a050601090b0a03 66
    0x40c20907000003405400120b41c10803070b0f0030b505280180900f96082c00902045034417542e5100b4591201400e03480d50030050710b4190f4468482c20050429081e941c1c4210000c0e0bd03041312400b95a00300c101c444251b03100414100b1786503180140844041d0070a00342803c942d60fa45601260030b55030814a003404a100b80c8001c191a0660f04082440380c00600c8000e41e01d03410f00c1c03034811041d65011403500c0302450a062964407a01d803030002c00d0090080302030003904a000c0e074603025800b503001814000341d001d46030119008001c415441503050380140c4603101c010b841c188045003240c60044628900b610002d4034141101c0c408003c0f00040c0c4482100404450f0000507003403041a140307da1249000c03090207002480c00c100c8400100c000e0300c0c000c2407064407500100302c1d41d40e90a0709001c95001580c100c9143d2201c661a414280c86910208001070042045d800ba03e909469000c03140c11842c0c1c1d0f840300034241941e45c1171501000b91500070852410040d07504004540c080c43c101c0600041c0e08641c2c1d001400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 716801618 1250 716800368 716800373
    0x1109150a180c020a03050a181805060f0105040b09100302070203030d091b03030c02010809070801020d020408160f12060212041101030506040605030703081b0f1c030519180519 77
    0x1c0360180381c541e60464010034108004170b900102114280840d500e030101070750005c00d8400b4003902480c2c1000e80c5461482003a04114866a000503000c1c6000b1100b04004481850040d111807180c0c0c030a40c414264248150140c5141c50311022026104c0346c240076107480240d80c002400c41e8020041100020351b155800e00c14040036600c8011020203003941c40745400d00319180501000207001c3c2c000d04205540c00043c480200501c443c40c018001100295158280030008030301075003080c0101c6115101d14a0780182201009014000311740100c0224004c450920740c01007148541c3c0a01520029000c00c1441c2802e0b1a0903a51881603000c0c8078500ba103441d41c040014151072010704040d1041d4180101800a0b42d40890303400c0880c0d40c403000ea10b81c1c1c3c140081004031151000d00d2040103500904103100e50004001c60030241d05580034200354092640540160101d0f50705680800d0a4609001c802d5070100140e070080f0064031070b207402c2944444055032121314007414403511001c0e40d802c0c0000c4008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 716802868 1250 716801618 716801621
    0x60405070b070804181d0708062d070302070b1504150308030718050a060e090f010b090d050c030106030602090321030406051b0a050418091109150a18 66
    0x50a240c181d02464075145450b07940841c000c500030b0382c0e041070801d0344001052105074484100c40300a010486503101283d500151034400c10321400b1400d02408000404500d81c20050309420f46040a21100f000030098400f4040f4070300400781000d05030308010100220f2412004184503500d2018001c5880d0242d40602c0107559410118640c807400004082c40055013040650307034001d03400d180854001b00e41d0503446d655108a9841142c02001e0038401140c0d8940c41444400c2418082d221403207075454020103c15032900921036420784500c2804241018a000911824598060801c0319420f59006e000207085555541c4100c41c50340d80050001203e0600740b050b602001d0940682d42511940c0d001501d00c107100c000c01c0102a141e44000103450071011228200350940001e05071034860b8401a07004d00b0b41d901c90700621008a44151a40c1d0001546000361034102c3e038007c40000c000c50103130040c40a468406000c24006450101c448200b545403044d100300200b100d1142c00012000f607982100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 716804118 1250 716802868 716802883
    0x1305040e0109111e130506042a0e0411130303020c030d12091b0602030a02190305190201020f071b06230304110907050901020d1107090f021b060405 65
    0x3026074140841c010120383c802e50f2840c80030303206071012480c0070002c465002c180e40c420386945621041c24880c800044200743d03c203d00c120780c2034400300b10061100c0504a851020782c1c8605007418035020140d4050f512481c449080d02c0009007021942c00400c0300f002c0301c1500320303010b02000d28070032400820501d035040140f461055001e4020740300c03614500b2001040302c28114120000c0545504d40d0303000700b1000c014806002d44098102540403911250002d489030311081c1c0c507500500c10070340e0841c20400380210300509580d140d12400d2810881c008078080040000700c00d903007595030911186c0982441200203100ba2482141d03010b62484149456440c44025600103804005101c1e40a172482d02c030b03681a10045a00c10b03688242c0300c2d983c528100f402001c0a01545803c003c03c44103100c030843e040000703413446ca1070036002d64001e8882c103401240ca41116248040d1250710000781004100b109a00031003890031140c001614144203105000510800c0711810109540481c04000130300c03000f84185d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 716805368 1250 716804118 716804141
    0xc0a05090115050708040306020412031805091f0314030702040f050108061b0d15090f0b030c10020703050a080705060a020c030a030203190510060e010318060504020d08130504 77
    0x14615541031482c10703807510314000300382014070a000a41105001d840000d8900466108100350342d51070301c1e001208070003c921030f0200e02103100b000c00c0726008a5401d40460507a04003602500c10381e074402c060010501100706c00180e10710040d40020010803034103181496001206002181e84440603c10b1001301c5400e00a1407481b030b803401d0010301c80e1400210740f982d000003070300c0d6a8554090080c0035158003032140350200580580f914942107010700007000e0320011100c1d80f4404205582c030a44081055030200783c0340d2a490b801c0300c4060582341c9800f0404066170703052441180c0000e900c80e070340c1500d003a000c150180c844002c089540700410500704102980401054000d6040a2581088550300c1c01161300d588149034000c80010301031244e81d02c1d1051011071034601031101d420302003020150268071340900400210041c13202c0900c0d5000303025030001420304030302c807076990072032910341a0042c203000d4000c90340000c0004400001c02e0000d8043c0c0b210425120452004901e48800c01045846941c0035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 716806618 1250 716805368 716805379
    0x1110703030504140301142a03070804290406020310030f0614090d0909110913060302040b0117060d0c1205010f0c08010501080f06010306090e0a060b01030b090c28020c0a05 76
    0x2c1d00c207164040d14016401441c2c00c7c0311960010440329000304002ca8600d82459415004002c0002b41c41e44900030340e000f41d00609426845a20405070b4119044001e48030348010980c50022900081041d0300442c1e012190044903441700d030321307940c0d000390082411005440c115195100c0000b0017000c10321740758102501031300500d41a01502d1001d001d070021442103c400c10341c0d640c14011807140720303000ca0303032145001815503101a00c96803098000f0075041c042a40290b140c208a000107500030701903092a03040c240444022a030310300040051807101d0081c2242c5205082e01c001910072858018174014a1059001182c180c0192005004580f22036030000100400d007001005a641c110a4094100c100d03a4200e0446544100058024010341c0d030207010210b24041f03504502a90210b40403d00074811041448005840d200440589410301955030340084500d000c40d00c1c080c1410b00405401030135031429010802d15203003550740010302d14800405a0000d00c3c0c0d80b1410302c0c101411a010745400c403035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 716807868 1250 716806618 716806631
    0x705121605060a1215050a0e160f09140d0f0309140d0201050d020d0b06030a02041a0a02070b1e030f0601032a0e0d050f070f0614071101110703030504140301 69
    0x80082c100a14043d000d40245e03529a4070b0403214040003050b070301500b8080c00030b43c00c1940d5a80d140260b0b000807107506801041d1100b045551234803a5038100300c403804a680d4451014240079528041569090000d030f400407402c0c50003c0081c900629141a09009443e5051080d1500162002d500840110a0300c86c550f1140d90600503a040b13019540640328500b00140c4807a420f0b05040028000414200d1740440f010013000b0b00056980c0092050741c1c01c05002c5a12180103982103000d501030480c05401580107241d00340004030711b40b0003402c1d600d80303402c410034030107a60100d0185180d40161449100e03019824200800c039601340c042d02022010254514030f214000044201c00c14a14424840800444000c0b50701240c0d2200c0301b024070103401070250b802440310040c10958a44c0da0f0300c81c11804008242001071802e0040c515290750400c820111890940c0c9681d031a04036003401d110303260500c800b00d0003619003ca000c1117190040d511a484242d52241046526450b00111440b1244a80e04201 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 716809118 1250 716807868 716807887
    0x1e1502030f160605090d1706060a0f021510050108010e192c030306010801050109030b04060f022503022a10031404052d0c0909070512160506 62
    0x456584102004115444070340c584000c095a141180c4003034400c604100034018405c2002c136264503040283e44400c141c081d01d407480c41650000c00c4560b1644104180070500c900ca006003008001c0504902c15540d808841404036081701e403094410240342d41c44a4004d00c500d582085146016045d5540000d00790324028403090444014000c2802d4045d0300c40741d0120340300c00748000b0411803101c4496011041d180030780810369203400c211030075400580c0c800c00001d11540032700c031902d0543c2c0c2c03c130300c11424641e00c50710341d980900951a40c5c0c20055908024004015800c0c40303051011219100b0303a031403c01201d05000786040003403604811080d100000104103031101504800000c001510300b001d903d015914190001d0599100309500c00c40700340104020810041002c6c100c11042e000c80100c0000118800e4901800300303600c1508580c800602c40e8801d00d4881e14003580300715040111a0342d1034a480100b1941c150f00100210950721000c040c405108085101c0c8000e440207407481c605010141 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 716810368 1250 716809118 716809123
    0x8010806180a240f0509060a05092a090f0a060506091e0a0b0415080703050606091c06020c0f070b07050304180e1f05071706011b06061e1502 62
    0x6000280f001c07440700b0003907400d681180d0000d035a0005034582046000c941c4808140500f03400c480e12092030180390009040d0000601c10503008d03050f40c0f401072040d8564041800d9507007c401909501c2d10001a812200580d542814a8429900b2600310301e05401c01c91820010b072465904094443d0f40144541681d54855505402c6184200010101030116100114035540c14540012031400000240414402c0e282c1440355200c203081d640703c00d999901c0c040304604807581542e800e5031000042040181c2d500c1c2c070111400100c03260f0780c1e000f5884881550f0310700403a4000c0060078415080500169801801070103344014000001c04038503002880ea502500e170f11903030082580c1050603505000075144540d11058600d40c544003181d1505288034a01003140d070406a85440c034a09180010746254850b8804840848000801407282d803103038801581c0d910f1040d140c0440003100080c1150101e2558014907004000310080c02c00001c101c85000282404a5040005412050500c140003141e00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 716811618 1250 716810368 716810383
    0xa03020616060e010203010308300406090303021902010507030b030c0a0b03130503070804050a09090c0306110d052707030302070e07120e060a06153c0801080618 71
    0x340545070000d00c40d5494403100910400314140c220f907102200200030085544018000203c501c6000d80d00da09081c5d15203100681704a49021040d030f09840401e000440d0380d04078803211482807c0250a007401c030a45955031984c00000324005030744400500000d43c2e058410145404c0b0141e0191a801c41d103000400da00e03240502c2a0180d2170400000110b102d1500b442d020640351348a03007507d6950841e410000c115070018042c0b14410740c0c00780c0002400e06054800c05030202d13884105602c0403441c64454100a00d850784001003035035001c01c0303140c6d05502d082c41154455485000b410700c6004000011100c0008503407a40c0d14941d200c02402d001090300000e10204541c5503565000141c1c2e50543e044890501d541c9403142c600742403500001b8a0300001c01c01d00c1c420880700908000107035a9607054618108032100500214000003448903081e00080802d180030301043d02c203586009000000c0e440810003410066002544441c0103104840091203600e0308182440f000503450036903100700030f856849 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 716812868 1250 716811618 716811637
    0xc05070f0209090c03060406150608130f0c050a08060108071e1e05150a2d03110f13031208011a09042c010b0405100519050904031106060a030206 64
    0xc003000242080f0001c000000140c00c0203030560384030341003130b280c0103024103d61200300c101c8496070800481c1440c800c481e0300d0311882d0b240e141d00110030500c3d202c0580081c82c401040d9500201c40d00040380c5c03626a005020010700e600c50080802c0d6140c07488541c10412103802581040200400b61000c4001c6072813a9400d4078241c0d55140030b0103130310f00040706c101030306944a160440c1c0840301030104407517a54050407a04070151500c0161908070944d020f00c0014003106a20490708068842003014800e50048800c0062184076925220410300c141c85560885c050035880080101d1090003008400380d52010360484c1410080459410706070404011071a0310b5501032400300208001e0720b40c0c0d85503007043d80440b40070070351145c1d40303040c26114210046030954030501a60030200e500010b17040c10321545105000d90390349000303010b041c0010404040c01d54501c0d050b849070389410100b4195078002d070f10b50181d446a2240900501000b01490a246000784130501c1000056030800151b00c640084518046 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 716814118 1250 716812868 716812879
    0x3270603050f070804021207151106090f07060f0912061b0504050d03050d18060608120c1c05070c062a030c1b08060907050a0b040b0a03020f09060a120c05070f02 71
    0xb0511091140342000582c0000608100c149c0100e0a040c1c202c5c012002c1e01044030182e444503551001c580d0b070344620345101d01480c0c1d4000f0380c3c200074003031180c22070001003030142c5400002c55558911703180c0501c480354401e40f44180c0e00e034841302a514040000102a440b1400c11908003494000018002c65483c0005002d0090001c0c1e099602415a031008920805104a2401c056103508000d00284058011411640708500855540d09044000d8401602c0310000170929500700302d982100c1c00030b07081c4c80403060020078004000015a01455840507007140d43c0d8014182c00b141203603003898404e42070014407100080d203ca00109038804418212290030486468030741c01031658000c07551281d540301c03458030301480e018007400c403a001c44c2003011100121401401301d03490340d500d11081e11452054580c910810800204118002e0300640010140aa00d140c28500c0c0b00300460000e17440503025900041c1201001c014800c5c0c80d200740c100340207280c5080c1d07081c181c2c1c6640709220500b51400c0603118030b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 716815368 1250 716814118 716814139
    0x609120c09051005060c0c03121c090f050a05010c020106050109052404080706080f090102120f060310020406030b1e01021e0c0303161202060f0103060903270603050f07080402 77
    0x140c06a03c07915009140c080d01d03a56071400c42c2034030142c880702c0c1008910310074050144000814080c40c070999600140e1030325940c000480401c070303250003460b1101007210440311042c2043d02054090200454040c080d070000311b440007901c0002030840310b0360f801c000d0500000c50010701081d29040c0b00c2c0342c00401a8000c0032840b40340c1200742101030080303078009211481240d00c0071030f403664060340050061000944505054071405031301d07404e0303000301d89801115040b0980065403888030341070595080803003d025a03c0d00300300e0001c0c00703040ea8010740080000c291544040f44842c10003101c00f420214000c403070b41c04c1d540c40b00300c0002d407913079150183c2d4014a070b0110100400c0403402d00c1651400300c40201125502d110422041002c0e1809460540d01e0170143d1050028050011070a43e200703d0303400d00005516803c1d40d07101c0d001000380142c190701304060305849100c07214050050300c95a0b40c2e91046a81900e10f441c00c0101540c3c002855145603082103410b00801030381141c1602d80150741122181d006 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 716816618 1250 716815368 716815381
    0xe0f1807031401020904180f0308070c02090109050412140f0d020f0406020a020a170d110309030604110a171002090303160c09050702060f06041a0a0f0609120c0905 72
    0x90000c0c035000580300002c035101441e041041503004140d8072405903014484840860621a410340c0d1071500030b056002c0d040d5805000078880c2100c554070450340d0810040c020307150303004147d02000c240c00801507a0307624010300041c415070841d480180704d01c0f440d19604509942c510b4402c1406680002d4055040103d08498400c0240c0c0503a29a000304480d059203982c5d88000096542c1c82102c3c060b4000e0710003000c0440c000c2e99480c825685070906a00400000310f003803104131251141e08005d58107600042c42181c080740e4041c043c1d5030085002b00c000c5500190602e003004011b6106074070180100b0000e80c08980391005c041070072451091188001a00c40e4203000101c1e00350300c03a00c203100c03101c07400100000f000c1081d01b5660109aa4003503004025070342d0344007001c1e0381d1000d0545e209010780b8101030000c0c102c1c0c80d0a4201714490b0306500350908182e103030a00031410003030090f0015042009002020f00070142d01000c0d1800400d03d03450204103501ca29243c0003640782003800b50108860b2107134005403a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 716817868 1250 716816618 716816623
    0xa02090c0702120c0901080304300614040204051f1505040f060c12030b13050603011805030715061503151a0702030c01140417010e03031e010e0f18 65
    0x1c858028214a0440e50080380007912940c0f6031010030712031245840049001d410000503035040d600e94a200b1000300801c10101d0350300741685010010703801c085401a1001900c01c0c080c1c907010000e000c0c188999810148100300a0359401002060040d1341200c2c0342c0c5100502a030020200c075900c0d000d140300780d02d80920495161140760031207901442001e50018078140d00054001050f4000c0026140c0d82244000c01c400782c0c0c06581710390f540081a41801d62490241d0b03405070340c0001c0000c1c0002500300089040c001102619481a9560341010076560144039061903d200215840c0508001e4141007804481840391aa08100105543d825054980010b811150000340500e0303d11b03c0c940000300d200554242d40485001c81c020b01610b4400c07007640d4000c00d64004910200c40145090038100b5008031902a00c0d01104140c3c1c2d0348441da03e8058500510085014207154203451010541d100031a2a0b00c0350306901c4813154020780000c0002005060080c41e40091030995000e1013610020700d4170b072 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 716819118 1250 716817868 716817877
    0x9101806180b06040212010905070329010806040e0a0b04062a02010e150c090d080d0501080601060e010f0305070c12050414030106050303071b17010504030e0306090a02090c 76
    0x20036032860700e41040c08240550180941e014422000300316156110703001e001c164040ca07000151004e0708480180310504154000c0359000016150004a16011851400c00c1d070340c81030121003e030000b01c14007181a5a100c40708a81c0150181d07024041d0000d0b400810350f403080c006601506000c0b6890114041252503040f02c495001100d50b8111401041c440709aa00ca40c0013051301d01540c83e08840c0000400f0214201c0001c21000c64000401d80d5005600304aa90100c0d01076584202880c841c0380020310b584028200030500c0e140009140e40c10840150f15006041e0089414003200c4401c0048a80c3d00241c8000c0900e624a4042200d451302003043e601460072510040c84442c44440341a80f541c0c0c800040d00c1200d005020501c40004e0800c1890308803641405441d80641042050342e01040550740403802c0211040000b2150039130f04d03c458010361b6000d0312210096511141840240359010200c03200000044020344200c0c14420045030355440841d0b4001d00440e04900000c010070801d00a40707 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 716820368 1250 716819118 716819123
    0x1a1512070806100212030c36180403020607112109041103040c03030e0d05190501050105010903171b060702071509181e0c080f070203030c0304170f040b090f09091018 73
    0xa6002c1c2c408c29540a00d1300e00c4043d41180503003918118450b80181c421001e034001c80e01500074180766103a90304121403240c3d85180c651a68454200d4041c20049001008508000ea001045899015030700410040d220818000c4411880c18402c0c000030401804003102140e51600301800c442c40c0c40804200c0c1c41e1248440506103029082d01402c0b1040d860b6940c0c0600e500c82c00080103d40e8a83e00103444004d203502001c2c10b5440c00c1c0c0c05900c00302400700005e0138a0703000301155241d18040000c1561402c0700031608080141c00c540c50403c4112040d819030549000755081002405040659015610411040761107003251034548102504210140b00c0300f4800e49404244080200300d1000f601612050340c900f0002c0304003000042d030740c62020050743d014140341c9880a107140c540741c03120361820703500c114000740d0b04d002088080c6113039a80000500c018038034544005d803940c0034242001140d0340300d02d40f80c2c1c0c001e01e1403104000e017104010490503144400600c0c00245e150501100c40011031000c07100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 716821618 1250 716820368 716820427
    0xa0309170c01020706060b0a020717010207050105180709141915091a041a060c1c2c030d0309080d02040e0117011a1512070806100212030c 61
    0x39001d8055064000b004054000c100600c1116507902000d20244103000354940141c00117241488007107181800e0908801c5842e0001d410001240c440c5421103409884030000b04007000080c42243d07000b40b0079a002001e0000040150a00c1d00c200f100001c03034000c1801c91952400c04810b400c1d5a00303a40100088402312811a040584032594100100105d607000d41d42144041508416450700703008014003025610042080950103006010a903040840201c5980c0529580300038500b80c8400406001c404a5541000d0315414258440b110000c0e00c04004c0c011201100c1a0300d29100014011001d0441e4a8001104100382c2000c00041c080c500402c01058000140081c1000724594954140c5012403410086406110313600c0b422241c40614015a01d606c01290003424500700e082100b540201810f102e10304518400c1c40307101c5003400ca5000001c20841424843c4030f040440b84502d460040380010240c84056404880c0340d07000042c0318030020351002402001d99030600c44503101034220700c5007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 716822868 1250 716821618 716821627
    0x60c010e01061503060b04210807080c101d0715030b030a140c031f021e0703020717070b03010b0d020f0c0c03060a0504080a0c030e061201031a0c0a030917 68
    0xc40d003010f8501d403148000682420008075000c05500d00301c070100c1e414800b441007682d80c1c2d140c8800400b03421140584401d0b00c144480800300d4001030041c00295a08006010700307012000e080801ca980c056101100e41c5500440e080759443c000900c402503441e103c9102d14120907800c1d048004e0000f800c0c0c5150540290202c51041100564808140c90f100300305507070300110076100703141e903602c804120b6401a410b400d00850550340542d000300402c1d1151000c1c1c01921544400c0718220380d01048003100181c4c02124100940e0128515001c641380c0002c0c09002d46910b010b0311a24140410300543d031100900040510329854164104d03441c0c1c1510000042d00c0c0c5040f904690348651401e0002406400b503080010043c82141c49502d1046501009081c10a40e0720751003122b8240d00381c9021403c0c0807400302c44040c07607602c00d070141c030a0f140d5041f0320702d5482d03040d8501188601d80d85100810aa6a0581444041301c4250141e0f006440240360000381c0c40900c3c101801400640304001c0752503100000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 716824118 1250 716822868 716822879
    0x604150e06120316030903051c0912061506050c0c04020301080d120e0607080118020a141305040e01020a090510020304120c0e040c060e0a15051c050f0106170403020c060c010e0106 79
    0x8031b58103d03402102924044440902003050b5041c10b00c031200001107004000b4044071401c0c41ea1706034030340d000f81c1c1d0004034000703409604840214541c00030b90100c1c0c004131756400c1010003040240900d074020380e02581554501752045a640c80945c1c0d15005001c40f92800c1c3c0d15080d00e41c0e04c0342c08421030504c11039a450070500400383c442c0c802070051010039007458442494441d0503008844442c09603544100070b69115940c89612500b1901107110980e80842e80003846544901600713400c2c941c03500006907181c01c1d04201420594103540319a01401c19800356000d40c6030080309841c00c40d4400280d6081d2046145072803608a03195400c918181440d080903c000d101c1080d2001081d980e26448070721164030500c00b0890030100304c1c400d0f80d0b10b20003004907114071944260003420406c1c0b0745142c02c1d05503001040c0300200341c42c01141c440481107a4040100034650740403035064441c15001001041c2410280c80094480312040d030483d00850000600810a48095002e9003040803094020454141c650 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 716825368 1250 716824118 716824127
    0x1c050706051b0a02011704060e010c051305030c0d0605190f090611030f15010e030a05010209010e0d0c06141209010b010f0914090402030304031a0604150e0612031603 73
    0x100e500700380c0b540803400c0c02030b40e0907001880ca080590142c60703030469903c090343d99810941004208451041d1245404030a4032001d00448034210b51a8030f442ea211079074007001d60380e48041d0b0303031009110760302c40d2581c04940e85070008904009600003901089665441c400500710703030700304010070402c03070700c0c00c1800c2200b07035010380c0203800507446028140030080b03d844545015001c103481d0007140a10b9480032408446154034800d5070480103050184c198119080001d00300548001c040d64665000902000590707404850f48503000303422541d45100c40801d8484010300b9815001c2c030703010b0090442d40c61030381220000c00e0b42c3d6600204820200c0c90b00d0010802406010080c00082c003040d000d01004c4040c030701815081d0107940d5284200120008540100002d4110180050360180001c10001c4046000d00008943c50321015600440303c0c00c0c10401d00c42110b071000f84100005a4070038040c000728801044440d00310200b180c102907219103600c845030952081400d89188210100c1f41c0004040e0030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 716826618 1250 716825368 716825377
    0x3030406080906010905160c02190e1602010e120a09050a090f0b030c060d1d0d170604020702060304060504060e100605010305090303130305030901060e1302040c020d0203091c05070605 81
    0x24001c0e12100d03642d0b296080f040c0c2e44113847c1c240e003a603d00c80c40d042d5007500c80c01c03843c00799a0004050200b100f0100b07005000b14025174015080a81c216000c02031080040d40502c40305088510080009101040c0041d4840c45005d01c0c402080383d000506500080c0301d251054060300e070040090300c0e66580c0d458500c0c01050721130b140c20384283c10583c5046007031801083c0191900c00142c6079a1810104042900040030610030000d041c0510b020407095009040004090807070164441d41540304800d079400417800d10041505100d50b004200380c0c00161a0f0038160703500a68081c80c041020385071441d203200640541410b00c083c80c4524481c0b94442c02d03450300048103d0f2802e803420001d070f07103c0400c81034032844100d405901c208084101a80000e00c40c0d40119400038501c17000107a12034944c07a542903150415102d81e10b02080010355401545040d105018260440740005d00d01000345000281d01c80c001d25a6851040d0302c54044140811250300da044142e80e400416502e4560302c5603006481a0030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 716827868 1250 716826618 716826631
    0x605310806150a05120304030b1017060103030c110102010f0e0715080c0f0c3c0102031e0604060e040b1509070e0d03111501051306290403020303040608 67
    0x262078042041882d00c01d204101810000d04071014181c2040e06000002d0000e64203800c07144410403001001c560394812140c01035100c000c0109030346180c5040c0d20b40001c1b174a0520302c2580c0044c80100006900050070700301040d4030070040480c0f880d0f80d10040c0d0041607103042080210b03041c40705e0302244503800b0445105880c611121208498074050741142c01c900704a0ba104050714080064004032000c0901802440c80307018200c50980f1a1092101000120201e074503030758190304000c1e8940da242c00c0c80700c8920201038100850030f6141411001c00d862640305000040d00c1c408901148881d00d0307a070080400352008410107015410300c0d00c3c2013046008112103441c00e01c080040f0305400c1c1d29094140a001d000b240e600e1a40c4c0e8003284c0c04100004a050705e044041c040c40c0c6032544c000000a1000b9148030762080c04030001c562504003132040300c951504054810303925007601031040c054051a20701002c41700603000340c02c03840b4058448802c8c0c41144c1000c0d50520020400050311130f40620128820340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 716829118 1250 716827868 716827873
    0x7020a050a151b120f11030901140c1f06050a06030513030c150c050d0b010c0203101a1503060f03191506080f06041b150c02180106050c010b030708060106053108 71
    0x4070412006d544030b0140400300c0740020f0384090ba000c00d4038581740140c4954401d180c255020881d0198a40b034a0300090410400c8250312000c1c20030035440c0c10501d074401070026040511162500300c101000b00340051708002c0600103180441d4091002e01000141d000301903040400902c03a0703d4034080c056030009900c94403541c2c20507544c41229442481a242c0c0e250303000e001402d5103195030900002a003030071607840404558001403a0441d583d103042c2c10050003c000011507407818001c060015406540220b00e0081c1e00c08000c0c001c4081c120704421403d2608030901960f082609501003020740341540c860403451058200a030480300c0b0101e11203018610428a040b54003802a4440d0341c04c0d04648984001e000d10145980702c180d000300525100300e44000e00e1080118a49000c12401d2403082c1c01080000390b001c0ba11a46020007486812400c0c08100d00600e503103494202d0f84c3c1e07030303901d01405004200000421840c84400703162101150084c08004c590741950304002051007205d1441c8210520b91 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 716830368 1250 716829118 716829137
    0x6020307031d030408030415020f0a0c050418050606060f120a06050909210a0e220e01050408090f2b0303060b0c0c060a021501090207020a050a151b120f 67
    0x5500010842c4e04842c000406035007014a003041c0340c2c0032840180701c40b800398003a000700c0128071a414404849014409d182e07444080c0d0034403090004440b1078442d115500da2001c00014081100003440f16489070040b41c00c5039990300c82000592240c09240e903008881c0680c403050000e014800d400c904282d0b0b00c1603c0d034001e90380e9510409695184040c44003030900280e40300c9003a150301d200000b8000000642001c1100390300303000215550441c071461560003040c13034021480400d252800f4603d4105130020080c000d40c1843d0701c51141c10f12a010b44144a880740e1290455240c9403680d008444a00044582513460900000c0070700041d80060100d00181c60319a02040c45001c0c081591500349502005083c11170f4108103202c102d5010401d103c0a51107500c603044000c03184190494043e244280d00940c58480a20601c8131444040d001b5a1244d04c40140511400501140004a080041c43c01c0c0e51000e948040800c82450303d1400a40310149404111140316080000050510607030b03038642c0200b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 716831618 1250 716830368 716830421
    0x5120a0b0f07080f1302100305070e010f140a111c2a11041e0b040b12030a0c0204020409020a050c0615062704021b06090d0e1c0602030703 61
    0x141c4004503003410202c0c0a010204007031900703102c0031542c4500c40c5600404000600d40010314448040804040000c0d107580400031081d9000b00c44c0107614100f820401d079901900f60300a802801000c54040111101040e00700c0031510501168840c000e441d82943c040c0301a415048011485181208022428003000911403080b104100700001c064404101c0480c0a240d50b043d010041944c001a40316440b0a00c0344680c5080d01c070103461110804200080b03942004043c4416070340c5070010203100b030205000f10090752101200703c481900b1546040000c503800740c0300040c0217000356040486094030104c0c4a003421078111004104000200d000c80340ca960761480d0210281042c0c03505980c102c030060011095015241c0e076100d5505185403002103051861801003002c907040b0f0f1941116003695030101c2d081c909070500210350883c665101401f100405c03c240a07003403280104640d40180038048480c0e03100c904103209403030850352044084d036036801c040c100200030b030040840300d0340301c500c040282032034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 716832868 1250 716831618 716831641
    0x50d08121b1207020a08040f0f0504020a0906051b0304151803020a05010c022841030a0c0905010504180b0411031603030216170709020309030405120a0b 67
    0x200d19001584051800740c1501e41491282c401400c01c3e802e41c030034003804400003400c8101030f01c0500003004a00801500d0802e400b0b000480d241c0c0824011841040490404c5501c02240015119241441d41d81d400540c103219100d40340c0e00502114070700000c58003066180760801c680c56903202950340c03100f0b003c0701040d0f40014461203105c025404800110304100e135501903e00c1e01c5500d0300041c0412801702d2145610540307210703802840c0c8003800021300240440b030b000b51440410705c030740341c00c9819210a001e03442a80c03460042d01120050003900011005545c0e08010301c0e40ca00e1703400010601650360307a01c01e2002514081c001e85104609040ea0310b030a006d0f5071810a50034036000301c514001070700c644d10707810104503185802caa09030007400080d00b09010030350b02410042d4426170042003c000d41000080401320b0540081c29040701817010840403c5d00000c02d0019508000030041e03403a1210803180d491807040ba40a16040291618200310a003c08601c0140442c00b8080314a540d0340d0781c0c40e1800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 716834118 1250 716832868 716832901
    0x1a060909031305040b011101020d0b12030315010513270c03020a080402091e0f06130902090a15080709021909031a06030304031509030e010206190b0a050d0812 70
    0x950000c0b15880c104103900d010303007008000308418140040305490201042d400c0e640a410320501c0d458840c4510801802c251140040b000340110245041d0b040003c0c085114a8102c20614100140881c0d6031000c01002c0d04c03158000c1450f1789014460340c00000c11103c4a0103000c00c0703c50780c035142002c01038038039000c0c4c000c4402c0144299038260040c1e546500300b00b95110050708060896400036502c1200820070b03400b045c050004203070004540e261110801640c100050200c41081c0e007044001301c010303284c0d814a9504280702034004100c0c80e001007c1d0441810172540400c1d114840c0001c0040d0403206a4000e2465003141a40100c0060181c030040e540c8103414400205498040604130981c1081d070444039070840d000038152864903903030352103024401c41d04441e8900e06e030381c0c2c40c0b03502c80030550000034524003804280080d00441c80d020a2888086000940720400552641041425075603244850005004001c0461501050790305041d64581c01110b5014480803031703c030110700d01e508243c1155 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 716835368 1250 716834118 716834137
    0x60105091b0c030c06040f06110f040902090d06111309181407031b080c0306060625290106030506030a060b01020c0a240311251a06090903 61
    0x1040c1c860103080341070070954888802c82c8080d0009218101e481401440064025401040d05801d080e002c2d051401c01c607031000c1c0540c0c0d4215800c2106d05080380c0c815013558210790002600585882c2030304085900c001e250031000b08034615054159106104500c09480301040924190640780d48460750b14046450102500f0781003585401e20380e0008140658180a00c0303400b506440c1c5580d0340303545905042d503420610303120b1855007420a00056a0030008140c499104a0003001e042c10300d440892060300c6050300454005034020041c20080781842d090310415070b0701204651003c044d607806150543d01d42a140030125184800000e1881e100c3d0240a0141c98001c01a01c0c6401d1981e07694001040d6010b1080e0550203503044620281d9100d0b4039a0004007204119151484810049108412941c82000091500e8200d8920228110030103032540c070003841c1e9074825a400115120314a00042003401480481811552032a490002d18418003a010689036181c840d2100380d1807035260700521080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 716836618 1250 716835368 716835391
    0xc0903050703020d0521071101030219081b0301180c020d023712020d03021305090c0909090c031e100b040b040204230d020d060507120207050a0506010509 68
    0x14009464904042038045210704101c2c0c184100580003400070890030030900c901d21201240e0307e000e2096006001c0519902403a0846c9400d0000400c0c41071113240c1c10350441001540000103000000800d007a5521181c03071614075459603550340c100820224100c3c0c981300744d18200144102e140b800055040010100354014144459440082c040d003103044060403628087d800c1200c44110b04100e0102182c2409040c0c540e003c0d203407210340680b03860000c190341ea003010710411800300e140c5151141d07078068403800c0315058400d4603101d4000440f40501c6114962200f00c0105100f140c0d9400140d000c0139810540503035011190800c2c070700b040d0141e001010016074000035502107503100e403603004500554004000054045807000441c08a8102c0d401142000e00c0c0c050041156141c803106d1514005802c5035070f209062282d07408512809580c0c10010b003800c1e00e4002113000d550003000c88880004103039000315101c2440c1c0c1040303503545200c94001c1c0c501d40900e000111303085c10102d412510800300d0b51700c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 716837868 1250 716836618 716836633
    0x60b0c06180a031d0a0e071106010e07021f02070b0c07050c031b130e070b070b151507030e18070e0f01082202090703060e011d0703050a0b04090c06030c090305 70
    0x2c00c41104040104803030b440405a43c5c04a0001c0c0039444841c02402d040e51400c1e21600d20003030701031400d00103810031120b100481c8100700205500203199001400d5030301c4680d00445541940401a015203d801001c1e10005002c10003003003994000780018074003880480c1d81101d42d0340d00b03164480600304303020320b114903c0d036109401c0c500700a10582e200817801040002c900f040004e069003400101d401c0310258102c0000d030a802d12a546004640040140c00c50030303122220f0300c0010b425a00342d81c0f0314400c41c140c0070450b181454091241e240e008c00002e001a10b02d2281882d1503043c00c44c04540700c50105025061a072180c0c00c3c190350916584006031075401b040d45038000d08030762050460300800c814000b2481e801c0c2c01602c030503000d5402030480da00c2c0864034600704544000100c005070881d2014105540d001005e40b11214040c540000c00341c1000a040c2d200c1003580d8000c4d06042400642003402c250b4080100b08240001e0412590315540800007445145000c46600300d50313120142842e404100c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 716839118 1250 716837868 716837897
    0x3010e15030f010e011a0108010e040b100f0b040e1501090e060604120b0105040533040e0a110a06390212010515090405031606060b0c06180a03 63
    0x20911905400c0080840d816001460300850a64194007000d1040381d440d1400300040308044a81500c41c60424242071705658100041030388820401000508811100700100300d103003c080080c1400ba0068024514002d80c0795610240d00b64030a1051032003044641e030005948250a40c1c0000405405031f680c0a40d80f4070b0701030034104684002c0c05040d403165081200140400007890580a070310301c1000314075250740c0b516082108842c0010005800c08101c0d00c01107441c1144100e40c00040c090440c0701e040b59002d40c101050081149048404981c0328048458040c8a2600d401000b50201102c1a0180c1c98851000300c03003013004002c1480810784c5181e420780d0b40b0ba030905042080050080448003503200e503900022803d9000d80c0c81a4066551902403095139204483c02044600013591051180d04180c3e94255882c800c036808219404200185a8108003d91f0850710080c000c01d4a216150449031079110b8907050306840e0b5114440d00501042088c0078080748002e00190141c070340841c41d10080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 716840368 1250 716839118 716839141
    0x30807030501050f0f0a090c120b01030b03100203040606030b0405010e1c141e03011706010b090a06031d0318011803050706050711030d0c060b0a0f0512010f0204060302090a0b03010e 80
    0x302c0c00c0c0d03a10920441b8046542070040c41a8142e0306001d55030706e050025960421003c542171504200c0c101420880c3c0c3e00c900d078400040002c1e000c0f803070180c0107a407551340c0e04240c0010912504010207120501c0b0904c4140300c015013008800d03034946c4050b02d820010301c495888041905190400c042a0440310710341c0034202c0032f00680072003620544c0d9420441c41c0b8605918a99109812501c1415600d0403024a0305004008a9003d00528000380e4609007031203001400b10521445a0010036859109408250303a44819400100710392f80c084075100e0220f80001850070040c61007045c001244801c2c41100000540182c400700c90b00000600781090900000302c4156101080940c3c0241004102c40b202e0f450400c000c1d020380080b0f07914140240810320b0a402607940313100381244a103180c24020300c8100c000c601c03032200302c41c403c0720b241c0e0180c11859030680c0034041d040f9001168a2000ca03000441c0780c5c258006010f000012a2140c5405496516000442c0000e00a40b08c880c0040b0001a11403a0351 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 716841618 1250 716840368 716840389
    0x910180603020a03020c070f21020a0e06010e03010911030f030717030c0705070902180105130504052e1a0a05091e03060a0f0f09080316030207050f0a030807030501050f 74
    0xf01d240c054a84001610703100e2a1241030381c4882c245030b005080c20003c10200400c441c0005c0b21908901141403141c3d00021100000c0d4011440c3c0360a640000c40c0c01680100c1c4207102401019000b03206087d814146070f4440d05407c3d21450103405a044d0b044561800401215401c0d40e221061a5001c418004016110380005000c060a10000c000e140045001080014020481c00b900940d4510000c107641c9080c0c02c1d84030006050000903c001080c48028907040011b80c0c0d41590700052036607c0580c0080343c001038200034149100d404c9003070f455501081c41100c080d102d0122812103e540411030a0386c89108003910030700051018007603104d00b07180c4250f04400c040e45030918000e4a00455002900702202030380c80c5a103c035615007a10404022034020020b0b855620301c0108455405629100b15030301c401801c6020744540f10b030702d140c00300c2c0c041d5040e1200542c0120803540719912046001d035a80d0501141034000c03030000c10004000511901403203060f940042c1512509100f02814001708840 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 716842868 1250 716841618 716841637
    0x10212070215030c0301060905060a17190f05010801180b040b040f02090a0507030b0f010c030c150c020304030605090c0a15030f1811030607050a080a02070506070302091018060302 79
    0x40c440302200d40020001d001c1d60103112504e541c1d81d5a949000d81c094001c5805600c0a030143e1000c0c007070700790071940004011440c1040005050100c0d40e03000d0200e218242c80c425110007991405400d0442a030540d8801416141500020000341c80302000198652503440002414148400002070000d0a036200440d0440c0c0302e00f01800c19083c1c0d6500143c0101011181061000e50742c02c10400d01d541e050191000c210750940340d1416618a100000b440d2000c1c03060027a0620030b0403c00b110400c415803601c1c4060141d01c030710400c600c0c00d90880081d120f504c60310003515418103150100783c94040202d0313101c4214000921107000f507890617600c14003102040c2c107241c05241c0d0360b59800301415503078015401c113024090025030000140b4a09942d01442640302d0705d0280c1e00000810405917044422101614003a00b001450303aa919000f910283c80f0b84d9600603c5d9000c2d42e02405855601500034250b4070100b100d034819441006901251701c21120070071204880d6184808104460003903004246100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 716844118 1250 716842868 716842879
    0x10506151315030203090c011403150a08010f06081608030406081503010c27080d03051f0305150f1005121006030804050a060504122d2a050102120702 66
    0x160740300440e106201e00b104180c800700c0e4001040102c82c034818030484c0f00721082400c161003100e502c000e0004003408010298406000d23146800a6190360310780c0d00b203000700801c1000b440341106074070030400500498855410548035800600010702010001039090351040c600841c24a0b2403da0100d0b0240c04c09003040f8049030042030100c000d61020301500d5151a49034990f04010b21685103042591880da51899845035541a410306c149000410080d2a60599142c0810541c41d03001d54020240d24078403101d0074044411700004100100858022a888040008003220307943d0400b00182004c4101d0381b1039174142509005007c1480c00b41e5040708200b00038412203600400303004942d001c40d00706400c00e507030b0600007140c02c2250749411440300d000b41c40d403850460b0a1038a8501c07840450910700000800003070152075410341a030083d0b5400e509404d41100c0c00c401240c001d003429038240908444407060741146101006c00b141c04c2d8940801103500c107030700810100707082c412510526049810101d0344031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 716845368 1250 716844118 716844157
    0x10207082125020f0616200a0e090709020c0307020904060f11120a06060918020f0412020a0801020a090603020f1201030503030a060503010605091317040f140301050615 74
    0x482d9200d1403022803840c6410120344104440c010091000c43c081c40a6200f05020061510055500c1c501c420304198041d0b030710541420320b050010b881050031900300e41c0040c14400006201501074080500409501c1c056500642d2903154400076449205410046588200010001800c0a0100c0380e48280155030002d14540402c80030310944800d03140310b0030300040204544c141681e00100301d07900081e204a017000014604940035204e41310302c3c070440103011007103c002c81d80200d81c0d4045408400411046507503a41d01c4101e401048078000c45c05078001e5801c414049154201442142d80401c0c06072030b0950020f140c100200c0c080d501c411421440e5420500440e00f17a002d1018085000c0c5101d00701541d244c0c90042c2c12441101c940c1d40c004c41c400c0c0e05011080200e500c41d02201500a04101542c041003042c0342003003030b0700d038051500340e0031480800500024806402d00360b1505840e1000c40c4010b000409104040c2038500554544e079000801007144d005e40d06c1140f000380712030240d014149504 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 716846618 1250 716845368 716845387
    0x218060307052701050d020a03021203070515041511031305031c06031a1003060c180303050309101a04021e0307120f09110402030a0608030403050a0c050102070821 72
    0x280e44644040803540c2070043e00028080034407000d01405132000b40c0e0010155101c0303070001f858411a03888083d02607140380707030300b40070340242441210a2950801e04039414030903004034110b10442c00700d0b4203441038404c2d14030585d06400b00e8004d10035802c190f600b100f810341d1680150181e64011009007150984800c02c51181c0605d0310400144d85000504400200d9070324508145000da00380403900e581c181c0701c2804110006240c11103000c15240c10103c002659414240f040d0b4010b404e4200a00c103105407044000100743d40700c8011032046881009036075503562514038400540d003c00c0d00c0810040e1101740c21700110f00b083e50180c5400c10508403140e443d00743c88101e524059005a070000300080e03101486501601580c028489024402d500800c943c01c204d8a441040c82110303030134184201d03000004a42c0341142c40d04103101514003401a01e945903a41c0c80d045984010383d52080b511650f8038400098198004541481251001c03c0a0020106900300700c10704448203000c05401c00d9400d004035100d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 716847868 1250 716846618 716846629
    0x7050909060609060307061409060714100c09051f05120c07060c090e06090402060417010207150e03070b10180b130507120509030c0114070e0d021806030705 69
    0x103106144050301d03060412a041c81400d03c0018451030107680f00c00c2c810000554803852081e56800700039503441c0c42d181401c0000b121403281207009040760b081102a050791900c04245007512160034601007040c000c03042025030303052802e403013540c0e030000031000103140e009829401007940c1c038464905a40307040c022441009071620152094480c8440202c0c5501c2084424841c9980e42c100f203080030540149019800c1c80b41e41001800d290041d9641008201103448040a81d401307043c08102040c10781102000c1a4000d402074501a1550510390160722850541849410380b44032110019602c2c00b603103501c46029040028180031408020101e0000700d080e040ca99040381c0d8040d4039000700b04041441d04016203074000d06040d040840c40d00b000e01803480d42010600880c9440c2140204895403002030300d60440c01360014103002d55003044207074102040300340b0020303104600039112403449080903001d00941c800800c3d4002c3d001842140c00100060802c0312140d80720000804440b05140c0744c001041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 716849118 1250 716847868 716847871
    0xf050f0d0c0608040b01050405041e050705091e0105060711010807020a02090709060320160f02100e10030515131d0601080106060c0822030b010b04050103060608090618070509 77
    0x80043c040600380000c02c84440f28443c010f085c100d030103100c241421b03225081d40403126024000410f049905000401c00700344448001020020403040c030300e1602d124504a0080d01640480c0d00c1100740c0c00104541c5005001e9070035240d00040b8910480c0b000c5401940d48840162565040d42300700741e20500143e41d044206841402a40d8036404401c0c90000d0190075100915120030010307001c8801100c5000c000d0b002c2e54200755501e05202070321301080c00c01035a901c0084034007a40040003200000c0307400e0b0700b1001101c0044802d40d0f202e585000c3c11242102203c1085c1c401080304100c00400040c1c91600e40c505c031480300c90540c40000d5543c00055980300992954082916503001a40100580302081c86060010b00460500e031443c150103685001540c411491036104400c100e0060b00e56082d500c403001c4d80034640c80152481d0550310f618a51170310340c002d8460580000d05010f4046142841842c0590150414000601c175684030b9004505902c0c0b100a01102d45202c0d180380025665111007072507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 716850368 1250 716849118 716849129
    0x1e020d060608070806010c03081f12170301080c01120209040203130c300c080304180f0c0c20030a261c020f1b0f10060f050f0d0c 57
    0x400c00d18011024251050040c40c48040c0701c48101080701e166000050802d20382c2d410302e0300044a54850040190465403030014820840300002c010800c004d0f0308042d800068040d81c0d070680105004441850584424054640507400c0041b85a4481d4054403100c20118a050b42c0941000210300100d0200d030011200300c40d02075111704101e41403100c0c07852002e01810202070000401201104100015240307288018600000b10f100130091040101510700078024440940755581e90b10700040080c0450415030611240c03402c051400c00c110301307202d6090410403e0321001492141074032425a580d40404c40b01d480203000e003946a9603660309004042c201d41c0301d4003401202080700f480c8642a0124090301c44240e05c0c08001003c2c0203c19203980e159070651040000d070341c840c88400303411198020040c00c00c20201c401c0e4504111441c000c00c48004802c9034030122130502e581925940c0c142c40f100e108500c09540d1501c028030060502031880390b0340500103001c0c44224400c940e11814111039aa00c030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 716851618 1250 716850368 716850371
    0xe01030335040b041a061005030903160b07030510060e01050c0c0406090e010e030307080f090c0607241509091b14030714030316210305010602010c02150a1e020d 71
    0xc0004100c3c5c06048036600156105c070500039880c2c02c00224a4151880809105201002c0000b130030580c001c00896110b582c0244074200040a60315040c420b0381e4080d80c05001003070800d00040ca070450b000f814042114040d64070841c045c4106001074400d0703803040c2d03600c00090041c011405206e403103d000d60001800c07566070009000356440d400c64211040ba00a0441980040041c4800300d030380490507503040881c503040080b80d501c411152614011920340295000f00c1c0110700e007402d00185043c950494061400403140e0f080003100c1035401c0b0348509010805010000c00700303101881c01076009803d864441c6004840c4000440c10040f12415564040b4012060794860180542000e04c00800101600b40107000c01800d40d8000036101c0c0200000c101c00320b90414054000d105607900180701d0750344220600e1140008444005000d40030074003a0078007540c00c080ca01034029200150745010107001941ca411203448825520b40504501d540040140c2c1d540c003140b1219401510060500b00007e050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 716852868 1250 716851618 716851621
    0xd0f0503071704090b03070503030304030e120d1d1008040b0a0b0d06151d0604090807080c0705010206090d0212090103150e0a14010e2a04120c0e01030335040b 70
    0x700a517001c400100e40640c0001c001006151000002d40b80c01642c1414800e4002c4a11000300303003500d0344100c101e0600c0c03085d14004101a500510303480c11101c10824014030042c04001030103161a415089007000485190004c0c020401016010340c116103540130201d0f050700c0c24000503481c104280c40980340c19946290582c400401e601449004004a102968142d06191000c0422080003000f0900481d00c5490440030070031032904540c0d4041c2c0c861040e0f62200714041c000750381c03082c0900a680c007510074407020402c5000c00003000198941140d00528042107070480b0032485400c0b0b0b5001505064175040550b020104140e481b0340540160004901e0500d8924400c409850482c0302541c601d48051005000e04021054010390000380c100761503024207041e2501c4003011441c2d4000b1802d000c6c01040218049210142032a000382c0651518482c072911380504000116003803000601103010344600c041101c01c5405a2404042c2c1100c0c07007c0c0b0b4014040107071440b96800c035400c61f02198601c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 716854118 1250 716852868 716852879
    0x19080a1a030607030f202a0a02130e03041509230f01141306140f030609040c080d0f12110f090f12030405011209020d0f0503071704 58
    0x8908003412484801110082508401094840304058489004c042c2ca40f080121094800d0b0801d04424800301042c0c2003010510341402c40581000840d4441c0220448940480100340e00d00c00003031500c0d100c068806540c0030390801000c00d20707210b00c003004d42c0d84454040b540110207102610080101000000d80840d5400000705101d040740c0083c604240700c000d0306009024609001480c810080e42c00c94600d40312000142e403041c41200b8100000b503400610060103035010b0020310200e1380725454140d6080c2c00c07925030108174000c400c0500c40e150310600c0014864a40a190140c0141c040c054032140e454441034041e0070f0001850100022403244681c02403c29801f0744083c12100010004000352440344070060094070451b096582d0040d0b01127070250f41680c2e040c009a492100082c00c0c4400c0319542c54030b0903140d4001d4800e090102d07607801c80a0010484034020044035590042226820740359940c4c8810103504402010f494601c420b1000a00007444140c200d0320f0400c40000da540c0351403504 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 716855368 1250 716854118 716854121
    0x50d06091403250c0b0711040e03040503010e0c0d060203060d080c0c010e091003081c1409010b01050c0a120e04020a180914060d030c02130207020405010b040518040819080a 76
    0x100104501c3e0030000c07044000702d40b0315120032084d103494884a5580d6040d070708007921544d81a140c0c0a034000e2800d120101080c1d0000014812604280c0082c401220818071141c0c450745040413542c0c1280050f48004006415540210303030152004050041201540d12066629044400e6140080c0c0c0401e52404480da002442c000440380c00b1101c0f914185002d1401a0690b440d0780300044c0034200110b00c0c034001c45141341072007520080603c420030071000601403401d4a2103050b91082d03159440d000565019500c00c4040741d5070001004010a0b400805989508100040c07100f41c0b01040390714440e14082d0307950713030008002200c5107940e07241c40054404c0220304d507414181d1160b40c80c1c91424154588580064924030740c0003500f154981200c100750308060307600980a00c0d00039440b4903245101c01c02c03601342e90702502d83c05000751010090741c0e898408401c0140304074090306a100c81040c038510f1410b003940c584194400d10440c101401e080003d0300a52511041c00c14120109414804000c1e4074880c6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 716856618 1250 716855368 716855407
    0x9021f0306031707021c061e0213050102010b06070b062409010807110d0c050a0b070810050114040b0304170c03040810050709050616050601091a010305010f050d06091403 75
    0x31060102d24218407940000c40b445c03804040307460b2000c039440c807050600c007c65011428a000611043c804914900b2412001354003840c1c900e555001c51500215155105200b0564401800340002d41b4280c0c0c039440342511904c0c0100440c0d4020b00c041c000c0b0b03232604500d4036001200c002c04007119466584c040005007112100a00c0c0c14104501c4039020040b501000441400d1110300e41004c1c21801d42500f800c5082145d4800d001d0404c1d500780090098096205042034440c9403441c0d9100d0ac815280c40046a01140d0802000300307401d42844140300c004600340065810508c2542007449a0684074004402c40e001041d200090b500049000c000412082c4152884071901c00c0f000c025518013284045c10600c0301c0d0142500a100110b07110300b07800e0715140710022261b0010101c0d0021342c0c1d03d000000c09040c502e0710b1070b4616280684009400c2d40203000d01410f170791180c00703c00c10f914101800d0222407924041c0544d4119101d02c140000b2400d1010700d00c5510710b907a00035568450240841142c203020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 716857868 1250 716856618 716856653
    0xc05030c0319080a0506131d031902060903030402060301140f0a1502010c0915050307021009111f09091e050c030601090b070f030c020409140d120c02060103020409021f030603 77
    0x101780402c5410340d240300d49109000b5000d1300010754070396001603c000070004401418245d1000151440c8003112980b0940c03403c0c00284d00b141c10f25614005166141d00084d54001e401900500040c4030191004140d8205284007a15001c00480d050300058a18192644203201050802500c1d42c5941e0b030a0083d46001c030041d00b80301c0010703481c10048aa20901d884000c8081190110114015a10910094460b022a0702d03082c4121041b5040410440013900c2d003182c81007080031940d0401903010307102007070b03101707441d85a01c036a4a26069540c030103400b5a040d0444940141540903004030298402c0a0040042211310307500c070303c3d00030005400c071580e0b600144070312141844010000342e0203c0624192aa0602d848886c0e5480381c07012070080c0c02c1104c0010240c1110300001200c0e00310001d82000307030200a5440c50150322504400c001152500c04007000103030402c20060001d428030b504203c60303441c8050400b000d041c44020805014a03120a5000002900c0340410030602c000c54006200d90389 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 716859118 1250 716857868 716857871
    0x1020418200a0f1b150c210b040618050105040c0c030203030604050c1b030d050108032b09080c06190b0f1908010507050304050c0303031012111302090315060901060c05030c0319080a 80
    0x201801c1d41f4071140e940a21070307020941c44044080d401e4850360003650040c054094100304078415016044007618090289078041d0f03160501c901d030b440d4822010115020b0f010303005140f03144c5a00c1e05006c084c040061601b0300e0043e04100316a080e042d19556103000880120156490310003010221b401e43d041a0b100045a900c2030091032a00102a4805189544060103804580d2420009040507102c1c00d00080d20703540340490000c0c1401004608284111507805564007000d00c070b40a45000c881614002c26040b80c03a4040781326407828a212000c103051900303844803003c590703101400307425200100e4801001900110a00c410001c3c10480365890030001c40140d03045250aa148000104980c403a042031005007001c00b8003072000a0203030f1810002d001d0241203145001c0c0e80d510020b1346c40324940d07500a1055400d00780c401100d4100c2a4091700300203100303130102e91031f081c0112508407110305c06886500040010100b4442d08100420310203d030138404080f207680c9818081c101d10b40080ca440c8956 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 716860368 1250 716859118 716859137
    0x21c020301181a10050a060801060e0108010803090607020609041d06160e01080c0d0903020303011e0b0f0c0f0a0b0613020a081603060801020418200a0f1b150c 70
    0x182c0001a82d203c80949002090690b642c2d42040b143d03205507035002d1508421505000304284d80d02000882c1a1802d981b505200305c03007801c0046803421000d108401d0b0582042c0319019103450700e0b100410740507000401090801c102030000030221518503140c1e010905161040302140041070003900e40c000443c00e03001145103010b410140110030b40c04251410441072000203080503085a0541d401020140e00c20800c80c00d03640b40180d902d500a0007942c11a249403d242c030703000e001065070350b0300740c4216180302da04140301e0080a903855000501c02c0190790103607640741d40c84180200001102c5500070b121a1801b41400c400784461070f0709148580096500410010342129000b000c0700e40c00c01009000c41450741c018450440007410107810180d2554000a80050110b002c8001800400340c0140b0805c10b001440650300760f218602252000742440038488050b0550007070366502c0c50348466090002c6a40207144400e4002c00302071000722110150300c6290200580580300d541d8800100e0305081c1000f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 716861618 1250 716860368 716860373
    0x12100306060e0c0d271109090d0203160609050a03031e14040b070908010c05031503010209010c1b0e07030f1b0c020909010b040c0c060f0209060405120a021c02030118 73
    0x2501c160341380b110441c1d464128600403004184140c1d0300e182911809040600a58584540040743d0f0540c42d80c4103900342e00110f41d02e000040b4400c44800c3c00c035002945403030b40401d85045d80d02080396054648a50707565a0f80c011507418070400150078402e9a0020724101502c100001c044641c210001d0641d01c3c0113600041d821b080c43d07036180c0164100a20800075030380e07480212088113286d00040c0007542840050030303105400c030f4044d5004007107101e10614030f4404c03034052500700d00a101e01d8034000346800c0118004a03501e0b078921420301800d23130042101d140d2990300008680358140e03106030000c0c1d0b41c1d0711421140c0a19100c4c08026020f000d1152064501d0a00000c1c140740d800384010b13119030001d81c08141000000d51041ea03400002400a0180010b10340010741001070801060711820704140040f82420749501c21075042c201c0c000c01d01801d1509020a11000c09640302e00701c0414420041c0180160303880b220f61001400e41041d50f503440701a24414182134488000201828140c0d0305c480200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 716862868 1250 716861618 716861641
    0x30c120f09010e120304062015060d0c09090b18060601021c030e19031709030f0c0a0b01090203060a0e0f150a2c0f090d1412100306060e 60
    0x70040901c0c200c43d84043c2100080d40780c00510706003000038480043c00007503560308030704c500e0070f4400c01d400c0d000003004040a50540341d800a80d1000070144016001603142d29203600e290310300c64090a4038000c03950300c0f2070f4108110348a0a4050f60741d50300d001c00b04992102581d418a5081d202d44000d084a0304012002039503500204824821303600d650404181002e03c280d02440c01600c0d07200456501c40200c550300701418030303060b00540005d60400e4030b20b52041d094081c030500a5080c1c400a40ca06900c0c1080440703c2c2e040803107901d07003600803e03c1c01404503c0c0180300e18045d0031000380050ba641032039410800c0070000c9a0100c044104410b00b0400f610740e038480c841c1d602c0b00f62940441e840507181800036000548940101c6000e120001c010f0104960f503030000b41da60342040952103065291410030034051041280d94002e03940c48200c40401e024840c454100040740d003d00c9141c1000c0305940345d461950720031214107001c040c40c42d000300103100045c0120f000800d40507184540c142400d0b4050070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 716864118 1250 716862868 716862877
    0x105030a020d17071707060b0d0c05011808010c020105161404030813151d0406030803072106031b0e07080f0c09211c051215060c030c120f 61
    0xc182410b107443c9100c1c00d0040b00100c0b6041c4d9800b00010701d1414511085801030340204a060300c00910700381c0803d09905142e409201000e40003440c0c440500c4c40c1c0001150000b205170060041c54280d4000000e010300d0074005c402589000e03400100c0c803445c06202d45a00350010351061810040c17903805006e0400c44e8002214140d035004403503a9556000009503102c440307410380c456000055618141300f10340398050524051810600307044884589407030100001d0322524017016100d91001c102007220280200e191704804581c0e11a44c4510003000607100e41280d20759842a10741d0344035403403245517088810302c25002605d44a0040666410700210041c1400740092400000118401c04141b030400380c1c8068514021004090044589810040720801001c07039031051030510a001d084c8584603080000c082d200e1005035640c502b010001034210004140151210102022051440c040703030f01c5d404018070b8510704080c000c641e901c0c0260080c5203002504c04083c0ca4211050001c001403521060849 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 716865368 1250 716864118 716864123
    0xc0c01090605011d071d151209030d0e0106150e04090b070c1415010b0708070c0303120c0806060a2d270807060302030403021f051005010c02031e0f010c030f050105030a020d 76
    0x80c047c0485000810915106611003500c001a00804110206200000030315840b076048009001049141e1b46c0d55080c2c0d0400d000350809400003035aa1074480b403080c2d008052051005101041c03040542e2201025440309851070000101c05101c202c043c42218594041d4004500c801010015503580b80b00080d28818002d1301d404050014250040c01024420b503030701644c10100d00b5030750b950740b0320b0702400c480003581c10300c1d132500e04058164903128009c0300414880c00d03010304403500e0074516210880e0001610304601200c040407060500d81e174445085842400301450300c401407100c1c10601e52820080320a0f20444c1010b14010041c0440c40c0042030104c100c5846040160b240d48540c5010390a18000c0c5c42c09040d2800c6075406400d044031075804c40d030700440c100024500d6458440c001101c1c1401403240181d0134ad4483c1010541c20302484c405041c05540c040240e408842c0380d44030150a45414111800000c1d858000c18078180c1054841c290052008500a1501c0101c950102e10a100c01c500701 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 716866618 1250 716865368 716865379
    0x6060309030714010c0f0203030f06090a0e070905041a091914030a02011a0402040506030c0a02191506120b070332160c0203060c0c01090605011d071d 66
    0x403402000381001603035041680050395032144201030249500825446010800180d4100054000e450000c0110382c06100b24000e40c0810f5542c20040c0008a900a00740c40790640c1c0c2d44220b640072130f00c1408250044c100005d40800d040c03c082c100384ac0500c0000407480c0101c90b5000c24401000800180c003085440700d400e41005188242c1085908114461344000d160b0000044203030744150b06510460b80e141010184981070800c46042c4012401940103150300004100003140400d0b03410750180043c465548129101901c001c1102c035804142e10504903060080d05081c0c4d0b4181c411809014081d01c2800305020100c1d501d0b4035401ca06940103012503052640d41c3c0981a0b03441e500e20340345002e010b804469181d14030300c86440003406e85011509900c00010741c0200c003030f8540c0309280340f40326250010b0040100751030b44241e94803203034000528402159a44c8100800040d100c0c060b8a00130441c00c0881100d0882c00e1840341c1d05100010182d40c100503106d40d0745a592046204014641c0109850 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 716867868 1250 716866618 716866621
    0x1706011d0601020319170a060609090b0409290903030408090418021507051510210606141002340b0c010506130902030a062307020606040b0a0806060603 67
    0x50b4114415001308642500904444018483c1c01c0b100a1442409051b421040307980d60030602000c550860150100142c0101000c009502d842d8006072140031005000180c1c0208507034030b28005c803401030840f130000d00d2800780ca84458131a010380c059004003070f00091469898980e5540400380710301e450543c07180f69200542c03007118034104a45038015a0140c081038000440c0c50f020701c0ca0340c0100340c2c102c406102d40e0005560356485250300f107014400e8040c102e400c1c14140344a1107050000042040004148044e08101003402402045c0042004000754032210480f0802c0c030102403807c85480055522001c2940800860142c0f4911045c0c000d20039440396070a486502d03805070346070398000704445a012401003504141980b200b402800c007150071100c142011f4142c41c0540c2d007500d4000e94907400c040940c801080558000f80050b0f808804081d000882c1c824143c80098001d544503c0141e002104105840c2820320902142200407030b007030301c2080d02d88843c1940d00c5100400d002e004850200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 716869118 1250 716867868 716867881
    0x100f0308040306603303021305010216051e120312070801060203040303230d0504050c061602060c0c101d0909030a08060a0f0801061706011d 62
    0x3a000c482c0c503100210481d15484401c1c901004d4800c1002c641c41c08480811039001026031803140f64483c409041000f03103079480c80c002054000074030500a540a01480b22480403c001340348000501a281646005803202001082841031810a0f00954150341c44042c00c4415048104a40c0c000c40310100d030345440c0301940090a181c6001144240385d004960340c403061b4040c1c3c00100180480482c0d466900300c6a40d21000c01b00d0309444284150300250f0404c11050022074480d032500110b0603000071208403405c2034100203041c0b680c4030f00002c502613640e80040c0300030000280000c0c1010350013214818100440d00840e14060348500d072009201d0702d03000400c540010002e200707441c0f078160001c1c403240c000600d10b1000b40c04000c24074108640d8030aa00d540d61080d00d0302d08d07a00c40c0a155010015428289003039000e031007141c1c0140c00541d00480380b107800140145c071044a40f0260032a031001041c032a02c1d0521009030701c0890848142c40c0d40282005215a44014074a606a590b00e150b410a5035242d04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 716870368 1250 716869118 716869151
    0x3002010912030905040f140c031005060c06100b03060f0f1c1a0a051905060a03080a030b120a020108060d080904020304080c16060e0d0303060f0e100f0308040306 71
    0x1507009032400300700c200c180d4080c940c124044808460040d1010b118100700720302030f041110000600401803254041c040707200702ca1a07101a550000103035280c498030a4982c000a101c0b41c200c000e8040c0b280c0c7c0310004120725081c400c117038013004004d06680b00f402c1d81000e074002014224150a8a0301610301888600940ea940c15051540350021600c1242003001504240c100919080c1c10541e50001d01c1c00428201c7c100e51003030600ca81d40300001c4404001101c24240040c0030007030200ca07400014500040b010a504c10001d01800415807400910320f0b0b183c100b800030107074100300040101c2d000f1191450151b40c210b010035520507402c03079620540d00c84915140e00c690042d810a00d8205102004100401202c04010b1180310184411a500c80c0e048500e080285c03c2c03280038041c0094982600f04155080081c003841481c1d200341008100d05444400c09840d8903170390b0f84000f4030b80c0040d0041c404182914a850780c060003645e400040902c2c110744843d0101d00c25480018241c44d5506060809103407031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 716871618 1250 716870368 716870387
    0x30c090c0302120108070305060907050a05061602150c0c090c0d0507021f020403020103291c0b1302010e060f040e040f0b10060e040b09010b03090703050f06010e01300201 75
    0x5866107680340d5171148440c86d501d500900085455104240128580020000d03002045850050600f44150b09000c103110b45030300600e891580b2851514203a80059440d0301d18400016214200c050300d4907100b40c3d0a41c681b00d0700540d80d5000d05821814404a5402e010449400e114500030108960701c2e000c104a01d8695010b02c000030034040800526604140340e001001268003d0340c042c0618110026145548514604010f0005c500b00d503211601707080c0b003100540c020443c080b10302001401c90701e540c0b80d0086c0480d011043c546c03007503043c10110340e04600b440c1d224040a4503000e0614032541c80c0351560b84140c2c011080c2a4114500150070006424a01c4060541c0b002d07201446040510f60501402854000c0502169603105245c40754103051040c8016100002c3c81550302c0d91030442000b40c15030000e090b00e4101e020703008000c00032950401c41c3d80340d082e541308010092036140c07488080c160313001a00f00000b082410032503d0b1403000240840c040c1d00717008092104040f8190300c0142d818800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 716872868 1250 716871618 716871637
    0x6150b070501061e0506070f030201200d050108030313030c1e0501020a030b011103070807061401081507091203081e13050709020703082701090807050c010801030c090c0302 76
    0x800040250802006420101c2241c001003010b81c4004090604480810083d028081d00800705001e60400314070300c08410300c46070b0b02a000014004500002000c10800040050700d1310042c00606401c00c1c0030b2602c509801014000d020f50b0031410240507500554442d88006001c101015001c03074240100d0180d040e07800516480140c0c0880308528002d8042d412030500c4001091414840700c0d8154020b1410b09120300250700a14603125550344d415500f60803040d03007926110740d0760174004130301030744e25003200c0c0a01540b0004021000c6a4044d1440c1c03440001c11a800f00440c05200300984050341e0322040c042545070034240b000341e030386c034071200f85c03806400d941c0090418041042c40780c00002c0d20034000c1c03d03d000b13000781ea20084d00d81c04008168410607c0c0140007840d01c0000441d06108000d846000d021075090b08691000904c64507407c0d925020070a8a071080000b900c003040010410405404c07035002e00f0003480640c5143c8580d202d0510b94894000d503a03071111500f102240c030030b60481300401c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 716874118 1250 716872868 716872889
    0x60303131a190c030e090402130f02250b0a022106120a030809100e07060f0c050f030901091502060a110403021807030e060f0a0207060b061204020a06030b0d0615 71
    0x10001c500800031883e880b420b0740824012282d06906080020a45200d07a4000e4181e2030210300d2030714484003e0600300c10b0301908070390034807032900181d00c440c1d489070495661f0410051020384900f001c00440c200500000c103054410003642c03106852501f0205150020300c012090315686500100740d0960314085d400e0003a0080320f414000300764200c0301490003454100d0807140032401e10301c1c3c1e03541114401c10300c081607a44801c008110380d03071040e42c05542306146403811104440341c030360720340c0e00e848041114120981c1020403209c1c281d503440307525500100919902c00713200c900303020406916024040e2010075596282e1a5404000b18100c045800950340a4900c40386c02081a05041843c14180e072030f07000003424446542605500041e840e40130b40c81039083c44c84035171201442000203520400381200c406490f030002312000d80c1d0342000380c03000240200d01203030b46103850310401940c4900350300000d0078103241031200c4490361503107005807098642c030550000b02802001e189e500c14105603404092802d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 716875368 1250 716874118 716874157
    0x406060b03040b0403111f091719031118092706012408070503040215041205011b020312060d020301060312020613023d03090209060303131a 62
    0x80c3c07042c105120310300941e5012281c62448122540310104856007101800e04107840442204c80c80c0d205603111441341d003814010540c1c0340141c1d40950046518982c200300b071900001a20f03505070040308036034550540035520f032092480c58000e180c64800350803402001d0100c00103803010425050f6600ca4000c00c000380d41d000e01a01c403943d41d10b0600340920f0b0b00000884119034000340d4259228a10030707072030752656181c0d541c520354110307241d0300010030603a4000d000c2074405000504101c001c001501d1200040c001e9421103003491400d640310260910782c0402044013082d1040d90110644100d1221843c003413086844940000d0b02c0c0b00c55200e0040e606501e0901e000013085540341600e169444035800b624155034402c82480020058054040c0d0040e00c007141d0b26640f0744074849110703902145421303042d038100c07600c49103e82461040245c80c00030a60380c1c1a44020b6141c040d031032607030060045000714500840303060050310010003441251058400e802d243c0e4401e111440a8034130126a14000e81c000307 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 716876618 1250 716875368 716875373
    0xe190507020c033f1b030918040209060a14040911030102040b03040b0a05011d0a02070f0b0106021029180a0605150a0c030f09030203030c070306050609090a02090406060b0304 77
    0x1030100d0510300141c48541c03070598040507000c1071814400b440f503034400c44d8240360805420103203c038002d401402c6103010070000e440c096560b03407001c041c1c843c8024450042c2e5141074414416101409401036110317070f02e80a01088405d45121509032001e6003920003040807e802d140c40080945442a419450b50020401050741c2c008900030394070a600901d111200c545441e40b42e507084035400c0c024509500041040f003800010b5079280660841d41c400c2c401450028192200d001c4445c1c948011a074012410004001d101d03070401444844400b0b0050400041d03000c03071001400b408002641c0c0c05004010301040300540d84004510500401c0b0940d00101890000301c010010400c50068134032036803a06001c2c1c00d417005600c003500c41d52803035070326004900503003074074240d4482c140c0c022440200725030342c5000300c0107032003c0c2f000c0c180750201d070002030189906519004059860062030b6602500c04034040000c2110000340424640d03406403448546a121810194060081034200211001002080c40304 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 716877868 1250 716876618 716876653
    0x90a0e030d06170c010f0504051c0b040c030201020d030e0a12090b030a05061c0201120e07081f05070309030c03080901061715010801060501090e1504090305130e190507020c03 77
    0x410051a0303082c4c1d10006804001954207480c065860340000e60240014441e506200381680101640a107002081c030030540c0d501c40c80c4100443d1304841d0340701cdc114410000c42d6010001104500a281010b00c40d210b0b6000c00c0d00c0c1d8a910100001d00105010480e1110242c05440854040c01c8036101b072554900c2c00c0001000036100c01ea60107401126186400e040e4201e071603514001569059546000e1010002240000703030215210044040c014000b000a10003010801c0703002c0340b80040e43c0300341020a6000000e046942c004c04000601d42030802090000c0e071b00c104481421945414100743c1c54480d124191300400642e00302c29410440c0f070f101101c10045c00a4040b20f40082c0d0021004185e80314000d4509803011072041c1030103d2240c0d1403d100500800040310380c0010041c01100e400c48003000010181c454421096011840000312100e01450f041403c0000d010860b8060070325081901c1030314025111001c0c0084003c0c0d48102103250706100b03101c2c216080000804517084901c1160f02e004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 716879118 1250 716877868 716877899
    0x20409050f160509070906030c0909150f090501030305040303080703140c07230c040c02030c03070311060907030b0708040203160e0901060609030510150314060103140309090a0e030d06 81
    0x40110b074074400024035140000216104400f640e84281001d4a03112041c0c018040c401c06941c18414601c07c0401d0412042c4140c40741c0002000c2d400840c54036060031080711081580050518504020043c07010a400604507800c0720f62528040ca9140e84149040b001000300d40b007100341d000c080f0800d0004ca400858080c00280b80948003d012088a0412002050850285011003604600c1d640d50082c50319a00c20342c086282401a6868045401052829548111000c4000c034540043d0b10a100320100b103116800348103e0020181581141c6415500c41b100400c440b0030085523a00140842d1024052007004040703003a03a20f0840354030b800410801c1c030000c4512403520740c43c0010004006216800003801c49030020041d100106028403280e000e09080c1041c1d5200c41041c040000000d014046a4424402c3c404090190342d411480c010110764502841342c1042d60051010760000d41d1071904442d0401c1e0705100c00030b90510300c1c030b04150850141d0118407180c81c1c988500044e0003003901d410b00c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 716880368 1250 716879118 716879143
    0x27040609170705070509090a1b08012003040b1506070f0b07020703080403080703050903060a15060c020f130b041a091305060106110304050a03080a0e06160807020409050f 75
    0x78000300c201000403509801a0b007005081e55100400800482c2400008107400ca08450166076503000151036058030381c0b13401400800b1280c543d44003041418028401c845400d44802d0040340b1100700b10544614a00002d000504510481000b00d2980d24048030071040052018000070b40f40d2485081406604503034030b0041d5001c28420000840d0944041a0340080da41d100c2003190030a811516142c2554110341d1080741400b0040200100580d810043d151003a102d4a0001c1345111207400c406c80321301c0e00303030740b2140c207000c01c60201c0801640c2d2103290300000602a070300c3c0d2081014801c000000b404041101c1508185403510440200c00303141d03040e64001c1c00981c4d5103040754071a500164480e40740b8050140a90b0030280c0144141881000351082100c1400210b80c1880e455100040b6015001d42c0120b6a1000c0040c40042d41a00b091460303141802c1203a80b1402c1041c00c0201084a910104000b442d108002921600315980c590182103031607001021a44030b1f454003070560f651a003444500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 716881618 1250 716880368 716880383
    0xa0e130c0c0204140105061b01090c03052a0109090b0406030c121e0206030609041106131401030902010f0c060f110913020310030b07120c180501140927040609 70
    0x13a4042e111440d194074101c0d180500020328102501010014130500c036a040405552500504c101260421102501950081015001070001380303680b0440d0306c1100f103401d2410550040204020703a08202d46008a0741055400700313032000701d800000d00800795504002c022021145021809483c0d0034072081519100c0d26400071080b2810600003031054107210020f41c00038081000a4246c10480c001e203402610030b09407104080c0800001400d1500300505003018803840d0740702008018059811751100c2403080c20b0402080b00036400003008943d42070315820a0180b030042d11001c1160b9503000350000718450104201415407a5079a110301d520694100c1c0c410070400780604505007030352080380c0c005d20661241e00b40c084c1c6103039105003013048000d000c48140000b280706590b1404031400380888509407969181400c26441c00d00400c2c100141c0c102504000c0c50a480d9045004000101c0c0c0180e1801c032088410704a17462500c6640020300b909030044074810100340000c0140f035411041c0f442c0d00c190107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 716882868 1250 716881618 716881631
    0x61807052110091104211e0c092f04050306070219060c0e030a0309050109120302070b090d050d02030c0c040203060f010f0e0415050a17030a0e130c0c0204 68
    0xa10141d04a0259280203079869884000c0180c03400070780c80701c0c1c40920301c42c0d001810b2a40e1055240a09000f64180700503424483e100360080211001009100301d400301026040007207030381c6a00704c0110650144080c101e56880c80404484407401c0c03410303603286007007d01e0b03003690003040c03001081070b04a4400d8900a11441c0c003c02d00b290300114008804a080708070030050209141c4404003d80800740e00344c003d0159480e65a0b6542d10140108000c00f8000d85903040386a02c0c1400040c4a500240d004039a49141c41140c0320019502140c120100e904c0c14a6054032400880d0000e03010030210003004255101e5121200942c42d00407002d4104c6841c6101030320225540802880243e1008480c40b03030f0b00c0610040010f14540c01410300742d180800506d06968402c600e2000314086401c000004102c0020004082056141005d01c1e20080d0502d419074402100b04403884075582d001e040180340078001480618200c0f82c81e078200c01d00c40000300c440c082c81100c203218000350002c805628183d018509008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 716884118 1250 716882868 716882917
    0x20f0a0614100e041101090939050d0b0a0302040c0e120106061407140303090708010522081806041d06030d05070201260708011e060801060e0409140102041d0f04020906180705 77
    0x1360320048201d4180c5600e454a540d00d50f44000600c00030723301a5000303d04413004005610f49110b418965071a5841d071000c84071000041112140c071080c81049a40e06001c401e100315070b80103601008480140d40440d4a901180c0382c0840c00282034001a51144004000c00c444014000740c0e080c1101d00350b000820080c0c9401030342c40c0010582100403245006448070b140e0006250000805040c003085141e008100450000035400340d1007503110006840040c400e95030401400305031150031110460091900d014041c0000d4518003071a18040d0501c903401100201c1d001c0480745107a1f0304500c199985100d441c00e42e5001d85000b800f80910703c141c0000d11340345007405000ca060441030f60040d8903142056880e000048460707400000c55540c1103070302c4010400000d5200c1c00300340c0c07a11000c034001507204c41c203180c0c03115060038950b16055907028001060200fa0540c90720b050782c01640580d84001c0564811021600030861880d94804099100d000c0003182c69110001c2c00341c14202402400030700c0f82d1403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 716885368 1250 716884118 716884211
    0xf0c1905010c080a090305121e15031009020f0d08041701050103120e03070b030c040f03050d080726040f02092503020f03010e07020f0a0614100e0411010909 69
    0x5c0c10010040703001006900d481e10215101c0540c01140030030b01811129206480d0203107081c083d01e5400401c450501549900d190610011034a9101030b00200704114282d000500c04100d03d140c900d01500050341c50205004901d41120060304100c10305660390382c0300d810881e008003401d1000380c507041c0c8605e02c0820030310310900c2c0002c001000240213040c83c508008135003186500241156182d42d41c00c000c0062600c8001801d60002c5024102401841041001c05000950024900030030841c040201180988582d140c02c107408510100440c060340e103038980110394001300c01000c1d41c8581191304000403147c0c0d090300d40c00c0700342d41d0a0041c0c18050107410190160300a0020b490b9000e44240010720491800c2c00d569036000f480340c4100da070340064036182142000700c0c0394000e640721a140c0740418204900c0c1c9070040e0b041881c0c038032034985881c0f0300110290034500c040c0c0700034800e40441d45a46003982c41103c0003005006604410401061303005100c40807819941c2c03079404004aa500c0350080820390 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 716886618 1250 716885368 716885381
    0x1813050105010e060609091005120f0d03150314070e011202040c050906070b041e0c0812040605070204020702011206060926060403080703111207030e120f0c1905010c080a 75
    0x5c0d000302c1c2081205030400000680080c10a080341c1d10341e840024a540d40c15400701c0c1c412107498086d1000f440941d01e46403c0c03444a08040080c9401e241c100400d0094402d5003a003181d0b0462400c244410158170007034207084181d03120500e5500c522001107159070611a114201074421501000800b00f80703e015a041d01800c0313030003903000805000140c085440b901f1000c0d4400c1c4035500904c5500418048040d2050200c1c100b9943c1c10008201481500d400300702850b89100103042050520703140410090079480380105c02400b075500440c920085902814815101500391481031080c01d4940310000c00744405845400500404101c1019240c9440e02891240c41e0192025050300d40e20364809035080c0c080038042508069480704c122004c0c010320400f0700b00e900c00703021040c55181007c0c0d00c0241a44d4140124129541000f02d4000201c81c011003140e0101842d030380f0791500c5801c00b440311400c241400c2c1040189445103545081004010351280c0070440c10f40c1c980071859112414610201c0740c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 716887868 1250 716886618 716886631
    0xb10090b0313060902030303090c100503063001060303031a150a050703050d09051608150a05180708070303140301060813060e0d09033c021813050105010e 68
    0x1080856400c00d01900600c2d000e502a11000c540d10b00c81e540440c0c5140c0c41269004901c1d001001100705910340151668141c00d0303103103403044c210b0906200148080c064060348803a01c414400e1059a80700d910385100030304185071002080525606c1c107000c1c028002c070329451140100c0e00b45a107129441d02040701c52306a214508031a041c020304800c10f84240d07001c100e042d01445030a012040512400e4021001010b01c510081d0010403c00c0c030020708410a40d8010a1700c1e038104d00c51042c1c181a0221402f039000c0b07440d01000ca400c1d102c144000c00950061500e41859005031840400c8a000004001c0e049a11035540d0085610000f54500c01a000c02e00a8000140e400c0022035003401071002640c1c0040d0283d403000920254508405140c0340740300c4101404203905241c200284407410442007c41002c54007070003812041404e0b5000b8034610300c42d00d01c118000152803001035485501d03c0b400c05508071403812915040c079107200424410704803411a1591b003080700225042100d0201c0314001e11 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 716889118 1250 716887868 716887889
    0xc0f03031211090a080307020312030405100b0f040c0e09090c0108070c060b10020a021915140408060108070f061803020123040b0c0c09010302090412090909060b1009 73
    0x1986400410141100001c058142c1c04203008550841da14038007000018140d00c0c00650780c40c911441414184060204c1f40b0380d954100303104000100c0c0d4042070502e403141408200240501015000030481d185020070315030440e00c0c0c01800342c50b503500000b403481c0c146421200902e050b075410445582d20403001180c28001404d1101084166000e031a0407080071b44a140042100c04400c3c000c0f070041c01154140c07400590041e070019041d030400c114000038082a80c4010080a82003484061130030400c590120200914400314400c0c00c2100c805440c050144c2505859045d6941c0c0301807542c9200c58050307055803007800c440005100307000c1e500b4040304090164405030518999001500e1040d010440c525030305c450b07003000b5100320280100903c081c00315440c0c00c54488004a28541c51b10100c1c0c071150b40140c11070801400940c1d01e00c4005644103078080c0d5880d91040d00004121100c075035550141202508015000c820805941c0091520900980300c84210300440b42c01211034002e40d22804030703110b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 716890368 1250 716889118 716889137
    0x150e07090c030c200a1e021807030b0a050603010b0c0c04020a0e01090b0406120908360312120618070e120309011e020f0a0602070b250305070e1305040c0f0303 70
    0x2881240c9105540c6d081d0402c83e0014031001d030081102001142d080505003034003002040902600f6210315810307c2030a03142800c50368100000b00d81d0b03911060152200403500071440444598040104441e10396002d0020f40d120080b121000d030a065140c04c02a020a0000d1004520300b4540c0b020740c0d0881703006984001016002c0202c10300148020242520701035010001e4444259003102c00c80e00b40c02004480500200c132800c0303a0040b0b080600308061080c1c02421040c1501da9020003a13030007044c054402c500c0c1ca40c898400040711000303840300220081041d0820000718a070440c040c21014482603500c584048900c1058030749034420018000e010030700490300705a100b080c00078203034003c400500459a0303555560300e001d89400c40c0e8000c115a004d40020301901008801c92000790001400c0402c01c004078400e400c0c42c0824003003100c446041540e00c0707000440c403e200300e40c5100440c2c80504820203200190034400082c003000c80f0203070b9208240d103900080322685060030741d00f01c9070140d072201c684 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 716891618 1250 716890368 716890373
    0x21150904050a2612060102120a02070b090a03050607030c2613031404090608070501020f03120a06050402030c0a0f082a13181503150e07090c030c200a 66
    0x81d80f4251260344400b075500141a040006008054400e090501040c80d482d060000a00c0c00d04810800040080107201c1548403e40024460f802e80d0342d00c03503d240e10390905c1d0b00407442d0134020354130140880c8208030512492540561107280340d0300003544c45c802d2200c4041d5040074991204803200d9451341c8042c0026248004aa041c452210322901d0010070f1003032803015002294120360481d0f02610380c3d9034030411403250708003c2c0340c0c010042800a4048c07030745c504844c9501c9001e0740d40681c08644981c00011100c0a90b035110b2009010000d00440d01d0b801c101e03d10741202d802544440c4007154504904a03d01802242018402c21107180a80f038030b8814269401c81c01f290010071040c010506101450100c6403059001c4050009420301410341040501c01e103051b10306443c421a80c0640d144000c0c804039880104142da01520f40002040000d004030082e4a0a401c80d840480c40e0351610785600d5101d641a088a100313201582d44411445989109070800881108448405603103d01a681300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 716892868 1250 716891618 716891633
    0x4030c0b120c07060f0204151701030b0714090303120f0f1012030c0c063513020315010b0903100e060402100c0c030506040b0a09170f21150904050a 65
    0x74024490400410000c940300d10781760903a0020740060040007103140d142102c485e403110021500b07141c8014001c409514585400c0c42c110b40240410702040511442440081540300444000200c0a001c0f01da8032240110545021801a86e44e02d0b44d81100a010500c400d640c44029800390340444039882c0303040d00d040c22104a1107154070003102071040954583d00400c000392810030040500751070f0140070741d545290352400291410381c002000300d4040120340358080b504c1805a1302546440014041c0010ba0000902e40308940300341684614000d400072454034000030140c52254015805c480c000c1400c0c40b4002e00f41e07101d404510b04194002c20019002d031400c04900500310441e0304000c2034561140c3c540d0461401130b90020b880c40d50041c0148401c2120304c0d8041e83c0e126401c3c0740208140d5074103903100d203500da001c20288060400f02013034408000d0b42e40c01c221035070440400d090120042860324012424142101c80c45105101a51416003a0400b14030580c42140e104018044004050b55502c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 716894118 1250 716892868 716892877
    0x20601060518030102040e07020c060a1d121009110103270f020a080d09060801060c030311090d0c03050106080a240b09040311010501080d050714010209100504030c0b120c 75
    0x854040703042c8400030340ca450038402000681000d840e06007280c41c0081001e80740040900e5000e01428040105000c00341c0d102110b00200300c0c0101c04524003010710f00c0024044007440303941c0038031401510484003e080c4580c0c09100344600c2001a91141454000154200c0d21000d21007003600c16140755622550f000c40d08d4000c90306114030b10410712400150040b41441d8815008440d2662000b800442010782020360900140b516142c140403c1d81130070b000605030902003000400307040d203c259124440c061380c800d0300c49044000d0309248112100e420260340b004203074402034030030b5460a0804114504041002c680c4c4541110820510b134080805000e003016400c0b064441301550f0b0480d403450381d42c4544400340100e00a954600d410184440b942c0d00311101a48012041e51014208040da590000c058528558005801c0032007000800c40d00350280c480c4005ca180e01480100012610a0b0000c000c1e00650703003e40703d28082145c072200d02d0400d910500d5185440e00c010040080d10a004101c02030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 716895368 1250 716894118 716894137
    0x91b190b04030c03170a0f030b03010b0306091e060f06060a0e03101424131803020607020d050304020a05060a020a1a01090b040207121b0f08130501030c0206010605 72
    0x20102255600640030301600700ea003080740d0200d1a40d004005000c9542d800100c6012800340301440c20040380c001800703000c1c25101c48410b164642d0b034141105c2e613080d4025210b588001c4c0c20750301070785001300096031200c2d16110b52180545c0008800365410750001a000d20401811907542d4542e03c422040042030b1700080e01540c100061040c4c1d000c0551024810f51030b2200c0c0d803850220340f0f20005201220551002000111540e00c2403c43c0310380095062007180c6da0b52010b580c0000074001c240c4070f25010708009180d03080d4a82001941608240d4009280740c8283c071181d00361964010b01040484d254841910041e51002d40300c0070504c07803440d2480c014013044045004803109104039544600365000412400c2010114030701c010403640380180078100c0307100001c4804524108141c0c3c2d03040c1840b10f0054035003041249811b0031024400040d40c41c005034640142d403961010001c1c2c90010306a5000520140c100945c081c00041c03154020f00a00d008010301e60003401050b0309207d002c580d203401c0000079 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 716896618 1250 716895368 716895409
    0xe071703130e0403030c1e080c070209040b15090114010305370b0301230622020702010f050a0203070b06130906020c1608031207030213080a0b091b 65
    0xd481201c0041c0c8440020962441004100e10701402c0c0901100d0b02c4450302818060400310412404200d00400700c200b00036030a1003031302e0383c031a82d00744400e60041d010002d4102c400e00040c4000c0c0031070208a148220456110f08940a1051003407010200c403e02c6150340c00f038204880f0039950f42c000d030400b981c0010102c1c00c081c403010703880882070041c1e01b8111000d0041e0703c2a1443e100142418043c035035900300c09600030f02441e40c8407406e030310320900328400ca45540c0c0301d00d4010030010343d600325400c1008402c103556031003503800389140070b4029800000224045000b03204110280d901840603180c00700d1640c2c01460038030980d615807801000000f000b855000c66400441803403610544504034085001c2c1c500140c694051b21400e9240c04021258054a203040000400c1038081c0041110185074226500c25065100d9681c1039002c0d00456401200c507a02c0c420005c24030804c00070394412028090031969810f0340302c861941e0380310803c4041601100403080c10007040340c00c201f140b405410061092 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 716897868 1250 716896618 716896627
    0x30f03120b090408030a1b0203040b0711150316031b080603010e1009050c030f0d050c0a0606030f060c171501020c0a060f0f021507080406090209010b0405130e071703 73
    0x20300d5000c0b0843d411110b464021040c4068018940300342a56a0344030190711100c198282d4002e9030320700a40c4201d8120840000c0e0042c10002e0a1511500c016400707044050b071824030104588450704100c41b10280000d02c58034000041e07110b80165148001141c1c21000d14152105084411410041880345c0542d21000d01c100d540d241040701d00d01c00b405014000031940041d10b041410101e40e02e404601c280c1c040c145504480300042200b550002da9800c2082d5552448418207043c01900c17100502002c1c82d15000005010000346c41540d00c510800e000c104000401c4403d035644607400c03070250a84281074000814010b543ca400d1101c03c0b0b01401101d492512a0780003070b0b07800010b904044002a140640560140d81001c100302d003601d5580003030850b200c004254481a1a4010020801c11910401090512500381e00410040d90080c201d44074542c7c503036003480003a921920505014100d61b080d2041040d03103034171421002c1c844d40000751424900d0102400070340348918a03d814503000401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 716899118 1250 716897868 716897891
    0xa1b0203040308071e21090e01080304050108040c17240403120b01021203040c0914091c0c0203031b0c0a0305070506030403030e030301030c06020d050705060703091401151e030f0312 80
    0x79005901c6c82c00c0036410002c410303004500200800490380c48404500490f000501c0b1204012098a00340c0703000f0b20745051150340707034100f401009c64075510030004001501c000f464548000714000c030410114000c11a41f5031907035001e07030700007681c00c85020300001c0100d5071040d413112150b00166010325052044800210754212214595401030743c0440d00740c841900e04020000882c02200351031803404121084900d000e070b4540340c8490020540800b504500c44e0000e05180c002c860005286401a080f203403034101410032a0b01880c4008049160741c400d040c4605440c0c6004800e03882a664441c0103045c00a06e070200303010140d040540308806040d00c2e00c400300c2c0d0802d01000914000e40c0185d068145092510304040c0c03c0100800c092010810104010000704900068041e0002c08900d030024000300103007030083d112600c0720040c900c15400c1074070741c112109001440c20291801c10741881c0c1104115810790b43c046000348402048804500c808001003405005600c0102e0043c0c80c0c007241510320360 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 716900368 1250 716899118 716899133
    0x41a070804141f060f06080613051b030702100b0f030a0303050c09040504230d0e0121020d0e06061e0613030615061101050f06150409050a1b0203040308071e 69
    0x400b06185220fa07030303031000c1003017001088402d0f00400301c40c104410a814980041b90a01c900306502d510340d6a1502c001c52034011980300590741711218528401d490f0f0501000094032a840300b07428100c2c2504100700c00720a4603107140c0b4445020701c014002c02c031841a60f038003540030304402049415030030814411501241c680b4003402d0300c2184103502504c1d08a0b110007882e02c4e007801680c5105000c0e0301401412038050b800032711641d0b18160900f01600010030002e050015400e800c01584040d42c0041068504021160021083c80c3d080c3e00030303920113645a40600c2219180003250f06400c58102e2040815410440d00405507994070400d0141511303240d40740d0b23600781c803c582c41411401071440000c1200c0b640c8a400c20394a070700c043c8000c1c0300e6420080b0700948550740107888180308808584d10303800c00c0b0052404507401021803400900a9103040b884180c000c100c0715101c42c009440c0b0703e0384951001c3c0301004440035170b5070040b0414140440354803400420030f500341c01c591010b04240740040100c0d00c00d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 716901618 1250 716900368 716900413
    0x40f020910020a02010801080106032609030f0d030c021515120706020a0314090a050108130b0a050f09060c030c09040b04052a0c07091109090f041a07080414 69
    0x102c0d00100b500402c01c4c4001484920142d0040000d0703490200e09000080c6640000ca0045040c854000480e40c440345d50164a03225101d421541886510140c41e07010744041013100d10314046c0e860400c00701c20100000d82c2c40d040c02520308545e0310440400641030000c2000300c40483c400180141c4690400c40341e0f494900300c403a4001f070003d85d0040310703400201940aa0070000e03190540c83c10302d0818458201041c0400d50301c3c01080e0602c034101c4001340705c0c00c404035412210300c0c0e0050132003111810f1410031400189410380b03680164682403000203203400c4c0c0001c3c00038011020342020501e95a5800500041508400700c01903100351100d1460900d41d94030b002c2c041c05002300ca545210840d41541c8a0b140034018413a032000e0104091114059610303012403514200d46500781301140c0180d07034403004100780c46050f5407298418000c50910080c1c040031813205109038424823080d0103030b0420000d0030b45184000c651034000204428002030000781010610b903403540c07001c8104d90280c40c0c04214031961070007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 716902868 1250 716901618 716901649
    0x4210504090b01030e0c0f03013902010e0312040c09020c0c19061b11030a0c06110109021e1807111002130b070c05060a0305042f040f0209 61
    0x1010030207000c1e141e203500c15031085a400342010803900c0440c08103030303440b003566032940c03440340e48100c9000115403402e40000c005c1820700c407000e29041d4001445800904820000d1409000180284030602c1d401440381e50b40d0564054001d50510382421142000440b0081003143c450202140000300c02e01a4009401c501c0c0744072001d4034803500c1c00c10038001c9038403445600c4150b400b60302004108807174000c55450010b8800902240c1258400d0508007a0009100c05040d010f10442d160101030081c2815020180c0f21180c1d03c5012031800040160b0030f0b10500b60010f580701805805c0c4808500b2040c4600030042d0307015290701c1c4000d15419100c3c2014008861000104d5401401075020355000d1100621140c0200740031400c0c00000014000307451140e0040171641d4100180100038464000000d170f0051078010074007030b500d00328000d00070f0281034140d41c22212603020003c518040c00786041c0314042c044160600110065101c01004042c00701c000c28000d40c01e6003045446126218004811441007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 716904118 1250 716902868 716902877
    0x24011e15030f0507081b0a14070303050f010b0705120a1101050403263c0a0c03141b03070302090418051c050708250b06040c170f0421 59
    0x2140a1500020703201c0c000d00704810060f1000170006c0440341d580e4421048a1303404101911501c1d148804c1d01c180070400e607210f07080900811801c00b0035030301d41c01c41340c030407004c800c00911166645c907600103c60048100081c52500030102d14903440300c40f28040c006101b0700d80b51120810f1007050006084032803e40d42500012100c0d01502c0c01904818010f0003e03600c441d080c0c0c01035141c820110030700e1a003001d0140500301d00c050700014088507050034044814105090b05240e03800d240e11158024403c80f10094017007420281416032941504030490b10444100082200442807100d55412a030300080c0000d0916509000d00c03101030310350344100300a001c040941201c50181c00c0c20024540118600d042203440348012090101c158044240c84045900c0403001d6160401060500440105038041e21210200c00362420f0500a034002c900d4068030003503c0801a0603080c0000f01d80d881382038066954030f00c1c08040411080000540110740c0580200a098038030354648245200a8251064040008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 716905368 1250 716904118 716904131
    0xc06090c090f0f1802010921020a08030c071212120e031206120a1707020a170a0c0609080c01081b1c0605030c10050a140c0304030524011e1503 63
    0x10103c5200390118422514103483e1a40415130009001e5074003405511103038000303012a042602504e841078004154014403030a80e05031500429540c81d004210007000d40c0c4078441000404140810705e48500035009405071803100d5010000346c48001e07807000000c40d8140d40d50504131a510051020f00400d0003019141c081600f003490400054010800800300650032440b0807400041190044a8201d00d1400c02540c0fa5076003800010414290b0342c0c0a0411540c52009299980c200441c00c6142107109151101c009a2204011508247c0d603009100c8240c0c050ba401040c41d41c000d120407588011020018a5400c0f03400320541965080303a42d000201885a404541034805c46001d5030014100c150000c20818690300000750211b401051a181440380024040c10304d84c2c4101400000c0180902d0f5032980c2d4407420303000541c1c950061100f41e491703010741514180386d8a5507035421503616820112201e8141d0800f9207045030180c0c1e461803000c000700d514070002640006d42078981c05200c2180c0380000c69 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 716906474 1106 716905368 716905391
    0x1207030b150a03031716020c04020903030f161a0403050304230105010803091e060304110a081618051b090d0c09090c0b0a0c06090c090f 60
    0x2081d502d11001c0141500300a036482c403412800c0420b012543c451000d0340000c0310385540c1a006070004000b03003115207000e4010300030705400101920326081c0c11605000b42c1d0f92002260612028a0030701c2c0d001407000018800785001019001c0f545103180550b0020080d02c0b0081000b080074140061214010f000c02d102845100807aa00800055844862480d500e80100c0d40b079621030945111090a210010074098400c490302500321070079602c669841c1c401c40010301141d5500000321480028001108100314600c4400741204500181c0c00d0410047c1902204030074220840c0c1404140030061007503000c490000704000750380c95100e0ba240c400240c0c206a00d404054071b2034025902c00701d1390600951007158120311070302101048681d1510200924061342c1c0c011404078120300260340c0881c800ea000316840c40d104008044565845940e594200d500380000280320720b9640c80c04402 = true := by decide +kernel

theorem cover : BRFrame.Cov 716726618 716906474 := by
  have h0 := BRFrame.cov_init 716726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 716726618 ≤ n) (h2 : n < 716906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
